using OpenTK;
using System;
using System.Collections.Generic;
using System.IO;
using System.Threading;
using System.Threading.Tasks;

namespace RayTracingMultiTrack
{
    struct Vec
    {
        public double x, y, z;
        public Vec(double x_ = 0, double y_ = 0, double z_ = 0) { x = x_; y = y_; z = z_; }
        public static Vec operator +(Vec a, Vec b) { return new Vec(a.x + b.x, a.y + b.y, a.z + b.z); }
        public static Vec operator -(Vec a, Vec b) { return new Vec(a.x - b.x, a.y - b.y, a.z - b.z); }
        public static Vec operator *(Vec a, double b) { return new Vec(a.x * b, a.y * b, a.z * b); }

        public Vec Mult(Vec b) { return new Vec(x * b.x, y * b.y, z * b.z); }
        public Vec Norm()
        {
            double lenght = Math.Sqrt(x * x + y * y + z * z);
            return new Vec(x / lenght, y / lenght, z / lenght);
        }


        public double Dot(Vec b) { return x * b.x + y * b.y + z * b.z; }

        public static Vec operator %(Vec a, Vec b) { return new Vec(a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x); }
    };

    struct Ray
    {
        public Vec o, d;
        public Ray(Vec o_, Vec d_) { o = o_; d = d_; }
    };

    enum Refl_t
    {
        DIFF, SPEC, REFR
    };

    struct Sphere
    {
        public double rad;
        public Vec p, e, c;
        public Refl_t refl;
        public Sphere(double rad_, Vec p_, Vec e_, Vec c_, Refl_t refl_)
        {
            rad = rad_;
            p = p_;
            e = e_;
            c = c_;
            refl = refl_;
        }

        public double Intersect(Ray r)
        {
            Vec op = p - r.o;
            double t, eps = 1e-4, b = op.Dot(r.d), det = b * b - op.Dot(op) + rad * rad;
            if (det < 0) return 0; else det = Math.Sqrt(det);
            return (t = b - det) > eps ? t : ((t = b + det) > eps ? t : 0);
        }
    }

    class Program
    {

        static readonly Sphere[] spheres = new Sphere[] {//Scene: radius, position, emission, color, material
            new Sphere(1e5, new Vec( 1e5+1,40.8,81.6), new Vec(),new Vec(.75,.25,.25),Refl_t.DIFF),//Left
            new Sphere(1e5, new Vec(-1e5+99,40.8,81.6),new Vec(),new Vec(.25,.25,.75),Refl_t.DIFF),//Rght
            new Sphere(1e5, new Vec(50,40.8, 1e5),     new Vec(),new Vec(.75,.75,.75),Refl_t.DIFF),//Back
            new Sphere(1e5, new Vec(50,40.8,-1e5+170), new Vec(),new Vec(),           Refl_t.DIFF),//Frnt
            new Sphere(1e5, new Vec(50, 1e5, 81.6),    new Vec(),new Vec(.75,.75,.75),Refl_t.DIFF),//Botm
            new Sphere(1e5, new Vec(50,-1e5+81.6,81.6),new Vec(),new Vec(.75,.75,.75),Refl_t.DIFF),//Top
            new Sphere(16.5,new Vec(27,16.5,47),       new Vec(),new Vec(1,1,1)*.999, Refl_t.SPEC),//Mirr
            new Sphere(16.5,new Vec(73,16.5,78),       new Vec(),new Vec(1,1,1)*.999, Refl_t.REFR),//Glas
            new Sphere(600, new Vec(50,681.6-.27,81.6),new Vec(12,12,12),  new Vec(), Refl_t.DIFF) //Lite
        };

        static double Clamp(double x)
        {
            return x < 0 ? 0 : x > 1 ? 1 : x;
        }

        static int ToInt(double x)
        {
            return (int)(Math.Pow(Clamp(x), 1 / 2.2) * 255 + .5);
        }

        private static double Erand48()
        {
            Random random = new Random();
            return random.NextDouble();
        }

        private static Vec Radiance(Ray r, int depth)
        {
            int id = 0;

            double t;
            double ni = spheres.Length - 1, di, inf = t = 1e20;
            for (int i = (int)ni; i >= 0; i--)
            {
                di = spheres[i].Intersect(r);
                if ((di != 0 && di < t))
                {
                    t = di;
                    id = i;
                }
            }
            if (!(t < inf)) { return new Vec(); }
            Sphere obj = spheres[id];
            Vec x = r.o + r.d * t, n = (x - obj.p).Norm(), nl = n.Dot(r.d) < 0 ? n : n * -1, f = obj.c;
            double p = f.x > f.y && f.x > f.z ? f.x : f.y > f.z ? f.y : f.z;
            if (++depth > 5)
            {
                double rand = Erand48();
                if (rand < p && depth < 150) f *= (1 / p); else return obj.e;
            }

            if (obj.refl == Refl_t.DIFF)
            {
                double r1 = 2 * Math.PI * Erand48(), r2 = Erand48(), r2s = Math.Sqrt(r2);
                Vec w = nl, u = ((Math.Abs(w.x) > .1 ? new Vec(0, 1) : new Vec(1)) % w).Norm(), v = w % u;
                Vec d = (u * Math.Cos(r1) * r2s + v * Math.Sin(r1) * r2s + w * Math.Sqrt(1 - r2)).Norm();
                return obj.e + f.Mult(Radiance(new Ray(x, d), depth));
            }
            else if (obj.refl == Refl_t.SPEC)
            {
                return obj.e + f.Mult(Radiance(new Ray(x, r.d - n * 2 * n.Dot(r.d)), depth));
            }

            Ray reflRay = new Ray(x, r.d - n * 2 * n.Dot(r.d));
            bool into = n.Dot(nl) > 0;
            double nc = 1, nt = 1.5, nnt = into ? nc / nt : nt / nc, ddn = r.d.Dot(nl), cos2t;
            cos2t = 1 - nnt * nnt * (1 - ddn * ddn);
            if (cos2t < 0)
            {
                return obj.e + f.Mult(Radiance(reflRay, depth));
            }

            Vec tdir = (r.d * nnt - n * ((into ? 1 : -1) * (ddn * nnt + Math.Sqrt(cos2t)))).Norm();
            double a = nt - nc, b = nt + nc, R0 = a * a / (b * b), c = 1 - (into ? -ddn : tdir.Dot(n));
            double Re = R0 + (1 - R0) * c * c * c * c * c, Tr = 1 - Re, P = .25 + .5 * Re, Rp = Re / P, TP = Tr / (1 - P);
            return obj.e + f.Mult(depth > 2 ? (Erand48() < P ?
                Radiance(reflRay, depth) * Rp : Radiance(new Ray(x, tdir), depth) * TP) :
                Radiance(reflRay, depth) * Re + Radiance(new Ray(x, tdir), depth) * Tr);
        }

        private static void Main(string[] args)
        {
            if (args is null)
            {
                throw new ArgumentNullException(nameof(args));
            }

            int w = 1024, h = 768, samps = 500;
            samps /= 4;
            Ray cam = new Ray(new Vec(50, 52, 295.6), new Vec(0, -0.042612, -1).Norm());
            Vec cx = new Vec(w * .5135 / h);
            Vec cy = (cx % cam.d).Norm() * .5135;
            Vec[] c = new Vec[w * h];

            void action(object obj)
            {
                int a = (int)obj;

                for (ushort x = 0; x < w; x++)
                {
                    ushort[] Xi = new ushort[] { 0, 0, (ushort)(a * a * a) };
                    for (int sy = 0, i = (h - a - 1) * w + x; sy < 2; sy++)
                        for (int sx = 0; sx < 2; sx++)
                        {
                            Vec r = new Vec();
                            for (int s = 0; s < samps; s++)
                            {
                                double r1 = 2 * Erand48(), dx = r1 < 1 ? Math.Sqrt(r1) - 1 : 1 - Math.Sqrt(2 - r1);
                                double r2 = 2 * Erand48(), dy = r2 < 1 ? Math.Sqrt(r2) - 1 : 1 - Math.Sqrt(2 - r2);
                                Vec d = cx * (((sx + .5 + dx) / 2 + x) / w - .5) + cy * (((sy + .5 + dy) / 2 + a) / h - .5) + cam.d;
                                r += Radiance(new Ray(cam.o + d * 140, d.Norm()), 0) * (1.0 / samps);
                            }
                            c[i] = c[i] + new Vec(Clamp(r.x), Clamp(r.y), Clamp(r.z)) * .25;
                        }
                }
            }

            List<Task> tasks = new List<Task>();

            for (int i = 0; i < h; i++)
            {
                int index = i;
                tasks.Add(Task.Factory.StartNew(action, index));
            }

            Task.WaitAll(tasks.ToArray());

            using StreamWriter writetext = new StreamWriter("D:\\write.ppm");
            writetext.WriteLine("P3");
            writetext.WriteLine(w + " " + h);
            writetext.WriteLine("255");
            for (int i = 0; i < w * h; i++)
            {
                writetext.Write(ToInt(c[i].x) + " " + ToInt(c[i].y) + " " + ToInt(c[i].z) + " ");
            }
        }
    }

}
