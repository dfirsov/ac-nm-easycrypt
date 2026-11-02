# Stress test of the first-hit reduction A'_k (paper, Appendix A), by exact
# enumeration in the ideal-commitment model.
# A halts with probability eta, independently of m (ideal hiding); otherwise,
# on challenge m, it opens y with probability K[m][y] or refuses with the rest.
# Checks, for random md, R, eta and K:
#   (a) k Real(A'_k) >= E[v g_k] + Pr[halt]
#   (b) k E[prior_k] <= 1 + C(k,2) cp
# With FLAT=1 in the environment, md is uniform, to show the gap in (a) is a
# collision effect that shrinks like 1/N.
import itertools, random, math, os

def run(N, k, seed, flat=False):
    rnd = random.Random(seed)
    md = [1.0 if flat else rnd.random()**3 for _ in range(N)]; s = sum(md); md = [x/s for x in md]
    R = [[rnd.random() < 0.4 for y in range(N)] for m in range(N)]
    K = []
    for m in range(N):
        row = [rnd.random()**2 for _ in range(N)]; tot = sum(row)/rnd.uniform(0.3, 1.0)
        K.append([x/tot for x in row])
    eta = rnd.uniform(0, 0.5); ystar = rnd.randrange(N)
    q = [sum(md[n] for n in range(N) if R[n][y]) for y in range(N)]
    cp = sum(x*x for x in md)
    def jstar(u, y):
        for j in range(k):
            if R[u[j]][y]: return j
        return 0
    realk = priork = 0.0
    for u in itertools.product(range(N), repeat=k):
        pu = math.prod(md[x] for x in u)
        succ = 0.0
        for J in range(k):
            m = u[J]
            s_ = eta*(u[J] == u[jstar(u, ystar)])
            s_ += (1-eta)*sum(K[m][y]*(u[J] == u[jstar(u, y)]) for y in range(N))
            succ += s_/k
        realk += pu*succ
        priork += pu*max(sum(u[i] == u[jstar(u, y)] for i in range(k))/k for y in range(N))
    def g(Rv, qv):
        G = sum((1-qv)**j for j in range(k))
        return Rv*G + (1-Rv)*(1-qv)**(k-1)
    Evg = (1-eta)*sum(md[m]*K[m][y]*g(R[m][y], q[y]) for m in range(N) for y in range(N))
    return k*realk - (Evg + eta), 1 + math.comb(k, 2)*cp - k*priork

if __name__ == "__main__":
    if os.environ.get("FLAT"):
        for N in [4, 8, 16]:
            for k in [2, 3]:
                print(N, k, "max gap in (a):", round(max(run(N, k, s, True)[0] for s in range(5)), 4))
    else:
        w1 = w2 = 1e9
        for seed in range(60):
            for N, k in [(3, 2), (3, 3), (4, 3), (4, 4), (5, 3)]:
                a, b = run(N, k, seed); w1 = min(w1, a); w2 = min(w2, b)
        print("min slack in (a):", w1, "(must be >= 0)")
        print("min slack in (b):", w2, "(must be >= 0)")
