# Weight sums for the geometric mixture (paper, Appendix A) and the final bound
#   min_t [(sqrt(B) t - sqrt(V))^2/(2t) + S(t)/(2t)] <= 1/(2T) + 2T e + 8T^3 cp,
#   S(t) = (1+t)^2 e + (1+t)^4 cp, taking t = min(sqrt(V/B), T), for V >= B.
import math, random
for t in [0.5, 1, 3, 10]:
    r = 1/(1+t)**2; w = lambda k: r*(1-r)**(k-1)
    s1 = sum(w(k)*k for k in range(1, 20000)); s2 = sum(w(k)*math.comb(k, 2) for k in range(1, 20000))
    K = 200; tail = sum(w(k)*k for k in range(K+1, 40000))
    print(t, abs(s1-(1+t)**2) < 1e-6, abs(s2-(1-r)/r**2) < 1e-4, s2 <= (1+t)**4,
          abs(tail-(1-r)**K*(K+1/r)) < 1e-9)
random.seed(0); bad = 0
for _ in range(200000):
    B = random.random()**3; V = random.random()
    if V < B: continue
    e = 10**random.uniform(-8, -1); cp = 10**random.uniform(-12, -1); T = random.uniform(1, 1e3)
    t = min(math.sqrt(V/B) if B > 0 else 1e18, T)
    val = (math.sqrt(B)*t-math.sqrt(V))**2/(2*t) + ((1+t)**2*e + (1+t)**4*cp)/(2*t)
    if val > 1/(2*T) + 2*T*e + 8*T**3*cp + 1e-12: bad += 1
print("violations of the T-bound:", bad)
