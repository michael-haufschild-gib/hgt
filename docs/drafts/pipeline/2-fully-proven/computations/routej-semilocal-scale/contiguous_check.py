from mpmath import mp, mpf, hyp2f1
import random
mp.dps = 40; random.seed(3)
F = lambda n, s2: hyp2f1(-n, n+mpf(1)/2, mpf(1)/2, s2)
H = lambda n, s2: hyp2f1(-n, n+mpf(3)/2, mpf(1)/2, s2)
K = lambda n, s2: hyp2f1(-n, n+mpf(5)/2, mpf(3)/2, s2)
e1=e2=0
for n in range(0, 15):
    for _ in range(3):
        s2 = mpf(random.random()*0.9)
        e1 = max(e1, abs(((2*n+1)*F(n+1,s2) + 2*(n+1)*F(n,s2)) / ((4*n+3)*(1-s2)*H(n,s2)) - 1))
        e2 = max(e2, abs((H(n+1,s2)-H(n,s2)) / (-(4*n+5)*s2*K(n,s2)) - 1))
print("(b') (2n+1)F_{n+1}+2(n+1)F_n = (4n+3)(1-s2)H_n : max rel err", e1)
print("(c') H_{n+1}-H_n = -(4n+5) s2 K_n : max rel err", e2)
