"""
gpt/34 core (A+B): does any seam-value (S_k) detector separate zeta from SAME-DENSITY RANDOM?
For 4 zero sets compute S_k = 2 sum_n gamma_n^{-2k} (k=1..N) and run PSLQ relation searches against
{pi^{2k}} and {pi^{2k}, beta(2k)} (the fused-arch field), reporting relation height (max |coeff|).
 - AP gamma_n = c*n: S_k proportional to zeta(2k) ~ rational*pi^{2k}  => LOW-height relation (separates).
 - zeta: S_k = arch(zeta,beta) + PRIME part  => no finite relation in Q(pi,beta).
 - same-density random: generic                => no relation.
If zeta behaves like same-density random (both: no relation), S_k-only is NOT an arithmetic detector
(the established no-go). AP separating is just simplicity, not zeta-arithmetic.
args: N dps
"""
import sys, mpmath as mp, hashlib
N=int(sys.argv[1]) if len(sys.argv)>1 else 6
mp.mp.dps=int(sys.argv[2]) if len(sys.argv)>2 else 60
Nz=120
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gz=[mp.mpf(f.readline().strip()) for _ in range(Nz)]
def det_rand(n):  # deterministic uniform(-1,1) from a hash (reproducible, pod-side)
    h=hashlib.sha256(str(n).encode()).hexdigest(); return mp.mpf(int(h[:12],16))/mp.mpf(16**12)*2-1
# build 4 zero sets (heights gamma_n>0)
def meangap(g): return 2*mp.pi/mp.log(g/(2*mp.pi)+2)
TN=gz[-1]
def tailz(k):  # tail of the zeta seam-moment beyond gamma_Nz
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
g_jit=[gz[n]+mp.mpf('0.15')*meangap(gz[n])*det_rand(n) for n in range(Nz)]   # jitter, preserves local gaps
# same-density random: random positive gaps with the RvM mean gap (density preserved, arithmetic destroyed)
g_rnd=[]; cur=gz[0]
for n in range(Nz):
    g_rnd.append(cur); cur=cur+meangap(cur)*(1+mp.mpf('0.8')*det_rand(1000+n))
def Sk(name,gam,k):
    if name=='AP(integer n)': return 2*mp.zeta(2*k)           # gamma_n=n exactly => S_k=2*zeta(2k) in Q(pi)
    if name=='zeta': return 2*mp.fsum(g**(-2*k) for g in gam)+tailz(k)
    return 2*mp.fsum(g**(-2*k) for g in gam)                  # finite synthetic divisor: exact
def beta(s): return mp.mpf(4)**(-s)*(mp.zeta(s,mp.mpf(1)/4)-mp.zeta(s,mp.mpf(3)/4))
sets={'zeta':gz,'AP(integer n)':None,'random(same-density)':g_rnd,'jittered-zeta':g_jit}
print(f"# A-axis separation, N={N}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
for name,gam in sets.items():
    print(f"## {name}")
    for k in range(1,N+1):
        s=Sk(name,gam,k); pk=mp.pi**(2*k); bk=beta(2*k)
        r1=mp.pslq([s,pk],maxcoeff=10**6,maxsteps=10**4)
        r2=mp.pslq([s,pk,bk],maxcoeff=10**6,maxsteps=10**4)
        h1='none' if not r1 else f"ht={max(abs(c) for c in r1)}"
        h2='none' if not r2 else f"ht={max(abs(c) for c in r2)}"
        print(f"   k={k}: pslq[S_k,pi^2k]={h1:>10s}   pslq[S_k,pi^2k,beta]={h2}")
