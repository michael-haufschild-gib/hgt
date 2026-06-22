"""
The reproducing kernel of the zero measure as a POSITIVE FUNCTION on R.
K(y) := e(y)^T (H^0)^{-1} e(y) = max_p p(y)^2/Q_0[p],  e(y)=(y^i).  Under RH (H^0>0) K(y)>0 for all real y.
An off-line zero makes H^0 indefinite -> K(y) dips NEGATIVE somewhere. Scan K(y) for:
  (a) on-line divisor  -> expect K(y)>0 everywhere;
  (b) injected off-line quartet at gamma0 (d>d*) -> find where K(y)<0, and whether the dip locates the
      off-line atom's reciprocal coordinate Re y_off = Re(-(beta+i gamma0)^{-2}).
args: N d gamma0 beta dps
"""
import sys, mpmath as mp
N=int(sys.argv[1]) if len(sys.argv)>1 else 250
d=int(sys.argv[2]) if len(sys.argv)>2 else 10
g0=mp.mpf(sys.argv[3]) if len(sys.argv)>3 else mp.mpf(20)
beta=mp.mpf(sys.argv[4]) if len(sys.argv)>4 else mp.mpf('0.2')
mp.mp.dps=int(sys.argv[5]) if len(sys.argv)>5 else 150
KMAX=2*d+1
with open("/root/gam_cache.txt") as f:
    hdr=f.readline().split(); gam=[mp.mpf(f.readline().strip()) for _ in range(N)]
TN=gam[-1]
def tail(k):
    pp=2*k-1; return (1/mp.pi)*TN**(-pp)/pp*(mp.log(TN/(2*mp.pi))+mp.mpf(1)/pp)
Tb={k:2*mp.fsum(g**(-2*k) for g in gam)+tail(k) for k in range(1,KMAX+1)}
def Kfun(Td):
    H=mp.matrix(d+1,d+1)
    for i in range(d+1):
        for j in range(d+1): H[i,j]=Td[i+j+1]
    Hi=mp.inverse(H)
    def K(y):
        e=mp.matrix([y**i for i in range(d+1)]); return (e.T*Hi*e)[0,0]
    return K
wo=mp.mpc(beta,g0); yo=-1/wo**2
Tp={k:mp.re(Tb[k]+2*(yo**k+mp.conj(yo)**k)) for k in range(1,KMAX+1)}
Kon=Kfun(Tb); Koff=Kfun(Tp)
print(f"# kernel scan, N={N}, d={d}, gamma0={mp.nstr(g0,5)}, beta={mp.nstr(beta,3)}, dps={mp.mp.dps} (cache {hdr[0]}@{hdr[1]})")
print(f"# off-line atom: Re y_off = {mp.nstr(mp.re(yo),5)}, |y_off|={mp.nstr(abs(yo),5)}, Im y_off={mp.nstr(mp.im(yo),5)}")
# scan y over negative axis (where trivial zeros + pole live) and a bit positive
ys=[mp.mpf(t)/mp.mpf(1000000) for t in range(0,6001,25)]   # positive y in [0,0.006], fine, covers y_off~0.0025
print(f"#    y          K_online        K_offline      (off<0 => kernel dips negative)")
neg_on=[]; neg_off=[]
for y in ys:
    ko=Kon(y); kf=Koff(y)
    flag=' <<NEG' if kf<0 else ''
    if ko<0: neg_on.append(y)
    if kf<0: neg_off.append(y)
    if flag or abs(float(y)*4000-round(float(y)*4000))<1e-9:
        print(f"  {mp.nstr(y,5):>9s}   {mp.nstr(ko,6):>13s}   {mp.nstr(kf,6):>13s}{flag}")
print(f"# K_online negative anywhere? {'yes at '+mp.nstr(neg_on[0],4) if neg_on else 'NO (positive everywhere)'}")
if neg_off:
    print(f"# K_offline NEGATIVE on y in [{mp.nstr(min(neg_off),4)}, {mp.nstr(max(neg_off),4)}]  (Re y_off={mp.nstr(mp.re(yo),5)})")
else:
    print(f"# K_offline stays positive on the grid (d below detection? d*={'~'}{mp.nstr(g0/3,3)})")
