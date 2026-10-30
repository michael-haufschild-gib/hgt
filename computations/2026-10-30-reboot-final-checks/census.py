import math
from mpmath import mp, quad, cot, sqrt, mpf
mp.dps=30
# Montgomery-Taylor constant HD(1)=3/2 - 2^{-1/2} cot(2^{-1/2})
s=1/sqrt(2); HD=mpf(3)/2 - s*cot(s); print("HD(1)=",HD, " 2HD/(1+HD)=",2*HD/(1+HD), " 1-(1-HD)/(1.5+sqrt2)=",1-(1-HD)/(1.5+sqrt(2)))
# rank-trace certificate 2-kappa(lambda), kappa = 1/l + (2/l^2) int_0^l (l-a)F(a) da, GUE F
def F(a): return a if a<1 else 1.0
for l in [0.5,1,4/3,1.5,math.sqrt(3),2,3,5,10]:
    k=1/l+2/l**2*quad(lambda a:(l-a)*F(a),[0,min(1,l),l] if l>1 else [0,l])
    print(f"lambda={l:.4f} cert(GUE)={2-k:.6f} closed form={1-1/(3*l*l) if l>=1 else 2-1/l-l/3:.6f}")
