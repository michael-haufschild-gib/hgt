import numpy as np, math
def edge(d, c=2.0):
    # T_j = c*H_{j-1}, j=1..d  (0-indexed T[0..d-1]); H_{j-1} cumulative
    Hs = np.concatenate(([0.0], np.cumsum(1.0/np.arange(1,d))))  # H_0..H_{d-1}
    T = c*Hs  # T[0]=T_1=0, T[j]=T_{j+1}
    def F(x):
        return np.sum(1.0/np.tanh((x-T)/2.0)) + d
    root=int(math.sqrt(d)); lo=max(2,root-int(0.8*root)); hi=min(d-2,root+int(1.6*root))
    best=None
    for i in range(lo,hi):
        a,b=T[i-1],T[i]              # gap i between pole i and i+1
        aa,bb=a+1e-9*(b-a), b-1e-9*(b-a)
        # F decreasing on gap; F(aa)>0,F(bb)<0 -> bisect
        for _ in range(80):
            m=0.5*(aa+bb)
            if F(m)>0: aa=m
            else: bb=m
        xs=0.5*(aa+bb); theta=(b-xs)/(b-a)
        if best is None or theta>best[1]: best=(i,theta)
    return best
print("target 1/pi=%.6f  pi/4=%.5f"%(1/math.pi, math.pi/4))
for d in [500,2000,8000,32000]:
    ip,tmax=edge(d); print("d=%6d margin*sqrtd=%.5f i_peak/sqrtd=%.4f theta_max=%.6f"%(d,(0.5-tmax)*math.sqrt(d),ip/math.sqrt(d),tmax))
