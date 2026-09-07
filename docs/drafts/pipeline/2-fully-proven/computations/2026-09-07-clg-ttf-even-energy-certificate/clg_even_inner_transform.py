exec(open('/tmp/clg_even_inner_explore.py').read().split("if __name__")[0])
from time import time
start=time()
data=json.load(open('/tmp/clg_even_inner_det.json'))
D={tuple(e):F(c) for e,c in data['D']};H={tuple(e):F(c) for e,c in data['head']}
G0=scale(mul(p[0],add(scale(mul(a,w),F(1,8)),scale(u,F(5,16)))),F(-137,1000))
G1=scale(p[0],F(-6,19))
D=add(D,scale(mul(H,add(G1,scale(G0,-1))),10**12))
R={}
for (ue,ae,we),c in D.items():
 assert (ue+we)%2==0
 for j in range(we+1):
  e=((ue+we)//2,ae,j)
  R[e]=R.get(e,F(0))+c*comb(we,j)/4**j
R={e:c for e,c in R.items() if c}
print('relative-shear polynomial terms',len(R),flush=True)
# coordinates r,t,v: a = 191/10 -12r/5+t(1/10+16r/15)
Ap={(0,0,0):F(191,10),(1,0,0):F(-12,5),(0,1,0):F(1,10),(1,1,0):F(16,15)}
aps=[{Z:F(1)}]
for n in range(max(e[1] for e in R)):aps.append(mul(aps[-1],Ap))
T={}
for (re,ae,ve),c in R.items():
 for e,d in aps[ae].items():
  f=(e[0]+re,e[1],e[2]+ve)
  T[f]=T.get(f,F(0))+c*d
T={e:c/F(10**24) for e,c in T.items() if c}
print('unit cube terms',len(T),'degrees',tuple(max(e[i] for e in T) for i in range(3)),'elapsed',time()-start,flush=True)
with open('/tmp/clg_even_inner_unit.json','w') as f:json.dump([[list(e),str(c)] for e,c in sorted(T.items())],f)
# Useful sufficient coefficient minorants: retain r,t,v cubic, bound negative higher powers downward.
for cut in [0,1,2,3]:
 lower={}
 for e,c in T.items():
  if c<0:
   f=tuple(min(i,cut) for i in e)
   lower[f]=lower.get(f,F(0))+c
  elif all(i<=cut for i in e):lower[e]=lower.get(e,F(0))+c
 print('minorant cut',cut,'coeff count',len(lower),'lowest grid',min(ev(lower,*s) for s in product([0,.5,1],repeat=3)),flush=True)
