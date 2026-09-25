from fractions import Fraction as F
from math import comb
from itertools import product
import json
Z=(0,0,0)
def add(*ps):
 o={}
 for p in ps:
  for e,c in p.items(): o[e]=o.get(e,F(0))+c
 return {e:c for e,c in o.items() if c}
def scale(p,c):return {e:v*c for e,v in p.items() if v*c}
def mul(p,q):
 o={}
 for e,c in p.items():
  for f,d in q.items():
   g=tuple(e[i]+f[i] for i in range(3));o[g]=o.get(g,F(0))+c*d
 return {e:c for e,c in o.items() if c}
def diff(p,i):
 o={}
 for e,c in p.items():
  if e[i]:
   f=list(e);f[i]-=1;o[tuple(f)]=c*e[i]
 return o
def ev(p,u,a,w):return sum(float(c)*u**e[0]*a**e[1]*w**e[2] for e,c in p.items())
u={(1,0,0):F(1)};a={(0,1,0):F(1)};w={(0,0,1):F(1)}
v=[add({Z:F(-3)},scale(mul(u,u),F(1,3)),scale(a,F(3,4))),scale(mul(a,w),F(-2)),add({Z:F(2)},scale(a,F(1,2)),scale(mul(u,u),F(2,9)),scale(mul(u,w),F(2,3)))]
p=[add({Z:F(-3,8)},scale(mul(u,u),F(1,24)),scale(a,F(1,16)))]
for n in range(12):p.append(add(*(mul(diff(p[-1],i),v[i]) for i in range(3)),scale(mul(u,p[-1]),F(1,6))))
m=[]
for k in range(7):m.append(scale(add(*(scale(mul(p[i],p[2*k-i]),F((-1)**i*comb(2*k,i))) for i in range(2*k+1))),F((-1)**k)))
def det(mat):
 a=[r[:] for r in mat];ans=1
 for i in range(len(a)):
  val=a[i][i];ans*=val
  if abs(val)<1e-100:return 0
  for j in range(i+1,len(a)):
   d=a[j][i]/val
   for k in range(i+1,len(a)):a[j][k]-=d*a[i][k]
 return ans
if __name__=='__main__':
 print('term counts source:',list(map(len,p)),'moments:',list(map(len,m)))
 best=(1e100,None)
 for U,A,W in product([0,.25,.5,.75,1],[17,18,19,19.2,20],[0,.25,.5,.75,1]):
  mm=[ev(v,U,A,W)/100**k for k,v in enumerate(m)]
  M=[[mm[i+j] for j in range(4)] for i in range(4)]
  G=3*ev(p[0],U,A,W)**2-.137*ev(p[0],U,A,W)*(A*W/8+5*U/16)
  M[3][3]+=G
  D=det(M);H=det([r[:3] for r in M[:3]])
  if D<best[0]:best=(D,(U,A,W,H,D/H))
 print('guidance box minimum det and coordinates/head/schur:',best)
 for U,A,W in [(0,19.15,0),(.5,18.7,.52),(1,17.5,1)]:
  mm=[ev(v,U,A,W)/100**k for k,v in enumerate(m)]
  M=[[mm[i+j] for j in range(4)] for i in range(4)]
  G=3*ev(p[0],U,A,W)**2-.137*ev(p[0],U,A,W)*(A*W/8+5*U/16)
  M[3][3]+=G
  print('guidance point',U,A,W,mm,'G',G,'det',det(M),'head',det([r[:3] for r in M[:3]]))
 with open('/tmp/clg_even_inner_polys.json','w') as f:json.dump({'p':[[[list(e),str(c)] for e,c in sorted(t.items())] for t in p],'m':[[[list(e),str(c)] for e,c in sorted(t.items())] for t in m]},f)
