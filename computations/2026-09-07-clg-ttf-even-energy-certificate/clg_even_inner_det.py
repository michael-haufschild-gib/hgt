exec(open('/tmp/clg_even_inner_explore.py').read().split("if __name__")[0])
from time import time
start=time()
def pp(p,n):
 z={Z:F(1)}
 for i in range(n):z=mul(z,p)
 return z
# symmetric 4x4 Hankel determinant, grouped by pair products
h=add(mul(mul(m[0],m[2]),m[4]),scale(mul(m[0],pp(m[3],2)),-1),scale(mul(pp(m[1],2),m[4]),-1),scale(mul(mul(m[1],m[2]),m[3]),2),scale(pp(m[2],3),-1))
x=[m[0],m[1],m[2],m[3],m[4],m[5],m[6]]
# Laplace cofactor decomposition retaining 6th-entry cofactor
from itertools import permutations
D={}
for perm in permutations(range(4)):
 inv=sum(perm[i]>perm[j] for i in range(4) for j in range(i+1,4))
 T={Z:F((-1)**inv)}
 for i in range(4):T=mul(T,x[i+perm[i]])
 D=add(D,T)
 print('det permutation',perm,'terms',len(D),'elapsed',round(time()-start,1),flush=True)
G=add(scale(pp(p[0],2),3),scale(mul(p[0],add(scale(mul(a,w),F(1,8)),scale(u,F(5,16)))),F(-137,1000)))
D=add(D,scale(mul(h,G),F(10**12)))
print('corrected det terms',len(D),'head',len(h),'elapsed',time()-start)
with open('/tmp/clg_even_inner_det.json','w') as f:json.dump({'D':[[list(e),str(c)] for e,c in sorted(D.items())],'head':[[list(e),str(c)] for e,c in sorted(h.items())]},f)
