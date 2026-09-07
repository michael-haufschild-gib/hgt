import math,json
N=100000
tau=[0]*(N+1)
for d in range(1,N+1):
 for n in range(d,N+1,d): tau[n]+=1
gamma=.5772156649015328606065120900824
A=H=L=T=0.; firstA=firstH=None; minH=(math.inf,None); vals=[]
for n in range(1,N+1):
 L+=math.log(n);T+=tau[n];D=L-T+2*gamma*n
 A+=D;H+=D/(math.sqrt(n+1)+math.sqrt(n))
 if A<0 and firstA is None: firstA=(n,A,D)
 if H<0 and firstH is None: firstH=(n+1,H,D)
 if H/math.sqrt(n+1)<minH[0]: minH=(H/math.sqrt(n+1),n+1)
 if n in [1,3,4,10,100,1000,10000,N]: vals.append((n,A,H,H/math.sqrt(n+1)))
print(json.dumps({'N':N,'first_negative_prefix':firstA,'first_negative_unsigned_channel':firstH,'min_normalized_channel':minH,'checkpoints':vals},indent=2))
