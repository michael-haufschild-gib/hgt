import math
def coth(x): return 1.0/math.tanh(x)
def csch2(x): return 1.0/math.sinh(x)**2
def phi(x): return csch2(x)*coth(x)   # -2*d/dx csch2 = ... φ = csch²·coth, positive decreasing

def poles(c,d):
    T=[0.0]*(d+2)
    for j in range(1,d+1): T[j+1]=T[j]+c/j
    return T

def field(T,d,x,i):
    # sum over all poles T_1..T_{d+1}, i.e. indices 1..d+1
    return sum(coth((x-T[j])/2) for j in range(1,d+2))

def equilibrium_theta(c,d,i):
    # solve field=-(d+1) in gap (T_i,T_{i+1}); level = -(#poles)= -(d+1)
    T=poles(c,d); a,b=T[i],T[i+1]
    lvl=-(d+1)
    lo,hi=a+1e-12*(b-a),b-1e-12*(b-a)
    # field decreasing; bisect
    for _ in range(80):
        mid=(lo+hi)/2
        if field(T,d,mid,i)>lvl: lo=mid
        else: hi=mid
    s=b-(lo+hi)/2                 # distance to ahead pole
    return s/(b-a)                # theta = s/delta

# --- 1. c_strip: max_i theta*(i) crosses 1/2 ---
print("=== c_strip: max theta* over i (d=400) ===")
for c in (2.0,2.3,2.5,2.7,2.9,3.0,3.2):
    d=400
    thetas=[equilibrium_theta(c,d,i) for i in range(1,25)]  # sparse edge dominates
    print(f"  c={c}: max theta*(edge) = {max(thetas):.4f}  (theta at i=1: {thetas[0]:.4f})")

# --- 2. rho at the E=0 shape boundary, vs d and c (universality) ---
def rho_at_boundary(c,d):
    T=poles(c,d)
    # find outer i where behind count (i-1) >= ahead count (d-i): i-1>=d-i -> i>=(d+1)/2
    i=(d+1)//2 + 1
    a,b=T[i],T[i+1]; m=(a+b)/2
    behind=[m-T[j] for j in range(i-1,0,-1)]
    ahead=[T[j]-m for j in range(i+2,d+2)]
    M=min(len(behind),len(ahead)); E=len(behind)-M
    D=sum((behind[k]-ahead[k])/2*csch2(ahead[k]/2) for k in range(M))
    return D/(2*M+2*E+2), i/d, E
print("=== rho at E>=0 boundary vs d (universality) ===")
for c in (2.0,3.0,5.0):
    print(f"  c={c}:")
    for d in (100,400,1000,4000):
        r,idr,E=rho_at_boundary(c,d)
        print(f"    d={d:5d}: rho={r:.4f}  i/d={idr:.4f}  E={E}")

# --- 3. dW/ds sign at real equilibria: outer (theta<1/2) vs strip (theta>1/2) ---
def dWds_sign(c,d,i):
    T=poles(c,d); a,b=T[i],T[i+1]; lvl=-(d+1)
    lo,hi=a+1e-12*(b-a),b-1e-12*(b-a)
    for _ in range(80):
        mid=(lo+hi)/2
        if field(T,d,mid,i)>lvl: lo=mid
        else: hi=mid
    xs=(lo+hi)/2
    # dW/ds where W=1/4 sum csch²((x-T)/2); s = b-x so d/ds = -d/dx
    # dW/dx = 1/4 sum csch²'((x-T)/2)*(1/2) = -1/4 sum phi((x-T)/2)*sign... 
    # csch²(u)' = -2 csch²coth = -2 phi(u); with u=(x-T)/2, d/dx=1/2 -> d/dx csch²=-phi(u)
    dWdx=sum(-phi((xs-T[j])/2) for j in range(1,d+2))/4.0
    dWds=-dWdx
    th=(b-xs)/(b-a)
    return th,dWds
print("=== dW/ds sign: outer vs strip (c=2, d=400) ===")
for i in (1,3,8,20,60,200,380):
    th,dw=dWds_sign(2.0,400,i)
    reg="STRIP" if th>0.5 else "outer"
    print(f"  i={i:4d}: theta*={th:.4f} [{reg}]  dW/ds={dw:+.4f}  sign={'+' if dw>0 else '-'}")
