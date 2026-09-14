from common import *
def em(s,N,M):
    # Explicit Euler--Maclaurin formula, implemented independently of mpmath.zeta.
    logs=[mp.log(n) for n in range(1,N)];v=mp.fsum(mp.exp(-s*l) for l in logs)
    logN=mp.log(N);v+=mp.exp((1-s)*logN)/(s-1)+mp.exp(-s*logN)/2
    rising=mp.mpc(1)
    for j in range(1,2*M):
        rising*=s+j-1
        if j%2:
            k=(j+1)//2;v+=mp.bernpoly(2*k,0)/mp.factorial(2*k)*rising*mp.exp((-s-j)*logN)
    return v

def independent_points(path,kind,dps):
    # Check 9 spread-out path locations with two independently chosen EM truncations.
    old=mp.mp.dps;mp.mp.dps=dps+70;rows=[]
    indices=sorted(set(round(j*(len(path)-1)/8) for j in range(9)))
    for index in indices:
        row=path[index];u=mp.mpf(row[0]);s=mp.mpc(row[1],row[2]);w=target(kind,u)
        n=max(96,int(abs(mp.im(s)))+80);m=dps+25
        a=em(s,n,m);c=em(s,n+40,m+20)
        rows.append(dict(u=str(u),zeta_disagreement=str(abs(c-mp.zeta(s))),truncation_disagreement=str(abs(a-c)),target_residual=str(abs(c-w))))
    mp.mp.dps=old;return rows
