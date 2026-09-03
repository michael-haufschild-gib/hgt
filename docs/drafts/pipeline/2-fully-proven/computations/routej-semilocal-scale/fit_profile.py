import json, math
import numpy as np
from scipy.optimize import least_squares
r=json.load(open("routej_collapse.json")); rows={row["p"]:row for row in r}
out={}
for p in (1009,1511):
    D=np.array(rows[p]["D_all"]); ks=np.arange(1,len(D)+1); x=2*ks/p; Phi=math.sqrt(p)*D
    m=(x>=0.35)&(2*ks<=3500); X=x[m]; Y=Phi[m]
    def model(par, X):
        A,alpha,omega,phi,B,beta=par
        return X**alpha*(A*np.sin(omega*X+phi)) + B*X**beta
    best=None
    for w0 in (3.5,4.0,4.5):
        for a0 in (1.0,1.5,2.0,2.5):
            sol=least_squares(lambda par: model(par,X)-Y,[30.0,a0,w0,0.0,0.0,0.5],max_nfev=20000)
            if best is None or sol.cost<best.cost: best=sol
    A,alpha,omega,phi,B,beta=best.x
    rms=math.sqrt(2*best.cost/len(X))
    print("p=%d free-omega fit: A=%.3f alpha=%.3f omega=%.4f phi=%.4f (phi/pi=%.4f) B=%.3f beta=%.3f rms=%.3f rms(Phi)=%.2f"%(p,A,alpha,omega,phi,phi/math.pi,B,beta,rms,math.sqrt(np.mean(Y**2))))
    best4=None
    for a0 in (1.0,1.5,2.0,2.5):
        sol=least_squares(lambda par: par[0]*X**par[1]*np.sin(4*X+par[2]) + par[3]*X**par[4]-Y,[30.0,a0,0.0,0.0,0.5],max_nfev=20000)
        if best4 is None or sol.cost<best4.cost: best4=sol
    A4,al4,ph4,B4,be4=best4.x
    print("        omega=4 fit:  A=%.3f alpha=%.3f phi=%.4f (phi/pi=%.4f) B=%.3f beta=%.3f rms=%.3f"%(A4,al4,ph4,ph4/math.pi,B4,be4,math.sqrt(2*best4.cost/len(X))))
    out[p]={"free":dict(A=A,alpha=alpha,omega=omega,phi=phi,B=B,beta=beta,rms=rms),"omega4":dict(A=A4,alpha=al4,phi=ph4,B=B4,beta=be4,rms=math.sqrt(2*best4.cost/len(X)))}
    for xv in (0.5,0.6,1.0,1.269,1.5,1.8,2.024,2.3):
        k=int(round(xv*p/2)); print("  x=%.3f Phi=%8.3f  -Phi/sin(4x)=%8.3f  Phi/x^2=%7.3f"%(xv,Phi[k-1],-Phi[k-1]/math.sin(4*xv),Phi[k-1]/xv**2))
json.dump(out,open("phi_fit.json","w"),indent=1)
