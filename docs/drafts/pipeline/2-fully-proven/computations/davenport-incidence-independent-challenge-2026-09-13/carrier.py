from common import *
import common as c
K=None

def configure(dps):
    global K
    mp.mp.dps=dps
    K=(mp.sqrt(5)/2-mp.sin(2*mp.pi/5))/mp.sin(4*mp.pi/5)
    c.zeta=D

def D(s,n=0):
    budget();logq=mp.log(5);co=[0,1,K,-K,-1]
    value=sum(co[r]*sum(mp.binomial(n,j)*(-logq)**(n-j)*mp.zeta(s,mp.mpf(r)/5,derivative=j) for j in range(n+1)) for r in range(1,5))
    return mp.exp(-s*logq)*value

def completed(s):
    return mp.exp((s+1)/2*mp.log(5/mp.pi)+mp.loggamma((s+1)/2))*D(s)

def prepare():
    configure(80);co=[0,1,K,-K,-1];controls=[]
    for s in [mp.mpc('.37','2.1'),mp.mpc('.8','86.3')]:
        a=completed(s);bb=completed(1-s);controls.append(str(abs(a-bb)/max(abs(a),abs(bb))))
    sine=[sum(mp.sin(2*mp.pi*r*j/5)*co[j] for j in range(5))/mp.sqrt(5) for r in range(5)]
    # Sum runs over all residues, so this is the odd real Fourier transform / i.
    sine_res=max(abs(sine[r]-co[r]) for r in range(5))
    assert max(map(mp.mpf,controls))<mp.mpf('1e-70') and sine_res<mp.mpf('1e-70')
    zz={}
    for label,seed in [('off_right',mp.mpc('.808517','85.699348')),('off_left',mp.mpc('.191483','85.699348'))]:
        s=seed
        for _ in range(12):s-=D(s)/D(s,1)
        assert abs(D(s))<mp.mpf('1e-65')
        zz[label]=enc(s)
    def hardy(t):return mp.re(completed(mp.mpc('.5',t)))*mp.exp(mp.pi*t/4)
    lo=mp.mpf(76);fl=hardy(lo);found=[]
    for j in range(1,81):
        hi=76+mp.mpf(j)/4;fh=hardy(hi)
        if fl*fh<0:
            t=mp.findroot(hardy,(lo,hi),solver='anderson',tol=mp.mpf('1e-65'))
            if not found or abs(t-found[-1])>mp.mpf('1e-30'):found.append(t)
        lo=hi;fl=fh
    for j,t in enumerate(found,1):zz['line_%02d'%j]=enc(mp.mpc('.5',t))
    save('catalog.json',zz);save('carrier-checks.json',dict(kappa=str(K),coefficient_multiplicativity_defect=str(1+K*K),completion_relative_errors=controls,sine_eigenvector_residual=str(sine_res),catalog_roots=len(zz),line_bracket_window=[76,96],root_residuals={k:str(abs(D(dec(v)))) for k,v in zz.items()}))
    return zz

def catalog():return json.loads(Path('catalog.json').read_text())
def classify(s):
    z=catalog();label=min(z,key=lambda k:abs(s-dec(z[k])));return [label,str(abs(s-dec(z[label])))]
def access(angle,u):return 1-mp.exp(-48*mp.log(2)*u+1j*angle*min(12*u,1))
