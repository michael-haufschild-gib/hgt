import json
import multiprocessing as mp
import time
from pathlib import Path
import sympy as sp
import mpmath as m
from symbolic import field,local_correction,r,y,B,jets,S,Sx,Sy

t,x=sp.symbols('t x')

def direct_jets(A,rate,rad):
    lam=(rate+1)*(rate+2)
    vals=[1,2,3,5,7,11,13]
    ss,sx,sy,sxx,sxy,sxxx,sxxy=map(sp.Integer,vals)
    syy=lam*ss-sxx;sxyy=lam*sx-sxxx;syyy=lam*sy-2*lam*ss-sxxy
    dy=y-1
    source=ss+sx*x+sy*dy+sxx*x*x/2+sxy*x*dy+syy*dy*dy/2+sxxx*x**3/6+sxxy*x*x*dy/2+sxyy*x*dy*dy/2+syyy*dy**3/6
    profile=sp.exp(rate*t)*((1-r**-2)/(1-rad**-2))**(rate/2)
    A=A.subs({B:profile,S:source,Sx:sp.diff(source,x),Sy:sp.diff(source,y)},simultaneous=True)
    point={t:0,x:0,y:1,r:rad}
    coord=[t,r,x,y]
    def at(C):return [str(sp.simplify(v.subs(point))) for v in C]
    first=[A.diff(q) for q in coord]
    return dict(g=at(A),d=[at(C) for C in first],
                dd=[[at(first[i].diff(coord[k])) for i in range(4)] for k in range(4)])

def number(s):
    if '/' in s:
        a,b=s.split('/');return m.mpf(a)/m.mpf(b)
    return m.mpf(s)

def matrix(values):
    vals=list(map(number,values))
    return m.matrix([vals[4*i:4*i+4] for i in range(4)])

def tensor(j):
    return (matrix(j['g']),[matrix(row) for row in j['d']],
            [[matrix(row) for row in rows] for rows in j['dd']])

def combine(g,p,q,k,e,z):
    return g+e*(p+z*q)+e*e*k

def direct_value(data,e,z,readers):
    gj,pj,qj,kj=data
    g=combine(gj[0],pj[0],qj[0],kj[0],e,z)
    dg=[combine(gj[1][k],pj[1][k],qj[1][k],kj[1][k],e,z) for k in range(4)]
    ddg=[[combine(gj[2][k][j],pj[2][k][j],qj[2][k][j],kj[2][k][j],e,z) for j in range(4)] for k in range(4)]
    inv=g**-1
    invd=[-inv*D*inv for D in dg]
    C=[[[dg[i][u,j]+dg[j][u,i]-dg[u][i,j] for j in range(4)] for i in range(4)] for u in range(4)]
    con=[[[sum(inv[u,a]*C[a][i][j] for a in range(4))/2 for j in range(4)] for i in range(4)] for u in range(4)]
    def dc(k,u,i,j):
        return sum(invd[k][u,a]*C[a][i][j]+inv[u,a]*(ddg[k][i][a,j]+ddg[k][j][a,i]-ddg[k][a][i,j]) for a in range(4))/2
    Ric=m.matrix(4)
    for i in range(4):
        for j in range(4):
            Ric[i,j]=sum(dc(u,u,j,i)-dc(j,u,u,i)+sum(con[u][u][a]*con[a][j][i]-con[u][j][a]*con[a][u][i] for a in range(4)) for u in range(4))
    trace=sum(inv[i,j]*Ric[j,i] for i in range(4) for j in range(4))
    E=Ric-(trace/2+3)*g
    volume=m.sqrt(m.det(g)/m.det(gj[0]))
    out=[]
    for reader in readers:
        weight=inv*reader*inv.T
        out.append(volume*sum(weight[i,j]*E[i,j] for i in range(4) for j in range(4)))
    return out

def task(args):
    case,dps=args;begin=time.monotonic();m.mp.dps=dps
    data=[tensor(case[key]) for key in ['G','Pjet','Qjet','K']]
    readers=[matrix(v) for v in case['readers']]
    radius=m.mpf(10)**(-(dps//10));coeff=[m.mpc(0) for _ in readers]
    for i in range(8):
        e=radius*m.exp(2*m.pi*m.j*i/8)
        for j in range(4):
            z=radius*m.exp(2*m.pi*m.j*j/4)
            values=direct_value(data,e,z,readers)
            for k,value in enumerate(values):coeff[k]+=value/e**3/z/32
    expected=[number(v) for v in case['expected']]
    errors=[abs(a-b)/max(1,abs(b)) for a,b in zip(coeff,expected)]
    return dict(point=case['point'],P=case['P'],Q=case['Q'],corrected=case['corrected'],dps=dps,
                radius=str(radius),readers=case['reader_names'],expected=case['expected'],
                values=[[m.nstr(v.real,dps),m.nstr(v.imag,dps)] for v in coeff],
                relative_errors=[m.nstr(v,30) for v in errors],
                passed=all(v< m.mpf(10)**(-m.mpf('.4')*dps) for v in errors),seconds=time.monotonic()-begin)

if __name__=='__main__':
    start=time.monotonic();cases=[]
    reference=[json.loads(l) for l in Path('reference.jsonl').read_text().splitlines()]
    for point,(rate,rad) in enumerate([(sp.Rational(-5,4),sp.Integer(2)),(sp.Rational(-2,3),sp.Rational(3,2))]):
        f=r*r-1;G=sp.diag(-f,1/f,r*r/y**2,r*r/y**2)
        Gjet=direct_jets(G,rate,rad)
        for p,q in [((1,0),(0,1)),((1,1),(1,0))]:
            Pjet=direct_jets(field(rate,*p),rate,rad)
            Qjet=direct_jets(field(-3-rate,*q),-3-rate,rad)
            for corrected in [0,1]:
                record=next(a for a in reference if a['point']==point and a['P']==list(p) and a['Q']==list(q) and a['corrected']==corrected)
                names=[];readers=[]
                for name,rrate in [('same',rate),('opposite',-3-rate)]:
                    for pol,amps in [('S',(1,0)),('V',(0,1))]:
                        names.append(name+'_'+pol)
                        M=field(rrate,*amps).subs({r:rad,y:1,B:1,S:2,Sx:3,Sy:-2})
                        readers.append([str(v) for v in M])
                cases.append(dict(point=point,P=p,Q=q,corrected=corrected,G=Gjet,Pjet=Pjet,Qjet=Qjet,
                                  K=direct_jets(corrected*local_correction(rate,*p),rate,rad),
                                  reader_names=names,readers=readers,expected=[a['total'] for a in record['rows']]))
    Path('explicit-coordinate-jets.json').write_text(json.dumps(cases)+'\n')
    print('coordinate jets constructed',time.monotonic()-start,flush=True)
    jobs=[(case,dps) for case in cases for dps in [50,100,160]]
    with open('validation.jsonl','w',buffering=1) as out,mp.Pool(14) as pool:
        for batch in [jobs[:1],jobs[1:]]:
            for row in pool.imap_unordered(task,batch):
                out.write(json.dumps(row)+'\n')
            print('stage completed',time.monotonic()-start,flush=True)
