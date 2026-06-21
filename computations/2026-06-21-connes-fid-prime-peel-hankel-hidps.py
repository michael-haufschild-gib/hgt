import mpmath as mp
def run(dps, MAXSIZE):
    mp.mp.dps = dps
    def seq_raw(n): return mp.zeta(2*n+3)
    def seq_peel(peeled, q):
        def f(n):
            s=2*n+3; v=mp.zeta(s)-mp.mpf(1)
            for p in peeled: v-=mp.power(p,-s)
            return v*mp.power(q,s)
        return f
    bases={"raw":seq_raw, "peel{}sc2":seq_peel([],2), "peel{2}sc3":seq_peel([2],3)}
    out={}
    for name,f in bases.items():
        b=[f(n) for n in range(0,2*MAXSIZE)]
        firstneg=None; mind=None
        for m in range(1,MAXSIZE+1):
            H=mp.matrix(m,m)
            for i in range(m):
                for j in range(m): H[i,j]=b[i+j]
            d=mp.det(H)
            if mind is None or d<mind: mind=d
            if d<=0 and firstneg is None: firstneg=(m,d)
        out[name]=(firstneg, mind)
    return out
for dps,MS in [(50,20),(150,24),(300,28)]:
    r=run(dps,MS)
    print(f"dps={dps}, to size {MS}:")
    for name,(fn,mind) in r.items():
        tag=f"first non-PSD size {fn[0]} (det {mp.nstr(fn[1],3)})" if fn else f"PSD through {MS}; min leading-det {mp.nstr(mind,3)}"
        print(f"   {name:<10} {tag}")
