"""Phase 1+2 of the dtG <= 0 attack: identity check, dense sign map, required-gamma margins,
Riccati chamber map, atom-vs-full sizing."""
import json, sys, time
from multiprocessing import Pool
import mpmath as mp
sys.path.insert(0, "/root/precert")
import theta_common as tc

NPROC = 110
DPS = 40

def jets(u, t):
    """q, q1, q2, q3 and r, alpha, beta, gamma for the literal theta action."""
    u = mp.mpf(u); t = mp.mpf(t)
    pl = tc.phi_derivs(u + t, order=3)
    mi = tc.phi_derivs(u - t, order=3)
    ce = tc.phi_derivs(u, order=0)
    P0, P1, P2, P3 = pl
    M0, M1, M2, M3 = mi
    lp1 = P1/P0; lp2 = P2/P0 - lp1**2; lp3 = P3/P0 - 3*lp1*(P2/P0) + 2*lp1**3
    lm1 = M1/M0; lm2 = M2/M0 - lm1**2; lm3 = M3/M0 - 3*lm1*(M2/M0) + 2*lm1**3
    q  = 2*mp.log(ce[0]) - mp.log(P0) - mp.log(M0)
    q1 = lm1 - lp1
    q2 = -lp2 - lm2
    q3 = lm3 - lp3
    r = mp.expm1(q)
    return q, q1, q2, q3, r, t*q1, t**2*q2, t**3*q3

def point(args):
    u, t = args
    mp.mp.dps = DPS
    try:
        q, q1, q2, q3, r, al, be, ga = jets(u, t)
        N = 9*r*al + 5*r*al**2 + 4*al**2
        D = 24*r**2 + 5*r*be
        P = al*(1+r)
        U1 = 9*P*al + 5*P*al**2 + (9*r + 10*r*al + 8*al)*(al+be)
        U2 = 48*r*P + 5*P*be + 10*r*be
        tW = U1*D - N*(U2 + 5*r*ga)          # sign of dG/dt
        Greq = (U1*D - N*U2)/(5*r*N)          # need gamma >= Greq
        M = 2*q1*q2 - q3                      # Riccati margin
        return {"u": float(u), "t": float(t),
                "tW_sign": int(mp.sign(tW)),
                "tW_log10": tc.log10_or_none(tW),
                "gap": float(ga - Greq) if abs(ga - Greq) < 1e300 else None,
                "gap_rel": float((ga - Greq)/(abs(Greq)+abs(ga)+1e-50)) if abs(ga)<1e300 and abs(Greq)<1e300 else None,
                "gamma": float(ga) if abs(ga) < 1e300 else None,
                "greq": float(Greq) if abs(Greq) < 1e300 else None,
                "riccati_sign": int(mp.sign(M)),
                "G": float(N/D)}
    except Exception as e:
        return {"u": float(u), "t": float(t), "error": repr(e)}

def main():
    t0 = time.time()
    # identity check: tW vs numerical derivative of G at random points
    mp.mp.dps = DPS
    import random
    rng = random.Random(7)
    print("== identity check tW vs finite-difference dG/dt ==")
    for _ in range(5):
        u = 3*rng.random(); t = 0.05 + 2*rng.random()
        q, q1, q2, q3, r, al, be, ga = jets(u, t)
        N = 9*r*al + 5*r*al**2 + 4*al**2
        D = 24*r**2 + 5*r*be
        P = al*(1+r)
        U1 = 9*P*al + 5*P*al**2 + (9*r+10*r*al+8*al)*(al+be)
        U2 = 48*r*P + 5*P*be + 10*r*be
        tW = U1*D - N*(U2 + 5*r*ga)
        def Gf(tt):
            _,_,_,_,rr,aa,bb,_ = jets(u, tt)
            return (9*rr*aa + 5*rr*aa**2 + 4*aa**2)/(24*rr**2 + 5*rr*bb)
        dG = mp.diff(Gf, mp.mpf(t))
        pred = tW/(mp.mpf(t)*D**2)
        print(f"  u={u:.3f} t={t:.3f} rel err = {mp.nstr((dG-pred)/(abs(dG)+1e-40), 5)}")
    # gamma via q3: verify phi_derivs order-3 once
    x0 = mp.mpf('0.83')
    v = tc.phi_derivs(x0, 3)
    nd3 = mp.diff(lambda x: tc.phi_derivs(x, 0)[0], x0, 3)
    print("phi''' check:", mp.nstr(v[3]-nd3, 5))

    us = [mp.mpf(i)/20 for i in range(0, 121)]
    ts = [mp.mpf(10) ** (mp.mpf(-3) + mp.mpf(i)*(mp.log10(mp.mpf(6))+3)/299) for i in range(300)]
    tasks = [(float(u), float(t)) for u in us for t in ts]
    posW = []; worst_gap = None; ric_neg = []
    out = open("/root/precert/dtg_map.jsonl", "w")
    with Pool(NPROC) as pool:
        for i, rec in enumerate(pool.imap_unordered(point, tasks, chunksize=64)):
            out.write(json.dumps(rec) + "\n")
            if "error" in rec: continue
            if rec["tW_sign"] > 0:
                posW.append(rec)
            if rec["riccati_sign"] < 0:
                ric_neg.append(rec)
            if rec["gap_rel"] is not None and (worst_gap is None or rec["gap_rel"] < worst_gap["gap_rel"]):
                worst_gap = rec
            if i % 8000 == 0:
                print(f"[{time.time()-t0:.0f}s] {i}/{len(tasks)} posW={len(posW)} ricNeg={len(ric_neg)}", flush=True)
    out.close()
    print("DONE", time.time()-t0)
    print("dG/dt > 0 count:", len(posW))
    for r in posW[:10]: print("  POS:", json.dumps(r))
    print("Riccati margin < 0 count:", len(ric_neg))
    for r in ric_neg[:6]: print("  RICNEG:", {k: r[k] for k in ("u","t")})
    print("worst gamma-gap rel:", json.dumps(worst_gap))
    json.dump({"posW": posW[:50], "ric_neg_count": len(ric_neg),
               "ric_neg_examples": [{k: r[k] for k in ("u","t")} for r in ric_neg[:20]],
               "worst_gap": worst_gap}, open("/root/precert/dtg_summary.json","w"), indent=1)

if __name__ == "__main__":
    main()
