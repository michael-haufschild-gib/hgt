from mpmath import mp, mpf, diff, exp
import clg_compensation as C
mp.dps = 50; C.mp.dps = 50; C.NMAX = 60
# (1) cumulant jets vs numerical derivatives of LP
for x in (mpf("0.1"), mpf("0.5"), mpf("1.0")):
    LP = lambda y: C.LPjets(y)[0]
    J = C.LPjets(x)
    print("x=%s  J1 %s vs %s | J2 %s vs %s | J3 %s vs %s" % (x, mp.nstr(J[1],12), mp.nstr(diff(LP, x, 1),12), mp.nstr(J[2],12), mp.nstr(diff(LP, x, 2),12), mp.nstr(J[3],12), mp.nstr(diff(LP, x, 3),12)))
# (2) affine layer: derivatives in l
def comp_all(u, t, l):
    D = C.data(u, t); c3, c0, act, vC = C.comp3(D, l); return c0, c3
for (u, t) in ((mpf("0.3"), mpf("0.1")), (mpf("1.0"), mpf("0.5"))):
    D = C.data(u, t)
    f0 = lambda l: C.comp3(D, l)[1]
    l = mpf("0.4")
    print("u,t=", u, t, " comp'''(num) =", mp.nstr(diff(f0, l, 3), 12), " compensationThree =", mp.nstr(C.comp3(D, l)[0], 12))
    # ingredient signs
    t_ = t
    print("   dq=%s da=%s db=%s dm=%s ds=%s" % tuple(mp.nstr(D[k], 8) for k in ("dq","da","db","dm","ds")))
    vC2 = 2*(D['da']*(t_*D['dm']) - (D['da'] + t_*D['db'])*D['ds'])
    print("   vC2 =", mp.nstr(vC2, 10), "  pieces: da*t*dm =", mp.nstr(D['da']*t_*D['dm'], 8), " -(da+t db)*ds =", mp.nstr(-(D['da']+t_*D['db'])*D['ds'], 8))
