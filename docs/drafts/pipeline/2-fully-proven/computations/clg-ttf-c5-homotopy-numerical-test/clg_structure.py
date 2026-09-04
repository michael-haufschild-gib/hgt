"""Verify the structural identities on the completed data:
   P = H + t H_t,  H = t^2 Phi_t^2 K with K = d/dt(Phi_u/(t Phi_t)),
   Theta = t^2 Phi_t^2 [ (15 - W) K + 10 t (Phi_tt/Phi_t) K + 5 t K' ],
 where Phi(u,t) = completed reflected action = q(A(u),t) + dq(u,t)."""
from mpmath import mp, mpf, diff, exp, log, pi, cosh
import clg_compensation as C
mp.dps = 50; C.mp.dps = 50; C.NMAX = 60
def Phi(u, t):
    A = C.Ascale(u); z = cosh(2*t) - 1; lam = 3*A/(A - mpf(3)/2)**2; F = 1 - lam*z
    q = 2*A*z - log(F)
    LPu = C.LPjets(u)[0]; LPp = C.LPjets(u+t)[0]; LPm = C.LPjets(u-t)[0]
    return q + (2*LPu - LPp - LPm)
def completed(u, t):
    D = C.data(u, t)
    Pt = D['a']+D['da']; Ptt = D['b']+D['db']; Pttt = D['c']+D['dc']
    Pu = D['s']+D['ds']; Put = D['m']+D['dm']; Putt = D['n']+D['dn']; q = D['q']+D['dq']
    H = Pt*(t*Put) - (Pt + t*Ptt)*Pu
    P = Pt*(t*Put + t**2*Putt) - (Pt + 3*t*Ptt + t**2*Pttt)*Pu
    W = 14 + 10*t*Pt + 8*t*Pt/(exp(q) - 1)
    Theta = 5*P - W*H
    return dict(Pt=Pt, Ptt=Ptt, Pttt=Pttt, Pu=Pu, Put=Put, Putt=Putt, q=q, H=H, P=P, W=W, Theta=Theta)
for (u, t) in ((mpf("0.5"), mpf("0.2")), (mpf("0.4"), mpf("0.39")), (mpf("1.2"), mpf("0.05"))):
    c = completed(u, t)
    # numerical derivatives of Phi
    Pt_n = diff(lambda s: Phi(u, s), t); Ptt_n = diff(lambda s: Phi(u, s), t, 2); Pttt_n = diff(lambda s: Phi(u, s), t, 3)
    Pu_n = diff(lambda v: Phi(v, t), u); Put_n = diff(lambda v: diff(lambda s: Phi(v, s), t), u); Putt_n = diff(lambda v: diff(lambda s: Phi(v, s), t, 2), u)
    print("u,t=", u, t, "jets vs derivs:", [mp.nstr(c['Pt']-Pt_n,3), mp.nstr(c['Ptt']-Ptt_n,3), mp.nstr(c['Pttt']-Pttt_n,3), mp.nstr(c['Pu']-Pu_n,3), mp.nstr(c['Put']-Put_n,3), mp.nstr(c['Putt']-Putt_n,3)], " q vs Phi:", mp.nstr(c['q']-Phi(u,t),3))
    Hfun = lambda s: completed(u, s)['H']
    Ht = diff(Hfun, t)
    print("   P - (H + t H_t) =", mp.nstr(c['P'] - (c['H'] + t*Ht), 5), "  H=", mp.nstr(c['H'],6), " P=", mp.nstr(c['P'],6))
    Kfun = lambda s: diff(lambda r: completed(u, r)['Pu']/(r*completed(u, r)['Pt']), s)
    K = Kfun(t); Kp = diff(Kfun, t)
    print("   H - t^2 Pt^2 K =", mp.nstr(c['H'] - t**2*c['Pt']**2*K, 5))
    rhs = t**2*c['Pt']**2*((15 - c['W'])*K + 10*t*(c['Ptt']/c['Pt'])*K + 5*t*Kp)
    print("   Theta =", mp.nstr(c['Theta'],8), " ODE form =", mp.nstr(rhs,8), " K=", mp.nstr(K,5), " W=", mp.nstr(c['W'],6))
    # the scalar criterion:  W > 15 + 10 t (log Phi_t)' + 5 t (log kappa)',  kappa = -K
    crit = 15 + 10*t*c['Ptt']/c['Pt'] + 5*t*Kp/K
    print("   criterion: W=%s vs 15+10t(logPhi_t)'+5t(logK)'=%s" % (mp.nstr(c['W'],8), mp.nstr(crit,8)))
