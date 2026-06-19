# Experiment for moonshot-2pi-monodromy-frobenius (DeWitt, 2026-06-19)
# Q: is the 2pi in a_inf = (1/2)log(2pi) the LOG-MONODROMY period 2*pi*i,
#    or the archimedean Gamma-factor / zeta-regularization (Stirling/theta) 2pi?
# And: is N(T)'s structure the archimedean Gamma-PHASE winding (Riemann-Siegel theta)?
import mpmath as mp
mp.mp.dps = 40

# E1 -- a_inf provenance: a_inf = -zeta'(0) = (1/2) log(2 pi), REAL (Stirling/zeta-reg),
#       vs the log-monodromy period 2*pi*i (IMAGINARY).
a_inf      = -mp.zeta(0, derivative=1)          # = -zeta'(0)
half_log2pi= mp.log(2*mp.pi)/2
monodromy  = 2*mp.pi*mp.mpc(0,1)                # the deck-transformation period of log
print("E1  a_inf = -zeta'(0)      =", mp.nstr(a_inf, 25))
print("E1  (1/2)log(2pi)          =", mp.nstr(half_log2pi, 25))
print("E1  |a_inf - half_log2pi|  =", mp.nstr(abs(a_inf-half_log2pi), 5))
print("E1  a_inf imag part        =", mp.nstr(mp.im(a_inf), 5), " (0 => REAL Stirling, not the imaginary monodromy)")
print("E1  log-monodromy period   =", mp.nstr(monodromy,10), " (purely imaginary; magnitude 2pi=%s)"%mp.nstr(2*mp.pi,10))
print()

# E2 -- N(T) is the archimedean Gamma-PHASE winding:  N(T) ~ theta(T)/pi + 1 + S(T),
#       theta = Riemann-Siegel phase = arg Gamma(1/4+iT/2) - (T/2)log pi  (the archimedean factor's phase).
#       Compare smooth count theta(T)/pi + 1 to the actual zero count nzeros(T).
print("E2  T      Nsmooth=theta/pi+1     Nactual=nzeros(T)     S(T)=diff")
for T in [50, 100]:
    theta   = mp.siegeltheta(T)
    Nsmooth = theta/mp.pi + 1
    Nact    = mp.nzeros(T)
    print("E2  %-6s %-22s %-18s %s" % (T, mp.nstr(Nsmooth,12), Nact, mp.nstr(Nsmooth-Nact,4)))
print()
print("CONCLUSION: a_inf's 2pi is the REAL archimedean Stirling/zeta-reg constant (im=0), NOT the imaginary")
print("monodromy period 2*pi*i. N(T)'s structure is the archimedean Gamma-PHASE winding (Riemann-Siegel theta),")
print("a degree-1 real-analytic argument-principle count -- not a 2*pi*i deck-transformation Frobenius.")
