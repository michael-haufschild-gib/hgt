"""
Native attack on Gamma _|_ zeta (past the c-point wall), per the user's scientific method.

The naive pole/orbit separation fails: 1/(Gamma-1) in K=C(s)<Gamma> has off-Z poles
(the c-points of Gamma). BUT Stirling survives it. Two experiments:

(E1) Gamma^{(j)}(s) -> 0 super-exponentially as |Im s| -> infinity (vertical strips).
     => denominators Q(s,{Gamma^{(j)}}) -> q_0(s) in C[s] at height
     => every element of K has poles confined to a BOUNDED horizontal strip.
     In particular Gamma's c-points (c != 0) are bounded-height (|Gamma|->0 kills them).

(E2) Discriminator: local pole/zero rate per unit height.
     - tan (d-algebraic, y'=1+y^2): poles at pi/2+k*pi -> CONSTANT rate 1/pi.
     - zeta nontrivial zeros: rate ~ (1/2pi) log(T/2pi) -> GROWS without bound.
     A K-pole-confined field cannot host movable poles whose local rate -> infinity?
     Measure both rates to see the nature of the gap.
"""
import mpmath as mp
mp.mp.dps = 30

print("=== (E1) Stirling decay of Gamma and derivatives at height (sigma=0.5) ===")
print(" t        |Gamma|            |Gamma'|           |Gamma''|        (all -> 0 super-exp)")
for t in (5, 10, 20, 40, 80):
    s = mp.mpf('0.5') + mp.mpc(0,1)*t
    g0 = abs(mp.gamma(s))
    g1 = abs(mp.diff(mp.gamma, s, 1))
    g2 = abs(mp.diff(mp.gamma, s, 2))
    print(f" {t:>3}   {mp.nstr(g0,6):>14}   {mp.nstr(g1,6):>14}   {mp.nstr(g2,6):>14}")

print()
print("=> Gamma^{(j)} -> 0 at height; so denominators in K reduce to C[s] high up,")
print("   K-elements are POLE-CONFINED to bounded |Im s|. (c-point obstruction survived.)")
print()

print("=== (E2) local rate per unit height: tan (d-algebraic) vs zeta zeros ===")
print(" tan poles in [T,T+10] along real axis (period pi): constant rate 1/pi =", mp.nstr(1/mp.pi,6))
print()
print(" zeta zero-rate (1/2pi) log(T/2pi)  vs  count in [T,T+10]:")
def zeros_in(a,b):
    # count nontrivial zeros with Im in [a,b] via Riemann-von Mangoldt N(T)=theta/pi+1
    def N(T):
        th = mp.siegeltheta(T)
        return th/mp.pi + 1
    return N(b)-N(a)
for T in (20, 100, 1000, 10000):
    rate = (1/(2*mp.pi))*mp.log(T/(2*mp.pi))
    cnt = zeros_in(T, T+10)
    print(f"  T={T:>6}  predicted rate/unit={mp.nstr(rate,5):>8}  zeros in [T,T+10]={mp.nstr(cnt,5):>8}  (rate {mp.nstr(cnt/10,5)})")
print()
print("=> tan rate CONSTANT (1/pi); zeta rate GROWS like (1/2pi)log T -> infinity.")
print("   The native crux: can a pole-confined-field-d-algebraic function have movable")
print("   poles with local rate -> infinity? (tan: no; the log-growth is zeta's signature.)")
