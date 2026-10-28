# Local capture of actual Ramanujan families

## Statement

Let v_m(n)=c_m(n)/sqrt(phi(m)n), let S be a finite set of positive conductors,
and write F_a(n)=sum_(m in S) a_m v_m(n). Set

D_S=1+2 sum_(m in S) m^2,
K_(S,L)=H_L sum_(m in S) phi(m).

For every coefficient vector and every natural L,N,

sum_(n<=L) F_a(n)^2 <= K_(S,L) sum_(m in S) a_m^2,

(log N-D_S) sum_(n<=L) F_a(n)^2 <= K_(S,L) sum_(n<=N) F_a(n)^2.

When log N>D_S, division gives the local/global ratio K_(S,L)/(log N-D_S).
For fixed S,L and every epsilon>0, this ratio is at most epsilon eventually,
uniformly over all coefficients.

## Proof

The normalized Ramanujan amplitude is at most sqrt(phi(m)), hence
v_m(n)^2<=phi(m)/n. Rowwise Cauchy–Schwarz gives the local bound. The global
Gram estimate gives (log N-D_S) sum a_m^2<=sum_(n<=N) F_a(n)^2.
Multiplication combines these bounds when log N-D_S is nonnegative; otherwise
the cross-multiplied statement follows directly from nonnegative masses.
Logarithmic divergence supplies the uniform eventual statement.

## Lean

Module:
formal/GaloisForLFunctions/SignedArithmeticHodgeTheory/RamanujanFamiliesHaveAnExplicitLocalCaptureCost.lean

Declarations:

- ramanujanPoleProfile_family_local_mass_le
- ramanujanPoleProfile_family_capture_bound
- ramanujanPoleProfile_family_local_fraction_le
- eventually_ramanujanPoleProfile_family_local_mass_le

The final individual no-olean check passes. All four capstones depend only on
propext, Classical.choice and Quot.sound. The module is wired into its umbrella.

## Scope

These are literal prime-matrix coordinate bounds. They supply a quantitative
readout law and a local escape boundary for fixed modal spans. They do not
identify the integer-coordinate norm with the complete source graph or determine
the continuous Gamma term, polar coordinates or full Weil sign.
