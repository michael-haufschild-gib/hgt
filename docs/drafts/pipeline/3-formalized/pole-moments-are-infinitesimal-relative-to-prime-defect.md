# Pole moments are infinitesimal relative to the prime defect

- **ID:** pole-moments-are-infinitesimal-relative-to-prime-defect
- **Stage:** 3-formalized
- **Type:** THEOREM

## Theorem

For `N≥3`, `0<w≤1`, `wN≤K`, compact continuous `g` supported in `[0,w]`,
let `G=∫g²`, `S=Σx_n²`, `D=D_N(x)`, and
`P=(∫f_x e^(-u/2))(∫f_x e^(u/2))`.
For every `ε>0`,

`2|P| ≤ G[εD+(ε+2 C_H e K²/ε)S]`,

where `C_H=48(log 4+4)²+51` is the established multiplicative Hardy constant.

## Source mechanism

The proof of `two_mul_abs_poleMoments_le_defect` already derives
`P²≤2 C_H e^w(wN)² G² S(D+S)` before weakening the bound.
Its ingredients are the exact atomic pole rows, harmonic Cauchy–Schwarz,
the multiplicative Hardy inequality `sq_vRow_le`, and compact-profile
Cauchy–Schwarz. Retaining the square and applying weighted Young gives the
target. No signed pole contribution is discarded.

## Signed arithmetic consequence

With `E_ar=log(N)S+(2P−primeSum(f_x))/G`, the directed non-ratio rows and
the sharp prime counterterm give, for every `ε>0`, eventually uniformly,

`E_ar ≥ (1−ε)D_N − A(K,ε)S`,

where `A(K,ε)=ε/3+nonRatioRelativeCost(K,ε/3)+poleRelativeCost(K,ε/3)−γ`.
Each of the three source estimates spends `ε/3` of the defect.
`CriticalArithmeticCorrelationTheory/TheSignedArithmeticSourceKeepsAlmostAllTheDefect.lean`
proves `eventually_overlapArithmeticEnergy_ge_defect`. Direct no-olean
audit passed with only the three standard logical axioms; CACT umbrella wired.
A separated low block, spline Gamma reserve, ordered-support interaction,
and logarithmic-tail payment supply the proposed complete-Weil defect
reserve. Full positivity and spectral identification remain separate.

## Lean status

`ArithmeticLorentzianGeometry/ThePoleIsInfinitesimalRelativeToThePrimeDefect.lean`
proves `sq_poleMoments_le_defect`, `two_mul_abs_poleMoments_le_young`, and
`two_mul_abs_poleMoments_le_relative_defect`. Direct no-olean check passed;
main declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
ALG umbrella import added. Counted together with the signed arithmetic
source consequence as one contribution; no separate credit for Young algebra.
