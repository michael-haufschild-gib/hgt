# CLG/TTF all-order center integration and local Schur compensation

- **Stage:** 3-formalized
- **Scope:** Exact all-order source integration; an explicit zero-integral correction; unconditional repair of the native rank-six seam obstruction on an open center interval.
- **Full chain:** Literal theta source → all signed center-mixed jet Hankel sections nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.
- **Boundary:** Neither the global rank-six sign nor the complete positive hierarchy is proved.

## Exact all-order integration

Write `Φ` for the literal all-integer theta source, `j_n(x)=D_t^n[Φ(x+t)Φ(x−t)]|_(t=0)`, and `w_a(r)=r sinh(ar)`. At every `0≤a<1/2`,

`f_a^(n)(0) = ∫_(r>0) w_a(r) j_n(r/2) dr`.

The proof uses the corpus's derivative-product family. Its derivative increments the first index minus the second. The finite alternating recurrence commutes with integration at every order; integrability of every term is already proved from the literal source. Thus every finite Fourier-signed native Hankel quadratic form integrates to the corresponding actual center-mixed form. The complete integrated native cone is exactly RH, by the existing signed-jet completeness theorem. No new regularity, determinacy, or Fourier-incidence premise occurs in this equivalence.

## Exact compensation and positive local survivor

Set `A=−j₂`, `B=j₄`, `C=−j₆`, `D=j₈`, `E=−j₁₀`. Let `Δ=AC−B²>0` and `H=ACE−AD²−B²E+2BCD−C³`. The corpus proves `H(0)<0`.

Define the literal flux

`F_a(r)=r² sinh(ar) Φ(r/2)²`.

For `|a|<1`, `F_a` is Schwartz: it is a polynomial times the difference of squares of the two dilated tilted Schwartz sources. Its derivative is integrable, `F_a(0)=0`, and `F_a(r)→0` as `r→∞`. The half-line fundamental theorem of calculus therefore proves

`∫_(r>0) F_a'(r) dr = 0`.

For `a,r≥0`, the exact derivative and `ar cosh(ar)≥sinh(ar)` give

`F_a'(r) ≥ w_a(r) G(r/2)`, where `G(x)=3Φ(x)²+2xΦ(x)Φ'(x)`.

Replace only the last entry of the weighted odd rank-three block by `w_a(r)E(r/2)+K F_a'(r)`. All its entries are integrable at critical apertures. Its integrated last entry is exactly `−f_a^(10)(0)`, for every real `K`. For `K≥0`, its determinant satisfies

`det(corrected block) ≥ w_a(r)³ [H(r/2)+K Δ(r/2)G(r/2)]`.

The source-selected constant

`K_* = −H(0)/(Δ(0)Φ(0)²) > 0`

is independent of aperture. At the seam the bracket equals `−2H(0)>0`. Continuity supplies one nontrivial center interval on which the corrected determinant is strictly positive for every `a>0`. This repairs the known local obstruction while preserving the actual integrated moment; it does not determine the contribution of the remaining centers.

## Precisely open comparison

The explicit target is

`H(x)+K_* Δ(x)G(x)>0` for every `x>0`.

Lean proves that a global positive comparison of this form, for any fixed `K≥0`, would give strict positivity of the actual mixed odd rank-three determinant through order ten. The proof uses the existing strict leading plane, positive integrated first entry, and division-free rank-three mixing theorem. The global comparison itself remains unproved. Even its proof would close only the next finite rank; RH still requires every order.

## Lean landing and verification

- `HTGeometry/AlternatingPairJetIntegral.lean`: finite recurrence, derivative identity, integrability, and exact integral transport.
- `RHTower/ThetaCusp/ThetaCuspCenterMixedAllOrderIntegration.lean`: literal all-order source transport and `thetaCuspIntegratedNativeSignedCone_iff_riemannHypothesis`.
- `RHTower/ThetaCusp/ThetaCuspCenterCompensationFlux.lean`: exact zero integral, derivative bound, and preservation of every integrated quadratic form.
- `RHTower/ThetaCusp/ThetaCuspNativeOddSchurCompensation.lean`: explicit source coefficient, exact positive seam margin, uniform local repair, unchanged tenth moment, and the conditional global-comparison receiver.

All four modules are checked individually and wired into their umbrellas. Eight new capstones report only `propext`, `Classical.choice`, and `Quot.sound`; no axioms were added. Formal lint passes, and all 39 new public declaration names are unique outside these modules. No umbrella or full build was run. Exploratory numerical signs are not used in any Lean proof.
