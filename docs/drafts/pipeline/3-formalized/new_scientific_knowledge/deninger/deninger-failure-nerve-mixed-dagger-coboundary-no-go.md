# Deninger failure-nerve mixed dagger coboundary no-go

- **ID:** `deninger-failure-nerve-mixed-dagger-coboundary-no-go`
- **Route:** L / finite filtered source mate
- **Stage:** 3-formalized
- **Status:** fully proved on paper; formalized unconditionally in Lean; RH not proved
- **Inputs:** actual normalized failure-nerve transition; unique purified face
  metric; Deninger tensor-square mate curvature

## Result

Fix a prime `p`, depth `m >= 1`, finite face `F` with `p` not in `F`, and
`Re(s)>0`.  Write

\[
 \lambda_{p,m}(s)=p^{-m(s-1/2)},\qquad
 R_{p,m}(s)=\lambda_{p,m}(s)Q_{p,m}(s),
\tag{1}
\]

and equip the face vertices with the forced metric

\[
 h_F=|Q_F|^{-2},\qquad h_{F\cup\{p\}}=h_F|Q_{p,m}|^{-2}.
\tag{2}
\]

### 1. Concrete source reversal and analytic dagger

Algebraic source reversal of the edge and its Hermitian adjoint for `(2)`
have coefficients

\[
 S_{p,m}=R_{p,m}^{-1}
   =Q_{p,m}^{-1}\lambda_{p,m}^{-1},
\tag{3}
\]

and

\[
 A_{p,m}=\frac{h_{F\cup\{p\}}}{h_F}\overline{R_{p,m}}
   =Q_{p,m}^{-1}\overline{\lambda_{p,m}}.
\tag{4}
\]

Indeed, with the convention
`<z,w>_F=h_F conjugate(z) w`, equation `(4)` is characterized by

\[
 \langle R_{p,m}z,w\rangle_{F\cup\{p\}}
 =\langle z,A_{p,m}w\rangle_F.
\tag{5}
\]

The Euler gauge is common to both reverse laws.  Their modular ratio is

\[
 S_{p,m}A_{p,m}^{-1}=|\lambda_{p,m}|^{-2},
\tag{6}
\]

and their linear mate defect is

\[
 \boxed{
 \Delta_{p,m}=S_{p,m}-A_{p,m}
 =Q_{p,m}^{-1}
   (\lambda_{p,m}^{-1}-\overline{\lambda_{p,m}})
 =Q_{p,m}^{-1}\overline{\lambda_{p,m}}
   (|\lambda_{p,m}|^{-2}-1).}
\tag{7}
\]

Since `p^m>1`,

\[
 \Delta_{p,m}=0
 \Longleftrightarrow |\lambda_{p,m}|=1
 \Longleftrightarrow \Re(s)=\frac12.
\tag{8}
\]

This is the concrete finite source transpose--analytic dagger comparison;
neither reverse law is defined from the Xi zero set.

### 2. Mixed Bianchi law and exactness classification

For two composable edge transitions, source reversal and metric dagger are
contravariantly multiplicative.  Hence their difference satisfies the mixed
Leibniz law

\[
 \Delta_{21}=S_1\Delta_2+\Delta_1A_2.
\tag{9}
\]

For two distinct prime edges `p,q`, commutativity of the actual face
transitions gives the square Bianchi identity

\[
 S_p\Delta_q+\Delta_pA_q
 =S_q\Delta_p+\Delta_qA_p.
\tag{10}
\]

More strongly, if the mixed cobar differential on a vertex cochain `H` is

\[
 (\delta_{S,A}H)_e=S_eH_{t(e)}-H_{s(e)}A_e,
\tag{11}
\]

then the constant identity cochain satisfies

\[
 \boxed{\Delta=\delta_{S,A}{\bf1}.}
\tag{12}
\]

Thus the linear source-inverse/analytic-dagger defect is always mixed-Bianchi
closed and mixed-cobar exact, including at every off-critical parameter where
it is nonzero.

### 3. Gamma curvature is a secondary norm transgression

The uniquely purified relative squared gains of source reversal and analytic
dagger are respectively `|lambda|^(-2)` and `|lambda|^2`.  Their difference is

\[
 \boxed{
 |\lambda_{p,m}|^{-2}-|\lambda_{p,m}|^2
 =K_{p^m}(s).}
\tag{13}
\]

At the actual ordered `(2,3)` witness, the companion comparison theorem gives

\[
 b_\Gamma(q)=c_{23}K_6(\rho_q),\qquad c_{23}>0.
\tag{14}
\]

Therefore actual Gamma reporter is a secondary norm transgression of the
linear mixed-exact defect.  Linear cobar exactness does not annihilate this
quadratic reporter.

## Proof

Equation `(3)` follows by inverting `(1)`.  For a one-dimensional weighted
Hermitian edge, the adjoint coefficient is
`(h_target/h_source) conjugate(R)`.  Substitute `(1)` and `(2)`:

\[
 \frac{h_{F\cup\{p\}}}{h_F}\overline{R}
 =|Q|^{-2}\overline{\lambda Q}
 =Q^{-1}\overline\lambda,
\]

which proves `(4)` and `(5)`.  Division of `(3)` by `(4)`, using
`lambda^(-1)/conjugate(lambda)=|lambda|^(-2)`, proves `(6)`.  Subtraction
gives `(7)`.  All factors outside `|lambda|^(-2)-1` are nonzero.  The existing
half-density unitarity theorem then gives `(8)`.

For a composite path, expand

\[
 S_1S_2-A_1A_2
 =S_1(S_2-A_2)+(S_1-A_1)A_2,
\]

which is `(9)`.  Applying it to the two orders around a commuting prime square
proves `(10)`.  Equation `(12)` is immediate from `(11)` with both endpoint
values equal to one.  Finally the two relative reverse gains are the inverse
and direct radial squared gains, so `(13)` is exactly the already identified
Deninger tensor-square curvature; `(14)` is the actual Gamma comparison.

## Hostile audit and frontier consequence

Not new:

- adjoint of a scalar map between weighted Hermitian lines;
- inverse-versus-adjoint mixed Leibniz identity;
- a difference of two representations as a mixed coboundary;
- scalar half-density unitarity criterion.

New Route-L classification is their forced simultaneous realization on the
actual prime-winning Euler gauge metric and its exact connection to the
independently constructed Gamma reporter.  It invalidates a previously live
research shortcut:

> A source Bianchi identity or mixed-cobar null-homotopy of the linear mate
> defect cannot prove RH.  Both hold identically off line.

The missing theorem must instead kill or control the secondary norm
transgression `(13)` after strict singular Cartier transport.  Equivalently,
it needs a Stokes/trace pairing with a boundary condition strong enough to
annihilate `K`, not merely exactness of `Delta`.  Imposing `Delta=0`, declaring
the identity homotopy zero, or defining the pairing from the Xi divisor is
circular.

This theorem does not produce that secondary Stokes law and does not prove
RH.  It removes linear Bianchi/null-homotopy as an eligible hard core and
replaces it by:

`[SECONDARY_CARTIER_NORM_TRANSgression_STOKES]`

> Construct the source-canonical pairing on the conormally renormalized
> singular Cartier completion and prove its boundary term is the actual
> Gamma curvature while its source Stokes term vanishes for structural,
> non-divisor-fitted reasons.

## Formalization target

Lean should formalize unconditionally:

- weighted Hermitian adjunction identity for the actual edge;
- closed formulas `(3)`--`(8)`;
- mixed Leibniz/Bianchi law `(9)`--`(10)`;
- tautological mixed coboundary `(12)`;
- reverse-gain difference `(13)` and actual Gamma specialization `(14)`.

## Lean status

All five formalization targets landed unconditionally in
`formal/GaloisForLFunctions/RHTower/DeningerFailureNerveMixedDaggerCoboundary.lean`.  Axiom audit
for all 16 declarations: `propext, Classical.choice, Quot.sound`.

**The weighted Hermitian adjunction identity and `(3)`--`(8)`.**

- `deningerMixedSourceReversal`, `deningerMixedAdjoint`, `deningerMixedDefect` — the two reverse
  laws `S = (λQ)⁻¹` and `A = Q⁻¹ conj λ` and their difference, defined for arbitrary scalars, so no
  step is fitted to the Xi divisor.
- `deningerMixedSourceReversal_eq` — `(3)`, source reversal in split coordinates.
- `deningerMixedAdjoint_metric_eq` — `(4)`: the ratio of the forced weights times the conjugate
  transition, `‖Q‖⁻² conj(λQ)`, is exactly `Q⁻¹ conj λ`.
- `deningerMixed_adjunction` — `(5)`: with the pairing `⟨z,w⟩_h = h · conj z · w` and the forced
  weights `h_{F∪{p}} = h_F ‖Q‖⁻²`, the transition moves across the two pairings into `A`.
- `deningerMixedModularRatio` — `(6)`: `S A⁻¹ = ‖λ‖⁻²`, the Euler gauge cancelling.
- `deningerMixedDefect_eq` and `deningerMixedDefect_eq_mul_sub_one` — the two closed forms `(7)`,
  the second exhibiting `‖λ‖⁻² − 1` as the only factor that can vanish.
- `deningerMixedDefect_eq_zero_iff_norm_one` — `(8)` abstractly: `Δ = 0` is unimodularity of `λ`;
  `deningerFailureNerveMixedDefect_eq_zero_iff` specializes it to the actual failure-nerve edge for
  a prime power at least two and `Re(s) > 0`, giving `Δ = 0 ↔ Re(s) = 1/2` from the existing
  half-density unitarity theorem `norm_bilateralHalfDensityCharacter_eq_one_iff`.

**The mixed Leibniz/Bianchi law `(9)`--`(10)` and the tautological coboundary `(12)`.**

- `deningerMixedDefect_comp` — `(9)`, `S₁S₂ − A₁A₂ = S₁(S₂−A₂) + (S₁−A₁)A₂`.
- `deningerMixedDefect_bianchi` — `(10)`, the two expansions around a commuting prime square agree.
- `DeningerMixedEdgeSystem` and `DeningerMixedEdgeSystem.cobar` — `(11)`, the mixed cobar
  differential `(δ_{S,A}H)_e = S_e H_{t(e)} − H_{s(e)} A_e` on an arbitrary edge system.
- `DeningerMixedEdgeSystem.cobar_one` and `.defect_mem_range` — `(12)`: the constant identity
  cochain has coboundary exactly `Δ`, so the defect is mixed-cobar exact **at every parameter**,
  including every off-critical one where it is nonzero.  This is the no-go: linear Bianchi
  closedness and linear null-homotopy of `Δ` hold identically on and off the critical line and
  therefore cannot prove RH.

**The reverse-gain difference `(13)` and the Gamma specialization `(14)`.**

- `deningerFailureNerveReverseGainDifference_eq` — `(13)`: the difference of the two uniquely
  purified relative squared gains, `‖λ‖⁻² − ‖λ‖²`, is the tensor-square radial mate curvature
  `deningerTensorSquareRadialMateCurvature (p^m) s`.
- `deningerFailureNerveMixedDefect_eq_zero_iff_reverseGainDifference_eq_zero` — both the linear
  defect and the quadratic reporter cut out the critical line, which is exactly why the identical
  exactness of the linear one carries no information about the quadratic one.
- `deningerFailureNerveGammaSecondaryTransgression` — `(14)`: the actual Gamma boundary defect
  coefficient is `c₂₃` times the tensor-square radial mate curvature at the forced composite degree
  `6`, with `c₂₃ > 0`.  The two inputs are the already-formalized
  `deningerCalderonWittBaseGammaBoundaryDefectCoefficient_eq_tensorSquareMateCurvature` and
  `deningerCalderonWittBaseGammaMateCalibration_pos`.

The successor core `[SECONDARY_CARTIER_NORM_TRANSGRESSION_STOKES]` is not part of this theorem and
stays open.

## Log

- 2026-08-06 — Formalized all five targets unconditionally and wired the module into
  `GaloisForLFunctions.RHTower`; card moves to `3-formalized`.
