# Astra top three questions: theta successors, macroscopic overlap, coalescent surplus

- **ID:** astra-top-three-answers
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** ../../../reports/review-2910/astra.md, "The top three research questions"
- **Statement:** Answer Q1 (signed theta successors `I_n(a)`), Q2 (complete Weil form at overlap
  `3/2`), Q3 (signed coalescent surplus `≤ 1/18`) with unconditional Lean theorems.

## Q1 — formalized

- `RHTower/ThetaCusp/ThetaCuspCenterTailRepresentation.lean`:
  `thetaCuspCenterMixedSignedJet_eq_integral_tail` (every order, every `0≤a<1/2`:
  `s_k(a)=∫_{r>0}(sinh(ar)+ar cosh(ar))U_k(r)dr`, `U_k(r)=∫_{s>r}h_k(s/2)ds`) and
  `thetaCuspCenterMixedSignedHankel_posSemidef_of_tail` (nonnegative `a`-free tail forms at
  every positive center give the size-`N` signed section at every critical aperture).
- `RHTower/ThetaCusp/ThetaCuspCenterTailSeamGram.lean`: `thetaCuspNativeTailHankelForm_zero_eq`
  (seam tail form `=∫_ℝ|Σ_j v_j(2i)^jΦ^(j)|²`, every order) and `_zero_nonneg`.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only. Wired into `RHTower.lean`.

Exact structure exposed: the fibre form is a perfect square plus a null Lagrangian,
`J_v=|G_v|²+B_v'` with `G_v=Σ_j v_j(2i)^jΦ^(j)`; hence the tail form at center `x=r/2` equals
`2∫_x^∞|G_v|²-2B_v(x)`, bulk `L²` mass beyond the center minus a local boundary flux. The
rank-`n` successor sign is exactly the statement that this mass dominates that flux at every
center.

## Q1 — mechanism under test

Notation: `N_n(x)` the native signed fibre Hankel matrix at center `x`, `w_a(r)=r sinh(ar)`,
`H_{a,n}=∫_0^∞ w_a(r) N_n(r/2) dr`.

Center-tail identity (exact, every order, every `a ≥ 0`): with `U_n(r)=∫_r^∞ N_n(s/2) ds`,
`H_{a,n}=∫_0^∞ (sinh(ar)+ar cosh(ar)) U_n(r) dr`, and `U_n(0)` is the Gram matrix of
`(2i)^j Φ^(j)` in `L²(ℝ)`, positive at every order. Hence `U_n ⪰ 0` on `[0,∞)` gives
`H_{a,n} ⪰ 0` for all `a>0` at once; the seam negativity of `N_n` is paid by bulk mass.

Guidance numerics (not a proof input): at rank eight the odd fibre block is negative only on
`x≲0.13`, positive beyond; `U_8`, the `s`- and `s²`-weighted tails are positive at every sampled
`r` with margin.

Big-picture constraint: the `a`-free tail conditions at every order are at least RH strength
(`U_n(0)` all orders is Plancherel; `r²`-tail at `r=0` all orders is the first Laguerre
inequality for Ξ; large-center tails inherit the Wigner negativity of the fibre). Fixed order
`n` sees zeros up to height about `n`.

## Q1 — which tail certificates can reach all orders (guidance numerics, not proofs)

Spectral form of the tail with center weight `s^p`:
`𝒯^p_r(τ)=∫∫_{u+v≥r}(u+v)^p Φ(u)Φ(v) e^{iτ(u-v)}`. Then
`d/dr 𝒯^0_r(τ)|_{r=0}=-∫Φ(u)²e^{2iτu}du` and `𝒯^0_0=½|Φ̂|²`, which vanishes at the zeros of
`Φ̂`. At the first zero `FT[Φ_cl²](2γ₁)=+0.00289>0`, so the weight-one tail is negative for
small `r` there: the `U` certificate cannot hold at all orders (finite rank cannot localize the
dip, which is why ranks up to 21 sample positive). Weights `s` and `s²` vanish at the seam and
survive this test: at `r=0` the `s`-tail is the weighted Turán integral
`∫_0^∞(Ξ(t)²-Ξ(t+α)Ξ(t-α))/α²dα`, positive at the first five zeros; on the grid
`τ≤60`, `y₀≤1.2` no negative `s`- or `s²`-tail was found, while the weight-one tail is negative
near `τ≈44`. Formalized certificates should therefore use weights vanishing at the seam.

## Q1 — rank eight (`I_7`) via the odd moment tail

Formalized reduction (`RHTower/ThetaCusp/ThetaCuspOddFourMomentTail.lean`,
`thetaCuspNativeSuccessorIntegral_seven_nonneg_of_oddTail`): if the `a`-free odd tail form
`Σ v_i v_j V_{2(i+j)+2}(r) ≥ 0` for all `r>0`, then `I_7(a) ≥ 0` for every `0<a<1/2`
(parity split: even block from rank seven, odd block = `a∫cosh(ar)·tail`).

Guidance numerics for `T(y)=∫_y^∞ x N(x)dx` (`N` = native odd-four fibre):
- `N(x) ≻ 0` for `q=πe^{2x} ≳ 4.3`; seam negativity only below.
- `T(y)` positive definite at every `y` (normalized min eig ≥ 5.4e-3); first atom alone gives
  the same margin.
- In `T(y₁)`'s geometry the seam piece `∫_y^{y₁} xN` is ≥ −2.5% (`y₁=.15`), and PSD for
  `y₁ = log(5/π)/2`.
- Bulk coercivity in first-atom central coordinates `y=A(q)c`, `S=8qf₁²`:
  `N ⪰ κ S AᵀA`, `κ ≥ 0.32` on `q ≥ 4.3`. Seam: first atom alone `≥ −0.43 S AᵀA`; the other
  atoms give `−25 S AᵀA` at `q=π` in one fixed polynomial direction
  `c ≈ (1, −0.044, 4.2e-4, −1e-6)` (not the corner).
- Directional negative part of `N` on `q∈[π,5]` integrated against `x` is ≤ 11% of the bulk
  `∫_{q≥5} x·0.2·S AᵀA`; isotropic or absolute-value bounds fail (×6 to ×10¹³).

Aperture-free seam split (`ThetaCuspOddFourSeamSplit.lean`,
`thetaCuspNativeSuccessorIntegral_seven_nonneg_of_seamSplit`): since `sinh(ay)/y` increases,
`I_7(a) ≥ 0` for all `0<a<1/2` follows from (i) fibre form `≥ 0` for `r > r_c` and
(ii) `∫_0^{r_c} r² min(f_v,0) + ∫_{r_c}^∞ r² f_v ≥ 0` for every `v`. Numerically (ii) holds with
`λ_max(A^{-1/2} B A^{-1/2}) ≈ 0.015–0.02` (≈50× slack) for split `q_c ∈ [4.3, 5]`, where
`A = ∫_{x_c} x²N`, `B = ∫_0^{x_c} x² N⁻`.

Atom sizes in the order-14 jet relative to the first atom: pair (1,2) ≈ 30 at `q=π`,
≈ 5 at `q=3.72`, ≈ 0.1 at `q=5`; pair (2,2) ≈ 1.8 at `q=π`; pair (1,3) ≈ 0.07 at `q=π`.
So the seam needs the exact two-atom formula plus a tail bound valid down to `q=π`.

Certificate design (numerics, guidance): seam fibre `≥ K·cᵀTA(q,e^{-3q})c + (2,2)-pair (PSD for
4q≥5) − tail`, with `TA_m = R1_m(q) + 8e^{-3q}R12_m(q)` (radial polynomials, order 7 generated;
order 6 matches `HTGeometry.twoAtomAffineEvenMoment6`). Tail beyond two atoms ≥ −0.02 (central
metric) at `q=π`. Rank-one compensation `λ(q)·wwᵀ + τI` in central coordinates,
`w=(0,.06,−.37,.93)`, `λ ≤ 27.4`, `τ=.05`: seam/bulk ratio 0.032 (`q_c=4.6`), 0.061 (`q_c=5`).
Lean plan: piecewise-constant certificates in piece-fixed central coordinates `A(q*)`, scalar
bounds for `∫_J r²K dr`, one final rational 4×4 comparison.

Implementation plan (rank eight), regions in `q = πe^{2x}`:
1. `[π, 3.72]` (`x ≤ 8/95`): modular-ODE exact jets `M²·P(u,a,w)` (needs reflected scalar 14);
   seam bound `Q ⪰ −P` over the corpus tube, weight `∫x²M²`.
2. `[3.72, q_c]`: two-atom `K·TA` + (2,2) PSD + factored error (corpus has order ≤ 12; extend
   to 14); piecewise rank-one compensation in piece-fixed central coordinates.
3. `[q_c, ∞)`: pure-native coercivity (first-atom Gershgorin reserve > mixed 1/40 + tail 1/10
   needs `q ≥ 6`); pieces `[q_c, 6]` by certificates.
4. Scalar bounds of `∫_J r² K`, final rational 4×4 comparison, assemble with
   `thetaCuspNativeSuccessorIntegral_seven_nonneg_of_seamSplit`.
Done: `ThetaCuspRadialCoefficients.lean` (coefficient recursion + explicit tables k ≤ 7).

Formalized (all axiom-clean):
- `ThetaCuspOddFourSeamSplit.lean`: aperture-free seam split for the odd block and at every rank
  (`thetaCuspCenterMixedSignedHankel_posSemidef_of_seamSplit`).
- `ThetaCuspOddFourNativeBulk.lean`: first-atom Gershgorin reserve ≥ 1/6 for `v ≤ 1/12`
  (row polynomials in `r=1−12v` with positive coefficients); native odd-four coercive
  (`≥ S/24 |y|²`) for `q ≥ 6`; hence `thetaCuspNativeSuccessorIntegral_seven_nonneg_of_logSixSplit`:
  `I_7(a) ≥ 0` for all `0<a<1/2` given the one inequality `hsplit` at `r_c = log(6/π)`.
- `ThetaCuspRadialCoefficients.lean`: radial coefficient tables through order 7.

Numerics for `hsplit` with isotropic bulk `κ S AᵀA`: `q_c=6, κ=1/24` → ratio 3.96 (fails);
`q_c=5, κ=0.08` → 0.53 (works). So: lower the bulk to `q ≥ 5` with a sharper tail bound
(corpus tail payment 1/10 vs actual ≤ 7e-6 at q=5; first-atom Gershgorin reserve at v=1/10 is
0.111, mixed ≥ −1/40), or certify the bulk non-isotropically.

Tail constants (Cauchy majorant + absolute envelope, S-units, guidance): beyond two atoms
`q=π`: ≥ 2.8 for every radius ≤ 0.35 (useless; actual 0.02); `q=3.72`: 0.07 (ρ=.35);
`q=5`: 3e-5 (ρ=.3). Hence on `q ∈ [π, ~3.7]` keep atom pairs with `n,m ≤ 3` exact
(radial polynomials at `a = n²m²q²`, `X = (n²+m²)q`; pairs (n,n) are rescaled first atoms,
PSD) and bound only beyond three atoms.
Certificate format: piece-fixed central coordinates `y* = A(q*)c`; per piece a constant
matrix bound via entry intervals in `t = q − q₀` plus a rational LDLᵀ check.

Formalized: `ThetaCuspThreeAtomCauchyTail.lean` (`native_threeAtom_cauchy_error`: beyond three
atoms `|Δ_n| ≤ n!·8000 f₁² e^{-(529/50)q}/(3/20)^n` on `q ≥ 3`); `ThetaCuspPairRadialValues.lean`
(pairs (1,1),(1,2),(1,3),(2,3), orders 1–7); `ThetaCuspOddFourThreeAtomModel.lean`
(`nativeOddForm_ge_threeAtom`: fibre ≥ `K(q)·vᵀT(q)v − Σ|v_i||v_j|·tail`, diagonal pairs dropped as
PSD).

Exact-rational certificate dry run (Python, rigorous t-expansions, outward-rounded exp bounds,
Gershgorin radii, tail radii, LDL checks): seam pieces of width 0.1 on `[3,5]` (20) and bulk pieces
of width 0.25 on `[5,8]` (12), center expansions in piece-fixed frames `A(q*)`: final 4×4
comparison PSD, ratio 0.064. Coarser grids fail at the bulk piece at 5 (crude `e^{-3q}` interval).
Lean obstacle: direct identities with exact `A(q*)⁻¹` literals time out at elaboration; must
split into small lemmas or use frames with short rational entries (no budget raises).

Formalized: `ThetaCuspOddFourCentralEntries.lean` (moving-frame numerators `N^{ab}_{ij}`,
64 entry identities, pair energies), `ThetaCuspOddFourCentralBound.lean`
(`nativeOddForm_ge_central`: native odd form ≥ `K(q)q⁻⁶[yᵀE(q)y − 8000(2q−3)²e^{-529q/50}Σρ̃_k y_k²]`
on `q ≥ 3`, `c = B(1/q)y`).
Moving-frame certificate design (rigorous dry run): seam pieces width 0.05 on `[3,3.5]`, 0.1 on
`[3.5,5]` (25), bulk width 0.25 on `[5,8]` (12): final comparison PSD, ratio 0.175. Per piece:
`W(q) − D(q)Ĉ ⪰ 0` (bulk) / `W(q) + D(q)Q̂ ⪰ 0` (seam), `D = 8q⁷(2q−3)²`, via Taylor shifts at the
center, linearized `e^{-3q}`, endpoint LDL checks; integral step `∫A(q)ᵀĈA(q)dq` exact.

Remaining for rank eight: a provable structured lower bound for the mixed atom pair on
`q∈[π,5]` capturing that direction, bulk coercivity on `q≥5` without compensation, and the
certified 4×4 comparison of the two integrated forms.

## Q2 — answered and formalized (unconditional)

Answer: yes. For the boosted unit spline the complete Weil matrix at any fixed overlap `c>0`,
in particular `c=3/2`, is positive definite for all large horizons
(`CACT/MacroscopicOverlapPositivityAtEveryOverlap.lean`:
`eventually_tiltedUnitSpline_completeWeilMatrix_posDef`, `..._three_halves`; axioms
`propext`, `Classical.choice`, `Quot.sound`).

Mechanism: fixed-overlap prime-defect reserve (other writer) + norm quasimodes
`‖W v_m − E_m(c) v_m‖ → 0` (`tendsto_completeWeilMatrix_ramanujan_quasimode_norm`) + common
conductor floor (`exists_tiltedUnitSpline_conductor_floor`) ⟹ min-max positivity
(`eventually_completeWeilMatrix_posDef_of_reserve_quasimodes`). The quasimode combines hgt-3b's
residual theorem (all blocks except the upward rows) with
`RAPT/TheUpwardPrimeWindowsCarryTheShellCorrection.lean`:
`tendsto_sum_sq_upwardPrimeRow_sub_shellCorrection` (upward rows → `κ_m(c)` in `ℓ²`: row =
Mangoldt sum of punctured windows; window vs affine-shell model `O(1/N)` by linearizing
`log(1±h/p)` and `√(p/j)`; boundary mass `≤ 4H log(2X)/X`; weighted affine prime shells give
`c_m(n)κ_m(c)` uniformly for `X=N/n ≥ J`; rows with `X<J` bounded with harmonic mass
`O(J/log N)`).

Open refinement (not asked as a condition): quantitative horizon threshold in terms of `m, c`.

## Log
- 2026-10-30 — card created.
