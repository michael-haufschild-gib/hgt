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

**Rank eight — the first test, answered: `I_7(a) ≥ 0` for every `0<a<1/2`** (unconditional).
`RHTower/ThetaCusp/ThetaCuspOddFourRankEight.lean`: `thetaCuspNativeSuccessorIntegral_seven_nonneg`,
`thetaCuspCenterMixedSignedHankel_eight_posSemidef` (size-8 signed section PSD),
`thetaCuspCenterMixedOddFour_posSemidef`; axioms `propext`, `Classical.choice`, `Quot.sound`.
Proof: aperture-free seam split at `r_c=log(5/π)`. Fibre `≥ K(q)q⁻⁶[yᵀE(q)y − tail]` in the
moving frame `c=B(1/q)y` (three exact atom pairs + Cauchy tail). 23 piece certificates
(`ThetaCuspOddFourCertificatePieces1–6`): `W(q)+D(q)X ⪰ 0` on each `q`-interval via Taylor shifts
at the center (all four atom-pair numerators, including `(1,3)`, `(2,3)`), linearized `e^{-3q}`,
endpoint `LDLᵀ`. Seam `q∈[π,5]` (15 pieces, `X⪰0`) bounds `r²min(f,0) ≥ −Ω·q·yᵀXy`; bulk
`q∈[5,8]` (8 pieces, `X⪯0`) gives `f≥0` with reserve; beyond `q=6` first-atom coercivity
(`ThetaCuspOddFourNativeBulk`). `ThetaCuspOddFourPieceIntegral` + `CertificateIntegrals1–4`: the
moving-frame form is polynomial in `q` and integrates exactly against `πe^r dr=dq`; rational
weight bounds per piece. Final 4×4 comparison (bulk reserve − seam cost) PSD by exact `LDLᵀ`
(slack ≈ 18×). Design note: crude absolute-coefficient bounds on the `(1,3)` pair cost ~10⁴ of
its true size in the badly scaled `y₃` direction; center-shifted bounds remove it.

Exact structure (formalized, `ThetaCuspCenterTailSquareFlux.lean`): the fibre form is a perfect
square plus a null Lagrangian, `J_v=|G_v|²+B_v'` with `G_v=Σ_j v_j(2i)^jΦ^(j)` and explicit flux
`B_v=Σ v_iv_jB_{ij}` (`hasDerivAt_thetaCuspNativeFlux`); hence the tail form at center `x=r/2`
equals `2∫_x^∞|G_v|²-2B_v(x)` (`thetaCuspNativeTailHankelForm_eq_square_sub_flux`), bulk `L²`
mass beyond the center minus a local boundary flux. Mechanism: Leibniz gives
`h_{2n}=(−1)^nΣ_m C(2n,m)(−1)^mφ_mφ_{2n−m}`, and `φ_aφ_{2n−a}≡(−1)^{n−a}φ_n²` modulo the derivative
of the alternating telescoping sum `Σ_l(−1)^lφ_{a+l}φ_{2n−1−a−l}`; Hankel and Gram entries both
reduce to `4^nφ_n²`. The rank-`n` successor sign is exactly the statement that this mass
dominates that flux at every center.

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

Big-picture remark (not proved): the `a`-free tail conditions at every order are at least RH strength
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

## Q1 — rank eight (`I_7`): reduction chain (all formalized, axiom-clean)

- `ThetaCuspOddFourMomentTail.lean`: parity split; the even block comes from rank seven, so
  `I_7(a) ≥ 0` reduces to the odd 4×4 block.
- `ThetaCuspOddFourSeamSplit.lean`: aperture-free seam split (`sinh(ay)/y` increasing): fibre
  `≥ 0` beyond `r_c` plus `∫_0^{r_c} r² min(f_v,0) + ∫_{r_c}^∞ r² f_v ≥ 0` give the odd block at
  every `0<a<1/2`; same split at every rank.
- `ThetaCuspOddFourNativeBulk.lean`: first-atom coercivity, fibre `≥ 0` for `q ≥ 6`.
- `ThetaCuspRadialCoefficients`, `ThetaCuspPairRadialValues`, `ThetaCuspThreeAtomCauchyTail`,
  `ThetaCuspOddFourThreeAtomModel`, `ThetaCuspOddFourCentralEntries`,
  `ThetaCuspOddFourCentralBound`: three exact atom pairs + Cauchy tail in the moving frame.
- `ThetaCuspOddFourCertificateTools`, `ThetaCuspOddFourPieceSetup`,
  `ThetaCuspOddFourCertificatePieces1–6`, `ThetaCuspOddFourPieceIntegral`,
  `ThetaCuspOddFourCertificateIntegrals1–4`, `ThetaCuspOddFourRankEight`: the piecewise
  certificate and final comparison (see top).

Guidance numerics (not proof inputs): odd fibre block negative only for `q ≲ 4.3`; true
seam/bulk ratio of the model ≈ 0.006 at `q_c ∈ [4.3,5]`; the certificate reaches 0.054.

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
