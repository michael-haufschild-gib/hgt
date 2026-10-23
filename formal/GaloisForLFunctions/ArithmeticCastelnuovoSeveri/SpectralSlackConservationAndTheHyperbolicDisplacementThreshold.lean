import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheTwoThirdsConstantIsPairCorrelation
import GaloisForLFunctions.RHTower.RankTraceNegativePartCredit
import GaloisForLFunctions.RHTower.RankTraceSpectralSlack
import GaloisForLFunctions.RHTower.Zeta23TheoremASpectralSlack

/-!
# Spectral-Slack Conservation, the Grid-Dimension Ceiling, and the Hyperbolic Displacement Thresholds

`BreakingTheCoalescenceBlindSpotAndThreeQuarters` showed via `zeta_three_quarters_of_spectralSlack`
and `RHTower.thmA_lam_spectralSlack` that for every sub-threshold bandwidth `λ ∈ (0, 1)`,
`(H(λ) − ε) N(T, 2T) + zeroSideSlack(λ, T) ≤ N₀*(T, 2T)`, so that proving
`zeroSideSlack(λ, T) ≥ (3/4 − H(λ)) N(T, 2T)` unconditionally would certify `3/4` (`75%`) of the
nontrivial zeros of `ζ(s)` on the critical line.

This module proves four unconditional structural theorems governing the spectral-slack path:

1. **Exact Spectral-Slack Conservation and Prime-Side Cancellation (`rank_trace_add_totalSlack_eq`,
   `zeroside_rank_core_slack_exact`, `zeroside_rank_core_slack_le_rank`):**
   For any Hermitian critical-line matrix `P` and off-line matrix `Q = Q₊ − Q₋`, the total spectral
   slack `totalSlack(P, Q, c) := c tr(Q₋) + posSlack(Q, c) + onSlack(P, Q, c)` satisfies the exact
   algebraic identity
   `(c tr P + 2c tr Q − c² n₊(Q) − ‖P + Q‖_F²) + totalSlack(P, Q, c) = (c²/4) rank P − Δ_c(P, Q)`,
   where `Δ_c(P, Q) ≥ 0` (`couplingDefect`) is the sum of the positive-part cross trace
   `2 Re tr(P Q₊)`, the Von Neumann eigenvalue-alignment defect `2(∑ₖ pₖ mₖ − Re tr(P Q₋))`, and
   the kernel defect `∑_{pₖ = 0} (mₖ² + c mₖ)`. At `c = 2`, adding `totalSlack(P, Q, 2)` to
   `4 tr(P + Q) − 2N − ‖P + Q‖_F²` **cancels the prime-side quadratic functional
   `4 tr(P + Q) − ‖P + Q‖_F²` identically**, leaving
   `rank P − 2(N − tr P − 2 n₊(Q)) − Δ₂(P, Q) ≤ rank P`.

2. **Unconditional Grid-Dimension Ceiling on `zeroSideSlack` and Refutation for `λ ∈ (0, 3/4)`
   (`seamA_spectralSlack_le_d`, `zeroSideSlack_eventually_le_lam_sub_Hfun`,
   `not_three_quarters_zeroSideSlack_of_lt_three_quarters`):**
   Because the critical-line matrix `P̂(T)` is a `d(T) × d(T)` matrix with
   `d(T) = ⌊λ l(T) T / 2π⌋ = (λ + o(1)) N(T, 2T)`, its rank satisfies `rank P̂(T) ≤ d(T)`
   unconditionally. Consequently, for every `λ ∈ (0, 1)` and `ε > 0`, for all large `T`,
   `zeroSideSlack(λ, T) ≤ (λ − H(λ) + ε) N(T, 2T) = (1/λ + 4λ/3 − 2 + ε) N(T, 2T)`.
   In particular, for **every `λ ∈ (0, 3/4)`**, eventually
   `zeroSideSlack(λ, T) < (3/4 − H(λ)) N(T, 2T)`: the hypothesis of
   `zeta_three_quarters_of_spectralSlack` is unconditionally false on `(0, 3/4)`.

3. **Universal Cauchy–Schwarz Lower Bound on `posSlack` from `hermNegPart`
   (`posSlack_mul_ge_sq_of_rtrace`, `offLine_slack_ge_of_rtrace_hermNegPart`):**
   For any Hermitian matrix `Q` with `n₊(Q) ≤ b` and `tr Q + tr(Q₋) ≥ c b` (`c ≥ 0`), Cauchy–Schwarz
   on the positive spectrum of `Q` yields
   `b · posSlack(Q, c) ≥ (tr Q + tr(Q₋) − c b)²`. At `c = 2`, whenever `tr Q ≥ 2b` and
   `tr(Q₋) ≥ 2 η b` (`η ≥ 0`), the off-line spectral slack satisfies
   `2 tr(Q₋) + posSlack(Q, 2) ≥ 4 b η (1 + η)`.

4. **Hyperbolic Displaced-Pair Block Calculus, the Pythagorean Counterexample at `κ = 4/3`, and the
   Three Exact Macroscopic Displacement Thresholds (`displacedPairBlockData`,
   `displacedPairBlockData_below_three_quarters`,
   `macroscopic_displacedPair_counterexample_at_four_thirds`,
   `hyperbolic_displacedPair_three_thresholds_at_four_thirds`):**
   An off-line zero pair with orthogonal evaluation components `‖x‖² = α² = 1 + η` and
   `‖y‖² = β² = η` (`α² − β² = 1`, preserving trace `2`) has positive eigenvalue `2(1 + η)`,
   negative eigenvalue `−2η`, and squared Frobenius norm `2 + 2(1 + 2η)²`. At the bandwidth-one
   Frobenius constant `κ = 4/3` (`2p(1 + 2η)² = N/3`), three distinct macroscopic thresholds
   govern the `3/4` barrier:
   * True critical-line count `s₁ = N − 2p ≥ (3/4) N` iff `(1 + 2η)² ≥ 4/3`
     (`η ≥ 1/√3 − 1/2 ≈ 0.07735`);
   * Full spectral slack `totalSlack ≥ (1/12) N` iff `η ≥ 1/6 ≈ 0.16667`;
   * Off-line spectral slack `2 tr(Q₋) + posSlack ≥ (1/12) N` iff `(1 + 2η)² ≥ 2`
     (`η ≥ (√2 − 1)/2 ≈ 0.20711`).
   Instantiating `displacedPairBlockData` at the Pythagorean rational point `α = 41/40, β = 9/40`
   (`η = 81/1600 > 0`, `s₁ = 3376966, p = 640000, N = 4656966`) gives an explicit `ZeroBlockData`
   configuration with `tr Â = N`, `‖Â‖_F² = (4/3) N`, and **strictly positive** negative-part
   credit `2 tr(Q₋) > 0` (`¬ Q.PosSemidef`, non-coalesced!), yet `s₁ < (3/4) N` and
   `totalSlack < (1/12) N`.
-/

open Complex Finset Matrix Filter
open scoped BigOperators ComplexOrder Topology
open Zeta23 Zeta23.ZeroSide RHLinalg RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ## 1. Exact Spectral-Slack Conservation and Prime-Side Cancellation -/

/-- The total spectral slack of the rank–trace inequality at scale `c`:
`c tr(Q₋) + posSlack(Q, c) + onSlack(P, Q, c)`. -/
def totalSlack {d : Type*} [Fintype d] [DecidableEq d]
    {P Q : Matrix d d ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (c : ℝ) : ℝ :=
  c * RHLinalg.rtrace (RHLinalg.hermNegPart hQ) +
    RHTower.posSlack hQ c + RHTower.onSlack hP hQ c

/-- The total spectral slack is nonnegative for every `c ≥ 0`. -/
theorem totalSlack_nonneg {d : Type*} [Fintype d] [DecidableEq d]
    {P Q : Matrix d d ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ totalSlack hP hQ c := by
  unfold totalSlack
  have h1 : 0 ≤ c * RHLinalg.rtrace (RHLinalg.hermNegPart hQ) :=
    mul_nonneg hc (RHTower.rtrace_hermNegPart_nonneg hQ)
  have h2 := RHTower.posSlack_nonneg hQ c
  have h3 := RHTower.onSlack_nonneg hP hQ c
  linarith

/-- The residual coupling defect `Δ_c(P, Q)` between the critical-line matrix `P` and the
positive/negative parts `Q₊, Q₋` of the off-line matrix `Q`:
`2 Re tr(P Q₊) + 2(∑ₖ pₖ mₖ − Re tr(P Q₋)) + ∑_{pₖ = 0} (mₖ² + c mₖ)`. -/
def couplingDefect {d : Type*} [Fintype d] [DecidableEq d]
    {P Q : Matrix d d ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (c : ℝ) : ℝ :=
  let Qp := RHLinalg.hermPosPart hQ
  let Qm := RHLinalg.hermNegPart hQ
  let hQm := (RHLinalg.hermNegPart_posSemidef hQ).isHermitian
  2 * RCLike.re (P * Qp).trace +
    2 * (∑ k, hP.eigenvalues₀ k * hQm.eigenvalues₀ k - RCLike.re (P * Qm).trace) +
    ∑ k, if hP.eigenvalues₀ k = 0 then
      (hQm.eigenvalues₀ k) ^ 2 + c * hQm.eigenvalues₀ k
    else 0

/-- **Nonnegativity of the coupling defect `Δ_c(P, Q)`.**
Whenever `P ⪰ 0`, `Q` is Hermitian, and `c ≥ 0`, all three components of `couplingDefect` are
nonnegative: `Re tr(P Q₊) ≥ 0` (trace of a product of PSD matrices), `∑ₖ pₖ mₖ ≥ Re tr(P Q₋)`
(Von Neumann's trace inequality), and `mₖ² + c mₖ ≥ 0` on `ker P`. -/
theorem couplingDefect_nonneg {d : Type*} [Fintype d] [DecidableEq d]
    {P Q : Matrix d d ℂ} (hP : P.PosSemidef) (hQ : Q.IsHermitian) {c : ℝ} (hc : 0 ≤ c) :
    0 ≤ couplingDefect hP.isHermitian hQ c := by
  unfold couplingDefect
  dsimp only
  set hQp := RHLinalg.hermPosPart_posSemidef hQ
  set hQm := RHLinalg.hermNegPart_posSemidef hQ
  have h1 : 0 ≤ RCLike.re (P * RHLinalg.hermPosPart hQ).trace :=
    RHLinalg.trace_mul_nonneg_of_posSemidef hP hQp
  have h2 : RCLike.re (P * RHLinalg.hermNegPart hQ).trace ≤
      ∑ k, hP.isHermitian.eigenvalues₀ k * hQm.isHermitian.eigenvalues₀ k :=
    RHLinalg.vonNeumann_trace_ineq hP.isHermitian hQm.isHermitian
  have h3 : 0 ≤ ∑ k, if hP.isHermitian.eigenvalues₀ k = 0 then
      (hQm.isHermitian.eigenvalues₀ k) ^ 2 + c * hQm.isHermitian.eigenvalues₀ k else 0 := by
    refine Finset.sum_nonneg fun k _ => ?_
    split_ifs
    · have hm : 0 ≤ hQm.isHermitian.eigenvalues₀ k := by
        rw [show hQm.isHermitian.eigenvalues₀ k =
            hQm.isHermitian.eigenvalues (RHLinalg.eigEquiv k) from
          (RHLinalg.eigenvalues_eigEquiv hQm.isHermitian k).symm]
        exact hQm.eigenvalues_nonneg _
      positivity
    · exact le_rfl
  linarith

/-- **Exact spectral-slack conservation law for the rank–trace functional.**
For any Hermitian matrices `P, Q : Matrix d d ℂ` and any real scale `c`, adding `totalSlack P Q c`
to `c tr P + 2c tr Q − c² n₊(Q) − ‖P + Q‖_F²` cancels all eigenvalue variances and equals
`(c² / 4) rank P − couplingDefect P Q c` identically. -/
theorem rank_trace_add_totalSlack_eq {d : Type*} [Fintype d] [DecidableEq d]
    {P Q : Matrix d d ℂ} (hP : P.IsHermitian) (hQ : Q.IsHermitian) (c : ℝ) :
    c * RHLinalg.rtrace P + 2 * c * RHLinalg.rtrace Q - c ^ 2 * (RHLinalg.posIndex hQ : ℝ) -
        RHLinalg.frobSq (P + Q) + totalSlack hP hQ c =
      (c ^ 2 / 4) * (P.rank : ℝ) - couplingDefect hP hQ c := by
  classical
  set Qp := RHLinalg.hermPosPart hQ with hQp_def
  set Qm := RHLinalg.hermNegPart hQ with hQm_def
  have hQdec : Q = Qp - Qm := (RHLinalg.hermPosPart_sub_hermNegPart hQ).symm
  have hQp_psd : Qp.PosSemidef := RHLinalg.hermPosPart_posSemidef hQ
  have hQm_psd : Qm.PosSemidef := RHLinalg.hermNegPart_posSemidef hQ
  have hQpQm : Qp * Qm = 0 := RHLinalg.hermPosPart_mul_hermNegPart hQ
  set p := hP.eigenvalues₀ with hp_def
  set m := hQm_psd.isHermitian.eigenvalues₀ with hm_def
  have htraceP : RHLinalg.rtrace P = ∑ k, p k :=
    (RHLinalg.rtrace_eq_sum_eigenvalues hP).trans (RHLinalg.sum_eigenvalues_reindex hP id)
  have htraceQm : RHLinalg.rtrace Qm = ∑ k, m k :=
    (RHLinalg.rtrace_eq_sum_eigenvalues hQm_psd.isHermitian).trans
      (RHLinalg.sum_eigenvalues_reindex hQm_psd.isHermitian id)
  have hfrobP : RHLinalg.frobSq P = ∑ k, (p k) ^ 2 :=
    (RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hP).trans
      (RHLinalg.sum_eigenvalues_reindex hP (· ^ 2))
  have hfrobQm : RHLinalg.frobSq Qm = ∑ k, (m k) ^ 2 :=
    (RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hQm_psd.isHermitian).trans
      (RHLinalg.sum_eigenvalues_reindex hQm_psd.isHermitian (· ^ 2))
  have hrankP : (P.rank : ℝ) = ∑ k, if p k ≠ 0 then (1 : ℝ) else 0 := by
    have hcard : #{k | p k ≠ 0} = P.rank :=
      (RHLinalg.card_eigenvalues_reindex hP (· ≠ 0)).symm.trans
        (by rw [hP.rank_eq_card_non_zero_eigs, Fintype.card_subtype])
    rw [← hcard, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  have hexpand : RHLinalg.frobSq (P + Q) =
      RHLinalg.frobSq P + 2 * RCLike.re (P * Qp).trace - 2 * RCLike.re (P * Qm).trace +
        RHLinalg.frobSq Qp + RHLinalg.frobSq Qm := by
    have h1 : RHLinalg.frobSq (-Qm) = RHLinalg.frobSq Qm := by
      unfold RHLinalg.frobSq; rw [conjTranspose_neg, neg_mul_neg]
    have h2 : RCLike.re (Qp * -Qm).trace = 0 := by
      rw [mul_neg, hQpQm]; simp
    rw [hQdec, RHLinalg.frobSq_add_hermitian hP (hQp_psd.isHermitian.sub hQm_psd.isHermitian),
      sub_eq_add_neg Qp Qm,
      RHLinalg.frobSq_add_hermitian hQp_psd.isHermitian hQm_psd.isHermitian.neg,
      h1, h2, mul_add, mul_neg, trace_add, trace_neg, map_add, map_neg]
    ring
  have hpos_eq : 2 * c * RHLinalg.rtrace Qp - c ^ 2 * (RHLinalg.posIndex hQ : ℝ) +
      RHTower.posSlack hQ c = RHLinalg.frobSq Qp := by
    rw [hQp_def, RHLinalg.rtrace_hermPosPart, RHLinalg.frobSq_hermPosPart, RHTower.posSlack]
    have hcard : (∑ i : d, if 0 < hQ.eigenvalues i then c ^ 2 else (0 : ℝ)) =
        c ^ 2 * (RHLinalg.posIndex hQ : ℝ) := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      rfl
    rw [← hcard, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : 0 < hQ.eigenvalues i
    · rw [if_pos h, if_pos h, posPart_eq_self.mpr h.le]; ring
    · rw [if_neg h, if_neg h, posPart_eq_zero.mpr (not_lt.mp h)]; ring
  have hon_eq : c * RHLinalg.rtrace P - (c ^ 2 / 4) * (P.rank : ℝ) - c * RHLinalg.rtrace Qm +
      RHTower.onSlack hP hQ c +
      (∑ k, if p k = 0 then (m k) ^ 2 + c * m k else 0) =
      RHLinalg.frobSq P - 2 * (∑ k, p k * m k) + RHLinalg.frobSq Qm := by
    unfold RHTower.onSlack
    rw [htraceP, hrankP, htraceQm, hfrobP, hfrobQm]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : p k = 0
    · simp only [p, m] at hk ⊢
      rw [if_neg (not_not.mpr hk), if_neg (not_not.mpr hk), if_pos hk, hk]
      ring
    · simp only [p, m] at hk ⊢
      rw [if_pos hk, if_pos hk, if_neg hk]
      ring
  have htraceQ : 2 * c * RHLinalg.rtrace Q =
      2 * c * RHLinalg.rtrace Qp - 2 * c * RHLinalg.rtrace Qm := by
    rw [RHLinalg.rtrace_sub_decomp hQ, ← hQp_def, ← hQm_def]; ring
  change c * RHLinalg.rtrace P + 2 * c * RHLinalg.rtrace Q - c ^ 2 * (RHLinalg.posIndex hQ : ℝ) -
      RHLinalg.frobSq (P + Q) + (c * RHLinalg.rtrace Qm + RHTower.posSlack hQ c +
        RHTower.onSlack hP hQ c) =
    (c ^ 2 / 4) * (P.rank : ℝ) -
      (2 * RCLike.re (P * Qp).trace +
        2 * (∑ k, p k * m k - RCLike.re (P * Qm).trace) +
        ∑ k, if p k = 0 then (m k) ^ 2 + c * m k else 0)
  linarith [hexpand, hpos_eq, hon_eq, htraceQ]

/-- **Exact prime-side cancellation at `c = 2`.**
For any decomposition `Â = P + Q` of Hermitian matrices and any scalar `N`, adding
`totalSlack P Q 2` to the `c = 2` rank–trace functional `4 tr Â − 2N − ‖Â‖_F²` cancels the
prime-side quadratic functional `4 tr Â − ‖Â‖_F²` identically, leaving
`rank P − 2(N − tr P − 2 n₊(Q)) − couplingDefect P Q 2`. -/
theorem zeroside_rank_core_slack_exact {d : Type*} [Fintype d] [DecidableEq d]
    {Ahat P Q : Matrix d d ℂ} (hPQ : Ahat = P + Q)
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) (N : ℝ) :
    4 * RHLinalg.rtrace Ahat - 2 * N - RHLinalg.frobSq Ahat + totalSlack hP hQ 2 =
      (P.rank : ℝ) - 2 * (N - RHLinalg.rtrace P - 2 * (RHLinalg.posIndex hQ : ℝ)) -
        couplingDefect hP hQ 2 := by
  have h := rank_trace_add_totalSlack_eq hP hQ 2
  subst hPQ
  rw [RHLinalg.rtrace_add]
  linarith

/-- **Rank ceiling for the slack-augmented rank–trace functional.**
Whenever `P ⪰ 0`, `Q` is Hermitian, and `tr P + 2 n₊(Q) ≤ N`, the slack-augmented functional
`4 tr Â − 2N − ‖Â‖_F² + totalSlack P Q 2` cannot exceed `rank P`. -/
theorem zeroside_rank_core_slack_le_rank {d : Type*} [Fintype d] [DecidableEq d]
    {Ahat P Q : Matrix d d ℂ} (hPQ : Ahat = P + Q)
    (hP : P.PosSemidef) (hQ : Q.IsHermitian) {N : ℝ}
    (hcount : RHLinalg.rtrace P + 2 * (RHLinalg.posIndex hQ : ℝ) ≤ N) :
    4 * RHLinalg.rtrace Ahat - 2 * N - RHLinalg.frobSq Ahat +
      totalSlack hP.isHermitian hQ 2 ≤ (P.rank : ℝ) := by
  rw [zeroside_rank_core_slack_exact hPQ hP.isHermitian hQ N]
  have hdef := couplingDefect_nonneg hP hQ (by norm_num : (0 : ℝ) ≤ 2)
  linarith

/-! ## 2. Unconditional Grid-Dimension Ceiling on `zeroSideSlack` and Refutation on `(0, 3/4)` -/

/-- The critical-line Gram matrix `hatP Z T P hconj` is a `d(T) × d(T)` matrix, so its rank is
unconditionally at most the grid dimension `P.d T`. -/
theorem rank_hatP_le_d (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : ZeroSide.PhiHatConj T P) (hc : 0 < P.a T * P.L T ^ 2) :
    (ZeroSide.hatP Z T P hconj).rank ≤ P.d T := by
  have hPm := ZeroSide.hatP_posSemidef Z T P hconj hc
  rw [← RHLinalg.posIndex_eq_rank_of_posSemidef hPm]
  exact (RHLinalg.posIndex_le_card hPm.isHermitian).trans_eq (Fintype.card_fin (P.d T))

/-- **Seam A with spectral slack bounded above by the grid dimension `P.d T`.**
Replacing `rank P̂ ≤ s₁ + s₂` by `rank P̂ ≤ d(T)` in `RHTower.seamA_spectralSlack` bounds the
slack-augmented zero-side functional above by `(P.d T : ℝ)`. -/
theorem seamA_spectralSlack_le_d {Z : ZeroConfig} {P : Params} {T : ℝ}
    (hT : 0 ≤ T) (hPois : ZeroSide.PoissonSq T P)
    {θ₀ : ℝ} (hTl : Assembly.TailInputs Z P T θ₀) (ha : 0 < P.a T) (hL : 0 < P.L T) :
    4 * RHLinalg.rtrace (P.hat T (Z.Gz P T)) - RHLinalg.frobSq (P.hat T (Z.Gz P T))
      - 2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ)
      - θ₀ / (P.a T * P.L T) * (4 + 2 * Real.sqrt (RHLinalg.frobSq (P.hat T (Z.Gz P T)))
          + θ₀ / (P.a T * P.L T))
      + RHTower.zeroSideSlack Z P T
      ≤ (P.d T : ℝ) := by
  have hconj : ZeroSide.PhiHatConj T P := fun z => GzGp.phiHat_conj P T z
  have hreal : ZeroSide.PhiHatReal T P := fun r => GzGp.phiHat_ofReal P T r
  have hc : 0 < P.a T * P.L T ^ 2 := mul_pos ha (pow_pos hL 2)
  have hdec := ZeroSide.hat_Az_eq_hatP_add_hatQ Z T P hconj
  have hPm := ZeroSide.hatP_posSemidef Z T P hconj hc
  have hQm := ZeroSide.hatQ_isHermitian Z T P hconj
  have hrank := rank_hatP_le_d Z P T hconj hc
  have htrP := ZeroSide.rtrace_hatP_le Z T P hconj hreal hPois hc
  have hpos := ZeroSide.posIndex_hatQ_le Z T P hconj hc hQm
  have hcount : (Z.NonIprime T : ℝ) + 2 * (Z.p T : ℝ) ≤ (Z.NIprime T : ℝ) := by
    exact_mod_cast ZeroSide.NonIprime_add_two_p_le_NIprime Z T
  obtain ⟨B, hB0, htrE, hfrE, hBle⟩ := hTl.hat
  have hGAE : P.hat T (Z.Gz P T) = P.hat T (Z.Az P T) + P.hat T (Z.Ez P T) := by
    rw [← Assembly.hat_add]; congr 1; simp [ZeroConfig.Ez]
  have hB₀ : 0 ≤ θ₀ / (P.a T * P.L T) := div_nonneg hTl.theta_nonneg (mul_pos ha hL).le
  have hcore := RHTower.zeroside_rank_core_slack hdec hPm hQm hrank hpos htrP hcount
  have hpert := Assembly.four_tr_sub_frobSq_perturb hGAE hB₀ (htrE.trans hBle)
    (hfrE.trans (pow_le_pow_left₀ hB0 hBle 2))
  have hNI : (Z.NIprime T : ℝ) = (Z.N T (2 * T) : ℝ) + (Assembly.NII Z T : ℝ) := by
    exact_mod_cast Assembly.NIprime_eq Z hT
  have hNII_nn : 0 ≤ (Assembly.NII Z T : ℝ) := Nat.cast_nonneg _
  have hS : RHTower.zeroSideSlack Z P T =
      2 * RHLinalg.rtrace (RHLinalg.hermNegPart hQm) + RHTower.posSlack hQm 2 +
        RHTower.onSlack hPm.isHermitian hQm 2 := by
    rw [RHTower.zeroSideSlack, RHTower.onLineParsevalDefect, dif_pos hc]; rfl
  rw [hNI] at hcore
  rw [hS]
  linarith

/-- Under Riemann–von Mangoldt, the grid dimension `P.d T = ⌊λ l(T) T / 2π⌋` is eventually bounded
above by `(P.lam + ε) N(T, 2T)`. -/
theorem eventually_d_le_lam_mul_N (Z : ZeroConfig) (hRvM : RiemannVonMangoldt Z)
    (P : Params) (hlam0 : 0 ≤ P.lam) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, (P.d T : ℝ) ≤ (P.lam + ε) * (Z.N T (2 * T) : ℝ) := by
  obtain ⟨CN, T₃, hRvMmain⟩ := hRvM.main
  have ho : (fun T => P.lam * |CN| * Real.log T) =o[atTop] (fun T => (Z.N T (2 * T) : ℝ)) := by
    simpa [mul_assoc] using
      (Assembly.isLittleO_N_of_isLittleO_Tl Z hRvM Assembly.isLittleO_log_Tl).const_mul_left
        (P.lam * |CN|)
  filter_upwards [ho.def hε, eventually_ge_atTop T₃, eventually_ge_atTop (0 : ℝ),
    Assembly.eventually_l_pos, Assembly.eventually_log_nonneg] with T h1 hT₃ hT0 hl hlog
  have hN0 : 0 ≤ (Z.N T (2 * T) : ℝ) := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN0] at h1
  have hlog_err : P.lam * |CN| * Real.log T ≤ ε * (Z.N T (2 * T) : ℝ) :=
    (le_abs_self _).trans h1
  have hd : (P.d T : ℝ) ≤ P.L T * T / (2 * Real.pi) :=
    Assembly.d_le P (by unfold Params.L; positivity)
  have hL_eq : P.L T * T / (2 * Real.pi) = P.lam * (T * l T / (2 * Real.pi)) := by
    unfold Params.L; ring
  have hl_le_ell1 : l T ≤ ell1 T := by
    rw [Assembly.ell1_eq]; linarith [Assembly.c₀_pos]
  have hTl_le : T * l T / (2 * Real.pi) ≤ T * ell1 T / (2 * Real.pi) := by gcongr
  have hRvM' : T * ell1 T / (2 * Real.pi) ≤ (Z.N T (2 * T) : ℝ) + |CN| * Real.log T := by
    have hrv := (abs_le.mp (hRvMmain T hT₃)).1
    have hcn : CN * Real.log T ≤ |CN| * Real.log T :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hlog
    have h3 : T / (2 * Real.pi) * ell1 T = T * ell1 T / (2 * Real.pi) := by ring
    linarith
  have hmul : P.lam * (T * l T / (2 * Real.pi)) ≤
      P.lam * ((Z.N T (2 * T) : ℝ) + |CN| * Real.log T) :=
    mul_le_mul_of_nonneg_left (hTl_le.trans hRvM') hlam0
  linarith

/-- **Grid-dimension ceiling for `thmA_abstract_err_spectralSlack`.**
For any abstract zero configuration `Z` satisfying the Theorem A inputs at bandwidth `P.lam < 1`,
`(H(λ) − ε) N(T, 2T) + zeroSideSlack Z P T ≤ P.d T` eventually in `T`. -/
theorem thmA_abstract_err_spectralSlack_le_d (Z : ZeroConfig) (hRvM : RiemannVonMangoldt Z)
    (P : Params) (hP : P.Valid) (hlam : P.lam < 1) (Err : ℝ → ℝ)
    (hTr : TracesBoundsE P Err P.a P.trGtilde P.trGtildeSq (fun T => (Z.N T (2 * T) : ℝ)))
    (hPois : ∀ᶠ T in atTop, ZeroSide.PoissonSq T P)
    (θ₀ : ℝ → ℝ) (hTail : ∀ᶠ T in atTop, Assembly.TailInputs Z P T (θ₀ T))
    (hθ₀ : ∃ C : ℝ, ∀ᶠ T in atTop, θ₀ T ≤ C * l T * T ^ (P.lam / 2 - 1))
    (hNII : ∃ C : ℝ, ∀ᶠ T in atTop, (Assembly.NII Z T : ℝ) ≤ C * Real.sqrt T * l T)
    (hGzGp : ∀ᶠ T in atTop, Z.Gz P T = P.Gp T)
    (ha : ∀ᶠ T in atTop, 1 - 2 * P.w / P.L T ≤ P.a T ∧ P.a T ≤ 1)
    (hcalE : Tendsto Err atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ T in atTop,
      (Hfun P.lam - ε) * (Z.N T (2 * T) : ℝ) + RHTower.zeroSideSlack Z P T ≤ (P.d T : ℝ) := by
  have hlam0 := hP.lam_pos
  have hlam1 : P.lam ≤ 1 := hlam.le
  obtain ⟨C₁, hC₁, T₁, htr1⟩ := hTr.tr1
  obtain ⟨C₂, hC₂, T₂, htr2⟩ := hTr.tr2
  obtain ⟨CN, T₃, hRvMmain⟩ := hRvM.main
  obtain ⟨Cθ, hθ⟩ := hθ₀
  obtain ⟨CII, hII⟩ := hNII
  set N : ℝ → ℝ := fun T => (Z.N T (2 * T) : ℝ) with hNdef
  set cl : ℝ → ℝ := fun T => 1 / P.lam1 T + P.lam1 T / 3 with hcl
  set K : ℝ → ℝ := fun T => (1 + C₂ * Err T) / P.a T ^ 2 with hK
  set R₁ : ℝ → ℝ := fun T => C₁ * Real.sqrt (P.X T) / P.a T with hR₁
  set R₂ : ℝ → ℝ := fun T => cl T * ((K T - 1) * N T + K T * (|CN| * Real.log T)) with hR₂
  set B : ℝ → ℝ := fun T => θ₀ T / (P.a T * P.L T) with hBdef
  set err : ℝ → ℝ := fun T => (4 * R₁ T + R₂ T + 3 * (Assembly.NII Z T : ℝ)
      + B T * (4 + 2 * Real.sqrt (cl T * N T + R₂ T) + B T)) + 1 / (P.lam * l T) * N T with herr
  have hLtop := Assembly.tendsto_L_atTop P hlam0
  have ha1 := Assembly.tendsto_a_one P hlam0 ha
  have hapos : ∀ᶠ T in atTop, 1 / 2 ≤ P.a T := by
    filter_upwards [ha, hLtop.eventually_ge_atTop (4 * P.w)] with T h hL4
    have hw := hP.one_le_w
    have hLpos : 0 < P.L T := by linarith
    have : 2 * P.w / P.L T ≤ 1 / 2 := by rw [div_le_iff₀ hLpos]; linarith
    linarith [h.1]
  have hcE0 : Tendsto (fun T => C₂ * Err T) atTop (𝓝 0) := by
    simpa using hcalE.const_mul C₂
  have hKto : Tendsto K atTop (𝓝 1) := by
    have h1 : Tendsto (fun T => 1 + C₂ * Err T) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hcE0
    have h2 : Tendsto (fun T => P.a T ^ 2) atTop (𝓝 1) := by simpa using ha1.pow 2
    simpa [hK, Pi.div_def] using h1.div h2 one_ne_zero
  have hmain : ∀ᶠ T in atTop,
      Hfun P.lam * N T - err T ≤ (P.d T : ℝ) - RHTower.zeroSideSlack Z P T := by
    filter_upwards [hPois, hTail, hGzGp, hapos, eventually_ge_atTop T₁,
      eventually_ge_atTop T₂, eventually_ge_atTop T₃, eventually_ge_atTop (0 : ℝ),
      Assembly.eventually_l_pos, Assembly.eventually_log_nonneg,
      hcE0.eventually (eventually_gt_nhds (show (-1 : ℝ) < 0 by norm_num))]
      with T hPT hTl hGG ha2 hT₁ hT₂ hT₃ hT0 hl hlog hcE
    have hapos' : 0 < P.a T := by linarith
    have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
    have hℓ₁ := Assembly.ell1_pos hl
    have hKnn : 0 ≤ 1 + C₂ * Err T := by linarith
    have hA := seamA_spectralSlack_le_d hT0 hPT hTl hapos' hLpos
    have htr2' : P.trGtildeSq T - P.mainTr2 T ≤ C₂ * Err T * P.mainTr2 T := by
      have := htr2 T hT₂; simp only at this; rw [← mul_assoc] at this
      exact (le_abs_self _).trans this
    have htr1' : |P.trGtilde T - P.a T * P.L T * (Z.N T (2 * T) : ℝ)|
        ≤ C₁ * (P.L T * Real.sqrt (P.X T)) := by
      have := htr1 T hT₁; simpa only using this
    have hRvM' : T * ell1 T / (2 * Real.pi) ≤ N T + |CN| * Real.log T := by
      have h1 := (abs_le.mp (hRvMmain T hT₃)).1
      have h2 : CN * Real.log T ≤ |CN| * Real.log T :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlog
      have h3 : T / (2 * Real.pi) * ell1 T = T * ell1 T / (2 * Real.pi) := by ring
      simp only [hNdef]; linarith
    have hSB := Assembly.seamB hGG hapos' hLpos hℓ₁ htr1' hKnn htr2' hRvM'
    have hB₀ : 0 ≤ B T := div_nonneg hTl.theta_nonneg (mul_pos hapos' hLpos).le
    have hA' : 4 * RHLinalg.rtrace (P.hat T (Z.Gz P T)) - RHLinalg.frobSq (P.hat T (Z.Gz P T))
        - 2 * (Z.N T (2 * T) : ℝ) - 3 * (Assembly.NII Z T : ℝ)
        - θ₀ T / (P.a T * P.L T) * (4 + 2 * Real.sqrt (RHLinalg.frobSq (P.hat T (Z.Gz P T)))
          + θ₀ T / (P.a T * P.L T))
        ≤ (P.d T : ℝ) - RHTower.zeroSideSlack Z P T := by linarith
    have h := Assembly.N0star_lower_H hB₀ hA' hSB.1 hSB.2
    have hH := Assembly.Hfun_lam1_ge P T hlam0 hl
    have hN0 : 0 ≤ N T := Nat.cast_nonneg _
    have hHN : (Hfun P.lam - 1 / (P.lam * l T)) * N T ≤ Hfun (P.lam1 T) * N T :=
      mul_le_mul_of_nonneg_right hH hN0
    simp only [herr, hR₁, hR₂, hBdef, hcl, hK, hNdef] at h hHN ⊢
    linarith
  have hNtop : Tendsto N atTop atTop := Assembly.tendsto_N_atTop Z hRvM
  have o1 : R₁ =o[atTop] N := by
    have hbd : (fun T => C₁ / P.a T) =O[atTop] (fun _ => (1 : ℝ)) := by
      refine Assembly.isBigO_one_of_abs_le (C := 2 * C₁) ?_
      filter_upwards [hapos] with T ha2
      rw [abs_of_nonneg (div_nonneg hC₁.le (by linarith)), div_le_iff₀ (by linarith)]
      nlinarith
    have := Assembly.isLittleO_of_bdd_mul hbd
      (Assembly.isLittleO_N_of_isLittleO_Tl Z hRvM (Assembly.isLittleO_sqrtX_Tl P hlam0 hlam1))
    exact this.congr_left fun T => by simp only [hR₁]; ring
  have o2 : R₂ =o[atTop] N := by
    have hclO : cl =O[atTop] (fun _ => (1 : ℝ)) := by
      refine Assembly.isBigO_one_of_abs_le (C := 2 / P.lam + 1 / 3) ?_
      filter_upwards [Assembly.eventually_clam_bounds P hlam0 hlam1] with T h
      rw [abs_of_nonneg h.1]; exact h.2
    have hK1 : Tendsto (fun T => K T - 1) atTop (𝓝 0) := by simpa using hKto.sub_const 1
    have hKO : K =O[atTop] (fun _ => (1 : ℝ)) := by
      refine Assembly.isBigO_one_of_abs_le (C := 2) ?_
      filter_upwards [hKto.eventually (eventually_ge_nhds (show (0 : ℝ) < 1 by norm_num)),
        hKto.eventually (eventually_le_nhds (show (1 : ℝ) < 2 by norm_num))] with T h1 h2
      rw [abs_of_nonneg h1]; exact h2
    have i1 : (fun T => (K T - 1) * N T) =o[atTop] N := Assembly.isLittleO_of_tendsto_zero_mul hK1
    have i2 : (fun T => K T * (|CN| * Real.log T)) =o[atTop] N :=
      Assembly.isLittleO_of_bdd_mul hKO
        ((Assembly.isLittleO_N_of_isLittleO_Tl Z hRvM Assembly.isLittleO_log_Tl).const_mul_left _)
    exact Assembly.isLittleO_of_bdd_mul hclO (i1.add i2)
  have o3 : (fun T => (Assembly.NII Z T : ℝ)) =o[atTop] N := by
    have hO : (fun T => (Assembly.NII Z T : ℝ)) =O[atTop] (fun T => Real.sqrt T * l T) := by
      refine Asymptotics.IsBigO.of_bound CII ?_
      filter_upwards [hII, Assembly.eventually_l_pos] with T h hl
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity)]
      simpa [mul_assoc] using h
    exact hO.trans_isLittleO
      (Assembly.isLittleO_N_of_isLittleO_Tl Z hRvM Assembly.isLittleO_sqrt_mul_l_Tl)
  have o4 : Tendsto B atTop (𝓝 0) := by
    have hup : Tendsto (fun T => 2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) atTop (𝓝 0) := by
      simpa using (Assembly.tendsto_theta_over_L P hlam0 hlam1).const_mul (2 * |Cθ|)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [hTail, hapos, Assembly.eventually_l_pos] with T hTl ha2 hl
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      exact div_nonneg hTl.theta_nonneg (by positivity)
    · filter_upwards [hTail, hapos, Assembly.eventually_l_pos, hθ, eventually_gt_atTop (0 : ℝ)]
        with T hTl ha2 hl hθT hT0
      have hLpos : 0 < P.L T := by simp only [Params.L]; positivity
      have hapos' : 0 < P.a T := by linarith
      simp only [hBdef]
      rw [div_le_iff₀ (mul_pos hapos' hLpos)]
      calc θ₀ T ≤ Cθ * l T * T ^ (P.lam / 2 - 1) := hθT
        _ ≤ |Cθ| * l T * T ^ (P.lam / 2 - 1) := by gcongr; exact le_abs_self _
        _ = |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T := by field_simp
        _ ≤ (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (P.a T * P.L T) := by
          have : |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T) * P.L T
              = (2 * |Cθ| * (l T * T ^ (P.lam / 2 - 1) / P.L T)) * (1 / 2 * P.L T) := by ring
          rw [this]; gcongr
  have o5 := Assembly.err_isLittleO (R₁ := R₁) (R₂ := R₂)
    (NII := fun T => (Assembly.NII Z T : ℝ)) (B := B) (cl := cl)
    hNtop o1 o2 o3 o4 (Assembly.eventually_clam_bounds P hlam0 hlam1)
  have o6 : (fun T => 1 / (P.lam * l T) * N T) =o[atTop] N :=
    Assembly.isLittleO_of_tendsto_zero_mul
      (tendsto_const_nhds.div_atTop (Assembly.tendsto_l_atTop.const_mul_atTop hlam0))
  have herr_o : err =o[atTop] N := o5.add o6
  intro ε hε
  filter_upwards [herr_o.def hε, hmain] with T h1 h2
  have hN0 : 0 ≤ N T := Nat.cast_nonneg _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hN0] at h1
  have herr_le : err T ≤ ε * N T := (le_abs_self _).trans h1
  simp only [hNdef] at herr_le h2 ⊢
  linarith

/-- **Unconditional grid-dimension ceiling on `zeroSideSlack` for `ζ(s)`.**
For every sub-threshold bandwidth `λ ∈ (0, 1)` and `ε > 0`, for all sufficiently large `T`:
1. `(H(λ) − ε/2) N(T, 2T) + zeroSideSlack(λ, T) ≤ d(T)`,
2. `d(T) ≤ (λ + ε/2) N(T, 2T)`,
3. `zeroSideSlack(λ, T) ≤ (λ − H(λ) + ε) N(T, 2T) = (1/λ + 4λ/3 − 2 + ε) N(T, 2T)`. -/
theorem zeroSideSlack_eventually_le_lam_sub_Hfun {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.Hfun lam - ε / 2) * (Zeta23.Ncount T (2 * T) : ℝ) +
        RHTower.zeroSideSlack Zeta23.zetaZeroConfig (Zeta23.paramsOf Zeta23.stdProfile lam) T ≤
        ((Zeta23.paramsOf Zeta23.stdProfile lam).d T : ℝ) ∧
      ((Zeta23.paramsOf Zeta23.stdProfile lam).d T : ℝ) ≤
        (lam + ε / 2) * (Zeta23.Ncount T (2 * T) : ℝ) ∧
      RHTower.zeroSideSlack Zeta23.zetaZeroConfig (Zeta23.paramsOf Zeta23.stdProfile lam) T ≤
        (lam - Zeta23.Hfun lam + ε) * (Zeta23.Ncount T (2 * T) : ℝ) := by
  have H := Zeta23.paperInputs_zeta
  have hP := Zeta23.paramsOf_valid Zeta23.taperProfile_stdProfile h0 h1.le
  have hTr := Zeta23.PrimeSide.thm_traces hP H
  obtain ⟨hGzGp, ha, hNII, hcalE⟩ :=
    Zeta23.eventually_side_conditions Zeta23.zetaZeroConfig H _ hP
  obtain ⟨θ₀, hTail, hθ₀⟩ := Zeta23.Tail.eventually_tailPackage Zeta23.zetaZeroConfig H _ hP
  have hlow := thmA_abstract_err_spectralSlack_le_d Zeta23.zetaZeroConfig H.RvM
    (Zeta23.paramsOf Zeta23.stdProfile lam) hP h1
    (Zeta23.paramsOf Zeta23.stdProfile lam).calE hTr.toE
    (RHTower.eventually_poissonSq _ hP) θ₀ hTail hθ₀ hNII hGzGp ha hcalE (ε / 2) (by linarith)
  have hhigh := eventually_d_le_lam_mul_N Zeta23.zetaZeroConfig H.RvM
    (Zeta23.paramsOf Zeta23.stdProfile lam) h0.le (ε := ε / 2) (by linarith)
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp (hlow.and hhigh)
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨h1', h2'⟩ := hT₀ T hT
  have hlam_eq : (Zeta23.paramsOf Zeta23.stdProfile lam).lam = lam := rfl
  have hN_eq : (Zeta23.zetaZeroConfig.N T (2 * T) : ℝ) = (Zeta23.Ncount T (2 * T) : ℝ) := by
    simp [Zeta23.zetaZeroConfig]
  rw [hlam_eq, hN_eq] at h1' h2'
  refine ⟨h1', h2', by linarith⟩

/-- **Unconditional refutation of the `3/4` spectral-slack hypothesis for all `λ ∈ (0, 3/4)`.**
For every `0 < λ < 3/4`, there exists `T₀` such that for all `T ≥ T₀`,
`zeroSideSlack(λ, T) < (3/4 − H(λ)) N(T, 2T)`. Thus the spectral-slack condition required by
`zeta_three_quarters_of_spectralSlack` is unconditionally impossible for `λ < 3/4`. -/
theorem not_three_quarters_zeroSideSlack_of_lt_three_quarters
    {lam : ℝ} (h0 : 0 < lam) (h34 : lam < 3 / 4) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀,
      RHTower.zeroSideSlack Zeta23.zetaZeroConfig (Zeta23.paramsOf Zeta23.stdProfile lam) T <
        (3 / 4 - Zeta23.Hfun lam) * (Zeta23.Ncount T (2 * T) : ℝ) := by
  have h1 : lam < 1 := by linarith
  have hε : 0 < (3 / 4 - lam) / 2 := by linarith
  obtain ⟨T₁, hT₁⟩ := zeroSideSlack_eventually_le_lam_sub_Hfun h0 h1 hε
  have hNtop := Assembly.tendsto_N_atTop Zeta23.zetaZeroConfig Zeta23.riemannVonMangoldt_zeta
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp (hNtop.eventually_gt_atTop (0 : ℝ))
  refine ⟨max T₁ T₂, fun T hT => ?_⟩
  have hslack := (hT₁ T ((le_max_left _ _).trans hT)).2.2
  have hNpos : 0 < (Zeta23.Ncount T (2 * T) : ℝ) := by
    have := hT₂ T ((le_max_right _ _).trans hT)
    simpa [Zeta23.zetaZeroConfig] using this
  have hgap : (lam - Zeta23.Hfun lam + (3 / 4 - lam) / 2) * (Zeta23.Ncount T (2 * T) : ℝ) <
      (3 / 4 - Zeta23.Hfun lam) * (Zeta23.Ncount T (2 * T) : ℝ) := by
    nlinarith
  linarith

/-! ## 3. Universal Cauchy–Schwarz Lower Bound on `posSlack` from `hermNegPart` -/

/-- **Universal Cauchy–Schwarz lower bound on `posSlack` from `rtrace Q` and `rtrace (hermNegPart hQ)`.**
For any Hermitian matrix `Q : Matrix d d ℂ` with `posIndex hQ ≤ b` and
`c * b ≤ rtrace Q + rtrace (hermNegPart hQ)` (`c ≥ 0`), Cauchy–Schwarz on the positive eigenvalues
of `Q` yields `(rtrace Q + rtrace (hermNegPart hQ) − c * b)² ≤ b * posSlack hQ c`. -/
theorem posSlack_mul_ge_sq_of_rtrace {d : Type*} [Fintype d] [DecidableEq d]
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian) {b : ℕ} (hb : RHLinalg.posIndex hQ ≤ b)
    {c : ℝ} (hc : 0 ≤ c)
    (htr : c * (b : ℝ) ≤ RHLinalg.rtrace Q + RHLinalg.rtrace (RHLinalg.hermNegPart hQ)) :
    (RHLinalg.rtrace Q + RHLinalg.rtrace (RHLinalg.hermNegPart hQ) - c * (b : ℝ)) ^ 2 ≤
      (b : ℝ) * RHTower.posSlack hQ c := by
  classical
  set e := hQ.eigenvalues
  set s : Finset d := {i | 0 < e i}
  have hs_le : (#s : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hS : RHTower.posSlack hQ c = ∑ i ∈ s, (e i - c) ^ 2 := by
    rw [RHTower.posSlack, ← Finset.sum_filter]
  have htrPos : RHLinalg.rtrace Q + RHLinalg.rtrace (RHLinalg.hermNegPart hQ) =
      ∑ i ∈ s, e i := by
    have h1 : RHLinalg.rtrace Q + RHLinalg.rtrace (RHLinalg.hermNegPart hQ) =
        RHLinalg.rtrace (RHLinalg.hermPosPart hQ) := by
      linarith [RHLinalg.rtrace_sub_decomp hQ]
    rw [h1, RHLinalg.rtrace_hermPosPart,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < e i)]
    rw [Finset.sum_eq_zero (s := Finset.filter (fun i => ¬ 0 < e i) Finset.univ) (fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact posPart_eq_zero.mpr (not_lt.mp hi)), add_zero]
    exact Finset.sum_congr rfl fun i hi => by
      simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact posPart_eq_self.mpr hi.le
  have hsum_shift : ∑ i ∈ s, (e i - c) =
      RHLinalg.rtrace Q + RHLinalg.rtrace (RHLinalg.hermNegPart hQ) - c * (#s : ℝ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, htrPos]
    ring
  have hle_sum : RHLinalg.rtrace Q + RHLinalg.rtrace (RHLinalg.hermNegPart hQ) - c * (b : ℝ) ≤
      ∑ i ∈ s, (e i - c) := by
    rw [hsum_shift]
    nlinarith
  have hsq : (RHLinalg.rtrace Q + RHLinalg.rtrace (RHLinalg.hermNegPart hQ) - c * (b : ℝ)) ^ 2 ≤
      (∑ i ∈ s, (e i - c)) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hle_sum 2
  have hCS : (∑ i ∈ s, (e i - c)) ^ 2 ≤ (#s : ℝ) * ∑ i ∈ s, (e i - c) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hmul : (#s : ℝ) * ∑ i ∈ s, (e i - c) ^ 2 ≤ (b : ℝ) * RHTower.posSlack hQ c := by
    rw [← hS]
    exact mul_le_mul_of_nonneg_right hs_le (RHTower.posSlack_nonneg hQ c)
  linarith

/-- **Quadratic amplification of off-line spectral slack at `c = 2`.**
Whenever `posIndex hQ ≤ b`, `2b ≤ rtrace Q` (trace conservation on `b` off-line pairs), and
`2 η b ≤ rtrace (hermNegPart hQ)` (`η ≥ 0`), the positive-spectrum slack satisfies
`4 η² b ≤ posSlack hQ 2` and the total off-line spectral slack satisfies
`4 b η (1 + η) ≤ 2 rtrace (hermNegPart hQ) + posSlack hQ 2`. -/
theorem offLine_slack_ge_of_rtrace_hermNegPart {d : Type*} [Fintype d] [DecidableEq d]
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian) {b : ℕ} (hb : RHLinalg.posIndex hQ ≤ b)
    {η : ℝ} (hη : 0 ≤ η) (htrQ : 2 * (b : ℝ) ≤ RHLinalg.rtrace Q)
    (htrQm : 2 * η * (b : ℝ) ≤ RHLinalg.rtrace (RHLinalg.hermNegPart hQ)) :
    4 * η ^ 2 * (b : ℝ) ≤ RHTower.posSlack hQ 2 ∧
      4 * (b : ℝ) * η * (1 + η) ≤
        2 * RHLinalg.rtrace (RHLinalg.hermNegPart hQ) + RHTower.posSlack hQ 2 := by
  rcases Nat.eq_zero_or_pos b with rfl | hbpos
  · simp only [Nat.cast_zero, mul_zero, zero_mul]
    refine ⟨RHTower.posSlack_nonneg hQ 2, ?_⟩
    have h1 := RHTower.rtrace_hermNegPart_nonneg hQ
    have h2 := RHTower.posSlack_nonneg hQ 2
    linarith
  · have hb_pos : (0 : ℝ) < (b : ℝ) := Nat.cast_pos.mpr hbpos
    have htr : 2 * (b : ℝ) ≤ RHLinalg.rtrace Q + RHLinalg.rtrace (RHLinalg.hermNegPart hQ) := by
      have : 0 ≤ 2 * η * (b : ℝ) := by positivity
      linarith
    have hcs := posSlack_mul_ge_sq_of_rtrace hQ hb (by norm_num : (0 : ℝ) ≤ 2) htr
    have hlow : 2 * η * (b : ℝ) ≤
        RHLinalg.rtrace Q + RHLinalg.rtrace (RHLinalg.hermNegPart hQ) - 2 * (b : ℝ) := by
      linarith
    have hsq : (2 * η * (b : ℝ)) ^ 2 ≤
        (RHLinalg.rtrace Q + RHLinalg.rtrace (RHLinalg.hermNegPart hQ) - 2 * (b : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hlow 2
    have hmul : (b : ℝ) * (4 * η ^ 2 * (b : ℝ)) ≤ (b : ℝ) * RHTower.posSlack hQ 2 := by
      calc (b : ℝ) * (4 * η ^ 2 * (b : ℝ)) = (2 * η * (b : ℝ)) ^ 2 := by ring
        _ ≤ (b : ℝ) * RHTower.posSlack hQ 2 := hsq.trans hcs
    have hpos : 4 * η ^ 2 * (b : ℝ) ≤ RHTower.posSlack hQ 2 :=
      le_of_mul_le_mul_left hmul hb_pos
    exact ⟨hpos, by linarith⟩

/-! ## 4. Hyperbolic Displaced-Pair Block Calculus and the Three Exact Thresholds at `κ = 4/3` -/

@[simp]
private lemma star_unitVec_apply {d : Type*} [DecidableEq d] (z k : d) :
    (starRingEnd ℂ) (unitVec z k) = unitVec z k := by
  simp only [unitVec]
  split_ifs <;> simp

/-- The hyperbolic displaced-pair `ZeroBlockData` configuration with `s₁` simple critical-line zeros
and `p` reflected off-line pairs whose real and imaginary evaluation components have amplitudes `α`
and `β` on an orthonormal probe frame of size `s₁ + p + p`. At `α = 1, β = 0`, this recovers the
coalesced-pair model; for `β ≠ 0` and `α² − β² = 1`, each off-line pair has positive eigenvalue
`2α²`, negative eigenvalue `−2β² < 0`, and conserved trace `2(α² − β²) = 2`. -/
def displacedPairBlockData (s₁ p : ℕ) (α β : ℝ) :
    ZeroBlockData (Fin s₁ ⊕ (Fin p ⊕ Fin p)) (Fin s₁ ⊕ (Fin p ⊕ Fin p)) where
  m _ := 1
  one_le_m _ := le_rfl
  v := Sum.elim (fun i => unitVec (Sum.inl i))
    (Sum.elim
      (fun j k => (α : ℂ) * unitVec (Sum.inr (Sum.inl j)) k +
        Complex.I * (β : ℂ) * unitVec (Sum.inr (Sum.inr j)) k)
      (fun j k => (α : ℂ) * unitVec (Sum.inr (Sum.inl j)) k -
        Complex.I * (β : ℂ) * unitVec (Sum.inr (Sum.inr j)) k))
  σ := Sum.map id (Equiv.sumComm (Fin p) (Fin p))
  σ_invol z := by rcases z with i | (j | j) <;> rfl
  m_σ _ := rfl
  v_σ z := by
    ext k
    rcases z with i | (j | j)
    · simp [Pi.star_apply, RCLike.star_def]
    · simp only [Sum.map_inr, Equiv.sumComm_apply, Sum.swap_inl, Sum.elim_inr, Sum.elim_inl,
        Pi.star_apply, RCLike.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I,
        star_unitVec_apply]
      ring
    · simp only [Sum.map_inr, Equiv.sumComm_apply, Sum.swap_inr, Sum.elim_inr, Sum.elim_inl,
        Pi.star_apply, RCLike.star_def, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I,
        star_unitVec_apply]
      ring

/-- Canonical off-line pair representatives for `displacedPairBlockData s₁ p α β`. -/
def displacedPairReps (s₁ p : ℕ) (α β : ℝ) : (displacedPairBlockData s₁ p α β).PairReps where
  R := Finset.univ.map ⟨fun j : Fin p => Sum.inr (Sum.inl j),
    fun _ _ h => Sum.inl.inj (Sum.inr.inj h)⟩
  off z hz := by
    rcases Finset.mem_map.mp hz with ⟨j, _, rfl⟩
    simp [displacedPairBlockData]
  σ_not_mem z hz hσ := by
    rcases Finset.mem_map.mp hz with ⟨j, _, rfl⟩
    rcases Finset.mem_map.mp hσ with ⟨j', _, hj'⟩
    simp [displacedPairBlockData] at hj'
  cover z hz := by
    rcases z with i | (j | j)
    · exact False.elim (hz rfl)
    · exact Or.inl (Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    · exact Or.inr (Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩)

/-- The diagonal Gram matrix `diag(1, …, 1, 2α², …, 2α², −2β², …, −2β²)` of
`displacedPairBlockData s₁ p α β`. -/
def displacedPairDiag (s₁ p : ℕ) (α β : ℝ) :
    Matrix (Fin s₁ ⊕ (Fin p ⊕ Fin p)) (Fin s₁ ⊕ (Fin p ⊕ Fin p)) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ : Fin s₁ => (1 : ℂ))
    (Sum.elim (fun _ : Fin p => ((2 * α ^ 2 : ℝ) : ℂ))
      (fun _ : Fin p => ((-2 * β ^ 2 : ℝ) : ℂ))))

/-- The diagonal off-line block matrix `diag(0, …, 0, 2α², …, 2α², −2β², …, −2β²)` of
`displacedPairBlockData s₁ p α β`. -/
def displacedPairQDiag (s₁ p : ℕ) (α β : ℝ) :
    Matrix (Fin s₁ ⊕ (Fin p ⊕ Fin p)) (Fin s₁ ⊕ (Fin p ⊕ Fin p)) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ : Fin s₁ => (0 : ℂ))
    (Sum.elim (fun _ : Fin p => ((2 * α ^ 2 : ℝ) : ℂ))
      (fun _ : Fin p => ((-2 * β ^ 2 : ℝ) : ℂ))))

@[simp]
private lemma unitVec_inl_Same {α β : Type*} [DecidableEq α] [DecidableEq β] (x y : α) :
    unitVec (Sum.inl x : α ⊕ β) (Sum.inl y) = unitVec x y := by
  simp [unitVec]

@[simp]
private lemma unitVec_inr_Same {α β : Type*} [DecidableEq α] [DecidableEq β] (x y : β) :
    unitVec (Sum.inr x : α ⊕ β) (Sum.inr y) = unitVec x y := by
  simp [unitVec]

@[simp]
private lemma unitVec_inl_Diff {α β : Type*} [DecidableEq α] [DecidableEq β] (x : α) (y : β) :
    unitVec (Sum.inl x : α ⊕ β) (Sum.inr y) = 0 := by
  simp [unitVec]

@[simp]
private lemma unitVec_inr_Diff {α β : Type*} [DecidableEq α] [DecidableEq β] (x : β) (y : α) :
    unitVec (Sum.inr x : α ⊕ β) (Sum.inl y) = 0 := by
  simp [unitVec]

private lemma unitVec_mul_eq {d : Type*} [DecidableEq d] (z k l : d) :
    unitVec z k * unitVec z l = if z = k then (if k = l then 1 else 0) else 0 := by
  simp only [unitVec]
  by_cases hzk : z = k
  · subst hzk
    by_cases hkl : z = l
    · subst hkl; simp
    · have hlk : l ≠ z := Ne.symm hkl
      simp [hkl, hlk]
  · have hkz : k ≠ z := Ne.symm hzk
    simp [hzk, hkz]

/-- The full Gram matrix `blockA` of `displacedPairBlockData s₁ p α β` is `displacedPairDiag s₁ p α β`. -/
theorem blockA_displacedPairBlockData (s₁ p : ℕ) (α β : ℝ) :
    (displacedPairBlockData s₁ p α β).blockA = displacedPairDiag s₁ p α β := by
  ext k l
  rw [ZeroBlockData.blockA_apply]
  simp only [displacedPairBlockData, Nat.cast_one, one_mul, displacedPairDiag, diagonal_apply]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  simp only [Sum.elim_inl, Sum.elim_inr]
  have hpair : ∀ j : Fin p,
      (((α : ℂ) * unitVec (Sum.inr (Sum.inl j)) k +
          Complex.I * (β : ℂ) * unitVec (Sum.inr (Sum.inr j)) k) *
        ((α : ℂ) * unitVec (Sum.inr (Sum.inl j)) l +
          Complex.I * (β : ℂ) * unitVec (Sum.inr (Sum.inr j)) l) +
      (((α : ℂ) * unitVec (Sum.inr (Sum.inl j)) k -
          Complex.I * (β : ℂ) * unitVec (Sum.inr (Sum.inr j)) k) *
        ((α : ℂ) * unitVec (Sum.inr (Sum.inl j)) l -
          Complex.I * (β : ℂ) * unitVec (Sum.inr (Sum.inr j)) l))) =
      ((2 * α ^ 2 : ℝ) : ℂ) *
        (unitVec (Sum.inr (Sum.inl j) : Fin s₁ ⊕ (Fin p ⊕ Fin p)) k *
          unitVec (Sum.inr (Sum.inl j) : Fin s₁ ⊕ (Fin p ⊕ Fin p)) l) +
      ((-2 * β ^ 2 : ℝ) : ℂ) *
        (unitVec (Sum.inr (Sum.inr j) : Fin s₁ ⊕ (Fin p ⊕ Fin p)) k *
          unitVec (Sum.inr (Sum.inr j) : Fin s₁ ⊕ (Fin p ⊕ Fin p)) l) := fun j => by
    push_cast
    calc _ = 2 * (α : ℂ) ^ 2 *
          (unitVec (Sum.inr (Sum.inl j)) k * unitVec (Sum.inr (Sum.inl j)) l) +
        2 * Complex.I ^ 2 * (β : ℂ) ^ 2 *
          (unitVec (Sum.inr (Sum.inr j)) k * unitVec (Sum.inr (Sum.inr j)) l) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  simp_rw [hpair, Finset.sum_add_distrib]
  rcases k with ik | (jk | wk) <;> rcases l with il | (jl | wl) <;>
    simp [unitVec_mul_eq, Finset.sum_ite_eq']

/-- The off-line block matrix `blockQ 1` of `displacedPairBlockData s₁ p α β` is
`displacedPairQDiag s₁ p α β`. -/
theorem blockQ_one_displacedPairBlockData (s₁ p : ℕ) (α β : ℝ) :
    (displacedPairBlockData s₁ p α β).blockQ 1 = displacedPairQDiag s₁ p α β := by
  have hon : (displacedPairBlockData s₁ p α β).onLine =
      Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext z
    simp only [ZeroBlockData.onLine, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    rcases z with i | (j | j) <;> simp [displacedPairBlockData]
  unfold ZeroBlockData.blockQ ZeroBlockData.onPart
  rw [inv_one, Complex.ofReal_one, one_smul, blockA_displacedPairBlockData, hon]
  ext k l
  simp only [Matrix.sub_apply, Matrix.sum_apply, Finset.sum_map, Function.Embedding.coeFn_mk,
    displacedPairBlockData, Nat.cast_one, one_smul, vecMulVec_apply, Sum.elim_inl,
    displacedPairDiag, displacedPairQDiag, diagonal_apply]
  rcases k with ik | (jk | wk) <;> rcases l with il | (jl | wl) <;>
    simp [unitVec_mul_eq, Finset.sum_ite_eq']

/-- Counting invariants of `displacedPairBlockData s₁ p α β`: `s₁` simple critical zeros, `0`
multiple critical zeros, `p` off-line pairs, and total zero count `Ncount = s₁ + 2p`. -/
theorem counts_displacedPairBlockData (s₁ p : ℕ) (α β : ℝ) :
    let D := displacedPairBlockData s₁ p α β
    D.s₁ = s₁ ∧ D.s₂ = 0 ∧ D.Non = s₁ ∧ D.Ncount = s₁ + 2 * p ∧
      (displacedPairReps s₁ p α β).p = p := by
  dsimp only
  have hS1 : (displacedPairBlockData s₁ p α β).S₁ =
      Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext z
    simp only [ZeroBlockData.S₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    rcases z with i | (j | j) <;> simp [displacedPairBlockData]
  have hS2 : (displacedPairBlockData s₁ p α β).S₂ = ∅ := by
    ext z
    simp [ZeroBlockData.S₂, displacedPairBlockData]
  have hon : (displacedPairBlockData s₁ p α β).onLine =
      Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext z
    simp only [ZeroBlockData.onLine, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
    rcases z with i | (j | j) <;> simp [displacedPairBlockData]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold ZeroBlockData.s₁; rw [hS1, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  · unfold ZeroBlockData.s₂; rw [hS2, Finset.card_empty]
  · unfold ZeroBlockData.Non
    rw [hon, Finset.sum_map]
    simp [displacedPairBlockData]
  · unfold ZeroBlockData.Ncount
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp [displacedPairBlockData, two_mul]
  · unfold ZeroBlockData.PairReps.p displacedPairReps
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

/-- Trace of `displacedPairDiag s₁ p α β`: `tr Â = s₁ + 2p α² − 2p β²`. -/
theorem rtrace_displacedPairDiag (s₁ p : ℕ) (α β : ℝ) :
    RHLinalg.rtrace (displacedPairDiag s₁ p α β) =
      (s₁ : ℝ) + 2 * (p : ℝ) * α ^ 2 - 2 * (p : ℝ) * β ^ 2 := by
  unfold RHLinalg.rtrace displacedPairDiag
  rw [trace_diagonal, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, RCLike.re_to_complex, add_re, mul_re, natCast_re, ofReal_re, natCast_im,
    ofReal_im, mul_zero, sub_zero, one_re]
  ring

/-- Trace of `displacedPairQDiag s₁ p α β`: `tr Q = 2p α² − 2p β²`. -/
theorem rtrace_displacedPairQDiag (s₁ p : ℕ) (α β : ℝ) :
    RHLinalg.rtrace (displacedPairQDiag s₁ p α β) =
      2 * (p : ℝ) * α ^ 2 - 2 * (p : ℝ) * β ^ 2 := by
  unfold RHLinalg.rtrace displacedPairQDiag
  rw [trace_diagonal, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, RCLike.re_to_complex, add_re, mul_re, natCast_re, ofReal_re, natCast_im,
    ofReal_im, mul_zero, sub_zero, zero_re]
  ring

/-- Squared Frobenius norm of `displacedPairDiag s₁ p α β`:
`‖Â‖_F² = s₁ + 4p α⁴ + 4p β⁴`. -/
theorem frobSq_displacedPairDiag (s₁ p : ℕ) (α β : ℝ) :
    RHLinalg.frobSq (displacedPairDiag s₁ p α β) =
      (s₁ : ℝ) + 4 * (p : ℝ) * α ^ 4 + 4 * (p : ℝ) * β ^ 4 := by
  have hd : (displacedPairDiag s₁ p α β)ᴴ = displacedPairDiag s₁ p α β := by
    ext i j
    simp only [displacedPairDiag, conjTranspose_apply, diagonal_apply]
    by_cases hij : j = i
    · subst hij
      rcases j with _ | (_ | _) <;> simp [RCLike.star_def, Complex.conj_ofReal]
    · have hji : i ≠ j := Ne.symm hij
      simp [hij, hji]
  unfold RHLinalg.frobSq
  rw [hd]
  unfold displacedPairDiag
  rw [diagonal_mul_diagonal, trace_diagonal, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, map_add, RCLike.re_to_complex,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- Whenever `p > 0` and `β ≠ 0`, `displacedPairQDiag s₁ p α β` has a strictly negative diagonal
entry `−2β² < 0`, so it is not positive semidefinite and its negative-part credit
`2 tr(Q₋)` is strictly positive. -/
theorem negPart_credit_pos_displacedPairQDiag (s₁ : ℕ) {p : ℕ} (hp : 0 < p) (α : ℝ)
    {β : ℝ} (hβ : β ≠ 0) :
    ¬ (displacedPairQDiag s₁ p α β).PosSemidef ∧
      ∀ hQh : (displacedPairQDiag s₁ p α β).IsHermitian,
        0 < 2 * RHLinalg.rtrace (RHLinalg.hermNegPart hQh) := by
  have hnot : ¬ (displacedPairQDiag s₁ p α β).PosSemidef := by
    intro hpsd
    let idx : Fin s₁ ⊕ (Fin p ⊕ Fin p) := Sum.inr (Sum.inr ⟨0, hp⟩)
    have hdiag := RCLike.nonneg_iff.mp (hpsd.diag_nonneg (i := idx))
    have hentry : displacedPairQDiag s₁ p α β idx idx = ((-2 * β ^ 2 : ℝ) : ℂ) := rfl
    rw [hentry] at hdiag
    simp only [ofReal_re] at hdiag
    have hβ2 : 0 < β ^ 2 := sq_pos_of_ne_zero hβ
    linarith [hdiag.1]
  refine ⟨hnot, fun hQh => ?_⟩
  by_contra hle
  have hnn : 0 ≤ RHLinalg.rtrace (RHLinalg.hermNegPart hQh) := RHTower.rtrace_hermNegPart_nonneg hQh
  have htr0 : RHLinalg.rtrace (RHLinalg.hermNegPart hQh) = 0 := by linarith
  rw [RHLinalg.rtrace_hermNegPart] at htr0
  have hall : ∀ i, (hQh.eigenvalues i)⁻ = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => negPart_nonneg _)).mp htr0 i (Finset.mem_univ i)
  have heig : ∀ i, 0 ≤ hQh.eigenvalues i := fun i => negPart_eq_zero.mp (hall i)
  exact hnot ((RHLinalg.specMap_id hQh) ▸ (RHLinalg.specMap_posSemidef hQh heig))

/-- The off-line block matrix `(displacedPairBlockData s₁ p α β).blockQ 1` is Hermitian. -/
theorem isHermitian_blockQ_one_displacedPairBlockData (s₁ p : ℕ) (α β : ℝ) :
    ((displacedPairBlockData s₁ p α β).blockQ 1).IsHermitian := by
  let D := displacedPairBlockData s₁ p α β
  let R := displacedPairReps s₁ p α β
  have hQeq : D.blockQ 1 = D.rePart R - D.imPart R := by
    rw [ZeroBlockData.blockQ_eq _ R, inv_one, Complex.ofReal_one, one_smul]
  rw [hQeq]
  exact (D.rePart_posSemidef R).isHermitian.sub (D.imPart_posSemidef R).isHermitian

/-- **General Displaced-Pair Theorem at `κ = 4/3`.**
For any `s₁, p : ℕ` (`p > 0`) and `α, β : ℝ` (`β ≠ 0`, `α² − β² = 1`) such that
`s₁ + 4p α⁴ + 4p β⁴ = (4/3)(s₁ + 2p)` and `s₁ < (3/4)(s₁ + 2p)`, the concrete `ZeroBlockData`
configuration `D = displacedPairBlockData s₁ p α β` satisfies:
1. `tr(D.blockA) = D.Ncount`,
2. `‖D.blockA‖_F² = (4/3) D.Ncount`,
3. `¬ (D.blockQ 1).PosSemidef` and `0 < 2 tr(Q₋)` (strictly positive off-line negative-part credit),
4. `D.s₁ < (3/4) D.Ncount` and `totalSlack P Q 2 < (1/12) D.Ncount`. -/
theorem displacedPairBlockData_below_three_quarters (s₁ : ℕ) {p : ℕ} (hp : 0 < p) {α β : ℝ}
    (hβ : β ≠ 0) (hαβ : α ^ 2 - β ^ 2 = 1)
    (hfrob_eq : (s₁ : ℝ) + 4 * (p : ℝ) * α ^ 4 + 4 * (p : ℝ) * β ^ 4 =
      (4 / 3 : ℝ) * ((s₁ : ℝ) + 2 * (p : ℝ)))
    (hs1_lt : (s₁ : ℝ) < (3 / 4 : ℝ) * ((s₁ : ℝ) + 2 * (p : ℝ))) :
    let D := displacedPairBlockData s₁ p α β
    let hP := D.blockP_posSemidef (by norm_num : (0 : ℝ) < 1)
    let hQ := isHermitian_blockQ_one_displacedPairBlockData s₁ p α β
    RHLinalg.rtrace D.blockA = (D.Ncount : ℝ) ∧
      RHLinalg.frobSq D.blockA = (4 / 3 : ℝ) * (D.Ncount : ℝ) ∧
      ¬ (D.blockQ 1).PosSemidef ∧
      0 < 2 * RHLinalg.rtrace (RHLinalg.hermNegPart hQ) ∧
      (D.s₁ : ℝ) < (3 / 4 : ℝ) * (D.Ncount : ℝ) ∧
      totalSlack hP.isHermitian hQ 2 < (1 / 12 : ℝ) * (D.Ncount : ℝ) := by
  dsimp only
  set D := displacedPairBlockData s₁ p α β
  set R := displacedPairReps s₁ p α β
  set hP := D.blockP_posSemidef (by norm_num : (0 : ℝ) < 1)
  set hQ := isHermitian_blockQ_one_displacedPairBlockData s₁ p α β
  have hcounts := counts_displacedPairBlockData s₁ p α β
  have hN : (D.Ncount : ℝ) = (s₁ : ℝ) + 2 * (p : ℝ) := by
    rw [hcounts.2.2.2.1]; push_cast; ring
  have hA := blockA_displacedPairBlockData s₁ p α β
  have hQeq := blockQ_one_displacedPairBlockData s₁ p α β
  have htr : RHLinalg.rtrace D.blockA = (D.Ncount : ℝ) := by
    rw [hA, rtrace_displacedPairDiag, hN]
    calc (s₁ : ℝ) + 2 * (p : ℝ) * α ^ 2 - 2 * (p : ℝ) * β ^ 2
        = (s₁ : ℝ) + 2 * (p : ℝ) * (α ^ 2 - β ^ 2) := by ring
      _ = (s₁ : ℝ) + 2 * (p : ℝ) := by rw [hαβ]; ring
  have hfrob : RHLinalg.frobSq D.blockA = (4 / 3 : ℝ) * (D.Ncount : ℝ) := by
    rw [hA, frobSq_displacedPairDiag, hN, hfrob_eq]
  have hneg := negPart_credit_pos_displacedPairQDiag s₁ hp α hβ
  have hnot_psd : ¬ (D.blockQ 1).PosSemidef := hQeq.symm ▸ hneg.1
  have hcred_pos : 0 < 2 * RHLinalg.rtrace (RHLinalg.hermNegPart hQ) := by
    by_contra hle
    have hnn : 0 ≤ RHLinalg.rtrace (RHLinalg.hermNegPart hQ) := RHTower.rtrace_hermNegPart_nonneg hQ
    have htr0 : RHLinalg.rtrace (RHLinalg.hermNegPart hQ) = 0 := by linarith
    rw [RHLinalg.rtrace_hermNegPart] at htr0
    have hall : ∀ i, (hQ.eigenvalues i)⁻ = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => negPart_nonneg _)).mp htr0 i (Finset.mem_univ i)
    have heig : ∀ i, 0 ≤ hQ.eigenvalues i := fun i => negPart_eq_zero.mp (hall i)
    exact hnot_psd ((RHLinalg.specMap_id hQ) ▸ (RHLinalg.specMap_posSemidef hQ heig))
  have hs1 : (D.s₁ : ℝ) < (3 / 4 : ℝ) * (D.Ncount : ℝ) := by
    rw [hcounts.1, hN]; exact hs1_lt
  have hdec : D.blockA = D.blockP 1 + D.blockQ 1 := by
    have h := D.blockP_add_blockQ 1
    rw [inv_one, Complex.ofReal_one, one_smul] at h
    exact h.symm
  have hrank : (D.blockP 1).rank ≤ s₁ := by
    have hr := D.rank_blockP_le (by norm_num : (0 : ℝ) < 1)
    rw [hcounts.1, hcounts.2.1, add_zero] at hr
    exact hr
  have hpos : RHLinalg.posIndex hQ ≤ p := by
    have hp1 : RHLinalg.posIndex
        ((D.rePart_posSemidef R).isHermitian.sub (D.imPart_posSemidef R).isHermitian) ≤ R.p :=
      (ZeroSide.posIndex_sub_le_rank (D.rePart_posSemidef R) (D.imPart_posSemidef R)).trans
        (D.rank_rePart_le R)
    have hQeq' : D.blockQ 1 = D.rePart R - D.imPart R := by
      rw [ZeroBlockData.blockQ_eq _ R, inv_one, Complex.ofReal_one, one_smul]
    rw [hcounts.2.2.2.2] at hp1
    exact (ZeroBlockData.posIndex_congr hQ _ hQeq').trans_le hp1
  have htrP : RHLinalg.rtrace (D.blockP 1) ≤ (s₁ : ℝ) := by
    have htrQ : RHLinalg.rtrace (D.blockQ 1) = 2 * (p : ℝ) := by
      rw [hQeq, rtrace_displacedPairQDiag]
      calc 2 * (p : ℝ) * α ^ 2 - 2 * (p : ℝ) * β ^ 2 = 2 * (p : ℝ) * (α ^ 2 - β ^ 2) := by ring
        _ = 2 * (p : ℝ) := by rw [hαβ]; ring
    have htrA : RHLinalg.rtrace D.blockA =
        RHLinalg.rtrace (D.blockP 1) + RHLinalg.rtrace (D.blockQ 1) := by
      rw [hdec, RHLinalg.rtrace_add]
    linarith
  have hcount : (s₁ : ℝ) + 2 * (p : ℝ) ≤ (D.Ncount : ℝ) := hN.symm.le
  have hcore := RHTower.zeroside_rank_core_slack hdec hP hQ hrank hpos htrP hcount
  have hslack_lt : totalSlack hP.isHermitian hQ 2 < (1 / 12 : ℝ) * (D.Ncount : ℝ) := by
    change 2 * RHLinalg.rtrace (RHLinalg.hermNegPart hQ) + RHTower.posSlack hQ 2 +
        RHTower.onSlack hP.isHermitian hQ 2 < (1 / 12 : ℝ) * (D.Ncount : ℝ)
    linarith [hcore, htr, hfrob, hN, hs1_lt]
  exact ⟨htr, hfrob, hnot_psd, hcred_pos, hs1, hslack_lt⟩

/-- **Macroscopic Displaced-Pair Counterexample at `κ = 4/3`.**
At the Pythagorean rational displacement `α = 41/40, β = 9/40` (`α² − β² = 1`,
`η = β² = 81/1600 > 0`) with `s₁ = 3376966` simple critical zeros and `p = 640000` off-line pairs
(`N = s₁ + 2p = 4656966`), the concrete `ZeroBlockData` configuration
`D = displacedPairBlockData 3376966 640000 (41/40) (9/40)` has `tr(D.blockA) = N`,
`‖D.blockA‖_F² = (4/3) N`, and strictly positive off-line negative-part credit `0 < 2 tr(Q₋)`
(`¬ (D.blockQ 1).PosSemidef`), yet `D.s₁ < (3/4) N` and `totalSlack P Q 2 < (1/12) N`. -/
theorem macroscopic_displacedPair_counterexample_at_four_thirds :
    let D := displacedPairBlockData 3376966 640000 (41 / 40) (9 / 40)
    let hP := D.blockP_posSemidef (by norm_num : (0 : ℝ) < 1)
    let hQ := isHermitian_blockQ_one_displacedPairBlockData 3376966 640000 (41 / 40) (9 / 40)
    RHLinalg.rtrace D.blockA = (D.Ncount : ℝ) ∧
      RHLinalg.frobSq D.blockA = (4 / 3 : ℝ) * (D.Ncount : ℝ) ∧
      ¬ (D.blockQ 1).PosSemidef ∧
      0 < 2 * RHLinalg.rtrace (RHLinalg.hermNegPart hQ) ∧
      (D.s₁ : ℝ) < (3 / 4 : ℝ) * (D.Ncount : ℝ) ∧
      totalSlack hP.isHermitian hQ 2 < (1 / 12 : ℝ) * (D.Ncount : ℝ) :=
  displacedPairBlockData_below_three_quarters 3376966 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- **The Three Exact Macroscopic Displacement Thresholds at `κ = 4/3`.**
For a configuration of `s₁ = N − 2p` simple critical zeros and `p` hyperbolic displaced off-line
pairs with orthogonal components `‖x‖² = 1 + η` and `‖y‖² = η` (`η ≥ 0`) satisfying the exact
bandwidth-one Frobenius identity `2p (1 + 2η)² = (1/3) N` (`N > 0`):
1. The off-line spectral slack `2 tr(Q₋) + posSlack = 4p η (1 + η)` and full spectral slack
   `totalSlack = 4p η (1 + 2η)` satisfy the exact conservation law
   `(2/3) N + 4p η (1 + 2η) = (N − 2p) − 4p η`;
2. **Threshold I (True critical-line proportion `≥ 3/4`):**
   `N − 2p ≥ (3/4) N ↔ 4 / 3 ≤ (1 + 2 * η) ^ 2`;
3. **Threshold II (Full spectral slack `≥ 1/12`):**
   `4 * p * η * (1 + 2 * η) ≥ (1 / 12) * N ↔ 1 / 6 ≤ η`;
4. **Threshold III (Off-line spectral slack alone `≥ 1/12`):**
   `4 * p * η * (1 + η) ≥ (1 / 12) * N ↔ 2 ≤ (1 + 2 * η) ^ 2`. -/
theorem hyperbolic_displacedPair_three_thresholds_at_four_thirds
    {N p η : ℝ} (hN : 0 < N) (hη : 0 ≤ η)
    (hfrob : 2 * p * (1 + 2 * η) ^ 2 = (1 / 3 : ℝ) * N) :
    (2 / 3 : ℝ) * N + 4 * p * η * (1 + 2 * η) = (N - 2 * p) - 4 * p * η ∧
      ((3 / 4 : ℝ) * N ≤ N - 2 * p ↔ (4 / 3 : ℝ) ≤ (1 + 2 * η) ^ 2) ∧
      ((1 / 12 : ℝ) * N ≤ 4 * p * η * (1 + 2 * η) ↔ (1 / 6 : ℝ) ≤ η) ∧
      ((1 / 12 : ℝ) * N ≤ 4 * p * η * (1 + η) ↔ 2 ≤ (1 + 2 * η) ^ 2) := by
  have h12 : 0 < 1 + 2 * η := by linarith
  have h12_sq : 0 < (1 + 2 * η) ^ 2 := sq_pos_of_pos h12
  have hp_pos : 0 < p := by
    by_contra hle
    have : 2 * p * (1 + 2 * η) ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) h12_sq.le
    linarith
  have hN_eq : N = 6 * p * (1 + 2 * η) ^ 2 := by linarith
  refine ⟨by rw [hN_eq]; ring, ?_, ?_, ?_⟩
  · constructor <;> intro h
    · have h1 : 8 * p ≤ 6 * p * (1 + 2 * η) ^ 2 := by linarith
      nlinarith
    · nlinarith
  · constructor <;> intro h
    · have h1 : p * (1 + 2 * η) * (6 * η - 1) ≥ 0 := by
        calc p * (1 + 2 * η) * (6 * η - 1)
            = 2 * (4 * p * η * (1 + 2 * η) - (1 / 12 : ℝ) * (6 * p * (1 + 2 * η) ^ 2)) := by ring
          _ ≥ 0 := by linarith
      have h2 : 0 < p * (1 + 2 * η) := mul_pos hp_pos h12
      nlinarith
    · have h1 : 0 ≤ p * (1 + 2 * η) * (6 * η - 1) :=
        mul_nonneg (mul_nonneg hp_pos.le h12.le) (by linarith)
      have hid : 4 * p * η * (1 + 2 * η) - (1 / 12 : ℝ) * N =
          (p * (1 + 2 * η) * (6 * η - 1)) / 2 := by
        rw [hN_eq]; ring
      linarith
  · constructor <;> intro h
    · have h1 : p * ((1 + 2 * η) ^ 2 - 2) ≥ 0 := by
        calc p * ((1 + 2 * η) ^ 2 - 2)
            = 2 * (4 * p * η * (1 + η) - (1 / 12 : ℝ) * (6 * p * (1 + 2 * η) ^ 2)) := by ring
          _ ≥ 0 := by linarith
      nlinarith
    · have h1 : 0 ≤ p * ((1 + 2 * η) ^ 2 - 2) := mul_nonneg hp_pos.le (by linarith)
      have hid : 4 * p * η * (1 + η) - (1 / 12 : ℝ) * N =
          (p * ((1 + 2 * η) ^ 2 - 2)) / 2 := by
        rw [hN_eq]; ring
      linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
