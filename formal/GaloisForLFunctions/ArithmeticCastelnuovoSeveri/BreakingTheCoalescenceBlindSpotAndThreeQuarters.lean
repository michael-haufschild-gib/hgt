import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheTwoThirdsConstantIsPairCorrelation
import GaloisForLFunctions.RHTower.RankTraceNegativePartCredit
import GaloisForLFunctions.RHTower.RankTraceSpectralSlack
import GaloisForLFunctions.RHTower.Zeta23TheoremASpectralSlack
import GaloisForLFunctions.RHTower.ZetaThreeQuartersOfPrimeSurplus
import GaloisForLFunctions.SquareRootThreshold.DoubleWindowMinApertureAndPairCorrelationExchange

/-!
# Breaking the Coalescence Blind Spot and Lowering `κ` to `5/4`: The Two Routes to `3/4` (`75%`)

`TheTwoThirdsConstantIsPairCorrelation` established that at the sub-threshold pair-correlation value
`κ = 4/3` (`λ = 1`), a lower bound valid for every normalized abstract `ZeroBlockData` and depending
only on `Â = P + Q` and `N` is at most `(2 − κ)N = (2/3)N` on the coordinate extremizer because
`doubleZeroBlockData (4k) k` (all `6k` zeros on the critical line, `4k` simple and `k` double) and
`coalescedPairBlockData (4k) k` (`4k` simple critical zeros and `k` coalesced off-line pairs) share
the identical summed matrix `Â = extremalDiag (4k) k`. These are abstract coordinate frames;
no realization by the prescribed zeta evaluation family is asserted. The barrier does not
restrict functionals whose validity uses additional arithmetic properties of that family.

This module proves exact finite-matrix identities and sufficient conditions for a critical-line
proportion of at least `3/4` (`75%`) along two complementary routes. The spectral-slack lower
bound and prime-surplus upper bound needed for the arithmetic conclusion remain premises:

1. **Route I: Breaking the blind spot between double critical zeros and off-line pairs on the zero side.**
   Although the summed matrix `Â = P + Q` is identical for `doubleZeroBlockData s₁ d₂` and
   `coalescedPairBlockData s₁ d₂`, the unsplit zero-side decomposition `(P, Q)` and the global
   Castelnuovo–Severi intersection form separate them unconditionally through three exact invariants:
   * **Exact on-line Parseval identity (`onSlack_of_posSemidef_eq`,
     `rank_trace_add_onSlack_of_posSemidef_eq_rank`, `onSlack_doubleZeroBlockData_eq`):** For any
     Hermitian critical-line Gram matrix `P` and any positive semidefinite `Q` (in particular `Q = 0`),
     the on-line spectral slack satisfies the exact identity
     `onSlack(P, Q, c) = ‖P‖_F² − c tr P + (c²/4) rank P`. At `c = 2` and `tr P = N`, adding
     `onSlack(P, 0, 2)` to `4 tr P − 2N − ‖P‖_F²` cancels the multiplicity loss identically and
     recovers the exact critical-line rank `rank P`. On `doubleZeroBlockData s₁ d₂`, `blockQ 1 = 0`
     and `onSlack = d₂` (raising the certified count from `s₁ = (2/3)N` to `s₁ + d₂ = (5/6)N > (3/4)N`).
   * **Off-line negative-part credit (`negPart_credit_pos_iff_not_posSemidef`):** In the rank–trace
     inequality `4 tr Â − 2N − ‖Â‖_F² + 2 tr(Q₋) ≤ rank P` (`RHTower.zeroside_rank_core_negPart`),
     the negative-part trace credit `2 tr(Q₋)` is strictly positive if and only if `Q` is not
     positive semidefinite (i.e. whenever an off-line pair contributes a negative square on the probe
     window), whereas every critical-line zero of any multiplicity has `Q = 0`.
   * **Joint `(c = 2, c = 3)` rank–trace elimination (`jointRankTrace23_at_four_thirds`,
     `three_quarters_of_broken_blind_spot_at_four_thirds`,
     `zeta_three_quarters_of_spectralSlack`):** The average of the `c = 2` simple-zero
     functional `4 tr Â − ‖Â‖_F² − 2N` and the `c = 3` distinct-zero functional
     `(6 tr Â − ‖Â‖_F² − 3N)/2` is `jointRankTrace23(Â, N) = (14 tr Â − 3 ‖Â‖_F² − 7N)/4 = ((7 − 3κ)/4)N`,
     which at the **unconditional bandwidth-one constant `κ = 4/3`** equals **exactly `(3/4)N` (`75%`)**.
     On `extremalDiag s₁ (d₂ + p)`, this equals `s₁ + (d₂ + p)/2`, certifying `≥ (3/4)N` distinct
     critical-line zeros whenever `p ≤ d₂` (and `≥ (3/4)N` with multiplicity whenever `p ≤ 3d₂`).
     For `ζ(s)` at any sub-threshold bandwidth `λ ∈ (0, 1)`, `thmA_lam_spectralSlack` unconditionally
     yields `(3/4 − ε)N(T, 2T) ≤ N₀*(T, 2T)` whenever the zero-side spectral slack is at least
     `(3/4 − H(λ))N(T, 2T)` (which approaches `(1/12)N(T, 2T)` as `λ → 1⁻`, half of the `(1/6)N`
     slack of `doubleZeroBlockData`).

2. **Route II: Lowering `κ` below `4/3` to `κ = 5/4` via prime correlations past `λ = 1`.**
   * **Exact `κ = 5/4` threshold (`kappa_five_fourths_iff_three_quarters`):** In the `c = 2`
     rank–trace capacity `2 − κ`, the critical-line proportion is at least `3/4` (`75%`) if and only
     if `κ ≤ 5/4 = 4/3 − 1/12`.
   * **Unconditional bandwidth-`4/3` decomposition and prime-surplus bridge for `ζ`
     (`zeta_three_quarters_from_prime_surplus`, `double_window_primeFreq_offDiag_and_exchange_rate`):**
     At bandwidth `λ = 4/3` (`X = (T/2π)^{4/3}`), the diagonal + archimedean + pole constant is
     unconditionally `43/36 = 5/4 − 1/18` (`diagonal_main_le`) and the prime–pole cross term
     `2|𝓜[P_X, Π_X]|` is unconditionally `O(T^{5/6} log² T)` (`abs_Mform_PX_PiX_params43_le`),
     leaving the exact margin `1/18` for `primeSurplus` to certify `(3/4 − ε)N(T) ≤ N₀*(T)` and
     `≤ N₀ˢ(T)`, while double-windowing (`norm_doubleWindow_primeFreq_offDiag_le`) unconditionally
     cuts off the prime-frequency off-diagonal at the minimum aperture `min(r, ρ)`.
-/

open Complex Finset Matrix Filter MeasureTheory
open scoped BigOperators ComplexOrder Topology
open GaloisForLFunctions.HTGeometry
open RiemannGaussian.HermitianRankTrace
open RiemannGaussian.HermitianRankTrace.Multiplicity
open Zeta23 Zeta23.ZeroSide RHLinalg RHTower

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ## 1. Route I: Breaking the Coalescence Blind Spot on the Zero Side -/

/-- On `doubleZeroBlockData s₁ d₂`, all zeros lie on the critical line (`σ = id`), so `onPart` equals
the full Gram matrix `blockA`. -/
theorem onPart_doubleZeroBlockData (s₁ d₂ : ℕ) :
    (doubleZeroBlockData s₁ d₂).onPart = (doubleZeroBlockData s₁ d₂).blockA := by
  have hon : (doubleZeroBlockData s₁ d₂).onLine = Finset.univ := by
    ext z; simp [ZeroBlockData.onLine, doubleZeroBlockData]
  unfold ZeroBlockData.onPart ZeroBlockData.blockA
  rw [hon]

/-- On `doubleZeroBlockData s₁ d₂`, the off-line block matrix `blockQ c` vanishes identically for
every scale `c`. -/
theorem blockQ_doubleZeroBlockData (s₁ d₂ : ℕ) (c : ℝ) :
    (doubleZeroBlockData s₁ d₂).blockQ c = 0 := by
  unfold ZeroBlockData.blockQ
  rw [onPart_doubleZeroBlockData, sub_self, smul_zero]

/-- On `doubleZeroBlockData s₁ d₂`, the unsplit critical-line Gram matrix `blockP 1` is the full
matrix `extremalDiag s₁ d₂ = diag(1, …, 1, 2, …, 2)`. -/
theorem blockP_one_doubleZeroBlockData (s₁ d₂ : ℕ) :
    (doubleZeroBlockData s₁ d₂).blockP 1 = extremalDiag s₁ d₂ := by
  have h := (doubleZeroBlockData s₁ d₂).blockP_add_blockQ 1
  rw [blockQ_doubleZeroBlockData, add_zero, inv_one, Complex.ofReal_one, one_smul,
    blockA_doubleZeroBlockData] at h
  exact h

/-- The negative-part trace `tr(Q₋)` vanishes for every positive semidefinite matrix `Q`. -/
theorem rtrace_hermNegPart_eq_zero_of_posSemidef {d : Type*} [Fintype d] [DecidableEq d]
    {Q : Matrix d d ℂ} (hQ : Q.PosSemidef) :
    RHLinalg.rtrace (RHLinalg.hermNegPart hQ.isHermitian) = 0 := by
  rw [RHLinalg.rtrace_hermNegPart]
  exact Finset.sum_eq_zero fun i _ =>
    negPart_eq_zero.mpr (hQ.eigenvalues_nonneg i)

/-- **Strict positivity of negative-part credit characterizes off-line negativity (`¬ Q.PosSemidef`).**
In the negative-part rank–trace inequality `4 tr Â − 2N − ‖Â‖_F² + 2 tr(Q₋) ≤ rank P`
(`RHTower.zeroside_rank_core_negPart`), the credit `2 tr(Q₋)` is always nonnegative and is strictly
positive if and only if `Q` is not positive semidefinite (i.e. `Q` has at least one negative
eigenvalue, resolved by the probe window from an off-line zero pair). -/
theorem negPart_credit_pos_iff_not_posSemidef {d : Type*} [Fintype d] [DecidableEq d]
    {Q : Matrix d d ℂ} (hQ : Q.IsHermitian) :
    0 ≤ 2 * RHLinalg.rtrace (RHLinalg.hermNegPart hQ) ∧
      (0 < 2 * RHLinalg.rtrace (RHLinalg.hermNegPart hQ) ↔ ¬ Q.PosSemidef) := by
  have hnn : 0 ≤ RHLinalg.rtrace (RHLinalg.hermNegPart hQ) := RHTower.rtrace_hermNegPart_nonneg hQ
  refine ⟨by linarith, ⟨fun hpos hpsd => ?_, fun hnot => ?_⟩⟩
  · have h0 := rtrace_hermNegPart_eq_zero_of_posSemidef hpsd
    linarith
  · by_contra hle
    have htr0 : RHLinalg.rtrace (RHLinalg.hermNegPart hQ) = 0 := by linarith
    rw [RHLinalg.rtrace_hermNegPart] at htr0
    have hall : ∀ i : d, (hQ.eigenvalues i)⁻ = 0 := fun i =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => negPart_nonneg _)).mp htr0 i
        (Finset.mem_univ i)
    have heig : ∀ i : d, 0 ≤ hQ.eigenvalues i := fun i =>
      negPart_eq_zero.mp (hall i)
    have hpsd : Q.PosSemidef := (RHLinalg.specMap_id hQ) ▸ (RHLinalg.specMap_posSemidef hQ heig)
    exact hnot hpsd

/-- **Exact on-line Parseval identity for `onSlack` whenever `Q ⪰ 0`.**
For any Hermitian matrix `P : Matrix d d ℂ` and any positive semidefinite `Q : Matrix d d ℂ`
(in particular `Q = 0`), the on-line spectral slack `onSlack P Q c` equals
`‖P‖_F² − c tr P + (c²/4) rank P` identically. -/
theorem onSlack_of_posSemidef_eq {d : Type*} [Fintype d] [DecidableEq d]
    {P Q : Matrix d d ℂ} (hP : P.IsHermitian) (hQ : Q.PosSemidef) (c : ℝ) :
    RHTower.onSlack hP hQ.isHermitian c =
      RHLinalg.frobSq P - c * RHLinalg.rtrace P + (c ^ 2 / 4) * (P.rank : ℝ) := by
  classical
  set hQm := RHLinalg.hermNegPart_posSemidef hQ.isHermitian
  set p := hP.eigenvalues₀
  set m := hQm.isHermitian.eigenvalues₀
  have hm_nn : ∀ k, 0 ≤ m k := fun k => by
    rw [show m k = hQm.isHermitian.eigenvalues (RHLinalg.eigEquiv k) from
      (RHLinalg.eigenvalues_eigEquiv hQm.isHermitian k).symm]
    exact hQm.eigenvalues_nonneg _
  have htrQm : ∑ k, m k = 0 := by
    have h1 : RHLinalg.rtrace (RHLinalg.hermNegPart hQ.isHermitian) = ∑ k, m k :=
      (RHLinalg.rtrace_eq_sum_eigenvalues hQm.isHermitian).trans
        (RHLinalg.sum_eigenvalues_reindex hQm.isHermitian id)
    linarith [rtrace_hermNegPart_eq_zero_of_posSemidef hQ]
  have hm0 : ∀ k, m k = 0 := fun k =>
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hm_nn j)).mp htrQm k (Finset.mem_univ k)
  have htraceP : RHLinalg.rtrace P = ∑ k, p k :=
    (RHLinalg.rtrace_eq_sum_eigenvalues hP).trans (RHLinalg.sum_eigenvalues_reindex hP id)
  have hfrobP : RHLinalg.frobSq P = ∑ k, (p k) ^ 2 :=
    (RHLinalg.frobSq_hermitian_eq_sum_sq_eigenvalues hP).trans
      (RHLinalg.sum_eigenvalues_reindex hP (· ^ 2))
  have hrankP : (P.rank : ℝ) = ∑ k, if p k ≠ 0 then (1 : ℝ) else 0 := by
    have hcard : #{k | p k ≠ 0} = P.rank :=
      (RHLinalg.card_eigenvalues_reindex hP (· ≠ 0)).symm.trans
        (by rw [hP.rank_eq_card_non_zero_eigs, Fintype.card_subtype])
    rw [← hcard, Finset.card_filter, Nat.cast_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp
  unfold RHTower.onSlack
  rw [hfrobP, htraceP, hrankP, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmk : hQm.isHermitian.eigenvalues₀ k = 0 := hm0 k
  rw [hmk, sub_zero]
  by_cases hk : p k = 0
  · simp [p, hk]
  · simp only [p, hk, ne_eq, not_false_eq_true, ↓reduceIte]
    ring

/-- **Complete elimination of critical-line multiplicity loss at `c = 2`.**
When `Q = 0` (all zeros in the block lie on the critical line, with arbitrary multiplicities) and
`tr P = N`, adding the on-line spectral slack `onSlack P 0 2` to the `c = 2` rank–trace functional
`4 tr P − 2N − ‖P‖_F²` recovers the exact rank `P.rank` identically. -/
theorem rank_trace_add_onSlack_of_posSemidef_eq_rank {d : Type*} [Fintype d] [DecidableEq d]
    {P : Matrix d d ℂ} (hP : P.IsHermitian) {N : ℝ} (hN : RHLinalg.rtrace P = N) :
    4 * RHLinalg.rtrace P - 2 * N - RHLinalg.frobSq P +
      RHTower.onSlack hP (Matrix.PosSemidef.zero : (0 : Matrix d d ℂ).PosSemidef).isHermitian 2 =
        (P.rank : ℝ) := by
  rw [onSlack_of_posSemidef_eq hP Matrix.PosSemidef.zero 2, hN]
  ring

/-- The diagonal matrix `extremalDiag s₁ d₂` has full rank `s₁ + d₂` (every diagonal entry `1` or `2`
is nonzero). -/
theorem rank_extremalDiag (s₁ d₂ : ℕ) :
    (extremalDiag s₁ d₂).rank = s₁ + d₂ := by
  have hdet : (extremalDiag s₁ d₂).det ≠ 0 := by
    unfold extremalDiag
    rw [det_diagonal, Finset.prod_ne_zero_iff]
    intro k _
    rcases k with i | j <;> simp
  have hfull : (extremalDiag s₁ d₂).rank = Fintype.card (Fin s₁ ⊕ Fin d₂) :=
    Matrix.rank_of_isUnit (extremalDiag s₁ d₂)
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  rw [hfull, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

/-- **Breaking the blind spot on `doubleZeroBlockData s₁ d₂` via `onSlack`.**
On `doubleZeroBlockData s₁ d₂`, the unsplit on-line slack `onSlack` equals `d₂`, raising the
certified critical-line zero count from `s₁` to the exact distinct critical-line count `s₁ + d₂`
(which at `s₁ = 4k, d₂ = k` is `5k = (5/6)N > (3/4)N`). -/
theorem onSlack_doubleZeroBlockData_eq (s₁ d₂ : ℕ) :
    let D := doubleZeroBlockData s₁ d₂
    let hP := (D.blockP_posSemidef (by norm_num : (0 : ℝ) < 1)).isHermitian
    let hQ0 := (Matrix.PosSemidef.zero : (0 : Matrix (Fin s₁ ⊕ Fin d₂) (Fin s₁ ⊕ Fin d₂) ℂ).PosSemidef).isHermitian
    RHTower.onSlack hP hQ0 2 = (d₂ : ℝ) ∧
      4 * RHLinalg.rtrace (D.blockP 1) - 2 * (D.Ncount : ℝ) - RHLinalg.frobSq (D.blockP 1) +
        RHTower.onSlack hP hQ0 2 = (s₁ : ℝ) + (d₂ : ℝ) := by
  dsimp only
  have hP1 : (doubleZeroBlockData s₁ d₂).blockP 1 = extremalDiag s₁ d₂ :=
    blockP_one_doubleZeroBlockData s₁ d₂
  have hN : ((doubleZeroBlockData s₁ d₂).Ncount : ℝ) = (s₁ : ℝ) + 2 * (d₂ : ℝ) := by
    rw [(Ncount_doubleZeroBlockData s₁ d₂).1]; push_cast; ring
  have htr : RHLinalg.rtrace ((doubleZeroBlockData s₁ d₂).blockP 1) = (s₁ : ℝ) + 2 * (d₂ : ℝ) := by
    rw [hP1, rtrace_extremalDiag]
  have hfrob : RHLinalg.frobSq ((doubleZeroBlockData s₁ d₂).blockP 1) = (s₁ : ℝ) + 4 * (d₂ : ℝ) := by
    rw [hP1, frobSq_extremalDiag]
  have hrank : (((doubleZeroBlockData s₁ d₂).blockP 1).rank : ℝ) = (s₁ : ℝ) + (d₂ : ℝ) := by
    rw [hP1, rank_extremalDiag]; push_cast; ring
  have hslack := onSlack_of_posSemidef_eq
    ((doubleZeroBlockData s₁ d₂).blockP_posSemidef (by norm_num : (0 : ℝ) < 1)).isHermitian
    Matrix.PosSemidef.zero 2
  rw [htr, hfrob, hrank] at hslack
  refine ⟨by linarith, ?_⟩
  rw [htr, hfrob, hN]
  linarith

/-! ## 2. Joint `(c = 2, c = 3)` Rank–Trace Elimination and `3/4` (`75%`) at `κ = 4/3` -/

/-- **The joint `(c = 2, c = 3)` rank–trace functional.**
The midpoint of the `c = 2` simple-zero functional `4 tr Â − ‖Â‖_F² − 2N` and the `c = 3`
distinct-zero functional `(6 tr Â − ‖Â‖_F² − 3N) / 2` is `(14 tr Â − 3 ‖Â‖_F² − 7N) / 4`. -/
def jointRankTrace23 {d : Type*} [Fintype d] (A : Matrix d d ℂ) (N : ℝ) : ℝ :=
  (14 * RHLinalg.rtrace A - 3 * RHLinalg.frobSq A - 7 * N) / 4

/-- `jointRankTrace23` is the exact average of the `c = 2` and `c = 3` rank–trace functionals. -/
theorem jointRankTrace23_eq_avg {d : Type*} [Fintype d] (A : Matrix d d ℂ) (N : ℝ) :
    jointRankTrace23 A N =
      ((4 * RHLinalg.rtrace A - RHLinalg.frobSq A - 2 * N) +
        (6 * RHLinalg.rtrace A - RHLinalg.frobSq A - 3 * N) / 2) / 2 := by
  unfold jointRankTrace23
  ring

/-- When `tr Â = N` and `‖Â‖_F² = κ N`, the joint `(c = 2, c = 3)` functional equals
`((7 − 3κ) / 4) N`. -/
theorem jointRankTrace23_of_kappa {d : Type*} [Fintype d] (A : Matrix d d ℂ) (N κ : ℝ)
    (htr : RHLinalg.rtrace A = N) (hfrob : RHLinalg.frobSq A = κ * N) :
    jointRankTrace23 A N = ((7 - 3 * κ) / 4) * N := by
  unfold jointRankTrace23
  rw [htr, hfrob]
  ring

/-- **At the unconditional bandwidth-one constant `κ = 4/3`, `jointRankTrace23` equals `3/4` (`75%`).**
Whenever `tr Â ≥ N` and `‖Â‖_F² ≤ (4/3) N`, `jointRankTrace23 Â N ≥ (3/4) N`, with exact equality at
`tr Â = N` and `‖Â‖_F² = (4/3) N`. -/
theorem jointRankTrace23_at_four_thirds {d : Type*} [Fintype d] (A : Matrix d d ℂ) (N : ℝ)
    (htr : N ≤ RHLinalg.rtrace A) (hfrob : RHLinalg.frobSq A ≤ (4 / 3 : ℝ) * N) :
    (3 / 4 : ℝ) * N ≤ jointRankTrace23 A N := by
  unfold jointRankTrace23
  linarith

/-- On `extremalDiag s₁ m₂` (`N = s₁ + 2m₂`), `jointRankTrace23` evaluates identically to
`s₁ + m₂ / 2`. -/
theorem jointRankTrace23_extremalDiag_exact (s₁ m₂ : ℕ) :
    jointRankTrace23 (extremalDiag s₁ m₂) ((s₁ : ℝ) + 2 * (m₂ : ℝ)) =
      (s₁ : ℝ) + (m₂ : ℝ) / 2 := by
  rw [jointRankTrace23_eq_avg, rankTrace_extremalDiag_exact, rankTrace_three_extremalDiag_exact]
  ring

/-- **Three quarters (`75%`) on the critical line at `κ = 4/3` once the blind spot is broken.**
For any configuration with `s₁` simple critical zeros, `d₂` double critical zeros, and `p`
off-line pairs realizing `extremalDiag s₁ (d₂ + p)` (`N = s₁ + 2d₂ + 2p`) with `‖Â‖_F² ≤ (4/3)N`:
1. The joint `(c = 2, c = 3)` functional satisfies `(3/4) N ≤ jointRankTrace23 Â N = s₁ + (d₂ + p)/2`.
2. If `p ≤ d₂` (off-line pairs do not outnumber double critical zeros), at least `3/4` (`75%`) of
   the zeros are **distinct critical-line zeros** (`(3/4) N ≤ s₁ + d₂`).
3. If `p ≤ 3 d₂`, at least `3/4` (`75%`) of the zeros lie on the **critical line with multiplicity**
   (`(3/4) N ≤ s₁ + 2 d₂`). -/
theorem three_quarters_of_broken_blind_spot_at_four_thirds (s₁ d₂ p : ℕ)
    (hfrob : RHLinalg.frobSq (extremalDiag s₁ (d₂ + p)) ≤
      (4 / 3 : ℝ) * ((s₁ : ℝ) + 2 * ((d₂ + p : ℕ) : ℝ))) :
    let N : ℝ := (s₁ : ℝ) + 2 * ((d₂ + p : ℕ) : ℝ)
    (3 / 4 : ℝ) * N ≤ jointRankTrace23 (extremalDiag s₁ (d₂ + p)) N ∧
      (p ≤ d₂ → (3 / 4 : ℝ) * N ≤ (s₁ : ℝ) + (d₂ : ℝ)) ∧
      (p ≤ 3 * d₂ → (3 / 4 : ℝ) * N ≤ (s₁ : ℝ) + 2 * (d₂ : ℝ)) := by
  dsimp only
  have htr : (s₁ : ℝ) + 2 * ((d₂ + p : ℕ) : ℝ) ≤
      RHLinalg.rtrace (extremalDiag s₁ (d₂ + p)) := by
    rw [rtrace_extremalDiag]
  have hjoint := jointRankTrace23_at_four_thirds (extremalDiag s₁ (d₂ + p))
    ((s₁ : ℝ) + 2 * ((d₂ + p : ℕ) : ℝ)) htr hfrob
  have hexact := jointRankTrace23_extremalDiag_exact s₁ (d₂ + p)
  push_cast at hexact hjoint ⊢
  refine ⟨hjoint, fun hpd => ?_, fun hp3d => ?_⟩
  · have hpd' : (p : ℝ) ≤ (d₂ : ℝ) := Nat.cast_le.mpr hpd
    linarith
  · have hp3d' : (p : ℝ) ≤ 3 * (d₂ : ℝ) := by exact_mod_cast hp3d
    linarith

/-- **Unconditional `ζ` Spectral-Slack Bridge to `3/4` (`75%`) Below the Square-Root Threshold.**
1. Unconditionally, for every `λ ∈ (0, 1)` and `ε > 0`, there exists `T₀` such that for all
   `T ≥ T₀`, the distinct critical-line zero count `N₀*(T, 2T)` of `ζ(s)` in `(T, 2T]` satisfies
   `(H(λ) − ε) N(T, 2T) + zeroSideSlack(λ, T) ≤ N₀*(T, 2T)`, where `zeroSideSlack ≥ 0` is the sum
   of the off-line negative-part credit `2 tr Q_-`, the off-line positive-spectrum slack `posSlack`,
   and the on-line Parseval slack `onSlack`.
2. At `λ = 1`, `3/4 − H(1) = 3/4 − 2/3 = 1/12`. For every `λ ∈ (0, 1)` and `T ≥ T₀` at which
   `zeroSideSlack(λ, T) ≥ (3/4 − H(λ)) N(T, 2T)` (which approaches `(1/12) N(T, 2T)` as `λ → 1⁻`,
   half of the `(1/6) N` on-line slack of `doubleZeroBlockData (4k) k`), at least `3/4 − ε` (`75%`)
   of the nontrivial zeros of `ζ(s)` in `(T, 2T]` are distinct critical-line zeros. -/
theorem zeta_three_quarters_of_spectralSlack :
    (3 / 4 : ℝ) - Zeta23.Hfun 1 = 1 / 12 ∧
    (∀ {lam : ℝ}, 0 < lam → lam < 1 → ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (Zeta23.Hfun lam - ε) * (Zeta23.Ncount T (2 * T) : ℝ) +
        RHTower.zeroSideSlack Zeta23.zetaZeroConfig (Zeta23.paramsOf Zeta23.stdProfile lam) T ≤
        (Zeta23.N0star T (2 * T) : ℝ)) ∧
    (∀ {lam : ℝ}, 0 < lam → lam < 1 → ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (3 / 4 - Zeta23.Hfun lam) * (Zeta23.Ncount T (2 * T) : ℝ) ≤
        RHTower.zeroSideSlack Zeta23.zetaZeroConfig (Zeta23.paramsOf Zeta23.stdProfile lam) T →
      (3 / 4 - ε) * (Zeta23.Ncount T (2 * T) : ℝ) ≤ (Zeta23.N0star T (2 * T) : ℝ)) := by
  refine ⟨by unfold Zeta23.Hfun; norm_num,
    fun h0 h1 ε hε => RHTower.thmA_lam_spectralSlack h0 h1 ε hε,
    fun h0 h1 ε hε => ?_⟩
  rcases RHTower.thmA_lam_spectralSlack h0 h1 ε hε with ⟨T₀, hT₀⟩
  refine ⟨T₀, fun T hT hslack => ?_⟩
  have h := hT₀ T hT
  linarith

/-! ## 3. Route II: Lowering `κ` Below `4/3` to `κ = 5/4` via Prime Correlations Past `λ = 1` -/

/-- **Exact `κ = 5/4` exchange-rate law for `3/4` (`75%`) critical-line zeros.**
In the `c = 2` rank–trace capacity `2 − κ`, the certified proportion is at least `3/4` (`75%`) if
and only if the normalized Frobenius norm satisfies `κ ≤ 5/4 = 4/3 − 1/12`. At bandwidth `λ = 4/3`,
pair-correlation bound `B = 2` gives `2 − certValue (4/3) 2 = 5/4` and `certValue (4/3) 2 = 3/4`,
while the random-matrix value `B = 1` gives `2 − certValue (4/3) 1 = 19/16 < 5/4`. -/
theorem kappa_five_fourths_iff_three_quarters (κ : ℝ) :
    (3 / 4 ≤ 2 - κ ↔ κ ≤ 5 / 4) ∧
      RHTower.certValue (4 / 3) 2 = 3 / 4 ∧
      2 - RHTower.certValue (4 / 3) 2 = 5 / 4 ∧
      2 - RHTower.certValue (4 / 3) 1 = 19 / 16 := by
  refine ⟨⟨fun h => by linarith, fun h => by linarith⟩,
    RHTower.certValue_four_thirds_two,
    RHTower.frobenius_target_gue.1,
    RHTower.frobenius_target_gue.2⟩

/-- **Unconditional bandwidth-`4/3` (`κ = 5/4`) synthesis and `75%` critical-line bridge for `ζ`.**
At bandwidth `λ = 4/3` (`X = (T/2π)^{4/3}`):
1. **Unconditional diagonal + archimedean + pole constant (`43/36 = 5/4 − 1/18`):** For all large
   `l` (`14/ε ≤ l`), `(T L / 2π)(ℓ₁² + L²/3) ≤ (43/36 + ε/2)(aL)² Tℓ₁/(2π)`
   (`RHTower.diagonal_main_le`).
2. **Unconditional prime–pole cross bound (`O(T^{5/6} log² T)`):** For all large `T`,
   `2 |𝓜[P_X, Π_X]| ≤ (320/3) (log T)² T^{5/6}` (`RHTower.abs_Mform_PX_PiX_params43_le`).
3. **Exact `1/18` prime-surplus bridge to `75%` (`43/36 + 1/18 = 5/4`, `2 − 5/4 = 3/4`):**
   Controlling the remaining prime surplus within the `1/18` margin (`RHTower.PrimeSurplusFourThirds`)
   certifies both `(3/4 − ε) N(T) ≤ N₀*(T)` (at least `75%` distinct critical-line zeros) and
   `(3/4 − ε) N(T) ≤ N₀ˢ(T)` (at least `75%` simple critical-line zeros). -/
theorem zeta_three_quarters_from_prime_surplus :
    ((43 / 36 : ℝ) + 1 / 18 = 5 / 4 ∧ (2 : ℝ) - 5 / 4 = 3 / 4) ∧
    (∀ {ε l c₀ a T : ℝ}, 0 < ε → ε ≤ 1 → 14 / ε ≤ l → 1 ≤ l → 0 ≤ c₀ → c₀ ≤ 1 →
      1 - 2 / (4 / 3 * l) ≤ a → 0 < T →
      T * (4 / 3 * l) / (2 * Real.pi) * ((l + c₀) ^ 2 + (4 / 3 * l) ^ 2 / 3) ≤
        (43 / 36 + ε / 2) * (a * (4 / 3 * l)) ^ 2 * (T * (l + c₀) / (2 * Real.pi))) ∧
    (∀ᶠ T in atTop,
      2 * |Zeta23.PrimeSide.Mform (RHTower.params43.PhiR T) T
            (Zeta23.PX (RHTower.params43.X T)) (Zeta23.PiX (RHTower.params43.X T))| ≤
        320 / 3 * (Real.log T ^ 2 * T ^ (5 / 6 : ℝ))) ∧
    (RHTower.PrimeSurplusFourThirds →
      (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
        (3 / 4 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.N0star 0 T : ℝ)) ∧
      (∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
        (3 / 4 - ε) * (Zeta23.Ncount 0 T : ℝ) ≤ (Zeta23.N0simple 0 T : ℝ))) :=
  ⟨⟨by norm_num, by norm_num⟩,
    fun hε hε1 hl hl1 hc₀ hc₁ ha hT => RHTower.diagonal_main_le hε hε1 hl hl1 hc₀ hc₁ ha hT,
    RHTower.abs_Mform_PX_PiX_params43_le,
    fun hPS => ⟨RHTower.zeta_three_quarters_of_prime_surplus hPS,
      RHTower.zeta_three_quarters_simple_of_prime_surplus hPS⟩⟩

/-- **Unconditional double-window minimum-aperture prime-pair bound and exchange rate beyond `λ = 1`.**
For any primary window `η` of aperture `r ≥ 0` (even past the square-root threshold) and secondary
height window `ω` of aperture `ρ ≥ 0` with `min r ρ ≤ log 2`, the double-windowed prime-frequency
off-diagonal up to `N ≤ X` is unconditionally bounded at scale `min r ρ` by
`(∫ ‖η‖²)(∫ ‖ω‖²) X (e^{2 min(r,ρ)} − e^{-2 min(r,ρ)}) V_f(N)`, and any finite pair-correlation
bound `F ≤ B` (`B > 2/3`) beyond `λ = 1` advances the certified critical-line proportion to
`certOpt B = 2/3 + 1/(3(3B − 2))` (`≥ 3/4` iff `B ≤ 2`). -/
theorem double_window_primeFreq_offDiag_and_exchange_rate
    {η ω f : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω)
    {r ρ X B lam : ℝ} {N : ℕ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hmin2 : min r ρ ≤ Real.log 2) (hNX : (N : ℝ) ≤ X)
    (hηs : tsupport η ⊆ Set.Icc (-r) r) (hωs : tsupport ω ⊆ Set.Icc (-ρ) ρ) (T : ℝ)
    (hB : 2 / 3 < B) (hlam : lam ≠ 0) :
    ‖∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool),
      ∑ k ∈ GaloisForLFunctions.SquareRootThreshold.closeSet
          (Finset.Icc 2 N ×ˢ Finset.univ)
          GaloisForLFunctions.SquareRootThreshold.primeFreq (min r ρ) j,
        GaloisForLFunctions.SquareRootThreshold.primeCoeff f j *
          (starRingEnd ℂ) (GaloisForLFunctions.SquareRootThreshold.primeCoeff f k) *
          Zeta23.EF.weilTest η η
            (GaloisForLFunctions.SquareRootThreshold.primeFreq j -
              GaloisForLFunctions.SquareRootThreshold.primeFreq k) *
          Zeta23.EF.weilTest ω ω
            (GaloisForLFunctions.SquareRootThreshold.primeFreq j -
              GaloisForLFunctions.SquareRootThreshold.primeFreq k) *
          Complex.exp (2 * Real.pi * Complex.I * T *
            ((GaloisForLFunctions.SquareRootThreshold.primeFreq j -
              GaloisForLFunctions.SquareRootThreshold.primeFreq k : ℝ) : ℂ))‖ ≤
      (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) *
        (X * (Real.exp (2 * min r ρ) - Real.exp (-(2 * min r ρ))) *
          GaloisForLFunctions.SquareRootThreshold.primeVariance f N) ∧
    (RHTower.certOpt B - RHTower.certValue lam B =
        (B - 2 / 3) * (1 / lam - 3 * (B - 1) / (3 * B - 2)) ^ 2 ∧
      RHTower.certOpt B - 2 / 3 = 1 / (3 * (3 * B - 2)) ∧
      (3 / 4 ≤ RHTower.certOpt B ↔ B ≤ 2)) :=
  ⟨GaloisForLFunctions.SquareRootThreshold.norm_doubleWindow_primeFreq_offDiag_le
      hη hω hr hρ hmin2 hNX hηs hωs T,
    GaloisForLFunctions.SquareRootThreshold.pairCorrelation_beyond_threshold_exchange_rate hB hlam⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
