import Zeta23.Assembly
import Zeta23.ZeroSide

/-!
# The counting step with weighted grid rows

Let the zero-side Gram data be the evaluation vectors `u_ρ = (φ̂(γ_ρ − τ_k))_k` of a reflection-symmetric zero
configuration (`ZeroBlockData`).  Multiplying the `k`-th grid coordinate by a real weight `w_k` with `|w_k| ≤ 1`
(`weightBlock`) keeps the reflection symmetry `u_{1−ρ̄} = conj u_ρ`, so the block structure of the Gram matrix
survives: its entries become `w_k w_l A_{kl}` (`weightBlock_blockA_apply`), the on-line part is positive semidefinite
of rank at most the number of distinct on-line zeros, the pair part has positive index at most the number of
off-line pairs, and the Poisson trace bound `Σ_k |u_ρ(k)|² ≤ aL²` passes to the weighted vectors
(`weightBlock_hPois`).  Hence the counting step holds for the weighted Gram matrix
(`weighted_rank_certificate`):

`4 tr Â_w − 2N − ‖Â_w‖_F² ≤ s₁ + s₂`,   `Â_w = (w_k w_l Â_{kl})`.

With weights that vanish smoothly near the ends of the grid the Gram matrix has no truncation edges; this is the
zero-side half of a smoothly tapered certificate.
-/

open Matrix Finset RHLinalg Zeta23.ZeroSide
open scoped ComplexOrder

noncomputable section

namespace RHTower

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]

/-- **Weighted block data**: the `k`-th coordinate of every evaluation vector is multiplied by `w k`. -/
def weightBlock (D : ZeroBlockData ι d) (w : d → ℝ) : ZeroBlockData ι d where
  m := D.m
  one_le_m := D.one_le_m
  v := fun z k => (w k : ℂ) * D.v z k
  σ := D.σ
  σ_invol := D.σ_invol
  m_σ := D.m_σ
  v_σ := fun z => by
    funext k
    have h := congrFun (D.v_σ z) k
    simp only [Pi.star_apply, RCLike.star_def] at h ⊢
    rw [h, map_mul, Complex.conj_ofReal]

/-- The weighted Gram matrix is `diag(w) A diag(w)`. -/
theorem weightBlock_blockA_apply (D : ZeroBlockData ι d) (w : d → ℝ) (k l : d) :
    (weightBlock D w).blockA k l = ((w k * w l : ℝ) : ℂ) * D.blockA k l := by
  rw [ZeroBlockData.blockA_apply, ZeroBlockData.blockA_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [weightBlock]
  push_cast; ring

omit [DecidableEq d] in
/-- Weights of modulus at most one preserve the Poisson trace bound. -/
theorem weightBlock_hPois (D : ZeroBlockData ι d) {w : d → ℝ} (hw : ∀ k, |w k| ≤ 1) {c : ℝ}
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    ∀ z ∈ (weightBlock D w).onLine, ∑ k, ‖(weightBlock D w).v z k‖ ^ 2 ≤ c := by
  intro z hz
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (hPois z hz)
  simp only [weightBlock, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have h1 : |w k| ^ 2 ≤ 1 := by
    have := abs_nonneg (w k)
    nlinarith [hw k]
  have h2 : 0 ≤ ‖D.v z k‖ ^ 2 := sq_nonneg _
  nlinarith

/-- Pair representatives transported to the weighted data (same reflection). -/
def weightPairReps (D : ZeroBlockData ι d) (w : d → ℝ) (P : D.PairReps) :
    (weightBlock D w).PairReps where
  R := P.R
  off := P.off
  σ_not_mem := P.σ_not_mem
  cover := P.cover

/-- **The counting step for the weighted Gram matrix.** -/
theorem weighted_rank_certificate (D : ZeroBlockData ι d) (P : D.PairReps) {w : d → ℝ}
    (hw : ∀ k, |w k| ≤ 1) {c : ℝ} (hc : 0 < c) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    4 * rtrace (((c⁻¹ : ℝ) : ℂ) • (weightBlock D w).blockA) - 2 * (D.Ncount : ℝ)
      - frobSq (((c⁻¹ : ℝ) : ℂ) • (weightBlock D w).blockA) ≤ (D.s₁ + D.s₂ : ℕ) := by
  set D' := weightBlock D w with hD'
  set P' := weightPairReps D w P with hP'
  have hdec := (D'.blockP_add_blockQ c).symm
  have hPsd := D'.blockP_posSemidef hc
  have hQ := D'.blockQ_isHermitian c
  have hrank := D'.rank_blockP_le hc
  have hpos := D'.posIndex_blockQ_le P' hc
  have htr := D'.rtrace_blockP_le hc (weightBlock_hPois D hw hPois)
  have hcount := D'.Non_add_two_p_le_Ncount P'
  have hcount' : (D'.Non : ℝ) + 2 * (P'.p : ℕ) ≤ (D'.Ncount : ℝ) := by exact_mod_cast hcount
  have h := Zeta23.Assembly.zeroside_rank_core hdec hPsd hQ hrank hpos htr hcount'
  have hN : D'.Ncount = D.Ncount := rfl
  have hs₁ : D'.s₁ = D.s₁ := rfl
  have hs₂ : D'.s₂ = D.s₂ := rfl
  rw [hN, hs₁, hs₂] at h
  exact h

end RHTower
