import GaloisForLFunctions.RHTower.EulerDeletionResidueMartingale

/-!
# Strong limit of Euler-deletion innovations

The physical residue innovations are not merely uniformly bounded at finite
cutoffs.  Their literal signed series is square summable in the physical
`L²` carrier, hence its finite martingale part has an unconditional strong
limit.  Thus any remaining asymptotic Euler-deletion source energy is in the
predictable drift, not in an unaccounted innovation tail.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open scoped BigOperators

namespace RHTower.DeletionResidueMartingale

/-- Literal signed innovations form a summable orthogonal series in the physical carrier. -/
theorem summable_signedInnovation : Summable signedInnovation := by
  let G : ℕ → Submodule ℝ (Lp ℝ 2 cellMeasure) :=
    fun i => Submodule.span ℝ {signedInnovation i}
  let V : ∀ i, G i →ₗᵢ[ℝ] Lp ℝ 2 cellMeasure := fun i => (G i).subtypeₗᵢ
  let f : ∀ i, G i := fun i =>
    ⟨signedInnovation i, Submodule.subset_span (Set.mem_singleton _)⟩
  have horth : OrthogonalFamily ℝ (fun i => (G i : Type _)) V := by
    have hsi {a b : ℕ} (hab : a < b) :
        inner ℝ (signedInnovation b) (signedInnovation a) = 0 := by
      simp only [signedInnovation, real_inner_smul_left, real_inner_smul_right,
        innovation_orthogonal hab, mul_zero]
    intro i j hij u v
    rcases (Submodule.mem_span_singleton.mp u.property) with ⟨a, ha⟩
    rcases (Submodule.mem_span_singleton.mp v.property) with ⟨b, hb⟩
    change inner ℝ (u : Lp ℝ 2 cellMeasure) (v : Lp ℝ 2 cellMeasure) = 0
    rw [← ha, ← hb]
    simp only [real_inner_smul_left, real_inner_smul_right]
    rcases lt_or_gt_of_ne hij with hij' | hij'
    · rw [real_inner_comm, hsi hij']
      simp
    · rw [hsi hij']
      simp
  have htail : Summable (fun j : ℕ => ‖signedInnovation (j + 2)‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) ?_ hasSum_cellWeight.summable
    intro j
    apply (signedInnovation_sq_le (j + 2)).trans
    unfold cellWeight
    apply one_div_le_one_div_of_le (by positivity)
    have hc : ((j : ℝ) + 1) * ((j : ℝ) + 2) ≤ (clock (j + 2) : ℝ) := by
      exact_mod_cast consecutive_le_clock j
    linarith
  have hsq : Summable (fun i : ℕ => ‖signedInnovation i‖ ^ 2) :=
    (summable_nat_add_iff 2).mp htail
  have hf : Summable (fun i => V i (f i)) :=
    (horth.summable_iff_norm_sq_summable f).mpr (by simpa [f] using hsq)
  simpa [V, f] using hf

/-- The unconditional physical `L²` limit of literal signed innovations. -/
def martingaleLimit : Lp ℝ 2 cellMeasure := ∑' i, signedInnovation i

/-- Finite Euler-deletion innovation sums converge strongly to `martingaleLimit`. -/
theorem tendsto_martingalePart :
    Tendsto martingalePart atTop (𝓝 martingaleLimit) := by
  change Tendsto (fun N => ∑ i ∈ range N, signedInnovation i) atTop
    (𝓝 (∑' i, signedInnovation i))
  exact summable_signedInnovation.tendsto_sum_tsum_nat

end RHTower.DeletionResidueMartingale
