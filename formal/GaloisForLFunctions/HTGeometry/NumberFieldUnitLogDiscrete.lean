import GaloisForLFunctions.HTGeometry.NumberFieldUnitLogProduct
import GaloisForLFunctions.HTGeometry.NumberFieldPrimitiveLattice

/-!
# Local finiteness of logarithmic number-ring units

Bounded logarithmic profiles force bounded mixed Minkowski embeddings.  Since algebraic integers
form a discrete lattice in mixed space and that embedding is injective on units, every bounded
logarithmic slice of the unit group is finite.  This supplies the discrete half of Dirichlet-unit
reduction without retaining any arithmetic premise.
-/

namespace GaloisForLFunctions.HTGeometry

open NumberField
open scoped Classical NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

/-- Mixed Minkowski embedding of a number-ring unit. -/
def numberFieldUnitMixedEmbedding (u : (𝓞 K)ˣ) : mixedEmbedding.mixedSpace K :=
  mixedEmbedding K (((u : 𝓞 K) : K))

omit [NumberField K] in
theorem numberFieldUnitMixedEmbedding_mem_integerLattice (u : (𝓞 K)ˣ) :
    numberFieldUnitMixedEmbedding u ∈ mixedEmbedding.integerLattice K := by
  exact ⟨(u : 𝓞 K), rfl⟩

theorem numberFieldUnitMixedEmbedding_injective :
    Function.Injective (numberFieldUnitMixedEmbedding (K := K)) := by
  intro u v huv
  apply Units.ext
  have hK : (((u : 𝓞 K) : K)) = (((v : 𝓞 K) : K)) :=
    (mixedEmbedding K).injective huv
  exact_mod_cast hK

private theorem numberFieldUnitEmbeddingNorm_le_exp_of_log_norm_le
    (u : (𝓞 K)ˣ) {R : ℝ}
    (hR : ‖numberFieldUnitLogEmbeddings u‖ ≤ R) (σ : K →+* ℂ) :
    ‖σ (((u : 𝓞 K) : K))‖ ≤ Real.exp R := by
  have hcoord : ‖numberFieldUnitLogEmbeddings u σ‖ ≤
      ‖numberFieldUnitLogEmbeddings u‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).1 le_rfl σ
  have hlog : Real.log ‖σ (((u : 𝓞 K) : K))‖ ≤ R := by
    exact le_trans (le_trans (le_abs_self _) hcoord) hR
  have hpos : 0 < ‖σ (((u : 𝓞 K) : K))‖ := by
    rw [norm_pos_iff]
    intro hz
    have hzK : (((u : 𝓞 K) : K)) = 0 := σ.injective (hz.trans (map_zero σ).symm)
    have huK : (((u : 𝓞 K) : K)) ≠ 0 := by
      norm_cast
      exact u.ne_zero
    exact huK hzK
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hpos] at hexp
  exact hexp

/-- A bounded logarithmic profile gives a bounded mixed Minkowski embedding. -/
theorem norm_numberFieldUnitMixedEmbedding_le_exp_of_log_norm_le
    (u : (𝓞 K)ˣ) {R : ℝ}
    (hR : ‖numberFieldUnitLogEmbeddings u‖ ≤ R) :
    ‖numberFieldUnitMixedEmbedding u‖ ≤ Real.exp R := by
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg R)).2
    intro w
    change ‖(InfinitePlace.embedding_of_isReal w.2) (((u : 𝓞 K) : K))‖ ≤ Real.exp R
    have h := numberFieldUnitEmbeddingNorm_le_exp_of_log_norm_le u hR w.1.embedding
    calc
      ‖(InfinitePlace.embedding_of_isReal w.2) (((u : 𝓞 K) : K))‖ =
          ‖((InfinitePlace.embedding_of_isReal w.2) (((u : 𝓞 K) : K)) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
      _ = ‖w.1.embedding (((u : 𝓞 K) : K))‖ := by
        rw [InfinitePlace.embedding_of_isReal_apply]
      _ ≤ Real.exp R := h
  · apply (pi_norm_le_iff_of_nonneg (Real.exp_nonneg R)).2
    intro w
    exact numberFieldUnitEmbeddingNorm_le_exp_of_log_norm_le u hR w.1.embedding

/-- Mixed embeddings of units in a bounded logarithmic ball form a finite set. -/
theorem finite_numberFieldUnitMixedEmbedding_of_log_norm_le (R : ℝ) :
    {x : mixedEmbedding.mixedSpace K |
      ∃ u : (𝓞 K)ˣ, ‖numberFieldUnitLogEmbeddings u‖ ≤ R ∧
        x = numberFieldUnitMixedEmbedding u}.Finite := by
  let S : Set (mixedEmbedding.mixedSpace K) :=
    {x | ∃ u : (𝓞 K)ˣ, ‖numberFieldUnitLogEmbeddings u‖ ≤ R ∧
      x = numberFieldUnitMixedEmbedding u}
  have hfinite :
      ((Metric.closedBall (0 : mixedEmbedding.mixedSpace K) (Real.exp R)) ∩
        (mixedEmbedding.integerLattice K : Set (mixedEmbedding.mixedSpace K))).Finite :=
    finite_lattice_inter_of_bounded (mixedEmbedding.integerLattice K)
      Metric.isBounded_closedBall
  change S.Finite
  refine hfinite.subset ?_
  intro x hx
  rcases hx with ⟨u, hu, rfl⟩
  constructor
  · simpa [Metric.mem_closedBall, dist_zero_right] using
      norm_numberFieldUnitMixedEmbedding_le_exp_of_log_norm_le u hu
  · exact numberFieldUnitMixedEmbedding_mem_integerLattice u

/-- Units with logarithmic profile in a fixed norm ball form a finite set. -/
theorem finite_numberFieldUnits_of_log_norm_le (R : ℝ) :
    {u : (𝓞 K)ˣ | ‖numberFieldUnitLogEmbeddings u‖ ≤ R}.Finite := by
  let S : Set (𝓞 K)ˣ := {u | ‖numberFieldUnitLogEmbeddings u‖ ≤ R}
  have himage :
      numberFieldUnitMixedEmbedding '' S =
        {x : mixedEmbedding.mixedSpace K |
          ∃ u : (𝓞 K)ˣ, ‖numberFieldUnitLogEmbeddings u‖ ≤ R ∧
            x = numberFieldUnitMixedEmbedding u} := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
  change S.Finite
  apply Set.Finite.of_finite_image
  · rw [himage]
    exact finite_numberFieldUnitMixedEmbedding_of_log_norm_le R
  · exact numberFieldUnitMixedEmbedding_injective.injOn

end

end GaloisForLFunctions.HTGeometry
