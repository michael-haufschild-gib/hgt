import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencySparseSynthesis
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyCoefficientShift
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.InfiniteSum.Module
open Filter Topology
open scoped Classical
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false
section Analysis
variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private theorem coefficient_mem_l2 (a : I → E →L[ℂ] ℂ)
    (hs : ∀ u, Summable (fun i => ‖a i u‖ ^ 2)) (u : E) :
    Memℓp (fun i => a i u) 2 := by
  apply memℓp_gen
  simpa using hs u

private def coefficientL2Linear (a : I → E →L[ℂ] ℂ)
    (hs : ∀ u, Summable (fun i => ‖a i u‖ ^ 2)) :
    E →ₗ[ℂ] lp (fun _ : I => ℂ) 2 where
  toFun u := ⟨fun i => a i u, coefficient_mem_l2 a hs u⟩
  map_add' u w := by
    apply lp.ext
    funext i
    exact map_add (a i) u w
  map_smul' c u := by
    apply lp.ext
    funext i
    exact map_smul (a i) c u

private theorem coefficientL2Linear_bound (a : I → E →L[ℂ] ℂ)
    (hs : ∀ u, Summable (fun i => ‖a i u‖ ^ 2))
    (hb : ∀ u, (∑' i, ‖a i u‖ ^ 2) ≤ ‖u‖ ^ 2) (u : E) :
    ‖coefficientL2Linear a hs u‖ ≤ ‖u‖ := by
  apply lp.norm_le_of_tsum_le (by norm_num) (norm_nonneg u)
  change (∑' i, ‖a i u‖ ^ (2 : ENNReal).toReal) ≤ ‖u‖ ^ (2 : ENNReal).toReal
  simpa using hb u

private def coefficientL2Map (a : I → E →L[ℂ] ℂ)
    (hs : ∀ u, Summable (fun i => ‖a i u‖ ^ 2))
    (hb : ∀ u, (∑' i, ‖a i u‖ ^ 2) ≤ ‖u‖ ^ 2) :
    E →L[ℂ] lp (fun _ : I => ℂ) 2 :=
  (coefficientL2Linear a hs).mkContinuous 1 (fun u => by
    simpa only [one_mul] using coefficientL2Linear_bound a hs hb u)

private theorem contraction_norm_one {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (A : E →L[ℂ] F) (hA : ∀ u, ‖A u‖ ≤ ‖u‖)
    (v : E) (hv : ‖v‖ = 1) (hAv : ‖A v‖ = 1) : ‖A‖ = 1 := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro u
    simpa only [one_mul] using hA u
  · have h := A.le_opNorm v
    simpa only [hAv, hv, mul_one] using h


private theorem bessel_analysis_bound
    (a : I → E →L[ℂ] ℂ)
    (hs : ∀ u, Summable (fun i => ‖a i u‖ ^ 2))
    (hb : ∀ u, (∑' i, ‖a i u‖ ^ 2) ≤ ‖u‖ ^ 2) (u : E) :
    ‖coefficientL2Map a hs hb u‖ ≤ ‖u‖ := coefficientL2Linear_bound a hs hb u

private theorem split_analysis_norm_one
    (A : E →L[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E)
    (hA : ∀ u, ‖A u‖ ≤ ‖u‖) (hAS : ∀ c, A (S c) = c)
    (v : ℕ → E) (hv : ∀ i, ‖v i‖ = 1)
    (hS : ∀ i z, S (lp.single 2 i z) = z • v i) : ‖A‖ = 1 := by
  apply contraction_norm_one A hA (v 0) (hv 0)
  have h := hAS (lp.single 2 0 (1 : ℂ))
  rw [hS, one_smul] at h
  rw [h, lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one]

end Analysis
section Projection
variable {I E : Type*} [DecidableEq I] [NormedAddCommGroup E] [NormedSpace ℂ E]

private theorem sparse_coeff_off_range
    (a : I → E →L[ℂ] ℂ) (f : ℕ → I) (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E)
    (hfull : ∀ c ξ, a ξ (S c) = ∑' i, if ξ = f i then c i else 0)
    (c : lp (fun _ : ℕ => ℂ) 2) (ξ : I) (hξ : ξ ∉ Set.range f) : a ξ (S c) = 0 := by
  rw [hfull]
  have hn (i : ℕ) : ξ ≠ f i := fun h => hξ ⟨i, h.symm⟩
  simp [hn]

private theorem sparse_analysis_synthesis_identity
    (a : I → E →L[ℂ] ℂ) (f : ℕ → I)
    (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E) (A : E →L[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (hA : ∀ u i, A u i = a (f i) u) (hS : ∀ c i, a (f i) (S c) = c i)
    (c : lp (fun _ : ℕ => ℂ) 2) : A (S c) = c := by
  apply lp.ext
  funext i
  rw [hA, hS]

private theorem sparse_synthesis_range_iff_support
    (a : I → E →L[ℂ] ℂ) (f : ℕ → I)
    (ha : Function.Injective (fun u : E => fun ξ => a ξ u))
    (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E) (A : E →L[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (hA : ∀ u i, A u i = a (f i) u) (hS : ∀ c i, a (f i) (S c) = c i)
    (hfull : ∀ c ξ, a ξ (S c) = ∑' i, if ξ = f i then c i else 0) (u : E) :
    u ∈ Set.range S ↔ Function.support (fun ξ => a ξ u) ⊆ Set.range f := by
  constructor
  · rintro ⟨c, rfl⟩ ξ hξ
    by_contra hnot
    exact hξ (sparse_coeff_off_range a f S hfull c ξ hnot)
  · intro hs
    refine ⟨A u, ha ?_⟩
    funext ξ
    change a ξ (S (A u)) = a ξ u
    by_cases hξ : ξ ∈ Set.range f
    · rcases hξ with ⟨i, rfl⟩
      rw [hS, hA]
    · rw [sparse_coeff_off_range a f S hfull (A u) ξ hξ]
      symm
      by_contra hne
      exact hξ (hs hne)

private theorem sparse_projection_coefficients
    (a : I → E →L[ℂ] ℂ) (f : ℕ → I)
    (S : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] E) (A : E →L[ℂ] lp (fun _ : ℕ => ℂ) 2)
    (hA : ∀ u i, A u i = a (f i) u) (hS : ∀ c i, a (f i) (S c) = c i)
    (hfull : ∀ c ξ, a ξ (S c) = ∑' i, if ξ = f i then c i else 0) (u : E) (ξ : I) :
    a ξ (S (A u)) = if ξ ∈ Set.range f then a ξ u else 0 := by
  classical
  by_cases hξ : ξ ∈ Set.range f
  · rw [if_pos hξ]
    rcases hξ with ⟨i, rfl⟩
    rw [hS, hA]
  · rw [if_neg hξ, sparse_coeff_off_range a f S hfull (A u) ξ hξ]

private theorem split_projection_idempotent
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (S : F →L[ℂ] E) (A : E →L[ℂ] F) (h : ∀ c, A (S c) = c) (u : E) :
    S (A (S (A u))) = S (A u) := by rw [h]

private theorem split_projection_range
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (S : F →L[ℂ] E) (A : E →L[ℂ] F) (h : ∀ c, A (S c) = c) :
    Set.range (S.comp A) = Set.range S := by
  apply Set.Subset.antisymm
  · rintro _ ⟨u, rfl⟩
    exact ⟨A u, rfl⟩
  · rintro _ ⟨c, rfl⟩
    exact ⟨S c, congrArg S (h c)⟩

private theorem spectral_mask_commutes
    (a : I → E →L[ℂ] ℂ) (ha : Function.Injective (fun u : E => fun ξ => a ξ u))
    (P T : E →L[ℂ] E) (D : Set I) (z : I → ℂ)
    (hP : ∀ u ξ, a ξ (P u) = if ξ ∈ D then a ξ u else 0)
    (hT : ∀ u ξ, a ξ (T u) = z ξ * a ξ u) (u : E) : P (T u) = T (P u) := by
  classical
  apply ha
  funext ξ
  change a ξ (P (T u)) = a ξ (T (P u))
  rw [hP, hT, hT, hP]
  by_cases hξ : ξ ∈ D <;> simp [hξ]
end Projection
private theorem actual_sparse_bessel (b : ℝ) (k : ℕ)
    (u : causalFrequencySpace b) (s : Finset ℕ) :
    ∑ i ∈ s, ‖causalFrequencyCoefficient b (causalFrequencySparseFrequency b k i) u‖ ^ 2 ≤
      ‖u‖ ^ 2 := by
  classical
  simpa only [Finset.sum_image (fun i _ j _ h =>
    (causalFrequencySparseFrequency_strictMono b k).injective h)] using
    causalFrequencyCoefficient_bessel b u (s.image (causalFrequencySparseFrequency b k))

private theorem actual_sparse_coefficients_summable (b : ℝ) (k : ℕ) (u : causalFrequencySpace b) :
    Summable (fun i => ‖causalFrequencyCoefficient b (causalFrequencySparseFrequency b k i) u‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (actual_sparse_bessel b k u)

private theorem actual_sparse_coefficients_tsum_le (b : ℝ) (k : ℕ) (u : causalFrequencySpace b) :
    (∑' i, ‖causalFrequencyCoefficient b (causalFrequencySparseFrequency b k i) u‖ ^ 2) ≤ ‖u‖ ^ 2 :=
  Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) (actual_sparse_bessel b k u)

/-- Contractive extraction of the canonical coefficients at the selected sparse
frequencies from an arbitrary actual completed chain. -/
def causalFrequencySparseAnalysis (b : ℝ) (k : ℕ) :
    causalFrequencySpace b →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  coefficientL2Map (fun i => causalFrequencyCoefficient b (causalFrequencySparseFrequency b k i))
    (actual_sparse_coefficients_summable b k) (actual_sparse_coefficients_tsum_le b k)

/-- Selecting sparse amplitudes is contractive in the canonical ℓ² norm. -/
theorem causalFrequencySparseAnalysis_norm_le (b : ℝ) (k : ℕ) (u : causalFrequencySpace b) :
    ‖causalFrequencySparseAnalysis b k u‖ ≤ ‖u‖ :=
  bessel_analysis_bound _ (actual_sparse_coefficients_summable b k)
    (actual_sparse_coefficients_tsum_le b k) u

/-- Analysis is an exact left inverse of completed sparse synthesis. -/
theorem causalFrequencySparseAnalysis_synthesis (b : ℝ) (k : ℕ)
    (c : lp (fun _ : ℕ => ℂ) 2) :
    causalFrequencySparseAnalysis b k (causalFrequencySparseSynthesis b k c) = c :=
  sparse_analysis_synthesis_identity (causalFrequencyCoefficient b)
    (causalFrequencySparseFrequency b k) (causalFrequencySparseSynthesis b k)
    (causalFrequencySparseAnalysis b k) (fun _ _ => rfl)
    (causalFrequencyCoefficient_sparseSynthesis_selected b k) c

/-- Sparse amplitude extraction has sharp operator norm one. -/
theorem norm_causalFrequencySparseAnalysis (b : ℝ) (k : ℕ) :
    ‖causalFrequencySparseAnalysis b k‖ = 1 :=
  split_analysis_norm_one (causalFrequencySparseAnalysis b k) (causalFrequencySparseSynthesis b k)
    (causalFrequencySparseAnalysis_norm_le b k) (causalFrequencySparseAnalysis_synthesis b k)
    (fun i => causalFrequencyMode b (causalFrequencySparseFrequency b k i))
    (fun i => norm_causalBoundedUnitEigenchain b _) (causalFrequencySparseSynthesis_single b k)

/-- The closed sparse image is exactly the actual vectors whose canonical
coefficient support is contained in the selected frequency set. -/
theorem causalFrequencySparseSynthesis_range_iff_support (b : ℝ) (k : ℕ)
    (u : causalFrequencySpace b) :
    u ∈ Set.range (causalFrequencySparseSynthesis b k) ↔
      Function.support (fun ξ => causalFrequencyCoefficient b ξ u) ⊆
        Set.range (causalFrequencySparseFrequency b k) :=
  sparse_synthesis_range_iff_support (causalFrequencyCoefficient b)
    (causalFrequencySparseFrequency b k) (causalFrequencyCoefficient_injective b)
    (causalFrequencySparseSynthesis b k) (causalFrequencySparseAnalysis b k)
    (fun _ _ => rfl) (causalFrequencyCoefficient_sparseSynthesis_selected b k)
    (causalFrequencyCoefficient_sparseSynthesis b k) u

/-- Bounded spectral projection onto the closed sparse ℓ² copy. -/
def causalFrequencySparseProjection (b : ℝ) (k : ℕ) :
    causalFrequencySpace b →L[ℂ] causalFrequencySpace b :=
  (causalFrequencySparseSynthesis b k).comp (causalFrequencySparseAnalysis b k)

/-- The projection retains precisely the selected canonical coefficients. -/
theorem causalFrequencyCoefficient_sparseProjection (b : ℝ) (k : ℕ)
    (u : causalFrequencySpace b) (ξ : ℝ) :
    causalFrequencyCoefficient b ξ (causalFrequencySparseProjection b k u) =
      if ξ ∈ Set.range (causalFrequencySparseFrequency b k) then
        causalFrequencyCoefficient b ξ u else 0 :=
  sparse_projection_coefficients (causalFrequencyCoefficient b) (causalFrequencySparseFrequency b k)
    (causalFrequencySparseSynthesis b k) (causalFrequencySparseAnalysis b k) (fun _ _ => rfl)
    (causalFrequencyCoefficient_sparseSynthesis_selected b k)
    (causalFrequencyCoefficient_sparseSynthesis b k) u ξ

/-- Applying the sparse spectral projection twice has the same effect as once. -/
theorem causalFrequencySparseProjection_idempotent (b : ℝ) (k : ℕ)
    (u : causalFrequencySpace b) :
    causalFrequencySparseProjection b k (causalFrequencySparseProjection b k u) =
      causalFrequencySparseProjection b k u :=
  split_projection_idempotent _ _ (causalFrequencySparseAnalysis_synthesis b k) u

/-- The spectral projection has exactly the closed sparse synthesis image. -/
theorem causalFrequencySparseProjection_range (b : ℝ) (k : ℕ) :
    Set.range (causalFrequencySparseProjection b k) =
      Set.range (causalFrequencySparseSynthesis b k) :=
  split_projection_range _ _ (causalFrequencySparseAnalysis_synthesis b k)

/-- The sparse spectral projections can have operator norm arbitrarily close to one. -/
theorem causalFrequencySparseProjection_norm_le (b : ℝ) (k : ℕ) :
    ‖causalFrequencySparseProjection b k‖ ≤ Real.sqrt (1 + 1 / ((k : ℝ) + 1)) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  exact (causalFrequencySparseSynthesis_norm_le b k (causalFrequencySparseAnalysis b k u)).trans
    (mul_le_mul_of_nonneg_left (causalFrequencySparseAnalysis_norm_le b k u) (Real.sqrt_nonneg _))

/-- Sparse spectral selection commutes with the actual derivative shift. -/
theorem causalFrequencySparseProjection_shift (b : ℝ) (k : ℕ) (u : causalFrequencySpace b) :
    causalFrequencySparseProjection b k (causalFrequencyShift b u) =
      causalFrequencyShift b (causalFrequencySparseProjection b k u) :=
  spectral_mask_commutes (causalFrequencyCoefficient b) (causalFrequencyCoefficient_injective b)
    (causalFrequencySparseProjection b k) (causalFrequencyShift b).toLinearIsometry.toContinuousLinearMap
    (Set.range (causalFrequencySparseFrequency b k)) (fun ξ => (causalUnitBoundaryRate b ξ).val)
    (causalFrequencyCoefficient_sparseProjection b k) (fun u ξ => causalFrequencyCoefficient_shift b ξ u) u

/-- Sparse spectral selection also commutes with the inverse derivative shift. -/
theorem causalFrequencySparseProjection_shift_symm (b : ℝ) (k : ℕ) (u : causalFrequencySpace b) :
    causalFrequencySparseProjection b k ((causalFrequencyShift b).symm u) =
      (causalFrequencyShift b).symm (causalFrequencySparseProjection b k u) :=
  spectral_mask_commutes (causalFrequencyCoefficient b) (causalFrequencyCoefficient_injective b)
    (causalFrequencySparseProjection b k)
    (causalFrequencyShift b).symm.toLinearIsometry.toContinuousLinearMap
    (Set.range (causalFrequencySparseFrequency b k)) (fun ξ => (causalUnitBoundaryRate b ξ).val⁻¹)
    (causalFrequencyCoefficient_sparseProjection b k)
    (fun u ξ => causalFrequencyCoefficient_shift_symm b ξ u) u

end RHTower.FokasLenells
