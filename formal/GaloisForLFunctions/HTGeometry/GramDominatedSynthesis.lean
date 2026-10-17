import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Synthesis from a bounded entrywise Gram majorant

If the absolute Gram entries of a Hilbert-space family are bounded by the real matrix of a
bounded operator on `ℓ²`, finite synthesis extends uniquely to the whole coefficient space.
The majorant is applied to the absolute values of the coefficients; no entrywise-to-Loewner
order implication is used.
-/

open Filter Topology
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {ι H : Type*} [DecidableEq ι] [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private def finiteL2Coordinates : (ι →₀ ℂ) →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 :=
  Finsupp.linearCombination ℂ (fun i => lp.single 2 i 1)

private theorem finiteL2Coordinates_single (i : ι) (z : ℂ) :
    finiteL2Coordinates (Finsupp.single i z) = lp.single 2 i z := by
  simp only [finiteL2Coordinates, Finsupp.linearCombination_single]
  simpa only [smul_eq_mul, mul_one] using
    (lp.single_smul (E := fun _ : ι => ℂ) 2 i z 1).symm

private theorem finiteL2Coordinates_sum (c : ι →₀ ℂ) :
    finiteL2Coordinates c = ∑ i ∈ c.support, lp.single 2 i (c i) := by
  simp only [finiteL2Coordinates, Finsupp.linearCombination_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun i _ => by
    simpa only [smul_eq_mul, mul_one] using
      (lp.single_smul (E := fun _ : ι => ℂ) 2 i (c i) 1).symm

private theorem finiteL2Coordinates_norm_sq (c : ι →₀ ℂ) :
    ‖finiteL2Coordinates c‖ ^ 2 = ∑ i ∈ c.support, ‖c i‖ ^ 2 := by
  rw [finiteL2Coordinates_sum]
  simpa using lp.norm_sum_single (E := fun _ : ι => ℂ)
    (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) c c.support

private theorem finiteL2Coordinates_dense :
    DenseRange (finiteL2Coordinates (ι := ι)) := by
  intro c
  apply mem_closure_of_tendsto (lp.hasSum_single (by norm_num) c)
  apply Filter.Eventually.of_forall
  intro s
  refine ⟨∑ i ∈ s, Finsupp.single i (c i), ?_⟩
  simp only [map_sum, finiteL2Coordinates_single]

/-- A bounded real matrix majorant controls every finite synthesis, including complex phases. -/
theorem norm_sq_sum_smul_le_of_gram_majorant
    (v : ι → H) {T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2}
    {K : ι → ι → ℝ} (hT : HasLpMatrix T fun i j => (K i j : ℂ))
    (hv : ∀ i j, ‖⟪v i, v j⟫_ℂ‖ ≤ K i j) (s : Finset ι) (c : ι → ℂ) :
    ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ ‖T‖ * ∑ i ∈ s, ‖c i‖ ^ 2 := by
  let z : lp (fun _ : ι => ℂ) 2 := ∑ i ∈ s, lp.single 2 i (‖c i‖ : ℂ)
  have hz : ‖z‖ ^ 2 = ∑ i ∈ s, ‖c i‖ ^ 2 := by
    simpa [z] using lp.norm_sum_single (E := fun _ : ι => ℂ)
      (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal) (fun i => (‖c i‖ : ℂ)) s
  have hmatrix : (⟪z, T z⟫_ℂ).re =
      ∑ i ∈ s, ∑ j ∈ s, ‖c i‖ * ‖c j‖ * K i j := by
    dsimp [z]
    rw [sum_inner]
    simp only [map_sum, inner_sum, lp.inner_single_left, RCLike.inner_apply]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsingle : lp.single 2 j (‖c j‖ : ℂ) = (‖c j‖ : ℂ) • lpBasisVec j := by
      simp [lpBasisVec, ← lp.single_smul]
    rw [hsingle, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hT i j]
    simp
    ring
  have hdom : ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ (⟪z, T z⟫_ℂ).re := by
    rw [hmatrix, norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner]
    simp only [inner_sum, inner_smul_left, inner_smul_right, map_sum]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    calc
      (c j * (conj (c i) * ⟪v i, v j⟫_ℂ)).re
          ≤ ‖c j * (conj (c i) * ⟪v i, v j⟫_ℂ)‖ := Complex.re_le_norm _
      _ = ‖c i‖ * ‖c j‖ * ‖⟪v i, v j⟫_ℂ‖ := by simp; ring
      _ ≤ ‖c i‖ * ‖c j‖ * K i j :=
        mul_le_mul_of_nonneg_left (hv i j) (by positivity)
  calc
    ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ (⟪z, T z⟫_ℂ).re := hdom
    _ ≤ ‖⟪z, T z⟫_ℂ‖ := Complex.re_le_norm _
    _ ≤ ‖z‖ * ‖T z‖ := norm_inner_le_norm _ _
    _ ≤ ‖z‖ * (‖T‖ * ‖z‖) := mul_le_mul_of_nonneg_left (T.le_opNorm z) (norm_nonneg _)
    _ = ‖T‖ * ∑ i ∈ s, ‖c i‖ ^ 2 := by rw [← hz]; ring

variable [CompleteSpace H]

/-- The extension of finite synthesis. Its column identity requires the finite bound below. -/
def finiteGramSynthesis (v : ι → H) : lp (fun _ : ι => ℂ) 2 →L[ℂ] H :=
  (Finsupp.linearCombination ℂ v).extendOfNorm finiteL2Coordinates

omit [CompleteSpace H] in
private theorem finite_synthesis_bound {v : ι → H} {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ s : Finset ι, ∀ c : ι → ℂ,
      ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ C * ∑ i ∈ s, ‖c i‖ ^ 2) (c : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ v c‖ ≤ Real.sqrt C * ‖finiteL2Coordinates c‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).1
  rw [mul_pow, Real.sq_sqrt hC, finiteL2Coordinates_norm_sq]
  simpa only [Finsupp.linearCombination_apply, Finsupp.sum] using hv c.support c

/-- The extension retains every original column and every complex coefficient. -/
theorem finiteGramSynthesis_single {v : ι → H} {C : ℝ} (hC : 0 ≤ C)
    (hv : ∀ s : Finset ι, ∀ c : ι → ℂ,
      ‖∑ i ∈ s, c i • v i‖ ^ 2 ≤ C * ∑ i ∈ s, ‖c i‖ ^ 2) (i : ι) (z : ℂ) :
    finiteGramSynthesis v (lp.single 2 i z) = z • v i := by
  have h := LinearMap.extendOfNorm_eq finiteL2Coordinates_dense
    ⟨Real.sqrt C, finite_synthesis_bound hC hv⟩ (Finsupp.single i z)
  simpa only [finiteGramSynthesis, finiteL2Coordinates_single,
    Finsupp.linearCombination_single] using h

/-- Complete source admission from a bounded matrix majorant. -/
theorem finiteGramSynthesis_single_of_majorant
    {v : ι → H} {T : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2}
    {K : ι → ι → ℝ} (hT : HasLpMatrix T fun i j => (K i j : ℂ))
    (hv : ∀ i j, ‖⟪v i, v j⟫_ℂ‖ ≤ K i j) (i : ι) (z : ℂ) :
    finiteGramSynthesis v (lp.single 2 i z) = z • v i :=
  finiteGramSynthesis_single (norm_nonneg T)
    (norm_sq_sum_smul_le_of_gram_majorant v hT hv) i z

end GaloisForLFunctions.HTGeometry
