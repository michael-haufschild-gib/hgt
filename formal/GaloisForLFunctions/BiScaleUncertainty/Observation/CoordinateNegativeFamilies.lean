import GaloisForLFunctions.HilbertMetric.Spectral.DenseNegativeFamilies
import GaloisForLFunctions.BiScaleUncertainty.Observation.BoundedCoordinateSignCone

/-!
# Polynomial realization of finite signed index

Dense polynomial test classes retain finite strictly negative families of bounded
signed multipliers. Disjoint negative windows supply such families explicitly.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
open HilbertMetric

private theorem coeFn_sum_smul_ae {μ : Measure ℝ} {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (v : ι → Lp ℝ 2 μ) :
    ((∑ i ∈ s, c i • v i : Lp ℝ 2 μ) : ℝ → ℝ) =ᵐ[μ]
      fun x => ∑ i ∈ s, c i * v i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa only [Pi.zero_apply] using hx
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (c i • v i) (∑ j ∈ s, c j • v j),
      Lp.coeFn_smul (c i) (v i), ih] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, smul_eq_mul, Finset.sum_insert hi]

/-- A dense polynomial test class realizes every finite negative family of a bounded signed multiplier. -/
theorem exists_negative_polynomial_family_in_dense_submodule {μ : Measure ℝ}
    (φ : ℝ → ℝ) (S : Submodule ℝ (Lp ℝ 2 μ)) (hS : Dense (S : Set (Lp ℝ 2 μ)))
    (Good : Polynomial ℝ → Prop)
    (hrep : ∀ v ∈ S, ∃ P : Polynomial ℝ, Good P ∧ v =ᵐ[μ] fun x => P.eval (φ x))
    (J : ℝ → ℝ) (hJ : MemLp J ∞ μ) (n : ℕ) (v : Fin n → Lp ℝ 2 μ)
    (hv : ∀ c : Fin n → ℝ, c ≠ 0 →
      finiteFamilyQuadratic (_root_.RHTower.linftyMultiplierOperator J hJ) v c < 0) :
    ∃ P : Fin n → Polynomial ℝ, (∀ i, Good (P i)) ∧ ∀ c : Fin n → ℝ, c ≠ 0 →
      (∫ x, (∑ i, c i * (P i).eval (φ x)) ^ 2 * J x ∂μ) < 0 := by
  classical
  obtain ⟨w, hwS, hw, _⟩ := exists_negative_family_in_dense_submodule
    (_root_.RHTower.linftyMultiplierOperator J hJ) S hS v hv
  choose P hgood hP using fun i => hrep (w i) (hwS i)
  refine ⟨P, hgood, fun c hc => ?_⟩
  have hneg := hw c hc
  change _root_.RHTower.linftyMultiplierQuadratic J hJ (∑ i, c i • w i) < 0 at hneg
  rw [_root_.RHTower.linftyMultiplierQuadratic_eq_integral] at hneg
  have he : ((∑ i, c i • w i : Lp ℝ 2 μ) : ℝ → ℝ) =ᵐ[μ]
      fun x => ∑ i, c i * (P i).eval (φ x) := by
    filter_upwards [coeFn_sum_smul_ae Finset.univ c w, ae_all_iff.mpr hP] with x hx hPx
    rw [hx]
    exact Finset.sum_congr rfl (fun i _ => by rw [hPx i])
  have hint : (∫ x, (∑ i, c i • w i : Lp ℝ 2 μ) x ^ 2 * J x ∂μ) =
      (∫ x, (∑ i, c i * (P i).eval (φ x)) ^ 2 * J x ∂μ) := by
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]
  exact hint ▸ hneg

/-- Polynomial-coordinate tests retain every finite negative index of a bounded signed multiplier. -/
theorem exists_negative_coordinate_polynomial_family {μ : Measure ℝ} [IsFiniteMeasure μ]
    {φ : ℝ → ℝ} (hφ : MeasurableEmbedding φ) (hb : ∀ᵐ x ∂μ, |φ x| ≤ 1)
    (J : ℝ → ℝ) (hJ : MemLp J ∞ μ) (n : ℕ) (v : Fin n → Lp ℝ 2 μ)
    (hv : ∀ c : Fin n → ℝ, c ≠ 0 →
      finiteFamilyQuadratic (_root_.RHTower.linftyMultiplierOperator J hJ) v c < 0) :
    ∃ P : Fin n → Polynomial ℝ, ∀ c : Fin n → ℝ, c ≠ 0 →
      (∫ x, (∑ i, c i * (P i).eval (φ x)) ^ 2 * J x ∂μ) < 0 := by
  obtain ⟨P, _, hP⟩ := exists_negative_polynomial_family_in_dense_submodule φ
    (coordinatePolynomialSpan hφ hb) (coordinatePolynomialSpan_dense hφ hb)
    (fun _ => True) (fun w hw => by
      obtain ⟨P, hP⟩ := exists_polynomial_coordinate_of_mem hφ hb hw
      exact ⟨P, trivial, hP⟩) J hJ n v hv
  exact ⟨P, hP⟩

private theorem finiteFamilyQuadratic_diagonal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (B : E →L[ℝ] E) {n : ℕ} (v : Fin n → E)
    (hcross : ∀ i j, i ≠ j → inner ℝ (v i) (B (v j)) = 0) (c : Fin n → ℝ) :
    finiteFamilyQuadratic B v c = ∑ i, c i ^ 2 * inner ℝ (v i) (B (v i)) := by
  classical
  simp only [finiteFamilyQuadratic, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hji
    rw [hcross j i hji]
    ring
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private theorem linfty_inner_zero_of_disjoint {μ : Measure ℝ}
    (J : ℝ → ℝ) (hJ : MemLp J ∞ μ) (v w : Lp ℝ 2 μ)
    (hvw : ∀ᵐ x ∂μ, v x * w x = 0) :
    inner ℝ v (_root_.RHTower.linftyMultiplierOperator J hJ w) = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, (0 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards [_root_.RHTower.linftyMultiplierOperator_ae J hJ w, hvw] with x hx hd
      rw [hx, RCLike.inner_apply]
      change (J x * w x) * v x = 0
      calc
        _ = J x * (v x * w x) := by ring
        _ = 0 := by rw [hd, mul_zero]
    _ = 0 := integral_zero _ _

/-- Disjoint strictly negative square-integrable tests have a strictly negative diagonal Gram form. -/
theorem finiteFamilyQuadratic_neg_of_disjoint_tests {μ : Measure ℝ}
    (J : ℝ → ℝ) (hJ : MemLp J ∞ μ) (n : ℕ) (v : Fin n → Lp ℝ 2 μ)
    (hdisj : ∀ i j, i ≠ j → ∀ᵐ x ∂μ, v i x * v j x = 0)
    (hneg : ∀ i, _root_.RHTower.linftyMultiplierQuadratic J hJ (v i) < 0) :
    ∀ c : Fin n → ℝ, c ≠ 0 →
      finiteFamilyQuadratic (_root_.RHTower.linftyMultiplierOperator J hJ) v c < 0 := by
  intro c hc
  rw [finiteFamilyQuadratic_diagonal _ _ (fun i j hij =>
    linfty_inner_zero_of_disjoint J hJ (v i) (v j) (hdisj i j hij))]
  have he : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  obtain ⟨i, hi⟩ := he
  have hlt : (∑ j, c j ^ 2 * inner ℝ (v j) (_root_.RHTower.linftyMultiplierOperator J hJ (v j))) <
      ∑ _j : Fin n, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro j _
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hneg j).le
    · exact ⟨i, Finset.mem_univ _, mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hi) (hneg i)⟩
  simpa only [Finset.sum_const_zero] using hlt

/-- Disjoint negative tests produce equally large strictly negative polynomial test spaces. -/
theorem exists_negative_polynomials_of_disjoint_tests {μ : Measure ℝ} [IsFiniteMeasure μ]
    {φ : ℝ → ℝ} (hφ : MeasurableEmbedding φ) (hb : ∀ᵐ x ∂μ, |φ x| ≤ 1)
    (J : ℝ → ℝ) (hJ : MemLp J ∞ μ) (n : ℕ) (v : Fin n → Lp ℝ 2 μ)
    (hdisj : ∀ i j, i ≠ j → ∀ᵐ x ∂μ, v i x * v j x = 0)
    (hneg : ∀ i, _root_.RHTower.linftyMultiplierQuadratic J hJ (v i) < 0) :
    ∃ P : Fin n → Polynomial ℝ, ∀ c : Fin n → ℝ, c ≠ 0 →
      (∫ x, (∑ i, c i * (P i).eval (φ x)) ^ 2 * J x ∂μ) < 0 := by
  exact exists_negative_coordinate_polynomial_family hφ hb J hJ n v
    (finiteFamilyQuadratic_neg_of_disjoint_tests J hJ n v hdisj hneg)

#print axioms exists_negative_polynomials_of_disjoint_tests
#print axioms exists_negative_coordinate_polynomial_family
end GaloisForLFunctions.BiScaleUncertainty.Observation
