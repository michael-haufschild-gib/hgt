import GaloisForLFunctions.RHTower.PaperHeatHankelOperator
import GaloisForLFunctions.HTGeometry.KernelClosedSpanInertia

/-! # Faithfulness of the completed heat-Hankel form

Polynomial tests are dense in the source-normalized Hilbert space. Positivity
and every finite strictly negative family therefore survive the completion.
-/

namespace RHTower.PaperHeatHankel
noncomputable section
open Filter Topology Polynomial GaloisForLFunctions.HTGeometry
open KernelClosedSpanInertia
open scoped ENNReal

theorem polynomialEmbedding_monomial (a : Time) (n : ℕ) (c : ℂ) :
    polynomialEmbedding a (monomial n c) = lp.single 2 n (c / (scale a n : ℂ)) := by
  apply lp.ext
  funext k
  change vector a (monomial n c) k = _
  rw [vector_apply]
  by_cases h : n = k
  · subst k
    simp
  · simp [coeff_monomial, lp.single_apply, h, Ne.symm h]

theorem single_mem_range (a : Time) (n : ℕ) (c : ℂ) :
    lp.single 2 n c ∈ LinearMap.range (polynomialEmbedding a) := by
  refine ⟨monomial n ((scale a n : ℂ) * c), ?_⟩
  rw [polynomialEmbedding_monomial]
  congr 1
  exact mul_div_cancel_left₀ c (Complex.ofReal_ne_zero.mpr (scale_pos a n).ne')

theorem polynomialEmbedding_dense (a : Time) : DenseRange (polynomialEmbedding a) := by
  intro x
  apply mem_closure_of_tendsto (lp.hasSum_single (by simp : (2 : ℝ≥0∞) ≠ ⊤) x)
  exact Filter.Eventually.of_forall fun s =>
    (LinearMap.range (polynomialEmbedding a)).sum_mem fun n _ => single_mem_range a n (x n)

theorem range_topologicalClosure (a : Time) :
    (LinearMap.range (polynomialEmbedding a)).topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp (polynomialEmbedding_dense a)

theorem operator_form_nonneg_iff_rh (a : Time) :
    (∀ x : Space, 0 ≤ (inner ℂ x (operator a x)).re) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply (riemannHypothesis_iff_heatHankel_nonneg a.property).mpr
    intro P
    rw [← inner_vector_operator a P P]
    exact h _
  · intro hRH
    have hcont : Continuous fun x : Space => (inner ℂ x (operator a x)).re := by fun_prop
    have hclosed : IsClosed {x : Space | 0 ≤ (inner ℂ x (operator a x)).re} :=
      isClosed_Ici.preimage hcont
    intro x
    apply hclosed.closure_subset_iff.mpr _ (polynomialEmbedding_dense a x)
    rintro _ ⟨P, rfl⟩
    change 0 ≤ (inner ℂ (vector a P) (operator a (vector a P))).re
    rw [inner_vector_operator]
    exact (riemannHypothesis_iff_heatHankel_nonneg a.property).mp hRH P

theorem operator_positive_iff_rh (a : Time) : (operator a).IsPositive ↔ RiemannHypothesis := by
  rw [ContinuousLinearMap.isPositive_def']
  constructor
  · rintro ⟨_, h⟩
    apply (operator_form_nonneg_iff_rh a).mp
    intro x
    have hx := h x
    change 0 ≤ (inner ℂ (operator a x) x).re at hx
    rwa [show (inner ℂ (operator a x) x).re = (inner ℂ x (operator a x)).re from
      inner_re_symm (𝕜 := ℂ) _ _] at hx
  · intro hRH
    refine ⟨operator_selfAdjoint a, fun x => ?_⟩
    have h := (operator_form_nonneg_iff_rh a).mpr hRH x
    change 0 ≤ (inner ℂ (operator a x) x).re
    rwa [show (inner ℂ (operator a x) x).re = (inner ℂ x (operator a x)).re from
      inner_re_symm (𝕜 := ℂ) _ _]

/-- Each finite negative family in the completed space has an exact polynomial counterpart. -/
theorem exists_negativeTuple_iff_polynomials (a : Time) (r : ℕ) :
    (∃ v : Fin r → Space, IsNegativeTuple (operator a) v) ↔
      ∃ P : Fin r → ℂ[X], ∀ c : Fin r → ℂ, c ≠ 0 →
        (heatHankel a.val (∑ i, c i • P i) (∑ i, c i • P i)).re < 0 := by
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨y, hy, hn⟩ := exists_negativeTuple_mem_of_mem_topologicalClosure
      (operator a) (LinearMap.range (polynomialEmbedding a)) v
      (fun _ => by rw [range_topologicalClosure]; trivial) hv
    choose P hP using hy
    refine ⟨P, fun c hc => ?_⟩
    have h := isNegativeTuple_quadratic_neg (operator a) hn hc
    have he : sectionSynthesis y c = polynomialEmbedding a (∑ i, c i • P i) := by
      simp only [sectionSynthesis, map_sum, map_smul, hP]
    rw [sectionQuadratic, he] at h
    exact (congrArg Complex.re (inner_vector_operator a _ _)) ▸ h
  · rintro ⟨P, hP⟩
    refine ⟨fun i => polynomialEmbedding a (P i), fun c hc => ?_⟩
    have hne : c ≠ 0 := by intro hz; simp [hz] at hc
    have he : sectionSynthesis (fun i => polynomialEmbedding a (P i)) c =
        polynomialEmbedding a (∑ i, c i • P i) := by
      simp only [sectionSynthesis, map_sum, map_smul]
    rw [sectionQuadratic, he]
    change (inner ℂ (vector a _) (operator a (vector a _))).re < 0
    rw [inner_vector_operator]
    exact hP c hne

end
end RHTower.PaperHeatHankel
