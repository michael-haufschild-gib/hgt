import GaloisForLFunctions.HTGeometry.BurnolDepthCompletion
import GaloisForLFunctions.RHTower.ExponentialMomentPolynomialSignCone

/-!
# Polynomial-square sign detection in a bounded coordinate

An injective measurable coordinate bounded by one has dense polynomial span in
`L²` of every finite measure. Hence its polynomial-square tests detect the sign
of every integrable real density, even when the underlying space is noncompact.
-/

open MeasureTheory Filter Set
open scoped ENNReal
namespace GaloisForLFunctions.BiScaleUncertainty.Observation
noncomputable section

section FiniteMeasure
variable {μ : Measure ℝ} [IsFiniteMeasure μ] {φ : ℝ → ℝ}
    (hφ : MeasurableEmbedding φ) (hb : ∀ᵐ x ∂μ, |φ x| ≤ 1)

include hφ hb

private lemma memLp_coordinateMonomial (n : ℕ) : MemLp (fun x => φ x^n) 2 μ := by
  apply MemLp.of_bound (hφ.measurable.pow_const n).aestronglyMeasurable 1
  filter_upwards [hb] with x hx
  simpa only [Real.norm_eq_abs,abs_pow] using pow_le_one₀ (abs_nonneg (φ x)) hx

/-- Powers of the bounded coordinate as actual square-integrable functions. -/
def coordinateMonomial (n : ℕ) : Lp ℝ 2 μ :=
  (memLp_coordinateMonomial hφ hb n).toLp _

lemma coordinateMonomial_ae (n : ℕ) :
    (coordinateMonomial hφ hb n : ℝ → ℝ) =ᵐ[μ] fun x => φ x^n :=
  (memLp_coordinateMonomial hφ hb n).coeFn_toLp

def coordinatePolynomialSpan : Submodule ℝ (Lp ℝ 2 μ) :=
  Submodule.span ℝ (range (coordinateMonomial hφ hb))

/-- Bounded-coordinate moment determinacy kills the orthogonal complement. -/
theorem coordinatePolynomialSpan_orthogonal : (coordinatePolynomialSpan hφ hb)ᗮ=⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun v hv => ?_
  have hint : Integrable (v : ℝ → ℝ) μ :=
    memLp_one_iff_integrable.mp ((Lp.memLp v).mono_exponent (by norm_num))
  have hmom (n : ℕ) : (∫ x, φ x^n*v x ∂μ)=0 := by
    have h := (Submodule.mem_orthogonal _ v).mp hv (coordinateMonomial hφ hb n)
      (Submodule.subset_span ⟨n,rfl⟩)
    rw [L2.inner_def] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards [coordinateMonomial_ae hφ hb n] with x hx
    rw [hx]
    simp [RCLike.inner_apply,mul_comm]
  exact Lp.eq_zero_iff_ae_eq_zero.mpr
    (_root_.HTGeometry.ae_eq_zero_of_boundedCoordinate_moments hφ hb hint hmom)

/-- Coordinate polynomials are dense without compactness of the original measure space. -/
theorem coordinatePolynomialSpan_dense : Dense (coordinatePolynomialSpan hφ hb : Set (Lp ℝ 2 μ)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.topologicalClosure_eq_top_iff.mpr (coordinatePolynomialSpan_orthogonal hφ hb))

lemma exists_polynomial_coordinate_of_mem {v : Lp ℝ 2 μ}
    (hv : v ∈ coordinatePolynomialSpan hφ hb) :
    ∃ P : Polynomial ℝ, v =ᵐ[μ] fun x => P.eval (φ x) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨n,rfl⟩ := hv
    exact ⟨Polynomial.X^n,by simpa only [Polynomial.eval_X_pow] using coordinateMonomial_ae hφ hb n⟩
  | zero =>
    refine ⟨0,?_⟩
    filter_upwards [Lp.coeFn_zero ℝ 2 μ] with x hx
    simpa using hx
  | add u v _ _ hu hv =>
    obtain ⟨P,hP⟩ := hu
    obtain ⟨Q,hQ⟩ := hv
    refine ⟨P+Q,?_⟩
    filter_upwards [Lp.coeFn_add u v,hP,hQ] with x huv hx hy
    rw [huv]
    change u x+v x=_
    rw [hx,hy,Polynomial.eval_add]
  | smul c v _ hv =>
    obtain ⟨P,hP⟩ := hv
    refine ⟨c • P,?_⟩
    filter_upwards [Lp.coeFn_smul c v,hP] with x hcv hx
    rw [hcv]
    change c*v x=_
    rw [hx,Polynomial.eval_smul]
    rfl

/-- Polynomial-coordinate squares detect every bounded multiplier's sign. -/
theorem coordinatePolynomialSquare_nonnegative_iff (J : ℝ → ℝ) (hJ : MemLp J ∞ μ) :
    (∀ P : Polynomial ℝ, 0 ≤ ∫ x, (P.eval (φ x))^2*J x ∂μ) ↔ 0 ≤ᵐ[μ] J := by
  constructor
  · intro hpoly
    have hspan : (coordinatePolynomialSpan hφ hb : Set (Lp ℝ 2 μ)) ⊆
        {v | 0 ≤ RHTower.linftyMultiplierQuadratic J hJ v} := by
      intro v hv
      obtain ⟨P,hP⟩ := exists_polynomial_coordinate_of_mem hφ hb hv
      change 0 ≤ RHTower.linftyMultiplierQuadratic J hJ v
      rw [RHTower.linftyMultiplierQuadratic_eq_integral]
      have he : (∫ x, (v x)^2*J x ∂μ)=(∫ x, (P.eval (φ x))^2*J x ∂μ) := by
        apply integral_congr_ae
        filter_upwards [hP] with x hx
        rw [hx]
      rw [he]
      exact hpoly P
    have hclosed : IsClosed {v | 0 ≤ RHTower.linftyMultiplierQuadratic J hJ v} :=
      isClosed_le continuous_const (RHTower.continuous_linftyMultiplierQuadratic J hJ)
    have hall (v : Lp ℝ 2 μ) : 0 ≤ RHTower.linftyMultiplierQuadratic J hJ v :=
      closure_minimal hspan hclosed ((coordinatePolynomialSpan_dense hφ hb) v)
    have hJint : Integrable J μ := memLp_one_iff_integrable.mp (hJ.mono_exponent (by simp))
    apply ae_nonneg_of_forall_setIntegral_nonneg hJint
    intro s hs hsmu
    let v : Lp ℝ 2 μ := indicatorConstLp 2 hs hsmu.ne (1:ℝ)
    have hv := hall v
    rw [RHTower.linftyMultiplierQuadratic_eq_integral] at hv
    have he : (fun x => (v x)^2*J x) =ᵐ[μ] s.indicator J := by
      filter_upwards [indicatorConstLp_coeFn (p := 2) (μ := μ)
        (s := s) (hs := hs) (hμs := hsmu.ne) (c := (1:ℝ))] with x hx
      by_cases hxs : x ∈ s
      · rw [hx,Set.indicator_of_mem hxs]
        simp [hxs]
      · rw [hx,Set.indicator_of_notMem hxs]
        simp [hxs]
    rw [integral_congr_ae he] at hv
    simpa only [integral_indicator hs] using hv
  · intro h P
    exact integral_nonneg_of_ae (h.mono fun x hx => mul_nonneg (sq_nonneg _) hx)
end FiniteMeasure

/-- Polynomial-square coordinate tests detect the sign of any integrable real density. -/
theorem density_nonnegative_iff_coordinate_squares {μ : Measure ℝ} {φ f : ℝ → ℝ}
    (hφ : MeasurableEmbedding φ) (hb : ∀ᵐ x ∂μ, |φ x| ≤ 1)
    (hfm : Measurable f) (hf : Integrable f μ) :
    (∀ P : Polynomial ℝ, 0 ≤ ∫ x, (P.eval (φ x))^2*f x ∂μ) ↔ 0 ≤ᵐ[μ] f := by
  constructor
  · intro hpoly
    let ρ : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal |f x|
    let ν : Measure ℝ := μ.withDensity ρ
    let J : ℝ → ℝ := fun x => if 0 ≤ f x then 1 else -1
    have hρm : Measurable ρ := ENNReal.measurable_ofReal.comp hfm.abs
    letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hf.abs.hasFiniteIntegral
    have hJm : Measurable J := Measurable.ite (measurableSet_le measurable_const hfm)
      measurable_const measurable_const
    have hJ : MemLp J ∞ ν := by
      apply memLp_top_of_bound hJm.aestronglyMeasurable 1
      filter_upwards [] with x
      dsimp only [J]
      split_ifs <;> norm_num
    have hbν : ∀ᵐ x ∂ν, |φ x| ≤ 1 := (withDensity_absolutelyContinuous μ ρ).ae_le hb
    have htest (P : Polynomial ℝ) : 0 ≤ ∫ x, (P.eval (φ x))^2*J x ∂ν := by
      change 0 ≤ ∫ x, (P.eval (φ x))^2*J x ∂μ.withDensity ρ
      rw [integral_withDensity_eq_integral_toReal_smul hρm
        (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
      have he : (∫ x, (ρ x).toReal • ((P.eval (φ x))^2*J x) ∂μ)=
          ∫ x, (P.eval (φ x))^2*f x ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp only [ρ,J]
        rw [ENNReal.toReal_ofReal (abs_nonneg _),smul_eq_mul]
        split_ifs with hx
        · rw [abs_of_nonneg hx]
          ring
        · rw [abs_of_neg (lt_of_not_ge hx)]
          ring
      rw [he]
      exact hpoly P
    have hJpos := (coordinatePolynomialSquare_nonnegative_iff hφ hbν J hJ).mp htest
    have hback := (ae_withDensity_iff hρm).mp hJpos
    filter_upwards [hback] with x hx
    change 0 ≤ f x
    by_contra hneg
    have hfx : f x < 0 := lt_of_not_ge hneg
    have hρne : ρ x ≠ 0 := (ENNReal.ofReal_pos.mpr (abs_pos.mpr hfx.ne)).ne'
    have h := hx hρne
    dsimp only [J] at h
    rw [if_neg hneg] at h
    norm_num at h
  · intro h P
    exact integral_nonneg_of_ae (h.mono fun x hx => mul_nonneg (sq_nonneg _) hx)

#print axioms coordinatePolynomialSpan_dense
#print axioms coordinatePolynomialSquare_nonnegative_iff
#print axioms density_nonnegative_iff_coordinate_squares
end
end GaloisForLFunctions.BiScaleUncertainty.Observation
