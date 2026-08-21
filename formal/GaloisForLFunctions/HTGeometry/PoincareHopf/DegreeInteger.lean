import GaloisForLFunctions.HTGeometry.PoincareHopf.RegularValue

/-!
# The degree is an integer

The degree is locally constant in the value: shifting the value shifts the weight of the degree
integral, and translation invariance absorbs the shift.  By the measure-zero image of the critical
set, every value has regular values arbitrarily close to it, and at a regular value the degree is a
finite sum of signs.  Hence the degree is always an integer.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)} {y : Fin n → ℝ} {ρ : ℝ}

theorem jac_sub_const (f : (Fin n → ℝ) → (Fin n → ℝ)) (y x : Fin n → ℝ) :
    jac (fun z => f z - y) x = jac f x := by
  funext a b
  rw [jac, jac, Matrix.of_apply, Matrix.of_apply, fderiv_sub_const]

theorem det_fderiv_eq_det_jac (f : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) :
    ContinuousLinearMap.det (fderiv ℝ f x) = (jac f x).det := by
  have hmat : LinearMap.toMatrix'
      ((fderiv ℝ f x : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
      = jac f x := by
    funext a b
    rw [LinearMap.toMatrix'_apply, jac, Matrix.of_apply]
    congr 1
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', hmat]

theorem admissibleRadius_sub_const :
    AdmissibleRadius (fun x => f x - y) Ω 0 ρ ↔ AdmissibleRadius f Ω y ρ := by
  constructor <;>
    exact fun h => ⟨h.1, fun x hx => by simpa using h.2 x hx⟩

theorem degree_sub_const (hf : ContDiff ℝ 2 f) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) :
    degree (fun x => f x - y) Ω 0 = degree f Ω y := by
  classical
  by_cases hex : ∃ ρ, AdmissibleRadius f Ω y ρ
  · obtain ⟨ρ₀, hadm⟩ := hex
    have hadm' : AdmissibleRadius (fun x => f x - y) Ω 0 ρ₀ := admissibleRadius_sub_const.mpr hadm
    rw [degree_eq_degIntegral (hf.sub contDiff_const) hΩ hΩb hadm' (bumpWeight_contDiff hadm.1)
        (bumpWeight_eq_zero hadm.1) (bumpWeight_integral hadm.1),
      degree_eq_degIntegral hf hΩ hΩb hadm (bumpWeight_contDiff hadm.1)
        (bumpWeight_eq_zero hadm.1) (bumpWeight_integral hadm.1)]
    simp only [degIntegral, sub_zero]
  · have hex' : ¬ ∃ ρ, AdmissibleRadius (fun x => f x - y) Ω 0 ρ := by
      rintro ⟨ρ₀, h⟩
      exact hex ⟨ρ₀, admissibleRadius_sub_const.mp h⟩
    rw [degree, degree, dif_neg hex, dif_neg hex']

/-- **Local constancy of the degree in the value.** -/
theorem degree_eq_of_close (hf : ContDiff ℝ 2 f) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hadm : AdmissibleRadius f Ω y ρ) {y' : Fin n → ℝ} (hy' : ‖y' - y‖ ≤ ρ / 2) :
    degree f Ω y' = degree f Ω y := by
  have hρ : 0 < ρ := hadm.1
  have hhalf : 0 < ρ / 2 := by linarith
  have hbc : ContDiff ℝ 1 (bumpWeight (n := n) (ρ / 2)) := bumpWeight_contDiff hhalf
  have hbs : ∀ w : Fin n → ℝ, ρ / 2 ≤ ‖w‖ → bumpWeight (ρ / 2) w = 0 := bumpWeight_eq_zero hhalf
  have hbm : ∫ w, bumpWeight (n := n) (ρ / 2) w = 1 := bumpWeight_integral hhalf
  have hadmy : AdmissibleRadius f Ω y (ρ / 2) := by
    refine ⟨hhalf, fun x hx => ?_⟩
    have := hadm.2 x hx
    linarith
  have hadmy' : AdmissibleRadius f Ω y' (ρ / 2) := by
    refine ⟨hhalf, fun x hx => ?_⟩
    have h1 := hadm.2 x hx
    have h2 : ‖f x - y‖ - ‖y' - y‖ ≤ ‖f x - y'‖ := by
      have h3 : ‖f x - y‖ ≤ ‖f x - y'‖ + ‖y' - y‖ := by
        have := norm_add_le (f x - y') (y' - y)
        simpa using this
      linarith
    linarith
  rw [degree_eq_degIntegral hf hΩ hΩb hadmy' hbc hbs hbm,
    degree_eq_degIntegral hf hΩ hΩb hadmy hbc hbs hbm]
  have hshift : degIntegral (fun x => f x - y') Ω (bumpWeight (ρ / 2))
      = degIntegral (fun x => f x - y) Ω (fun w => bumpWeight (ρ / 2) (w - (y' - y))) := by
    simp only [degIntegral, jac_sub_const]
    refine MeasureTheory.setIntegral_congr_fun hΩ.measurableSet fun x _ => ?_
    congr 2
    abel
  rw [hshift]
  refine degIntegral_translate (ρ₀ := ρ / 2) (ρ₁ := ρ / 2) (hf.sub contDiff_const) hbc hbs
    hΩ hΩb hy' ?_
  intro x hx
  have := hadm.2 x hx
  linarith

/-- **Density of regular values.**  The image of the critical set is null, so every value has
regular values arbitrarily close by. -/
theorem exists_regular_value_near (hf : ContDiff ℝ 2 f) (y : Fin n → ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ y' : Fin n → ℝ, ‖y' - y‖ < δ ∧ ∀ x : Fin n → ℝ, f x = y' → (jac f x).det ≠ 0 := by
  classical
  set C := {x : Fin n → ℝ | (jac f x).det = 0} with hC
  have hnull : volume (f '' C) = 0 := by
    refine MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun x => fderiv ℝ f x) (fun x _ => ?_) (fun x hx => ?_)
    · exact ((hf.differentiable (by simp) x).hasFDerivAt).hasFDerivWithinAt
    · rw [det_fderiv_eq_det_jac]
      exact hx
  have hpos : 0 < volume (Metric.ball y δ) := Metric.measure_ball_pos volume y hδ
  have hnotsub : ¬ Metric.ball y δ ⊆ f '' C := by
    intro hsub
    have hle : volume (Metric.ball y δ) ≤ 0 := hnull ▸ measure_mono hsub
    exact absurd hpos (not_lt.mpr hle)
  obtain ⟨y', hy'ball, hy'not⟩ := Set.not_subset.mp hnotsub
  refine ⟨y', ?_, fun x hx hdet => hy'not ⟨x, hdet, hx⟩⟩
  rw [Metric.mem_ball, dist_eq_norm] at hy'ball
  exact hy'ball

/-- **The Brouwer degree is an integer.** -/
theorem exists_int_degree (hf : ContDiff ℝ 2 f) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hy : y ∉ f '' frontier Ω) : ∃ k : ℤ, degree f Ω y = (k : ℝ) := by
  classical
  obtain ⟨ρ, hadm⟩ := exists_admissibleRadius hf.continuous hΩb hy
  obtain ⟨y', hy'close, hy'reg⟩ := exists_regular_value_near hf y (δ := ρ / 4) (by linarith [hadm.1])
  have hclose : ‖y' - y‖ ≤ ρ / 2 := by linarith [hadm.1]
  have hadmy' : AdmissibleRadius f Ω y' (ρ / 2) := by
    refine ⟨by linarith [hadm.1], fun x hx => ?_⟩
    have h1 := hadm.2 x hx
    have h3 : ‖f x - y‖ ≤ ‖f x - y'‖ + ‖y' - y‖ := by
      have := norm_add_le (f x - y') (y' - y)
      simpa using this
    linarith [hadm.1, hy'close]
  set v : (Fin n → ℝ) → (Fin n → ℝ) := fun x => f x - y' with hv
  have hvcd : ContDiff ℝ 2 v := hf.sub contDiff_const
  have hjacv : ∀ x, jac v x = jac f x := fun x => jac_sub_const f y' x
  have hZΩ : ∀ x ∈ closure Ω, v x = 0 → x ∈ Ω := by
    intro x hx hvx
    by_contra hxΩ
    have hfr : x ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hx, hxΩ⟩
    have hb := hadmy'.2 x hfr
    have hzero : f x - y' = 0 := hvx
    rw [hzero, norm_zero] at hb
    linarith [hadm.1]
  have hreg : ∀ x ∈ Ω, v x = 0 → (jac v x).det ≠ 0 := by
    intro x _ hvx
    rw [hjacv x]
    have hzero : f x - y' = 0 := hvx
    exact hy'reg x (sub_eq_zero.mp hzero)
  obtain ⟨k, hk⟩ := exists_int_degree_of_nondegenerate hvcd hΩ hΩb hZΩ hreg
  refine ⟨k, ?_⟩
  rw [← degree_eq_of_close hf hΩ hΩb hadm hclose, ← degree_sub_const hf hΩ hΩb, ← hv, hk]

end GaloisForLFunctions.HTGeometry.PoincareHopf
