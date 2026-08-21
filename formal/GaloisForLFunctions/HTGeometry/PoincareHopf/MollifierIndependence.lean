import GaloisForLFunctions.HTGeometry.PoincareHopf.TranslationInvariance

/-!
# Independence of the degree integral from the mollifier

Two weights `φ` and `ψ` of total mass `1`, both vanishing outside the ball of radius `ρ`, give the
same degree integral, provided `‖f‖ > 2ρ` on the boundary of `Ω`.

The bridge is the convolution.  Fubini turns `∫_Ω (φ ⋆ ψ) (f x) · det (Df x) dx` into an average of
translates of the degree integral of `ψ`, all equal to it by translation invariance; since `φ` has
mass one, the average is the degree integral of `ψ`.  Convolution is commutative, so the same
quantity also equals the degree integral of `φ`.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {f : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)}
  {φ ψ : (Fin n → ℝ) → ℝ} {ρ : ℝ}

/-- Joint integrability of a continuous function over a product of two bounded sets. -/
theorem integrable_uncurry_of_continuous {F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
    (hF : Continuous (Function.uncurry F)) (hΩm : MeasurableSet Ω)
    (hΩb : Bornology.IsBounded Ω) {S : Set (Fin n → ℝ)} (hSm : MeasurableSet S)
    (hSb : Bornology.IsBounded S) :
    Integrable (Function.uncurry F) ((volume.restrict Ω).prod (volume.restrict S)) := by
  have hK : IsCompact ((closure Ω) ×ˢ (closure S)) :=
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩb.closure).prod
      (Metric.isCompact_of_isClosed_isBounded isClosed_closure hSb.closure)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  rw [Measure.prod_restrict]
  haveI : IsFiniteMeasure ((volume.prod volume).restrict (Ω ×ˢ S)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Measure.prod_prod]
    exact ENNReal.mul_lt_top hΩb.measure_lt_top hSb.measure_lt_top
  refine Integrable.mono' (g := fun _ => C) (integrable_const C)
    hF.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem (hΩm.prod hSm)] with p hp
  exact hC p ⟨subset_closure hp.1, subset_closure hp.2⟩

/-- The weighted average form of the degree integral of a convolution. -/
theorem degIntegral_convolution (hf : ContDiff ℝ 2 f) (hφc : Continuous φ) (hψc : Continuous ψ)
    (hΩm : MeasurableSet Ω) (hΩb : Bornology.IsBounded Ω) :
    (∫ x in Ω, (∫ z in Metric.ball (0 : Fin n → ℝ) ρ, φ z * ψ (f x - z)) * (jac f x).det)
      = ∫ z in Metric.ball (0 : Fin n → ℝ) ρ,
          φ z * degIntegral f Ω (fun w => ψ (w - z)) := by
  have hdetc : Continuous fun x => (jac f x).det := continuous_det_jac hf
  have hfc : Continuous f := hf.continuous
  set F : (Fin n → ℝ) → (Fin n → ℝ) → ℝ :=
    fun x z => φ z * ψ (f x - z) * (jac f x).det with hFdef
  have hFcont : Continuous (Function.uncurry F) := by
    have h1 : Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => f p.1 - p.2 :=
      (hfc.comp continuous_fst).sub continuous_snd
    exact ((hφc.comp continuous_snd).mul (hψc.comp h1)).mul (hdetc.comp continuous_fst)
  have hint : Integrable (Function.uncurry F)
      ((volume.restrict Ω).prod (volume.restrict (Metric.ball (0 : Fin n → ℝ) ρ))) :=
    integrable_uncurry_of_continuous hFcont hΩm hΩb measurableSet_ball Metric.isBounded_ball
  have hleft : (∫ x in Ω, (∫ z in Metric.ball (0 : Fin n → ℝ) ρ, φ z * ψ (f x - z))
        * (jac f x).det)
      = ∫ x in Ω, ∫ z in Metric.ball (0 : Fin n → ℝ) ρ, F x z := by
    refine MeasureTheory.setIntegral_congr_fun hΩm fun x _ => ?_
    simp only [hFdef]
    rw [MeasureTheory.integral_mul_const]
  have hswap : (∫ x in Ω, ∫ z in Metric.ball (0 : Fin n → ℝ) ρ, F x z)
      = ∫ z in Metric.ball (0 : Fin n → ℝ) ρ, ∫ x in Ω, F x z :=
    MeasureTheory.integral_integral_swap hint
  have hright : (∫ z in Metric.ball (0 : Fin n → ℝ) ρ, ∫ x in Ω, F x z)
      = ∫ z in Metric.ball (0 : Fin n → ℝ) ρ, φ z * degIntegral f Ω (fun w => ψ (w - z)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    simp only [hFdef, degIntegral]
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun hΩm fun x _ => by ring
  rw [hleft, hswap, hright]

/-- The inner convolution integral is symmetric in its two weights. -/
theorem convolution_comm_ball (hφsupp : ∀ w, ρ ≤ ‖w‖ → φ w = 0)
    (hψsupp : ∀ w, ρ ≤ ‖w‖ → ψ w = 0) (w : Fin n → ℝ) :
    (∫ z in Metric.ball (0 : Fin n → ℝ) ρ, φ z * ψ (w - z))
      = ∫ z in Metric.ball (0 : Fin n → ℝ) ρ, ψ z * φ (w - z) := by
  have hφ0 : ∀ z ∉ Metric.ball (0 : Fin n → ℝ) ρ, φ z * ψ (w - z) = 0 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hz
    rw [hφsupp z hz, zero_mul]
  have hψ0 : ∀ z ∉ Metric.ball (0 : Fin n → ℝ) ρ, ψ z * φ (w - z) = 0 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hz
    rw [hψsupp z hz, zero_mul]
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hφ0,
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hψ0]
  have := MeasureTheory.integral_sub_left_eq_self (fun z => φ z * ψ (w - z)) volume w
  simpa [mul_comm] using this.symm

/-- **The degree integral does not depend on the mollifier.** -/
theorem degIntegral_eq_of_mass_one
    (hf : ContDiff ℝ 2 f) (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ)
    (hφsupp : ∀ w, ρ ≤ ‖w‖ → φ w = 0) (hψsupp : ∀ w, ρ ≤ ‖w‖ → ψ w = 0)
    (hφmass : ∫ z, φ z = 1) (hψmass : ∫ z, ψ z = 1)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfront : ∀ x ∈ frontier Ω, ρ + ρ < ‖f x‖) :
    degIntegral f Ω φ = degIntegral f Ω ψ := by
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hballb : Bornology.IsBounded (Metric.ball (0 : Fin n → ℝ) ρ) := Metric.isBounded_ball
  -- translation invariance for both weights on the ball
  have htransψ : ∀ z ∈ Metric.ball (0 : Fin n → ℝ) ρ,
      degIntegral f Ω (fun w => ψ (w - z)) = degIntegral f Ω ψ := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact degIntegral_translate hf hψ hψsupp hΩ hΩb hz.le hfront
  have htransφ : ∀ z ∈ Metric.ball (0 : Fin n → ℝ) ρ,
      degIntegral f Ω (fun w => φ (w - z)) = degIntegral f Ω φ := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact degIntegral_translate hf hφ hφsupp hΩ hΩb hz.le hfront
  -- masses on the ball
  have hφball : (∫ z in Metric.ball (0 : Fin n → ℝ) ρ, φ z) = 1 := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero, hφmass]
    intro z hz
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hz
    exact hφsupp z hz
  have hψball : (∫ z in Metric.ball (0 : Fin n → ℝ) ρ, ψ z) = 1 := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero, hψmass]
    intro z hz
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hz
    exact hψsupp z hz
  -- the two evaluations of the convolution integral
  have h1 : (∫ x in Ω, (∫ z in Metric.ball (0 : Fin n → ℝ) ρ, φ z * ψ (f x - z))
        * (jac f x).det) = degIntegral f Ω ψ := by
    rw [degIntegral_convolution hf hφ.continuous hψ.continuous hΩm hΩb]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_ball
      (fun z hz => by dsimp only; rw [htransψ z hz] : Set.EqOn
        (fun z => φ z * degIntegral f Ω (fun w => ψ (w - z)))
        (fun z => φ z * degIntegral f Ω ψ) (Metric.ball (0 : Fin n → ℝ) ρ))]
    rw [MeasureTheory.integral_mul_const, hφball, one_mul]
  have h2 : (∫ x in Ω, (∫ z in Metric.ball (0 : Fin n → ℝ) ρ, ψ z * φ (f x - z))
        * (jac f x).det) = degIntegral f Ω φ := by
    rw [degIntegral_convolution hf hψ.continuous hφ.continuous hΩm hΩb]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_ball
      (fun z hz => by dsimp only; rw [htransφ z hz] : Set.EqOn
        (fun z => ψ z * degIntegral f Ω (fun w => φ (w - z)))
        (fun z => ψ z * degIntegral f Ω φ) (Metric.ball (0 : Fin n → ℝ) ρ))]
    rw [MeasureTheory.integral_mul_const, hψball, one_mul]
  have hcomm : (∫ x in Ω, (∫ z in Metric.ball (0 : Fin n → ℝ) ρ, φ z * ψ (f x - z))
        * (jac f x).det)
      = ∫ x in Ω, (∫ z in Metric.ball (0 : Fin n → ℝ) ρ, ψ z * φ (f x - z))
        * (jac f x).det := by
    refine MeasureTheory.setIntegral_congr_fun hΩm fun x _ => ?_
    rw [convolution_comm_ball hφsupp hψsupp (f x)]
  rw [← h2, ← hcomm, h1]

end GaloisForLFunctions.HTGeometry.PoincareHopf
