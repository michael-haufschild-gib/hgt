import GaloisForLFunctions.goldbach.LiLiu.Mellin.ConvolutionScaling

/-! # Positive-ray Mellin integrals of the two additive profiles -/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Set
noncomputable section

def centralInterval : Set ℝ := Icc (1/3) (2/3)

def orientedProfile (φ : TestWeight) (d y : ℝ) : ℂ :=
  ∫ r in centralInterval, (φ r:ℂ) * (φ (d*(y-r)):ℂ)

theorem orientedProfile_add (φ : TestWeight) (y : ℝ) :
    orientedProfile φ 1 y = (sumProfile φ y : ℂ) := by
  rw [orientedProfile, sumProfile, ← integral_complex_ofReal]
  simp only [one_mul, Complex.ofReal_mul]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  simp [Function.notMem_support.mp (fun h => hr (φ.supported h))]

theorem orientedProfile_sub (φ : TestWeight) (y : ℝ) :
    orientedProfile φ (-1) y = (sumProfile φ (1-y) : ℂ) := by
  rw [orientedProfile, sumProfile, ← integral_complex_ofReal,
    ← integral_sub_left_eq_self (fun r : ℝ => ((φ r * φ (1-y-r) : ℝ):ℂ)) volume 1]
  simp only [Complex.ofReal_mul,φ.symmetric,neg_one_mul,neg_sub]
  simp_rw [show ∀ r : ℝ, 1-y-(1-r) = r-y from fun r => by ring]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro r hr
  simp [Function.notMem_support.mp (fun h => hr (φ.supported h))]

private theorem weight_zero_above (φ : TestWeight) {d r y : ℝ}
    (hd : d^2 = 1) (hr : r ∈ centralInterval) (hy : 2 < y) : φ (d*(y-r)) = 0 := by
  by_contra! hn
  obtain ⟨hl,hu⟩ := φ.supported hn
  obtain ⟨_,hr'⟩ := hr
  rcases sq_eq_one_iff.mp hd with rfl | rfl <;> linarith only [hl,hu,hr',hy]

/-- After interchange of the two physical variables the positive argument r
stays in the compact weight support. The domain of u distinguishes the
finite Beta integral from the half-line Beta integral. -/
theorem orientedProfile_mellin (φ : TestWeight) {d : ℝ} (hd : d^2=1) {w : ℂ} (hw : 0 < w.re) :
    mellin (orientedProfile φ d) w =
      ∫ r in centralInterval, ∫ u in shapeDomain d,
        ((r:ℂ)^w * (φ r:ℂ)) * ((1+d*u:ℝ):ℂ)^(w-1) * (φ (r*u):ℂ) := by
  let F (y r : ℝ) := (y:ℂ)^(w-1) * (φ r:ℂ) * (φ (d*(y-r)):ℂ)
  have hφ (x : ℝ) : ‖(φ x : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (φ.values x).1] using (φ.values x).2
  have hmeas : Measurable (Function.uncurry F) := by
    have h := (Complex.continuous_ofReal.comp φ.smooth.continuous).measurable
    exact (((Complex.continuous_ofReal.measurable.comp measurable_fst).pow_const _).mul
      (h.comp measurable_snd)).mul (h.comp (measurable_const.mul (measurable_fst.sub measurable_snd)))
  have hY : IntervalIntegrable (fun y : ℝ => (y:ℂ)^(w-1)) volume 0 2 :=
    intervalIntegral.intervalIntegrable_cpow' (by simp only [sub_re,one_re]; linarith only [hw])
  have hR : IntegrableOn (fun _ : ℝ => (1:ℝ)) centralInterval :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hI : Integrable (Function.uncurry F)
      ((volume.restrict (Ioc (0:ℝ) 2)).prod (volume.restrict centralInterval)) := by
    apply (hY.1.norm.mul_prod hR).mono' hmeas.aestronglyMeasurable
    filter_upwards with p
    simp only [Function.uncurry,F,norm_mul,mul_one]
    exact (mul_le_of_le_one_right (by positivity) (hφ _)).trans
      (mul_le_of_le_one_right (norm_nonneg _) (hφ _))
  have hrow (y : ℝ) : (y:ℂ)^(w-1) * orientedProfile φ d y = ∫ r in centralInterval, F y r := by
    simp only [orientedProfile,F,mul_assoc,integral_const_mul]
  have htail {y : ℝ} (hy : 2 < y) : orientedProfile φ d y = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    simp [weight_zero_above φ hd hr hy]
  rw [mellin]
  simp_rw [smul_eq_mul]
  calc
    _ = ∫ y in Ioc (0:ℝ) 2, (y:ℂ)^(w-1) * orientedProfile φ d y := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ h => h.1)
      intro y hy
      rw [htail (lt_of_not_ge fun h => hy.2 ⟨hy.1,h⟩),mul_zero]
    _ = ∫ r in centralInterval, ∫ y in Ioc (0:ℝ) 2, F y r := by
      simp_rw [hrow]
      exact integral_integral_swap hI
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      dsimp only
      have hr0 : 0 < r := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/3) hr.1
      have hy : (∫ y in Ioi (0:ℝ), F y r) = ∫ y in Ioc (0:ℝ) 2, F y r := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ h => h.1)
        intro y hy
        simp [F, weight_zero_above φ hd hr (lt_of_not_ge fun h => hy.2 ⟨hy.1,h⟩)]
      rw [← hy]
      have he (y : ℝ) : F y r = (φ r:ℂ) * ((y:ℂ)^(w-1) * (φ (d*(y-r)):ℂ)) := by dsimp [F]; ring
      simp_rw [he]
      rw [integral_const_mul, oriented_weight_integral φ hr0 hd w]
      simp only [mul_assoc,integral_const_mul]
      ring

#print axioms orientedProfile_mellin
end
end GaloisForLFunctions.Goldbach.LiLiu
