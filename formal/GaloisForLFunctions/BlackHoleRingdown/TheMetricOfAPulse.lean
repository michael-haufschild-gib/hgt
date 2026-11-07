import GaloisForLFunctions.BlackHoleRingdown.TheMetricOfARow

/-!
# The metric of a pulse

Summing the perturbations of the rows over `(c, d)`, a locally finite sum, gives for every compact profile `m` an
exact vacuum perturbation of the metric of the massless topological black hole with modular horizon.

For the profile `m(S) = e^{-S/2}(½h(S) + h'(S))` of a pulse `h` the perturbation is an explicit differential
expression in the image field `Π_h`. With `τ = t + γ(r)`, `F = r² - 1` and `𝓥 = (∂_y Π_h, -∂_x Π_h)`,

`h_{t i} = e^{-τ/2} ((F - ½) 𝓥_i + ∂_τ 𝓥_i)`,  `h_{r i} = (r/F) e^{-τ/2} (∂_τ 𝓥_i - ½ 𝓥_i)`.

So the scalar wave of a pulse carries a gravitational wave in closed form, with no Fourier integral. The constant term
of `Π_h` has no gradient, so the metric sees only the packet `𝓕_h`.
-/

open Complex Filter Topology Set
open scoped ContDiff BigOperators

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open _root_.RHTower _root_.RHTower.D4BMHorizon _root_.RHTower.D4BMMetricReconstruction
open EisensteinSeries

/-- The hyperboloidal time `τ = t + γ(r)`. -/
def hyperTime (x : Fin 4 → ℝ) : ℝ := x 0 + radialPhase (x 1)

theorem rowS_eq (c d : ℝ) (x : Fin 4 → ℝ) :
    rowS c d x = hyperTime x + Real.log (rowHgt c d (x 2) (x 3)) := rfl

theorem pulseF_eq_zero_iff (h : ℝ → ℂ) (τ : ℝ) {s : ℝ} (hs : 0 < s) (h0 : pulseF h τ s = 0) :
    h (τ + Real.log s) = 0 := by
  have hq : ((Real.sqrt s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hs).ne'
  exact (mul_eq_zero.mp h0).resolve_left hq

theorem rowHgt_pos_row (p : gammaSet 1 1 0) (x : ℝ) {Y : ℝ} (hY : 0 < Y) :
    0 < rowHgt (rowC p) (rowD p) x Y := div_pos hY (rowDen_pos p x hY)

/-- Near a point only finitely many rows are active. -/
theorem exists_finset_metric (m : CompactPulse) (q : D4BMBackground.ExteriorPoint) :
    ∃ S : Finset (gammaSet 1 1 0), ∀ᶠ x in 𝓝 q.val, ∀ p ∉ S,
      m (rowS (rowC p) (rowD p) x) = 0 ∧ m.D (rowS (rowC p) (rowD p) x) = 0 := by
  classical
  have hy := q.property.2
  have hr := q.property.1
  obtain ⟨S₁, h₁⟩ := exists_finset_box m (hyperTime q.val) (q.val 2) hy
  obtain ⟨S₂, h₂⟩ := exists_finset_box m.D (hyperTime q.val) (q.val 2) hy
  refine ⟨S₁ ∪ S₂, ?_⟩
  have hτc : ContinuousAt hyperTime q.val := by
    have hP : ContinuousAt (fun x : Fin 4 → ℝ => radialPhase (x 1)) q.val :=
      ContinuousAt.comp (f := fun x : Fin 4 → ℝ => x 1) (contDiffAt_radialPhase hr).continuousAt
        (continuous_apply 1).continuousAt
    exact (continuous_apply 0).continuousAt.add hP
  have hτ : ∀ᶠ x in 𝓝 q.val, |hyperTime x - hyperTime q.val| < 1 := by
    have := hτc.tendsto.eventually (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [this] with x hx
    simpa [Real.dist_eq] using hx
  have hx2 : ∀ᶠ x : Fin 4 → ℝ in 𝓝 q.val, |x 2 - q.val 2| < 1 := by
    have := (continuous_apply 2).continuousAt.tendsto.eventually
      (Metric.ball_mem_nhds (q.val 2) one_pos)
    filter_upwards [this] with x hx
    simpa [Real.dist_eq] using hx
  have hx3 : ∀ᶠ x : Fin 4 → ℝ in 𝓝 q.val, x 3 ∈ Ioo (q.val 3 / 2) (2 * q.val 3) :=
    (continuous_apply 3).continuousAt.tendsto.eventually
      (Ioo_mem_nhds (by linarith) (by linarith))
  filter_upwards [hτ, hx2, hx3] with x a1 a2 a3 p hp
  simp only [Finset.mem_union, not_or] at hp
  have hY : 0 < x 3 := by linarith [a3.1]
  have hs := rowHgt_pos_row p (x 2) hY
  exact ⟨pulseF_eq_zero_iff _ _ hs (h₁ _ _ _ a1.le a2.le (Ioo_subset_Icc_self a3) p hp.1),
    pulseF_eq_zero_iff _ _ hs (h₂ _ _ _ a1.le a2.le (Ioo_subset_Icc_self a3) p hp.2)⟩

/-- The temporal block of the sum over rows. -/
def imageT (m : CompactPulse) (i : Fin 2) (x : Fin 4 → ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : gammaSet 1 1 0, rowT (rowC p) (rowD p) m m.D i x

/-- The radial block of the sum over rows. -/
def imageR (m : CompactPulse) (i : Fin 2) (x : Fin 4 → ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : gammaSet 1 1 0, rowR (rowC p) (rowD p) m.D i x

/-- **The perturbation of the sum over rows.** -/
def imageMetric (m : CompactPulse) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, imageT m 0 x, imageT m 1 x;
    0, 0, imageR m 0 x, imageR m 1 x;
    imageT m 0 x, imageR m 0 x, 0, 0;
    imageT m 1 x, imageR m 1 x, 0, 0]

/-- **Every compact profile gives an exact vacuum perturbation of the metric.** -/
theorem imageMetric_vacuum (m : CompactPulse) (q : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (imageMetric m) q.val) (-3) i j = 0 := by
  obtain ⟨S, hS⟩ := exists_finset_metric m q
  have hgerm : imageMetric m =ᶠ[𝓝 q.val] fun x => ∑ p ∈ S, (1 / 2 : ℂ) •
      rowMetric (rowC p) (rowD p) m m.D x := by
    filter_upwards [hS] with x hx
    have hT : ∀ k, imageT m k x = (1 / 2 : ℂ) * ∑ p ∈ S, rowT (rowC p) (rowD p) m m.D k x := fun k => by
      rw [imageT, tsum_eq_sum (s := S) fun p hp => ?_]
      simp [rowT, (hx p hp).1, (hx p hp).2]
    have hR : ∀ k, imageR m k x = (1 / 2 : ℂ) * ∑ p ∈ S, rowR (rowC p) (rowD p) m.D k x := fun k => by
      rw [imageR, tsum_eq_sum (s := S) fun p hp => ?_]
      simp [rowR, (hx p hp).2]
    ext u v
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    fin_cases u <;> fin_cases v
    all_goals first
      | (simp [rowMetric, imageMetric]; done)
      | exact hT 0 | exact hT 1 | exact hR 0 | exact hR 1
  rw [ofMetricField_congr_germ hgerm]
  have hm3 : ∀ s, ContDiffAt ℝ 3 m s := fun s => by
    exact_mod_cast (contDiff_infty.mp m.smooth 3).contDiffAt
  have hm2 : ∀ s, ContDiffAt ℝ 2 m s := fun s => (hm3 s).of_le (by norm_num)
  have hm1 : ∀ s, ContDiffAt ℝ 2 m.D s := fun s => by
    exact_mod_cast (contDiff_infty.mp m.D.smooth 2).contDiffAt
  exact vac_sum _ S (fun _ => (1 / 2 : ℂ)) (fun p => rowMetric (rowC p) (rowD p) m m.D)
    (fun p _ a b => contDiffAt_rowMetric (fun x y hy => rowDen_pos p x hy) q (hm2 _) (hm1 _) a b)
    (fun p _ => rowMetric_vacuum (fun x y hy => rowDen_pos p x hy) q (hm3 _)) i j

/-! ### The profile of a pulse -/

namespace CompactPulse

/-- The profile `m(S) = e^{-S/2}(½h(S) + h'(S))`. -/
def profile (h : CompactPulse) : CompactPulse where
  toFun S := Complex.exp (-(1 / 2 : ℂ) * (S : ℂ)) * ((1 / 2 : ℂ) * h S + h.D S)
  smooth := (contDiff_exp_real_mul _).mul ((contDiff_const.mul h.smooth).add h.D.smooth)
  compact := ((h.compact.mul_left (f := fun _ => (1 / 2 : ℂ))).add h.D.compact).mul_left

theorem hasDerivAt_profile (h : CompactPulse) (S : ℝ) :
    HasDerivAt h.profile (Complex.exp (-(1 / 2 : ℂ) * (S : ℂ)) * ((1 / 2 : ℂ) * h.D S + h.D.D S) -
      (1 / 2 : ℂ) * h.profile S) S := by
  have h1 := ((h.hasDerivAt S).const_mul (1 / 2 : ℂ)).add (h.D.hasDerivAt S)
  refine ((hasDerivAt_exp_real_mul (-(1 / 2 : ℂ)) S).mul h1).congr_deriv ?_
  change _ = _ - (1 / 2 : ℂ) * (Complex.exp (-(1 / 2 : ℂ) * (S : ℂ)) * ((1 / 2 : ℂ) * h S + h.D S))
  simp only [Pi.add_apply]
  ring

theorem exp_half_row (τ : ℝ) {s : ℝ} (hs : 0 < s) :
    Complex.exp (-(1 / 2 : ℂ) * ((τ + Real.log s : ℝ) : ℂ)) =
      Complex.exp (-(1 / 2 : ℂ) * (τ : ℂ)) * (((Real.sqrt s)⁻¹ : ℝ) : ℂ) := by
  have h1 : (((Real.sqrt s)⁻¹ : ℝ) : ℂ) = Complex.exp (-(1 / 2 : ℂ) * ((Real.log s : ℝ) : ℂ)) := by
    have h2 : (Real.sqrt s)⁻¹ = Real.exp (-(1 / 2) * Real.log s) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hs, ← Real.exp_neg]
      congr 1
      ring
    rw [h2, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [h1, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem profile_row (h : CompactPulse) (τ : ℝ) {s : ℝ} (hs : 0 < s) :
    h.profile (τ + Real.log s) = Complex.exp (-(1 / 2 : ℂ) * (τ : ℂ)) * pulseF1 h h.D τ s := by
  change Complex.exp (-(1 / 2 : ℂ) * ((τ + Real.log s : ℝ) : ℂ)) * _ = _
  rw [exp_half_row τ hs, pulseF1]
  ring

theorem profileD_row (h : CompactPulse) (τ : ℝ) {s : ℝ} (hs : 0 < s) :
    h.profile.D (τ + Real.log s) = Complex.exp (-(1 / 2 : ℂ) * (τ : ℂ)) *
      (pulseF1 h.D h.D.D τ s - (1 / 2 : ℂ) * pulseF1 h h.D τ s) := by
  have hd := (h.hasDerivAt_profile (τ + Real.log s)).deriv
  change deriv h.profile (τ + Real.log s) = _
  have hp := h.profile_row τ hs
  rw [hd, hp, exp_half_row τ hs]
  simp only [pulseF1]
  ring

end CompactPulse

/-! ### The covector of the image field -/

/-- The covector `𝓥 = (∂_y Π_h, -∂_x Π_h)` of the image field, as a sum over rows. -/
def imageCov (h : CompactPulse) (i : Fin 2) (τ : ℝ) (x : Fin 4 → ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑' p : gammaSet 1 1 0,
    (rowSigma (rowC p) (rowD p) i x : ℂ) * pulseF1 h h.D τ (rowHgt (rowC p) (rowD p) (x 2) (x 3))

/-- A finite set of rows active at a point, with all the derivatives that enter. -/
theorem exists_finset_point (h : CompactPulse) (τ : ℝ) {x : Fin 4 → ℝ} (hy : 0 < x 3) :
    ∃ S : Finset (gammaSet 1 1 0), ∀ p ∉ S,
      pulseF1 h h.D τ (rowHgt (rowC p) (rowD p) (x 2) (x 3)) = 0 ∧
      pulseF1 h.D h.D.D τ (rowHgt (rowC p) (rowD p) (x 2) (x 3)) = 0 := by
  obtain ⟨S, hS⟩ := exists_finset_box_three h τ (x 2) hy
  refine ⟨S, fun p hp => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hS τ (x 2) (x 3) (by simp) (by simp) (mem_window_self hy) p hp
  have hs := rowHgt_pos_row p (x 2) hy
  have a1 := pulseF_eq_zero_iff _ _ hs h1
  have a2 := pulseF_eq_zero_iff _ _ hs h2
  have a3 := pulseF_eq_zero_iff _ _ hs h3
  simp [pulseF1, a1, a2, a3]

/-- **The closed form of the temporal block.** -/
theorem imageT_profile (h : CompactPulse) (i : Fin 2) {x : Fin 4 → ℝ} (hy : 0 < x 3) :
    imageT h.profile i x = Complex.exp (-(1 / 2 : ℂ) * (hyperTime x : ℂ)) *
      ((rowF x - 1 / 2) * imageCov h i (hyperTime x) x + imageCov h.D i (hyperTime x) x) := by
  obtain ⟨S, hS⟩ := exists_finset_point h (hyperTime x) hy
  have hrow : ∀ p : gammaSet 1 1 0, rowT (rowC p) (rowD p) h.profile h.profile.D i x =
      Complex.exp (-(1 / 2 : ℂ) * (hyperTime x : ℂ)) *
        ((rowF x - 1 / 2) * ((rowSigma (rowC p) (rowD p) i x : ℂ) *
            pulseF1 h h.D (hyperTime x) (rowHgt (rowC p) (rowD p) (x 2) (x 3))) +
          (rowSigma (rowC p) (rowD p) i x : ℂ) *
            pulseF1 h.D h.D.D (hyperTime x) (rowHgt (rowC p) (rowD p) (x 2) (x 3))) := fun p => by
    have hs := rowHgt_pos_row p (x 2) hy
    simp only [rowT, rowS_eq]
    rw [h.profile_row _ hs, h.profileD_row _ hs]
    ring
  rw [imageT, imageCov, imageCov, tsum_eq_sum (s := S) fun p hp => by
      rw [hrow, (hS p hp).1, (hS p hp).2]
      simp,
    tsum_eq_sum (s := S) fun p hp => by rw [(hS p hp).1, mul_zero],
    tsum_eq_sum (s := S) fun p hp => by rw [(hS p hp).2, mul_zero]]
  simp only [hrow]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- **The closed form of the radial block.** -/
theorem imageR_profile (h : CompactPulse) (i : Fin 2) {x : Fin 4 → ℝ} (hy : 0 < x 3) :
    imageR h.profile i x = (x 1 : ℂ) * (rowF x)⁻¹ * Complex.exp (-(1 / 2 : ℂ) * (hyperTime x : ℂ)) *
      (imageCov h.D i (hyperTime x) x - (1 / 2 : ℂ) * imageCov h i (hyperTime x) x) := by
  obtain ⟨S, hS⟩ := exists_finset_point h (hyperTime x) hy
  have hrow : ∀ p : gammaSet 1 1 0, rowR (rowC p) (rowD p) h.profile.D i x =
      (x 1 : ℂ) * (rowF x)⁻¹ * Complex.exp (-(1 / 2 : ℂ) * (hyperTime x : ℂ)) *
        ((rowSigma (rowC p) (rowD p) i x : ℂ) *
            pulseF1 h.D h.D.D (hyperTime x) (rowHgt (rowC p) (rowD p) (x 2) (x 3)) -
          (1 / 2 : ℂ) * ((rowSigma (rowC p) (rowD p) i x : ℂ) *
            pulseF1 h h.D (hyperTime x) (rowHgt (rowC p) (rowD p) (x 2) (x 3)))) := fun p => by
    have hs := rowHgt_pos_row p (x 2) hy
    simp only [rowR, rowS_eq]
    rw [h.profileD_row _ hs]
    ring
  rw [imageR, imageCov, imageCov, tsum_eq_sum (s := S) fun p hp => by
      rw [hrow, (hS p hp).1, (hS p hp).2]
      simp,
    tsum_eq_sum (s := S) fun p hp => by rw [(hS p hp).2, mul_zero],
    tsum_eq_sum (s := S) fun p hp => by rw [(hS p hp).1, mul_zero]]
  simp only [hrow]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- **The covector is the rotated gradient of the image field: first component.** -/
theorem imageCov_zero (h : CompactPulse) (τ : ℝ) {x : Fin 4 → ℝ} (hy : 0 < x 3) :
    HasDerivAt (fun q => imageField h τ (x 2) q) (imageCov h 0 τ x) (x 3) := by
  obtain ⟨S, hS⟩ := exists_finset_box_three h τ (x 2) hy
  have hS₁ := fun τ' x' Y' a b c p hp => (hS τ' x' Y' a b c p hp).1
  have hsum : HasDerivAt (fun q => (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) τ (x 2) q)
      ((1 / 2 : ℂ) * ∑ p ∈ S, imageTermY h (rowC p) (rowD p) τ (x 2) (x 3)) (x 3) :=
    (HasDerivAt.fun_sum fun p _ =>
      hasDerivAt_imageTerm_y h τ hy (rowDen_pos p (x 2) hy)).const_mul _
  have hev : (fun q => imageField h τ (x 2) q) =ᶠ[𝓝 (x 3)]
      fun q => (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) τ (x 2) q := by
    filter_upwards [Ioo_mem_nhds (by linarith : x 3 / 2 < x 3) (by linarith : x 3 < 2 * x 3)] with q hq
    exact imageField_eq_sum hS₁ (by simp) (by simp) (Ioo_subset_Icc_self hq)
  have hval : imageCov h 0 τ x = (1 / 2 : ℂ) * ∑ p ∈ S, imageTermY h (rowC p) (rowD p) τ (x 2) (x 3) := by
    rw [imageCov, tsum_eq_sum (s := S) fun p hp => ?_]
    · congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [rowSigma, imageTermY, mul_comm]
    · obtain ⟨h1, h2, -⟩ := hS τ (x 2) (x 3) (by simp) (by simp) (mem_window_self hy) p hp
      have hs := rowHgt_pos_row p (x 2) hy
      simp [pulseF1, pulseF_eq_zero_iff _ _ hs h1, pulseF_eq_zero_iff _ _ hs h2]
  rw [hval]
  exact hsum.congr_of_eventuallyEq hev

/-- **The covector is the rotated gradient of the image field: second component.** -/
theorem imageCov_one (h : CompactPulse) (τ : ℝ) {x : Fin 4 → ℝ} (hy : 0 < x 3) :
    HasDerivAt (fun q => imageField h τ q (x 3)) (-imageCov h 1 τ x) (x 2) := by
  obtain ⟨S, hS⟩ := exists_finset_box_three h τ (x 2) hy
  have hS₁ := fun τ' x' Y' a b c p hp => (hS τ' x' Y' a b c p hp).1
  have hsum : HasDerivAt (fun q => (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) τ q (x 3))
      ((1 / 2 : ℂ) * ∑ p ∈ S, imageTermX h (rowC p) (rowD p) τ (x 2) (x 3)) (x 2) :=
    (HasDerivAt.fun_sum fun p _ =>
      hasDerivAt_imageTerm_x h τ hy (rowDen_pos p (x 2) hy)).const_mul _
  have hev : (fun q => imageField h τ q (x 3)) =ᶠ[𝓝 (x 2)]
      fun q => (1 / 2 : ℂ) * ∑ p ∈ S, imageTerm h (rowC p) (rowD p) τ q (x 3) := by
    filter_upwards [Metric.ball_mem_nhds (x 2) one_pos] with q hq
    have : |q - x 2| ≤ 1 := by
      rw [Metric.mem_ball, Real.dist_eq] at hq
      exact hq.le
    exact imageField_eq_sum hS₁ (by simp) this (mem_window_self hy)
  have hval : -imageCov h 1 τ x = (1 / 2 : ℂ) * ∑ p ∈ S, imageTermX h (rowC p) (rowD p) τ (x 2) (x 3) := by
    rw [imageCov, tsum_eq_sum (s := S) fun p hp => ?_]
    · rw [← mul_neg, ← Finset.sum_neg_distrib]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      simp [rowSigma, imageTermX, mul_comm]
    · obtain ⟨h1, h2, -⟩ := hS τ (x 2) (x 3) (by simp) (by simp) (mem_window_self hy) p hp
      have hs := rowHgt_pos_row p (x 2) hy
      simp [pulseF1, pulseF_eq_zero_iff _ _ hs h1, pulseF_eq_zero_iff _ _ hs h2]
  rw [hval]
  exact hsum.congr_of_eventuallyEq hev

/-- **The gravitational wave of a pulse.**  For every pulse `h` the explicit perturbation built from the image field
solves the vacuum linearized Einstein equations on the exterior. -/
theorem pulseMetric_vacuum (h : CompactPulse) (q : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (imageMetric h.profile) q.val) (-3) i j = 0 :=
  imageMetric_vacuum h.profile q i j

end GaloisForLFunctions.BlackHoleRingdown

end
