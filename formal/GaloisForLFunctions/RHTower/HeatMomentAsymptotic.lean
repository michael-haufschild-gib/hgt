import GaloisForLFunctions.RHTower.HeatMultiplierTail
import GaloisForLFunctions.RHTower.GaussianAbsoluteMoment

/-!
# The Gaussian moment of the heat multiplier

On the phase window `(0, π]` the multiplier `W_x` is `x^{-1/2}` times a single Gaussian of
variance `2πx`, plus an exponentially small remainder.  Integrating `θ^λ` against it therefore
reproduces the Gaussian absolute moment up to exponentially small corrections.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

/-- The Gaussian parameter of the central Poisson bump. -/
noncomputable def heatRate (x : ℝ) : ℝ := 1 / (4 * Real.pi * x)

theorem heatRate_pos {x : ℝ} (hx : 0 < x) : 0 < heatRate x := by
  rw [heatRate]
  positivity

theorem ofReal_heatGauss_zero (x : ℝ) (θ : ℝ) :
    ((heatGauss x 0 θ : ℝ) : ℂ)
      = Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2)) := by
  rw [heatGauss, heatRate, Complex.ofReal_exp]
  congr 1
  push_cast
  field_simp
  ring

/-- **Splitting the window integral into the Gaussian and the exponentially small remainder.** -/
theorem heatMultiplier_window_split {x : ℝ} (hx : 0 < x) (θ : ℝ) :
    heatMultiplier x θ
      = ((x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
          * (Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2))
            + ((heatRemainder x θ : ℝ) : ℂ)) := by
  rw [heatMultiplier_eq_ofReal hx, tsum_heatGauss_split hx, Complex.ofReal_mul,
    Complex.ofReal_add, ofReal_heatGauss_zero x]

/-- A negative power of `x` is absorbed by half of an exponential. -/
theorem rpow_neg_half_le_exp {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (hx1 : x ≤ 1) :
    x ^ (-(1 : ℝ) / 2) ≤ (2 / a) * Real.exp (a / (2 * x)) := by
  have hinv : x ^ (-(1 : ℝ) / 2) ≤ 1 / x := by
    have hle : x ≤ x ^ ((2 : ℝ)⁻¹) := by
      rw [← one_div]
      have h := Real.rpow_le_rpow_of_exponent_ge hx hx1 (show (1 / 2 : ℝ) ≤ 1 by norm_num)
      simpa using h
    rw [show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx.le, one_div, one_div]
    exact inv_anti₀ hx hle
  have hexp : a / (2 * x) ≤ Real.exp (a / (2 * x)) := (Real.add_one_le_exp _).trans' (by linarith)
  have h1 : (1 : ℝ) / x = (2 / a) * (a / (2 * x)) := by
    field_simp
  calc x ^ (-(1 : ℝ) / 2) ≤ 1 / x := hinv
    _ = (2 / a) * (a / (2 * x)) := h1
    _ ≤ (2 / a) * Real.exp (a / (2 * x)) := by
        refine mul_le_mul_of_nonneg_left hexp ?_
        positivity

/-- The heat multiplier is continuous in the phase. -/
theorem continuous_heatMultiplier {x : ℝ} (hx : 0 < x) :
    Continuous (fun θ : ℝ => heatMultiplier x θ) := by
  have him : 0 < (I * (x : ℂ)).im := by
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      one_mul, zero_mul]
    simpa using hx
  have hcont : Continuous (fun θ : ℝ => jacobiTheta₂ (((θ / (2 * Real.pi) : ℝ)) : ℂ)
      (I * (x : ℂ))) := by
    have hz : Continuous (fun z : ℂ => jacobiTheta₂ z (I * (x : ℂ))) :=
      continuous_iff_continuousAt.mpr fun z =>
        (differentiableAt_jacobiTheta₂_fst z him).continuousAt
    exact hz.comp (by fun_prop)
  refine hcont.congr fun θ => ?_
  rw [heatMultiplier_eq_jacobiTheta₂]

/-- The remainder of the window decomposition is uniformly exponentially small. -/
theorem norm_heatMultiplier_sub_gauss_le {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi) :
    ‖heatMultiplier x θ
        - ((x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
          * Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2))‖
      ≤ x ^ (-(1 : ℝ) / 2) * (Real.exp (-(Real.pi / (4 * x))) * heatTailConst) := by
  rw [heatMultiplier_window_split hx]
  have hcancel : ((x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
      * (Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2))
        + ((heatRemainder x θ : ℝ) : ℂ))
      - ((x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
        * Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2))
      = ((x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * ((heatRemainder x θ : ℝ) : ℂ) := by ring
  rw [hcancel, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg hx.le _),
    Real.norm_of_nonneg (heatRemainder_nonneg x θ)]
  exact mul_le_mul_of_nonneg_left (heatRemainder_le hx hx1 hθ0 hθ1)
    (Real.rpow_nonneg hx.le _)

/-- The pure power is integrable on the phase window. -/
theorem integrableOn_rpow_window {sig : ℝ} (hsig : -1 < sig) :
    IntegrableOn (fun θ : ℝ => θ ^ sig) (Ioc (0 : ℝ) Real.pi) := by
  have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := Real.pi) hsig
  rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le] at h

/-- The exact value of the pure power integral on the phase window. -/
theorem integral_rpow_window {sig : ℝ} (hsig : -1 < sig) :
    (∫ θ in Ioc (0 : ℝ) Real.pi, θ ^ sig) = Real.pi ^ (sig + 1) / (sig + 1) := by
  have h := integral_rpow (a := (0 : ℝ)) (b := Real.pi) (Or.inl hsig)
  rw [intervalIntegral.integral_of_le Real.pi_pos.le] at h
  rw [h]
  have hz : (0 : ℝ) ^ (sig + 1) = 0 := Real.zero_rpow (by linarith)
  rw [hz, sub_zero]

/-- The window integrand of the full multiplier is integrable. -/
theorem integrableOn_cpow_mul_heatMultiplier {lam : ℂ} (hlam : -1 < lam.re) {x : ℝ}
    (hx : 0 < x) :
    IntegrableOn (fun θ : ℝ => ((θ : ℝ) : ℂ) ^ lam * heatMultiplier x θ)
      (Ioc (0 : ℝ) Real.pi) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := Real.pi)).exists_bound_of_continuousOn
    ((continuous_heatMultiplier hx).continuousOn)
  have hmeas : AEStronglyMeasurable
      (fun θ : ℝ => ((θ : ℝ) : ℂ) ^ lam * heatMultiplier x θ)
      (volume.restrict (Ioc (0 : ℝ) Real.pi)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine ContinuousOn.mul ?_ ((continuous_heatMultiplier hx).continuousOn)
    intro θ hθ
    have hθ0 : (0 : ℝ) < θ := hθ.1
    have hslit : ((θ : ℝ) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by simpa using hθ0)
    exact ((continuousAt_cpow_const hslit).comp
      (Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  refine Integrable.mono' ((integrableOn_rpow_window hlam).const_mul M) hmeas ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with θ hθ
  have hθ0 : (0 : ℝ) < θ := hθ.1
  have hmem : θ ∈ Icc (0 : ℝ) Real.pi := ⟨hθ0.le, hθ.2⟩
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hθ0]
  refine mul_le_mul_of_nonneg_left (hM θ hmem) (Real.rpow_nonneg hθ0.le _) |>.trans ?_
  rw [mul_comm]

/-- The central Gaussian is integrable on the window. -/
theorem integrableOn_gauss_window {lam : ℂ} (hlam : -1 < lam.re) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun θ : ℝ => ((θ : ℝ) : ℂ) ^ lam
      * Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2))) (Ioc (0 : ℝ) Real.pi) :=
  (integrableOn_cpow_mul_exp_neg_mul_sq_Ioi hlam (heatRate_pos hx)).mono_set
    Set.Ioc_subset_Ioi_self

/-- The central Gaussian is integrable past the window. -/
theorem integrableOn_gauss_tail {lam : ℂ} (hlam : -1 < lam.re) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun θ : ℝ => ((θ : ℝ) : ℂ) ^ lam
      * Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2))) (Ioi Real.pi) :=
  (integrableOn_cpow_mul_exp_neg_mul_sq_Ioi hlam (heatRate_pos hx)).mono_set
    (Set.Ioi_subset_Ioi Real.pi_pos.le)

/-- **Splitting the half line at the window edge.** -/
theorem integral_gauss_window_eq {lam : ℂ} (hlam : -1 < lam.re) {x : ℝ} (hx : 0 < x) :
    (∫ θ in Ioc (0 : ℝ) Real.pi, ((θ : ℝ) : ℂ) ^ lam
        * Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2)))
      = (∫ θ in Ioi (0 : ℝ), ((θ : ℝ) : ℂ) ^ lam
            * Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2)))
        - ∫ θ in Ioi Real.pi, ((θ : ℝ) : ℂ) ^ lam
            * Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2)) := by
  have hdisj : Disjoint (Ioc (0 : ℝ) Real.pi) (Ioi Real.pi) := by
    rw [Set.disjoint_left]
    intro a ha ha'
    exact absurd ha' (by simpa using ha.2)
  have hsplit := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi
    (integrableOn_gauss_window hlam hx) (integrableOn_gauss_tail hlam hx)
  rw [Set.Ioc_union_Ioi_eq_Ioi Real.pi_pos.le] at hsplit
  rw [hsplit]
  ring

/-- **The Gaussian moment of the heat multiplier on the phase window.**  This is equation `(6)`:
the window moment is the half-line Gaussian moment up to two exponentially small corrections. -/
theorem norm_heatWindowMoment_sub_main_le {lam : ℂ} (hlam : -1 < lam.re) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖(∫ θ in Ioc (0 : ℝ) Real.pi, ((θ : ℝ) : ℂ) ^ lam * heatMultiplier x θ)
        - ((x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ)
          * (1 / 2 * (((4 * Real.pi * x : ℝ)) : ℂ) ^ ((lam + 1) / 2)
              * Complex.Gamma ((lam + 1) / 2))‖
      ≤ x ^ (-(1 : ℝ) / 2)
        * (Real.exp (-(Real.pi / (4 * x))) * heatTailConst
              * (Real.pi ^ (lam.re + 1) / (lam.re + 1))
          + Real.exp (-(Real.pi / (8 * x)))
              * (1 / 2 * (8 * Real.pi * x) ^ ((lam.re + 1) / 2)
                  * Real.Gamma ((lam.re + 1) / 2))) := by
  have hbpos := heatRate_pos hx
  have hApos : (0 : ℝ) ≤ x ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hx.le _
  set A : ℂ := ((x ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) with hA
  set G : ℝ → ℂ := fun θ => ((θ : ℝ) : ℂ) ^ lam
    * Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2)) with hG
  set F : ℝ → ℂ := fun θ => ((θ : ℝ) : ℂ) ^ lam * heatMultiplier x θ with hF
  -- the half-line value
  have hmain : (∫ θ in Ioi (0 : ℝ), G θ)
      = 1 / 2 * (((4 * Real.pi * x : ℝ)) : ℂ) ^ ((lam + 1) / 2)
        * Complex.Gamma ((lam + 1) / 2) := by
    rw [hG, integral_cpow_mul_exp_neg_mul_sq_Ioi hlam hbpos]
    congr 2
    rw [heatRate]
    push_cast
    field_simp
  -- the decomposition
  have hint1 : IntegrableOn F (Ioc (0 : ℝ) Real.pi) :=
    integrableOn_cpow_mul_heatMultiplier hlam hx
  have hint2 : IntegrableOn (fun θ => A * G θ) (Ioc (0 : ℝ) Real.pi) :=
    (integrableOn_gauss_window hlam hx).const_mul A
  have hsplit : (∫ θ in Ioc (0 : ℝ) Real.pi, F θ)
      = (∫ θ in Ioc (0 : ℝ) Real.pi, (F θ - A * G θ)) + A * ∫ θ in Ioc (0 : ℝ) Real.pi, G θ := by
    rw [MeasureTheory.integral_sub hint1 hint2, MeasureTheory.integral_const_mul]
    ring
  have hgw : (∫ θ in Ioc (0 : ℝ) Real.pi, G θ)
      = (∫ θ in Ioi (0 : ℝ), G θ) - ∫ θ in Ioi Real.pi, G θ :=
    integral_gauss_window_eq hlam hx
  have hrewrite : (∫ θ in Ioc (0 : ℝ) Real.pi, F θ)
      - A * (1 / 2 * (((4 * Real.pi * x : ℝ)) : ℂ) ^ ((lam + 1) / 2)
          * Complex.Gamma ((lam + 1) / 2))
      = (∫ θ in Ioc (0 : ℝ) Real.pi, (F θ - A * G θ)) - A * ∫ θ in Ioi Real.pi, G θ := by
    rw [hsplit, hgw, ← hmain]
    ring
  rw [hrewrite]
  -- the two error bounds
  set K : ℝ := x ^ (-(1 : ℝ) / 2) * (Real.exp (-(Real.pi / (4 * x))) * heatTailConst) with hK
  have hKnn : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg hApos (mul_nonneg (Real.exp_nonneg _) heatTailConst_nonneg)
  have hptwise : ∀ θ ∈ Ioc (0 : ℝ) Real.pi, ‖F θ - A * G θ‖ ≤ θ ^ lam.re * K := by
    intro θ hθ
    have hθ0 : (0 : ℝ) < θ := hθ.1
    have hfac : F θ - A * G θ = ((θ : ℝ) : ℂ) ^ lam
        * (heatMultiplier x θ
            - A * Complex.exp (-((((heatRate x : ℝ)) : ℂ) * ((θ : ℝ) : ℂ) ^ 2))) := by
      rw [hF, hG]
      ring
    rw [hfac, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hθ0]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hθ0.le _)
    exact norm_heatMultiplier_sub_gauss_le hx hx1 hθ0 hθ.2
  have hbound1 : ‖∫ θ in Ioc (0 : ℝ) Real.pi, (F θ - A * G θ)‖
      ≤ K * (Real.pi ^ (lam.re + 1) / (lam.re + 1)) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    have hmono := MeasureTheory.setIntegral_mono_on
      (hint1.sub hint2).norm ((integrableOn_rpow_window hlam).mul_const K)
      measurableSet_Ioc hptwise
    refine hmono.trans ?_
    rw [MeasureTheory.integral_mul_const, integral_rpow_window hlam]
    rw [mul_comm]
  have hbound2 : ‖∫ θ in Ioi Real.pi, G θ‖
      ≤ Real.exp (-(Real.pi / (8 * x)))
        * (1 / 2 * (8 * Real.pi * x) ^ ((lam.re + 1) / 2) * Real.Gamma ((lam.re + 1) / 2)) := by
    have h := norm_integral_cpow_mul_exp_neg_mul_sq_Ioi_le (lam := lam) hlam
      (b := heatRate x) (c := Real.pi) hbpos Real.pi_pos.le
    have harg : heatRate x * Real.pi ^ 2 / 2 = Real.pi / (8 * x) := by
      rw [heatRate]
      field_simp
      ring
    have hscale : 2 / heatRate x = 8 * Real.pi * x := by
      rw [heatRate]
      field_simp
      ring
    rw [harg, hscale] at h
    exact h
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, hA, Complex.norm_real, Real.norm_of_nonneg hApos]
  have hstep := add_le_add hbound1 (mul_le_mul_of_nonneg_left hbound2 hApos)
  refine hstep.trans ?_
  rw [hK]
  ring_nf
  exact le_rfl

/-- The real normalisation behind `(6)`. -/
theorem heatMoment_scalar {x : ℝ} (hx : 0 < x) :
    (1 / Real.pi) * (x ^ (-(1 : ℝ) / 2)) * (1 / 2) * Real.sqrt (4 * Real.pi * x)
      = 1 / Real.sqrt Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hsp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr hpi).ne'
  have hxr : x ^ (-(1 : ℝ) / 2) = 1 / Real.sqrt x := by
    rw [Real.sqrt_eq_rpow, show (-(1 : ℝ) / 2) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx.le,
      one_div, one_div]
  have hfour : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hsq : Real.sqrt (4 * Real.pi * x) = 2 * Real.sqrt Real.pi * Real.sqrt x := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num), hfour]
  rw [hxr, hsq]
  have hpp : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt hpi.le
  field_simp
  linear_combination hpp

/-- **The main term of `(6)` in the card's normalisation.** -/
theorem heatMomentMain_eq (lam : ℂ) {x : ℝ} (hx : 0 < x) :
    (1 / ((Real.pi : ℝ) : ℂ)) * (((x ^ (-(1 : ℝ) / 2) : ℝ)) : ℂ)
        * (1 / 2 * (((4 * Real.pi * x : ℝ)) : ℂ) ^ ((lam + 1) / 2)
            * Complex.Gamma ((lam + 1) / 2))
      = (((4 * Real.pi * x : ℝ)) : ℂ) ^ (lam / 2) * Complex.Gamma ((lam + 1) / 2)
          / ((Real.sqrt Real.pi : ℝ) : ℂ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h4 : (0 : ℝ) < 4 * Real.pi * x := by positivity
  have hne : (((4 * Real.pi * x : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h4.ne'
  have hexp : (((4 * Real.pi * x : ℝ)) : ℂ) ^ ((lam + 1) / 2)
      = (((4 * Real.pi * x : ℝ)) : ℂ) ^ (lam / 2)
        * (((4 * Real.pi * x : ℝ)) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) := by
    rw [← Complex.cpow_add _ _ hne]
    congr 1
    push_cast
    ring
  have hsqrt : (((4 * Real.pi * x : ℝ)) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ)
      = ((Real.sqrt (4 * Real.pi * x) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_cpow h4.le, Real.sqrt_eq_rpow]
  have hscal := heatMoment_scalar hx
  have hsp : ((Real.sqrt Real.pi : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpi).ne'
  have hcast : ((1 / Real.pi * x ^ (-(1 : ℝ) / 2) * (1 / 2)
      * Real.sqrt (4 * Real.pi * x) : ℝ) : ℂ) = ((1 / Real.sqrt Real.pi : ℝ) : ℂ) := by
    rw [hscal]
  rw [hexp, hsqrt]
  push_cast at hcast
  field_simp at hcast ⊢
  linear_combination (((4 * Real.pi * x : ℝ)) : ℂ) ^ (lam / 2) * Complex.Gamma ((lam + 1) / 2)
    * hcast

end RHTower
