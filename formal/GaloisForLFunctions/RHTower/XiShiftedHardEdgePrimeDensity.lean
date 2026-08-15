import GaloisForLFunctions.RHTower.XiShiftedHardEdgeArchimedeanDensity
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtPerron

/-!
# The prime density of the completed source

The prime term of the completed source in density coordinates is

`Pi_n(X) = sum_m Lambda(m) m^{-1/2}·∫ (X + x²)^{-(n+1)} e^{-i x log m} dx`.

Every summand carries the exponential frequency aperture of the mass kernel, so on any half line
`X > X_0 > 1/4` the series is dominated by `C·sum_m Lambda(m) m^{-1/2-h}` with `1/2 < h < √X_0`,
uniformly in `X`.  That makes the series termwise differentiable in the mass, so the prime moments
obey the same mass-derivative recursion as the archimedean ones, and at order zero the closed form
is the von Mangoldt Dirichlet series:

`Pi_0(X) = (pi/√X)·L_Lambda(1/2 + √X)`.
-/

open Complex MeasureTheory
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- One prime-power term of the completed source in density coordinates. -/
def routeUPrimeTerm (n m : ℕ) (X : ℝ) : ℂ :=
  ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ)
    * massPairing (cauchyFourierWeight (Real.log m)) n X

/-- The prime moments of the completed source. -/
def routeUPrimeMoment (n : ℕ) (X : ℝ) : ℂ := ∑' m : ℕ, routeUPrimeTerm n m X

/-- The uniform aperture constant on a half line of masses. -/
def routeUPrimeApertureConst (X₀ h : ℝ) (n : ℕ) : ℝ :=
  Real.pi / Real.sqrt (X₀ - h ^ 2) * ((X₀ - h ^ 2) ^ n)⁻¹

theorem routeUPrimeApertureConst_nonneg {X₀ h : ℝ} (hhX : h ^ 2 < X₀) (n : ℕ) :
    0 ≤ routeUPrimeApertureConst X₀ h n := by
  have hpos : (0 : ℝ) < X₀ - h ^ 2 := by linarith
  unfold routeUPrimeApertureConst
  positivity

theorem log_natCast_nonneg (m : ℕ) : 0 ≤ Real.log (m : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hm)

/-- **The uniform prime aperture.**  Every term of the prime series is dominated, uniformly on a
half line of masses, by a von Mangoldt term of exponent `1/2 + h`. -/
theorem norm_routeUPrimeTerm_le {X₀ h : ℝ} (hh : 0 < h) (hhX : h ^ 2 < X₀) (n m : ℕ) {X : ℝ}
    (hX : X₀ < X) :
    ‖routeUPrimeTerm n m X‖
      ≤ routeUPrimeApertureConst X₀ h n
          * ((ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-(1 / 2 + h))) := by
  have hX0 : (0 : ℝ) < X₀ - h ^ 2 := by linarith
  have hXh : h ^ 2 < X := by linarith
  have hXpos : (0 : ℝ) < X - h ^ 2 := by linarith
  have hΛ : (0 : ℝ) ≤ (ArithmeticFunction.vonMangoldt m : ℝ) :=
    ArithmeticFunction.vonMangoldt_nonneg
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [routeUPrimeTerm]
    have h0 : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by simp
    rw [h0]
    simp [routeUPrimeApertureConst]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  -- the aperture bound at the mass `X`
  have hker := norm_massPairing_cauchyFourierWeight_le (Z := X) (L := Real.log (m : ℝ)) hh hXh
    hlog n
  -- monotone in the mass
  have hmono : Real.exp (-(Real.log (m : ℝ) * h)) * ((X - h ^ 2) ^ n)⁻¹
        * (Real.pi / Real.sqrt (X - h ^ 2))
      ≤ Real.exp (-(Real.log (m : ℝ) * h)) * routeUPrimeApertureConst X₀ h n := by
    have h1 : ((X - h ^ 2) ^ n)⁻¹ ≤ ((X₀ - h ^ 2) ^ n)⁻¹ := by
      have hpow : (X₀ - h ^ 2) ^ n ≤ (X - h ^ 2) ^ n := pow_le_pow_left₀ hX0.le (by linarith) n
      have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (X₀ - h ^ 2) ^ n) hpow
      simpa [one_div] using this
    have h2 : Real.pi / Real.sqrt (X - h ^ 2) ≤ Real.pi / Real.sqrt (X₀ - h ^ 2) := by
      refine div_le_div_of_nonneg_left Real.pi_pos.le (Real.sqrt_pos.mpr hX0) ?_
      exact Real.sqrt_le_sqrt (by linarith)
    have hnn : (0 : ℝ) ≤ Real.exp (-(Real.log (m : ℝ) * h)) := Real.exp_nonneg _
    unfold routeUPrimeApertureConst
    have hp1 : (0 : ℝ) ≤ ((X - h ^ 2) ^ n)⁻¹ := by positivity
    have hp2 : (0 : ℝ) ≤ Real.pi / Real.sqrt (X - h ^ 2) := by positivity
    nlinarith [mul_le_mul h1 h2 hp2 (by positivity : (0 : ℝ) ≤ ((X₀ - h ^ 2) ^ n)⁻¹)]
  -- the prefactor
  have hpre : ‖((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ)‖
      = (ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg hmpos.le]
  have hexp : Real.exp (-(Real.log (m : ℝ) * h)) = (m : ℝ) ^ (-h) := by
    rw [Real.rpow_def_of_pos hmpos]
    congr 1
    ring
  have hsplit : (m : ℝ) ^ (-(1 / 2 + h)) = (m : ℝ) ^ (-(1 / 2 : ℝ)) * (m : ℝ) ^ (-h) := by
    rw [← Real.rpow_add hmpos]
    congr 1
    ring
  rw [routeUPrimeTerm, norm_mul, hpre]
  calc (ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ))
        * ‖massPairing (cauchyFourierWeight (Real.log (m : ℝ))) n X‖
      ≤ (ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-(1 / 2 : ℝ))
          * (Real.exp (-(Real.log (m : ℝ) * h)) * routeUPrimeApertureConst X₀ h n) := by
        refine mul_le_mul_of_nonneg_left (le_trans hker hmono) ?_
        have : (0 : ℝ) ≤ (m : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hmpos.le _
        positivity
    _ = routeUPrimeApertureConst X₀ h n
          * ((ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-(1 / 2 + h))) := by
        rw [hsplit, hexp]
        ring

theorem summable_vonMangoldt_rpow_real {s : ℝ} (hs : 1 < s) :
    Summable fun m : ℕ => (ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-s) := by
  have h := RHTower.Sieve.summable_vonMangoldt_rpow (σ := s) hs
  refine h.congr fun m => ?_
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ArithmeticFunction.vonMangoldt_nonneg)]

theorem summable_routeUPrimeTerm {X₀ h : ℝ} (hh : 1 / 2 < h) (hhX : h ^ 2 < X₀) (n : ℕ) {X : ℝ}
    (hX : X₀ < X) : Summable fun m : ℕ => routeUPrimeTerm n m X := by
  have hh0 : (0 : ℝ) < h := by linarith
  refine Summable.of_norm_bounded
    (g := fun m : ℕ => routeUPrimeApertureConst X₀ h n
      * ((ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-(1 / 2 + h))))
    ((summable_vonMangoldt_rpow_real (s := 1 / 2 + h) (by linarith)).mul_left _)
    (fun m => norm_routeUPrimeTerm_le hh0 hhX n m hX)


theorem exists_routeUPrimeAperture {X₀ : ℝ} (hX₀ : 1 / 4 < X₀) :
    ∃ h : ℝ, 1 / 2 < h ∧ h ^ 2 < X₀ := by
  have hX0 : (0 : ℝ) < X₀ := by linarith
  have hsq : (1 : ℝ) / 2 < Real.sqrt X₀ := by
    rw [show (1 : ℝ) / 2 = Real.sqrt (1 / 4) by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) hX₀
  refine ⟨(1 / 2 + Real.sqrt X₀) / 2, by linarith, ?_⟩
  have hlt : (1 / 2 + Real.sqrt X₀) / 2 < Real.sqrt X₀ := by linarith
  have hnn : (0 : ℝ) ≤ (1 / 2 + Real.sqrt X₀) / 2 := by linarith
  have hsq2 : Real.sqrt X₀ ^ 2 = X₀ := Real.sq_sqrt hX0.le
  nlinarith [hlt, hnn, hsq2]

theorem hasDerivAt_routeUPrimeMoment (n : ℕ) {X : ℝ} (hX : 1 / 4 < X) :
    HasDerivAt (routeUPrimeMoment n) (-((n : ℂ) + 1) * routeUPrimeMoment (n + 1) X) X := by
  obtain ⟨X₀, hX₀lo, hX₀hi⟩ : ∃ X₀ : ℝ, 1 / 4 < X₀ ∧ X₀ < X :=
    ⟨(1 / 4 + X) / 2, by linarith, by linarith⟩
  obtain ⟨h, hh, hhX⟩ := exists_routeUPrimeAperture hX₀lo
  have hh0 : (0 : ℝ) < h := by linarith
  have hnorm : ‖-((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    rw [norm_neg]
    rw [show ((n : ℂ) + 1) = (((n + 1 : ℕ) : ℕ) : ℂ) by push_cast; ring]
    rw [Complex.norm_natCast]
    push_cast
    ring
  have hg : ∀ (m : ℕ) (Y : ℝ), Y ∈ Set.Ioi X₀ →
      HasDerivAt (fun Z : ℝ => routeUPrimeTerm n m Z)
        (-((n : ℂ) + 1) * routeUPrimeTerm (n + 1) m Y) Y := by
    intro m Y hY
    simp only [Set.mem_Ioi] at hY
    have hYpos : (0 : ℝ) < Y := by linarith
    have hd := hasDerivAt_massPairing (continuous_cauchyFourierWeight (Real.log (m : ℝ)))
      (cauchyFourierWeight_bound (Real.log (m : ℝ))) n hYpos
    have hmul := hd.const_mul ((ArithmeticFunction.vonMangoldt m / Real.sqrt m : ℝ) : ℂ)
    refine hmul.congr_deriv ?_
    simp only [routeUPrimeTerm]
    ring
  have hg' : ∀ (m : ℕ) (Y : ℝ), Y ∈ Set.Ioi X₀ →
      ‖-((n : ℂ) + 1) * routeUPrimeTerm (n + 1) m Y‖
        ≤ ((n : ℝ) + 1) * (routeUPrimeApertureConst X₀ h (n + 1)
            * ((ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-(1 / 2 + h)))) := by
    intro m Y hY
    simp only [Set.mem_Ioi] at hY
    rw [norm_mul, hnorm]
    refine mul_le_mul_of_nonneg_left (norm_routeUPrimeTerm_le hh0 hhX (n + 1) m hY) ?_
    positivity
  have hu : Summable fun m : ℕ => ((n : ℝ) + 1) * (routeUPrimeApertureConst X₀ h (n + 1)
      * ((ArithmeticFunction.vonMangoldt m : ℝ) * (m : ℝ) ^ (-(1 / 2 + h)))) :=
    (((summable_vonMangoldt_rpow_real (s := 1 / 2 + h) (by linarith)).mul_left _)).mul_left _
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi (isPreconnected_Ioi)
    hg hg' (y₀ := X) hX₀hi (summable_routeUPrimeTerm hh hhX n hX₀hi) hX₀hi
  refine hmain.congr_deriv ?_
  rw [tsum_mul_left, routeUPrimeMoment]

theorem iteratedDeriv_routeUPrimeMoment :
    ∀ (n : ℕ) {X : ℝ}, 1 / 4 < X →
      iteratedDeriv n (routeUPrimeMoment 0) X
        = (-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ) * routeUPrimeMoment n X := by
  intro n
  induction n with
  | zero =>
    intro X _
    simp
  | succ n ih =>
    intro X hX
    have heq : (fun Z : ℝ => iteratedDeriv n (routeUPrimeMoment 0) Z)
        =ᶠ[nhds X] fun Z : ℝ =>
          (-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ) * routeUPrimeMoment n Z := by
      filter_upwards [Ioi_mem_nhds hX] with Z hZ
      exact ih hZ
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hderiv : HasDerivAt
        (fun Z : ℝ => (-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ) * routeUPrimeMoment n Z)
        ((-1 : ℂ) ^ n * ((Nat.factorial n : ℕ) : ℂ)
          * (-((n : ℂ) + 1) * routeUPrimeMoment (n + 1) X)) X :=
      (hasDerivAt_routeUPrimeMoment n hX).const_mul _
    rw [hderiv.deriv]
    have hfac : ((Nat.factorial (n + 1) : ℕ) : ℂ) = ((n : ℂ) + 1) * ((Nat.factorial n : ℕ) : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfac]
    ring

/-- **The prime term of the completed source in density coordinates.** -/
theorem routeUPrimeMoment_zero_eq {X : ℝ} (hX : 1 / 4 < X) :
    routeUPrimeMoment 0 X
      = ((Real.pi / Real.sqrt X : ℝ) : ℂ)
        * LSeries (fun m => ((ArithmeticFunction.vonMangoldt m : ℝ) : ℂ))
            (((1 / 2 + Real.sqrt X : ℝ)) : ℂ) := by
  have hXpos : (0 : ℝ) < X := by linarith
  have hs : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.mpr hXpos
  rw [routeUPrimeMoment, LSeries, ← tsum_mul_left]
  refine tsum_congr fun m => ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [routeUPrimeTerm]
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  rw [routeUPrimeTerm, massPairing_cauchyFourierWeight_zero hXpos,
    LSeries.term_of_ne_zero (by omega)]
  have habs : |Real.log (m : ℝ)| = Real.log (m : ℝ) := abs_of_nonneg hlog
  rw [habs]
  have hexp : Real.exp (-(Real.sqrt X * Real.log (m : ℝ))) = (m : ℝ) ^ (-Real.sqrt X) := by
    rw [Real.rpow_def_of_pos hmpos]
    congr 1
    ring
  have hpow : ((m : ℂ)) ^ (((1 / 2 + Real.sqrt X : ℝ)) : ℂ)
      = (((m : ℝ) ^ (1 / 2 + Real.sqrt X) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hmpos.le]
    norm_cast
  rw [hexp, hpow]
  have hsplit : (m : ℝ) ^ (1 / 2 + Real.sqrt X) = Real.sqrt m * (m : ℝ) ^ (Real.sqrt X) := by
    rw [Real.rpow_add hmpos, Real.sqrt_eq_rpow (m : ℝ)]
  have hne : Real.sqrt (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmpos
    exact ne_of_gt this
  have hne2 : ((m : ℝ) ^ (Real.sqrt X)) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) ^ (Real.sqrt X) := Real.rpow_pos_of_pos hmpos _
    exact ne_of_gt this
  rw [hsplit, ← Complex.ofReal_div, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  rw [Real.rpow_neg hmpos.le]
  field_simp

end RHTower

end
