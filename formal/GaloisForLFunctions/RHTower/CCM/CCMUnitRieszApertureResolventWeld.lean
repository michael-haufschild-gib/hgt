import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszFUCurvatureTransport
import GaloisForLFunctions.RHTower.CCM.CCMCriticalMellinApertureResolvent
import GaloisForLFunctions.RHTower.XiMassCriticalOutgoingCurrent

/-!
# Unit-Riesz / CCM aperture-resolvent weld

Substitution of the literal completed-error Volterra law into the finite-aperture unit-Riesz
Stieltjes response cancels one exponential channel exactly.  The response becomes one unit-rate
positive causal resolvent of the normalized Chebyshev error plus an explicit elementary remainder.

This is an unconditional source identity.  It proves no source estimate and assumes no zero
location, RH, or smoothing of the prime staircase.
-/

open Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- Positive unit-rate ray integral before adjoining the elementary `0 < y < 1` source tail. -/
def unitRieszChebyshevRayIntegral (t : ℝ) : ℝ :=
  ∫ h in (0 : ℝ)..t,
    Real.exp h * criticalMellinNormalizedChebyshevError h

/-- Exact collapse of the literal completed-source unit-Riesz response to one Chebyshev ray
integral plus an elementary polar remainder. -/
theorem unitRieszCompletedSourceResponse_eq_chebyshevRayIntegral
    {t : ℝ} (ht : 0 ≤ t) :
    unitRieszCompletedSourceResponse t =
      ((3 * (t - 3) * Real.exp (-t) +
          9 * Real.exp (-3 * t / 2) -
          (3 / 2) * Real.exp (-3 * t / 2) *
            unitRieszChebyshevRayIntegral t : ℝ) : ℂ) := by
  let g : ℝ → ℝ := criticalMellinNormalizedErrorCutoff t
  let V : ℝ → ℝ := fun h => ∫ u in (0 : ℝ)..h, g u
  let F : ℝ → ℝ := unitRieszCompletedSourceTestReal t
  let F' : ℝ → ℝ := unitRieszCompletedSourceTestDerivReal t
  have hgmeas : Measurable g := measurable_criticalMellinNormalizedErrorCutoff t
  let C : ℝ := criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k)
      (Real.exp t) + Real.exp t
  have hgbound : ∀ h, |g h| ≤ C := by
    intro h
    exact abs_criticalMellinNormalizedErrorCutoff_le t h
  have hgint : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    exact GaloisForLFunctions.RHTower.intervalIntegrable_of_bound hgmeas hgbound a b
  have hFderiv : ∀ h ∈ Icc (0 : ℝ) t, HasDerivAt F (F' h) h := by
    intro h _
    exact hasDerivAt_unitRieszCompletedSourceTestReal t h
  have hF'cont : Continuous F' := by
    change Continuous (fun s : ℝ =>
      (3 / 2) * Real.exp (-t + s / 2) - 3 * Real.exp (-3 * t / 2 + s))
    fun_prop
  have hFcont : Continuous F := by
    change Continuous (fun s : ℝ =>
      3 * (Real.exp (-t + s / 2) - Real.exp (-3 * t / 2 + s)))
    fun_prop
  have hF'bound : ∀ h ∈ Icc (0 : ℝ) t, |F' h| ≤ 9 / 2 := by
    intro h hh
    have he1 : Real.exp (-t + h / 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hh.2, ht]
    have he2 : Real.exp (-3 * t / 2 + h) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hh.2, ht]
    dsimp only [F', unitRieszCompletedSourceTestDerivReal]
    calc
      |(3 / 2) * Real.exp (-t + h / 2) -
          3 * Real.exp (-3 * t / 2 + h)| ≤
        |(3 / 2) * Real.exp (-t + h / 2)| +
          |3 * Real.exp (-3 * t / 2 + h)| := abs_sub _ _
      _ = (3 / 2) * Real.exp (-t + h / 2) +
          3 * Real.exp (-3 * t / 2 + h) := by
        rw [abs_of_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le),
          abs_of_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le)]
      _ ≤ 9 / 2 := by nlinarith
  have hVibp :
      (∫ h in (0 : ℝ)..t, F' h * V h) =
        F t * (∫ h in (0 : ℝ)..t, g h) -
          ∫ h in (0 : ℝ)..t, F h * g h := by
    exact GaloisForLFunctions.RHTower.integral_deriv_mul_primitive ht
      hgmeas hgbound hF'cont.measurable hFderiv hF'bound
  have hFt : F t = 0 := by
    dsimp only [F, unitRieszCompletedSourceTestReal]
    have he : Real.exp (-t + t / 2) = Real.exp (-3 * t / 2 + t) := by
      congr 1
      ring
    rw [he]
    ring
  have hVibp' :
      (∫ h in (0 : ℝ)..t, V h * F' h) =
        -(∫ h in (0 : ℝ)..t, g h * F h) := by
    rw [show (fun h => V h * F' h) = fun h => F' h * V h by
      funext h; ring, hVibp, hFt]
    simp only [zero_mul, zero_sub]
    congr 1
    apply intervalIntegral.integral_congr
    intro h _
    ring
  have hVcont : Continuous V := by
    exact intervalIntegral.continuous_primitive hgint 0
  have hgF'int : IntervalIntegrable (fun h => g h * F' h) volume 0 t :=
    (hgint 0 t).mul_continuousOn hF'cont.continuousOn
  have hgFint : IntervalIntegrable (fun h => g h * F h) volume 0 t :=
    (hgint 0 t).mul_continuousOn hFcont.continuousOn
  have hVF'int : IntervalIntegrable (fun h => V h * F' h) volume 0 t :=
    (hVcont.mul hF'cont).intervalIntegrable 0 t
  have hpF'int : IntervalIntegrable
      (fun h => (1 - 2 * Real.exp (-h / 2)) * F' h) volume 0 t := by
    exact (by fun_prop : Continuous
      (fun h => (1 - 2 * Real.exp (-h / 2)) * F' h)).intervalIntegrable 0 t
  have hmodel : ∀ h ∈ Icc (0 : ℝ) t,
      criticalMellinCompletedError h =
        1 - 2 * Real.exp (-h / 2) - g h - (1 / 2) * V h := by
    intro h hh
    rw [criticalMellinCompletedError_eq_cutoff_volterra hh]
  have hreal :
      -(∫ h in (0 : ℝ)..t, criticalMellinCompletedError h * F' h) =
        3 * (t - 3) * Real.exp (-t) +
          9 * Real.exp (-3 * t / 2) -
          (3 / 2) * Real.exp (-3 * t / 2) *
            unitRieszChebyshevRayIntegral t := by
    have hrewrite :
        (∫ h in (0 : ℝ)..t, criticalMellinCompletedError h * F' h) =
          ∫ h in (0 : ℝ)..t,
            ((1 - 2 * Real.exp (-h / 2)) * F' h - g h * F' h -
              (1 / 2) * (V h * F' h)) := by
      apply intervalIntegral.integral_congr
      intro h hh
      have hi : h ∈ Icc (0 : ℝ) t := by
        rw [uIcc_of_le ht] at hh
        exact hh
      change criticalMellinCompletedError h * F' h = _
      rw [hmodel h hi]
      ring
    have hpoint : ∀ h ∈ Icc (0 : ℝ) t, g h =
        criticalMellinNormalizedChebyshevError h := by
      intro h hh
      dsimp only [g]
      rw [criticalMellinNormalizedErrorCutoff, if_pos hh]
    have hsource :
        (∫ h in (0 : ℝ)..t, g h * F' h) -
            (1 / 2) * (∫ h in (0 : ℝ)..t, g h * F h) =
          -(3 / 2) * Real.exp (-3 * t / 2) *
            unitRieszChebyshevRayIntegral t := by
      calc
        (∫ h in (0 : ℝ)..t, g h * F' h) -
              (1 / 2) * (∫ h in (0 : ℝ)..t, g h * F h) =
            ∫ h in (0 : ℝ)..t,
              (g h * F' h - (1 / 2) * (g h * F h)) := by
          rw [intervalIntegral.integral_sub hgF'int
            (hgFint.const_mul (1 / 2)), intervalIntegral.integral_const_mul]
        _ = ∫ h in (0 : ℝ)..t,
              (-(3 / 2) * Real.exp (-3 * t / 2)) *
                (Real.exp h * criticalMellinNormalizedChebyshevError h) := by
          apply intervalIntegral.integral_congr
          intro h hh
          have hi : h ∈ Icc (0 : ℝ) t := by
            rw [uIcc_of_le ht] at hh
            exact hh
          change g h * F' h - (1 / 2) * (g h * F h) = _
          rw [hpoint h hi]
          dsimp only [F, F', unitRieszCompletedSourceTestReal,
            unitRieszCompletedSourceTestDerivReal]
          have he : Real.exp (-3 * t / 2) * Real.exp h =
              Real.exp (-3 * t / 2 + h) := by rw [← Real.exp_add]
          rw [← he]
          ring
        _ = _ := by
          rw [intervalIntegral.integral_const_mul]
          rfl
    have hpolar :
        -(∫ h in (0 : ℝ)..t,
            (1 - 2 * Real.exp (-h / 2)) * F' h) =
          3 * (t - 3) * Real.exp (-t) +
            9 * Real.exp (-3 * t / 2) := by
      let p : ℝ → ℝ := fun h => 1 - 2 * Real.exp (-h / 2)
      let p' : ℝ → ℝ := fun h => Real.exp (-h / 2)
      have hpderiv : ∀ h ∈ uIcc (0 : ℝ) t, HasDerivAt p (p' h) h := by
        intro h _
        have he : HasDerivAt (fun x : ℝ => Real.exp (-x / 2))
            (-(1 / 2) * Real.exp (-h / 2)) h := by
          have he0 := (Real.hasDerivAt_exp (-h / 2)).comp h
            ((hasDerivAt_neg h).div_const 2)
          exact he0.congr_deriv (by ring)
        have hp0 := (hasDerivAt_const h (1 : ℝ)).sub (he.const_mul 2)
        change HasDerivAt
          ((fun _ : ℝ => 1) - fun y : ℝ => 2 * Real.exp (-y / 2))
          (Real.exp (-h / 2)) h
        exact hp0.congr_deriv (by ring)
      have hFderivU : ∀ h ∈ uIcc (0 : ℝ) t, HasDerivAt F (F' h) h := by
        intro h hh
        apply hFderiv h
        rwa [uIcc_of_le ht] at hh
      have hp'int : IntervalIntegrable p' volume 0 t := by
        exact (by
          dsimp only [p']
          fun_prop : Continuous p').intervalIntegrable 0 t
      have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
        hpderiv hFderivU hp'int (hF'cont.intervalIntegrable 0 t)
      have hp0 : p 0 = -1 := by norm_num [p]
      have hF0 : F 0 = 3 * (Real.exp (-t) - Real.exp (-3 * t / 2)) := by
        simp [F, unitRieszCompletedSourceTestReal]
      have hpF :
          (∫ h in (0 : ℝ)..t, p' h * F h) =
            3 * t * Real.exp (-t) - 6 * Real.exp (-t) +
              6 * Real.exp (-3 * t / 2) := by
        have hrewritePF :
            (∫ h in (0 : ℝ)..t, p' h * F h) =
              ∫ h in (0 : ℝ)..t,
                (3 * Real.exp (-t) -
                  3 * Real.exp (-3 * t / 2) * Real.exp ((1 / 2) * h)) := by
          apply intervalIntegral.integral_congr
          intro h _
          dsimp only [p', F, unitRieszCompletedSourceTestReal]
          calc
            Real.exp (-h / 2) *
                (3 * (Real.exp (-t + h / 2) -
                  Real.exp (-3 * t / 2 + h))) =
              3 * (Real.exp (-h / 2) * Real.exp (-t + h / 2)) -
                3 * (Real.exp (-h / 2) * Real.exp (-3 * t / 2 + h)) := by ring
            _ = _ := by
              rw [show Real.exp (-h / 2) * Real.exp (-t + h / 2) =
                    Real.exp (-t) by rw [← Real.exp_add]; congr 1; ring,
                  show Real.exp (-h / 2) * Real.exp (-3 * t / 2 + h) =
                    Real.exp (-3 * t / 2) * Real.exp ((1 / 2) * h) by
                    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring]
              ring
        rw [hrewritePF]
        have hiexp : (∫ h in (0 : ℝ)..t, Real.exp ((1 / 2) * h)) =
            2 * (Real.exp (t / 2) - 1) := by
          have hderiv : ∀ h : ℝ, HasDerivAt
              (fun x : ℝ => 2 * Real.exp ((1 / 2) * x))
              (Real.exp ((1 / 2) * h)) h := by
            intro h
            have hd := (Real.hasDerivAt_exp ((1 / 2) * h)).comp h
              ((hasDerivAt_const h (1 / 2 : ℝ)).mul (hasDerivAt_id h))
            exact (hd.const_mul 2).congr_deriv (by ring)
          have hi : IntervalIntegrable (fun h : ℝ => Real.exp ((1 / 2) * h))
              volume 0 t := (by fun_prop : Continuous
                (fun h : ℝ => Real.exp ((1 / 2) * h))).intervalIntegrable 0 t
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun h _ => hderiv h) hi]
          norm_num
          ring
        have hc : IntervalIntegrable (fun _ : ℝ => 3 * Real.exp (-t)) volume 0 t :=
          intervalIntegrable_const
        have he : IntervalIntegrable
            (fun h : ℝ => 3 * Real.exp (-3 * t / 2) * Real.exp ((1 / 2) * h))
            volume 0 t := (by fun_prop : Continuous
              (fun h : ℝ => 3 * Real.exp (-3 * t / 2) *
                Real.exp ((1 / 2) * h))).intervalIntegrable 0 t
        rw [intervalIntegral.integral_sub hc he,
          intervalIntegral.integral_const,
          intervalIntegral.integral_const_mul,
          hiexp]
        have hmix : Real.exp (-3 * t / 2) * Real.exp (t / 2) =
            Real.exp (-t) := by
          rw [← Real.exp_add]
          congr 1
          ring
        simp only [smul_eq_mul, sub_zero]
        rw [show 3 * Real.exp (-3 * t / 2) *
            (2 * (Real.exp (t / 2) - 1)) =
              6 * (Real.exp (-3 * t / 2) * Real.exp (t / 2) -
                Real.exp (-3 * t / 2)) by ring,
          hmix]
        ring
      change -(∫ h in (0 : ℝ)..t, p h * F' h) = _
      rw [show (∫ h in (0 : ℝ)..t, p h * F' h) =
          p t * F t - p 0 * F 0 - ∫ h in (0 : ℝ)..t, p' h * F h by
        linarith [hparts], hFt, hp0, hF0, hpF]
      ring
    rw [hrewrite, intervalIntegral.integral_sub
      (hpF'int.sub hgF'int) (hVF'int.const_mul (1 / 2)),
      intervalIntegral.integral_sub hpF'int hgF'int,
      intervalIntegral.integral_const_mul, hVibp']
    linear_combination hpolar + hsource
  rw [unitRieszCompletedSourceResponse_eq_errorIntegral ht]
  have hcomplex :
      (∫ h in Ioc (0 : ℝ) t,
          (criticalMellinCompletedError h : ℂ) *
            unitRieszCompletedSourceTestDeriv t h) =
        ((∫ h in Ioc (0 : ℝ) t,
          criticalMellinCompletedError h * F' h : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with h
    dsimp only [F', unitRieszCompletedSourceTestDeriv,
      unitRieszCompletedSourceTestDerivReal]
    push_cast
    ring
  rw [hcomplex, ← intervalIntegral.integral_of_le ht]
  exact_mod_cast hreal

/-- The normalized errors used by completed-current and aperture-resolvent modules coincide. -/
theorem criticalMellinNormalizedChebyshevError_eq_apertureError (x : ℝ) :
    criticalMellinNormalizedChebyshevError x =
      criticalMellinChebyshevError x := by
  rw [criticalMellinNormalizedChebyshevError, criticalMellinError,
    criticalCumulative_vonMangoldt_eq_psi,
    criticalMellinChebyshevError_eq_exp]
  have hsqrt : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
    rw [← Real.exp_half]
  rw [hsqrt, div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

/-- Logarithmic substitution: ray integral is exactly the weighted Chebyshev prime integral from
`1` to the moving aperture. -/
theorem unitRieszChebyshevRayIntegral_eq_primeIntegral
    (t : ℝ) :
    unitRieszChebyshevRayIntegral t =
      ∫ y in (1 : ℝ)..Real.exp t,
        (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ)) := by
  let G : ℝ → ℝ := fun y =>
    (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := t) (f := Real.exp) (f' := Real.exp) (g := G)
    Real.continuous_exp.continuousOn
    (fun x _ => Real.hasDerivAt_exp x)
    (fun x _ => (Real.exp_pos x).le)
  calc
    unitRieszChebyshevRayIntegral t =
        ∫ x in (0 : ℝ)..t, (G ∘ Real.exp) x * Real.exp x := by
      unfold unitRieszChebyshevRayIntegral
      apply intervalIntegral.integral_congr
      intro x _
      change Real.exp x * criticalMellinNormalizedChebyshevError x =
        (G ∘ Real.exp) x * Real.exp x
      rw [criticalMellinNormalizedChebyshevError_eq_apertureError,
        criticalMellinChebyshevError_eq_exp]
      dsimp only [Function.comp_apply, G]
      have he : Real.exp x ^ (-(1 / 2 : ℝ)) = Real.exp (-x / 2) := by
        rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
        congr 1
        ring
      rw [he]
      ring
    _ = ∫ u in Real.exp (0 : ℝ)..Real.exp t, G u := hsub
    _ = _ := by norm_num [G]

/-- Exact elementary tail needed to pass from the ray-initialized to full causal resolvent. -/
theorem integral_chebyshevHalfWeight_zero_one :
    (∫ y in (0 : ℝ)..1,
      (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))) = -(2 / 3 : ℝ) := by
  calc
    (∫ y in (0 : ℝ)..1,
        (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))) =
      ∫ y in (0 : ℝ)..1, -(y ^ (1 / 2 : ℝ)) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hy' : y ∈ Icc (0 : ℝ) 1 := by
          rwa [uIcc_of_le zero_le_one] at hy
        change (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ)) =
          -(y ^ (1 / 2 : ℝ))
        rw [Chebyshev.psi_eq_zero_of_le_one hy'.2, zero_sub]
        by_cases hy0 : y = 0
        · simp [hy0]
        · have hyp : 0 < y := lt_of_le_of_ne hy'.1 (Ne.symm hy0)
          rw [neg_mul]
          congr 1
          nth_rewrite 1 [← Real.rpow_one y]
          rw [← Real.rpow_add hyp]
          congr 1
          ring
    _ = -(∫ y in (0 : ℝ)..1, y ^ (1 / 2 : ℝ)) := by
      rw [intervalIntegral.integral_neg]
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
      norm_num

/-- The ray integral differs from the corpus unit aperture resolvent only by its exact elementary
past tail `2/3`. -/
theorem unitRieszChebyshevRayIntegral_eq_fullResolvent
    {t : ℝ} (ht : 0 ≤ t) :
    unitRieszChebyshevRayIntegral t =
      Real.exp t * criticalMellinChebyshevResolventSource t + 2 / 3 := by
  let G : ℝ → ℝ := fun y =>
    (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))
  have hX : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hbase : IntervalIntegrable (fun y : ℝ => Chebyshev.psi y - y)
      volume 1 (Real.exp t) :=
    Chebyshev.psi_mono.intervalIntegrable.sub
      (continuous_id.intervalIntegrable 1 (Real.exp t))
  have hrpow : ContinuousOn (fun y : ℝ => y ^ (-(1 / 2 : ℝ)))
      (uIcc (1 : ℝ) (Real.exp t)) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro y hy
    left
    rw [uIcc_of_le hX] at hy
    simpa only [id_eq] using ne_of_gt (zero_lt_one.trans_le hy.1)
  have hlarge : IntervalIntegrable G volume 1 (Real.exp t) := by
    exact hbase.mul_continuousOn hrpow
  have hsmall : IntervalIntegrable G volume 0 1 := by
    have heq : EqOn G (fun y : ℝ => -(y ^ (1 / 2 : ℝ))) (uIoc (0 : ℝ) 1) := by
      intro y hy
      have hy' : y ∈ Ioc (0 : ℝ) 1 := by
        rwa [uIoc_of_le zero_le_one] at hy
      dsimp only [G]
      rw [Chebyshev.psi_eq_zero_of_le_one hy'.2, zero_sub, neg_mul]
      congr 1
      nth_rewrite 1 [← Real.rpow_one y]
      rw [← Real.rpow_add hy'.1]
      congr 1
      ring
    rw [intervalIntegrable_congr heq]
    exact (Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).neg.intervalIntegrable
      0 1
  have hadd := intervalIntegral.integral_add_adjacent_intervals hsmall hlarge
  have hres := criticalMellinChebyshevResolventSource_log_eq
    (X := Real.exp t) (Real.exp_pos t)
  rw [Real.log_exp] at hres
  have hinv : (Real.exp t)⁻¹ = Real.exp (-t) := by
    rw [← Real.exp_neg]
  rw [hinv] at hres
  have hprime := unitRieszChebyshevRayIntegral_eq_primeIntegral t
  have hsmallValue : (∫ y in (0 : ℝ)..1, G y) = -(2 / 3 : ℝ) := by
    exact integral_chebyshevHalfWeight_zero_one
  change (∫ y in (0 : ℝ)..1, G y) +
      (∫ y in (1 : ℝ)..Real.exp t, G y) =
        ∫ y in (0 : ℝ)..Real.exp t, G y at hadd
  change criticalMellinChebyshevResolventSource t =
      Real.exp (-t) * (∫ y in (0 : ℝ)..Real.exp t, G y) at hres
  change unitRieszChebyshevRayIntegral t =
      ∫ y in (1 : ℝ)..Real.exp t, G y at hprime
  rw [hsmallValue, ← hprime] at hadd
  rw [hres, ← hadd]
  have he : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [show Real.exp t *
      (Real.exp (-t) * (-(2 / 3) + unitRieszChebyshevRayIntegral t)) =
        (Real.exp t * Real.exp (-t)) *
          (-(2 / 3) + unitRieszChebyshevRayIntegral t) by ring,
    he]
  ring

/-- **Literal source weld.** The two-exponential unit-Riesz response is one positive unit CCM
aperture resolvent plus a completely explicit exponentially decaying remainder. -/
theorem unitRieszCompletedSourceResponse_eq_apertureResolvent
    {t : ℝ} (ht : 0 ≤ t) :
    unitRieszCompletedSourceResponse t =
      ((3 * (t - 3) * Real.exp (-t) +
          8 * Real.exp (-3 * t / 2) -
          (3 / 2) * Real.exp (-t / 2) *
            criticalMellinChebyshevResolventSource t : ℝ) : ℂ) := by
  rw [unitRieszCompletedSourceResponse_eq_chebyshevRayIntegral ht,
    unitRieszChebyshevRayIntegral_eq_fullResolvent ht]
  congr 1
  have he : Real.exp (-3 * t / 2) * Real.exp t = Real.exp (-t / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show (3 / 2) * Real.exp (-3 * t / 2) *
      (Real.exp t * criticalMellinChebyshevResolventSource t + 2 / 3) =
        (3 / 2) * (Real.exp (-3 * t / 2) * Real.exp t) *
            criticalMellinChebyshevResolventSource t +
          Real.exp (-3 * t / 2) by ring,
    he]
  ring

/-- Elementary remainder after exact unit-resolvent collapse. -/
def unitRieszApertureResolventRemainder (t : ℝ) : ℝ :=
  3 * (t - 3) * Real.exp (-t) + 8 * Real.exp (-3 * t / 2)

theorem unitRieszCompletedSourceResponse_re_eq_apertureResolvent
    {t : ℝ} (ht : 0 ≤ t) :
    (unitRieszCompletedSourceResponse t).re =
      unitRieszApertureResolventRemainder t -
        (3 / 2) * Real.exp (-t / 2) *
          criticalMellinChebyshevResolventSource t := by
  rw [unitRieszCompletedSourceResponse_eq_apertureResolvent ht]
  rfl

/-- Exact orientation law: every lower bound for the literal unit-Riesz response is the
corresponding upper bound for the positive unit CCM aperture resolvent, with no exponent loss. -/
theorem unitRieszCompletedSourceResponse_re_ge_iff_apertureResolvent_le
    {t B : ℝ} (ht : 0 ≤ t) :
    B ≤ (unitRieszCompletedSourceResponse t).re ↔
      criticalMellinChebyshevResolventSource t ≤
        (2 / 3) * Real.exp (t / 2) *
          (unitRieszApertureResolventRemainder t - B) := by
  rw [unitRieszCompletedSourceResponse_re_eq_apertureResolvent ht]
  let a : ℝ := (3 / 2) * Real.exp (-t / 2)
  let q : ℝ := (2 / 3) * Real.exp (t / 2)
  have ha : 0 < a := mul_pos (by norm_num) (Real.exp_pos _)
  have hq : 0 < q := mul_pos (by norm_num) (Real.exp_pos _)
  have haq : a * q = 1 := by
    dsimp only [a, q]
    rw [show (3 / 2) * Real.exp (-t / 2) *
        ((2 / 3) * Real.exp (t / 2)) =
          ((3 / 2) * (2 / 3)) *
            (Real.exp (-t / 2) * Real.exp (t / 2)) by ring]
    have he : Real.exp (-t / 2) * Real.exp (t / 2) = 1 := by
      rw [← Real.exp_add]
      have : -t / 2 + t / 2 = 0 := by ring
      rw [this, Real.exp_zero]
    rw [he]
    norm_num
  have hqa : q * a = 1 := by rw [mul_comm, haq]
  change B ≤ unitRieszApertureResolventRemainder t -
      a * criticalMellinChebyshevResolventSource t ↔
    criticalMellinChebyshevResolventSource t ≤
      q * (unitRieszApertureResolventRemainder t - B)
  constructor
  · intro h
    have hm := mul_le_mul_of_nonneg_left
      (show a * criticalMellinChebyshevResolventSource t ≤
          unitRieszApertureResolventRemainder t - B by linarith) hq.le
    rw [show q * (a * criticalMellinChebyshevResolventSource t) =
        (q * a) * criticalMellinChebyshevResolventSource t by ring,
      hqa, one_mul] at hm
    exact hm
  · intro h
    have hm := mul_le_mul_of_nonneg_left h ha.le
    rw [show a *
        (q * (unitRieszApertureResolventRemainder t - B)) =
          (a * q) * (unitRieszApertureResolventRemainder t - B) by ring,
      haq, one_mul] at hm
    linarith

end GaloisForLFunctions.RHTower

end
