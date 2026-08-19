import GaloisForLFunctions.RHTower.PutnamFejerMass
import GaloisForLFunctions.HTGeometry.CosineArc

/-!
# The approximate-identity estimate for the periodised kernel

If every Fourier coefficient of the periodisation vanishes then pairing it against a Fejér kernel
centred at a point gives zero, while the Fejér kernel has total mass equal to the period and
concentrates at that point.  Comparing the two pairings bounds the value of the periodisation at
any continuity point by the local oscillation, hence forces it to vanish there.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- The Fejér kernel is integrable on a period. -/
theorem integrableOn_fejer_shift (d x₀ b : ℝ) (N : ℕ) :
    IntegrableOn (fun x => HTGeometry.fejerKernel N (d * (x - x₀))) (Ioc (0 : ℝ) b) :=
  Continuous.integrableOn_Ioc
    ((HTGeometry.continuous_fejerKernel N).comp (by fun_prop))

/-- The real form of the Fejér mass on a period. -/
theorem integral_fejer_mass_real {d : ℝ} (hd : 0 < d) (x₀ : ℝ) (N : ℕ) :
    (∫ x in Ioc (0 : ℝ) (putnamPeriod d), HTGeometry.fejerKernel N (d * (x - x₀)))
      = putnamPeriod d := by
  have h := integral_fejer_mass hd x₀ N
  have hcast : (∫ x in Ioc (0 : ℝ) (putnamPeriod d),
        ((HTGeometry.fejerKernel N (d * (x - x₀)) : ℝ) : ℂ))
      = (((∫ x in Ioc (0 : ℝ) (putnamPeriod d),
            HTGeometry.fejerKernel N (d * (x - x₀))) : ℝ) : ℂ) := integral_ofReal
  rw [hcast] at h
  exact_mod_cast h

/-- The oscillation of the periodisation around a point is integrable on a period. -/
theorem integrableOn_oscillation {a d : ℝ} (hd : 0 < d) (x₀ : ℝ) :
    IntegrableOn (fun x => ‖putnamPeriodization a d x₀ - putnamPeriodization a d x‖)
      (Ioc (0 : ℝ) (putnamPeriod d)) := by
  have hfin : (volume (Ioc (0 : ℝ) (putnamPeriod d))) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  exact (((integrableOn_const hfin).sub (integrableOn_putnamPeriodization (a := a) hd)).norm)

/-- On a period the step `dδ` never reaches a full turn, so its cosine is `< 1`. -/
theorem cos_period_step_lt_one {d δ : ℝ} (hd : 0 < d) (hδ0 : 0 < δ)
    (hδP : 2 * δ ≤ putnamPeriod d) : Real.cos (d * δ) < 1 := by
  have hdP : d * putnamPeriod d = 2 * Real.pi := by
    rw [putnamPeriod]
    field_simp
  have hpi := Real.pi_pos
  have hpos : 0 < d * δ := by positivity
  have hle : d * δ ≤ Real.pi := by nlinarith [hδP, hdP]
  rcases lt_or_eq_of_le (Real.cos_le_one (d * δ)) with h | h
  · exact h
  · exfalso
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff (d * δ)).mp h
    rcases lt_trichotomy n 0 with hnneg | hn0 | hnpos
    · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hnneg
      nlinarith
    · rw [hn0] at hn
      simp at hn
      rcases hn with h | h <;> linarith
    · have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
      nlinarith

/-- Away from the centre the Fejér kernel is uniformly small on a period. -/
theorem fejer_far_le {d : ℝ} (hd : 0 < d) {x₀ δ x : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ x₀)
    (hδ2 : x₀ + δ ≤ putnamPeriod d) (hx : x ∈ Ioc (0 : ℝ) (putnamPeriod d))
    (hfar : δ ≤ |x - x₀|) (N : ℕ) :
    HTGeometry.fejerKernel N (d * (x - x₀))
      ≤ 2 / (((N : ℝ) + 1) * (1 - Real.cos (d * δ))) := by
  have hdP : d * putnamPeriod d = 2 * Real.pi := by
    rw [putnamPeriod]
    field_simp
  have hcosδ : Real.cos (d * δ) < 1 := cos_period_step_lt_one hd hδ0 (by linarith)
  have habs : |d * (x - x₀)| = d * |x - x₀| := by
    rw [abs_mul, abs_of_pos hd]
  have hxle : |x - x₀| ≤ putnamPeriod d - δ := by
    rw [abs_le]
    constructor
    · linarith [hx.1]
    · linarith [hx.2]
  have harc : Real.cos (d * (x - x₀)) ≤ Real.cos (d * δ) := by
    refine HTGeometry.cos_le_cos_of_abs_mem_arc (by positivity) ?_ ?_
    · rw [habs]
      exact mul_le_mul_of_nonneg_left hfar hd.le
    · rw [habs]
      have : d * |x - x₀| ≤ d * (putnamPeriod d - δ) :=
        mul_le_mul_of_nonneg_left hxle hd.le
      nlinarith [hdP]
  have hne : Complex.exp (((d * (x - x₀) : ℝ) : ℂ) * Complex.I) ≠ 1 := by
    intro hE
    have hre := congrArg Complex.re hE
    rw [Complex.exp_ofReal_mul_I_re] at hre
    simp at hre
    linarith
  refine le_trans (HTGeometry.fejerKernel_le hne) ?_
  have hNn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hd1 : 0 < 1 - Real.cos (d * δ) := by linarith
  have hd2 : 0 < 1 - Real.cos (d * (x - x₀)) := by linarith
  refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
  nlinarith [harc, hNn]

/-- **The approximate-identity estimate.**  If all Fourier coefficients of the periodisation
vanish, its value at a point is controlled by its oscillation there. -/
theorem norm_putnamPeriodization_mul_period_le {a d : ℝ} (hd : 0 < d)
    (hzero : ∀ k : ℤ, (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d k x) = 0)
    {x₀ ε δ : ℝ} (hε : 0 ≤ ε) (hδ0 : 0 < δ) (hδ1 : δ ≤ x₀)
    (hδ2 : x₀ + δ ≤ putnamPeriod d)
    (hosc : ∀ x, |x - x₀| < δ →
      ‖putnamPeriodization a d x₀ - putnamPeriodization a d x‖ ≤ ε)
    (N : ℕ) :
    ‖putnamPeriodization a d x₀‖ * putnamPeriod d
      ≤ ε * putnamPeriod d
        + 2 / (((N : ℝ) + 1) * (1 - Real.cos (d * δ)))
            * ∫ x in Ioc (0 : ℝ) (putnamPeriod d),
                ‖putnamPeriodization a d x₀ - putnamPeriodization a d x‖ := by
  classical
  set P := putnamPeriod d with hPdef
  set D := putnamPeriodization a d with hDdef
  set K : ℝ → ℝ := fun x => HTGeometry.fejerKernel N (d * (x - x₀)) with hKdef
  set C : ℝ := 2 / (((N : ℝ) + 1) * (1 - Real.cos (d * δ))) with hCdef
  have hPpos : 0 < P := putnamPeriod_pos hd
  have hcosδ : Real.cos (d * δ) < 1 := cos_period_step_lt_one hd hδ0 (by linarith)
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    have : (0 : ℝ) < 1 - Real.cos (d * δ) := by linarith
    positivity
  have hfin : (volume (Ioc (0 : ℝ) P)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hKint : IntegrableOn K (Ioc (0 : ℝ) P) := integrableOn_fejer_shift d x₀ P N
  have hKbdd : ∀ x : ℝ, ‖((K x : ℝ) : ℂ)‖ ≤ (N : ℝ) + 1 := by
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (HTGeometry.fejerKernel_nonneg _ _)]
    exact HTGeometry.fejerKernel_le_card N _
  have hDint : IntegrableOn D (Ioc (0 : ℝ) P) := integrableOn_putnamPeriodization hd
  have hOscInt : IntegrableOn (fun x => ‖D x₀ - D x‖) (Ioc (0 : ℝ) P) :=
    integrableOn_oscillation hd x₀
  have hKC : IntegrableOn (fun x => ((K x : ℝ) : ℂ)) (Ioc (0 : ℝ) P) := hKint.ofReal
  have hint1 : IntegrableOn (fun x => ((K x : ℝ) : ℂ) * D x₀) (Ioc (0 : ℝ) P) :=
    hKC.mul_const _
  have hint2 : IntegrableOn (fun x => ((K x : ℝ) : ℂ) * D x) (Ioc (0 : ℝ) P) :=
    hDint.bdd_mul
      ((Complex.continuous_ofReal.comp
        ((HTGeometry.continuous_fejerKernel N).comp (by fun_prop))).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall hKbdd)
  have hzero2 : (∫ x in Ioc (0 : ℝ) P, ((K x : ℝ) : ℂ) * D x) = 0 := by
    rw [← integral_putnamPeriodization_fejer hd hzero x₀ N]
    exact setIntegral_congr_fun measurableSet_Ioc (fun x _ => mul_comm _ _)
  have hmass2 : (∫ x in Ioc (0 : ℝ) P, ((K x : ℝ) : ℂ) * D x₀) = D x₀ * ((P : ℝ) : ℂ) := by
    rw [integral_mul_const, integral_fejer_mass hd x₀ N]
    ring
  have hkey : (∫ x in Ioc (0 : ℝ) P, ((K x : ℝ) : ℂ) * (D x₀ - D x)) = D x₀ * ((P : ℝ) : ℂ) := by
    have hsplit : ∀ x : ℝ, ((K x : ℝ) : ℂ) * (D x₀ - D x)
        = ((K x : ℝ) : ℂ) * D x₀ - ((K x : ℝ) : ℂ) * D x := fun x => by ring
    rw [setIntegral_congr_fun measurableSet_Ioc (fun x _ => hsplit x),
      integral_sub hint1 hint2, hmass2, hzero2, sub_zero]
  have hnorm : ‖D x₀‖ * P ≤ ∫ x in Ioc (0 : ℝ) P, K x * ‖D x₀ - D x‖ := by
    have h1 : ‖D x₀ * ((P : ℝ) : ℂ)‖ = ‖D x₀‖ * P := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hPpos]
    calc ‖D x₀‖ * P = ‖∫ x in Ioc (0 : ℝ) P, ((K x : ℝ) : ℂ) * (D x₀ - D x)‖ := by
          rw [hkey, h1]
      _ ≤ ∫ x in Ioc (0 : ℝ) P, ‖((K x : ℝ) : ℂ) * (D x₀ - D x)‖ :=
          norm_integral_le_integral_norm _
      _ = ∫ x in Ioc (0 : ℝ) P, K x * ‖D x₀ - D x‖ := by
          refine setIntegral_congr_fun measurableSet_Ioc (fun x _ => ?_)
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (HTGeometry.fejerKernel_nonneg _ _)]
  have hpt : ∀ x ∈ Ioc (0 : ℝ) P, K x * ‖D x₀ - D x‖ ≤ ε * K x + C * ‖D x₀ - D x‖ := by
    intro x hx
    have hKnn : 0 ≤ K x := HTGeometry.fejerKernel_nonneg _ _
    have hOnn : (0 : ℝ) ≤ ‖D x₀ - D x‖ := norm_nonneg _
    rcases lt_or_ge |x - x₀| δ with hnear | hfar
    · have h := hosc x hnear
      nlinarith [mul_le_mul_of_nonneg_left h hKnn, mul_nonneg hCnn hOnn]
    · have h := fejer_far_le hd hδ0 hδ1 hδ2 hx hfar N
      have h' : K x ≤ C := h
      nlinarith [mul_le_mul_of_nonneg_right h' hOnn, mul_nonneg hε hKnn]
  have hintL : IntegrableOn (fun x => K x * ‖D x₀ - D x‖) (Ioc (0 : ℝ) P) := by
    refine hOscInt.bdd_mul (c := (N : ℝ) + 1)
      (((HTGeometry.continuous_fejerKernel N).comp (by fun_prop)).aestronglyMeasurable.restrict)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (HTGeometry.fejerKernel_nonneg _ _)]
    exact HTGeometry.fejerKernel_le_card N _
  have hintR : IntegrableOn (fun x => ε * K x + C * ‖D x₀ - D x‖) (Ioc (0 : ℝ) P) :=
    (hKint.const_mul ε).add (hOscInt.const_mul C)
  have hmono := setIntegral_mono_on hintL hintR measurableSet_Ioc hpt
  have hRHS : (∫ x in Ioc (0 : ℝ) P, (ε * K x + C * ‖D x₀ - D x‖))
      = ε * P + C * ∫ x in Ioc (0 : ℝ) P, ‖D x₀ - D x‖ := by
    rw [integral_add (hKint.const_mul ε) (hOscInt.const_mul C), integral_const_mul,
      integral_const_mul, integral_fejer_mass_real hd x₀ N]
  linarith [hnorm, hmono, hRHS.le, hRHS.ge]

end RHTower

end
