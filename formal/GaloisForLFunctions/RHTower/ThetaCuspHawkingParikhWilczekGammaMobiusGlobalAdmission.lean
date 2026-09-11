import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusParameterGenerator
import Mathlib.NumberTheory.SumPrimeReciprocals
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier

/-!
# Exact global absolute admission of the actual Gamma/Möbius family

The individual atom masses on the positive ray with Lebesgue measure are
Gamma(3/2) times the full absolute Möbius coefficient and n^(-Re(z)-1).
The derivative atom retains its additional logarithmic factor. Both mass
series converge exactly when Re(z)>0; prime restriction proves necessity.
In that open region the complete signed source and current are integrable,
and both series pass through the ray integral.

Failure of the original atom mass sum at zero does not establish failure
of integrability of the signed source. No spectral parameter identification,
finite critical energy, stationarity or Riemann hypothesis is asserted.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set
noncomputable section

/-- The actual coefficient-deformed Gamma/Möbius atom. -/
def pwGammaMobiusGlobalAtom (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  ((moebius n : ℤ) : ℂ) * Complex.exp (-z * (Real.log (n : ℝ) : ℂ)) *
    pwGammaRaySource ((n : ℝ) * x)

/-- The derivative atom, retaining its logarithmic and Möbius coefficients. -/
def pwGammaMobiusGlobalCurrentAtom (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  -(Real.log (n : ℝ) : ℂ) * pwGammaMobiusGlobalAtom z n x

theorem pwGammaMobiusTilt_eq_global_atoms (z : ℂ) (x : ℝ) :
    pwGammaMobiusTilt z x = ∑' n, pwGammaMobiusGlobalAtom z n x := rfl

theorem pwGammaMobiusTiltCurrent_eq_global_atoms (z : ℂ) (x : ℝ) :
    pwGammaMobiusTiltCurrent z x = ∑' n, pwGammaMobiusGlobalCurrentAtom z n x := rfl

private theorem pwGammaRaySource_norm_eq {x : ℝ} (hx : 0 < x) :
    ‖pwGammaRaySource x‖ = Real.exp (-x) * x ^ ((3 / 2 : ℝ) - 1) := by
  rw [pwGammaRaySource_eq hx, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.sqrt_eq_rpow]
  rw [show (3 / 2 : ℝ) - 1 = 1 / 2 by ring]
  ring

theorem pwGammaRaySource_integrable : IntegrableOn pwGammaRaySource (Ioi 0) := by
  refine IntegrableOn.congr_fun
    ((Real.GammaIntegral_convergent (s := 3 / 2) (by positivity)).ofReal) ?_ measurableSet_Ioi
  intro x hx
  rw [pwGammaRaySource_eq hx, Real.sqrt_eq_rpow,
    show (3 / 2 : ℝ) - 1 = 1 / 2 by ring]
  exact congrArg (fun y : ℝ => (y : ℂ)) (mul_comm _ _)

theorem pwGammaRaySource_norm_integral :
    (∫ x in Ioi (0 : ℝ), ‖pwGammaRaySource x‖) = Real.Gamma (3 / 2) := by
  rw [Real.Gamma_eq_integral (s := 3 / 2) (by positivity)]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => pwGammaRaySource_norm_eq hx

theorem pwGammaMobiusGlobalAtom_integrable (z : ℂ) (n : ℕ) :
    IntegrableOn (pwGammaMobiusGlobalAtom z n) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hf : pwGammaMobiusGlobalAtom z 0 = 0 := by
      funext x
      simp [pwGammaMobiusGlobalAtom]
    rw [hf]
    exact integrable_zero ℝ ℂ (volume.restrict (Ioi 0))
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hscale : IntegrableOn (fun x => pwGammaRaySource ((n : ℝ) * x)) (Ioi 0) := by
      apply (integrableOn_Ioi_comp_mul_left_iff pwGammaRaySource 0 hnr).mpr
      simpa only [mul_zero] using pwGammaRaySource_integrable
    exact hscale.const_mul _

theorem pwGammaMobiusGlobalCurrentAtom_integrable (z : ℂ) (n : ℕ) :
    IntegrableOn (pwGammaMobiusGlobalCurrentAtom z n) (Ioi 0) :=
  (pwGammaMobiusGlobalAtom_integrable z n).const_mul _

theorem pwGammaMobiusGlobalAtom_norm_integral (z : ℂ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusGlobalAtom z n x‖) =
      Real.Gamma (3 / 2) * ‖((moebius n : ℤ) : ℂ)‖ * (n : ℝ) ^ (-z.re - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusGlobalAtom]
  · have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    simp only [pwGammaMobiusGlobalAtom, norm_mul, integral_const_mul]
    rw [integral_comp_mul_left_Ioi (fun x => ‖pwGammaRaySource x‖) 0 hnr, mul_zero, smul_eq_mul,
      pwGammaRaySource_norm_integral, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [show -z.re - 1 = -z.re + (-1) by ring, Real.rpow_add hnr,
      Real.rpow_neg_one, Real.rpow_def_of_pos hnr]
    rw [mul_comm (Real.log (n : ℝ)) (-z.re)]
    ring

private theorem pwNatLog_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact Real.log_nonneg (by exact_mod_cast hn)

theorem pwGammaMobiusGlobalCurrentAtom_norm_integral (z : ℂ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusGlobalCurrentAtom z n x‖) =
      Real.Gamma (3 / 2) *
        (Real.log (n : ℝ) * ‖((moebius n : ℤ) : ℂ)‖ * (n : ℝ) ^ (-z.re - 1)) := by
  simp only [pwGammaMobiusGlobalCurrentAtom, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (pwNatLog_nonneg n), integral_const_mul]
  rw [pwGammaMobiusGlobalAtom_norm_integral]
  ring

private theorem pwMobius_norm_le_one (n : ℕ) : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact_mod_cast (show |moebius n| ≤ 1 from abs_moebius_le_one)

private theorem pwMobius_prime_norm (p : Nat.Primes) :
    ‖((moebius (p : ℕ) : ℤ) : ℂ)‖ = 1 := by
  simp [moebius_apply_prime p.prop]

set_option backward.isDefEq.respectTransparency true in
private theorem pwGammaMobiusAbsoluteWeight_summable_iff (z : ℂ) :
    Summable (fun n : ℕ => ‖((moebius n : ℤ) : ℂ)‖ * (n : ℝ) ^ (-z.re - 1)) ↔
      0 < z.re := by
  constructor
  · intro h
    have hp : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-z.re - 1)) := by
      have hr : Summable (fun p : Nat.Primes =>
          ‖((moebius (p : ℕ) : ℤ) : ℂ)‖ * (p : ℝ) ^ (-z.re - 1)) :=
        h.comp_injective Nat.Primes.coe_nat_injective
      exact hr.congr (fun p => by rw [pwMobius_prime_norm p, one_mul])
    have hlt := Nat.Primes.summable_rpow.mp hp
    linarith
  · intro hz
    refine (Real.summable_nat_rpow.mpr (by linarith : -z.re - 1 < -1)).of_nonneg_of_le
      (fun n => by positivity) ?_
    intro n
    calc
      _ ≤ 1 * (n : ℝ) ^ (-z.re - 1) :=
        mul_le_mul_of_nonneg_right (pwMobius_norm_le_one n) (Real.rpow_nonneg (by positivity) _)
      _ = _ := one_mul _

set_option backward.isDefEq.respectTransparency true in
private theorem pwGammaMobiusAbsoluteLogWeight_summable_iff (z : ℂ) :
    Summable (fun n : ℕ => Real.log (n : ℝ) * ‖((moebius n : ℤ) : ℂ)‖ *
      (n : ℝ) ^ (-z.re - 1)) ↔ 0 < z.re := by
  constructor
  · intro h
    have hp : Summable (fun p : Nat.Primes => Real.log (p : ℝ) * (p : ℝ) ^ (-z.re - 1)) := by
      have hr : Summable (fun p : Nat.Primes =>
          Real.log (p : ℝ) * ‖((moebius (p : ℕ) : ℤ) : ℂ)‖ * (p : ℝ) ^ (-z.re - 1)) :=
        h.comp_injective Nat.Primes.coe_nat_injective
      exact hr.congr (fun p => by rw [pwMobius_prime_norm p, mul_one])
    have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hbound : Summable (fun p : Nat.Primes => Real.log 2 * (p : ℝ) ^ (-z.re - 1)) := by
      refine hp.of_nonneg_of_le (fun p => by positivity) ?_
      intro p
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
      exact Real.log_le_log (by positivity) (by exact_mod_cast p.prop.two_le)
    have hprime : Summable (fun p : Nat.Primes => (p : ℝ) ^ (-z.re - 1)) :=
      (summable_mul_left_iff hlog.ne').mp hbound
    have hlt := Nat.Primes.summable_rpow.mp hprime
    linarith
  · intro hz
    have hsum := Mertens.summable_log_div_rpow (s := z.re + 1) (by linarith)
    refine hsum.of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (pwNatLog_nonneg n)
      (norm_nonneg _)) (Real.rpow_nonneg (by positivity) _)) ?_
    intro n
    rw [show -z.re - 1 = -(z.re + 1) by ring, Real.rpow_neg (by positivity)]
    calc
      _ ≤ (Real.log (n : ℝ) * 1) * ((n : ℝ) ^ (z.re + 1))⁻¹ := by
        gcongr
        exact pwMobius_norm_le_one n
      _ = _ := by rw [mul_one, div_eq_mul_inv]

theorem pwGammaMobiusGlobalAtom_absolute_admission (z : ℂ) :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusGlobalAtom z n x‖) ↔
      0 < z.re := by
  simp_rw [pwGammaMobiusGlobalAtom_norm_integral, mul_assoc]
  rw [summable_mul_left_iff (Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < 3 / 2)).ne']
  exact pwGammaMobiusAbsoluteWeight_summable_iff z

theorem pwGammaMobiusGlobalCurrentAtom_absolute_admission (z : ℂ) :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusGlobalCurrentAtom z n x‖) ↔
      0 < z.re := by
  simp_rw [pwGammaMobiusGlobalCurrentAtom_norm_integral]
  rw [summable_mul_left_iff (Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < 3 / 2)).ne']
  exact pwGammaMobiusAbsoluteLogWeight_summable_iff z


/-- The complete signed source is globally integrable throughout the absolute region. -/
theorem pwGammaMobiusTilt_integrable {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (pwGammaMobiusTilt z) (Ioi 0) := by
  change Integrable (fun x => pwGammaMobiusTilt z x) (volume.restrict (Ioi 0))
  simp_rw [pwGammaMobiusTilt_eq_global_atoms]
  exact GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (pwGammaMobiusGlobalAtom_integrable z) ((pwGammaMobiusGlobalAtom_absolute_admission z).mpr hz)

/-- The same positive region admits the complete logarithmic derivative current. -/
theorem pwGammaMobiusTiltCurrent_integrable {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (pwGammaMobiusTiltCurrent z) (Ioi 0) := by
  change Integrable (fun x => pwGammaMobiusTiltCurrent z x) (volume.restrict (Ioi 0))
  simp_rw [pwGammaMobiusTiltCurrent_eq_global_atoms]
  exact GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (pwGammaMobiusGlobalCurrentAtom_integrable z)
    ((pwGammaMobiusGlobalCurrentAtom_absolute_admission z).mpr hz)

theorem pwGammaMobiusTilt_integral_eq_tsum {z : ℂ} (hz : 0 < z.re) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusTilt z x) =
      ∑' n, ∫ x in Ioi (0 : ℝ), pwGammaMobiusGlobalAtom z n x := by
  simp_rw [pwGammaMobiusTilt_eq_global_atoms]
  exact (integral_tsum_of_summable_integral_norm (pwGammaMobiusGlobalAtom_integrable z)
    ((pwGammaMobiusGlobalAtom_absolute_admission z).mpr hz)).symm

theorem pwGammaMobiusTiltCurrent_integral_eq_tsum {z : ℂ} (hz : 0 < z.re) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusTiltCurrent z x) =
      ∑' n, ∫ x in Ioi (0 : ℝ), pwGammaMobiusGlobalCurrentAtom z n x := by
  simp_rw [pwGammaMobiusTiltCurrent_eq_global_atoms]
  exact (integral_tsum_of_summable_integral_norm (pwGammaMobiusGlobalCurrentAtom_integrable z)
    ((pwGammaMobiusGlobalCurrentAtom_absolute_admission z).mpr hz)).symm

/-- Exact absolute boundary with its positive survivor. This says nothing about
nonintegrability of the signed sum at the boundary. -/
theorem pwGammaMobiusGlobalAdmission_closed :
    (∀ z : ℂ,
      (Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusGlobalAtom z n x‖) ↔
        0 < z.re) ∧
      (Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusGlobalCurrentAtom z n x‖) ↔
        0 < z.re)) ∧
    (∀ z : ℂ, 0 < z.re →
      IntegrableOn (pwGammaMobiusTilt z) (Ioi 0) ∧
      IntegrableOn (pwGammaMobiusTiltCurrent z) (Ioi 0)) ∧
    (¬ Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusGlobalAtom 0 n x‖)) ∧
    (¬ Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusGlobalCurrentAtom 0 n x‖)) := by
  refine ⟨fun z => ⟨pwGammaMobiusGlobalAtom_absolute_admission z,
      pwGammaMobiusGlobalCurrentAtom_absolute_admission z⟩,
    fun z hz => ⟨pwGammaMobiusTilt_integrable hz, pwGammaMobiusTiltCurrent_integrable hz⟩, ?_, ?_⟩
  · rw [pwGammaMobiusGlobalAtom_absolute_admission]
    simp
  · rw [pwGammaMobiusGlobalCurrentAtom_absolute_admission]
    simp

end
end RHTower
