import GaloisForLFunctions.RHTower.RoutePLatePrimeIncrementJumps
import Mathlib.Analysis.PSeries

/-!
# Positive exponential admission of the actual prime-increment variation

Both the continuous velocity and every prime-square removal mass are
retained. These are measure-admission statements, not a bound for the
signed mixed primitive or for the native square energy.
-/

noncomputable section
open MeasureTheory Set Filter

namespace RHTower

private def velocityMass : ℝ :=
  ∫ t in Ioi (0 : ℝ), |criticalAbelLogVelocity t|

private theorem velocityMass_nonneg : 0 ≤ velocityMass :=
  integral_nonneg (fun _ => abs_nonneg _)

private theorem atom_norm_integral_le {p : ℕ} (hp : p.Prime) :
    (∫ t : ℝ, ‖routePLatePrimeVelocityAtom p t‖) ≤ velocityMass / p := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have heq : (fun t => ‖routePLatePrimeVelocityAtom p t‖) =
      (Ioc (Real.log p) (2 * Real.log p)).indicator
        (fun t => |criticalAbelLogVelocity (t - Real.log p)| / p) := by
    funext t
    by_cases ht : t ∈ Ioc (Real.log p) (2 * Real.log p)
    · simp [routePLatePrimeVelocityAtom, ht, norm_div, Real.norm_eq_abs]
    · simp [routePLatePrimeVelocityAtom, ht]
  rw [heq, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : Real.log (p : ℝ) ≤ 2 * Real.log p),
    intervalIntegral.integral_div,
    intervalIntegral.integral_comp_sub_right (fun u : ℝ => |criticalAbelLogVelocity u|),
    sub_self, show 2 * Real.log (p : ℝ) - Real.log p = Real.log p by ring,
    intervalIntegral.integral_of_le hl]
  apply div_le_div_of_nonneg_right _ hp0.le
  apply setIntegral_mono_set integrableOn_criticalAbelLogVelocity.norm
  · exact Eventually.of_forall (fun _ => abs_nonneg _)
  · exact Eventually.of_forall (fun _ hs => hs.1)

private theorem damped_atom_norm_le {η : ℝ} (hη : 0 < η) (p : ℕ) (t : ℝ) :
    ‖Real.exp (-η * t) * routePLatePrimeVelocityAtom p t‖ ≤
      Real.exp (-η * Real.log p) * ‖routePLatePrimeVelocityAtom p t‖ := by
  by_cases ht : t ∈ Ioc (Real.log p) (2 * Real.log p)
  · rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith [ht.1]
  · simp [routePLatePrimeVelocityAtom, ht]

private theorem integrable_damped_atom {η : ℝ} (hη : 0 < η) {p : ℕ} (hp : p.Prime) :
    Integrable (fun t => Real.exp (-η * t) * routePLatePrimeVelocityAtom p t) := by
  apply ((integrable_routePLatePrimeVelocityAtom hp).norm.const_mul
    (Real.exp (-η * Real.log p))).mono'
  · exact ((show Measurable (fun t : ℝ => Real.exp (-η * t)) by fun_prop).mul
      (measurable_routePLatePrimeVelocityAtom p)).aestronglyMeasurable
  · exact Eventually.of_forall (damped_atom_norm_le hη p)

private theorem exp_log_weight (η : ℝ) {p : ℕ} (hp : p.Prime) :
    Real.exp (-η * Real.log p) / p = 1 / (p : ℝ) ^ (1 + η) := by
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  rw [Real.rpow_add hp0, Real.rpow_one, Real.rpow_def_of_pos hp0]
  rw [show -η * Real.log (p : ℝ) = -(Real.log p * η) by ring, Real.exp_neg]
  ring

private theorem damped_atom_integral_norm_le {η : ℝ} (hη : 0 < η)
    {p : ℕ} (hp : p.Prime) :
    (∫ t : ℝ, ‖Real.exp (-η * t) * routePLatePrimeVelocityAtom p t‖) ≤
      velocityMass * (1 / (p : ℝ) ^ (1 + η)) := by
  calc
    _ ≤ ∫ t : ℝ, Real.exp (-η * Real.log p) * ‖routePLatePrimeVelocityAtom p t‖ :=
      integral_mono (integrable_damped_atom hη hp).norm
        ((integrable_routePLatePrimeVelocityAtom hp).norm.const_mul _)
        (damped_atom_norm_le hη p)
    _ = Real.exp (-η * Real.log p) * ∫ t : ℝ, ‖routePLatePrimeVelocityAtom p t‖ :=
      integral_const_mul _ _
    _ ≤ Real.exp (-η * Real.log p) * (velocityMass / p) :=
      mul_le_mul_of_nonneg_left (atom_norm_integral_le hp) (Real.exp_pos _).le
    _ = velocityMass * (1 / (p : ℝ) ^ (1 + η)) := by
      rw [← exp_log_weight η hp]
      ring

/-- Every positive damping admits the literal continuous velocity, with the
complete moving prime family retained. -/
theorem integrableOn_exp_mul_routePLatePrimeVelocity {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun t => Real.exp (-η * t) * routePLatePrimeVelocity t) (Ioi 0) := by
  let f : ℕ → ℝ → ℝ := fun p t => Real.exp (-η * t) * routePLatePrimeVelocityAtom p t
  have hf (p : ℕ) (hp : p.Prime) : Integrable (f p) := integrable_damped_atom hη hp
  have hfinite (T : ℝ) : Integrable (fun t =>
      ∑ p ∈ Nat.primesLE ⌊Real.exp T⌋₊, f p t) :=
    integrable_finsetSum _ (fun _ hp => hf _ (Nat.mem_primesLE.mp hp).2)
  have hfreeze (T t : ℝ) (ht : t ≤ T) :
      Real.exp (-η * t) * routePLatePrimeVelocity t =
        ∑ p ∈ Nat.primesLE ⌊Real.exp T⌋₊, f p t := by
    rw [routePLatePrimeVelocity_eq_finite ht, Finset.mul_sum]
  have hlocal (T : ℝ) : IntegrableOn
      (fun t => Real.exp (-η * t) * routePLatePrimeVelocity t) (Ioc 0 T) :=
    (hfinite T).integrableOn.congr_fun
      (fun t ht => (hfreeze T t ht.2).symm) measurableSet_Ioc
  have hseries : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + η)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  apply integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (velocityMass * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + η)) 0 hlocal tendsto_id
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  rw [intervalIntegral.integral_of_le hT]
  calc
    _ = ∫ t in Ioc (0 : ℝ) T, ‖∑ p ∈ Nat.primesLE ⌊Real.exp T⌋₊, f p t‖ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t ht
      dsimp only
      rw [hfreeze T t ht.2]
    _ ≤ ∫ t : ℝ, ‖∑ p ∈ Nat.primesLE ⌊Real.exp T⌋₊, f p t‖ := by
      have h := setIntegral_mono_set (s := Ioc (0 : ℝ) T)
        ((hfinite T).norm.integrableOn (s := univ))
        (Eventually.of_forall (fun _ => norm_nonneg _))
        (Eventually.of_forall (fun t _ => mem_univ t))
      simpa only [setIntegral_univ] using h
    _ ≤ ∫ t : ℝ, ∑ p ∈ Nat.primesLE ⌊Real.exp T⌋₊, ‖f p t‖ := by
      apply integral_mono (hfinite T).norm
        (integrable_finsetSum _ (fun _ hp => (hf _ (Nat.mem_primesLE.mp hp).2).norm))
      intro t
      exact norm_sum_le _ _
    _ = ∑ p ∈ Nat.primesLE ⌊Real.exp T⌋₊, ∫ t : ℝ, ‖f p t‖ :=
      integral_finsetSum _ (fun _ hp => (hf _ (Nat.mem_primesLE.mp hp).2).norm)
    _ ≤ ∑ p ∈ Nat.primesLE ⌊Real.exp T⌋₊, velocityMass * (1 / (p : ℝ) ^ (1 + η)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact damped_atom_integral_norm_le hη (Nat.mem_primesLE.mp hp).2
    _ = velocityMass * ∑ p ∈ Nat.primesLE ⌊Real.exp T⌋₊, 1 / (p : ℝ) ^ (1 + η) :=
      (Finset.mul_sum ..).symm
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ velocityMass_nonneg
      exact hseries.sum_le_tsum _ (fun _ _ => by positivity)

/-- Every actual prime-square jump is admitted under positive exponential
damping. The absolute value prevents cancellation from hiding removal mass. -/
theorem summable_exp_mul_routePLatePrimeRemovalMass {η : ℝ} (hη : 0 < η) :
    Summable (fun p : Nat.Primes => Real.exp (-η * (2 * Real.log (p : ℕ))) *
      |criticalAbelLogProfile (Real.log (p : ℕ))| / (p : ℕ)) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (1 + 2 * η)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  apply ((hs.subtype Nat.Prime).mul_left velocityMass).of_norm_bounded
  intro p
  have hp0 : 0 < ((p : ℕ) : ℝ) := by exact_mod_cast p.property.pos
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ Real.exp (-η * (2 * Real.log (p : ℕ))) * velocityMass / (p : ℕ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (criticalAbelLogProfile_uniform_bound _)
          (Real.exp_pos _).le) hp0.le
    _ = velocityMass * (1 / ((p : ℕ) : ℝ) ^ (1 + 2 * η)) := by
      rw [← exp_log_weight (2 * η) p.property]
      rw [show -η * (2 * Real.log (p : ℕ)) = -(2 * η) * Real.log (p : ℕ) by ring]
      ring

private theorem polynomial_damping_domination (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      Real.exp (-η * t) * t ^ k ≤ C * Real.exp (-(η / 2) * t) := by
  have hh : 0 < η / 2 := half_pos hη
  have hf : 0 < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  refine ⟨(k.factorial : ℝ) / (η / 2) ^ k, by positivity, ?_⟩
  intro t ht
  have he := Real.pow_div_factorial_le_exp _ (mul_nonneg hh.le ht) k
  rw [div_le_iff₀ hf, mul_pow] at he
  have hb : t ^ k ≤ (k.factorial : ℝ) / (η / 2) ^ k * Real.exp ((η / 2) * t) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hh k)]
    nlinarith only [he]
  calc
    _ ≤ Real.exp (-η * t) *
        ((k.factorial : ℝ) / (η / 2) ^ k * Real.exp ((η / 2) * t)) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = ((k.factorial : ℝ) / (η / 2) ^ k) *
        (Real.exp (-η * t) * Real.exp ((η / 2) * t)) := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

/-- Polynomial losses from a reciprocal chain rule do not exhaust any
strictly positive damping margin on the continuous part. -/
theorem integrableOn_exp_mul_pow_mul_routePLatePrimeVelocity
    (k : ℕ) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun t => Real.exp (-η * t) * t ^ k * routePLatePrimeVelocity t)
      (Ioi 0) := by
  obtain ⟨C, hC, hb⟩ := polynomial_damping_domination k hη
  apply ((integrableOn_exp_mul_routePLatePrimeVelocity (half_pos hη)).norm.const_mul C).mono'
  · exact (((show Measurable (fun t : ℝ => Real.exp (-η * t) * t ^ k) by fun_prop).mul
      measurable_routePLatePrimeVelocity).aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hpow : 0 ≤ t ^ k := pow_nonneg (show (0 : ℝ) ≤ t from ht.le) k
    simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg hpow]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hb t ht.le)
      (abs_nonneg (routePLatePrimeVelocity t))

/-- The same polynomial losses are admitted for all physical removal atoms. -/
theorem summable_exp_mul_pow_mul_routePLatePrimeRemovalMass
    (k : ℕ) {η : ℝ} (hη : 0 < η) :
    Summable (fun p : Nat.Primes =>
      Real.exp (-η * (2 * Real.log (p : ℕ))) * (2 * Real.log (p : ℕ)) ^ k *
        |criticalAbelLogProfile (Real.log (p : ℕ))| / (p : ℕ)) := by
  obtain ⟨C, hC, hb⟩ := polynomial_damping_domination k hη
  apply ((summable_exp_mul_routePLatePrimeRemovalMass (half_pos hη)).mul_left C).of_norm_bounded
  intro p
  have hl : 0 ≤ Real.log ((p : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)
  have hp0 : 0 < ((p : ℕ) : ℝ) := by exact_mod_cast p.property.pos
  rw [Real.norm_of_nonneg (by positivity)]
  have hb' := mul_le_mul_of_nonneg_right (hb (2 * Real.log (p : ℕ)) (by positivity))
    (div_nonneg (abs_nonneg (criticalAbelLogProfile (Real.log (p : ℕ)))) hp0.le)
  simpa only [mul_div_assoc, mul_assoc] using hb'

end RHTower
