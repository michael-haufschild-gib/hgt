import Mathlib.Tactic

/-! # The sharp binary probability contrast at bounded odds distortion -/

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells

/-- Exact remainder in the sharp event-probability inequality. The square measures
the error in the reference probability and the second term measures the unsaturated odds. -/
theorem contrast_balance {s : ℝ} (hs : 1 ≤ s) (p q : ℝ) :
    ((s-1)/(s+1)-(q-p))*((s+1)*(1+(s^2-1)*p)) =
    (s-1)*((s+1)*p-1)^2+(s+1)*(s^2*p*(1-q)-q*(1-p)) := by
  have h : 0 < s+1 := by linarith only [hs]
  field_simp [h.ne']
  ring

private theorem multiplier_pos {s p : ℝ} (hs : 1 ≤ s) (hp : 0 ≤ p) :
    0 < (s+1)*(1+(s^2-1)*p) := by
  have hs2 : 0 ≤ s^2-1 := by nlinarith only [hs,sq_nonneg (s-1)]
  exact mul_pos (by linarith only [hs]) (add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hs2 hp))

theorem binary_bound {s p q : ℝ} (hs : 1 ≤ s) (hp : 0 ≤ p) (hc : q*(1-p) ≤ s^2*p*(1-q)) :
    q-p ≤ (s-1)/(s+1) := by
  apply sub_nonneg.mp
  apply nonneg_of_mul_nonneg_left _ (multiplier_pos hs hp)
  rw [contrast_balance hs]
  exact add_nonneg (mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg _))
    (mul_nonneg (by linarith only [hs]) (sub_nonneg.mpr hc))

/-- At positive distortion both the reference event probability and its odds are forced at equality. -/
theorem binary_equality {s p q : ℝ} (hs : 1 < s) (hp : 0 ≤ p) (hc : q*(1-p) ≤ s^2*p*(1-q)) :
    q-p = (s-1)/(s+1) ↔ (s+1)*p = 1 ∧ q*(1-p) = s^2*p*(1-q) := by
  have h := contrast_balance hs.le p q
  have ha := sub_pos.mpr hs
  have hb : 0 < s+1 := by linarith only [hs]
  constructor
  · intro he
    rw [he,sub_self,zero_mul] at h
    obtain ⟨h1,h2⟩ := (add_eq_zero_iff_of_nonneg (mul_nonneg ha.le (sq_nonneg _))
      (mul_nonneg hb.le (sub_nonneg.mpr hc))).mp h.symm
    exact ⟨sub_eq_zero.mp (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp h1).resolve_left ha.ne')),
      (sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hb.ne')).symm⟩
  · rintro ⟨h1,h2⟩
    rw [h1,← h2,sub_self,sub_self,zero_pow (Nat.succ_ne_zero 1),mul_zero,mul_zero,add_zero] at h
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (multiplier_pos hs.le hp).ne')).symm

#print axioms contrast_balance
#print axioms binary_bound
#print axioms binary_equality

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells
