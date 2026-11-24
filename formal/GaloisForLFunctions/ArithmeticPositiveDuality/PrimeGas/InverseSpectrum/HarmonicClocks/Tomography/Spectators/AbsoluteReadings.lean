import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Spectators.Equilibrium

/-! # Identifying the energy and degeneracy of a finite spectator -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open _root_.RHTower.PrimeCoShift

/-- The absolute loss in a clock event relative to the gas without a spectator. -/
def spectatorExcess (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+)
    (q : Nat.Primes) (g : ℕ) : ℝ :=
  gibbsClockReturn χ β p D / spectatorReturn β p D q g - 1

theorem spectatorExcess_eq (χ : ℕ+ → Circle) (β : TraceTemperature) {p q : Nat.Primes}
    (hpq : p ≠ q) (D : ℕ+) (g : ℕ) :
    spectatorExcess χ β p D q g = g * thermalWeight β (primePNat q) := by
  rw [spectatorExcess,spectatorReturn_eq χ β hpq D,div_div_eq_mul_div]
  rw [mul_div_cancel_left₀ _ (clockReturn_positive χ β p D).ne']
  exact add_sub_cancel_left 1 _

/-- At two temperatures the measured excess determines the excited energy. -/
theorem spectator_read_energy (χ : ℕ+ → Circle) {β γ : TraceTemperature} (hβγ : β < γ)
    {p q : Nat.Primes} (hpq : p ≠ q) (D : ℕ+) (g : ℕ+) :
    Real.log (spectatorExcess χ β p D q g.val / spectatorExcess χ γ p D q g.val) /
      (γ.val - β.val) = energy (primePNat q) := by
  rw [spectatorExcess_eq χ β hpq,spectatorExcess_eq χ γ hpq]
  rw [mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr g.ne_zero)]
  rw [thermalWeight,thermalWeight,← Real.exp_sub,Real.log_exp]
  apply (div_eq_iff (sub_pos.mpr hβγ).ne').mpr
  ring

/-- Once the energy is calibrated, an absolute event counts the excited states. -/
theorem spectator_read_degeneracy (χ : ℕ+ → Circle) (β : TraceTemperature) {p q : Nat.Primes}
    (hpq : p ≠ q) (D : ℕ+) (g : ℕ) :
    spectatorExcess χ β p D q g * Real.exp (β.val * energy (primePNat q)) = g := by
  rw [spectatorExcess_eq χ β hpq,thermalWeight,mul_assoc,← Real.exp_add]
  simp only [neg_mul,neg_add_cancel,Real.exp_zero,mul_one]

/-- One absolute event detects the presence of any excited spectator state. -/
theorem spectatorReturn_eq_base_iff (χ : ℕ+ → Circle) (β : TraceTemperature) {p q : Nat.Primes}
    (hpq : p ≠ q) (D : ℕ+) (g : ℕ) :
    spectatorReturn β p D q g = gibbsClockReturn χ β p D ↔ g = 0 := by
  constructor
  · intro h
    have he := spectatorExcess_eq χ β hpq D g
    rw [spectatorExcess,h,div_self (clockReturn_positive χ β p D).ne',sub_self] at he
    exact Nat.cast_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right (thermalWeight_pos β _).ne')
  · rintro rfl
    simp only [spectatorReturn_eq χ β hpq D,spectatorWeight,Nat.cast_zero,zero_mul,add_zero,div_one]

/-- The pair of absolute readings identifies an unknown foreign prime and positive degeneracy. -/
theorem spectator_pair_identifies (χ : ℕ+ → Circle) {β γ : TraceTemperature} (hβγ : β < γ)
    {p q r : Nat.Primes} (hpq : p ≠ q) (hpr : p ≠ r) (D : ℕ+) (g h : ℕ+) :
    (spectatorReturn β p D q g.val,spectatorReturn γ p D q g.val) =
      (spectatorReturn β p D r h.val,spectatorReturn γ p D r h.val) ↔ q = r ∧ g = h := by
  constructor
  · intro he
    have hb : spectatorExcess χ β p D q g.val = spectatorExcess χ β p D r h.val := by
      unfold spectatorExcess
      rw [show spectatorReturn β p D q g.val = _ from congrArg Prod.fst he]
    have hc : spectatorExcess χ γ p D q g.val = spectatorExcess χ γ p D r h.val := by
      unfold spectatorExcess
      rw [show spectatorReturn γ p D q g.val = _ from congrArg Prod.snd he]
    have hE := spectator_read_energy χ hβγ hpq D g
    rw [hb,hc,spectator_read_energy χ hβγ hpr D h] at hE
    have hq : q = r := by
      apply Subtype.ext
      apply Nat.cast_injective (R := ℝ)
      have hl := congrArg Real.exp hE.symm
      change Real.exp (Real.log (q.val:ℝ)) = Real.exp (Real.log (r.val:ℝ)) at hl
      rwa [Real.exp_log (Nat.cast_pos.mpr q.property.pos),Real.exp_log (Nat.cast_pos.mpr r.property.pos)] at hl
    subst r
    refine ⟨rfl,PNat.coe_injective ?_⟩
    have hg := spectator_read_degeneracy χ β hpq D g.val
    rw [hb,spectator_read_degeneracy χ β hpq D h.val] at hg
    exact_mod_cast hg.symm
  · rintro ⟨rfl,rfl⟩
    rfl

#print axioms spectatorExcess_eq
#print axioms spectator_read_energy
#print axioms spectator_read_degeneracy
#print axioms spectatorReturn_eq_base_iff
#print axioms spectator_pair_identifies

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
