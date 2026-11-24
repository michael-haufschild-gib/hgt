import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.OneReading

/-! # Self-calibration of the prime species, block size and temperature -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set
open _root_.RHTower.PrimeCoShift

/-- Return probabilities at a clock time and at half that time. -/
def nestedReturns (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) : ℝ × ℝ :=
  (gibbsClockReturn χ β p D,gibbsClockReturn χ β p (D+D))

/-- Doubling the block exponent separates off its Boltzmann factor. -/
theorem nestedReturns_ratio (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) :
    (nestedReturns χ β p D).1 / (nestedReturns χ β p D).2 = 1 + gibbsBlockRatio β p D := by
  have he : gibbsBlockRatio β p (D+D) = (gibbsBlockRatio β p D)^2 := by
    simp only [gibbsBlockRatio,PNat.add_coe,Nat.cast_add,sq,← Real.exp_add]
    congr 1
    ring
  have h₁ := (sub_pos.mpr (clockRatio_lt_one β p D)).ne'
  have h₂ := (sub_pos.mpr (clockRatio_lt_one β p (D+D))).ne'
  rw [he] at h₂
  change gibbsClockReturn χ β p D / gibbsClockReturn χ β p (D+D) = _
  rw [gibbsClockReturn_eq,gibbsClockReturn_eq,he]
  field_simp [h₁,h₂,(gasPartition_pos β).ne']
  ring

theorem nestedReturns_partition (χ : ℕ+ → Circle) (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) :
    ((nestedReturns χ β p D).1 * (2 - (nestedReturns χ β p D).1 / (nestedReturns χ β p D).2))⁻¹ =
      (riemannZeta β.val).re := by
  rw [nestedReturns_ratio]
  change (gibbsClockReturn χ β p D * _)⁻¹ = _
  rw [gibbsClockReturn_eq,show 2 - (1 + gibbsBlockRatio β p D) = 1 - gibbsBlockRatio β p D by ring]
  field_simp [(sub_pos.mpr (clockRatio_lt_one β p D)).ne',(gasPartition_pos β).ne']

private theorem ratio_as_weight (β : TraceTemperature) (p : Nat.Primes) (D : ℕ+) :
    gibbsBlockRatio β p D = thermalWeight β (primeRayLabel p D.val) := by
  rw [thermalWeight,energy_primeRayLabel,gibbsBlockRatio]

private theorem different_blocks {a b : ℕ+} (h : a < b) (β : TraceTemperature) :
    thermalWeight β b < thermalWeight β a := by
  apply Real.exp_lt_exp.mpr
  have he : energy a < energy b := Real.log_lt_log (Nat.cast_pos.mpr a.pos)
    (by exact_mod_cast (show a.val < b.val from h))
  exact mul_lt_mul_of_neg_left he (neg_neg_of_pos (zero_lt_one.trans β.property))

private theorem block_identity {p q : Nat.Primes} {D E : ℕ+}
    (h : primeRayLabel p D.val = primeRayLabel q E.val) : p = q ∧ D = E := by
  have he := congrArg PNat.val h
  change p.val^D.val = q.val^E.val at he
  have hd := dvd_pow_self p.val D.ne_zero
  rw [he] at hd
  have hp : p = q := Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.property q.property).mp
    (p.property.dvd_of_dvd_pow hd))
  subst q
  exact ⟨rfl,PNat.coe_injective (Nat.pow_right_injective p.property.two_le he)⟩

/-- The nested readings identify all three unknowns, with arbitrary phases of both preparations. -/
theorem nestedReturns_identify (χ ψ : ℕ+ → Circle) (β γ : TraceTemperature) (p q : Nat.Primes) (D E : ℕ+) :
    nestedReturns χ β p D = nestedReturns ψ γ q E ↔ β = γ ∧ p = q ∧ D = E := by
  constructor
  · intro h
    have hz := congrArg (fun u : ℝ × ℝ => (u.1*(2-u.1/u.2))⁻¹) h
    change ((nestedReturns χ β p D).1*(2-(nestedReturns χ β p D).1/(nestedReturns χ β p D).2))⁻¹ = _ at hz
    rw [nestedReturns_partition] at hz
    have hb := gasPartition_strictAnti.injective (hz.trans (nestedReturns_partition ψ γ q E))
    subst γ
    have hr := congrArg (fun u : ℝ × ℝ => u.1/u.2) h
    change (nestedReturns χ β p D).1/(nestedReturns χ β p D).2 =
      (nestedReturns ψ β q E).1/(nestedReturns ψ β q E).2 at hr
    rw [nestedReturns_ratio,nestedReturns_ratio] at hr
    have hw := add_left_cancel hr
    rw [ratio_as_weight,ratio_as_weight] at hw
    have he : primeRayLabel p D.val = primeRayLabel q E.val := by
      rcases lt_trichotomy (primeRayLabel p D.val) (primeRayLabel q E.val) with ht | ht | ht
      · exact False.elim ((different_blocks ht β).ne hw.symm)
      · exact ht
      · exact False.elim ((different_blocks ht β).ne hw)
    exact ⟨rfl,block_identity he⟩
  · rintro ⟨rfl,rfl,rfl⟩
    simp only [nestedReturns,gibbsClockReturn_eq]

/-- Larger blocks require strictly larger inverse temperatures for the same scalar return. -/
theorem sameReturn_orders_temperatures (χ ψ : ℕ+ → Circle) (p q : Nat.Primes) (D E : ℕ+)
    (h : primeRayLabel p D.val < primeRayLabel q E.val) (u : Ioo (0:ℝ) 1) :
    (clockCalibration χ p D).symm u < (clockCalibration ψ q E).symm u := by
  let β := (clockCalibration χ p D).symm u
  let γ := (clockCalibration ψ q E).symm u
  have ha : gibbsClockReturn χ β p D = u.val := congrArg Subtype.val ((clockCalibration χ p D).apply_symm_apply u)
  have hb : gibbsClockReturn ψ γ q E = u.val := congrArg Subtype.val ((clockCalibration ψ q E).apply_symm_apply u)
  have hr : gibbsBlockRatio β q E < gibbsBlockRatio β p D := by
    rw [ratio_as_weight,ratio_as_weight]
    exact different_blocks h β
  have ht : gibbsClockReturn ψ β q E < gibbsClockReturn χ β p D := by
    rw [gibbsClockReturn_eq,gibbsClockReturn_eq]
    apply div_lt_div_of_pos_right _ (gasPartition_pos β)
    exact (inv_lt_inv₀ (sub_pos.mpr (clockRatio_lt_one β q E)) (sub_pos.mpr (clockRatio_lt_one β p D))).mpr
      (sub_lt_sub_left hr 1)
  exact (clockReturn_strictMono ψ q E).lt_iff_lt.mp (ht.trans_eq (ha.trans hb.symm))

#print axioms nestedReturns_ratio
#print axioms nestedReturns_partition
#print axioms nestedReturns_identify
#print axioms sameReturn_orders_temperatures

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
