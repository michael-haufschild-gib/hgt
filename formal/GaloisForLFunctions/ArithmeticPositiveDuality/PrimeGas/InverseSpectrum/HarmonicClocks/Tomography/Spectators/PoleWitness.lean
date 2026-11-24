import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Spectators.Divisor
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Tomography.Calibration.OneReading

/-! # A positive ensemble with a clock-return pole off the isometry line -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open HTGeometry ZeroForcingCalculus
open _root_.RHTower.PrimeCoShift

/-- The first upper-half-plane zero of a positive-degeneracy spectator. -/
def spectatorRoot (q : Nat.Primes) (g : ℕ+) : ℂ :=
  ((Real.log (g.val:ℝ):ℂ) + (Real.pi:ℂ)*Complex.I) / (energy (primePNat q):ℂ)

theorem spectatorRoot_re (q : Nat.Primes) (g : ℕ+) :
    (spectatorRoot q g).re = Real.log (g.val:ℝ) / energy (primePNat q) := by
  simp [spectatorRoot,Complex.div_ofReal_re]

theorem spectatorRoot_zero (q : Nat.Primes) (g : ℕ+) :
    spectatorFactor q g.val (spectatorRoot q g) = 0 := by
  have hL := Complex.ofReal_ne_zero.mpr (prime_energy_pos q).ne'
  have hg : (g.val:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr g.ne_zero
  rw [spectatorFactor,heat,spectatorRoot,neg_mul,div_mul_cancel₀ _ hL,Complex.exp_neg,Complex.exp_add,
    ← Complex.ofReal_exp,Real.exp_log (Nat.cast_pos.mpr g.pos),Complex.exp_pi_mul_I,Complex.ofReal_natCast]
  field_simp

/-- At a finite-factor zero in the strip, the base partition contributes a nonnegative
order, so the simple spectator zero always produces a pole. -/
theorem spectator_zero_forces_pole (p : Nat.Primes) (D : ℕ+) (q : Nat.Primes) (g : ℕ)
    (z : OpenStrip) (hz : spectatorFactor q g z.val = 0) :
    meromorphicOrderAt (continuedSpectatorReturn p D q g) z.val < 0 := by
  have h1 : z.val ≠ 1 := fun he => z.property.2.ne (by rw [he]; rfl)
  have ha := (HTGeometry.analyticAt_riemannZeta h1).meromorphicOrderAt_nonneg
  rw [continuedSpectatorReturn_order p D q g z.property.1,if_pos hz]
  lift meromorphicOrderAt riemannZeta z.val to ℤ using meromorphicOrderAt_riemannZeta_ne_top z.val with k
  have hk : 0 ≤ k := by exact_mod_cast ha
  exact_mod_cast (show -k - 1 < 0 by omega)

private theorem five_two_left :
    0 < (spectatorRoot ⟨5,Nat.prime_five⟩ 2).re ∧ (spectatorRoot ⟨5,Nat.prime_five⟩ 2).re < 1/2 := by
  rw [spectatorRoot_re]
  change 0 < Real.log 2 / Real.log 5 ∧ Real.log 2 / Real.log 5 < 1/2
  have h5 : 0 < Real.log 5 := Real.log_pos (by norm_num)
  refine ⟨div_pos (Real.log_pos (by norm_num)) h5,(div_lt_iff₀ h5).mpr ?_⟩
  have h := Real.log_lt_log (show (0:ℝ)<2*2 by norm_num) (show (2:ℝ)*2<5 by norm_num)
  rw [Real.log_mul (by norm_num) (by norm_num)] at h
  linarith only [h]

/-- The twofold level at energy log 5 creates a pole strictly to the left of 1/2 for
every block of the prime-two clock. Every real return is a probability in (0,1). -/
theorem five_two_positive_off_line (D : ℕ+) :
    let p : Nat.Primes := ⟨2,Nat.prime_two⟩
    let q : Nat.Primes := ⟨5,Nat.prime_five⟩
    let z := spectatorRoot q 2
    (∀ β : TraceTemperature, spectatorReturn β p D q 2 ∈ Set.Ioo (0:ℝ) 1) ∧
      0 < z.re ∧ z.re < 1/2 ∧ meromorphicOrderAt (continuedSpectatorReturn p D q 2) z < 0 := by
  dsimp only
  let p : Nat.Primes := ⟨2,Nat.prime_two⟩
  let q : Nat.Primes := ⟨5,Nat.prime_five⟩
  have hpq : p ≠ q := fun h => (by norm_num : (2:ℕ) ≠ 5) (congrArg Subtype.val h)
  obtain ⟨hlo,hhi⟩ := five_two_left
  refine ⟨fun β => ?_,hlo,hhi,spectator_zero_forces_pole p D q 2
    ⟨spectatorRoot q 2,hlo,hhi.trans (by norm_num)⟩ (spectatorRoot_zero q 2)⟩
  let χ := fun _ : ℕ+ => (1:Circle)
  rw [spectatorReturn_eq χ β hpq D]
  have hb := clockReturn_mem_unit χ β p D
  have hw : (1:ℝ) ≤ spectatorWeight β q 2 :=
    le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) (thermalWeight_pos β _).le)
  exact ⟨div_pos hb.1 (spectatorWeight_pos β q 2),
    (div_lt_iff₀ (spectatorWeight_pos β q 2)).mpr (by rw [one_mul]; exact hb.2.trans_le hw)⟩

#print axioms spectatorRoot_re
#print axioms spectatorRoot_zero
#print axioms spectator_zero_forces_pole
#print axioms five_two_positive_off_line

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
