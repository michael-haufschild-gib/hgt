import GaloisForLFunctions.RHTower.WeilWorkQuantizationRationalResonance
import GaloisForLFunctions.RHTower.WeilProducerZetaQuotientBohrRecurrence

/-!
# Prime agreement forced by bilateral rational canonical phases

Every nonzero rational resonance needs a numerator or denominator divisor.
The full actual phase equations therefore fix all rough coefficients and every
prime beyond the numerator. No finite Toeplitz block is assumed invertible.
-/

open Complex
noncomputable section
namespace RHTower.WeilSpectral
open IntegerMassRigidity GaloisForLFunctions.HTGeometry

theorem quantization_bilateral_rational_rough_residue {lam : ℕ → ℝ} {u v m : ℕ}
    (hu : 2 ≤ u) (hv : 2 ≤ v) (huv : u.Coprime v) (hm : 1 ≤ m)
    (hum : ¬u ∣ m) (hvm : ¬v ∣ m) (k : ℤ) :
    quantizationFrequencyResidue lam (2 * (k : ℝ) * Real.log ((u : ℝ) / v)) m =
      if k = 0 then dirichletExp (lamLog lam) m else 0 := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hvR : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hval (b : ℕ) (hb : 2 ≤ b) (hbm : ¬b ∣ m) : padicValNat b m = 0 := by
    by_contra h
    have hd := (Nat.pow_dvd_iff_le_padicValNat (by omega : b ≠ 1)
      (by omega : m ≠ 0)).mpr (show 1 ≤ padicValNat b m by omega)
    exact hbm (by simpa using hd)
  obtain ⟨j, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simp only [Int.cast_natCast]
    rw [quantization_rational_residue hu (by omega) huv hm, hval u hu hum]
    by_cases hj : j = 0
    · simp [hj]
    · simp [hj]
  · have he : 2 * ((-(j : ℤ) : ℤ) : ℝ) * Real.log ((u : ℝ) / v) =
        2 * (j : ℝ) * Real.log ((v : ℝ) / u) := by
      rw [Int.cast_neg, Int.cast_natCast, Real.log_div huR.ne' hvR.ne',
        Real.log_div hvR.ne' huR.ne']
      ring
    rw [he, quantization_rational_residue hv (by omega) huv.symm hm, hval v hv hvm]
    by_cases hj : j = 0
    · simp [hj]
    · simp [hj]

theorem quantization_bilateral_rational_rough_coeff {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {u v : ℕ} (hu : 2 ≤ u) (hv : 2 ≤ v)
    (huv : u.Coprime v) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log ((u : ℝ) / v)| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log ((u : ℝ) / v) * x : ℝ) : ℂ) * I)) :
    p 0 ≠ 0 ∧ ∀ m : ℕ, 1 ≤ m → ¬u ∣ m → ¬v ∣ m →
      dirichletExp (lamLog lam) m = 1 := by
  have hsum (m : ℕ) (hm : 1 ≤ m) (hum : ¬u ∣ m) (hvm : ¬v ∣ m) :
      (∑' k : ℤ, p k * quantizationFrequencyResidue lam
        (2 * (k : ℝ) * Real.log ((u : ℝ) / v)) m) =
        p 0 * dirichletExp (lamLog lam) m := by
    rw [tsum_eq_single 0]
    · rw [quantization_bilateral_rational_rough_residue hu hv huv hm hum hvm]
      simp
    · intro k hk
      rw [quantization_bilateral_rational_rough_residue hu hv huv hm hum hvm, if_neg hk,
        mul_zero]
  have hu1 : ¬u ∣ 1 := by simpa using (show u ≠ 1 by omega)
  have hv1 : ¬v ∣ 1 := by simpa using (show v ≠ 1 by omega)
  obtain ⟨hne, hrow⟩ := quantization_phase_resonance_constant hW hp hphase
  rw [hsum 1 (by omega) hu1 hv1, dirichletExp_one (lamLog_zero lam) (lamLog_one lam),
    mul_one] at hne hrow
  refine ⟨hne, fun m hm hum hvm => ?_⟩
  have he := hrow m hm
  rw [hsum m hm hum hvm] at he
  exact (mul_left_cancel₀ hne (he.trans (mul_one _).symm))

theorem quantization_bilateral_rational_prime_agreement {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {u v : ℕ} (hv : 2 ≤ v) (hvu : v < u)
    (huv : u.Coprime v) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * Real.exp (|2 * (k : ℝ) * Real.log ((u : ℝ) / v)| / 2))
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log ((u : ℝ) / v) * x : ℝ) : ℂ) * I)) :
    ∀ q : ℕ, q.Prime → u < q → lam q = ArithmeticFunction.vonMangoldt q := by
  intro q hq huq
  have hu : 2 ≤ u := by omega
  have hnd (b : ℕ) (hb : 2 ≤ b) (hbq : b < q) : ¬b ∣ q := by
    intro hd
    rcases hq.eq_one_or_self_of_dvd b hd with h | h <;> omega
  have ha := (quantization_bilateral_rational_rough_coeff hW hu hv huv hp hphase).2
    q hq.one_le (hnd u hu huq) (hnd v hv (by omega))
  rw [RHTower.dirichletExp_prime (lamLog_zero lam) (lamLog_one lam) hq,
    lamLog, if_pos hq.two_le] at ha
  have hl : (Real.log q : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast hq.one_lt)).ne'
  have he := (div_eq_iff hl).mp ha
  rw [one_mul] at he
  rw [ArithmeticFunction.vonMangoldt_apply_prime hq]
  exact_mod_cast he

end RHTower.WeilSpectral
