import GaloisForLFunctions.RHTower.WeilWorkQuantizationBilateralRough
import GaloisForLFunctions.RHTower.WeilWorkQuantizationPeriodicResidues
/-!
# Rational dilation versus unit translation

A reduced rational power has one dilation resonance; adding one removes
every resonance. The argument retains both positive and negative harmonics.
-/

open Complex Set Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RHTower.WeilSpectral
open TruncatedRadial AbelianTwist IntegerMassRigidity HamburgerStability
  PhaseLockRigidity GaloisForLFunctions.HTGeometry


/-- A rough integer can resonate only with the zero rational harmonic. -/
theorem quantization_rough_resonance_index {u v m n : ℕ}
    (hu : 2 ≤ u) (hv : 2 ≤ v) (huv : u.Coprime v) (hm : 1 ≤ m)
    (hum : ¬u ∣ m) (hvm : ¬v ∣ m) {j : ℤ}
    (hres : quantizationFrequencyResonates (2 * (j : ℝ) * Real.log ((u : ℝ) / v)) m n) :
    j = 0 := by
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hvR : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hnat {u v m n j : ℕ} (hu : 0 < u) (hv : 0 < v) (hm : 0 < m)
      (hcop : u.Coprime v) (hno : ¬u ∣ m)
      (hr : quantizationFrequencyResonates (2 * (j : ℝ) * Real.log ((u : ℝ) / v)) m n) : j = 0 := by
    by_contra hj
    have he := ((quantization_rational_resonance_iff hu hv hm).mp hr).2
    have hpow : u ^ j ∣ m := (hcop.pow j j).dvd_of_dvd_mul_right
      (he ▸ dvd_mul_left (u ^ j) n)
    have huj : u ∣ u ^ j := by
      simpa using (pow_dvd_pow u (show 1 ≤ j by omega))
    exact hno (huj.trans hpow)
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · have hk := hnat (by omega) (by omega) (by omega) huv hum hres
    simp [hk]
  · have he : 2 * ((-(k : ℤ) : ℤ) : ℝ) * Real.log ((u : ℝ) / v) =
        2 * (k : ℝ) * Real.log ((v : ℝ) / u) := by
      rw [Int.cast_neg, Int.cast_natCast, Real.log_div huR.ne' hvR.ne',
        Real.log_div hvR.ne' huR.ne']
      ring
    rw [he] at hres
    have hk := hnat (by omega) (by omega) (by omega) huv.symm hvm hres
    simp [hk]

/-- Translating a nonintegral rational power by one leaves every dilation resonance. -/
theorem quantization_rational_power_add_one_nonresonant {u v k n : ℕ}
    (hu : 2 ≤ u) (hv : 2 ≤ v) (huv : u.Coprime v) (hk : 1 ≤ k) (hn : 1 ≤ n) (j : ℤ) :
    Real.log n + (j : ℝ) * Real.log ((u : ℝ) / v) ≠
      Real.log (Real.exp ((k : ℝ) * Real.log ((u : ℝ) / v)) + 1) := by
  intro he
  have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
  have hvR : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let A : ℕ := u ^ k + v ^ k
  have hA : 1 ≤ A := by
    have hp : 0 < u ^ k := pow_pos (by omega) k
    dsimp only [A]
    omega
  have huPow : u ∣ u ^ k := by simpa using pow_dvd_pow u hk
  have hvPow : v ∣ v ^ k := by simpa using pow_dvd_pow v hk
  have huA : ¬u ∣ A := by
    intro hd
    have hvp : u ∣ v ^ k := (Nat.dvd_add_iff_right huPow).mpr hd
    have hone := Nat.eq_one_of_dvd_coprimes (huv.pow_right k) dvd_rfl hvp
    omega
  have hvA : ¬v ∣ A := by
    intro hd
    have hup : v ∣ u ^ k := (Nat.dvd_add_iff_left hvPow).mpr hd
    have hone := Nat.eq_one_of_dvd_coprimes (huv.symm.pow_right k) dvd_rfl hup
    omega
  have hscale : (v : ℝ) ^ k * (Real.exp ((k : ℝ) * Real.log ((u : ℝ) / v)) + 1) = A := by
    rw [Real.exp_nat_mul, Real.exp_log (div_pos huR hvR), div_pow]
    dsimp only [A]
    push_cast
    field_simp
  have hlog := congrArg Real.log hscale
  rw [Real.log_mul (pow_pos hvR k).ne' (by positivity), Real.log_pow] at hlog
  have hr : quantizationFrequencyResonates (2 * (j : ℝ) * Real.log ((u : ℝ) / v)) A (n * v ^ k) := by
    refine ⟨Nat.mul_pos (by omega) (pow_pos (by omega) k), ?_⟩
    rw [Nat.cast_mul, Nat.cast_pow, Real.log_mul hnR.ne' (pow_pos hvR k).ne', Real.log_pow]
    linarith
  have hj := quantization_rough_resonance_index hu hv huv hA huA hvA hr
  rw [hj] at hr
  have hnm : n * v ^ k = A := quantizationFrequencyResonates_unique hr
    ⟨hA, by simp⟩
  apply hvA
  rw [← hnm]
  exact hvPow.trans (dvd_mul_left (v ^ k) n)



/-- Translation isolates negative as well as positive rational harmonics. -/
theorem quantization_rational_zpower_add_one_nonresonant {u v n : ℕ}
    (hu : 2 ≤ u) (hv : 2 ≤ v) (huv : u.Coprime v) (hn : 1 ≤ n)
    {k : ℤ} (hk : k ≠ 0) (j : ℤ) :
    Real.log n + (j : ℝ) * Real.log ((u : ℝ) / v) ≠
      Real.log (Real.exp ((k : ℝ) * Real.log ((u : ℝ) / v)) + 1) := by
  obtain ⟨q, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · exact quantization_rational_power_add_one_nonresonant hu hv huv (by omega) hn j
  · have huR : (0 : ℝ) < u := by exact_mod_cast (show 0 < u by omega)
    have hvR : (0 : ℝ) < v := by exact_mod_cast (show 0 < v by omega)
    have hl : Real.log ((v : ℝ) / u) = -Real.log ((u : ℝ) / v) := by
      rw [Real.log_div huR.ne' hvR.ne', Real.log_div hvR.ne' huR.ne']
      ring
    have h := quantization_rational_power_add_one_nonresonant hv hu huv.symm
      (by omega : 1 ≤ q) hn (-j)
    simpa only [hl, Int.cast_neg, Int.cast_natCast, neg_mul_neg, mul_neg, neg_mul, neg_neg] using h

/-- A rational power has exactly one active harmonic in the complete real-height sum. -/
theorem quantization_rational_real_sum_power {lam : ℕ → ℝ} {u v : ℕ}
    (hu : 2 ≤ u) (hv : 2 ≤ v) (huv : u.Coprime v) (p : ℤ → ℂ) (k : ℤ) :
    quantizationRealFrequencySum lam p (fun j => 2 * (j : ℝ) * Real.log ((u : ℝ) / v))
      (Real.exp ((k : ℝ) * Real.log ((u : ℝ) / v))) =
      (Real.exp ((k : ℝ) * Real.log ((u : ℝ) / v) / 2) : ℂ) * p k := by
  classical
  have hu1 : ¬u ∣ 1 := by intro hd; have := Nat.le_of_dvd zero_lt_one hd; omega
  have hv1 : ¬v ∣ 1 := by intro hd; have := Nat.le_of_dvd zero_lt_one hd; omega
  have he (j : ℤ) : 2 * (j : ℝ) * Real.log ((u : ℝ) / v) -
      2 * ((k : ℝ) * Real.log ((u : ℝ) / v)) =
      2 * ((j - k : ℤ) : ℝ) * Real.log ((u : ℝ) / v) := by push_cast; ring
  unfold quantizationRealFrequencySum
  rw [Real.log_exp]
  congr 1
  rw [tsum_eq_single k]
  · rw [he, quantization_bilateral_rational_rough_residue hu hv huv le_rfl hu1 hv1]
    simp [dirichletExp_one (lamLog_zero lam) (lamLog_one lam)]
  · intro j hj
    rw [he, quantization_bilateral_rational_rough_residue hu hv huv le_rfl hu1 hv1]
    simp [sub_eq_zero, hj]

/-- A translated nonzero rational power has no active harmonic. -/
theorem quantization_rational_real_sum_power_add_one {lam : ℕ → ℝ} {u v : ℕ}
    (hu : 2 ≤ u) (hv : 2 ≤ v) (huv : u.Coprime v) (p : ℤ → ℂ)
    {k : ℤ} (hk : k ≠ 0) :
    quantizationRealFrequencySum lam p (fun j => 2 * (j : ℝ) * Real.log ((u : ℝ) / v))
      (Real.exp ((k : ℝ) * Real.log ((u : ℝ) / v)) + 1) = 0 := by
  have hzero (j : ℤ) : quantizationFrequencyResidue lam
      (2 * (j : ℝ) * Real.log ((u : ℝ) / v) -
        2 * Real.log (Real.exp ((k : ℝ) * Real.log ((u : ℝ) / v)) + 1)) 1 = 0 := by
    have hn : ¬∃ n : ℕ, quantizationFrequencyResonates
        (2 * (j : ℝ) * Real.log ((u : ℝ) / v) -
          2 * Real.log (Real.exp ((k : ℝ) * Real.log ((u : ℝ) / v)) + 1)) 1 n := by
      rintro ⟨n, hn, he⟩
      rw [Nat.cast_one, Real.log_one] at he
      apply quantization_rational_zpower_add_one_nonresonant hu hv huv hn hk j
      linarith
    simp only [quantizationFrequencyResidue, dif_neg hn]
  simp only [quantizationRealFrequencySum, hzero, mul_zero, tsum_zero]

end RHTower.WeilSpectral
