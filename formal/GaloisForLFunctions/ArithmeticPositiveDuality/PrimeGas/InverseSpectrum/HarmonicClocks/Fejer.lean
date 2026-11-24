import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Readings

/-! # Fejér energy of equally spaced split observations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- Expected squared clock polynomial, expressed recursively through its observed harmonics. -/
def fejerReading (v : MissingWave) (t : ℝ) : ℕ → ℝ
  | 0 => 0
  | d+1 => fejerReading v t d+1+2*(blockReading v t 1 d).re

theorem fejer_hasSum (v : MissingWave) (t : ℝ) (d : ℕ) :
    HasSum (fun n => occupationProbability v n*‖clockPolynomial d (splitPhase t n)‖^2) (fejerReading v t d) := by
  induction d with
  | zero => simp [fejerReading,clockPolynomial]
  | succ d ih =>
    have h := ((ih.add (occupationLaw_hasSum v)).add ((Complex.hasSum_re (blockReading_hasSum v t 1 d)).mul_left 2))
    apply h.congr_fun
    intro n
    simp only [clockPolynomial_step_sq d (splitPhase_norm t n),pow_one,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring

private theorem blockReading_re_bound {r : ℕ+} {δ : ℝ} {v : MissingWave} {t : ℝ}
    (ht : harmonicTest r δ v t) {d : ℕ} (hd : d < r.val) :
    (blockReading v t 1 d).re ≤ d*δ := by
  rw [blockReading,Complex.re_sum]
  calc
    _ ≤ ∑ _ ∈ Finset.range d, δ := Finset.sum_le_sum fun i hi =>
      (Complex.re_le_norm _).trans (ht (1+i) (by omega) (by have := Finset.mem_range.mp hi; omega))
    _ = _ := by simp

/-- Bounds on the first r−1 harmonics control the Fejér energy at every order through r. -/
theorem fejer_bound {r : ℕ+} {δ : ℝ} {v : MissingWave} {t : ℝ}
    (ht : harmonicTest r δ v t) (d : ℕ) (hd : d ≤ r.val) :
    fejerReading v t d ≤ d+(d:ℝ)*(d-1)*δ := by
  induction d with
  | zero => simp [fejerReading]
  | succ d ih =>
    have h := blockReading_re_bound ht (show d < r.val by omega)
    have hi := ih (show d ≤ r.val by omega)
    rw [fejerReading,Nat.cast_succ]
    linarith only [hi,h]

theorem harmonic_zero_iff (r : ℕ+) (v : MissingWave) (t : ℝ) :
    harmonicTest r 0 v t ↔ ∀ h : ℕ, 0 < h → h < r.val → harmonicReading v t h = 0 := by
  simp only [harmonicTest,norm_le_zero_iff]

/-- Exact cancellation makes the expected squared clock polynomial equal its order. -/
theorem fejer_exact {r : ℕ+} {v : MissingWave} {t : ℝ} (ht : harmonicTest r 0 v t)
    (d : ℕ) (hd : d ≤ r.val) : fejerReading v t d = d := by
  induction d with
  | zero => simp [fejerReading]
  | succ d ih =>
    have hb : blockReading v t 1 d = 0 := Finset.sum_eq_zero fun i hi =>
      (harmonic_zero_iff _ _ _).mp ht (1+i) (by omega) (by have := Finset.mem_range.mp hi; omega)
    rw [fejerReading,ih (by omega),hb,Complex.zero_re,mul_zero,add_zero,Nat.cast_succ]

def retentionCeiling (r : ℕ+) (δ : ℝ) : ℝ := δ+(1-δ)/(r.val:ℝ)

theorem retentionCeiling_mul_sq (r : ℕ+) (δ : ℝ) :
    (r.val:ℝ)^2*retentionCeiling r δ = r.val+(r.val:ℝ)*(r.val-1)*δ := by
  unfold retentionCeiling
  field_simp [show (r.val:ℝ) ≠ 0 by exact_mod_cast r.ne_zero]
  ring

theorem retentionCeiling_pos (r : ℕ+) {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) :
    0 < retentionCeiling r δ := by
  by_cases h : δ = 1
  · simp [retentionCeiling,h]
  · exact add_pos_of_nonneg_of_pos hδ (div_pos (sub_pos.mpr (lt_of_le_of_ne hδ' h))
      (Nat.cast_pos.mpr r.pos))

#print axioms fejer_hasSum
#print axioms fejer_bound
#print axioms harmonic_zero_iff
#print axioms fejer_exact
#print axioms retentionCeiling_mul_sq
#print axioms retentionCeiling_pos

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
