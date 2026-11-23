import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.CoherentProbes

/-! # Recovering a complex amplitude with five pole readings -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- The unperturbed reading and the four signed real and imaginary reference readings. -/
structure PoleScan where
  base : ℝ
  plusReal : ℝ
  minusReal : ℝ
  plusImag : ℝ
  minusImag : ℝ

def poleScan (v : MissingWave) (k : ℕ) : PoleScan :=
  ⟨poleReading v,poleReading (addNative v k 1),poleReading (addNative v k (-1)),
    poleReading (addNative v k Complex.I),poleReading (addNative v k (-Complex.I))⟩

private def readingRatio (a b y : ℝ) := (b-y)/(y-a)

private theorem readingRatio_eq (v : MissingWave) (k : ℕ) (c : ℂ) (hk : poleReading v ≠ occupationWeight k) :
    readingRatio (occupationWeight k) (poleReading v) (poleReading (addNative v k c)) =
      probeIncrement (v.val (number k)) c/‖v.val‖^2 := by
  have h := poleReading_displacement v k c
  rw [addNative_norm_sq] at h
  apply (div_eq_div_iff (sub_ne_zero.mpr ((probe_blind_iff v k c).not.mpr hk))
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v)))).mpr
  linear_combination -h

/-- The complex coordinate reconstructed at a nonblind native level. -/
def PoleScan.coordinate (s : PoleScan) (a : ℝ) : ℂ :=
  let R := readingRatio a s.base
  let d := 2*(R s.plusReal+R s.minusReal)
  ⟨(R s.plusReal-R s.minusReal)/d,(R s.plusImag-R s.minusImag)/d⟩

private theorem ratios_eval (z : ℂ) (M : ℝ) (hM : M ≠ 0) :
    let r := fun c => probeIncrement z c/M
    let d := 2*(r 1+r (-1))
    (((r 1-r (-1))/d : ℝ) = z.re) ∧ (((r Complex.I-r (-Complex.I))/d : ℝ) = z.im) := by
  dsimp only
  have hd : 2*(probeIncrement z 1/M+probeIncrement z (-1)/M) = 4/M := by
    simp [probeIncrement]
    <;> ring
  rw [hd]
  constructor <;> apply (div_eq_iff (div_ne_zero (by norm_num : (4:ℝ)≠0) hM)).mpr
  · simp [probeIncrement]
    <;> ring
  · simp [probeIncrement]
    <;> ring

theorem poleScan_coordinate (v : MissingWave) (k : ℕ) (hk : poleReading v ≠ occupationWeight k) :
    (poleScan v k).coordinate (occupationWeight k) = v.val (number k) := by
  have h := ratios_eval (v.val (number k)) (‖v.val‖^2) (pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v)))
  apply Complex.ext
  · simpa only [PoleScan.coordinate,poleScan,readingRatio_eq v k _ hk] using h.1
  · simpa only [PoleScan.coordinate,poleScan,readingRatio_eq v k _ hk] using h.2

/-- A reference leaves the pole reading fixed exactly when the chosen level is blind or the reference preserves the coordinate intensity. -/
theorem poleReading_fixed_iff (v : MissingWave) (k : ℕ) (c : ℂ) :
    poleReading (addNative v k c) = poleReading v ↔
      poleReading v = occupationWeight k ∨ probeIncrement (v.val (number k)) c = 0 := by
  have h := poleReading_displacement v k c
  rw [addNative_norm_sq,mul_add] at h
  constructor
  · intro hf
    rw [hf] at h
    have h0 : (poleReading v-occupationWeight k)*probeIncrement (v.val (number k)) c = 0 := by linarith only [h]
    exact (mul_eq_zero.mp h0).imp_left sub_eq_zero.mp
  · rintro (hb|hi)
    · exact ((probe_blind_iff v k c).mpr hb).trans hb.symm
    · rw [hi,mul_zero,add_zero] at h
      exact sub_left_inj.mp (mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v))) h)

/-- The two real reference readings also recover the total mass at each nonblind level. -/
def PoleScan.mass (s : PoleScan) (a : ℝ) :=
  2/(readingRatio a s.base s.plusReal+readingRatio a s.base s.minusReal)

theorem poleScan_mass (v : MissingWave) (k : ℕ) (hk : poleReading v ≠ occupationWeight k) :
    (poleScan v k).mass (occupationWeight k) = ‖v.val‖^2 := by
  have hM := pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v))
  have hi : probeIncrement (v.val (number k)) 1+probeIncrement (v.val (number k)) (-1) = 2 := by
    simp [probeIncrement]
    <;> ring
  simp only [PoleScan.mass,poleScan,readingRatio_eq v k _ hk]
  rw [← add_div,hi]
  field_simp

#print axioms poleScan_mass
#print axioms poleScan_coordinate
#print axioms poleReading_fixed_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
