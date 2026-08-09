import GaloisForLFunctions.RHTower.RankOnePolarizedExchangeCurvature

/-!
# Modular gain, purity line, and Hermitian transgression

The power character `n ↦ n ^ θ` is the modular gain of weight `θ`.  It is trivial exactly at
`θ = 0`, so the one-sided polarized exchange transport of that gain is composition coherent exactly
at zero modular weight, and already the single identity `T 2 * T 2 = T 4` detects this.

Inserting a spectral parameter through `θ = 2 Re s - w` gives a family that depends only on the real
part of the parameter and is coherent exactly on the purity line `Re s = w / 2`.  For `w = 1` the
gain is the Deninger half-density mate gain, so the polarized transport is the existing one-sided
framed transport.

For a complex character the Hermitian torsion `τ = |λ| ^ 2` is a real character, its anomaly
`a = 1 - τ` obeys the crossed-cocycle law, the exchange curvature of `τ` is the affine transgression
of that anomaly, and reciprocal flatness of `λ` is exactly vanishing of the anomaly.
-/

namespace RHTower

noncomputable section

open Matrix

/-! ## The modular gain character -/

/-- The modular gain of weight `θ`: the power character `n ↦ n ^ θ`. -/
def modularGain (θ : ℝ) : ℕ+ →* ℝˣ where
  toFun n := Units.mk0 (((n : ℕ) : ℝ) ^ θ)
    (Real.rpow_pos_of_pos (by exact_mod_cast n.pos) θ).ne'
  map_one' := by
    refine Units.ext ?_
    simp
  map_mul' m n := by
    refine Units.ext ?_
    have hm : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [Units.val_mk0, Units.val_mul, PNat.mul_coe, Nat.cast_mul]
    exact Real.mul_rpow hm hn

@[simp] theorem modularGain_apply (θ : ℝ) (n : ℕ+) :
    ((modularGain θ n : ℝˣ) : ℝ) = ((n : ℕ) : ℝ) ^ θ := rfl

/-- The modular gain is trivial at degree two exactly at zero weight. -/
theorem modularGain_two_eq_one_iff (θ : ℝ) : modularGain θ 2 = 1 ↔ θ = 0 := by
  constructor
  · intro h
    have hval : ((2 : ℕ) : ℝ) ^ θ = 1 := by
      have := congrArg (fun u : ℝˣ => (u : ℝ)) h
      simpa using this
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < ((2 : ℕ) : ℝ))] at hval
    have hzero := (Real.exp_eq_one_iff _).1 hval
    have hlog : Real.log ((2 : ℕ) : ℝ) ≠ 0 := by
      have : (1 : ℝ) < ((2 : ℕ) : ℝ) := by norm_num
      exact (Real.log_pos this).ne'
    rcases mul_eq_zero.1 hzero with h' | h'
    · exact absurd h' hlog
    · exact h'
  · rintro rfl
    refine Units.ext ?_
    simp

/-- **The modular gain is trivial exactly at zero weight.** -/
theorem modularGain_eq_one_iff (θ : ℝ) : modularGain θ = 1 ↔ θ = 0 := by
  constructor
  · intro h
    refine (modularGain_two_eq_one_iff θ).1 ?_
    rw [h]
    rfl
  · rintro rfl
    ext n
    simp

/-! ## The zero-weight horizon -/

/-- **Composition coherence of the polarized modular family happens exactly at zero weight.** -/
theorem exchangeTransport_modularGain_mul_iff (θ : ℝ) :
    (∀ m n : ℕ+, exchangeTransport (modularGain θ) m * exchangeTransport (modularGain θ) n =
        exchangeTransport (modularGain θ) (m * n)) ↔ θ = 0 := by
  rw [exchangeTransport_mul_iff, modularGain_eq_one_iff]

/-- **The single square identity at degree two already detects the horizon.** -/
theorem exchangeTransport_modularGain_two_sq_iff (θ : ℝ) :
    exchangeTransport (modularGain θ) 2 * exchangeTransport (modularGain θ) 2 =
        exchangeTransport (modularGain θ) 4 ↔ θ = 0 := by
  have h4 : (2 : ℕ+) * 2 = 4 := rfl
  rw [← modularGain_two_eq_one_iff θ, ← exchangeCurvature_two_eq_zero_iff (modularGain θ) 2,
    exchangeCurvature, h4, sub_eq_zero]

/-- At zero weight the polarized transport is the flat affine transport. -/
theorem exchangeTransport_modularGain_zero (n : ℕ+) :
    exchangeTransport (modularGain 0) n = conormalTransport ℝ n := by
  rw [(modularGain_eq_one_iff 0).2 rfl, exchangeTransport_one]

/-! ## Spectral insertion -/

/-- The centred spectral gain of weight `w`: the modular gain of weight `2 Re s - w`. -/
def spectralGain (w : ℝ) (s : ℂ) : ℕ+ →* ℝˣ := modularGain (2 * s.re - w)

/-- **The framed exchange family is blind to imaginary height.** -/
theorem spectralGain_eq_of_re_eq (w : ℝ) {s t : ℂ} (h : s.re = t.re) :
    spectralGain w s = spectralGain w t := by
  rw [spectralGain, spectralGain, h]

/-- **Universal rank-one purity template.**  The centred spectral family of weight `w` is
composition coherent exactly on the line `Re s = w / 2`. -/
theorem exchangeTransport_spectralGain_mul_iff (w : ℝ) (s : ℂ) :
    (∀ m n : ℕ+, exchangeTransport (spectralGain w s) m * exchangeTransport (spectralGain w s) n =
        exchangeTransport (spectralGain w s) (m * n)) ↔ s.re = w / 2 := by
  rw [spectralGain, exchangeTransport_modularGain_mul_iff]
  constructor
  · intro h; linarith
  · intro h; rw [h]; ring

/-- **Critical-line specialization.**  For the half-density weight `w = 1` the family is coherent
exactly on the critical line. -/
theorem exchangeTransport_spectralGain_one_mul_iff (s : ℂ) :
    (∀ m n : ℕ+, exchangeTransport (spectralGain 1 s) m * exchangeTransport (spectralGain 1 s) n =
        exchangeTransport (spectralGain 1 s) (m * n)) ↔ s.re = 1 / 2 :=
  exchangeTransport_spectralGain_mul_iff 1 s

/-! ## Identification with the Deninger half-density mate gain -/

theorem spectralGain_one_apply (s : ℂ) (n : ℕ+) :
    ((spectralGain 1 s n : ℝˣ) : ℝ) = deningerHalfDensityMateGain (n : ℕ) s := by
  rw [spectralGain, modularGain_apply, deningerHalfDensityMateGain,
    Real.rpow_def_of_pos (by exact_mod_cast n.pos : (0 : ℝ) < ((n : ℕ) : ℝ))]
  ring_nf

/-- **The polarized exchange transport of the half-density spectral gain is the existing one-sided
framed transport.** -/
theorem exchangeTransport_spectralGain_one_eq (s : ℂ) (n : ℕ+) :
    exchangeTransport (spectralGain 1 s) n =
      deningerOneSidedFramedTransport (fun d => deningerHalfDensityMateGain d s) (n : ℕ) := by
  ext i j
  fin_cases i
  all_goals fin_cases j
  all_goals simp [exchangeTransport, deningerOneSidedFramedTransport, spectralGain_one_apply]

/-! ## Hermitian torsion and its transgression -/

/-- The Hermitian torsion of a complex character. -/
def hermitianTorsion (lam : ℕ+ →* ℂˣ) : ℕ+ →* ℝˣ where
  toFun n := Units.mk0 (Complex.normSq ((lam n : ℂˣ) : ℂ))
    (by simp)
  map_one' := by
    refine Units.ext ?_
    simp
  map_mul' m n := by
    refine Units.ext ?_
    simp [Complex.normSq_mul]

@[simp] theorem hermitianTorsion_apply (lam : ℕ+ →* ℂˣ) (n : ℕ+) :
    ((hermitianTorsion lam n : ℝˣ) : ℝ) = Complex.normSq ((lam n : ℂˣ) : ℂ) := rfl

/-- The Hermitian anomaly of a complex character. -/
def hermitianAnomaly (lam : ℕ+ →* ℂˣ) (n : ℕ+) : ℝ :=
  1 - ((hermitianTorsion lam n : ℝˣ) : ℝ)

/-- **The Hermitian anomaly is a crossed cocycle for its torsion.** -/
theorem hermitianAnomaly_mul (lam : ℕ+ →* ℂˣ) (m n : ℕ+) :
    hermitianAnomaly lam (m * n) =
      hermitianAnomaly lam m +
        ((hermitianTorsion lam m : ℝˣ) : ℝ) * hermitianAnomaly lam n := by
  simp only [hermitianAnomaly, map_mul, Units.val_mul]
  ring

/-- **The one-sided framed curvature of the Hermitian torsion is the affine transgression of its
anomaly.** -/
theorem exchangeCurvature_hermitianTorsion (lam : ℕ+ →* ℂˣ) (m n : ℕ+) :
    exchangeCurvature (hermitianTorsion lam) m n =
      (((hermitianTorsion lam m : ℝˣ) : ℝ) * (((m : ℕ) : ℝ) - 1) * hermitianAnomaly lam n) •
        exchangeE12 ℝ := by
  rw [exchangeCurvature_eq, hermitianAnomaly]

/-- **Reciprocal flatness, unit torsion, and vanishing anomaly agree.** -/
theorem inv_eq_conj_iff_torsion_eq_one (lam : ℕ+ →* ℂˣ) (n : ℕ+) :
    (((lam n : ℂˣ) : ℂ))⁻¹ = (starRingEnd ℂ) ((lam n : ℂˣ) : ℂ) ↔
      ((hermitianTorsion lam n : ℝˣ) : ℝ) = 1 := by
  have hz : ((lam n : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero (lam n)
  constructor
  · intro h
    have hmul : ((lam n : ℂˣ) : ℂ) * (starRingEnd ℂ) ((lam n : ℂˣ) : ℂ) = 1 := by
      rw [← h, mul_inv_cancel₀ hz]
    rw [Complex.mul_conj] at hmul
    have : (Complex.normSq ((lam n : ℂˣ) : ℂ) : ℝ) = 1 := by exact_mod_cast hmul
    simpa using this
  · intro h
    have hmul : ((lam n : ℂˣ) : ℂ) * (starRingEnd ℂ) ((lam n : ℂˣ) : ℂ) = 1 := by
      rw [Complex.mul_conj]
      simpa using congrArg (fun r : ℝ => (r : ℂ)) (by simpa using h)
    exact (eq_inv_of_mul_eq_one_left (by rw [mul_comm] at hmul; exact hmul)).symm

theorem hermitianAnomaly_eq_zero_iff (lam : ℕ+ →* ℂˣ) (n : ℕ+) :
    hermitianAnomaly lam n = 0 ↔ ((hermitianTorsion lam n : ℝˣ) : ℝ) = 1 := by
  rw [hermitianAnomaly, sub_eq_zero, eq_comm]

end

end RHTower
