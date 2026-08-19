import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedPublishedGrowthPriorArt
import GaloisForLFunctions.RHTower.XiProjectiveReflectionSourceTemperatureSpectrum
import GaloisForLFunctions.RHTower.PrimeClockShaleDiagonal
import GaloisForLFunctions.RHTower.GaussHodgeSeamEnergyBridge
import GaloisForLFunctions.RHTower.FarFieldAnchor

/-!
# Outer Euler modulus and first-prime seam are exactly antialigned

On a strip fibre the two completed values `xi(h + conj rho)` and `xi(h + 1 - rho)` lie on one
horizontal line strictly inside the Euler half-plane.  Horizontal strict monotonicity of `|xi|`
orients their modulus defect by the sign of `Re rho - 1/2`, while the demodulated first-prime seam
`2^(-Re rho) - 2^(Re rho - 1)` has the opposite orientation.

The two defects therefore always have product at most zero, with equality exactly on the critical
line.  A nonnegative cross-scale alignment on the Xi divisor forces every first-prime seam charge to
vanish, which is the Riemann hypothesis.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The demodulated real seam amplitude -/

/-- The unsquared reflected prime-clock amplitude: the demodulated seam charge. -/
def primeClockReflectionAmplitude (sigma : ℝ) (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-sigma) - (p : ℝ) ^ (-(1 - sigma))

theorem primeClockReflectionAmplitude_sq (sigma : ℝ) (p : Nat.Primes) :
    primeClockReflectionAmplitude sigma (p : ℕ) ^ 2 =
      primeClockReflectionEnergy sigma p := rfl

private theorem cpow_vertical_shift {p : ℕ} (hp : 1 < p) (t gamma : ℝ) :
    ((p : ℝ) : ℂ) ^ (((-t : ℝ) : ℂ) + ((gamma : ℝ) : ℂ) * I) =
      Complex.exp (Complex.I * ((gamma * Real.log p : ℝ) : ℂ)) *
        (((p : ℝ) ^ (-t) : ℝ) : ℂ) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by positivity
  have hpne : ((p : ℝ) : ℂ) ≠ 0 := by simpa using (ne_of_gt hp0)
  have hlog : Complex.log ((p : ℝ) : ℂ) = ((Real.log p : ℝ) : ℂ) :=
    (Complex.ofReal_log hp0.le).symm
  rw [Complex.cpow_def_of_ne_zero hpne, hlog]
  have hsplit : ((Real.log p : ℝ) : ℂ) * (((-t : ℝ) : ℂ) + ((gamma : ℝ) : ℂ) * I) =
      ((Real.log p * (-t) : ℝ) : ℂ) + Complex.I * ((gamma * Real.log p : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, mul_comm]
  congr 1
  rw [← Complex.ofReal_exp, Real.rpow_def_of_pos hp0]

/-- **Demodulation.**  The canonical prime seam is the positive logarithmic scale times a
unimodular vertical character times the real reflected amplitude. -/
theorem orbitwiseNatPrimeSeamCharge_eq_character_mul_amplitude
    {p : ℕ} (hp : 1 < p) (rho : ℂ) :
    orbitwiseNatPrimeSeamCharge p rho =
      ((Real.log p : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((rho.im * Real.log p : ℝ) : ℂ)) *
        ((primeClockReflectionAmplitude rho.re p : ℝ) : ℂ) := by
  have hconj : -(starRingEnd ℂ) rho = ((-rho.re : ℝ) : ℂ) + ((rho.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  have hrefl : -(1 - rho) = ((-(1 - rho.re) : ℝ) : ℂ) + ((rho.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp
  rw [orbitwiseNatPrimeSeamCharge, orbitwiseScaleSeamCharge, hconj, hrefl,
    cpow_vertical_shift hp rho.re rho.im, cpow_vertical_shift hp (1 - rho.re) rho.im,
    primeClockReflectionAmplitude]
  push_cast
  ring

/-! ## Orientation of the demodulated amplitude -/

theorem primeClockReflectionAmplitude_pos_iff {p : ℕ} (hp : 1 < p) (sigma : ℝ) :
    0 < primeClockReflectionAmplitude sigma p ↔ sigma < 1 / 2 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [primeClockReflectionAmplitude, sub_pos, Real.rpow_lt_rpow_left_iff hp1]
  constructor <;> intro h <;> linarith

theorem primeClockReflectionAmplitude_neg_iff {p : ℕ} (hp : 1 < p) (sigma : ℝ) :
    primeClockReflectionAmplitude sigma p < 0 ↔ 1 / 2 < sigma := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  rw [primeClockReflectionAmplitude, sub_neg, Real.rpow_lt_rpow_left_iff hp1]
  constructor <;> intro h <;> linarith

theorem primeClockReflectionAmplitude_eq_zero_iff {p : ℕ} (hp : 1 < p) (sigma : ℝ) :
    primeClockReflectionAmplitude sigma p = 0 ↔ sigma = 1 / 2 := by
  have hpos := primeClockReflectionAmplitude_pos_iff hp sigma
  have hneg := primeClockReflectionAmplitude_neg_iff hp sigma
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd h (ne_of_gt (hpos.2 hlt))
    · exact absurd h (ne_of_lt (hneg.2 hgt))
  · intro h
    rw [primeClockReflectionAmplitude, h]
    norm_num

/-- The seam charge vanishes exactly when the demodulated amplitude does. -/
theorem orbitwiseNatPrimeSeamCharge_eq_zero_iff_amplitude
    {p : ℕ} (hp : 1 < p) (rho : ℂ) :
    orbitwiseNatPrimeSeamCharge p rho = 0 ↔
      primeClockReflectionAmplitude rho.re p = 0 := by
  rw [orbitwiseNatPrimeSeamCharge_eq_character_mul_amplitude hp rho]
  have hlogne : ((Real.log p : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp)
    exact Complex.ofReal_ne_zero.mpr hpos.ne'
  have hexpne : Complex.exp (Complex.I * ((rho.im * Real.log p : ℝ) : ℂ)) ≠ 0 :=
    Complex.exp_ne_zero _
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · rcases mul_eq_zero.mp h1 with h3 | h4
      · exact absurd h3 hlogne
      · exact absurd h4 hexpne
    · exact_mod_cast h2
  · intro h
    rw [h]
    simp

/-! ## Orientation of the outer modulus defect -/

/-- The real outer modulus defect at shift `h`. -/
def xiOuterModulusDefect (h : ℝ) (rho : ℂ) : ℝ :=
  Real.log (‖xi ((h : ℂ) + (starRingEnd ℂ) rho)‖ / ‖xi ((h : ℂ) + 1 - rho)‖)

private theorem xi_shift_conj_eq_XiC (h : ℝ) (rho : ℂ) :
    xi ((h : ℂ) + (starRingEnd ℂ) rho) =
      XiC (((-rho.im : ℝ) : ℂ) - ((h + rho.re - 1 / 2 : ℝ) : ℂ) * I) := by
  rw [XiC]
  congr 1
  apply Complex.ext <;> simp

private theorem xi_shift_reflect_eq_XiC (h : ℝ) (rho : ℂ) :
    xi ((h : ℂ) + 1 - rho) =
      XiC (((-rho.im : ℝ) : ℂ) - ((h + 1 / 2 - rho.re : ℝ) : ℂ) * I) := by
  rw [XiC]
  congr 1
  apply Complex.ext
  · simp; ring
  · simp

private theorem norm_xi_shift_strictMono {h : ℝ} (hh : 1 ≤ h) {rho : ℂ}
    (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    (‖xi ((h : ℂ) + 1 - rho)‖ < ‖xi ((h : ℂ) + (starRingEnd ℂ) rho)‖ ↔ 1 / 2 < rho.re) := by
  have hmono := strictMonoOn_norm_XiC_horizontal_of_halfPlaneBound
    (alpha := 1 / 2) (by norm_num) xiZeroHalfPlaneBound_half (-rho.im)
  have hplus : (h + rho.re - 1 / 2 : ℝ) ∈ Set.Ici (1 / 2 : ℝ) := by
    simp only [Set.mem_Ici]; linarith
  have hminus : (h + 1 / 2 - rho.re : ℝ) ∈ Set.Ici (1 / 2 : ℝ) := by
    simp only [Set.mem_Ici]; linarith
  rw [xi_shift_conj_eq_XiC, xi_shift_reflect_eq_XiC]
  constructor
  · intro hlt
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt2
    · rw [← heq] at hlt
      simp at hlt
    · have := hmono hplus hminus (by linarith)
      exact absurd hlt (not_lt.mpr (le_of_lt this))
  · intro hgt
    exact hmono hminus hplus (by linarith)

private theorem norm_xi_shift_conj_pos {h : ℝ} (hh : 1 ≤ h) {rho : ℂ}
    (h0 : 0 < rho.re) : 0 < ‖xi ((h : ℂ) + (starRingEnd ℂ) rho)‖ := by
  refine norm_pos_iff.2 (xi_ne_zero_of_one_lt_re ?_)
  simp only [Complex.add_re, Complex.ofReal_re, Complex.conj_re]
  linarith

private theorem norm_xi_shift_reflect_pos {h : ℝ} (hh : 1 ≤ h) {rho : ℂ}
    (h1 : rho.re < 1) : 0 < ‖xi ((h : ℂ) + 1 - rho)‖ := by
  refine norm_pos_iff.2 (xi_ne_zero_of_one_lt_re ?_)
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re]
  linarith

theorem xiOuterModulusDefect_pos_iff {h : ℝ} (hh : 1 ≤ h) {rho : ℂ}
    (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    0 < xiOuterModulusDefect h rho ↔ 1 / 2 < rho.re := by
  have hden := norm_xi_shift_reflect_pos hh h1
  rw [xiOuterModulusDefect, Real.log_pos_iff (by positivity), one_lt_div hden]
  exact norm_xi_shift_strictMono hh h0 h1

theorem xiOuterModulusDefect_neg_iff {h : ℝ} (hh : 1 ≤ h) {rho : ℂ}
    (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    xiOuterModulusDefect h rho < 0 ↔ rho.re < 1 / 2 := by
  have hden := norm_xi_shift_reflect_pos hh h1
  have hnum := norm_xi_shift_conj_pos hh h0
  rw [xiOuterModulusDefect, Real.log_neg_iff (by positivity), div_lt_one hden]
  have hmono := strictMonoOn_norm_XiC_horizontal_of_halfPlaneBound
    (alpha := 1 / 2) (by norm_num) xiZeroHalfPlaneBound_half (-rho.im)
  have hplus : (h + rho.re - 1 / 2 : ℝ) ∈ Set.Ici (1 / 2 : ℝ) := by
    simp only [Set.mem_Ici]; linarith
  have hminus : (h + 1 / 2 - rho.re : ℝ) ∈ Set.Ici (1 / 2 : ℝ) := by
    simp only [Set.mem_Ici]; linarith
  rw [xi_shift_conj_eq_XiC, xi_shift_reflect_eq_XiC]
  constructor
  · intro hlt
    by_contra hcon
    push Not at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt2
    · rw [heq] at hlt
      simp at hlt
    · have := hmono hminus hplus (by linarith)
      exact absurd hlt (not_lt.mpr (le_of_lt this))
  · intro hlt
    exact hmono hplus hminus (by linarith)

theorem xiOuterModulusDefect_eq_zero_iff {h : ℝ} (hh : 1 ≤ h) {rho : ℂ}
    (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    xiOuterModulusDefect h rho = 0 ↔ rho.re = 1 / 2 := by
  have hpos := xiOuterModulusDefect_pos_iff hh h0 h1
  have hneg := xiOuterModulusDefect_neg_iff hh h0 h1
  constructor
  · intro hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hz (ne_of_lt (hneg.2 hlt))
    · exact absurd hz (ne_of_gt (hpos.2 hgt))
  · intro he
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd (hneg.1 hlt) (by rw [he]; exact lt_irrefl _)
    · exact absurd (hpos.1 hgt) (by rw [he]; exact lt_irrefl _)

/-! ## Exact antialignment -/

/-- **Antialignment.**  The outer modulus defect and the demodulated first-prime seam always have
product at most zero. -/
theorem xiOuterModulusDefect_mul_amplitude_nonpos {h : ℝ} (hh : 1 ≤ h) {rho : ℂ}
    (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    xiOuterModulusDefect h rho * primeClockReflectionAmplitude rho.re 2 ≤ 0 := by
  rcases lt_trichotomy rho.re (1 / 2) with hlt | heq | hgt
  · have hM : xiOuterModulusDefect h rho < 0 := (xiOuterModulusDefect_neg_iff hh h0 h1).2 hlt
    have hd : 0 < primeClockReflectionAmplitude rho.re 2 :=
      (primeClockReflectionAmplitude_pos_iff one_lt_two rho.re).2 hlt
    nlinarith
  · have hd : primeClockReflectionAmplitude rho.re 2 = 0 :=
      (primeClockReflectionAmplitude_eq_zero_iff one_lt_two rho.re).2 heq
    rw [hd, mul_zero]
  · have hM : 0 < xiOuterModulusDefect h rho := (xiOuterModulusDefect_pos_iff hh h0 h1).2 hgt
    have hd : primeClockReflectionAmplitude rho.re 2 < 0 :=
      (primeClockReflectionAmplitude_neg_iff one_lt_two rho.re).2 hgt
    nlinarith

/-- The product vanishes exactly on the critical line. -/
theorem xiOuterModulusDefect_mul_amplitude_eq_zero_iff {h : ℝ} (hh : 1 ≤ h) {rho : ℂ}
    (h0 : 0 < rho.re) (h1 : rho.re < 1) :
    xiOuterModulusDefect h rho * primeClockReflectionAmplitude rho.re 2 = 0 ↔
      rho.re = 1 / 2 := by
  constructor
  · intro hz
    rcases mul_eq_zero.mp hz with hM | hd
    · exact (xiOuterModulusDefect_eq_zero_iff hh h0 h1).1 hM
    · exact (primeClockReflectionAmplitude_eq_zero_iff one_lt_two rho.re).1 hd
  · intro he
    rw [(primeClockReflectionAmplitude_eq_zero_iff one_lt_two rho.re).2 he, mul_zero]

/-! ## The top-down chain -/

/-- Nonnegative cross-scale alignment of the two source defects on the Xi divisor. -/
def XiOuterPrimeTwoAligned (h : ℝ) : Prop :=
  ∀ q : XiZeroCopy,
    0 ≤ xiOuterModulusDefect h ((q.1 : ℂ)) *
      primeClockReflectionAmplitude ((q.1 : ℂ)).re 2

/-- **The alignment chain.**  A nonnegative cross-scale alignment at one shift `h >= 1` forces
every first-prime seam charge to vanish, which is RH. -/
theorem riemannHypothesis_of_xiOuterPrimeTwoAligned {h : ℝ} (hh : 1 ≤ h)
    (hal : XiOuterPrimeTwoAligned h) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_seamCharge_eq_zero]
  intro q
  obtain ⟨h0, h1⟩ := xiZeroCopy_re_mem_open_unit q
  have hle := xiOuterModulusDefect_mul_amplitude_nonpos hh h0 h1
  have hzero : xiOuterModulusDefect h ((q.1 : ℂ)) *
      primeClockReflectionAmplitude ((q.1 : ℂ)).re 2 = 0 :=
    le_antisymm hle (hal q)
  have hre : ((q.1 : ℂ)).re = 1 / 2 :=
    (xiOuterModulusDefect_mul_amplitude_eq_zero_iff hh h0 h1).1 hzero
  rw [orbitwiseNatPrimeSeamCharge_eq_zero_iff_amplitude one_lt_two]
  exact (primeClockReflectionAmplitude_eq_zero_iff one_lt_two _).2 hre

end

end RHTower
