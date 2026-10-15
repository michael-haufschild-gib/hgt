import GaloisForLFunctions.RHTower.ThetaRenewalFullDivisorCharge
import GaloisForLFunctions.RHTower.ThetaPrimeDeletionMellin

/-!
# Prime deletion, vacuum credit, and full-divisor renewal charge

At shift `h=2 log p`, literal prime deletion sends the profile and increment to
`P_h(t)=P(t)-exp(-h/4)P(t+h)` and `nu_h(t)=nu(t)-exp(-h/4)nu(t+h)`.
It removes the growing vacuum from the profile. With the remaining seam
`P_h(0)`, the denominator is exactly `(s-1/4)` times the Laplace transform
of the positive deleted profile. Its only real zero is `1/4`, and its
normalized weighted renewal mass exceeds one.

Keeping the original seam instead carries the exact credit
`exp(-h/4)P(h)` and preserves the original zero-free half-plane. The
two-ended return then changes by half that credit.

The exact translation law retains the finite profile prefix and the physical
full renewal charge, including at arbitrary Xi divisor points. It does not
prove that the charge is real there. Neither boundary term may be discarded
when attempting divisor orientation.
-/

open Complex Filter Topology Set MeasureTheory HurwitzZeta

namespace RHTower
noncomputable section
local notation "Θ" => evenKernel (0 : UnitAddCircle)

private def RightSuperexp (f : ℝ → ℝ) : Prop :=
  ∀ K : ℝ, ∃ C, 0 < C ∧ ∀ t, 0 ≤ t →
    Real.exp (K * t) * |f t| ≤ C * Real.exp (-t)

private theorem rightSuperexp_shift {f : ℝ → ℝ} (hf : RightSuperexp f)
    {h : ℝ} (hh : 0 ≤ h) : RightSuperexp (fun t => f (t + h)) := by
  intro K
  obtain ⟨C, hC, hbound⟩ := hf K
  refine ⟨C * Real.exp (-(K + 1) * h), by positivity, fun t ht => ?_⟩
  calc
    Real.exp (K * t) * |f (t + h)| =
        Real.exp (-K * h) * (Real.exp (K * (t + h)) * |f (t + h)|) := by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          ring
    _ ≤ Real.exp (-K * h) * (C * Real.exp (-(t + h))) :=
      mul_le_mul_of_nonneg_left (hbound (t + h) (add_nonneg ht hh)) (by positivity)
    _ = (C * Real.exp (-(K + 1) * h)) * Real.exp (-t) := by
      rw [mul_left_comm, mul_assoc, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring

private theorem rightSuperexp_sub_shift {f : ℝ → ℝ} (hf : RightSuperexp f)
    {h : ℝ} (hh : 0 ≤ h) (b : ℝ) :
    RightSuperexp (fun t => f t - b * f (t + h)) := by
  intro K
  obtain ⟨C, hC, hb⟩ := hf K
  obtain ⟨D, hD, hd⟩ := rightSuperexp_shift hf hh K
  refine ⟨C + |b| * D, by positivity, fun t ht => ?_⟩
  calc
    Real.exp (K * t) * |f t - b * f (t + h)| ≤
        Real.exp (K * t) * (|f t| + |b| * |f (t + h)|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [Real.norm_eq_abs, abs_mul] using norm_sub_le (f t) (b * f (t + h))
    _ = Real.exp (K * t) * |f t| + |b| * (Real.exp (K * t) * |f (t + h)|) := by ring
    _ ≤ C * Real.exp (-t) + |b| * (D * Real.exp (-t)) :=
      add_le_add (hb t ht) (mul_le_mul_of_nonneg_left (hd t ht) (abs_nonneg b))
    _ = _ := by ring

private theorem rightSuperexp_weighted_limit {f : ℝ → ℝ} (hf : RightSuperexp f) (s : ℂ) :
    Tendsto (fun t : ℝ => Complex.exp (-(s * t)) * (f t : ℂ)) atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := hf (-s.re)
  apply squeeze_zero_norm' _ (by simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul C)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  simpa using hC t ht

/-- The profile left after a weighted forward arithmetic shift. -/
def thetaRenewalDeletedProfile (h t : ℝ) : ℝ :=
  thetaLogProfile t - Real.exp (-h / 4) * thetaLogProfile (t + h)

/-- The corresponding literal deletion of the renewal increment. -/
def thetaRenewalDeletedIncrement (h t : ℝ) : ℝ :=
  thetaRenewalIncrement t - Real.exp (-h / 4) * thetaRenewalIncrement (t + h)

def thetaRenewalDeletedProfileLaplace (h : ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (thetaRenewalDeletedProfile h t : ℂ)

/-- The remaining seam, rather than the old undeleted seam, normalizes this denominator. -/
def thetaRenewalDeletedDenominator (h : ℝ) (s : ℂ) : ℂ :=
  (thetaRenewalDeletedProfile h 0 : ℂ) -
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (thetaRenewalDeletedIncrement h t : ℂ)

theorem thetaRenewalDeletedProfile_eq_tail (h t : ℝ) :
    thetaRenewalDeletedProfile h t =
      thetaLogTail t - Real.exp (-h / 4) * thetaLogTail (t + h) := by
  rw [thetaRenewalDeletedProfile, thetaLogProfile_eq_add, thetaLogProfile_eq_add]
  have he : Real.exp (-h / 4) * Real.exp ((t + h) / 4) = Real.exp (t / 4) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith

theorem thetaRenewalDeletedProfile_pos {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) :
    0 < thetaRenewalDeletedProfile h t := by
  rw [thetaRenewalDeletedProfile_eq_tail]
  have hb : Real.exp (-h / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hd := strictAntiOn_thetaLogTail ht (show 0 ≤ t + h by linarith)
    (show t < t + h by linarith)
  have hm := mul_le_mul_of_nonneg_right hb (thetaLogTail_pos (t + h)).le
  linarith

theorem hasDerivAt_thetaRenewalDeletedProfile (h t : ℝ) :
    HasDerivAt (thetaRenewalDeletedProfile h)
      (thetaRenewalDeletedProfile h t / 4 - thetaRenewalDeletedIncrement h t) t := by
  have hd := (hasDerivAt_thetaLogProfile t).sub
    (((hasDerivAt_thetaLogProfile (t + h)).comp t ((hasDerivAt_id t).add_const h)).const_mul
      (Real.exp (-h / 4)))
  exact hd.congr_deriv (by simp only [thetaRenewalDeletedProfile, thetaRenewalDeletedIncrement]; ring)

private theorem deletedProfile_superexp {h : ℝ} (hh : 0 ≤ h) :
    RightSuperexp (thetaRenewalDeletedProfile h) := by
  simpa only [RightSuperexp, thetaRenewalDeletedProfile_eq_tail] using
    rightSuperexp_sub_shift thetaLogTail_superexp hh (Real.exp (-h / 4))

private theorem deletedIncrement_superexp {h : ℝ} (hh : 0 ≤ h) :
    RightSuperexp (thetaRenewalDeletedIncrement h) :=
  rightSuperexp_sub_shift thetaRenewalIncrement_superexp hh (Real.exp (-h / 4))

theorem integrableOn_thetaRenewalDeletedProfileLaplace {h : ℝ} (hh : 0 ≤ h) (s : ℂ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) *
      (thetaRenewalDeletedProfile h t : ℂ)) (Ioi 0) :=
  integrableOn_cexp_mul_of_superexp
    (continuous_iff_continuousAt.mpr fun t => (hasDerivAt_thetaRenewalDeletedProfile h t).continuousAt)
    (deletedProfile_superexp hh) s

theorem integrableOn_thetaRenewalDeletedIncrementLaplace {h : ℝ} (hh : 0 ≤ h) (s : ℂ) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) *
      (thetaRenewalDeletedIncrement h t : ℂ)) (Ioi 0) := by
  apply integrableOn_cexp_mul_of_superexp _ (deletedIncrement_superexp hh) s
  exact continuous_thetaRenewalIncrement.sub
    ((continuous_thetaRenewalIncrement.comp (continuous_id.add continuous_const)).const_mul _)

/-- Removing the growing vacuum forces the exact linear factor `s-1/4`. -/
theorem thetaRenewalDeletedDenominator_eq {h : ℝ} (hh : 0 ≤ h) (s : ℂ) :
    thetaRenewalDeletedDenominator h s =
      (s - 1 / 4) * thetaRenewalDeletedProfileLaplace h s := by
  let f : ℝ → ℂ := fun t => Complex.exp (-(s * t)) * (thetaRenewalDeletedProfile h t : ℂ)
  let g : ℝ → ℂ := fun t => (1 / 4 - s) * f t -
    Complex.exp (-(s * t)) * (thetaRenewalDeletedIncrement h t : ℂ)
  have hd (t : ℝ) : HasDerivAt f (g t) t := by
    have he : HasDerivAt (fun t : ℝ => Complex.exp (-(s * t)))
        (-s * Complex.exp (-(s * t))) t := by
      simpa [mul_comm] using
        (((hasDerivAt_id (t : ℂ)).const_mul (-s)).cexp.comp_ofReal)
    have hp := (hasDerivAt_thetaRenewalDeletedProfile h t).ofReal_comp
    refine (he.mul hp).congr_deriv ?_
    dsimp [f, g]
    push_cast
    ring
  have hi : IntegrableOn g (Ioi 0) :=
    ((integrableOn_thetaRenewalDeletedProfileLaplace hh s).const_mul (1 / 4 - s)).sub
      (integrableOn_thetaRenewalDeletedIncrementLaplace hh s)
  have he := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hd t) hi
    (rightSuperexp_weighted_limit (deletedProfile_superexp hh) s)
  simp only [g, f, integral_sub
      ((integrableOn_thetaRenewalDeletedProfileLaplace hh s).const_mul (1 / 4 - s))
      (integrableOn_thetaRenewalDeletedIncrementLaplace hh s), integral_const_mul,
    Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_mul, zero_sub] at he
  unfold thetaRenewalDeletedDenominator thetaRenewalDeletedProfileLaplace
  linear_combination he

theorem thetaRenewalDeletedProfileLaplace_ofReal (h x : ℝ) :
    thetaRenewalDeletedProfileLaplace h x =
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(x * t)) * thetaRenewalDeletedProfile h t : ℝ) : ℂ) := by
  unfold thetaRenewalDeletedProfileLaplace
  calc
    _ = ∫ t in Ioi (0 : ℝ), ((Real.exp (-(x * t)) * thetaRenewalDeletedProfile h t : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      push_cast
      rfl
    _ = _ := integral_ofReal

theorem re_thetaRenewalDeletedProfileLaplace_pos {h : ℝ} (hh : 0 < h) (x : ℝ) :
    0 < (thetaRenewalDeletedProfileLaplace h x).re := by
  rw [thetaRenewalDeletedProfileLaplace_ofReal, Complex.ofReal_re]
  have hi := (integrableOn_thetaRenewalDeletedProfileLaplace hh.le (x : ℂ)).re
  change IntegrableOn (fun t : ℝ => (Complex.exp (-((x : ℂ) * t)) *
    (thetaRenewalDeletedProfile h t : ℂ)).re) (Ioi 0) at hi
  have he : (fun t : ℝ => (Complex.exp (-((x : ℂ) * t)) *
      (thetaRenewalDeletedProfile h t : ℂ)).re) =
      fun t : ℝ => Real.exp (-(x * t)) * thetaRenewalDeletedProfile h t := by
    funext t
    simp [Complex.exp_re, Complex.mul_re]
  rw [he] at hi
  exact setIntegral_Ioi_pos hi fun t ht =>
    mul_pos (Real.exp_pos _) (thetaRenewalDeletedProfile_pos hh ht.le)

/-- The deleted denominator has exactly one real zero, at the right critical boundary. -/
theorem thetaRenewalDeletedDenominator_ofReal_eq_zero_iff {h : ℝ} (hh : 0 < h) (x : ℝ) :
    thetaRenewalDeletedDenominator h x = 0 ↔ x = 1 / 4 := by
  rw [thetaRenewalDeletedDenominator_eq hh.le]
  have hp : thetaRenewalDeletedProfileLaplace h (x : ℂ) ≠ 0 := by
    intro hz
    have := re_thetaRenewalDeletedProfileLaplace_pos hh x
    simp [hz] at this
  simp only [mul_eq_zero, hp, or_false, sub_eq_zero]
  constructor
  · intro he
    have hr := congrArg Complex.re he
    simpa using hr
  · rintro rfl
    norm_num

theorem re_thetaRenewalDeletedDenominator_eq (h x : ℝ) (hh : 0 ≤ h) :
    (thetaRenewalDeletedDenominator h x).re =
      (x - 1 / 4) * (thetaRenewalDeletedProfileLaplace h x).re := by
  rw [thetaRenewalDeletedDenominator_eq hh]
  simp [Complex.mul_re]

theorem re_thetaRenewalDeletedDenominator_neg_iff {h : ℝ} (hh : 0 < h) (x : ℝ) :
    (thetaRenewalDeletedDenominator h x).re < 0 ↔ x < 1 / 4 := by
  rw [re_thetaRenewalDeletedDenominator_eq h x hh.le]
  have hp := re_thetaRenewalDeletedProfileLaplace_pos hh x
  constructor
  · intro hneg
    by_contra hn
    exact (not_lt_of_ge (mul_nonneg (by linarith) hp.le)) hneg
  · intro hx
    exact mul_neg_of_neg_of_pos (by linarith) hp

theorem re_thetaRenewalDeletedDenominator_pos_iff {h : ℝ} (hh : 0 < h) (x : ℝ) :
    0 < (thetaRenewalDeletedDenominator h x).re ↔ 1 / 4 < x := by
  rw [re_thetaRenewalDeletedDenominator_eq h x hh.le]
  have hp := re_thetaRenewalDeletedProfileLaplace_pos hh x
  constructor
  · intro hpos
    by_contra hn
    exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (by linarith) hp.le)) hpos
  · intro hx
    exact mul_pos (by linarith) hp

/-- The deleted increment remains positive on the causal ray. -/
theorem thetaRenewalDeletedIncrement_pos {h t : ℝ} (hh : 0 < h) (ht : 0 ≤ t) :
    0 < thetaRenewalDeletedIncrement h t := by
  have hanti : StrictAntiOn thetaRenewalIncrement (Ici 0) := by
    simpa using strictAntiOn_exp_mul_thetaRenewalIncrement (x := 0) (by norm_num)
  have hd := hanti ht (show 0 ≤ t + h by linarith) (show t < t + h by linarith)
  have hb : Real.exp (-h / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hm := mul_le_mul_of_nonneg_right hb (thetaRenewalIncrement_pos (t + h)).le
  unfold thetaRenewalDeletedIncrement
  linarith

/-- The boundary zero is forced even though the deleted source is positive. -/
theorem thetaRenewalDeletedDenominator_quarter {h : ℝ} (hh : 0 ≤ h) :
    thetaRenewalDeletedDenominator h (1 / 4) = 0 := by
  rw [thetaRenewalDeletedDenominator_eq hh, sub_self, zero_mul]

/-- Exact mass excess after removal of the growing vacuum. -/
theorem thetaRenewalDeleted_weighted_mass_eq {h : ℝ} (hh : 0 ≤ h) :
    (∫ t in Ioi (0 : ℝ), Real.exp (t / 4) * thetaRenewalDeletedIncrement h t) =
      thetaRenewalDeletedProfile h 0 +
        1 / 2 * (thetaRenewalDeletedProfileLaplace h (-(1 / 4))).re := by
  have he := re_thetaRenewalDeletedDenominator_eq h (-(1 / 4)) hh
  have hi := integrableOn_thetaRenewalDeletedIncrementLaplace hh (-(1 / 4))
  have hr : (∫ t in Ioi (0 : ℝ), Complex.exp (-((-(1 / 4) : ℂ) * t)) *
      (thetaRenewalDeletedIncrement h t : ℂ)).re =
      ∫ t in Ioi (0 : ℝ), Real.exp (t / 4) * thetaRenewalDeletedIncrement h t := by
    calc
      _ = ∫ t in Ioi (0 : ℝ),
          (Complex.exp (-((-(1 / 4) : ℂ) * t)) * (thetaRenewalDeletedIncrement h t : ℂ)).re :=
        (integral_re hi).symm
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _
        simp [Complex.exp_re, Complex.mul_re, div_eq_mul_inv, mul_comm]
  norm_num at he
  rw [thetaRenewalDeletedDenominator, Complex.sub_re, Complex.ofReal_re, hr] at he
  linarith

/-- Natural seam normalization puts the deleted renewal strictly above critical mass. -/
theorem thetaRenewalDeleted_normalized_mass_gt_one {h : ℝ} (hh : 0 < h) :
    1 < (∫ t in Ioi (0 : ℝ), Real.exp (t / 4) * thetaRenewalDeletedIncrement h t) /
      thetaRenewalDeletedProfile h 0 := by
  rw [lt_div_iff₀ (thetaRenewalDeletedProfile_pos hh le_rfl), one_mul,
    thetaRenewalDeleted_weighted_mass_eq hh.le]
  have hp := re_thetaRenewalDeletedProfileLaplace_pos hh (-(1 / 4))
  norm_num at hp
  linarith

private theorem primeDeletion_renewal_time {p : ℕ} (hp : 0 < p) (f : ℝ → ℝ) (t : ℝ) :
    thetaPrimeDeletion {p} (fun x => f (2 * x)) (t / 2) =
      f t - Real.exp (-(2 * Real.log p) / 4) * f (t + 2 * Real.log p) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have he : Real.exp (-(2 * Real.log p) / 4) = (p : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hpR]
    congr 1
    ring
  rw [show ({p} : Finset ℕ) = insert p ∅ by rfl,
    thetaPrimeDeletion_insert hp (by simp) (by simp),
    thetaPrimeDeletion_empty, he]
  rw [show 2 * (t / 2) = t by ring,
    show 2 * (t / 2 + Real.log (p : ℝ)) = t + 2 * Real.log p by ring]

/-- The shift is exactly literal prime deletion in renewal time `t=2x`. -/
theorem thetaRenewalDeletedProfile_eq_primeDeletion {p : ℕ} (hp : 0 < p) (t : ℝ) :
    thetaRenewalDeletedProfile (2 * Real.log p) t =
      thetaPrimeDeletion {p} (fun x => thetaLogProfile (2 * x)) (t / 2) :=
  (primeDeletion_renewal_time hp thetaLogProfile t).symm

theorem thetaRenewalDeletedIncrement_eq_primeDeletion {p : ℕ} (hp : 0 < p) (t : ℝ) :
    thetaRenewalDeletedIncrement (2 * Real.log p) t =
      thetaPrimeDeletion {p} (fun x => thetaRenewalIncrement (2 * x)) (t / 2) :=
  (primeDeletion_renewal_time hp thetaRenewalIncrement t).symm

/-- Every prime deletion exhibits the forced boundary zero and supercritical mass. -/
theorem thetaRenewal_primeDeletion_phase (p : ℕ) (hp : p.Prime) :
    thetaRenewalDeletedDenominator (2 * Real.log p) (1 / 4) = 0 ∧
      1 < (∫ t in Ioi (0 : ℝ), Real.exp (t / 4) *
        thetaRenewalDeletedIncrement (2 * Real.log p) t) /
        thetaRenewalDeletedProfile (2 * Real.log p) 0 := by
  have hh : 0 < 2 * Real.log (p : ℝ) :=
    mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hp.one_lt))
  exact ⟨thetaRenewalDeletedDenominator_quarter hh.le,
    thetaRenewalDeleted_normalized_mass_gt_one hh⟩

/-- The original seam keeps an explicit vacuum credit after deletion. -/
def thetaRenewalCreditedDenominator (h : ℝ) (s : ℂ) : ℂ :=
  (Θ 1 : ℂ) -
    ∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (thetaRenewalDeletedIncrement h t : ℂ)

theorem thetaRenewalCreditedDenominator_eq (h : ℝ) (s : ℂ) :
    thetaRenewalCreditedDenominator h s = thetaRenewalDeletedDenominator h s +
      ((Real.exp (-h / 4) * thetaLogProfile h : ℝ) : ℂ) := by
  have hp : thetaLogProfile 0 = Θ 1 := by simp [thetaLogProfile]
  simp only [thetaRenewalCreditedDenominator, thetaRenewalDeletedDenominator,
    thetaRenewalDeletedProfile, zero_add, hp]
  push_cast
  ring

theorem thetaRenewalDeletedIncrement_le (h t : ℝ) :
    thetaRenewalDeletedIncrement h t ≤ thetaRenewalIncrement t := by
  unfold thetaRenewalDeletedIncrement
  have hp := mul_pos (Real.exp_pos (-h / 4)) (thetaRenewalIncrement_pos (t + h))
  linarith

private theorem norm_deletedIncrementLaplace_le {h : ℝ} (hh : 0 < h)
    {s : ℂ} (hs : -(1 / 4) ≤ s.re) :
    ‖∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) *
      (thetaRenewalDeletedIncrement h t : ℂ)‖ ≤ Θ 1 * thetaRenewalMass := by
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [thetaRenewalMass, ← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_thetaRenewalDeletedIncrementLaplace hh.le s).norm
    (integrableOn_thetaRenewalDensity.const_mul _) measurableSet_Ioi fun t ht => ?_
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaRenewalDeletedIncrement_pos hh ht.le), thetaRenewalDensity]
  have hre : (-(s * (t : ℂ))).re = -s.re * t := by simp
  rw [hre, mul_div_assoc', mul_div_cancel_left₀ _ thetaSeam_pos.ne']
  calc
    Real.exp (-s.re * t) * thetaRenewalDeletedIncrement h t ≤
        Real.exp (-s.re * t) * thetaRenewalIncrement t :=
      mul_le_mul_of_nonneg_left (thetaRenewalDeletedIncrement_le h t) (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by
      have ht0 : 0 ≤ t := le_of_lt ht
      have hm := mul_le_mul_of_nonneg_right (show -s.re ≤ 1 / 4 by linarith) ht0
      nlinarith)) (thetaRenewalIncrement_pos t).le

/-- Carrying the vacuum credit retains the original stable half-plane. -/
theorem re_thetaRenewalCreditedDenominator_ge {h : ℝ} (hh : 0 < h)
    {s : ℂ} (hs : -(1 / 4) ≤ s.re) :
    Θ 1 * (1 - thetaRenewalMass) ≤ (thetaRenewalCreditedDenominator h s).re := by
  have hb := norm_deletedIncrementLaplace_le hh hs
  have hre := Complex.re_le_norm (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) *
    (thetaRenewalDeletedIncrement h t : ℂ))
  rw [thetaRenewalCreditedDenominator, Complex.sub_re, Complex.ofReal_re]
  nlinarith

theorem thetaRenewalCreditedDenominator_ne_zero {h : ℝ} (hh : 0 < h)
    {s : ℂ} (hs : -(1 / 4) ≤ s.re) : thetaRenewalCreditedDenominator h s ≠ 0 := by
  intro hz
  have hb := re_thetaRenewalCreditedDenominator_ge hh hs
  rw [hz, Complex.zero_re] at hb
  have hp := mul_pos thetaSeam_pos
    (sub_pos.mpr (thetaRenewalMass_lt.trans (by norm_num : (1 : ℝ) / 6 < 1)))
  linarith

/-- Restoring the original seam changes the two-ended return by an exact constant. -/
theorem thetaRenewalCredited_two_ended (h : ℝ) (s : ℂ) :
    (1 / 4 + s) * thetaRenewalCreditedDenominator h s +
      (1 / 4 - s) * thetaRenewalCreditedDenominator h (-s) =
    (1 / 4 + s) * thetaRenewalDeletedDenominator h s +
      (1 / 4 - s) * thetaRenewalDeletedDenominator h (-s) +
      ((Real.exp (-h / 4) * thetaLogProfile h / 2 : ℝ) : ℂ) := by
  rw [thetaRenewalCreditedDenominator_eq, thetaRenewalCreditedDenominator_eq]
  push_cast
  ring

/-- The finite profile segment crossed by an arithmetic translation. -/
def thetaRenewalDeletionPrefix (h : ℝ) (s : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..h, Complex.exp (-(s * t)) * (thetaLogProfile t : ℂ)

def thetaRenewalDeletionMultiplier (h : ℝ) (s : ℂ) : ℂ :=
  (Real.exp (-h / 4) : ℂ) * Complex.exp (s * h)

private theorem increment_prefix (h : ℝ) (s : ℂ) :
    (∫ t in (0 : ℝ)..h, Complex.exp (-(s * t)) * (thetaRenewalIncrement t : ℂ)) =
      (Θ 1 : ℂ) - Complex.exp (-(s * h)) * (thetaLogProfile h : ℂ) +
        (1 / 4 - s) * thetaRenewalDeletionPrefix h s := by
  let f : ℝ → ℂ := fun t => Complex.exp (-(s * t)) * (thetaLogProfile t : ℂ)
  let n : ℝ → ℂ := fun t => Complex.exp (-(s * t)) * (thetaRenewalIncrement t : ℂ)
  have hc : Continuous f := by
    dsimp [f]
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).mul
      (Complex.continuous_ofReal.comp continuous_thetaLogProfile)
  have hn : Continuous n := by
    dsimp [n]
    exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal).neg).mul
      (Complex.continuous_ofReal.comp continuous_thetaRenewalIncrement)
  have hd (t : ℝ) : HasDerivAt f ((1 / 4 - s) * f t - n t) t := by
    have he : HasDerivAt (fun t : ℝ => Complex.exp (-(s * t)))
        (-s * Complex.exp (-(s * t))) t := by
      simpa [mul_comm] using
        (((hasDerivAt_id (t : ℂ)).const_mul (-s)).cexp.comp_ofReal)
    refine (he.mul (hasDerivAt_thetaLogProfile t).ofReal_comp).congr_deriv ?_
    dsimp [f, n]
    push_cast
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (((hc.const_mul (1 / 4 - s)).sub hn).intervalIntegrable 0 h)
  rw [intervalIntegral.integral_sub ((hc.const_mul _).intervalIntegrable _ _)
    (hn.intervalIntegrable _ _), intervalIntegral.integral_const_mul] at he
  have hz : f 0 = (Θ 1 : ℂ) := by simp [f, thetaLogProfile]
  rw [hz] at he
  change (∫ t in (0 : ℝ)..h, n t) = (Θ 1 : ℂ) - f h +
    (1 / 4 - s) * ∫ t in (0 : ℝ)..h, f t
  linear_combination -he

private theorem shifted_increment_laplace (h : ℝ) (s : ℂ) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (thetaRenewalIncrement (t + h) : ℂ)) =
      Complex.exp (s * h) *
        ∫ t in Ioi h, Complex.exp (-(s * t)) * (thetaRenewalIncrement t : ℂ) := by
  calc
    _ = Complex.exp (s * h) * ∫ t in Ioi (0 : ℝ),
        (fun u : ℝ => Complex.exp (-(s * u)) * (thetaRenewalIncrement u : ℂ)) (h + t) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _
      dsimp only
      rw [← mul_assoc, ← Complex.exp_add]
      push_cast
      rw [show s * (h : ℂ) + -(s * ((h : ℂ) + t)) = -(s * t) by ring]
      simp only [add_comm t h]
    _ = _ := congrArg (fun z : ℂ => Complex.exp (s * h) * z)
      (integral_Ioi_comp_add
        (fun t : ℝ => Complex.exp (-(s * t)) * (thetaRenewalIncrement t : ℂ)) h)

/-- Exact arithmetic transport includes the finite boundary segment. -/
theorem thetaRenewalDeletedDenominator_boundary {h : ℝ} (hh : 0 ≤ h) (s : ℂ) :
    thetaRenewalDeletedDenominator h s =
      (1 - thetaRenewalDeletionMultiplier h s) * thetaRenewalDenominator s -
        (1 / 4 - s) * thetaRenewalDeletionMultiplier h s * thetaRenewalDeletionPrefix h s := by
  have hn := integrableOn_cexp_mul_of_superexp continuous_thetaRenewalIncrement
    thetaRenewalIncrement_superexp s
  have hs := integrableOn_cexp_mul_of_superexp
    (continuous_thetaRenewalIncrement.comp (continuous_id.add continuous_const))
    (rightSuperexp_shift thetaRenewalIncrement_superexp hh) s
  change IntegrableOn (fun t : ℝ => Complex.exp (-(s * t)) *
    (thetaRenewalIncrement (t + h) : ℂ)) (Ioi 0) at hs
  have hsplit := intervalIntegral.integral_interval_add_Ioi hn (hn.mono_set (Ioi_subset_Ioi hh))
  rw [increment_prefix] at hsplit
  have he : (fun t : ℝ => Complex.exp (-(s * t)) * (thetaRenewalDeletedIncrement h t : ℂ)) =
      fun t : ℝ => Complex.exp (-(s * t)) * (thetaRenewalIncrement t : ℂ) -
        (Real.exp (-h / 4) : ℂ) *
          (Complex.exp (-(s * t)) * (thetaRenewalIncrement (t + h) : ℂ)) := by
    funext t
    simp only [thetaRenewalDeletedIncrement]
    push_cast
    ring
  rw [thetaRenewalDeletedDenominator, he, integral_sub hn (hs.const_mul _), integral_const_mul,
    shifted_increment_laplace]
  have hz : thetaLogProfile 0 = Θ 1 := by simp [thetaLogProfile]
  simp only [thetaRenewalDeletedProfile, zero_add, hz, thetaRenewalDeletionMultiplier,
    thetaRenewalDenominator, thetaRenewalLaplace]
  push_cast
  have hexp : Complex.exp (s * h) * Complex.exp (-(s * h)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  linear_combination Complex.exp (-(h : ℂ) / 4) * Complex.exp (s * h) * hsplit +
    Complex.exp (-(h : ℂ) / 4) * (thetaLogProfile h : ℂ) * hexp

/-- The physical full charge occurs in the literal two-ended deletion boundary law. -/
theorem thetaRenewalDeleted_two_ended_transport {h : ℝ} (hh : 0 ≤ h) (s : ℂ) :
    (1 / 4 + s) * thetaRenewalDeletedDenominator h s +
      (1 / 4 - s) * thetaRenewalDeletedDenominator h (-s) =
      (1 - (thetaRenewalDeletionMultiplier h s + thetaRenewalDeletionMultiplier h (-s)) / 2) *
        XiC (2 * I * s) +
      I * (thetaRenewalDeletionMultiplier h (-s) - thetaRenewalDeletionMultiplier h s) *
        thetaRenewalFullCharge s -
      ((1 / 4 : ℂ) ^ 2 - s ^ 2) *
        (thetaRenewalDeletionMultiplier h s * thetaRenewalDeletionPrefix h s +
          thetaRenewalDeletionMultiplier h (-s) * thetaRenewalDeletionPrefix h (-s)) := by
  rw [thetaRenewalDeletedDenominator_boundary hh, thetaRenewalDeletedDenominator_boundary hh,
    XiC_two_I_mul_eq_thetaLoop, thetaRenewalFullCharge]
  simp only [thetaLoopA, thetaLoopB]
  field_simp
  ring

/-- The boundary term survives at every full-divisor point; no simplicity or axis premise. -/
theorem thetaRenewalDeleted_two_ended_at_divisor {h : ℝ} (hh : 0 ≤ h) {s : ℂ}
    (hz : XiC (2 * I * s) = 0) :
    (1 / 4 + s) * thetaRenewalDeletedDenominator h s +
      (1 / 4 - s) * thetaRenewalDeletedDenominator h (-s) =
      I * (thetaRenewalDeletionMultiplier h (-s) - thetaRenewalDeletionMultiplier h s) *
        thetaRenewalFullCharge s -
      ((1 / 4 : ℂ) ^ 2 - s ^ 2) *
        (thetaRenewalDeletionMultiplier h s * thetaRenewalDeletionPrefix h s +
          thetaRenewalDeletionMultiplier h (-s) * thetaRenewalDeletionPrefix h (-s)) := by
  rw [thetaRenewalDeleted_two_ended_transport hh, hz, mul_zero, zero_add]

end
end RHTower
