import GaloisForLFunctions.RHTower.ParabolicMassBlowup

/-!
# The exact orientation defect of a parabolic mass jet

The elementary identity `|u|² − Re(u²) = 2(Im u)²` applied to `u = P(w) e^{-iθ}` turns the
difference between the Hermitian mass `∑ weight·|P(w)|²` and the real part of the oriented jet
`∑ weight·Re(P(w)² e^{-2iθ})` into an explicit sum of squares:

`G − Re M = 2 ∑ weight · [Im(P(w) e^{-iθ})]² ≥ 0`.

For the constant polynomial and the heat orientation `θ = tB/2` this is

`D₁(t) = ∑ e^{-tA}(1 − cos(tB))`,

each summand nonnegative, and the family vanishes at every positive time exactly when every
transverse part `B` vanishes: a single nonzero `B` is detected at `t = π/|B|`.  The Hermitian mass
alone is therefore not the sharp datum; the orientation cap `D ≤ G` is.
-/

open Filter Topology Complex

namespace RHTower

noncomputable section

/-! ## The elementary orientation identity -/

theorem normSq_sub_re_sq (u : ℂ) : ‖u‖ ^ 2 - (u ^ 2).re = 2 * u.im ^ 2 := by
  rw [Complex.sq_abs.symm.trans rfl]
  simp only [Complex.sq_abs, Complex.normSq_apply, pow_two, Complex.mul_re]
  ring

theorem norm_mul_exp_neg_mul_I (z : ℂ) (theta : ℝ) :
    ‖z * Complex.exp (-((theta : ℝ) : ℂ) * Complex.I)‖ = ‖z‖ := by
  rw [norm_mul, Complex.norm_exp]
  simp

/-- **(24.123)** The pointwise orientation identity. -/
theorem orientation_identity (z : ℂ) (theta : ℝ) :
    ‖z‖ ^ 2 - ((z * Complex.exp (-((theta : ℝ) : ℂ) * Complex.I)) ^ 2).re
      = 2 * ((z * Complex.exp (-((theta : ℝ) : ℂ) * Complex.I)).im) ^ 2 := by
  have h := normSq_sub_re_sq (z * Complex.exp (-((theta : ℝ) : ℂ) * Complex.I))
  rwa [norm_mul_exp_neg_mul_I] at h

/-! ## The finite orientation decomposition -/

variable {ι : Type*}

/-- The Hermitian mass of a finite family. -/
def parabolicHermitianMass (s : Finset ι) (weight : ι → ℝ) (P : ι → ℂ) : ℝ :=
  ∑ q ∈ s, weight q * ‖P q‖ ^ 2

/-- The real part of the oriented jet of a finite family. -/
def parabolicOrientedJet (s : Finset ι) (weight : ι → ℝ) (P : ι → ℂ) (theta : ι → ℝ) : ℝ :=
  ∑ q ∈ s, weight q * ((P q * Complex.exp (-((theta q : ℝ) : ℂ) * Complex.I)) ^ 2).re

/-- The orientation defect of a finite family. -/
def parabolicOrientationDefect (s : Finset ι) (weight : ι → ℝ) (P : ι → ℂ) (theta : ι → ℝ) : ℝ :=
  ∑ q ∈ s, 2 * weight q * ((P q * Complex.exp (-((theta q : ℝ) : ℂ) * Complex.I)).im) ^ 2

/-- **(24.123)/(24.125) The exact defect identity.** -/
theorem parabolicHermitianMass_sub_orientedJet (s : Finset ι) (weight : ι → ℝ) (P : ι → ℂ)
    (theta : ι → ℝ) :
    parabolicHermitianMass s weight P - parabolicOrientedJet s weight P theta
      = parabolicOrientationDefect s weight P theta := by
  rw [parabolicHermitianMass, parabolicOrientedJet, parabolicOrientationDefect,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h := orientation_identity (P q) (theta q)
  nlinarith [h]

/-- The defect is a sum of squares. -/
theorem parabolicOrientationDefect_nonneg {s : Finset ι} {weight : ι → ℝ} (P : ι → ℂ)
    (theta : ι → ℝ) (hw : ∀ q ∈ s, 0 ≤ weight q) :
    0 ≤ parabolicOrientationDefect s weight P theta := by
  refine Finset.sum_nonneg fun q hq => ?_
  have := hw q hq
  positivity

/-- **(24.127) The orientation cap.**  The oriented jet never exceeds the Hermitian mass. -/
theorem parabolicOrientedJet_le_hermitianMass {s : Finset ι} {weight : ι → ℝ} (P : ι → ℂ)
    (theta : ι → ℝ) (hw : ∀ q ∈ s, 0 ≤ weight q) :
    parabolicOrientedJet s weight P theta ≤ parabolicHermitianMass s weight P := by
  have hid := parabolicHermitianMass_sub_orientedJet s weight P theta
  have hnn := parabolicOrientationDefect_nonneg P theta hw
  linarith

/-! ## The unfiltered heat defect -/

/-- **(24.126)** The unfiltered orientation defect at heat time `t`. -/
def parabolicHeatDefect (s : Finset ι) (A B : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ q ∈ s, Real.exp (-(t * A q)) * (1 - Real.cos (t * B q))

theorem parabolicHeatDefect_eq_orientationDefect (s : Finset ι) (A B : ι → ℝ) (t : ℝ) :
    parabolicHeatDefect s A B t
      = parabolicOrientationDefect s (fun q => Real.exp (-(t * A q))) (fun _ => 1)
          (fun q => t * B q / 2) := by
  rw [parabolicHeatDefect, parabolicOrientationDefect]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hexp : ((1 : ℂ) * Complex.exp (-((t * B q / 2 : ℝ) : ℂ) * Complex.I)).im
      = -Real.sin (t * B q / 2) := by
    rw [one_mul]
    have hform : -((t * B q / 2 : ℝ) : ℂ) * Complex.I
        = ((-(t * B q / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hform, Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  rw [hexp]
  have hcos : Real.cos (t * B q) = 1 - 2 * Real.sin (t * B q / 2) ^ 2 := by
    have h := Real.cos_sq_half (t * B q)
    have h2 := Real.sin_sq_half_eq (t * B q)
    linarith [h2]
  rw [hcos]
  ring

theorem parabolicHeatDefect_nonneg (s : Finset ι) (A B : ι → ℝ) (t : ℝ) :
    0 ≤ parabolicHeatDefect s A B t := by
  refine Finset.sum_nonneg fun q _ => ?_
  have hcos : Real.cos (t * B q) ≤ 1 := Real.cos_le_one _
  have hexp : (0 : ℝ) < Real.exp (-(t * A q)) := Real.exp_pos _
  nlinarith

theorem parabolicHeatDefect_summand_eq_zero {s : Finset ι} {A B : ι → ℝ} {t : ℝ}
    (h : parabolicHeatDefect s A B t = 0) {q : ι} (hq : q ∈ s) :
    Real.cos (t * B q) = 1 := by
  have hnn : ∀ r ∈ s, 0 ≤ Real.exp (-(t * A r)) * (1 - Real.cos (t * B r)) := by
    intro r _
    have hcos : Real.cos (t * B r) ≤ 1 := Real.cos_le_one _
    have hexp : (0 : ℝ) < Real.exp (-(t * A r)) := Real.exp_pos _
    nlinarith
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h q hq
  have hexp : (0 : ℝ) < Real.exp (-(t * A q)) := Real.exp_pos _
  have := mul_eq_zero.1 hzero
  rcases this with hcase | hcase
  · exact absurd hcase hexp.ne'
  · linarith

/-- **(24.126) The rigidity of the unfiltered defect.**  The heat defect vanishes at every positive
time exactly when every transverse part vanishes. -/
theorem parabolicHeatDefect_eq_zero_iff (s : Finset ι) (A B : ι → ℝ) :
    (∀ t : ℝ, 0 < t → parabolicHeatDefect s A B t = 0) ↔ ∀ q ∈ s, B q = 0 := by
  constructor
  · intro h q hq
    by_contra hB
    have habs : 0 < |B q| := abs_pos.2 hB
    have ht : 0 < Real.pi / |B q| := by positivity
    have hcos := parabolicHeatDefect_summand_eq_zero (h _ ht) hq
    have hval : Real.pi / |B q| * B q = Real.pi ∨ Real.pi / |B q| * B q = -Real.pi := by
      rcases lt_or_gt_of_ne hB with hneg | hpos
      · right
        rw [abs_of_neg hneg]
        field_simp
      · left
        rw [abs_of_pos hpos]
        field_simp
    rcases hval with hv | hv <;> rw [hv] at hcos
    · rw [Real.cos_pi] at hcos
      norm_num at hcos
    · rw [Real.cos_neg, Real.cos_pi] at hcos
      norm_num at hcos
  · intro h t _
    rw [parabolicHeatDefect]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [h q hq, mul_zero, Real.cos_zero]
    ring

/-! ## The parabolic limits of the orbit data -/

/-- **(24.124)** In the parabolic limit the longitudinal gap converges to the real part of the
spectral point. -/
theorem tendsto_parabolic_longitudinal {w : ℂ} {beta : ℝ → ℂ}
    (hbeta : ∀ a : ℝ, beta a ^ 2 = (a : ℂ) ^ 2 + w)
    (hre : ∀ a : ℝ, 0 ≤ (beta a).re) :
    Tendsto (fun a : ℝ => 2 * a * ((beta a).re - a)) atTop (nhds w.re) := by
  have hbase := tendsto_parabolic_remainder hbeta hre
  have hcomp := (Complex.continuous_re.tendsto w).comp hbase
  refine hcomp.congr fun a => ?_
  rw [Function.comp_apply]
  simp [Complex.mul_re, Complex.sub_re]

/-- **(24.124)** In the parabolic limit the transverse part converges to half the imaginary part of
the spectral point. -/
theorem tendsto_parabolic_transverse {w : ℂ} {beta : ℝ → ℂ}
    (hbeta : ∀ a : ℝ, beta a ^ 2 = (a : ℂ) ^ 2 + w)
    (hre : ∀ a : ℝ, 0 ≤ (beta a).re) :
    Tendsto (fun a : ℝ => a * (beta a).im) atTop (nhds (w.im / 2)) := by
  have hbase := tendsto_parabolic_remainder hbeta hre
  have hcomp := (Complex.continuous_im.tendsto w).comp hbase
  have hhalf := hcomp.div_const 2
  refine hhalf.congr fun a => ?_
  rw [Function.comp_apply]
  simp [Complex.mul_im, Complex.sub_im]
  ring

end

end RHTower
