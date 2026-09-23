import GaloisForLFunctions.RHTower.XiDyadicBandReciprocalPhaseAmplification
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinBufferedTail
import GaloisForLFunctions.RHTower.XiEndpointSourceHeightGap
import GaloisForLFunctions.HTGeometry.ScheffeCounting
import GaloisForLFunctions.HTGeometry.ResolventSubordination

/-!
# Poisson--Hilbert Xi phase amplification

The odd two-sided exponential kernel has `L¹` norm exactly one at every positive scale and
physical-frequency multiplier `-i T y / (T² + y²)`.  On a critical-line conjugate zero pair this
rotates the explicit-formula coefficients `-1/(1/2 ± i y)` into a positive summable weight.

Riemann--von Mangoldt supplies at least order `T log T` copies in the dyadic band `(T,2T]`, where
each weight is at least order `1/T`.  The complete weighted divisor therefore has coherent mass
at least order `log T`.  Absolute summability closes the infinite spectral tail, and simultaneous
phase recurrence makes the complete packet cofinally unbounded.

For the CCM--FU/Suzuki first-moment hostile audit this discharges the detector, multiplier, pair
sign, spectral-tail, and amplification burdens.  The remaining no-go weld is solely arithmetic:
transporting the bounded critical-normalized Chebyshev error through this exact kernel to the
completed explicit formula.
-/

open Complex Filter Set Topology MeasureTheory GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Positive response of one Xi copy under the Poisson--Hilbert detector. -/
def xiPoissonHilbertWeight (T : ℝ) (q : XiZeroCopy) : ℝ :=
  let y := |(q.1 : ℂ).im|
  (2 * T * y ^ (2 : ℕ)) / ((T ^ (2 : ℕ) + y ^ (2 : ℕ)) * (1 / 4 + y ^ (2 : ℕ)))

/-- Odd two-sided exponential detector. Its scale changes bandwidth without changing `L¹` norm. -/
def xiPoissonHilbertKernel (T x : ℝ) : ℝ :=
  if 0 ≤ x then (T / 2) * Real.exp (-(T * x))
  else -(T / 2) * Real.exp (T * x)

theorem abs_xiPoissonHilbertKernel {T : ℝ} (hT : 0 < T) (x : ℝ) :
    |xiPoissonHilbertKernel T x| =
      (T / 2) * Real.exp (-(T * |x|)) := by
  rw [xiPoissonHilbertKernel]
  split_ifs with hx
  · rw [abs_of_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le),
      abs_of_nonneg hx]
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ T / 2),
      abs_of_pos (Real.exp_pos _), abs_of_neg hx']
    congr 2
    ring

theorem integrable_xiPoissonHilbertKernel {T : ℝ} (hT : 0 < T) :
    Integrable (xiPoissonHilbertKernel T) := by
  have hdom : Integrable (fun x : ℝ =>
      (T / 2) * (|x| ^ (0 : ℕ) * Real.exp (-T * |x|))) :=
    (HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hT).const_mul (T / 2)
  refine Integrable.mono' hdom ?_ ?_
  · unfold xiPoissonHilbertKernel
    exact (Measurable.ite measurableSet_Ici (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_xiPoissonHilbertKernel hT]
    simp

/-- Exact scale-invariant detector budget. -/
theorem integral_abs_xiPoissonHilbertKernel_eq_one {T : ℝ} (hT : 0 < T) :
    (∫ x : ℝ, |xiPoissonHilbertKernel T x|) = 1 := by
  have hmoment := HTGeometry.integral_abs_evenPow_mul_exp_neg_abs 0 hT
  rw [show (∫ x : ℝ, |xiPoissonHilbertKernel T x|) =
      (T / 2) * ∫ x : ℝ, |x| ^ (2 * 0) * Real.exp (-T * |x|) by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    rw [abs_xiPoissonHilbertKernel hT]
    simp]
  rw [hmoment]
  norm_num
  field_simp [hT.ne']

/-- Physical-frequency multiplier of the odd exponential detector. -/
def xiPoissonHilbertMultiplier (T y : ℝ) : ℂ :=
  -Complex.I * (T * y / (T ^ (2 : ℕ) + y ^ (2 : ℕ)) : ℝ)

/-- Physical Fourier integral of the detector kernel. -/
def xiPoissonHilbertKernelTransform (T y : ℝ) : ℂ :=
  ∫ x : ℝ, (xiPoissonHilbertKernel T x : ℂ) *
    Complex.exp (-(Complex.I * (y : ℂ) * (x : ℂ)))

/-- Exact rational multiplier of the scale-invariant odd exponential detector. -/
theorem xiPoissonHilbertKernelTransform_eq_multiplier {T : ℝ} (hT : 0 < T) (y : ℝ) :
    xiPoissonHilbertKernelTransform T y = xiPoissonHilbertMultiplier T y := by
  let g : ℝ → ℂ := fun x => (xiPoissonHilbertKernel T x : ℂ) *
    Complex.exp (-(Complex.I * (y : ℂ) * (x : ℂ)))
  have hg : Integrable g := by
    apply (integrable_xiPoissonHilbertKernel hT).ofReal.mul_bdd (c := 1)
    · exact (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable
    · filter_upwards with x
      rw [Complex.norm_exp]
      simp
  have hsplit :
      (∫ x : ℝ, g x) = (∫ x in Iic (0 : ℝ), g x) +
        ∫ x in Ioi (0 : ℝ), g x := by
    rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    exact setIntegral_union (by simp [Set.disjoint_left]) measurableSet_Ioi
      hg.integrableOn hg.integrableOn
  let cp : ℂ := (T : ℂ) + Complex.I * (y : ℂ)
  let cm : ℂ := (T : ℂ) - Complex.I * (y : ℂ)
  have hcp : 0 < cp.re := by simp [cp, hT]
  have hcm : 0 < cm.re := by simp [cm, hT]
  have hpos :
      (∫ x in Ioi (0 : ℝ), g x) = (T / 2 : ℝ) / cp := by
    have hpoint : ∀ x ∈ Ioi (0 : ℝ),
        g x = ((T / 2 : ℝ) : ℂ) * Complex.exp (-(cp * (x : ℂ))) := by
      intro x hx
      dsimp only [g]
      rw [xiPoissonHilbertKernel, if_pos hx.le]
      push_cast
      rw [show (T : ℂ) / 2 * Complex.exp (-((T : ℂ) * (x : ℂ))) *
          Complex.exp (-(Complex.I * (y : ℂ) * (x : ℂ))) =
        (T : ℂ) / 2 * (Complex.exp (-((T : ℂ) * (x : ℂ))) *
          Complex.exp (-(Complex.I * (y : ℂ) * (x : ℂ)))) by ring]
      rw [← Complex.exp_add]
      congr 1
      dsimp only [cp]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint,
      integral_const_mul,
      GaloisForLFunctions.HTGeometry.integral_Ioi_cexp_neg hcp]
    ring
  have hneg :
      (∫ x in Iic (0 : ℝ), g x) = -(T / 2 : ℝ) / cm := by
    have hreflect := integral_comp_neg_Ioi (0 : ℝ) g
    simp only [neg_zero] at hreflect
    rw [← hreflect]
    have hpoint : ∀ x ∈ Ioi (0 : ℝ),
        g (-x) = ((-(T / 2) : ℝ) : ℂ) * Complex.exp (-(cm * (x : ℂ))) := by
      intro x hx
      have hx0 : 0 < x := hx
      have hnx : ¬ 0 ≤ -x := by linarith
      dsimp only [g]
      rw [xiPoissonHilbertKernel, if_neg hnx]
      push_cast
      rw [show (-((T : ℂ) / 2)) * Complex.exp ((T : ℂ) * -(x : ℂ)) *
          Complex.exp (-(Complex.I * (y : ℂ) * -(x : ℂ))) =
        (-((T : ℂ) / 2)) * (Complex.exp ((T : ℂ) * -(x : ℂ)) *
          Complex.exp (-(Complex.I * (y : ℂ) * -(x : ℂ)))) by ring]
      rw [← Complex.exp_add]
      congr 1
      dsimp only [cm]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpoint,
      integral_const_mul,
      GaloisForLFunctions.HTGeometry.integral_Ioi_cexp_neg hcm]
    push_cast
    ring
  rw [xiPoissonHilbertKernelTransform, show (fun x =>
      (xiPoissonHilbertKernel T x : ℂ) *
        Complex.exp (-(Complex.I * (y : ℂ) * (x : ℂ)))) = g by rfl,
    hsplit, hneg, hpos, xiPoissonHilbertMultiplier]
  have hcp0 : cp ≠ 0 := ne_zero_of_re_pos hcp
  have hcm0 : cm ≠ 0 := ne_zero_of_re_pos hcm
  have hTy : T ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 := by positivity
  have hTyC : (((T ^ (2 : ℕ) + y ^ (2 : ℕ) : ℝ) : ℂ)) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hTy
  have hTyC' : (T : ℂ) ^ (2 : ℕ) + (y : ℂ) ^ (2 : ℕ) ≠ 0 := by
    exact_mod_cast hTy
  dsimp only [cp, cm] at hcp0 hcm0 ⊢
  push_cast
  field_simp [hcp0, hcm0, hTy, hTyC, hTyC']
  ring_nf
  rw [show Complex.I ^ (3 : ℕ) = -Complex.I by
    rw [pow_succ, Complex.I_sq]
    ring]
  ring

/-- On a critical-line conjugate pair, the detector rotates the two explicit-formula residues
into one positive Poisson--Hilbert weight. -/
theorem xiPoissonHilbertMultiplier_criticalPair {T y : ℝ}
    (hT : 0 < T) (hy : 0 < y) :
    -(1 / 2 + Complex.I * (y : ℂ))⁻¹ * xiPoissonHilbertMultiplier T y +
        -(1 / 2 - Complex.I * (y : ℂ))⁻¹ * xiPoissonHilbertMultiplier T (-y) =
      ((2 * T * y ^ (2 : ℕ)) /
        ((T ^ (2 : ℕ) + y ^ (2 : ℕ)) * (1 / 4 + y ^ (2 : ℕ))) : ℝ) := by
  have hTy : T ^ (2 : ℕ) + y ^ (2 : ℕ) ≠ 0 := by positivity
  have hyc : (1 / 2 + Complex.I * (y : ℂ)) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    exact hy.ne' him
  have hyc' : (1 / 2 - Complex.I * (y : ℂ)) ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    norm_num at him
    nlinarith
  have hdenY : 1 / 4 + y ^ (2 : ℕ) ≠ 0 := by positivity
  have hinvPlus :
      (1 / 2 + Complex.I * (y : ℂ))⁻¹ =
        (1 / 2 - Complex.I * (y : ℂ)) / (1 / 4 + y ^ (2 : ℕ) : ℝ) := by
    apply inv_eq_of_mul_eq_one_right
    have hprod :
        (1 / 2 + Complex.I * (y : ℂ)) *
            (1 / 2 - Complex.I * (y : ℂ)) =
          ((1 / 4 + y ^ (2 : ℕ) : ℝ) : ℂ) := by
      ring_nf
      rw [Complex.I_sq]
      norm_num
    rw [← mul_div_assoc, hprod, div_self (Complex.ofReal_ne_zero.mpr hdenY)]
  have hinvMinus :
      (1 / 2 - Complex.I * (y : ℂ))⁻¹ =
        (1 / 2 + Complex.I * (y : ℂ)) / (1 / 4 + y ^ (2 : ℕ) : ℝ) := by
    apply inv_eq_of_mul_eq_one_right
    have hprod :
        (1 / 2 - Complex.I * (y : ℂ)) *
            (1 / 2 + Complex.I * (y : ℂ)) =
          ((1 / 4 + y ^ (2 : ℕ) : ℝ) : ℂ) := by
      ring_nf
      rw [Complex.I_sq]
      norm_num
    rw [← mul_div_assoc, hprod, div_self (Complex.ofReal_ne_zero.mpr hdenY)]
  have hmultNeg :
      xiPoissonHilbertMultiplier T (-y) =
        Complex.I * (T * y / (T ^ (2 : ℕ) + y ^ (2 : ℕ)) : ℝ) := by
    rw [xiPoissonHilbertMultiplier]
    push_cast
    field_simp [hTy]
  rw [hinvPlus, hinvMinus, hmultNeg, xiPoissonHilbertMultiplier]
  push_cast
  field_simp [hTy, hdenY]
  have hparen :
      (1 : ℂ) - 2 * Complex.I * (y : ℂ) +
          -(1 + 2 * Complex.I * (y : ℂ)) =
        -4 * Complex.I * (y : ℂ) := by ring
  rw [hparen]
  ring_nf
  rw [Complex.I_sq]
  ring

theorem xiPoissonHilbertWeight_nonneg {T : ℝ} (hT : 0 ≤ T) (q : XiZeroCopy) :
    0 ≤ xiPoissonHilbertWeight T q := by
  rw [xiPoissonHilbertWeight]
  positivity

theorem xiPoissonHilbertWeight_le_inv_sq {T : ℝ} (hT : 0 < T) (q : XiZeroCopy) :
    xiPoissonHilbertWeight T q ≤
      2 * T * (1 / |(q.1 : ℂ).im| ^ (2 : ℕ)) := by
  let y := |(q.1 : ℂ).im|
  have hy : 0 < y := abs_pos.mpr (xiSupport_im_ne_zero q.1)
  have hden1 : 0 < T ^ (2 : ℕ) + y ^ (2 : ℕ) := by positivity
  have hden2 : 0 < 1 / 4 + y ^ (2 : ℕ) := by positivity
  change (2 * T * y ^ (2 : ℕ)) / ((T ^ (2 : ℕ) + y ^ (2 : ℕ)) * (1 / 4 + y ^ (2 : ℕ))) ≤
    2 * T * (1 / y ^ (2 : ℕ))
  rw [div_le_iff₀ (mul_pos hden1 hden2)]
  field_simp [hy.ne']
  nlinarith [sq_nonneg T, sq_nonneg y]

theorem summable_xiPoissonHilbertWeight {T : ℝ} (hT : 0 < T) :
    Summable (xiPoissonHilbertWeight T) := by
  have hmajor :=
    RHTower.Sieve.summable_xiZeroCopy_one_div_abs_im_sq.mul_left (2 * T)
  exact Summable.of_nonneg_of_le
    (fun q => xiPoissonHilbertWeight_nonneg hT.le q)
    (fun q => xiPoissonHilbertWeight_le_inv_sq hT q) hmajor

/-- Total coherent response of the complete multiplicity-aware Xi divisor. -/
def xiPoissonHilbertMass (T : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiPoissonHilbertWeight T q

/-- Complete recurrent Poisson--Hilbert Xi packet. -/
def xiPoissonHilbertPhase (T t : ℝ) : ℝ :=
  ∑' q : XiZeroCopy, xiPoissonHilbertWeight T q *
    (GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t).re

theorem summable_xiPoissonHilbertPhase {T : ℝ} (hT : 0 < T) (t : ℝ) :
    Summable (fun q : XiZeroCopy => xiPoissonHilbertWeight T q *
      (GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t).re) := by
  apply (summable_xiPoissonHilbertWeight hT).of_norm_bounded
  intro q
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (xiPoissonHilbertWeight_nonneg hT.le q)]
  calc
    xiPoissonHilbertWeight T q *
        |(GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t).re| ≤
      xiPoissonHilbertWeight T q *
        ‖GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t‖ := by
          exact mul_le_mul_of_nonneg_left
            (Complex.abs_re_le_norm
              (GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t))
            (xiPoissonHilbertWeight_nonneg hT.le q)
    _ = xiPoissonHilbertWeight T q := by
      rw [GaloisForLFunctions.norm_bohrChar, mul_one]

theorem xiPoissonHilbertWeight_band_lower {T : ℝ} (hT : 0 < T)
    {q : XiZeroCopy} (hq : q ∈ xiCopiesBand T (2 * T)) :
    1 / (5 * T) ≤ xiPoissonHilbertWeight T q := by
  let y := |(q.1 : ℂ).im|
  have hmem := mem_xiCopiesBand.mp hq
  have hyT : T < y := hmem.1
  have hy2T : y ≤ 2 * T := hmem.2
  have hy : 0 < y := hT.trans hyT
  have hy_sq_lower : T ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by nlinarith
  have hy_sq_upper : y ^ (2 : ℕ) ≤ 4 * T ^ (2 : ℕ) := by nlinarith
  have hy_one : 1 < y := xiZeroCopy_one_lt_abs_im q
  have hfactor : 1 ≤ 2 * y ^ (2 : ℕ) / (1 / 4 + y ^ (2 : ℕ)) := by
    rw [le_div_iff₀ (by positivity : 0 < (1 / 4 : ℝ) + y ^ (2 : ℕ))]
    nlinarith
  have hpoisson : 1 / (5 * T) ≤ T / (T ^ (2 : ℕ) + y ^ (2 : ℕ)) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 5 * T)
      (by positivity : 0 < T ^ (2 : ℕ) + y ^ (2 : ℕ))]
    nlinarith
  rw [xiPoissonHilbertWeight]
  calc
    1 / (5 * T) ≤ T / (T ^ (2 : ℕ) + y ^ (2 : ℕ)) := hpoisson
    _ ≤ (T / (T ^ (2 : ℕ) + y ^ (2 : ℕ))) *
        (2 * y ^ (2 : ℕ) / (1 / 4 + y ^ (2 : ℕ))) := by
          exact le_mul_of_one_le_right (by positivity) hfactor
    _ = (2 * T * y ^ (2 : ℕ)) /
        ((T ^ (2 : ℕ) + y ^ (2 : ℕ)) * (1 / 4 + y ^ (2 : ℕ))) := by
          field_simp

/-- Coherent mass of the complete rational detector grows at least logarithmically. -/
theorem eventually_xiPoissonHilbertMass_log_lower :
    ∀ᶠ T : ℝ in atTop,
      (1 / (20 * Real.pi)) * Real.log T ≤ xiPoissonHilbertMass T := by
  filter_upwards [eventually_card_xiCopiesBand_mul_two_lower,
    eventually_ge_atTop (4 : ℝ)] with T hcard hT4
  have hT : 0 < T := by linarith
  have hsum := summable_xiPoissonHilbertWeight hT
  have hfin :
      ∑ q ∈ xiCopiesBand T (2 * T), 1 / (5 * T) ≤
        ∑ q ∈ xiCopiesBand T (2 * T), xiPoissonHilbertWeight T q := by
    exact Finset.sum_le_sum (fun q hq => xiPoissonHilbertWeight_band_lower hT hq)
  have hpartial :
      ∑ q ∈ xiCopiesBand T (2 * T), xiPoissonHilbertWeight T q ≤
        xiPoissonHilbertMass T := by
    rw [xiPoissonHilbertMass]
    exact hsum.sum_le_tsum _ (fun q _ => xiPoissonHilbertWeight_nonneg hT.le q)
  calc
    (1 / (20 * Real.pi)) * Real.log T =
        ((1 / (4 * Real.pi)) * (T * Real.log T)) * (1 / (5 * T)) := by
          field_simp [hT.ne']
          ring
    _ ≤ ((xiCopiesBand T (2 * T)).card : ℝ) * (1 / (5 * T)) := by
      exact mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = ∑ q ∈ xiCopiesBand T (2 * T), 1 / (5 * T) := by simp
    _ ≤ ∑ q ∈ xiCopiesBand T (2 * T), xiPoissonHilbertWeight T q := hfin
    _ ≤ xiPoissonHilbertMass T := hpartial

/-- Complete summable packet returns cofinally to more than half of its coherent mass. -/
theorem exists_xiPoissonHilbertPhase_gt_half_mass {T : ℝ} (hT : 0 < T)
    (hMass : 0 < xiPoissonHilbertMass T) (L : ℝ) :
    ∃ t : ℝ, L ≤ t ∧
      xiPoissonHilbertMass T / 2 < xiPoissonHilbertPhase T t := by
  let w : XiZeroCopy → ℝ := xiPoissonHilbertWeight T
  have hw0 : ∀ q, 0 ≤ w q := fun q => xiPoissonHilbertWeight_nonneg hT.le q
  have hwsum : Summable w := summable_xiPoissonHilbertWeight hT
  have hmassEq : ∑' q, w q = xiPoissonHilbertMass T := rfl
  obtain ⟨F, htail⟩ :=
    exists_finset_tsum_compl_lt hwsum.hasSum
      (show 0 < xiPoissonHilbertMass T / 8 by positivity)
  let omega : {q : XiZeroCopy // q ∈ F} → ℝ :=
    fun q => |(q.1.1 : ℂ).im|
  obtain ⟨t, htL, hrec⟩ :=
    exists_simultaneous_phase_recurrence omega
      (ε := (1 / 4 : ℝ)) (by norm_num) L
  refine ⟨t, htL, ?_⟩
  let p : XiZeroCopy → ℝ := fun q =>
    w q * (GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t).re
  have hpsum : Summable p := by
    simpa only [p, w] using summable_xiPoissonHilbertPhase hT t
  have hhead :
      (3 / 4 : ℝ) * ∑ q ∈ F, w q ≤ ∑ q ∈ F, p q := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    have habs := Complex.abs_re_le_norm
      (GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t - 1)
    have hnorm := hrec ⟨q, hq⟩
    have hreal :
        (GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t - 1).re =
          (GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t).re - 1 := by simp
    rw [hreal] at habs
    have hre : (3 / 4 : ℝ) ≤
        (GaloisForLFunctions.bohrChar |(q.1 : ℂ).im| t).re := by
      have := neg_le_of_abs_le (habs.trans hnorm)
      linarith
    dsimp only [p]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hre (hw0 q)
  let tailMass : ℝ := ∑' q : ↑((↑F : Set XiZeroCopy)ᶜ), w q
  let tailPhase : ℝ := ∑' q : ↑((↑F : Set XiZeroCopy)ᶜ), p q
  have htailPhase : -tailMass ≤ tailPhase := by
    dsimp only [tailMass, tailPhase]
    rw [← tsum_neg]
    apply Summable.tsum_le_tsum
    · intro q
      have hre : (-1 : ℝ) ≤
          (GaloisForLFunctions.bohrChar |(q.1.1 : ℂ).im| t).re := by
        have habs := Complex.abs_re_le_norm
          (GaloisForLFunctions.bohrChar |(q.1.1 : ℂ).im| t)
        rw [GaloisForLFunctions.norm_bohrChar] at habs
        exact neg_le_of_abs_le habs
      dsimp only [p]
      have := mul_le_mul_of_nonneg_left hre (hw0 q.1)
      linarith
    · exact (hwsum.subtype _).neg
    · exact hpsum.subtype _
  have hmassSplit :
      (∑ q ∈ F, w q) + tailMass = xiPoissonHilbertMass T := by
    have hsplit := hwsum.sum_add_tsum_compl (s := F)
    rw [hmassEq] at hsplit
    exact hsplit
  have hphaseSplit :
      (∑ q ∈ F, p q) + tailPhase = xiPoissonHilbertPhase T t := by
    have hsplit := hpsum.sum_add_tsum_compl (s := F)
    change (∑ q ∈ F, p q) + tailPhase = ∑' q, p q
    rw [hsplit]
  have htail' : tailMass < xiPoissonHilbertMass T / 8 := by
    exact htail
  rw [← hphaseSplit]
  nlinarith

/-- Scale-invariant rational Xi detector has arbitrarily large excursions arbitrarily late. -/
theorem xiPoissonHilbertPhase_cofinally_unbounded :
    ∀ C L : ℝ, ∃ T t : ℝ,
      0 < T ∧ L ≤ t ∧ C < xiPoissonHilbertPhase T t := by
  intro C L
  have hlog : ∀ᶠ T : ℝ in atTop,
      80 * Real.pi * |C| + 1 ≤ Real.log T :=
    Real.tendsto_log_atTop.eventually_ge_atTop (80 * Real.pi * |C| + 1)
  have hlarge : ∀ᶠ T : ℝ in atTop,
      0 < T ∧ 0 < xiPoissonHilbertMass T ∧
        2 * C < xiPoissonHilbertMass T := by
    filter_upwards [eventually_xiPoissonHilbertMass_log_lower,
      hlog, eventually_ge_atTop (4 : ℝ)] with T hmass hlogT hT4
    have hT : 0 < T := by linarith
    have hpi : 0 < Real.pi := Real.pi_pos
    have hC : 2 * C < (1 / (20 * Real.pi)) * Real.log T := by
      have habsC : C ≤ |C| := le_abs_self C
      calc
        2 * C ≤ 2 * |C| := by linarith
        _ < 4 * |C| + 1 / (20 * Real.pi) := by
          have hinv : 0 < 1 / (20 * Real.pi) := by positivity
          nlinarith [abs_nonneg C]
        _ = (1 / (20 * Real.pi)) * (80 * Real.pi * |C| + 1) := by
          field_simp
          ring
        _ ≤ (1 / (20 * Real.pi)) * Real.log T := by
          exact mul_le_mul_of_nonneg_left hlogT (by positivity)
    have hlog0 : 0 < Real.log T := Real.log_pos (by linarith)
    have hmass0 : 0 < xiPoissonHilbertMass T :=
      (mul_pos (by positivity) hlog0).trans_le hmass
    exact ⟨hT, hmass0, hC.trans_le hmass⟩
  obtain ⟨T, hT, hmass0, hmass⟩ := hlarge.exists
  obtain ⟨t, htL, ht⟩ :=
    exists_xiPoissonHilbertPhase_gt_half_mass hT hmass0 L
  exact ⟨T, t, hT, htL, by linarith⟩

end

end RHTower
