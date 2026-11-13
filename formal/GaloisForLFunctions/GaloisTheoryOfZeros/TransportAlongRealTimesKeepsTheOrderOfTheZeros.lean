import GaloisForLFunctions.GaloisTheoryOfZeros.AZeroOfAStripStaysInItsStripWhereTheCosineTermDominates
import GaloisForLFunctions.GaloisTheoryOfZeros.TheMonodromyOverAUnionOfTwoRegionsComesFromTheRegions
import GaloisForLFunctions.GaloisTheoryOfZeros.TheFunctionalEquationIsAMonodromyOfTheHeatCover
import GaloisForLFunctions.GaloisTheoryOfZeros.ConjugationOfTheZerosIsAMonodromyOfTheHeatCover

/-!
# Transport along real times keeps the order of the zeros

For real `t ≥ 1/8` all zeros of `H_t` are real and simple, and `H_t(0) > 0`. Along a segment of
such times the zeros move on the real line without meeting each other or the centre.

**Theorem** (`re_pos_iff_of_lift`, `re_lt_iff_of_lifts`). A lift of zeros along a segment of real
times beyond `1/8` keeps its sign, and two lifts keep their order.

Proof. The real part of a lift is continuous and never zero; the difference of two lifts is
continuous and, by the uniqueness of lifts through simple zeros, never zero unless the lifts agree.

Also: simple joins are invariant under `z ↦ −z`, since `H_τ` is even.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Evenness -/

theorem IsZeroLift.neg {γ : ℝ → ℂ} {b : ℝ} {z : ℝ → ℂ} (h : IsZeroLift γ b z) :
    IsZeroLift γ b fun s => -z s :=
  ⟨h.continuousOn.neg, fun s hs => by rw [complexHeat_neg]; exact h.zero s hs⟩

theorem deriv_complexHeat_neg (τ z : ℂ) :
    deriv (complexHeat τ) (-z) = -deriv (complexHeat τ) z := by
  have h : (fun w => complexHeat τ (-w)) = complexHeat τ := funext (complexHeat_neg τ)
  have h1 := deriv_comp_neg (complexHeat τ) z
  rw [h] at h1
  rw [h1, neg_neg]

/-- Simple joins are invariant under `z ↦ −z`. -/
theorem SimplyJoined.neg {τ z τ' z' : ℂ} (h : SimplyJoined τ z τ' z') :
    SimplyJoined τ (-z) τ' (-z') := by
  obtain ⟨γ, w, hγ, hpos, hw, hs, rfl, rfl, rfl, rfl⟩ := h
  exact ⟨γ, fun s => -w s, hγ, hpos, hw.neg, fun s hs' => by
    show deriv (complexHeat (γ s)) (-w s) ≠ 0
    rw [deriv_complexHeat_neg]
    exact neg_ne_zero.mpr (hs s hs'), rfl, rfl, rfl, rfl⟩

/-- A simple zero at a forward time is joined to itself. -/
theorem SimplyJoined.refl {τ z : ℂ} (hτ : 0 < τ.re) (hz : complexHeat τ z = 0)
    (hs : deriv (complexHeat τ) z ≠ 0) : SimplyJoined τ z τ z :=
  ⟨fun _ => τ, fun _ => z, continuousOn_const, fun _ _ => hτ,
    ⟨continuousOn_const, fun _ _ => hz⟩, fun _ _ => hs, rfl, rfl, rfl, rfl⟩

/-! ## Segments of real times -/

/-- The segment of real times from `t₁` to `t₂`. -/
def timeSeg (t₁ t₂ : ℝ) (s : ℝ) : ℂ := ((t₁ + s * (t₂ - t₁) : ℝ) : ℂ)

theorem timeSeg_zero (t₁ t₂ : ℝ) : timeSeg t₁ t₂ 0 = (t₁ : ℂ) := by
  rw [timeSeg, zero_mul, add_zero]

theorem timeSeg_one (t₁ t₂ : ℝ) : timeSeg t₁ t₂ 1 = (t₂ : ℂ) := by
  rw [timeSeg, one_mul, add_sub_cancel]

theorem eighth_le_of_mem_Icc {t₁ t₂ s : ℝ} (h₁ : 1 / 8 ≤ t₁) (h₂ : 1 / 8 ≤ t₂)
    (hs : s ∈ Icc (0 : ℝ) 1) : 1 / 8 ≤ t₁ + s * (t₂ - t₁) := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h₁),
    mul_nonneg hs.1 (sub_nonneg.mpr h₂)]

theorem isForwardPath_timeSeg {t₁ t₂ : ℝ} (h₁ : 1 / 8 ≤ t₁) (h₂ : 1 / 8 ≤ t₂) :
    IsForwardPath (timeSeg t₁ t₂) :=
  ⟨(Complex.continuous_ofReal.comp
      (by fun_prop : Continuous fun s : ℝ => t₁ + s * (t₂ - t₁))).continuousOn,
    fun s hs => by
      rw [timeSeg, Complex.ofReal_re]
      linarith [eighth_le_of_mem_Icc h₁ h₂ hs],
    fun s hs => ofReal_not_mem_branchTimes_of_eighth_le (eighth_le_of_mem_Icc h₁ h₂ hs)⟩

/-- The zeros at a real time beyond `1/8` are real. -/
theorem im_eq_zero_of_zero {t : ℝ} (ht : 1 / 8 ≤ t) {z : ℂ}
    (hz : complexHeat (t : ℂ) z = 0) : z.im = 0 := by
  rw [complexHeat_ofReal] at hz
  exact (riemannHeat_zeros_real_simple_of_eighth_le ht hz).1

/-- The centre is not a zero at a real time. -/
theorem ne_zero_of_zero_ofReal {t : ℝ} {z : ℂ} (hz : complexHeat (t : ℂ) z = 0) : z ≠ 0 := by
  rintro rfl
  exact im_ne_zero_of_complexHeat_center_eq_zero hz (Complex.ofReal_im t)

/-- The zeros at a real time beyond `1/8` are simple. -/
theorem deriv_ne_zero_of_zero {t : ℝ} (ht : 1 / 8 ≤ t) {z : ℂ}
    (hz : complexHeat (t : ℂ) z = 0) : deriv (complexHeat (t : ℂ)) z ≠ 0 :=
  deriv_complexHeat_ne_zero_of_not_mem_branchTimes (ofReal_not_mem_branchTimes_of_eighth_le ht) hz

/-! ## Lifts along a segment of real times -/

section Lifts

variable {t₁ t₂ : ℝ} {w w' : ℝ → ℂ}

theorem IsZeroLift.im_timeSeg (h₁ : 1 / 8 ≤ t₁) (h₂ : 1 / 8 ≤ t₂)
    (hw : IsZeroLift (timeSeg t₁ t₂) 1 w) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : (w s).im = 0 :=
  im_eq_zero_of_zero (eighth_le_of_mem_Icc h₁ h₂ hs) (hw.zero s hs)

/-- A lift that starts on the positive side ends on the positive side. -/
theorem re_pos_of_lift (h₁ : 1 / 8 ≤ t₁) (h₂ : 1 / 8 ≤ t₂)
    (hw : IsZeroLift (timeSeg t₁ t₂) 1 w) (h0 : 0 < (w 0).re) : 0 < (w 1).re := by
  have hc : ContinuousOn (fun s => -(w s).re) (Icc 0 1) :=
    (Complex.continuous_re.comp_continuousOn hw.continuousOn).neg
  have h := lt_of_continuousOn_avoid (r := 0) hc (by show -(w 0).re < 0; linarith)
    (fun s hs h0' => by
      have hre : (w s).re = 0 := by linarith
      exact ne_zero_of_zero_ofReal (t := t₁ + s * (t₂ - t₁)) (hw.zero s hs)
        (Complex.ext hre (hw.im_timeSeg h₁ h₂ hs)))
  have h' : -(w 1).re < 0 := h
  linarith

/-- Two lifts that start in an order end in the same order. -/
theorem re_lt_of_lifts (h₁ : 1 / 8 ≤ t₁) (h₂ : 1 / 8 ≤ t₂)
    (hw : IsZeroLift (timeSeg t₁ t₂) 1 w) (hw' : IsZeroLift (timeSeg t₁ t₂) 1 w')
    (h0 : (w 0).re < (w' 0).re) : (w 1).re < (w' 1).re := by
  have hγ := isForwardPath_timeSeg h₁ h₂
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hc : ContinuousOn (fun s => (w s).re - (w' s).re) (Icc 0 1) :=
    (Complex.continuous_re.comp_continuousOn hw.continuousOn).sub
      (Complex.continuous_re.comp_continuousOn hw'.continuousOn)
  have h := lt_of_continuousOn_avoid (r := 0) hc (by show (w 0).re - (w' 0).re < 0; linarith)
    (fun s hs heq => by
      have hre : (w s).re = (w' s).re := by linarith
      have hws : w s = w' s :=
        Complex.ext hre (by rw [hw.im_timeSeg h₁ h₂ hs, hw'.im_timeSeg h₁ h₂ hs])
      have T := hw.transports_subPath hs h00
      have T' := hw'.transports_subPath hs h00
      rw [← hws] at T'
      have h1 := (hγ.sub hs h00).transports_unique T T'
      rw [h1] at h0
      exact lt_irrefl _ h0)
  have h' : (w 1).re - (w' 1).re < 0 := h
  linarith

/-- **A lift keeps its sign.** -/
theorem re_pos_iff_of_lift (h₁ : 1 / 8 ≤ t₁) (h₂ : 1 / 8 ≤ t₂)
    (hw : IsZeroLift (timeSeg t₁ t₂) 1 w) : 0 < (w 0).re ↔ 0 < (w 1).re := by
  refine ⟨re_pos_of_lift h₁ h₂ hw, fun h1 => ?_⟩
  by_contra hcon
  push Not at hcon
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hne : w 0 ≠ 0 := ne_zero_of_zero_ofReal (t := t₁ + 0 * (t₂ - t₁)) (hw.zero 0 h00)
  have hlt : (w 0).re < 0 :=
    lt_of_le_of_ne hcon fun h0 => hne (Complex.ext h0 (hw.im_timeSeg h₁ h₂ h00))
  have h2 : 0 < (-(w 1)).re :=
    re_pos_of_lift h₁ h₂ hw.neg (by show 0 < (-(w 0)).re; rw [Complex.neg_re]; linarith)
  rw [Complex.neg_re] at h2
  linarith

/-- **Two lifts keep their order.** -/
theorem re_lt_iff_of_lifts (h₁ : 1 / 8 ≤ t₁) (h₂ : 1 / 8 ≤ t₂)
    (hw : IsZeroLift (timeSeg t₁ t₂) 1 w) (hw' : IsZeroLift (timeSeg t₁ t₂) 1 w') :
    (w 0).re < (w' 0).re ↔ (w 1).re < (w' 1).re := by
  refine ⟨re_lt_of_lifts h₁ h₂ hw hw', fun h1 => ?_⟩
  by_contra hcon
  push Not at hcon
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rcases hcon.lt_or_eq with hlt | heq
  · have h2 := re_lt_of_lifts h₁ h₂ hw' hw hlt
    linarith
  · have hγ := isForwardPath_timeSeg h₁ h₂
    have h0 : w' 0 = w 0 :=
      Complex.ext heq (by rw [hw.im_timeSeg h₁ h₂ h00, hw'.im_timeSeg h₁ h₂ h00])
    have heq1 := IsZeroLift.eqOn hγ.continuousOn hw' hw h0 (fun s hs =>
      deriv_complexHeat_ne_zero_of_not_mem_branchTimes (hγ.simple s hs) (hw'.zero s hs))
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨zero_le_one, le_rfl⟩)
    rw [heq1] at h1
    exact lt_irrefl _ h1

/-- A lift along a segment of real times joins its ends through simple zeros. -/
theorem IsZeroLift.simplyJoined_timeSeg (h₁ : 1 / 8 ≤ t₁) (h₂ : 1 / 8 ≤ t₂)
    (hw : IsZeroLift (timeSeg t₁ t₂) 1 w) : SimplyJoined (t₁ : ℂ) (w 0) (t₂ : ℂ) (w 1) := by
  have h := (isForwardPath_timeSeg h₁ h₂).simplyJoined ⟨w, hw, rfl, rfl⟩
  rwa [timeSeg_zero, timeSeg_one] at h

end Lifts

/-- Every zero at the start of a segment of real times is the start of a lift. -/
theorem exists_lift_starting_at {t₁ t₂ : ℝ} (h₁ : 1 / 8 ≤ t₁) (h₂ : 1 / 8 ≤ t₂) {x : ℂ}
    (hx : complexHeat (t₁ : ℂ) x = 0) : ∃ w, IsZeroLift (timeSeg t₁ t₂) 1 w ∧ w 0 = x := by
  have hγ := isForwardPath_timeSeg h₁ h₂
  exact exists_isZeroLift_of_re_pos hγ.continuousOn hγ.re_pos hγ.simple
    (by rw [timeSeg_zero]; exact hx)

/-- Every zero at the end of a segment of real times is the end of a lift. -/
theorem exists_lift_ending_at {t₁ t₂ : ℝ} (h₁ : 1 / 8 ≤ t₁) (h₂ : 1 / 8 ≤ t₂) {y : ℂ}
    (hy : complexHeat (t₂ : ℂ) y = 0) : ∃ w, IsZeroLift (timeSeg t₁ t₂) 1 w ∧ w 1 = y := by
  have hγ := isForwardPath_timeSeg h₁ h₂
  exact exists_isZeroLift_ending_at hγ.continuousOn hγ.re_pos hγ.simple
    (by rw [timeSeg_one]; exact hy)

end

end GaloisForLFunctions.GaloisTheoryOfZeros
