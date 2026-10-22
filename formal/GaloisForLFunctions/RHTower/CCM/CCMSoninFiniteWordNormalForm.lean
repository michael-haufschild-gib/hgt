import GaloisForLFunctions.RHTower.SoninEulerCrossShellOverlap
import GaloisForLFunctions.RHTower.SoninCalkinNormBound

/-!
# Finite-word normal forms for CCM Sonin Gram operators

This module proves a complete multiplicative normal form for every nonempty finite word of
even-Sonin quadratic Gram corners.  A general two-polarization window is encoded by a ceiling,
floor, and multiplicative displacement.  Products intersect the current shell with the
inverse-dilated next shell, multiply the displacements, and normalize against the central Sonin
complement.

The recursion has an exact zero/live dichotomy.  On the genuine CCM Gram operators, a finite word
is compact if and only if the canonical overlap state is zero.  Every live state is noncompact and
represents a partial isometry in the Calkin algebra.  No composability relation between adjacent
Gram factors is assumed.
-/

noncomputable section


namespace RHTower


open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- Physical branch of a general Sonin window translation. -/
def evenPhysicalWindowTranslation (a C F x : ℝ) (hx : 0 < x) :
    evenSubspace →L[Complex] evenSubspace :=
  (evenIndicatorCutoff C - evenIndicatorCutoff F) *
    evenDilationCLM x hx * (1 - evenIndicatorCutoff a)

/-- Fourier branch paired with a physical window translation. -/
def evenFourierWindowTranslation (a C F x : ℝ) (hx : 0 < x) :
    evenSubspace →L[Complex] evenSubspace :=
  (evenFourierCutoff C - evenFourierCutoff F) *
    evenDilationCLM x⁻¹ (inv_pos.mpr hx) * (1 - evenFourierCutoff a)

/-- Two-polarization Sonin window translation. -/
def evenSoninWindowTranslation (a C F x : ℝ) (hx : 0 < x) :
    evenSubspace →L[Complex] evenSubspace :=
  evenPhysicalWindowTranslation a C F x hx +
    evenFourierWindowTranslation a C F x hx

/-- Ceiling of the intersection of a window with an inverse-dilated window. -/
def soninWindowComposeCeiling (C₁ x C₂ : ℝ) : ℝ := min C₁ (x⁻¹ * C₂)

/-- Floor of the intersection, clamped to its ceiling so disjoint windows give zero. -/
def soninWindowComposeFloor (C₁ F₁ x C₂ F₂ : ℝ) : ℝ :=
  min (max F₁ (x⁻¹ * F₂)) (soninWindowComposeCeiling C₁ x C₂)

/-- Exact multiplication law for general physical Sonin windows. -/
theorem evenPhysicalWindowTranslation_mul
    (a C₁ F₁ x C₂ F₂ y : ℝ)
    (haF₂ : a ≤ F₂) (hF₁C₁ : F₁ ≤ C₁) (hF₂C₂ : F₂ ≤ C₂)
    (hx : 0 < x) (hy : 0 < y) :
    evenPhysicalWindowTranslation a C₁ F₁ x hx *
        evenPhysicalWindowTranslation a C₂ F₂ y hy =
      evenPhysicalWindowTranslation a
        (soninWindowComposeCeiling C₁ x C₂)
        (soninWindowComposeFloor C₁ F₁ x C₂ F₂)
        (x * y) (mul_pos hx hy) := by
  let A := evenIndicatorCutoff a
  let AC₁ := evenIndicatorCutoff C₁
  let AF₁ := evenIndicatorCutoff F₁
  let AC₂ := evenIndicatorCutoff C₂
  let AF₂ := evenIndicatorCutoff F₂
  let AXC₂ := evenIndicatorCutoff (x⁻¹ * C₂)
  let AXF₂ := evenIndicatorCutoff (x⁻¹ * F₂)
  let Ux := evenDilationCLM x hx
  let Uy := evenDilationCLM y hy
  let Uxy := evenDilationCLM (x * y) (mul_pos hx hy)
  have haC₂ : a ≤ C₂ := haF₂.trans hF₂C₂
  have hE : (1 - A) * (AC₂ - AF₂) = AC₂ - AF₂ :=
    evenIndicatorCutoff_complement_shellProduct C₂ F₂ a haF₂ haC₂
  have hmove : Ux * (AC₂ - AF₂) = (AXC₂ - AXF₂) * Ux := by
    have hC := evenDilationCLM_mul_evenIndicatorCutoff C₂ x hx
    have hF := evenDilationCLM_mul_evenIndicatorCutoff F₂ x hx
    change Ux * AC₂ = AXC₂ * Ux at hC
    change Ux * AF₂ = AXF₂ * Ux at hF
    rw [mul_sub, hC, hF, sub_mul]
  have hcomp : Ux * Uy = Uxy := evenDilationCLM_mul x y hx hy
  have hscaled : x⁻¹ * F₂ ≤ x⁻¹ * C₂ :=
    mul_le_mul_of_nonneg_left hF₂C₂ (inv_pos.mpr hx).le
  have hshell : (AC₁ - AF₁) * (AXC₂ - AXF₂) =
      evenIndicatorCutoff (soninWindowComposeCeiling C₁ x C₂) -
        evenIndicatorCutoff (soninWindowComposeFloor C₁ F₁ x C₂ F₂) := by
    simpa [AC₁, AF₁, AXC₂, AXF₂, soninWindowComposeCeiling,
      soninWindowComposeFloor] using
      evenIndicatorCutoff_generalShellProduct F₁ C₁ (x⁻¹ * F₂) (x⁻¹ * C₂)
        hF₁C₁ hscaled
  change (AC₁ - AF₁) * Ux * (1 - A) * ((AC₂ - AF₂) * Uy * (1 - A)) = _
  change _ =
    (evenIndicatorCutoff (soninWindowComposeCeiling C₁ x C₂) -
      evenIndicatorCutoff (soninWindowComposeFloor C₁ F₁ x C₂ F₂)) *
        Uxy * (1 - A)
  calc
    (AC₁ - AF₁) * Ux * (1 - A) * ((AC₂ - AF₂) * Uy * (1 - A)) =
        (AC₁ - AF₁) * Ux * ((1 - A) * (AC₂ - AF₂)) *
          (Uy * (1 - A)) := by noncomm_ring
    _ = (AC₁ - AF₁) * (Ux * (AC₂ - AF₂)) * (Uy * (1 - A)) := by
      rw [hE]
      noncomm_ring
    _ = (AC₁ - AF₁) * ((AXC₂ - AXF₂) * Ux) * (Uy * (1 - A)) := by
      rw [hmove]
    _ = ((AC₁ - AF₁) * (AXC₂ - AXF₂)) * (Ux * Uy) * (1 - A) := by
      noncomm_ring
    _ = _ := by rw [hshell, hcomp]

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- Exact multiplication law for general Fourier Sonin windows. -/
theorem evenFourierWindowTranslation_mul
    (a C₁ F₁ x C₂ F₂ y : ℝ)
    (haF₂ : a ≤ F₂) (hF₁C₁ : F₁ ≤ C₁) (hF₂C₂ : F₂ ≤ C₂)
    (hx : 0 < x) (hy : 0 < y) :
    evenFourierWindowTranslation a C₁ F₁ x hx *
        evenFourierWindowTranslation a C₂ F₂ y hy =
      evenFourierWindowTranslation a
        (soninWindowComposeCeiling C₁ x C₂)
        (soninWindowComposeFloor C₁ F₁ x C₂ F₂)
        (x * y) (mul_pos hx hy) := by
  let R := evenFourierCutoff a
  let RC₁ := evenFourierCutoff C₁
  let RF₁ := evenFourierCutoff F₁
  let RC₂ := evenFourierCutoff C₂
  let RF₂ := evenFourierCutoff F₂
  let RXC₂ := evenFourierCutoff (x⁻¹ * C₂)
  let RXF₂ := evenFourierCutoff (x⁻¹ * F₂)
  let Ux := evenDilationCLM x⁻¹ (inv_pos.mpr hx)
  let Uy := evenDilationCLM y⁻¹ (inv_pos.mpr hy)
  let Uxy := evenDilationCLM (x * y)⁻¹ (inv_pos.mpr (mul_pos hx hy))
  have haC₂ : a ≤ C₂ := haF₂.trans hF₂C₂
  have hE : (1 - R) * (RC₂ - RF₂) = RC₂ - RF₂ :=
    evenFourierCutoff_complement_shellProduct C₂ F₂ a haF₂ haC₂
  have hmove : Ux * (RC₂ - RF₂) = (RXC₂ - RXF₂) * Ux := by
    have hC := evenDilationCLM_mul_evenFourierCutoff C₂ x⁻¹
      (inv_pos.mpr hx)
    have hF := evenDilationCLM_mul_evenFourierCutoff F₂ x⁻¹
      (inv_pos.mpr hx)
    change Ux * RC₂ = RXC₂ * Ux at hC
    change Ux * RF₂ = RXF₂ * Ux at hF
    rw [mul_sub, hC, hF, sub_mul]
  have hcomp : Ux * Uy = Uxy := by
    have h := evenDilationCLM_mul x⁻¹ y⁻¹ (inv_pos.mpr hx) (inv_pos.mpr hy)
    have hscale : x⁻¹ * y⁻¹ = (x * y)⁻¹ := by field_simp
    change Ux * Uy = Uxy
    rw [h]
    congr 1
  have hscaled : x⁻¹ * F₂ ≤ x⁻¹ * C₂ :=
    mul_le_mul_of_nonneg_left hF₂C₂ (inv_pos.mpr hx).le
  have hshell : (RC₁ - RF₁) * (RXC₂ - RXF₂) =
      evenFourierCutoff (soninWindowComposeCeiling C₁ x C₂) -
        evenFourierCutoff (soninWindowComposeFloor C₁ F₁ x C₂ F₂) := by
    simpa [RC₁, RF₁, RXC₂, RXF₂, soninWindowComposeCeiling,
      soninWindowComposeFloor] using
      evenFourierCutoff_generalShellProduct F₁ C₁ (x⁻¹ * F₂) (x⁻¹ * C₂)
        hF₁C₁ hscaled
  change (RC₁ - RF₁) * Ux * (1 - R) * ((RC₂ - RF₂) * Uy * (1 - R)) = _
  change _ =
    (evenFourierCutoff (soninWindowComposeCeiling C₁ x C₂) -
      evenFourierCutoff (soninWindowComposeFloor C₁ F₁ x C₂ F₂)) *
        Uxy * (1 - R)
  calc
    (RC₁ - RF₁) * Ux * (1 - R) * ((RC₂ - RF₂) * Uy * (1 - R)) =
        (RC₁ - RF₁) * Ux * ((1 - R) * (RC₂ - RF₂)) *
          (Uy * (1 - R)) := by noncomm_ring
    _ = (RC₁ - RF₁) * (Ux * (RC₂ - RF₂)) * (Uy * (1 - R)) := by
      rw [hE]
      noncomm_ring
    _ = (RC₁ - RF₁) * ((RXC₂ - RXF₂) * Ux) * (Uy * (1 - R)) := by
      rw [hmove]
    _ = ((RC₁ - RF₁) * (RXC₂ - RXF₂)) * (Ux * Uy) * (1 - R) := by
      noncomm_ring
    _ = _ := by rw [hshell, hcomp]

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- General two-polarization windows are closed under multiplication modulo compacts. -/
theorem evenSoninWindowTranslation_mul_compactEq
    (a C₁ F₁ x C₂ F₂ y : ℝ)
    (ha : 0 < a) (haF₁ : a ≤ F₁) (haF₂ : a ≤ F₂)
    (hF₁C₁ : F₁ ≤ C₁) (hF₂C₂ : F₂ ≤ C₂)
    (hx : 0 < x) (hy : 0 < y) :
    evenSoninWindowTranslation a C₁ F₁ x hx *
        evenSoninWindowTranslation a C₂ F₂ y hy =ₖ
      evenSoninWindowTranslation a
        (soninWindowComposeCeiling C₁ x C₂)
        (soninWindowComposeFloor C₁ F₁ x C₂ F₂)
        (x * y) (mul_pos hx hy) := by
  have hC₁ : 0 < C₁ := lt_of_lt_of_le ha (haF₁.trans hF₁C₁)
  have hF₁ : 0 < F₁ := lt_of_lt_of_le ha haF₁
  have hPP := CompactOperatorEq.of_eq
    (evenPhysicalWindowTranslation_mul a C₁ F₁ x C₂ F₂ y
      haF₂ hF₁C₁ hF₂C₂ hx hy)
  have hFF := CompactOperatorEq.of_eq
    (evenFourierWindowTranslation_mul a C₁ F₁ x C₂ F₂ y
      haF₂ hF₁C₁ hF₂C₂ hx hy)
  have hPF : evenPhysicalWindowTranslation a C₁ F₁ x hx *
      evenFourierWindowTranslation a C₂ F₂ y hy =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact (by
      dsimp only [evenPhysicalWindowTranslation, evenFourierWindowTranslation]
      exact isCompactOperator_physicalWindow_mul_fourierWindow
        a C₁ F₁ C₂ F₂ x y⁻¹ ha hC₁ hF₁ hx (inv_pos.mpr hy))
  have hFP : evenFourierWindowTranslation a C₁ F₁ x hx *
      evenPhysicalWindowTranslation a C₂ F₂ y hy =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact (by
      dsimp only [evenPhysicalWindowTranslation, evenFourierWindowTranslation]
      exact isCompactOperator_fourierWindow_mul_physicalWindow
        a C₁ F₁ C₂ F₂ x⁻¹ y ha hC₁ hF₁ (inv_pos.mpr hx) hy)
  have hsum := CompactOperatorEq.add
    (CompactOperatorEq.add hPP hPF) (CompactOperatorEq.add hFP hFF)
  dsimp only [evenSoninWindowTranslation]
  simpa only [mul_add, add_mul, add_zero, zero_add, add_assoc,
    add_left_comm, add_comm] using hsum

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- The central Sonin complement raises a window floor by the inverse displacement cutoff. -/
def soninWindowNormalizedFloor (a C F x : ℝ) : ℝ :=
  min (max F (x⁻¹ * a)) C

/-- Exact physical normalization against the trailing Sonin complement. -/
theorem evenPhysicalWindowTranslation_normalize
    (a C F x : ℝ) (hFC : F ≤ C) (hx : 0 < x) :
    evenPhysicalWindowTranslation a C F x hx =
      evenPhysicalWindowTranslation a C (soninWindowNormalizedFloor a C F x) x hx := by
  let A := evenIndicatorCutoff a
  let AC := evenIndicatorCutoff C
  let AF := evenIndicatorCutoff F
  let Az := evenIndicatorCutoff (x⁻¹ * a)
  let U := evenDilationCLM x hx
  have hmove : U * (1 - A) = (1 - Az) * U := by
    have h := evenDilationCLM_mul_evenIndicatorCutoff a x hx
    change U * A = Az * U at h
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hshell : (AC - AF) * (1 - Az) =
      AC - evenIndicatorCutoff (soninWindowNormalizedFloor a C F x) := by
    rcases le_total (x⁻¹ * a) C with hzC | hCz
    · have hmaxC : max F (x⁻¹ * a) ≤ C := max_le hFC hzC
      have h := evenIndicatorCutoff_shellComplementProduct C F (x⁻¹ * a) hzC
      rw [soninWindowNormalizedFloor, min_eq_left hmaxC]
      exact h
    · have hzero : (AC - AF) * (1 - Az) = 0 := by
        exact evenIndicatorShell_mul_complement_eq_zero C F (x⁻¹ * a)
          hCz (hFC.trans hCz)
      have hfloor : soninWindowNormalizedFloor a C F x = C := by
        rw [soninWindowNormalizedFloor, min_eq_right]
        exact le_trans hCz (le_max_right _ _)
      rw [hzero, hfloor, sub_self]
  have hfixed :
      (AC - evenIndicatorCutoff (soninWindowNormalizedFloor a C F x)) * (1 - Az) =
        AC - evenIndicatorCutoff (soninWindowNormalizedFloor a C F x) := by
    rcases le_total (x⁻¹ * a) C with hzC | hCz
    · have hzF : x⁻¹ * a ≤ soninWindowNormalizedFloor a C F x := by
        rw [soninWindowNormalizedFloor]
        exact le_min (le_max_right _ _) hzC
      have h := evenIndicatorCutoff_shellComplementProduct C
        (soninWindowNormalizedFloor a C F x) (x⁻¹ * a) hzC
      rw [max_eq_left hzF] at h
      exact h
    · have hfloor : soninWindowNormalizedFloor a C F x = C := by
        rw [soninWindowNormalizedFloor, min_eq_right]
        exact le_trans hCz (le_max_right _ _)
      rw [hfloor, sub_self, zero_mul]
  dsimp only [evenPhysicalWindowTranslation]
  change (AC - AF) * U * (1 - A) =
    (AC - evenIndicatorCutoff (soninWindowNormalizedFloor a C F x)) * U * (1 - A)
  calc
    (AC - AF) * U * (1 - A) =
        (AC - evenIndicatorCutoff (soninWindowNormalizedFloor a C F x)) * U := by
      rw [mul_assoc, hmove, ← mul_assoc, hshell]
    _ = (AC - evenIndicatorCutoff (soninWindowNormalizedFloor a C F x)) *
        U * (1 - A) := by
      rw [mul_assoc, hmove, ← mul_assoc, hfixed]

/-- Exact Fourier normalization against the trailing Sonin complement. -/
theorem evenFourierWindowTranslation_normalize
    (a C F x : ℝ) (hFC : F ≤ C) (hx : 0 < x) :
    evenFourierWindowTranslation a C F x hx =
      evenFourierWindowTranslation a C (soninWindowNormalizedFloor a C F x) x hx := by
  let R := evenFourierCutoff a
  let RC := evenFourierCutoff C
  let RF := evenFourierCutoff F
  let Rz := evenFourierCutoff (x⁻¹ * a)
  let U := evenDilationCLM x⁻¹ (inv_pos.mpr hx)
  have hmove : U * (1 - R) = (1 - Rz) * U := by
    have h := evenDilationCLM_mul_evenFourierCutoff a x⁻¹ (inv_pos.mpr hx)
    change U * R = Rz * U at h
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hshell : (RC - RF) * (1 - Rz) =
      RC - evenFourierCutoff (soninWindowNormalizedFloor a C F x) := by
    rcases le_total (x⁻¹ * a) C with hzC | hCz
    · have hmaxC : max F (x⁻¹ * a) ≤ C := max_le hFC hzC
      have h := evenFourierCutoff_shellComplementProduct C F (x⁻¹ * a) hzC
      rw [soninWindowNormalizedFloor, min_eq_left hmaxC]
      exact h
    · have hzero : (RC - RF) * (1 - Rz) = 0 := by
        exact evenFourierShell_mul_complement_eq_zero C F (x⁻¹ * a)
          hCz (hFC.trans hCz)
      have hfloor : soninWindowNormalizedFloor a C F x = C := by
        rw [soninWindowNormalizedFloor, min_eq_right]
        exact le_trans hCz (le_max_right _ _)
      rw [hzero, hfloor, sub_self]
  have hfixed :
      (RC - evenFourierCutoff (soninWindowNormalizedFloor a C F x)) * (1 - Rz) =
        RC - evenFourierCutoff (soninWindowNormalizedFloor a C F x) := by
    rcases le_total (x⁻¹ * a) C with hzC | hCz
    · have hzF : x⁻¹ * a ≤ soninWindowNormalizedFloor a C F x := by
        rw [soninWindowNormalizedFloor]
        exact le_min (le_max_right _ _) hzC
      have h := evenFourierCutoff_shellComplementProduct C
        (soninWindowNormalizedFloor a C F x) (x⁻¹ * a) hzC
      rw [max_eq_left hzF] at h
      exact h
    · have hfloor : soninWindowNormalizedFloor a C F x = C := by
        rw [soninWindowNormalizedFloor, min_eq_right]
        exact le_trans hCz (le_max_right _ _)
      rw [hfloor, sub_self, zero_mul]
  dsimp only [evenFourierWindowTranslation]
  change (RC - RF) * U * (1 - R) =
    (RC - evenFourierCutoff (soninWindowNormalizedFloor a C F x)) * U * (1 - R)
  calc
    (RC - RF) * U * (1 - R) =
        (RC - evenFourierCutoff (soninWindowNormalizedFloor a C F x)) * U := by
      rw [mul_assoc, hmove, ← mul_assoc, hshell]
    _ = (RC - evenFourierCutoff (soninWindowNormalizedFloor a C F x)) *
        U * (1 - R) := by
      rw [mul_assoc, hmove, ← mul_assoc, hfixed]

/-- Exact normalization of a two-polarization Sonin window. -/
theorem evenSoninWindowTranslation_normalize
    (a C F x : ℝ) (hFC : F ≤ C) (hx : 0 < x) :
    evenSoninWindowTranslation a C F x hx =
      evenSoninWindowTranslation a C (soninWindowNormalizedFloor a C F x) x hx := by
  dsimp only [evenSoninWindowTranslation]
  rw [evenPhysicalWindowTranslation_normalize a C F x hFC hx,
    evenFourierWindowTranslation_normalize a C F x hFC hx]

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- Canonical floor after composing two windows and normalizing the trailing complement. -/
def soninWindowComposeNormalizedFloor
    (a C₁ F₁ x C₂ F₂ y : ℝ) : ℝ :=
  soninWindowNormalizedFloor a
    (soninWindowComposeCeiling C₁ x C₂)
    (soninWindowComposeFloor C₁ F₁ x C₂ F₂) (x * y)

/-- Normalized two-polarization composition law. -/
theorem evenSoninWindowTranslation_mul_compactEq_normalized
    (a C₁ F₁ x C₂ F₂ y : ℝ)
    (ha : 0 < a) (haF₁ : a ≤ F₁) (haF₂ : a ≤ F₂)
    (hF₁C₁ : F₁ ≤ C₁) (hF₂C₂ : F₂ ≤ C₂)
    (hx : 0 < x) (hy : 0 < y) :
    evenSoninWindowTranslation a C₁ F₁ x hx *
        evenSoninWindowTranslation a C₂ F₂ y hy =ₖ
      evenSoninWindowTranslation a
        (soninWindowComposeCeiling C₁ x C₂)
        (soninWindowComposeNormalizedFloor a C₁ F₁ x C₂ F₂ y)
        (x * y) (mul_pos hx hy) := by
  have hraw := evenSoninWindowTranslation_mul_compactEq
    a C₁ F₁ x C₂ F₂ y ha haF₁ haF₂ hF₁C₁ hF₂C₂ hx hy
  have hfloorle : soninWindowComposeFloor C₁ F₁ x C₂ F₂ ≤
      soninWindowComposeCeiling C₁ x C₂ := by
    exact min_le_right _ _
  have hnorm := evenSoninWindowTranslation_normalize a
    (soninWindowComposeCeiling C₁ x C₂)
    (soninWindowComposeFloor C₁ F₁ x C₂ F₂) (x * y)
    hfloorle (mul_pos hx hy)
  exact hraw.trans (CompactOperatorEq.of_eq (by
    simpa [soninWindowComposeNormalizedFloor] using hnorm))

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- A nondegenerate canonical Sonin window. -/
structure SoninLiveWindow (a : ℝ) where
  ceiling : ℝ
  floor : ℝ
  scale : ℝ
  scale_pos : 0 < scale
  base_le_floor : a ≤ floor
  floor_lt_ceiling : floor < ceiling
  domain_le : a ≤ scale * floor

/-- The ceiling obtained by composing two live windows. -/
def soninLiveComposeCeiling {a : ℝ} (d e : SoninLiveWindow a) : ℝ :=
  soninWindowComposeCeiling d.ceiling d.scale e.ceiling

/-- The normalized floor obtained by composing two live windows. -/
def soninLiveComposeFloor {a : ℝ} (d e : SoninLiveWindow a) : ℝ :=
  soninWindowComposeNormalizedFloor a d.ceiling d.floor d.scale
    e.ceiling e.floor e.scale

/-- The displacement obtained by composing two live windows. -/
def soninLiveComposeScale {a : ℝ} (d e : SoninLiveWindow a) : ℝ :=
  d.scale * e.scale

lemma soninLiveComposeScale_pos {a : ℝ} (d e : SoninLiveWindow a) :
    0 < soninLiveComposeScale d e := mul_pos d.scale_pos e.scale_pos

/-- A nondegenerate composed floor remains above the physical base cutoff. -/
theorem base_le_soninLiveComposeFloor_of_lt {a : ℝ} (d e : SoninLiveWindow a)
    (h : soninLiveComposeFloor d e < soninLiveComposeCeiling d e) :
    a ≤ soninLiveComposeFloor d e := by
  let C := soninLiveComposeCeiling d e
  let M := max d.floor (d.scale⁻¹ * e.floor)
  let R := min M C
  let z := (d.scale * e.scale)⁻¹ * a
  have hF : soninLiveComposeFloor d e = min (max R z) C := by
    dsimp only [soninLiveComposeFloor, soninWindowComposeNormalizedFloor,
      soninWindowNormalizedFloor, soninWindowComposeFloor,
      soninWindowComposeCeiling, soninLiveComposeCeiling, C, M, R, z]
  have hmaxC : max R z < C := by
    by_contra hn
    have hCmax : C ≤ max R z := le_of_not_gt hn
    have heq : soninLiveComposeFloor d e = C := by
      rw [hF, min_eq_right hCmax]
    linarith
  have hRC : R < C := lt_of_le_of_lt (le_max_left _ _) hmaxC
  have hMC : M < C := by
    by_contra hn
    have hCM : C ≤ M := le_of_not_gt hn
    have hRCeq : R = C := by
      dsimp only [R]
      rw [min_eq_right hCM]
    linarith
  have hRM : R = M := by
    dsimp only [R]
    rw [min_eq_left hMC.le]
  have hFloor : soninLiveComposeFloor d e = max R z := by
    rw [hF, min_eq_left hmaxC.le]
  rw [hFloor, hRM]
  exact d.base_le_floor.trans ((le_max_left _ _).trans (le_max_left _ _))

/-- A nondegenerate composed floor also clears the pulled-back domain cutoff. -/
theorem domain_le_soninLiveComposeFloor_of_lt {a : ℝ} (d e : SoninLiveWindow a)
    (h : soninLiveComposeFloor d e < soninLiveComposeCeiling d e) :
    a ≤ soninLiveComposeScale d e * soninLiveComposeFloor d e := by
  let C := soninLiveComposeCeiling d e
  let R := soninWindowComposeFloor d.ceiling d.floor d.scale e.ceiling e.floor
  let z := (d.scale * e.scale)⁻¹ * a
  have hF : soninLiveComposeFloor d e = min (max R z) C := by
    dsimp only [soninLiveComposeFloor, soninWindowComposeNormalizedFloor,
      soninWindowNormalizedFloor, soninLiveComposeCeiling, C, R, z]
  have hmaxC : max R z < C := by
    by_contra hn
    have hCmax : C ≤ max R z := le_of_not_gt hn
    have heq : soninLiveComposeFloor d e = C := by
      rw [hF, min_eq_right hCmax]
    linarith
  have hzF : z ≤ soninLiveComposeFloor d e := by
    rw [hF, min_eq_left hmaxC.le]
    exact le_max_right _ _
  have hscale := soninLiveComposeScale_pos d e
  calc
    a = soninLiveComposeScale d e * z := by
      dsimp only [soninLiveComposeScale, z]
      have hd : d.scale ≠ 0 := d.scale_pos.ne'
      have he : e.scale ≠ 0 := e.scale_pos.ne'
      field_simp [hd, he]
    _ ≤ soninLiveComposeScale d e * soninLiveComposeFloor d e :=
      mul_le_mul_of_nonneg_left hzF hscale.le

/-- A window word is either already compactly zero or has canonical live data. -/
inductive SoninWindowState (a : ℝ) where
  | zero
  | live (datum : SoninLiveWindow a)

/-- Operator represented by a canonical window state. -/
def SoninWindowState.operator {a : ℝ} : SoninWindowState a →
    (evenSubspace →L[Complex] evenSubspace)
  | .zero => 0
  | .live d => evenSoninWindowTranslation a d.ceiling d.floor d.scale d.scale_pos

/-- Operator carried by live canonical data. -/
def SoninLiveWindow.operator {a : ℝ} (d : SoninLiveWindow a) :
    evenSubspace →L[Complex] evenSubspace :=
  (SoninWindowState.live d).operator

/-- Compose two live data, returning zero exactly when their normalized overlap degenerates. -/
def composeSoninLiveWindows {a : ℝ} (d e : SoninLiveWindow a) : SoninWindowState a :=
  if h : soninLiveComposeFloor d e < soninLiveComposeCeiling d e then
    .live
      { ceiling := soninLiveComposeCeiling d e
        floor := soninLiveComposeFloor d e
        scale := soninLiveComposeScale d e
        scale_pos := soninLiveComposeScale_pos d e
        base_le_floor := base_le_soninLiveComposeFloor_of_lt d e h
        floor_lt_ceiling := h
        domain_le := domain_le_soninLiveComposeFloor_of_lt d e h }
  else .zero

/-- Multiplication on canonical window states; zero is absorbing. -/
def composeSoninWindowStates {a : ℝ} :
    SoninWindowState a → SoninWindowState a → SoninWindowState a
  | .live d, .live e => composeSoninLiveWindows d e
  | _, _ => .zero

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

@[simp] theorem SoninWindowState.operator_zero {a : ℝ} :
    (SoninWindowState.zero : SoninWindowState a).operator = 0 := rfl

@[simp] theorem SoninWindowState.operator_live {a : ℝ} (d : SoninLiveWindow a) :
    (SoninWindowState.live d).operator =
      evenSoninWindowTranslation a d.ceiling d.floor d.scale d.scale_pos := rfl

/-- Canonical state composition realizes operator multiplication modulo compacts. -/
theorem soninWindowState_operator_mul_compactEq
    {a : ℝ} (ha : 0 < a) (s t : SoninWindowState a) :
    s.operator * t.operator =ₖ (composeSoninWindowStates s t).operator := by
  cases s with
  | zero =>
      exact CompactOperatorEq.of_eq (by
        simp [composeSoninWindowStates])
  | live d =>
      cases t with
      | zero =>
          exact CompactOperatorEq.of_eq (by
            simp [composeSoninWindowStates])
      | live e =>
          have hprod := evenSoninWindowTranslation_mul_compactEq_normalized
            a d.ceiling d.floor d.scale e.ceiling e.floor e.scale
            ha d.base_le_floor e.base_le_floor d.floor_lt_ceiling.le
            e.floor_lt_ceiling.le d.scale_pos e.scale_pos
          by_cases h : soninLiveComposeFloor d e < soninLiveComposeCeiling d e
          · let D : SoninLiveWindow a :=
              { ceiling := soninLiveComposeCeiling d e
                floor := soninLiveComposeFloor d e
                scale := soninLiveComposeScale d e
                scale_pos := soninLiveComposeScale_pos d e
                base_le_floor := base_le_soninLiveComposeFloor_of_lt d e h
                floor_lt_ceiling := h
                domain_le := domain_le_soninLiveComposeFloor_of_lt d e h }
            have hstate : composeSoninWindowStates
                (SoninWindowState.live d) (SoninWindowState.live e) =
                SoninWindowState.live D := by
              simp [composeSoninWindowStates, composeSoninLiveWindows, h, D]
            rw [hstate]
            simpa [D, soninLiveComposeCeiling, soninLiveComposeFloor,
              soninLiveComposeScale] using hprod
          · have hfloorle : soninLiveComposeFloor d e ≤ soninLiveComposeCeiling d e := by
              exact min_le_right _ _
            have heq : soninLiveComposeFloor d e = soninLiveComposeCeiling d e :=
              le_antisymm hfloorle (le_of_not_gt h)
            have hzero : evenSoninWindowTranslation a
                (soninLiveComposeCeiling d e) (soninLiveComposeFloor d e)
                (soninLiveComposeScale d e) (soninLiveComposeScale_pos d e) = 0 := by
              rw [heq]
              simp [evenSoninWindowTranslation, evenPhysicalWindowTranslation,
                evenFourierWindowTranslation]
            have hprod' : (SoninWindowState.live d).operator *
                (SoninWindowState.live e).operator =ₖ 0 := by
              refine hprod.trans (CompactOperatorEq.of_eq ?_)
              simpa [soninLiveComposeCeiling, soninLiveComposeFloor,
                soninLiveComposeScale] using hzero
            simpa [composeSoninWindowStates, composeSoninLiveWindows, h] using hprod'

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- Left-associated multiplication of window operators. -/
def foldSoninWindowOperators {a : ℝ}
    (T : evenSubspace →L[Complex] evenSubspace) :
    List (SoninLiveWindow a) → (evenSubspace →L[Complex] evenSubspace)
  | [] => T
  | d :: ds => foldSoninWindowOperators
      (T * (SoninWindowState.live d).operator) ds

/-- Parallel fold of canonical window states. -/
def foldSoninWindowStates {a : ℝ} (s : SoninWindowState a) :
    List (SoninLiveWindow a) → SoninWindowState a
  | [] => s
  | d :: ds => foldSoninWindowStates
      (composeSoninWindowStates s (SoninWindowState.live d)) ds

/-- The state fold is a normal form for every left-associated operator fold. -/
theorem foldSoninWindowOperators_compactEq_state
    {a : ℝ} (ha : 0 < a) (ds : List (SoninLiveWindow a))
    (T : evenSubspace →L[Complex] evenSubspace) (s : SoninWindowState a)
    (hTs : T =ₖ s.operator) :
    foldSoninWindowOperators T ds =ₖ (foldSoninWindowStates s ds).operator := by
  induction ds generalizing T s with
  | nil => simpa [foldSoninWindowOperators, foldSoninWindowStates] using hTs
  | cons d ds ih =>
      apply ih
      exact (CompactOperatorEq.mul hTs
        (CompactOperatorEq.refl (SoninWindowState.live d).operator)).trans
          (soninWindowState_operator_mul_compactEq ha s (SoninWindowState.live d))

/-- Normal form of a nonempty finite word of canonical live windows. -/
theorem finiteSoninWindowWord_compactEq_state
    {a : ℝ} (ha : 0 < a) (d : SoninLiveWindow a)
    (ds : List (SoninLiveWindow a)) :
    foldSoninWindowOperators (SoninWindowState.live d).operator ds =ₖ
      (foldSoninWindowStates (SoninWindowState.live d) ds).operator :=
  foldSoninWindowOperators_compactEq_state ha ds
    (SoninWindowState.live d).operator (SoninWindowState.live d)
    (CompactOperatorEq.refl _)

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- Initial Calkin projection of a general two-polarization window. -/
theorem evenSoninWindowTranslation_adjoint_mul_compactEq_shell
    (a C F x : ℝ) (hC : 0 < C) (hF : 0 < F) (hFC : F ≤ C) (hx : 0 < x) :
    (evenSoninWindowTranslation a C F x hx)† *
        evenSoninWindowTranslation a C F x hx =ₖ
      evenTwoPolarizationShell (max (x * F) a) (max (x * C) a) := by
  have c1 := physicalWindow_adjoint_mul a C F x hx hFC
  have c4 := fourierWindow_adjoint_mul a C F x⁻¹ (inv_pos.mpr hx) hFC
  simp only [inv_inv] at c4
  have hadjP := physicalWindow_adjoint a C F x hx
  have hadjF := fourierWindow_adjoint a C F x⁻¹ (inv_pos.mpr hx)
  have c2 : (evenPhysicalWindowTranslation a C F x hx)† *
      evenFourierWindowTranslation a C F x hx =ₖ 0 := by
    dsimp only [evenPhysicalWindowTranslation, evenFourierWindowTranslation]
    rw [hadjP]
    exact compactOperatorEq_zero_of_isCompact
      (isCompactOperator_physicalCoWindow_mul_fourierWindow
        a C F C F x⁻¹ x⁻¹ hC hF (inv_pos.mpr hx) (inv_pos.mpr hx))
  have c3 : (evenFourierWindowTranslation a C F x hx)† *
      evenPhysicalWindowTranslation a C F x hx =ₖ 0 := by
    dsimp only [evenPhysicalWindowTranslation, evenFourierWindowTranslation]
    rw [hadjF]
    exact compactOperatorEq_zero_of_isCompact
      (isCompactOperator_fourierCoWindow_mul_physicalWindow
        a C F C F (x⁻¹)⁻¹ x hC hF (by positivity) hx)
  have hsum := CompactOperatorEq.add
    (CompactOperatorEq.add (CompactOperatorEq.of_eq c1) c2)
    (CompactOperatorEq.add c3 (CompactOperatorEq.of_eq c4))
  dsimp only [evenSoninWindowTranslation, evenPhysicalWindowTranslation,
    evenFourierWindowTranslation, evenTwoPolarizationShell]
  rw [adjoint_add_clm, add_mul, mul_add, mul_add]
  simpa only [add_zero, zero_add] using! hsum

/-- Every canonical live window is noncompact. -/
theorem SoninLiveWindow.not_isCompactOperator {a : ℝ} (ha : 0 < a)
    (d : SoninLiveWindow a) : ¬ IsCompactOperator d.operator := by
  intro hcpt
  have hF0 : 0 < d.floor := lt_of_lt_of_le ha d.base_le_floor
  have hC0 : 0 < d.ceiling := hF0.trans d.floor_lt_ceiling
  have hxF : a ≤ d.scale * d.floor := d.domain_le
  have hxC : a ≤ d.scale * d.ceiling :=
    hxF.trans (mul_le_mul_of_nonneg_left d.floor_lt_ceiling.le d.scale_pos.le)
  have hmaxF : max (d.scale * d.floor) a = d.scale * d.floor := max_eq_left hxF
  have hmaxC : max (d.scale * d.ceiling) a = d.scale * d.ceiling := max_eq_left hxC
  have hI := evenSoninWindowTranslation_adjoint_mul_compactEq_shell
    a d.ceiling d.floor d.scale hC0 hF0 d.floor_lt_ceiling.le d.scale_pos
  rw [hmaxF, hmaxC] at hI
  have hTT : IsCompactOperator ((d.operator†) * d.operator) :=
    hcpt.clm_comp (d.operator†)
  have hS : IsCompactOperator
      (evenTwoPolarizationShell (d.scale * d.floor) (d.scale * d.ceiling)) := by
    have hdifference : IsCompactOperator
        (((d.operator†) * d.operator) -
          evenTwoPolarizationShell (d.scale * d.floor) (d.scale * d.ceiling)) := hI
    have heq : evenTwoPolarizationShell (d.scale * d.floor) (d.scale * d.ceiling) =
        (d.operator†) * d.operator -
          (((d.operator†) * d.operator) -
            evenTwoPolarizationShell (d.scale * d.floor) (d.scale * d.ceiling)) := by
      abel
    rw [heq]
    exact hTT.sub hdifference
  exact not_isCompactOperator_evenTwoPolarizationShell
    (d.scale * d.floor) (d.scale * d.ceiling)
    (mul_pos d.scale_pos hF0)
    (mul_lt_mul_of_pos_left d.floor_lt_ceiling d.scale_pos) hS

/-- Every canonical live window is a partial isometry in the Calkin algebra. -/
theorem SoninLiveWindow.isCalkinPartialIsometry {a : ℝ} (ha : 0 < a)
    (d : SoninLiveWindow a) : IsCalkinPartialIsometry d.operator := by
  have hF0 : 0 < d.floor := lt_of_lt_of_le ha d.base_le_floor
  have hC0 : 0 < d.ceiling := hF0.trans d.floor_lt_ceiling
  have hxF : a ≤ d.scale * d.floor := d.domain_le
  have hxC : a ≤ d.scale * d.ceiling :=
    hxF.trans (mul_le_mul_of_nonneg_left d.floor_lt_ceiling.le d.scale_pos.le)
  have hmaxF : max (d.scale * d.floor) a = d.scale * d.floor := max_eq_left hxF
  have hmaxC : max (d.scale * d.ceiling) a = d.scale * d.ceiling := max_eq_left hxC
  let S := evenTwoPolarizationShell (d.scale * d.floor) (d.scale * d.ceiling)
  have hI := evenSoninWindowTranslation_adjoint_mul_compactEq_shell
    a d.ceiling d.floor d.scale hC0 hF0 d.floor_lt_ceiling.le d.scale_pos
  rw [hmaxF, hmaxC] at hI
  change (d.operator†) * d.operator =ₖ S at hI
  have hSadj : S† = S := adjoint_evenTwoPolarizationShell _ _
  have hSS : S * S =ₖ S := evenTwoPolarizationShell_mul_compactEq_self
    (d.scale * d.floor) (d.scale * d.ceiling) (mul_pos d.scale_pos hF0)
    (mul_le_mul_of_nonneg_left d.floor_lt_ceiling.le d.scale_pos.le)
  refine ⟨compactEq_idempotent_of_compactEq hI hSS, ?_⟩
  exact mul_adjoint_sq_compactEq_of_adjoint_mul_compactEq
    d.operator S hSadj hI hSS

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- Compactness is invariant under compact congruence, forward direction. -/
theorem IsCompactOperator.compactEq_right
    {T S : evenSubspace →L[Complex] evenSubspace}
    (hT : IsCompactOperator T) (hTS : T =ₖ S) : IsCompactOperator S := by
  have hdiff : IsCompactOperator (T - S) := hTS
  have heq : S = T - (T - S) := by abel
  rw [heq]
  exact hT.sub hdiff

/-- Compactness is invariant under compact congruence, reverse direction. -/
theorem IsCompactOperator.compactEq_left
    {T S : evenSubspace →L[Complex] evenSubspace}
    (hS : IsCompactOperator S) (hTS : T =ₖ S) : IsCompactOperator T := by
  have hdiff : IsCompactOperator (T - S) := hTS
  have heq : T = (T - S) + S := by abel
  rw [heq]
  exact hdiff.add hS

/-- **Sharp finite-word compactness law.**  A nonempty canonical window word is compact exactly
when its recursively computed normal state is zero. -/
theorem finiteSoninWindowWord_isCompactOperator_iff_state_zero
    {a : ℝ} (ha : 0 < a) (d : SoninLiveWindow a)
    (ds : List (SoninLiveWindow a)) :
    IsCompactOperator
        (foldSoninWindowOperators (SoninWindowState.live d).operator ds) ↔
      foldSoninWindowStates (SoninWindowState.live d) ds = SoninWindowState.zero := by
  let T := foldSoninWindowOperators (SoninWindowState.live d).operator ds
  let s := foldSoninWindowStates (SoninWindowState.live d) ds
  have hTs : T =ₖ s.operator := finiteSoninWindowWord_compactEq_state ha d ds
  constructor
  · intro hT
    change IsCompactOperator T at hT
    cases hs : s with
    | zero => exact hs
    | live e =>
        exfalso
        have heCompact : IsCompactOperator e.operator := by
          have hsop : s.operator = e.operator := by rw [hs]; rfl
          rw [← hsop]
          exact RHTower.IsCompactOperator.compactEq_right hT hTs
        exact e.not_isCompactOperator ha heCompact
  · intro hs
    change s = SoninWindowState.zero at hs
    have hsop : s.operator = 0 := by rw [hs]; rfl
    rw [hsop] at hTs
    have hzero : IsCompactOperator (0 : evenSubspace →L[Complex] evenSubspace) :=
      isCompactOperator_zero
    exact RHTower.IsCompactOperator.compactEq_left hzero hTs

/-- A live finite-word normal form carries a Calkin partial isometry. -/
theorem finiteSoninWindowWord_live_partialIsometry
    {a : ℝ} (ha : 0 < a) (d : SoninLiveWindow a)
    (ds : List (SoninLiveWindow a)) (e : SoninLiveWindow a)
    (hstate : foldSoninWindowStates (SoninWindowState.live d) ds =
      SoninWindowState.live e) :
    foldSoninWindowOperators (SoninWindowState.live d).operator ds =ₖ e.operator ∧
      IsCalkinPartialIsometry e.operator := by
  constructor
  · have h := finiteSoninWindowWord_compactEq_state ha d ds
    rw [hstate] at h
    exact h
  · exact e.isCalkinPartialIsometry ha

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- A positive pair of CCM dilation scales. -/
structure SoninGramFactor where
  source : ℝ
  target : ℝ
  source_gt_one : 1 < source
  target_gt_one : 1 < target

/-- Canonical live window attached to one CCM Gram factor. -/
def SoninGramFactor.liveWindow (a : ℝ) (ha : 0 < a)
    (g : SoninGramFactor) : SoninLiveWindow a where
  ceiling := g.source * a
  floor := max a ((g.source * g.target⁻¹) * a)
  scale := g.source⁻¹ * g.target
  scale_pos := mul_pos (inv_pos.mpr (zero_lt_one.trans g.source_gt_one))
    (zero_lt_one.trans g.target_gt_one)
  base_le_floor := le_max_left _ _
  floor_lt_ceiling := by
    have hsa : a < g.source * a := by
      nlinarith [mul_pos (sub_pos.mpr g.source_gt_one) ha]
    apply max_lt
    · exact hsa
    · have htinv : g.target⁻¹ < 1 := inv_lt_one_of_one_lt₀ g.target_gt_one
      nlinarith [mul_pos (zero_lt_one.trans g.source_gt_one) ha]
  domain_le := by
    have hs0 := zero_lt_one.trans g.source_gt_one
    have ht0 := zero_lt_one.trans g.target_gt_one
    have hscale : 0 ≤ g.source⁻¹ * g.target :=
      (mul_pos (inv_pos.mpr hs0) ht0).le
    rw [mul_max_of_nonneg _ _ hscale]
    have heq : (g.source⁻¹ * g.target) *
        ((g.source * g.target⁻¹) * a) = a := by field_simp
    rw [heq]
    exact le_max_right _ _

/-- Actual even-Sonin quadratic Gram corner attached to a scale pair. -/
def SoninGramFactor.operator (a : ℝ) (g : SoninGramFactor) :
    evenSubspace →L[Complex] evenSubspace :=
  evenCentralSoninQuadraticCorner a g.source g.target
    g.source_gt_one g.target_gt_one

/-- The pair-specific mixed shell translation is the corresponding raw general window. -/
theorem evenSoninMixedShellTranslation_eq_window
    (a p q : ℝ) (hp : 1 < p) (hq : 1 < q) :
    evenSoninMixedShellTranslation a p q hp hq =
      evenSoninWindowTranslation a (p * a) a (p⁻¹ * q)
        (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq)) := by
  have hscale : (p⁻¹ * q)⁻¹ = p * q⁻¹ := by field_simp
  have hU : evenDilationCLM (p⁻¹ * q)⁻¹
        (inv_pos.mpr
          (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq))) =
      evenDilationCLM (p * q⁻¹)
        (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hq))) := by
    congr 1
  dsimp only [evenSoninMixedShellTranslation, evenSoninWindowTranslation,
    evenPhysicalMixedShellTranslation, evenPhysicalWindowTranslation,
    evenFourierMixedShellTranslation, evenFourierWindowTranslation]
  rw [hU]

/-- The actual CCM Gram corner has the canonical live window as its Calkin normal form. -/
theorem SoninGramFactor.operator_compactEq_liveWindow
    (a : ℝ) (ha : 0 < a) (g : SoninGramFactor) :
    g.operator a =ₖ (g.liveWindow a ha).operator := by
  have hcorner := evenCentralSoninQuadraticCorner_compactEq_shellTranslation
    a g.source g.target ha g.source_gt_one g.target_gt_one
  have hraw := evenSoninMixedShellTranslation_eq_window
    a g.source g.target g.source_gt_one g.target_gt_one
  have hfloor : soninWindowNormalizedFloor a (g.source * a) a
      (g.source⁻¹ * g.target) = max a ((g.source * g.target⁻¹) * a) := by
    have hscale : (g.source⁻¹ * g.target)⁻¹ * a =
        (g.source * g.target⁻¹) * a := by field_simp
    rw [soninWindowNormalizedFloor, hscale]
    have hsa : a < g.source * a := by
      nlinarith [mul_pos (sub_pos.mpr g.source_gt_one) ha]
    have hmaxlt : max a ((g.source * g.target⁻¹) * a) < g.source * a := by
      apply max_lt
      · exact hsa
      · have htinv : g.target⁻¹ < 1 := inv_lt_one_of_one_lt₀ g.target_gt_one
        nlinarith [mul_pos (zero_lt_one.trans g.source_gt_one) ha]
    rw [min_eq_left hmaxlt.le]
  have hnorm := evenSoninWindowTranslation_normalize a (g.source * a) a
    (g.source⁻¹ * g.target) (by
      nlinarith [mul_pos (sub_pos.mpr g.source_gt_one) ha])
    (mul_pos (inv_pos.mpr (zero_lt_one.trans g.source_gt_one))
      (zero_lt_one.trans g.target_gt_one))
  rw [hfloor] at hnorm
  refine hcorner.trans (CompactOperatorEq.of_eq ?_)
  rw [hraw, hnorm]
  rfl

end RHTower

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-- Left-associated multiplication of actual CCM Gram factors. -/
def foldSoninGramFactorOperators (a : ℝ)
    (T : evenSubspace →L[Complex] evenSubspace) :
    List SoninGramFactor → (evenSubspace →L[Complex] evenSubspace)
  | [] => T
  | g :: gs => foldSoninGramFactorOperators a (T * g.operator a) gs

/-- Actual Gram words are compactly represented by their canonical live-window words. -/
theorem foldSoninGramFactorOperators_compactEq_windows
    (a : ℝ) (ha : 0 < a) (gs : List SoninGramFactor)
    (T W : evenSubspace →L[Complex] evenSubspace) (hTW : T =ₖ W) :
    foldSoninGramFactorOperators a T gs =ₖ
      foldSoninWindowOperators W (gs.map fun g => g.liveWindow a ha) := by
  induction gs generalizing T W with
  | nil => simpa [foldSoninGramFactorOperators, foldSoninWindowOperators] using hTW
  | cons g gs ih =>
      apply ih
      exact CompactOperatorEq.mul hTW (g.operator_compactEq_liveWindow a ha)

/-- **Actual CCM finite-word normal form.**  Every nonempty word of genuine even-Sonin Gram
corners is compactly equal to its recursively computed zero/live window state. -/
theorem finiteSoninGramWord_compactEq_state
    (a : ℝ) (ha : 0 < a) (g : SoninGramFactor) (gs : List SoninGramFactor) :
    foldSoninGramFactorOperators a (g.operator a) gs =ₖ
      (foldSoninWindowStates (SoninWindowState.live (g.liveWindow a ha))
        (gs.map fun h => h.liveWindow a ha)).operator := by
  have hactual := foldSoninGramFactorOperators_compactEq_windows a ha gs
    (g.operator a) (g.liveWindow a ha).operator
    (g.operator_compactEq_liveWindow a ha)
  have hwindow := finiteSoninWindowWord_compactEq_state ha (g.liveWindow a ha)
    (gs.map fun h => h.liveWindow a ha)
  exact hactual.trans hwindow

/-- **Sharp compactness classification for actual CCM Gram words.**  A nonempty finite word is
compact exactly when its multiplicative interval recursion reaches the zero state. -/
theorem finiteSoninGramWord_isCompactOperator_iff_state_zero
    (a : ℝ) (ha : 0 < a) (g : SoninGramFactor) (gs : List SoninGramFactor) :
    IsCompactOperator (foldSoninGramFactorOperators a (g.operator a) gs) ↔
      foldSoninWindowStates (SoninWindowState.live (g.liveWindow a ha))
        (gs.map fun h => h.liveWindow a ha) = SoninWindowState.zero := by
  let T := foldSoninGramFactorOperators a (g.operator a) gs
  let W := foldSoninWindowOperators (SoninWindowState.live (g.liveWindow a ha)).operator
    (gs.map fun h => h.liveWindow a ha)
  have hTW : T =ₖ W := foldSoninGramFactorOperators_compactEq_windows a ha gs
    (g.operator a) (g.liveWindow a ha).operator
    (g.operator_compactEq_liveWindow a ha)
  have hW := finiteSoninWindowWord_isCompactOperator_iff_state_zero
    ha (g.liveWindow a ha) (gs.map fun h => h.liveWindow a ha)
  constructor
  · intro hT
    have hWcompact : IsCompactOperator W := by
      change IsCompactOperator T at hT
      exact RHTower.IsCompactOperator.compactEq_right hT hTW
    exact hW.mp hWcompact
  · intro hs
    have hWcompact : IsCompactOperator W := hW.mpr hs
    change IsCompactOperator T
    exact RHTower.IsCompactOperator.compactEq_left hWcompact hTW

/-- A live normal state gives the polar representative of the actual CCM Gram word. -/
theorem finiteSoninGramWord_live_partialIsometry
    (a : ℝ) (ha : 0 < a) (g : SoninGramFactor) (gs : List SoninGramFactor)
    (e : SoninLiveWindow a)
    (hstate : foldSoninWindowStates (SoninWindowState.live (g.liveWindow a ha))
      (gs.map fun h => h.liveWindow a ha) = SoninWindowState.live e) :
    foldSoninGramFactorOperators a (g.operator a) gs =ₖ e.operator ∧
      IsCalkinPartialIsometry e.operator := by
  constructor
  · have h := finiteSoninGramWord_compactEq_state a ha g gs
    rw [hstate] at h
    exact h
  · exact e.isCalkinPartialIsometry ha

end RHTower
