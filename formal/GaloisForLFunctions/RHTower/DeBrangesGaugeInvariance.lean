import GaloisForLFunctions.RHTower.SuzukiFiniteApertureHermiteBiehler

/-!
# Exact de Branges gauge invariance

This leaf isolates the algebraic part of the gauge claim.  Multiplication by a
pointwise nonvanishing gauge fixed by Schwarz reflection preserves the strict
Hermite--Biehler inequality, every canonical real-angle zero set, and the inner
quotient.  The algebraic reproducing kernel transforms by the expected
`H(z) * conj (H(w))` factor.

No analyticity, finite-order, or saturation assumption is hidden here; those
belong to the remaining de Branges/HT realization and rigidity obligations.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- A gauge fixed by Schwarz reflection. -/
def SchwarzRealGauge (H : ℂ → ℂ) : Prop :=
  ∀ z, suzukiEntireSharp H z = H z

/-- A pointwise nonvanishing gauge. -/
def ZeroFreeGauge (H : ℂ → ℂ) : Prop :=
  ∀ z, H z ≠ 0

theorem suzukiEntireSharp_mul_of_schwarzReal
    {H E : ℂ → ℂ} (hH : SchwarzRealGauge H) (z : ℂ) :
    suzukiEntireSharp (fun w => H w * E w) z =
      H z * suzukiEntireSharp E z := by
  rw [suzukiEntireSharp, map_mul, ← suzukiEntireSharp]
  rw [hH]
  rfl

/-- A real zero-free gauge preserves the strict Hermite--Biehler condition exactly. -/
theorem suzukiHermiteBiehler_mul_iff
    {H E : ℂ → ℂ} (hH : SchwarzRealGauge H) (hzero : ZeroFreeGauge H) :
    SuzukiHermiteBiehler (fun z => H z * E z) ↔ SuzukiHermiteBiehler E := by
  constructor
  · intro hE z hz
    have h := hE z hz
    rw [suzukiEntireSharp_mul_of_schwarzReal hH, norm_mul, norm_mul] at h
    have hpos : 0 < ‖H z‖ := norm_pos_iff.mpr (hzero z)
    nlinarith
  · intro hE z hz
    rw [suzukiEntireSharp_mul_of_schwarzReal hH, norm_mul, norm_mul]
    exact mul_lt_mul_of_pos_left (hE z hz) (norm_pos_iff.mpr (hzero z))

/-- Real part of a de Branges structure function. -/
def deBrangesRealPart (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  (E z + suzukiEntireSharp E z) / 2

/-- Imaginary-part entire function in the convention `E=A-iB`. -/
def deBrangesImaginaryPart (E : ℂ → ℂ) (z : ℂ) : ℂ :=
  (suzukiEntireSharp E z - E z) / (2 * I)

theorem deBrangesRealPart_mul_of_schwarzReal
    {H E : ℂ → ℂ} (hH : SchwarzRealGauge H) (z : ℂ) :
    deBrangesRealPart (fun w => H w * E w) z =
      H z * deBrangesRealPart E z := by
  rw [deBrangesRealPart, suzukiEntireSharp_mul_of_schwarzReal hH,
    deBrangesRealPart]
  ring

theorem deBrangesImaginaryPart_mul_of_schwarzReal
    {H E : ℂ → ℂ} (hH : SchwarzRealGauge H) (z : ℂ) :
    deBrangesImaginaryPart (fun w => H w * E w) z =
      H z * deBrangesImaginaryPart E z := by
  rw [deBrangesImaginaryPart, suzukiEntireSharp_mul_of_schwarzReal hH,
    deBrangesImaginaryPart]
  ring

/-- Canonical real-angle spectral pencil. -/
def deBrangesCanonicalPencil (E : ℂ → ℂ) (α : ℝ) (z : ℂ) : ℂ :=
  (Real.cos α : ℂ) * deBrangesRealPart E z -
    (Real.sin α : ℂ) * deBrangesImaginaryPart E z

theorem deBrangesCanonicalPencil_mul_of_schwarzReal
    {H E : ℂ → ℂ} (hH : SchwarzRealGauge H) (α : ℝ) (z : ℂ) :
    deBrangesCanonicalPencil (fun w => H w * E w) α z =
      H z * deBrangesCanonicalPencil E α z := by
  rw [deBrangesCanonicalPencil, deBrangesRealPart_mul_of_schwarzReal hH,
    deBrangesImaginaryPart_mul_of_schwarzReal hH, deBrangesCanonicalPencil]
  ring

/-- Every canonical real spectrum is unchanged by a real zero-free gauge. -/
theorem deBrangesCanonicalPencil_mul_eq_zero_iff
    {H E : ℂ → ℂ} (hH : SchwarzRealGauge H) (hzero : ZeroFreeGauge H)
    (α : ℝ) (z : ℂ) :
    deBrangesCanonicalPencil (fun w => H w * E w) α z = 0 ↔
      deBrangesCanonicalPencil E α z = 0 := by
  rw [deBrangesCanonicalPencil_mul_of_schwarzReal hH, mul_eq_zero]
  exact or_iff_right (hzero z)

/-- Exact de Branges inner quotient invariance. -/
theorem deBrangesInnerQuotient_mul_of_schwarzReal
    {H E : ℂ → ℂ} (hH : SchwarzRealGauge H) (hzero : ZeroFreeGauge H)
    (z : ℂ) :
    suzukiEntireSharp (fun w => H w * E w) z / (H z * E z) =
      suzukiEntireSharp E z / E z := by
  rw [suzukiEntireSharp_mul_of_schwarzReal hH]
  exact mul_div_mul_left _ _ (hzero z)

/-- Algebraic de Branges reproducing-kernel expression. -/
def deBrangesKernel (E : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (E z * star (E w) -
    suzukiEntireSharp E z * star (suzukiEntireSharp E w)) /
      (2 * Real.pi * I * (star w - z))

/-- Reproducing kernels transform by `H(z) * conj (H(w))`. -/
theorem deBrangesKernel_mul_of_schwarzReal
    {H E : ℂ → ℂ} (hH : SchwarzRealGauge H) (z w : ℂ) :
    deBrangesKernel (fun u => H u * E u) z w =
      H z * star (H w) * deBrangesKernel E z w := by
  rw [deBrangesKernel, suzukiEntireSharp_mul_of_schwarzReal hH,
    suzukiEntireSharp_mul_of_schwarzReal hH, deBrangesKernel]
  rw [star_mul, star_mul]
  ring

end

end GaloisForLFunctions.RHTower
