import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62MellinKernel
import GaloisForLFunctions.RHTower.MellinQuadraticStripDecay
import GaloisForLFunctions.RHTower.MellinQuinticStripDecay
import GaloisForLFunctions.RHTower.MellinUniformStripAllOrder

/-!
# Chen--Gupta--Li Lemma 6.2: uniform horizontal-edge decay

The compact logarithmic profile on the line `Re(s) = 2` belongs to Meyer's
all-weight target.  Its strong logarithmic Mellin transform is exactly the
source kernel after the affine reflection `s ↦ 2 - s`.  The existing uniform
quadratic strip theorem therefore supplies one decay budget simultaneously
for every abscissa used in CGL's first contour rectangle.
-/

open Complex MeasureTheory Filter Set Asymptotics
open scoped FourierTransform Topology
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- A real abscissa in the first CGL contour rectangle.  The strip membership
is data, so closed downstream contour theorems require no raw side premise. -/
structure CGLLemma62FirstShiftAbscissa where
  value : ℝ
  lower : -1 ≤ value
  upper : value ≤ 2

instance : Coe CGLLemma62FirstShiftAbscissa ℝ where
  coe sigma := sigma.value

/-- The compact line-two logarithmic profile, packaged in Meyer's strong
all-weight target. -/
def cglLemma62StrongLogSource (w : CGLRealSmoothBump) :
    DeningerMeyerStrongLogTarget :=
  ⟨cglLemma62LogMellinProfile w 2,
    deningerMeyerStrongLogDecay_of_hasCompactSupport
      (contDiff_cglLemma62LogMellinProfile w 2)
      (hasCompactSupport_cglLemma62LogMellinProfile w 2)⟩

@[simp] theorem cglLemma62StrongLogSource_coe (w : CGLRealSmoothBump) :
    (cglLemma62StrongLogSource w : ℝ → ℂ) =
      cglLemma62LogMellinProfile w 2 :=
  rfl

/-- The CGL Mellin kernel agrees with the strong log-Mellin transform on the
initial line. -/
private theorem cglLemma62_mellinTransform_eq_strongLogMellin_line
    (w : CGLRealSmoothBump) (t : ℝ) :
    cglLemma62MellinTransform w ((2 : ℂ) + (t : ℂ) * I) =
      deningerMeyerStrongLogMellin (cglLemma62StrongLogSource w)
        (2 - ((2 : ℂ) + (t : ℂ) * I)) := by
  change cglLemma62MellinTransform w (((2 : ℝ) : ℂ) + (t : ℂ) * I) = _
  rw [cglLemma62_mellinTransform_eq_fourier_logMellinProfile]
  have hstrong := deningerMeyerStrongLogMellin_eq_fourier
    (cglLemma62StrongLogSource w) (t / (2 * Real.pi))
  rw [cglLemma62StrongLogSource_coe] at hstrong
  have harg :
      -((2 * Real.pi * (t / (2 * Real.pi)) : ℝ) : ℂ) * I =
        2 - ((2 : ℂ) + (t : ℂ) * I) := by
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp [hpi]
    ring
  rw [harg] at hstrong
  change 𝓕 (cglLemma62LogMellinProfile w 2) (t / (2 * Real.pi)) =
    deningerMeyerStrongLogMellin (cglLemma62LogMellinProfile w 2)
      (2 - ((2 : ℂ) + (t : ℂ) * I))
  simpa using hstrong.symm

/-- Exact affine identification of CGL's source Mellin kernel with the
strong logarithmic Mellin transform of its compact profile. -/
theorem cglLemma62_mellinTransform_eq_strongLogMellin
    (w : CGLRealSmoothBump) (s : ℂ) :
    cglLemma62MellinTransform w s =
      deningerMeyerStrongLogMellin (cglLemma62StrongLogSource w) (2 - s) := by
  have hH := cglLemma62_mellinTransform_analyticOnNhd w
  have hG : AnalyticOnNhd ℂ
      (fun z : ℂ => deningerMeyerStrongLogMellin (cglLemma62StrongLogSource w)
        (2 - z)) univ := by
    let G : ℂ → ℂ := fun z : ℂ =>
      deningerMeyerStrongLogMellin (cglLemma62StrongLogSource w) z
    let q : ℂ → ℂ := fun z : ℂ => (2 : ℂ) - z
    have hGbase : AnalyticOnNhd ℂ G univ :=
      analyticOnNhd_deningerMeyerStrongLogMellin
        (cglLemma62StrongLogSource w).property
    have hq : AnalyticOnNhd ℂ q univ := by
      exact analyticOnNhd_const.sub analyticOnNhd_id
    change AnalyticOnNhd ℂ (G ∘ q) univ
    exact hGbase.comp hq (fun _ _ => mem_univ _)
  have hTendsto : Tendsto (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I)
      (𝓝[≠] 0) (𝓝[≠] (2 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · apply tendsto_nhdsWithin_of_tendsto_nhds
      have hcont : Continuous (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) := by
        fun_prop
      have hcontAt : ContinuousAt (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) 0 :=
        hcont.continuousAt
      have hval : (2 : ℂ) + ((0 : ℝ) : ℂ) * I = (2 : ℂ) := by norm_num
      change Tendsto (fun t : ℝ => (2 : ℂ) + (t : ℂ) * I) (𝓝 0)
        (𝓝 ((2 : ℂ) + ((0 : ℝ) : ℂ) * I)) at hcontAt
      rw [hval] at hcontAt
      exact hcontAt
    · apply eventually_nhdsWithin_iff.mpr
      exact Eventually.of_forall fun t ht hEq => by
        have him := congrArg Complex.im hEq
        simp at him
        exact ht him
  have hfrequent : ∃ᶠ z in 𝓝[≠] (2 : ℂ),
      cglLemma62MellinTransform w z =
        deningerMeyerStrongLogMellin (cglLemma62StrongLogSource w) (2 - z) := by
    apply hTendsto.frequently
    exact (Eventually.of_forall fun t =>
      cglLemma62_mellinTransform_eq_strongLogMellin_line w t).frequently
  exact congrFun (AnalyticOnNhd.eq_of_frequently_eq hH hG hfrequent) s

/-- CGL's explicit, cutoff-dependent uniform quadratic-decay budget on the
first-shift strip. -/
def cglLemma62MellinFirstShiftQuadraticBudget (w : CGLRealSmoothBump) : ℝ :=
  (∫ t : ℝ, deningerMeyerQuadraticStripMajorant0 3
    (cglLemma62StrongLogSource w) t) +
    ∫ t : ℝ, deningerMeyerQuadraticStripMajorant2 3
      (cglLemma62StrongLogSource w) t

/-- Uniform quadratic decay of the CGL Mellin kernel on the closed first-shift
strip `-1 ≤ Re(s) ≤ 2`.  This is the horizontal-edge input left implicit in
CGL equation (6.3). -/
theorem cglLemma62_mellinTransform_firstShift_uniformQuadraticDecay
    (w : CGLRealSmoothBump) (sigma : CGLLemma62FirstShiftAbscissa) (tau : ℝ) :
    ‖cglLemma62MellinTransform w ((sigma.value : ℂ) + (tau : ℂ) * I)‖ ≤
      cglLemma62MellinFirstShiftQuadraticBudget w * (1 + tau ^ 2)⁻¹ := by
  have hsigma0 : 0 ≤ 2 - sigma.value := by linarith [sigma.upper]
  have hsigmac : 2 - sigma.value ≤ 3 := by linarith [sigma.lower]
  have hstrong := norm_deningerMeyerStrongLogMellin_le_inv_one_add_sq
    (cglLemma62StrongLogSource w) (c := 3) (sigma := 2 - sigma.value)
      (by norm_num) hsigma0 hsigmac (-tau)
  have harg :
      ((2 - sigma.value : ℝ) : ℂ) + ((-tau : ℝ) : ℂ) * I =
        2 - ((sigma.value : ℂ) + (tau : ℂ) * I) := by
    push_cast
    ring
  rw [harg] at hstrong
  rw [← cglLemma62_mellinTransform_eq_strongLogMellin] at hstrong
  simpa [cglLemma62MellinFirstShiftQuadraticBudget] using hstrong

/-- The explicit fifth-order first-shift budget.  It is strong enough to
absorb the certified cubic induced-character envelope on horizontal edges. -/
def cglLemma62MellinFirstShiftQuinticBudget (w : CGLRealSmoothBump) : ℝ :=
  ∫ t : ℝ, deningerMeyerQuinticStripMajorant (cglLemma62StrongLogSource w) t

/-- Uniform fifth-order decay of CGL's Mellin kernel throughout the first
contour rectangle.  The strip qualification is carried by `sigma`, never by a
caller-supplied proposition. -/
theorem cglLemma62_mellinTransform_firstShift_uniformQuinticDecay
    (w : CGLRealSmoothBump) (sigma : CGLLemma62FirstShiftAbscissa) (tau : ℝ) :
    |tau| ^ 5 * ‖cglLemma62MellinTransform w ((sigma.value : ℂ) + (tau : ℂ) * I)‖ ≤
      cglLemma62MellinFirstShiftQuinticBudget w := by
  let sigma' : DeningerMeyerQuinticStripAbscissa :=
    ⟨2 - sigma.value, by linarith [sigma.upper], by linarith [sigma.lower]⟩
  have hstrong := abs_im_pow_five_mul_norm_deningerMeyerStrongLogMellin_le
    (cglLemma62StrongLogSource w) sigma' (-tau)
  have harg :
      ((sigma'.value : ℝ) : ℂ) + ((-tau : ℝ) : ℂ) * I =
        2 - ((sigma.value : ℂ) + (tau : ℂ) * I) := by
    dsimp [sigma']
    push_cast
    ring
  rw [harg] at hstrong
  rw [← cglLemma62_mellinTransform_eq_strongLogMellin] at hstrong
  simpa [cglLemma62MellinFirstShiftQuinticBudget] using hstrong

/-- The closed budget used to absorb an arbitrary polynomial vertical envelope
on the first CGL contour rectangle. -/
def cglLemma62MellinFirstShiftUniformBudget
    (w : CGLRealSmoothBump) (n : ℕ) : ℝ :=
  ∫ t : ℝ,
    deningerMeyerUniformStripMajorant (cglLemma62StrongLogSource w) n t

/-- Uniform CGL kernel decay of every prescribed order on the first contour
rectangle.  The order is data, while the strip conditions remain contained in
the abscissa structure. -/
theorem cglLemma62_mellinTransform_firstShift_uniformAllOrderDecay
    (w : CGLRealSmoothBump) (n : ℕ)
    (sigma : CGLLemma62FirstShiftAbscissa) (tau : ℝ) :
    |tau| ^ n *
        ‖cglLemma62MellinTransform w
          ((sigma.value : ℂ) + (tau : ℂ) * I)‖ ≤
      cglLemma62MellinFirstShiftUniformBudget w n := by
  let sigma' : DeningerMeyerUniformStripAbscissa :=
    ⟨2 - sigma.value, by linarith [sigma.upper], by linarith [sigma.lower]⟩
  have hstrong := abs_im_pow_mul_norm_deningerMeyerStrongLogMellin_le_uniform
    (cglLemma62StrongLogSource w) n sigma' (-tau)
  have harg :
      ((sigma'.value : ℝ) : ℂ) + ((-tau : ℝ) : ℂ) * I =
        2 - ((sigma.value : ℂ) + (tau : ℂ) * I) := by
    dsimp [sigma']
    push_cast
    ring
  rw [harg] at hstrong
  rw [← cglLemma62_mellinTransform_eq_strongLogMellin] at hstrong
  simpa [cglLemma62MellinFirstShiftUniformBudget] using hstrong

end

end RHTower
