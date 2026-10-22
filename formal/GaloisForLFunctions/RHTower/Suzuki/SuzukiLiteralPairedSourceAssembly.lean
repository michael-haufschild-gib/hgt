import GaloisForLFunctions.RHTower.Suzuki.SuzukiCoordinateCutoffPrimitiveFlux
import GaloisForLFunctions.RHTower.Suzuki.SuzukiSupportPrunedSelfAdjointSeamCarrier
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Literal paired source assembly for Suzuki's two rooted seam cosets

The left and right endpoint cosets transport valuation labels in opposite directions under a
physical prime translation.  This module records the exact rooted sign, decomposes each translated
sample into its centered marked descendant plus its center value, constructs a canonical smooth
cutoff supported exactly inside the physical aperture, and proves the complete
physical-source-plus-cutoff primitive identity.

All results are unconditional algebraic or elementary real-analytic identities.  No completed-mode
equation, RH premise, derivative regularity, or extra axiom is assumed.
-/

open Real

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Valuation step induced by subtracting a prime displacement from a rooted seam location. -/
def suzukiSourceOrientedStep (root : SuzukiSeamRoot) (delta : SuzukiSeamValuation) :
    SuzukiSeamValuation :=
  match root with
  | .left => -delta
  | .right => delta

@[simp] theorem suzukiSourceOrientedStep_left (delta : SuzukiSeamValuation) :
    suzukiSourceOrientedStep .left delta = -delta := rfl

@[simp] theorem suzukiSourceOrientedStep_right (delta : SuzukiSeamValuation) :
    suzukiSourceOrientedStep .right delta = delta := rfl

/-- Correct two-coset transport law.  Prime subtraction reverses valuation direction at the
left root and preserves it at the right root. -/
theorem suzukiSeamLocation_add_sourceOrientedStep
    (a : ℝ) (root : SuzukiSeamRoot) (nu delta : SuzukiSeamValuation) :
    suzukiSeamLocation a (root, nu + suzukiSourceOrientedStep root delta) =
      suzukiSeamLocation a (root, nu) - primeSeamCoordinate delta := by
  cases root <;> simp [suzukiSeamLocation, map_add, map_neg] <;> ring

/-- Adding a physical prime displacement uses the opposite rooted valuation step. -/
theorem suzukiSeamLocation_sub_sourceOrientedStep
    (a : ℝ) (root : SuzukiSeamRoot) (nu delta : SuzukiSeamValuation) :
    suzukiSeamLocation a (root, nu - suzukiSourceOrientedStep root delta) =
      suzukiSeamLocation a (root, nu) + primeSeamCoordinate delta := by
  cases root <;> simp [suzukiSeamLocation, map_sub] <;> ring

/-- Centered punctured sample at an oriented rooted seam. -/
def suzukiCenteredSeamSample (u : ℝ → ℂ) (a : ℝ) (root : SuzukiSeamRoot)
    (nu : SuzukiSeamValuation) (o r : ℝ) : ℂ :=
  u (suzukiSeamLocation a (root, nu) + o * r) - u (suzukiSeamLocation a (root, nu))

/-- Exact marked-descendant decomposition of a negative prime translate. -/
theorem suzuki_primeTranslate_sub_centered
    (u : ℝ → ℂ) (a : ℝ) (root : SuzukiSeamRoot)
    (nu delta : SuzukiSeamValuation) (o r : ℝ) :
    u (suzukiSeamLocation a (root, nu) + o * r - primeSeamCoordinate delta) =
      suzukiCenteredSeamSample u a root
          (nu + suzukiSourceOrientedStep root delta) o r +
        u (suzukiSeamLocation a
          (root, nu + suzukiSourceOrientedStep root delta)) := by
  unfold suzukiCenteredSeamSample
  rw [suzukiSeamLocation_add_sourceOrientedStep]
  have harg :
      suzukiSeamLocation a (root, nu) + o * r - primeSeamCoordinate delta =
        (suzukiSeamLocation a (root, nu) - primeSeamCoordinate delta) + o * r := by
    ring
  rw [harg]
  abel

/-- Exact marked-descendant decomposition of a positive prime translate. -/
theorem suzuki_primeTranslate_add_centered
    (u : ℝ → ℂ) (a : ℝ) (root : SuzukiSeamRoot)
    (nu delta : SuzukiSeamValuation) (o r : ℝ) :
    u (suzukiSeamLocation a (root, nu) + o * r + primeSeamCoordinate delta) =
      suzukiCenteredSeamSample u a root
          (nu - suzukiSourceOrientedStep root delta) o r +
        u (suzukiSeamLocation a
          (root, nu - suzukiSourceOrientedStep root delta)) := by
  unfold suzukiCenteredSeamSample
  rw [suzukiSeamLocation_sub_sourceOrientedStep]
  have harg :
      suzukiSeamLocation a (root, nu) + o * r + primeSeamCoordinate delta =
        (suzukiSeamLocation a (root, nu) + primeSeamCoordinate delta) + o * r := by
    ring
  rw [harg]
  abel

/-- Scale-buffered right-wall cutoff argument. -/
def suzukiRightScaleBufferArgument (a x o L : ℝ) : ℝ :=
  Real.exp L * (a - (x + o * Real.exp (-L)))

/-- Scale-buffered left-wall cutoff argument. -/
def suzukiLeftScaleBufferArgument (a x o L : ℝ) : ℝ :=
  Real.exp L * (a + (x + o * Real.exp (-L)))

/-- Canonical smooth event cutoff: it vanishes outside `(-a,a)` and becomes one once the
sample lies at least one current physical scale from both walls. -/
def suzukiScaleBufferedCutoff (a x o L : ℝ) : ℝ :=
  Real.smoothTransition (suzukiRightScaleBufferArgument a x o L) *
    Real.smoothTransition (suzukiLeftScaleBufferArgument a x o L)

theorem suzukiRightScaleBufferArgument_eq (a x o L : ℝ) :
    suzukiRightScaleBufferArgument a x o L = Real.exp L * (a - x) - o := by
  have hexp : Real.exp L * Real.exp (-L) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [suzukiRightScaleBufferArgument]
  calc
    Real.exp L * (a - (x + o * Real.exp (-L))) =
        Real.exp L * (a - x) - o * (Real.exp L * Real.exp (-L)) := by ring
    _ = Real.exp L * (a - x) - o := by rw [hexp, mul_one]

theorem suzukiLeftScaleBufferArgument_eq (a x o L : ℝ) :
    suzukiLeftScaleBufferArgument a x o L = Real.exp L * (a + x) + o := by
  have hexp : Real.exp L * Real.exp (-L) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [suzukiLeftScaleBufferArgument]
  calc
    Real.exp L * (a + (x + o * Real.exp (-L))) =
        Real.exp L * (a + x) + o * (Real.exp L * Real.exp (-L)) := by ring
    _ = Real.exp L * (a + x) + o := by rw [hexp, mul_one]

/-- The canonical cutoff is nonzero exactly when the sampled physical point is strictly inside
the aperture.  Thus multiplying by it never invokes Suzuki's interior equation outside its
literal support. -/
theorem suzukiScaleBufferedCutoff_ne_zero_iff (a x o L : ℝ) :
    suzukiScaleBufferedCutoff a x o L ≠ 0 ↔
      -a < x + o * Real.exp (-L) ∧ x + o * Real.exp (-L) < a := by
  unfold suzukiScaleBufferedCutoff
  rw [mul_ne_zero_iff]
  simp only [ne_eq, Real.smoothTransition.zero_iff_nonpos, not_le,
    suzukiRightScaleBufferArgument, suzukiLeftScaleBufferArgument]
  constructor
  · rintro ⟨hright, hleft⟩
    constructor
    · have := (mul_pos_iff.mp hleft)
      rcases this with h | h
      · linarith
      · linarith [Real.exp_pos L]
    · have := (mul_pos_iff.mp hright)
      rcases this with h | h
      · linarith
      · linarith [Real.exp_pos L]
  · rintro ⟨hleft, hright⟩
    constructor
    · exact mul_pos (Real.exp_pos L) (by linarith)
    · exact mul_pos (Real.exp_pos L) (by linarith)

/-- Literal paired cutoff assembly identity.  Its first bracket is the derivative of the
primitive source `M G + [C,M]F`; the right side contains only the uncut residual and zero-order
event terms.  No derivative of `F` occurs in an event source. -/
theorem literalPairedCutoffSourceAssembly_pointwise
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : ℝ) (C Z M Mdot : Module.End ℝ V) (F Fdot G Gdot : V) :
    (twoLPlus L C (Mdot F + M Fdot) + Z (M F)) -
        ((Mdot G + M Gdot) +
          (C (Mdot F) + C (M Fdot) - Mdot (C F) - M (C Fdot))) =
      M ((twoLPlus L C Fdot + Z F) - Gdot) +
        Mdot (twoLPlus L C F - G) + linearCommutator Z M F := by
  simp only [twoLPlus, linearCommutator, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq, LinearMap.sub_apply, LinearMap.comp_apply, map_add, map_sub,
    map_smul]
  module

end

end GaloisForLFunctions.RHTower

