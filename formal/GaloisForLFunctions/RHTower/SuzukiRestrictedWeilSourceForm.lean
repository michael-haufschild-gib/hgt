import GaloisForLFunctions.RHTower.SuzukiRestrictedWeilForm
import GaloisForLFunctions.RHTower.SuzukiOriginRemainderWeilBridge

/-!
# Suzuki's restricted Weil form with every source parameter discharged

`SuzukiRestrictedWeilForm` assembled the four distributional blocks but deliberately left the
smooth remainder and finite prime aperture as parameters.  This file inserts Suzuki's literal
source data:

* `A = (log(2π) - ψ(2))/2`;
* visible indices `2 ≤ n ≤ exp(2a)`;
* the continuous even remainder kernel proved in
  `SuzukiWeilRemainderRegularity`.

The resulting form and representative contain no free analytic kernel.  We also prove the exact
atomic Dirichlet decomposition and unconditional lower bound for its complete visible-prime
sector.  The only remaining semiboundedness work is therefore the finite-part block; smooth
remainder boundedness is now a theorem of the literal source.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- Literal real smooth core of Suzuki's restricted form.  Regularity and aperture support are
intrinsic data, so source theorems need no external analytic premises. -/
structure SuzukiRestrictedWeilCore (a : ℝ) where
  toFun : ℝ → ℝ
  smooth : ContDiff ℝ (⊤ : ℕ∞) toFun
  supportRadius : ℝ
  supportRadius_nonneg : 0 ≤ supportRadius
  supportRadius_lt_aperture : supportRadius < a
  support_subset : Function.support toFun ⊆ Icc (-supportRadius) supportRadius

instance (a : ℝ) : CoeFun (SuzukiRestrictedWeilCore a) fun _ => ℝ → ℝ :=
  ⟨SuzukiRestrictedWeilCore.toFun⟩

theorem SuzukiRestrictedWeilCore.continuous {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) : Continuous u :=
  u.smooth.continuous

theorem SuzukiRestrictedWeilCore.hasCompactSupport {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) : HasCompactSupport u :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc u.support_subset

theorem SuzukiRestrictedWeilCore.support_subset_aperture {a : ℝ}
    (u : SuzukiRestrictedWeilCore a) : Function.support u ⊆ Ioo (-a) a := by
  intro x hx
  have hxr := u.support_subset hx
  constructor
  · linarith [hxr.1, u.supportRadius_lt_aperture]
  · linarith [hxr.2, u.supportRadius_lt_aperture]

/-- Suzuki's exact scalar coefficient in the local screw expansion. -/
def suzukiWeilArchimedeanConstant : ℝ :=
  (Real.log (2 * Real.pi) - (Complex.digamma (2 : ℂ)).re) / 2

/-- Prime powers visible in the difference interval `[-2a,2a]`. -/
def suzukiRestrictedWeilIndices (a : ℝ) : Finset ℕ :=
  RHTower.suzukiVisibleWeilIndices (2 * a)

/-- Literal source-locked restricted Weil form at aperture `a`. -/
def suzukiRestrictedWeilForm (a : ℝ) (u φ : ℝ → ℝ) : ℝ :=
  restrictedWeilForm a suzukiWeilArchimedeanConstant
    (suzukiRestrictedWeilIndices a) RHTower.suzukiWeilRemainderKernel u φ

/-- Literal source-locked distributional representative. -/
def suzukiRestrictedWeilRepresentative (a : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  restrictedWeilRepresentative a suzukiWeilArchimedeanConstant
    (suzukiRestrictedWeilIndices a) RHTower.suzukiWeilRemainderKernel u

/-- The source-locked form is exactly Suzuki's four published blocks. -/
theorem suzukiRestrictedWeilForm_eq_fourBlocks (a : ℝ) (u φ : ℝ → ℝ) :
    suzukiRestrictedWeilForm a u φ =
      weilFinitePartBlock a u φ +
        weilScalarBlock a suzukiWeilArchimedeanConstant u φ +
        weilPrimeBlock (suzukiRestrictedWeilIndices a) u φ +
        weilSmoothBlock a RHTower.suzukiWeilRemainderKernel u φ := by
  rfl

/-- The source-locked four-block form uses exactly the curvature of Suzuki's origin remainder;
the independently derived hyperbolic and screw-kernel normalizations agree pointwise. -/
theorem suzukiRestrictedWeilForm_eq_originRemainderFourBlocks
    (a : ℝ) (u φ : ℝ → ℝ) :
    suzukiRestrictedWeilForm a u φ =
      weilFinitePartBlock a u φ +
        weilScalarBlock a suzukiWeilArchimedeanConstant u φ +
        weilPrimeBlock (suzukiRestrictedWeilIndices a) u φ +
        weilSmoothBlock a suzukiOriginRemainderCurvature u φ := by
  rw [suzukiRestrictedWeilForm_eq_fourBlocks]
  congr 1
  unfold weilSmoothBlock
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  apply congrArg (fun z : ℝ => z * φ x)
  apply intervalIntegral.integral_congr
  intro y _
  dsimp only
  rw [suzukiWeilRemainderKernel_eq_originCurvature]

/-- The source-locked representative has Suzuki's exact finite-part, scalar, prime, and smooth
convolution terms, with no kernel parameter left. -/
theorem suzukiRestrictedWeilRepresentative_eq (a : ℝ) (u : ℝ → ℝ) (x : ℝ) :
    suzukiRestrictedWeilRepresentative a u x =
      -(1 / 2) * cauchyFinitePart a x u -
        (2 * suzukiWeilArchimedeanConstant + 1) * u x -
        (∑ n ∈ suzukiRestrictedWeilIndices a,
          primePairWeight n * (u (x + Real.log n) + u (x - Real.log n))) +
        weilSmoothRepresentative a RHTower.suzukiWeilRemainderKernel u x := by
  rfl

/-- A self-jump is a nonnegative Dirichlet energy. -/
theorem jumpForm_self_nonneg (h : ℝ) (u : ℝ → ℝ) :
    0 ≤ jumpForm h u u := by
  rw [jumpForm]
  exact integral_nonneg fun x => mul_self_nonneg (u (x + h) - u x)

/-- The complete literal visible-prime block is a nonnegative atomic jump energy minus its exact
scalar potential. -/
theorem suzukiRestrictedWeilPrimeBlock_eq_jumpForms
    {u : ℝ → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u) (a : ℝ) :
    weilPrimeBlock (suzukiRestrictedWeilIndices a) u u =
      (∑ n ∈ suzukiRestrictedWeilIndices a,
        primePairWeight n * jumpForm (Real.log n) u u) -
      2 * (∑ n ∈ suzukiRestrictedWeilIndices a, primePairWeight n) * pairing u u :=
  weilPrimeBlock_eq_jumpForms hu hu hcu _

/-- Unconditional lower bound for Suzuki's entire visible-prime sector. -/
theorem suzukiRestrictedWeilPrimeBlock_lowerBound
    {u : ℝ → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u) (a : ℝ) :
    -(2 * (∑ n ∈ suzukiRestrictedWeilIndices a, primePairWeight n)) * pairing u u ≤
      weilPrimeBlock (suzukiRestrictedWeilIndices a) u u := by
  rw [suzukiRestrictedWeilPrimeBlock_eq_jumpForms hu hcu a]
  have henergy : 0 ≤ ∑ n ∈ suzukiRestrictedWeilIndices a,
      primePairWeight n * jumpForm (Real.log n) u u :=
    sum_primePairWeight_jumpForm_nonneg _ _ _
      (fun n _ => jumpForm_self_nonneg (Real.log n) u)
  linarith

/-- Closed source-core form of the visible-prime lower bound. -/
theorem suzukiRestrictedWeilPrimeBlock_lowerBound_core
    (a : ℝ) (u : SuzukiRestrictedWeilCore a) :
    -(2 * (∑ n ∈ suzukiRestrictedWeilIndices a, primePairWeight n)) * pairing u u ≤
      weilPrimeBlock (suzukiRestrictedWeilIndices a) u u :=
  suzukiRestrictedWeilPrimeBlock_lowerBound u.continuous u.hasCompactSupport a

/-- The exact smooth source kernel has a uniform bound on all differences of aperture points. -/
theorem exists_abs_suzukiWeilRemainderKernel_sub_le (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-a) a, ∀ y ∈ Icc (-a) a,
      |RHTower.suzukiWeilRemainderKernel (x - y)| ≤ C := by
  obtain ⟨C, hC⟩ := RHTower.exists_abs_suzukiWeilRemainderKernel_le a
  have hC0 : 0 ≤ C := by
    have hzero : (0 : ℝ) ∈ Icc (-2 * |a|) (2 * |a|) := by
      constructor <;> nlinarith [abs_nonneg a]
    exact (abs_nonneg (RHTower.suzukiWeilRemainderKernel 0)).trans (hC 0 hzero)
  refine ⟨C, hC0, ?_⟩
  intro x hx y hy
  apply hC
  have ha : 0 ≤ a := by linarith [hx.1, hx.2]
  have hxa : |x| ≤ |a| := by
    rw [abs_of_nonneg ha]
    exact (abs_le).2 hx
  have hya : |y| ≤ |a| := by
    rw [abs_of_nonneg ha]
    exact (abs_le).2 hy
  have hsub : |x - y| ≤ 2 * |a| := by
    calc
      |x - y| ≤ |x| + |y| := abs_sub x y
      _ ≤ 2 * |a| := by linarith
  rw [mem_Icc]
  exact ⟨by nlinarith [neg_abs_le (x - y)],
    (le_abs_self (x - y)).trans hsub⟩

end GaloisForLFunctions.RHTower
