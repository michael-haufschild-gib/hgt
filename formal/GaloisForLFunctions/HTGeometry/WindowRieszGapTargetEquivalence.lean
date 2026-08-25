import GaloisForLFunctions.HTGeometry.JordanWindowArgumentPrinciple
import GaloisForLFunctions.HTGeometry.KernelFredholmDeterminant
import GaloisForLFunctions.HTGeometry.ClosedCompactResolventWindowRiesz
import GaloisForLFunctions.HTGeometry.WindowRieszRelativeNeumann

open Complex Metric Set

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt

noncomputable section

variable {ι : Type*} [DecidableEq ι]

/-- Chosen positive Carathéodory--Schoenflies chart of a bounded Jordan domain. Any bounded Jordan
domain admits such a global plane homeomorphism whose restriction to the open unit disc is the
conformal Riemann map. -/
structure BoundedJordanDomain where
  chart : ℂ ≃ₜ ℂ
  analytic_chart : AnalyticOnNhd ℂ chart (ball (0 : ℂ) 1)
  conformal_chart : ∀ w ∈ ball (0 : ℂ) 1, deriv chart w ≠ 0

namespace BoundedJordanDomain

def interior (J : BoundedJordanDomain) : Set ℂ := J.chart '' ball (0 : ℂ) 1

def boundary (J : BoundedJordanDomain) : Set ℂ := J.chart '' sphere (0 : ℂ) 1

def closure (J : BoundedJordanDomain) : Set ℂ := J.chart '' closedBall (0 : ℂ) 1

theorem interior_bounded (J : BoundedJordanDomain) : Bornology.IsBounded J.interior := by
  exact (isCompact_closedBall (0 : ℂ) 1).image J.chart.continuous |>.isBounded.subset
    (image_mono ball_subset_closedBall)

end BoundedJordanDomain

/-- A literal trace-class kernel family. Its associated operator is `I + K(z)` and its ordinary
Fredholm determinant is the global `det₂` times the zero-free trace correction. -/
structure TraceClassKernelFamily (ι : Type*) [DecidableEq ι] where
  K : ℂ → ι × ι → ℂ
  isHS : ∀ z, IsHS (K z)
  traceClass : ∀ z, RHTower.MemSchattenClass 1 (toOperator (isHS z))

namespace TraceClassKernelFamily

def operator (A : TraceClassKernelFamily ι) (z : ℂ) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  kernelFredholmOperator (A.K z) (A.isHS z)

def determinant (A : TraceClassKernelFamily ι) (z : ℂ) : ℂ :=
  kernelFredholmDeterminant (A.K z) (A.isHS z)

theorem determinant_eq_zero_iff_not_isUnit (A : TraceClassKernelFamily ι) (z : ℂ) :
    A.determinant z = 0 ↔ ¬ IsUnit (A.operator z) :=
  kernelFredholmDeterminant_eq_zero_iff_not_isUnit (A.K z) (A.isHS z)

/-- Exact bundled meaning of a holomorphic trace-class Fredholm family on a neighbourhood: the
operator family and its canonical Fredholm determinant are analytic on one open set. -/
def IsHolomorphicFredholmOn (A : TraceClassKernelFamily ι) (U : Set ℂ) : Prop :=
  IsOpen U ∧ AnalyticOnNhd ℂ A.operator U ∧ AnalyticOnNhd ℂ A.determinant U

end TraceClassKernelFamily

def jordanFredholmRootMultiplicity (J : BoundedJordanDomain)
    (A : TraceClassKernelFamily ι) : ℕ :=
  unitDiscZeroMultiplicity (A.determinant ∘ J.chart)

def jordanFredholmBoundaryWinding (J : BoundedJordanDomain)
    (A : TraceClassKernelFamily ι) : ℤ :=
  RHTower.windingNumber
    (fun θ : ℝ => A.determinant (J.chart (Complex.exp (Complex.I * (θ : ℂ)))))
    0 (2 * Real.pi)

theorem zeroMult_determinant_comp_chart
    (J : BoundedJordanDomain) (A : TraceClassKernelFamily ι)
    {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) :
    zeroMult (A.determinant ∘ J.chart) w = zeroMult A.determinant (J.chart w) := by
  rw [zeroMult, zeroMult,
    analyticOrderAt_comp_of_deriv_ne_zero (J.analytic_chart w hw)
      (J.conformal_chart w hw)]

/-- Full five-way Window--Riesz/Fredholm target equivalence on an arbitrary bounded Jordan domain.
No source exclusion is hidden: the sole arithmetic input is exactly characteristic-divisor law
`(C)`. -/
theorem windowRieszGapTarget_equivalent
    (J : BoundedJordanDomain) (A : TraceClassKernelFamily ι)
    {U : Set ℂ} (hfamily : A.IsHolomorphicFredholmOn U)
    (hclosure : J.closure ⊆ U)
    (hboundary : ∀ z ∈ J.boundary, IsUnit (A.operator z))
    (freeOrbitMultiplicity : ℂ → ℕ)
    (hC : ∀ z ∈ J.interior,
      zeroMult A.determinant z = freeOrbitMultiplicity z) :
    let rootMultiplicityZero := jordanFredholmRootMultiplicity J A = 0
    let invertibleInside := ∀ z ∈ J.interior, IsUnit (A.operator z)
    let determinantZeroFree := ∀ z ∈ J.interior, A.determinant z ≠ 0
    let windingZero := jordanFredholmBoundaryWinding J A = 0
    let noFreeOrbit := ∀ z ∈ J.interior, freeOrbitMultiplicity z = 0
    (rootMultiplicityZero ↔ invertibleInside) ∧
      (invertibleInside ↔ determinantZeroFree) ∧
      (determinantZeroFree ↔ windingZero) ∧
      (windingZero ↔ noFreeOrbit) := by
  dsimp only
  obtain ⟨hU, hoperator, hdeterminant⟩ := hfamily
  let f : ℂ → ℂ := A.determinant ∘ J.chart
  have hclosedball : ∀ w ∈ closedBall (0 : ℂ) 1, J.chart w ∈ U := by
    intro w hw
    exact hclosure ⟨w, hw, rfl⟩
  have hfan : AnalyticOnNhd ℂ f (ball (0 : ℂ) 1) := by
    intro w hw
    exact (hdeterminant (J.chart w) (hclosedball w (ball_subset_closedBall hw))).comp
      (J.analytic_chart w hw)
  have hfc : ContinuousOn f (closedBall (0 : ℂ) 1) := by
    exact hdeterminant.continuousOn.comp J.chart.continuous.continuousOn hclosedball
  have hfboundary : ∀ w ∈ sphere (0 : ℂ) 1, f w ≠ 0 := by
    intro w hw hzero
    have hunit : IsUnit (A.operator (J.chart w)) := hboundary _ ⟨w, hw, rfl⟩
    exact (A.determinant_eq_zero_iff_not_isUnit (J.chart w)).mp hzero hunit
  have hcount_iff_preZeroFree : jordanFredholmRootMultiplicity J A = 0 ↔
      ∀ w ∈ ball (0 : ℂ) 1, f w ≠ 0 := by
    exact unitDiscZeroMultiplicity_eq_zero_iff hfan hfc hfboundary
  have hpreZeroFree_iff_inside :
      (∀ w ∈ ball (0 : ℂ) 1, f w ≠ 0) ↔
        ∀ z ∈ J.interior, A.determinant z ≠ 0 := by
    constructor
    · intro h z hz
      rcases hz with ⟨w, hw, rfl⟩
      exact h w hw
    · intro h w hw
      exact h (J.chart w) ⟨w, hw, rfl⟩
  have hroot_iff_det : jordanFredholmRootMultiplicity J A = 0 ↔
      ∀ z ∈ J.interior, A.determinant z ≠ 0 :=
    hcount_iff_preZeroFree.trans hpreZeroFree_iff_inside
  have hinv_iff_det :
      (∀ z ∈ J.interior, IsUnit (A.operator z)) ↔
        ∀ z ∈ J.interior, A.determinant z ≠ 0 := by
    constructor
    · intro hinv z hz hzero
      exact (A.determinant_eq_zero_iff_not_isUnit z).mp hzero (hinv z hz)
    · intro hfree z hz
      by_contra hnot
      exact hfree z hz ((A.determinant_eq_zero_iff_not_isUnit z).mpr hnot)
  have hwinding : jordanFredholmBoundaryWinding J A =
      (jordanFredholmRootMultiplicity J A : ℤ) := by
    exact windingNumber_unitCircle_eq_unitDiscZeroMultiplicity hfan hfc hfboundary
  have hdet_iff_winding :
      (∀ z ∈ J.interior, A.determinant z ≠ 0) ↔
        jordanFredholmBoundaryWinding J A = 0 := by
    rw [← hroot_iff_det]
    rw [hwinding]
    exact_mod_cast Nat.cast_eq_zero
  have hdet_iff_orbit :
      (∀ z ∈ J.interior, A.determinant z ≠ 0) ↔
        ∀ z ∈ J.interior, freeOrbitMultiplicity z = 0 := by
    constructor
    · intro hfree z hz
      rw [← hC z hz, zeroMult]
      exact congrArg ENat.toNat
        ((hdeterminant z (hclosure (by
          rcases hz with ⟨w, hw, rfl⟩
          exact ⟨w, ball_subset_closedBall hw, rfl⟩))).analyticOrderAt_eq_zero.mpr
            (hfree z hz))
    · intro horbit
      have hcount0 : jordanFredholmRootMultiplicity J A = 0 := by
        rw [jordanFredholmRootMultiplicity, unitDiscZeroMultiplicity]
        apply finsum_eq_zero_of_forall_eq_zero
        intro w
        by_cases hw : w ∈ ball (0 : ℂ) 1
        · rw [if_pos hw, zeroMult_determinant_comp_chart J A hw,
            hC (J.chart w) ⟨w, hw, rfl⟩, horbit (J.chart w) ⟨w, hw, rfl⟩]
        · rw [if_neg hw]
      exact hroot_iff_det.mp hcount0
  refine ⟨?_, hinv_iff_det, hdet_iff_winding, ?_⟩
  · exact hroot_iff_det.trans hinv_iff_det.symm
  · exact hdet_iff_winding.symm.trans hdet_iff_orbit

end

end GaloisForLFunctions.HTGeometry
