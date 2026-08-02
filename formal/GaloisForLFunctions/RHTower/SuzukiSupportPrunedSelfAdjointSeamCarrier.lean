import GaloisForLFunctions.RHTower.SuzukiPrimeValuationSeam
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicAffineProjection

/-!
# Support-pruned self-adjoint carrier for Suzuki prime seams

At fixed aperture Suzuki's visible prime-power alphabet is finite.  This module realizes its
oriented valuation transport on complex `ell²`, proves that every symmetric valuation step is
self-adjoint, and proves that strict-aperture support pruning preserves self-adjointness by
orthogonal compression.  The two endpoint roots remain oriented labels at opposite-end spatial
resonances.

No theorem here asserts that Suzuki's completed form domain maps into this `ell²` carrier.  That is
the separate source-analytic trace-zero regularity problem.
-/

open Complex Set
open scoped BigOperators ENNReal InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.RHTower

open ContinuousLinearMap
open GaloisForLFunctions.HTGeometry

/-- Oriented endpoint from which a seam germ descends. -/
inductive SuzukiSeamRoot
  | left
  | right
  deriving DecidableEq

/-- Complete finite-support prime-valuation label. -/
abbrev SuzukiSeamValuation := Nat.Primes →₀ ℤ

/-- Oriented seam vertex.  Root labels are retained at opposite-end spatial resonances. -/
abbrev SuzukiSeamVertex := SuzukiSeamRoot × SuzukiSeamValuation

/-- Exact Hilbert coefficient carrier for square-summable oriented seam amplitudes. -/
abbrev SuzukiSeamHilbert := lp (fun _ : SuzukiSeamVertex => ℂ) 2

/-- Physical logarithmic position of an oriented seam vertex. -/
def suzukiSeamLocation (a : ℝ) : SuzukiSeamVertex → ℝ
  | (.left, ν) => -a + primeSeamCoordinate ν
  | (.right, ν) => a - primeSeamCoordinate ν

/-- Strict-interior vertices retained by aperture compression. -/
def suzukiAdmissibleSeamVertices (a : ℝ) : Set SuzukiSeamVertex :=
  {q | |suzukiSeamLocation a q| < a}

/-- Translation of the valuation label while preserving oriented root. -/
def suzukiSeamVertexShiftEquiv (δ : SuzukiSeamValuation) :
    SuzukiSeamVertex ≃ SuzukiSeamVertex :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.addRight δ)

/-- Unitary valuation translation on the oriented seam Hilbert carrier. -/
def suzukiSeamShift (δ : SuzukiSeamValuation) :
    SuzukiSeamHilbert ≃ₗᵢ[ℂ] SuzukiSeamHilbert :=
  _root_.RHTower.lpReindexEquiv (suzukiSeamVertexShiftEquiv δ)

@[simp] theorem suzukiSeamShift_apply
    (δ : SuzukiSeamValuation) (f : SuzukiSeamHilbert)
    (q : SuzukiSeamVertex) :
    suzukiSeamShift δ f q =
      f (q.1, q.2 - δ) := by
  rcases q with ⟨root, ν⟩
  simp [suzukiSeamShift, suzukiSeamVertexShiftEquiv, sub_eq_add_neg]

/-- Real symmetric Laurent step `U_delta + U_delta*`. -/
def suzukiSymmetricSeamStep (δ : SuzukiSeamValuation) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert) +
    ContinuousLinearMap.adjoint
      (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert)

theorem suzukiSymmetricSeamStep_isSelfAdjoint (δ : SuzukiSeamValuation) :
    IsSelfAdjoint (suzukiSymmetricSeamStep δ) := by
  exact IsSelfAdjoint.add_star_self
    (suzukiSeamShift δ : SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert)

@[simp] theorem suzukiSymmetricSeamStep_apply
    (δ : SuzukiSeamValuation) (f : SuzukiSeamHilbert)
    (q : SuzukiSeamVertex) :
    suzukiSymmetricSeamStep δ f q =
      f (q.1, q.2 - δ) + f (q.1, q.2 + δ) := by
  rw [suzukiSymmetricSeamStep, add_apply]
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  change suzukiSeamShift δ f q + (suzukiSeamShift δ).symm f q = _
  rw [suzukiSeamShift_apply]
  change f (q.1, q.2 - δ) +
    _root_.RHTower.lpReindexEquiv (suzukiSeamVertexShiftEquiv δ).symm f q = _
  rcases q with ⟨root, ν⟩
  change f (root, ν - δ) +
    f (suzukiSeamVertexShiftEquiv δ (root, ν)) =
    f (root, ν - δ) + f (root, ν + δ)
  simp [suzukiSeamVertexShiftEquiv]

/-- Finite real symmetric valuation Laurent polynomial with Suzuki's prime-term sign. -/
def suzukiFinitePrimeAdjacency
    {ι : Type*} (steps : ι → SuzukiSeamValuation)
    (weight : ι → ℝ) (s : Finset ι) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  ∑ i ∈ s, (-(weight i : ℂ)) • suzukiSymmetricSeamStep (steps i)

theorem suzukiFinitePrimeAdjacency_isSelfAdjoint
    {ι : Type*} (steps : ι → SuzukiSeamValuation)
    (weight : ι → ℝ) (s : Finset ι) :
    IsSelfAdjoint (suzukiFinitePrimeAdjacency steps weight s) := by
  classical
  apply isSelfAdjoint_sum
  intro i hi
  apply IsSelfAdjoint.smul
  · simp [IsSelfAdjoint]
  · exact suzukiSymmetricSeamStep_isSelfAdjoint (steps i)

/-- Exact strict-aperture compression `P_S A P_S` of finite prime adjacency. -/
def suzukiSupportPrunedPrimeAdjacency
    {ι : Type*} (a : ℝ) (steps : ι → SuzukiSeamValuation)
    (weight : ι → ℝ) (s : Finset ι) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  let P := lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
  P ∘L suzukiFinitePrimeAdjacency steps weight s ∘L P

/-- Gamma-normalized positive adjacency.  `suzukiSupportPrunedPrimeAdjacency` already contains
Suzuki's negative prime-symbol sign, while the Gamma equation is written as `scalar - T`. -/
def suzukiGammaPositivePrimeAdjacency
    {ι : Type*} (a : ℝ) (steps : ι → SuzukiSeamValuation)
    (weight : ι → ℝ) (s : Finset ι) :
    SuzukiSeamHilbert →L[ℂ] SuzukiSeamHilbert :=
  -suzukiSupportPrunedPrimeAdjacency a steps weight s

/-- Orthogonal support pruning preserves self-adjointness of exact finite prime transport. -/
theorem suzukiSupportPrunedPrimeAdjacency_isSelfAdjoint
    {ι : Type*} (a : ℝ) (steps : ι → SuzukiSeamValuation)
    (weight : ι → ℝ) (s : Finset ι) :
    IsSelfAdjoint (suzukiSupportPrunedPrimeAdjacency a steps weight s) := by
  let P := lpCoordinateProjection (suzukiAdmissibleSeamVertices a)
  have hP : ContinuousLinearMap.adjoint P = P :=
    lpCoordinateProjection_selfAdjoint _
  have hA :=
    (suzukiFinitePrimeAdjacency_isSelfAdjoint steps weight s).conj_adjoint P
  simpa only [suzukiSupportPrunedPrimeAdjacency, P, hP] using hA

/-- Negating the already-negative Suzuki adjacency gives the sign-correct bounded self-adjoint
coupling in a Gamma equation normalized as `scalar - T`. -/
theorem suzukiGammaPositivePrimeAdjacency_isSelfAdjoint
    {ι : Type*} (a : ℝ) (steps : ι → SuzukiSeamValuation)
    (weight : ι → ℝ) (s : Finset ι) :
    IsSelfAdjoint (suzukiGammaPositivePrimeAdjacency a steps weight s) := by
  exact (suzukiSupportPrunedPrimeAdjacency_isSelfAdjoint a steps weight s).neg

/-- Left endpoint root is forcing data, not a homogeneous strict-interior coordinate. -/
theorem suzukiSeamRoot_left_not_admissible (a : ℝ) (ha : 0 < a) :
    (SuzukiSeamRoot.left, 0) ∉ suzukiAdmissibleSeamVertices a := by
  simp [suzukiAdmissibleSeamVertices, suzukiSeamLocation, abs_of_pos ha]

/-- Right endpoint root is forcing data, not a homogeneous strict-interior coordinate. -/
theorem suzukiSeamRoot_right_not_admissible (a : ℝ) (ha : 0 < a) :
    (SuzukiSeamRoot.right, 0) ∉ suzukiAdmissibleSeamVertices a := by
  simp [suzukiAdmissibleSeamVertices, suzukiSeamLocation, abs_of_pos ha]

end GaloisForLFunctions.RHTower
