import GaloisForLFunctions.RHTower.SuzukiFiniteMorseResolventJetCompletion

/-!
# Resolvent-jet tomography of Suzuki's homogeneous Plücker blade

The actual two-shift Suzuki response is projective.  Its exact source carrier has homogeneous
blade `(v,0) ∧ (Av,1)`, whose one-mode coordinates are the Neumann homogeneous channel and whose
two-mode coordinates are Euler--Gamma spectral-pair curvature.

This file proves finite source tomography for that correct carrier.  A zero-constant polynomial
in one admissible resolvent can isolate any coordinate of a cyclic finite spectral source.  One
isolated mode gives the homogeneous coordinate; subtracting two one-mode blades from the blade of
their sum isolates the spectral pair with exact gap factor.  Thus finite resolvent jets see every
one-mode and two-mode direction required by a Christoffel--Darboux boundary matrix.

No positivity, RH premise, Xi-zero data, estimate, or computation is used.
-/

open Polynomial

namespace RHTower

noncomputable section

/-- Zero-constant Lagrange polynomial with arbitrary prescribed values at finite nonzero nodes. -/
def suzukiZeroConstantResolventInterpolant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (resolventNode value : ι → ℝ) : ℝ[X] :=
  X * Lagrange.interpolate Finset.univ resolventNode
    (fun i => value i / resolventNode i)

@[simp]
theorem suzukiZeroConstantResolventInterpolant_eval_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (resolventNode value : ι → ℝ) :
    (suzukiZeroConstantResolventInterpolant resolventNode value).eval 0 = 0 := by
  simp [suzukiZeroConstantResolventInterpolant]

/-- Exact arbitrary-value interpolation at every finite resolvent node. -/
theorem suzukiZeroConstantResolventInterpolant_eval
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (resolventNode value : ι → ℝ)
    (hnode : Function.Injective resolventNode)
    (hnode0 : ∀ i, resolventNode i ≠ 0) (i : ι) :
    (suzukiZeroConstantResolventInterpolant resolventNode value).eval
        (resolventNode i) = value i := by
  rw [suzukiZeroConstantResolventInterpolant, Polynomial.eval_mul, Polynomial.eval_X,
    Lagrange.eval_interpolate_at_node _ hnode.injOn (Finset.mem_univ i)]
  exact mul_div_cancel₀ _ (hnode0 i)

/-- Polynomial filter choosing desired spectral coordinates from a cyclic source. -/
def suzukiCyclicResolventFilter
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (resolventNode source target : ι → ℝ) : ℝ[X] :=
  suzukiZeroConstantResolventInterpolant resolventNode
    (fun i => target i / source i)

/-- Coordinate of the source after applying a scalar spectral polynomial. -/
def suzukiResolventFilteredSourceCoordinate
    {ι : Type*} (source resolventNode : ι → ℝ) (q : ℝ[X]) (i : ι) : ℝ :=
  source i * q.eval (resolventNode i)

/-- Cyclic source plus finite resolvent interpolation realizes an arbitrary target vector. -/
theorem suzukiCyclicResolventFilter_realizes_target
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (resolventNode source target : ι → ℝ)
    (hnode : Function.Injective resolventNode)
    (hnode0 : ∀ i, resolventNode i ≠ 0)
    (hsource0 : ∀ i, source i ≠ 0) (i : ι) :
    suzukiResolventFilteredSourceCoordinate source resolventNode
        (suzukiCyclicResolventFilter resolventNode source target) i = target i := by
  rw [suzukiResolventFilteredSourceCoordinate, suzukiCyclicResolventFilter,
    suzukiZeroConstantResolventInterpolant_eval resolventNode
      (fun j => target j / source j) hnode hnode0 i]
  rw [mul_comm]
  exact div_mul_cancel₀ _ (hsource0 i)

/-- Function-level form: finite jet filter recovers every coordinate of target simultaneously. -/
theorem suzukiCyclicResolventFilter_realizes_target_fun
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (resolventNode source target : ι → ℝ)
    (hnode : Function.Injective resolventNode)
    (hnode0 : ∀ i, resolventNode i ≠ 0)
    (hsource0 : ∀ i, source i ≠ 0) :
    (fun i => suzukiResolventFilteredSourceCoordinate source resolventNode
      (suzukiCyclicResolventFilter resolventNode source target) i) = target := by
  funext i
  exact suzukiCyclicResolventFilter_realizes_target
    resolventNode source target hnode hnode0 hsource0 i

/-- Kronecker spectral coordinate. -/
def suzukiSpectralCoordinateUnit
    {ι : Type*} [DecidableEq ι] (i : ι) : ι → ℝ :=
  fun j => if j = i then 1 else 0

/-- Coefficient of `e_i ∧ infinity` in homogeneous blade `(v,0) ∧ (Av,1)`. -/
def suzukiHomogeneousBladeInfinityCoordinate
    {ι : Type*} (v : ι → ℝ) (i : ι) : ℝ :=
  v i

/-- Coefficient of `e_i ∧ e_j` in homogeneous blade `(v,0) ∧ (Av,1)`. -/
def suzukiHomogeneousBladePairCoordinate
    {ι : Type*} (spectralLevel v : ι → ℝ) (i j : ι) : ℝ :=
  (spectralLevel j - spectralLevel i) * v i * v j

/-- Polarizing homogeneous blades cancels one-mode coordinates identically. -/
theorem suzukiHomogeneousBladeInfinityCoordinate_polarization
    {ι : Type*} (v w : ι → ℝ) (i : ι) :
    suzukiHomogeneousBladeInfinityCoordinate (v + w) i -
        suzukiHomogeneousBladeInfinityCoordinate v i -
        suzukiHomogeneousBladeInfinityCoordinate w i = 0 := by
  simp [suzukiHomogeneousBladeInfinityCoordinate]

/-- Exact polarization of spectral-pair coordinate. -/
theorem suzukiHomogeneousBladePairCoordinate_polarization
    {ι : Type*} (spectralLevel v w : ι → ℝ) (i j : ι) :
    suzukiHomogeneousBladePairCoordinate spectralLevel (v + w) i j -
        suzukiHomogeneousBladePairCoordinate spectralLevel v i j -
        suzukiHomogeneousBladePairCoordinate spectralLevel w i j =
      (spectralLevel j - spectralLevel i) * (v i * w j + w i * v j) := by
  simp only [suzukiHomogeneousBladePairCoordinate, Pi.add_apply]
  ring

/-- A single isolated spectral mode has no Euler--Gamma pair curvature. -/
theorem suzukiHomogeneousBladePairCoordinate_unit_eq_zero
    {ι : Type*} [DecidableEq ι] (spectralLevel : ι → ℝ)
    (mode i j : ι) (hij : i ≠ j) :
    suzukiHomogeneousBladePairCoordinate spectralLevel
      (suzukiSpectralCoordinateUnit mode) i j = 0 := by
  by_cases hi : i = mode
  · have hj : j ≠ mode := by
      intro h
      apply hij
      exact hi.trans h.symm
    simp [suzukiHomogeneousBladePairCoordinate, suzukiSpectralCoordinateUnit, hi, hj]
  · simp [suzukiHomogeneousBladePairCoordinate, suzukiSpectralCoordinateUnit, hi]

/-- Subtracting two one-mode blades from their summed blade isolates exactly one ordered spectral
pair, with the nonzero gap factor and no node-sign factor. -/
theorem suzukiHomogeneousBlade_twoModeDifference_isolates_pair
    {ι : Type*} [DecidableEq ι] (spectralLevel : ι → ℝ)
    (i j : ι) (hij : i ≠ j) :
    suzukiHomogeneousBladePairCoordinate spectralLevel
          (suzukiSpectralCoordinateUnit i + suzukiSpectralCoordinateUnit j) i j -
        suzukiHomogeneousBladePairCoordinate spectralLevel
          (suzukiSpectralCoordinateUnit i) i j -
        suzukiHomogeneousBladePairCoordinate spectralLevel
          (suzukiSpectralCoordinateUnit j) i j =
      spectralLevel j - spectralLevel i := by
  rw [suzukiHomogeneousBladePairCoordinate_polarization]
  simp [suzukiSpectralCoordinateUnit, hij, hij.symm]

/-- Same two-mode difference has no residual homogeneous/Neumann coordinate. -/
theorem suzukiHomogeneousBlade_twoModeDifference_infinity_zero
    {ι : Type*} [DecidableEq ι] (i j k : ι) :
    suzukiHomogeneousBladeInfinityCoordinate
          (suzukiSpectralCoordinateUnit i + suzukiSpectralCoordinateUnit j) k -
        suzukiHomogeneousBladeInfinityCoordinate (suzukiSpectralCoordinateUnit i) k -
        suzukiHomogeneousBladeInfinityCoordinate (suzukiSpectralCoordinateUnit j) k = 0 := by
  exact suzukiHomogeneousBladeInfinityCoordinate_polarization
    (suzukiSpectralCoordinateUnit i) (suzukiSpectralCoordinateUnit j) k

/-- Resolvent-node specialization: simple spectral levels and a cyclic source produce any target
homogeneous coordinate packet using one below-spectrum resolvent jet. -/
theorem suzukiSpectralResolventJet_realizes_target
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : ℝ) (spectralLevel source target : ι → ℝ)
    (hlevel : Function.Injective spectralLevel)
    (hrho : ∀ i, rho < spectralLevel i)
    (hsource0 : ∀ i, source i ≠ 0) :
    (fun i => suzukiResolventFilteredSourceCoordinate source
      (fun j => suzukiFiniteMorseResolventNode rho (spectralLevel j))
      (suzukiCyclicResolventFilter
        (fun j => suzukiFiniteMorseResolventNode rho (spectralLevel j)) source target) i) = target := by
  apply suzukiCyclicResolventFilter_realizes_target_fun
  · exact suzukiFiniteMorseResolventNode_injective hlevel
  · exact fun i => suzukiFiniteMorseResolventNode_ne_zero (hrho i)
  · exact hsource0

end

end RHTower
