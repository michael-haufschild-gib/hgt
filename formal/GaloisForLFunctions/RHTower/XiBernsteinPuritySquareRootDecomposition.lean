import GaloisForLFunctions.RHTower.FiniteBernsteinDiagonalSquareRootDecomposition
import GaloisForLFunctions.RHTower.PrimeArchBernsteinExactHalfOrderAbelBoundary

/-!
# Exact maximal-diagonal square-root decomposition of the Xi susceptibility

If RH fails, the full endpoint susceptibility has one finite source-attained maximal packet.
The diagonal part of that packet is an exact finite sum of algebraic square-root kernels.  After
subtracting this explicit term, the remaining full Xi source has zero square-root-scaled Abel
boundary.  Thus the universal half-order singularity is localized in a finite, positive,
source-selected diagonal packet rather than only detected through a coefficient asymptotic.
-/

open Complex Filter Topology
open scoped BigOperators Real
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Positive diagonal energy carried by a finite Xi coordinate packet. -/
def xiEndpointCoordinateDiagonalPurity (D : Finset XiZeroCopy) (n : ℕ) : ℝ :=
  finiteBernsteinCoordinateDiagonalEnergy
    (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) n

/-- The full-purity remainder after removing the finite Xi diagonal packet. -/
def primeArchEndpointBernsteinDiagonalRemainder
    (D : Finset XiZeroCopy) (n : ℕ) : ℝ :=
  primeArchEndpointBernsteinPurity n - xiEndpointCoordinateDiagonalPurity D n

/-- Abel susceptibility of the finite Xi diagonal packet. -/
def xiEndpointCoordinateDiagonalAbelSusceptibility
    (D : Finset XiZeroCopy) (t : ℝ) : ℝ :=
  ∑' n : ℕ, xiEndpointCoordinateDiagonalPurity D n * t ^ n

/-- Abel susceptibility of the remainder after the maximal diagonal packet is removed. -/
def primeArchEndpointBernsteinDiagonalRemainderAbelSusceptibility
    (D : Finset XiZeroCopy) (t : ℝ) : ℝ :=
  ∑' n : ℕ, primeArchEndpointBernsteinDiagonalRemainder D n * t ^ n

private lemma xiEndpoint_coordinate_amplitude
    {D : Finset XiZeroCopy} {B : ℝ}
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    {u : ℂ} (hu : u ∈ xiEndpointCoordinateSet D) :
    ‖u‖ + ‖1 - u‖ = B := by
  obtain ⟨q, hqD, rfl⟩ := Finset.mem_image.mp hu
  simpa only [xiEndpointBernsteinAtomAmplitudeBase] using hD q hqD

private lemma xiEndpoint_coordinate_ne_zero
    {D : Finset XiZeroCopy} {B : ℝ} (hB : 1 < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    {u : ℂ} (hu : u ∈ xiEndpointCoordinateSet D) : u ≠ 0 := by
  intro hu0
  have hamp := xiEndpoint_coordinate_amplitude hD hu
  rw [hu0] at hamp
  norm_num at hamp
  linarith

private lemma xiEndpoint_coordinate_ne_one
    {D : Finset XiZeroCopy} {B : ℝ} (hB : 1 < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    {u : ℂ} (hu : u ∈ xiEndpointCoordinateSet D) : u ≠ 1 := by
  intro hu1
  have hamp := xiEndpoint_coordinate_amplitude hD hu
  rw [hu1] at hamp
  norm_num at hamp
  linarith

/-- The finite Xi diagonal packet has the sharp positive half-order coefficient displayed by its
occupied coordinate fibres. -/
theorem tendsto_sqrtNat_mul_xiEndpointCoordinateDiagonalPurity_div_pow
    {D : Finset XiZeroCopy} {B : ℝ} (hB : 1 < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) :
    Tendsto
      (fun n : ℕ => Real.sqrt n * xiEndpointCoordinateDiagonalPurity D n /
        (B ^ 2) ^ n)
      atTop
      (nhds (∑ u ∈ xiEndpointCoordinateSet D,
        ‖xiEndpointCoordinateWeight D u‖ ^ 2 *
          bernsteinAffineRowHalfOrderConstant u)) := by
  exact tendsto_sqrtNat_mul_finiteBernsteinCoordinateDiagonalEnergy_div_pow
    (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D)
    (lt_trans zero_lt_one hB)
    (fun u hu => xiEndpoint_coordinate_amplitude hD hu)
    (fun u hu => xiEndpoint_coordinate_ne_zero hB hD hu)
    (fun u hu => xiEndpoint_coordinate_ne_one hB hD hu)

/-- The finite Xi diagonal susceptibility is exactly the finite square-root kernel throughout
the open maximal-packet collar. -/
theorem hasSum_xiEndpointCoordinateDiagonalPurity_eq_squareRootKernel
    {D : Finset XiZeroCopy} {B t : ℝ} (hB : 1 < B)
    (hD : ∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B)
    (ht0 : 0 < t) (htB : t < 1 / B ^ 2) :
    HasSum
      (fun n : ℕ => xiEndpointCoordinateDiagonalPurity D n * t ^ n)
      (finiteBernsteinCoordinateDiagonalSquareRootKernel
        (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) B t) := by
  exact hasSum_finiteBernsteinCoordinateDiagonalEnergy_eq_squareRootKernel
    (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D)
    (lt_trans zero_lt_one hB)
    (fun u hu => xiEndpoint_coordinate_amplitude hD hu)
    (fun u hu => xiEndpoint_coordinate_ne_zero hB hD hu)
    (fun u hu => xiEndpoint_coordinate_ne_one hB hD hu) ht0 htB

/-- **Exact false-phase square-root decomposition.**  If RH fails, one finite maximal Xi packet
has an exact algebraic diagonal Abel kernel.  The complete Xi susceptibility is that kernel plus
a summable remainder at every interior point, and the remainder vanishes after multiplication by
the boundary square root. -/
theorem exists_exact_maximalDiagonalSquareRootDecomposition_of_not_rh
    (hRH : ¬ RiemannHypothesis) :
    ∃ D : Finset XiZeroCopy, ∃ B beta L : ℝ,
      1 < B ∧ 1 < beta ∧ beta < B ∧ D.Nonempty ∧
      (∀ q ∈ D, xiEndpointBernsteinAtomAmplitudeBase q = B) ∧
      (∀ q ∉ D, xiEndpointBernsteinAtomAmplitudeBase q ≤ beta) ∧
      L = ∑ u ∈ xiEndpointCoordinateSet D,
        ‖xiEndpointCoordinateWeight D u‖ ^ 2 *
          bernsteinAffineRowHalfOrderConstant u ∧
      0 < L ∧
      PrimeArchEndpointBernsteinAbelCriticalRadius (1 / B ^ 2) ∧
      (∀ t : ℝ, 0 < t → t < 1 / B ^ 2 →
        HasSum
          (fun n : ℕ => xiEndpointCoordinateDiagonalPurity D n * t ^ n)
          (finiteBernsteinCoordinateDiagonalSquareRootKernel
            (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) B t)) ∧
      (∀ t : ℝ, 0 < t → t < 1 / B ^ 2 →
        primeArchEndpointBernsteinAbelSusceptibility t =
          finiteBernsteinCoordinateDiagonalSquareRootKernel
            (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) B t +
          primeArchEndpointBernsteinDiagonalRemainderAbelSusceptibility D t) ∧
      Tendsto
        (fun t : ℝ => Real.sqrt (1 - B ^ 2 * t) *
          primeArchEndpointBernsteinDiagonalRemainderAbelSusceptibility D t)
        (nhdsWithin (1 / B ^ 2) (Set.Ico 0 (1 / B ^ 2)))
        (nhds 0) ∧
      Tendsto
        (fun t : ℝ => Real.sqrt (1 - B ^ 2 * t) *
          xiEndpointCoordinateDiagonalAbelSusceptibility D t)
        (nhdsWithin (1 / B ^ 2) (Set.Ico 0 (1 / B ^ 2)))
        (nhds (Real.sqrt Real.pi * L)) ∧
      Tendsto
        (fun t : ℝ => Real.sqrt (1 - B ^ 2 * t) *
          primeArchEndpointBernsteinAbelSusceptibility t)
        (nhdsWithin (1 / B ^ 2) (Set.Ico 0 (1 / B ^ 2)))
        (nhds (Real.sqrt Real.pi * L)) := by
  obtain ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hL, hLpos, hfullCoeff⟩ :=
    exists_positive_halfOrder_primeArchEndpointBernsteinPurity_of_not_rh hRH
  have hBpos : 0 < B := lt_trans zero_lt_one hB
  have hdiagCoeff :=
    tendsto_sqrtNat_mul_xiEndpointCoordinateDiagonalPurity_div_pow hB hD
  have hremCoeff : Tendsto
      (fun n : ℕ => Real.sqrt n *
        primeArchEndpointBernsteinDiagonalRemainder D n / (B ^ 2) ^ n)
      atTop (nhds 0) := by
    have hsub := hfullCoeff.sub hdiagCoeff
    convert hsub using 1
    · funext n
      rw [primeArchEndpointBernsteinDiagonalRemainder]
      ring
    · rw [hL]
      ring
  obtain ⟨B', hthreshold, hcritical⟩ :=
    exists_attained_primeArchEndpointBernsteinAbelCriticalRadius_of_not_rh hRH
  obtain ⟨qD, hqD⟩ := hDne
  have hB_le : B ≤ B' := by
    calc
      B = xiEndpointBernsteinAtomAmplitudeBase qD := (hD qD hqD).symm
      _ ≤ B' := hthreshold.2.2.2.1 qD
  obtain ⟨q', hq'⟩ := hthreshold.2.2.1
  have hB'_le : B' ≤ B := by
    calc
      B' = xiEndpointBernsteinAtomAmplitudeBase q' := hq'.symm
      _ ≤ B := by
        by_cases hqmem : q' ∈ D
        · exact (hD q' hqmem).le
        · exact (hDsub q' hqmem).trans hbeta.le
  have hBB' : B = B' := le_antisymm hB_le hB'_le
  have hcriticalB : PrimeArchEndpointBernsteinAbelCriticalRadius (1 / B ^ 2) := by
    rw [hBB']
    exact hcritical
  have hdiagExact : ∀ t : ℝ, 0 < t → t < 1 / B ^ 2 →
      HasSum
        (fun n : ℕ => xiEndpointCoordinateDiagonalPurity D n * t ^ n)
        (finiteBernsteinCoordinateDiagonalSquareRootKernel
          (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) B t) := by
    intro t ht0 htB
    exact hasSum_xiEndpointCoordinateDiagonalPurity_eq_squareRootKernel
      hB hD ht0 htB
  have hpointDecomp : ∀ t : ℝ, 0 < t → t < 1 / B ^ 2 →
      primeArchEndpointBernsteinAbelSusceptibility t =
        finiteBernsteinCoordinateDiagonalSquareRootKernel
          (xiEndpointCoordinateSet D) (xiEndpointCoordinateWeight D) B t +
        primeArchEndpointBernsteinDiagonalRemainderAbelSusceptibility D t := by
    intro t ht0 htB
    have hfullSum := hcriticalB.2.1 t ht0.le htB
    have hdiagSum := hdiagExact t ht0 htB
    have hremSum : Summable (fun n : ℕ =>
        primeArchEndpointBernsteinDiagonalRemainder D n * t ^ n) := by
      have hsub := hfullSum.sub hdiagSum.summable
      apply hsub.congr
      intro n
      rw [primeArchEndpointBernsteinDiagonalRemainder]
      ring
    rw [primeArchEndpointBernsteinAbelSusceptibility,
      primeArchEndpointBernsteinDiagonalRemainderAbelSusceptibility]
    calc
      (∑' n : ℕ, primeArchEndpointBernsteinPurity n * t ^ n) =
          ∑' n : ℕ,
            (xiEndpointCoordinateDiagonalPurity D n * t ^ n +
              primeArchEndpointBernsteinDiagonalRemainder D n * t ^ n) := by
        apply tsum_congr
        intro n
        rw [primeArchEndpointBernsteinDiagonalRemainder]
        ring
      _ = (∑' n : ℕ, xiEndpointCoordinateDiagonalPurity D n * t ^ n) +
          ∑' n : ℕ,
            primeArchEndpointBernsteinDiagonalRemainder D n * t ^ n := by
        rw [hdiagSum.summable.tsum_add hremSum]
      _ = _ := by rw [hdiagSum.tsum_eq]
  have hremBoundary :=
    tendsto_sqrt_scaled_boundary_mul_tsum_of_halfOrder hBpos hremCoeff
  have hdiagBoundary :=
    tendsto_sqrt_scaled_boundary_mul_tsum_of_halfOrder hBpos hdiagCoeff
  have hfullBoundary :=
    tendsto_sqrt_scaled_boundary_mul_tsum_of_halfOrder hBpos hfullCoeff
  refine ⟨D, B, beta, L, hB, hbeta1, hbeta, ⟨qD, hqD⟩, hD, hDsub, hL,
    hLpos, hcriticalB, hdiagExact, hpointDecomp, ?_, ?_, ?_⟩
  · simpa only [primeArchEndpointBernsteinDiagonalRemainderAbelSusceptibility,
      mul_zero] using hremBoundary
  · simpa only [xiEndpointCoordinateDiagonalAbelSusceptibility, hL] using hdiagBoundary
  · simpa only [primeArchEndpointBernsteinAbelSusceptibility] using hfullBoundary

end

end RHTower
