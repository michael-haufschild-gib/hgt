import GaloisForLFunctions.RHTower.FiniteBernsteinCoordinatePacketAsymptotic
import GaloisForLFunctions.HTGeometry.CentralBinomialDiagonalKernel

/-!
# Exact square-root kernel of a finite Bernstein diagonal packet

The diagonal part of a finite affine Bernstein packet has two simultaneous descriptions.  Its
coefficients have the universal half-order asymptotic, while its Abel sum is an exact finite sum
of factored square-root kernels.  This is the generic algebraic component of the maximal-packet
decomposition used by the Xi endpoint susceptibility.
-/

open Complex Filter Topology
open scoped BigOperators Real
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The diagonal square energy of a finite affine-coordinate packet. -/
def finiteBernsteinCoordinateDiagonalEnergy
    (U : Finset ℂ) (C : ℂ → ℂ) (n : ℕ) : ℝ :=
  ∑ u ∈ U, ‖C u‖ ^ 2 * bernsteinAffineRowEnergy u n

/-- Equal-amplitude nondegenerate coordinates have the expected half-order diagonal limit.
Positivity of the common amplitude is automatic for a nonempty packet; the empty packet is zero. -/
theorem tendsto_sqrtNat_mul_finiteBernsteinCoordinateDiagonalEnergy_div_pow
    (U : Finset ℂ) (C : ℂ → ℂ) {B : ℝ}
    (hamp : ∀ u ∈ U, ‖u‖ + ‖1 - u‖ = B)
    (hu0 : ∀ u ∈ U, u ≠ 0) (hu1 : ∀ u ∈ U, u ≠ 1) :
    Tendsto
      (fun n : ℕ => Real.sqrt n *
        finiteBernsteinCoordinateDiagonalEnergy U C n / (B ^ 2) ^ n)
      atTop
      (nhds (∑ u ∈ U,
        ‖C u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u)) := by
  have hterm (u : ℂ) (hu : u ∈ U) : Tendsto
      (fun n : ℕ => Real.sqrt n *
        (‖C u‖ ^ 2 * bernsteinAffineRowEnergy u n) / (B ^ 2) ^ n)
      atTop
      (nhds (‖C u‖ ^ 2 * bernsteinAffineRowHalfOrderConstant u)) := by
    have hrow := tendsto_sqrtNat_mul_bernsteinAffineRowEnergy_div_pow
      (hu0 u hu) (hu1 u hu)
    have hrowB : Tendsto
        (fun n : ℕ => Real.sqrt n * bernsteinAffineRowEnergy u n / (B ^ 2) ^ n)
        atTop (nhds (bernsteinAffineRowHalfOrderConstant u)) := by
      simpa only [hamp u hu, bernsteinAffineRowHalfOrderConstant] using hrow
    convert hrowB.const_mul (‖C u‖ ^ 2) using 1
    funext n
    ring
  have hsum := tendsto_finsetSum U (fun u hu => hterm u hu)
  convert hsum using 1
  funext n
  rw [finiteBernsteinCoordinateDiagonalEnergy, Finset.mul_sum, Finset.sum_div]

/-- The exact finite algebraic Abel kernel of the diagonal packet. -/
def finiteBernsteinCoordinateDiagonalSquareRootKernel
    (U : Finset ℂ) (C : ℂ → ℂ) (B t : ℝ) : ℝ :=
  ∑ u ∈ U, ‖C u‖ ^ 2 *
    bernsteinSquareRootKernel B (‖u‖ - ‖1 - u‖) t

/-- Inside the first characteristic radius, the Abel sum of the diagonal packet is exactly its
finite square-root kernel.  Positivity of the common amplitude follows from any occupied
nondegenerate coordinate; the empty packet is zero. -/
theorem hasSum_finiteBernsteinCoordinateDiagonalEnergy_eq_squareRootKernel
    (U : Finset ℂ) (C : ℂ → ℂ) {B t : ℝ}
    (hamp : ∀ u ∈ U, ‖u‖ + ‖1 - u‖ = B)
    (hu0 : ∀ u ∈ U, u ≠ 0) (hu1 : ∀ u ∈ U, u ≠ 1)
    (ht0 : 0 < t) (htB : t < 1 / B ^ 2) :
    HasSum
      (fun n : ℕ => finiteBernsteinCoordinateDiagonalEnergy U C n * t ^ n)
      (finiteBernsteinCoordinateDiagonalSquareRootKernel U C B t) := by
  by_cases hU : U.Nonempty
  · obtain ⟨u, hu⟩ := hU
    have hB : 0 < B := by
      rw [← hamp u hu]
      exact add_pos_of_pos_of_nonneg
        (norm_pos_iff.mpr (hu0 u hu)) (norm_nonneg _)
    have hBsq : 0 < B ^ 2 := sq_pos_of_pos hB
    have hBt : B ^ 2 * t < 1 := by
      simpa only [mul_comm] using (lt_div_iff₀ hBsq).mp htB
    have hterm (u : ℂ) (hu : u ∈ U) : HasSum
        (fun n : ℕ =>
          (‖C u‖ ^ 2 * bernsteinAffineRowEnergy u n) * t ^ n)
        (‖C u‖ ^ 2 *
          bernsteinSquareRootKernel B (‖u‖ - ‖1 - u‖) t) := by
      let D : ℝ := ‖u‖ - ‖1 - u‖
      have ha : 0 < ‖u‖ := norm_pos_iff.mpr (hu0 u hu)
      have hb : 0 < ‖1 - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hu1 u hu).symm)
      have hDsq : D ^ 2 < B ^ 2 := by
        dsimp only [D]
        rw [← hamp u hu]
        nlinarith
      have hDt : D ^ 2 * t < 1 :=
        (mul_lt_mul_of_pos_right hDsq ht0).trans hBt
      have hkernel := hasSum_centralBinomialDiagonalKernelCoefficient_eq_kernel
        ht0 hBt hDt
      have hrow : HasSum
          (fun n : ℕ => bernsteinAffineRowEnergy u n * t ^ n)
          (bernsteinSquareRootKernel B D t) := by
        rw [show (fun n : ℕ => bernsteinAffineRowEnergy u n * t ^ n) =
            fun n : ℕ => centralBinomialDiagonalKernelCoefficient B D n * t ^ n by
          funext n
          rw [bernsteinAffineRowEnergy_eq_centralBinomialDiagonalKernelCoefficient,
            hamp u hu]]
        exact hkernel
      simpa only [mul_assoc] using hrow.mul_left (‖C u‖ ^ 2)
    have hsum_aux (V : Finset ℂ) (hVU : V ⊆ U) : HasSum
        (fun n : ℕ => ∑ u ∈ V,
          (‖C u‖ ^ 2 * bernsteinAffineRowEnergy u n) * t ^ n)
        (∑ u ∈ V, ‖C u‖ ^ 2 *
          bernsteinSquareRootKernel B (‖u‖ - ‖1 - u‖) t) := by
      classical
      induction V using Finset.induction_on with
      | empty => simp
      | @insert u V huV ih =>
          have huU : u ∈ U := hVU (Finset.mem_insert_self u V)
          have hVsub : V ⊆ U := fun v hv => hVU (Finset.mem_insert_of_mem hv)
          simpa only [Finset.sum_insert huV] using (hterm u huU).add (ih hVsub)
    have hsum := hsum_aux U (fun _ h => h)
    apply hsum.congr
    intro n
    simp only [finiteBernsteinCoordinateDiagonalEnergy, Finset.sum_mul]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hU]
    simp [finiteBernsteinCoordinateDiagonalEnergy,
      finiteBernsteinCoordinateDiagonalSquareRootKernel]

end

end RHTower
