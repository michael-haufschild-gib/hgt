import GaloisForLFunctions.HeightHomotopyArithmeticCounts.InfiniteTorsionForms
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedProbeSpace
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Continuous completion of arithmetic kernels

A uniform finite absolute quadratic bound gives absolutely convergent mixed
pairings on the weighted Hilbert carrier. Normalizing both arguments yields a
bilinear norm bound. The continuous completion retains the original kernel
series and inherits symmetry when the kernel is symmetric.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts

/-- The arithmetic kernel pairing in weighted Hilbert coordinates. -/
def weightedKernelPairing (δ : ℝ) (K : ℕ → ℕ → ℝ) (u v : WeightedProbe δ) : ℝ :=
  ∑' p : ℕ×ℕ, probeCoefficients δ u p.1*probeCoefficients δ v p.2*K p.1 p.2

/-- A symmetric arithmetic kernel gives a symmetric Hilbert pairing. -/
theorem weightedKernelPairing_comm (δ : ℝ) (K : ℕ → ℕ → ℝ)
    (hK : ∀ m n, K m n=K n m) (u v : WeightedProbe δ) :
    weightedKernelPairing δ K u v=weightedKernelPairing δ K v u := by
  unfold weightedKernelPairing
  rw [← (Equiv.prodComm ℕ ℕ).tsum_eq]
  apply tsum_congr
  intro p
  change probeCoefficients δ u p.2*probeCoefficients δ v p.1*K p.2 p.1 = _
  rw [hK p.2 p.1]
  ring

section KernelBound
variable (δ C : ℝ) (hC : 0 ≤ C) (K : ℕ → ℕ → ℝ)
variable (hbound : ∀ (S : Finset ℕ) (x : ℕ → ℝ), (∀ n ∈ S, 0 < n) →
  (∑ m ∈ S, ∑ n ∈ S, |x m*x n*K m n|) ≤ C*∑ n ∈ S, (n:ℝ)^δ*(x n)^2)

include hC hbound

/-- Finite arithmetic estimates give absolute convergence on the full Hilbert carrier. -/
theorem weightedKernelPairing_absolute (u v : WeightedProbe δ) :
    Summable (fun p : ℕ×ℕ =>
      |probeCoefficients δ u p.1*probeCoefficients δ v p.2*K p.1 p.2|) ∧
    (∑' p : ℕ×ℕ, |probeCoefficients δ u p.1*probeCoefficients δ v p.2*K p.1 p.2|) ≤
      2*C*(‖u‖^2+‖v‖^2) := by
  have h := kernel_infinite_mixed_of_finite_bound δ C hC K hbound
    (probeCoefficients δ u) (probeCoefficients δ v) rfl rfl
    (probeCoefficients_summable δ u) (probeCoefficients_summable δ v)
  simpa only [probeCoefficients_mass] using h

/-- Absolute convergence makes the arithmetic pairing bilinear. -/
def weightedKernelBilinear : WeightedProbe δ →ₗ[ℝ] WeightedProbe δ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (weightedKernelPairing δ K)
    (fun u v w => by
      unfold weightedKernelPairing
      simp_rw [probeCoefficients_add, add_mul]
      exact ((weightedKernelPairing_absolute δ C hC K hbound u w).1.of_abs).tsum_add
        ((weightedKernelPairing_absolute δ C hC K hbound v w).1.of_abs))
    (fun a u v => by
      unfold weightedKernelPairing
      simp_rw [probeCoefficients_smul]
      calc _ = ∑' p : ℕ×ℕ, a*(probeCoefficients δ u p.1*probeCoefficients δ v p.2*K p.1 p.2) :=
            tsum_congr fun p => by ring
           _ = _ := tsum_mul_left)
    (fun u v w => by
      unfold weightedKernelPairing
      simp_rw [probeCoefficients_add, mul_add, add_mul]
      exact ((weightedKernelPairing_absolute δ C hC K hbound u v).1.of_abs).tsum_add
        ((weightedKernelPairing_absolute δ C hC K hbound u w).1.of_abs))
    (fun a u v => by
      unfold weightedKernelPairing
      simp_rw [probeCoefficients_smul]
      calc _ = ∑' p : ℕ×ℕ, a*(probeCoefficients δ u p.1*probeCoefficients δ v p.2*K p.1 p.2) :=
            tsum_congr fun p => by ring
           _ = _ := tsum_mul_left)

/-- The bilinear map retains the defining arithmetic series. -/
@[simp] theorem weightedKernelBilinear_apply (u v : WeightedProbe δ) :
    weightedKernelBilinear δ C hC K hbound u v=weightedKernelPairing δ K u v := rfl

/-- Normalizing each probe converts the quadratic majorant into a bilinear norm bound. -/
theorem weightedKernelBilinear_bound (u v : WeightedProbe δ) :
    ‖weightedKernelBilinear δ C hC K hbound u v‖ ≤ 4*C*‖u‖*‖v‖ := by
  let B := weightedKernelBilinear δ C hC K hbound
  have hquad (u v : WeightedProbe δ) : ‖B u v‖ ≤ 2*C*(‖u‖^2+‖v‖^2) := by
    obtain ⟨hs, hb⟩ := weightedKernelPairing_absolute δ C hC K hbound u v
    have hn : ‖B u v‖ ≤ ∑' p : ℕ×ℕ,
        |probeCoefficients δ u p.1*probeCoefficients δ v p.2*K p.1 p.2| := by
      simpa only [B, weightedKernelBilinear_apply, weightedKernelPairing, Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := fun p : ℕ×ℕ =>
          probeCoefficients δ u p.1*probeCoefficients δ v p.2*K p.1 p.2) hs
    exact hn.trans hb
  change ‖B u v‖ ≤ _
  by_cases hu0 : u=0
  · subst u; simp
  by_cases hv0 : v=0
  · subst v; simp
  have hu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hunit (w : WeightedProbe δ) (hw : 0 < ‖w‖) : ‖‖w‖⁻¹ • w‖=1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hw), inv_mul_cancel₀ hw.ne']
  have h := hquad (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)
  rw [hunit u hu, hunit v hv] at h
  have hdiv : ‖B u v‖/(‖u‖*‖v‖) ≤ 4*C := by
    calc _ = ‖B (‖u‖⁻¹ • u) (‖v‖⁻¹ • v)‖ := by
          simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, norm_mul,
            Real.norm_eq_abs, abs_inv, abs_norm]
          field_simp [hu.ne', hv.ne']
         _ ≤ _ := by nlinarith only [h]
  calc _ ≤ (4*C)*(‖u‖*‖v‖) := (div_le_iff₀ (mul_pos hu hv)).mp hdiv
       _ = _ := by ring

/-- Continuous completion of a kernel with its proved finite arithmetic bound. -/
def weightedKernelContinuous : WeightedProbe δ →L[ℝ] WeightedProbe δ →L[ℝ] ℝ :=
  (weightedKernelBilinear δ C hC K hbound).mkContinuous₂ (4*C)
    (weightedKernelBilinear_bound δ C hC K hbound)

/-- Completion preserves the original absolutely convergent arithmetic series. -/
@[simp] theorem weightedKernelContinuous_apply (u v : WeightedProbe δ) :
    weightedKernelContinuous δ C hC K hbound u v=weightedKernelPairing δ K u v := rfl

/-- The completion retains the uniform arithmetic operator bound. -/
theorem weightedKernelContinuous_norm_le : ‖weightedKernelContinuous δ C hC K hbound‖ ≤ 4*C :=
  (weightedKernelBilinear δ C hC K hbound).mkContinuous₂_norm_le (by positivity)
    (weightedKernelBilinear_bound δ C hC K hbound)
end KernelBound

#print axioms weightedKernelPairing_comm
#print axioms weightedKernelBilinear_bound
#print axioms weightedKernelContinuous
#print axioms weightedKernelContinuous_norm_le
end GaloisForLFunctions.HeightHomotopyArithmeticCounts
