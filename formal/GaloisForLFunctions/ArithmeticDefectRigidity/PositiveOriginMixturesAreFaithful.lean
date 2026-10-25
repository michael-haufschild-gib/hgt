import GaloisForLFunctions.ArithmeticDefectRigidity.TheOriginStepModuleHasTheFullBohrHull
import GaloisForLFunctions.ArithmeticDefectRigidity.TheCofactorLimitCarriesACyclicDilationAction
import GaloisForLFunctions.HTGeometry.DominatedKernelsHaveContractiveComparisons

/-!
# Positive origin mixtures are faithful

Every positive max-kernel mixture of an actual cofactor Gram has a bounded
comparison onto the origin-step cyclic module. This forces its entire Wiener
action to be faithful, without assuming an orthogonal direct-sum splitting.
-/

section
noncomputable section
set_option autoImplicit false
open Finset Filter Topology
open scoped InnerProductSpace NNReal
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticDefectRigidity.MixedOriginModule

/-- The normalized actual Gram with a prescribed nonnegative origin-step mass. -/
def kernel {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0)
    (j k : ℕ+) : ℝ :=
  (L.kernel j k + (c : ℝ) * OriginStepModule.kernel j k) / (1 + (c : ℝ))

theorem kernel_symm {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0)
    (j k : ℕ+) : kernel L c j k = kernel L c k j := by
  rw [kernel, kernel, L.kernel_symm, OriginStepModule.kernel_symm]

theorem packet_reindex_eq {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0)
    (i : ℕ+ → ℕ+) (S : Finset ℕ+) (a : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, a j * a k * kernel L c (i j) (i k)) =
      ((∑ j ∈ S, ∑ k ∈ S, a j * a k * L.kernel (i j) (i k)) +
        (c : ℝ) * ∑ j ∈ S, ∑ k ∈ S, a j * a k * OriginStepModule.kernel (i j) (i k)) /
          (1 + (c : ℝ)) := by
  simp only [kernel, add_div, mul_sum, sum_div, ← sum_add_distrib]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

theorem packet_eq {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0)
    (S : Finset ℕ+) (a : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, a j * a k * kernel L c j k) =
      ((∑ j ∈ S, ∑ k ∈ S, a j * a k * L.kernel j k) +
        (c : ℝ) * ∑ j ∈ S, ∑ k ∈ S, a j * a k * OriginStepModule.kernel j k) /
          (1 + (c : ℝ)) := by
  simpa only [id_eq] using packet_reindex_eq L c id S a

theorem packet_nonneg {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0)
    (S : Finset ℕ+) (a : ℕ+ → ℝ) :
    0 ≤ ∑ j ∈ S, ∑ k ∈ S, a j * a k * kernel L c j k := by
  rw [packet_eq L c]
  exact div_nonneg (add_nonneg (L.packet_nonneg S a)
    (mul_nonneg c.property (OriginStepModule.packet_nonneg S a))) (by positivity)

theorem packet_dilation_le {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0)
    (p : ℕ+) (S : Finset ℕ+) (a : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, a j * a k * kernel L c (p * j) (p * k)) ≤
      (1 / (p : ℝ)) * (∑ j ∈ S, ∑ k ∈ S, a j * a k * kernel L c j k) := by
  rw [packet_reindex_eq L c (fun j => p * j), packet_eq L c]
  have h := add_le_add (L.packet_dilation_le p S a)
    (mul_le_mul_of_nonneg_left (OriginStepModule.packet_dilation p S a).le c.property)
  have halgebra (x y α d b : ℝ) : (α * x + b * (α * y)) / d = α * ((x + b * y) / d) := by
    ring
  exact (div_le_div_of_nonneg_right h (by positivity : 0 ≤ 1 + (c : ℝ))).trans_eq
    (halgebra _ _ _ _ _)

def complexKernel {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0)
    (j k : ℕ+) : ℂ := kernel L c j k

instance {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0) :
    Fact (IsPSDKernel (complexKernel L c)) :=
  ⟨isPSDKernel_of_real_packet_nonneg (kernel L c) (kernel_symm L c) (packet_nonneg L c)⟩

abbrev Hilbert {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0) :=
  KernelHilbert (complexKernel L c)

theorem complex_packet_dilation {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0)
    (p : ℕ+) (a : ℕ+ →₀ ℂ) :
    (kernelForm (fun j k => complexKernel L c (p * j) (p * k)) a a).re ≤
      (1 / Real.sqrt (p : ℝ)) ^ 2 * (kernelForm (complexKernel L c) a a).re := by
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  exact kernelForm_real_re_le (packet_dilation_le L c p) a

def representation {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0) :
    WienerAlgebraAt (1 / 2) →ₐ[ℂ] (Hilbert L c →L[ℂ] Hilbert L c) :=
  CriticalKernelAction.representation (complexKernel L c) (complex_packet_dilation L c)

/-- A positive step component controls its whole Gram form from below. -/
theorem step_packet_le {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) (S : Finset ℕ+) (a : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, a j * a k * OriginStepModule.kernel j k) ≤
      ((1 + (c : ℝ)) / c) * (∑ j ∈ S, ∑ k ∈ S, a j * a k * kernel L c j k) := by
  rw [packet_eq L c]
  have hnonneg := div_nonneg (L.packet_nonneg S a) hc.le
  have hd : (1 : ℝ) + c ≠ 0 := by positivity
  calc
    _ ≤ (∑ j ∈ S, ∑ k ∈ S, a j * a k * L.kernel j k) / (c : ℝ) +
        (∑ j ∈ S, ∑ k ∈ S, a j * a k * OriginStepModule.kernel j k) :=
      le_add_of_nonneg_left hnonneg
    _ = _ := by field_simp [hc.ne', hd]

theorem step_comparison_bound {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) (a : ℕ+ →₀ ℂ) :
    (kernelForm OriginStepModule.complexKernel a a).re ≤
      Real.sqrt ((1 + (c : ℝ)) / c) ^ 2 * (kernelForm (complexKernel L c) a a).re := by
  rw [Real.sq_sqrt (by positivity)]
  exact kernelForm_real_re_le (step_packet_le L c hc) a

/-- Projection to the step component is defined on the mixed cyclic completion itself. -/
def stepComparison {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) : Hilbert L c →L[ℂ] OriginStepModule.Hilbert :=
  KernelHilbert.comparison (complexKernel L c) OriginStepModule.complexKernel id
    (Real.sqrt_nonneg _) (step_comparison_bound L c hc)

theorem stepComparison_vector {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) (j : ℕ+) :
    stepComparison L c hc (KernelHilbert.vector (complexKernel L c) j) =
      KernelHilbert.vector OriginStepModule.complexKernel j :=
  KernelHilbert.comparison_vector (complexKernel L c) OriginStepModule.complexKernel id
    (Real.sqrt_nonneg _) (step_comparison_bound L c hc) j

/-- Every positive origin-step mass makes the mixed cyclic Wiener module faithful. -/
theorem cyclic_map_injective {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    Function.Injective (fun a => representation L c a (KernelHilbert.vector (complexKernel L c) 1)) := by
  have hinter (a : WienerAlgebraAt (1 / 2)) :
      stepComparison L c hc (representation L c a (KernelHilbert.vector (complexKernel L c) 1)) =
        OriginStepModule.representation a (KernelHilbert.vector OriginStepModule.complexKernel 1) :=
    CriticalKernelAction.intertwines_cyclic_vector (complexKernel L c) (complex_packet_dilation L c)
      OriginStepModule.complexKernel OriginStepModule.complex_packet_dilation
      (stepComparison L c hc) (stepComparison_vector L c hc) a
  intro a b hab
  change representation L c a (KernelHilbert.vector (complexKernel L c) 1) =
    representation L c b (KernelHilbert.vector (complexKernel L c) 1) at hab
  apply OriginStepModule.cyclic_map_injective
  change OriginStepModule.representation a (KernelHilbert.vector OriginStepModule.complexKernel 1) =
    OriginStepModule.representation b (KernelHilbert.vector OriginStepModule.complexKernel 1)
  rw [← hinter a, ← hinter b, hab]

theorem representation_injective {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) : Function.Injective (representation L c) := by
  intro a b hab
  exact cyclic_map_injective L c hc
    (congrArg (fun f => f (KernelHilbert.vector (complexKernel L c) 1)) hab)

def annihilator {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0) :
    Ideal (WienerAlgebraAt (1 / 2)) := RingHom.ker (representation L c).toRingHom

theorem annihilator_eq_bot {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) : annihilator L c = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro a ha
  change a = 0
  exact representation_injective L c hc (ha.trans (map_zero (representation L c)).symm)

def hull {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0) : Set BohrPoint :=
  {ω | ∀ a ∈ annihilator L c, ArithmeticOrientationTheory.bohrEval (1 / 2) a.toFn ω = 0}

/-- Every positive reset-origin boundary has the full Bohr hull. -/
theorem hull_eq_univ {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) : hull L c = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω a ha
  rw [annihilator_eq_bot L c hc] at ha
  have hz : a = 0 := ha
  subst a
  rw [← ArithmeticOrientationTheory.WienerAlgebraAt.bohrCharacter_apply, map_zero]

end GaloisForLFunctions.ArithmeticDefectRigidity.MixedOriginModule

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.MixedOriginModule.cyclic_map_injective
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.MixedOriginModule.hull_eq_univ
end
end
