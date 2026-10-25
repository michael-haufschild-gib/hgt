import GaloisForLFunctions.ArithmeticDefectRigidity.OriginStepsHaveTheMaxKernel
import GaloisForLFunctions.ArithmeticOrientationTheory.TheMaxKernelWienerMapIsFaithful
import GaloisForLFunctions.ArithmeticOrientationTheory.CriticalKernelActionsExtendToTheWienerAlgebra

/-!
# The origin-step module has the full Bohr hull

The max kernel has exact critical dilation homogeneity. Its canonical
Wiener action is faithful, with zero annihilator and the full Bohr hull.
-/

section
noncomputable section
set_option autoImplicit false
open Finset Filter Topology
open scoped InnerProductSpace
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- The pronic energy of a finite feature packet equals its complete Gram quadratic form. -/
theorem pronicNorm_featurePacket_sq {X : Type*} (T : ℕ) (S : Finset X)
    (c : X → ℝ) (v : X → ℕ → ℝ) :
    pronicNorm T (fun n => ∑ j ∈ S, c j * v j n) ^ 2 =
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * pronicPairing T (v j) (v k) := by
  rw [pronicNorm_sq]
  simp only [pronicPairing, pow_two, sum_mul, mul_sum, sum_div]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  exact sum_congr rfl fun n _ => by ring

namespace OriginStepModule

/-- The exact max kernel of the reset-origin step orbit. -/
def kernel (j k : ℕ+) : ℝ := 1 / ((max (j : ℕ) (k : ℕ) : ℕ) : ℝ)

theorem kernel_symm (j k : ℕ+) : kernel j k = kernel k j := by
  simp only [kernel, max_comm]

theorem packet_nonneg (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel j k := by
  have hlim : Tendsto (fun T => ∑ j ∈ S, ∑ k ∈ S, c j * c k *
      pronicPairing T (rowDilate j originStep) (rowDilate k originStep)) atTop
      (𝓝 (∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel j k)) := by
    apply tendsto_finsetSum
    intro j _
    apply tendsto_finsetSum
    intro k _
    exact tendsto_const_nhds.mul (pronicPairing_originSteps_tendsto j k)
  apply ge_of_tendsto' hlim
  intro T
  rw [← pronicNorm_featurePacket_sq]
  exact sq_nonneg _

/-- Integer dilation scales the entire step Gram by its exact pronic mass ratio. -/
theorem kernel_dilation (p j k : ℕ+) :
    kernel (p * j) (p * k) = (1 / (p : ℝ)) * kernel j k := by
  have hmax : max ((p : ℕ) * j) ((p : ℕ) * k) = (p : ℕ) * max (j : ℕ) (k : ℕ) := by
    rcases le_total (j : ℕ) (k : ℕ) with h | h
    · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_left _ h)]
    · rw [max_eq_left h, max_eq_left (Nat.mul_le_mul_left _ h)]
  simp only [kernel, PNat.mul_coe, hmax, Nat.cast_mul]
  ring

theorem packet_dilation (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel (p * j) (p * k)) =
      (1 / (p : ℝ)) * (∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel j k) := by
  simp only [kernel_dilation, mul_sum]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by ring

def complexKernel (j k : ℕ+) : ℂ := kernel j k

instance : Fact (IsPSDKernel complexKernel) :=
  ⟨isPSDKernel_of_real_packet_nonneg kernel kernel_symm packet_nonneg⟩

abbrev Hilbert := KernelHilbert complexKernel

theorem complex_packet_dilation (p : ℕ+) (a : ℕ+ →₀ ℂ) :
    (kernelForm (fun j k => complexKernel (p * j) (p * k)) a a).re ≤
      (1 / Real.sqrt (p : ℝ)) ^ 2 * (kernelForm complexKernel a a).re := by
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]
  exact kernelForm_real_re_le (fun S c => (packet_dilation p S c).le) a

/-- The critical Wiener action on the complete step Gram space. -/
def representation : WienerAlgebraAt (1 / 2) →ₐ[ℂ] (Hilbert →L[ℂ] Hilbert) :=
  CriticalKernelAction.representation complexKernel complex_packet_dilation

/-- Every Wiener coefficient is visible in the step cyclic vector. -/
theorem cyclic_map_injective :
    Function.Injective (fun a => representation a (KernelHilbert.vector complexKernel 1)) := by
  apply wiener_cyclic_map_injective_of_max_gram representation
    (CriticalKernelAction.norm_representation_le complexKernel complex_packet_dilation)
    (KernelHilbert.vector complexKernel 1)
  intro j k
  change inner ℂ
    (CriticalKernelAction.representation complexKernel complex_packet_dilation
      (WienerAlgebraAt.pointMass k) (KernelHilbert.vector complexKernel 1))
    (CriticalKernelAction.representation complexKernel complex_packet_dilation
      (WienerAlgebraAt.pointMass j) (KernelHilbert.vector complexKernel 1)) = _
  rw [CriticalKernelAction.representation_pointMass_vector,
    CriticalKernelAction.representation_pointMass_vector, mul_one, mul_one,
    KernelHilbert.inner_vector]
  rfl

theorem representation_injective : Function.Injective representation := by
  intro a b hab
  exact cyclic_map_injective (congrArg (fun f => f (KernelHilbert.vector complexKernel 1)) hab)

def annihilator : Ideal (WienerAlgebraAt (1 / 2)) := RingHom.ker representation.toRingHom

theorem annihilator_eq_bot : annihilator = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro a ha
  change a = 0
  exact representation_injective (ha.trans (map_zero representation).symm)

def hull : Set BohrPoint :=
  {ω | ∀ a ∈ annihilator, ArithmeticOrientationTheory.bohrEval (1 / 2) a.toFn ω = 0}

/-- The step module has the full Bohr hull despite its exact critical dilation law. -/
theorem hull_eq_univ : hull = Set.univ := by
  apply Set.eq_univ_of_forall
  intro ω a ha
  rw [annihilator_eq_bot] at ha
  have hz : a = 0 := ha
  subst a
  rw [← ArithmeticOrientationTheory.WienerAlgebraAt.bohrCharacter_apply, map_zero]

end OriginStepModule
end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.OriginStepModule.cyclic_map_injective
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.OriginStepModule.hull_eq_univ
end
end
