import GaloisForLFunctions.ArithmeticDefectRigidity.RepairingKernelsVanishOnEscape
import GaloisForLFunctions.HTGeometry.BoundedKernelReindexing
import GaloisForLFunctions.HTGeometry.RealPositiveKernelComplexification

/-!
# The actual cofactor limit carries a cyclic dilation action

Choose one common subsequential limit of the actual receiver's Gram tables.
Its real packet inequalities give a complex Gram Hilbert space and bounded
integer dilations. These multiply exactly, and the receiver vector is cyclic.
On escape, every finite repairing packet is zero in this Hilbert space.
-/

noncomputable section
set_option autoImplicit false

open Finset Filter Topology RHTower
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit

/-- One cofinal horizon sequence realizing all cofactor covariances simultaneously. -/
def subsequence (ε : SubcriticalDamping) : ℕ → ℕ :=
  (exists_cofactorGram_limit ε).choose

theorem subsequence_strictMono (ε : SubcriticalDamping) : StrictMono (subsequence ε) :=
  (exists_cofactorGram_limit ε).choose_spec.1

/-- The corresponding actual cofactor covariance kernel. -/
def kernel (ε : SubcriticalDamping) : ℕ+ → ℕ+ → ℝ :=
  (exists_cofactorGram_limit ε).choose_spec.2.choose

theorem kernel_properties (ε : SubcriticalDamping) :
    (∀ j k, Tendsto (fun m => cofactorGram ε (subsequence ε m) j k) atTop
      (𝓝 (kernel ε j k))) ∧
    kernel ε 1 1 = 1 ∧
    (∀ j k, kernel ε j k = kernel ε k j) ∧
    (∀ j k, |kernel ε j k| ≤ cofactorGramRadius j k) ∧
    (∀ (S : Finset ℕ+) (c : ℕ+ → ℝ),
      0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel ε j k) ∧
    ∀ (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ),
      (∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel ε (p * j) (p * k)) ≤
        (1 / (p : ℝ)) * (∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel ε j k) :=
  (exists_cofactorGram_limit ε).choose_spec.2.choose_spec

/-- Complexification of the real covariance kernel. -/
def complexKernel (ε : SubcriticalDamping) (j k : ℕ+) : ℂ := kernel ε j k

instance (ε : SubcriticalDamping) : Fact (IsPSDKernel (complexKernel ε)) :=
  ⟨isPSDKernel_of_real_packet_nonneg (kernel ε) (kernel_properties ε).2.2.1
    (kernel_properties ε).2.2.2.2.1⟩

/-- The Hilbert realization of the actual common cofactor limit. -/
abbrev Hilbert (ε : SubcriticalDamping) := KernelHilbert (complexKernel ε)

/-- The limiting Gram vector of one fixed cofactor row. -/
def vector (ε : SubcriticalDamping) (j : ℕ+) : Hilbert ε :=
  KernelHilbert.vector (complexKernel ε) j

theorem inner_vector (ε : SubcriticalDamping) (j k : ℕ+) :
    ⟪vector ε k, vector ε j⟫_ℂ = (kernel ε j k : ℂ) :=
  KernelHilbert.inner_vector j k

theorem norm_vector_sq (ε : SubcriticalDamping) (j : ℕ+) :
    ‖vector ε j‖ ^ 2 = kernel ε j j := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_vector]
  rfl

/-- Unit receiver mass makes the cyclic vector nonzero. -/
theorem vector_one_ne_zero (ε : SubcriticalDamping) : vector ε 1 ≠ 0 := by
  intro h
  have hn := norm_vector_sq ε 1
  rw [h, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    (kernel_properties ε).2.1] at hn
  exact zero_ne_one hn

theorem complex_packet_dilation_le (ε : SubcriticalDamping) (p : ℕ+) (c : ℕ+ →₀ ℂ) :
    (kernelForm (fun j k => complexKernel ε (p * j) (p * k)) c c).re ≤
      (1 / Real.sqrt (p : ℝ)) ^ 2 * (kernelForm (complexKernel ε) c c).re := by
  have hp : (0 : ℝ) ≤ p := by positivity
  rw [div_pow, one_pow, Real.sq_sqrt hp]
  exact kernelForm_real_re_le ((kernel_properties ε).2.2.2.2.2 p) c

/-- Integer dilation on the actual Gram Hilbert space. -/
def dilation (ε : SubcriticalDamping) (p : ℕ+) : Hilbert ε →L[ℂ] Hilbert ε :=
  KernelHilbert.pushforward (complexKernel ε) (fun j => p * j)
    (by positivity : 0 ≤ 1 / Real.sqrt (p : ℝ)) (complex_packet_dilation_le ε p)

theorem dilation_vector (ε : SubcriticalDamping) (p j : ℕ+) :
    dilation ε p (vector ε j) = vector ε (p * j) :=
  KernelHilbert.pushforward_vector _ _ _ _ j

/-- The sharp pronic contraction passes to the completed dilation operators. -/
theorem norm_dilation_le (ε : SubcriticalDamping) (p : ℕ+) :
    ‖dilation ε p‖ ≤ 1 / Real.sqrt (p : ℝ) :=
  KernelHilbert.norm_pushforward_le _ _ _ _

theorem dilation_one (ε : SubcriticalDamping) : dilation ε 1 = 1 := by
  apply KernelHilbert.ext_on_vectors (complexKernel ε)
  intro j
  change dilation ε 1 (vector ε j) = (1 : Hilbert ε →L[ℂ] Hilbert ε) (vector ε j)
  rw [dilation_vector, one_mul, ContinuousLinearMap.one_apply]

/-- Integer multiplication is represented exactly, including after completion. -/
theorem dilation_mul (ε : SubcriticalDamping) (p q : ℕ+) :
    dilation ε p * dilation ε q = dilation ε (p * q) := by
  apply KernelHilbert.ext_on_vectors (complexKernel ε)
  intro j
  change dilation ε p (dilation ε q (vector ε j)) = dilation ε (p * q) (vector ε j)
  rw [dilation_vector, dilation_vector, dilation_vector, mul_assoc]

/-- Dilating the receiver vector gives a total family. -/
theorem receiver_cyclic (ε : SubcriticalDamping) :
    Dense ((Submodule.span ℂ (Set.range (fun p => dilation ε p (vector ε 1))) :
      Submodule ℂ (Hilbert ε)) : Set (Hilbert ε)) := by
  simpa only [dilation_vector, mul_one] using
    KernelHilbert.dense_span_vectors (complexKernel ε)

/-- Real packet norms are precisely the limiting real covariance energies. -/
theorem norm_real_packet_sq (ε : SubcriticalDamping) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    ‖∑ j ∈ S, (c j : ℂ) • vector ε j‖ ^ 2 =
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel ε j k := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, inner_vector,
    Complex.conj_ofReal, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by
    rw [(kernel_properties ε).2.2.1 k j]
    ring

/-- Every finite repairing packet vanishes in the actual escape Hilbert space. -/
theorem admits_or_finite_repairs_vanish (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      ∀ (S : Finset ℕ+) (c : ℕ+ → ℝ),
        TransHorizonIncidenceMechanics.ReceiverBounded
          (dirichletConv (finiteCofactorKernel S c) (pmPowerDampedRealWeight ε)) →
        (∑ j ∈ S, (c j : ℂ) • vector ε j) = 0 := by
  rcases admits_or_all_gram_limits_annihilate_repairs ε with h | h
  · exact Or.inl h
  · refine Or.inr fun S c hpaid => ?_
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    rw [norm_real_packet_sq]
    exact h (subsequence ε) (kernel ε) (subsequence_strictMono ε)
      (kernel_properties ε).1 S c hpaid

end GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit
