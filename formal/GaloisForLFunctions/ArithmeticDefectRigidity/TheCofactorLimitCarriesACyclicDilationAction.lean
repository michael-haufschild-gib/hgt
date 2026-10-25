import GaloisForLFunctions.ArithmeticDefectRigidity.RepairingKernelsVanishOnEscape
import GaloisForLFunctions.HTGeometry.BoundedKernelReindexing
import GaloisForLFunctions.HTGeometry.RealPositiveKernelComplexification

/-!
# Every actual cofactor limit carries a cyclic dilation action

A cofinal common limit is specified only by source covariance convergence.
Positivity and the sharp packet contraction follow from the finite Gram tables.
They give a complex Hilbert realization with a cyclic multiplicative dilation
action. The chosen compactness limit is a specialization.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A cofinal common Gram limit of the actual receiver. Only source convergence
is stored; positivity and contraction are consequences. -/
structure ActualCofactorLimit (ε : SubcriticalDamping) where
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  kernel : ℕ+ → ℕ+ → ℝ
  converges : ∀ j k,
    Tendsto (fun m => cofactorGram ε (subsequence m) j k) atTop (𝓝 (kernel j k))

namespace ActualCofactorLimit

/-- Compactness supplies an actual common limit at every subcritical damping. -/
def chosen (ε : SubcriticalDamping) : ActualCofactorLimit ε where
  subsequence := (exists_cofactorGram_limit ε).choose
  strictMono := (exists_cofactorGram_limit ε).choose_spec.1
  kernel := (exists_cofactorGram_limit ε).choose_spec.2.choose
  converges := (exists_cofactorGram_limit ε).choose_spec.2.choose_spec.1

variable {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)

/-- Every finite packet converges, including packets whose indices are reindexed. -/
theorem packet_tendsto (S : Finset ℕ+) (c : ℕ+ → ℝ) (a : ℕ+ → ℕ+) :
    Tendsto (fun m => ∑ j ∈ S, ∑ k ∈ S,
      c j * c k * cofactorGram ε (L.subsequence m) (a j) (a k)) atTop
      (𝓝 (∑ j ∈ S, ∑ k ∈ S, c j * c k * L.kernel (a j) (a k))) := by
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro k _
  exact tendsto_const_nhds.mul (L.converges (a j) (a k))

theorem kernel_one_one : L.kernel 1 1 = 1 := by
  have h := L.converges 1 1
  simp only [cofactorGram_one_one] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

theorem kernel_symm (j k : ℕ+) : L.kernel j k = L.kernel k j := by
  exact tendsto_nhds_unique (L.converges j k)
    ((L.converges k j).congr fun m => cofactorGram_symm ε (L.subsequence m) k j)

theorem abs_kernel_le (j k : ℕ+) : |L.kernel j k| ≤ cofactorGramRadius j k :=
  le_of_tendsto (L.converges j k).abs
    (Eventually.of_forall fun m => abs_cofactorGram_le ε (L.subsequence m) j k)

theorem packet_nonneg (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * L.kernel j k :=
  ge_of_tendsto (L.packet_tendsto S c id)
    (Eventually.of_forall fun m => cofactorGram_quadratic_nonneg ε (L.subsequence m) S c)

/-- The sharp packet contraction holds for every actual common Gram limit. -/
theorem packet_dilation_le (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    (∑ j ∈ S, ∑ k ∈ S, c j * c k * L.kernel (p * j) (p * k)) ≤
      (1 / (p : ℝ)) * (∑ j ∈ S, ∑ k ∈ S, c j * c k * L.kernel j k) :=
  le_of_tendsto_of_tendsto' (L.packet_tendsto S c fun j => p * j)
    (tendsto_const_nhds.mul (L.packet_tendsto S c id)) fun m =>
      cofactorGram_packet_dilation_le ε (L.subsequence m) p S c

end ActualCofactorLimit
end GaloisForLFunctions.ArithmeticDefectRigidity


open Finset Filter Topology RHTower
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- Complexification of the real covariance kernel. -/
def complexKernel {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (j k : ℕ+) : ℂ := kernel L j k

instance {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) : Fact (IsPSDKernel (complexKernel L)) :=
  ⟨isPSDKernel_of_real_packet_nonneg (kernel L) L.kernel_symm
    L.packet_nonneg⟩

/-- The Hilbert realization of the actual common cofactor limit. -/
abbrev Hilbert {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) := KernelHilbert (complexKernel L)

/-- The limiting Gram vector of one fixed cofactor row. -/
def vector {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (j : ℕ+) : Hilbert L :=
  KernelHilbert.vector (complexKernel L) j

theorem inner_vector {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (j k : ℕ+) :
    ⟪vector L k, vector L j⟫_ℂ = (kernel L j k : ℂ) :=
  KernelHilbert.inner_vector j k

theorem norm_vector_sq {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (j : ℕ+) :
    ‖vector L j‖ ^ 2 = kernel L j j := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_vector]
  rfl

/-- Unit receiver mass makes the cyclic vector nonzero. -/
theorem vector_one_ne_zero {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) : vector L 1 ≠ 0 := by
  intro h
  have hn := norm_vector_sq L 1
  rw [h, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
    L.kernel_one_one] at hn
  exact zero_ne_one hn

theorem complex_packet_dilation_le {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (p : ℕ+) (c : ℕ+ →₀ ℂ) :
    (kernelForm (fun j k => complexKernel L (p * j) (p * k)) c c).re ≤
      (1 / Real.sqrt (p : ℝ)) ^ 2 * (kernelForm (complexKernel L) c c).re := by
  have hp : (0 : ℝ) ≤ p := by positivity
  rw [div_pow, one_pow, Real.sq_sqrt hp]
  exact kernelForm_real_re_le (L.packet_dilation_le p) c

/-- Integer dilation on the actual Gram Hilbert space. -/
def dilation {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (p : ℕ+) : Hilbert L →L[ℂ] Hilbert L :=
  KernelHilbert.pushforward (complexKernel L) (fun j => p * j)
    (by positivity : 0 ≤ 1 / Real.sqrt (p : ℝ)) (complex_packet_dilation_le L p)

theorem dilation_vector {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (p j : ℕ+) :
    dilation L p (vector L j) = vector L (p * j) :=
  KernelHilbert.pushforward_vector _ _ _ _ j

/-- The sharp pronic contraction passes to the completed dilation operators. -/
theorem norm_dilation_le {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (p : ℕ+) :
    ‖dilation L p‖ ≤ 1 / Real.sqrt (p : ℝ) :=
  KernelHilbert.norm_pushforward_le _ _ _ _

theorem dilation_one {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) : dilation L 1 = 1 := by
  apply KernelHilbert.ext_on_vectors (complexKernel L)
  intro j
  change dilation L 1 (vector L j) = (1 : Hilbert L →L[ℂ] Hilbert L) (vector L j)
  rw [dilation_vector, one_mul]
  rfl

/-- Integer multiplication is represented exactly, including after completion. -/
theorem dilation_mul {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (p q : ℕ+) :
    dilation L p * dilation L q = dilation L (p * q) := by
  apply KernelHilbert.ext_on_vectors (complexKernel L)
  intro j
  change dilation L p (dilation L q (vector L j)) = dilation L (p * q) (vector L j)
  rw [dilation_vector, dilation_vector, dilation_vector, mul_assoc]

/-- Dilating the receiver vector gives a total family. -/
theorem receiver_cyclic {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    Dense ((Submodule.span ℂ (Set.range (fun p => dilation L p (vector L 1))) :
      Submodule ℂ (Hilbert L)) : Set (Hilbert L)) := by
  simp only [dilation_vector, mul_one]
  exact KernelHilbert.dense_span_vectors (complexKernel L)

/-- Real packet norms are precisely the limiting real covariance energies. -/
theorem norm_real_packet_sq {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    ‖∑ j ∈ S, (c j : ℂ) • vector L j‖ ^ 2 =
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel L j k := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
  change (⟪∑ j ∈ S, (c j : ℂ) • vector L j,
    ∑ j ∈ S, (c j : ℂ) • vector L j⟫_ℂ).re = _
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, inner_vector,
    Complex.conj_ofReal, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero]
  exact sum_congr rfl fun j _ => sum_congr rfl fun k _ => by
    rw [L.kernel_symm k j]
    ring

/-- Every finite repairing packet vanishes in the actual escape Hilbert space. -/
theorem admits_or_finite_repairs_vanish {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨
      ∀ (S : Finset ℕ+) (c : ℕ+ → ℝ),
        TransHorizonIncidenceMechanics.ReceiverBounded
          (dirichletConv (finiteCofactorKernel S c) (pmPowerDampedRealWeight ε)) →
        (∑ j ∈ S, (c j : ℂ) • vector L j) = 0 := by
  rcases admits_or_all_gram_limits_annihilate_repairs ε with h | h
  · exact Or.inl h
  · refine Or.inr fun S c hpaid => ?_
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    rw [norm_real_packet_sq]
    exact h (subsequence L) (kernel L) L.strictMono
      L.converges S c hpaid


end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

namespace GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit

abbrev subsequence (ε : SubcriticalDamping) : ℕ → ℕ :=
  ActualCofactorLimit.subsequence (ActualCofactorLimit.chosen ε)

theorem subsequence_strictMono (ε : SubcriticalDamping) : StrictMono (subsequence ε) :=
  ActualCofactorLimit.strictMono (ActualCofactorLimit.chosen ε)

abbrev kernel (ε : SubcriticalDamping) : ℕ+ → ℕ+ → ℝ :=
  ActualCofactorLimit.kernel (ActualCofactorLimit.chosen ε)

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

abbrev complexKernel (ε : SubcriticalDamping) (j k : ℕ+) : ℂ :=
  ActualCofactorLimit.complexKernel (ActualCofactorLimit.chosen ε) j k

abbrev Hilbert (ε : SubcriticalDamping) :=
  ActualCofactorLimit.Hilbert (ActualCofactorLimit.chosen ε)

abbrev vector (ε : SubcriticalDamping) (j : ℕ+) : Hilbert ε :=
  ActualCofactorLimit.vector (ActualCofactorLimit.chosen ε) j

theorem inner_vector (ε : SubcriticalDamping) (j k : ℕ+) :
    ⟪vector ε k, vector ε j⟫_ℂ = (kernel ε j k : ℂ) :=
  ActualCofactorLimit.inner_vector (ActualCofactorLimit.chosen ε) j k

theorem norm_vector_sq (ε : SubcriticalDamping) (j : ℕ+) :
    ‖vector ε j‖ ^ 2 = kernel ε j j :=
  ActualCofactorLimit.norm_vector_sq (ActualCofactorLimit.chosen ε) j

theorem vector_one_ne_zero (ε : SubcriticalDamping) : vector ε 1 ≠ 0 :=
  ActualCofactorLimit.vector_one_ne_zero (ActualCofactorLimit.chosen ε)

theorem complex_packet_dilation_le (ε : SubcriticalDamping) (p : ℕ+) (c : ℕ+ →₀ ℂ) :
    (kernelForm (fun j k => complexKernel ε (p * j) (p * k)) c c).re ≤
      (1 / Real.sqrt (p : ℝ)) ^ 2 * (kernelForm (complexKernel ε) c c).re :=
  ActualCofactorLimit.complex_packet_dilation_le (ActualCofactorLimit.chosen ε) p c

abbrev dilation (ε : SubcriticalDamping) (p : ℕ+) : Hilbert ε →L[ℂ] Hilbert ε :=
  ActualCofactorLimit.dilation (ActualCofactorLimit.chosen ε) p

theorem dilation_vector (ε : SubcriticalDamping) (p j : ℕ+) :
    dilation ε p (vector ε j) = vector ε (p * j) :=
  ActualCofactorLimit.dilation_vector (ActualCofactorLimit.chosen ε) p j

theorem norm_dilation_le (ε : SubcriticalDamping) (p : ℕ+) :
    ‖dilation ε p‖ ≤ 1 / Real.sqrt (p : ℝ) :=
  ActualCofactorLimit.norm_dilation_le (ActualCofactorLimit.chosen ε) p

theorem dilation_one (ε : SubcriticalDamping) : dilation ε 1 = 1 :=
  ActualCofactorLimit.dilation_one (ActualCofactorLimit.chosen ε)

theorem dilation_mul (ε : SubcriticalDamping) (p q : ℕ+) :
    dilation ε p * dilation ε q = dilation ε (p * q) :=
  ActualCofactorLimit.dilation_mul (ActualCofactorLimit.chosen ε) p q

theorem receiver_cyclic (ε : SubcriticalDamping) :
    Dense ((Submodule.span ℂ (Set.range (fun p => dilation ε p (vector ε 1))) :
      Submodule ℂ (Hilbert ε)) : Set (Hilbert ε)) :=
  ActualCofactorLimit.receiver_cyclic (ActualCofactorLimit.chosen ε)

theorem norm_real_packet_sq (ε : SubcriticalDamping) (S : Finset ℕ+) (c : ℕ+ → ℝ) :
    ‖∑ j ∈ S, (c j : ℂ) • vector ε j‖ ^ 2 =
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * kernel ε j k :=
  ActualCofactorLimit.norm_real_packet_sq (ActualCofactorLimit.chosen ε) S c

theorem admits_or_finite_repairs_vanish (ε : SubcriticalDamping) :
    Admits dampedMobiusEnergy ε ∨
      ∀ (S : Finset ℕ+) (c : ℕ+ → ℝ),
        TransHorizonIncidenceMechanics.ReceiverBounded
          (dirichletConv (finiteCofactorKernel S c) (pmPowerDampedRealWeight ε)) →
        (∑ j ∈ S, (c j : ℂ) • vector ε j) = 0 :=
  ActualCofactorLimit.admits_or_finite_repairs_vanish (ActualCofactorLimit.chosen ε)

end GaloisForLFunctions.ArithmeticDefectRigidity.CofactorLimit
