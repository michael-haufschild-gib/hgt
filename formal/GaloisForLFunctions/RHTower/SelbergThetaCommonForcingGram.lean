import GaloisForLFunctions.RHTower.SelbergThetaCommonForcingGraph

/-!
# Native Gram identities for the common theta forcing

The literal centered theta responses have a common forcing in the original closed native
operator. Their full response Gram obeys a scalar displacement identity. Mixed vector/image
and image/image entries retain every source cross term. Both energies of every finite domain
packet are computed in the original native norm. Away from reflected energy collisions the
response Gram reduces to one-variable native source-pairing data; collisions retain the
cleared compatibility law. No source-pairing sign or vanishing normalized residual is asserted.
-/

open Complex
open scoped ComplexConjugate BigOperators InnerProductSpace
open GaloisForLFunctions.HTGeometry
set_option autoImplicit false

namespace RHTower.SelbergThetaCommonForcingGram
open D4BMGlobalAngularResponse D4BMModularCore SelbergThetaCommonForcing
noncomputable section

/-- The actual centered theta response, in the original native norm. -/
def vector (q : XiZeroCopy) : Space := (centeredDomain q : Space)

/-- Its complete native operator image. -/
def image (q : XiZeroCopy) : Space := energyOperator (centeredDomain q)

/-- The fixed centered theta forcing shared by every Xi copy. -/
def forcing : Space := -(1/4:ℂ) • SelbergNativeConstantMode.centered nativePositive

/-- One scalar native source pairing for each actual Xi copy. -/
def sourcePairing (q : XiZeroCopy) : ℂ := inner ℂ forcing (vector q)

/-- The full native response Gram kernel. -/
def gram (q r : XiZeroCopy) : ℂ := inner ℂ (vector q) (vector r)

theorem image_eq (q : XiZeroCopy) : image q = energy q • vector q + forcing := by
  have h := centeredDomain_equation q
  change image q - energy q • vector q = forcing at h
  have he : image q = forcing + energy q • vector q := sub_eq_iff_eq_add.mp h
  exact he.trans (add_comm _ _)

private theorem inner_vector_forcing (q : XiZeroCopy) :
    inner ℂ (vector q) forcing = conj (sourcePairing q) := by
  exact (inner_conj_symm (vector q) forcing).symm

/-- The mixed native Gram is determined by the vector Gram and the scalar source pairing. -/
theorem vector_image_inner (q r : XiZeroCopy) :
    inner ℂ (vector q) (image r) =
      energy r * gram q r + conj (sourcePairing q) := by
  rw [image_eq, inner_add_right, inner_smul_right, inner_vector_forcing]
  rfl

/-- The adjoint mixed native Gram, with every common-forcing term retained. -/
theorem image_vector_inner (q r : XiZeroCopy) :
    inner ℂ (image q) (vector r) =
      conj (energy q) * gram q r + sourcePairing r := by
  rw [image_eq, inner_add_left, inner_smul_left]
  rfl

/-- The actual two-parameter native Gram satisfies a scalar displacement identity.
The cleared form includes every reflected energy collision. -/
theorem gram_displacement (q r : XiZeroCopy) :
    (energy r - conj (energy q)) * gram q r =
      sourcePairing r - conj (sourcePairing q) := by
  have h := isFormalAdjoint_of_isSelfAdjoint energyOperator_selfAdjoint
    (centeredDomain q) (centeredDomain r)
  change inner ℂ (image q) (vector r) = inner ℂ (vector q) (image r) at h
  rw [image_vector_inner, vector_image_inner] at h
  linear_combination -h

/-- Away from reflected energy collisions, one-variable native source data determines
the entire complex response Gram entry. -/
theorem gram_eq_divided_difference (q r : XiZeroCopy)
    (h : energy r - conj (energy q) ≠ 0) :
    gram q r = (sourcePairing r - conj (sourcePairing q)) /
      (energy r - conj (energy q)) := by
  apply (eq_div_iff h).2
  simpa only [mul_comm] using gram_displacement q r

/-- At reflected collisions, the same source data obeys the exact compatibility law. -/
theorem sourcePairing_eq_conj_of_energy_eq (q r : XiZeroCopy)
    (h : energy r = conj (energy q)) : sourcePairing r = conj (sourcePairing q) := by
  have hg := gram_displacement q r
  rw [h, sub_self, zero_mul] at hg
  exact sub_eq_zero.mp hg.symm

/-- Diagonal source flux measures the imaginary native energy with the actual native mass. -/
theorem sourcePairing_im (q : XiZeroCopy) :
    (sourcePairing q).im = (energy q).im * ‖vector q‖ ^ (2 : ℕ) := by
  have h := congrArg Complex.im (gram_displacement q q)
  have hg : (gram q q).re = ‖vector q‖ ^ (2 : ℕ) := by
    simpa only [gram, RCLike.re_to_complex] using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (vector q))
  simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, sub_self, zero_mul, zero_add, hg] at h
  linarith

/-- Every native image/image Gram entry is fixed by the same scalar data. -/
theorem image_image_inner (q r : XiZeroCopy) :
    inner ℂ (image q) (image r) =
      conj (energy q) * energy r * gram q r +
      conj (energy q) * conj (sourcePairing q) +
      energy r * sourcePairing r + inner ℂ forcing forcing := by
  rw [image_eq q, image_eq r]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_vector_forcing]
  simp only [gram, sourcePairing]
  ring

/-- Full native residual at an arbitrary complex energy. -/
def residual (z : ℂ) (q : XiZeroCopy) : Space := image q - z • vector q

theorem residual_eq (z : ℂ) (q : XiZeroCopy) :
    residual z q = (energy q-z) • vector q + forcing := by
  rw [residual, image_eq, sub_smul]
  abel

/-- Explicit complete residual kernel, including the source cross terms. -/
def residualKernel (z : ℂ) (q r : XiZeroCopy) : ℂ :=
  conj (energy q-z) * (energy r-z) * gram q r +
  conj (energy q-z) * conj (sourcePairing q) +
  (energy r-z) * sourcePairing r + inner ℂ forcing forcing

theorem residual_inner (z : ℂ) (q r : XiZeroCopy) :
    inner ℂ (residual z q) (residual z r) = residualKernel z q r := by
  rw [residual_eq z q, residual_eq z r]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    inner_vector_forcing]
  simp only [residualKernel, gram, sourcePairing]
  ring

/-- Exact residual energy of every finite packet of actual centered theta responses. -/
theorem packet_residual_norm_sq {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ) (z : ℂ) :
    ‖∑ i, c i • residual z (q i)‖ ^ (2 : ℕ) =
      (∑ i, ∑ j, conj (c i) * c j * residualKernel z (q i) (q j)).re := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (∑ i, c i • residual z (q i))
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    residual_inner] at h
  rw [← h]
  change (∑ j, c j * ∑ i, conj (c i) * residualKernel z (q i) (q j)).re = _
  apply congrArg Complex.re
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The matching denominator energy uses the complete native vector Gram. -/
theorem packet_norm_sq {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ) :
    ‖∑ i, c i • vector (q i)‖ ^ (2 : ℕ) =
      (∑ i, ∑ j, conj (c i) * c j * gram (q i) (q j)).re := by
  have h := inner_self_eq_norm_sq (𝕜 := ℂ) (∑ i, c i • vector (q i))
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right] at h
  rw [← h]
  change (∑ j, c j * ∑ i, conj (c i) * gram (q i) (q j)).re = _
  apply congrArg Complex.re
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Every finite packet belongs to the original native operator domain. -/
def packetDomain {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ) : energyOperator.domain :=
  ∑ i, c i • centeredDomain (q i)

theorem packetDomain_coe {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ) :
    (packetDomain q c : Space) = ∑ i, c i • vector (q i) := by
  change energyOperator.domain.subtype (∑ i, c i • centeredDomain (q i)) = _
  rw [map_sum]
  rfl

/-- The packet kernel measures the full residual of the actual native domain packet. -/
theorem packetDomain_residual {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ) (z : ℂ) :
    energyOperator (packetDomain q c)-z • (packetDomain q c : Space) =
      ∑ i, c i • residual z (q i) := by
  change shiftedMap energyOperator z (∑ i, c i • centeredDomain (q i)) = _
  rw [map_sum]
  simp only [map_smul, shiftedMap_apply, residual, image, vector]

theorem packetDomain_residual_norm_sq {ι : Type*} [Fintype ι]
    (q : ι → XiZeroCopy) (c : ι → ℂ) (z : ℂ) :
    ‖energyOperator (packetDomain q c)-z • (packetDomain q c : Space)‖ ^ (2 : ℕ) =
      (∑ i, ∑ j, conj (c i) * c j * residualKernel z (q i) (q j)).re := by
  rw [packetDomain_residual]
  exact packet_residual_norm_sq q c z

end
end RHTower.SelbergThetaCommonForcingGram
