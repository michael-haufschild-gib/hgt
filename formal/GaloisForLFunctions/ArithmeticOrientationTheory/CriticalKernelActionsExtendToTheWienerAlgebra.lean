import GaloisForLFunctions.ArithmeticOrientationTheory.BoundedMultiplicativeSequencesActOnWienerAlgebras
import GaloisForLFunctions.HTGeometry.BoundedKernelReindexing

/-!
# Critical kernel actions extend to the Wiener algebra

Critical packet contraction extends integer reindexing to bounded dilation
operators and then to a contractive Wiener action. Bounded feature maps
intertwining dilations also intertwine the complete cyclic Wiener action.
-/

section

noncomputable section
set_option autoImplicit false
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticOrientationTheory.CriticalKernelAction
open WienerAlgebraAt

variable (K : ℕ+ → ℕ+ → ℂ) [Fact (IsPSDKernel K)]
  (hK : ∀ (p : ℕ+) (a : ℕ+ →₀ ℂ),
    (kernelForm (fun j k => K (p * j) (p * k)) a a).re ≤
      (1 / Real.sqrt (p : ℝ)) ^ 2 * (kernelForm K a a).re)

/-- Integer dilation on any critical-contracting Gram kernel. -/
def dilation (p : ℕ+) : KernelHilbert K →L[ℂ] KernelHilbert K :=
  KernelHilbert.pushforward K (fun j => p * j) (by positivity) (hK p)

theorem dilation_vector (p j : ℕ+) :
    dilation K hK p (KernelHilbert.vector K j) = KernelHilbert.vector K (p * j) :=
  KernelHilbert.pushforward_vector K _ _ _ j

theorem norm_dilation_le (p : ℕ+) : ‖dilation K hK p‖ ≤ 1 / Real.sqrt (p : ℝ) :=
  KernelHilbert.norm_pushforward_le K _ _ _

theorem dilation_one : dilation K hK 1 = 1 := by
  apply KernelHilbert.ext_on_vectors K
  intro j
  change dilation K hK 1 (KernelHilbert.vector K j) =
    (1 : KernelHilbert K →L[ℂ] KernelHilbert K) (KernelHilbert.vector K j)
  rw [dilation_vector, one_mul]
  rfl

theorem dilation_mul (p q : ℕ+) : dilation K hK p * dilation K hK q = dilation K hK (p * q) := by
  apply KernelHilbert.ext_on_vectors K
  intro j
  change dilation K hK p (dilation K hK q (KernelHilbert.vector K j)) =
    dilation K hK (p * q) (KernelHilbert.vector K j)
  rw [dilation_vector, dilation_vector, dilation_vector, mul_assoc]

def naturalDilation (n : ℕ) : KernelHilbert K →L[ℂ] KernelHilbert K :=
  if hn : 0 < n then dilation K hK ⟨n, hn⟩ else 0

theorem naturalDilation_zero : naturalDilation K hK 0 = 0 :=
  dif_neg (Nat.not_lt_zero 0)

theorem naturalDilation_pos (n : ℕ) (hn : 0 < n) :
    naturalDilation K hK n = dilation K hK ⟨n, hn⟩ := dif_pos hn

theorem naturalDilation_one : naturalDilation K hK 1 = 1 := by
  rw [naturalDilation_pos K hK 1 Nat.zero_lt_one]
  exact dilation_one K hK

theorem naturalDilation_mul (m n : ℕ) :
    naturalDilation K hK (m * n) = naturalDilation K hK m * naturalDilation K hK n := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [zero_mul, naturalDilation_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [mul_zero, naturalDilation_zero]
  rw [naturalDilation_pos K hK m hm, naturalDilation_pos K hK n hn,
    naturalDilation_pos K hK (m * n) (Nat.mul_pos hm hn)]
  exact (dilation_mul K hK ⟨m, hm⟩ ⟨n, hn⟩).symm

theorem norm_naturalDilation_le (n : ℕ) (hn : n ≠ 0) :
    ‖naturalDilation K hK n‖ ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
  rw [naturalDilation_pos K hK n (Nat.pos_of_ne_zero hn)]
  calc
    _ ≤ 1 / Real.sqrt (n : ℝ) := norm_dilation_le K hK ⟨n, Nat.pos_of_ne_zero hn⟩
    _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_neg (Nat.cast_nonneg n), one_div]

/-- Absolute Wiener summation integrates the critical dilation action. -/
def representation : WienerAlgebraAt (1 / 2) →ₐ[ℂ] (KernelHilbert K →L[ℂ] KernelHilbert K) :=
  sequenceRepresentation (naturalDilation K hK) (naturalDilation_zero K hK)
    (norm_naturalDilation_le K hK) (naturalDilation_one K hK) (naturalDilation_mul K hK)

def representationLinear : WienerAlgebraAt (1 / 2) →L[ℂ] (KernelHilbert K →L[ℂ] KernelHilbert K) :=
  sequenceExtension (naturalDilation K hK) (naturalDilation_zero K hK) (norm_naturalDilation_le K hK)

theorem representation_pointMass (n : ℕ) :
    representation K hK (pointMass n) = naturalDilation K hK n :=
  sequenceExtension_pointMass (naturalDilation K hK) (naturalDilation_zero K hK)
    (norm_naturalDilation_le K hK) n

theorem representation_pointMass_vector (p j : ℕ+) :
    representation K hK (pointMass p) (KernelHilbert.vector K j) =
      KernelHilbert.vector K (p * j) := by
  rw [representation_pointMass, naturalDilation_pos K hK p p.property, dilation_vector]
  rfl

theorem norm_representation_le (a : WienerAlgebraAt (1 / 2)) : ‖representation K hK a‖ ≤ ‖a‖ :=
  norm_tsum_coefficient_smul_le (naturalDilation K hK) (naturalDilation_zero K hK)
    (norm_naturalDilation_le K hK) a

variable (L : ℕ+ → ℕ+ → ℂ) [Fact (IsPSDKernel L)]
  (hL : ∀ (p : ℕ+) (a : ℕ+ →₀ ℂ),
    (kernelForm (fun j k => L (p * j) (p * k)) a a).re ≤
      (1 / Real.sqrt (p : ℝ)) ^ 2 * (kernelForm L a a).re)

/-- A continuous comparison of Gram generators intertwines every Wiener cyclic vector. -/
theorem intertwines_cyclic_vector
    (P : KernelHilbert K →L[ℂ] KernelHilbert L)
    (hP : ∀ j, P (KernelHilbert.vector K j) = KernelHilbert.vector L j)
    (a : WienerAlgebraAt (1 / 2)) :
    P (representation K hK a (KernelHilbert.vector K 1)) =
      representation L hL a (KernelHilbert.vector L 1) := by
  let F : WienerAlgebraAt (1 / 2) →L[ℂ] KernelHilbert L :=
    P.comp ((ContinuousLinearMap.apply ℂ (KernelHilbert K) (KernelHilbert.vector K 1)).comp
      (representationLinear K hK))
  let G : WienerAlgebraAt (1 / 2) →L[ℂ] KernelHilbert L :=
    (ContinuousLinearMap.apply ℂ (KernelHilbert L) (KernelHilbert.vector L 1)).comp
      (representationLinear L hL)
  have hpoint (n : ℕ) : F (pointMass n) = G (pointMass n) := by
    change P (representation K hK (pointMass n) (KernelHilbert.vector K 1)) =
      representation L hL (pointMass n) (KernelHilbert.vector L 1)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [representation_pointMass, naturalDilation_zero, zero_apply, map_zero,
        representation_pointMass, naturalDilation_zero, zero_apply]
    · let p : ℕ+ := ⟨n, hn⟩
      change P (representation K hK (pointMass p) (KernelHilbert.vector K 1)) =
        representation L hL (pointMass p) (KernelHilbert.vector L 1)
      rw [representation_pointMass_vector, representation_pointMass_vector, hP]
  have hF := F.hasSum (hasSum_pointMass a)
  have hG := G.hasSum (hasSum_pointMass a)
  have hFG : F a = G a := (hF.congr_fun fun n => by simp only [map_smul, hpoint]).unique hG
  exact hFG

end GaloisForLFunctions.ArithmeticOrientationTheory.CriticalKernelAction

#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.CriticalKernelAction.intertwines_cyclic_vector
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.CriticalKernelAction.representation
#print axioms GaloisForLFunctions.ArithmeticOrientationTheory.CriticalKernelAction.norm_representation_le
end
end
