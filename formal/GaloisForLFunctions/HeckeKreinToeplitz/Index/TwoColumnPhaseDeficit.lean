import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnForm

/-!
# Exact phase deficits in the kernel column space

The unit complex phase maximizing a mixed pairing has an explicit formula.
It turns the energy of two columns into the sum of their diagonal energies
minus twice the magnitude of their interaction. The threshold works for
indefinite kernels. Hermitian symmetrization extends it to arbitrary kernels.
This is the complex version of the relative-sign mechanism in
Corollary 5 of arXiv:2611.10726.
-/

open Complex

open scoped ComplexConjugate
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {G : Type*} [Group G]

/-- The Hermitian part of any group kernel. -/
def hermitianKernelPart (k : G → ℂ) (g : G) : ℂ :=
  (k g + conj (k g⁻¹)) / 2

theorem isHermKernel_hermitianKernelPart (k : G → ℂ) :
    IsHermKernel (hermitianKernelPart k) := by
  intro g
  simp only [hermitianKernelPart, inv_inv, map_div₀, map_add, conj_conj, map_ofNat]
  rw [add_comm]

private theorem columnPair_sub_left {k : G → ℂ} (hk : IsHermKernel k)
    (v w z : kernelColumnSpan k) :
    kernelColumnPairing k (v - w) z = kernelColumnPairing k v z - kernelColumnPairing k w z := by
  rw [kernelColumnPairing_conj_symm hk, map_sub, map_sub,
    ← kernelColumnPairing_conj_symm hk, ← kernelColumnPairing_conj_symm hk]

theorem kernelColumnPairing_unit_phase {k : G → ℂ} (hk : IsHermKernel k)
    (v w : kernelColumnSpan k) {a : ℂ} (ha : ‖a‖ = 1) :
    (kernelColumnPairing k (v - a • w) (v - a • w)).re =
      (kernelColumnPairing k v v).re + (kernelColumnPairing k w w).re -
        2 * (a * kernelColumnPairing k v w).re := by
  have haa : conj a * a = 1 := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, ha]
    norm_num
  have he : kernelColumnPairing k (v - a • w) (v - a • w) =
      kernelColumnPairing k v v + kernelColumnPairing k w w -
        (a * kernelColumnPairing k v w + conj (a * kernelColumnPairing k v w)) := by
    simp only [columnPair_sub_left hk, map_sub, map_smul, smul_eq_mul,
      kernelColumnPairing_smul_left hk]
    rw [kernelColumnPairing_conj_symm hk w v, map_mul]
    linear_combination haa * kernelColumnPairing k w w
  rw [he]
  simp only [Complex.sub_re, Complex.add_re, Complex.conj_re]
  ring

private theorem exists_unit_phase (z : ℂ) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ (a * z).re = ‖z‖ := by
  by_cases hz : z = 0
  · exact ⟨1, norm_one, by simp only [hz, mul_zero, zero_re, norm_zero]⟩
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hn, div_self hn.ne']
    · rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq, Complex.div_ofReal_re, Complex.ofReal_re,
        sq, mul_div_assoc, div_self hn.ne', mul_one]

/-- The optimal complex phase attains the full magnitude of the mixed pairing. -/
theorem kernelColumnPairing_exists_phase_min {k : G → ℂ} (hk : IsHermKernel k)
    (v w : kernelColumnSpan k) :
    ∃ a : ℂ, ‖a‖ = 1 ∧
      (kernelColumnPairing k (v - a • w) (v - a • w)).re =
        (kernelColumnPairing k v v).re + (kernelColumnPairing k w w).re -
          2 * ‖kernelColumnPairing k v w‖ := by
  obtain ⟨a, ha, he⟩ := exists_unit_phase (kernelColumnPairing k v w)
  exact ⟨a, ha, by rw [kernelColumnPairing_unit_phase hk v w ha, he]⟩

/-- A unit-phase negative direction is characterized exactly by its mixed magnitude. -/
theorem kernelColumnPairing_phase_negative_iff {k : G → ℂ} (hk : IsHermKernel k)
    (v w : kernelColumnSpan k) :
    (∃ a : ℂ, ‖a‖ = 1 ∧ (kernelColumnPairing k (v - a • w) (v - a • w)).re < 0) ↔
      (kernelColumnPairing k v v).re + (kernelColumnPairing k w w).re <
        2 * ‖kernelColumnPairing k v w‖ := by
  constructor
  · rintro ⟨a, ha, he⟩
    rw [kernelColumnPairing_unit_phase hk v w ha] at he
    have h := Complex.re_le_norm (a * kernelColumnPairing k v w)
    rw [norm_mul, ha, one_mul] at h
    linarith only [he, h]
  · intro h
    obtain ⟨a, ha, he⟩ := kernelColumnPairing_exists_phase_min hk v w
    exact ⟨a, ha, he.trans_lt (by linarith only [h])⟩

/-- Hermitian symmetrization gives an unconditional phase threshold for every group kernel. -/
theorem hermitianKernelPart_phase_negative_iff (k : G → ℂ)
    (v w : kernelColumnSpan (hermitianKernelPart k)) :
    (∃ a : ℂ, ‖a‖ = 1 ∧
      (kernelColumnPairing (hermitianKernelPart k) (v - a • w) (v - a • w)).re < 0) ↔
      (kernelColumnPairing (hermitianKernelPart k) v v).re +
        (kernelColumnPairing (hermitianKernelPart k) w w).re <
          2 * ‖kernelColumnPairing (hermitianKernelPart k) v w‖ :=
  kernelColumnPairing_phase_negative_iff (isHermKernel_hermitianKernelPart k) v w

#print axioms hermitianKernelPart_phase_negative_iff
end GaloisForLFunctions.HeckeKreinToeplitz
