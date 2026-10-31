import GaloisForLFunctions.HeckeKreinToeplitz.FiniteIndexIsPositiveMinusFiniteRank

/-!
# Subgroup zero sets at negative index one

A Hermitian group kernel with zero value at identity and at most one negative square has a
subgroup as its zero set. A nonzero coefficient supplies a hyperbolic plane. Haynsworth
additivity then forces every pair of zeros to have zero pairing.

In particular, vanishing on two subgroups whose product is the whole group forces the kernel
to vanish everywhere.
-/

open Complex Finset Matrix
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz


private def nullPlane (z : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, z; conj z, 0]

private theorem nullPlane_isHermitian (z : ℂ) : (nullPlane z).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [nullPlane, Matrix.conjTranspose_apply]

private theorem one_le_nullPlane_index {z : ℂ} (hz : z ≠ 0) :
    1 ≤ hermNegIndex (nullPlane z) := by
  by_contra hn
  have hzero : hermNegIndex (nullPlane z) = 0 := by omega
  have h := hermQuad_nonneg_of_negIndex_eq_zero hzero ![-z, 1]
  have hq : hermQuad (nullPlane z) ![-z, 1] = -2 * normSq z := by
    simp [hermQuad, nullPlane, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
      Complex.normSq_apply, Complex.mul_re]
    ring
  rw [hq] at h
  have hp := normSq_pos.mpr hz
  linarith only [h, hp]

private theorem nullPlane_isUnit {z : ℂ} (hz : z ≠ 0) : IsUnit (nullPlane z) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  have hzc : conj z ≠ 0 := by simpa using hz
  simpa [nullPlane, Matrix.det_fin_two] using mul_ne_zero hz hzc

private theorem nullPlane_inv {z : ℂ} (hz : z ≠ 0) :
    (nullPlane z)⁻¹ = !![0, (conj z)⁻¹; z⁻¹, 0] := by
  have hzc : conj z ≠ 0 := by simpa using hz
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nullPlane, Matrix.mul_apply, Fin.sum_univ_two, hz, hzc]

private theorem nullPlane_schur_zero {z : ℂ} (hz : z ≠ 0) (u v : ℂ) :
    (!![0, 0; u, v])ᴴ * (nullPlane z)⁻¹ * !![0, 0; u, v] = 0 := by
  rw [nullPlane_inv hz]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

variable {G : Type*} [Group G]

/-- The quotient of two zeros is zero when the kernel has at most one negative square. -/
theorem inv_mul_eq_zero_of_negIndex_le_one {k : G → ℂ} (hk : IsHermKernel k)
    (h1 : k 1 = 0) (hi : negIndex k ≤ 1) {x y : G} (hx : k x = 0) (hy : k y = 0) :
    k (x⁻¹ * y) = 0 := by
  classical
  by_cases hzero : ∀ g, k g = 0
  · exact hzero _
  push Not at hzero
  obtain ⟨w, hw⟩ := hzero
  let p : Fin 2 → G := ![1, w]
  let q : Fin 2 → G := ![x, y]
  let B : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; k (w⁻¹ * x), k (w⁻¹ * y)]
  have hrev (a b : G) : k (a⁻¹ * b) = conj (k (b⁻¹ * a)) := by
    rw [← hk, _root_.mul_inv_rev, inv_inv]
  have hG : gram k (Sum.elim p q) =
      Matrix.fromBlocks (nullPlane (k w)) B Bᴴ (nullPlane (k (x⁻¹ * y))) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      fin_cases a <;> fin_cases b <;>
      simp [gram, p, q, B, nullPlane, Matrix.fromBlocks, Matrix.conjTranspose_apply,
        h1, hx, hy, hk w, hk x, hk y, hrev x w, hrev y w, hrev y x]
  have hle : hermNegIndex (gram k (Sum.elim p q)) ≤ 1 := by
    exact_mod_cast (hermNegIndex_gram_le_negIndex k (Sum.elim p q)).trans hi
  -- The first cross-block row is zero, so the Schur correction vanishes.
  rw [hG, haynsworth_negIndex (nullPlane_isUnit hw) (nullPlane_isHermitian _) B
    (nullPlane_isHermitian _), nullPlane_schur_zero hw, sub_zero] at hle
  have hwindex := one_le_nullPlane_index hw
  by_contra hxy
  have hxyindex := one_le_nullPlane_index hxy
  omega

/-- The zeros of a null Hermitian kernel of index at most one form a subgroup. -/
def nullKernelZeroSubgroup {k : G → ℂ} (hk : IsHermKernel k) (h1 : k 1 = 0)
    (hi : negIndex k ≤ 1) : Subgroup G where
  carrier := {g | k g = 0}
  one_mem' := h1
  inv_mem' := by
    intro x hx
    change k x⁻¹ = 0
    rw [hk, hx, map_zero]
  mul_mem' := by
    intro x y hx hy
    have hxi : k x⁻¹ = 0 := by rw [hk, hx, map_zero]
    change k (x * y) = 0
    simpa only [inv_inv] using inv_mul_eq_zero_of_negIndex_le_one hk h1 hi hxi hy


/-- Two subgroups whose product is the group determine every null kernel of index at most one. -/
theorem eq_zero_of_subgroup_readings {k : G → ℂ} (hk : IsHermKernel k)
    (hi : negIndex k ≤ 1) (A B : Subgroup G)
    (hA : ∀ a ∈ A, k a = 0) (hB : ∀ b ∈ B, k b = 0)
    (hprod : ∀ g, ∃ a ∈ A, ∃ b ∈ B, g = a * b) : k = 0 := by
  let Z := nullKernelZeroSubgroup hk (hA 1 A.one_mem) hi
  funext g
  obtain ⟨a, ha, b, hb, rfl⟩ := hprod g
  exact Z.mul_mem (hA a ha) (hB b hb)

#print axioms inv_mul_eq_zero_of_negIndex_le_one
#print axioms nullKernelZeroSubgroup
#print axioms eq_zero_of_subgroup_readings
end GaloisForLFunctions.HeckeKreinToeplitz
