import GaloisForLFunctions.HTGeometry.MomentHankelNormalBlocks

/-!
# Kernel coordinates and the Gram block at a singular Hankel gap

The kernel parametrization is a linear isomorphism from exactly
`min k (d-k)` free coordinates. Consecutive multiples of the canonical monic
admission are orthogonal to the old head; their Gram block vanishes before
its constant nonzero anti-diagonal. These statements hold without positivity.
-/

open scoped BigOperators
open Polynomial Matrix
namespace HTGeometry
noncomputable section

theorem ofFn_toFn_of_degree_lt {p : ℝ[X]} {N : ℕ}
    (hp : p.degree < (N : WithBot ℕ)) : Polynomial.ofFn N (Polynomial.toFn N p) = p := by
  by_cases h0 : p = 0
  · simp [h0]
  · exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
      ((Polynomial.natDegree_lt_iff_degree_lt h0).mpr hp)

theorem MomentSectionKernel.toFn_mem_ker {s : ℕ → ℝ} {N : ℕ} {p : ℝ[X]}
    (hp : MomentSectionKernel s N p) :
    Polynomial.toFn N p ∈ LinearMap.ker (momentHankelMatrix s N).mulVecLin := by
  change momentHankelMatrix s N *ᵥ Polynomial.toFn N p = 0
  apply (momentSectionKernel_ofFn_iff s N _).mp
  rwa [ofFn_toFn_of_degree_lt hp.1]

namespace MomentNormalBlock
variable {s : ℕ → ℝ} {n d : ℕ} (h : MomentNormalBlock s n d)

/-- Coordinates of every kernel vector, through the canonical null polynomial. -/
def kernelParam {k : ℕ} (hk : k ≤ d) :
    (Fin (min k (d - k)) → ℝ) →ₗ[ℝ]
      LinearMap.ker (momentHankelMatrix s (n + k)).mulVecLin where
  toFun c :=
    ⟨Polynomial.toFn (n + k)
      (monicMomentAdmissionPolynomial s n * Polynomial.ofFn (min k (d - k)) c),
      ((h.kernel_iff hk _).mpr ⟨_, Polynomial.ofFn_degree_lt c, rfl⟩).toFn_mem_ker⟩
  map_add' x y := by
    apply Subtype.ext
    change Polynomial.toFn (n + k) (_ * Polynomial.ofFn _ (x + y)) = _
    simp only [map_add, mul_add]
    rfl
  map_smul' r x := by
    apply Subtype.ext
    change Polynomial.toFn (n + k) (_ * Polynomial.ofFn _ (r • x)) = _
    simp only [map_smul, mul_smul_comm]
    rfl

include h in
theorem kernelParam_bijective {k : ℕ} (hk : k ≤ d) :
    Function.Bijective (h.kernelParam hk) := by
  constructor
  · intro x y hxy
    have hh := congrArg (fun c : LinearMap.ker (momentHankelMatrix s (n + k)).mulVecLin =>
      Polynomial.ofFn (n + k) c.val) hxy
    change Polynomial.ofFn (n + k) (Polynomial.toFn (n + k)
      (monicMomentAdmissionPolynomial s n * Polynomial.ofFn _ x)) =
        Polynomial.ofFn (n + k) (Polynomial.toFn (n + k)
          (monicMomentAdmissionPolynomial s n * Polynomial.ofFn _ y)) at hh
    rw [ofFn_toFn_of_degree_lt ((h.kernel_iff hk _).mpr
      ⟨_, Polynomial.ofFn_degree_lt x, rfl⟩).1,
      ofFn_toFn_of_degree_lt ((h.kernel_iff hk _).mpr
        ⟨_, Polynomial.ofFn_degree_lt y, rfl⟩).1] at hh
    exact Polynomial.injective_ofFn _
      (mul_left_cancel₀ (monicMomentAdmissionPolynomial_monic s n).ne_zero hh)
  · intro c
    have hc : MomentSectionKernel s (n + k) (Polynomial.ofFn (n + k) c.val) :=
      (momentSectionKernel_ofFn_iff s (n + k) c.val).mpr c.property
    obtain ⟨q, hq, hpq⟩ := (h.kernel_iff hk _).mp hc
    refine ⟨Polynomial.toFn (min k (d - k)) q, ?_⟩
    apply Subtype.ext
    change Polynomial.toFn (n + k) (monicMomentAdmissionPolynomial s n *
      Polynomial.ofFn _ (Polynomial.toFn _ q)) = c.val
    rw [ofFn_toFn_of_degree_lt hq, ← hpq, Polynomial.toFn_comp_ofFn_eq_id]

include h in
/-- Exact triangular nullity profile across a singular Hankel gap. -/
theorem nullity {k : ℕ} (hk : k ≤ d) :
    Module.finrank ℝ (LinearMap.ker (momentHankelMatrix s (n + k)).mulVecLin) =
      min k (d - k) := by
  let e := LinearEquiv.ofBijective (h.kernelParam hk) (h.kernelParam_bijective hk)
  simpa using e.finrank_eq.symm

/-- Gram block in consecutive multiples of the admission polynomial. -/
def gram (s : ℕ → ℝ) (n d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => momentInner s (X ^ (i : ℕ) * monicMomentAdmissionPolynomial s n)
    (X ^ (j : ℕ) * monicMomentAdmissionPolynomial s n)

include h in
theorem orthogonal_to_head (i : Fin n) (j : Fin d) :
    momentInner s (X ^ (i : ℕ)) (X ^ (j : ℕ) * monicMomentAdmissionPolynomial s n) = 0 := by
  rw [momentInner_def, ← mul_assoc, ← pow_add]
  apply h.vanishing
  have := i.isLt
  have := j.isLt
  omega

theorem gram_eq (i j : Fin d) :
    gram s n d i j = momentFunctional s (X ^ ((i : ℕ) + j) *
      (monicMomentAdmissionPolynomial s n * monicMomentAdmissionPolynomial s n)) := by
  unfold gram momentInner
  congr 1
  rw [pow_add]
  ring

include h in
theorem gram_before_antidiagonal (i j : Fin d) (hij : (i : ℕ) + j < d - 1) :
    gram s n d i j = 0 := by
  rw [gram_eq]
  apply momentFunctional_X_pow_mul_mul_eq_zero h.vanishing
  intro a ha
  have hh := le_natDegree_of_ne_zero (mem_support_iff.mp ha)
  rw [monicMomentAdmissionPolynomial_natDegree] at hh
  omega

include h in
theorem gram_antidiagonal (i j : Fin d) (hij : (i : ℕ) + j = d - 1) :
    gram s n d i j =
      momentFunctional s (X ^ (n + d - 1) * monicMomentAdmissionPolynomial s n) := by
  rw [gram_eq, momentFunctional_X_pow_mul_mul_first h.vanishing]
  · rw [(monicMomentAdmissionPolynomial_monic s n).leadingCoeff, one_mul]
  · rw [monicMomentAdmissionPolynomial_natDegree]
    have := h.length_pos
    omega

end MomentNormalBlock
end
end HTGeometry
