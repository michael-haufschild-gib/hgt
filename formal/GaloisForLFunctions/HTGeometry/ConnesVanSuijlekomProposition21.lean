import GaloisForLFunctions.HTGeometry.ConnesVanSuijlekomToeplitz

/-!
# Connes--van Suijlekom Proposition 2.1: source audit and nonzero correction

Proposition 2.1 of arXiv:2511.23257v1 omits the necessary hypothesis that
its kernel vector is nonzero.  With the zero vector, its Laurent generator is
zero and the asserted basis in clause (2) cannot span the quotient.  This
module closes that obstruction and proves the first positive fact required by
the corrected quotient construction: a nonzero source kernel vector has
nonzero leading coefficient.
-/

open scoped BigOperators ComplexOrder
open Matrix Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Laurent generator `P = ∑ aⱼXʲ` used in Proposition 2.1. -/
def connesVanSuijlekomP21Generator {N : ℕ} (a : Fin (N + 1) → ℝ) :
    LaurentPolynomial ℂ :=
  ∑ j : Fin (N + 1), LaurentPolynomial.C (a j : ℂ) * LaurentPolynomial.T (j : ℤ)

/-- The principal Laurent ideal used in Proposition 2.1. -/
def connesVanSuijlekomP21Ideal {N : ℕ} (a : Fin (N + 1) → ℝ) :
    Ideal (LaurentPolynomial ℂ) :=
  Ideal.span {connesVanSuijlekomP21Generator a}

/-- The canonical involution of the source Laurent algebra: conjugate
coefficients and reverse the Laurent exponent. -/
def connesVanSuijlekomP21Star : LaurentPolynomial ℂ →+* LaurentPolynomial ℂ :=
  (LaurentPolynomial.invert (R := ℂ)).toRingEquiv.toRingHom.comp
    (AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ))

/-- Action of the source involution on a Laurent monomial. -/
theorem connesVanSuijlekomP21_star_C_mul_T (z : ℂ) (n : ℤ) :
    connesVanSuijlekomP21Star (LaurentPolynomial.C z * LaurentPolynomial.T n) =
      LaurentPolynomial.C (star z) * LaurentPolynomial.T (-n) := by
  simp only [connesVanSuijlekomP21Star, RingHom.comp_apply, map_mul]
  rw [show AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ) (LaurentPolynomial.C z) =
      LaurentPolynomial.C (star z) by
    apply LaurentPolynomial.ext
    intro k
    rw [AddMonoidAlgebra.coeff_mapRingHom, LaurentPolynomial.C_apply,
      LaurentPolynomial.C_apply]
    by_cases hk : k = 0 <;> simp [hk],
    show AddMonoidAlgebra.mapRingHom ℤ (starRingEnd ℂ) (LaurentPolynomial.T n) =
      LaurentPolynomial.T n by
    apply LaurentPolynomial.ext
    intro k
    rw [AddMonoidAlgebra.coeff_mapRingHom]
    by_cases hk : n = k <;> simp [LaurentPolynomial.T_apply, hk]]
  simp

/-- The canonical source involution is involutive. -/
theorem connesVanSuijlekomP21_star_involutive (p : LaurentPolynomial ℂ) :
    connesVanSuijlekomP21Star (connesVanSuijlekomP21Star p) = p := by
  apply LaurentPolynomial.ext
  intro n
  simp [connesVanSuijlekomP21Star, AddMonoidAlgebra.coeff_mapRingHom]

/-- The spanning consequence of the source's clause (2) when `N = 1`: the
sole listed monomial `1` would span the Laurent quotient. -/
def connesVanSuijlekomP21SingleMonomialSpans (J : Ideal (LaurentPolynomial ℂ)) : Prop :=
  ∀ z : LaurentPolynomial ℂ, ∃ a : ℂ,
    Ideal.Quotient.mk J z = Ideal.Quotient.mk J (LaurentPolynomial.C a)

/-- The zero source kernel vector generates the zero Laurent polynomial. -/
theorem connesVanSuijlekomP21_generator_zero :
    connesVanSuijlekomP21Generator (fun _ : Fin 2 => (0 : ℝ)) = 0 := by
  simp [connesVanSuijlekomP21Generator]

/-- Its source ideal is therefore the zero ideal. -/
theorem connesVanSuijlekomP21_ideal_zero :
    connesVanSuijlekomP21Ideal (fun _ : Fin 2 => (0 : ℝ)) = ⊥ := by
  rw [connesVanSuijlekomP21Ideal, connesVanSuijlekomP21_generator_zero]
  simp

/-- A single constant Laurent monomial cannot span the full Laurent algebra. -/
theorem connesVanSuijlekomP21_singleMonomialSpans_bot_false :
    ¬ connesVanSuijlekomP21SingleMonomialSpans (⊥ : Ideal (LaurentPolynomial ℂ)) := by
  intro h
  obtain ⟨a, ha⟩ := h (LaurentPolynomial.T 1)
  have hzero : Ideal.Quotient.mk (⊥ : Ideal (LaurentPolynomial ℂ))
      (LaurentPolynomial.T 1 - LaurentPolynomial.C a) = 0 := by
    rw [map_sub, ha, sub_self]
  have hmem : LaurentPolynomial.T 1 - LaurentPolynomial.C a ∈
      (⊥ : Ideal (LaurentPolynomial ℂ)) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  have heq : LaurentPolynomial.T 1 - LaurentPolynomial.C a = 0 := by
    simpa using hmem
  have hcoeff := congrArg (fun p : LaurentPolynomial ℂ => p.coeff 1) heq
  simp at hcoeff

/-- **Source obstruction for Proposition 2.1(2).**

The printed hypotheses admit the zero kernel vector, but for that vector the
claimed one-monomial quotient spanning statement is false. -/
theorem connesVanSuijlekomP21_zero_kernel_clauseTwo_obstruction :
    ¬ connesVanSuijlekomP21SingleMonomialSpans
      (connesVanSuijlekomP21Ideal (fun _ : Fin 2 => (0 : ℝ))) := by
  rw [connesVanSuijlekomP21_ideal_zero]
  exact connesVanSuijlekomP21_singleMonomialSpans_bot_false

/-- The zero vector satisfies every finite Toeplitz kernel equation, exposing
the missing nonzero-vector hypothesis in the printed proposition. -/
theorem connesVanSuijlekomP21_zero_vector_in_kernel
    {N : ℕ} (c : ℕ → ℝ) :
    connesVanSuijlekomRealToeplitz N c *ᵥ (fun _ => (0 : ℂ)) = 0 := by
  ext i
  simp [Matrix.mulVec]

/-- The source rank hypothesis gives the exact one-dimensional complex kernel
needed for the corrected quotient construction. -/
theorem connesVanSuijlekomP21_kernel_finrank_eq_one
    {N : ℕ} (c : ℕ → ℝ)
    (hRank : (connesVanSuijlekomRealToeplitz N c).rank = N) :
    Module.finrank ℂ
      (LinearMap.ker (connesVanSuijlekomRealToeplitz N c).mulVecLin) = 1 := by
  have hsum := LinearMap.finrank_range_add_finrank_ker
    (connesVanSuijlekomRealToeplitz N c).mulVecLin
  change (connesVanSuijlekomRealToeplitz N c).rank +
      Module.finrank ℂ (LinearMap.ker (connesVanSuijlekomRealToeplitz N c).mulVecLin) =
        Module.finrank ℂ (Fin (N + 1) → ℂ) at hsum
  rw [hRank, Module.finrank_fintype_fun_eq_card] at hsum
  simp only [Fintype.card_fin] at hsum
  omega

/-- The source real Toeplitz matrix is invariant under reversal of both
finite indices. -/
theorem connesVanSuijlekomP21_toeplitz_reverse_entries
    (N : ℕ) (c : ℕ → ℝ) (i j : Fin (N + 1)) :
    connesVanSuijlekomRealToeplitz N c i.rev j.rev =
      connesVanSuijlekomRealToeplitz N c i j := by
  have hi : (i.rev : ℤ) + (i : ℤ) = N := by
    exact_mod_cast i.rev_add_cast
  have hj : (j.rev : ℤ) + (j : ℤ) = N := by
    exact_mod_cast j.rev_add_cast
  have hdiff : (i.rev : ℤ) - (j.rev : ℤ) = -((i : ℤ) - (j : ℤ)) := by omega
  simp only [connesVanSuijlekomRealToeplitz, circleToeplitzGram]
  rw [hdiff, Int.natAbs_neg]

/-- Reversal of a finite Fourier coefficient vector. -/
def connesVanSuijlekomP21ReverseVector {N : ℕ} (v : Fin (N + 1) → ℂ) :
    Fin (N + 1) → ℂ :=
  fun i => v i.rev

/-- Reflection preserves the kernel of every source real Toeplitz matrix. -/
theorem connesVanSuijlekomP21_reverse_vector_in_kernel
    {N : ℕ} (c : ℕ → ℝ) (a : Fin (N + 1) → ℂ)
    (hker : connesVanSuijlekomRealToeplitz N c *ᵥ a = 0) :
    connesVanSuijlekomRealToeplitz N c *ᵥ connesVanSuijlekomP21ReverseVector a = 0 := by
  ext i
  rw [Matrix.mulVec]
  calc
    ∑ j, connesVanSuijlekomRealToeplitz N c i j * connesVanSuijlekomP21ReverseVector a j =
        ∑ j, connesVanSuijlekomRealToeplitz N c i j.rev * a j := by
      have hsum := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (N + 1)))
        (fun j => connesVanSuijlekomRealToeplitz N c i j *
          connesVanSuijlekomP21ReverseVector a j)
      simpa [connesVanSuijlekomP21ReverseVector] using hsum.symm
    _ = ∑ j, connesVanSuijlekomRealToeplitz N c i.rev j * a j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← connesVanSuijlekomP21_toeplitz_reverse_entries N c i j.rev]
      simp
    _ = 0 := by
      exact congrFun hker i.rev

/-- Reversal is an involution on finite Fourier coefficient vectors. -/
theorem connesVanSuijlekomP21_reverse_reverse
    {N : ℕ} (v : Fin (N + 1) → ℂ) :
    connesVanSuijlekomP21ReverseVector (connesVanSuijlekomP21ReverseVector v) = v := by
  funext i
  simp [connesVanSuijlekomP21ReverseVector]

/-- Reversal commutes with complex scalar multiplication. -/
theorem connesVanSuijlekomP21_reverse_smul
    {N : ℕ} (z : ℂ) (v : Fin (N + 1) → ℂ) :
    connesVanSuijlekomP21ReverseVector (z • v) =
      z • connesVanSuijlekomP21ReverseVector v := by
  funext i
  simp [connesVanSuijlekomP21ReverseVector]

/-- The one-dimensional source kernel is palindromic or anti-palindromic:
reversing a nonzero real kernel vector multiplies it by a scalar whose square
is one. -/
theorem connesVanSuijlekomP21_reverse_vector_smul
    {N : ℕ} (c : ℕ → ℝ)
    (hRank : (connesVanSuijlekomRealToeplitz N c).rank = N)
    (a : Fin (N + 1) → ℝ)
    (hker : connesVanSuijlekomRealToeplitz N c *ᵥ (fun j => (a j : ℂ)) = 0)
    (ha : a ≠ 0) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧
      connesVanSuijlekomP21ReverseVector (fun j => (a j : ℂ)) = ε • (fun j => (a j : ℂ)) := by
  let M := connesVanSuijlekomRealToeplitz N c
  let v : Fin (N + 1) → ℂ := fun j => (a j : ℂ)
  have hv : v ≠ 0 := by
    intro h
    apply ha
    funext j
    have hj : (a j : ℂ) = 0 := by
      simpa [v] using congrFun h j
    exact_mod_cast hj
  let K := LinearMap.ker M.mulVecLin
  have hvK : v ∈ K := by
    exact hker
  have hrevK : connesVanSuijlekomP21ReverseVector v ∈ K := by
    exact connesVanSuijlekomP21_reverse_vector_in_kernel c v hker
  let x : K := ⟨v, hvK⟩
  let y : K := ⟨connesVanSuijlekomP21ReverseVector v, hrevK⟩
  have hx : x ≠ 0 := by
    intro h
    apply hv
    exact congrArg Subtype.val h
  have hdim : Module.finrank ℂ K = 1 := by
    simpa [K, M] using connesVanSuijlekomP21_kernel_finrank_eq_one c hRank
  obtain ⟨ε, hε⟩ := (finrank_eq_one_iff_of_nonzero' x hx).mp hdim y
  have hvec : ε • v = connesVanSuijlekomP21ReverseVector v := by
    exact congrArg Subtype.val hε
  have hrev : connesVanSuijlekomP21ReverseVector v = ε • v := hvec.symm
  have hsqVec : ε ^ 2 • v = v := by
    calc
      ε ^ 2 • v = ε • (ε • v) := by rw [pow_two, smul_smul]
      _ = ε • connesVanSuijlekomP21ReverseVector v := by rw [hrev]
      _ = connesVanSuijlekomP21ReverseVector (ε • v) :=
        (connesVanSuijlekomP21_reverse_smul ε v).symm
      _ = connesVanSuijlekomP21ReverseVector (connesVanSuijlekomP21ReverseVector v) := by
        rw [hrev]
      _ = v := connesVanSuijlekomP21_reverse_reverse v
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  have hpoint := congrFun hsqVec j
  have hsq : ε ^ 2 = 1 := by
    apply (mul_right_cancel₀ hj)
    simpa [smul_eq_mul] using hpoint
  exact ⟨ε, hsq, hrev⟩

/-- Positive survivor of the Proposition 2.1 obstruction.  Under the source
Toeplitz hypotheses, a *nonzero* real kernel vector has nonzero leading
coefficient, so its Laurent generator can support the quotient construction.

This uses the independently formalized Toeplitz root theorem, not the flawed
printed quotient argument. -/
theorem connesVanSuijlekomP21_nonzero_kernel_head_ne_zero
    {N : ℕ} (c : ℕ → ℝ)
    (hG : (connesVanSuijlekomRealToeplitz N c).PosSemidef)
    (hRank : (connesVanSuijlekomRealToeplitz N c).rank = N)
    (a : Fin (N + 1) → ℝ)
    (hker : connesVanSuijlekomRealToeplitz N c *ᵥ (fun j => (a j : ℂ)) = 0)
    (ha : a ≠ 0) :
    a 0 ≠ 0 := by
  intro ha0
  let p := finiteToeplitzKernelPolynomial (fun j => (a j : ℂ))
  have hcoeff (j : Fin (N + 1)) : p.coeff (j : ℕ) = (a j : ℂ) := by
    have hfin (i : Fin (N + 1)) : (j : ℕ) = (i : ℕ) ↔ j = i := Fin.ext_iff.symm
    simp [p, finiteToeplitzKernelPolynomial, hfin]
  have hp : p ≠ 0 := by
    intro hp
    obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      funext i
      exact h i
    have hcoeffj := hcoeff j
    rw [hp] at hcoeffj
    have hzero : (a j : ℂ) = 0 := by simpa using hcoeffj.symm
    exact hj (by exact_mod_cast hzero)
  have hroot : (0 : ℂ) ∈ p.roots := by
    rw [Polynomial.mem_roots hp]
    change p.eval 0 = 0
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    simpa [ha0] using hcoeff (0 : Fin (N + 1))
  have hunit := connesVanSuijlekom_proposition_2_2 c hG hRank a hker hroot
  norm_num at hunit

end

end GaloisForLFunctions.HTGeometry
