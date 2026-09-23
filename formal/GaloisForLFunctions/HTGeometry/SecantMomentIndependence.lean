import Mathlib
import GaloisForLFunctions.HTGeometry.JacobianAlgebraicIndependence

/-!
# The moment map of `r` atoms is dominant in degree `2r`

The `n`-th moment of `r` weighted atoms is `mₙ = ∑ⱼ Uⱼ Tⱼⁿ`.  The first `2r` of these are
algebraically independent, which is the statement that the `r`-th secant variety of the rational
normal curve has dimension `2r`, hence codimension `2k − 1` inside the `(2m−1)`-dimensional space of
consecutive coefficients when `r = m − k`.

The proof is the Jacobian criterion.  The Jacobian of `(m₀, …, m_{2r−1})` in the amplitudes and the
nodes is the confluent Vandermonde matrix, and its determinant is nonzero at distinct nodes because
a Hermite functional `p ↦ ∑ⱼ aⱼ p(tⱼ) + ∑ⱼ bⱼ p'(tⱼ)` that kills every polynomial of degree below
`2r` has zero weights: testing it against `∏_{i≠j}(X − tᵢ)²·(X − tⱼ)` isolates `bⱼ`, and against
`∏_{i≠j}(X − tᵢ)²` isolates `aⱼ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Finset
open MvPolynomial (pderiv)

variable {K : Type*} [Field K] {r : ℕ}

/-- The Hermite functional of a pair of weight vectors at a family of nodes:
`Φ(p) = ∑ⱼ aⱼ p(tⱼ) + ∑ⱼ bⱼ p'(tⱼ)`. -/
noncomputable def hermiteFunctional (t : Fin r → K) (a b : Fin r → K) (p : K[X]) : K :=
  ∑ j, a j * p.eval (t j) + ∑ j, b j * (derivative p).eval (t j)

theorem hermiteFunctional_add (t a b : Fin r → K) (p q : K[X]) :
    hermiteFunctional t a b (p + q)
      = hermiteFunctional t a b p + hermiteFunctional t a b q := by
  simp only [hermiteFunctional, eval_add, derivative_add, mul_add, Finset.sum_add_distrib]
  ring

theorem hermiteFunctional_zero (t a b : Fin r → K) :
    hermiteFunctional t a b 0 = 0 := by
  simp [hermiteFunctional]

theorem hermiteFunctional_smul (t a b : Fin r → K) (c : K) (p : K[X]) :
    hermiteFunctional t a b (C c * p) = c * hermiteFunctional t a b p := by
  simp only [hermiteFunctional, eval_mul, eval_C, derivative_mul, derivative_C, zero_mul,
    zero_add]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring

theorem hermiteFunctional_sum (t a b : Fin r → K) (s : Finset ℕ) (f : ℕ → K[X]) :
    hermiteFunctional t a b (∑ i ∈ s, f i) = ∑ i ∈ s, hermiteFunctional t a b (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [hermiteFunctional]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, hermiteFunctional_add, ih, Finset.sum_insert hi]

/-- A Hermite functional vanishing on every monomial below a degree bound vanishes on every
polynomial below it. -/
theorem hermiteFunctional_eq_zero_of_monomials {t a b : Fin r → K} {n : ℕ}
    (h : ∀ i : ℕ, i < n → hermiteFunctional t a b (X ^ i) = 0)
    (p : K[X]) (hp : p.natDegree < n) : hermiteFunctional t a b p = 0 := by
  classical
  have hsum : p = ∑ i ∈ range n, C (p.coeff i) * X ^ i := by
    conv_lhs => rw [p.as_sum_range' n hp]
    exact Finset.sum_congr rfl fun i _ => by rw [C_mul_X_pow_eq_monomial]
  rw [hsum, hermiteFunctional_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hermiteFunctional_smul, h i (Finset.mem_range.mp hi), mul_zero]

/-! ### The Hermite nodes -/

theorem eval_derivative_eq_zero_of_sq_dvd {p : K[X]} {c : K}
    (h : (X - C c) ^ (2 : ℕ) ∣ p) : (derivative p).eval c = 0 := by
  obtain ⟨u, rfl⟩ := h
  rw [derivative_mul, derivative_pow]
  simp

/-- The double-node polynomial at every node except `j`. -/
noncomputable def hermiteNodePoly (t : Fin r → K) (j : Fin r) : K[X] :=
  ∏ i ∈ Finset.univ.erase j, (X - C (t i)) ^ (2 : ℕ)

theorem natDegree_hermiteNodePoly_le (t : Fin r → K) (j : Fin r) :
    (hermiteNodePoly t j).natDegree ≤ 2 * r - 2 := by
  classical
  refine le_trans (natDegree_prod_le _ _) ?_
  have hcard : (Finset.univ.erase j).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  calc ∑ i ∈ Finset.univ.erase j, ((X - C (t i)) ^ (2 : ℕ)).natDegree
      ≤ ∑ _i ∈ Finset.univ.erase j, 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine le_trans (natDegree_pow_le) ?_
        have : (X - C (t i)).natDegree ≤ 1 := natDegree_X_sub_C_le _
        omega
    _ = (r - 1) * 2 := by rw [Finset.sum_const, hcard, smul_eq_mul]
    _ ≤ 2 * r - 2 := by omega

theorem eval_hermiteNodePoly_of_ne (t : Fin r → K) {i j : Fin r} (hij : i ≠ j) :
    (hermiteNodePoly t j).eval (t i) = 0 := by
  classical
  rw [hermiteNodePoly, eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩) ?_
  simp

theorem eval_derivative_hermiteNodePoly_of_ne (t : Fin r → K) {i j : Fin r} (hij : i ≠ j) :
    (derivative (hermiteNodePoly t j)).eval (t i) = 0 := by
  classical
  refine eval_derivative_eq_zero_of_sq_dvd ?_
  exact Finset.dvd_prod_of_mem _ (Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩)

theorem eval_hermiteNodePoly_self_ne_zero (t : Fin r → K) (ht : Function.Injective t)
    (j : Fin r) : (hermiteNodePoly t j).eval (t j) ≠ 0 := by
  classical
  rw [hermiteNodePoly, eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
  have hij : i ≠ j := (Finset.mem_erase.mp hi).1
  have : t j - t i ≠ 0 := sub_ne_zero.mpr fun h => hij (ht h.symm)
  simpa using pow_ne_zero 2 this

/-- The Hermite interpolation polynomial isolating the derivative weight at `j`. -/
noncomputable def hermiteDerivPoly (t : Fin r → K) (j : Fin r) : K[X] :=
  hermiteNodePoly t j * (X - C (t j))

theorem natDegree_hermiteDerivPoly_le (t : Fin r → K) (j : Fin r) :
    (hermiteDerivPoly t j).natDegree ≤ 2 * r - 1 := by
  refine le_trans (natDegree_mul_le) ?_
  have h1 := natDegree_hermiteNodePoly_le t j
  have h2 : (X - C (t j)).natDegree ≤ 1 := natDegree_X_sub_C_le _
  have hr : 1 ≤ r := j.pos
  omega

theorem eval_hermiteDerivPoly (t : Fin r → K) (i j : Fin r) :
    (hermiteDerivPoly t j).eval (t i) = 0 := by
  classical
  by_cases hij : i = j
  · subst hij; simp [hermiteDerivPoly]
  · rw [hermiteDerivPoly, eval_mul, eval_hermiteNodePoly_of_ne t hij, zero_mul]

theorem eval_derivative_hermiteDerivPoly_of_ne (t : Fin r → K) {i j : Fin r} (hij : i ≠ j) :
    (derivative (hermiteDerivPoly t j)).eval (t i) = 0 := by
  rw [hermiteDerivPoly, derivative_mul, eval_add, eval_mul, eval_mul,
    eval_derivative_hermiteNodePoly_of_ne t hij, eval_hermiteNodePoly_of_ne t hij]
  ring

theorem eval_derivative_hermiteDerivPoly_self (t : Fin r → K) (j : Fin r) :
    (derivative (hermiteDerivPoly t j)).eval (t j) = (hermiteNodePoly t j).eval (t j) := by
  rw [hermiteDerivPoly, derivative_mul, eval_add, eval_mul, eval_mul]
  simp


/-- **Hermite interpolation rigidity.**  A Hermite functional at distinct nodes that kills every
monomial of degree below `2r` has zero weights. -/
theorem hermiteFunctional_weights_eq_zero {t a b : Fin r → K} (ht : Function.Injective t)
    (h : ∀ i : ℕ, i < 2 * r → hermiteFunctional t a b (X ^ i) = 0) :
    a = 0 ∧ b = 0 := by
  classical
  have hall : ∀ p : K[X], p.natDegree < 2 * r → hermiteFunctional t a b p = 0 := fun p hp =>
    hermiteFunctional_eq_zero_of_monomials h p hp
  have hb : ∀ j : Fin r, b j = 0 := by
    intro j
    have hr : 1 ≤ r := j.pos
    have hdeg : (hermiteDerivPoly t j).natDegree < 2 * r := by
      have := natDegree_hermiteDerivPoly_le t j
      omega
    have hΦ := hall _ hdeg
    rw [hermiteFunctional] at hΦ
    have h1 : ∑ i, a i * (hermiteDerivPoly t j).eval (t i) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [eval_hermiteDerivPoly, mul_zero]
    have h2 : ∑ i, b i * (derivative (hermiteDerivPoly t j)).eval (t i)
        = b j * (hermiteNodePoly t j).eval (t j) := by
      rw [Finset.sum_eq_single j]
      · rw [eval_derivative_hermiteDerivPoly_self]
      · intro i _ hij
        rw [eval_derivative_hermiteDerivPoly_of_ne t hij, mul_zero]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rw [h1, h2, zero_add] at hΦ
    rcases mul_eq_zero.mp hΦ with hbj | hev
    · exact hbj
    · exact absurd hev (eval_hermiteNodePoly_self_ne_zero t ht j)
  refine ⟨funext fun j => ?_, funext fun j => hb j⟩
  have hr : 1 ≤ r := j.pos
  have hdeg : (hermiteNodePoly t j).natDegree < 2 * r := by
    have := natDegree_hermiteNodePoly_le t j
    omega
  have hΦ := hall _ hdeg
  rw [hermiteFunctional] at hΦ
  have h2 : ∑ i, b i * (derivative (hermiteNodePoly t j)).eval (t i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hb i, zero_mul]
  have h1 : ∑ i, a i * (hermiteNodePoly t j).eval (t i)
      = a j * (hermiteNodePoly t j).eval (t j) := by
    rw [Finset.sum_eq_single j]
    · intro i _ hij
      rw [eval_hermiteNodePoly_of_ne t hij, mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  rw [h1, h2, add_zero] at hΦ
  rcases mul_eq_zero.mp hΦ with haj | hev
  · exact haj
  · exact absurd hev (eval_hermiteNodePoly_self_ne_zero t ht j)


/-! ### The confluent Vandermonde matrix -/

/-- The exponent attached to a column index. -/
def confluentExp (k : Fin r ⊕ Fin r) : ℕ := (finSumFinEquiv k : ℕ)

theorem confluentExp_lt (k : Fin r ⊕ Fin r) : confluentExp k < 2 * r := by
  have := (finSumFinEquiv k).isLt
  rw [confluentExp]
  omega

theorem exists_confluentExp (i : ℕ) (hi : i < 2 * r) : ∃ k : Fin r ⊕ Fin r, confluentExp k = i := by
  refine ⟨finSumFinEquiv.symm ⟨i, by omega⟩, ?_⟩
  rw [confluentExp, Equiv.apply_symm_apply]

/-- The confluent Vandermonde matrix at a family of nodes: the value rows are the ordinary
Vandermonde rows and the derivative rows are their formal derivatives. -/
noncomputable def confluentVandermonde (t : Fin r → K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  Matrix.of fun j k => Sum.elim
    (fun j' : Fin r => t j' ^ confluentExp k)
    (fun j' : Fin r => ((confluentExp k : ℕ) : K) * t j' ^ (confluentExp k - 1)) j

/-- **The confluent Vandermonde determinant is nonzero at distinct nodes.** -/
theorem det_confluentVandermonde_ne_zero (t : Fin r → K) (ht : Function.Injective t) :
    (confluentVandermonde t).det ≠ 0 := by
  classical
  intro hdet
  have hT : (confluentVandermonde t).transpose.det = 0 := by rw [Matrix.det_transpose]; exact hdet
  obtain ⟨v, hv, hmul⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hT
  set a : Fin r → K := fun j => v (Sum.inl j) with ha
  set b : Fin r → K := fun j => v (Sum.inr j) with hb
  have hmono : ∀ i : ℕ, i < 2 * r → hermiteFunctional t a b (X ^ i) = 0 := by
    intro i hi
    obtain ⟨k, hk⟩ := exists_confluentExp i hi
    have hrow := congrFun hmul k
    rw [Matrix.mulVec, dotProduct] at hrow
    have hsplit : ∑ j : Fin r ⊕ Fin r, (confluentVandermonde t).transpose k j * v j
        = (∑ j : Fin r, t j ^ confluentExp k * a j)
          + ∑ j : Fin r, ((confluentExp k : ℕ) : K) * t j ^ (confluentExp k - 1) * b j := by
      rw [Fintype.sum_sum_type]
      rfl
    rw [hsplit] at hrow
    rw [hermiteFunctional]
    simp only [eval_pow, eval_X, derivative_X_pow, eval_mul, eval_C, eval_pow]
    rw [← hk]
    calc (∑ j : Fin r, a j * t j ^ confluentExp k)
          + ∑ j : Fin r, b j * (((confluentExp k : ℕ) : K) * t j ^ (confluentExp k - 1))
        = (∑ j : Fin r, t j ^ confluentExp k * a j)
          + ∑ j : Fin r, ((confluentExp k : ℕ) : K) * t j ^ (confluentExp k - 1) * b j := by
          congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
      _ = 0 := hrow
  obtain ⟨ha0, hb0⟩ := hermiteFunctional_weights_eq_zero ht hmono
  refine hv (funext fun j => ?_)
  cases j with
  | inl j => exact congrFun ha0 j
  | inr j => exact congrFun hb0 j


/-! ### The moment map of `r` atoms -/

/-- The `n`-th moment of `r` atoms with amplitudes `X (j,0)` and nodes `X (j,1)`. -/
noncomputable def secantMomentPoly (K : Type*) [CommRing K] (r n : ℕ) :
    MvPolynomial (Fin r × Fin 2) K :=
  ∑ j : Fin r, MvPolynomial.X (j, (0 : Fin 2)) * MvPolynomial.X (j, (1 : Fin 2)) ^ n

/-- The coordinate attached to a row index: amplitudes first, then nodes. -/
def secantCoordinate (r : ℕ) : Fin r ⊕ Fin r → Fin r × Fin 2 :=
  Sum.elim (fun j => (j, (0 : Fin 2))) (fun j => (j, (1 : Fin 2)))

theorem pderiv_amplitude_secantMomentPoly (K : Type*) [CommRing K] (r n : ℕ) (j : Fin r) :
    pderiv (j, (0 : Fin 2)) (secantMomentPoly K r n)
      = MvPolynomial.X (j, (1 : Fin 2)) ^ n := by
  classical
  rw [secantMomentPoly, map_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hlj
    have h1 : ((j, (0 : Fin 2)) : Fin r × Fin 2) ≠ (l, (0 : Fin 2)) := by
      simpa using fun h => hlj h.symm
    simp [h1]
  · intro hj; exact absurd (Finset.mem_univ j) hj

theorem pderiv_node_secantMomentPoly (K : Type*) [CommRing K] (r n : ℕ) (j : Fin r) :
    pderiv (j, (1 : Fin 2)) (secantMomentPoly K r n)
      = MvPolynomial.X (j, (0 : Fin 2)) * ((n : MvPolynomial (Fin r × Fin 2) K)
          * MvPolynomial.X (j, (1 : Fin 2)) ^ (n - 1)) := by
  classical
  rw [secantMomentPoly, map_sum]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hlj
    have h2 : ((j, (1 : Fin 2)) : Fin r × Fin 2) ≠ (l, (1 : Fin 2)) := by
      simpa using fun h => hlj h.symm
    simp [h2]
  · intro hj; exact absurd (Finset.mem_univ j) hj


/-- **The first `2r` moments of `r` atoms are algebraically independent.**  Equivalently, the
`r`-th secant variety of the rational normal curve has dimension `2r`: the moment map is dominant
onto a `2r`-dimensional image. -/
theorem algebraicIndependent_secantMomentPoly (K : Type*) [Field K] [CharZero K] (r : ℕ) :
    AlgebraicIndependent K
      (fun k : Fin r ⊕ Fin r => secantMomentPoly K r (confluentExp k)) := by
  classical
  haveI : Infinite K := CharZero.infinite K
  set t : Fin r → K := fun j => Infinite.natEmbedding K (j : ℕ) with hts
  have ht : Function.Injective t := by
    intro i j hij
    exact Fin.ext ((Infinite.natEmbedding K).injective hij)
  set pt : Fin r × Fin 2 → K := fun p => if p.2 = 0 then 1 else t p.1 with hpt
  refine MvPolynomial.algebraicIndependent_of_jacobian_det_ne_zero
    (fun k : Fin r ⊕ Fin r => secantMomentPoly K r (confluentExp k)) (secantCoordinate r) ?_
  intro hdet
  have hmap : (MvPolynomial.polynomialJacobianMinor
      (fun k : Fin r ⊕ Fin r => secantMomentPoly K r (confluentExp k))
      (secantCoordinate r)).map (MvPolynomial.eval pt) = confluentVandermonde t := by
    funext j k
    cases j with
    | inl j' =>
        simp only [Matrix.map_apply, MvPolynomial.polynomialJacobianMinor, secantCoordinate,
          Sum.elim_inl, confluentVandermonde, Matrix.of_apply, Sum.elim_inl]
        rw [pderiv_amplitude_secantMomentPoly]
        simp [hpt]
    | inr j' =>
        simp only [Matrix.map_apply, MvPolynomial.polynomialJacobianMinor, secantCoordinate,
          Sum.elim_inr, confluentVandermonde, Matrix.of_apply, Sum.elim_inr]
        rw [pderiv_node_secantMomentPoly]
        simp [hpt]
  have hzero : (confluentVandermonde t).det = 0 := by
    have hd := RingHom.map_det (MvPolynomial.eval pt)
      (MvPolynomial.polynomialJacobianMinor
        (fun k : Fin r ⊕ Fin r => secantMomentPoly K r (confluentExp k)) (secantCoordinate r))
    rw [RingHom.mapMatrix_apply] at hd
    rw [← hmap, ← hd, hdet, map_zero]
  exact det_confluentVandermonde_ne_zero t ht hzero


end GaloisForLFunctions.HTGeometry
