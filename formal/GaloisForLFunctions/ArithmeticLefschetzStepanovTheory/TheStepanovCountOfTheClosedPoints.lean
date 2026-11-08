import GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.IntegralityActsOnlyOnTheTorsion

/-!
# The Stepanov count of the closed points

Stepanov's count is the product formula: zeros, counted with order and degree, are bounded by the
degree of the auxiliary. Over `ℤ` the exact fixed points on the prime orbit are the points over the
closed points of the prime circles: `s` with `p^{-s}` a primitive `m`-th root of unity, a closed
point of degree `φ(m)` on the circle of `p` (the Frobenius progression `2πiℤ/log p` is `m = 1`). An
integer auxiliary `F` vanishes to order `J` along that closed point when `Φ_m(u_p)^J` divides `F`;
then `A(s) = Φ_m(p^{-s})^J B(s)` (`orbitFun_circlePoly_mul`).

* **The degree gain of one circle factor** (`pow_natDegree_mul_length_le`). For a nonzero
  one-variable `h` and `G ≠ 0`, the length `N(F) = max_{α ∈ supp F} Π p^{α_p}` satisfies
  `p^{deg h} N(G) ≤ N(h(u_p) G)`: the coefficient of the top monomial of `G` shifted by `p^{deg h}`
  is the leading coefficient of `h` times a nonzero coefficient of `G`, because every other
  contribution comes from a monomial of `G` above the top.
* **The Stepanov count** (`stepanov_count_closedPoints`). If `Π_{(p,m,J)} Φ_m(u_p)^J` divides a nonzero
  integer auxiliary, then `Σ φ(m) J log p ≤ log N(F)`: the closed points of degree `φ(m)`, each of
  weight `log p`, counted with order, are bounded by the degree. It is sharp
  (`length_circlePoly`): `Φ_m(u_p)^J` has length exactly `p^{φ(m)J}`.

This extends the Bézout theorem of `𝔾_m(ℚ)` (`EffectiveArithmeticHodgeTheory`, the closed point
`m = 1`) to all closed points of all prime circles. The count is linear algebra: vanishing along a
closed point of degree `φ(m)` costs `p^{φ(m)}` in length, whatever else the auxiliary does. There
is no cheap vanishing at the exact fixed points of `ℤ`; the Stepanov count over them is Chebyshev's.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

variable {P : Finset Nat.Primes}

/-- The integer `n = Π p^{α_p}` of an exponent vector. -/
def weight (α : P →₀ ℕ) : ℕ := ∏ p : P, ((p : Nat.Primes) : ℕ) ^ α p

theorem weight_add (α β : P →₀ ℕ) : weight (α + β) = weight α * weight β := by
  simp only [weight, Finsupp.add_apply, pow_add, prod_mul_distrib]

theorem weight_single (p : P) (k : ℕ) : weight (Finsupp.single p k) = ((p : Nat.Primes) : ℕ) ^ k := by
  classical
  rw [weight, prod_eq_single p]
  · simp
  · intro q _ hq
    rw [Finsupp.single_eq_of_ne hq, pow_zero]
  · intro h; exact absurd (mem_univ p) h

theorem weight_pos (α : P →₀ ℕ) : 0 < weight α :=
  prod_pos fun p _ => pow_pos (p : Nat.Primes).2.pos _

/-- The length `N(F) = max_{α ∈ supp F} Π p^{α_p}` of an integer auxiliary. -/
def length (F : MvPolynomial P ℤ) : ℕ := F.support.sup weight

/-- The one-variable polynomial `h` placed on the circle of `p`: `h(u_p)`. -/
def circlePoly (h : Polynomial ℤ) (p : P) : MvPolynomial P ℤ :=
  Polynomial.aeval (MvPolynomial.X p) h

theorem circlePoly_eq_sum (h : Polynomial ℤ) (p : P) :
    circlePoly h p = ∑ k ∈ range (h.natDegree + 1),
      MvPolynomial.monomial (Finsupp.single p k) (h.coeff k) := by
  rw [circlePoly, Polynomial.aeval_eq_sum_range]
  refine sum_congr rfl fun k _ => ?_
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]

/-- On the orbit a circle factor is the one-variable polynomial at `p^{-s}`. -/
theorem orbitFun_circlePoly_mul (h : Polynomial ℤ) (p : P) (G : MvPolynomial P ℤ) (s : ℂ) :
    orbitFun (circlePoly h p * G) s =
      Polynomial.aeval (Complex.exp (-s * Real.log ((p : Nat.Primes) : ℕ))) h * orbitFun G s := by
  rw [orbitFun, orbitFun, map_mul, circlePoly, ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]

/-- **The degree gain of one circle factor.** -/
theorem pow_natDegree_mul_length_le {h : Polynomial ℤ} (hh : h ≠ 0) (p : P)
    {G : MvPolynomial P ℤ} (hG : G ≠ 0) :
    ((p : Nat.Primes) : ℕ) ^ h.natDegree * length G ≤ length (circlePoly h p * G) := by
  classical
  have hne : G.support.Nonempty := MvPolynomial.support_nonempty.mpr hG
  obtain ⟨α, hα, htop⟩ := exists_mem_eq_sup G.support hne weight
  set d := h.natDegree
  set β := α + Finsupp.single p d with hβdef
  have hp2 : 2 ≤ ((p : Nat.Primes) : ℕ) := (p : Nat.Primes).2.two_le
  have hcoeff : MvPolynomial.coeff β (circlePoly h p * G) = h.leadingCoeff * G.coeff α := by
    rw [circlePoly_eq_sum, sum_mul, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial_mul']
    rw [sum_eq_single d]
    · have hle : Finsupp.single p d ≤ β := le_add_self
      rw [if_pos hle, add_tsub_cancel_right]
      rfl
    · intro k hk hkd
      have hkd' : k < d := lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hk)) hkd
      have hle : Finsupp.single p k ≤ β := by
        intro q
        by_cases hq : q = p
        · subst hq; simp [β]; omega
        · have hpq : p ≠ q := Ne.symm hq
          simp [β, hpq]
      rw [if_pos hle]
      have hsub : β - Finsupp.single p k = α + Finsupp.single p (d - k) := by
        ext q
        by_cases hq : q = p
        · subst hq; simp [β]; omega
        · have hpq : p ≠ q := Ne.symm hq
          simp [β, hpq]
      rw [hsub]
      have hnot : α + Finsupp.single p (d - k) ∉ G.support := by
        intro hmem
        have hle' := le_sup (f := weight) hmem
        rw [htop, weight_add, weight_single] at hle'
        have hpow : 2 ≤ ((p : Nat.Primes) : ℕ) ^ (d - k) :=
          le_trans hp2 (Nat.le_self_pow (by omega) _)
        have := weight_pos α
        nlinarith
      rw [MvPolynomial.notMem_support_iff.mp hnot, mul_zero]
    · intro hd; exact absurd (mem_range.mpr (Nat.lt_succ_self d)) hd
  have hβ : β ∈ (circlePoly h p * G).support := by
    rw [MvPolynomial.mem_support_iff, hcoeff]
    exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hh) (MvPolynomial.mem_support_iff.mp hα)
  have hle := le_sup (f := weight) hβ
  rw [hβdef, weight_add, weight_single] at hle
  rw [length, length, htop]
  linarith [mul_comm (weight α) (((p : Nat.Primes) : ℕ) ^ d)]

theorem one_le_length {G : MvPolynomial P ℤ} (hG : G ≠ 0) : 1 ≤ length G := by
  obtain ⟨α, hα⟩ := MvPolynomial.support_nonempty.mpr hG
  exact (weight_pos α).trans_le (le_sup (f := weight) hα)

theorem ne_zero_of_length_ne_zero {F : MvPolynomial P ℤ} (h : length F ≠ 0) : F ≠ 0 := by
  rintro rfl
  exact h (by simp [length])

/-- **Sharpness.** A circle factor `h(u_p)` has length exactly `p^{deg h}`. -/
theorem length_circlePoly {h : Polynomial ℤ} (hh : h ≠ 0) (p : P) :
    length (circlePoly h p) = ((p : Nat.Primes) : ℕ) ^ h.natDegree := by
  classical
  apply le_antisymm
  · refine Finset.sup_le fun α hα => ?_
    rw [circlePoly_eq_sum] at hα
    obtain ⟨k, hk, hαk⟩ := mem_biUnion.mp (MvPolynomial.support_sum hα)
    have hαs : α = Finsupp.single p k := by
      have := MvPolynomial.support_monomial_subset hαk
      simpa using this
    rw [hαs, weight_single]
    exact Nat.pow_le_pow_right (p : Nat.Primes).2.pos (Nat.lt_succ_iff.mp (mem_range.mp hk))
  · have h1 := pow_natDegree_mul_length_le hh p (G := 1) one_ne_zero
    have hl1 : length (1 : MvPolynomial P ℤ) = 1 := by
      rw [length, MvPolynomial.support_one, sup_singleton]
      simp [weight]
    rw [hl1, mul_one, mul_one] at h1
    exact h1

/-- A finite family of circle factors: `(p, h)` stands for `h(u_p)`. -/
def circleProduct (L : List (P × Polynomial ℤ)) : MvPolynomial P ℤ :=
  (L.map fun x => circlePoly x.2 x.1).prod

/-- **The degree gain of a family of circle factors.** -/
theorem prod_pow_mul_length_le (L : List (P × Polynomial ℤ)) (hL : ∀ x ∈ L, x.2 ≠ 0)
    {G : MvPolynomial P ℤ} (hG : G ≠ 0) :
    (L.map fun x => ((x.1 : Nat.Primes) : ℕ) ^ x.2.natDegree).prod * length G ≤
      length (circleProduct L * G) := by
  induction L with
  | nil => simp [circleProduct]
  | cons x L ih =>
    have hx : x.2 ≠ 0 := hL x (List.mem_cons_self ..)
    have ih' := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    have hprod : 1 ≤ (L.map fun x => ((x.1 : Nat.Primes) : ℕ) ^ x.2.natDegree).prod := by
      refine Nat.one_le_iff_ne_zero.mpr (List.prod_ne_zero ?_)
      simp only [List.mem_map, not_exists, not_and]
      intro y _ hy
      exact (pow_pos (y.1 : Nat.Primes).2.pos _).ne' hy
    have hne : circleProduct L * G ≠ 0 := by
      refine ne_zero_of_length_ne_zero ?_
      have := one_le_length hG
      nlinarith
    have hstep := pow_natDegree_mul_length_le hx x.1 hne
    have hrw : circleProduct (x :: L) * G = circlePoly x.2 x.1 * (circleProduct L * G) := by
      simp [circleProduct, mul_assoc]
    rw [hrw, List.map_cons, List.prod_cons, mul_assoc]
    exact (Nat.mul_le_mul_left _ ih').trans hstep

/-- **The Stepanov count of the closed points.** If `Π Φ_m(u_p)^J` over a family `(p, m, J)`
divides a nonzero integer auxiliary `F`, then `Π p^{φ(m) J} ≤ N(F)`, i.e.
`Σ φ(m) J log p ≤ log N(F)`. -/
theorem stepanov_count_closedPoints (D : List (P × ℕ × ℕ)) {F : MvPolynomial P ℤ} (hF : F ≠ 0)
    (hdvd : circleProduct (D.map fun x => (x.1, Polynomial.cyclotomic x.2.1 ℤ ^ x.2.2)) ∣ F) :
    (D.map fun x => ((x.1 : Nat.Primes) : ℕ) ^ (x.2.1.totient * x.2.2)).prod ≤ length F := by
  obtain ⟨G, rfl⟩ := hdvd
  have hG : G ≠ 0 := right_ne_zero_of_mul hF
  have hL : ∀ x ∈ D.map (fun x => (x.1, Polynomial.cyclotomic x.2.1 ℤ ^ x.2.2)), x.2 ≠ 0 := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact pow_ne_zero _ (Polynomial.cyclotomic_ne_zero _ _)
  have h := prod_pow_mul_length_le _ hL hG
  rw [List.map_map] at h
  have hdeg : (fun x : P × ℕ × ℕ => ((x.1 : Nat.Primes) : ℕ) ^ (x.2.1.totient * x.2.2)) =
      (fun x => ((x.1 : Nat.Primes) : ℕ) ^ x.2.natDegree) ∘
        (fun x : P × ℕ × ℕ => (x.1, Polynomial.cyclotomic x.2.1 ℤ ^ x.2.2)) := by
    funext x
    simp only [Function.comp_apply, Polynomial.natDegree_pow, Polynomial.natDegree_cyclotomic,
      mul_comm]
  rw [hdeg]
  exact le_trans (Nat.le_mul_of_pos_right _ (one_le_length hG)) h

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
