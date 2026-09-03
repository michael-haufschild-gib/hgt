import GaloisForLFunctions.HTGeometry.FirstOrderCoefficientDecomposition
import GaloisForLFunctions.HTGeometry.GoldbergCentralIndex

open Finset Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ}

/-- Shift one value/derivative exponent by one actual derivative factor. -/
def firstOrderDerivativeShift (p : ℕ × ℕ) : ℕ × ℕ := (p.1, p.2 + 1)

/-- Exact coefficient-level certificate that a row is obtained from `P` by deleting zero collected
rows, multiplying by the actual derivative, and multiplying every coefficient by `X^d`. -/
def IsPositiveDerivativeCoefficientShift
    (P : MvPolynomial (Fin 3) ℂ) (S : Finset (ℕ × ℕ))
    (A : ℕ × ℕ → Polynomial ℂ) (d : ℕ) : Prop :=
  ∃ (S₀ : Finset (ℕ × ℕ)) (A₀ : ℕ × ℕ → Polynomial ℂ),
    firstOrderMvPoly S₀ A₀ = P ∧
    (∀ p ∈ S₀, A₀ p ≠ 0) ∧
    S = S₀.image firstOrderDerivativeShift ∧
    ∀ p ∈ S₀, A (firstOrderDerivativeShift p) = Polynomial.X ^ d * A₀ p

/-- An arbitrary order-one ADE can be replaced by a nonzero relation whose selected top-total-degree
monomial has positive derivative degree and maximal derivative degree on that face. Multiplication
by the actual derivative is what makes positivity unconditional. -/
theorem exists_firstOrderPositiveDerivativeTopRelation_of_relation
    (P : MvPolynomial (Fin 3) ℂ) (hP : P ≠ 0)
    (hPrel : ∀ z : ℂ, MvPolynomial.eval
      (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) (coeffFun a) z) P = 0) :
    ∃ (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d m : ℕ),
      (∀ p ∈ S, p.1 + p.2 ≤ d) ∧
      (∀ z : ℂ,
        ∑ p ∈ S, (A p).eval z * (coeffFun a z) ^ p.1 *
          (deriv (coeffFun a) z) ^ p.2 = 0) ∧
      1 ≤ m ∧ m ≤ d ∧ (d - m, m) ∈ S ∧
      (∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ m) ∧
      A (d - m, m) ≠ 0 ∧ d ≤ (A (d - m, m)).natDegree ∧
      firstOrderMvPoly S A =
        MvPolynomial.X 0 ^ d * MvPolynomial.X 2 * P ∧
      IsPositiveDerivativeCoefficientShift P S A d := by
  classical
  let S : Finset (ℕ × ℕ) := firstOrderSupport P
  let A : ℕ × ℕ → Polynomial ℂ := firstOrderCoeff P
  have hne : ∃ p ∈ S, A p ≠ 0 := by
    simpa [S, A] using exists_nonzero_firstOrderCoeff hP
  have hrel : ∀ z : ℂ,
      ∑ p ∈ S, (A p).eval z * (coeffFun a z) ^ p.1 *
        (deriv (coeffFun a) z) ^ p.2 = 0 := by
    intro z
    change ∑ p ∈ firstOrderSupport P, (firstOrderCoeff P p).eval z *
      (coeffFun a z) ^ p.1 * (deriv (coeffFun a) z) ^ p.2 = 0
    rw [eval_firstOrderSupport]
    have hvec : (Fin.cons z fun j : Fin 2 =>
        iteratedDeriv (j : ℕ) (coeffFun a) z) =
        (![z, coeffFun a z, deriv (coeffFun a) z] : Fin 3 → ℂ) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rw [Fin.cons_succ]
        fin_cases j <;> simp [iteratedDeriv_zero, iteratedDeriv_one]
    rw [← hvec]
    exact hPrel z
  set S₀ : Finset (ℕ × ℕ) := S.filter (fun p => A p ≠ 0) with hS₀
  have hS₀ne : S₀.Nonempty := by
    obtain ⟨p, hpS, hpA⟩ := hne
    exact ⟨p, Finset.mem_filter.mpr ⟨hpS, hpA⟩⟩
  have hS₀sub : S₀ ⊆ S := by
    rw [hS₀]
    exact Finset.filter_subset _ _
  have hA₀ : ∀ p ∈ S₀, A p ≠ 0 := by
    intro p hp
    rw [hS₀, Finset.mem_filter] at hp
    exact hp.2
  have hrel₀ : ∀ z : ℂ,
      ∑ p ∈ S₀, (A p).eval z * (coeffFun a z) ^ p.1 *
        (deriv (coeffFun a) z) ^ p.2 = 0 := by
    intro z
    rw [Finset.sum_subset hS₀sub]
    · exact hrel z
    · intro p hpS hpnot
      have hAp : A p = 0 := by
        by_contra hpA
        exact hpnot (by rw [hS₀, Finset.mem_filter]; exact ⟨hpS, hpA⟩)
      rw [hAp]
      simp
  obtain ⟨q, hqS₀, hqmax⟩ :=
    Finset.exists_max_image S₀ (fun p => p.1 + p.2) hS₀ne
  set d₀ : ℕ := q.1 + q.2 with hd₀
  have hdeg₀ : ∀ p ∈ S₀, p.1 + p.2 ≤ d₀ := by
    intro p hp
    rw [hd₀]
    exact hqmax p hp
  let sh : ℕ × ℕ → ℕ × ℕ := firstOrderDerivativeShift
  have hshinj : Function.Injective sh := by
    rintro ⟨p₁, p₂⟩ ⟨q₁, q₂⟩ hpq
    simp only [sh, firstOrderDerivativeShift, Prod.mk.injEq] at hpq ⊢
    omega
  set S₁ : Finset (ℕ × ℕ) := S₀.image sh with hS₁
  let A₁ : ℕ × ℕ → Polynomial ℂ := fun p => A (p.1, p.2 - 1)
  have hmem₁ : ∀ p, p ∈ S₁ ↔ ∃ q ∈ S₀, sh q = p := by
    intro p
    rw [hS₁, Finset.mem_image]
  have hA₁sh : ∀ p, A₁ (sh p) = A p := by
    intro p
    simp [A₁, sh, firstOrderDerivativeShift]
  have hdeg₁ : ∀ p ∈ S₁, p.1 + p.2 ≤ d₀ + 1 := by
    intro p hp
    obtain ⟨q', hq'S₀, rfl⟩ := (hmem₁ p).mp hp
    have hq'deg := hdeg₀ q' hq'S₀
    dsimp [sh, firstOrderDerivativeShift]
    omega
  have hrel₁ : ∀ z : ℂ,
      ∑ p ∈ S₁, (A₁ p).eval z * (coeffFun a z) ^ p.1 *
        (deriv (coeffFun a) z) ^ p.2 = 0 := by
    intro z
    rw [hS₁, Finset.sum_image]
    · simp_rw [hA₁sh]
      calc
        ∑ p ∈ S₀, (A p).eval z * (coeffFun a z) ^ p.1 *
              deriv (coeffFun a) z ^ (p.2 + 1) =
            (∑ p ∈ S₀, (A p).eval z * (coeffFun a z) ^ p.1 *
              deriv (coeffFun a) z ^ p.2) * deriv (coeffFun a) z := by
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro p _
                rw [pow_succ]
                ring
        _ = 0 := by rw [hrel₀ z, zero_mul]
    · exact fun x _ y _ hxy => hshinj hxy
  set Stop : Finset (ℕ × ℕ) := S₁.filter (fun p => p.1 + p.2 = d₀ + 1) with hStop
  have hqStop : sh q ∈ Stop := by
    rw [hStop, Finset.mem_filter, hS₁, Finset.mem_image]
    refine ⟨⟨q, hqS₀, rfl⟩, ?_⟩
    dsimp [sh, firstOrderDerivativeShift]
    omega
  have hStopne : Stop.Nonempty := ⟨sh q, hqStop⟩
  obtain ⟨t, htStop, htmax⟩ := Finset.exists_max_image Stop Prod.snd hStopne
  set m : ℕ := t.2 with hm
  have htStop' := htStop
  rw [hStop, Finset.mem_filter] at htStop'
  have htS₁ : t ∈ S₁ := htStop'.1
  have htd : t.1 + t.2 = d₀ + 1 := htStop'.2
  obtain ⟨u, huS₀, hu⟩ := (hmem₁ t).mp htS₁
  have hmpos : 1 ≤ m := by
    rw [hm, ← hu]
    dsimp [sh, firstOrderDerivativeShift]
    omega
  have hmle : m ≤ d₀ + 1 := by omega
  have htcoord : t = (d₀ + 1 - m, m) := by
    apply Prod.ext
    · dsimp
      rw [hm]
      omega
    · exact hm.symm
  have htargetMem : (d₀ + 1 - m, m) ∈ S₁ := by
    rw [← htcoord]
    exact htS₁
  have htopdeg : ∀ p ∈ S₁, p.1 + p.2 = d₀ + 1 → p.2 ≤ m := by
    intro p hpS₁ hpd
    have hpStop : p ∈ Stop := by
      rw [hStop, Finset.mem_filter]
      exact ⟨hpS₁, hpd⟩
    rw [hm]
    exact htmax p hpStop
  have hAne : A₁ (d₀ + 1 - m, m) ≠ 0 := by
    rw [← htcoord, ← hu, hA₁sh]
    exact hA₀ u huS₀
  let B : ℕ × ℕ → Polynomial ℂ :=
    fun p => Polynomial.X ^ (d₀ + 1) * A₁ p
  have hrelB : ∀ z : ℂ,
      ∑ p ∈ S₁, (B p).eval z * (coeffFun a z) ^ p.1 *
        (deriv (coeffFun a) z) ^ p.2 = 0 := by
    intro z
    simp_rw [B, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    calc
      ∑ p ∈ S₁, (z ^ (d₀ + 1) * (A₁ p).eval z) * (coeffFun a z) ^ p.1 *
          deriv (coeffFun a) z ^ p.2 =
          z ^ (d₀ + 1) * ∑ p ∈ S₁, (A₁ p).eval z * (coeffFun a z) ^ p.1 *
            deriv (coeffFun a) z ^ p.2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _
              ring
      _ = 0 := by rw [hrel₁ z, mul_zero]
  have hBne : B (d₀ + 1 - m, m) ≠ 0 := by
    exact mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hAne
  have hBdeg : d₀ + 1 ≤ (B (d₀ + 1 - m, m)).natDegree := by
    change d₀ + 1 ≤
      (Polynomial.X ^ (d₀ + 1) * A₁ (d₀ + 1 - m, m)).natDegree
    rw [Polynomial.natDegree_mul (pow_ne_zero _ Polynomial.X_ne_zero) hAne,
      Polynomial.natDegree_X_pow]
    omega
  have hpoly₀ : firstOrderMvPoly S₀ A = P := by
    calc
      firstOrderMvPoly S₀ A = firstOrderMvPoly S A := by
        rw [firstOrderMvPoly, firstOrderMvPoly, Finset.sum_subset hS₀sub]
        intro p hpS hpnot
        have hAp : A p = 0 := by
          by_contra hpA
          exact hpnot (by rw [hS₀, Finset.mem_filter]; exact ⟨hpS, hpA⟩)
        rw [hAp]
        simp
      _ = P := by simpa [S, A] using firstOrderMvPoly_support_coeff_eq P
  have hpoly₁ : firstOrderMvPoly S₁ A₁ =
      MvPolynomial.X 2 * firstOrderMvPoly S₀ A := by
    apply MvPolynomial.funext
    intro x
    have hx : (![x 0, x 1, x 2] : Fin 3 → ℂ) = x := by
      funext i
      fin_cases i <;> rfl
    rw [← hx, eval_firstOrderMvPoly, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      eval_firstOrderMvPoly, hS₁, Finset.sum_image]
    · simp_rw [hA₁sh]
      change (∑ p ∈ S₀, (A p).eval (x 0) * x 1 ^ (sh p).1 * x 2 ^ (sh p).2) =
        x 2 * ∑ p ∈ S₀, (A p).eval (x 0) * x 1 ^ p.1 * x 2 ^ p.2
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      dsimp [sh, firstOrderDerivativeShift]
      ring
    · exact fun x _ y _ hxy => hshinj hxy
  have hpolyB₁ : firstOrderMvPoly S₁ B =
      MvPolynomial.X 0 ^ (d₀ + 1) * firstOrderMvPoly S₁ A₁ := by
    apply MvPolynomial.funext
    intro x
    have hx : (![x 0, x 1, x 2] : Fin 3 → ℂ) = x := by
      funext i
      fin_cases i <;> rfl
    rw [← hx, eval_firstOrderMvPoly, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_X, eval_firstOrderMvPoly]
    simp_rw [B, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    change (∑ p ∈ S₁, (x 0 ^ (d₀ + 1) * (A₁ p).eval (x 0)) *
        x 1 ^ p.1 * x 2 ^ p.2) =
      x 0 ^ (d₀ + 1) * ∑ p ∈ S₁, (A₁ p).eval (x 0) * x 1 ^ p.1 * x 2 ^ p.2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  have hpolyB : firstOrderMvPoly S₁ B =
      MvPolynomial.X 0 ^ (d₀ + 1) * MvPolynomial.X 2 * P := by
    rw [hpolyB₁, hpoly₁, hpoly₀]
    ring
  have hshift : IsPositiveDerivativeCoefficientShift P S₁ B (d₀ + 1) := by
    refine ⟨S₀, A, hpoly₀, hA₀, ?_, ?_⟩
    · simpa [sh] using hS₁
    · intro p hp
      simp [B, A₁, firstOrderDerivativeShift]
  exact ⟨S₁, B, d₀ + 1, m, hdeg₁, hrelB, hmpos, hmle,
    htargetMem, htopdeg, hBne, hBdeg, hpolyB, hshift⟩

/-- Existential wrapper around
`exists_firstOrderPositiveDerivativeTopRelation_of_relation`. -/
theorem exists_firstOrderPositiveDerivativeTopRelation
    (hDA : GaloisForLFunctions.DifferentiallyAlgebraicOfOrder (coeffFun a) 1) :
    ∃ (S : Finset (ℕ × ℕ)) (A : ℕ × ℕ → Polynomial ℂ) (d m : ℕ),
      (∀ p ∈ S, p.1 + p.2 ≤ d) ∧
      (∀ z : ℂ,
        ∑ p ∈ S, (A p).eval z * (coeffFun a z) ^ p.1 *
          (deriv (coeffFun a) z) ^ p.2 = 0) ∧
      1 ≤ m ∧ m ≤ d ∧ (d - m, m) ∈ S ∧
      (∀ p ∈ S, p.1 + p.2 = d → p.2 ≤ m) ∧
      A (d - m, m) ≠ 0 ∧ d ≤ (A (d - m, m)).natDegree ∧
      ∃ P : MvPolynomial (Fin 3) ℂ, P ≠ 0 ∧
        (∀ z : ℂ, MvPolynomial.eval
          (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) (coeffFun a) z) P = 0) ∧
        firstOrderMvPoly S A =
          MvPolynomial.X 0 ^ d * MvPolynomial.X 2 * P ∧
        IsPositiveDerivativeCoefficientShift P S A d := by
  obtain ⟨P, hP, hPrel⟩ := hDA
  obtain ⟨S, A, d, m, hdeg, hrel, hmpos, hmle, hmem, htop, hAne, hAdeg,
    hpoly, hshift⟩ :=
    exists_firstOrderPositiveDerivativeTopRelation_of_relation P hP hPrel
  exact ⟨S, A, d, m, hdeg, hrel, hmpos, hmle, hmem, htop, hAne, hAdeg,
    P, hP, hPrel, hpoly, hshift⟩

/-- Every transcendental entire solution of an arbitrary order-one ADE has eventually polynomially
bounded central index. -/
theorem exists_centralIndex_le_pow_of_order_one
    (ha : EntireCoeffs a) {n₀ : ℕ} (hn₀ : a n₀ ≠ 0)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : GaloisForLFunctions.DifferentiallyAlgebraicOfOrder (coeffFun a) 1) :
    ∃ (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ᶠ t : ℝ in atTop, ((centralIndex a t : ℕ) : ℝ) ≤ C * t ^ K := by
  obtain ⟨S, A, d, m, hdeg, hrel, hmpos, hmle, htargetMem, htopdeg, hAne,
    -, -, -⟩ :=
    exists_firstOrderPositiveDerivativeTopRelation hDA
  exact exists_centralIndex_le_pow_of_relation ha hn₀ htrans hdeg hrel
    hmpos hmle htargetMem htopdeg hAne

end

end GaloisForLFunctions.HTGeometry
