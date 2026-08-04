import GaloisForLFunctions.HTGeometry.TwoBlockEquivDerivation

/-!
# Pseudo-division over a commutative ring

Dividing by a polynomial whose leading coefficient is not invertible still works after multiplying
the dividend by a power of that leading coefficient.  mathlib has division by a monic polynomial and
division over a field; this is the pseudo-division that works over an arbitrary commutative ring, in
the univariate case and at a distinguished variable of a multivariable ring.

The point of proving it over a ring rather than a field is that the multiplier is then explicitly a
power of the initial: no denominators are introduced, so a certificate obtained this way stays inside
the polynomial ring and its multiplier is controlled.
-/

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

/-- **Univariate pseudo-division over a commutative ring.** -/
theorem exists_pseudoDivision {R : Type*} [CommRing R] {q : Polynomial R}
    (hq : 0 < q.natDegree) (p : Polynomial R) :
    ∃ (e : ℕ) (a b : Polynomial R),
      Polynomial.C q.leadingCoeff ^ e * p = q * a + b ∧ b.natDegree < q.natDegree := by
  classical
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | _ n ih =>
    by_cases hlt : p.natDegree < q.natDegree
    · exact ⟨0, 0, p, by simp, hlt⟩
    · push Not at hlt
      set d := p.natDegree with hd
      set m := q.natDegree with hm
      set p' : Polynomial R := Polynomial.C q.leadingCoeff * p -
        Polynomial.C p.leadingCoeff * (q * Polynomial.X ^ (d - m)) with hp'
      have hcoeff : ∀ k : ℕ, d ≤ k → p'.coeff k = 0 := by
        intro k hk
        rw [hp']
        simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul,
          Polynomial.coeff_mul_X_pow']
        rw [if_pos (by omega)]
        rcases lt_or_eq_of_le hk with hlt' | heq
        · have h1 : p.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          have h2 : q.coeff (k - (d - m)) = 0 :=
            Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          rw [h1, h2]
          ring
        · rw [← heq]
          have h2 : d - (d - m) = m := by omega
          rw [h2]
          simp only [Polynomial.leadingCoeff, ← hd, ← hm]
          ring
      have hdlt : p'.natDegree < d := by
        by_contra hcon
        push Not at hcon
        have hne : p'.coeff p'.natDegree ≠ 0 := by
          intro h0
          have hp'0 : p' = 0 := Polynomial.leadingCoeff_eq_zero.1 h0
          rw [hp'0] at hcon
          simp only [Polynomial.natDegree_zero] at hcon
          omega
        exact hne (hcoeff _ hcon)
      obtain ⟨e, a, b, hab, hb⟩ := ih p'.natDegree (by omega) p' rfl
      refine ⟨e + 1, a + Polynomial.C q.leadingCoeff ^ e *
        (Polynomial.C p.leadingCoeff * Polynomial.X ^ (d - m)), b, ?_, hb⟩
      have hstep : Polynomial.C q.leadingCoeff ^ (e + 1) * p =
          Polynomial.C q.leadingCoeff ^ e * p' +
            Polynomial.C q.leadingCoeff ^ e *
              (Polynomial.C p.leadingCoeff * (q * Polynomial.X ^ (d - m))) := by
        rw [hp']
        ring
      rw [hstep, hab]
      ring

/-- **Pseudo-division at a distinguished variable, over a commutative ring.**  The multiplier is a
power of the initial at that variable, so the identity stays inside the polynomial ring. -/
theorem exists_mvPolynomial_pseudoDivision {R σ : Type*} [CommRing R] (i : σ)
    (Q D : MvPolynomial σ R) (hD : 0 < MvPolynomial.degreeOf i D) :
    ∃ (e : ℕ) (a b : MvPolynomial σ R),
      mvPolynomialInitialAt i D ^ e * Q = D * a + b ∧
        MvPolynomial.degreeOf i b < MvPolynomial.degreeOf i D := by
  classical
  set eq := mvPolynomialPolynomialEquivAt (K := R) i with heq
  have hDdeg : 0 < (eq D).natDegree := by
    rw [heq, mvPolynomialPolynomialEquivAt_apply,
      ← mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt]
    exact hD
  obtain ⟨e, a, b, hab, hb⟩ := exists_pseudoDivision hDdeg (eq Q)
  refine ⟨e, eq.symm a, eq.symm b, ?_, ?_⟩
  · apply eq.injective
    rw [map_mul, map_add, map_mul, map_pow, AlgEquiv.apply_symm_apply,
      AlgEquiv.apply_symm_apply]
    rw [heq, mvPolynomialPolynomialEquivAt_initial]
    exact hab
  · have hbdeg : MvPolynomial.degreeOf i (eq.symm b) = b.natDegree := by
      rw [mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt,
        ← mvPolynomialPolynomialEquivAt_apply, heq, AlgEquiv.apply_symm_apply]
    have hDdeg' : MvPolynomial.degreeOf i D = (eq D).natDegree := by
      rw [heq, mvPolynomialPolynomialEquivAt_apply,
        mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt]
    rw [hbdeg, hDdeg']
    exact hb

open scoped Differential

/-- **The fresh-jet commutator, for an arbitrary index type.**  Differentiating in the jet `(i, n+1)`
after the total derivation equals total differentiation after that partial derivative, plus the
partial derivative in the jet `(i, n)`.  This is the corpus's scalar commutator, proved for a general
family of differential indeterminates so that it applies to a doubled jet ring. -/
theorem pderiv_succ_differentialPolynomialOverDerivation_family
    {ι K : Type*} [CommRing K] [Differential K] [DecidableEq ι] (i : ι) (n : ℕ)
    (P : DifferentialPolynomial ι K) :
    MvPolynomial.pderiv (i, n + 1) (differentialPolynomialOverDerivation ι K P) =
      differentialPolynomialOverDerivation ι K (MvPolynomial.pderiv (i, n + 1) P) +
        MvPolynomial.pderiv (i, n) P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
      simp only [map_add, hP, hQ]
      abel
  | mul_X P j hP =>
      rcases j with ⟨a, m⟩
      simp only [Derivation.leibniz, smul_eq_mul,
        differentialPolynomialOverDerivation_X]
      by_cases hai : a = i
      · subst hai
        by_cases hmn : m = n
        · subst hmn
          simp [MvPolynomial.pderiv_X]
          rw [hP]
          ring
        · by_cases hmtop : m = n + 1
          · subst hmtop
            have hne : n + 1 ≠ n := Nat.ne_of_gt (Nat.lt_succ_self n)
            simp [MvPolynomial.pderiv_X, Nat.add_comm]
            rw [hP]
            ring
          · have hne1 : ((a, m + 1) : ι × ℕ) ≠ (a, n + 1) := by
              simp only [ne_eq, Prod.mk.injEq, true_and]
              omega
            have hne2 : ((a, m) : ι × ℕ) ≠ (a, n + 1) := by
              simp only [ne_eq, Prod.mk.injEq, true_and]
              omega
            have hne3 : ((a, m) : ι × ℕ) ≠ (a, n) := by
              simp only [ne_eq, Prod.mk.injEq, true_and]
              omega
            simp [MvPolynomial.pderiv_X, hne1, hne2, hne3]
            rw [hP]
            ring
      · have hne1 : ((a, m + 1) : ι × ℕ) ≠ (i, n + 1) := by
          simp only [ne_eq, Prod.mk.injEq, not_and]
          intro h
          exact absurd h hai
        have hne2 : ((a, m) : ι × ℕ) ≠ (i, n + 1) := by
          simp only [ne_eq, Prod.mk.injEq, not_and]
          intro h
          exact absurd h hai
        have hne3 : ((a, m) : ι × ℕ) ≠ (i, n) := by
          simp only [ne_eq, Prod.mk.injEq, not_and]
          intro h
          exact absurd h hai
        simp [MvPolynomial.pderiv_X, hne1, hne2, hne3]
        rw [hP]
        ring

/-- Above its order in one block, a polynomial's partial derivatives vanish, and total
differentiation raises that bound by exactly one. -/
theorem pderiv_iterate_eq_zero_of_lt {ι K : Type*} [CommRing K] [Differential K] [DecidableEq ι]
    {i : ι} {m : ℕ} {A : DifferentialPolynomial ι K}
    (hA : ∀ j : ℕ, m < j → MvPolynomial.pderiv (i, j) A = 0) :
    ∀ (s j : ℕ), m + s < j →
      MvPolynomial.pderiv (i, j) (diffPolyIterate s A) = 0 := by
  intro s
  induction s with
  | zero =>
      intro j hj
      exact hA j (by omega)
  | succ s ih =>
      intro j hj
      obtain ⟨l, rfl⟩ : ∃ l, j = l + 1 := ⟨j - 1, by omega⟩
      rw [diffPolyIterate_succ, pderiv_succ_differentialPolynomialOverDerivation_family,
        ih (l + 1) (by omega), ih l (by omega), map_zero, add_zero]

/-- **Every derivative has the same separant.**  The partial derivative of the `k`-th total
derivative in its own fresh jet is the separant of the original polynomial. -/
theorem pderiv_top_iterate_eq_separant {ι K : Type*} [CommRing K] [Differential K] [DecidableEq ι]
    {i : ι} {m : ℕ} {A : DifferentialPolynomial ι K}
    (hA : ∀ j : ℕ, m < j → MvPolynomial.pderiv (i, j) A = 0) (k : ℕ) :
    MvPolynomial.pderiv (i, m + k) (diffPolyIterate k A) = MvPolynomial.pderiv (i, m) A := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hzero := pderiv_iterate_eq_zero_of_lt hA k (m + k + 1) (by omega)
      rw [show m + (k + 1) = (m + k) + 1 from by omega, diffPolyIterate_succ,
        pderiv_succ_differentialPolynomialOverDerivation_family, hzero, map_zero, zero_add, ih]

/-- The corpus's coefficient identity for `X * pderiv`, over an arbitrary commutative semiring. -/
theorem coeff_X_mul_pderiv_semiring {σ C : Type*} [CommSemiring C] (j : σ)
    (P : MvPolynomial σ C) (s : σ →₀ ℕ) :
    MvPolynomial.coeff s (MvPolynomial.X j * MvPolynomial.pderiv j P) =
      (s j : C) * MvPolynomial.coeff s P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [map_add, mul_add, hP, hQ]
  | monomial m c =>
      rw [MvPolynomial.X_mul_pderiv_monomial]
      rw [MvPolynomial.coeff_smul, nsmul_eq_mul]
      simp [MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst m
        ring
      · simp

/-- Over a domain of characteristic zero, a variable occurring in a polynomial has a nonzero partial
derivative. -/
theorem pderiv_ne_zero_of_mem_vars_domain {σ C : Type*} [CommRing C] [IsDomain C] [CharZero C]
    {P : MvPolynomial σ C} {i : σ} (hi : i ∈ P.vars) :
    MvPolynomial.pderiv i P ≠ 0 := by
  classical
  obtain ⟨s, hs, his⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  intro hzero
  have hcoeff := coeff_X_mul_pderiv_semiring i P s
  rw [hzero, mul_zero, MvPolynomial.coeff_zero] at hcoeff
  have hsj : (s i : C) ≠ 0 := by
    exact_mod_cast Finsupp.mem_support_iff.mp his
  exact mul_ne_zero hsj (MvPolynomial.mem_support_iff.mp hs) hcoeff.symm

/-- Over a domain of characteristic zero, a vanishing partial derivative means the variable is
absent. -/
theorem degreeOf_eq_zero_of_pderiv_eq_zero {σ C : Type*} [CommRing C] [IsDomain C] [CharZero C]
    {P : MvPolynomial σ C} {i : σ} (h : MvPolynomial.pderiv i P = 0) :
    MvPolynomial.degreeOf i P = 0 := by
  by_contra hne
  exact pderiv_ne_zero_of_mem_vars_domain
    (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.2 hne) h

/-- **The iterated derivative is linear in its fresh jet, with the separant as coefficient.** -/
theorem iterate_eq_separant_mul_add {ι K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    [Differential K] [DecidableEq ι] {i : ι} {m : ℕ} {A : DifferentialPolynomial ι K}
    (hA : ∀ j : ℕ, m < j → ((i, j) : ι × ℕ) ∉ A.vars) (k : ℕ) (hk : 0 < k) :
    ∃ T : DifferentialPolynomial ι K,
      MvPolynomial.degreeOf ((i, m + k) : ι × ℕ) T = 0 ∧
        diffPolyIterate k A =
          MvPolynomial.pderiv ((i, m) : ι × ℕ) A * MvPolynomial.X ((i, m + k) : ι × ℕ) + T := by
  classical
  have hApd : ∀ j : ℕ, m < j → MvPolynomial.pderiv ((i, j) : ι × ℕ) A = 0 := fun j hj =>
    MvPolynomial.pderiv_eq_zero_of_notMem_vars (hA j hj)
  set S : DifferentialPolynomial ι K := MvPolynomial.pderiv ((i, m) : ι × ℕ) A with hS
  set v : ι × ℕ := (i, m + k) with hv
  have hSv : MvPolynomial.pderiv v S = 0 := by
    refine MvPolynomial.pderiv_eq_zero_of_notMem_vars ?_
    intro hmem
    exact hA (m + k) (by omega) (mvPolynomial_vars_pderiv_subset ((i, m) : ι × ℕ) A hmem)
  refine ⟨diffPolyIterate k A - S * MvPolynomial.X v, ?_, by ring⟩
  refine degreeOf_eq_zero_of_pderiv_eq_zero ?_
  rw [map_sub, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hSv, MvPolynomial.pderiv_X_self,
    mul_zero, add_zero, mul_one]
  have htop : MvPolynomial.pderiv v (diffPolyIterate k A) = S := by
    rw [hv, hS]
    exact pderiv_top_iterate_eq_separant hApd k
  rw [htop, sub_self]

/-- For a polynomial of degree one in a variable, the initial at that variable is the partial
derivative. -/
theorem initialAt_eq_pderiv_of_degreeOf_eq_one {σ K : Type*} [CommRing K]
    {P : MvPolynomial σ K} {v : σ} (h : MvPolynomial.degreeOf v P = 1) :
    mvPolynomialInitialAt v P = MvPolynomial.pderiv v P := by
  classical
  have hnat : (mvPolynomialAsPolynomialAt v P).natDegree = 1 := by
    rw [← mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt]
    exact h
  have h1 : mvPolynomialPolynomialEquivAt v (MvPolynomial.pderiv v P) =
      Polynomial.C ((mvPolynomialAsPolynomialAt v P).leadingCoeff) := by
    rw [mvPolynomialPolynomialEquivAt_apply, mvPolynomialAsPolynomialAt_pderiv,
      Polynomial.derivative_eq_C_leadingCoeff_of_natDegree_eq_one hnat]
  have h2 : mvPolynomialPolynomialEquivAt v (mvPolynomialInitialAt v P) =
      Polynomial.C ((mvPolynomialAsPolynomialAt v P).leadingCoeff) :=
    mvPolynomialPolynomialEquivAt_initial v P
  exact (mvPolynomialPolynomialEquivAt v).injective (h2.trans h1.symm)

/-- **The iterated derivative has degree one in its fresh jet.** -/
theorem degreeOf_iterate_eq_one {ι K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    [Differential K] [DecidableEq ι] {i : ι} {m : ℕ} {A : DifferentialPolynomial ι K}
    (hA : ∀ j : ℕ, m < j → ((i, j) : ι × ℕ) ∉ A.vars)
    (hS : MvPolynomial.pderiv ((i, m) : ι × ℕ) A ≠ 0) (k : ℕ) (hk : 0 < k) :
    MvPolynomial.degreeOf ((i, m + k) : ι × ℕ) (diffPolyIterate k A) = 1 := by
  classical
  obtain ⟨T, hT, hdec⟩ := iterate_eq_separant_mul_add hA k hk
  set v : ι × ℕ := (i, m + k) with hv
  have hSv : MvPolynomial.degreeOf v (MvPolynomial.pderiv ((i, m) : ι × ℕ) A) = 0 := by
    refine degreeOf_eq_zero_of_pderiv_eq_zero (MvPolynomial.pderiv_eq_zero_of_notMem_vars ?_)
    intro hmem
    exact hA (m + k) (by omega) (mvPolynomial_vars_pderiv_subset ((i, m) : ι × ℕ) A hmem)
  have hle : MvPolynomial.degreeOf v (diffPolyIterate k A) ≤ 1 := by
    rw [hdec]
    refine le_trans (MvPolynomial.degreeOf_add_le _ _ _) ?_
    refine max_le ?_ (by omega)
    rw [MvPolynomial.degreeOf_mul_eq hS (MvPolynomial.X_ne_zero v)]
    have : MvPolynomial.degreeOf v (MvPolynomial.X v : MvPolynomial (ι × ℕ) K) = 1 := by
      simp
    omega
  have hpos : 0 < MvPolynomial.degreeOf v (diffPolyIterate k A) := by
    by_contra hzero
    have hz : MvPolynomial.degreeOf v (diffPolyIterate k A) = 0 := by omega
    have hnot : v ∉ (diffPolyIterate k A).vars := by
      rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
      simp [hz]
    have hpd : MvPolynomial.pderiv v (diffPolyIterate k A) = 0 :=
      MvPolynomial.pderiv_eq_zero_of_notMem_vars hnot
    have hApd : ∀ j : ℕ, m < j → MvPolynomial.pderiv ((i, j) : ι × ℕ) A = 0 := fun j hj =>
      MvPolynomial.pderiv_eq_zero_of_notMem_vars (hA j hj)
    rw [hv, pderiv_top_iterate_eq_separant hApd k] at hpd
    exact hS hpd
  omega

/-- **The higher-jet reduction step.**  A polynomial can be pseudo-divided by the `k`-th total
derivative at the fresh jet, and the multiplier is a power of the SEPARANT of the original
polynomial -- not of the derivative's own initial, which would drift upward in the other block. -/
theorem exists_higherJet_reduction_step {ι K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    [Differential K] [DecidableEq ι] {i : ι} {m : ℕ} {A : DifferentialPolynomial ι K}
    (hA : ∀ j : ℕ, m < j → ((i, j) : ι × ℕ) ∉ A.vars)
    (hS : MvPolynomial.pderiv ((i, m) : ι × ℕ) A ≠ 0) {k : ℕ} (hk : 0 < k)
    (Q : DifferentialPolynomial ι K) :
    ∃ (e : ℕ) (a b : DifferentialPolynomial ι K),
      MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e * Q = diffPolyIterate k A * a + b ∧
        MvPolynomial.degreeOf ((i, m + k) : ι × ℕ) b = 0 := by
  classical
  have hdeg := degreeOf_iterate_eq_one hA hS k hk
  obtain ⟨e, a, b, hab, hb⟩ :=
    exists_mvPolynomial_pseudoDivision ((i, m + k) : ι × ℕ) Q (diffPolyIterate k A)
      (by rw [hdeg]; omega)
  have hApd : ∀ j : ℕ, m < j → MvPolynomial.pderiv ((i, j) : ι × ℕ) A = 0 := fun j hj =>
    MvPolynomial.pderiv_eq_zero_of_notMem_vars (hA j hj)
  have hinit : mvPolynomialInitialAt ((i, m + k) : ι × ℕ) (diffPolyIterate k A) =
      MvPolynomial.pderiv ((i, m) : ι × ℕ) A := by
    rw [initialAt_eq_pderiv_of_degreeOf_eq_one hdeg]
    exact pderiv_top_iterate_eq_separant hApd k
  refine ⟨e, a, b, ?_, by omega⟩
  rw [← hinit]
  exact hab

end

end GaloisForLFunctions
