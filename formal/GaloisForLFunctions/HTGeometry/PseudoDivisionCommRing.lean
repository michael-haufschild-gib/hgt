import GaloisForLFunctions.HTGeometry.DifferentialLurothVariableSupport
import GaloisForLFunctions.HTGeometry.MvPolynomialPDerivDegree
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

/-- **One pseudo-division step lowers the degree, over a commutative ring.**  Multiplying the
dividend by the divisor's leading coefficient makes the leading terms cancel exactly, so no
invertibility and no absence of zero divisors is needed. -/
theorem natDegree_pseudoDivision_step_lt {R : Type*} [CommRing R] {p q : Polynomial R}
    (hq : 0 < q.natDegree) (hpq : q.natDegree ≤ p.natDegree) :
    (Polynomial.C q.leadingCoeff * p -
        q * (Polynomial.C p.leadingCoeff *
          Polynomial.X ^ (p.natDegree - q.natDegree))).natDegree < p.natDegree := by
  classical
  set d := p.natDegree with hd
  set m := q.natDegree with hm
  set p' : Polynomial R := Polynomial.C q.leadingCoeff * p -
    q * (Polynomial.C p.leadingCoeff * Polynomial.X ^ (d - m)) with hp'
  have hp'eq : p' = Polynomial.C q.leadingCoeff * p -
      Polynomial.C p.leadingCoeff * (q * Polynomial.X ^ (d - m)) := by
    rw [hp']
    ring
  have hcoeff : ∀ k : ℕ, d ≤ k → p'.coeff k = 0 := by
    intro k hk
    rw [hp'eq]
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
  by_contra hcon
  push Not at hcon
  have hne : p'.coeff p'.natDegree ≠ 0 := by
    intro h0
    have hp'0 : p' = 0 := Polynomial.leadingCoeff_eq_zero.1 h0
    rw [hp'0] at hcon
    simp only [Polynomial.natDegree_zero] at hcon
    omega
  exact hne (hcoeff _ hcon)

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
      set p' : Polynomial R := Polynomial.C q.leadingCoeff * p -
        q * (Polynomial.C p.leadingCoeff *
          Polynomial.X ^ (p.natDegree - q.natDegree)) with hp'
      have hdlt : p'.natDegree < p.natDegree := natDegree_pseudoDivision_step_lt hq hlt
      obtain ⟨e, a, b, hab, hb⟩ := ih p'.natDegree (by omega) p' rfl
      refine ⟨e + 1, a + Polynomial.C q.leadingCoeff ^ e *
        (Polynomial.C p.leadingCoeff * Polynomial.X ^ (p.natDegree - q.natDegree)), b, ?_, hb⟩
      have hstep : Polynomial.C q.leadingCoeff ^ (e + 1) * p =
          Polynomial.C q.leadingCoeff ^ e * p' +
            Polynomial.C q.leadingCoeff ^ e *
              (q * (Polynomial.C p.leadingCoeff *
                Polynomial.X ^ (p.natDegree - q.natDegree))) := by
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

/-- Over a domain of characteristic zero, a variable occurring in a polynomial has a nonzero partial
derivative. -/
theorem pderiv_ne_zero_of_mem_vars_domain {σ C : Type*} [CommRing C] [NoZeroDivisors C]
    [CharZero C] {P : MvPolynomial σ C} {i : σ} (hi : i ∈ P.vars) :
    MvPolynomial.pderiv i P ≠ 0 := fun hzero =>
  MvPolynomial.mem_vars_iff_degreeOf_ne_zero.1 hi (degreeOf_eq_zero_of_pderiv_eq_zero hzero)

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

/-- **The pseudo-division step at a distinguished variable, over a commutative ring.** -/
theorem mvPolynomialPseudoDivision_step_degreeOf_lt {K σ : Type*} [CommRing K] (i : σ)
    {Q D : MvPolynomial σ K} (hD : MvPolynomial.degreeOf i D ≠ 0)
    (hQD : MvPolynomial.degreeOf i D ≤ MvPolynomial.degreeOf i Q) :
    MvPolynomial.degreeOf i
        (mvPolynomialInitialAt i D * Q -
          D * (mvPolynomialInitialAt i Q *
            MvPolynomial.X i ^ (MvPolynomial.degreeOf i Q - MvPolynomial.degreeOf i D)))
      < MvPolynomial.degreeOf i Q := by
  classical
  set A : ℕ := MvPolynomial.degreeOf i Q - MvPolynomial.degreeOf i D with hA
  set E : MvPolynomial σ K := mvPolynomialInitialAt i D * Q -
    D * (mvPolynomialInitialAt i Q * MvPolynomial.X i ^ A) with hE
  have h2 : mvPolynomialAsPolynomialAt i E =
      Polynomial.C (mvPolynomialAsPolynomialAt i D).leadingCoeff *
          mvPolynomialAsPolynomialAt i Q -
        mvPolynomialAsPolynomialAt i D *
          (Polynomial.C (mvPolynomialAsPolynomialAt i Q).leadingCoeff * Polynomial.X ^ A) := by
    have hpush : mvPolynomialPolynomialEquivAt (K := K) i E =
        Polynomial.C (mvPolynomialAsPolynomialAt i D).leadingCoeff *
            mvPolynomialAsPolynomialAt i Q -
          mvPolynomialAsPolynomialAt i D *
            (Polynomial.C (mvPolynomialAsPolynomialAt i Q).leadingCoeff * Polynomial.X ^ A) := by
      rw [hE, map_sub, map_mul, map_mul, map_mul, map_pow,
        mvPolynomialPolynomialEquivAt_initial, mvPolynomialPolynomialEquivAt_initial,
        mvPolynomialPolynomialEquivAt_X_self, mvPolynomialPolynomialEquivAt_apply,
        mvPolynomialPolynomialEquivAt_apply]
    simpa using hpush
  have hdQ : MvPolynomial.degreeOf i Q = (mvPolynomialAsPolynomialAt i Q).natDegree :=
    mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt i Q
  have hdD : MvPolynomial.degreeOf i D = (mvPolynomialAsPolynomialAt i D).natDegree :=
    mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt i D
  have hAeq : A = (mvPolynomialAsPolynomialAt i Q).natDegree -
      (mvPolynomialAsPolynomialAt i D).natDegree := by
    rw [hA, hdQ, hdD]
  rw [mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt i E, h2, hAeq, hdQ]
  exact natDegree_pseudoDivision_step_lt (by omega) (by omega)

/-- A power of a variable involves no other variable, with no nontriviality assumption. -/
theorem vars_X_pow_subset {K σ : Type*} [CommRing K] [DecidableEq σ] (i : σ) (n : ℕ) :
    ((MvPolynomial.X i : MvPolynomial σ K) ^ n).vars ⊆ {i} := by
  classical
  refine (MvPolynomial.vars_pow _ _).trans ?_
  rcases subsingleton_or_nontrivial K with hK | hK
  · have hzero : (MvPolynomial.X i : MvPolynomial σ K) = 0 := Subsingleton.elim _ _
    simp [hzero]
  · simp [MvPolynomial.vars_X]

/-- **Support-preserving pseudo-division at a distinguished variable, over a commutative ring.**
The recursion is performed in the multivariable ring itself, so at every cancellation step the
quotient and the remainder are visibly built from the dividend and the divisor: no variable is
introduced, and the multiplier is a power of the divisor's initial. -/
noncomputable def supportedMvPolynomialPseudoReductionAtOfCommRing
    {K σ : Type*} [CommRing K] [DecidableEq σ] (i : σ) :
    ∀ (Q D : MvPolynomial σ K), MvPolynomial.degreeOf i D ≠ 0 →
      SupportedMvPolynomialPseudoReductionAt i Q D
  | Q, D, hDdegree => by
      classical
      by_cases h : MvPolynomial.degreeOf i D ≤ MvPolynomial.degreeOf i Q
      · let A := mvPolynomialInitialAt i D
        let Z := mvPolynomialInitialAt i Q *
          MvPolynomial.X i ^ (MvPolynomial.degreeOf i Q - MvPolynomial.degreeOf i D)
        let Q₁ := A * Q - D * Z
        have hwf : MvPolynomial.degreeOf i Q₁ < MvPolynomial.degreeOf i Q := by
          simpa [A, Z, Q₁] using mvPolynomialPseudoDivision_step_degreeOf_lt i hDdegree h
        have hiD : i ∈ D.vars := (MvPolynomial.mem_vars_iff_degreeOf_ne_zero).mpr hDdegree
        have hAvars : A.vars ⊆ D.vars := by
          simpa [A] using mvPolynomialInitialAt_vars_subset i D
        have hZvars : Z.vars ⊆ Q.vars ∪ D.vars := by
          intro j hj
          rcases Finset.mem_union.mp (MvPolynomial.vars_mul _ _ hj) with hjQ | hjX
          · exact Finset.mem_union_left _ (mvPolynomialInitialAt_vars_subset i Q hjQ)
          · rw [Finset.mem_singleton.mp (vars_X_pow_subset (K := K) i _ hjX)]
            exact Finset.mem_union_right _ hiD
        have hQ₁vars : Q₁.vars ⊆ Q.vars ∪ D.vars := by
          intro j hj
          rcases Finset.mem_union.mp (MvPolynomial.vars_sub_subset (A * Q) (q := D * Z) hj) with
            hjAQ | hjDZ
          · rcases Finset.mem_union.mp (MvPolynomial.vars_mul A Q hjAQ) with hjA | hjQ
            · exact Finset.mem_union_right _ (hAvars hjA)
            · exact Finset.mem_union_left _ hjQ
          · rcases Finset.mem_union.mp (MvPolynomial.vars_mul D Z hjDZ) with hjD | hjZ
            · exact Finset.mem_union_right _ hjD
            · exact hZvars hjZ
        let d := supportedMvPolynomialPseudoReductionAtOfCommRing i Q₁ D hDdegree
        have hdQuotientVars : d.quotient.vars ⊆ Q.vars ∪ D.vars := by
          intro j hj
          rcases Finset.mem_union.mp (d.quotient_vars_subset hj) with hjQ₁ | hjD
          · exact hQ₁vars hjQ₁
          · exact Finset.mem_union_right _ hjD
        have hdRemainderVars : d.remainder.vars ⊆ Q.vars ∪ D.vars := by
          intro j hj
          rcases Finset.mem_union.mp (d.remainder_vars_subset hj) with hjQ₁ | hjD
          · exact hQ₁vars hjQ₁
          · exact Finset.mem_union_right _ hjD
        have hAZvars : (A ^ d.exponent * Z).vars ⊆ Q.vars ∪ D.vars := by
          intro j hj
          rcases Finset.mem_union.mp (MvPolynomial.vars_mul (A ^ d.exponent) Z hj) with hjA | hjZ
          · exact Finset.mem_union_right _ (hAvars (MvPolynomial.vars_pow A d.exponent hjA))
          · exact hZvars hjZ
        exact
          { exponent := d.exponent + 1
            quotient := A ^ d.exponent * Z + d.quotient
            remainder := d.remainder
            eq_mul_add := by
              have hd := d.eq_mul_add
              dsimp only [Q₁, A, Z] at hd ⊢
              linear_combination hd
            remainder_degree_lt := d.remainder_degree_lt
            quotient_vars_subset := by
              intro j hj
              rcases Finset.mem_union.mp
                  (MvPolynomial.vars_add_subset (A ^ d.exponent * Z) d.quotient hj) with hjAZ | hjd
              · exact hAZvars hjAZ
              · exact hdQuotientVars hjd
            remainder_vars_subset := hdRemainderVars }
      · exact
          { exponent := 0
            quotient := 0
            remainder := Q
            eq_mul_add := by simp
            remainder_degree_lt := by omega
            quotient_vars_subset := by simp
            remainder_vars_subset := Finset.subset_union_left }
  termination_by Q _ _ => MvPolynomial.degreeOf i Q

/-- Total differentiation raises a one-block jet bound by at most one, so no iterated derivative
involves a jet above its own order. -/
theorem notMem_vars_iterate_of_lt {ι K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    [Differential K] [DecidableEq ι] {i : ι} {m : ℕ} {A : DifferentialPolynomial ι K}
    (hA : ∀ j : ℕ, m < j → ((i, j) : ι × ℕ) ∉ A.vars) (k : ℕ) {j : ℕ} (hj : m + k < j) :
    ((i, j) : ι × ℕ) ∉ (diffPolyIterate k A).vars := by
  have hApd : ∀ l : ℕ, m < l → MvPolynomial.pderiv ((i, l) : ι × ℕ) A = 0 := fun l hl =>
    MvPolynomial.pderiv_eq_zero_of_notMem_vars (hA l hl)
  rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]
  push Not
  exact degreeOf_eq_zero_of_pderiv_eq_zero (pderiv_iterate_eq_zero_of_lt hApd k j hj)

/-- **The higher-jet reduction step.**  A polynomial can be pseudo-divided by the `k`-th total
derivative at the fresh jet, the multiplier is a power of the SEPARANT of the original polynomial
-- not of the derivative's own initial, which would drift upward in the other block -- and the
remainder introduces no variable that was not already present. -/
theorem exists_higherJet_reduction_step {ι K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    [Differential K] [DecidableEq ι] {i : ι} {m : ℕ} {A : DifferentialPolynomial ι K}
    (hA : ∀ j : ℕ, m < j → ((i, j) : ι × ℕ) ∉ A.vars)
    (hS : MvPolynomial.pderiv ((i, m) : ι × ℕ) A ≠ 0) {k : ℕ} (hk : 0 < k)
    (Q : DifferentialPolynomial ι K) :
    ∃ (e : ℕ) (a b : DifferentialPolynomial ι K),
      MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e * Q = diffPolyIterate k A * a + b ∧
        MvPolynomial.degreeOf ((i, m + k) : ι × ℕ) b = 0 ∧
          b.vars ⊆ Q.vars ∪ (diffPolyIterate k A).vars := by
  classical
  have hdeg := degreeOf_iterate_eq_one hA hS k hk
  have hApd : ∀ j : ℕ, m < j → MvPolynomial.pderiv ((i, j) : ι × ℕ) A = 0 := fun j hj =>
    MvPolynomial.pderiv_eq_zero_of_notMem_vars (hA j hj)
  have hinit : mvPolynomialInitialAt ((i, m + k) : ι × ℕ) (diffPolyIterate k A) =
      MvPolynomial.pderiv ((i, m) : ι × ℕ) A := by
    rw [initialAt_eq_pderiv_of_degreeOf_eq_one hdeg]
    exact pderiv_top_iterate_eq_separant hApd k
  let d := supportedMvPolynomialPseudoReductionAtOfCommRing ((i, m + k) : ι × ℕ) Q
    (diffPolyIterate k A) (by rw [hdeg]; omega)
  refine ⟨d.exponent, d.quotient, d.remainder, ?_, ?_, d.remainder_vars_subset⟩
  · rw [← hinit]
    exact d.eq_mul_add
  · have := d.remainder_degree_lt
    rw [hdeg] at this
    omega

/-- The differential principal ideal generated by an arbitrary differential polynomial over a
commutative differential coefficient ring. -/
def diffPolyIterateIdeal {ι K : Type*} [CommRing K] [Differential K]
    (P : DifferentialPolynomial ι K) : Ideal (DifferentialPolynomial ι K) :=
  Ideal.span (Set.range fun n : ℕ ↦ diffPolyIterate n P)

theorem diffPolyIterate_mem_diffPolyIterateIdeal {ι K : Type*} [CommRing K] [Differential K]
    (P : DifferentialPolynomial ι K) (n : ℕ) :
    diffPolyIterate n P ∈ diffPolyIterateIdeal P :=
  Ideal.subset_span ⟨n, rfl⟩

/-- **Phase one of the two-block Ritt reduction.**  Every polynomial can be reduced modulo the
differential ideal of `A` until it involves no jet above the leader of `A` in the distinguished
block, and the only multiplier used is a power of the separant of `A`.

The reduction descends on the highest jet present: at each level the fresh jet occurs linearly in
the corresponding total derivative of `A`, with the separant as its coefficient, so one
pseudo-division removes it without introducing any higher jet. -/
theorem exists_phaseOne_reduction {ι K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    [Differential K] [DecidableEq ι] {i : ι} {m : ℕ} {A : DifferentialPolynomial ι K}
    (hA : ∀ j : ℕ, m < j → ((i, j) : ι × ℕ) ∉ A.vars)
    (hS : MvPolynomial.pderiv ((i, m) : ι × ℕ) A ≠ 0) :
    ∀ (N : ℕ) (Q : DifferentialPolynomial ι K),
      (∀ j : ℕ, m + N < j → ((i, j) : ι × ℕ) ∉ Q.vars) →
      ∃ (e : ℕ) (b : DifferentialPolynomial ι K),
        MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e * Q - b ∈ diffPolyIterateIdeal A ∧
          ∀ j : ℕ, m < j → ((i, j) : ι × ℕ) ∉ b.vars := by
  intro N
  induction N with
  | zero =>
      intro Q hQ
      refine ⟨0, Q, ?_, ?_⟩
      · simp
      · intro j hj
        exact hQ j (by omega)
  | succ N ih =>
      intro Q hQ
      obtain ⟨e₁, a, b₁, hab, hb₁deg, hb₁vars⟩ :=
        exists_higherJet_reduction_step hA hS (k := N + 1) (by omega) Q
      have hb₁ : ∀ j : ℕ, m + N < j → ((i, j) : ι × ℕ) ∉ b₁.vars := by
        intro j hj hmem
        rcases Nat.lt_or_ge (m + N + 1) j with hlt | hle
        · rcases Finset.mem_union.mp (hb₁vars hmem) with hQmem | hAmem
          · exact hQ j (by omega) hQmem
          · exact notMem_vars_iterate_of_lt hA (N + 1) (by omega) hAmem
        · have hjeq : j = m + (N + 1) := by omega
          rw [hjeq] at hmem
          exact (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hmem) hb₁deg
      obtain ⟨e₂, b, hmem, hbvars⟩ := ih b₁ hb₁
      refine ⟨e₂ + e₁, b, ?_, hbvars⟩
      have hrewrite : MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ (e₂ + e₁) * Q - b =
          MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e₂ * (diffPolyIterate (N + 1) A * a) +
            (MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e₂ * b₁ - b) := by
        rw [pow_add]
        calc MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e₂ *
              MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e₁ * Q - b
            = MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e₂ *
                (MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e₁ * Q) - b := by ring
          _ = MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e₂ *
                (diffPolyIterate (N + 1) A * a + b₁) - b := by rw [hab]
          _ = _ := by ring
      rw [hrewrite]
      exact (diffPolyIterateIdeal A).add_mem
        ((diffPolyIterateIdeal A).mul_mem_left _
          ((diffPolyIterateIdeal A).mul_mem_right _
            (diffPolyIterate_mem_diffPolyIterateIdeal A (N + 1))))
        hmem

/-- **The two-block Ritt reduction.**  Every polynomial is congruent, modulo the differential ideal
of `A` and after multiplication by a power of the initial and a power of the separant of `A`, to a
polynomial that is reduced with respect to `A`: it involves no jet above the leader of `A` in the
distinguished block, and its degree in the leader is smaller than that of `A`.

Both multipliers are explicit polynomials in the jets of `A`, so the certificate never leaves the
polynomial ring and never raises the order in any other block -- the two properties that a
denominator produced by working over a fraction field would destroy. -/
theorem exists_ritt_reduction {ι K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    [Differential K] [DecidableEq ι] {i : ι} {m : ℕ} {A : DifferentialPolynomial ι K}
    (hA : ∀ j : ℕ, m < j → ((i, j) : ι × ℕ) ∉ A.vars)
    (hS : MvPolynomial.pderiv ((i, m) : ι × ℕ) A ≠ 0)
    (hAleader : MvPolynomial.degreeOf ((i, m) : ι × ℕ) A ≠ 0)
    (N : ℕ) (Q : DifferentialPolynomial ι K)
    (hQ : ∀ j : ℕ, m + N < j → ((i, j) : ι × ℕ) ∉ Q.vars) :
    ∃ (a b : ℕ) (R : DifferentialPolynomial ι K),
      mvPolynomialInitialAt ((i, m) : ι × ℕ) A ^ a *
            (MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ b * Q) - R ∈ diffPolyIterateIdeal A ∧
        (∀ j : ℕ, m < j → ((i, j) : ι × ℕ) ∉ R.vars) ∧
          MvPolynomial.degreeOf ((i, m) : ι × ℕ) R <
            MvPolynomial.degreeOf ((i, m) : ι × ℕ) A := by
  classical
  obtain ⟨e, b, hmem, hbvars⟩ := exists_phaseOne_reduction hA hS N Q hQ
  let d := supportedMvPolynomialPseudoReductionAtOfCommRing ((i, m) : ι × ℕ) b A hAleader
  refine ⟨d.exponent, e, d.remainder, ?_, ?_, d.remainder_degree_lt⟩
  · have hsplit : mvPolynomialInitialAt ((i, m) : ι × ℕ) A ^ d.exponent *
        (MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e * Q) - d.remainder =
          mvPolynomialInitialAt ((i, m) : ι × ℕ) A ^ d.exponent *
              (MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ e * Q - b) + A * d.quotient := by
      have hd := d.eq_mul_add
      linear_combination hd
    rw [hsplit]
    exact (diffPolyIterateIdeal A).add_mem
      ((diffPolyIterateIdeal A).mul_mem_left _ hmem)
      ((diffPolyIterateIdeal A).mul_mem_right _
        (diffPolyIterate_mem_diffPolyIterateIdeal A 0))
  · intro j hj hmemj
    rcases Finset.mem_union.mp (d.remainder_vars_subset hmemj) with hjb | hjA
    · exact hbvars j hj hjb
    · exact hA j hj hjA

/-- The differential principal ideal is contained in every derivation-stable ideal containing the
polynomial. -/
theorem diffPolyIterateIdeal_le_of_derivation_stable {ι K : Type*} [CommRing K] [Differential K]
    {A : DifferentialPolynomial ι K} {P : Ideal (DifferentialPolynomial ι K)} (hA : A ∈ P)
    (hstable : ∀ Q : DifferentialPolynomial ι K, Q ∈ P →
      differentialPolynomialOverDerivation ι K Q ∈ P) :
    diffPolyIterateIdeal A ≤ P := by
  rw [diffPolyIterateIdeal, Ideal.span_le]
  rintro _ ⟨n, rfl⟩
  induction n with
  | zero => exact hA
  | succ n hn =>
      show diffPolyIterate (n + 1) A ∈ P
      rw [diffPolyIterate_succ]
      exact hstable _ hn

/-- **Ritt's reduction theorem over a coefficient ring.**  If every polynomial of the ideal that is
reduced with respect to `A` vanishes -- the defining property of a characteristic -- then every
element of the ideal is absorbed into the differential ideal of `A` after multiplication by a power
of the initial and a power of the separant.

The multipliers are polynomials in the jets of `A`, so the certificate introduces no denominator and
no variable outside those of `A` and of the element being reduced. -/
theorem exists_initial_separant_powers_mem_diffPolyIterateIdeal {ι K : Type*} [CommRing K]
    [IsDomain K] [CharZero K] [Differential K] [DecidableEq ι] {i : ι} {m : ℕ}
    {A : DifferentialPolynomial ι K}
    (hA : ∀ j : ℕ, m < j → ((i, j) : ι × ℕ) ∉ A.vars)
    (hS : MvPolynomial.pderiv ((i, m) : ι × ℕ) A ≠ 0)
    (hAleader : MvPolynomial.degreeOf ((i, m) : ι × ℕ) A ≠ 0)
    {P : Ideal (DifferentialPolynomial ι K)} (hle : diffPolyIterateIdeal A ≤ P)
    (hreduced : ∀ R : DifferentialPolynomial ι K, R ∈ P →
      (∀ j : ℕ, m < j → ((i, j) : ι × ℕ) ∉ R.vars) →
      MvPolynomial.degreeOf ((i, m) : ι × ℕ) R <
        MvPolynomial.degreeOf ((i, m) : ι × ℕ) A → R = 0)
    (N : ℕ) {Q : DifferentialPolynomial ι K}
    (hQN : ∀ j : ℕ, m + N < j → ((i, j) : ι × ℕ) ∉ Q.vars) (hQ : Q ∈ P) :
    ∃ a b : ℕ,
      mvPolynomialInitialAt ((i, m) : ι × ℕ) A ^ a *
          (MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ b * Q) ∈ diffPolyIterateIdeal A := by
  obtain ⟨a, b, R, hmem, hRvars, hRdeg⟩ := exists_ritt_reduction hA hS hAleader N Q hQN
  have hRP : R ∈ P := by
    have hdiff : mvPolynomialInitialAt ((i, m) : ι × ℕ) A ^ a *
        (MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ b * Q) - R ∈ P := hle hmem
    have hmul : mvPolynomialInitialAt ((i, m) : ι × ℕ) A ^ a *
        (MvPolynomial.pderiv ((i, m) : ι × ℕ) A ^ b * Q) ∈ P :=
      P.mul_mem_left _ (P.mul_mem_left _ hQ)
    simpa using P.sub_mem hmul hdiff
  refine ⟨a, b, ?_⟩
  have hR0 : R = 0 := hreduced R hRP hRvars hRdeg
  rw [hR0, sub_zero] at hmem
  exact hmem

end

end GaloisForLFunctions
