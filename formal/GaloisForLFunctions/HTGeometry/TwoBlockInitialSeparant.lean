import GaloisForLFunctions.HTGeometry.PseudoDivisionCommRing
import GaloisForLFunctions.HTGeometry.TwoBlockEquivDerivation

/-!
# Right-block initial and separant of a two-block polynomial

The two-block splitting reads a polynomial in two jet blocks as a polynomial in the right block over
the ring of the left block.  Partial differentiation in a right-block jet is the same operation on
both sides of that splitting, and the coefficients of the right-block initial are coefficients of the
polynomial itself.

Both facts are support statements in disguise: they say that the multiplier produced by a
right-block pseudo-division introduces no left-block jet that was not already present.
-/

namespace GaloisForLFunctions

noncomputable section

variable {F : Type*} [CommRing F]

/-- Partial differentiation in a right-block jet commutes with the two-block splitting. -/
theorem differentialPolynomialTwoBlockEquiv_pderiv_inr (n : ℕ)
    (X : DifferentialPolynomial (Unit ⊕ Unit) F) :
    differentialPolynomialTwoBlockEquiv F
        (MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), n) X) =
      MvPolynomial.pderiv (((), n) : Unit × ℕ)
        (differentialPolynomialTwoBlockEquiv F X) := by
  classical
  induction X using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP =>
      rcases j with ⟨u, k⟩
      cases u with
      | inl u =>
          obtain rfl : u = () := Subsingleton.elim _ _
          have hne : ((Sum.inl () : Unit ⊕ Unit), k) ≠ ((Sum.inr () : Unit ⊕ Unit), n) := by
            simp
          rw [Derivation.leibniz]
          simp only [smul_eq_mul, map_add, map_mul, hP,
            differentialPolynomialTwoBlockEquiv_X_inl,
            MvPolynomial.pderiv_X_of_ne hne]
          rw [Derivation.leibniz]
          simp [smul_eq_mul]
      | inr u =>
          obtain rfl : u = () := Subsingleton.elim _ _
          rw [Derivation.leibniz]
          simp only [smul_eq_mul, map_add, map_mul, hP,
            differentialPolynomialTwoBlockEquiv_X_inr]
          rw [Derivation.leibniz]
          simp only [smul_eq_mul]
          by_cases hk : k = n
          · subst hk
            simp
          · have hne1 : ((Sum.inr () : Unit ⊕ Unit), k) ≠ ((Sum.inr () : Unit ⊕ Unit), n) := by
              simp [hk]
            have hne2 : (((), k) : Unit × ℕ) ≠ (((), n) : Unit × ℕ) := by
              simp [hk]
            rw [MvPolynomial.pderiv_X_of_ne hne1, MvPolynomial.pderiv_X_of_ne hne2]
            simp

/-- **A prime polynomial does not divide a power of its own separant.**  The separant is nonzero in
characteristic zero and has strictly smaller degree in the differentiated variable, so no multiple of
the polynomial can equal it. -/
theorem not_dvd_pderiv_pow {σ C : Type*} [Field C] [CharZero C] {A : MvPolynomial σ C}
    (hAprime : Prime A) {v : σ} (hv : MvPolynomial.degreeOf v A ≠ 0) (e : ℕ) :
    ¬ A ∣ (MvPolynomial.pderiv v A) ^ e := by
  classical
  intro hdvd
  rcases Nat.eq_zero_or_pos e with he | he
  · subst he
    rw [pow_zero] at hdvd
    exact hAprime.not_unit (isUnit_of_dvd_one hdvd)
  have hS0 : MvPolynomial.pderiv v A ≠ 0 :=
    mvPolynomial_pderiv_ne_zero_of_mem_vars_charZero
      (MvPolynomial.mem_vars_iff_degreeOf_ne_zero.2 hv)
  have hdvdS : A ∣ MvPolynomial.pderiv v A := hAprime.dvd_of_dvd_pow hdvd
  obtain ⟨T, hT⟩ := hdvdS
  have hA0 : A ≠ 0 := hAprime.ne_zero
  have hT0 : T ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hT
    exact hS0 hT
  have hdeg : MvPolynomial.degreeOf v (MvPolynomial.pderiv v A) =
      MvPolynomial.degreeOf v A + MvPolynomial.degreeOf v T := by
    rw [hT, MvPolynomial.degreeOf_mul_eq hA0 hT0]
  have hlt : MvPolynomial.degreeOf v (MvPolynomial.pderiv v A) <
      MvPolynomial.degreeOf v A := mvPolynomial_degreeOf_pderiv_lt hv
  omega

variable {F' : Type*} [Field F']

/-- The right-block embedding is injective. -/
theorem differentialPolynomialRight_injective :
    Function.Injective (differentialPolynomialRight (ι := Unit) (κ := Unit) (C := F')) := by
  refine MvPolynomial.rename_injective _ ?_
  rintro ⟨u, n⟩ ⟨v, m⟩ h
  obtain rfl : u = v := Subsingleton.elim _ _
  simpa using h

/-- A one-block polynomial whose right-block embedding is a unit is itself a unit. -/
theorem isUnit_of_isUnit_differentialPolynomialRight {r : DifferentialPolynomial Unit F'}
    (h : IsUnit (differentialPolynomialRight (ι := Unit) r)) : IsUnit r := by
  classical
  have hvars : (differentialPolynomialRight (ι := Unit) r).vars = ∅ := by
    refine Finset.eq_empty_of_forall_notMem fun j hj => ?_
    have hsubset := mvPolynomial_vars_subset_of_dvd h.dvd
      (one_ne_zero (α := DifferentialPolynomial (Unit ⊕ Unit) F'))
    have hj1 : j ∈ (1 : DifferentialPolynomial (Unit ⊕ Unit) F').vars := hsubset hj
    simp at hj1
  have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars
  have hrC : r = MvPolynomial.C ((differentialPolynomialRight (ι := Unit) r).coeff 0) := by
    refine differentialPolynomialRight_injective ?_
    rw [hC]
    simp [differentialPolynomialRight]
  have hc0 : (differentialPolynomialRight (ι := Unit) r).coeff 0 ≠ 0 := by
    intro h0
    rw [h0, MvPolynomial.C_0] at hrC
    rw [hrC] at h
    simp at h
  rw [hrC]
  exact (MvPolynomial.C (σ := Unit × ℕ)).isUnit_map (isUnit_iff_ne_zero.2 hc0)

/-- The block swap is an involution. -/
theorem differentialPolynomialTwoBlockSwap_involutive
    (X : DifferentialPolynomial (Unit ⊕ Unit) F') :
    differentialPolynomialTwoBlockSwap F' (differentialPolynomialTwoBlockSwap F' X) = X := by
  unfold differentialPolynomialTwoBlockSwap
  rw [MvPolynomial.rename_rename]
  rw [show ((fun p : (Unit ⊕ Unit) × ℕ ↦ ((Equiv.sumComm Unit Unit) p.1, p.2)) ∘
      fun p : (Unit ⊕ Unit) × ℕ ↦ ((Equiv.sumComm Unit Unit) p.1, p.2)) = id by
    funext p
    obtain ⟨u, n⟩ := p
    cases u <;> simp]
  simp

/-- **An irreducible two-block polynomial with a left-block jet is primitive for the right block.**
A right-block constant divisor would make the polynomial a right-block polynomial, which has no
left-block jet. -/
theorem primitive_swap_of_irreducible {A : DifferentialPolynomial (Unit ⊕ Unit) F'}
    (hAirr : Irreducible A) {k : ℕ} (hAleft : ((Sum.inl () : Unit ⊕ Unit), k) ∈ A.vars) :
    MvPolynomialPrimitive (differentialPolynomialTwoBlockEquiv F'
      (differentialPolynomialTwoBlockSwap F' A)) := by
  classical
  intro r hr
  obtain ⟨Z, hZ⟩ := hr
  have hswap : differentialPolynomialTwoBlockSwap F' A =
      differentialPolynomialLeft (κ := Unit) r *
        (differentialPolynomialTwoBlockEquiv F').symm Z := by
    apply (differentialPolynomialTwoBlockEquiv F').injective
    rw [map_mul, differentialPolynomialTwoBlockEquiv_left, AlgEquiv.apply_symm_apply]
    exact hZ
  have hA : A = differentialPolynomialRight (ι := Unit) r *
      differentialPolynomialTwoBlockSwap F'
        ((differentialPolynomialTwoBlockEquiv F').symm Z) := by
    have hcong := congrArg (differentialPolynomialTwoBlockSwap F') hswap
    rw [differentialPolynomialTwoBlockSwap_involutive, map_mul,
      differentialPolynomialTwoBlockSwap_left] at hcong
    exact hcong
  rcases hAirr.isUnit_or_isUnit hA with hu | hu
  · exact isUnit_of_isUnit_differentialPolynomialRight hu
  · exfalso
    obtain ⟨u, hu'⟩ := hu
    have hdvd : A ∣ differentialPolynomialRight (ι := Unit) r := by
      refine ⟨((u⁻¹ : (DifferentialPolynomial (Unit ⊕ Unit) F')ˣ) :
        DifferentialPolynomial (Unit ⊕ Unit) F'), ?_⟩
      rw [hA, ← hu', mul_assoc]
      simp
    have hr0 : differentialPolynomialRight (ι := Unit) r ≠ 0 := by
      intro h0
      have hA0 : A = 0 := by rw [hA, h0, zero_mul]
      rw [hA0] at hAleft
      simp at hAleft
    have hmem := mvPolynomial_vars_subset_of_dvd hdvd hr0 hAleft
    obtain ⟨b, _, hb⟩ := MvPolynomial.mem_vars_rename
      (fun p : Unit × ℕ ↦ ((Sum.inr p.1 : Unit ⊕ Unit), p.2)) r hmem
    exact absurd hb (by simp)

section VarsTranslation

variable {F'' : Type*} [Field F''] [CharZero F'']

/-- **Right-block variables are the variables of the split polynomial.**  In characteristic zero a
variable occurs exactly when its partial derivative does not vanish, and the right-block partial
derivative commutes with the splitting. -/
theorem mem_vars_twoBlockEquiv_iff (X : DifferentialPolynomial (Unit ⊕ Unit) F'') (n : ℕ) :
    (((), n) : Unit × ℕ) ∈ (differentialPolynomialTwoBlockEquiv F'' X).vars ↔
      ((Sum.inr () : Unit ⊕ Unit), n) ∈ X.vars := by
  classical
  constructor
  · intro h
    by_contra hcon
    have h1 : MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), n) X = 0 :=
      MvPolynomial.pderiv_eq_zero_of_notMem_vars hcon
    have h2 : MvPolynomial.pderiv (((), n) : Unit × ℕ)
        (differentialPolynomialTwoBlockEquiv F'' X) = 0 := by
      rw [← differentialPolynomialTwoBlockEquiv_pderiv_inr, h1, map_zero]
    exact pderiv_ne_zero_of_mem_vars_domain h h2
  · intro h
    by_contra hcon
    have h1 : MvPolynomial.pderiv (((), n) : Unit × ℕ)
        (differentialPolynomialTwoBlockEquiv F'' X) = 0 :=
      MvPolynomial.pderiv_eq_zero_of_notMem_vars hcon
    have h2 : differentialPolynomialTwoBlockEquiv F''
        (MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), n) X) = 0 := by
      rw [differentialPolynomialTwoBlockEquiv_pderiv_inr]
      exact h1
    have h3 : MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), n) X = 0 :=
      (differentialPolynomialTwoBlockEquiv F'').injective (by simpa using h2)
    exact pderiv_ne_zero_of_mem_vars_domain h h3

/-- The block swap exchanges the two blocks of variables. -/
theorem mem_vars_twoBlockSwap_iff (X : DifferentialPolynomial (Unit ⊕ Unit) F'') (n : ℕ) :
    ((Sum.inr () : Unit ⊕ Unit), n) ∈ (differentialPolynomialTwoBlockSwap F'' X).vars ↔
      ((Sum.inl () : Unit ⊕ Unit), n) ∈ X.vars := by
  classical
  have hinj : Function.Injective
      (fun p : (Unit ⊕ Unit) × ℕ ↦ ((Equiv.sumComm Unit Unit) p.1, p.2)) := by
    rintro ⟨u, a⟩ ⟨v, b⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact Prod.ext ((Equiv.sumComm Unit Unit).injective h1) h2
  have hpd : MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), n)
      (differentialPolynomialTwoBlockSwap F'' X) =
      differentialPolynomialTwoBlockSwap F''
        (MvPolynomial.pderiv ((Sum.inl () : Unit ⊕ Unit), n) X) := by
    unfold differentialPolynomialTwoBlockSwap
    rw [show ((Sum.inr () : Unit ⊕ Unit), n) =
        (fun p : (Unit ⊕ Unit) × ℕ ↦ ((Equiv.sumComm Unit Unit) p.1, p.2))
          ((Sum.inl () : Unit ⊕ Unit), n) by simp]
    exact MvPolynomial.pderiv_rename hinj _ _
  constructor
  · intro h
    by_contra hcon
    have h1 : MvPolynomial.pderiv ((Sum.inl () : Unit ⊕ Unit), n) X = 0 :=
      MvPolynomial.pderiv_eq_zero_of_notMem_vars hcon
    exact pderiv_ne_zero_of_mem_vars_domain h (by rw [hpd, h1, map_zero])
  · intro h
    by_contra hcon
    have h1 : MvPolynomial.pderiv ((Sum.inr () : Unit ⊕ Unit), n)
        (differentialPolynomialTwoBlockSwap F'' X) = 0 :=
      MvPolynomial.pderiv_eq_zero_of_notMem_vars hcon
    rw [hpd] at h1
    have h2 : MvPolynomial.pderiv ((Sum.inl () : Unit ⊕ Unit), n) X = 0 := by
      unfold differentialPolynomialTwoBlockSwap at h1
      exact MvPolynomial.rename_injective _ hinj (by simpa using h1)
    exact pderiv_ne_zero_of_mem_vars_domain h h2

/-- **The left-block order of a two-block polynomial.**  It is bounded by `N` exactly when no
left-block jet above `N` occurs. -/
theorem scalarDifferentialPolynomialOrder_swap_le_iff
    (X : DifferentialPolynomial (Unit ⊕ Unit) F'') (N : ℕ) :
    scalarDifferentialPolynomialOrder (differentialPolynomialTwoBlockEquiv F''
        (differentialPolynomialTwoBlockSwap F'' X)) ≤ N ↔
      ∀ n : ℕ, N < n → ((Sum.inl () : Unit ⊕ Unit), n) ∉ X.vars := by
  classical
  constructor
  · intro h n hn hmem
    have hmem' : (((), n) : Unit × ℕ) ∈ (differentialPolynomialTwoBlockEquiv F''
        (differentialPolynomialTwoBlockSwap F'' X)).vars :=
      (mem_vars_twoBlockEquiv_iff _ n).2 ((mem_vars_twoBlockSwap_iff X n).2 hmem)
    have hle : n ≤ scalarDifferentialPolynomialOrder (differentialPolynomialTwoBlockEquiv F''
        (differentialPolynomialTwoBlockSwap F'' X)) :=
      Finset.le_sup (f := fun p : Unit × ℕ ↦ p.2) hmem'
    omega
  · intro h
    refine Finset.sup_le ?_
    rintro ⟨u, n⟩ hp
    obtain rfl : u = () := Subsingleton.elim _ _
    by_contra hcon
    exact h n (by omega)
      ((mem_vars_twoBlockSwap_iff X n).1 ((mem_vars_twoBlockEquiv_iff _ n).1 hp))

end VarsTranslation

end

end GaloisForLFunctions
