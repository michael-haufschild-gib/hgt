import GaloisForLFunctions.HTGeometry.DifferentialLurothCoefficient

/-!
# The general component of an irreducible differential polynomial, as an ideal

The corpus builds the general-component jets one level at a time, correcting the jet of order
`ord A + n + 1` at step `n`.  Each coordinate is therefore eventually constant, so the construction
has a limit point, and the vanishing ideal of that point is a prime differential ideal containing
every iterated derivative of the polynomial.

Below the order of the polynomial the limit point is the base point, so a member of the component of
low order is a multiple of the polynomial whenever the base point is a generic point of the ordinary
hypersurface.  That is the general component in ideal form: prime, containing the differential ideal,
and detecting divisibility in low order.
-/

namespace GaloisForLFunctions

open MvPolynomial

open scoped Differential

noncomputable section

universe u

variable {K : Type u} {L : Type*} [Field K] [Differential K] [CharZero K] [Field L]

/-- The limit of the general-component jets: each coordinate is eventually constant. -/
def generalComponentPoint (f : K →+* L) (A : DifferentialPolynomial Unit K)
    (x₀ : Unit × ℕ → L) : Unit × ℕ → L :=
  fun q => differentialPolynomialGeneralComponentJets f A x₀ q.2 q

omit [CharZero K] in
/-- The construction only ever updates the coordinate of order `ord A + n + 1` at step `n`, so each
coordinate stabilizes from its own index on. -/
theorem generalComponentJets_stabilizes (f : K →+* L) (A : DifferentialPolynomial Unit K)
    (x₀ : Unit × ℕ → L) (q : Unit × ℕ) {N : ℕ} (hN : q.2 ≤ N) :
    differentialPolynomialGeneralComponentJets f A x₀ N q =
      differentialPolynomialGeneralComponentJets f A x₀ q.2 q := by
  induction N with
  | zero =>
      have : q.2 = 0 := Nat.eq_zero_of_le_zero hN
      rw [this]
  | succ N hN' =>
      rcases lt_or_eq_of_le hN with hlt | heq
      · have hle : q.2 ≤ N := by omega
        rw [differentialPolynomialGeneralComponentJets_succ]
        have hne : q ≠ ((), scalarDifferentialPolynomialOrder A + N + 1) := by
          intro h
          rw [h] at hle
          simp only at hle
          omega
        simp only [Function.update_of_ne hne]
        exact hN' hle
      · rw [heq]

omit [CharZero K] in
theorem generalComponentPoint_eq (f : K →+* L) (A : DifferentialPolynomial Unit K)
    (x₀ : Unit × ℕ → L) {q : Unit × ℕ} {N : ℕ} (hN : q.2 ≤ N) :
    generalComponentPoint f A x₀ q =
      differentialPolynomialGeneralComponentJets f A x₀ N q :=
  (generalComponentJets_stabilizes f A x₀ q hN).symm

omit [CharZero K] in
/-- Below the order of the polynomial the limit point is the base point. -/
theorem generalComponentPoint_apply_of_le_order (f : K →+* L)
    (A : DifferentialPolynomial Unit K) (x₀ : Unit × ℕ → L) {q : Unit × ℕ}
    (hq : q.2 ≤ scalarDifferentialPolynomialOrder A) :
    generalComponentPoint f A x₀ q = x₀ q := by
  rw [generalComponentPoint]
  obtain ⟨u, k⟩ := q
  obtain rfl : u = () := Subsingleton.elim _ _
  exact differentialPolynomialGeneralComponentJets_apply_of_le_order f A x₀ k k hq

omit [CharZero K] in
/-- Evaluations at the limit point and at any sufficiently late stage agree. -/
theorem eval₂_generalComponentPoint_eq (f : K →+* L) (A : DifferentialPolynomial Unit K)
    (x₀ : Unit × ℕ → L) {Q : DifferentialPolynomial Unit K} {N : ℕ}
    (hQ : ∀ q ∈ Q.vars, q.2 ≤ N) :
    MvPolynomial.eval₂ f (generalComponentPoint f A x₀) Q =
      MvPolynomial.eval₂ f (differentialPolynomialGeneralComponentJets f A x₀ N) Q := by
  classical
  refine MvPolynomial.eval₂_congr _ _ _ ?_
  intro q c hqc hc
  exact generalComponentPoint_eq f A x₀
    (hQ q ((MvPolynomial.mem_vars_iff_mem_support q).2
      ⟨c, MvPolynomial.mem_support_iff.2 hc, hqc⟩))

/-- **The general component**, as the vanishing ideal of the limit point. -/
def generalComponent (f : K →+* L) (A : DifferentialPolynomial Unit K)
    (x₀ : Unit × ℕ → L) : Ideal (DifferentialPolynomial Unit K) :=
  RingHom.ker (MvPolynomial.eval₂Hom f (generalComponentPoint f A x₀))

omit [CharZero K] in
theorem mem_generalComponent_iff (f : K →+* L) (A : DifferentialPolynomial Unit K)
    (x₀ : Unit × ℕ → L) (Q : DifferentialPolynomial Unit K) :
    Q ∈ generalComponent f A x₀ ↔
      MvPolynomial.eval₂ f (generalComponentPoint f A x₀) Q = 0 := Iff.rfl

omit [CharZero K] in
/-- The general component is a prime ideal, being the kernel of a map to a field. -/
theorem generalComponent_isPrime (f : K →+* L) (A : DifferentialPolynomial Unit K)
    (x₀ : Unit × ℕ → L) : (generalComponent f A x₀).IsPrime :=
  RingHom.ker_isPrime _

/-- **The differential ideal sits inside the general component.** -/
theorem iterateIdeal_le_generalComponent (f : K →+* L) {A : DifferentialPolynomial Unit K}
    (hAvars : A.vars.Nonempty) (x₀ : Unit × ℕ → L)
    (hA : MvPolynomial.eval₂ f x₀ A = 0)
    (hSeparant : MvPolynomial.eval₂ f x₀
      (scalarDifferentialPolynomialSeparant A) ≠ 0) :
    differentialPolynomialIterateIdeal A ≤ generalComponent f A x₀ := by
  classical
  intro Q hQ
  obtain ⟨N, hN⟩ := mem_differentialPolynomialIterateIdeal_exists_upTo A Q hQ
  set M := max N (scalarDifferentialPolynomialOrder Q) with hM
  have hQvars : ∀ q ∈ Q.vars, q.2 ≤ M := by
    intro q hq
    have hle : q.2 ≤ scalarDifferentialPolynomialOrder Q :=
      Finset.le_sup (f := fun j : Unit × ℕ ↦ j.2) hq
    omega
  have hupto : Q ∈ differentialPolynomialIterateIdealUpTo A M :=
    differentialPolynomialIterateIdealUpTo_mono A (le_max_left _ _) hN
  rw [mem_generalComponent_iff, eval₂_generalComponentPoint_eq f A x₀ hQvars]
  exact differentialPolynomialGeneralComponentJets_eval_mem_iterateIdealUpTo f hAvars x₀ hA
    hSeparant hupto

omit [CharZero K] in
/-- **Low-order members of the component are multiples.**  If the base point is a generic point of
the ordinary hypersurface, then a member of the component whose jets stay below the order of the
polynomial is divisible by it. -/
theorem dvd_of_mem_generalComponent_of_order_le (f : K →+* L)
    {A : DifferentialPolynomial Unit K} (x₀ : Unit × ℕ → L)
    (hx₀ : ∀ R : DifferentialPolynomial Unit K, MvPolynomial.eval₂ f x₀ R = 0 → A ∣ R)
    {Q : DifferentialPolynomial Unit K}
    (hQorder : scalarDifferentialPolynomialOrder Q ≤ scalarDifferentialPolynomialOrder A)
    (hQ : Q ∈ generalComponent f A x₀) : A ∣ Q := by
  classical
  refine hx₀ Q ?_
  have hQvars : ∀ q ∈ Q.vars, q.2 ≤ scalarDifferentialPolynomialOrder A := by
    intro q hq
    have hle : q.2 ≤ scalarDifferentialPolynomialOrder Q :=
      Finset.le_sup (f := fun j : Unit × ℕ ↦ j.2) hq
    omega
  have hcongr : MvPolynomial.eval₂ f x₀ Q =
      MvPolynomial.eval₂ f (generalComponentPoint f A x₀) Q := by
    refine MvPolynomial.eval₂_congr _ _ _ ?_
    intro q c hqc hc
    exact (generalComponentPoint_apply_of_le_order f A x₀
      (hQvars q ((MvPolynomial.mem_vars_iff_mem_support q).2
        ⟨c, MvPolynomial.mem_support_iff.2 hc, hqc⟩))).symm
  rw [hcongr]
  exact (mem_generalComponent_iff f A x₀ Q).1 hQ

omit [CharZero K] in
/-- **Cancellation in the component.**  A factor outside the component can be cancelled from a
product lying in it. -/
theorem mem_generalComponent_of_mul_mem (f : K →+* L) (A : DifferentialPolynomial Unit K)
    (x₀ : Unit × ℕ → L) {T Q : DifferentialPolynomial Unit K}
    (hT : T ∉ generalComponent f A x₀) (h : T * Q ∈ generalComponent f A x₀) :
    Q ∈ generalComponent f A x₀ :=
  ((generalComponent_isPrime f A x₀).mem_or_mem h).resolve_left hT

omit [CharZero K] in
/-- **A distinct irreducible of no larger order is outside the component.**  This is what makes the
already-divided factors cancellable in Ritt's peeling. -/
theorem not_mem_generalComponent_of_irreducible (f : K →+* L)
    {A B : DifferentialPolynomial Unit K} (x₀ : Unit × ℕ → L)
    (hx₀ : ∀ R : DifferentialPolynomial Unit K, MvPolynomial.eval₂ f x₀ R = 0 → A ∣ R)
    (hB : Irreducible B) (hAunit : ¬ IsUnit A) (hnotassoc : ¬ Associated A B)
    (hBorder : scalarDifferentialPolynomialOrder B ≤ scalarDifferentialPolynomialOrder A) :
    B ∉ generalComponent f A x₀ := by
  intro hmem
  have hdvd := dvd_of_mem_generalComponent_of_order_le f x₀ hx₀ hBorder hmem
  obtain ⟨c, hc⟩ := hdvd
  rcases hB.isUnit_or_isUnit hc with hu | hu
  · exact hAunit hu
  · refine hnotassoc ⟨hu.unit, ?_⟩
    rw [hu.unit_spec]
    exact hc.symm

omit [Differential K] [CharZero K] in
/-- A nonzero multiple of `A` cannot have smaller Ritt rank than `A`. -/
theorem not_rank_lt_of_dvd {A R : DifferentialPolynomial Unit K} (hA : A ≠ 0) (hR : R ≠ 0)
    (hdvd : A ∣ R) :
    ¬ (scalarDifferentialPolynomialOrder R < scalarDifferentialPolynomialOrder A ∨
      (scalarDifferentialPolynomialOrder R = scalarDifferentialPolynomialOrder A ∧
        scalarDifferentialPolynomialLeaderDegree R <
          scalarDifferentialPolynomialLeaderDegree A)) := by
  obtain ⟨T, rfl⟩ := hdvd
  have hT : T ≠ 0 := by
    intro h0
    exact hR (by rw [h0, mul_zero])
  have horder := scalarDifferentialPolynomialOrder_left_le_mul hA hT
  rintro (hlt | ⟨heq, hdeg⟩)
  · omega
  · have hleader := scalarDifferentialPolynomialLeaderDegree_left_le_mul hA hT heq.symm
    omega

/-- **The general component is the smallest prime differential ideal containing the polynomial and
avoiding its initial and separant.**  Ritt reduction sends any member of the component to a
remainder of smaller rank which the component forces to vanish, so the member is caught by the
initial/separant saturation, which any such prime absorbs. -/
theorem generalComponent_le_of_iterateIdeal_le (f : K →+* L)
    {A : DifferentialPolynomial Unit K} (hAvars : A.vars.Nonempty) (x₀ : Unit × ℕ → L)
    (hA : MvPolynomial.eval₂ f x₀ A = 0)
    (hSeparant : MvPolynomial.eval₂ f x₀ (scalarDifferentialPolynomialSeparant A) ≠ 0)
    (hx₀ : ∀ R : DifferentialPolynomial Unit K, MvPolynomial.eval₂ f x₀ R = 0 → A ∣ R)
    {J : Ideal (DifferentialPolynomial Unit K)} (hJ : J.IsPrime)
    (hAmem : differentialPolynomialIterateIdeal A ≤ J)
    (hI : scalarDifferentialPolynomialInitial A ∉ J)
    (hS : scalarDifferentialPolynomialSeparant A ∉ J) :
    generalComponent f A x₀ ≤ J := by
  classical
  intro Q hQ
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0] at hAvars
    simp at hAvars
  set red := characteristicPseudoReduction A hAvars Q with hred
  set W : DifferentialPolynomial Unit K :=
    scalarDifferentialPolynomialInitial A ^ red.initialExponent *
      scalarDifferentialPolynomialSeparant A ^ red.separantExponent * Q with hW
  have hcong : W - red.remainder ∈ differentialPolynomialIterateIdeal A := red.congruence
  have hWmem : W ∈ generalComponent f A x₀ := Ideal.mul_mem_left _ _ hQ
  have hRmem : red.remainder ∈ generalComponent f A x₀ := by
    have hsub : W - red.remainder ∈ generalComponent f A x₀ :=
      iterateIdeal_le_generalComponent f hAvars x₀ hA hSeparant hcong
    have := Ideal.sub_mem _ hWmem hsub
    simpa using this
  have hRorder : scalarDifferentialPolynomialOrder red.remainder ≤
      scalarDifferentialPolynomialOrder A := by
    rcases red.remainder_rank_lt with hlt | ⟨heq, -⟩
    · omega
    · omega
  have hR0 : red.remainder = 0 := by
    by_contra hne
    exact not_rank_lt_of_dvd hA0 hne
      (dvd_of_mem_generalComponent_of_order_le f x₀ hx₀ hRorder hRmem) red.remainder_rank_lt
  rw [hR0, sub_zero] at hcong
  have hWJ : W ∈ J := hAmem hcong
  rw [hW] at hWJ
  rcases hJ.mem_or_mem hWJ with hleft | hright
  · rcases hJ.mem_or_mem hleft with hIpow | hSpow
    · exact absurd (hJ.mem_of_pow_mem _ hIpow) hI
    · exact absurd (hJ.mem_of_pow_mem _ hSpow) hS
  · exact hright

omit [CharZero K] in
/-- The initial is outside the component: it has strictly smaller order, so divisibility by `A`
would be impossible. -/
theorem initial_not_mem_generalComponent (f : K →+* L) {A : DifferentialPolynomial Unit K}
    (hAvars : A.vars.Nonempty) (x₀ : Unit × ℕ → L)
    (hx₀ : ∀ R : DifferentialPolynomial Unit K, MvPolynomial.eval₂ f x₀ R = 0 → A ∣ R) :
    scalarDifferentialPolynomialInitial A ∉ generalComponent f A x₀ := by
  intro hmem
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0] at hAvars
    simp at hAvars
  have hI0 : scalarDifferentialPolynomialInitial A ≠ 0 :=
    scalarDifferentialPolynomialInitial_ne_zero hA0
  by_cases hvars : (scalarDifferentialPolynomialInitial A).vars.Nonempty
  · have hlt := scalarDifferentialPolynomialInitial_order_lt hvars
    exact not_rank_lt_of_dvd hA0 hI0
      (dvd_of_mem_generalComponent_of_order_le f x₀ hx₀ (le_of_lt hlt) hmem)
      (Or.inl hlt)
  · rw [Finset.not_nonempty_iff_eq_empty] at hvars
    have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars
    have hc : (scalarDifferentialPolynomialInitial A).coeff 0 ≠ 0 := by
      intro h0
      apply hI0
      rw [hC, h0, map_zero]
    have hunit : IsUnit (scalarDifferentialPolynomialInitial A) := by
      rw [hC]
      exact IsUnit.map MvPolynomial.C hc.isUnit
    have hdvd := dvd_of_mem_generalComponent_of_order_le f x₀ hx₀
      (by
        rw [scalarDifferentialPolynomialOrder, hC]
        simp) hmem
    have hAunit : IsUnit A := isUnit_of_dvd_unit hdvd hunit
    obtain ⟨j, hj⟩ := hAvars
    obtain ⟨v, hv⟩ := hAunit.exists_right_inv
    have hv0 : v ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hv
      exact zero_ne_one hv
    have hdeg := MvPolynomial.degreeOf_mul_eq (n := j) hA0 hv0
    rw [hv] at hdeg
    simp only [MvPolynomial.degreeOf_one] at hdeg
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero] at hj
    omega

omit [CharZero K] in
/-- The separant is outside the component. -/
theorem separant_not_mem_generalComponent (f : K →+* L) {A : DifferentialPolynomial Unit K}
    (hAvars : A.vars.Nonempty) (hS0 : scalarDifferentialPolynomialSeparant A ≠ 0)
    (x₀ : Unit × ℕ → L)
    (hx₀ : ∀ R : DifferentialPolynomial Unit K, MvPolynomial.eval₂ f x₀ R = 0 → A ∣ R) :
    scalarDifferentialPolynomialSeparant A ∉ generalComponent f A x₀ := by
  intro hmem
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0] at hAvars
    simp at hAvars
  have hle := scalarDifferentialPolynomialSeparant_order_le A
  have hdvd := dvd_of_mem_generalComponent_of_order_le f x₀ hx₀ hle hmem
  refine not_rank_lt_of_dvd hA0 hS0 hdvd ?_
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, scalarDifferentialPolynomialSeparant_leaderDegree_lt hAvars heq⟩

/-- **Ranking independence.**  Two general components of the same polynomial, built from any two
generic base points, coincide: each is the smallest prime containing the differential ideal and
avoiding the initial and separant, and each satisfies the other's hypotheses. -/
theorem generalComponent_eq {L' : Type*} [Field L'] (f : K →+* L) (f' : K →+* L')
    {A : DifferentialPolynomial Unit K} (hAvars : A.vars.Nonempty)
    (hS0 : scalarDifferentialPolynomialSeparant A ≠ 0)
    (x₀ : Unit × ℕ → L) (x₀' : Unit × ℕ → L')
    (hA : MvPolynomial.eval₂ f x₀ A = 0)
    (hSeparant : MvPolynomial.eval₂ f x₀ (scalarDifferentialPolynomialSeparant A) ≠ 0)
    (hx₀ : ∀ R : DifferentialPolynomial Unit K, MvPolynomial.eval₂ f x₀ R = 0 → A ∣ R)
    (hA' : MvPolynomial.eval₂ f' x₀' A = 0)
    (hSeparant' : MvPolynomial.eval₂ f' x₀' (scalarDifferentialPolynomialSeparant A) ≠ 0)
    (hx₀' : ∀ R : DifferentialPolynomial Unit K, MvPolynomial.eval₂ f' x₀' R = 0 → A ∣ R) :
    generalComponent f A x₀ = generalComponent f' A x₀' := by
  refine le_antisymm ?_ ?_
  · exact generalComponent_le_of_iterateIdeal_le f hAvars x₀ hA hSeparant hx₀
      (generalComponent_isPrime f' A x₀')
      (iterateIdeal_le_generalComponent f' hAvars x₀' hA' hSeparant')
      (initial_not_mem_generalComponent f' hAvars x₀' hx₀')
      (separant_not_mem_generalComponent f' hAvars hS0 x₀' hx₀')
  · exact generalComponent_le_of_iterateIdeal_le f' hAvars x₀' hA' hSeparant' hx₀'
      (generalComponent_isPrime f A x₀)
      (iterateIdeal_le_generalComponent f hAvars x₀ hA hSeparant)
      (initial_not_mem_generalComponent f hAvars x₀ hx₀)
      (separant_not_mem_generalComponent f hAvars hS0 x₀ hx₀)

/-- **Divisibility from a certificate, with no constraint on the multiplier's order.**  If the
multiplier lies outside the general component, primality cancels it, and the low-order divisibility
of the component finishes.  This strengthens the corpus's bridge, whose multiplier had to have order
at most that of the divisor. -/
theorem dvd_of_mul_mem_iterateIdeal_of_notMem_generalComponent (f : K →+* L)
    {A : DifferentialPolynomial Unit K} (hAvars : A.vars.Nonempty) (x₀ : Unit × ℕ → L)
    (hA : MvPolynomial.eval₂ f x₀ A = 0)
    (hSeparant : MvPolynomial.eval₂ f x₀ (scalarDifferentialPolynomialSeparant A) ≠ 0)
    (hx₀ : ∀ R : DifferentialPolynomial Unit K, MvPolynomial.eval₂ f x₀ R = 0 → A ∣ R)
    {M Q : DifferentialPolynomial Unit K}
    (hM : M ∉ generalComponent f A x₀)
    (hQorder : scalarDifferentialPolynomialOrder Q ≤ scalarDifferentialPolynomialOrder A)
    (hmem : M * Q ∈ differentialPolynomialIterateIdeal A) :
    A ∣ Q := by
  have hmemComp : M * Q ∈ generalComponent f A x₀ :=
    iterateIdeal_le_generalComponent f hAvars x₀ hA hSeparant hmem
  exact dvd_of_mem_generalComponent_of_order_le f x₀ hx₀ hQorder
    (mem_generalComponent_of_mul_mem f A x₀ hM hmemComp)

omit [CharZero K] in
/-- **Cancelling an already-divided factor.**  A product of polynomials outside the component is
outside it, so a quotient inherits membership. -/
theorem mem_generalComponent_of_mul_mem_of_notMem (f : K →+* L)
    (A : DifferentialPolynomial Unit K) (x₀ : Unit × ℕ → L)
    {T L' : DifferentialPolynomial Unit K}
    (hT : T ∉ generalComponent f A x₀)
    (h : T * L' ∈ generalComponent f A x₀) :
    L' ∈ generalComponent f A x₀ :=
  mem_generalComponent_of_mul_mem f A x₀ hT h

omit [CharZero K] in
/-- A product of polynomials outside a prime is outside it. -/
theorem mul_notMem_generalComponent (f : K →+* L) (A : DifferentialPolynomial Unit K)
    (x₀ : Unit × ℕ → L) {S T : DifferentialPolynomial Unit K}
    (hS : S ∉ generalComponent f A x₀) (hT : T ∉ generalComponent f A x₀) :
    S * T ∉ generalComponent f A x₀ := by
  intro hmem
  rcases (generalComponent_isPrime f A x₀).mem_or_mem hmem with h | h
  · exact hS h
  · exact hT h

omit [CharZero K] in
/-- **The peeling step.**  Suppose the factors processed so far multiply to `T`, so that
`D = T * L`, and suppose `T` avoids the component of the next factor `A` while `D` lies in it.  If
the running quotient has order at most `A`'s, then `T * A` divides `D`: the step both divides one
more factor out and keeps the shape of the invariant. -/
theorem mul_dvd_of_peeling_step (f : K →+* L) {A : DifferentialPolynomial Unit K}
    (x₀ : Unit × ℕ → L)
    (hx₀ : ∀ R : DifferentialPolynomial Unit K, MvPolynomial.eval₂ f x₀ R = 0 → A ∣ R)
    {T Lq D : DifferentialPolynomial Unit K}
    (hD : D = T * Lq)
    (hT : T ∉ generalComponent f A x₀)
    (hDmem : D ∈ generalComponent f A x₀)
    (hLorder : scalarDifferentialPolynomialOrder Lq ≤ scalarDifferentialPolynomialOrder A) :
    T * A ∣ D := by
  have hLmem : Lq ∈ generalComponent f A x₀ := by
    refine mem_generalComponent_of_mul_mem f A x₀ hT ?_
    rw [← hD]
    exact hDmem
  obtain ⟨W, hW⟩ := dvd_of_mem_generalComponent_of_order_le f x₀ hx₀ hLorder hLmem
  exact ⟨W, by rw [hD, hW]; ring⟩

/-- **The peeling loop.**  If from every partial product `T` of factors of `C` that already divides
`D` one can always split off one more non-unit factor and keep dividing `D`, then `C` divides `D`.
The induction is on the number of irreducible factors left to process. -/
theorem dvd_of_peeling_loop {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {C D : R} (hC0 : C ≠ 0)
    (step : ∀ T S : R, C = T * S → T ∣ D → ¬ IsUnit S →
      ∃ A B : R, S = A * B ∧ ¬ IsUnit A ∧ T * A ∣ D) :
    C ∣ D := by
  classical
  suffices h : ∀ n : ℕ, ∀ T S : R, C = T * S → T ∣ D →
      (UniqueFactorizationMonoid.factors S).card ≤ n → C ∣ D by
    exact h (UniqueFactorizationMonoid.factors C).card 1 C (by ring) (one_dvd D) le_rfl
  have hunit_of_card : ∀ S : R, S ≠ 0 →
      (UniqueFactorizationMonoid.factors S).card = 0 → IsUnit S := by
    intro S hS0 hcard
    have hfact : UniqueFactorizationMonoid.factors S = 0 := Multiset.card_eq_zero.1 hcard
    have hprod := UniqueFactorizationMonoid.factors_prod hS0
    rw [hfact] at hprod
    simpa using hprod.isUnit isUnit_one
  have hfinish : ∀ T S : R, C = T * S → T ∣ D → IsUnit S → C ∣ D := by
    intro T S hC hT hunit
    obtain ⟨u, hu⟩ := hunit
    have hCT : C ∣ T := ⟨(↑u⁻¹ : R), by rw [hC, ← hu]; simp [mul_assoc]⟩
    exact hCT.trans hT
  intro n
  induction n with
  | zero =>
      intro T S hC hT hcard
      have hS0 : S ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hC
        exact hC0 hC
      exact hfinish T S hC hT (hunit_of_card S hS0 (Nat.le_zero.1 hcard))
  | succ n ih =>
      intro T S hC hT hcard
      have hS0 : S ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hC
        exact hC0 hC
      by_cases hunit : IsUnit S
      · exact hfinish T S hC hT hunit
      obtain ⟨A, B, hSAB, hA, hTA⟩ := step T S hC hT hunit
      have hA0 : A ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hSAB
        exact hS0 hSAB
      have hB0 : B ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hSAB
        exact hS0 hSAB
      have hcards : (UniqueFactorizationMonoid.factors S).card =
          (UniqueFactorizationMonoid.factors A).card +
            (UniqueFactorizationMonoid.factors B).card := by
        have hrel := UniqueFactorizationMonoid.factors_mul (x := A) (y := B) hA0 hB0
        rw [hSAB]
        rw [Multiset.card_eq_card_of_rel hrel, Multiset.card_add]
      have hAcard : 1 ≤ (UniqueFactorizationMonoid.factors A).card := by
        by_contra hlt
        exact hA (hunit_of_card A hA0 (by omega))
      refine ih (T * A) B ?_ hTA (by omega)
      rw [hC, hSAB]
      ring

omit [Differential K] [CharZero K] in
/-- **Ritt's peeling, assembled.**  Suppose that at every stage -- a partial product `T` of factors
of `C` with `C = T * S` and `D = T * L` -- one can name the next factor `A` of `S` together with a
prime ideal that detects divisibility by `A` in low order, avoids `T`, contains `D`, and bounds the
running quotient's order.  Then `C` divides `D`.

The prime plays the role of the general component of `A`; stating it abstractly avoids naming the
residue field, which differs from factor to factor. -/
theorem dvd_of_peeling_prime {C D : DifferentialPolynomial Unit K} (hC0 : C ≠ 0)
    (H : ∀ T Lq S : DifferentialPolynomial Unit K, C = T * S → D = T * Lq → ¬ IsUnit S →
      ∃ (A B : DifferentialPolynomial Unit K) (P : Ideal (DifferentialPolynomial Unit K)),
        S = A * B ∧ ¬ IsUnit A ∧ P.IsPrime ∧
        (∀ Q : DifferentialPolynomial Unit K, Q ∈ P →
          scalarDifferentialPolynomialOrder Q ≤ scalarDifferentialPolynomialOrder A → A ∣ Q) ∧
        T ∉ P ∧ D ∈ P ∧
        scalarDifferentialPolynomialOrder Lq ≤ scalarDifferentialPolynomialOrder A) :
    C ∣ D := by
  refine dvd_of_peeling_loop hC0 ?_
  intro T S hC hTD hS
  obtain ⟨Lq, hLq⟩ := hTD
  obtain ⟨A, B, P, hSAB, hA, hPprime, hPdvd, hTnot, hDmem, hord⟩ := H T Lq S hC hLq hS
  refine ⟨A, B, hSAB, hA, ?_⟩
  have hLmem : Lq ∈ P := by
    refine (hPprime.mem_or_mem ?_).resolve_left hTnot
    rw [← hLq]
    exact hDmem
  obtain ⟨W, hW⟩ := hPdvd Lq hLmem hord
  exact ⟨W, by rw [hLq, hW]; ring⟩

omit [Differential K] [CharZero K] in
/-- **A generic point of the ordinary hypersurface exists.**  The residue field of the principal
prime provides one: evaluation there is the quotient map into the fraction field, so a polynomial
vanishes at the point exactly when the irreducible divides it. -/
theorem exists_generic_point_of_irreducible {A : DifferentialPolynomial Unit K}
    (hA : Irreducible A) :
    ∃ (M : Type u) (_ : Field M) (f : K →+* M) (x₀ : Unit × ℕ → M),
      MvPolynomial.eval₂ f x₀ A = 0 ∧
        ∀ R : DifferentialPolynomial Unit K, MvPolynomial.eval₂ f x₀ R = 0 → A ∣ R := by
  classical
  haveI hIprime : (Ideal.span ({A} : Set (DifferentialPolynomial Unit K))).IsPrime :=
    (Ideal.span_singleton_prime hA.ne_zero).mpr hA.prime
  haveI : IsDomain (DifferentialPolynomial Unit K ⧸
      Ideal.span ({A} : Set (DifferentialPolynomial Unit K))) :=
    (Ideal.Quotient.isDomain_iff_prime _).mpr hIprime
  set q : DifferentialPolynomial Unit K →+*
      DifferentialPolynomial Unit K ⧸ Ideal.span ({A} : Set (DifferentialPolynomial Unit K)) :=
    Ideal.Quotient.mk _ with hq
  set Φ : DifferentialPolynomial Unit K →+*
      FractionRing (DifferentialPolynomial Unit K ⧸
        Ideal.span ({A} : Set (DifferentialPolynomial Unit K))) :=
    (algebraMap _ _).comp q with hΦ
  have hcanonical : ∀ T : DifferentialPolynomial Unit K,
      MvPolynomial.eval₂ (Φ.comp MvPolynomial.C) (fun j => Φ (MvPolynomial.X j)) T = Φ T := by
    intro T
    have hring : MvPolynomial.eval₂Hom (Φ.comp MvPolynomial.C)
        (fun j => Φ (MvPolynomial.X j)) = Φ := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp
      · intro j
        simp
    exact RingHom.congr_fun hring T
  refine ⟨_, inferInstance, Φ.comp MvPolynomial.C, fun j => Φ (MvPolynomial.X j), ?_, ?_⟩
  · rw [hcanonical, hΦ, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self A), map_zero]
  · intro T hT
    rw [hcanonical, hΦ, RingHom.comp_apply] at hT
    have hq0 : q T = 0 :=
      IsFractionRing.injective _ (FractionRing _) (by rw [hT, map_zero])
    have hmem : T ∈ Ideal.span ({A} : Set (DifferentialPolynomial Unit K)) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hq0
    rwa [Ideal.mem_span_singleton] at hmem

/-- **The per-factor package.**  For an irreducible nonconstant differential polynomial there is a
prime ideal which contains its differential ideal, detects divisibility by it in low order, and
avoids its initial, its separant, and every non-associate irreducible of no larger order.

These are exactly the data `dvd_of_peeling_prime` consumes at each stage of Ritt's peeling. -/
theorem exists_component_prime_of_irreducible {A : DifferentialPolynomial Unit K}
    (hAvars : A.vars.Nonempty) (hA : Irreducible A) :
    ∃ P : Ideal (DifferentialPolynomial Unit K),
      P.IsPrime ∧
        differentialPolynomialIterateIdeal A ≤ P ∧
        (∀ Q : DifferentialPolynomial Unit K, Q ∈ P →
          scalarDifferentialPolynomialOrder Q ≤ scalarDifferentialPolynomialOrder A → A ∣ Q) ∧
        scalarDifferentialPolynomialInitial A ∉ P ∧
        scalarDifferentialPolynomialSeparant A ∉ P ∧
        ∀ B : DifferentialPolynomial Unit K, Irreducible B → ¬ Associated A B →
          scalarDifferentialPolynomialOrder B ≤ scalarDifferentialPolynomialOrder A → B ∉ P := by
  classical
  obtain ⟨M, _instM, f, x₀, hAeval, hx₀⟩ := exists_generic_point_of_irreducible hA
  have hSne : scalarDifferentialPolynomialSeparant A ≠ 0 :=
    scalarDifferentialPolynomialSeparant_ne_zero hAvars
  have hSeparant : MvPolynomial.eval₂ f x₀ (scalarDifferentialPolynomialSeparant A) ≠ 0 := by
    intro h0
    exact (irreducible_not_dvd_scalarDifferentialPolynomialSeparant hAvars hA) (hx₀ _ h0)
  refine ⟨generalComponent f A x₀, generalComponent_isPrime f A x₀,
    iterateIdeal_le_generalComponent f hAvars x₀ hAeval hSeparant,
    fun Q hQ hQorder => dvd_of_mem_generalComponent_of_order_le f x₀ hx₀ hQorder hQ,
    initial_not_mem_generalComponent f hAvars x₀ hx₀,
    separant_not_mem_generalComponent f hAvars hSne x₀ hx₀, ?_⟩
  intro B hB hnotassoc hBorder
  exact not_mem_generalComponent_of_irreducible f x₀ hx₀ hB hA.not_isUnit hnotassoc hBorder

end

end GaloisForLFunctions
