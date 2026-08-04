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

variable {K L : Type*} [Field K] [Differential K] [CharZero K] [Field L]

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

end

end GaloisForLFunctions
