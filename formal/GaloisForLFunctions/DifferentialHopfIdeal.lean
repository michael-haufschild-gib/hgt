import GaloisForLFunctions.DifferentialPolynomial

/-!
# Scale-stable ideals in a differential polynomial Hopf algebra

This file begins the characteristic-zero Hopf-ideal argument behind the additive
differential-algebraic subgroup theorem. Folding additive comultiplication makes a Hopf ideal
stable under uniform doubling of all jet variables. The lemmas below extract the resulting grading
rigidity without assuming a finite jet index set.
-/

namespace GaloisForLFunctions

noncomputable section

/-- An ideal stable under uniformly doubling every formal jet. -/
def IsDifferentialPolynomialScaleTwoStable
    {ι C : Type*} [Field C] (I : Ideal (DifferentialPolynomial ι C)) : Prop :=
  ∀ ⦃P : DifferentialPolynomial ι C⦄,
    P ∈ I → differentialPolynomialScale (2 : C) P ∈ I

/-- A proper additive differential Hopf ideal, expressed in the doubled-variable polynomial model.
The first clause is the coideal law. The second is the counit law: every relation vanishes at the
additive identity. -/
def IsAdditiveDifferentialHopfIdeal
    {ι C : Type*} [Field C] (I : Ideal (DifferentialPolynomial ι C)) : Prop :=
  (∀ ⦃P : DifferentialPolynomial ι C⦄, P ∈ I →
      differentialAddComultiplication (C := C) P ∈
        Ideal.map (differentialPolynomialLeft (κ := ι) (C := C)).toRingHom I ⊔
        Ideal.map (differentialPolynomialRight (ι := ι) (C := C)).toRingHom I) ∧
    ∀ ⦃P : DifferentialPolynomial ι C⦄, P ∈ I → MvPolynomial.constantCoeff P = 0

/-- Folding the coideal law along the diagonal makes every additive Hopf ideal stable under
doubling. -/
theorem additiveDifferentialHopfIdeal_scaleTwoStable
    {ι C : Type*} [Field C] {I : Ideal (DifferentialPolynomial ι C)}
    (hI : IsAdditiveDifferentialHopfIdeal I) :
    IsDifferentialPolynomialScaleTwoStable I := by
  intro P hPI
  have hleft :
      Ideal.map (differentialPolynomialLeft (κ := ι) (C := C)).toRingHom I ≤
        Ideal.comap (differentialPolynomialFold (ι := ι) (C := C)).toRingHom I := by
    rw [Ideal.map_le_iff_le_comap]
    intro Q hQI
    change differentialPolynomialFold (differentialPolynomialLeft Q) ∈ I
    simpa [differentialPolynomialFold_left] using hQI
  have hright :
      Ideal.map (differentialPolynomialRight (ι := ι) (C := C)).toRingHom I ≤
        Ideal.comap (differentialPolynomialFold (ι := ι) (C := C)).toRingHom I := by
    rw [Ideal.map_le_iff_le_comap]
    intro Q hQI
    change differentialPolynomialFold (differentialPolynomialRight Q) ∈ I
    simpa [differentialPolynomialFold_right] using hQI
  have hcomap : differentialAddComultiplication (C := C) P ∈
      Ideal.comap (differentialPolynomialFold (ι := ι) (C := C)).toRingHom I :=
    (sup_le hleft hright) (hI.1 hPI)
  change differentialPolynomialFold (differentialAddComultiplication P) ∈ I at hcomap
  simpa [differentialPolynomialFold_comultiplication] using hcomap

/-- Subtracting the top scaling eigenvalue cancels every top-degree monomial. -/
theorem scale_two_sub_top_totalDegree_lt
    {ι C : Type*} [Field C] [CharZero C]
    (P : DifferentialPolynomial ι C)
    (hP0 : differentialPolynomialScale (2 : C) P -
      MvPolynomial.C ((2 : C) ^ P.totalDegree) * P ≠ 0) :
    (differentialPolynomialScale (2 : C) P -
      MvPolynomial.C ((2 : C) ^ P.totalDegree) * P).totalDegree < P.totalDegree := by
  classical
  let Q := differentialPolynomialScale (2 : C) P -
    MvPolynomial.C ((2 : C) ^ P.totalDegree) * P
  have hcoeffQ (s : (ι × ℕ) →₀ ℕ) :
      MvPolynomial.coeff s Q =
        MvPolynomial.coeff s P *
          ((2 : C) ^ (s.sum fun _ n => n) - (2 : C) ^ P.totalDegree) := by
    simp only [Q, MvPolynomial.coeff_sub, coeff_differentialPolynomialScale,
      MvPolynomial.coeff_C_mul]
    ring
  have hmono : ∀ s ∈ Q.support, s.sum (fun _ n => n) < P.totalDegree := by
    intro s hs
    have hsQ : MvPolynomial.coeff s Q ≠ 0 := MvPolynomial.mem_support_iff.mp hs
    have hsP : s ∈ P.support := by
      by_contra hsP
      have hc : MvPolynomial.coeff s P = 0 := by
        simpa [MvPolynomial.mem_support_iff] using hsP
      exact hsQ (by rw [hcoeffQ, hc, zero_mul])
    have hsle : s.sum (fun _ n => n) ≤ P.totalDegree := MvPolynomial.le_totalDegree hsP
    exact lt_of_le_of_ne hsle fun hEq => by
      apply hsQ
      rw [hcoeffQ, hEq, sub_self, mul_zero]
  obtain ⟨s, hs⟩ := (Finsupp.support_nonempty_iff.mpr hP0)
  have hDpos : 0 < P.totalDegree := lt_of_le_of_lt (Nat.zero_le _) (hmono s hs)
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hDpos]
  exact hmono

/-- A nonzero ideal element of minimal total degree in a doubling-stable ideal is homogeneous. -/
theorem minimal_totalDegree_mem_is_homogeneous
    {ι C : Type*} [Field C] [CharZero C]
    {I : Ideal (DifferentialPolynomial ι C)}
    (hscale : IsDifferentialPolynomialScaleTwoStable I)
    {P : DifferentialPolynomial ι C} (hPI : P ∈ I)
    (hmin : ∀ ⦃Q : DifferentialPolynomial ι C⦄, Q ∈ I → Q ≠ 0 →
      P.totalDegree ≤ Q.totalDegree) :
    ∀ ⦃s : (ι × ℕ) →₀ ℕ⦄, s ∈ P.support →
      s.sum (fun _ n => n) = P.totalDegree := by
  classical
  let D := P.totalDegree
  let Q := differentialPolynomialScale (2 : C) P -
    MvPolynomial.C ((2 : C) ^ D) * P
  have hQI : Q ∈ I := by
    apply I.sub_mem (hscale hPI)
    exact I.mul_mem_left _ hPI
  have hcoeffQ (s : (ι × ℕ) →₀ ℕ) :
      MvPolynomial.coeff s Q =
        MvPolynomial.coeff s P *
          ((2 : C) ^ (s.sum fun _ n => n) - (2 : C) ^ D) := by
    simp only [Q, MvPolynomial.coeff_sub, coeff_differentialPolynomialScale,
      MvPolynomial.coeff_C_mul]
    ring
  have hQ0 : Q = 0 := by
    by_contra hQ0
    have hDle : D ≤ Q.totalDegree := hmin hQI hQ0
    have hQlt : Q.totalDegree < D := scale_two_sub_top_totalDegree_lt P hQ0
    exact (not_lt_of_ge hDle) hQlt
  intro s hs
  have hc : MvPolynomial.coeff s P ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have hcoeffZero := congrArg (MvPolynomial.coeff s) hQ0
  rw [hcoeffQ, MvPolynomial.coeff_zero] at hcoeffZero
  have hpows : (2 : C) ^ (s.sum fun _ n => n) = (2 : C) ^ D := by
    exact sub_eq_zero.mp (mul_eq_zero.mp hcoeffZero |>.resolve_left hc)
  have hnat : 2 ^ (s.sum fun _ n => n) = 2 ^ D := by
    apply Nat.cast_injective (R := C)
    simpa using hpows
  exact Nat.pow_right_injective (by omega : 1 < 2) hnat

/-- If `P` realizes the least nonzero total degree of a doubling-stable ideal, then no polynomial
in the ideal contains a monomial of degree below `P.totalDegree`. This is the truncated gradedness
needed to extract a derivative from additive comultiplication. -/
theorem no_low_degree_support_of_minimal_scale_stable
    {ι C : Type*} [Field C] [CharZero C]
    {I : Ideal (DifferentialPolynomial ι C)}
    (hscale : IsDifferentialPolynomialScaleTwoStable I)
    {P : DifferentialPolynomial ι C}
    (hmin : ∀ ⦃Q : DifferentialPolynomial ι C⦄, Q ∈ I → Q ≠ 0 →
      P.totalDegree ≤ Q.totalDegree) :
    ∀ ⦃Q : DifferentialPolynomial ι C⦄, Q ∈ I →
      ∀ ⦃s : (ι × ℕ) →₀ ℕ⦄, s ∈ Q.support →
        P.totalDegree ≤ s.sum (fun _ n => n) := by
  classical
  intro Q hQI
  induction hE : Q.totalDegree using Nat.strong_induction_on generalizing Q with
  | h E ih =>
      intro s hs
      have hQ0 : Q ≠ 0 := fun h => by
        subst Q
        simp at hs
      have hDE : P.totalDegree ≤ E := by simpa [hE] using hmin hQI hQ0
      by_contra hlow
      have hes : s.sum (fun _ n => n) < P.totalDegree := Nat.lt_of_not_ge hlow
      let R := differentialPolynomialScale (2 : C) Q -
        MvPolynomial.C ((2 : C) ^ E) * Q
      have hRI : R ∈ I := by
        apply I.sub_mem (hscale hQI)
        exact I.mul_mem_left _ hQI
      have hcoeffR : MvPolynomial.coeff s R =
          MvPolynomial.coeff s Q *
            ((2 : C) ^ (s.sum fun _ n => n) - (2 : C) ^ E) := by
        simp only [R, MvPolynomial.coeff_sub, coeff_differentialPolynomialScale,
          MvPolynomial.coeff_C_mul]
        ring
      have hpowne : (2 : C) ^ (s.sum fun _ n => n) ≠ (2 : C) ^ E := by
        intro hpows
        have hnat : 2 ^ (s.sum fun _ n => n) = 2 ^ E := by
          apply Nat.cast_injective (R := C)
          simpa using hpows
        have heq := Nat.pow_right_injective (by omega : 1 < 2) hnat
        omega
      have hsR : s ∈ R.support := by
        rw [MvPolynomial.mem_support_iff, hcoeffR]
        exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hs) (sub_ne_zero.mpr hpowne)
      have hR0 : R ≠ 0 := fun h => by
        subst R
        simp at hsR
      have hRlt : R.totalDegree < E := by
        have hR0' : differentialPolynomialScale (2 : C) Q -
            MvPolynomial.C ((2 : C) ^ Q.totalDegree) * Q ≠ 0 := by
          simpa [R, hE] using hR0
        simpa [R, hE] using scale_two_sub_top_totalDegree_lt Q hR0'
      exact (not_le_of_gt hes) (ih R.totalDegree hRlt hRI rfl hsR)

end

end GaloisForLFunctions
