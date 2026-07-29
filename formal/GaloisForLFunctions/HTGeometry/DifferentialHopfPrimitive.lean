import GaloisForLFunctions.HTGeometry.DifferentialHopfIdeal
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Primitive extraction from additive differential Hopf ideals

For a nonzero additive differential Hopf ideal over a characteristic-zero field, choose a nonzero
relation of least total degree. Doubling stability makes it homogeneous. If its degree were at
least two, take a first derivative in one right-hand variable of additive comultiplication and then
evaluate all right variables at zero. The coideal and counit laws keep that derivative inside the
original ideal, but its degree is smaller and it is nonzero. Therefore the minimal relation has
degree one and is primitive.
-/

namespace GaloisForLFunctions
noncomputable section

def differentialPolynomialRightZero
    {ι C : Type*} [Field C] :
    DifferentialPolynomial (Sum ι ι) C →ₐ[C] DifferentialPolynomial ι C :=
  MvPolynomial.aeval fun p =>
    match p.1 with
    | Sum.inl i => MvPolynomial.X (i, p.2)
    | Sum.inr _ => 0

@[simp] theorem differentialPolynomialRightZero_X_left
    {ι C : Type*} [Field C] (i : ι) (n : ℕ) :
    differentialPolynomialRightZero (C := C) (MvPolynomial.X (Sum.inl i, n)) =
      MvPolynomial.X (i,n) := by simp [differentialPolynomialRightZero]

@[simp] theorem differentialPolynomialRightZero_X_right
    {ι C : Type*} [Field C] (i : ι) (n : ℕ) :
    differentialPolynomialRightZero (C := C) (MvPolynomial.X (Sum.inr i, n)) = 0 := by
  simp [differentialPolynomialRightZero]

def differentialPolynomialRightPartialAtZero
    {ι C : Type*} [Field C] (j : ι × ℕ) :
    DifferentialPolynomial (Sum ι ι) C →ₗ[C] DifferentialPolynomial ι C :=
  (differentialPolynomialRightZero (ι := ι) (C := C)).toLinearMap.comp
    (MvPolynomial.pderiv (Sum.inr j.1, j.2)).toLinearMap

theorem differentialPolynomialRightPartialAtZero_mul
    {ι C : Type*} [Field C] (j : ι × ℕ)
    (P Q : DifferentialPolynomial (Sum ι ι) C) :
    differentialPolynomialRightPartialAtZero j (P * Q) =
      differentialPolynomialRightPartialAtZero j P * differentialPolynomialRightZero Q +
      differentialPolynomialRightZero P * differentialPolynomialRightPartialAtZero j Q := by
  simp [differentialPolynomialRightPartialAtZero, map_add, map_mul]
  ring

theorem differentialPolynomialRightZero_left
    {ι C : Type*} [Field C] (P : DifferentialPolynomial ι C) :
    differentialPolynomialRightZero (C := C) (differentialPolynomialLeft (κ := ι) P) = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [differentialPolynomialRightZero]
  | add P Q hP hQ => simp [hP,hQ]
  | mul_X P p hP => rcases p with ⟨i,n⟩; simp [hP]

theorem differentialPolynomialRightPartialAtZero_left
    {ι C : Type*} [Field C] (j : ι × ℕ) (P : DifferentialPolynomial ι C) :
    differentialPolynomialRightPartialAtZero j (differentialPolynomialLeft (κ := ι) P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [differentialPolynomialRightPartialAtZero, differentialPolynomialLeft]
  | add P Q hP hQ => simp [hP,hQ]
  | mul_X P p hP =>
      rw [map_mul, differentialPolynomialRightPartialAtZero_mul, hP,
        differentialPolynomialRightZero_left]
      rcases p with ⟨i,n⟩
      simp [differentialPolynomialRightPartialAtZero, differentialPolynomialLeft]

theorem differentialPolynomialRightZero_right
    {ι C : Type*} [Field C] (P : DifferentialPolynomial ι C) :
    differentialPolynomialRightZero (C := C) (differentialPolynomialRight (ι := ι) P) =
      MvPolynomial.C (MvPolynomial.constantCoeff P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [differentialPolynomialRightZero]
  | add P Q hP hQ => simp [hP,hQ]
  | mul_X P p hP =>
      rcases p with ⟨i,n⟩
      simp [hP]

theorem differentialPolynomialRightPartialAtZero_right
    {ι C : Type*} [Field C] (j : ι × ℕ) (P : DifferentialPolynomial ι C) :
    differentialPolynomialRightPartialAtZero j (differentialPolynomialRight (ι := ι) P) =
      MvPolynomial.C (MvPolynomial.coeff (Finsupp.single j 1) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      classical
      have hne : (0 : (ι × ℕ) →₀ ℕ) ≠ Finsupp.single j 1 := by
        intro h
        have hj := congrArg (fun f : (ι × ℕ) →₀ ℕ => f j) h
        simp at hj
      simp [differentialPolynomialRightPartialAtZero, differentialPolynomialRight,
        MvPolynomial.coeff_C, hne]
  | add P Q hP hQ => simp [hP,hQ]
  | mul_X P p hP =>
      rw [map_mul, differentialPolynomialRightPartialAtZero_mul, hP,
        differentialPolynomialRightZero_right]
      rcases p with ⟨i,n⟩
      rw [differentialPolynomialRightZero_right]
      classical
      by_cases h : (i, n) = j
      · subst j
        simp [differentialPolynomialRightPartialAtZero, differentialPolynomialRight,
          MvPolynomial.pderiv_X, MvPolynomial.coeff_mul_X', MvPolynomial.constantCoeff_eq]
      · simp [differentialPolynomialRightPartialAtZero, differentialPolynomialRight,
          MvPolynomial.pderiv_X, MvPolynomial.coeff_mul_X', MvPolynomial.constantCoeff_eq,
          Pi.single_apply, h]
        intro hi hn
        exact (h (Prod.ext hi hn)).elim

theorem differentialPolynomialRightZero_comultiplication
    {ι C : Type*} [Field C] (P : DifferentialPolynomial ι C) :
    differentialPolynomialRightZero (C := C) (differentialAddComultiplication P) = P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [differentialPolynomialRightZero]
  | add P Q hP hQ => simp [hP,hQ]
  | mul_X P p hP => rcases p with ⟨i,n⟩; simp [hP]

@[simp] theorem differentialPolynomialRightPartialAtZero_comultiplication_X
    {ι C : Type*} [Field C] [DecidableEq ι] (j : ι × ℕ) (i : ι) (n : ℕ) :
    differentialPolynomialRightPartialAtZero j
        (differentialAddComultiplication (C := C) (MvPolynomial.X (i,n))) =
      if (i,n) = j then 1 else 0 := by
  simp [differentialPolynomialRightPartialAtZero, MvPolynomial.pderiv_X,
    Pi.single_apply]
  by_cases h : (i,n)=j
  · subst j
    simp
  · simp [h]
    intro hi hn
    exact (h (Prod.ext hi hn)).elim

theorem differentialPolynomialRightPartialAtZero_comultiplication
    {ι C : Type*} [Field C] (j : ι × ℕ) (P : DifferentialPolynomial ι C) :
    differentialPolynomialRightPartialAtZero j (differentialAddComultiplication P) =
      MvPolynomial.pderiv j P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [differentialPolynomialRightPartialAtZero]
  | add P Q hP hQ => simp [hP,hQ]
  | mul_X P p hP =>
      rw [map_mul, differentialPolynomialRightPartialAtZero_mul, hP,
        differentialPolynomialRightZero_comultiplication]
      rcases p with ⟨i,n⟩
      classical
      rw [differentialPolynomialRightPartialAtZero_comultiplication_X,
        differentialPolynomialRightZero_comultiplication]
      simp [MvPolynomial.pderiv_X, Pi.single_apply]
      ring

theorem coeff_X_mul_pderiv
    {σ C : Type*} [Field C] [CharZero C]
    (j : σ) (P : MvPolynomial σ C) (s : σ →₀ ℕ) :
    MvPolynomial.coeff s (MvPolynomial.X j * MvPolynomial.pderiv j P) =
      (s j : C) * MvPolynomial.coeff s P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ => simp [map_add, mul_add, hP, hQ, mul_add]
  | monomial m c =>
      rw [MvPolynomial.X_mul_pderiv_monomial]
      rw [MvPolynomial.coeff_smul, nsmul_eq_mul]
      simp [MvPolynomial.coeff_monomial]
      split_ifs with h
      · subst m
        ring
      · simp

theorem pderiv_ne_zero_of_mem_support
    {σ C : Type*} [Field C] [CharZero C]
    {P : MvPolynomial σ C} {s : σ →₀ ℕ} (hs : s ∈ P.support)
    {j : σ} (hj : j ∈ s.support) : MvPolynomial.pderiv j P ≠ 0 := by
  intro hzero
  have hcoeff := coeff_X_mul_pderiv j P s
  rw [hzero, mul_zero, MvPolynomial.coeff_zero] at hcoeff
  have hsj : (s j : C) ≠ 0 := by
    exact_mod_cast Finsupp.mem_support_iff.mp hj
  exact mul_ne_zero hsj (MvPolynomial.mem_support_iff.mp hs) hcoeff.symm

def differentialPolynomialFirstOrderVanishingIdeal
    {ι C : Type*} [Field C] (I : Ideal (DifferentialPolynomial ι C)) (j : ι × ℕ) :
    Ideal (DifferentialPolynomial (Sum ι ι) C) where
  carrier := {P | differentialPolynomialRightZero P ∈ I ∧
    differentialPolynomialRightPartialAtZero j P ∈ I}
  zero_mem' := by simp
  add_mem' {P Q} hP hQ := by
    constructor
    · simpa using I.add_mem hP.1 hQ.1
    · simpa using I.add_mem hP.2 hQ.2
  smul_mem' P Q hQ := by
    constructor
    · rw [smul_eq_mul, map_mul]
      exact I.mul_mem_left _ hQ.1
    · rw [smul_eq_mul, differentialPolynomialRightPartialAtZero_mul]
      exact I.add_mem (I.mul_mem_left _ hQ.1) (I.mul_mem_left _ hQ.2)

@[simp] theorem mem_differentialPolynomialFirstOrderVanishingIdeal
    {ι C : Type*} [Field C] {I : Ideal (DifferentialPolynomial ι C)} {j : ι × ℕ}
    {P : DifferentialPolynomial (Sum ι ι) C} :
    P ∈ differentialPolynomialFirstOrderVanishingIdeal I j ↔
      differentialPolynomialRightZero P ∈ I ∧
        differentialPolynomialRightPartialAtZero j P ∈ I := Iff.rfl

theorem additiveHopf_minimal_pderiv_mem
    {ι C : Type*} [Field C] [CharZero C]
    {I : Ideal (DifferentialPolynomial ι C)}
    (hHopf : IsAdditiveDifferentialHopfIdeal I)
    {P : DifferentialPolynomial ι C} (hPI : P ∈ I)
    (hmin : ∀ ⦃Q : DifferentialPolynomial ι C⦄, Q ∈ I → Q ≠ 0 →
      P.totalDegree ≤ Q.totalDegree)
    (hD : 2 ≤ P.totalDegree) (j : ι × ℕ) :
    MvPolynomial.pderiv j P ∈ I := by
  let J := differentialPolynomialFirstOrderVanishingIdeal I j
  have hleft :
      Ideal.map (differentialPolynomialLeft (κ := ι) (C := C)).toRingHom I ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro Q hQI
    change differentialPolynomialLeft Q ∈ J
    rw [mem_differentialPolynomialFirstOrderVanishingIdeal]
    rw [differentialPolynomialRightZero_left,
      differentialPolynomialRightPartialAtZero_left]
    exact ⟨hQI, I.zero_mem⟩
  have hright :
      Ideal.map (differentialPolynomialRight (ι := ι) (C := C)).toRingHom I ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro Q hQI
    change differentialPolynomialRight Q ∈ J
    rw [mem_differentialPolynomialFirstOrderVanishingIdeal,
      differentialPolynomialRightZero_right, differentialPolynomialRightPartialAtZero_right]
    constructor
    · rw [hHopf.2 hQI, map_zero]
      exact I.zero_mem
    · by_cases hc : MvPolynomial.coeff (Finsupp.single j 1) Q = 0
      · rw [hc, map_zero]
        exact I.zero_mem
      · exfalso
        have hs : Finsupp.single j 1 ∈ Q.support := MvPolynomial.mem_support_iff.mpr hc
        have hlow := no_low_degree_support_of_minimal_scale_stable
          (additiveDifferentialHopfIdeal_scaleTwoStable hHopf) hmin hQI hs
        simpa using (hD.trans hlow)
  have hDeltaJ : differentialAddComultiplication (C := C) P ∈ J :=
    (sup_le hleft hright) (hHopf.1 hPI)
  rw [← differentialPolynomialRightPartialAtZero_comultiplication j P]
  exact (mem_differentialPolynomialFirstOrderVanishingIdeal.mp hDeltaJ).2

theorem nonzero_additiveHopfIdeal_exists_nonzero_primitive
    {ι C : Type*} [Field C] [CharZero C]
    {I : Ideal (DifferentialPolynomial ι C)}
    (hHopf : IsAdditiveDifferentialHopfIdeal I) (hI : I ≠ ⊥) :
    ∃ P : DifferentialPolynomial ι C,
      P ∈ I ∧ P ≠ 0 ∧ IsPrimitiveDifferentialPolynomial P := by
  classical
  obtain ⟨P, hPI, hP0, hmin⟩ := Ideal.exists_minimal_totalDegree_ne_zero hI
  have hhom := minimal_totalDegree_mem_is_homogeneous
    (additiveDifferentialHopfIdeal_scaleTwoStable hHopf) hPI hmin
  have hDpos : 0 < P.totalDegree := by
    by_contra hD
    have hDz : P.totalDegree = 0 := Nat.eq_zero_of_not_pos hD
    have hPC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hDz
    have hc : MvPolynomial.coeff 0 P = 0 := by
      simpa [MvPolynomial.constantCoeff_eq] using hHopf.2 hPI
    apply hP0
    rw [hPC, hc, map_zero]
  rcases (show P.totalDegree = 1 ∨ 2 ≤ P.totalDegree by omega) with hD1 | hD2
  · refine ⟨P, hPI, hP0, isPrimitive_of_support_degree_eq_one ?_⟩
    intro s hs
    simpa [hD1] using hhom hs
  · exfalso
    obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hP0
    have hsdeg : s.sum (fun _ n => n) = P.totalDegree := hhom hs
    have hssupp : s.support.Nonempty := by
      by_contra hs0
      have : s = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hs0)
      subst s
      simp at hsdeg
      omega
    obtain ⟨j, hj⟩ := hssupp
    have hpI : MvPolynomial.pderiv j P ∈ I :=
      additiveHopf_minimal_pderiv_mem hHopf hPI hmin hD2 j
    have hp0 : MvPolynomial.pderiv j P ≠ 0 := pderiv_ne_zero_of_mem_support hs hj
    have hHom : P.IsHomogeneous P.totalDegree := by
      intro m hm
      have hm' : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hm
      simpa [MvPolynomial.IsHomogeneous, MvPolynomial.IsWeightedHomogeneous,
        Finsupp.weight_apply] using hhom hm'
    have hpHom := hHom.pderiv (i := j)
    have hpdeg : (MvPolynomial.pderiv j P).totalDegree = P.totalDegree - 1 :=
      hpHom.totalDegree hp0
    have hcontra := hmin hpI hp0
    rw [hpdeg] at hcontra
    omega

/-- Coordinate-ideal form of the characteristic-zero additive subgroup theorem: every nonzero
additive differential Hopf ideal contains a nonzero relation which is an explicit finite
constant-coefficient linear combination of formal jets. -/
theorem nonzero_additiveHopfIdeal_exists_finite_jet_linear_relation
    {ι C : Type*} [Field C] [CharZero C]
    {I : Ideal (DifferentialPolynomial ι C)}
    (hHopf : IsAdditiveDifferentialHopfIdeal I) (hI : I ≠ ⊥) :
    ∃ P : DifferentialPolynomial ι C,
      P ∈ I ∧ P ≠ 0 ∧
        ∃ j : (↥P.support) → (ι × ℕ),
          P = ∑ s ∈ (Finset.univ : Finset ↥P.support),
            MvPolynomial.C (MvPolynomial.coeff s.1 P) * MvPolynomial.X (j s) := by
  obtain ⟨P, hPI, hP0, hPprimitive⟩ :=
    nonzero_additiveHopfIdeal_exists_nonzero_primitive hHopf hI
  obtain ⟨j, hj⟩ := primitive_eq_finite_jet_linear_sum hPprimitive
  exact ⟨P, hPI, hP0, j, hj⟩

end
end GaloisForLFunctions
