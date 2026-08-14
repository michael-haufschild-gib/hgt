import GaloisForLFunctions.HTGeometry.DifferentialHopfPrimitive
import GaloisForLFunctions.HTGeometry.SymmetricHopfPrimitive

/-!
# Primitive extraction from ordinary additive Hopf ideals

For an arbitrary variable type, a nonzero characteristic-zero additive Hopf ideal in a
multivariable polynomial algebra contains a nonzero degree-one relation.  This generalizes the
jet-specific minimal-degree derivative argument to ordinary polynomial coordinates.
-/

namespace GaloisForLFunctions.HTGeometry
namespace AdditivePolynomialHopf

noncomputable section

variable {σ k : Type*} [Field k]

def left : MvPolynomial σ k →ₐ[k] MvPolynomial (Sum σ σ) k :=
  MvPolynomial.rename Sum.inl

def right : MvPolynomial σ k →ₐ[k] MvPolynomial (Sum σ σ) k :=
  MvPolynomial.rename Sum.inr

def addComul : MvPolynomial σ k →ₐ[k] MvPolynomial (Sum σ σ) k :=
  MvPolynomial.aeval fun i => MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i)

def fold : MvPolynomial (Sum σ σ) k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval fun p => MvPolynomial.X (Sum.elim id id p)

def rightZero : MvPolynomial (Sum σ σ) k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval fun p => Sum.elim MvPolynomial.X (fun _ => 0) p

def rightPartialAtZero (j : σ) :
    MvPolynomial (Sum σ σ) k →ₗ[k] MvPolynomial σ k :=
  rightZero.toLinearMap.comp (MvPolynomial.pderiv (Sum.inr j)).toLinearMap

@[simp] theorem rightPartialAtZero_X_left (j i : σ) :
    rightPartialAtZero (k := k) j (MvPolynomial.X (Sum.inl i)) = 0 := by
  simp [rightPartialAtZero, rightZero]

@[simp] theorem rightPartialAtZero_X_right [DecidableEq σ] (j i : σ) :
    rightPartialAtZero (k := k) j (MvPolynomial.X (Sum.inr i)) =
      if i = j then 1 else 0 := by
  simp [rightPartialAtZero, rightZero]
  by_cases h : i = j
  · subst i
    simp
  · simp [h]

@[simp] theorem left_X (i : σ) : left (k := k) (MvPolynomial.X i) =
    MvPolynomial.X (Sum.inl i) := by simp [left]

@[simp] theorem right_X (i : σ) : right (k := k) (MvPolynomial.X i) =
    MvPolynomial.X (Sum.inr i) := by simp [right]

@[simp] theorem addComul_X (i : σ) : addComul (k := k) (MvPolynomial.X i) =
    MvPolynomial.X (Sum.inl i) + MvPolynomial.X (Sum.inr i) := by simp [addComul]

@[simp] theorem fold_left (P : MvPolynomial σ k) : fold (left P) = P := by
  have h : (fold (k := k)).comp left = AlgHom.id k (MvPolynomial σ k) := by
    ext i
    simp [fold, left]
  exact DFunLike.congr_fun h P

@[simp] theorem fold_right (P : MvPolynomial σ k) : fold (right P) = P := by
  have h : (fold (k := k)).comp right = AlgHom.id k (MvPolynomial σ k) := by
    ext i
    simp [fold, right]
  exact DFunLike.congr_fun h P

@[simp] theorem fold_addComul (P : MvPolynomial σ k) :
    fold (addComul P) = SymmetricPrimitive.mvScale (2 : k) P := by
  have h : (fold (σ := σ) (k := k)).comp (addComul (σ := σ) (k := k)) =
      SymmetricPrimitive.mvScale (ι := σ) (2 : k) := by
    ext i
    simp [fold, addComul, SymmetricPrimitive.mvScale]
    ring
  exact DFunLike.congr_fun h P

@[simp] theorem rightZero_left (P : MvPolynomial σ k) : rightZero (left P) = P := by
  have h : (rightZero (k := k)).comp left = AlgHom.id k (MvPolynomial σ k) := by
    ext i
    simp [rightZero, left]
  exact DFunLike.congr_fun h P

@[simp] theorem rightZero_right (P : MvPolynomial σ k) :
    rightZero (right P) = MvPolynomial.C (MvPolynomial.constantCoeff P) := by
  have h : (rightZero (σ := σ) (k := k)).comp (right (σ := σ) (k := k)) =
      MvPolynomial.aeval (fun _ : σ => (0 : MvPolynomial σ k)) := by
    ext i
    simp [rightZero, right]
  have hp := DFunLike.congr_fun h P
  change rightZero (right P) =
    (MvPolynomial.aeval fun _ : σ => (0 : MvPolynomial σ k)) P at hp
  have heval (Q : MvPolynomial σ k) :
      (MvPolynomial.aeval fun _ : σ => (0 : MvPolynomial σ k)) Q =
        MvPolynomial.C (MvPolynomial.constantCoeff Q) := by
    induction Q using MvPolynomial.induction_on with
    | C c => simp
    | add Q R hQ hR =>
      rw [map_add, map_add, hQ, hR]
      rw [map_add]
    | mul_X Q i hQ =>
      rw [map_mul]
      simp
  exact hp.trans (heval P)

@[simp] theorem rightZero_addComul (P : MvPolynomial σ k) : rightZero (addComul P) = P := by
  have h : (rightZero (k := k)).comp addComul = AlgHom.id k (MvPolynomial σ k) := by
    ext i
    simp [rightZero, addComul]
  exact DFunLike.congr_fun h P

theorem rightPartialAtZero_mul (j : σ) (P Q : MvPolynomial (Sum σ σ) k) :
    rightPartialAtZero j (P * Q) =
      rightPartialAtZero j P * rightZero Q + rightZero P * rightPartialAtZero j Q := by
  simp [rightPartialAtZero, map_add, map_mul]
  ring

@[simp] theorem rightPartialAtZero_left (j : σ) (P : MvPolynomial σ k) :
    rightPartialAtZero j (left P) = 0 := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [rightPartialAtZero, left, rightZero]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, rightPartialAtZero_mul, hP, rightZero_left, left_X,
        rightPartialAtZero_X_left]
      simp

@[simp] theorem rightPartialAtZero_right (j : σ) (P : MvPolynomial σ k) :
    rightPartialAtZero j (right P) =
      MvPolynomial.C (MvPolynomial.coeff (Finsupp.single j 1) P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      classical
      have hne : (0 : σ →₀ ℕ) ≠ Finsupp.single j 1 := by
        intro h
        have hj := congrArg (fun f : σ →₀ ℕ => f j) h
        simp at hj
      simp [rightPartialAtZero, right, rightZero, MvPolynomial.coeff_C, hne]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      classical
      rw [map_mul, rightPartialAtZero_mul, hP, rightZero_right]
      rw [right_X, rightPartialAtZero_X_right]
      rw [rightZero_right]
      by_cases h : i = j
      · subst j
        simp [MvPolynomial.coeff_mul_X', MvPolynomial.constantCoeff_eq]
      · simp [MvPolynomial.coeff_mul_X', h]

@[simp] theorem rightPartialAtZero_addComul (j : σ) (P : MvPolynomial σ k) :
    rightPartialAtZero j (addComul P) = MvPolynomial.pderiv j P := by
  classical
  induction P using MvPolynomial.induction_on with
  | C c => simp [rightPartialAtZero, addComul, rightZero]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, rightPartialAtZero_mul, hP, rightZero_addComul]
      rw [addComul_X]
      by_cases h : i = j
      · subst i
        simp [rightPartialAtZero_X_left, rightPartialAtZero_X_right,
          rightZero_addComul, MvPolynomial.pderiv_X]
        ring
      · simp [h, rightPartialAtZero_X_left, rightPartialAtZero_X_right,
          rightZero_addComul, MvPolynomial.pderiv_X]
        ring

def IsAdditiveHopfIdeal (I : Ideal (MvPolynomial σ k)) : Prop :=
  (∀ ⦃P : MvPolynomial σ k⦄, P ∈ I → addComul P ∈
      Ideal.map left.toRingHom I ⊔ Ideal.map right.toRingHom I) ∧
    ∀ ⦃P : MvPolynomial σ k⦄, P ∈ I → MvPolynomial.constantCoeff P = 0

def IsScaleTwoStable (I : Ideal (MvPolynomial σ k)) : Prop :=
  ∀ ⦃P : MvPolynomial σ k⦄, P ∈ I → SymmetricPrimitive.mvScale (2 : k) P ∈ I

theorem scaleTwoStable {I : Ideal (MvPolynomial σ k)} (hI : IsAdditiveHopfIdeal I) :
    IsScaleTwoStable I := by
  intro P hPI
  have hleft : Ideal.map left.toRingHom I ≤ Ideal.comap fold.toRingHom I := by
    rw [Ideal.map_le_iff_le_comap]
    intro Q hQ
    change fold (left Q) ∈ I
    simpa using hQ
  have hright : Ideal.map right.toRingHom I ≤ Ideal.comap fold.toRingHom I := by
    rw [Ideal.map_le_iff_le_comap]
    intro Q hQ
    change fold (right Q) ∈ I
    simpa using hQ
  have h := (sup_le hleft hright) (hI.1 hPI)
  change fold (addComul P) ∈ I at h
  simpa using h

theorem scale_two_sub_top_totalDegree_lt [CharZero k]
    (P : MvPolynomial σ k)
    (hP0 : SymmetricPrimitive.mvScale (2 : k) P -
      MvPolynomial.C ((2 : k) ^ P.totalDegree) * P ≠ 0) :
    (SymmetricPrimitive.mvScale (2 : k) P -
      MvPolynomial.C ((2 : k) ^ P.totalDegree) * P).totalDegree < P.totalDegree := by
  classical
  let Q := SymmetricPrimitive.mvScale (2 : k) P -
    MvPolynomial.C ((2 : k) ^ P.totalDegree) * P
  have hcoeffQ (s : σ →₀ ℕ) :
      MvPolynomial.coeff s Q = MvPolynomial.coeff s P *
        ((2 : k) ^ (s.sum fun _ n => n) - (2 : k) ^ P.totalDegree) := by
    simp only [Q, MvPolynomial.coeff_sub, SymmetricPrimitive.coeff_mvScale,
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
    have hsle := MvPolynomial.le_totalDegree hsP
    exact lt_of_le_of_ne hsle fun hEq => by
      apply hsQ
      rw [hcoeffQ, hEq, sub_self, mul_zero]
  obtain ⟨s, hs⟩ := MvPolynomial.support_nonempty.mpr hP0
  have hDpos : 0 < P.totalDegree := lt_of_le_of_lt (Nat.zero_le _) (hmono s hs)
  rw [MvPolynomial.totalDegree, Finset.sup_lt_iff hDpos]
  exact hmono

theorem minimal_mem_is_homogeneous [CharZero k]
    {I : Ideal (MvPolynomial σ k)} (hscale : IsScaleTwoStable I)
    {P : MvPolynomial σ k} (hPI : P ∈ I)
    (hmin : ∀ ⦃Q : MvPolynomial σ k⦄, Q ∈ I → Q ≠ 0 →
      P.totalDegree ≤ Q.totalDegree) :
    ∀ ⦃s : σ →₀ ℕ⦄, s ∈ P.support →
      s.sum (fun _ n => n) = P.totalDegree := by
  classical
  let D := P.totalDegree
  let Q := SymmetricPrimitive.mvScale (2 : k) P - MvPolynomial.C ((2 : k) ^ D) * P
  have hQI : Q ∈ I := I.sub_mem (hscale hPI) (I.mul_mem_left _ hPI)
  have hcoeffQ (s : σ →₀ ℕ) :
      MvPolynomial.coeff s Q = MvPolynomial.coeff s P *
        ((2 : k) ^ (s.sum fun _ n => n) - (2 : k) ^ D) := by
    simp only [Q, MvPolynomial.coeff_sub, SymmetricPrimitive.coeff_mvScale,
      MvPolynomial.coeff_C_mul]
    ring
  have hQ0 : Q = 0 := by
    by_contra hQ0
    exact (not_lt_of_ge (hmin hQI hQ0)) (scale_two_sub_top_totalDegree_lt P hQ0)
  intro s hs
  have hc : MvPolynomial.coeff s P ≠ 0 := MvPolynomial.mem_support_iff.mp hs
  have hz := congrArg (MvPolynomial.coeff s) hQ0
  rw [hcoeffQ, MvPolynomial.coeff_zero] at hz
  have hpows : (2 : k) ^ (s.sum fun _ n => n) = (2 : k) ^ D := by
    exact sub_eq_zero.mp (mul_eq_zero.mp hz |>.resolve_left hc)
  have hnat : 2 ^ (s.sum fun _ n => n) = 2 ^ D := by
    apply Nat.cast_injective (R := k)
    simpa using hpows
  exact Nat.pow_right_injective (by omega : 1 < 2) hnat

theorem no_low_degree_support_of_minimal [CharZero k]
    {I : Ideal (MvPolynomial σ k)} (hscale : IsScaleTwoStable I)
    {P : MvPolynomial σ k}
    (hmin : ∀ ⦃Q : MvPolynomial σ k⦄, Q ∈ I → Q ≠ 0 →
      P.totalDegree ≤ Q.totalDegree) :
    ∀ ⦃Q : MvPolynomial σ k⦄, Q ∈ I →
      ∀ ⦃s : σ →₀ ℕ⦄, s ∈ Q.support →
        P.totalDegree ≤ s.sum (fun _ n => n) := by
  classical
  intro Q hQI
  induction hE : Q.totalDegree using Nat.strong_induction_on generalizing Q with
  | h E ih =>
      intro s hs
      have hQ0 : Q ≠ 0 := fun h => by
        have hc := MvPolynomial.mem_support_iff.mp hs
        rw [h, MvPolynomial.coeff_zero] at hc
        exact hc rfl
      have hDE : P.totalDegree ≤ E := by simpa [hE] using hmin hQI hQ0
      by_contra hlow
      have hes : s.sum (fun _ n => n) < P.totalDegree := Nat.lt_of_not_ge hlow
      let R := SymmetricPrimitive.mvScale (2 : k) Q -
        MvPolynomial.C ((2 : k) ^ E) * Q
      have hRI : R ∈ I := I.sub_mem (hscale hQI) (I.mul_mem_left _ hQI)
      have hcoeffR : MvPolynomial.coeff s R = MvPolynomial.coeff s Q *
          ((2 : k) ^ (s.sum fun _ n => n) - (2 : k) ^ E) := by
        simp only [R, MvPolynomial.coeff_sub, SymmetricPrimitive.coeff_mvScale,
          MvPolynomial.coeff_C_mul]
        ring
      have hpowne : (2 : k) ^ (s.sum fun _ n => n) ≠ (2 : k) ^ E := by
        intro hpows
        have hnat : 2 ^ (s.sum fun _ n => n) = 2 ^ E := by
          apply Nat.cast_injective (R := k)
          simpa using hpows
        have heq := Nat.pow_right_injective (by omega : 1 < 2) hnat
        omega
      have hsR : s ∈ R.support := by
        rw [MvPolynomial.mem_support_iff, hcoeffR]
        exact mul_ne_zero (MvPolynomial.mem_support_iff.mp hs) (sub_ne_zero.mpr hpowne)
      have hR0 : R ≠ 0 := fun h => by
        have hc := MvPolynomial.mem_support_iff.mp hsR
        rw [h, MvPolynomial.coeff_zero] at hc
        exact hc rfl
      have hRlt : R.totalDegree < E := by
        have hR0' : SymmetricPrimitive.mvScale (2 : k) Q -
            MvPolynomial.C ((2 : k) ^ Q.totalDegree) * Q ≠ 0 := by
          simpa [R, hE] using hR0
        simpa [R, hE] using scale_two_sub_top_totalDegree_lt Q hR0'
      exact (not_le_of_gt hes) (ih R.totalDegree hRlt hRI rfl hsR)

theorem exists_minimal_totalDegree_ne_zero {I : Ideal (MvPolynomial σ k)} (hI : I ≠ ⊥) :
    ∃ P : MvPolynomial σ k, P ∈ I ∧ P ≠ 0 ∧
      ∀ ⦃Q : MvPolynomial σ k⦄, Q ∈ I → Q ≠ 0 →
        P.totalDegree ≤ Q.totalDegree := by
  classical
  have hexP : ∃ P : MvPolynomial σ k, P ∈ I ∧ P ≠ 0 := by
    by_contra h
    apply hI
    ext P
    simp only [Ideal.mem_bot]
    constructor
    · intro hPI
      by_contra hP0
      exact h ⟨P, hPI, hP0⟩
    · rintro rfl
      exact I.zero_mem
  have hexD : ∃ d : ℕ, ∃ P : MvPolynomial σ k,
      P ∈ I ∧ P ≠ 0 ∧ P.totalDegree = d := by
    obtain ⟨P, hPI, hP0⟩ := hexP
    exact ⟨P.totalDegree, P, hPI, hP0, rfl⟩
  obtain ⟨P, hPI, hP0, hPd⟩ := Nat.find_spec hexD
  refine ⟨P, hPI, hP0, ?_⟩
  intro Q hQI hQ0
  rw [hPd]
  exact Nat.find_min' hexD ⟨Q, hQI, hQ0, rfl⟩

def firstOrderVanishingIdeal (I : Ideal (MvPolynomial σ k)) (j : σ) :
    Ideal (MvPolynomial (Sum σ σ) k) where
  carrier := {P | rightZero P ∈ I ∧ rightPartialAtZero j P ∈ I}
  zero_mem' := by simp
  add_mem' {P Q} hP hQ := ⟨by simpa using I.add_mem hP.1 hQ.1,
    by simpa using I.add_mem hP.2 hQ.2⟩
  smul_mem' P Q hQ := by
    constructor
    · rw [smul_eq_mul, map_mul]
      exact I.mul_mem_left _ hQ.1
    · rw [smul_eq_mul, rightPartialAtZero_mul]
      exact I.add_mem (I.mul_mem_left _ hQ.1) (I.mul_mem_left _ hQ.2)

theorem minimal_pderiv_mem [CharZero k]
    {I : Ideal (MvPolynomial σ k)} (hHopf : IsAdditiveHopfIdeal I)
    {P : MvPolynomial σ k} (hPI : P ∈ I)
    (hmin : ∀ ⦃Q : MvPolynomial σ k⦄, Q ∈ I → Q ≠ 0 →
      P.totalDegree ≤ Q.totalDegree)
    (hD : 2 ≤ P.totalDegree) (j : σ) : MvPolynomial.pderiv j P ∈ I := by
  let J := firstOrderVanishingIdeal I j
  have hleft : Ideal.map left.toRingHom I ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro Q hQI
    change left Q ∈ J
    exact ⟨by simpa using hQI, by simp⟩
  have hright : Ideal.map right.toRingHom I ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro Q hQI
    change right Q ∈ J
    constructor
    · rw [rightZero_right, hHopf.2 hQI, map_zero]
      exact I.zero_mem
    · rw [rightPartialAtZero_right]
      by_cases hc : MvPolynomial.coeff (Finsupp.single j 1) Q = 0
      · rw [hc, map_zero]
        exact I.zero_mem
      · exfalso
        have hs : Finsupp.single j 1 ∈ Q.support := MvPolynomial.mem_support_iff.mpr hc
        have hlow := no_low_degree_support_of_minimal (scaleTwoStable hHopf) hmin hQI hs
        simpa using (hD.trans hlow)
  have hDelta : addComul P ∈ J := (sup_le hleft hright) (hHopf.1 hPI)
  rw [← rightPartialAtZero_addComul j P]
  exact hDelta.2

/-- Every nonzero ordinary additive Hopf ideal contains a nonzero degree-one polynomial. -/
theorem nonzero_exists_degree_one [CharZero k]
    {I : Ideal (MvPolynomial σ k)} (hHopf : IsAdditiveHopfIdeal I) (hI : I ≠ ⊥) :
    ∃ P : MvPolynomial σ k, P ∈ I ∧ P ≠ 0 ∧
      ∀ ⦃s : σ →₀ ℕ⦄, s ∈ P.support → s.sum (fun _ n => n) = 1 := by
  classical
  obtain ⟨P, hPI, hP0, hmin⟩ := exists_minimal_totalDegree_ne_zero hI
  have hhom := minimal_mem_is_homogeneous (scaleTwoStable hHopf) hPI hmin
  have hDpos : 0 < P.totalDegree := by
    by_contra hD
    have hDz : P.totalDegree = 0 := Nat.eq_zero_of_not_pos hD
    have hPC := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hDz
    have hc : MvPolynomial.coeff 0 P = 0 := by
      simpa [MvPolynomial.constantCoeff_eq] using hHopf.2 hPI
    apply hP0
    rw [hPC, hc, map_zero]
  rcases (show P.totalDegree = 1 ∨ 2 ≤ P.totalDegree by omega) with hD1 | hD2
  · exact ⟨P, hPI, hP0, fun s hs => by simpa [hD1] using hhom hs⟩
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
    have hpI := minimal_pderiv_mem hHopf hPI hmin hD2 j
    have hp0 : MvPolynomial.pderiv j P ≠ 0 :=
      GaloisForLFunctions.pderiv_ne_zero_of_mem_support hs hj
    have hHom : P.IsHomogeneous P.totalDegree := by
      intro m hm
      have hm' : m ∈ P.support := MvPolynomial.mem_support_iff.mpr hm
      simpa [MvPolynomial.IsHomogeneous, MvPolynomial.IsWeightedHomogeneous,
        Finsupp.weight_apply] using hhom hm'
    have hpHom := hHom.pderiv (i := j)
    have hpdeg : (MvPolynomial.pderiv j P).totalDegree = P.totalDegree - 1 := hpHom.totalDegree hp0
    have hcontra := hmin hpI hp0
    rw [hpdeg] at hcontra
    omega

end
end AdditivePolynomialHopf
end GaloisForLFunctions.HTGeometry

