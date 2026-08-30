import GaloisForLFunctions.HTGeometry.DifferentialTangentSubmodule

/-!
# A differential-algebraic set with everywhere-full tangent space is Kolchin-dense

Over a differential field admitting no universal linear jet relation, the vanishing ideal of a set
of points whose tangent space is the whole ambient space at every one of its points is closed under
every partial derivative: the linearisation at a point of the set annihilates every perturbation, so
each partial derivative of a vanishing polynomial vanishes on the set again.

In characteristic zero an ideal of that kind cannot contain a nonzero element — differentiating
lowers the total degree, and a variable-free polynomial vanishing at one point of the set is zero.
This is the characteristic-zero mechanism behind Cartier's theorem, carried out in the free
differential polynomial ring and with no smoothness or dimension theory.

* `totalDegree_pderiv_lt`, `exists_pderiv_ne_zero`;
* `NoUniversalJetRelation`;
* `pderiv_mem_vanishing_of_full_tangent`;
* `eq_zero_of_vanishing_of_full_tangent` — **the vanishing ideal is zero.**
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

/-! ### Differentiating lowers the total degree -/

private theorem totalDegree_pderiv_lt {σ R : Type*} [CommRing R] {Q : MvPolynomial σ R} {i : σ}
    (h : MvPolynomial.pderiv i Q ≠ 0) :
    (MvPolynomial.pderiv i Q).totalDegree < Q.totalDegree := by
  classical
  have hsucc : ∀ m ∈ (MvPolynomial.pderiv i Q).support,
      (m.sum fun _ e => e) + 1 ≤ Q.totalDegree := by
    intro m hm
    have hcoeff : MvPolynomial.coeff m (MvPolynomial.pderiv i Q) ≠ 0 :=
      MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv] at hcoeff
    have hQm : MvPolynomial.coeff (m + Finsupp.single i 1) Q ≠ 0 := by
      intro hz; exact hcoeff (by rw [hz, zero_mul])
    have hmem : m + Finsupp.single i 1 ∈ Q.support := MvPolynomial.mem_support_iff.mpr hQm
    have hle := MvPolynomial.le_totalDegree hmem
    have hsum : ((m + Finsupp.single i 1).sum fun _ e => e) = (m.sum fun _ e => e) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    rwa [hsum] at hle
  have hne : (MvPolynomial.pderiv i Q).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hcon
    exact h (MvPolynomial.support_eq_empty.mp hcon)
  obtain ⟨m, hm⟩ := hne
  have hpos : 0 < Q.totalDegree := lt_of_lt_of_le (Nat.succ_pos _) (hsucc m hm)
  refine (Finset.sup_lt_iff hpos).mpr fun n hn => ?_
  exact Nat.lt_of_succ_le (hsucc n hn)

/-- In characteristic zero a polynomial of positive total degree has a nonzero partial
derivative. -/
private theorem exists_pderiv_ne_zero {σ R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    {Q : MvPolynomial σ R} (h : Q.totalDegree ≠ 0) :
    ∃ i : σ, MvPolynomial.pderiv i Q ≠ 0 := by
  classical
  rw [Ne, MvPolynomial.totalDegree_eq_zero_iff] at h
  push Not at h
  obtain ⟨m, hm, i, hi⟩ := h
  refine ⟨i, ?_⟩
  intro hzero
  have hcoeff := MvPolynomial.coeff_pderiv (i := i) Q (m - Finsupp.single i 1)
  rw [hzero] at hcoeff
  have hadd : (m - Finsupp.single i 1) + Finsupp.single i 1 = m := by
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [hj]
  have hnat : ((m - Finsupp.single i 1 : σ →₀ ℕ) i) + 1 = m i := by simp; omega
  have hval : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : R) + 1 = ((m i : ℕ) : R) := by
    exact_mod_cast hnat
  rw [hadd, hval] at hcoeff
  have hQm : MvPolynomial.coeff m Q ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hmi : ((m i : R)) ≠ 0 := Nat.cast_ne_zero.mpr hi
  simp only [MvPolynomial.coeff_zero] at hcoeff
  exact (mul_ne_zero hQm hmi) hcoeff.symm

/-! ### No universal linear jet relation -/

variable (C : Type*) [Field C] [Differential C]

/-- A differential field in which no nonzero linear jet relation holds for every element.  It fails
exactly when the field is finite-dimensional over its constants. -/
def NoUniversalJetRelation : Prop :=
  ∀ (s : Finset ℕ) (c : ℕ → C), (∀ x : C, ∑ k ∈ s, c k * differentialJet k x = 0) →
    ∀ k ∈ s, c k = 0

variable {C}

/-! ### Closure of the vanishing ideal under partial derivatives -/

variable {ι : Type*}

/-- Restricting the linearisation to a single differential indeterminate. -/
theorem linearisationForm_single [DecidableEq ι] (p : ι → C)
    (Q : DifferentialPolynomial ι C) (i : ι) (x : C) :
    linearisationForm p Q Q.vars (fun j => if j = i then x else 0)
      = ∑ k ∈ (Q.vars.filter fun w => w.1 = i).image Prod.snd,
          differentialPolynomialEvalOver (K := C) p
            (MvPolynomial.pderiv (i, k) Q) * differentialJet k x := by
  rw [linearisationForm, ← Finset.sum_filter_add_sum_filter_not (Q.vars) (fun w => w.1 = i)]
  have hzero : ∑ w ∈ Q.vars.filter (fun w => ¬ w.1 = i),
      differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv w Q)
        * differentialJet w.2 (if w.1 = i then x else 0) = 0 := by
    refine Finset.sum_eq_zero fun w hw => ?_
    rw [if_neg (Finset.mem_filter.mp hw).2, differentialJet_eq_zero_zero, mul_zero]
  rw [hzero, add_zero]
  have hstep : ∀ w ∈ Q.vars.filter (fun w => w.1 = i),
      differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv w Q)
          * differentialJet w.2 (if w.1 = i then x else 0)
        = differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv (i, w.2) Q)
          * differentialJet w.2 x := by
    intro w hw
    have hw1 : w.1 = i := (Finset.mem_filter.mp hw).2
    have hwe : w = (i, w.2) := by simp [Prod.ext_iff, hw1]
    rw [if_pos hw1, ← hwe]
  rw [Finset.sum_congr rfl hstep]
  refine (Finset.sum_image (s := Q.vars.filter fun w => w.1 = i) (g := Prod.snd)
    (f := fun k => differentialPolynomialEvalOver (K := C) p
      (MvPolynomial.pderiv (i, k) Q) * differentialJet k x) ?_).symm
  intro a ha b hb hab
  have ha1 : a.1 = i := (Finset.mem_filter.mp ha).2
  have hb1 : b.1 = i := (Finset.mem_filter.mp hb).2
  simp [Prod.ext_iff, ha1, hb1, hab]

/-- **The vanishing ideal of a set with full tangent space is closed under partial
derivatives.** -/
theorem pderiv_mem_vanishing_of_full_tangent [CharZero C]
    (hrank : NoUniversalJetRelation C) {T : Set (ι → C)}
    {Q : DifferentialPolynomial ι C}
    (hfull : ∀ p ∈ T, ∀ V : ι → C, linearisationForm p Q Q.vars V = 0)
    (v : ι × ℕ) (p : ι → C) (hp : p ∈ T) :
    differentialPolynomialEvalOver (K := C) p (MvPolynomial.pderiv v Q) = 0 := by
  classical
  by_cases hv : v ∈ Q.vars
  · have hall : ∀ x : C,
        ∑ k ∈ (Q.vars.filter fun w => w.1 = v.1).image Prod.snd,
          differentialPolynomialEvalOver (K := C) p
            (MvPolynomial.pderiv (v.1, k) Q) * differentialJet k x = 0 := by
      intro x
      rw [← linearisationForm_single p Q v.1 x]
      exact hfull p hp _
    have hmem : v.2 ∈ (Q.vars.filter fun w => w.1 = v.1).image Prod.snd :=
      Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, rfl⟩, rfl⟩
    have hzero := hrank _ _ hall v.2 hmem
    rwa [Prod.mk.eta] at hzero
  · rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars (fun hcon => hv hcon), map_zero]

/-- **A differential-algebraic set whose tangent space is the whole ambient space at each of its
points has zero vanishing ideal**, hence is Kolchin-dense in the ambient affine space. -/
theorem eq_zero_of_vanishing_of_full_tangent [CharZero C]
    (hrank : NoUniversalJetRelation C) {T : Set (ι → C)} (hT : T.Nonempty)
    {J : Set (DifferentialPolynomial ι C)}
    (hJ : ∀ Q, Q ∈ J ↔ ∀ p ∈ T, differentialPolynomialEvalOver (K := C) p Q = 0)
    (hfull : ∀ Q ∈ J, ∀ p ∈ T, ∀ V : ι → C, linearisationForm p Q Q.vars V = 0) :
    ∀ Q ∈ J, Q = 0 := by
  classical
  intro Q hQ
  induction hd : Q.totalDegree using Nat.strong_induction_on generalizing Q with
  | _ d ih =>
    by_cases hdeg : Q.totalDegree = 0
    · obtain ⟨p, hp⟩ := hT
      have hval := (hJ Q).mp hQ p hp
      have hCQ : Q = MvPolynomial.C (MvPolynomial.coeff 0 Q) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
      rw [hCQ, differentialPolynomialEvalOver_C] at hval
      have hc : MvPolynomial.coeff 0 Q = 0 := by simpa using hval
      rw [hCQ, hc, map_zero]
    · obtain ⟨v, hv⟩ := exists_pderiv_ne_zero hdeg
      have hmem : MvPolynomial.pderiv v Q ∈ J := by
        refine (hJ _).mpr fun p hp => ?_
        exact pderiv_mem_vanishing_of_full_tangent hrank (hfull Q hQ) v p hp
      have hlt : (MvPolynomial.pderiv v Q).totalDegree < d := hd ▸ totalDegree_pderiv_lt hv
      exact absurd (ih _ hlt _ hmem rfl) hv

/-- Differentiating does not introduce new variables. -/
theorem vars_pderiv_subset {σ R : Type*} [CommRing R] [DecidableEq σ]
    (Q : MvPolynomial σ R) (v : σ) : (MvPolynomial.pderiv v Q).vars ⊆ Q.vars := by
  intro u hu
  obtain ⟨m, hm, hmu⟩ := (MvPolynomial.mem_vars_iff_mem_support u).mp hu
  have hcoeff : MvPolynomial.coeff m (MvPolynomial.pderiv v Q) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hcoeff
  have hQm : MvPolynomial.coeff (m + Finsupp.single v 1) Q ≠ 0 := by
    intro hz; exact hcoeff (by rw [hz, zero_mul])
  refine (MvPolynomial.mem_vars_iff_mem_support u).mpr
    ⟨m + Finsupp.single v 1, MvPolynomial.mem_support_iff.mpr hQm, ?_⟩
  have hmu' : m u ≠ 0 := by simpa using Finsupp.mem_support_iff.mp hmu
  refine Finsupp.mem_support_iff.mpr ?_
  simp only [Finsupp.add_apply]
  omega

/-- **The degree induction, with the closure under partial derivatives taken as a hypothesis.**  A
set of differential polynomials all vanishing at some point and closed under every partial
derivative contains only zero. -/
theorem eq_zero_of_pderiv_closed [CharZero C] {T : Set (ι → C)} (hT : T.Nonempty)
    {J : Set (DifferentialPolynomial ι C)}
    (hvanish : ∀ Q ∈ J, ∀ p ∈ T, differentialPolynomialEvalOver (K := C) p Q = 0)
    (hclosed : ∀ Q ∈ J, ∀ v, MvPolynomial.pderiv v Q ∈ J) :
    ∀ Q ∈ J, Q = 0 := by
  classical
  intro Q hQ
  induction hd : Q.totalDegree using Nat.strong_induction_on generalizing Q with
  | _ d ih =>
    by_cases hdeg : Q.totalDegree = 0
    · obtain ⟨p, hp⟩ := hT
      have hval := hvanish Q hQ p hp
      have hCQ : Q = MvPolynomial.C (MvPolynomial.coeff 0 Q) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hdeg
      rw [hCQ, differentialPolynomialEvalOver_C] at hval
      have hc : MvPolynomial.coeff 0 Q = 0 := by simpa using hval
      rw [hCQ, hc, map_zero]
    · obtain ⟨v, hv⟩ := exists_pderiv_ne_zero hdeg
      have hlt : (MvPolynomial.pderiv v Q).totalDegree < d := hd ▸ totalDegree_pderiv_lt hv
      exact absurd (ih _ hlt _ (hclosed Q hQ v) rfl) hv

end

end GaloisForLFunctions.HTGeometry
