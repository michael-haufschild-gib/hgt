import GaloisForLFunctions.HTGeometry.RittBasisFinishingStep
import GaloisForLFunctions.HTGeometry.RittBasisPrimeReduction
import GaloisForLFunctions.HTGeometry.PseudoDivisionCommRing
import GaloisForLFunctions.HTGeometry.DifferentialKernelCharacteristic
import GaloisForLFunctions.HTGeometry.DifferentialPolynomialRankDomain

/-!
# Ritt's basis theorem over a coefficient domain with trivial contraction

Over a field the only property of the coefficients used by Ritt's argument is that a nonzero
constant generates the unit ideal, which forbids constants in a proper ideal.  Over a coefficient
domain the same role is played by the hypothesis that the ideal contains no nonzero constant, and
every remaining step — minimal Ritt rank, nonvanishing of the initial and the separant, and the
pseudo-division reduction — already works over a differential domain of characteristic zero.

* `initial_not_mem_of_trivialContraction`, `separant_not_mem_of_trivialContraction`;
* `radDiffFG_of_trivialContraction` — a radical differential ideal of `R{y}` meeting the
  coefficients only in zero is the radical differential ideal of a finite set.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

attribute [local instance] differentialPolynomialDifferential

variable {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [Differential R]

omit [IsDomain R] [CharZero R] [Differential R] in
/-- A rank-minimal relation of an ideal containing no nonzero constant avoids its own initial. -/
theorem initial_not_mem_of_trivialContraction
    {I : Ideal (DifferentialPolynomial Unit R)}
    (hIC : ∀ r : R, (MvPolynomial.C r : DifferentialPolynomial Unit R) ∈ I → r = 0)
    {P : DifferentialPolynomial Unit R}
    (hP : IsMinimalScalarDifferentialPolynomialRank (I : Set _) P) :
    scalarDifferentialPolynomialInitial P ∉ I := by
  intro hInitial
  have hInitial0 := scalarDifferentialPolynomialInitial_ne_zero hP.2.1
  by_cases hvars : (scalarDifferentialPolynomialInitial P).vars.Nonempty
  · have hmin := hP.2.2.2 hInitial hInitial0 hvars
    exact (Nat.not_le_of_lt (scalarDifferentialPolynomialInitial_order_lt hvars)) hmin.1
  · have hvars0 := Finset.not_nonempty_iff_eq_empty.mp hvars
    have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars0
    have hc : (scalarDifferentialPolynomialInitial P).coeff 0 = 0 :=
      hIC _ (by rw [← hC]; exact hInitial)
    exact hInitial0 (by rw [hC, hc]; simp)

omit [Differential R] in
/-- A rank-minimal relation of an ideal containing no nonzero constant avoids its own separant. -/
theorem separant_not_mem_of_trivialContraction
    {I : Ideal (DifferentialPolynomial Unit R)}
    (hIC : ∀ r : R, (MvPolynomial.C r : DifferentialPolynomial Unit R) ∈ I → r = 0)
    {P : DifferentialPolynomial Unit R}
    (hP : IsMinimalScalarDifferentialPolynomialRank (I : Set _) P) :
    scalarDifferentialPolynomialSeparant P ∉ I := by
  intro hSeparant
  have hSeparant0 : scalarDifferentialPolynomialSeparant P ≠ 0 :=
    pderiv_ne_zero_of_mem_vars_domain
      (scalarDifferentialPolynomialLeader_mem_vars hP.2.2.1)
  by_cases hvars : (scalarDifferentialPolynomialSeparant P).vars.Nonempty
  · have hmin := hP.2.2.2 hSeparant hSeparant0 hvars
    have hOrderLe := scalarDifferentialPolynomialSeparant_order_le P
    have hOrder : scalarDifferentialPolynomialOrder (scalarDifferentialPolynomialSeparant P) =
        scalarDifferentialPolynomialOrder P :=
      Nat.le_antisymm hOrderLe hmin.1
    exact (Nat.not_le_of_lt
      (scalarDifferentialPolynomialSeparant_leaderDegree_lt hP.2.2.1 hOrder))
        (hmin.2.1 hOrder.symm)
  · have hvars0 := Finset.not_nonempty_iff_eq_empty.mp hvars
    have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars0
    have hc : (scalarDifferentialPolynomialSeparant P).coeff 0 = 0 :=
      hIC _ (by rw [← hC]; exact hSeparant)
    exact hSeparant0 (by rw [hC, hc]; simp)

/-- The zero ideal of a differential polynomial ring over a domain is the radical differential
ideal of the empty set. -/
theorem isRadDiffFG_bot_of_domain :
    IsRadDiffFG (⊥ : Ideal (DifferentialPolynomial Unit R)) := by
  refine ⟨∅, ?_⟩
  refine (le_antisymm ?_ bot_le).symm
  refine radicalDifferentialIdeal_le (by simp) ?_ ?_
  · intro y hy
    obtain ⟨n, hn⟩ := hy
    rw [Ideal.mem_bot] at hn ⊢
    exact pow_eq_zero_iff'.mp hn |>.1
  · intro x hx
    rw [Ideal.mem_bot] at hx ⊢
    rw [hx, map_zero]

/-- **Ritt's basis theorem over a coefficient domain, for ideals meeting the coefficients only in
zero.**  Such a radical differential ideal of `R{y}` is the radical differential ideal of a finite
set. -/
theorem radDiffFG_of_trivialContraction
    (I : Ideal (DifferentialPolynomial Unit R))
    (hrad : I.IsRadical) (hδ : ∀ x ∈ I, Differential.deriv x ∈ I)
    (hIC : ∀ r : R, (MvPolynomial.C r : DifferentialPolynomial Unit R) ∈ I → r = 0)
    (hmax : ∀ J : Ideal (DifferentialPolynomial Unit R), J.IsRadical →
      (∀ x ∈ J, Differential.deriv x ∈ J) → I < J → IsRadDiffFG J)
    (hprime : I.IsPrime) : IsRadDiffFG I := by
  classical
  by_contra hIfg
  have hIbot : I ≠ ⊥ := fun h => hIfg (h ▸ isRadDiffFG_bot_of_domain)
  obtain ⟨A, hA⟩ :=
    Ideal.exists_minimal_scalarDifferentialPolynomialRank_of_trivialContraction hIbot hIC
  set m : ℕ := scalarDifferentialPolynomialOrder A with hm
  have hAI : A ∈ I := hA.1
  have hAvars : ∀ j : ℕ, m < j → ((), j) ∉ A.vars := by
    intro j hj hmem
    have : j ≤ m := Finset.le_sup (f := fun p : Unit × ℕ => p.2) hmem
    omega
  have hSep : MvPolynomial.pderiv (((), m) : Unit × ℕ) A ≠ 0 :=
    pderiv_ne_zero_of_mem_vars_domain (scalarDifferentialPolynomialLeader_mem_vars hA.2.2.1)
  have hLeader : MvPolynomial.degreeOf (((), m) : Unit × ℕ) A ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (scalarDifferentialPolynomialLeaderDegree_pos hA.2.2.1)
  have hle : diffPolyIterateIdeal A ≤ I :=
    diffPolyIterateIdeal_le_of_derivation_stable hAI (fun Q hQ => hδ Q hQ)
  have hreduced : ∀ Rp : DifferentialPolynomial Unit R, Rp ∈ I →
      (∀ j : ℕ, m < j → ((), j) ∉ Rp.vars) →
      MvPolynomial.degreeOf (((), m) : Unit × ℕ) Rp <
        MvPolynomial.degreeOf (((), m) : Unit × ℕ) A → Rp = 0 := by
    intro Rp hRI hRvars hRdeg
    by_contra hR0
    by_cases hRnc : Rp.vars.Nonempty
    · obtain ⟨hord, hdeg, -⟩ := hA.2.2.2 hRI hR0 hRnc
      have hRord : scalarDifferentialPolynomialOrder Rp ≤ m := by
        refine Finset.sup_le ?_
        intro p hp
        by_contra hcon
        exact hRvars p.2 (by omega) (by rcases p with ⟨u, j⟩; rwa [Subsingleton.elim u ()] at hp)
      have hordeq : m = scalarDifferentialPolynomialOrder Rp := le_antisymm hord hRord
      have hdeg' := hdeg hordeq
      rw [scalarDifferentialPolynomialLeaderDegree, scalarDifferentialPolynomialLeaderDegree,
        scalarDifferentialPolynomialLeader, scalarDifferentialPolynomialLeader,
        ← hm, ← hordeq] at hdeg'
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hRnc
      have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hRnc
      have hcz : Rp.coeff 0 = 0 := hIC _ (by rw [← hC]; exact hRI)
      exact hR0 (by rw [hC, hcz]; simp)
  have hsat : ∀ Q ∈ I, ∃ j : ℕ,
      (scalarDifferentialPolynomialInitial A * scalarDifferentialPolynomialSeparant A) ^ j * Q
        ∈ radicalDifferentialIdeal (({A} : Finset (DifferentialPolynomial Unit R)) : Set _) := by
    intro Q hQ
    obtain ⟨a, b, hmem⟩ :=
      exists_initial_separant_powers_mem_diffPolyIterateIdeal (i := ()) (m := m)
        hAvars hSep hLeader hle hreduced (scalarDifferentialPolynomialOrder Q)
        (Q := Q) (fun j hj hmemj => by
          have : j ≤ scalarDifferentialPolynomialOrder Q :=
            Finset.le_sup (f := fun p : Unit × ℕ => p.2) hmemj
          omega) hQ
    have hAle : diffPolyIterateIdeal A
        ≤ radicalDifferentialIdeal (({A} : Finset (DifferentialPolynomial Unit R)) : Set _) :=
      diffPolyIterateIdeal_le_of_derivation_stable
        (subset_radicalDifferentialIdeal _ (by simp))
        (fun Q hQ => deriv_mem_radicalDifferentialIdeal _ Q hQ)
    refine ⟨max a b, hAle ?_⟩
    have hrw : (scalarDifferentialPolynomialInitial A
          * scalarDifferentialPolynomialSeparant A) ^ (max a b) * Q
        = (scalarDifferentialPolynomialInitial A ^ (max a b - a)
            * scalarDifferentialPolynomialSeparant A ^ (max a b - b))
          * (mvPolynomialInitialAt (((), m) : Unit × ℕ) A ^ a *
              (MvPolynomial.pderiv (((), m) : Unit × ℕ) A ^ b * Q)) := by
      rw [mul_pow]
      rw [show scalarDifferentialPolynomialInitial A
          = mvPolynomialInitialAt (((), m) : Unit × ℕ) A from rfl,
        show scalarDifferentialPolynomialSeparant A
          = MvPolynomial.pderiv (((), m) : Unit × ℕ) A from rfl]
      have e1 : mvPolynomialInitialAt (((), m) : Unit × ℕ) A ^ (max a b)
          = mvPolynomialInitialAt (((), m) : Unit × ℕ) A ^ (max a b - a)
            * mvPolynomialInitialAt (((), m) : Unit × ℕ) A ^ a := by
        rw [← pow_add]; congr 1; omega
      have e2 : MvPolynomial.pderiv (((), m) : Unit × ℕ) A ^ (max a b)
          = MvPolynomial.pderiv (((), m) : Unit × ℕ) A ^ (max a b - b)
            * MvPolynomial.pderiv (((), m) : Unit × ℕ) A ^ b := by
        rw [← pow_add]; congr 1; omega
      rw [e1, e2]
      ring
    rw [hrw]
    exact Ideal.mul_mem_left _ _ hmem
  have hhM : scalarDifferentialPolynomialInitial A
      * scalarDifferentialPolynomialSeparant A ∉ I := by
    intro hmem
    rcases hprime.mem_or_mem hmem with h | h
    · exact initial_not_mem_of_trivialContraction hIC hA h
    · exact separant_not_mem_of_trivialContraction hIC hA h
  exact hIfg (isRadDiffFG_of_saturation hrad hδ hmax hhM
    (by
      intro y hy
      have hyA : y = A := by simpa using hy
      rw [hyA]
      exact hAI) hsat)

end

end GaloisForLFunctions.HTGeometry
