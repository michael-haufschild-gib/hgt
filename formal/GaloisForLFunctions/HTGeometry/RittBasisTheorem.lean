import GaloisForLFunctions.HTGeometry.RittBasisFinishingStep
import GaloisForLFunctions.HTGeometry.RittBasisPrimeReduction
import GaloisForLFunctions.HTGeometry.PseudoDivisionCommRing
import GaloisForLFunctions.HTGeometry.DifferentialKernelCharacteristic

/-!
# Ritt's basis theorem for one differential indeterminate

Every radical differential ideal of `K{y}`, for a differential field `K` of characteristic zero, is
the radical differential ideal of a finite set.

A maximal counterexample exists and is prime.  Inside it choose a relation of minimal Ritt rank; its
initial and separant lie outside, and Ritt's reduction — already available in the tree — pushes a
power of their product times any member into the differential ideal of that single relation.  The
saturation decomposition then collapses the counterexample onto the radical differential ideal of a
finite set.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [Differential K]

attribute [local instance] differentialPolynomialDifferential

omit [CharZero K] in
theorem isRadDiffFG_bot :
    IsRadDiffFG (⊥ : Ideal (DifferentialPolynomial Unit K)) := by
  refine ⟨∅, ?_⟩
  refine (le_antisymm ?_ ?_).symm
  · refine radicalDifferentialIdeal_le (by simp) ?_ ?_
    · intro y hy
      obtain ⟨n, hn⟩ := hy
      rw [Ideal.mem_bot] at hn ⊢
      exact pow_eq_zero_iff'.mp hn |>.1
    · intro x hx
      rw [Ideal.mem_bot] at hx ⊢
      rw [hx, map_zero]
  · exact bot_le

/-- **Ritt's basis theorem for one differential indeterminate.** -/
theorem radDiffFG_differentialPolynomial (I : Ideal (DifferentialPolynomial Unit K))
    (hrad : I.IsRadical) (hδ : ∀ x ∈ I, Differential.deriv x ∈ I) : IsRadDiffFG I := by
  classical
  by_contra hI
  obtain ⟨M, hMrad, hMδ, hMfg, hMmax⟩ := exists_maximal_not_radDiffFG ⟨I, hrad, hδ, hI⟩
  have hMtop : M ≠ ⊤ := fun h => hMfg (h ▸ isRadDiffFG_top)
  have hMbot : M ≠ ⊥ := fun h => hMfg (h ▸ isRadDiffFG_bot)
  have hMprime : M.IsPrime :=
    ⟨hMtop, fun {x y} hxy => mem_or_mem_of_maximal_not_radDiffFG hMrad hMδ hMfg hMmax hxy⟩
  obtain ⟨A, hA⟩ := Ideal.exists_minimal_scalarDifferentialPolynomialRank_ne_zero hMbot hMtop
  set m : ℕ := scalarDifferentialPolynomialOrder A with hm
  have hAM : A ∈ M := hA.1
  have hAvars : ∀ j : ℕ, m < j → ((), j) ∉ A.vars := by
    intro j hj hmem
    have : j ≤ m := Finset.le_sup (f := fun p : Unit × ℕ => p.2) hmem
    omega
  have hSep : MvPolynomial.pderiv (((), m) : Unit × ℕ) A ≠ 0 :=
    scalarDifferentialPolynomialSeparant_ne_zero hA.2.2.1
  have hLeader : MvPolynomial.degreeOf (((), m) : Unit × ℕ) A ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (scalarDifferentialPolynomialLeaderDegree_pos hA.2.2.1)
  have hle : diffPolyIterateIdeal A ≤ M :=
    diffPolyIterateIdeal_le_of_derivation_stable hAM (fun Q hQ => hMδ Q hQ)
  have hreduced : ∀ R : DifferentialPolynomial Unit K, R ∈ M →
      (∀ j : ℕ, m < j → ((), j) ∉ R.vars) →
      MvPolynomial.degreeOf (((), m) : Unit × ℕ) R <
        MvPolynomial.degreeOf (((), m) : Unit × ℕ) A → R = 0 := by
    intro R hRM hRvars hRdeg
    by_contra hR0
    by_cases hRnc : R.vars.Nonempty
    · obtain ⟨hord, hdeg, -⟩ := hA.2.2.2 hRM hR0 hRnc
      have hRord : scalarDifferentialPolynomialOrder R ≤ m := by
        refine Finset.sup_le ?_
        intro p hp
        by_contra hcon
        exact hRvars p.2 (by omega) (by rcases p with ⟨u, j⟩; rwa [Subsingleton.elim u ()] at hp)
      have hordeq : m = scalarDifferentialPolynomialOrder R := le_antisymm hord hRord
      have hdeg' := hdeg hordeq
      rw [scalarDifferentialPolynomialLeaderDegree, scalarDifferentialPolynomialLeaderDegree,
        scalarDifferentialPolynomialLeader, scalarDifferentialPolynomialLeader,
        ← hm, ← hordeq] at hdeg'
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at hRnc
      have hC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hRnc
      have hcne : R.coeff 0 ≠ 0 := by
        intro h0
        exact hR0 (by rw [hC, h0]; simp)
      exact hMtop (M.eq_top_of_isUnit_mem hRM
        (by rw [hC]; exact IsUnit.map MvPolynomial.C (isUnit_iff_ne_zero.mpr hcne)))
  have hsat : ∀ Q ∈ M, ∃ j : ℕ,
      (scalarDifferentialPolynomialInitial A * scalarDifferentialPolynomialSeparant A) ^ j * Q
        ∈ radicalDifferentialIdeal (({A} : Finset (DifferentialPolynomial Unit K)) : Set _) := by
    intro Q hQ
    obtain ⟨a, b, hmem⟩ :=
      exists_initial_separant_powers_mem_diffPolyIterateIdeal (i := ()) (m := m)
        hAvars hSep hLeader hle hreduced (scalarDifferentialPolynomialOrder Q)
        (Q := Q) (fun j hj hmemj => by
          have : j ≤ scalarDifferentialPolynomialOrder Q :=
            Finset.le_sup (f := fun p : Unit × ℕ => p.2) hmemj
          omega) hQ
    have hAle : diffPolyIterateIdeal A
        ≤ radicalDifferentialIdeal (({A} : Finset (DifferentialPolynomial Unit K)) : Set _) :=
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
      * scalarDifferentialPolynomialSeparant A ∉ M := by
    intro hmem
    rcases hMprime.mem_or_mem hmem with h | h
    · exact hA.initial_not_mem hMtop h
    · exact hA.separant_not_mem hMtop h
  exact hMfg (isRadDiffFG_of_saturation hMrad hMδ hMmax hhM
    (by
      intro y hy
      have hyA : y = A := by simpa using hy
      rw [hyA]
      exact hAM) hsat)

end

end GaloisForLFunctions.HTGeometry
