import GaloisForLFunctions.HTGeometry.FirstOrderCoefficientDecomposition
import GaloisForLFunctions.HTGeometry.EntireJetEvaluation
import GaloisForLFunctions.Bottcher.AnalyticDomain

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- An entire order-one differential-algebraic function has an irreducible polynomial relation on
its actual `(z,f,f')` jet. -/
theorem exists_irreducible_firstOrderRelation {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hDA : DifferentiallyAlgebraicOfOrder f 1) :
    ∃ P : MvPolynomial (Fin 3) ℂ, P ≠ 0 ∧ Irreducible P ∧
      ∀ z : ℂ, MvPolynomial.eval
        (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) f z) P = 0 := by
  classical
  let RelDegree : ℕ → Prop := fun d =>
    ∃ P : MvPolynomial (Fin 3) ℂ, P ≠ 0 ∧ P.totalDegree = d ∧
      ∀ z : ℂ, MvPolynomial.eval
        (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) f z) P = 0
  have hex : ∃ d, RelDegree d := by
    obtain ⟨P, hP, hrel⟩ := hDA
    exact ⟨P.totalDegree, P, hP, rfl, hrel⟩
  let d : ℕ := Nat.find hex
  obtain ⟨P, hP, hPd, hrel⟩ := Nat.find_spec hex
  have hminimal {Q : MvPolynomial (Fin 3) ℂ} (hQ : Q ≠ 0)
      (hQrel : ∀ z : ℂ, MvPolynomial.eval
        (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) f z) Q = 0) :
      d ≤ Q.totalDegree := by
    apply Nat.find_min' hex
    exact ⟨Q, hQ, rfl, hQrel⟩
  have hIrred : Irreducible P := by
    rw [irreducible_iff]
    constructor
    · intro hunit
      have hu := hunit.map (MvPolynomial.eval
        (Fin.cons (0 : ℂ) fun j : Fin 2 => iteratedDeriv (j : ℕ) f 0))
      exact hu.ne_zero (hrel 0)
    · intro A B hfac
      have hA0 : A ≠ 0 := by
        intro hzero
        apply hP
        rw [hfac, hzero, zero_mul]
      have hB0 : B ≠ 0 := by
        intro hzero
        apply hP
        rw [hfac, hzero, mul_zero]
      by_cases hAunit : IsUnit A
      · exact Or.inl hAunit
      by_cases hBunit : IsUnit B
      · exact Or.inr hBunit
      exfalso
      let eA : ℂ → ℂ := fun z => MvPolynomial.eval
        (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) f z) A
      let eB : ℂ → ℂ := fun z => MvPolynomial.eval
        (Fin.cons z fun j : Fin 2 => iteratedDeriv (j : ℕ) f z) B
      have heA : AnalyticOnNhd ℂ eA Set.univ := analyticOnNhd_jetEval hf 1 A
      have heB : AnalyticOnNhd ℂ eB Set.univ := analyticOnNhd_jetEval hf 1 B
      have hprod : Set.EqOn (fun z => eA z * eB z) 0 Set.univ := by
        intro z _
        dsimp [eA, eB]
        rw [← MvPolynomial.eval_mul, ← hfac]
        exact hrel z
      have honeRel : Set.EqOn eA 0 Set.univ ∨ Set.EqOn eB 0 Set.univ := by
        by_cases hAe : Set.EqOn eA 0 Set.univ
        · exact Or.inl hAe
        · right
          by_contra hBe
          exact (Bottcher.analyticOnNhd_mul_ne_zero heA heB isPreconnected_univ isOpen_univ
            hAe hBe) hprod
      have hdegadd : d = A.totalDegree + B.totalDegree := by
        calc
          d = P.totalDegree := by simpa [d] using hPd.symm
          _ = (A * B).totalDegree := by rw [hfac]
          _ = A.totalDegree + B.totalDegree :=
            MvPolynomial.totalDegree_mul_of_isDomain hA0 hB0
      rcases honeRel with hAe | hBe
      · have hBdeg : 0 < B.totalDegree := by
          by_contra hnot
          have hzero : B.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
          have hBC : B = MvPolynomial.C (B.coeff 0) :=
            MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
          have hBc : B.coeff 0 ≠ 0 := by
            intro hc
            apply hB0
            rw [hBC, hc]
            simp
          apply hBunit
          rw [hBC]
          exact IsUnit.map MvPolynomial.C hBc.isUnit
        have hminA : d ≤ A.totalDegree := hminimal hA0 (fun z => hAe (Set.mem_univ z))
        omega
      · have hAdeg : 0 < A.totalDegree := by
          by_contra hnot
          have hzero : A.totalDegree = 0 := Nat.eq_zero_of_not_pos hnot
          have hAC : A = MvPolynomial.C (A.coeff 0) :=
            MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
          have hAc : A.coeff 0 ≠ 0 := by
            intro hc
            apply hA0
            rw [hAC, hc]
            simp
          apply hAunit
          rw [hAC]
          exact IsUnit.map MvPolynomial.C hAc.isUnit
        have hminB : d ≤ B.totalDegree := hminimal hB0 (fun z => hBe (Set.mem_univ z))
        omega
  exact ⟨P, hP, hIrred, hrel⟩

end

end GaloisForLFunctions.HTGeometry
