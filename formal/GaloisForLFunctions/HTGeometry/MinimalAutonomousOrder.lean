import GaloisForLFunctions.HTGeometry.PhaseJetRelationTransfer
import GaloisForLFunctions.HTGeometry.LastVariableJetLift

/-!
# The least order of an autonomous relation

An autonomous relation whose top derivative is absent is a relation of one
order lower: read as a polynomial in the last jet it is constant, and the
constant is a relation among the lower jets.

Hence at the least order for which a nonzero autonomous relation exists, every
nonzero relation has the top derivative genuinely present — at order zero
because a nonzero constant does not vanish.  Order minimality therefore never
has to be assumed: it can be arranged.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Dropping an absent top derivative -/

theorem exists_realAutonomousAnnihilator_of_natDegree_zero {f : ℂ → ℂ} {m : ℕ}
    {P : Polynomial (MvPolynomial (Fin (m + 1)) ℂ)} (hP : P ≠ 0)
    (hdeg : P.natDegree = 0) (hA : RealAutonomousAnnihilator f (m + 1) P) :
    ∃ P' : Polynomial (MvPolynomial (Fin m) ℂ), P' ≠ 0 ∧
      RealAutonomousAnnihilator f m P' := by
  set q : MvPolynomial (Fin (m + 1)) ℂ := P.coeff 0 with hq
  have hPC : P = Polynomial.C q := Polynomial.eq_C_of_natDegree_eq_zero hdeg
  have hqne : q ≠ 0 := by
    intro h
    exact hP (by rw [hPC, h, map_zero])
  refine ⟨jetUnlift q, jetUnlift_ne_zero hqne, fun t => ?_⟩
  have hzero : MvPolynomial.eval
      (fun i : Fin (m + 1) => iteratedDeriv (i : ℕ) f (t : ℂ)) q = 0 := by
    have := hA t
    rw [hPC, Polynomial.eval₂_C] at this
    exact this
  have heval := eval_jetLift
    (fun i : Fin (m + 1) => iteratedDeriv (i : ℕ) f (t : ℂ)) (jetUnlift q)
  rw [lastVariableJetLift_jetUnlift, hzero] at heval
  exact heval.symm

/-! ### The least order -/

/-- At an order below which no nonzero relation exists, every nonzero relation
has the top derivative genuinely present. -/
theorem natDegree_ne_zero_of_no_lower_annihilator {f : ℂ → ℂ} : ∀ {k : ℕ},
    (∀ j, j < k → ¬ ∃ P : Polynomial (MvPolynomial (Fin j) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator f j P) →
    ∀ {Q : Polynomial (MvPolynomial (Fin k) ℂ)}, Q ≠ 0 →
      RealAutonomousAnnihilator f k Q → Q.natDegree ≠ 0 := by
  intro k
  cases k with
  | zero =>
      intro _ Q hQ hAQ hdeg
      set q : MvPolynomial (Fin 0) ℂ := Q.coeff 0 with hq
      have hQC : Q = Polynomial.C q := Polynomial.eq_C_of_natDegree_eq_zero hdeg
      have hqne : q ≠ 0 := fun h => hQ (by rw [hQC, h, map_zero])
      have hzero : MvPolynomial.eval
          (fun i : Fin 0 => iteratedDeriv (i : ℕ) f ((0 : ℝ) : ℂ)) q = 0 := by
        have := hAQ 0
        rw [hQC, Polynomial.eval₂_C] at this
        exact this
      refine hqne (MvPolynomial.funext fun g => ?_)
      rw [map_zero]
      rwa [Subsingleton.elim
        (fun i : Fin 0 => iteratedDeriv (i : ℕ) f ((0 : ℝ) : ℂ)) g] at hzero
  | succ j =>
      intro hmin Q hQ hAQ hdeg
      exact hmin j (Nat.lt_succ_self j)
        (exists_realAutonomousAnnihilator_of_natDegree_zero hQ hdeg hAQ)

/-- **Order minimality can be arranged.**  If some nonzero autonomous relation
of order `n` holds, then for some `k ≤ n` a nonzero relation of order `k` holds
and every nonzero relation of order `k` has the top derivative present. -/
theorem exists_minimal_order_realAutonomousAnnihilator {f : ℂ → ℂ} {n : ℕ}
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator f n P) :
    ∃ k, k ≤ n ∧
      (∃ P : Polynomial (MvPolynomial (Fin k) ℂ), P ≠ 0 ∧
        RealAutonomousAnnihilator f k P) ∧
      ∀ Q : Polynomial (MvPolynomial (Fin k) ℂ), Q ≠ 0 →
        RealAutonomousAnnihilator f k Q → Q.natDegree ≠ 0 := by
  classical
  have hS : ∃ k : ℕ, ∃ P : Polynomial (MvPolynomial (Fin k) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator f k P := ⟨n, hex⟩
  exact ⟨Nat.find hS, Nat.find_le hex, Nat.find_spec hS,
    fun Q hQ hAQ => natDegree_ne_zero_of_no_lower_annihilator
      (fun j hj => Nat.find_min hS hj) hQ hAQ⟩

end

end GaloisForLFunctions.HTGeometry
