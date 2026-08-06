import GaloisForLFunctions.HTGeometry.ActiveLatticeRankBound
import GaloisForLFunctions.HTGeometry.AbstractSeparantMinimality
import GaloisForLFunctions.HTGeometry.LastVariableJetLift
import GaloisForLFunctions.HTGeometry.MinimalAutonomousOrder

/-!
# The frequency rank of a differentially algebraic quasiperiodic function

A quasiperiodic function whose phase observable is analytic on a polyannulus
and which satisfies a nonzero autonomous algebraic differential equation of
order `n` along the real time axis has active lattice of rank at most `n`.

The equation is replaced by a degree-minimal one, whose separant then fails to
annihilate: at some real time the separant is nonzero.  Lifting the equation to
the last variable turns it into a jet relation on the polyannulus whose last
partial derivative is the separant, and the rank bound applies at the orbit
point of that time.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-- The lifted equation evaluates on the jets exactly as the univariate one. -/
theorem jetRelationEval_jetLift {omega : d → ℝ} {F : (d → ℂ) → ℂ} {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) (z : d → ℂ) :
    jetRelationEval omega F (lastVariableJetLift P) z = phaseJetEval omega F P z := by
  rw [jetRelationEval, eval_jetLift]
  rfl

/-- **The frequency rank is at most the autonomous order.**  If the phase
function of an analytic phase observable with rationally independent frequencies
satisfies a nonzero autonomous algebraic differential equation of order `n`, and
no such equation is free of the top derivative, then the active lattice of the
observable has rank at most `n`. -/
theorem rank_activeLattice_le_of_realAutonomousAnnihilator {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega F) n P)
    (hpos : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 →
      RealAutonomousAnnihilator (phaseFunction omega F) n Q → Q.natDegree ≠ 0) :
    Module.rank ℤ (activeLattice F) ≤ (n : Cardinal) := by
  obtain ⟨P, -, hA, -, hsep⟩ := exists_pred_with_separant hex hpos
  have hsep' : ∃ t : ℝ, Polynomial.eval₂
      (MvPolynomial.eval fun j : Fin n =>
        iteratedDeriv (j : ℕ) (phaseFunction omega F) (t : ℂ))
      (iteratedDeriv n (phaseFunction omega F) (t : ℂ))
      (Polynomial.derivative P) ≠ 0 := by
    by_contra hc
    exact hsep fun t => not_not.1 fun h => hc ⟨t, h⟩
  obtain ⟨t, ht⟩ := hsep'
  refine rank_activeLattice_le hρ hindep hF (lastVariableJetLift P) ?_
    (torusOrbitPoint_mem_polyannulus hρ omega t) ?_
  · intro z hz
    rw [jetRelationEval_jetLift]
    exact phaseJetEval_eq_zero_of_realAutonomousAnnihilator hρ hindep hF hA z hz
  · rw [pderiv_last_jetLift]
    have heval : MvPolynomial.eval
        (fun i : Fin (n + 1) => phaseJet omega F (i : ℕ) (torusOrbitPoint omega t))
        (lastVariableJetLift (Polynomial.derivative P))
        = phaseJetEval omega F (Polynomial.derivative P) (torusOrbitPoint omega t) :=
      jetRelationEval_jetLift _ _
    rw [heval, phaseJetEval_torusOrbitPoint hρ hF]
    exact ht

/-- **The frequency rank is at most the order of any autonomous equation.**
No minimality is assumed: the order can be lowered until the top derivative is
present, which only decreases the bound. -/
theorem rank_activeLattice_le_of_exists_realAutonomousAnnihilator {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega F) n P) :
    Module.rank ℤ (activeLattice F) ≤ (n : Cardinal) := by
  obtain ⟨k, hkn, hexk, hposk⟩ := exists_minimal_order_realAutonomousAnnihilator hex
  refine le_trans
    (rank_activeLattice_le_of_realAutonomousAnnihilator hρ hindep hF hexk hposk) ?_
  exact Nat.cast_le.2 hkn

end

end GaloisForLFunctions.HTGeometry
