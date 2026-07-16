import GaloisForLFunctions.HTGeometry.DirectionalWordPolynomialSurjectivity

/-!
# Every finite projective zero locus is a complete hypertranscendence horizon

Homogeneous equations of unequal degrees are lifted to one common positive degree by multiplying
each equation by every law monomial of the complementary degree.  At a nonzero law direction these
products vanish exactly when the original equation vanishes.  Combining this reduction with the
complete word-field realization proves that every zero locus of a finite homogeneous family is the
exact directional differential-algebraicity horizon of one observable; off the locus its complete
jet tower is algebraically independent.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

universe u v

variable {K : Type u} {ι η : Type v} [Field K] [Fintype ι] [Fintype η]

/-- A common positive degree exceeding every degree in a finite family. -/
def commonDegreeLiftDegree (d : η → ℕ) : ℕ := 1 + ∑ j, d j

/-- An original equation together with an ordered monomial of its complementary degree. -/
abbrev CommonDegreeEquationIndex (ι : Type v) (d : η → ℕ) [Fintype η] :=
  Σ j : η, Fin (commonDegreeLiftDegree d - d j) → ι

/-- Multiply one equation by one law monomial to reach the common degree. -/
def commonDegreeLift (P : η → MvPolynomial ι K) (d : η → ℕ)
    (q : CommonDegreeEquationIndex ι d) : MvPolynomial ι K :=
  (∏ r, MvPolynomial.X (q.2 r)) * P q.1

/-- Every lifted equation has the same positive homogeneous degree. -/
theorem commonDegreeLift_isHomogeneous
    (P : η → MvPolynomial ι K) (d : η → ℕ)
    (hP : ∀ j, (P j).IsHomogeneous (d j)) :
    ∀ q, (commonDegreeLift P d q).IsHomogeneous (commonDegreeLiftDegree d) := by
  intro q
  have hdle : d q.1 ≤ commonDegreeLiftDegree d := by
    dsimp [commonDegreeLiftDegree]
    exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ q.1)).trans
      (Nat.le_add_left _ 1)
  have hmon : MvPolynomial.IsHomogeneous
      (∏ r, MvPolynomial.X (q.2 r) : MvPolynomial ι K)
      (commonDegreeLiftDegree d - d q.1) := by
    have h := MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun r => MvPolynomial.X (q.2 r)) (fun _ => 1)
      (fun r _ => MvPolynomial.isHomogeneous_X K (q.2 r))
    simpa using h
  have hmul := hmon.mul (hP q.1)
  simpa [commonDegreeLift, Nat.sub_add_cancel hdle] using hmul

/-- At every nonzero law direction, the lifted common-degree family and the original family have
exactly the same simultaneous zero locus. -/
theorem commonDegreeLift_zero_iff
    (P : η → MvPolynomial ι K) (d : η → ℕ) (c : ι → K)
    (hc : ∃ i, c i ≠ 0) :
    (∀ q : CommonDegreeEquationIndex ι d,
        MvPolynomial.eval c (commonDegreeLift P d q) = 0) ↔
      ∀ j, MvPolynomial.eval c (P j) = 0 := by
  classical
  constructor
  · intro h j
    obtain ⟨i, hi⟩ := hc
    let w : Fin (commonDegreeLiftDegree d - d j) → ι := fun _ ↦ i
    have hq := h ⟨j, w⟩
    have hpow : (∏ _ : Fin (commonDegreeLiftDegree d - d j), c i) ≠ 0 := by
      simpa using pow_ne_zero (commonDegreeLiftDegree d - d j) hi
    simp only [commonDegreeLift, map_mul, map_prod, eval_X] at hq
    exact (mul_eq_zero.mp hq).resolve_left hpow
  · intro h q
    simp [commonDegreeLift, h q.1]

/-- **Universal finite-projective-zero-locus realization.**  Every finite homogeneous family,
with arbitrary individual degrees, is the exact complete-jet dependence horizon of one root
observable in an explicitly constructed rational differential field. -/
theorem exists_completeJet_horizon_eq_finiteHomogeneousZeroLocus
    (P : η → MvPolynomial ι K) (d : η → ℕ)
    (hP : ∀ j, (P j).IsHomogeneous (d j)) :
    ∃ a : CommonDegreeEquationIndex ι d → ProjectiveWordState ι → K,
      ∀ (c : ι → K), (∃ i, c i ≠ 0) →
        ((¬ AlgebraicIndependent K
            (fun r : ℕ ↦ directionalJet
              (projectiveCompleteDerivation a ((∑ j, d j) + 1)) c r
              (projectiveCompleteRoot
                (K := K) (ι := ι) (η := CommonDegreeEquationIndex ι d)))) ↔
          ∀ j, MvPolynomial.eval c (P j) = 0) := by
  let Q : CommonDegreeEquationIndex ι d → MvPolynomial ι K := commonDegreeLift P d
  have hQ : ∀ q, (Q q).IsHomogeneous ((∑ j, d j) + 1) := by
    intro q
    simpa [Q, commonDegreeLiftDegree, Nat.add_comm] using
      commonDegreeLift_isHomogeneous P d hP q
  obtain ⟨a, ha⟩ :=
    exists_completeJet_horizon_eq_homogeneousZeroLocus Q (∑ j, d j) hQ
  refine ⟨a, ?_⟩
  intro c hc
  rw [ha c hc]
  exact commonDegreeLift_zero_iff P d c hc

end

end GaloisForLFunctions.HTGeometry
