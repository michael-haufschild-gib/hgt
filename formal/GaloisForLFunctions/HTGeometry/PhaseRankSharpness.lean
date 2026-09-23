import GaloisForLFunctions.HTGeometry.LinearPhaseObservable
import GaloisForLFunctions.HTGeometry.BohrFrequencyRankLaw

/-!
# Sharpness of the frequency-rank law

For an exponential sum with rationally independent frequencies and no vanishing
coefficient, the frequency rank is the number of frequencies, and the
characteristic polynomial of the frequencies gives a linear autonomous
differential equation of exactly that order.

Equality therefore holds in the frequency-rank law, and no autonomous algebraic
differential equation of lower order annihilates the function.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### The characteristic polynomial of the frequencies -/

/-- The monic polynomial with roots the imaginary frequencies. -/
def frequencyCharPoly (omega : d → ℝ) : Polynomial ℂ :=
  ∏ j, (Polynomial.X - Polynomial.C (Complex.I * (omega j : ℂ)))

omit [DecidableEq d] in
theorem monic_frequencyCharPoly (omega : d → ℝ) : (frequencyCharPoly omega).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

omit [DecidableEq d] in
theorem natDegree_frequencyCharPoly (omega : d → ℝ) :
    (frequencyCharPoly omega).natDegree = Fintype.card d := by
  rw [frequencyCharPoly,
    Polynomial.natDegree_prod _ _ fun j _ => Polynomial.X_sub_C_ne_zero _]
  rw [Finset.sum_congr rfl fun j _ => Polynomial.natDegree_X_sub_C
    (Complex.I * (omega j : ℂ))]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

omit [DecidableEq d] in
theorem eval_frequencyCharPoly (omega : d → ℝ) (i : d) :
    Polynomial.eval (Complex.I * (omega i : ℂ)) (frequencyCharPoly omega) = 0 := by
  rw [frequencyCharPoly, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

omit [DecidableEq d] in
theorem coeff_natDegree_frequencyCharPoly (omega : d → ℝ) :
    (frequencyCharPoly omega).coeff (Fintype.card d) = 1 := by
  have h := monic_frequencyCharPoly omega
  rw [Polynomial.Monic, Polynomial.leadingCoeff,
    natDegree_frequencyCharPoly] at h
  exact h

/-! ### The linear autonomous equation -/

/-- The autonomous relation given by the characteristic polynomial: the linear
differential operator with the frequencies as its characteristic roots. -/
private def linearRelationPoly (omega : d → ℝ) :
    Polynomial (MvPolynomial (Fin (Fintype.card d)) ℂ) :=
  Polynomial.C (∑ k : Fin (Fintype.card d),
      MvPolynomial.C ((frequencyCharPoly omega).coeff (k : ℕ)) * MvPolynomial.X k)
    + Polynomial.X

omit [DecidableEq d] in
theorem linearRelationPoly_ne_zero_phaseRankSharpness (omega : d → ℝ) : linearRelationPoly omega ≠ 0 := by
  intro h
  have hcoeff : (linearRelationPoly omega).coeff 1 = 1 := by
    rw [linearRelationPoly, Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_X_one, if_neg one_ne_zero, zero_add]
  rw [h, Polynomial.coeff_zero] at hcoeff
  exact zero_ne_one hcoeff

/-- **The exponential sum satisfies the linear equation of its characteristic
polynomial.** -/
theorem realAutonomousAnnihilator_linearObservable {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (a : d → ℂ) :
    RealAutonomousAnnihilator (phaseFunction omega (linearObservable a))
      (Fintype.card d) (linearRelationPoly omega) := by
  classical
  intro t
  have hF : AnalyticOnNhd ℂ (linearObservable a) (polyannulus ρ) :=
    analyticOnNhd_linearObservable a _
  have hjet : ∀ k : ℕ,
      iteratedDeriv k (phaseFunction omega (linearObservable a)) (t : ℂ)
      = ∑ j, (Complex.I * (omega j : ℂ)) ^ k * a j * torusOrbitPoint omega t j := by
    intro k
    rw [← phaseJet_torusOrbitPoint hρ hF k t, phaseJet_linearObservable]
    rfl
  rw [linearRelationPoly, Polynomial.eval₂_add, Polynomial.eval₂_C,
    Polynomial.eval₂_X, map_sum]
  have hterm : ∀ k : Fin (Fintype.card d),
      MvPolynomial.eval
        (fun i : Fin (Fintype.card d) =>
          iteratedDeriv (i : ℕ) (phaseFunction omega (linearObservable a)) (t : ℂ))
        (MvPolynomial.C ((frequencyCharPoly omega).coeff (k : ℕ)) * MvPolynomial.X k)
      = ∑ j, (frequencyCharPoly omega).coeff (k : ℕ) *
          ((Complex.I * (omega j : ℂ)) ^ (k : ℕ) * a j * torusOrbitPoint omega t j) := by
    intro k
    rw [map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X, hjet, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_comm, hjet]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hsplit : (∑ k : Fin (Fintype.card d), (frequencyCharPoly omega).coeff (k : ℕ) *
        ((Complex.I * (omega j : ℂ)) ^ (k : ℕ) * a j * torusOrbitPoint omega t j))
      + (Complex.I * (omega j : ℂ)) ^ (Fintype.card d) * a j * torusOrbitPoint omega t j
      = (a j * torusOrbitPoint omega t j) *
        Polynomial.eval (Complex.I * (omega j : ℂ)) (frequencyCharPoly omega) := by
    rw [Polynomial.eval_eq_sum_range, natDegree_frequencyCharPoly,
      Finset.sum_range_succ, coeff_natDegree_frequencyCharPoly, one_mul,
      mul_add, Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun k => (frequencyCharPoly omega).coeff k *
        ((Complex.I * (omega j : ℂ)) ^ k * a j * torusOrbitPoint omega t j))
        (Fintype.card d)]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun k _ => by ring) (by ring)
  rw [hsplit, eval_frequencyCharPoly, mul_zero]

/-! ### Sharpness -/

/-- **The frequency rank of an exponential sum is the number of its
frequencies.** -/
theorem rank_bohrFrequencyModule_linearObservable {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {a : d → ℂ} (ha : ∀ j, a j ≠ 0) :
    Module.rank ℚ
      (bohrFrequencyModule (realPhaseFunction omega (linearObservable a)))
      = (Fintype.card d : Cardinal) := by
  rw [rank_bohrFrequencyModule_eq_rank_activeLattice hρ hindep
    (analyticOnNhd_linearObservable a _), rank_activeLattice_linearObservable ha]

/-- **Equality is attained in the frequency-rank law.**  The exponential sum has
frequency rank the number of frequencies and satisfies an autonomous equation of
exactly that order. -/
theorem sharpness_linearObservable {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega) {a : d → ℂ} (ha : ∀ j, a j ≠ 0) :
    Module.rank ℚ
        (bohrFrequencyModule (realPhaseFunction omega (linearObservable a)))
        = (Fintype.card d : Cardinal) ∧
      ∃ P : Polynomial (MvPolynomial (Fin (Fintype.card d)) ℂ), P ≠ 0 ∧
        RealAutonomousAnnihilator (phaseFunction omega (linearObservable a))
          (Fintype.card d) P :=
  ⟨rank_bohrFrequencyModule_linearObservable hρ hindep ha,
    linearRelationPoly omega, linearRelationPoly_ne_zero_phaseRankSharpness omega,
    realAutonomousAnnihilator_linearObservable hρ a⟩

/-- **No autonomous equation of lower order.** -/
theorem not_realAutonomousAnnihilator_linearObservable {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {a : d → ℂ} (ha : ∀ j, a j ≠ 0) {m : ℕ} (hm : m < Fintype.card d) :
    ¬ ∃ P : Polynomial (MvPolynomial (Fin m) ℂ), P ≠ 0 ∧
      RealAutonomousAnnihilator (phaseFunction omega (linearObservable a)) m P := by
  refine not_realAutonomousAnnihilator_of_lt_rank hρ hindep
    (analyticOnNhd_linearObservable a _) ?_
  rw [rank_bohrFrequencyModule_linearObservable hρ hindep ha]
  exact Nat.cast_lt.2 hm

end

end GaloisForLFunctions.HTGeometry
