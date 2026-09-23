import GaloisForLFunctions.HTGeometry.StokesAnalyticFunctorialMicrolocalIndex
import GaloisForLFunctions.HTGeometry.StokesUniversalMicrolocalWittLaw

/-!
# Analytic-functorial polarized Stokes--Witt law

The coefficient-generated Stokes pairing and its one-port coarea decomposition are rewritten
entirely using orbit-normalized finrank sums of actual analytic-wall microstalk functor outputs.
-/

open scoped BigOperators

namespace GaloisForLFunctions.IrregularStokes.PuiseuxOrbitCoareaDatum

variable {n m K N : ℕ}

/-- Polarized pairing built from actual analytic-wall microstalk functor ranks. -/
noncomputable def analyticFunctorialMicrolocalPairing
    (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * x j *
    d.normalizedAnalyticMicrolocalHomMass (fun _ => 1) i j

/-- Analytic-functorial pairing agrees with the previous cellular categorical pairing. -/
theorem analyticFunctorialMicrolocalPairing_eq_categoricalMicrolocalPairing
    (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℝ) :
    d.analyticFunctorialMicrolocalPairing x = d.categoricalMicrolocalPairing x := by
  simp only [analyticFunctorialMicrolocalPairing, categoricalMicrolocalPairing,
    d.normalizedAnalyticMicrolocalHomMass_eq_normalizedMicrolocalHomMass]

/-- One-dimensional fibers identify analytic functor rank mass with mixed Hom irregularity. -/
theorem normalizedAnalyticMicrolocalHomMass_one
    (d : PuiseuxOrbitCoareaDatum n m K N) (i j : Fin n) :
    d.normalizedAnalyticMicrolocalHomMass (fun _ => 1) i j =
      d.toOrbitCoareaDatum.homIrregularity i j := by
  simpa using d.normalizedAnalyticMicrolocalHomMass_eq (fun _ => 1) i j

/-- Analytic-functorial pairing is exactly the orbit-descended contact pairing. -/
theorem analyticFunctorialMicrolocalPairing_eq_contactPairing
    (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℝ) :
    d.analyticFunctorialMicrolocalPairing x =
      d.toOrbitCoareaDatum.contactPairing x := by
  rw [d.analyticFunctorialMicrolocalPairing_eq_categoricalMicrolocalPairing,
    d.categoricalMicrolocalPairing_eq_contactPairing]

/-- Cartan polarization as terminal energy plus physical rank square minus actual analytic
microstalk-functor pairing. -/
theorem cartanQuadratic_eq_analyticFunctorialMicrolocalIndex
    (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℝ) :
    d.toOrbitCoareaDatum.cartanQuadratic x =
      d.toOrbitCoareaDatum.terminalEnergy x +
        d.toOrbitCoareaDatum.physicalRank x ^ (2 : ℕ) -
      d.analyticFunctorialMicrolocalPairing x := by
  rw [d.analyticFunctorialMicrolocalPairing_eq_contactPairing]
  rfl

/-- Analytic-functorial microlocal coarea law with one global physical-rank channel. -/
theorem analyticFunctorialMicrolocalIndex_eq_coarea_onePort
    (d : PuiseuxOrbitCoareaDatum n m K N) (x : Fin n → ℝ) :
    d.toOrbitCoareaDatum.terminalEnergy x +
        d.toOrbitCoareaDatum.physicalRank x ^ (2 : ℕ) -
      d.analyticFunctorialMicrolocalPairing x =
    d.toOrbitCoareaDatum.terminalEnergy x +
        d.toOrbitCoareaDatum.blockEnergy x -
      (d.toOrbitCoareaDatum.cuts.root - 1) *
        d.toOrbitCoareaDatum.physicalRank x ^ (2 : ℕ) := by
  rw [← d.cartanQuadratic_eq_analyticFunctorialMicrolocalIndex,
    d.toOrbitCoareaDatum.cartanQuadratic_eq_positive_sub_onePort]

/-- Finite polarized Stokes--Witt law with every microlocal mass realized by analytic-wall
microstalk functors. -/
theorem polarizedAnalyticFunctorialStokesWittLaw
    (d : PuiseuxOrbitCoareaDatum n m K N)
    (fiberRank : Fin n → ℕ) (x : Fin n → ℝ) :
    (∀ i j,
      d.normalizedAnalyticMicrolocalHomMass fiberRank i j =
        d.toOrbitCoareaDatum.homIrregularity i j *
          ((fiberRank i : ℝ) * fiberRank j)) ∧
    d.toOrbitCoareaDatum.cartanQuadratic x =
      d.toOrbitCoareaDatum.terminalEnergy x +
        d.toOrbitCoareaDatum.blockEnergy x -
      (((K + 1 : ℕ) : ℝ) / N - 1) *
        d.toOrbitCoareaDatum.physicalRank x ^ (2 : ℕ) ∧
    (d.toOrbitCoareaDatum.physicalRank x = 0 → x ≠ 0 →
      0 < d.toOrbitCoareaDatum.cartanQuadratic x) ∧
    (∑ edge, d.toOrbitCoareaDatum.gradedChannel x edge ^ (2 : ℕ)) =
      d.toOrbitCoareaDatum.blockEnergy x := by
  refine ⟨?_, d.cartanQuadratic_eq_coefficient_onePort x, ?_,
    d.toOrbitCoareaDatum.sum_gradedChannel_sq_eq_blockEnergy x⟩
  · exact fun i j => d.normalizedAnalyticMicrolocalHomMass_eq fiberRank i j
  · exact fun hrank hx => d.cartanQuadratic_pos_of_physicalRank_eq_zero hrank hx

end GaloisForLFunctions.IrregularStokes.PuiseuxOrbitCoareaDatum
