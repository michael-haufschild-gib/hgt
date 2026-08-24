import GaloisForLFunctions.HTGeometry.StokesAnalyticWallMicrostalkFunctor
import GaloisForLFunctions.HTGeometry.StokesPuiseuxMicrolocalIndex

/-!
# Functorial analytic realization of the Puiseux microlocal index

The directed Morse mass used in the coefficient-generated Puiseux/Witt laws is realized here as
a sum of finranks of actual analytic-wall microstalk functor outputs. Diagonal branch pairs have
zero mass; distinct pairs use the analytic decay walls of their leading exponential difference.
Orbit normalization then recovers mixed Hom irregularity exactly.
-/

open CategoryTheory
open scoped BigOperators

namespace GaloisForLFunctions.IrregularStokes.AnalyticMicrolocal

open AnalyticWall CellularMicrolocal CellularStokesCategory

/-- Directed multiplicity of a distinct branch pair is the sum of ranks of its actual analytic
wall microstalk functors. -/
theorem branchPairAnalyticWallMicrostalk_directedMultiplicity_sum {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) (d : ℕ) :
    let c := branchPairLeadingCoefficient p hij
    let k := p.contactNumerator i j
    let hk := p.contactNumerator_pos_of_ne hij
    let hc := branchPairLeadingCoefficient_ne_zero p hij
    (∑ a : Fin k,
      Module.finrank ℚ
        ((branchPairAnalyticWallMicrostalkFunctor p hij
          (analyticDecayWall c hk hc a)
          (analyticActiveConormal c hk hc (analyticDecayWall c hk hc a))).obj
            (branchPairExponentialBoundary p hij d))) = k * d := by
  let c := branchPairLeadingCoefficient p hij
  let k := p.contactNumerator i j
  let hk := p.contactNumerator_pos_of_ne hij
  let hc := branchPairLeadingCoefficient_ne_zero p hij
  calc
    (∑ a : Fin k,
      Module.finrank ℚ
        ((branchPairAnalyticWallMicrostalkFunctor p hij
          (analyticDecayWall c hk hc a)
          (analyticActiveConormal c hk hc (analyticDecayWall c hk hc a))).obj
            (branchPairExponentialBoundary p hij d))) =
        ∑ a : Fin k,
          analyticMicroRank c hk hc d (analyticDecayWall c hk hc a)
            (analyticActiveConormal c hk hc (analyticDecayWall c hk hc a)) := by
              apply Finset.sum_congr rfl
              intro a _
              exact branchPairAnalyticWallMicrostalk_finrank p hij d _ _
    _ = k * d := analyticDirectedDecayMicroRank_sum c hk hc d

end GaloisForLFunctions.IrregularStokes.AnalyticMicrolocal

namespace GaloisForLFunctions.IrregularStokes.FinitePuiseuxFamily

open AnalyticWall AnalyticMicrolocal CellularMicrolocal CellularStokesCategory

/-- Directed analytic microstalk mass of an ordered branch pair. Diagonal pairs contribute zero;
off-diagonal pairs sum actual analytic-wall microstalk-functor ranks. -/
noncomputable def analyticDirectedPairMorseMass {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) (fiberRank : Fin m → ℕ) (a b : Fin m) : ℕ :=
  if hab : a = b then 0 else
    let c := branchPairLeadingCoefficient p hab
    let k := p.contactNumerator a b
    let hk := p.contactNumerator_pos_of_ne hab
    let hc := branchPairLeadingCoefficient_ne_zero p hab
    ∑ wall : Fin k,
      Module.finrank ℚ
        ((branchPairAnalyticWallMicrostalkFunctor p hab
          (analyticDecayWall c hk hc wall)
          (analyticActiveConormal c hk hc (analyticDecayWall c hk hc wall))).obj
            (branchPairExponentialBoundary p hab
              (fiberRank a * fiberRank b)))

/-- Functorially realized analytic mass is contact order times root-space dimension. -/
theorem analyticDirectedPairMorseMass_eq {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) (fiberRank : Fin m → ℕ) (a b : Fin m) :
    p.analyticDirectedPairMorseMass fiberRank a b =
      p.contactNumerator a b * (fiberRank a * fiberRank b) := by
  by_cases hab : a = b
  · subst b
    simp [analyticDirectedPairMorseMass]
  · rw [analyticDirectedPairMorseMass, dif_neg hab]
    exact AnalyticMicrolocal.branchPairAnalyticWallMicrostalk_directedMultiplicity_sum
      p hab (fiberRank a * fiberRank b)

/-- Actual analytic-wall functor mass equals the previous cellular directed Morse mass. -/
theorem analyticDirectedPairMorseMass_eq_directedPairMorseMass {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) (fiberRank : Fin m → ℕ) (a b : Fin m) :
    p.analyticDirectedPairMorseMass fiberRank a b =
      p.directedPairMorseMass fiberRank a b := by
  rw [analyticDirectedPairMorseMass_eq, directedPairMorseMass_eq]

end GaloisForLFunctions.IrregularStokes.FinitePuiseuxFamily

namespace GaloisForLFunctions.IrregularStokes.PuiseuxOrbitCoareaDatum

/-- Orbit-normalized mixed Hom mass built from actual analytic-wall microstalk functors. -/
noncomputable def normalizedAnalyticMicrolocalHomMass {n m K N : ℕ}
    (d : PuiseuxOrbitCoareaDatum n m K N) (fiberRank : Fin n → ℕ)
    (i j : Fin n) : ℝ :=
  d.toOrbitCoareaDatum.fiberSum i fun a =>
    d.toOrbitCoareaDatum.fiberSum j fun b =>
      (d.branches.analyticDirectedPairMorseMass
        (d.branchFiberRank fiberRank) a b : ℝ) / N

/-- Analytic-wall functor mass agrees with the cellular scalar microlocal mass. -/
theorem normalizedAnalyticMicrolocalHomMass_eq_normalizedMicrolocalHomMass
    {n m K N : ℕ} (d : PuiseuxOrbitCoareaDatum n m K N)
    (fiberRank : Fin n → ℕ) (i j : Fin n) :
    d.normalizedAnalyticMicrolocalHomMass fiberRank i j =
      d.normalizedMicrolocalHomMass fiberRank i j := by
  simp only [normalizedAnalyticMicrolocalHomMass, normalizedMicrolocalHomMass,
    OrbitCoareaDatum.fiberSum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [FinitePuiseuxFamily.analyticDirectedPairMorseMass_eq_directedPairMorseMass]

/-- Functorial analytic microlocal index equals mixed Hom irregularity times fiber rank. -/
theorem normalizedAnalyticMicrolocalHomMass_eq {n m K N : ℕ}
    (d : PuiseuxOrbitCoareaDatum n m K N) (fiberRank : Fin n → ℕ)
    (i j : Fin n) :
    d.normalizedAnalyticMicrolocalHomMass fiberRank i j =
      d.toOrbitCoareaDatum.homIrregularity i j *
        ((fiberRank i : ℝ) * fiberRank j) := by
  rw [normalizedAnalyticMicrolocalHomMass_eq_normalizedMicrolocalHomMass]
  exact d.normalizedMicrolocalHomMass_eq fiberRank i j

end GaloisForLFunctions.IrregularStokes.PuiseuxOrbitCoareaDatum
