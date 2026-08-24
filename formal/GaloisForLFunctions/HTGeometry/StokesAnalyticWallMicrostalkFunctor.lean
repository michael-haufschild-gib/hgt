import GaloisForLFunctions.HTGeometry.StokesGlobalMicrostalkRestriction
import GaloisForLFunctions.HTGeometry.StokesAnalyticMicrolocalRealization
import GaloisForLFunctions.HTGeometry.StokesPuiseuxEnhancedExponential

/-!
# Analytic-wall-indexed microstalk functors

Actual analytic Stokes walls now index functors from global cellular boundary data to rational
microstalk modules. Their ranks realize the previously transported scalar microlocal
multiplicities, including the full characteristic multiplicity of genuine Puiseux branch pairs.
-/

open CategoryTheory
open scoped BigOperators

namespace GaloisForLFunctions.IrregularStokes.AnalyticMicrolocal

open AnalyticWall CellularMicrolocal CellularStokesCategory

/-- Wallwise microstalk functor indexed by an actual analytic Stokes wall. -/
noncomputable def analyticWallMicrostalkFunctor (c : ℂ) {k : ℕ}
    (hk : 0 < k) (hc : c ≠ 0) (w : AnalyticStokesWall c k) (s : ConormalSide) :
    BoundaryCategory k hk ⥤ ModuleCat ℚ :=
  wallMicrostalkFunctor hk (analyticWallLabel c hk hc w) s

/-- Functorial wallwise microstalk rank realizes the scalar analytic micro-rank. -/
theorem exponentialBoundary_analyticWallMicrostalk_finrank (c : ℂ) {k : ℕ}
    (hk : 0 < k) (hc : c ≠ 0) (d : ℕ) (w : AnalyticStokesWall c k)
    (s : ConormalSide) :
    Module.finrank ℚ
        ((analyticWallMicrostalkFunctor c hk hc w s).obj
          (exponentialBoundary k d hk)) =
      analyticMicroRank c hk hc d w s := by
  unfold analyticWallMicrostalkFunctor analyticMicroRank
  cases s
  · rw [exponentialBoundary_wallMicrostalk_left_finrank, microRank_eq]
    rfl
  · rw [exponentialBoundary_wallMicrostalk_right_finrank, microRank_eq]
    rcases analyticWallLabel c hk hc w with ⟨a, b⟩
    cases b <;> rfl

/-- Global exponential boundary attached to the actual contact order of a Puiseux branch pair. -/
noncomputable def branchPairExponentialBoundary {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) (d : ℕ) :
    BoundaryCategory (p.contactNumerator i j) (p.contactNumerator_pos_of_ne hij) :=
  exponentialBoundary (p.contactNumerator i j) d (p.contactNumerator_pos_of_ne hij)

/-- Analytic-wall-indexed microstalk functor for an actual Puiseux branch pair. -/
noncomputable def branchPairAnalyticWallMicrostalkFunctor {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j)
    (w : AnalyticStokesWall (branchPairLeadingCoefficient p hij)
      (p.contactNumerator i j)) (s : ConormalSide) :
    BoundaryCategory (p.contactNumerator i j) (p.contactNumerator_pos_of_ne hij) ⥤
      ModuleCat ℚ :=
  analyticWallMicrostalkFunctor (branchPairLeadingCoefficient p hij)
    (p.contactNumerator_pos_of_ne hij) (branchPairLeadingCoefficient_ne_zero p hij) w s

/-- Actual branch-pair wallwise functor rank equals its analytic microlocal multiplicity. -/
theorem branchPairAnalyticWallMicrostalk_finrank {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) (d : ℕ)
    (w : AnalyticStokesWall (branchPairLeadingCoefficient p hij)
      (p.contactNumerator i j)) (s : ConormalSide) :
    Module.finrank ℚ
        ((branchPairAnalyticWallMicrostalkFunctor p hij w s).obj
          (branchPairExponentialBoundary p hij d)) =
      analyticMicroRank (branchPairLeadingCoefficient p hij)
        (p.contactNumerator_pos_of_ne hij) (branchPairLeadingCoefficient_ne_zero p hij)
        d w s := by
  exact exponentialBoundary_analyticWallMicrostalk_finrank
    (branchPairLeadingCoefficient p hij) (p.contactNumerator_pos_of_ne hij)
      (branchPairLeadingCoefficient_ne_zero p hij) d w s

/-- Sum of functorially realized characteristic multiplicities over all analytic walls of an
actual Puiseux branch pair. -/
theorem branchPairAnalyticWallMicrostalk_fullMultiplicity_sum {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) (d : ℕ) :
    let c := branchPairLeadingCoefficient p hij
    let k := p.contactNumerator i j
    let hk := p.contactNumerator_pos_of_ne hij
    let hc := branchPairLeadingCoefficient_ne_zero p hij
    letI := Fintype.ofEquiv (StokesWall k) (branchPairWallEquivAnalytic p hij)
    (∑ w : AnalyticStokesWall c k,
      Module.finrank ℚ
        ((branchPairAnalyticWallMicrostalkFunctor p hij w
          (analyticActiveConormal c hk hc w)).obj
            (branchPairExponentialBoundary p hij d))) = 2 * k * d := by
  let c := branchPairLeadingCoefficient p hij
  let k := p.contactNumerator i j
  let hk := p.contactNumerator_pos_of_ne hij
  let hc := branchPairLeadingCoefficient_ne_zero p hij
  letI : Fintype (AnalyticStokesWall c k) :=
    Fintype.ofEquiv (StokesWall k) (branchPairWallEquivAnalytic p hij)
  calc
    (∑ w : AnalyticStokesWall c k,
      Module.finrank ℚ
        ((branchPairAnalyticWallMicrostalkFunctor p hij w
          (analyticActiveConormal c hk hc w)).obj
            (branchPairExponentialBoundary p hij d))) =
        ∑ w : AnalyticStokesWall c k,
          analyticMicroRank c hk hc d w (analyticActiveConormal c hk hc w) := by
            apply Finset.sum_congr rfl
            intro w _
            exact branchPairAnalyticWallMicrostalk_finrank p hij d w
              (analyticActiveConormal c hk hc w)
    _ = 2 * k * d := branchPairFullCharacteristicMultiplicity_sum p hij d

end GaloisForLFunctions.IrregularStokes.AnalyticMicrolocal
