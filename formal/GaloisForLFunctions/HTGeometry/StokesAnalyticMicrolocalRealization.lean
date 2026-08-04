import GaloisForLFunctions.HTGeometry.StokesAnalyticWallRealization

/-!
# Microlocal multiplicities on actual analytic Stokes walls

The phase-zero theorem identifies the finite wall labels with the zero directions of the actual
leading exponential phase.  This module performs the corresponding transport of microstalk ranks,
microsupport, transverse orientation, and characteristic multiplicity.  Thus these invariants live
on the analytic zero set itself rather than on an independently supplied cellular wall set.
-/

open scoped BigOperators

namespace GaloisForLFunctions.IrregularStokes.AnalyticMicrolocal

open AnalyticWall CellularMicrolocal

noncomputable section

/-- Unique finite label of an actual analytic Stokes wall. -/
def analyticWallLabel (c : ℂ) {k : ℕ} (hk : 0 < k) (hc : c ≠ 0)
    (w : AnalyticStokesWall c k) : StokesWall k :=
  (cellularWallEquivAnalytic c hk hc).symm w

/-- Microlocal Morse rank transported to an actual zero direction of the leading phase. -/
def analyticMicroRank (c : ℂ) {k : ℕ} (hk : 0 < k) (hc : c ≠ 0)
    (d : ℕ) (w : AnalyticStokesWall c k) (s : ConormalSide) : ℕ :=
  microRank d (analyticWallLabel c hk hc w) s

/-- Unique microsupported conormal over an actual analytic wall. -/
def analyticActiveConormal (c : ℂ) {k : ℕ} (hk : 0 < k) (hc : c ≠ 0)
    (w : AnalyticStokesWall c k) : ConormalSide :=
  activeConormalSide (analyticWallLabel c hk hc w)

/-- Microsupport membership on the actual phase-zero locus. -/
def IsInAnalyticMicrosupport (c : ℂ) {k : ℕ} (hk : 0 < k) (hc : c ≠ 0)
    (d : ℕ) (w : AnalyticStokesWall c k) (s : ConormalSide) : Prop :=
  analyticMicroRank c hk hc d w s ≠ 0

/-- Positive-rank exponential data have exactly one microsupported conormal over every actual
analytic wall. -/
theorem isInAnalyticMicrosupport_iff_active (c : ℂ) {k d : ℕ}
    (hk : 0 < k) (hc : c ≠ 0) (hd : 0 < d)
    (w : AnalyticStokesWall c k) (s : ConormalSide) :
    IsInAnalyticMicrosupport c hk hc d w s ↔
      s = analyticActiveConormal c hk hc w := by
  exact isInMicrosupport_iff_active hd (analyticWallLabel c hk hc w) s

/-- Characteristic-cycle coefficient at the unique analytic conormal is the fiber rank. -/
theorem analyticMicroRank_active (c : ℂ) {k : ℕ} (hk : 0 < k) (hc : c ≠ 0)
    (d : ℕ) (w : AnalyticStokesWall c k) :
    analyticMicroRank c hk hc d w (analyticActiveConormal c hk hc w) = d :=
  microRank_activeConormal d (analyticWallLabel c hk hc w)

/-- The conormal orientation on the analytic zero set is the transverse sign of the actual
leading phase, not an independent Boolean decoration. -/
theorem analyticWall_transverse_sign (c : ℂ) {k : ℕ} (hk : 0 < k) (hc : c ≠ 0)
    (w : AnalyticStokesWall c k) :
    Real.Angle.sin
        (((Complex.arg c : ℝ) : Real.Angle) - k • w.1) =
      if (analyticWallLabel c hk hc w).2 then -1 else 1 := by
  let e := cellularWallEquivAnalytic c hk hc
  let u := analyticWallLabel c hk hc w
  have he : labelledWallAngle c hk u = w.1 := by
    exact congrArg Subtype.val (e.apply_symm_apply w)
  rw [← he]
  exact labelledWall_transverse_sign c hk u

/-- Full characteristic multiplicity on the actual analytic phase-zero set is `2 k d`. -/
theorem analyticFullCharacteristicMultiplicity_sum (c : ℂ) {k : ℕ}
    (hk : 0 < k) (hc : c ≠ 0) (d : ℕ) :
    letI := Fintype.ofEquiv (StokesWall k) (cellularWallEquivAnalytic c hk hc)
    (∑ w : AnalyticStokesWall c k,
      analyticMicroRank c hk hc d w (analyticActiveConormal c hk hc w)) =
        2 * k * d := by
  let e := cellularWallEquivAnalytic c hk hc
  letI : Fintype (AnalyticStokesWall c k) := Fintype.ofEquiv (StokesWall k) e
  calc
    (∑ w : AnalyticStokesWall c k,
        analyticMicroRank c hk hc d w (analyticActiveConormal c hk hc w)) =
        ∑ u : StokesWall k,
          analyticMicroRank c hk hc d (e u) (analyticActiveConormal c hk hc (e u)) := by
            exact (e.sum_comp fun w =>
              analyticMicroRank c hk hc d w (analyticActiveConormal c hk hc w)).symm
    _ = ∑ u : StokesWall k, microRank d u (activeConormalSide u) := by
          apply Finset.sum_congr rfl
          intro u _
          simp [analyticMicroRank, analyticActiveConormal, analyticWallLabel, e]
    _ = 2 * k * d := fullCharacteristicMultiplicity_sum k d

/-- Actual wall corresponding to the directed-decay member of one antipodal pair. -/
def analyticDecayWall (c : ℂ) {k : ℕ} (hk : 0 < k) (hc : c ≠ 0)
    (a : Fin k) : AnalyticStokesWall c k :=
  cellularWallEquivAnalytic c hk hc (decayWall k a)

/-- Directed analytic microstalk mass is `k d`. -/
theorem analyticDirectedDecayMicroRank_sum (c : ℂ) {k : ℕ}
    (hk : 0 < k) (hc : c ≠ 0) (d : ℕ) :
    (∑ a : Fin k,
      analyticMicroRank c hk hc d (analyticDecayWall c hk hc a)
        (analyticActiveConormal c hk hc (analyticDecayWall c hk hc a))) = k * d := by
  simpa [analyticMicroRank, analyticActiveConormal, analyticWallLabel, analyticDecayWall]
    using directedDecayMicroRank_sum k d

/-! ## Coefficient-generated branch-pair specialization -/

/-- Full characteristic multiplicity for the actual leading difference of two distinct
coefficient-generated Puiseux branches. -/
theorem branchPairFullCharacteristicMultiplicity_sum {m K N : ℕ}
    (p : FinitePuiseuxFamily m K N) {i j : Fin m} (hij : i ≠ j) (d : ℕ) :
    let c := branchPairLeadingCoefficient p hij
    let k := p.contactNumerator i j
    letI := Fintype.ofEquiv (StokesWall k) (branchPairWallEquivAnalytic p hij)
    (∑ w : AnalyticStokesWall c k,
      analyticMicroRank c (p.contactNumerator_pos_of_ne hij)
        (branchPairLeadingCoefficient_ne_zero p hij) d w
        (analyticActiveConormal c (p.contactNumerator_pos_of_ne hij)
          (branchPairLeadingCoefficient_ne_zero p hij) w)) =
      2 * k * d := by
  exact analyticFullCharacteristicMultiplicity_sum
    (branchPairLeadingCoefficient p hij) (p.contactNumerator_pos_of_ne hij)
      (branchPairLeadingCoefficient_ne_zero p hij) d

end

end GaloisForLFunctions.IrregularStokes.AnalyticMicrolocal
