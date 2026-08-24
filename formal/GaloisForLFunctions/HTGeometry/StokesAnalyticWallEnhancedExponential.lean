import GaloisForLFunctions.HTGeometry.StokesEnhancedExponentialObject
import GaloisForLFunctions.HTGeometry.StokesAnalyticWallRealization

/-!
# Analytic Stokes walls as enhanced exponential objects

The intrinsic dominance phase on the oriented boundary circle now defines actual enhanced
exponential objects. Analytic and labelled Stokes walls land on the zero enhanced level of their
compactified epigraph support.
-/

open CategoryTheory Topology

namespace GaloisForLFunctions.IrregularStokes.AnalyticWall

open CompactIndSheaf EnhancedIndPullback EnhancedExponential CellularMicrolocal

/-- The real angle circle is compact. -/
noncomputable instance realAngleCompactSpace : CompactSpace Real.Angle := by
  letI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨Real.two_pi_pos⟩
  change CompactSpace (AddCircle (2 * Real.pi))
  infer_instance

/-- The intrinsic analytic Stokes dominance phase is continuous on the boundary circle. -/
theorem continuous_stokesPhase_angle (c : ℂ) (k : ℕ) :
    Continuous (stokesPhase c k) := by
  unfold stokesPhase
  have hc : Continuous (fun _ : Real.Angle =>
      ((Complex.arg c : ℝ) : Real.Angle)) := continuous_const
  have hk : Continuous (fun θ : Real.Angle => k • θ) := continuous_nsmul k
  have h : Continuous (fun θ : Real.Angle =>
      ((Complex.arg c : ℝ) : Real.Angle) - k • θ) :=
    hc.sub hk
  exact continuous_const.mul (Real.Angle.continuous_cos.comp h)

/-- Ind-sheaf exponential object of the analytic Stokes phase. -/
noncomputable def stokesPhaseExponentialIndSheaf (c : ℂ) (k : ℕ) :
    IndSheaf (EnhancedCompactification (TopCat.of Real.Angle)) :=
  compactifiedExponentialIndSheaf (TopCat.of Real.Angle) (stokesPhase c k)
    (continuous_stokesPhase_angle c k)

/-- Unbounded derived exponential object of the analytic Stokes phase. -/
noncomputable def stokesPhaseExponentialDerivedObject (c : ℂ) (k : ℕ) :
    DerivedIndSheaf (EnhancedCompactification (TopCat.of Real.Angle)) :=
  compactifiedExponentialDerivedObject (TopCat.of Real.Angle) (stokesPhase c k)
    (continuous_stokesPhase_angle c k)

/-- Analytic Stokes-phase object in the unbounded generated enhanced quotient. -/
noncomputable def stokesPhaseExponentialEnhancedObject (c : ℂ) (k : ℕ) :
    GeneratedEnhancedQuotient (TopCat.of Real.Angle) :=
  compactifiedExponentialEnhancedObject (TopCat.of Real.Angle) (stokesPhase c k)
    (continuous_stokesPhase_angle c k)

/-- Analytic Stokes-phase object in the bounded generated enhanced quotient. -/
noncomputable def stokesPhaseExponentialBoundedEnhancedObject (c : ℂ) (k : ℕ) :
    BoundedGeneratedEnhancedQuotient (TopCat.of Real.Angle) :=
  compactifiedExponentialBoundedEnhancedObject (TopCat.of Real.Angle) (stokesPhase c k)
    (continuous_stokesPhase_angle c k)

/-- At enhanced level zero, epigraph membership is nonpositive Stokes dominance. -/
theorem zeroLevel_mem_stokesPhaseEpigraph_iff (c : ℂ) (k : ℕ) (θ : Real.Angle) :
    compactifiedExponentialEpigraph (stokesPhase c k) (θ, (0 : ℝ)) ↔
      stokesPhase c k θ ≤ 0 :=
  compactifiedExponentialEpigraph_coe _ _ _

/-- Every analytic Stokes wall lies on zero-level exponential support. -/
theorem analyticStokesWall_mem_zeroLevel (c : ℂ) (k : ℕ)
    (θ : AnalyticStokesWall c k) :
    compactifiedExponentialEpigraph (stokesPhase c k) (θ.1, (0 : ℝ)) := by
  rw [zeroLevel_mem_stokesPhaseEpigraph_iff, θ.2]

/-- Every combinatorially labelled wall lands on zero-level exponential support under the
analytic wall realization. -/
theorem labelledWall_mem_zeroLevel (c : ℂ) {k : ℕ} (hk : 0 < k)
    (hc : c ≠ 0) (w : StokesWall k) :
    compactifiedExponentialEpigraph (stokesPhase c k)
      (labelledWallAngle c hk w, (0 : ℝ)) := by
  rw [zeroLevel_mem_stokesPhaseEpigraph_iff, labelledWallAngle_mem c hk hc w]

end GaloisForLFunctions.IrregularStokes.AnalyticWall
