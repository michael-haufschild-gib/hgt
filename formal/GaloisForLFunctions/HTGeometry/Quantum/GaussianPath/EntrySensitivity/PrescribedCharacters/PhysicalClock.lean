import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.EntrySensitivity.PrescribedCharacters.Nonresonance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.ArcLaw
import Mathlib.NumberTheory.Niven

/-! # Sampling at the first scalar return after the physical crossing -/

open Set Filter Topology MeasureTheory Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters
open PrecisionReturns AdaptiveSampling
noncomputable section

/-- The scalar tolerance one tenth corresponds to an irrational fraction
of a turn, since the sine of its half-angle is one twentieth. -/
theorem physicalArc_tenth_irrational : Irrational (SharpOccupation.physicalArc (1/10)) := by
  rintro ⟨q,hq⟩
  let θ := arcsin (1/20)
  have hs : sin θ=1/20 := sin_arcsin (by norm_num) (by norm_num)
  have ha : θ=(q/2 : ℚ)*π := by
    unfold SharpOccupation.physicalArc at hq
    rw [show (1/10:ℝ)/2=1/20 by norm_num] at hq
    push_cast
    have h := (eq_div_iff pi_ne_zero).mp hq
    dsimp only [θ]
    linarith only [h]
  have h := niven_sin (θ:=θ) ⟨q/2,ha⟩ ⟨1/20,by simpa using hs⟩
  rw [hs] at h
  norm_num [Set.mem_insert_iff,Set.mem_singleton_iff] at h

/-- At the actual first near-Hilbert crossing, use the absolute date of
the next empty-circuit visit at error one tenth as sampling period.
Every time translate sees full projective Haar measure and every shifted
arc test has its exact enclosing-arc frequency. -/
theorem gaussian_first_crossing_scalar_clock :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      let E := energy ω k
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t ∈ Ico 0 σ, orbitCircuitDistance H P t < 9/80) ∧
        let v := firstVisit H σ 0 (1/10)
        ∀ b : Label k, FreeAtStep (projectiveFrequency E b) v ∧ ∀ a : ℝ,
          Tendsto (integerClockPrefixLaw (fun j : ℕ => finiteClockPhasePoint
            (projectiveFrequency E b) (a+(j:ℝ)*v))) atTop
            (𝓝 (finiteTorusHaarProbabilityMeasure {l : Label k // l≠b})) ∧
          ∀ (ψ : Label k → ℝ) (r : Icc (0:ℝ) (1/2)),
            Tendsto (fun j => (timeLaw a v j).real (arcTimes E ψ r)) atTop
              (𝓝 (zeroGateArcDensity (2^N) r)) := by
  have hs : (1/10:ℝ)<sqrt 2 := by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2]
  filter_upwards [gaussian_first_entry_free (1/10) (by norm_num) hs physicalArc_tenth_irrational,
    FirstGate.gaussian_first_crossing_one_gate] with ω hfree hcross
  filter_upwards [hcross] with k hk
  intro N H P E
  obtain ⟨σ,hσ,he,hbefore,hstrict⟩ := hk
  have hfar : 1/10 < orbitCircuitDistance H 0 σ := by
    by_contra! h
    have hfit := (hasProjectiveCircuitApproximation_iff_infDist _ 0 (1/10:ℝ)).mpr h
    have h0 := (firstVisit_isLeast H σ 0 (by norm_num : (0:ℝ)<1/10)).2 ⟨le_rfl,hfit⟩
    have h1 := (firstVisit_isLeast H σ 1 (by norm_num : (0:ℝ)<1/10)).1.1
    exact hstrict.not_ge (h0.trans h1)
  refine ⟨σ,hσ,he,hbefore,?_⟩
  intro v b
  have hf := hfree k σ hσ hfar b
  refine ⟨hf,?_⟩
  intro a
  refine ⟨affine_phaseLaw _ _ _ hf,?_⟩
  intro ψ r
  simpa only [Label,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using
    arc_timeLaw E ψ b r a v hf

#print axioms gaussian_first_crossing_scalar_clock
end
end GaloisForLFunctions.HTGeometry.EntrySensitivity.PrescribedCharacters
