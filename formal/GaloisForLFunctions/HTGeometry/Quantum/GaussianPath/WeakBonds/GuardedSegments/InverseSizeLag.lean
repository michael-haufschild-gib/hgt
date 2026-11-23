import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianClock
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PhysicalComponents.AngularProfile
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.CrossingOrigin
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ShortWindows.PrefixProbability
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # A deterministic inverse-length lag far from every scalar -/
open MeasureTheory Filter Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.GuardedSegments
open PrescribedTimes
noncomputable section

abbrev segmentPoint (n : ℕ) (ω : PathPauliDisorder) : PrefixIndex n → ℝ :=
  fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)

/-- Along a typical infinite chain, a single inverse-length lag gives
opposite longitudinal probes uniformly on all sufficiently long segments
starting at the first site. -/
theorem gaussian_segment_lag :
    ∃ B>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      2/3 < pathGateDistance n 0 (segmentPoint n ω) (B/(n+2:ℕ)) := by
  obtain ⟨a,b,ha,_,hwidth⟩ := FirstAscent.gaussian_initial_clock
  let B := 25*π/a
  have hB : 0<B := div_pos (mul_pos (by norm_num) pi_pos) ha
  refine ⟨B,hB,?_⟩
  filter_upwards [hwidth,ReturnSpacing.PhysicalComponents.gaussian_chord_from_width B hB] with ω hw hc
  filter_upwards [hw,hc] with n hn hchord
  let N := n+2
  let u := pathPauliDisorderShell ω n
  let H : selfAdjoint (Matrix (Fin N→Bool) (Fin N→Bool) ℂ) := ⟨_,isSelfAdjoint_pathHamiltonian u⟩
  let W := circuitHamiltonianSpectralWidth H
  have hN : 0<(N:ℝ) := by dsimp only [N]; positivity
  have hW : a*(N:ℝ) ≤ W := hn.1
  have ht := div_pos hB hN
  have hang : 25*π ≤ 2*(B/N*W) := by
    have h := mul_le_mul_of_nonneg_left hW ht.le
    have he : B/(N:ℝ)*(a*N)=25*π := by dsimp only [B]; field_simp [ha.ne',hN.ne']
    rw [he] at h
    linarith only [h,pi_pos]
  have h := hchord (B/N) ht le_rfl π pi_pos.le le_rfl hang
  rw [sin_pi_div_two] at h
  rw [pathGateDistance,show numberedGenerator n (segmentPoint n ω)=H.val from numberedGenerator_shell _]
  exact (by norm_num : (2/3:ℝ) < 1-1/70).trans h

/-- Two scalar fits on the same trajectory give a fit at the difference
of their dates, with the sum of their errors. -/
theorem one_hard_date (n : ℕ) (ω : PathPauliDisorder) (t h : ℝ)
    (hh : 2/3 < pathGateDistance n 0 (segmentPoint n ω) h) :
    1/3 < pathGateDistance n 0 (segmentPoint n ω) t ∨
      1/3 < pathGateDistance n 0 (segmentPoint n ω) (t-h) := by
  let u := pathPauliDisorderShell ω n
  let H : selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ) := ⟨_,isSelfAdjoint_pathHamiltonian u⟩
  have he (v : ℝ) : pathGateDistance n 0 (segmentPoint n ω) v = orbitCircuitDistance H 0 v := by
    rw [pathGateDistance,show numberedGenerator n (segmentPoint n ω)=H.val from numberedGenerator_shell _]
    rfl
  by_contra! hboth
  have fit (v : ℝ) (hv : pathGateDistance n 0 (segmentPoint n ω) v ≤ 1/3) :
      HasProjectiveCircuitApproximation (n+2) (1/3) 0 (unitaryEvolution H.val v) :=
    (hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mpr ((he v).symm.trans_le hv)
  have hs := affordable_add_time H (x := -(t-h)) (y:=t) ((fit _ hboth.2).neg_time H) (fit _ hboth.1)
  rw [show -(t-h)+t=h by ring,show (1/3:ℝ)+1/3=2/3 by norm_num] at hs
  exact hh.not_ge ((he h).le.trans ((hasProjectiveCircuitApproximation_iff_infDist _ 0 _).mp hs))

#print axioms gaussian_segment_lag
end
end GaloisForLFunctions.HTGeometry.WeakBonds.GuardedSegments
