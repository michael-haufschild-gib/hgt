import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Subperiods.Midpoint.FirstGap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.GaussianLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ZeroGateOperatorWindow

/-! # Operator distance in the gap containing the original near-Hilbert crossing -/

open Set Filter Real MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
open SharpOccupation
noncomputable section

/-- The two possible extreme chords of the midpoint spectrum, in the
physical operator error of the endpoint circuits. -/
private theorem midpoint_chords {ε : ℝ} (he : ε∈Ioc (0:ℝ) (1/10)) :
    let c := sqrt (1-(ε/2)^2)
    zeroGateArcTolerance (1/2-physicalArc ε)=sqrt 2*(c-ε/2) ∧
    zeroGateArcTolerance (1/2+physicalArc ε)=sqrt 2*(c+ε/2) := by
  intro c
  have hx : -(1:ℝ)≤ε/2 := by linarith only [he.1]
  have hy : ε/2≤1 := by linarith only [he.2]
  have h₁ : π*(1/2-physicalArc ε)/2=π/4-arcsin (ε/2) := by
    unfold physicalArc
    field_simp [pi_ne_zero]
    ring
  have h₂ : π*(1/2+physicalArc ε)/2=π/4+arcsin (ε/2) := by
    unfold physicalArc
    field_simp [pi_ne_zero]
    ring
  simp only [zeroGateArcTolerance,h₁,h₂,sin_sub,sin_add,sin_pi_div_four,cos_pi_div_four,
    sin_arcsin hx hy,cos_arcsin,c]
  constructor <;> ring

/-- On the original draw, the last scalar visit before the first robust
plateau crossing and the first scalar return after it enclose a gap.
Its midpoint has scalar distance within the displayed interval even at
the fixed physical error one tenth. -/
theorem gaussian_first_crossing_gap_midpoint :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),
        isSelfAdjoint_pathHamiltonian _⟩
      let P := nearHilbertContinuousCircuitBudget N
      ∃ σ > (0:ℝ), orbitCircuitDistance H P σ=9/80 ∧
        (∀ t∈Ico 0 σ, orbitCircuitDistance H P t<9/80) ∧
        ∀ ε∈Ioc (0:ℝ) (1/10), let v := firstVisit H σ 0 ε
          ∃ u : ℝ, IsGreatest {t : ℝ | 0≤t ∧ t≤σ ∧ orbitCircuitDistance H 0 t≤ε} u ∧
            u<σ ∧ σ<v ∧ (∀ t∈Ioo u v, ε<orbitCircuitDistance H 0 t) ∧
            orbitCircuitDistance H 0 ((u+v)/2) ∈
              Icc (sqrt 2*(sqrt (1-(ε/2)^2)-ε/2)) (sqrt 2*(sqrt (1-(ε/2)^2)+ε/2)) := by
  filter_upwards [gaussian_first_crossing_precision_wait] with ω hω
  filter_upwards [hω] with k hk
  intro N H P
  obtain ⟨σ,hσ,he,hprior,_⟩ := hk
  refine ⟨σ,hσ,he,hprior,?_⟩
  intro ε hε v
  have hs : ε<sqrt 2 := hε.2.trans_lt (by nlinarith only [sq_sqrt (by norm_num : (0:ℝ)≤2),sqrt_nonneg 2])
  have hout : ε<orbitCircuitDistance H 0 σ := by
    by_contra! h
    obtain ⟨z,hz,C,hC,herr⟩ := (hasProjectiveCircuitApproximation_iff_infDist _ 0 ε).mpr h
    have hp : orbitCircuitDistance H P σ≤ε := (hasProjectiveCircuitApproximation_iff_infDist _ P _).mp
      ⟨z,hz,C,hC.trans (Nat.zero_le _),herr⟩
    rw [show orbitCircuitDistance H P σ=9/80 from he] at hp
    linarith only [hp,hε.2]
  obtain ⟨u,hu,hlo,hhi,hgap,hw⟩ := first_gap H hσ ⟨hε.1,hs⟩ hout
  refine ⟨u,hu,hlo,hhi,hgap,?_⟩
  have hx := (physicalArc_spec hε.1 hs).1
  have h₁ : 1/2-physicalArc ε∈Icc (0:ℝ) 1 := by constructor <;> linarith only [hx.1,hx.2]
  have h₂ : 1/2+physicalArc ε∈Icc (0:ℝ) 1 := by constructor <;> linarith only [hx.1,hx.2]
  let t := (u+v)/2
  have hr := turnWidth_range H t
  have hm : turnWidth H t∈Icc (0:ℝ) 1 := ⟨hr.1,hr.2.le⟩
  have hmono := strictMonoOn_zeroGateArcTolerance_full.monotoneOn
  rw [scalar_distance_eq_chord,←(midpoint_chords hε).1,←(midpoint_chords hε).2]
  exact ⟨hmono h₁ hm hw.1,hmono hm h₂ hw.2⟩

#print axioms gaussian_first_crossing_gap_midpoint
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
