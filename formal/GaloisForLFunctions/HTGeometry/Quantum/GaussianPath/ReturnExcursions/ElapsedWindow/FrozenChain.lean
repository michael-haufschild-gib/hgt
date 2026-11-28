import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ElapsedWindow.InitialAscent
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CrossingProfile.Slack
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.Precision.ExponentialCompiler

/-! # Circuit fits on the reflected initial ascent and at its endpoints -/

open Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator Topology
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
open PrescribedTimes ShortWindows LocalPatches
noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- A short increment on either side of the reflected crossing changes
both circuit-distance bounds by at most its own error. -/
private theorem elapsed_edge (H : selfAdjoint (Reg n)) {P s L : ℕ} {σ v u η : ℝ}
    (hc : orbitCircuitDistance H P σ = 9/80)
    (hv : HasProjectiveCircuitApproximation n (1/10) s (unitaryEvolution H.val v))
    (hu : HasProjectiveCircuitApproximation n η L (unitaryEvolution H.val u)) :
    orbitCircuitDistance H (P+s+L) (v-σ+u) ≤ 17/80+η ∧
      ∀ j, s+j+L ≤ P → 1/80-η ≤ orbitCircuitDistance H j (v-σ+u) := by
  obtain ⟨hup,hlo⟩ := reflected_distances H hv P σ
  rw [hc,Nat.add_comm s P] at hup
  have ha := distance_add H (P+s) (v-σ) hu
  refine ⟨by linarith only [hup,ha],?_⟩
  intro j hj
  have hb := hlo (j+L) (by omega)
  have hd := distance_add H j (v-σ+u) (hu.neg_time H)
  rw [show v-σ+u+-u=v-σ by ring] at hd
  rw [hc] at hb
  linarith only [hb,hd]

private theorem original_crossing :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let x := prefixPoint k ω
      let σ := crossingOrigin (k+1) P (9/80) x
      localCrossingWidth N < σ ∧ pathGateDistance (k+1) P x σ=9/80 := by
  filter_upwards [gaussian_first_crossing_local_width] with ω hfirst
  filter_upwards [hfirst] with k hf
  intro N P x σ
  let a := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian a,isSelfAdjoint_pathHamiltonian a⟩
  have hd (b : ℕ) (t : ℝ) : pathGateDistance (k+1) b x t = orbitCircuitDistance H b t := by
    unfold pathGateDistance orbitCircuitDistance
    rw [show numberedGenerator (k+1) x=H.val from numberedGenerator_shell a]
  obtain ⟨τ,hτ,he,hbefore,_⟩ := hf
  have hw : 0 ≤ localCrossingWidth N := by unfold localCrossingWidth; positivity
  have hor : σ=τ := crossingOrigin_eq_of_first (hw.trans hτ.le) ((hd P τ).trans he)
    (fun u hu => (hd P u).trans_lt (hbefore u hu))
  rw [hor]
  exact ⟨hτ,(hd P τ).trans he⟩

/-- The early-ascent term in the first-wait bound vanishes for the
deterministic local simulation width. -/
theorem early_ascent_probability_vanishes :
    Tendsto (fun k : ℕ => pathPauliDisorderLaw.real {ω |
      crossingOrigin (k+1) (nearHilbertContinuousCircuitBudget (k+3)) (9/80) (prefixPoint k ω) <
        localCrossingWidth (k+3)}) atTop (𝓝 0) := by
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  apply probability_vanishes
  · intro k
    exact measurableSet_lt ((measurable_crossingOrigin ..).comp
      (gaussian_pauli_prefix_coordinates_law (k+1)).measurable) measurable_const
  · filter_upwards [original_crossing] with ω hw
    exact hw.mono fun k hk => hk.1.le.not_gt

/-- On one frozen Gaussian chain the exact elapsed first wait starts an
affordable interval twice as long as the first ascent. In an exponential
neighborhood of that elapsed time both edges of the circuit-distance
estimate hold to any prescribed linear number of accuracy bits. -/
theorem gaussian_reflected_first_wait :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ (c : ℕ) (γ α : ℝ), 0 ≤ γ → γ < α → α ≤ 1 →
      ∀ᶠ k : ℕ in atTop,
        let N := k+3
        let P := nearHilbertContinuousCircuitBudget N
        let x := prefixPoint k ω
        let σ := crossingOrigin (k+1) P (9/80) x
        let L := ⌊(2:ℝ)^(α*(N:ℝ))⌋₊
        let η := 1/(2:ℝ)^(c*N)
        ∀ s : ℕ, let Δ := crossingWait (k+1) P s x
          (∀ t ∈ Icc Δ (Δ+2*σ), pathGateDistance (k+1) (P+s) x t ≤ 17/80) ∧
          ∀ u : ℝ, |u| ≤ (2:ℝ)^(γ*(N:ℝ)) →
            pathGateDistance (k+1) (P+s+L) x (Δ+u) ≤ 17/80+η ∧
            ∀ j, s+j+L ≤ P → 1/80-η ≤ pathGateDistance (k+1) j x (Δ+u) := by
  filter_upwards [original_crossing,gaussian_exponential_precision_compiler]
    with ω hfirst hsim
  intro c γ α hγ hγα hα
  filter_upwards [hfirst,hsim c γ α hγ hγα hα] with k hf hi
  intro N P x σ L η s Δ
  let a := pathPauliDisorderShell ω (k+1)
  let H : selfAdjoint (Reg N) := ⟨pathHamiltonian a,isSelfAdjoint_pathHamiltonian a⟩
  have hd (b : ℕ) (t : ℝ) : pathGateDistance (k+1) b x t = orbitCircuitDistance H b t := by
    unfold pathGateDistance orbitCircuitDistance
    rw [show numberedGenerator (k+1) x=H.val from numberedGenerator_shell a]
  have hc : orbitCircuitDistance H P σ = 9/80 := (hd P σ).symm.trans hf.2
  have hfit := (hasProjectiveCircuitApproximation_iff_infDist (unitaryEvolution H.val (σ+Δ))
    s (1/10:ℝ)).mpr ((hd s _).symm.trans_le (first_wait_fit (k+1) P s x).2)
  refine ⟨reflected_initial_segment (k+1) P s x,?_⟩
  intro u hu
  have hh := elapsed_edge H hc hfit (hi u hu)
  rw [add_sub_cancel_left] at hh
  exact ⟨(hd _ _).trans_le hh.1, fun j hj => (hh.2 j hj).trans_eq (hd j _).symm⟩

#print axioms early_ascent_probability_vanishes
#print axioms gaussian_reflected_first_wait
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ElapsedWindow
