import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.BudgetLaw
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseFluctuations.DimensionBounds.PhysicalTails

/-! # Reading an individual draw's mean gate cost from its finite prefix -/
open Set Filter MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
open SharpOccupation PhaseFluctuations
open private dimension_tails from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseFluctuations.DimensionBounds.PhysicalTails
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- A Borel version of the affordable fraction uses only the prefix
coordinates. Its orbit samples are taken from the identity. -/
def prefixFraction (k s : ℕ) (ε : ℝ) (x : PrefixIndex (k+1)→ℝ) : ℝ :=
  limsup (fun m : ℕ => rayMass 2 {y | pathGateDistance (k+1) s y (m:ℝ)≤ε} x) atTop

theorem measurable_prefixFraction (k s : ℕ) (ε : ℝ) : Measurable (prefixFraction k s ε) := by
  apply Measurable.limsup
  intro m
  apply measurable_rayMass
  simpa only [zero_add] using measurable_origin_event (k+1) s ε m (fun _ => 0) measurable_const

theorem prefixFraction_eq (k s : ℕ) (ε : ℝ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      prefixFraction k s ε x=affordablePhaseMass k s ε ω := by
  have h := budget_ray_limit k s ε (fun _ => 0) (fun _ _ _ => mul_zero _) (b:=2) (by norm_num)
  simp only [zero_add,show (2:ℝ)-1=1 by norm_num,one_mul] at h
  filter_upwards [h] with ω hw
  exact (hw.comp tendsto_natCast_atTop_atTop).limsup_eq

/-- A bounded natural cost is the sum of its strict budget exceedances. -/
private theorem discrete_layer_cake {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω→ℕ) (hf : Measurable f)
    (M : ℕ) (hM : ∀ x, f x≤M) :
    (∫ x, (f x:ℝ) ∂μ) = ∑ j ∈ Finset.range M, (1-μ.real {x | f x≤j}) := by
  classical
  let F (j : ℕ) := {x | f x≤j}ᶜ.indicator (fun _ => (1:ℝ))
  have hm j : MeasurableSet {x | f x≤j} := measurableSet_le hf measurable_const
  have hF j : Integrable (F j) μ := (integrable_const _).indicator (hm j).compl
  have he (x) : (f x:ℝ) = ∑ j ∈ Finset.range M, F j x := by
    calc _ = ∑ j ∈ Finset.range (f x), F j x := by
           have hj (j) (hj : j∈Finset.range (f x)) : F j x=1 :=
             indicator_of_mem (show x∈{y | f y≤j}ᶜ from Nat.not_le.mpr (Finset.mem_range.mp hj)) _
           rw [Finset.sum_congr rfl hj]
           simp
         _ = _ := Finset.sum_subset (Finset.range_mono (hM x)) fun j _ h =>
           indicator_of_notMem (show x∉{y | f y≤j}ᶜ from fun hh => hh (Nat.le_of_not_gt (fun h' => h (Finset.mem_range.mpr h')))) _
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => hF j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [show (∫ x, F j x ∂μ)=μ.real {x | f x≤j}ᶜ from integral_indicator_one (hm j).compl,
    measureReal_compl (hm j),probReal_univ]

/-- The conditional Haar mean on a prefix, defined without choosing a
measurable eigenbasis. -/
def prefixMean (k : ℕ) (ε : ℝ) (x : PrefixIndex (k+1)→ℝ) : ℝ :=
  ∑ j ∈ Finset.range (35*(2^(k+3))^2), (1-prefixFraction k j ε x)

theorem measurable_prefixMean (k : ℕ) (ε : ℝ) : Measurable (prefixMean k ε) :=
  Finset.measurable_sum _ (fun j _ => measurable_const.sub (measurable_prefixFraction k j ε))

theorem prefixMean_eq (k : ℕ) {ε : ℝ} (hε : 0≤ε) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, let n := k+3
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      let H : selfAdjoint (Register n) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let e := (qubitConfigFin n).trans (prefixPhaseEnergyEquiv k)
      prefixMean k ε x=meanCost (by dsimp [n]; omega) e (hermitianEigenbasisUnitary H.2.isHermitian) hε := by
  filter_upwards [ae_all_iff.mpr (fun j => prefixFraction_eq k j ε)] with ω hw
  intro n x H e
  let V := hermitianEigenbasisUnitary H.2.isHermitian
  have hn : 2≤n := by dsimp only [n]; omega
  let f := phaseCost hn e V hε
  have hM (z) : f z≤35*(2^n)^2 := by
    apply (phaseCost_le hn e V hε z).mpr
    exact (DiagonalSynthesis.MultiplexedPhases.quadratic_eigenbasis_phases hn V
      (fun j => fourier 1 (RHTower.zeroAnchoredPhase _ z (e j))) (fun _ => by rw [fourier_apply,Circle.norm_coe])).approx hε
  change _=∫ z, (f z:ℝ)
  rw [discrete_layer_cake volume f (measurable_phaseCost ..) _ hM]
  apply Finset.sum_congr rfl
  intro j _
  rw [hw j]
  change 1-volume.real (projectiveContinuousCircuitCaptureTarget e V j ε)=1-volume.real {z | f z≤j}
  apply congrArg (fun A => (1:ℝ)-volume.real A)
  ext z
  exact (mem_projectiveContinuousCircuitCaptureTarget_iff e V j ε z).trans (phaseCost_le hn e V hε z).symm

/-- On one draw the same Borel mean controls every integer budget.
This permits choosing the tested budget after reading the prefix. -/
theorem prefix_mean_tails (k : ℕ) {ε u : ℝ} (hε : 0≤ε) (hu : 0≤u) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, let K := k+3
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      let m := prefixMean k ε x
      let q := Real.exp (-u^2/(2*(((2^K-1:ℕ):ℝ)*(((35*2^K:ℕ):ℝ)/2)^2)))
      ∀ s : ℕ, ((s:ℝ)+u ≤ m → prefixFraction k s ε x ≤ q) ∧
        (m+u ≤ (s:ℝ)+1 → 1-prefixFraction k s ε x ≤ q) := by
  filter_upwards [prefixMean_eq k hε,ae_all_iff.mpr (fun s => prefixFraction_eq k s ε)] with ω hM hF
  intro K x m q s
  let H : selfAdjoint (Register K) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
  let e := (qubitConfigFin K).trans (prefixPhaseEnergyEquiv k)
  change ((s:ℝ)+u ≤ prefixMean k ε x → prefixFraction k s ε x ≤ q) ∧
    (prefixMean k ε x+u ≤ (s:ℝ)+1 → 1-prefixFraction k s ε x ≤ q)
  rw [hM,hF s]
  exact dimension_tails (by dsimp only [K]; omega) e (hermitianEigenbasisUnitary H.2.isHermitian) hε hu s

#print axioms prefix_mean_tails
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
