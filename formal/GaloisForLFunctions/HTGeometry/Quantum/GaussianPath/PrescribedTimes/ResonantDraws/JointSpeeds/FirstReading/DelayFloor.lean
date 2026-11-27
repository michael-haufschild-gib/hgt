import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.JointSpeeds.ScalarProbes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.FirstExcursion
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.GeodesicPacking

/-! # Time needed for independent late scalar readings at the original crossing -/
open Set Filter MeasureTheory ProbabilityTheory Topology Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
open ResonantDraws SharpOccupation Dephasing.GappedSpin.CentralCut.FreeAxis
open private orbitCircuitDistance_antitone_budget from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.GeodesicPacking
noncomputable section
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- Any probes confined to the first T time units after the original
crossing miss together on the positive-coupling survival sector. Probe
dates and the choice of budget may vary across the observations. -/
theorem first_window_miss_floor :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop, let n := k+1
      let K := k+3
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n P (9/80)
      ∀ T ≥ (1:ℝ), ∀ (I : Type) (j : I→ℕ), (∀ i, j i ≤ P/2) →
        ∀ d : I→(PrefixIndex n→ℝ)→ℝ, (∀ i x, d i x∈Icc 0 T) →
          exp (-C*(K:ℝ)^2) ≤ T^6*μ.real {x | (∀ l, x l∈Icc (1/20:ℝ) 4) ∧
            ∀ i, (1/10:ℝ)<pathGateDistance n (j i) x (σ x+d i x)} := by
  obtain ⟨C,hC,_,_,h⟩ := positive_first_excursions
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with k hk
  intro n K P μ σ T hT I j hj d hd
  obtain ⟨E,_,hprice,hE⟩ := hk T hT
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  let B := {x | (∀ l, x l∈Icc (1/20:ℝ) 4) ∧ ∀ i, (1/10:ℝ)<pathGateDistance n (j i) x (σ x+d i x)}
  have hX := gaussian_pauli_prefix_coordinates_law n
  have hincl : E ≤ᵐ[pathPauliDisorderLaw] X ⁻¹' B := by
    filter_upwards [hE] with ω hw
    intro hω
    obtain ⟨hbox,_,hwait,_,_⟩ := hw hω
    refine ⟨hbox,?_⟩
    intro i
    apply lt_of_not_ge
    intro hfit
    have he := (crossingWait_le_iff n P (j i) (X ω) T).mpr
      ⟨σ (X ω)+d i (X ω),⟨le_add_of_nonneg_right (hd i _).1,add_le_add le_rfl (hd i (X ω)).2⟩,hfit⟩
    exact (not_le_of_gt (hwait _ (hj i))) he
  exact hprice.trans (mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top μ B)
    ((measure_mono_ae hincl).trans (hX.measure_preimage_le B))) (by positivity))

/-- For q prescribed incommensurate speeds in [0,1], the conditional
late miss probability is at most (1-p)^q at every half budget. Even
on the positive coefficient box, reaching twice the actual limiting
probability forces 6 log T ≥ qp - C K² - log 2. -/
theorem independent_budget_delay_floor :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop, let n := k+1
      let K := k+3
      let D := (2:ℕ)^K
      let p := (D:ℝ)*physicalArc (1/10)^(D-1)
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n P (9/80)
      ∀ j ≤ P/2, ∀ (q : ℕ) (c : Fin q→ℝ), RationallyIndependentFrequency c → (∀ i, c i∈Icc (0:ℝ) 1) →
        ∀ B : Set (PrefixIndex n→ℝ), MeasurableSet B → {x | ∀ i, x i∈Icc (1/20:ℝ) 4}⊆B →
        let f := fun t => μ.real (B ∩ {x | ∀ i, (1/10:ℝ)<pathGateDistance n j x (σ x+c i*t)})
        ∃ L ≤ μ.real B*(1-p)^q, Tendsto f atTop (𝓝 L) ∧
          ∀ T ≥ (1:ℝ), f T ≤ 2*L → (q:ℝ)*p-C*(K:ℝ)^2 ≤ 6*log T+log 2 := by
  obtain ⟨C,hC,h⟩ := first_window_miss_floor
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with k hk
  intro n K D p P μ σ j hj q c hc hb B hB hbox f
  have hε : (1/10:ℝ)∈Ioo (0:ℝ) (sqrt 2) := by
    refine ⟨by norm_num,?_⟩
    have h := sq_sqrt (by norm_num : (0:ℝ)≤2)
    nlinarith only [h,sqrt_nonneg 2]
  have hh := scalar_probe_pattern k 0 hε c hc false (fun _ => false) B hB
  have hscalar : Tendsto (fun t => μ.real (B ∩ {x | ∀ i, (1/10:ℝ)<pathGateDistance n 0 x (σ x+c i*t)}))
      atTop (𝓝 (μ.real B*(1-p)^q)) := by
    simpa only [Bool.false_eq_true,if_false,iff_false,not_le,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  let L := ∫ ω in X ⁻¹' B, (1-affordablePhaseMass k j (1/10) ω)^q ∂pathPauliDisorderLaw
  have hlim : Tendsto f atTop (𝓝 L) := by
    have h := joint_first_excursion_snapshot k P c hc (fun _ => false) (fun _ => false)
      (fun _ => 0) (fun _ => j) (fun _ => 1/10) B hB
    simpa only [Bool.false_eq_true,if_false,iff_false,not_le,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using h
  have hu : L ≤ μ.real B*(1-p)^q := by
    refine le_of_tendsto_of_tendsto hlim hscalar (Eventually.of_forall fun t => ?_)
    refine measureReal_mono ?_ (measure_ne_top μ _)
    rintro x ⟨hx,hm⟩
    refine ⟨hx,fun i => (hm i).trans_le ?_⟩
    exact orbitCircuitDistance_antitone_budget (prefixGenerator n x) (Nat.zero_le j) (σ x+c i*t)
  refine ⟨L,hu,hlim,?_⟩
  intro T hT hmiss
  have hpos := zero_lt_one.trans_le hT
  have hfloor := hk T hT (Fin q) (fun _ => j) (fun _ => hj) (fun i _ => c i*T)
    (fun i _ => ⟨mul_nonneg (hb i).1 hpos.le,(mul_le_mul_of_nonneg_right (hb i).2 hpos.le).trans_eq (one_mul _)⟩)
  have hprob : exp (-C*(K:ℝ)^2) ≤ T^6*f T :=
    hfloor.trans (mul_le_mul_of_nonneg_left
      (measureReal_mono (fun _ h => ⟨hbox h.1,h.2⟩) (measure_ne_top μ _)) (pow_nonneg hpos.le _))
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  obtain ⟨ω,hw⟩ := (scalar_phase_mass k hε).exists
  have heq : affordablePhaseMass k 0 (1/10) ω=p := hw
  have hp : p≤1 := heq ▸ (show affordablePhaseMass k 0 (1/10) ω≤1 from measureReal_le_one)
  have hbase : 1-p ≤ exp (-p) := by linarith only [add_one_le_exp (-p)]
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hp) hbase q
  rw [←exp_nat_mul,mul_neg] at hpow
  have hsel : μ.real B*(1-p)^q ≤ (1-p)^q :=
    mul_le_of_le_one_left (pow_nonneg (sub_nonneg.mpr hp) q) measureReal_le_one
  have hprod := hprob.trans (mul_le_mul_of_nonneg_left
    (hmiss.trans (mul_le_mul_of_nonneg_left (hu.trans (hsel.trans hpow)) (by norm_num))) (pow_nonneg hpos.le 6))
  have he := log_le_log (exp_pos _) hprod
  rw [log_exp,log_mul (pow_pos hpos 6).ne' (mul_pos (by norm_num) (exp_pos _)).ne',
    log_pow,log_mul (by norm_num) (exp_pos _).ne',log_exp] at he
  change -C*(K:ℝ)^2 ≤ (6:ℝ)*log T+(log 2+ -((q:ℝ)*p)) at he
  linarith only [he]

#print axioms first_window_miss_floor
#print axioms independent_budget_delay_floor
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.JointSpeeds
