import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Fluctuations.MaximumAtom
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Fluctuations.SelectedTails

/-! # Late observations of the actual maximum after the original excursion -/
open Set Filter MeasureTheory ProbabilityTheory Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
open JointSpeeds
open private measurable_selected_test from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Fluctuations.SelectedTails
noncomputable section

/-- A date attains the all-time minimum-circuit maximum exactly when
its predecessor budget fails. A zero maximum is attained at every date. -/
private theorem maximum_test (n : ℕ) {ε : ℝ} (hε : 0 < ε) (x : PrefixIndex n→ℝ) (t : ℝ) :
    let m := prefixMaximum n ε x
    (∀ s, pathGateDistance n s x t ≤ ε ↔ m ≤ s) ↔ m=0 ∨ ε < pathGateDistance n (m-1) x t := by
  intro m
  have hcap (s : ℕ) (h : m ≤ s) : pathGateDistance n s x t ≤ ε := by
    have hx : x∈(prefixMaximum n ε) ⁻¹' Iic s := h
    rw [prefixMaximum_sublevel n s hε] at hx
    exact hx t
  constructor
  · intro hall
    by_cases he : m=0
    · exact Or.inl he
    · exact Or.inr (lt_of_not_ge (fun hp => (by omega : ¬m ≤ m-1) ((hall _).mp hp)))
  · intro h s
    refine ⟨?_,hcap s⟩
    intro fit
    rcases h with he|hfail
    · omega
    by_contra! hs
    have hsmall := (hasProjectiveCircuitApproximation_iff_infDist _ s ε).mpr fit
    obtain ⟨z,hz,C,hC,hfit⟩ := hsmall
    exact hfail.not_ge ((hasProjectiveCircuitApproximation_iff_infDist _ (m-1) ε).mp
      ⟨z,hz,C,hC.trans (by omega),hfit⟩)

/-- From either end of the original first excursion, the probability
of observing the exact same-error maximum tends to the selected mass
of its Haar atom. Every positive-mass prefix selection has positive limit. -/
theorem selected_maximum_observation (k P r : ℕ) {ε : ℝ} (hε : 0 < ε) (afterReturn : Bool)
    (B : Set (PrefixIndex (k+1)→ℝ)) (hB : MeasurableSet B) :
    let n := k+1
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
    let σ := crossingOrigin n P (9/80)
    let o := fun x => if afterReturn then σ x+crossingWait n P r x else σ x
    let p := ∫ ω in X ⁻¹' B, maximumAtom k ε (X ω) ∂pathPauliDisorderLaw
    (0 < μ.real B → 0 < p) ∧ Tendsto (fun t => μ.real (B ∩ {x | ∀ s : ℕ,
      pathGateDistance n s x (o x+t) ≤ ε ↔ prefixMaximum n ε x ≤ s})) atTop (𝓝 p) := by
  classical
  intro n μ X σ o p
  let m := prefixMaximum n ε
  let j := fun x => m x-1
  let G := {x | m x≠0}
  let ν := pathPauliDisorderLaw
  letI : IsProbabilityMeasure ν := by dsimp only [ν,pathPauliDisorderLaw]; infer_instance
  have hX : MeasurePreserving X ν μ := gaussian_pauli_prefix_coordinates_law n
  have hm : Measurable m := measurable_prefixMaximum n hε
  have hj : Measurable j := (measurable_of_countable (fun s : ℕ => s-1)).comp hm
  have hG : MeasurableSet G := (measurableSet_eq_fun hm measurable_const).compl
  have ho : Measurable o := by
    cases afterReturn <;> simp only [o,Bool.false_eq_true,if_false,if_true]
    · exact measurable_crossingOrigin ..
    · exact (measurable_crossingOrigin ..).add (measurable_crossingWait ..)
  let f := fun ω => prefixFraction k (j (X ω)) ε (X ω)
  let a := fun ω => maximumAtom k ε (X ω)
  have hfi : Integrable f ν := integrable_selected_fraction k ε j hj
  have hform : a = fun ω => 1-(X ⁻¹' G).indicator f ω := by
    funext ω
    by_cases h : m (X ω)=0
    · rw [indicator_of_notMem (show ω∉X ⁻¹' G from fun hh => hh h)]
      exact (if_pos h).trans (sub_zero (1:ℝ)).symm
    · rw [indicator_of_mem (show ω∈X ⁻¹' G from h)]
      exact if_neg h
  have hai : Integrable a ν := hform ▸ (integrable_const (1:ℝ)).sub (hfi.indicator (hG.preimage hX.measurable))
  have hpos : ∀ᵐ ω ∂ν, 0 < a ω := (maximum_atom_bounds k hε).mono (fun _ h => h.1)
  constructor
  · intro hBpos
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_restrict_of_ae (s:=X ⁻¹' B) (hpos.mono fun _ h => h.le)) hai.integrableOn).mpr
    have he : (Function.support a ∩ X ⁻¹' B : Set PathPauliDisorder) =ᵐ[ν] X ⁻¹' B := by
      filter_upwards [hpos] with ω hw
      exact propext (and_iff_right hw.ne')
    rw [measure_congr he,hX.measure_preimage hB.nullMeasurableSet]
    exact pos_iff_ne_zero.mpr (fun h => hBpos.ne' (by simp [measureReal_def,h]))
  let v := ∫ ω in X ⁻¹' (B ∩ G), f ω ∂ν
  have hp : p=μ.real B-v := by
    change (∫ ω in X ⁻¹' B, a ω ∂ν)=_
    rw [hform,integral_sub (integrable_const _) (hfi.indicator (hG.preimage hX.measurable)).integrableOn,
      setIntegral_indicator (hG.preimage hX.measurable),setIntegral_const,smul_eq_mul,mul_one,
      hX.measureReal_preimage hB.nullMeasurableSet]
    rfl
  have hlim : Tendsto (fun t => μ.real ((B∩G) ∩ {x | pathGateDistance n (j x) x (o x+t) ≤ ε})) atTop (𝓝 v) := by
    have h := selected_fraction_limit k P r ε j hj (B∩G) (hB.inter hG)
    cases afterReturn <;> simp only [o,Bool.false_eq_true,if_false,if_true]
    · exact h.1
    · exact h.2
  rw [hp]
  apply (hlim.const_sub (μ.real B)).congr
  intro t
  let F := {x | pathGateDistance n (j x) x (o x+t) ≤ ε}
  have hF : MeasurableSet F := measurable_selected_test j hj
    (fun s => {x | pathGateDistance n s x (o x+t) ≤ ε}) (fun s => measurable_origin_event n s ε t o ho)
  have he : B ∩ {x | ∀ s, pathGateDistance n s x (o x+t) ≤ ε ↔ prefixMaximum n ε x ≤ s}
      = B \ ((B∩G)∩F) := by
    ext x
    simp only [mem_inter_iff,mem_setOf_eq,Set.mem_sdiff,F,G,maximum_test n hε x,m,j,←not_le]
    tauto
  rw [he,measureReal_sdiff (inter_subset_left.trans inter_subset_left) ((hB.inter hG).inter hF)]

#print axioms selected_maximum_observation
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
