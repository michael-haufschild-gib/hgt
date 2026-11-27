import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.FirstPassageSelection.PhaseWeights.Fluctuations.SelectedFraction

/-! # Late concentration about the individual prefix's mean gate count -/
open Set MeasureTheory ProbabilityTheory Filter Topology Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
noncomputable section

private theorem measurable_selected_test {X : Type*} [MeasurableSpace X]
    (j : X→ℕ) (hj : Measurable j) (E : ℕ→Set X) (hE : ∀ s, MeasurableSet (E s)) :
    MeasurableSet {x | x∈E (j x)} := by
  have he : {x | x∈E (j x)}=⋃ s : ℕ, j ⁻¹' {s} ∩ E s := by
    ext x
    constructor
    · exact fun hx => mem_iUnion.mpr ⟨j x,rfl,hx⟩
    · intro hx
      obtain ⟨s,hs,ht⟩ := mem_iUnion.mp hx
      change x∈E (j x)
      rwa [show j x=s from hs]
  rw [he]
  exact MeasurableSet.iUnion fun s => ((measurableSet_singleton s).preimage hj).inter (hE s)

/-- From either end of the original first excursion, both tails of
the late gate cost about this draw's own Haar mean have the same
bounded-differences exponent, even on arbitrarily rare histories. -/
theorem selected_mean_concentration (k P r : ℕ) {ε u : ℝ} (hε : 0≤ε) (hu : 0≤u)
    (afterReturn : Bool) (B : Set (PrefixIndex (k+1)→ℝ)) (hB : MeasurableSet B) :
    let n := k+1
    let K := k+3
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let σ := crossingOrigin n P (9/80)
    let o := fun x => if afterReturn then σ x+crossingWait n P r x else σ x
    let M := prefixMean k ε
    let q := exp (-u^2/(2*(((2^K-1:ℕ):ℝ)*(((35*2^K:ℕ):ℝ)/2)^2)))
    ∃ a b : ℝ, a ≤ μ.real B*q ∧ b ≤ μ.real B*q ∧
      Tendsto (fun t => μ.real ((B ∩ {x | u≤M x}) ∩
        {x | pathGateDistance n ⌊M x-u⌋₊ x (o x+t)≤ε})) atTop (𝓝 a) ∧
      Tendsto (fun t => μ.real (B ∩ {x | ε<pathGateDistance n ⌊M x+u⌋₊ x (o x+t)})) atTop (𝓝 b) := by
  classical
  intro n K μ σ o M q
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  let ν := pathPauliDisorderLaw
  letI : IsProbabilityMeasure ν := by dsimp only [ν,pathPauliDisorderLaw]; infer_instance
  have hX : MeasurePreserving X ν μ := gaussian_pauli_prefix_coordinates_law n
  have ho : Measurable o := by
    cases afterReturn <;> simp only [o,Bool.false_eq_true,if_false,if_true]
    · exact measurable_crossingOrigin ..
    · exact (measurable_crossingOrigin ..).add (measurable_crossingWait ..)
  let f (j : (PrefixIndex n→ℝ)→ℕ) (ω : PathPauliDisorder) := prefixFraction k (j (X ω)) ε (X ω)
  have test (A : Set (PrefixIndex n→ℝ)) (hA : MeasurableSet A) (j : (PrefixIndex n→ℝ)→ℕ) (hj : Measurable j) :
      Tendsto (fun t => μ.real (A ∩ {x | pathGateDistance n (j x) x (o x+t)≤ε})) atTop
        (𝓝 (∫ ω in X ⁻¹' A, f j ω ∂ν)) := by
    have h := selected_fraction_limit k P r ε j hj A hA
    cases afterReturn <;> simp only [o,Bool.false_eq_true,if_false,if_true]
    · exact h.1
    · exact h.2
  let A := B ∩ {x | u≤M x}
  have hM : Measurable M := measurable_prefixMean k ε
  have hA : MeasurableSet A := hB.inter (measurableSet_le measurable_const hM)
  let j₁ := fun x => ⌊M x-u⌋₊
  let j₂ := fun x => ⌊M x+u⌋₊
  have hj₁ : Measurable j₁ := (hM.sub_const u).nat_floor
  have hj₂ : Measurable j₂ := (hM.add_const u).nat_floor
  let a := ∫ ω in X ⁻¹' A, f j₁ ω ∂ν
  let b := ∫ ω in X ⁻¹' B, f j₂ ω ∂ν
  have hraw := prefix_mean_tails k hε hu
  have hlow : a ≤ μ.real A*q := by
    have hbds : ∀ᵐ ω ∂ν.restrict (X ⁻¹' A), f j₁ ω ≤ q := by
      filter_upwards [ae_restrict_mem (μ:=ν) (hA.preimage hX.measurable),
        ae_restrict_of_ae (s:=X ⁻¹' A) hraw] with ω hω hw
      apply (hw (j₁ (X ω))).1
      have hp := Nat.floor_le (sub_nonneg.mpr (show u≤M (X ω) from hω.2))
      change (⌊M (X ω)-u⌋₊:ℝ)+u ≤ M (X ω)
      linarith only [hp]
    have hh := integral_mono_ae (integrable_selected_fraction k ε j₁ hj₁).integrableOn (integrable_const q) hbds
    rwa [setIntegral_const,smul_eq_mul,hX.measureReal_preimage hA.nullMeasurableSet] at hh
  have hhigh : μ.real B*(1-q) ≤ b := by
    have hbds : ∀ᵐ ω ∂ν.restrict (X ⁻¹' B), 1-q≤f j₂ ω := by
      filter_upwards [ae_restrict_of_ae (s:=X ⁻¹' B) hraw] with ω hw
      have h := (hw (j₂ (X ω))).2 (Nat.lt_floor_add_one (M (X ω)+u)).le
      change 1-f j₂ ω≤q at h
      linarith only [h]
    have hh := integral_mono_ae (integrable_const (1-q)) (integrable_selected_fraction k ε j₂ hj₂).integrableOn hbds
    rwa [setIntegral_const,smul_eq_mul,hX.measureReal_preimage hB.nullMeasurableSet] at hh
  refine ⟨a,μ.real B-b,hlow.trans (mul_le_mul_of_nonneg_right (measureReal_mono inter_subset_left) (exp_pos _).le),
    ?_,test A hA j₁ hj₁,?_⟩
  · linarith only [hhigh]
  apply ((test B hB j₂ hj₂).const_sub (μ.real B)).congr
  intro t
  let F := {x | pathGateDistance n (j₂ x) x (o x+t)≤ε}
  have hF : MeasurableSet F := measurable_selected_test j₂ hj₂
    (fun s => {x | pathGateDistance n s x (o x+t)≤ε}) (fun s => measurable_origin_event n s ε t o ho)
  have he : B ∩ {x | ε<pathGateDistance n (j₂ x) x (o x+t)}=B \ (B ∩ F) := by
    ext x
    simp only [F,mem_inter_iff,mem_setOf_eq,Set.mem_sdiff,←not_le]
    tauto
  rw [he,measureReal_sdiff inter_subset_left (hB.inter hF)]

#print axioms selected_mean_concentration
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.FirstPassageSelection
