import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NormalizedRadius.WeakBox

/-! # Size-independent first-excursion survival at fixed coupling norm -/
open Set Filter MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NormalizedRadius
open PrescribedTimes
noncomputable section

/-- After fixing the Gaussian coefficient norm at its root mean square,
the same T⁻¹⁸ floor delays the true onset and all half-budget first waits.
Its constant is independent of both the prefix and the deadline. -/
theorem gaussian_normalized_joint_survival :
    ∃ c > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (k+3)
      let r := sqrt (Fintype.card (PrefixIndex n):ℝ)
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      ∀ T ≥ (1:ℝ), c ≤ T^18*μ.real {x | T<crossingOrigin n P (9/80) (atRadius r x) ∧
        ∀ s≤P/2, T<crossingWait n P s (atRadius r x)} := by
  let α := sqrt (bulkMass/4)
  have hα : 0<α := sqrt_pos.mpr (div_pos bulkMass_pos (by norm_num))
  have hp₁ : bulkMass≤1 := (measureReal_mono (μ:=gaussianReal 0 1) (subset_univ (Icc (1:ℝ) 2))).trans_eq probReal_univ
  have hα₁ : α≤1 := sqrt_le_one.mpr (by linarith only [hp₁])
  let c := ((2*gaussianDensityFloor)*α/1800)^18*(bulkMass/2)
  have hc : 0<c := mul_pos (pow_pos (div_pos (mul_pos (mul_pos two_pos gaussianDensityFloor_pos) hα) (by norm_num)) _) (half_pos bulkMass_pos)
  refine ⟨c,hc,?_⟩
  filter_upwards [gaussian_two_cut_travel,eventually_ge_atTop 3] with k hf hk
  intro n P r μ T hT
  obtain ⟨a,b,hab,htravel⟩ := hf
  let S := cutSet a b
  let V := T/α
  let δ := 1/(1800*V)
  have ht := zero_lt_one.trans_le hT
  have hv : 0<V := div_pos ht hα
  have hv₁ : 1 ≤ V := (le_div_iff₀ hα).mpr (by rw [one_mul]; exact hα₁.trans hT)
  have hδ : 0<δ := one_div_pos.mpr (mul_pos (by norm_num) hv)
  have hδ₁ : δ≤1 := (div_le_one (mul_pos (by norm_num) hv)).mpr (by linarith only [hv₁])
  have hm : 36≤Fintype.card (PrefixIndex n) := by
    rw [Fintype.card_congr (pathCoeffEquiv n)]
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    dsimp only [n]; omega
  have hr : 0<r := sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  let E := {x : PrefixIndex n → ℝ | (∀ i∈S, |x i|≤δ) ∧ r*α≤coefficientNorm x}
  let F := {x : PrefixIndex n → ℝ | T<crossingOrigin n P (9/80) (atRadius r x) ∧
    ∀ s≤P/2, T<crossingWait n P s (atRadius r x)}
  let X := fun ω i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  have hX : MeasurePreserving X pathPauliDisorderLaw μ := gaussian_pauli_prefix_coordinates_law n
  have hE : MeasurableSet E := by
    have he : MeasurableSet {x : PrefixIndex n → ℝ | ∀ i∈S, |x i|≤δ} := by
      rw [show {x : PrefixIndex n → ℝ | ∀ i∈S, |x i|≤δ}=⋂ i ∈ S, {x | |x i|≤δ} by ext; simp]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        measurableSet_le (measurable_pi_apply i).abs measurable_const
    exact he.inter (measurableSet_le measurable_const (MeasurableEquiv.toLp 2 (PrefixIndex n → ℝ)).measurable.norm)
  have hs : X ⁻¹' E ≤ᵐ[pathPauliDisorderLaw] X ⁻¹' F := by
    filter_upwards [htravel] with ω hw hx
    let x := X ω
    change (∀ i∈S, |x i|≤δ) ∧ r*α≤coefficientNorm x at hx
    let q := r/coefficientNorm x
    have hn : 0<coefficientNorm x := (mul_pos hr hα).trans_le hx.2
    have hq : 0<q := div_pos hr hn
    have hq' : q≤1/α := (div_le_div_iff₀ hn hα).mpr (by simpa only [one_mul] using hx.2)
    have htime : q*T≤V := (mul_le_mul_of_nonneg_right hq' ht.le).trans_eq (by dsimp only [V]; ring)
    obtain ⟨hfirst,_⟩ := lt_min_iff.mp (hw V hv hx.1 0 (Nat.zero_le _))
    constructor
    · apply (mul_lt_mul_iff_right₀ hq).mp
      change q*T < q*crossingOrigin n P (9/80) (q • x)
      rw [smul_crossingOrigin _ _ _ hq]
      exact htime.trans_lt hfirst
    · intro s hbudget
      apply (mul_lt_mul_iff_right₀ hq).mp
      change q*T < q*crossingWait n P s (q • x)
      rw [smul_crossingWait _ _ _ hq]
      exact htime.trans_lt (lt_min_iff.mp (hw V hv hx.1 s hbudget)).2
  have hμ : μ E ≤ μ F := by
    rw [←hX.measure_preimage hE.nullMeasurableSet]
    apply (measure_mono_ae hs).trans
    simpa only [hX.map_eq] using Measure.le_map_apply (μ:=pathPauliDisorderLaw) hX.measurable.aemeasurable F
  have hmass := (weak_box_norm n S (cutSet_card hab) hm hδ.le hδ₁).trans
    (ENNReal.toReal_mono (measure_ne_top _ _) hμ)
  apply le_trans _ (mul_le_mul_of_nonneg_left hmass (pow_nonneg ht.le 18))
  change c≤T^18*(((2*gaussianDensityFloor)*δ)^18*(bulkMass/2))
  rw [←mul_assoc,←mul_pow]
  have he : T*((2*gaussianDensityFloor)*δ)=(2*gaussianDensityFloor)*α/1800 := by
    dsimp only [δ,V]; field_simp
  rw [he]

#print axioms gaussian_normalized_joint_survival
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NormalizedRadius
