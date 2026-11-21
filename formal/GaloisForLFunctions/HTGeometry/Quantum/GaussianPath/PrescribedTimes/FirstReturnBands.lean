import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.MeasurableTest

/-! # Timing resolution for the actual first return after the first crossing -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes
noncomputable section

private theorem inverse_power_loss {a : ℝ} (ha : 1 ≤ a) (m : ℕ) :
    1 - a⁻¹^m ≤ (m:ℝ)*(a-1) := by
  have hp := zero_lt_one.trans_le ha
  have hi := (inv_le_one₀ hp).mpr ha
  have hneg := inv_nonneg.mpr hp.le
  have hstep : 1-a⁻¹ ≤ a-1 := calc
    _ ≤ a*(1-a⁻¹) := le_mul_of_one_le_left (sub_nonneg.mpr hi) ha
    _ = a-1 := by rw [mul_sub,mul_one,mul_inv_cancel₀ hp.ne']
  induction m with
  | zero => simp
  | succ m ih =>
    have h := mul_le_of_le_one_left (sub_nonneg.mpr hi) (pow_le_one₀ hneg hi (n := m))
    rw [pow_succ,Nat.cast_succ]
    linarith only [ih,h,hstep]

/-- Among draws that have survived to T after the first crossing, at most
the fraction m(a−1) have their first return by aT. The bound holds at
every elapsed time and every budget. -/
theorem gaussian_first_return_band (n j s : ℕ) {T a : ℝ} (hT : 0 ≤ T) (ha : 1 ≤ a) :
    let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
    let m := Fintype.card (ChainLabel (n+2))
    let Δ := crossingWait n j s
    μ.real {x | T < Δ x ∧ Δ x ≤ a*T} ≤ m*(a-1)*μ.real {x | T < Δ x} := by
  intro μ m Δ
  let E := fun t : ℝ => {x | t < Δ x}
  have hm (t : ℝ) : MeasurableSet (E t) := measurableSet_lt measurable_const (measurable_crossingWait _ _ _)
  have hp := zero_lt_one.trans_le ha
  have he : (fun x : PrefixIndex n → ℝ => a • x) ⁻¹' E T = E (a*T) := by
    ext x
    change T < Δ (a • x) ↔ a*T < crossingWait n j s x
    rw [← smul_crossingWait n j s hp x]
    exact (mul_lt_mul_iff_right₀ hp).symm
  have hs : μ.real (E T) ≤ a^m * μ.real (E (a*T)) := by
    simpa only [he,Fintype.card_fin] using gaussian_dilation_comparison ha (E T) (hm T)
  have hq : μ.real (E T)*a⁻¹^m ≤ μ.real (E (a*T)) := by
    rw [inv_pow,←div_eq_mul_inv]
    exact (div_le_iff₀ (pow_pos hp m)).mpr (hs.trans_eq (mul_comm ..))
  have hset : {x | T < Δ x ∧ Δ x ≤ a*T} = E T \ E (a*T) := by ext x; simp [E]
  have hsub : E (a*T) ⊆ E T := fun _ hx => (le_mul_of_one_le_left hT ha).trans_lt hx
  rw [hset,measureReal_sdiff (μ := μ) hsub (hm _)]
  change μ.real (E T) - μ.real (E (a*T)) ≤ _ * μ.real (E T)
  have hbound := mul_le_mul_of_nonneg_right (inverse_power_loss ha m) (measureReal_nonneg (μ := μ) (s := E T))
  linarith only [hq,hbound]

/-- Each budget may have its own prescribed date at each prefix length.
Almost surely all first waits miss their prescribed bands simultaneously
on sufficiently large prefixes. The admissible dates start at zero. -/
theorem gaussian_first_return_avoids_prescribed_bands (j q : ℕ → ℕ) (t : ℕ → ℕ → ℝ) :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop,
      let m := Fintype.card (ChainLabel (k+3))
      let a := 1 + (1/2:ℝ)^k/(((q k:ℝ)+1)*m)
      let x := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
      ∀ s ≤ q k, crossingWait (k+1) (j k) s x ∉ Ioc |t k s| (a*|t k s|) := by
  let m (k : ℕ) := Fintype.card (ChainLabel (k+3))
  let a (k : ℕ) := 1 + (1/2:ℝ)^k/(((q k:ℝ)+1)*m k)
  let x (k : ℕ) (ω : PathPauliDisorder) := fun i => pathPauliDisorderShell ω (k+1) (pathCoeffEquiv (k+1) i)
  let E (k s : ℕ) := crossingWait (k+1) (j k) s ⁻¹' Ioc |t k s| (a k*|t k s|)
  let U (k : ℕ) := ⋃ s ∈ Finset.range (q k+1), E k s
  have hm (k : ℕ) : MeasurableSet (U k) := MeasurableSet.iUnion fun s =>
    MeasurableSet.iUnion fun _ => measurableSet_Ioc.preimage (measurable_crossingWait _ _ _)
  have hmass (k : ℕ) : pathPauliDisorderLaw (x k ⁻¹' U k) ≤ (1/2:ℝ≥0∞)^k := by
    let μ := Measure.pi (fun _ : PrefixIndex (k+1) => gaussianReal 0 1)
    have hmpos : 0 < (m k : ℝ) := by
      have hi := ((pathCoeffEquiv (k+1)).symm (Sum.inl (0,0))).isLt
      exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hi : 0 < m k)
    have hq : 0 < (q k:ℝ)+1 := by positivity
    have ha : 1 ≤ a k := le_add_of_nonneg_right (div_nonneg (by positivity) (mul_pos hq hmpos).le)
    have hcost : (m k:ℝ)*(a k-1) = (1/2:ℝ)^k/((q k:ℝ)+1) := by
      dsimp only [a]
      rw [add_sub_cancel_left]
      field_simp
    have hE (s : ℕ) : μ.real (E k s) ≤ (1/2:ℝ)^k/((q k:ℝ)+1) := by
      have h := gaussian_first_return_band (k+1) (j k) s (abs_nonneg (t k s)) ha
      apply h.trans
      rw [←hcost]
      exact mul_le_of_le_one_right (mul_nonneg hmpos.le (sub_nonneg.mpr ha)) (measureReal_le_one (μ := μ))
    have hU : μ.real (U k) ≤ (1/2:ℝ)^k := calc
      _ ≤ ∑ s ∈ Finset.range (q k+1), μ.real (E k s) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _s ∈ Finset.range (q k+1), (1/2:ℝ)^k/((q k:ℝ)+1) := Finset.sum_le_sum fun s _ => hE s
      _ = _ := by rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_add,Nat.cast_one,mul_comm,div_mul_cancel₀ _ hq.ne']
    have hmp := gaussian_pauli_prefix_coordinates_law (k+1)
    have he : pathPauliDisorderLaw (x k ⁻¹' U k) = μ (U k) := hmp.measure_preimage (hm k).nullMeasurableSet
    rw [he,←ENNReal.ofReal_toReal (measure_ne_top μ (U k))]
    apply (ENNReal.ofReal_le_ofReal hU).trans_eq
    rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/2),one_div,ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
    norm_num
  have hgood : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ k : ℕ in atTop, ω ∉ x k ⁻¹' U k := by
    apply ae_eventually_notMem
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hmass)
    simp only [one_div,ENNReal.tsum_geometric_two]
    norm_num
  filter_upwards [hgood] with ω hω
  filter_upwards [hω] with k hk
  intro _ _ _ s hs h
  exact hk (mem_iUnion₂.mpr ⟨s,Finset.mem_range.mpr (Nat.lt_succ_of_le hs),h⟩)

#print axioms gaussian_first_return_band
#print axioms gaussian_first_return_avoids_prescribed_bands
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes
