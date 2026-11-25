import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost.Rate

/-! # Open and closed event bounds at speed 1/h for ordered prime energies -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost

open Set Filter Topology MeasureTheory Endpoints _root_.RHTower
attribute [local instance] Classical.propDecidable

theorem continuous_rate (c d β : ℝ) (k : ℕ) : Continuous (rate c d (k := k) β) :=
  continuous_const.sub ((continuous_finset_sum Finset.univ fun i _ => continuous_apply i).const_mul (1-β))

private theorem prefactor (h : Ioi (0:ℝ)) (x : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.exp (x/h.val)*a/b = Real.exp ((x+h.val*Real.log a-h.val*Real.log b)/h.val) := by
  have hw (z : ℝ) : h.val*z/h.val = z := mul_div_cancel_left₀ z (show 0 < h.val from h.property).ne'
  rw [sub_div,add_div,hw,hw,Real.exp_sub,Real.exp_add,Real.exp_log ha,Real.exp_log hb]

private theorem eventWeight_lower (S : Finset Nat.Primes) (β : ℝ) (h : Ioi (0:ℝ)) {k : ℕ}
    (U G : Set (Fin k → ℝ)) (hUG : U ⊆ G) (x : ℝ)
    (hx : ∀ R : BreadthSubset k ↥S, spectrum h R ∈ U → x ≤ (1-β)*energyOf R) :
    Real.exp x*eventWeight S 1 h k U ≤ eventWeight S β h k G := by
  rw [eventWeight,eventWeight,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro R _
  by_cases hr : spectrum h R ∈ U
  · rw [if_pos hr,if_pos (hUG hr),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith only [hx R hr]
  · rw [if_neg hr,mul_zero]
    split <;> positivity

private theorem configuration_exponent {c d β : ℝ} (h : Ioi (0:ℝ)) {k : ℕ} (R : BreadthSubset k ↥(added c d h)) :
    (1-β)*energyOf R*h.val = pressure c d k β-rate c d β (spectrum h R) := by
  rw [rate,sum_spectrum]
  ring

private theorem log_ratio_limit {c d : ℝ} (hc : 0 < c) (hcd : c < d) (β t : ℝ) {k : ℕ} (hk : 0 < k)
    {A : Ioi (0:ℝ) → ℝ} (hA : Tendsto (fun h => h.val*Real.log (A h)) criticalApproach (𝓝 0)) :
    Tendsto (fun h => pressure c d k β-t+h.val*Real.log (A h)-h.val*Real.log (coefficient (added c d h) β k))
      criticalApproach (𝓝 (-t)) := by
  have H := (hA.const_add (pressure c d k β-t)).sub (pressure_limit hc hcd β hk)
  rwa [show pressure c d k β-t+0-pressure c d k β = -t by ring] at H

/-- Closed events missing the admissible band satisfy the bound at every finite rate. On the band,
the minimum rate over the event controls its probability. -/
theorem closed_upper {c d : ℝ} (hc : 0 < c) (hcd : c < d) (β : ℝ) {k : ℕ} (hk : 0 < k)
    {C : Set (Fin k → ℝ)} (hC : IsClosed C) (r : ℝ)
    (hr : ∀ v ∈ orderedBand c d k ∩ C, r < rate c d β v) :
    ∀ᶠ h in criticalApproach, (thermalLaw c d h β k C : ℝ) ≤ Real.exp (-r/h.val) := by
  obtain ⟨t,hrt,ht⟩ : ∃ t > r, ∀ v ∈ orderedBand c d k ∩ C, t ≤ rate c d β v := by
    by_cases hn : (orderedBand c d k ∩ C).Nonempty
    · obtain ⟨z,hz,hm⟩ := ((orderedBand_compact c d k).inter_right hC).exists_isMinOn hn (continuous_rate c d β k).continuousOn
      exact ⟨_,hr z hz,isMinOn_iff.mp hm⟩
    · exact ⟨r+1,lt_add_of_pos_right _ zero_lt_one,fun v hv => False.elim (hn ⟨v,hv⟩)⟩
  have hA := pressure_limit hc hcd 1 hk
  rw [pressure,if_pos le_rfl,sub_self,zero_mul] at hA
  have hratio := log_ratio_limit hc hcd β t hk hA
  filter_upwards [hratio.eventually_lt_const (neg_lt_neg hrt),
    (coefficient_limit hc hcd k).eventually_const_lt (critical_limit_pos hc hcd k),
    eventually_positive hc hcd β (fun _ : Fin k → ℝ => (0:ℝ))] with h hlog h1 hβ
  let S := added c d h
  have he := eventWeight_le S β ((pressure c d k β-t)/h.val) h k C (fun R hR => by
    apply (le_div_iff₀ (show 0 < h.val from h.property)).mpr
    rw [configuration_exponent h R]
    exact sub_le_sub_left (ht _ ⟨spectrum_mem_band h R,hR⟩) _)
  calc (thermalLaw c d h β k C : ℝ) = eventWeight S β h k C/coefficient S β k := thermalLaw_event h k hC.measurableSet hβ.1
       _ ≤ (Real.exp ((pressure c d k β-t)/h.val)*coefficient S 1 k)/coefficient S β k :=
         div_le_div_of_nonneg_right he hβ.1.le
       _ = _ := prefactor h _ h1 hβ.1
       _ ≤ _ := Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hlog.le h.property.le)

/-- Every neighborhood of v has probability at least exp(−r/h) for any r strictly above its rate. -/
theorem open_lower {c d : ℝ} (hc : 0 < c) (hcd : c < d) (β : ℝ) {k : ℕ} (hk : 0 < k)
    {G : Set (Fin k → ℝ)} (hG : IsOpen G) {v : Fin k → ℝ} (hv : v ∈ orderedBand c d k)
    (hvG : v ∈ G) (r : ℝ) (hr : rate c d β v < r) :
    ∀ᶠ h in criticalApproach, Real.exp (-r/h.val) ≤ (thermalLaw c d h β k G : ℝ) := by
  obtain ⟨t,hvt,htr⟩ := exists_between hr
  let U := G ∩ (rate c d β) ⁻¹' Iio t
  have hU : IsOpen U := hG.inter (isOpen_Iio.preimage (continuous_rate c d β k))
  obtain ⟨a,ha,haU⟩ := eventWeight_eventually_pos hc hcd hv hU ⟨hvG,hvt⟩
  have h0 : Tendsto (Subtype.val : Ioi (0:ℝ) → ℝ) criticalApproach (𝓝[>] 0) := tendsto_comap
  have hA := (h0.mono_right nhdsWithin_le_nhds).mul_const (Real.log a)
  rw [zero_mul] at hA
  have hratio := log_ratio_limit hc hcd β t hk (A := fun _ => a) hA
  filter_upwards [haU,hratio.eventually_const_lt (neg_lt_neg htr),
    eventually_positive hc hcd β (fun _ : Fin k → ℝ => (0:ℝ))] with h hU' hlog hβ
  let S := added c d h
  have he := eventWeight_lower S β h U G inter_subset_left ((pressure c d k β-t)/h.val) (fun R hR => by
    apply (div_le_iff₀ (show 0 < h.val from h.property)).mpr
    rw [configuration_exponent h R]
    exact sub_le_sub_left (show rate c d β (spectrum h R) < t from hR.2).le _)
  calc Real.exp (-r/h.val) ≤ Real.exp ((pressure c d k β-t+h.val*Real.log a-h.val*Real.log (coefficient S β k))/h.val) :=
         Real.exp_le_exp.mpr (div_le_div_of_nonneg_right hlog.le h.property.le)
       _ = (Real.exp ((pressure c d k β-t)/h.val)*a)/coefficient S β k := (prefactor h _ ha hβ.1).symm
       _ ≤ eventWeight S β h k G/coefficient S β k := div_le_div_of_nonneg_right
         ((mul_le_mul_of_nonneg_left hU' (Real.exp_pos _).le).trans he) hβ.1.le
       _ = (thermalLaw c d h β k G : ℝ) := (thermalLaw_event h k hG.measurableSet hβ.1).symm

#print axioms closed_upper
#print axioms open_lower

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.SpectrumCost
