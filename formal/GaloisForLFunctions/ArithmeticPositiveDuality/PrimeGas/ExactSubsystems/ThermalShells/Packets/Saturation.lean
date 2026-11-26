import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Balance
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Configurations

/-! # Optimal finite prime thermometry and the isometric midpoint -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets

open Real Filter Topology Set _root_.RHTower
open BinaryOrientation.LargestPrime.Bands
open BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints

/-- Total variation of the actual conditional Born laws on the two packets. -/
def contrast (c d D k β γ : ℝ) (h : Ioi (0:ℝ)) :=
  variation (born β) (born γ) (physical c d D k h)

theorem contrast_limit {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k) (β γ : ℝ) :
    Tendsto (contrast c d D k β γ) criticalApproach (𝓝 |upperProbability D k β-upperProbability D k γ|) := by
  apply ((variation_limit hD hk β γ).comp (translation_limit hc)).congr'
  filter_upwards [physical_window hc hcd hD hk] with h hw
  change variation (shifted β (c/h.val)) (shifted γ (c/h.val)) (both D k (c/h.val)) = variation (born β) (born γ) _
  rw [recode_variation β γ (c/h.val),hw.1]

/-- Conditional probability of occupying the upper packet. -/
def upperRead (c d D k b : ℝ) (h : Ioi (0:ℝ)) := share (born b) (physical c d D k h)
  (selected (added c d h) (high D k (c/h.val)))

theorem physical_upper_limit {c d D k : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k) (b : ℝ) :
    Tendsto (upperRead c d D k b) criticalApproach (𝓝 (upperProbability D k b)) := by
  apply ((upper_limit hD hk b).comp (translation_limit hc)).congr'
  filter_upwards [physical_window hc hcd hD hk] with h hw
  have him := sub_selected_image (Q := high D k (c/h.val)) Finset.subset_union_right hw.1
  change share (shifted b (c/h.val)) (both D k (c/h.val)) (high D k (c/h.val)) = share (born b) _ _
  rw [recode_share b (c/h.val),hw.1,him]

/-- At a single damping parameter the equal-width packet choice is asymptotically fair
precisely when cyclic-order splitting is isometric. -/
theorem split_isometric_iff_fair_packets {c d D : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      Tendsto (upperRead c d D 1 (2*s.re)) criticalApproach (𝓝 (1/2)) := by
  letI := criticalApproach_neBot
  have H := physical_upper_limit hc hcd hD zero_lt_one (2*s.re)
  rw [split_isometric_iff]
  constructor
  · intro he
    simpa only [upperProbability,odds,he,show (2:ℝ)*(1/2)=1 by ring,sub_self,zero_mul,exp_zero,one_mul,one_add_one_eq_two] using H
  · intro ht
    have hh := tendsto_nhds_unique H ht
    have ho := odds_pos D zero_lt_one (2*s.re)
    have e := (div_eq_div_iff (add_pos zero_lt_one ho).ne' (two_ne_zero : (2:ℝ) ≠ 0)).mp hh
    have u : odds D 1 (2*s.re) = 1 := by linarith only [e]
    rw [odds,one_mul,exp_eq_one_iff,mul_eq_zero,or_iff_left hD.ne'] at u
    linarith only [u]

/-- For sufficiently far bands, the yes/no upper-packet measurement attains the full finite
contrast between two ordered distinct temperatures. -/
theorem physical_high_is_cut {c d D k β γ : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D)
    (hk : 0 < k) (hbg : β < γ) :
    ∀ᶠ h in criticalApproach, let H := selected (added c d h) (high D k (c/h.val))
      contrast c d D k β γ h = share (born β) (physical c d D k h) H-share (born γ) (physical c d D k h) H := by
  filter_upwards [physical_window hc hcd hD hk,(translation_limit hc).eventually (high_is_cut hD hk hbg)] with h hw ht
  have him := sub_selected_image (Q := high D k (c/h.val)) Finset.subset_union_right hw.1
  dsimp only
  rw [contrast,recode_variation β γ (c/h.val),recode_share β (c/h.val),recode_share γ (c/h.val),hw.1,him]
  exact ht

/-- The sharp limiting width ratio is necessary and sufficient for actual count-one Born laws. -/
theorem saturation_iff {c d D k β γ : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (hk : 0 < k) (hne : β ≠ γ) :
    Tendsto (contrast c d D k β γ) criticalApproach (𝓝 (tanh (|β-γ| * D/4))) ↔ k=optimal D β γ := by
  letI := criticalApproach_neBot
  have H := contrast_limit hc hcd hD hk β γ
  constructor
  · intro h
    exact (sharp_iff hD hk hne).mp (tendsto_nhds_unique H h)
  · intro hk'
    rwa [← (sharp_iff hD hk hne).mpr hk']

/-- Two equal-width packets saturate at temperatures symmetric around 2 Re(s) exactly when
the cyclic-order split at s preserves norm. -/
theorem split_isometric_iff_equal_packet_saturation {c d D a : ℝ}
    (hc : 0 < c) (hcd : c < d) (hD : 0 < D) (ha : 0 < a) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
      Tendsto (contrast c d D 1 (2*s.re-a) (2*s.re+a)) criticalApproach (𝓝 (tanh (a*D/2))) := by
  let β := 2*s.re-a
  let γ := 2*s.re+a
  have hbg : β < γ := by dsimp [β,γ]; linarith only [ha]
  have hb : |β-γ| * D/4 = a*D/2 := by
    rw [abs_of_neg (sub_neg.mpr hbg)]; dsimp [β,γ]; ring
  change _ ↔ Tendsto (contrast c d D 1 β γ) _ _
  rw [split_isometric_iff,← hb,saturation_iff hc hcd hD zero_lt_one hbg.ne,eq_comm (a := (1:ℝ)),optimal_eq_one_iff hD]
  dsimp [β,γ]; constructor <;> intro h <;> linarith only [h]

/-- Largest contrast among all nonempty physical selections whose total energy span is ≤ D.
The value is zero when the sector has no eligible state. -/
def best (S : Finset Nat.Primes) (D β γ : ℝ) : ℝ := by
  classical
  let F := (Finset.univ : Finset (BreadthSubset 1 ↥S)).powerset
  exact F.sup' (Finset.powerset_nonempty _) fun U =>
    if U.Nonempty ∧ (∀ x ∈ U, ∀ y ∈ U, |energyOf x-energyOf y| ≤ D) then variation (born β) (born γ) U else 0

private theorem le_best {S : Finset Nat.Primes} {D : ℝ} (β γ : ℝ) {U : Finset (BreadthSubset 1 ↥S)}
    (hU : U.Nonempty) (hw : ∀ x ∈ U, ∀ y ∈ U, |energyOf x-energyOf y| ≤ D) :
    variation (born β) (born γ) U ≤ best S D β γ := by
  classical
  unfold best
  apply Finset.le_sup'_of_le _ (Finset.mem_powerset.mpr (Finset.subset_univ U))
  rw [if_pos ⟨hU,hw⟩]

/-- Finite positive-temperature optima are strictly below the asymptotic bound. -/
theorem best_strict (S : Finset Nat.Primes) {D β γ : ℝ} (hD : 0 < D) (hβ : 0 < β) (hγ : 0 < γ) (hne : β ≠ γ) :
    best S D β γ < tanh (|β-γ| * D/4) := by
  classical
  unfold best
  apply (Finset.sup'_lt_iff _).mpr
  intro U _
  split
  · next h => exact strict_at_positive_temperatures h.1 hβ hγ hne hD h.2
  · have hη := mul_pos (abs_pos.mpr (sub_ne_zero.mpr hne)) hD
    rw [← defect_eq]
    exact div_pos (sub_pos.mpr (one_lt_exp_iff.mpr (half_pos hη))) (add_pos (exp_pos _) zero_lt_one)

/-- In every moving band the optimum over genuine positive-temperature selections converges
to the universal thermal bound, although every finite optimum is strictly smaller. -/
theorem best_limit {c d D β γ : ℝ} (hc : 0 < c) (hcd : c < d) (hD : 0 < D)
    (hβ : 0 < β) (hγ : 0 < γ) (hne : β ≠ γ) :
    Tendsto (fun h => best (added c d h) D β γ) criticalApproach (𝓝 (tanh (|β-γ| * D/4))) := by
  let k := optimal D β γ
  have hk : 0 < k := exp_pos _
  have hlo := (saturation_iff hc hcd hD hk hne).mpr rfl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [physical_window hc hcd hD hk] with h hw
    exact le_best β γ hw.2.1 hw.2.2
  · exact Filter.Eventually.of_forall fun h => (best_strict (added c d h) hD hβ hγ hne).le

#print axioms physical_upper_limit
#print axioms split_isometric_iff_fair_packets
#print axioms physical_high_is_cut
#print axioms contrast_limit
#print axioms saturation_iff
#print axioms best_strict
#print axioms best_limit
#print axioms split_isometric_iff_equal_packet_saturation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets
