import GaloisForLFunctions.ZeroConfigurationGeometry.HeatStepsNeverShrinkTheMesh
import GaloisForLFunctions.ArithmeticGaugeTheory.TheArchimedeanLineCarriesTheExponent

/-!
# Power mass of an exceptional set

A decreasing power has maximal mass when indices are packed against
one. For growing powers at least half the indices carry weight
comparable to the cardinality raised to that power.
-/

noncomputable section
open Finset Filter
open scoped Topology
namespace GaloisForLFunctions.ArithmeticPowerMass

/-- The reciprocal power mass of m distinct positive indices is largest at the first m. -/
theorem packed_power {v : ℝ} (hv : 0<v) (hv1 : v ≤ 1)
    (S : Finset ℕ) (hs : ∀ k ∈ S, 1 ≤ k) :
    (∑ k ∈ S, (k:ℝ)^(v-1)) ≤ (1+1/v)*((S.card:ℝ)+1)^v := by
  have sep (k l : ℕ) (hne : k ≠ l) : 1 ≤ |(-(k:ℝ)) - (-(l:ℝ))| := by
    rw [show -(k:ℝ) - -(l:ℝ) = l-k by ring]
    rcases lt_or_gt_of_ne hne with h|h
    · have h' : (k:ℝ)+1 ≤ l := by exact_mod_cast h
      rw [abs_of_nonneg (by linarith)]; linarith
    · have h' : (l:ℝ)+1 ≤ k := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]; linarith
  have h := ZeroConfigurationGeometry.sum_le_sum_range_of_sep (fun k : ℕ => -(k:ℝ))
    (μ:=1) zero_le_one S.card S 0 (fun t => t^(v-1)) rfl
    (fun t ht => Real.rpow_nonneg (zero_le_one.trans ht) _)
    (fun x y hx hxy => Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx) hxy (sub_nonpos.mpr hv1))
    (fun k _ l _ => sep k l) (fun k hk => by simpa using (Nat.one_le_cast (α:=ℝ)).mpr (hs k hk))
  simp only [zero_sub,neg_neg,mul_one] at h
  exact h.trans (ArithmeticGaugeTheory.sum_rpow_sub_one_le hv _)

/-- A set of m distinct nonnegative integers has shifted v-th power
mass at least (m/2)^(1+v), uniformly for every real v ≥ 0. -/
theorem cardinal_power_le_mass (S : Finset ℕ) {v : ℝ} (hv : 0≤v) :
    (S.card:ℝ)^(1+v) ≤ 2^(1+v)*∑ k ∈ S, ((k:ℝ)+1)^v := by
  classical
  rcases S.eq_empty_or_nonempty with hh|hne
  · subst S
    simp [Real.zero_rpow (ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one hv))]
  have hm := (Nat.cast_pos (α:=ℝ)).mpr (card_pos.mpr hne)
  let T := S.filter (· < S.card/2)
  let H := S \ T
  have ht : T ⊆ S := filter_subset _ _
  have hl : T.card ≤ S.card/2 := by
    have h := card_le_card (show T ⊆ range (S.card/2) from fun _ hk => mem_range.mpr (mem_filter.mp hk).2)
    simpa only [card_range] using h
  have hcard : (S.card:ℝ) ≤ 2*(H.card:ℝ) := by
    have h := card_sdiff_of_subset ht
    change (S.card:ℝ) ≤ 2*((S \ T).card:ℝ)
    exact_mod_cast (show S.card ≤ 2*(S \ T).card by omega)
  have hw (k : ℕ) (hk : k ∈ H) : (S.card:ℝ)^v ≤ 2^v*((k:ℝ)+1)^v := by
    have hks := mem_sdiff.mp hk
    have hk' : S.card/2 ≤ k := le_of_not_gt fun hh => hks.2 (mem_filter.mpr ⟨hks.1,hh⟩)
    have h : (S.card:ℝ) ≤ 2*((k:ℝ)+1) := by exact_mod_cast (show S.card ≤ 2*(k+1) by omega)
    simpa only [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity : 0≤(k:ℝ)+1)] using
      Real.rpow_le_rpow hm.le h hv
  have hsum := sum_le_sum (s:=H) (fun k hk => hw k hk)
  rw [sum_const,nsmul_eq_mul,←mul_sum] at hsum
  have hall : (∑ k ∈ H,((k:ℝ)+1)^v) ≤ ∑ k ∈ S,((k:ℝ)+1)^v :=
    sum_le_sum_of_subset_of_nonneg sdiff_subset (fun k _ _ => Real.rpow_nonneg (by positivity) _)
  rw [Real.rpow_add hm,Real.rpow_one,Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
  linarith only [mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hm.le v),hsum,
    mul_le_mul_of_nonneg_left hall (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) v)]

/-- Strict lower powers and upper power bounds determine the ordinary
logarithmic order of a nonnegative mass. -/
theorem log_order_of_power_envelope {H : ℕ → ℝ} {θ : ℝ} (hθ : 0<θ) (hH : ∀ N, 0≤H N)
    (hlo : ∀ {b : ℝ}, 0≤b → b<θ → ∀ᶠ N : ℕ in Filter.atTop, ((N:ℝ)+1)^b < H N)
    (hhi : ∀ {b : ℝ}, θ<b → ∃ C : ℝ, 0≤C ∧ ∀ N, H N ≤ C*((N:ℝ)+1)^b) :
    Tendsto (fun N : ℕ => Real.log (1+H N)/Real.log ((N:ℝ)+1)) atTop (𝓝 θ) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    let c := (max 0 b+θ)/2
    have hm : max 0 b < θ := max_lt hθ hb
    have hbc : b<c := by dsimp only [c]; linarith only [le_max_right 0 b,hm]
    have hc0 : 0 ≤ c := by dsimp only [c]; linarith only [le_max_left 0 b,hθ]
    have hc : c < θ := by dsimp only [c]; linarith only [hm]
    filter_upwards [hlo hc0 hc,eventually_ge_atTop 1] with N hn hN
    have hX : 1<(N:ℝ)+1 := by linarith only [(Nat.one_le_cast (α:=ℝ)).mpr hN]
    have hl := Real.log_lt_log (Real.rpow_pos_of_pos (zero_lt_one.trans hX) c)
      (hn.trans (lt_add_of_pos_left _ zero_lt_one))
    rw [Real.log_rpow (zero_lt_one.trans hX)] at hl
    exact hbc.trans ((lt_div_iff₀ (Real.log_pos hX)).mpr hl)
  · intro b hb
    obtain ⟨a,ha,hab⟩ := exists_between hb
    obtain ⟨C,hC,hbound⟩ := hhi ha
    have ha0 : 0≤a := hθ.le.trans ha.le
    have hX : Tendsto (fun N : ℕ => (N:ℝ)+1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    filter_upwards [((tendsto_rpow_atTop (sub_pos.mpr hab)).comp hX).eventually_gt_atTop (1+C),
      eventually_ge_atTop 1] with N hn hN
    have hx : 1<(N:ℝ)+1 := by linarith only [(Nat.one_le_cast (α:=ℝ)).mpr hN]
    have hp := zero_lt_one.trans hx
    have hw := Real.one_le_rpow hx.le ha0
    have hs := mul_lt_mul_of_pos_right hn (Real.rpow_pos_of_pos hp a)
    change (1+C)*((N:ℝ)+1)^a < ((N:ℝ)+1)^(b-a)*((N:ℝ)+1)^a at hs
    rw [←Real.rpow_add hp,sub_add_cancel] at hs
    have hle : 1+H N < ((N:ℝ)+1)^b := by linarith only [hw,hs,hbound N]
    have hl := Real.log_lt_log (by linarith only [hH N] : 0<1+H N) hle
    rw [Real.log_rpow hp] at hl
    exact (div_lt_iff₀ (Real.log_pos hx)).mpr hl

#print axioms packed_power
#print axioms cardinal_power_le_mass
end GaloisForLFunctions.ArithmeticPowerMass
