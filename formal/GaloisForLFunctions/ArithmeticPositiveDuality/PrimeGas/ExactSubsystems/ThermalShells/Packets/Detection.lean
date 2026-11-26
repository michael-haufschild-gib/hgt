import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Windows
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Resolution

/-! # Packet membership as an exact binary temperature measurement -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets

open Real Filter Topology

private theorem sum_gate {Ω : Type*} [DecidableEq Ω] {A U : Finset Ω} (hA : A ⊆ U) (f : Ω → ℝ) :
    (∑ x ∈ U, if x ∈ A then f x else 0) = ∑ x ∈ A, f x := by
  rw [← Finset.sum_filter]
  have he : U.filter (· ∈ A) = A := by ext x; simp only [Finset.mem_filter,and_iff_right_of_imp (fun h => hA h)]
  rw [he]

/-- A sign cut of the difference of two probability mass functions attains total variation. -/
theorem variation_at_cut {Ω : Type*} [DecidableEq Ω] {U H : Finset Ω} {w z : Ω → ℝ}
    (hw : ∀ x, 0 < w x) (hz : ∀ x, 0 < z x) (hU : U.Nonempty) (hH : H ⊆ U)
    (hpos : ∀ x ∈ H, z x/mass z U ≤ w x/mass w U)
    (hneg : ∀ x ∈ U, x ∉ H → w x/mass w U ≤ z x/mass z U) :
    variation w z U = share w U H-share z U H := by
  let f x := w x/mass w U-z x/mass z U
  have signed (A : Finset Ω) : share w U A-share z U A = ∑ x ∈ A, f x := by
    simp only [f,share,mass,Finset.sum_sub_distrib,← Finset.sum_div]
  have upper (A : Finset Ω) (hA : A ⊆ U) : share w U A-share z U A ≤ share w U H-share z U H := by
    rw [signed,signed,← sum_gate hA,← sum_gate hH]
    apply Finset.sum_le_sum
    intro x hx
    by_cases ha : x ∈ A <;> by_cases hh : x ∈ H
    · simp only [if_pos ha,if_pos hh,le_refl]
    · simpa only [if_pos ha,if_neg hh] using (show f x ≤ 0 from sub_nonpos.mpr (hneg x hx hh))
    · simpa only [if_neg ha,if_pos hh] using (show 0 ≤ f x from sub_nonneg.mpr (hpos x hh))
    · simp only [if_neg ha,if_neg hh,le_refl]
  apply le_antisymm _ ((le_abs_self _).trans (event_le_variation _ _ hH))
  apply variation_le
  intro A hA
  have hc := upper (U \ A) Finset.sdiff_subset
  rw [← one_sub_share hw hU hA,← one_sub_share hz hU hA] at hc
  exact abs_le.mpr ⟨by linarith only [hc],upper A hA⟩

theorem variation_comm {Ω : Type*} (w z : Ω → ℝ) (U : Finset Ω) : variation w z U = variation z w U := by
  unfold variation
  simp only [abs_sub_comm (share w U _) (share z U _)]

theorem odds_step (D k β γ : ℝ) : odds D k β = exp ((γ-β)*D)*odds D k γ := by
  unfold odds
  rw [mul_left_comm,← exp_add]
  congr 2; ring

private theorem weight_step (β γ t : ℝ) (p : ℕ) : shifted β t p = shifted (β-γ) t p*shifted γ t p := by
  rw [shifted,shifted,shifted,← exp_add]; congr 1; ring

/-- For ordered distinct temperatures the upper packet is eventually the exact positive likelihood cut. -/
theorem high_is_cut {D k β γ : ℝ} (hD : 0 < D) (hk : 0 < k) (hβγ : β < γ) :
    ∀ᶠ t in atTop, variation (shifted β t) (shifted γ t) (both D k t) =
      share (shifted β t) (both D k t) (high D k t)-share (shifted γ t) (both D k t) (high D k t) := by
  let e := exp ((γ-β)*D)
  let r := (1+odds D k β)/(1+odds D k γ)
  have he : 1 < e := one_lt_exp_iff.mpr (mul_pos (sub_pos.mpr hβγ) hD)
  have ho := odds_pos D hk γ
  have hden := add_pos zero_lt_one ho
  have hfactor : odds D k β = e*odds D k γ := odds_step D k β γ
  have hr₁ : 1 < r := by
    apply (lt_div_iff₀ hden).mpr
    rw [one_mul,hfactor]
    linarith only [mul_lt_mul_of_pos_right he ho]
  have hr₂ : r < e := by
    apply (div_lt_iff₀ hden).mpr
    rw [hfactor,mul_add,mul_one]
    linarith only [he]
  have hratio := (both_mass hD hk β).div (both_mass hD hk γ) hden.ne'
  have lo := (logWidth_limit 1).const_mul |β-γ|
  rw [mul_zero] at lo
  have h₁ := (continuous_exp.tendsto _).comp lo
  rw [exp_zero] at h₁
  have hi := ((offset_limit D k).const_mul (-(β-γ))).sub ((logWidth_limit k).const_mul |β-γ|)
  rw [mul_zero,sub_zero,show -(β-γ)*D=(γ-β)*D by ring] at hi
  have h₂ := (continuous_exp.tendsto _).comp hi
  filter_upwards [windows hD hk,eventually_gt_atTop (0:ℝ),h₁.eventually_lt hratio hr₁,
    hratio.eventually_lt h₂ hr₂] with t hwt ht hlt hgt
  let U := both D k t
  have hU : U.Nonempty := hwt.1.mono Finset.subset_union_left
  have mβ := mass_pos (shifted_pos β t) hU
  have mγ := mass_pos (shifted_pos γ t) hU
  have hs : scale t ≠ 0 := (div_pos (sq_pos_of_pos ht) (exp_pos t)).ne'
  simp only [Pi.div_apply,Function.comp_apply,mul_div_mul_left _ _ hs] at hlt hgt
  apply variation_at_cut (shifted_pos β t) (shifted_pos γ t) hU Finset.subset_union_right
  · intro p hp
    have hb := (packet_weight_bounds (β-γ) ht hk hp).1
    have hu := (div_le_iff₀ mγ).mp (hgt.le.trans hb)
    apply (div_le_div_iff₀ mγ mβ).mpr
    rw [weight_step β γ]
    calc _ ≤ shifted γ t p*(shifted (β-γ) t p*mass (shifted γ t) U) :=
              mul_le_mul_of_nonneg_left hu (shifted_pos γ t p).le
         _ = _ := by ring
  · intro p hp hh
    have hl := (Finset.mem_union.mp hp).resolve_right hh
    have hb := (packet_weight_bounds (β-γ) ht zero_lt_one hl).2
    rw [mul_zero,zero_add] at hb
    have hu := (le_div_iff₀ mγ).mp (hb.trans hlt.le)
    apply (div_le_div_iff₀ mβ mγ).mpr
    rw [weight_step β γ]
    calc _ = shifted γ t p*(shifted (β-γ) t p*mass (shifted γ t) U) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hu (shifted_pos γ t p).le

/-- Every temperature pair has limiting total variation equal to the binary upper-packet contrast. -/
theorem variation_limit {D k : ℝ} (hD : 0 < D) (hk : 0 < k) (β γ : ℝ) :
    Tendsto (fun t => variation (shifted β t) (shifted γ t) (both D k t)) atTop
      (𝓝 |upperProbability D k β-upperProbability D k γ|) := by
  have ordered (b g : ℝ) (hb : b < g) : Tendsto
      (fun t => variation (shifted b t) (shifted g t) (both D k t)) atTop
      (𝓝 |upperProbability D k b-upperProbability D k g|) := by
    apply ((upper_limit hD hk b).sub (upper_limit hD hk g)).abs.congr'
    filter_upwards [high_is_cut hD hk hb] with t ht
    rw [← ht,abs_of_nonneg (variation_nonneg _ _ _)]
  rcases lt_trichotomy β γ with hh | rfl | hh
  · exact ordered β γ hh
  · simp only [sub_self,abs_zero,variation,share,Finset.sup'_const]
    exact tendsto_const_nhds
  · simpa only [variation_comm (shifted γ _) (shifted β _),abs_sub_comm (upperProbability D k γ) (upperProbability D k β)] using ordered γ β hh

#print axioms variation_at_cut
#print axioms high_is_cut
#print axioms variation_limit

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets
