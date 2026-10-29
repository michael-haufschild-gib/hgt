import GaloisForLFunctions.ArithmeticCountingPositivity.TheFinitePrimeSecularSignsDetermineTheGap

/-!
# Interior roots and strict comparison of finite-prime gaps

The arithmetic secular series is continuous below the first excitation.
Its unique interior zero is the greatest gap. Every added prime contributes
a positive conductor term, so proper prime-set inclusion decreases the gap
strictly unless both constraints retain the maximal gap.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open private conductor_energy_gap summable_conductor_weights conductor_weight_nonneg from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheFullResolvent

local notation "γ" => Real.eulerMascheroniConstant

private theorem finiteFlip_secular_tail_continuousOn (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) {b : ℝ} (hb : b < 2 * Real.log 2) :
    ContinuousOn (fun s : ℝ => ∑' k : ℕ, finiteFlipSpectralWeight F (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s)) (Set.Iic b) := by
  have hsum := (summable_nat_add_iff 2).mpr (summable_conductor_weights F hF)
  refine continuousOn_tsum (fun k => ?_) (hsum.div_const (2 * Real.log 2 - b))
    (fun k s hs => ?_)
  · apply ContinuousOn.div continuousOn_const (continuousOn_const.sub continuousOn_id)
    intro s hs
    have he := conductor_energy_gap k
    have hsb : s ≤ b := hs
    exact (sub_pos.mpr ((hsb.trans_lt hb).trans_le he)).ne'
  · have he := conductor_energy_gap k
    have hsb : s ≤ b := hs
    have hp : 0 < ramanujanAdjunctionEnergy (k + 2) - γ - s :=
      sub_pos.mpr ((hsb.trans_lt hb).trans_le he)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (conductor_weight_nonneg F _) hp.le)]
    exact div_le_div_of_nonneg_left (conductor_weight_nonneg F _) (sub_pos.mpr hb)
      (sub_le_sub he hsb)

/-- The full arithmetic secular function is continuous at every point in the
physical first gap, by a locally uniform summable denominator bound. -/
theorem finiteFlipSecular_continuousAt (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    {s : ℝ} (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    ContinuousAt (finiteFlipSecular F) s := by
  obtain ⟨b, hsb, hb⟩ := exists_between hs2
  have htail := (finiteFlip_secular_tail_continuousOn F hF hb).continuousAt (Iic_mem_nhds hsb)
  exact (continuousAt_const.div continuousAt_id hs.ne').neg.add htail

/-- Every submaximal greatest gap is a zero of the counted secular series. -/
theorem finiteFlipSecular_greatestGap_eq_zero (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    (hbelow : finiteFlipGreatestGap F < 2 * Real.log 2) :
    finiteFlipSecular F (finiteFlipGreatestGap F) = 0 := by
  have hpos := finiteFlipGreatestGap_pos F hF
  have hc := finiteFlipSecular_continuousAt F hF hpos hbelow
  have hchar := (finiteFlip_hasHyperplaneGap_iff_secular F hF _).mp
    (isGreatest_finiteFlip_hyperplaneGap F hF).1
  apply le_antisymm
  · by_contra hnot
    have he : ∀ᶠ s : ℝ in 𝓝[<] (finiteFlipGreatestGap F), 0 < finiteFlipSecular F s :=
      (hc.eventually_const_lt (lt_of_not_ge hnot)).filter_mono nhdsWithin_le_nhds
    have hs : ∀ᶠ s : ℝ in 𝓝[<] (finiteFlipGreatestGap F), 0 < s :=
      (lt_mem_nhds hpos).filter_mono nhdsWithin_le_nhds
    have hb : ∀ᶠ s : ℝ in 𝓝[<] (finiteFlipGreatestGap F), s < finiteFlipGreatestGap F :=
      self_mem_nhdsWithin
    obtain ⟨s, hp, hs, hb⟩ := (he.and (hs.and hb)).exists
    exact not_lt_of_ge (hchar.2 s hs hb) hp
  · by_contra hnot
    have he : ∀ᶠ s : ℝ in 𝓝[>] (finiteFlipGreatestGap F), finiteFlipSecular F s < 0 :=
      (hc.eventually_lt_const (lt_of_not_ge hnot)).filter_mono nhdsWithin_le_nhds
    have hs : ∀ᶠ s : ℝ in 𝓝[>] (finiteFlipGreatestGap F), s < 2 * Real.log 2 :=
      (gt_mem_nhds hbelow).filter_mono nhdsWithin_le_nhds
    have hb : ∀ᶠ s : ℝ in 𝓝[>] (finiteFlipGreatestGap F), finiteFlipGreatestGap F < s :=
      self_mem_nhdsWithin
    obtain ⟨s, hn, hs, hb⟩ := (he.and (hs.and hb)).exists
    have hgap : HasHyperplaneGap (finiteFlip F) s := by
      apply (finiteFlip_hasHyperplaneGap_iff_secular F hF s).mpr
      refine ⟨hs.le, fun t ht hts => ?_⟩
      exact (((finiteFlipSecular_strictMonoOn F hF) ⟨ht, hts.trans hs⟩
        ⟨hpos.trans hb, hs⟩ hts).trans hn).le
    exact not_lt_of_ge ((isGreatest_finiteFlip_hyperplaneGap F hF).2 hgap) hb

/-- Within the physical first gap, vanishing of the arithmetic secular series
is equivalent to being the greatest gap. -/
theorem finiteFlipGreatestGap_eq_iff_secular_zero (F : Finset ℕ)
    (hF : ∀ p ∈ F, p.Prime) {s : ℝ} (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    finiteFlipGreatestGap F = s ↔ finiteFlipSecular F s = 0 := by
  constructor
  · intro he
    have hbelow : finiteFlipGreatestGap F < 2 * Real.log 2 := by simpa only [he] using hs2
    simpa only [he] using finiteFlipSecular_greatestGap_eq_zero F hF hbelow
  · intro hz
    have hgap : HasHyperplaneGap (finiteFlip F) s := by
      apply (finiteFlip_hasHyperplaneGap_iff_secular F hF s).mpr
      refine ⟨hs2.le, fun t ht hts => ?_⟩
      have hh := finiteFlipSecular_strictMonoOn F hF ⟨ht, hts.trans hs2⟩ ⟨hs, hs2⟩ hts
      rw [hz] at hh
      exact hh.le
    have hle := (isGreatest_finiteFlip_hyperplaneGap F hF).2 hgap
    apply le_antisymm ?_ hle
    by_contra hnot
    obtain ⟨t, hst, htδ⟩ := exists_between (lt_of_not_ge hnot)
    have ht2 := htδ.trans_le (finiteFlipGreatestGap_bounds F hF).2
    have hh := finiteFlipSecular_strictMonoOn F hF ⟨hs, hs2⟩ ⟨hs.trans hst, ht2⟩ hst
    rw [hz] at hh
    have hchar := (finiteFlip_hasHyperplaneGap_iff_secular F hF _).mp
      (isGreatest_finiteFlip_hyperplaneGap F hF).1
    exact not_lt_of_ge (hchar.2 t (hs.trans hst) htδ) hh

/-- Every newly flipped prime contributes a strictly positive reciprocal term
throughout the physical first gap. -/
theorem finiteFlipSecular_lt_of_ssubset {F G : Finset ℕ} (hFG : F ⊂ G)
    (hG : ∀ p ∈ G, p.Prime) {s : ℝ} (hs : 0 < s) (hs2 : s < 2 * Real.log 2) :
    finiteFlipSecular F s < finiteFlipSecular G s := by
  classical
  have hF : ∀ p ∈ F, p.Prime := fun p hp => hG p (hFG.1 hp)
  obtain ⟨p, hpG, hpF⟩ := Finset.exists_of_ssubset hFG
  have hp := hG p hpG
  have hbF : finiteFlipMobius F p = 0 := by
    simpa only [Nat.zero_add, pow_one, if_neg hpF] using finiteFlipMobius_prime_pow F hp 0
  have hbG : finiteFlipMobius G p = -2 := by
    simpa only [Nat.zero_add, pow_one, if_pos hpG, mul_neg, mul_one] using
      finiteFlipMobius_prime_pow G hp 0
  have hφ : (0 : ℝ) < p.totient := by exact_mod_cast Nat.totient_pos.mpr hp.pos
  have hwprime : finiteFlipSpectralWeight F p < finiteFlipSpectralWeight G p := by
    rw [finiteFlipSpectralWeight, finiteFlipSpectralWeight, hbF, hbG]
    norm_num only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_div]
    exact div_pos (by norm_num) hφ
  have hle (k : ℕ) : finiteFlipSpectralWeight F (k + 2) /
      (ramanujanAdjunctionEnergy (k + 2) - γ - s) ≤
      finiteFlipSpectralWeight G (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s) :=
    div_le_div_of_nonneg_right (finiteFlipSpectralWeight_mono hFG.1 _)
      (sub_pos.mpr (hs2.trans_le (conductor_energy_gap k))).le
  have hk : p - 2 + 2 = p := Nat.sub_add_cancel hp.two_le
  have hi : finiteFlipSpectralWeight F (p - 2 + 2) /
      (ramanujanAdjunctionEnergy (p - 2 + 2) - γ - s) <
      finiteFlipSpectralWeight G (p - 2 + 2) /
        (ramanujanAdjunctionEnergy (p - 2 + 2) - γ - s) := by
    apply div_lt_div_of_pos_right
    · simpa only [hk] using hwprime
    · exact sub_pos.mpr (hs2.trans_le (conductor_energy_gap (p - 2)))
  have htail := hasSum_lt hle hi (summable_finiteFlipSecularTail F hF hs hs2).hasSum
    (summable_finiteFlipSecularTail G hG hs hs2).hasSum
  unfold finiteFlipSecular
  exact add_lt_add_of_le_of_lt le_rfl htail

/-- Under proper prime-set inclusion, equality of greatest gaps is possible
only on the maximal plateau. Every submaximal larger-set gap is strictly smaller. -/
theorem finiteFlipGreatestGap_lt_iff_of_ssubset {F G : Finset ℕ} (hFG : F ⊂ G)
    (hG : ∀ p ∈ G, p.Prime) :
    finiteFlipGreatestGap G < finiteFlipGreatestGap F ↔
      finiteFlipGreatestGap G < 2 * Real.log 2 := by
  have hF : ∀ p ∈ F, p.Prime := fun p hp => hG p (hFG.1 hp)
  constructor
  · intro h
    exact h.trans_le (finiteFlipGreatestGap_bounds F hF).2
  · intro hbelow
    have hle := finiteFlipGreatestGap_antitone hFG.1 hG
    by_contra hnot
    have heq : finiteFlipGreatestGap G = finiteFlipGreatestGap F :=
      le_antisymm hle (le_of_not_gt hnot)
    have hzG := finiteFlipSecular_greatestGap_eq_zero G hG hbelow
    have hzF : finiteFlipSecular F (finiteFlipGreatestGap G) = 0 := by
      rw [heq]
      exact finiteFlipSecular_greatestGap_eq_zero F hF (by simpa only [heq] using hbelow)
    have hstrict := finiteFlipSecular_lt_of_ssubset hFG hG
      (finiteFlipGreatestGap_pos G hG) hbelow
    rw [hzF, hzG] at hstrict
    exact lt_irrefl 0 hstrict

end GaloisForLFunctions.ArithmeticCountingPositivity
