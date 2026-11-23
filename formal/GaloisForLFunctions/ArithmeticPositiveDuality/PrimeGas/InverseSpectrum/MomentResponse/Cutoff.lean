import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.MomentLoss

/-! # Cofinal moment bounds determine the first changed occupation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

private theorem loss_cap_iff_root_cap (q : GibbsExponent) (b : SpectralBand 1) {h : ℝ} (hh : 0 ≤ h) :
    momentLoss q b ≤ h^q.val ↔ momentLoss q b^q.val⁻¹ ≤ h := by
  have hq : 0 < q.val := q.property
  constructor
  · intro hc
    simpa only [Real.rpow_rpow_inv hh hq.ne'] using
      Real.rpow_le_rpow (momentLoss_nonneg q b) hc (inv_nonneg.mpr q.property.le)
  · intro hc
    simpa only [Real.rpow_inv_rpow (momentLoss_nonneg q b) hq.ne'] using
      Real.rpow_le_rpow (Real.rpow_nonneg (momentLoss_nonneg q b) _) hc q.property.le

private theorem changed_level_exceeds_cap (b : SpectralBand 1) {h : ℝ} (hh : 0 ≤ h) (k : ℕ)
    (hhot : h < occupationWeight k) (hd : (b k).val < occupationWeight k) :
    ∃ q : GibbsExponent, h^q.val < momentLoss q b := by
  let a := occupationWeight k
  let x := (b k).val
  have ha : 0 < a := occupationWeight_pos _
  have hx : 0 ≤ x := (band_pos b k).le
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hx ha.le) ((div_lt_one ha).mpr hd)).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hh ha.le) ((div_lt_one ha).mpr hhot))
  rw [add_zero] at ht
  obtain ⟨n,hn,hl⟩ := ((eventually_gt_atTop (1:ℕ)).and (ht.eventually_lt_const zero_lt_one)).exists
  let q : GibbsExponent := ⟨n,show 0 < (n:ℝ) from Nat.cast_pos.mpr (Nat.zero_lt_one.trans hn)⟩
  refine ⟨q,lt_of_not_ge (fun hbad => ?_)⟩
  have he := (summable_spectralDrop (powerResponse q) b).le_tsum k (fun j _ => drop_nonneg _ b j)
  change a^(n:ℝ)-x^(n:ℝ) ≤ momentLoss q b at he
  have hb := he.trans hbad
  change a^(n:ℝ)-x^(n:ℝ) ≤ h^(n:ℝ) at hb
  simp only [Real.rpow_natCast] at hb
  apply hl.not_ge
  change 1 ≤ (x/a)^n+(h/a)^n
  rw [div_pow,div_pow,← add_div,le_div_iff₀ (pow_pos ha n),one_mul]
  linarith only [hb]

/-- Uniform power ceilings at every moment order hold exactly when all occupations above the cutoff are fixed. -/
theorem all_moment_ceilings_iff (b : SpectralBand 1) {h : ℝ} (hh : 0 ≤ h) :
    (∀ q : GibbsExponent, momentLoss q b ≤ h^q.val) ↔ ∀ k, h < occupationWeight k → (b k).val = occupationWeight k := by
  constructor
  · intro hc k hk
    apply le_antisymm (b k).property.2
    by_contra! hlt
    obtain ⟨q,hq⟩ := changed_level_exceeds_cap b hh k hk hlt
    exact hq.not_ge (hc q)
  · intro hfixed q
    classical
    by_cases hex : ∃ k, (b k).val ≠ occupationWeight k
    · let j := Nat.find hex
      have hj : (b j).val ≠ occupationWeight j := Nat.find_spec hex
      have hhead (k : ℕ) (hk : k < j) : (b k).val = occupationWeight k := not_not.mp (Nat.find_min hex hk)
      exact (momentLoss_le_tail q b j hhead).trans (Real.rpow_le_rpow (occupationWeight_pos j).le
        (le_of_not_gt (fun hl => hj (hfixed j hl))) q.property.le)
    · push Not at hex
      have hz : momentLoss q b = 0 := by
        change (∑' k, spectralDrop (powerResponse q) b k) = 0
        simp only [spectralDrop,hex,sub_self,tsum_zero]
      exact hz.trans_le (Real.rpow_nonneg hh _)

/-- Any unbounded family of moment orders imposes exactly the same cutoff, even if its orders are arbitrarily sparse. -/
theorem cofinal_moment_ceilings_iff (b : SpectralBand 1) {h : ℝ} (hh : 0 ≤ h) (S : Set GibbsExponent)
    (hS : ∀ a : GibbsExponent, ∃ q ∈ S, a ≤ q) :
    (∀ q ∈ S, momentLoss q b ≤ h^q.val) ↔ ∀ k, h < occupationWeight k → (b k).val = occupationWeight k := by
  rw [← all_moment_ceilings_iff b hh]
  constructor
  · intro hc a
    obtain ⟨q,hq,ha⟩ := hS a
    exact (loss_cap_iff_root_cap a b hh).mpr ((moment_root_monotone b ha).trans ((loss_cap_iff_root_cap q b hh).mp (hc q hq)))
  · exact fun hc q _ => hc q

/-- The high-moment root converges to the first occupation that actually moves. -/
theorem moment_root_tendsto_first_change (b : SpectralBand 1) (j : ℕ)
    (hhead : ∀ k < j, (b k).val = occupationWeight k) (hj : (b j).val ≠ occupationWeight j) :
    Tendsto (fun q : GibbsExponent => momentLoss q b^q.val⁻¹) atTop (𝓝 (occupationWeight j)) := by
  apply tendsto_order.mpr
  constructor
  · intro h hh
    by_cases hneg : h < 0
    · exact Eventually.of_forall (fun q => hneg.trans_le (Real.rpow_nonneg (momentLoss_nonneg q b) _))
    obtain ⟨a,ha⟩ := changed_level_exceeds_cap b (le_of_not_gt hneg) j hh (lt_of_le_of_ne (b j).property.2 hj)
    have hroot : h < momentLoss a b^a.val⁻¹ := lt_of_not_ge (fun hle => ha.not_ge ((loss_cap_iff_root_cap a b (le_of_not_gt hneg)).mpr hle))
    filter_upwards [eventually_ge_atTop a] with q hq
    exact hroot.trans_le (moment_root_monotone b hq)
  · intro h hh
    exact Eventually.of_forall (fun q => ((loss_cap_iff_root_cap q b (occupationWeight_pos j).le).mp (momentLoss_le_tail q b j hhead)).trans_lt hh)

/-- Simultaneously measuring all ordinary traces at inverse-height root resolution freezes exactly the levels below log energy 2 log t. -/
theorem ordinary_moment_energy_cutoff (b : SpectralBand 1) {t : ℝ} (ht : 0 < t) :
    (∀ q : GibbsExponent, 1 < q.val → momentLoss q b ≤ (1/t^2)^q.val) ↔
      ∀ k : ℕ, Real.log ((k:ℝ)+1) < 2*Real.log t → (b k).val = occupationWeight k := by
  let S := {q : GibbsExponent | 1 < q.val}
  have hc (a : GibbsExponent) : ∃ q ∈ S, a ≤ q := by
    have ha : 0 < a.val := a.property
    exact ⟨⟨a.val+2,show 0 < a.val+2 by linarith only [ha]⟩,show 1 < a.val+2 by linarith only [ha],
      show a.val ≤ a.val+2 by linarith⟩
  have he := cofinal_moment_ceilings_iff b (one_div_pos.mpr (sq_pos_of_pos ht)).le S hc
  change (∀ q ∈ S, momentLoss q b ≤ (1/t^2)^q.val) ↔ _
  rw [he]
  apply forall_congr'
  intro k
  have hk : 0 < (k:ℝ)+1 := by positivity
  have hiff : 1/t^2 < occupationWeight k ↔ Real.log ((k:ℝ)+1) < 2*Real.log t := by
    rw [occupationWeight_eq,← one_div ((k:ℝ)+1),one_div_lt_one_div (sq_pos_of_pos ht) hk,
      ← Real.log_lt_log_iff hk (sq_pos_of_pos ht),Real.log_pow]
    norm_num
  rw [hiff]

#print axioms all_moment_ceilings_iff
#print axioms cofinal_moment_ceilings_iff
#print axioms moment_root_tendsto_first_change
#print axioms ordinary_moment_energy_cutoff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
