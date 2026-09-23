import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue

/-!
# The first interior crossing of a real belief-propagation map

A continuous displacement that is positive at the left endpoint and negative at the right endpoint
has a first zero, and to the left of that zero it is positive; the derivative there is therefore
nonpositive.  Applied to the homogeneous belief-propagation map of a strictly positive binary
channel on a regular tree, this produces an interior fixed point whose multiplier is strictly
positive and at most one: attracting but not superattracting, or parabolic.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Filter Topology

noncomputable section

/-- **First crossing.**  A continuous function positive at the left endpoint and negative at the
right endpoint has a zero before which it stays positive. -/
theorem exists_first_zero_of_pos_of_neg {H : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn H (Icc a b)) (hpos : 0 < H a) (hneg : H b < 0) :
    ∃ c ∈ Ioo a b, H c = 0 ∧ ∀ y ∈ Ico a c, 0 < H y := by
  classical
  set S : Set ℝ := Icc a b ∩ H ⁻¹' Iic 0 with hS
  have hSclosed : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨b, ⟨⟨hab.le, le_refl b⟩, hneg.le⟩⟩
  have hSbdd : BddBelow S := ⟨a, fun x hx => hx.1.1⟩
  set c := sInf S with hc
  have hcS : c ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hac : a ≤ c := hcS.1.1
  have hcb : c ≤ b := hcS.1.2
  have hHc_le : H c ≤ 0 := hcS.2
  have hane : a ≠ c := by
    intro h
    rw [← h] at hHc_le
    exact absurd hpos (not_lt.2 hHc_le)
  have hac' : a < c := lt_of_le_of_ne hac hane
  have hleft : ∀ y ∈ Ico a c, 0 < H y := by
    intro y hy
    by_contra hcon
    have hyS : y ∈ S := ⟨⟨hy.1, le_trans hy.2.le hcb⟩, not_lt.1 hcon⟩
    exact absurd (csInf_le hSbdd hyS) (not_le.2 hy.2)
  have hIoo : Ioo a c ∈ 𝓝[<] c := by
    have h1 : Ioi a ∈ 𝓝 c := Ioi_mem_nhds hac'
    have h2 := inter_mem_nhdsWithin (Iio c) h1
    have hset : Iio c ∩ Ioi a = Ioo a c := by
      ext y
      simp [Set.mem_Ioo, and_comm]
    rwa [hset] at h2
  have hHc_ge : 0 ≤ H c := by
    have hcw : ContinuousWithinAt H (Icc a b) c := hcont c ⟨hac, hcb⟩
    have hle : 𝓝[<] c ≤ 𝓝[Icc a b] c := by
      refine le_inf inf_le_left ?_
      refine le_principal_iff.2 ?_
      filter_upwards [hIoo] with y hy
      exact ⟨hy.1.le, le_trans hy.2.le hcb⟩
    have htend : Tendsto H (𝓝[<] c) (𝓝 (H c)) := hcw.tendsto.mono_left hle
    refine ge_of_tendsto htend ?_
    filter_upwards [hIoo] with y hy
    exact (hleft y ⟨hy.1.le, hy.2⟩).le
  have hHc : H c = 0 := le_antisymm hHc_le hHc_ge
  have hcb' : c < b := by
    refine lt_of_le_of_ne hcb fun h => ?_
    rw [h] at hHc
    exact absurd hneg (by rw [hHc]; exact lt_irrefl 0)
  exact ⟨c, ⟨hac', hcb'⟩, hHc, hleft⟩

/-- The derivative at a first crossing is nonpositive. -/
theorem deriv_nonpos_of_first_zero {H : ℝ → ℝ} {d a c : ℝ} (hac : a < c)
    (hd : HasDerivAt H d c) (hHc : H c = 0) (hpos : ∀ y ∈ Ico a c, 0 < H y) :
    d ≤ 0 := by
  have hslope : Tendsto (slope H c) (𝓝[≠] c) (𝓝 d) := hasDerivAt_iff_tendsto_slope.mp hd
  have hmono : 𝓝[<] c ≤ 𝓝[≠] c := nhdsWithin_mono c fun y hy => ne_of_lt hy
  have htend : Tendsto (slope H c) (𝓝[<] c) (𝓝 d) := hslope.mono_left hmono
  have hIoo : Ioo a c ∈ 𝓝[<] c := by
    have h1 : Ioi a ∈ 𝓝 c := Ioi_mem_nhds hac
    have h2 := inter_mem_nhdsWithin (Iio c) h1
    have hset : Iio c ∩ Ioi a = Ioo a c := by
      ext y
      simp [Set.mem_Ioo, and_comm]
    rwa [hset] at h2
  refine le_of_tendsto htend ?_
  filter_upwards [hIoo] with y hy
  have hy' : 0 < H y := hpos y ⟨hy.1.le, hy.2⟩
  have hlt : y - c < 0 := sub_neg.2 hy.2
  rw [slope_def_field, div_nonpos_iff]
  left
  refine ⟨?_, hlt.le⟩
  rw [hHc, sub_zero]
  exact hy'.le

/-- The homogeneous belief-propagation map of a binary channel on a `p`-ary tree. -/
def treeBP (p : ℕ) (u v y : ℝ) : ℝ :=
  ((1 + u * y) ^ p - (1 + v * y) ^ p) / ((1 + u * y) ^ p + (1 + v * y) ^ p)

theorem branch_pos {u y : ℝ} (hu : |u| < 1) (hy : |y| ≤ 1) : 0 < 1 + u * y := by
  have habs : |u * y| < 1 := by
    rw [abs_mul]
    calc |u| * |y| ≤ |u| * 1 := by
          exact mul_le_mul_of_nonneg_left hy (abs_nonneg u)
      _ = |u| := mul_one _
      _ < 1 := hu
  have := (abs_lt.mp habs).1
  linarith

theorem abs_lt_one_of_between {v u : ℝ} (hv : -1 < v) (huv : v < u) (hu : u < 1) :
    |u| < 1 ∧ |v| < 1 := by
  constructor
  · exact abs_lt.mpr ⟨by linarith, hu⟩
  · exact abs_lt.mpr ⟨hv, by linarith⟩

@[simp] theorem treeBP_zero (p : ℕ) (u v : ℝ) : treeBP p u v 0 = 0 := by
  simp [treeBP]

theorem treeBP_lt_one {p : ℕ} {u v y : ℝ}
    (hA : 0 < 1 + u * y) (hB : 0 < 1 + v * y) : treeBP p u v y < 1 := by
  have hApow : 0 < (1 + u * y) ^ p := pow_pos hA p
  have hBpow : 0 < (1 + v * y) ^ p := pow_pos hB p
  rw [treeBP, div_lt_one (by linarith)]
  linarith

/-- The exact derivative of the belief-propagation map. -/
theorem hasDerivAt_treeBP {p : ℕ} (hp : 0 < p) {u v y : ℝ}
    (hA : 0 < 1 + u * y) (hB : 0 < 1 + v * y) :
    HasDerivAt (treeBP p u v)
      (2 * (p : ℝ) * (u - v) * (1 + u * y) ^ (p - 1) * (1 + v * y) ^ (p - 1) /
        ((1 + u * y) ^ p + (1 + v * y) ^ p) ^ (2 : ℕ)) y := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hAaff : HasDerivAt (fun t : ℝ => 1 + u * t) u y := by
    simpa using ((hasDerivAt_id y).const_mul u).const_add (1 : ℝ)
  have hBaff : HasDerivAt (fun t : ℝ => 1 + v * t) v y := by
    simpa using ((hasDerivAt_id y).const_mul v).const_add (1 : ℝ)
  have hAp : HasDerivAt (fun t : ℝ => (1 + u * t) ^ (q + 1))
      (((q : ℝ) + 1) * (1 + u * y) ^ q * u) y := by
    have h := (hasDerivAt_pow (q + 1) (1 + u * y)).comp y hAaff
    simpa [Function.comp_def] using h
  have hBp : HasDerivAt (fun t : ℝ => (1 + v * t) ^ (q + 1))
      (((q : ℝ) + 1) * (1 + v * y) ^ q * v) y := by
    have h := (hasDerivAt_pow (q + 1) (1 + v * y)).comp y hBaff
    simpa [Function.comp_def] using h
  have hden : (0 : ℝ) < (1 + u * y) ^ (q + 1) + (1 + v * y) ^ (q + 1) := by
    have := pow_pos hA (q + 1)
    have := pow_pos hB (q + 1)
    linarith
  have hquot := (hAp.sub hBp).div (hAp.add hBp) (ne_of_gt hden)
  refine hquot.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply, Nat.add_sub_cancel]
  congr 1
  push_cast
  ring

theorem treeBP_deriv_pos {p : ℕ} (hp : 0 < p) {u v y : ℝ} (huv : v < u)
    (hA : 0 < 1 + u * y) (hB : 0 < 1 + v * y) :
    0 < 2 * (p : ℝ) * (u - v) * (1 + u * y) ^ (p - 1) * (1 + v * y) ^ (p - 1) /
      ((1 + u * y) ^ p + (1 + v * y) ^ p) ^ (2 : ℕ) := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < u - v := by linarith
  have h2 : (0 : ℝ) < (1 + u * y) ^ (p - 1) := pow_pos hA _
  have h3 : (0 : ℝ) < (1 + v * y) ^ (p - 1) := pow_pos hB _
  have hden : (0 : ℝ) < ((1 + u * y) ^ p + (1 + v * y) ^ p) ^ (2 : ℕ) := by
    have := pow_pos hA p
    have := pow_pos hB p
    positivity
  positivity

/-- The multiplier of the belief-propagation map at the uninformative message. -/
theorem hasDerivAt_treeBP_zero {p : ℕ} (hp : 0 < p) (u v : ℝ) :
    HasDerivAt (treeBP p u v) ((p : ℝ) * (u - v) / 2) 0 := by
  have h := hasDerivAt_treeBP hp (u := u) (v := v) (y := 0) (by norm_num) (by norm_num)
  simpa using h.congr_deriv (by norm_num; ring)

/-- **The interior fixed point in the expansive regime.**  A strictly positive informative binary
channel with multiplier greater than one has a fixed point in `(0,1)` whose multiplier is strictly
positive and at most one: attracting but not superattracting, or parabolic. -/
theorem exists_treeBP_interior_fixedPoint {p : ℕ} (hp : 2 ≤ p) {u v : ℝ}
    (hv : -1 < v) (huv : v < u) (hu : u < 1)
    (hlam : 1 < (p : ℝ) * (u - v) / 2) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ treeBP p u v c = c ∧
      0 < deriv (treeBP p u v) c ∧ deriv (treeBP p u v) c ≤ 1 := by
  obtain ⟨hu', hv'⟩ := abs_lt_one_of_between hv huv hu
  have hp0 : 0 < p := by omega
  set R : ℝ → ℝ := treeBP p u v with hR
  set H : ℝ → ℝ := fun y => R y - y with hH
  have hDR : ∀ y : ℝ, |y| ≤ 1 → HasDerivAt R
      (2 * (p : ℝ) * (u - v) * (1 + u * y) ^ (p - 1) * (1 + v * y) ^ (p - 1) /
        ((1 + u * y) ^ p + (1 + v * y) ^ p) ^ (2 : ℕ)) y := fun y hy =>
    hasDerivAt_treeBP hp0 (branch_pos hu' hy) (branch_pos hv' hy)
  have hDH : ∀ y : ℝ, |y| ≤ 1 → HasDerivAt H
      (2 * (p : ℝ) * (u - v) * (1 + u * y) ^ (p - 1) * (1 + v * y) ^ (p - 1) /
        ((1 + u * y) ^ p + (1 + v * y) ^ p) ^ (2 : ℕ) - 1) y := fun y hy =>
    (hDR y hy).sub (hasDerivAt_id y)
  have hH0 : H 0 = 0 := by simp [hH, hR]
  have hDH0 : HasDerivAt H ((p : ℝ) * (u - v) / 2 - 1) 0 :=
    ((hasDerivAt_treeBP_zero hp0 u v).sub (hasDerivAt_id (0 : ℝ)))
  -- a point just to the right of the origin where the displacement is positive
  have hslope : Tendsto (slope H 0) (𝓝[≠] (0 : ℝ)) (𝓝 ((p : ℝ) * (u - v) / 2 - 1)) :=
    hasDerivAt_iff_tendsto_slope.mp hDH0
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), 0 < slope H 0 y := by
    refine (hslope.mono_left (nhdsWithin_mono 0 fun y hy => ne_of_gt hy)).eventually ?_
    exact eventually_gt_nhds (by linarith)
  obtain ⟨d, hd, hdsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hev
  set δ : ℝ := min d (1 / 2) with hδ
  have hδpos : 0 < δ := lt_min hd (by norm_num)
  have hδlt : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδmem : δ ∈ Ioc (0 : ℝ) d := ⟨hδpos, min_le_left _ _⟩
  have hHδ : 0 < H δ := by
    have := hdsub hδmem
    simp only [Set.mem_setOf_eq] at this
    rw [slope_def_field, hH0, sub_zero, sub_zero] at this
    exact (div_pos_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_lt.2 hδpos.le))
  have hH1 : H 1 < 0 := by
    have hA : (0 : ℝ) < 1 + u * 1 := branch_pos hu' (by norm_num)
    have hB : (0 : ℝ) < 1 + v * 1 := branch_pos hv' (by norm_num)
    have := treeBP_lt_one (p := p) hA hB
    simp only [hH, hR]
    linarith
  have hcont : ContinuousOn H (Icc δ 1) := by
    intro y hy
    have hy1 : |y| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [hy.1, hδpos], hy.2⟩
    exact ((hDH y hy1).continuousAt).continuousWithinAt
  obtain ⟨c, hcmem, hHc, hleft⟩ := exists_first_zero_of_pos_of_neg hδlt hcont hHδ hH1
  have hc1 : |c| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [hcmem.1, hδpos], hcmem.2.le⟩
  have hDHc := hDH c hc1
  have hnonpos := deriv_nonpos_of_first_zero hcmem.1 hDHc hHc hleft
  have hDRc := hDR c hc1
  have hpos := treeBP_deriv_pos hp0 huv (branch_pos hu' hc1) (branch_pos hv' hc1)
  refine ⟨c, lt_trans hδpos hcmem.1, hcmem.2, ?_, ?_, ?_⟩
  · have := hHc
    simp only [hH] at this
    linarith [this]
  · rw [hDRc.deriv]
    exact hpos
  · rw [hDRc.deriv]
    linarith

/-- The multiplier at the uninformative message in channel coordinates: `λ = p(α − γ)`. -/
theorem treeBP_channel_multiplier (p : ℕ) (α γ : ℝ) :
    (p : ℝ) * ((2 * α - 1) - (2 * γ - 1)) / 2 = p * (α - γ) := by ring

/-- **Channel form of the interior fixed point.**  A strictly positive positively informative
binary channel `0 < γ < α < 1` on a `p`-ary tree whose multiplier `p(α − γ)` exceeds one has an
interior fixed point that is attracting but not superattracting, or parabolic. -/
theorem exists_channelTreeBP_interior_fixedPoint {p : ℕ} (hp : 2 ≤ p) {α γ : ℝ}
    (hγ : 0 < γ) (hγα : γ < α) (hα : α < 1) (hlam : 1 < (p : ℝ) * (α - γ)) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ treeBP p (2 * α - 1) (2 * γ - 1) c = c ∧
      0 < deriv (treeBP p (2 * α - 1) (2 * γ - 1)) c ∧
      deriv (treeBP p (2 * α - 1) (2 * γ - 1)) c ≤ 1 := by
  refine exists_treeBP_interior_fixedPoint hp (by linarith) (by linarith) (by linarith) ?_
  rw [treeBP_channel_multiplier]
  exact hlam

/-- **Symmetric (zero-field Ising / BSC) form of the interior fixed point.** -/
theorem exists_symmetricTreeBP_interior_fixedPoint {p : ℕ} (hp : 2 ≤ p) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hlam : 1 < (p : ℝ) * a) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧ treeBP p a (-a) c = c ∧
      0 < deriv (treeBP p a (-a)) c ∧ deriv (treeBP p a (-a)) c ≤ 1 := by
  refine exists_treeBP_interior_fixedPoint hp (by linarith) (by linarith) ha1 ?_
  have : (p : ℝ) * (a - -a) / 2 = p * a := by ring
  rw [this]
  exact hlam

end

end GaloisForLFunctions.HTGeometry
