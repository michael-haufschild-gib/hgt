import GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.ElevenFlipNegativity

/-!
# The eleven flip fails at every sufficiently large horizon

The strict negative margin survives a varying sub-horizon width. Rounding
`(99 / (100 c)) N` down then transfers it to every fixed ratio `c ≥ 99 / 100`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

open RenormalizedArithmeticPotentialTheory ArithmeticElectrostatics
  ArithmeticCountingPositivity SpacingScaleHarmonicAnalysis

/-- The eleven-flip witness is stable under convergent separated width ratios. -/
theorem eventually_elevenFlip_negative_variable {H : ℕ → ℕ} (hH : Tendsto H atTop atTop)
    {r : ℕ → ℝ} (hr : Tendsto r atTop (𝓝 (99 / 100))) :
    ∀ᶠ N : ℕ in atTop,
      weilQuadTw (primeFlipWeight 11)
        (atomicTest (H N) (fun n => primeSquareTrial 11 n / Real.sqrt n)
          (atomDilate transMetzlerProfile (r N / H N))) < 0 := by
  let U : ℕ → ℝ := fun N =>
    weilQuad (atomicTest (H N) (fun n => primeSquareTrial 11 n / Real.sqrt n)
      (atomDilate transMetzlerProfile (r N / H N))) / ((r N / H N) * Real.log (H N)) +
      (∫ u, transMetzlerProfile u ^ 2) * (primeSquareFlipBound 11 (H N) / Real.log (H N))
  have hwlim := tendsto_ramanujanPacketTest_weil_variable contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) integral_transMetzlerProfile_sq_pos
    hr (by norm_num : (0 : ℝ) < 99 / 100) (by norm_num : (99 / 100 : ℝ) < 1)
    hH elevenPacketConductors elevenPacketConductors_pos elevenPacketCoefficient
  simp only [elevenPacketTest_eq, elevenPacket_energy] at hwlim
  have hu : Tendsto U atTop
      (𝓝 ((∫ u, transMetzlerProfile u ^ 2) * elevenTrialUpperMargin)) := by
    have h := hwlim.add (((tendsto_primeSquareFlipBound (by norm_num : Nat.Prime 11)).comp hH).const_mul
      (∫ u, transMetzlerProfile u ^ 2))
    have heq :
        (∫ u, transMetzlerProfile u ^ 2) *
          (completeWeilSelfFinitePart transMetzlerProfile (99 / 100) + 4 * Real.log 11 / 11 +
            completeWeilPoleShift transMetzlerProfile (99 / 100) * (101 / 121 : ℝ) ^ 2) +
          (∫ u, transMetzlerProfile u ^ 2) *
            (-4 * Real.log (11 : ℕ) / (11 : ℕ) + 4 * Real.log (11 : ℕ) *
              (2 / ((11 : ℕ) : ℝ) ^ 3 + 1 / (((11 : ℕ) : ℝ) ^ 2 * (((11 : ℕ) : ℝ) - 1)))) =
        (∫ u, transMetzlerProfile u ^ 2) * elevenTrialUpperMargin := by
      norm_num only [Nat.cast_ofNat, elevenTrialUpperMargin, elevenPrimeTailCost]
      ring
    rw [heq] at h
    exact h
  have hneg : (∫ u, transMetzlerProfile u ^ 2) * elevenTrialUpperMargin < 0 :=
    mul_neg_of_pos_of_neg integral_transMetzlerProfile_sq_pos elevenTrialUpperMargin_neg
  filter_upwards [hu.eventually (gt_mem_nhds hneg),
    hr.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 99 / 100)),
    hr.eventually (gt_mem_nhds (by norm_num : (99 / 100 : ℝ) < 199 / 200)),
    hH.eventually (eventually_div_horizon_lt_atomSpacing
      (by norm_num : (0 : ℝ) < 199 / 200) (by norm_num : (199 / 200 : ℝ) < 1)),
    hH.eventually (eventually_ge_atTop 2)] with N huN hr0 hr1 hsep hN
  have hN0 : (0 : ℝ) < H N := by exact_mod_cast (show 0 < H N by omega)
  have hw : 0 < r N / H N := div_pos hr0 hN0
  have hlog : 0 < Real.log (H N) := Real.log_pos (by exact_mod_cast (show 1 < H N by omega))
  have hs : r N / H N < atomSpacing (H N) :=
    (div_lt_div_of_pos_right hr1 hN0).trans hsep.2.2
  obtain ⟨hg, hsupp, hgc⟩ := atomDilate_facts contDiff_transMetzlerProfile
    (fun u hu => transMetzlerProfile_eq_zero hu) hw
  have hb := div_le_div_of_nonneg_right
    (primeSquareTrial_complete_le hg hgc hsupp hs (by norm_num : Nat.Prime 11))
    (mul_pos hw hlog).le
  rw [add_div, integral_atomDilate_sq hw] at hb
  have hscale :
      ((r N / H N) * (∫ u, transMetzlerProfile u ^ 2) * primeSquareFlipBound 11 (H N)) /
        ((r N / H N) * Real.log (H N)) =
      (∫ u, transMetzlerProfile u ^ 2) * (primeSquareFlipBound 11 (H N) / Real.log (H N)) := by
    field_simp [hN0.ne', hr0.ne', hlog.ne'] <;> ring
  rw [hscale] at hb
  have hlt := hb.trans_lt huN
  have h := (div_lt_iff₀ (mul_pos hw hlog)).mp hlt
  simpa only [zero_mul] using h

private theorem floor_subhorizon_tendsto {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun N : ℕ => ⌊θ * (N : ℝ)⌋₊) atTop atTop := by
  refine tendsto_atTop.mpr fun B => ?_
  filter_upwards [eventually_ge_atTop (⌈((B : ℝ) + 1) / θ⌉₊)] with N hN
  have h1 : ((B : ℝ) + 1) / θ ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have h2 : (B : ℝ) ≤ θ * (N : ℝ) := by
    have h := (div_le_iff₀ hθ).mp h1
    linarith only [h]
  exact Nat.le_floor h2

private theorem floor_subhorizon_ratio {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun N : ℕ => (⌊θ * (N : ℝ)⌋₊ : ℝ) / N) atTop (𝓝 θ) := by
  have hi : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hl : Tendsto (fun N : ℕ => θ - 1 / (N : ℝ)) atTop (𝓝 θ) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hi
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [le_div_iff₀ hN0, sub_mul, div_mul_cancel₀ _ hN0.ne']
    exact (Nat.sub_one_lt_floor _).le
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hN0]
    exact Nat.floor_le (mul_nonneg hθ.le (Nat.cast_nonneg N))

/-- Every fixed ratio at least `99 / 100` eventually has a negative eleven-flip test. -/
theorem eventually_elevenFlip_negative_of_ratio {c : ℝ} (hc : (99 / 100 : ℝ) ≤ c) :
    ∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (primeFlipWeight 11)
        (atomicTest N x (atomDilate transMetzlerProfile (c / N))) < 0 := by
  have hc0 : 0 < c := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 99 / 100) hc
  let θ : ℝ := (99 / 100) / c
  have hθ : 0 < θ := div_pos (by norm_num) hc0
  have hθ1 : θ ≤ 1 := (div_le_one hc0).mpr hc
  let H : ℕ → ℕ := fun N => ⌊θ * (N : ℝ)⌋₊
  have hH : Tendsto H atTop atTop := floor_subhorizon_tendsto hθ
  have hr : Tendsto (fun N : ℕ => c * ((H N : ℝ) / N)) atTop (𝓝 (99 / 100)) := by
    have h := (floor_subhorizon_ratio hθ).const_mul c
    simpa only [H, θ, mul_div_cancel₀ _ hc0.ne'] using h
  filter_upwards [eventually_elevenFlip_negative_variable hH hr,
    hH.eventually (eventually_ge_atTop 1)] with N hneg hN
  have hHN : H N ≤ N := Nat.floor_le_of_le
    (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ1 (Nat.cast_nonneg N))
  refine ⟨fun n => if n ≤ H N then primeSquareTrial 11 n / Real.sqrt n else 0, ?_⟩
  rw [atomicTest_zero_padding hHN]
  have hwidth : (c * ((H N : ℝ) / N)) / H N = c / N := by
    have hH0 : (H N : ℝ) ≠ 0 := by exact_mod_cast (show H N ≠ 0 by omega)
    field_simp [hH0] <;> ring
  simpa only [hwidth] using hneg

/-- The requested ratio-two eleven-flip decision holds at every sufficiently large horizon. -/
theorem eventually_elevenFlip_negative_two :
    ∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (primeFlipWeight 11)
        (atomicTest N x (atomDilate transMetzlerProfile (2 / N))) < 0 :=
  eventually_elevenFlip_negative_of_ratio (by norm_num)

/-- The eleven flip is already detected at the explicit first-overlap ratio. -/
theorem eventually_elevenFlip_negative_cZero :
    ∀ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      weilQuadTw (primeFlipWeight 11)
        (atomicTest N x (atomDilate transMetzlerProfile (cZero / N))) < 0 :=
  eventually_elevenFlip_negative_of_ratio (by norm_num [cZero, deltaZero])

end GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.eventually_elevenFlip_negative_two
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap.eventually_elevenFlip_negative_cZero
