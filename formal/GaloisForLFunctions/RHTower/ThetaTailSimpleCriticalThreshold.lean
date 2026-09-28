import GaloisForLFunctions.RHTower.ThetaTailDivisorCapacity
import GaloisForLFunctions.RHTower.Zeta23SimpleCriticalDensity
import GaloisForLFunctions.RHTower.XiCensusVonMangoldtBridge

/-!
# The real-divisor-only capacity threshold

If `u` is even, `|u(x)| ≤ C exp(-a e^{b|x|})`, and `H` vanishes at every simple critical-line Xi
zero, then `u = 0` as soon as `b > 3`. The unconditional two-thirds theorem supplies
`N₀,s(T) ≥ (2/3 - ε) N(T)` simple critical ordinates; with their negative reflections they give
`[2/(3π) + o(1)] R log R` zeros of `H` in the disc of radius `R`, against the angular capacity
`[2/(πb) + o(1)] R log R`. This uses only the known real divisor.
-/

open MeasureTheory Set Filter Topology Complex Metric

namespace RHTower

noncomputable section

variable {u : ℝ → ℂ} {a b C : ℝ}

/-- An even source has an even transform. -/
theorem sourceTransform_neg_of_even (heven : ∀ x, u (-x) = u x) (z : ℂ) :
    sourceTransform u (-z) = sourceTransform u z := by
  rw [sourceTransform, sourceTransform,
    ← integral_neg_eq_self (fun x : ℝ => Complex.exp (-I * z * x) * u x) volume]
  congr 1; funext x
  rw [heven]; push_cast; ring_nf

/-- **The simple critical count in a disc.** If an entire `H ≢ 0` is even and vanishes at every
simple critical ordinate `γ > 0` (`ξ(1/2 + iγ) = 0` simple), then `closedBall c r` carries at
least `2 N₀,s(T)` zeros of `H` once `T + |c| ≤ r`. -/
theorem two_mul_xiSimpleCriticalZeroCount_le_finsum_divisor {H : ℂ → ℂ} (hH : Differentiable ℂ H)
    (hH0 : ∃ z, H z ≠ 0) (heven : ∀ z, H (-z) = H z)
    (hvan : ∀ γ : ℝ, 0 < γ → xi (1 / 2 + γ * I) = 0 →
      (analyticOrderAt xi (1 / 2 + γ * I)).toNat = 1 → H γ = 0)
    (c : ℂ) {T r : ℝ} (hTr : T + ‖c‖ ≤ r) :
    2 * (xiSimpleCriticalZeroCount T : ℝ) ≤
      ∑ᶠ z, (MeromorphicOn.divisor H (closedBall c r) z : ℝ) := by
  set P := (stripFinsetPos T).filter (fun z => z.re = 1 / 2 ∧ (analyticOrderAt xi z).toNat = 1)
  have hP : ∀ ρ ∈ P, 0 < ρ.im ∧ ρ.im ≤ T ∧ ρ = 1 / 2 + (ρ.im : ℂ) * I ∧ xi ρ = 0 ∧
      (analyticOrderAt xi ρ).toNat = 1 := by
    intro ρ hρ
    rw [Finset.mem_filter, mem_stripFinsetPos] at hρ
    obtain ⟨⟨_, _, him, hT, hxi⟩, hre, hsimple⟩ := hρ
    refine ⟨him, hT, ?_, hxi, hsimple⟩
    apply Complex.ext <;> simp [hre]
  set S₁ := P.image fun ρ => ((ρ.im : ℝ) : ℂ)
  set S₂ := P.image fun ρ => ((-ρ.im : ℝ) : ℂ)
  have hinj : Set.InjOn (fun ρ : ℂ => ρ.im) P := by
    intro ρ hρ σ hσ h
    rw [(hP ρ hρ).2.2.1, (hP σ hσ).2.2.1]
    simp only at h
    rw [h]
  have hc1 : S₁.card = P.card := Finset.card_image_of_injOn fun ρ hρ σ hσ h => by
    have := Complex.ofReal_injective h
    exact hinj hρ hσ this
  have hc2 : S₂.card = P.card := Finset.card_image_of_injOn fun ρ hρ σ hσ h => by
    have := Complex.ofReal_injective h
    exact hinj hρ hσ (by simpa using this)
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz1
    obtain ⟨σ, hσ, h⟩ := Finset.mem_image.mp hz2
    have := congrArg Complex.re h
    simp only [Complex.ofReal_re] at this
    linarith [(hP ρ hρ).1, (hP σ hσ).1]
  set S := S₁ ∪ S₂
  have hcard : (S.card : ℝ) = 2 * (xiSimpleCriticalZeroCount T : ℝ) := by
    rw [Finset.card_union_of_disjoint hdisj, hc1, hc2, xiSimpleCriticalZeroCount]
    push_cast; ring
  have hHA : AnalyticOnNhd ℂ H (closedBall c r) := fun z _ => hH.analyticAt z
  have hzero : ∀ z ∈ S, H z = 0 ∧ z ∈ closedBall c r := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨h1, h2, h3, h4, h5⟩ := hP ρ hρ
      refine ⟨hvan ρ.im h1 (by rw [← h3]; exact h4) (by rw [← h3]; exact h5), ?_⟩
      rw [mem_closedBall, dist_eq_norm]
      calc ‖((ρ.im : ℝ) : ℂ) - c‖ ≤ ‖((ρ.im : ℝ) : ℂ)‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ r := by rw [Complex.norm_real, Real.norm_of_nonneg h1.le]; linarith
    · obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨h1, h2, h3, h4, h5⟩ := hP ρ hρ
      refine ⟨?_, ?_⟩
      · rw [Complex.ofReal_neg, heven]
        exact hvan ρ.im h1 (by rw [← h3]; exact h4) (by rw [← h3]; exact h5)
      · rw [mem_closedBall, dist_eq_norm]
        calc ‖((-ρ.im : ℝ) : ℂ) - c‖ ≤ ‖((-ρ.im : ℝ) : ℂ)‖ + ‖c‖ := norm_sub_le _ _
          _ ≤ r := by rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos h1]; linarith
  have hge1 : ∀ z ∈ S, (1 : ℝ) ≤ (MeromorphicOn.divisor H (closedBall c r) z : ℝ) := by
    intro z hz
    obtain ⟨hHz, hzb⟩ := hzero z hz
    rw [MeromorphicOn.divisor_apply hHA.meromorphicOn hzb, (hH.analyticAt z).meromorphicOrderAt_eq]
    have hne : analyticOrderAt H z ≠ ⊤ := by
      have := meromorphicOrderAt_ne_top_of_differentiable hH hH0 z
      rwa [(hH.analyticAt z).meromorphicOrderAt_eq, Ne, ENat.map_eq_top_iff] at this
    have hpos : analyticOrderAt H z ≠ 0 := by
      rw [Ne, (hH.analyticAt z).analyticOrderAt_eq_zero]; exact not_not.mpr hHz
    lift analyticOrderAt H z to ℕ using hne with n hn
    rw [ENat.map_coe, WithTop.untop₀_coe]
    have : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; exact hpos rfl)
    exact_mod_cast this
  have hnn : ∀ z, (0 : ℝ) ≤ (MeromorphicOn.divisor H (closedBall c r) z : ℝ) := fun z => by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hHA z
  have hfin : (MeromorphicOn.divisor H (closedBall c r)).support.Finite :=
    (MeromorphicOn.divisor H _).finiteSupport (isCompact_closedBall c r)
  have hsupp : Function.support (fun z => (MeromorphicOn.divisor H (closedBall c r) z : ℝ)) ⊆
      (hfin.toFinset ∪ S : Finset ℂ) := by
    intro z hz
    rw [Function.mem_support] at hz
    rw [Finset.coe_union, Set.Finite.coe_toFinset]
    left
    rw [Function.mem_support]
    exact_mod_cast hz
  rw [finsum_eq_sum_of_support_subset _ hsupp, ← hcard]
  calc (S.card : ℝ) = ∑ z ∈ S, (1 : ℝ) := by simp
    _ ≤ ∑ z ∈ S, (MeromorphicOn.divisor H (closedBall c r) z : ℝ) := Finset.sum_le_sum hge1
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
        fun z _ _ => hnn z

/-- **Real-divisor-only threshold (`b ≤ 3`).** If an even measurable `u` obeys
`|u(x)| ≤ C exp(-a e^{b|x|})` with `b > 3`, and its transform vanishes at every simple critical
zero of Xi, then `u = 0` almost everywhere. The input is the unconditional Alpöge–Furman two-thirds
density of simple critical zeros. -/
theorem ae_eq_zero_of_doubleExp_simpleCritical (hu : AEStronglyMeasurable u)
    (heven : ∀ x, u (-x) = u x) (ha : 0 < a) (hb : 3 < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hvan : ∀ γ : ℝ, 0 < γ → xi (1 / 2 + γ * I) = 0 →
      (analyticOrderAt xi (1 / 2 + γ * I)).toNat = 1 → sourceTransform u γ = 0) :
    u =ᵐ[volume] 0 := by
  have hb0 : 0 < b := by linarith
  have hms := measurableMomentSource_of_doubleExp hu ha hb0 hC
  have hHd := hms.differentiable_sourceTransform
  have hint_u : Integrable u := (hms.moment 0).mono' hu (Eventually.of_forall fun x => by simp)
  by_cases hH : ∀ z, sourceTransform u z = 0
  · exact ae_eq_zero_of_sourceTransform_eq_zero hint_u hH
  exfalso
  push Not at hH
  obtain ⟨c, hc⟩ := hH
  have hπ := Real.pi_pos
  set δ := 2 / (3 * Real.pi) - 2 / (Real.pi * b) with hδdef
  have hδ : 0 < δ := by
    rw [hδdef, sub_pos, div_lt_div_iff₀ (by positivity) (by positivity)]; nlinarith
  set η := min (1 / 10) (δ / 4) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (by linarith)
  have hη6 : η ≤ 1 / 10 := min_le_left _ _
  have hηδ : η ≤ δ / 4 := min_le_right _ _
  obtain ⟨T₁, hT₁⟩ := two_thirds_simpleCritical_epsilon η hη0
  obtain ⟨T₂, hT₂4, hN⟩ := exists_xiZeroCount_close η hη0
  set κ := 2 * ((2 / 3 - η) * (1 / (2 * Real.pi) - η)) with hκdef
  have hπ3 : 3 < Real.pi := Real.pi_gt_three
  have hκ : 2 / (Real.pi * b) < κ := by
    have h1 : κ = 2 / (3 * Real.pi) - 4 * η / 3 - η / Real.pi + 2 * η ^ 2 := by
      rw [hκdef]; field_simp; ring
    have h2 : η / Real.pi ≤ η / 3 := div_le_div_of_nonneg_left hη0.le (by norm_num) hπ3.le
    nlinarith
  refine false_of_capacity hu ha hb0 hC hc (κ := κ) (K := ‖c‖) (T₀ := max (max T₁ T₂) 1)
    (norm_nonneg _) hκ (le_max_right _ _) fun T hT => ?_
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans ((le_max_left _ _).trans hT)
  have hT2 : T₂ ≤ T := (le_max_right _ _).trans ((le_max_left _ _).trans hT)
  have hTone : 1 ≤ T := (le_max_right _ _).trans hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hTone
  have hsimple := hT₁ T hT1
  have hNT := (abs_le.mp (hN T hT2)).1
  rw [← xiPosZeroCount_eq_xiZeroCount (by linarith)] at hNT
  push_cast at hNT
  have hcount := two_mul_xiSimpleCriticalZeroCount_le_finsum_divisor hHd ⟨c, hc⟩
    (sourceTransform_neg_of_even heven) hvan c (T := T) (r := T + ‖c‖) le_rfl
  have hpos1 : 0 ≤ 2 / 3 - η := by linarith
  have hpos2 : 0 ≤ 1 / (2 * Real.pi) - η := by
    have : 1 / 10 < 1 / (2 * Real.pi) := by
      rw [div_lt_div_iff₀ (by norm_num) (by positivity)]; nlinarith [Real.pi_lt_d2]
    linarith
  have hlow : (1 / (2 * Real.pi) - η) * (T * Real.log T) ≤ (xiPosZeroCount T : ℝ) := by linarith
  calc κ * (T * Real.log T) = 2 * ((2 / 3 - η) * ((1 / (2 * Real.pi) - η) * (T * Real.log T))) := by
        rw [hκdef]; ring
    _ ≤ 2 * ((2 / 3 - η) * (xiPosZeroCount T : ℝ)) := by
        gcongr
    _ ≤ 2 * (xiSimpleCriticalZeroCount T : ℝ) := by linarith
    _ ≤ _ := hcount

/-- For continuous `u` the real-divisor-only threshold is pointwise. -/
theorem eq_zero_of_doubleExp_simpleCritical_of_continuous (hu : Continuous u)
    (heven : ∀ x, u (-x) = u x) (ha : 0 < a) (hb : 3 < b)
    (hC : ∀ x, ‖u x‖ ≤ C * Real.exp (-a * Real.exp (b * |x|)))
    (hvan : ∀ γ : ℝ, 0 < γ → xi (1 / 2 + γ * I) = 0 →
      (analyticOrderAt xi (1 / 2 + γ * I)).toNat = 1 → sourceTransform u γ = 0) : u = 0 :=
  (hu.ae_eq_iff_eq volume continuous_const).mp
    (ae_eq_zero_of_doubleExp_simpleCritical hu.aestronglyMeasurable heven ha hb hC hvan)

end

end RHTower
