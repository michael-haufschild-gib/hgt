import GaloisForLFunctions.RHTower.KiKimLeeTwoThirdsHorizon
import GaloisForLFunctions.RHTower.Heat.HeatZeroDisplacement
import GaloisForLFunctions.RHTower.DeBruijnNewmanHalfBound

/-!
# The local de Bruijn–Newman constant

The **local de Bruijn–Newman constant** at height `X` is

  `Λ_X = inf{s ≥ 0 : for every s' ≥ s, every zero of H_{s'} with |Re z − X| ≤ 1 is real}`
  (`localNewmanConstant`),

the heat after which the de Bruijn flow is real-rooted in the unit window about `X`.

**Theorem.**
* **Supremum** (`newmanConstant_eq_iSup_localNewmanConstant`).  `Λ = sup_X Λ_X`, and
  RH holds iff `Λ_X = 0` for every `X` (`riemannHypothesis_iff_forall_localNewmanConstant_eq_zero`).
* **Upper bound** (`eventually_localNewmanConstant_le_twoThirds`).  For every `ε > 0` and all large
  `X`, `Λ_X ≤ (2/3 + ε)/log((X − 1)/2π)`: the reality horizon `2π e^{(2/3+ε)/s}`
  (`riemannHeat_zeros_real_twoThirds`) passes below the window.
* **Lower bound** (`exists_le_localNewmanConstant_of_offLine_zero`).  There is `c > 0` such that a
  zero `ρ` of `ξ` of depth `d = |Re ρ − ½|` at height `X = Im ρ ≥ X₀` gives `Λ_X ≥ c d²/log X`: the
  heated zero stays nonreal within `d/2` of the original one up to heat `c d²/log X`
  (`exists_nonreal_riemannHeat_zero_at_uniform_depth_scale`).

So `c · depth²/log X ≤ Λ_X ≤ (2/3 + ε)/log X`: the de Bruijn pincer has the shape of the slice
pincer (`TheLocalHeatThreshold`), and `Λ_X → 0`.  The global constant `Λ` is a supremum over bounded
heights.
-/

open Complex Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- Heats `s ≥ 0` after which every zero of `H_{s'}` in the window `|Re z − X| ≤ 1` is real. -/
def localRealTimes (X : ℝ) : Set ℝ :=
  {s | 0 ≤ s ∧ ∀ s' : ℝ, s ≤ s' → ∀ z : ℂ, riemannHeat s' z = 0 → |z.re - X| ≤ 1 → z.im = 0}

/-- **The local de Bruijn–Newman constant** `Λ_X = inf localRealTimes X`. -/
def localNewmanConstant (X : ℝ) : ℝ := sInf (localRealTimes X)

/-- Above the de Bruijn–Newman constant every window is real-rooted. -/
theorem mem_localRealTimes_of_newmanConstant_le {X s : ℝ} (hs : 0 ≤ s)
    (hΛ : newmanConstant ≤ s) : s ∈ localRealTimes X := by
  refine ⟨hs, fun s' hs' z hz _ => ?_⟩
  exact ((mem_realRootedTimes_iff (hs.trans hs')).mpr (hΛ.trans hs')).2 z hz

theorem localRealTimes_nonempty (X : ℝ) : (localRealTimes X).Nonempty :=
  ⟨_, mem_localRealTimes_of_newmanConstant_le newmanConstant_nonneg le_rfl⟩

theorem localRealTimes_bddBelow (X : ℝ) : BddBelow (localRealTimes X) := ⟨0, fun _ h => h.1⟩

theorem localNewmanConstant_nonneg (X : ℝ) : 0 ≤ localNewmanConstant X :=
  le_csInf (localRealTimes_nonempty X) fun _ h => h.1

theorem localNewmanConstant_le {X s : ℝ} (h : s ∈ localRealTimes X) : localNewmanConstant X ≤ s :=
  csInf_le (localRealTimes_bddBelow X) h

/-- `Λ_X ≤ Λ`. -/
theorem localNewmanConstant_le_newmanConstant (X : ℝ) : localNewmanConstant X ≤ newmanConstant :=
  localNewmanConstant_le (mem_localRealTimes_of_newmanConstant_le newmanConstant_nonneg le_rfl)

/-- A nonreal zero of `H_t` in the window about `X` gives `Λ_X ≥ t`. -/
theorem le_localNewmanConstant_of_nonreal {X t : ℝ} {z : ℂ} (hz : riemannHeat t z = 0)
    (him : z.im ≠ 0) (hre : |z.re - X| ≤ 1) : t ≤ localNewmanConstant X := by
  refine le_csInf (localRealTimes_nonempty X) fun s hs => ?_
  by_contra hlt
  push Not at hlt
  exact him (hs.2 t hlt.le z hz hre)

/-- **The global constant is the supremum of the local ones**: `Λ = sup_X Λ_X`. -/
theorem newmanConstant_eq_iSup_localNewmanConstant :
    newmanConstant = ⨆ X : ℝ, localNewmanConstant X := by
  have hbdd : BddAbove (Set.range localNewmanConstant) :=
    ⟨newmanConstant, by rintro _ ⟨X, rfl⟩; exact localNewmanConstant_le_newmanConstant X⟩
  refine le_antisymm ?_ (ciSup_le localNewmanConstant_le_newmanConstant)
  by_contra hlt
  push Not at hlt
  have h0 : 0 ≤ ⨆ X : ℝ, localNewmanConstant X :=
    (localNewmanConstant_nonneg 0).trans (le_ciSup hbdd 0)
  obtain ⟨s, hs1, hs2⟩ := exists_between hlt
  have hs0 : 0 ≤ s := h0.trans hs1.le
  -- below `Λ` some zero of `H_s` is nonreal
  have hnot : s ∉ realRootedTimes := fun h => by
    have := (mem_realRootedTimes_iff hs0).mp h; linarith
  obtain ⟨z, hz, him⟩ : ∃ z, riemannHeat s z = 0 ∧ z.im ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hnot ⟨hs0, hall⟩
  have h1 := le_localNewmanConstant_of_nonreal hz him (by simp : |z.re - z.re| ≤ 1)
  have h2 := le_ciSup hbdd z.re
  linarith

/-- **RH holds iff every local de Bruijn–Newman constant vanishes.** -/
theorem riemannHypothesis_iff_forall_localNewmanConstant_eq_zero :
    RiemannHypothesis ↔ ∀ X : ℝ, localNewmanConstant X = 0 := by
  rw [riemannHypothesis_iff_newmanConstant_eq_zero]
  constructor
  · intro h X
    exact le_antisymm (h ▸ localNewmanConstant_le_newmanConstant X) (localNewmanConstant_nonneg X)
  · intro h
    rw [newmanConstant_eq_iSup_localNewmanConstant]
    simp [h]

/-- **Upper bound from the reality horizon.**  For every `ε > 0`, for all large `X`,
`Λ_X ≤ (2/3 + ε)/log((X − 1)/2π)`. -/
theorem eventually_localNewmanConstant_le_twoThirds {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop, localNewmanConstant X ≤ (2 / 3 + ε) / Real.log ((X - 1) / (2 * Real.pi)) := by
  obtain ⟨X₀, hX₀⟩ := riemannHeat_zeros_real_twoThirds hε
  have hlog : Tendsto (fun X : ℝ => Real.log ((X - 1) / (2 * Real.pi))) atTop atTop := by
    refine Real.tendsto_log_atTop.comp ?_
    refine Tendsto.atTop_div_const (by positivity) ?_
    exact tendsto_atTop_add_const_right _ (-1) tendsto_id
  filter_upwards [hlog.eventually_ge_atTop (8 * (2 / 3 + ε) + 1), eventually_ge_atTop (|X₀| + 3)]
    with X hL hX
  set L := Real.log ((X - 1) / (2 * Real.pi)) with hLdef
  have hL0 : 0 < L := by linarith
  set s := (2 / 3 + ε) / L with hs
  have hs0 : 0 < s := by positivity
  have hs8 : s ≤ 1 / 8 := by
    rw [hs, div_le_iff₀ hL0]; linarith
  refine localNewmanConstant_le ⟨hs0.le, fun s' hss' z hz hre => ?_⟩
  rcases le_or_gt (1 / 8) s' with h8 | h8
  · exact ((mem_realRootedTimes_iff (by linarith)).mpr
      ((newmanConstant_lt_eighth.le).trans h8)).2 z hz
  · have hzre : X - 1 ≤ |z.re| := by
      have := abs_le.mp hre
      rw [abs_of_pos (by linarith [abs_nonneg X₀])]
      linarith
    refine hX₀ s' (hs0.trans_le hss') h8.le z hz ?_ ?_
    · linarith [le_abs_self X₀]
    · -- `e^{(2/3+ε)/s'} ≤ e^{(2/3+ε)/s} = (X − 1)/2π`
      have hexp : Real.exp ((2 / 3 + ε) / s') ≤ Real.exp ((2 / 3 + ε) / s) :=
        Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (by positivity) hs0 hss')
      have hval : Real.exp ((2 / 3 + ε) / s) = (X - 1) / (2 * Real.pi) := by
        rw [hs, div_div_cancel₀ (by positivity : (2 / 3 + ε : ℝ) ≠ 0), hLdef,
          Real.exp_log (by
            have : (1 : ℝ) < X - 1 := by linarith [abs_nonneg X₀]
            positivity)]
      have hπ : 0 < 2 * Real.pi := by positivity
      calc 2 * Real.pi * Real.exp ((2 / 3 + ε) / s')
          ≤ 2 * Real.pi * ((X - 1) / (2 * Real.pi)) := by
            rw [← hval]; exact mul_le_mul_of_nonneg_left hexp hπ.le
        _ = X - 1 := by field_simp
        _ ≤ |z.re| := hzre

/-- **Lower bound from an off-line zero.**  There are `c > 0` and `X₀` such that a zero `ρ` of `ξ`
with `Im ρ ≥ X₀` and depth `d = |Re ρ − ½| > 0` gives `Λ_{Im ρ} ≥ c d²/log Im ρ`. -/
theorem exists_le_localNewmanConstant_of_offLine_zero :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ ρ : ℂ, xi ρ = 0 → X₀ ≤ ρ.im → ρ.re ≠ 1 / 2 →
      c * (ρ.re - 1 / 2) ^ 2 / Real.log ρ.im ≤ localNewmanConstant ρ.im := by
  obtain ⟨c, hc, X₀, hX₀, h⟩ := exists_nonreal_riemannHeat_zero_at_uniform_depth_scale
  refine ⟨c, hc, X₀, hX₀, fun ρ hρ hX hne => ?_⟩
  -- the strip and the depth
  have hre1 : ρ.re < 1 := by
    by_contra hge; push Not at hge; exact xi_ne_zero_of_one_le_re hge hρ
  have hre0 : 0 < ρ.re := by
    by_contra hle
    have h1 : xi (1 - ρ) = 0 := by rw [xi_one_sub, hρ]
    exact xi_ne_zero_of_one_le_re
      (by simp only [Complex.sub_re, Complex.one_re]; linarith only [not_lt.mp hle]) h1
  set d := |ρ.re - 1 / 2| with hd
  have hd0 : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hd2 : d ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  set z : ℂ := (ρ - 1 / 2) * (-I) with hz
  have hzre : z.re = ρ.im := by simp [hz]
  have hzim : z.im = -(ρ.re - 1 / 2) := by simp [hz]
  have hz0 : riemannHeat 0 z = 0 := by
    have hpoint : (1 / 2 : ℂ) + I * z = ρ := by
      rw [hz]; ring_nf; rw [I_sq]; ring
    rw [riemannHeat_zero, hpoint, hρ]
  have hL : 0 < Real.log ρ.im := Real.log_pos (by linarith)
  have ht : 0 < c * d ^ 2 / Real.log ρ.im := by positivity
  have htL : c * d ^ 2 / Real.log ρ.im * Real.log ρ.im ≤ c * d ^ 2 := by
    rw [div_mul_cancel₀ _ hL.ne']
  have hzim' : d ≤ |z.im| := by rw [hzim, abs_neg]
  have hzim'' : |z.im| ≤ 1 / 2 := by rw [hzim, abs_neg]; exact hd2
  obtain ⟨w, hw, hwim, hwz⟩ := h ρ.im hX d hd0 hd2 _ ht htL z hzre hzim' hzim'' hz0
  have hwre : |w.re - ρ.im| ≤ 1 := by
    have h1 := (Complex.abs_re_le_norm (w - z)).trans hwz
    rw [Complex.sub_re, hzre] at h1
    linarith
  have hsq : (ρ.re - 1 / 2) ^ 2 = d ^ 2 := by rw [hd, sq_abs]
  rw [hsq]
  exact le_localNewmanConstant_of_nonreal hw hwim hwre

end

end RHTower.DeBruijn
