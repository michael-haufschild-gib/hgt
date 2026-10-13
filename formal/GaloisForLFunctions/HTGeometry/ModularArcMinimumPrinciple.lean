import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Compact

/-!
# A minimum principle above the bottom arc of the modular fundamental domain

Let `v(u, y)` be `1`-periodic in `u`, twice differentiable in each variable on `y > 0`, and a
solution of

`L v = y (v_uu + v_yy) + v_y = 0`,

which is `Δ(√y v) = −¼ √y v` for the hyperbolic Laplacian `Δ = y²(∂_u² + ∂_y²)`.  If `v → 0`
uniformly as `y → ∞` and `v ≥ 0` on the arc `{u² + y² = 1, |u| ≤ ½}` (the bottom of the standard
fundamental domain of `SL₂(ℤ)`), then `v ≥ 0` at every height `y ≥ 1`
(`nonneg_of_nonneg_on_modularArc`).

Proof.  Suppose `v(u₀, y₀) = −m < 0`.  Truncate at a height `Y` where `|v| ≤ m/4`, and subtract
`ε eᵞ` with `ε e^Y ≤ m/4`; since `L eʸ = (y + 1) eʸ > 0`, the function `f = v − ε eʸ` satisfies
`L f < 0`.  On the compact region above the three arcs `(u − n)² + y² = 1` (`n = −1, 0, 1`) with
`|u| ≤ 1`, `y ≤ Y`, the minimum of `f` is `< −m`; by periodicity it is attained at some `|u₁| ≤ ½`.
It is neither on `y = Y` (there `f ≥ −m/2`) nor on the arc (there `f ≥ −m/4`), so it is an
interior minimum.  The one-dimensional second-derivative test (`nonneg_of_isLocalMin_of_hasDerivAt`)
gives `f_uu ≥ 0`, `f_yy ≥ 0`, `f_y = 0` there, hence `L f ≥ 0`: a contradiction.
-/

open Filter Topology Set

namespace GaloisForLFunctions
namespace HTGeometry

/-- **Second-derivative test.**  At a local minimum the second derivative is nonnegative. -/
theorem nonneg_of_isLocalMin_of_hasDerivAt {g g' : ℝ → ℝ} {a c : ℝ} (hmin : IsLocalMin g a)
    (hg : ∀ᶠ s in 𝓝 a, HasDerivAt g (g' s) s) (hg' : HasDerivAt g' c a) : 0 ≤ c := by
  by_contra hc
  rw [not_le] at hc
  have hga : g' a = 0 := IsLocalMin.hasDerivAt_eq_zero hmin hg.self_of_nhds
  have hslope : Tendsto (slope g' a) (𝓝[>] a) (𝓝 c) :=
    hg'.tendsto_slope.mono_left (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
  have h1 : ∀ᶠ s in 𝓝[>] a, slope g' a s < 0 := hslope.eventually (gt_mem_nhds hc)
  have h2 : ∀ᶠ s in 𝓝[>] a, HasDerivAt g (g' s) s := nhdsWithin_le_nhds hg
  have h3 : ∀ᶠ s in 𝓝[>] a, g a ≤ g s := nhdsWithin_le_nhds hmin
  obtain ⟨b, hab, hb⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (h1.and (h2.and h3))
  have hab' : a < b := hab
  set s := (a + b) / 2 with hs
  have has : a < s := by rw [hs]; linarith
  have hsb : s < b := by rw [hs]; linarith
  have hcont : ContinuousOn g (Icc a s) := by
    intro x hx
    rcases hx.1.eq_or_lt with h | h
    · rw [← h]; exact hg.self_of_nhds.continuousAt.continuousWithinAt
    · exact (hb ⟨h, lt_of_le_of_lt hx.2 hsb⟩).2.1.continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope g g' has hcont
    fun x hx => (hb ⟨hx.1, hx.2.trans hsb⟩).2.1
  have hξneg : g' ξ < 0 := by
    have hsl := (hb ⟨hξ.1, hξ.2.trans hsb⟩).1
    rw [slope_def_field, hga, sub_zero] at hsl
    have hpos : 0 < ξ - a := by linarith [hξ.1]
    exact (div_neg_iff.mp hsl).elim (fun h => absurd h.2 (not_lt.mpr hpos.le)) (fun h => h.1)
  have hle := (hb ⟨has, hsb⟩).2.2
  rw [eq_div_iff (by linarith)] at hξeq
  nlinarith

/-- The compact region above the three arcs `(u − n)² + y² = 1`, `n ∈ {−1, 0, 1}`. -/
def arcRegion (Y : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2 ≤ Y ∧ 1 ≤ p.1 ^ 2 + p.2 ^ 2 ∧
    1 ≤ (p.1 - 1) ^ 2 + p.2 ^ 2 ∧ 1 ≤ (p.1 + 1) ^ 2 + p.2 ^ 2}

theorem arcRegion_y_pos {Y : ℝ} {p : ℝ × ℝ} (hp : p ∈ arcRegion Y) :
    3 / 4 ≤ p.2 ^ 2 := by
  obtain ⟨⟨h1, h2⟩, -, h3, h4, h5⟩ := hp
  rcases le_or_gt p.1 (-1 / 2) with h | h
  · nlinarith
  · rcases le_or_gt p.1 (1 / 2) with h' | h'
    · nlinarith
    · nlinarith

theorem isCompact_arcRegion_inter (Y : ℝ) :
    IsCompact (arcRegion Y ∩ {p : ℝ × ℝ | 0 ≤ p.2}) := by
  have hsub : arcRegion Y ∩ {p : ℝ × ℝ | 0 ≤ p.2} ⊆ Icc (-1 : ℝ) 1 ×ˢ Icc 0 Y := by
    rintro p ⟨⟨h1, h2, -⟩, h3⟩
    exact ⟨h1, h3, h2⟩
  have heq : arcRegion Y ∩ {p : ℝ × ℝ | 0 ≤ p.2} =
      {p : ℝ × ℝ | -1 ≤ p.1} ∩ {p | p.1 ≤ 1} ∩ {p | p.2 ≤ Y} ∩ {p | 1 ≤ p.1 ^ 2 + p.2 ^ 2} ∩
        {p | 1 ≤ (p.1 - 1) ^ 2 + p.2 ^ 2} ∩ {p | 1 ≤ (p.1 + 1) ^ 2 + p.2 ^ 2} ∩
        {p | 0 ≤ p.2} := by
    ext p
    simp only [arcRegion, mem_inter_iff, mem_setOf_eq, mem_Icc]
    tauto
  refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ hsub
  rw [heq]
  refine ((((((isClosed_le ?_ ?_).inter (isClosed_le ?_ ?_)).inter (isClosed_le ?_ ?_)).inter
    (isClosed_le ?_ ?_)).inter (isClosed_le ?_ ?_)).inter (isClosed_le ?_ ?_)).inter
    (isClosed_le ?_ ?_) <;> fun_prop

/-- **Minimum principle above the modular arc.** -/
theorem nonneg_of_nonneg_on_modularArc {v vu vuu vy vyy : ℝ → ℝ → ℝ}
    (hu : ∀ u y, 0 < y → HasDerivAt (fun s => v s y) (vu u y) u)
    (huu : ∀ u y, 0 < y → HasDerivAt (fun s => vu s y) (vuu u y) u)
    (hy : ∀ u y, 0 < y → HasDerivAt (fun s => v u s) (vy u y) y)
    (hyy : ∀ u y, 0 < y → HasDerivAt (fun s => vy u s) (vyy u y) y)
    (hL : ∀ u y, 0 < y → y * (vuu u y + vyy u y) + vy u y = 0)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) {p | 0 < p.2})
    (hper : ∀ u y, v (u + 1) y = v u y)
    (hdecay : ∀ ε > 0, ∃ Y, ∀ u y, Y ≤ y → |v u y| ≤ ε)
    (harc : ∀ u y, 0 < y → |u| ≤ 1 / 2 → u ^ 2 + y ^ 2 = 1 → 0 ≤ v u y)
    {u₀ y₀ : ℝ} (hy₀ : 1 ≤ y₀) : 0 ≤ v u₀ y₀ := by
  by_contra hneg
  rw [not_le] at hneg
  -- reduce `u₀` to `[−½, ½]`
  have hperZ : ∀ (n : ℤ) u y, v (u + n) y = v u y := by
    intro n u y
    have hP : Function.Periodic (fun u => v u y) 1 := fun u => hper u y
    have := (hP.int_mul n) u
    simpa using this
  set n₀ : ℤ := ⌊u₀ + 1 / 2⌋ with hn₀
  set u₀' : ℝ := u₀ - n₀ with hu₀'
  have hu₀'v : v u₀' y₀ = v u₀ y₀ := by
    have := hperZ n₀ u₀' y₀
    rw [hu₀', sub_add_cancel] at this
    exact this.symm
  have hu₀'lo : -1 / 2 ≤ u₀' := by
    have := Int.floor_le (u₀ + 1 / 2); rw [hu₀']; linarith
  have hu₀'hi : u₀' < 1 / 2 := by
    have := Int.lt_floor_add_one (u₀ + 1 / 2); rw [hu₀']; linarith
  set m := -v u₀ y₀ with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  obtain ⟨Y₁, hY₁⟩ := hdecay (m / 4) (by linarith)
  set Y := max Y₁ (y₀ + 1) with hY
  have hYy₀ : y₀ < Y := by rw [hY]; linarith [le_max_right Y₁ (y₀ + 1)]
  have hYdec : ∀ u, |v u Y| ≤ m / 4 := fun u => hY₁ u Y (le_max_left _ _)
  set ε := m / 4 / Real.exp Y with hε
  have hε0 : 0 < ε := by positivity
  have hεY : ε * Real.exp Y = m / 4 := by rw [hε]; field_simp
  have hεy : ∀ y, y ≤ Y → ε * Real.exp y ≤ m / 4 := fun y hy =>
    hεY ▸ mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) hε0.le
  set f : ℝ × ℝ → ℝ := fun p => v p.1 p.2 - ε * Real.exp p.2 with hf
  set K := arcRegion Y ∩ {p : ℝ × ℝ | 0 ≤ p.2} with hK
  have hK0 : ∀ p ∈ K, 0 < p.2 := by
    intro p hp
    have h0 : 0 ≤ p.2 := hp.2
    have h34 := arcRegion_y_pos hp.1
    nlinarith
  have hp₀K : (u₀', y₀) ∈ K := by
    refine ⟨⟨⟨by linarith, by linarith⟩, hYy₀.le, ?_, ?_, ?_⟩, by simp; linarith⟩ <;>
      simp only <;> nlinarith
  have hfcont : ContinuousOn f K := by
    refine (hcont.mono fun p hp => hK0 p hp).sub ?_
    exact (continuous_const.mul (Real.continuous_exp.comp continuous_snd)).continuousOn
  obtain ⟨p₁, hp₁K, hp₁min⟩ :=
    (isCompact_arcRegion_inter Y).exists_isMinOn ⟨_, hp₀K⟩ hfcont
  -- move the minimizer into `|u| ≤ ½`
  have hshift : ∃ q ∈ K, f q = f p₁ ∧ |q.1| ≤ 1 / 2 := by
    obtain ⟨⟨⟨h1, h2⟩, h3, h4, h5, h6⟩, h7⟩ := hp₁K
    rcases le_or_gt p₁.1 (1 / 2) with hhi | hhi
    · rcases le_or_gt (-1 / 2) p₁.1 with hlo | hlo
      · exact ⟨p₁, ⟨⟨⟨h1, h2⟩, h3, h4, h5, h6⟩, h7⟩, rfl, abs_le.mpr ⟨by linarith, hhi⟩⟩
      · refine ⟨(p₁.1 + 1, p₁.2), ⟨⟨⟨by linarith, by linarith⟩, h3, ?_, ?_, ?_⟩, h7⟩, ?_, ?_⟩
        · simp only; nlinarith
        · simp only; nlinarith
        · simp only; nlinarith
        · simp only [hf]
          have := hperZ 1 p₁.1 p₁.2
          simpa using this
        · simp only; rw [abs_le]; constructor <;> linarith
    · refine ⟨(p₁.1 - 1, p₁.2), ⟨⟨⟨by linarith, by linarith⟩, h3, ?_, ?_, ?_⟩, h7⟩, ?_, ?_⟩
      · simp only; nlinarith
      · simp only; nlinarith
      · simp only; nlinarith
      · simp only [hf]
        have := hperZ 1 (p₁.1 - 1) p₁.2
        simp only [Int.cast_one, sub_add_cancel] at this
        rw [this]
      · simp only; rw [abs_le]; constructor <;> linarith
  obtain ⟨q, hqK, hqf, hqu⟩ := hshift
  have hqmin : ∀ p ∈ K, f q ≤ f p := fun p hp => hqf ▸ hp₁min hp
  have hfq : f q < -m := by
    have := hqmin _ hp₀K
    simp only [hf] at this ⊢
    rw [hu₀'v] at this
    have := Real.exp_pos y₀
    nlinarith
  have hq0 : 0 < q.2 := hK0 q hqK
  obtain ⟨⟨⟨hq1, hq2⟩, hq3, hq4, hq5, hq6⟩, hq7⟩ := hqK
  -- the minimizer is not on the top
  have hqY : q.2 < Y := by
    rcases hq3.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hYdec q.1
      have h2 := hεy q.2 hq3
      simp only [hf] at hfq
      rw [h] at hfq h2
      rw [abs_le] at h1
      linarith [h1.1]
  -- the minimizer is not on the arc
  have hqarc : 1 < q.1 ^ 2 + q.2 ^ 2 := by
    rcases hq4.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := harc q.1 q.2 hq0 hqu h.symm
      have h2 := hεy q.2 hq3
      simp only [hf] at hfq
      linarith
  have hqa : |q.1| ≤ 1 / 2 := hqu
  rw [abs_le] at hqa
  have hq5' : 1 < (q.1 - 1) ^ 2 + q.2 ^ 2 := by nlinarith
  have hq6' : 1 < (q.1 + 1) ^ 2 + q.2 ^ 2 := by nlinarith
  -- local minimality in each direction
  have hmemK : ∀ᶠ p in 𝓝 q, p ∈ K := by
    have c1 : ∀ᶠ p in 𝓝 q, p.1 ∈ Ioo (-1 : ℝ) 1 :=
      continuous_fst.continuousAt.eventually_mem (Ioo_mem_nhds (by linarith) (by linarith))
    have c2 : ∀ᶠ p in 𝓝 q, p.2 < Y :=
      continuous_snd.continuousAt.eventually_lt continuousAt_const hqY
    have c3 : ∀ᶠ p in 𝓝 q, 1 < p.1 ^ 2 + p.2 ^ 2 :=
      continuousAt_const.eventually_lt (by fun_prop) hqarc
    have c4 : ∀ᶠ p in 𝓝 q, 1 < (p.1 - 1) ^ 2 + p.2 ^ 2 :=
      continuousAt_const.eventually_lt (by fun_prop) hq5'
    have c5 : ∀ᶠ p in 𝓝 q, 1 < (p.1 + 1) ^ 2 + p.2 ^ 2 :=
      continuousAt_const.eventually_lt (by fun_prop) hq6'
    have c6 : ∀ᶠ p in 𝓝 q, 0 < p.2 :=
      continuousAt_const.eventually_lt continuous_snd.continuousAt hq0
    filter_upwards [c1, c2, c3, c4, c5, c6] with p h1 h2 h3 h4 h5 h6
    exact ⟨⟨⟨h1.1.le, h1.2.le⟩, h2.le, h3.le, h4.le, h5.le⟩, h6.le⟩
  have hlinU : Tendsto (fun s : ℝ => (s, q.2)) (𝓝 q.1) (𝓝 q) := by
    have : Continuous fun s : ℝ => (s, q.2) := by fun_prop
    simpa using this.tendsto q.1
  have hlinY : Tendsto (fun s : ℝ => (q.1, s)) (𝓝 q.2) (𝓝 q) := by
    have : Continuous fun s : ℝ => (q.1, s) := by fun_prop
    simpa using this.tendsto q.2
  have hminU : IsLocalMin (fun s => v s q.2 - ε * Real.exp q.2) q.1 :=
    (hlinU.eventually hmemK).mono fun s hs => by
      have := hqmin _ hs
      simpa [hf] using this
  have hminY : IsLocalMin (fun s => v q.1 s - ε * Real.exp s) q.2 :=
    (hlinY.eventually hmemK).mono fun s hs => by
      have := hqmin _ hs
      simpa [hf] using this
  have hposY : ∀ᶠ s in 𝓝 q.2, 0 < s := lt_mem_nhds hq0
  have hUU : 0 ≤ vuu q.1 q.2 :=
    nonneg_of_isLocalMin_of_hasDerivAt hminU
      (Eventually.of_forall fun s => (hu s q.2 hq0).sub_const _) (huu q.1 q.2 hq0)
  have hYY : 0 ≤ vyy q.1 q.2 - ε * Real.exp q.2 :=
    nonneg_of_isLocalMin_of_hasDerivAt hminY
      (hposY.mono fun s hs => (hy q.1 s hs).sub ((Real.hasDerivAt_exp s).const_mul ε))
      ((hyy q.1 q.2 hq0).sub ((Real.hasDerivAt_exp q.2).const_mul ε))
  have hY1 : vy q.1 q.2 - ε * Real.exp q.2 = 0 :=
    hminY.hasDerivAt_eq_zero ((hy q.1 q.2 hq0).sub ((Real.hasDerivAt_exp q.2).const_mul ε))
  have hLq := hL q.1 q.2 hq0
  have h2 : 0 < ε * Real.exp q.2 := mul_pos hε0 (Real.exp_pos q.2)
  have h1 : 0 ≤ q.2 * (vuu q.1 q.2 + (vyy q.1 q.2 - ε * Real.exp q.2)) :=
    mul_nonneg hq0.le (by linarith)
  have h3 : 0 < q.2 * (ε * Real.exp q.2) := mul_pos hq0 h2
  nlinarith

end HTGeometry
end GaloisForLFunctions
