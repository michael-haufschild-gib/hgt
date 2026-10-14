import GaloisForLFunctions.HTGeometry.ModularArcMinimumPrinciple

/-!
# The minimum principle above the modular arc at a nonpositive level

`nonneg_of_nonneg_on_modularArc` with the boundary level `0` replaced by any `c ≤ 0`
(`le_of_le_on_modularArc`): a decaying `1`-periodic solution of the stream equation
`y(v_uu + v_yy) + v_y = 0` that is at least `c` on the bottom arc `{u² + y² = 1, |u| ≤ ½}` is at
least `c` at every height `y ≥ 1`.

The proof is the same perturbation argument.  With `m = c − v(u₀, y₀) > 0`, the function
`f = v − εe^y` (`εe^Y = m/4`) attains its minimum on the compact region above the three arcs at a
point with `f < c − m`.  This point is not on the top (`f ≥ −m/2 > c − m` there, as `c ≤ 0`), not
on the arc (`f ≥ c − m/4` there), and not interior (the equation forbids it).
-/

open Filter Topology Set

namespace GaloisForLFunctions
namespace HTGeometry

/-- **Minimum principle above the modular arc at a nonpositive level.**  A decaying `1`-periodic
solution of `y(v_uu + v_yy) + v_y = 0` that is at least `c ≤ 0` on the bottom arc is at least `c`
on every height `y₀ ≥ 1`. -/
theorem le_of_le_on_modularArc {v vu vuu vy vyy : ℝ → ℝ → ℝ}
    (hu : ∀ u y, 0 < y → HasDerivAt (fun s => v s y) (vu u y) u)
    (huu : ∀ u y, 0 < y → HasDerivAt (fun s => vu s y) (vuu u y) u)
    (hy : ∀ u y, 0 < y → HasDerivAt (fun s => v u s) (vy u y) y)
    (hyy : ∀ u y, 0 < y → HasDerivAt (fun s => vy u s) (vyy u y) y)
    (hL : ∀ u y, 0 < y → y * (vuu u y + vyy u y) + vy u y = 0)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) {p | 0 < p.2})
    (hper : ∀ u y, v (u + 1) y = v u y)
    (hdecay : ∀ ε > 0, ∃ Y, ∀ u y, Y ≤ y → |v u y| ≤ ε)
    {c : ℝ} (hc : c ≤ 0)
    (harc : ∀ u y, 0 < y → |u| ≤ 1 / 2 → u ^ 2 + y ^ 2 = 1 → c ≤ v u y)
    {u₀ y₀ : ℝ} (hy₀ : 1 ≤ y₀) : c ≤ v u₀ y₀ := by
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
  set m := c - v u₀ y₀ with hm
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
  have hfq : f q < c - m := by
    have := hqmin _ hp₀K
    simp only [hf] at this ⊢
    rw [hu₀'v] at this
    have h2 := mul_pos hε0 (Real.exp_pos y₀)
    linarith
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
      linarith [h1.1, hc, hm0]
  -- the minimizer is not on the arc
  have hqarc : 1 < q.1 ^ 2 + q.2 ^ 2 := by
    rcases hq4.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := harc q.1 q.2 hq0 hqu h.symm
      have h2 := hεy q.2 hq3
      simp only [hf] at hfq
      linarith [hm0]
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
