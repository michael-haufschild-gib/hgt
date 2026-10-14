import GaloisForLFunctions.HTGeometry.ModularArcMinimumPrinciple

/-!
# A minimum principle above the side arcs of the modular cylinder

On the cylinder `ℍ/(z ↦ z + 1)` the unit semicircle splits into the bottom arc
`{|z| = 1, |Re z| ≤ ½}` and the two side arcs `{|z| = 1, ½ ≤ |Re z| < 1}`.  Translated into the
strip `0 ≤ u ≤ 1`, the side arcs are

`{(u − 1)² + y² = 1, 0 ≤ u ≤ ½}` and `{u² + y² = 1, ½ ≤ u ≤ 1}`,

which meet at `ρ = ½ + i√3/2` and run down to the cusps `u = 0` and `u = 1` on the real axis.  The
region above them is `{u² + y² ≥ 1} ∪ {(u − 1)² + y² ≥ 1}`; it contains the standard fundamental
domain together with its image under `z ↦ −1/z`, and it reaches the real axis in a horn of width
`≈ y²` at every integer.

Let `v(u, y)` be `1`-periodic in `u`, twice differentiable in each variable on `y > 0`, and a
solution of `L v = y (v_uu + v_yy) + v_y = 0` (that is, `Δ(√y v) = −¼ √y v`).  Suppose `v → 0`
uniformly as `y → ∞`, `v ≥ 0` on the side arcs, and `v` is almost nonnegative on the horn
cross-sections: for every `δ > 0` there is `η₀ > 0` with `v ≥ −δ` at every point of the region at
height `η ≤ η₀`.  Then `v ≥ 0` at every height `y ≥ 1` (`nonneg_of_nonneg_on_modularSideArc`).

Proof.  As for the bottom arc: subtract `ε eʸ` (with `L eʸ > 0`), truncate the region to
`η ≤ y ≤ Y`, `−1 ≤ u ≤ 2`, and move a minimizer into `0 ≤ u ≤ 1` by periodicity.  The top, the
horn cross-sections and the side arcs carry values `> −m`, so the minimizer is interior, where the
second-derivative test contradicts `L(v − ε eʸ) < 0`.
-/

open Filter Topology Set

namespace GaloisForLFunctions
namespace HTGeometry

/-- The truncated region above the side arcs, over `−1 ≤ u ≤ 2`, between heights `η` and `Y`.
Each disjunction is the condition of one period: outside the lens of the two unit disks centred
at consecutive integers. -/
def sideRegion (η Y : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (-1 : ℝ) 2 ∧ η ≤ p.2 ∧ p.2 ≤ Y ∧
    (1 ≤ (p.1 + 1) ^ 2 + p.2 ^ 2 ∨ 1 ≤ p.1 ^ 2 + p.2 ^ 2) ∧
    (1 ≤ p.1 ^ 2 + p.2 ^ 2 ∨ 1 ≤ (p.1 - 1) ^ 2 + p.2 ^ 2) ∧
    (1 ≤ (p.1 - 1) ^ 2 + p.2 ^ 2 ∨ 1 ≤ (p.1 - 2) ^ 2 + p.2 ^ 2)}

theorem isCompact_sideRegion (η Y : ℝ) : IsCompact (sideRegion η Y) := by
  have hsub : sideRegion η Y ⊆ Icc (-1 : ℝ) 2 ×ˢ Icc η Y := fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩
  refine (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset ?_ hsub
  have heq : sideRegion η Y =
      {p : ℝ × ℝ | -1 ≤ p.1} ∩ {p | p.1 ≤ 2} ∩ {p | η ≤ p.2} ∩ {p | p.2 ≤ Y} ∩
        ({p | 1 ≤ (p.1 + 1) ^ 2 + p.2 ^ 2} ∪ {p | 1 ≤ p.1 ^ 2 + p.2 ^ 2}) ∩
        ({p | 1 ≤ p.1 ^ 2 + p.2 ^ 2} ∪ {p | 1 ≤ (p.1 - 1) ^ 2 + p.2 ^ 2}) ∩
        ({p | 1 ≤ (p.1 - 1) ^ 2 + p.2 ^ 2} ∪ {p | 1 ≤ (p.1 - 2) ^ 2 + p.2 ^ 2}) := by
    ext p
    simp only [sideRegion, mem_inter_iff, mem_union, mem_setOf_eq, mem_Icc]
    tauto
  rw [heq]
  refine (((((((isClosed_le ?_ ?_).inter (isClosed_le ?_ ?_)).inter (isClosed_le ?_ ?_)).inter
    (isClosed_le ?_ ?_)).inter ((isClosed_le ?_ ?_).union (isClosed_le ?_ ?_))).inter
    ((isClosed_le ?_ ?_).union (isClosed_le ?_ ?_))).inter
    ((isClosed_le ?_ ?_).union (isClosed_le ?_ ?_))) <;> fun_prop

/-- A point of the region with `−1 ≤ u < 0` moves to the region under `u ↦ u + 1`. -/
theorem sideRegion_add_one {η Y : ℝ} {p : ℝ × ℝ} (hp : p ∈ sideRegion η Y) (h : p.1 < 0) :
    (p.1 + 1, p.2) ∈ sideRegion η Y := by
  obtain ⟨⟨h1, -⟩, h3, h4, h5, -, -⟩ := hp
  refine ⟨⟨by linarith, by linarith⟩, h3, h4, Or.inl (by simp only; nlinarith), ?_,
    Or.inr (by simp only; nlinarith)⟩
  simp only [add_sub_cancel_right]
  rcases h5 with h5 | h5
  · exact Or.inl h5
  · exact Or.inr h5

/-- A point of the region with `1 < u ≤ 2` moves to the region under `u ↦ u − 1`. -/
theorem sideRegion_sub_one {η Y : ℝ} {p : ℝ × ℝ} (hp : p ∈ sideRegion η Y) (h : 1 < p.1) :
    (p.1 - 1, p.2) ∈ sideRegion η Y := by
  obtain ⟨⟨-, h2⟩, h3, h4, -, -, h7⟩ := hp
  refine ⟨⟨by linarith, by linarith⟩, h3, h4, Or.inl (by simp only; nlinarith), ?_,
    Or.inr (by simp only; nlinarith)⟩
  simp only [show p.1 - 1 - 1 = p.1 - 2 by ring]
  exact h7

/-- **Minimum principle above the side arcs.** -/
theorem nonneg_of_nonneg_on_modularSideArc {v vu vuu vy vyy : ℝ → ℝ → ℝ}
    (hu : ∀ u y, 0 < y → HasDerivAt (fun s => v s y) (vu u y) u)
    (huu : ∀ u y, 0 < y → HasDerivAt (fun s => vu s y) (vuu u y) u)
    (hy : ∀ u y, 0 < y → HasDerivAt (fun s => v u s) (vy u y) y)
    (hyy : ∀ u y, 0 < y → HasDerivAt (fun s => vy u s) (vyy u y) y)
    (hL : ∀ u y, 0 < y → y * (vuu u y + vyy u y) + vy u y = 0)
    (hcont : ContinuousOn (fun p : ℝ × ℝ => v p.1 p.2) {p | 0 < p.2})
    (hper : ∀ u y, v (u + 1) y = v u y)
    (hdecay : ∀ ε > 0, ∃ Y, ∀ u y, Y ≤ y → |v u y| ≤ ε)
    (harc₁ : ∀ u y, 0 < y → 0 ≤ u → u ≤ 1 / 2 → (u - 1) ^ 2 + y ^ 2 = 1 → 0 ≤ v u y)
    (harc₂ : ∀ u y, 0 < y → 1 / 2 ≤ u → u ≤ 1 → u ^ 2 + y ^ 2 = 1 → 0 ≤ v u y)
    (hcusp : ∀ δ > 0, ∃ η₀ > 0, ∀ η, 0 < η → η ≤ η₀ → ∀ u, 0 ≤ u → u ≤ 1 →
      (1 ≤ u ^ 2 + η ^ 2 ∨ 1 ≤ (u - 1) ^ 2 + η ^ 2) → -δ ≤ v u η)
    {u₀ y₀ : ℝ} (hy₀ : 1 ≤ y₀) : 0 ≤ v u₀ y₀ := by
  by_contra hneg
  rw [not_le] at hneg
  have hperZ : ∀ (n : ℤ) u y, v (u + n) y = v u y := by
    intro n u y
    have hP : Function.Periodic (fun u => v u y) 1 := fun u => hper u y
    have := (hP.int_mul n) u
    simpa using this
  -- reduce `u₀` to `[0, 1)`
  set n₀ : ℤ := ⌊u₀⌋ with hn₀
  set u₀' : ℝ := u₀ - n₀ with hu₀'
  have hu₀'v : v u₀' y₀ = v u₀ y₀ := by
    have := hperZ n₀ u₀' y₀
    rw [hu₀', sub_add_cancel] at this
    exact this.symm
  have hu₀'lo : 0 ≤ u₀' := by have := Int.floor_le u₀; rw [hu₀']; linarith
  have hu₀'hi : u₀' < 1 := by have := Int.lt_floor_add_one u₀; rw [hu₀']; linarith
  set m := -v u₀ y₀ with hm
  have hm0 : 0 < m := by rw [hm]; linarith
  obtain ⟨Y₁, hY₁⟩ := hdecay (m / 4) (by linarith)
  set Y := max Y₁ (y₀ + 1) with hY
  have hYy₀ : y₀ < Y := by rw [hY]; linarith [le_max_right Y₁ (y₀ + 1)]
  have hYdec : ∀ u, |v u Y| ≤ m / 4 := fun u => hY₁ u Y (le_max_left _ _)
  obtain ⟨η₀, hη₀, hcη⟩ := hcusp (m / 4) (by linarith)
  set η := min η₀ (1 / 2) with hη
  have hη0 : 0 < η := lt_min hη₀ (by norm_num)
  have hηη₀ : η ≤ η₀ := min_le_left _ _
  have hηh : η ≤ 1 / 2 := min_le_right _ _
  set ε := m / 4 / Real.exp Y with hε
  have hε0 : 0 < ε := by positivity
  have hεY : ε * Real.exp Y = m / 4 := by rw [hε]; field_simp
  have hεy : ∀ y, y ≤ Y → ε * Real.exp y ≤ m / 4 := fun y hy =>
    hεY ▸ mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) hε0.le
  set f : ℝ × ℝ → ℝ := fun p => v p.1 p.2 - ε * Real.exp p.2 with hf
  set K := sideRegion η Y with hK
  have hK0 : ∀ p ∈ K, 0 < p.2 := fun p hp => lt_of_lt_of_le hη0 hp.2.1
  have hp₀K : (u₀', y₀) ∈ K := by
    refine ⟨⟨by linarith, by linarith⟩, by simp only; linarith, hYy₀.le, ?_, ?_, ?_⟩ <;>
      simp only <;> [exact Or.inl (by nlinarith); exact Or.inl (by nlinarith);
        exact Or.inr (by nlinarith)]
  have hfcont : ContinuousOn f K := by
    refine (hcont.mono fun p hp => hK0 p hp).sub ?_
    exact (continuous_const.mul (Real.continuous_exp.comp continuous_snd)).continuousOn
  obtain ⟨p₁, hp₁K, hp₁min⟩ := (isCompact_sideRegion η Y).exists_isMinOn ⟨_, hp₀K⟩ hfcont
  -- move the minimizer into `0 ≤ u ≤ 1`
  have hshift : ∃ q ∈ K, f q = f p₁ ∧ 0 ≤ q.1 ∧ q.1 ≤ 1 := by
    rcases lt_or_ge p₁.1 0 with hlo | hlo
    · refine ⟨(p₁.1 + 1, p₁.2), sideRegion_add_one hp₁K hlo, ?_, ?_, ?_⟩
      · simp only [hf]
        have := hperZ 1 p₁.1 p₁.2
        simpa using this
      · simp only; have := hp₁K.1.1; linarith
      · simp only; linarith
    · rcases le_or_gt p₁.1 1 with hhi | hhi
      · exact ⟨p₁, hp₁K, rfl, hlo, hhi⟩
      · refine ⟨(p₁.1 - 1, p₁.2), sideRegion_sub_one hp₁K hhi, ?_, ?_, ?_⟩
        · simp only [hf]
          have := hperZ 1 (p₁.1 - 1) p₁.2
          simp only [Int.cast_one, sub_add_cancel] at this
          rw [this]
        · simp only; linarith
        · simp only; have := hp₁K.1.2; linarith
  obtain ⟨q, hqK, hqf, hq1lo, hq1hi⟩ := hshift
  have hqmin : ∀ p ∈ K, f q ≤ f p := fun p hp => hqf ▸ hp₁min hp
  have hfq : f q < -m := by
    have := hqmin _ hp₀K
    simp only [hf] at this ⊢
    rw [hu₀'v] at this
    have := Real.exp_pos y₀
    nlinarith
  have hq0 : 0 < q.2 := hK0 q hqK
  obtain ⟨⟨hq1, hq2⟩, hq3, hq4, -, hq6, -⟩ := hqK
  -- not on the top
  have hqY : q.2 < Y := by
    rcases hq4.lt_or_eq with h | h
    · exact h
    · exfalso
      have h1 := hYdec q.1
      have h2 := hεy q.2 hq4
      simp only [hf] at hfq
      rw [h] at hfq h2
      rw [abs_le] at h1
      linarith [h1.1]
  -- not on the horn cross-section
  have hqη : η < q.2 := by
    rcases hq3.lt_or_eq with h | h
    · exact h
    · exfalso
      have hreg : 1 ≤ q.1 ^ 2 + η ^ 2 ∨ 1 ≤ (q.1 - 1) ^ 2 + η ^ 2 := by rw [h]; exact hq6
      have h1 := hcη η hη0 hηη₀ q.1 hq1lo hq1hi hreg
      have h2 := hεy q.2 hq4
      simp only [hf] at hfq
      rw [h] at h1
      linarith
  -- not on the side arcs
  have hqarc : 1 < q.1 ^ 2 + q.2 ^ 2 ∨ 1 < (q.1 - 1) ^ 2 + q.2 ^ 2 := by
    by_contra hcon
    rw [not_or, not_lt, not_lt] at hcon
    obtain ⟨hc1, hc2⟩ := hcon
    have h2 := hεy q.2 hq4
    simp only [hf] at hfq
    rcases hq6 with h6 | h6
    · have heq : q.1 ^ 2 + q.2 ^ 2 = 1 := le_antisymm hc1 h6
      have hhalf : 1 / 2 ≤ q.1 := by nlinarith
      have := harc₂ q.1 q.2 hq0 hhalf hq1hi heq
      linarith
    · have heq : (q.1 - 1) ^ 2 + q.2 ^ 2 = 1 := le_antisymm hc2 h6
      have hhalf : q.1 ≤ 1 / 2 := by nlinarith
      have := harc₁ q.1 q.2 hq0 hq1lo hhalf heq
      linarith
  -- local minimality in each direction
  have hmemK : ∀ᶠ p in 𝓝 q, p ∈ K := by
    have c1 : ∀ᶠ p in 𝓝 q, p.1 ∈ Ioo (-1 : ℝ) 2 :=
      continuous_fst.continuousAt.eventually_mem (Ioo_mem_nhds (by linarith) (by linarith))
    have c2 : ∀ᶠ p in 𝓝 q, p.2 < Y :=
      continuous_snd.continuousAt.eventually_lt continuousAt_const hqY
    have c3 : ∀ᶠ p in 𝓝 q, η < p.2 :=
      continuousAt_const.eventually_lt continuous_snd.continuousAt hqη
    have c4 : ∀ᶠ p in 𝓝 q, 1 < (p.1 + 1) ^ 2 + p.2 ^ 2 :=
      continuousAt_const.eventually_lt (by fun_prop) (by nlinarith)
    have c5 : ∀ᶠ p in 𝓝 q, 1 < (p.1 - 2) ^ 2 + p.2 ^ 2 :=
      continuousAt_const.eventually_lt (by fun_prop) (by nlinarith)
    have c6 : ∀ᶠ p in 𝓝 q, 1 < p.1 ^ 2 + p.2 ^ 2 ∨ 1 < (p.1 - 1) ^ 2 + p.2 ^ 2 := by
      have g1 : ContinuousAt (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) q := by fun_prop
      have g2 : ContinuousAt (fun p : ℝ × ℝ => (p.1 - 1) ^ 2 + p.2 ^ 2) q := by fun_prop
      rcases hqarc with h | h
      · exact (continuousAt_const.eventually_lt g1 h).mono fun p hp => Or.inl hp
      · exact (continuousAt_const.eventually_lt g2 h).mono fun p hp => Or.inr hp
    filter_upwards [c1, c2, c3, c4, c5, c6] with p h1 h2 h3 h4 h5 h6
    refine ⟨⟨h1.1.le, h1.2.le⟩, h3.le, h2.le, Or.inl h4.le, ?_, Or.inr h5.le⟩
    rcases h6 with h6 | h6
    · exact Or.inl h6.le
    · exact Or.inr h6.le
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
