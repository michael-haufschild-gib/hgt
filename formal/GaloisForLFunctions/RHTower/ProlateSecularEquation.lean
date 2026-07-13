import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# The rank-one secular equation of the constrained prolate ground state

The Connes–Consani–Moscovici vanishing-integral prolate ground state (card
`constrained-prolate-two-mode-ground-state`, §2) is characterized as a root of the **secular
equation** of a diagonal operator under a rank-one linear constraint: for a constrained eigenvalue
`μ` strictly between two consecutive leakage values `d_j`, the eigenvector coordinates are
`v_j = ℓ_j/(d_j − μ)`, and the constraint `⟨v, ℓ⟩ = 0` is exactly

`F(μ) := ∑_j ℓ_j² / (d_j − μ) = 0`.

The load-bearing fact — which forces simplicity of the constrained ground state — is that `F` is
**strictly increasing** on any interval free of the poles `d_j` (provided some `ℓ_j ≠ 0`), so it has
at most one root there.  This file proves that strict monotonicity unconditionally.
-/

open Finset

namespace GaloisForLFunctions

variable {ι : Type*}

/-- The rank-one secular function `F(μ) = ∑_j ℓ_j² / (d_j − μ)` of a diagonal operator with
eigenvalues `d` under the linear constraint with Riesz coordinates `ℓ`. -/
noncomputable def secularFunction (s : Finset ι) (d ℓ : ι → ℝ) (μ : ℝ) : ℝ :=
  ∑ j ∈ s, (ℓ j) ^ 2 / (d j - μ)

/-- On an interval `(a, b)` free of all poles `d_j`, each secular summand is monotone in `μ`, and
strictly so at any index with `ℓ_j ≠ 0`: `ℓ_j²/(d_j − μ₁) ≤ ℓ_j²/(d_j − μ₂)` for `μ₁ < μ₂`. -/
theorem secular_term_lt {d ℓ : ι → ℝ} {a b μ₁ μ₂ : ℝ} (j : ι)
    (hpole : d j ≤ a ∨ b ≤ d j) (hμ₁ : μ₁ ∈ Set.Ioo a b) (hμ₂ : μ₂ ∈ Set.Ioo a b)
    (hlt : μ₁ < μ₂) (hℓ : ℓ j ≠ 0) :
    (ℓ j) ^ 2 / (d j - μ₁) < (ℓ j) ^ 2 / (d j - μ₂) := by
  obtain ⟨ha₁, hb₁⟩ := hμ₁
  obtain ⟨ha₂, hb₂⟩ := hμ₂
  -- both denominators share a sign, so their product is positive and both are nonzero
  have hprod : 0 < (d j - μ₂) * (d j - μ₁) := by
    rcases hpole with h | h
    · exact mul_pos_of_neg_of_neg (by linarith) (by linarith)
    · exact mul_pos (by linarith) (by linarith)
  have hne₁ : d j - μ₁ ≠ 0 := by
    rcases hpole with h | h
    · exact ne_of_lt (by linarith)
    · exact ne_of_gt (by linarith)
  have hne₂ : d j - μ₂ ≠ 0 := by
    rcases hpole with h | h
    · exact ne_of_lt (by linarith)
    · exact ne_of_gt (by linarith)
  have hdiff : (ℓ j) ^ 2 / (d j - μ₂) - (ℓ j) ^ 2 / (d j - μ₁)
      = (ℓ j) ^ 2 * (μ₂ - μ₁) / ((d j - μ₂) * (d j - μ₁)) := by
    field_simp
    ring
  have hpos : 0 < (ℓ j) ^ 2 * (μ₂ - μ₁) / ((d j - μ₂) * (d j - μ₁)) :=
    div_pos (mul_pos (by positivity) (by linarith)) hprod
  linarith [hdiff ▸ hpos]

/-- The non-strict version of `secular_term_lt`, valid at every index (trivial when `ℓ_j = 0`). -/
theorem secular_term_le {d ℓ : ι → ℝ} {a b μ₁ μ₂ : ℝ} (j : ι)
    (hpole : d j ≤ a ∨ b ≤ d j) (hμ₁ : μ₁ ∈ Set.Ioo a b) (hμ₂ : μ₂ ∈ Set.Ioo a b)
    (hlt : μ₁ < μ₂) :
    (ℓ j) ^ 2 / (d j - μ₁) ≤ (ℓ j) ^ 2 / (d j - μ₂) := by
  rcases eq_or_ne (ℓ j) 0 with h | h
  · simp [h]
  · exact (secular_term_lt j hpole hμ₁ hμ₂ hlt h).le

/-- **Strict monotonicity of the secular function.**  If every pole `d_j` lies outside `(a, b)` and
some coordinate `ℓ_{j₀} ≠ 0`, then `F(μ) = ∑_j ℓ_j²/(d_j − μ)` is strictly increasing on `(a, b)`.
Hence `F` has at most one root there: the constrained prolate ground eigenvalue is simple. -/
theorem secular_strictMonoOn (s : Finset ι) (d ℓ : ι → ℝ) {a b : ℝ}
    (hpole : ∀ j ∈ s, d j ≤ a ∨ b ≤ d j)
    {j₀ : ι} (hj₀ : j₀ ∈ s) (hℓ : ℓ j₀ ≠ 0) :
    StrictMonoOn (secularFunction s d ℓ) (Set.Ioo a b) := by
  intro μ₁ hμ₁ μ₂ hμ₂ hlt
  refine Finset.sum_lt_sum (fun j hj => secular_term_le j (hpole j hj) hμ₁ hμ₂ hlt) ?_
  exact ⟨j₀, hj₀, secular_term_lt j₀ (hpole j₀ hj₀) hμ₁ hμ₂ hlt hℓ⟩

/-- The constrained prolate ground state is simple: the secular function has at most one root on a
pole-free interval. -/
theorem secular_root_unique (s : Finset ι) (d ℓ : ι → ℝ) {a b : ℝ}
    (hpole : ∀ j ∈ s, d j ≤ a ∨ b ≤ d j) {j₀ : ι} (hj₀ : j₀ ∈ s) (hℓ : ℓ j₀ ≠ 0)
    {μ μ' : ℝ} (hμ : μ ∈ Set.Ioo a b) (hμ' : μ' ∈ Set.Ioo a b)
    (h : secularFunction s d ℓ μ = 0) (h' : secularFunction s d ℓ μ' = 0) : μ = μ' :=
  (secular_strictMonoOn s d ℓ hpole hj₀ hℓ).injOn hμ hμ' (h.trans h'.symm)

/-- The exact root of the two-mode secular equation — the CCM two-mode trial value
`μ_2mode = (ℓ₀² d₁ + ℓ₁² d₀)/(ℓ₀² + ℓ₁²)` of the ground-state card (eq. 12). -/
noncomputable def twoModeSecularRoot (d₀ d₁ ℓ₀ ℓ₁ : ℝ) : ℝ :=
  (ℓ₀ ^ 2 * d₁ + ℓ₁ ^ 2 * d₀) / (ℓ₀ ^ 2 + ℓ₁ ^ 2)

/-- The two-mode trial value is a strict convex combination of the two leakage values: it lies
strictly between `d₀` and `d₁`.  (This is the card's "`μ_2mode` lies strictly between `d₀` and
`d₁`", giving a constrained eigenvalue below `d₁`.) -/
theorem twoModeSecularRoot_mem_Ioo {d₀ d₁ ℓ₀ ℓ₁ : ℝ} (hd : d₀ < d₁) (h₀ : ℓ₀ ≠ 0) (h₁ : ℓ₁ ≠ 0) :
    twoModeSecularRoot d₀ d₁ ℓ₀ ℓ₁ ∈ Set.Ioo d₀ d₁ := by
  have hden : (0 : ℝ) < ℓ₀ ^ 2 + ℓ₁ ^ 2 := by positivity
  have h0 : (0 : ℝ) < ℓ₀ ^ 2 := by positivity
  have h1 : (0 : ℝ) < ℓ₁ ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · rw [twoModeSecularRoot, lt_div_iff₀ hden]; nlinarith
  · rw [twoModeSecularRoot, div_lt_iff₀ hden]; nlinarith

/-- The two-mode trial value is exactly the root of the two-mode secular equation
`ℓ₀²/(d₀ − μ) + ℓ₁²/(d₁ − μ) = 0`. -/
theorem twoModeSecular_eq_zero {d₀ d₁ ℓ₀ ℓ₁ : ℝ} (hd : d₀ < d₁) (h₀ : ℓ₀ ≠ 0) (h₁ : ℓ₁ ≠ 0) :
    ℓ₀ ^ 2 / (d₀ - twoModeSecularRoot d₀ d₁ ℓ₀ ℓ₁)
      + ℓ₁ ^ 2 / (d₁ - twoModeSecularRoot d₀ d₁ ℓ₀ ℓ₁) = 0 := by
  obtain ⟨hlo, hhi⟩ := twoModeSecularRoot_mem_Ioo hd h₀ h₁
  have hne₀ : d₀ - twoModeSecularRoot d₀ d₁ ℓ₀ ℓ₁ ≠ 0 := by intro h; simp only [sub_eq_zero] at h; linarith
  have hne₁ : d₁ - twoModeSecularRoot d₀ d₁ ℓ₀ ℓ₁ ≠ 0 := by intro h; simp only [sub_eq_zero] at h; linarith
  have hden : (0 : ℝ) < ℓ₀ ^ 2 + ℓ₁ ^ 2 := by positivity
  rw [div_add_div _ _ hne₀ hne₁, div_eq_zero_iff]
  left
  rw [twoModeSecularRoot]
  field_simp
  ring

open Filter Topology

/-- Pole limit: `c/(p − μ) → −∞` as `μ → p⁺` for `c > 0`. -/
theorem tendsto_const_div_sub_atBot {p c : ℝ} (hc : 0 < c) :
    Tendsto (fun μ => c / (p - μ)) (𝓝[>] p) atBot := by
  have h1 : Tendsto (fun μ : ℝ => μ - p) (𝓝[>] p) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using ((continuous_sub_right p).tendsto p).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Ioi] at hx ⊢; linarith
  have h3 : Tendsto (fun μ : ℝ => c * (μ - p)⁻¹) (𝓝[>] p) atTop :=
    Filter.Tendsto.const_mul_atTop hc (tendsto_inv_nhdsGT_zero.comp h1)
  have heq : (fun μ : ℝ => c / (p - μ)) = (fun μ => -(c * (μ - p)⁻¹)) := by
    funext μ; rw [div_eq_mul_inv, show p - μ = -(μ - p) from by ring, inv_neg, mul_neg]
  rw [heq]; exact tendsto_neg_atTop_atBot.comp h3

/-- Pole limit: `c/(p − μ) → +∞` as `μ → p⁻` for `c > 0`. -/
theorem tendsto_const_div_sub_atTop {p c : ℝ} (hc : 0 < c) :
    Tendsto (fun μ => c / (p - μ)) (𝓝[<] p) atTop := by
  have h1 : Tendsto (fun μ : ℝ => p - μ) (𝓝[<] p) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc' : Continuous (fun μ : ℝ => p - μ) := continuous_const.sub continuous_id
      simpa using (hc'.tendsto p).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Ioi, Set.mem_Iio] at hx ⊢; linarith
  have h3 : Tendsto (fun μ : ℝ => c * (p - μ)⁻¹) (𝓝[<] p) atTop :=
    Filter.Tendsto.const_mul_atTop hc (tendsto_inv_nhdsGT_zero.comp h1)
  exact h3.congr (fun μ => by rw [div_eq_mul_inv])

/-- **Secular root existence.**  If `a₀, b₀` index consecutive poles (`d a₀ < d b₀`, nothing strictly
between them and no other pole coinciding with either), both with nonzero constraint coordinate, then
the secular equation `F(μ) = 0` has a root in `(d a₀, d b₀)`. -/
theorem secular_exists_root [DecidableEq ι] (s : Finset ι) (d ℓ : ι → ℝ) {a₀ b₀ : ι}
    (ha₀ : a₀ ∈ s) (hb₀ : b₀ ∈ s) (hd : d a₀ < d b₀) (hℓa : ℓ a₀ ≠ 0) (hℓb : ℓ b₀ ≠ 0)
    (hsep : ∀ j ∈ s, j ≠ a₀ → j ≠ b₀ → d j < d a₀ ∨ d b₀ < d j) :
    ∃ μ ∈ Set.Ioo (d a₀) (d b₀), secularFunction s d ℓ μ = 0 := by
  -- every pole other than a₀ is ≠ d a₀; other than b₀ is ≠ d b₀
  have hjne_a : ∀ j ∈ s, j ≠ a₀ → d j ≠ d a₀ := by
    intro j hj hja
    rcases eq_or_ne j b₀ with rfl | hjb
    · exact ne_of_gt hd
    · rcases hsep j hj hja hjb with h | h
      · exact ne_of_lt h
      · exact ne_of_gt (hd.trans h)
  have hjne_b : ∀ j ∈ s, j ≠ b₀ → d j ≠ d b₀ := by
    intro j hj hjb
    rcases eq_or_ne j a₀ with rfl | hja
    · exact ne_of_lt hd
    · rcases hsep j hj hja hjb with h | h
      · exact ne_of_lt (h.trans hd)
      · exact ne_of_gt h
  -- interior points avoid all poles
  have hinterior : ∀ μ ∈ Set.Ioo (d a₀) (d b₀), ∀ j ∈ s, d j - μ ≠ 0 := by
    rintro μ ⟨hμa, hμb⟩ j hj
    rcases eq_or_ne j a₀ with rfl | hja
    · exact ne_of_lt (by linarith)
    · rcases eq_or_ne j b₀ with rfl | hjb
      · exact ne_of_gt (by linarith)
      · rcases hsep j hj hja hjb with h | h
        · exact ne_of_lt (by linarith)
        · exact ne_of_gt (by linarith)
  -- F is continuous on the open interval
  have hcont : ContinuousOn (secularFunction s d ℓ) (Set.Ioo (d a₀) (d b₀)) := by
    apply continuousOn_finsetSum
    intro j hj
    exact (continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      (fun μ hμ => hinterior μ hμ j hj))
  -- the pole hypothesis in the form needed by `secular_strictMonoOn`
  have hpole : ∀ j ∈ s, d j ≤ d a₀ ∨ d b₀ ≤ d j := by
    intro j hj
    rcases eq_or_ne j a₀ with rfl | hja
    · exact Or.inl le_rfl
    · rcases eq_or_ne j b₀ with rfl | hjb
      · exact Or.inr le_rfl
      · rcases hsep j hj hja hjb with h | h
        · exact Or.inl h.le
        · exact Or.inr h.le
  have hmono := secular_strictMonoOn s d ℓ hpole ha₀ hℓa
  -- limit `→ −∞` at `d a₀⁺`
  have hatBot : Tendsto (secularFunction s d ℓ) (𝓝[>] (d a₀)) atBot := by
    have hsplit : secularFunction s d ℓ = fun μ =>
        (ℓ a₀) ^ 2 / (d a₀ - μ) + ∑ j ∈ s.erase a₀, (ℓ j) ^ 2 / (d j - μ) :=
      funext fun μ => (Finset.add_sum_erase s (fun j => (ℓ j) ^ 2 / (d j - μ)) ha₀).symm
    rw [hsplit]
    have hrest : Tendsto (fun μ => ∑ j ∈ s.erase a₀, (ℓ j) ^ 2 / (d j - μ)) (𝓝[>] (d a₀))
        (𝓝 (∑ j ∈ s.erase a₀, (ℓ j) ^ 2 / (d j - d a₀))) := by
      refine tendsto_finsetSum _ fun j hj => ?_
      refine (ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds
      exact continuousAt_const.div (continuousAt_const.sub continuousAt_id)
        (sub_ne_zero.mpr (hjne_a j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)))
    exact Tendsto.atBot_add (tendsto_const_div_sub_atBot (by positivity)) hrest
  -- limit `→ +∞` at `d b₀⁻`
  have hatTop : Tendsto (secularFunction s d ℓ) (𝓝[<] (d b₀)) atTop := by
    have hsplit : secularFunction s d ℓ = fun μ =>
        (ℓ b₀) ^ 2 / (d b₀ - μ) + ∑ j ∈ s.erase b₀, (ℓ j) ^ 2 / (d j - μ) :=
      funext fun μ => (Finset.add_sum_erase s (fun j => (ℓ j) ^ 2 / (d j - μ)) hb₀).symm
    rw [hsplit]
    have hrest : Tendsto (fun μ => ∑ j ∈ s.erase b₀, (ℓ j) ^ 2 / (d j - μ)) (𝓝[<] (d b₀))
        (𝓝 (∑ j ∈ s.erase b₀, (ℓ j) ^ 2 / (d j - d b₀))) := by
      refine tendsto_finsetSum _ fun j hj => ?_
      refine (ContinuousAt.tendsto ?_).mono_left nhdsWithin_le_nhds
      exact continuousAt_const.div (continuousAt_const.sub continuousAt_id)
        (sub_ne_zero.mpr (hjne_b j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)))
    exact Tendsto.atTop_add (tendsto_const_div_sub_atTop (by positivity)) hrest
  -- a point with `F < 0` and one with `F > 0`, both in the interval
  have hev_lo : ∀ᶠ μ in 𝓝[>] (d a₀),
      secularFunction s d ℓ μ < 0 ∧ μ ∈ Set.Ioo (d a₀) (d b₀) := by
    refine (hatBot.eventually (eventually_lt_atBot 0)).and ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hd).filter_mono (nhdsWithin_le_nhds)] with μ h1 h2
    exact ⟨h1, h2⟩
  have hev_hi : ∀ᶠ μ in 𝓝[<] (d b₀),
      0 < secularFunction s d ℓ μ ∧ μ ∈ Set.Ioo (d a₀) (d b₀) := by
    refine (hatTop.eventually (eventually_gt_atTop 0)).and ?_
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hd).filter_mono (nhdsWithin_le_nhds)] with μ h1 h2
    exact ⟨h2, h1⟩
  obtain ⟨μlo, hμlo_neg, hμlo_mem⟩ := hev_lo.exists
  obtain ⟨μhi, hμhi_pos, hμhi_mem⟩ := hev_hi.exists
  have hlt : μlo < μhi := by
    by_contra h
    push Not at h
    exact absurd (hmono.monotoneOn hμhi_mem hμlo_mem h) (by linarith)
  -- intermediate value theorem
  have hsub : Set.Icc μlo μhi ⊆ Set.Ioo (d a₀) (d b₀) :=
    Set.Icc_subset_Ioo hμlo_mem.1 hμhi_mem.2
  have : (0 : ℝ) ∈ secularFunction s d ℓ '' Set.Icc μlo μhi :=
    intermediate_value_Icc hlt.le (hcont.mono hsub) ⟨hμlo_neg.le, hμhi_pos.le⟩
  obtain ⟨μ, hμmem, hμ0⟩ := this
  exact ⟨μ, hsub hμmem, hμ0⟩

/-- **The CCM ground-state constant `8/11`** (card eq. 11).  With the prolate-to-Hermite limits
`a₀ = 2^{1/4}` (on mode `0`) and `a₁ = √3 · 2^{−5/4}` (on mode `4`), the limiting two-mode weight is
`a₀²/(a₀² + a₁²) = 8/11` — the value `μ_0(λ)/d_1(λ)` converges to in (5). -/
theorem ccm_groundState_weight_eq :
    ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 /
      (((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 + (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2) = 8 / 11 := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have ha0 : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 4)) 2, ← Real.rpow_mul h2]; norm_num
  have ha1 : (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2 = 3 / (2 : ℝ) ^ ((5 : ℝ) / 2) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
      ← Real.rpow_natCast ((2 : ℝ) ^ ((5 : ℝ) / 4)) 2, ← Real.rpow_mul h2]; norm_num
  have h22 : (2 : ℝ) ^ (2 : ℝ) = 4 := by norm_num [Real.rpow_natCast]
  have h52 : (2 : ℝ) ^ ((5 : ℝ) / 2) = 4 * (2 : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [show (5 : ℝ) / 2 = 1 / 2 + 2 by norm_num, Real.rpow_add (by norm_num), h22]
    ring
  rw [ha0, ha1, h52]
  have hs : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hsq : ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = 2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 2)) 2, ← Real.rpow_mul h2]; norm_num
  set s := (2 : ℝ) ^ ((1 : ℝ) / 2) with hsdef
  rw [div_eq_iff (by positivity)]
  field_simp
  nlinarith [hsq, hs]


/-- **Codimension-one interlacing** (card eq. 23).  For three consecutive poles
`d a₀ < d b₀ < d c₀` (nothing strictly between them, no other pole coinciding, all with `ℓ ≠ 0`),
the constrained eigenvalues interlace them: there are roots `μ₀ ∈ (d a₀, d b₀)` and
`μ₁ ∈ (d b₀, d c₀)`, so `d a₀ < μ₀ < d b₀ < μ₁ < d c₀`. -/
theorem secular_interlacing [DecidableEq ι] (s : Finset ι) (d ℓ : ι → ℝ) {a₀ b₀ c₀ : ι}
    (ha₀ : a₀ ∈ s) (hb₀ : b₀ ∈ s) (hc₀ : c₀ ∈ s) (hab : d a₀ < d b₀) (hbc : d b₀ < d c₀)
    (hℓa : ℓ a₀ ≠ 0) (hℓb : ℓ b₀ ≠ 0) (hℓc : ℓ c₀ ≠ 0)
    (hsep : ∀ j ∈ s, j ≠ a₀ → j ≠ b₀ → j ≠ c₀ → d j < d a₀ ∨ d c₀ < d j) :
    ∃ μ₀ ∈ Set.Ioo (d a₀) (d b₀), ∃ μ₁ ∈ Set.Ioo (d b₀) (d c₀),
      secularFunction s d ℓ μ₀ = 0 ∧ secularFunction s d ℓ μ₁ = 0 := by
  have hsep1 : ∀ j ∈ s, j ≠ a₀ → j ≠ b₀ → d j < d a₀ ∨ d b₀ < d j := by
    intro j hj hja hjb
    rcases eq_or_ne j c₀ with rfl | hjc
    · exact Or.inr hbc
    · rcases hsep j hj hja hjb hjc with h | h
      · exact Or.inl h
      · exact Or.inr (hbc.trans h)
  have hsep2 : ∀ j ∈ s, j ≠ b₀ → j ≠ c₀ → d j < d b₀ ∨ d c₀ < d j := by
    intro j hj hjb hjc
    rcases eq_or_ne j a₀ with rfl | hja
    · exact Or.inl hab
    · rcases hsep j hj hja hjb hjc with h | h
      · exact Or.inl (h.trans hab)
      · exact Or.inr h
  obtain ⟨μ₀, hμ₀mem, hμ₀0⟩ := secular_exists_root s d ℓ ha₀ hb₀ hab hℓa hℓb hsep1
  obtain ⟨μ₁, hμ₁mem, hμ₁0⟩ := secular_exists_root s d ℓ hb₀ hc₀ hbc hℓb hℓc hsep2
  exact ⟨μ₀, hμ₀mem, μ₁, hμ₁mem, hμ₀0, hμ₁0⟩


end GaloisForLFunctions
