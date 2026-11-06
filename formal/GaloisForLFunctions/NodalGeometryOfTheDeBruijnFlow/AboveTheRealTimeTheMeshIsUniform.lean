import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheGapsObeyAMaximumPrinciple
import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.AboveTheHorizonTheZerosAreSpaced

/-!
# Above the real time the mesh is uniform

The local repulsion law in closed form. Suppose that all zeros of the flow above a fixed height are real and simple during `[a, t]`, with `t ≤ 5a/4`. Then every pair of real zeros of `H_t` in the range
`t log x ≤ 1` satisfies

`(x' − x)² ≥ min(c a (t − a), c a², g₁²)`    (`exists_uniform_mesh`),

with `c` absolute and `g₁ > 0` the least gap in a bounded range of heights during `[a, t]`, which is positive by compactness (`exists_low_gap`).

The top of the cylinder is the horizon height `2π e^{0.7/a}`, where the gaps are spaced by `≍ a` from the half-Gauss estimates, and there the barrier starts: the maximum principle carries it down to all lower heights in
heat time `≍ a(t − a)`. At a real time `a = 4t/5` this is `g_t² ≫ t²`. It is the shape of the local repulsion law: a rate `≍ 1/log X` from the mesh pair, which a cluster of `≍ log X` zeros would saturate. Every `a` above the de Bruijn–Newman constant
is a real time (`exists_uniform_mesh_above_newman`).
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- **The gaps in a bounded range of heights** are bounded below by compactness, if the zeros there stay real and simple. -/
theorem exists_low_gap {A A₁ a t : ℝ} (ha : 0 < a)
    (hreal : ∀ s ∈ Icc a t, ∀ x : ℝ, x ∈ Icc A (A₁ + 1) → riemannHeat s (x : ℂ) = 0 →
      deriv (riemannHeat s) (x : ℂ) ≠ 0) :
    ∃ g₁ : ℝ, 0 < g₁ ∧ g₁ ≤ 1 ∧ ∀ s ∈ Icc a t, ∀ x x' : ℝ, x < x' → x ∈ Icc A A₁ → x' ∈ Icc A (A₁ + 1) ∨ A₁ + 1 < x' →
      riemannHeat s (x : ℂ) = 0 → riemannHeat s (x' : ℂ) = 0 → g₁ ≤ x' - x := by
  by_contra hcon
  have hseq (n : ℕ) : ∃ p : ℝ × ℝ × ℝ, p.1 ∈ Icc a t ∧ p.2.1 ∈ Icc A A₁ ∧ p.2.2 ∈ Icc A (A₁ + 1) ∧
      p.2.1 < p.2.2 ∧ riemannHeat p.1 (p.2.1 : ℂ) = 0 ∧ riemannHeat p.1 (p.2.2 : ℂ) = 0 ∧
      p.2.2 - p.2.1 < 1 / ((n : ℝ) + 1) := by
    by_contra hn
    push Not at hn
    refine hcon ⟨1 / ((n : ℝ) + 1), by positivity, ?_, ?_⟩
    · rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith only [this]
    · intro s hs x x' h1 h2 h3 h4 h5
      rcases h3 with h3 | h3
      · exact hn (s, x, x') hs h2 h3 h1 h4 h5
      · have h6 : (1 : ℝ) ≤ x' - x := by linarith only [h3, h2.2]
        refine le_trans ?_ h6
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith only [this]
  choose P hP using hseq
  have hmem (n : ℕ) : P n ∈ Icc a t ×ˢ (Icc A A₁ ×ˢ Icc A (A₁ + 1)) :=
    ⟨(hP n).1, (hP n).2.1, (hP n).2.2.1⟩
  obtain ⟨⟨s₀, y, y'⟩, hlimmem, φ, hφ, hlim⟩ :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).tendsto_subseq hmem
  have hs₀pos : 0 < s₀ := ha.trans_le hlimmem.1.1
  have h1 : Tendsto (fun n => (P (φ n)).1) atTop (𝓝 s₀) := (continuous_fst.tendsto _).comp hlim
  have h2 : Tendsto (fun n => (P (φ n)).2.1) atTop (𝓝 y) :=
    ((continuous_fst.comp continuous_snd).tendsto _).comp hlim
  have h3 : Tendsto (fun n => (P (φ n)).2.2) atTop (𝓝 y') :=
    ((continuous_snd.comp continuous_snd).tendsto _).comp hlim
  have hgap : Tendsto (fun n => (P (φ n)).2.2 - (P (φ n)).2.1) atTop (𝓝 0) := by
    have h4 : Tendsto (fun n : ℕ => 1 / (((φ n : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    refine squeeze_zero (fun n => ?_) (fun n => (hP (φ n)).2.2.2.2.2.2.le) h4
    have := (hP (φ n)).2.2.2.1
    linarith only [this]
  have hyy : y' - y = 0 := tendsto_nhds_unique (h3.sub h2) hgap
  have hyeq : y' = y := by linarith only [hyy]
  have hy0 : riemannHeat s₀ (y : ℂ) = 0 := by
    have h := tendsto_riemannHeat_comp hs₀pos h1 (Complex.continuous_ofReal.continuousAt.tendsto.comp h2)
    refine tendsto_nhds_unique h ?_
    simp only [Function.comp_def, fun n => (hP (φ n)).2.2.2.2.1]
    exact tendsto_const_nhds
  have hyin : y ∈ Icc A (A₁ + 1) := ⟨hlimmem.2.1.1, by linarith only [hlimmem.2.1.2]⟩
  obtain ⟨ε, hε, z, -, -, -, hz⟩ := exists_real_branch hs₀pos hy0 (hreal s₀ hlimmem.1 y hyin hy0)
  have hev1 : ∀ᶠ n in atTop, |(P (φ n)).2.1 - y| ≤ ε := by
    have := (h2.sub_const y).abs
    simp only [sub_self, abs_zero] at this
    exact (this.eventually (gt_mem_nhds hε)).mono fun _ h => h.le
  have hev2 : ∀ᶠ n in atTop, |(P (φ n)).2.2 - y| ≤ ε := by
    have h3' : Tendsto (fun n => (P (φ n)).2.2) atTop (𝓝 y) := by rwa [hyeq] at h3
    have := (h3'.sub_const y).abs
    simp only [sub_self, abs_zero] at this
    exact (this.eventually (gt_mem_nhds hε)).mono fun _ h => h.le
  obtain ⟨n, hn, hn1, hn2⟩ := ((h1.eventually hz).and (hev1.and hev2)).exists
  have hA := hn _ hn1 (hP (φ n)).2.2.2.2.1
  have hB := hn _ hn2 (hP (φ n)).2.2.2.2.2.1
  have hlt := (hP (φ n)).2.2.2.1
  rw [hA, hB] at hlt
  exact lt_irrefl _ hlt

/-- **The uniform mesh above the real time.** If the zeros above a fixed height are real and simple during `[a, t]`, `t ≤ 5a/4`, then the pairs of real zeros of `H_t` in the range `t log x ≤ 1` satisfy
`(x' − x)² ≥ min(c a (t − a), c a², g₁)`, with `g₁ > 0` depending only on the bounded range of heights. -/
theorem exists_uniform_mesh :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ a₀ : ℝ, 4096 ≤ X₀ ∧ 0 < a₀ ∧ ∀ a t : ℝ, 0 < a → a ≤ a₀ → a ≤ t → t ≤ 5 / 4 * a →
      (∀ s ∈ Icc a t, ∀ z : ℂ, riemannHeat s z = 0 → X₀ ≤ z.re → z.im = 0 ∧ deriv (riemannHeat s) z ≠ 0) →
      ∃ g₁ : ℝ, 0 < g₁ ∧ ∀ x x' : ℝ, x < x' → X₀ ≤ x → t * Real.log x ≤ 1 →
        riemannHeat t (x : ℂ) = 0 → riemannHeat t (x' : ℂ) = 0 →
        min (min (c * a * (t - a)) (c * a ^ 2)) g₁ ≤ (x' - x) ^ 2 := by
  obtain ⟨C, hC, X₁, hX₁, hmax⟩ := exists_gap_maximum_principle
  obtain ⟨cB, X₂, hcB, hX₂, hgap⟩ := exists_gap_ge_above_horizon (ε := 1 / 100) (by norm_num)
  have he420 := Real.exp_pos 420
  have he421 := Real.add_one_le_exp (420 : ℝ)
  obtain ⟨X₀, hX₀def⟩ : ∃ X₀, X₀ = X₁ + X₂ := ⟨_, rfl⟩
  have hX₀1 : X₁ ≤ X₀ := by rw [hX₀def]; linarith only [hX₂, he420]
  have hX₀2 : X₂ ≤ X₀ := by rw [hX₀def]; linarith only [hX₁]
  have hX₀big : Real.exp 420 ≤ X₀ := hX₂.trans hX₀2
  have hlogX₀ : 420 ≤ Real.log (X₀ + 100) := by
    have h := Real.log_le_log he420 (show Real.exp 420 ≤ X₀ + 100 by linarith only [hX₀big])
    rwa [Real.log_exp] at h
  obtain ⟨c, hcdef⟩ : ∃ c, c = min 1 (min (1 / C) (min (1 / C ^ 2) (4 * cB ^ 2))) := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hc1 : c ≤ 1 := by rw [hcdef]; exact min_le_left _ _
  have hc2 : c ≤ 1 / C := by rw [hcdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hc3 : c ≤ 1 / C ^ 2 := by
    rw [hcdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc4 : c ≤ 4 * cB ^ 2 := by
    rw [hcdef]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨c, hcpos, X₀, min (1 / 240) (7 / 10 / Real.log (X₀ + 100)), hX₁.trans hX₀1, by
    have : 0 < Real.log (X₀ + 100) := by linarith only [hlogX₀]
    positivity, ?_⟩
  intro a t ha ha₀ hat ht hreal
  have ha240 : a ≤ 1 / 240 := ha₀.trans (min_le_left _ _)
  have halog : a * Real.log (X₀ + 100) ≤ 7 / 10 := by
    have h1 := ha₀.trans (min_le_right _ _)
    have h2 : 0 < Real.log (X₀ + 100) := by linarith only [hlogX₀]
    exact (le_div_iff₀ h2).mp h1
  have htpos : 0 < t := ha.trans_le hat
  have ht8 : t ≤ 1 / 8 := by linarith only [ht, ha240]
  -- the top of the cylinder
  obtain ⟨Xh, hXh⟩ : ∃ Xh, Xh = 2 * Real.pi * Real.exp (7 / 10 / a) := ⟨_, rfl⟩
  have hexpge : X₀ + 100 ≤ Real.exp (7 / 10 / a) := by
    rw [← Real.exp_log (show 0 < X₀ + 100 by linarith only [hX₀big, he420])]
    apply Real.exp_le_exp.mpr
    rw [le_div_iff₀ ha, mul_comm]
    exact halog
  have hpi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith only [Real.pi_gt_three]
  have hXhge : X₀ + 100 ≤ Xh := by
    rw [hXh]
    nlinarith only [hexpge, hpi, Real.exp_pos (7 / 10 / a)]
  have hXhpos : 0 < Xh := by linarith only [hXhge, hX₀big, he420]
  have hαXh : (horizontalSlope Xh).re = 7 / 10 / a / 2 := by
    rw [horizontalSlope_re, hXh]
    have h2π : 2 * Real.pi ≠ 0 := by positivity
    rw [mul_div_cancel_left₀ _ h2π, Real.log_exp]
  obtain ⟨B, hBdef⟩ : ∃ B, B = Xh + 4 := ⟨_, rfl⟩
  have hBpos : 0 < B := by rw [hBdef]; linarith only [hXhpos]
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log B := ⟨_, rfl⟩
  have hLlow : 7 / 10 / a ≤ L := by
    rw [hLdef]
    have h1 : Real.exp (7 / 10 / a) ≤ B := by
      rw [hBdef, hXh]
      nlinarith only [hpi, Real.exp_pos (7 / 10 / a)]
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at h2
  have hLup : L ≤ 7 / 10 / a + 12 := by
    rw [hLdef]
    have hB2 : B ≤ 4 * Real.pi * Real.exp (7 / 10 / a) := by
      rw [hBdef]
      have : 4 ≤ Xh := by linarith only [hXhge, hX₀big, he420, he421]
      rw [hXh] at this ⊢
      linarith only [this]
    have h1 := Real.log_le_log hBpos hB2
    rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at h1
    have h2 := Real.log_le_sub_one_of_pos (by positivity : 0 < 4 * Real.pi)
    have h3 := Real.pi_lt_d2
    linarith only [h1, h2, h3]
  have haL : a * L ≤ 3 / 4 := by
    have h1 : a * L ≤ a * (7 / 10 / a + 12) := mul_le_mul_of_nonneg_left hLup ha.le
    have h2 : a * (7 / 10 / a + 12) = 7 / 10 + 12 * a := by
      field_simp
    linarith only [h1, h2, ha240]
  have hLpos : 0 < L := lt_of_lt_of_le (by positivity) hLlow
  have htL : t * L ≤ 1 := by
    have h1 : t * L ≤ 5 / 4 * a * L := mul_le_mul_of_nonneg_right ht hLpos.le
    nlinarith only [h1, haL]
  have hLa : a ≤ 1 / L := by
    rw [le_div_iff₀ hLpos]
    linarith only [haL]
  -- the horizon applies above `Xh`
  have hor (s x x' : ℝ) (hs : s ∈ Icc a t) (hx : Xh ≤ x) (hsl : s * Real.log x ≤ 1) (hxx' : x < x')
      (h0 : riemannHeat s (x : ℂ) = 0) (h0' : riemannHeat s (x' : ℂ) = 0) :
      4 * cB ^ 2 / Real.log x ^ 2 ≤ (x' - x) ^ 2 := by
    have hs0 : 0 < s := ha.trans_le hs.1
    have hxpos : 0 < x := hXhpos.trans_le hx
    have hxge : X₂ ≤ x := by linarith only [hX₀2, hXhge, hx]
    have hlog : Real.log (Xh / (2 * Real.pi)) ≤ Real.log (x / (2 * Real.pi)) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_right hx (by positivity))
    have hαx : 7 / 10 / a / 2 ≤ (horizontalSlope x).re := by
      rw [← hαXh, horizontalSlope_re, horizontalSlope_re]
      linarith only [hlog]
    have hc : 6600 / 9991 + 1 / 100 ≤ 2 * s * (horizontalSlope x).re := by
      have h1 : 2 * a * (7 / 10 / a / 2) = 7 / 10 := by
        field_simp
      have h2 : 2 * a * (7 / 10 / a / 2) ≤ 2 * s * (horizontalSlope x).re :=
        mul_le_mul (by linarith only [hs.1]) hαx (by positivity) (by positivity)
      rw [h1] at h2
      norm_num at h2 ⊢
      linarith only [h2]
    have hg := hgap s x x' hs0 hxge hsl hc hxx' h0 h0'
    have hLx : 2 * (horizontalSlope x).re ≤ Real.log x := by
      rw [horizontalSlope_re]
      have h1 : x / (2 * Real.pi) ≤ x := div_le_self hxpos.le hpi
      have h2 := Real.log_le_log (by positivity) h1
      linarith only [h2]
    have hαpos : 0 < (horizontalSlope x).re := lt_of_lt_of_le (by positivity) hαx
    have hLxpos : 0 < Real.log x := by linarith only [hLx, hαpos]
    have hg2 : 2 * cB / Real.log x ≤ x' - x := by
      refine le_trans ?_ hg
      rw [div_le_div_iff₀ hLxpos hαpos]
      have := mul_le_mul_of_nonneg_left hLx hcB.le
      linarith only [this]
    have hsq := pow_le_pow_left₀ (by positivity) hg2 2
    refine le_trans (le_of_eq ?_) hsq
    field_simp
    norm_num
  -- the bottom of the cylinder
  have hbreal : ∀ s ∈ Icc a t, ∀ x : ℝ, x ∈ Icc X₀ (X₀ + 2 + 1) → riemannHeat s (x : ℂ) = 0 →
      deriv (riemannHeat s) (x : ℂ) ≠ 0 := fun s hs x hx h0 =>
    (hreal s hs _ h0 (by rw [Complex.ofReal_re]; exact hx.1)).2
  obtain ⟨g₀, hg₀, hg₀1, hlow⟩ := exists_low_gap (A := X₀) (A₁ := X₀ + 2) ha hbreal
  refine ⟨g₀ ^ 2, by positivity, ?_⟩
  -- the barrier
  obtain ⟨θ, hθdef⟩ : ∃ θ, θ = min (min (1 / (C * L) ^ 2) (4 * cB ^ 2 / L ^ 2)) (g₀ ^ 2) := ⟨_, rfl⟩
  have hθ1 : θ ≤ 1 / (C * L) ^ 2 := by
    rw [hθdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hθ2 : θ ≤ 4 * cB ^ 2 / L ^ 2 := by
    rw [hθdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hθ3 : θ ≤ g₀ ^ 2 := by rw [hθdef]; exact min_le_right _ _
  have hθpos : 0 < θ := by rw [hθdef]; positivity
  obtain ⟨μ, hμdef⟩ : ∃ μ, μ = min ((t - a) / (C * L)) θ := ⟨_, rfl⟩
  have hμ1 : μ ≤ (t - a) / (C * L) := by rw [hμdef]; exact min_le_left _ _
  have hμ2 : μ ≤ θ := by rw [hμdef]; exact min_le_right _ _
  have hCL : 0 < C * L := by positivity
  have hμ0 : 0 ≤ μ := by
    rw [hμdef]
    exact le_min (div_nonneg (by linarith only [hat]) hCL.le) hθpos.le
  obtain ⟨a', ha'def⟩ : ∃ a', a' = t - μ * (C * L) := ⟨_, rfl⟩
  have ha'a : a ≤ a' := by
    rw [ha'def]
    have := (le_div_iff₀ hCL).mp hμ1
    linarith only [this]
  have ha't : a' ≤ t := by
    rw [ha'def]
    have : 0 ≤ μ * (C * L) := by positivity
    linarith only [this]
  have hbar (s : ℝ) (hs : s ∈ Icc a' t) : (s - a') / (C * L) ≤ μ := by
    rw [div_le_iff₀ hCL, ha'def]
    linarith only [hs.2]
  have hIcc (s : ℝ) (hs : s ∈ Icc a' t) : s ∈ Icc a t := ⟨ha'a.trans hs.1, hs.2⟩
  have hbarrier : ∀ x x' : ℝ, x < x' → x ∈ Icc X₀ B → x' ∈ Icc X₀ B → riemannHeat t (x : ℂ) = 0 →
      riemannHeat t (x' : ℂ) = 0 → μ ≤ (x' - x) ^ 2 := by
    intro x x' h1 h2 h3 h4 h5
    have hval : 0 + (t - a') / (C * Real.log B) = μ := by
      rw [← hLdef, zero_add, ha'def, show t - (t - μ * (C * L)) = μ * (C * L) by ring,
        mul_div_cancel_right₀ _ hCL.ne']
    have hm := hmax X₀ B a' t 0 hX₀1 (ha.trans_le ha'a) ha't ht8
      (by rw [← hLdef]; exact htL) (by
        rw [hval, ← hLdef]
        exact hμ2.trans hθ1)
      (fun s hs z hz hzre => hreal s (hIcc s hs) z hz hzre.1)
      (fun x x' _ _ _ _ _ => by positivity)
      (fun s hs x x' h6 h7 h8 h9 h10 h11 => by
        rw [zero_add, ← hLdef]
        refine ((hbar s hs).trans hμ2).trans ?_
        rcases h11 with h12 | h12
        · have h13 := hlow s (hIcc s hs) x x' h6 ⟨h7.1, h12.le⟩ (by
            by_cases h14 : x' ≤ X₀ + 2 + 1
            · exact Or.inl ⟨h8.1, h14⟩
            · exact Or.inr (not_le.mp h14)) h9 h10
          exact hθ3.trans (pow_le_pow_left₀ hg₀.le h13 2)
        · by_cases h13 : 1 ≤ x' - x
          · have h14 : g₀ ^ 2 ≤ 1 := by nlinarith only [hg₀, hg₀1]
            have h15 : 1 ≤ (x' - x) ^ 2 := by nlinarith only [h13]
            linarith only [hθ3, h14, h15]
          · have h14 := not_le.mp h13
            have hxXh : Xh ≤ x := by
              rw [hBdef] at h12
              linarith only [h12, h14]
            have hxpos : 0 < x := hXhpos.trans_le hxXh
            have hlogx : Real.log x ≤ L := by
              rw [hLdef]
              exact Real.log_le_log hxpos h7.2
            have hlogx1 : 1 ≤ Real.log x := by
              have h15 : Real.exp 1 ≤ x := by
                have h16 := Real.exp_one_lt_d9
                linarith only [h16, hxXh, hXhge, hX₀big, he420, he421]
              have h17 := Real.log_le_log (Real.exp_pos 1) h15
              rwa [Real.log_exp] at h17
            have hs1 : s * Real.log x ≤ 1 := by
              have h15 : s * Real.log x ≤ t * L :=
                mul_le_mul hs.2 hlogx (by linarith only [hlogx1]) htpos.le
              exact h15.trans htL
            have h16 := hor s x x' (hIcc s hs) hxXh hs1 h6 h9 h10
            refine (hθ2.trans ?_).trans h16
            apply div_le_div_of_nonneg_left (by positivity) (by positivity)
            exact pow_le_pow_left₀ (by linarith only [hlogx1]) hlogx 2)
      t (right_mem_Icc.mpr ha't) x x' h1 h2 h3 h4 h5
    rwa [hval] at hm
  have hca : c * a ^ 2 ≤ 1 := by
    have h1 : a ^ 2 ≤ 1 := by nlinarith only [ha, ha240]
    have h2 := mul_le_mul hc1 h1 (by positivity) (by norm_num)
    linarith only [h2]
  intro x x' h1 hx hlog h0 h0'
  set W := min (min (c * a * (t - a)) (c * a ^ 2)) (g₀ ^ 2) with hW
  have hW1 : W ≤ c * a * (t - a) := (min_le_left _ _).trans (min_le_left _ _)
  have hW2 : W ≤ c * a ^ 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hW3 : W ≤ g₀ ^ 2 := min_le_right _ _
  by_cases hxh : Xh ≤ x
  · have hxpos : 0 < x := hXhpos.trans_le hxh
    have hg := hor t x x' (right_mem_Icc.mpr hat) hxh hlog h1 h0 h0'
    have hlogpos : 0 < Real.log x := by
      apply Real.log_pos
      linarith only [hxh, hXhge, hX₀big, he420, he421]
    have hlogle : a * Real.log x ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hat hlogpos.le
      linarith only [this, hlog]
    have hbound : c * a ^ 2 ≤ 4 * cB ^ 2 / Real.log x ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : (a * Real.log x) ^ 2 ≤ 1 := by
        have h3 : 0 ≤ a * Real.log x := by positivity
        nlinarith only [h3, hlogle]
      calc c * a ^ 2 * Real.log x ^ 2 = c * (a * Real.log x) ^ 2 := by ring
        _ ≤ (4 * cB ^ 2) * 1 := mul_le_mul hc4 h2 (by positivity) (by positivity)
        _ = 4 * cB ^ 2 := by ring
    exact hW2.trans (hbound.trans hg)
  · have hxh' := not_le.mp hxh
    by_cases hx'B : x' ≤ B
    · have hμW : W ≤ μ := by
        rw [hμdef, hθdef]
        refine le_min ?_ (le_min (le_min ?_ ?_) hW3)
        · refine hW1.trans ?_
          rw [le_div_iff₀ hCL]
          have h2 : c * C ≤ 1 := by
            have := (le_div_iff₀ hC).mp hc2
            exact this
          have h3 : a * L ≤ 1 := by linarith only [haL]
          have h4 : (c * C) * (a * L) ≤ 1 * 1 := mul_le_mul h2 h3 (by positivity) (by norm_num)
          have h5 : 0 ≤ t - a := by linarith only [hat]
          have h6 := mul_le_mul_of_nonneg_right h4 h5
          nlinarith only [h6]
        · refine hW2.trans ?_
          rw [le_div_iff₀ (by positivity)]
          have h2 : c * C ^ 2 ≤ 1 := (le_div_iff₀ (by positivity)).mp hc3
          have h3 : (a * L) ^ 2 ≤ 1 := by
            have h4 : 0 ≤ a * L := by positivity
            nlinarith only [h4, haL]
          have h4 := mul_le_mul h2 h3 (by positivity) (by norm_num)
          nlinarith only [h4]
        · refine hW2.trans ?_
          rw [le_div_iff₀ (by positivity)]
          have h3 : (a * L) ^ 2 ≤ 1 := by
            have h4 : 0 ≤ a * L := by positivity
            nlinarith only [h4, haL]
          have h4 := mul_le_mul hc4 h3 (by positivity) (by positivity)
          nlinarith only [h4]
      exact hμW.trans (hbarrier x x' h1 ⟨hx, by rw [hBdef]; linarith only [hxh']⟩
        ⟨by linarith only [h1, hx], hx'B⟩ h0 h0')
    · have hbig : 4 ≤ x' - x := by
        have := not_le.mp hx'B
        rw [hBdef] at this
        linarith only [this, hxh']
      have h2 : 1 ≤ (x' - x) ^ 2 := by nlinarith only [hbig]
      exact hW2.trans (hca.trans h2)

/-- **The uniform mesh above the de Bruijn–Newman constant.** For `Λ < a ≤ t ≤ 5a/4`, every pair of real zeros of `H_t` in the range `t log x ≤ 1` satisfies `(x' − x)² ≥ min(c a (t − a), c a², g₁)`. So near `Λ` the mesh opens at the rate `≍ Λ` in heat time, and away from it the mesh is `≫ t²`. -/
theorem exists_uniform_mesh_above_newman :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ a₀ : ℝ, 4096 ≤ X₀ ∧ 0 < a₀ ∧ ∀ a t : ℝ, newmanConstant < a → a ≤ a₀ → a ≤ t → t ≤ 5 / 4 * a →
      ∃ g₁ : ℝ, 0 < g₁ ∧ ∀ x x' : ℝ, x < x' → X₀ ≤ x → t * Real.log x ≤ 1 →
        riemannHeat t (x : ℂ) = 0 → riemannHeat t (x' : ℂ) = 0 →
        min (min (c * a * (t - a)) (c * a ^ 2)) g₁ ≤ (x' - x) ^ 2 := by
  obtain ⟨c, hc, X₀, a₀, hX₀, ha₀, hmesh⟩ := exists_uniform_mesh
  refine ⟨c, hc, X₀, a₀, hX₀, ha₀, ?_⟩
  intro a t hΛ haa₀ hat ht
  have ha : 0 < a := newmanConstant_nonneg.trans_lt hΛ
  refine hmesh a t ha haa₀ hat ht fun s hs z hz _ => ?_
  have hlt : newmanConstant < s := hΛ.trans_le hs.1
  have hs0 : 0 < s := ha.trans_le hs.1
  exact ⟨((mem_realRootedTimes_iff hs0.le).mpr hlt.le).2 z hz,
    deriv_riemannHeat_ne_zero_of_newmanConstant_lt hlt hz⟩

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
