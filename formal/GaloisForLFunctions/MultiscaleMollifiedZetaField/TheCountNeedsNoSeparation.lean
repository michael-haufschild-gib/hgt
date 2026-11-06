import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheDerivativeReadsTheBlaschkeFactor

/-!
# The hyperbolic count needs no separation

Isolation limits how many zeros of a depth shell can share a window. For `α ≥ 2(1 + 1/c)`, zeros of depth in `[α/L, (α+1)/L]` at heights within `2/(5cL)` have ratio `ϱ ≤ 1/4`
(`hyperbolicRatio_le_quarter`), so a family of them with Blaschke product `≥ e^{−x/8}` has at most `1 + x/8` members (`card_group_le`). A maximal separated subfamily
(`exists_maximal_separated`) therefore loses only the factor `α + 1`, and the separation condition of the hyperbolic density theorem can be dropped:

**Theorem** (`exists_card_hyperbolic_zeros_unseparated_le`, `exists_card_zeros_with_normal_derivative_unseparated_le`). Fix `0 < c ≤ 1/28800`, `x = (1−3c)α`, `α ≥ 2(1 + 1/c)`, `x ≤ (3/2)cL`.
Any zeros of depth in `[α/L, (α+1)/L]` with `T + 1 ≤ γ ≤ 2T − 1` and `Π ϱ ≥ B₀ ≥ e^{−x/8}` over the zeros deeper than `x/(2L)`, in particular any zeros with `N(ρ) ≥ B₀`, number
`≪_c (α+1)² T L e^{−2x}/B₀² + (α+1) L³ T^{1/2}`.
-/

noncomputable section

open Complex MeasureTheory Filter Set
open scoped ComplexConjugate
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

variable {v : ℝ → ℝ}

/-- A maximal separated subfamily: every member of the family lies within `r` of it. -/
theorem exists_maximal_separated {ι : Type*} [DecidableEq ι] (S : Finset ι) (g : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ S₀ ⊆ S, (∀ a ∈ S₀, ∀ b ∈ S₀, a ≠ b → r ≤ |g a - g b|) ∧ ∀ a ∈ S, ∃ b ∈ S₀, |g a - g b| < r := by
  classical
  obtain ⟨S₀, hS₀, hmax⟩ := Finset.exists_max_image
    (S.powerset.filter fun P => ∀ a ∈ P, ∀ b ∈ P, a ≠ b → r ≤ |g a - g b|) Finset.card
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _, by simp⟩⟩
  obtain ⟨hsub, hsep⟩ := Finset.mem_filter.mp hS₀
  have hsub' := Finset.mem_powerset.mp hsub
  refine ⟨S₀, hsub', hsep, fun a ha => ?_⟩
  by_contra hno
  push_neg at hno
  have haS₀ : a ∉ S₀ := fun h => by
    have := hno a h
    rw [sub_self, abs_zero] at this
    linarith
  have hins : insert a S₀ ∈ S.powerset.filter fun P => ∀ a ∈ P, ∀ b ∈ P, a ≠ b → r ≤ |g a - g b| := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.insert_subset ha hsub'), ?_⟩
    intro x hx y hy hxy
    rcases Finset.mem_insert.mp hx with hx' | hx'
    · rcases Finset.mem_insert.mp hy with hy' | hy'
      · exact absurd (hx'.trans hy'.symm) hxy
      · rw [hx']
        exact hno y hy'
    · rcases Finset.mem_insert.mp hy with hy' | hy'
      · rw [hy', abs_sub_comm]
        exact hno x hx'
      · exact hsep x hx' y hy' hxy
  have := hmax _ hins
  rw [Finset.card_insert_of_notMem haS₀] at this
  omega

/-- Zeros of one depth shell at heights within `2/(5cL)` have pseudo-hyperbolic ratio at most `1/4`, once `α ≥ 2(1 + 1/c)`. -/
theorem hyperbolicRatio_le_quarter {c L α : ℝ} (hc0 : 0 < c) (hL : 0 < L) (hα : 2 * (1 + 1 / c) ≤ α) {ρ a : ℂ}
    (h1 : α / L ≤ ρ.re - 1 / 2) (h2 : ρ.re - 1 / 2 ≤ (α + 1) / L)
    (h3 : α / L ≤ a.re - 1 / 2) (h4 : a.re - 1 / 2 ≤ (α + 1) / L)
    (hh : |ρ.im - a.im| ≤ 2 / (5 * (c * L))) : hyperbolicRatio ρ a ≤ 1 / 4 := by
  have hw : 0 < 1 / c := by positivity
  have hu : 0 < 1 / L := by positivity
  have hα0 : 0 < α := by linarith
  have e1 : α / L = α * (1 / L) := by ring
  have e2 : (α + 1) / L = α * (1 / L) + 1 / L := by ring
  have e3 : 2 / (5 * (c * L)) = 2 / 5 * (1 / c) * (1 / L) := by
    field_simp
  rw [e1] at h1 h3
  rw [e2] at h2 h4
  rw [e3] at hh
  have hre : |ρ.re - a.re| ≤ 1 / L := by
    rw [abs_le]
    constructor <;> linarith
  have hnum : ‖ρ - a‖ ≤ 1 / L + 2 / 5 * (1 / c) * (1 / L) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im]
    exact add_le_add hre hh
  have hden : 2 * (α * (1 / L)) ≤ ‖ρ + conj a - 1‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re]
    linarith
  have hd0 : 0 < 2 * (α * (1 / L)) := by positivity
  unfold hyperbolicRatio
  rw [div_le_iff₀ (lt_of_lt_of_le hd0 hden)]
  have hkey : 1 / L + 2 / 5 * (1 / c) * (1 / L) ≤ 1 / 4 * (2 * (α * (1 / L))) := by
    have h5 : (1 + 1 / c) * (1 / L) ≤ α / 2 * (1 / L) :=
      mul_le_mul_of_nonneg_right (by linarith) hu.le
    have h6 : 0 ≤ (1 / c) * (1 / L) := by positivity
    nlinarith
  linarith

/-- A family of zeros of one shell in a short window, each with Blaschke product at least `e^{−y}` over the family, has at most `1 + y` members. -/
theorem card_group_le {c L α y B₀ : ℝ} (hc0 : 0 < c) (hL : 0 < L) (hα : 2 * (1 + 1 / c) ≤ α)
    (hB₀ : Real.exp (-y) ≤ B₀) (G : Finset zetaZeroConfig.carrier) (hG : G.Nonempty)
    (hdepth : ∀ a ∈ G, α / L ≤ (a : ℂ).re - 1 / 2 ∧ (a : ℂ).re - 1 / 2 ≤ (α + 1) / L)
    (hheight : ∀ a ∈ G, ∀ b ∈ G, |(a : ℂ).im - (b : ℂ).im| ≤ 2 / (5 * (c * L)))
    (hprod : ∀ ρ ∈ G, B₀ ≤ ∏ a ∈ G.erase ρ, hyperbolicRatio (ρ : ℂ) (a : ℂ)) :
    (G.card : ℝ) ≤ 1 + y := by
  classical
  obtain ⟨ρ, hρ⟩ := hG
  have hle : ∏ a ∈ G.erase ρ, hyperbolicRatio (ρ : ℂ) (a : ℂ) ≤ ∏ _a ∈ G.erase ρ, (1 / 4 : ℝ) := by
    refine Finset.prod_le_prod (fun a _ => ?_) fun a ha => ?_
    · unfold hyperbolicRatio
      positivity
    · have ha' := (Finset.mem_erase.mp ha).2
      exact hyperbolicRatio_le_quarter hc0 hL hα (hdepth ρ hρ).1 (hdepth ρ hρ).2 (hdepth a ha').1
        (hdepth a ha').2 (hheight ρ hρ a ha')
  rw [Finset.prod_const] at hle
  obtain ⟨n, hn⟩ : ∃ n, n = (G.erase ρ).card := ⟨_, rfl⟩
  rw [← hn] at hle
  have hq : (1 / 4 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, inv_eq_one_div]
    refine one_div_le_one_div_of_le (Real.exp_pos _) ?_
    have := Real.exp_one_lt_d9
    linarith
  have hpow : (1 / 4 : ℝ) ^ n ≤ Real.exp (-(n : ℝ)) := by
    have e : Real.exp (-(n : ℝ)) = Real.exp (-1) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) hq n
  have hexp : Real.exp (-y) ≤ Real.exp (-(n : ℝ)) := hB₀.trans ((hprod ρ hρ).trans (hle.trans hpow))
  have hny : (n : ℝ) ≤ y := by
    have := Real.exp_le_exp.1 hexp
    linarith
  have hcard : G.card = n + 1 := by
    rw [hn, Finset.card_erase_of_mem hρ]
    have := Finset.card_pos.mpr ⟨ρ, hρ⟩
    omega
  rw [hcard]
  push_cast
  linarith

/-- **The hyperbolic count needs no separation.** Fix `0 < c ≤ 1/28800`, `x = (1−3c)α`, `α ≥ 2(1 + 1/c)`, `x ≤ (3/2)c log T`. Zeros of depth in `[α/L, (α+1)/L]` whose
pseudo-hyperbolic product over the zeros deeper than `x/(2L)` is at least `B₀ ≥ e^{−x/8}` number `≪_c (α+1)² T L e^{−2x}/B₀² + (α+1) L³ T^{1/2}`. -/
theorem exists_card_hyperbolic_zeros_unseparated_le (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ 1 / 28800) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α B₀ : ℝ, 2 * (1 + 1 / c) ≤ α →
      (1 - 3 * c) * α ≤ 3 / 2 * (c * Real.log T) →
      Real.exp (-((1 - 3 * c) * α / 8)) ≤ B₀ → B₀ ≤ 1 →
      ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S, α / Real.log T ≤ (ρ : ℂ).re - 1 / 2 ∧ (ρ : ℂ).re - 1 / 2 ≤ (α + 1) / Real.log T ∧
        T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧
        ∀ D : Finset zetaZeroConfig.carrier, ρ ∈ D →
          (∀ ρ' ∈ D, (1 - 3 * c) * α / 2 / Real.log T ≤ (ρ' : ℂ).re - 1 / 2) →
          B₀ ≤ ∏ ρ' ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (ρ' : ℂ)) →
      (S.card : ℝ) ≤ C * (α + 1) ^ 2 * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) / B₀ ^ 2 +
        C * ((α + 1) * (Real.log T ^ 3 * T ^ ((1 : ℝ) / 2))) := by
  classical
  obtain ⟨C, hC, hmain⟩ := exists_card_hyperbolically_isolated_zeros_unconditional_le hv hsupp hv0 hI hc0 hc
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmain, Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT hL0 α B₀ hα hxL hB₀low hB₀1 S hS
  have h13 : 0 ≤ 1 - 3 * c := by linarith
  have h131 : 1 - 3 * c ≤ 1 := by linarith
  have hw : 0 < 1 / c := by positivity
  have hα0 : 0 < α := by linarith
  have hαx : (1 - 3 * c) * α / 2 ≤ α := by nlinarith
  have hr : 0 < 1 / (5 * (c * Real.log T)) := by positivity
  obtain ⟨S₀, hS₀, hsep, hcov⟩ := exists_maximal_separated S
    (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im) hr
  have hcount := hT α B₀ hα0.le hxL hB₀low hB₀1 S₀ (fun ρ hρ => hS ρ (hS₀ hρ)) hsep
  -- the groups around the separated family
  obtain ⟨G, hGdef⟩ : ∃ G : zetaZeroConfig.carrier → Finset zetaZeroConfig.carrier, G = fun b =>
      S.filter fun a : zetaZeroConfig.carrier => |(a : ℂ).im - (b : ℂ).im| < 1 / (5 * (c * Real.log T)) :=
    ⟨_, rfl⟩
  have hGmem : ∀ b a, a ∈ G b ↔ a ∈ S ∧ |(a : ℂ).im - (b : ℂ).im| < 1 / (5 * (c * Real.log T)) := by
    intro b a
    rw [hGdef]
    exact Finset.mem_filter
  have hcover : S ⊆ S₀.biUnion G := fun a ha => by
    obtain ⟨b, hb, hab⟩ := hcov a ha
    exact Finset.mem_biUnion.mpr ⟨b, hb, (hGmem b a).2 ⟨ha, hab⟩⟩
  have hgroup : ∀ b ∈ S₀, ((G b).card : ℝ) ≤ 1 + (1 - 3 * c) * α / 8 := by
    intro b hb
    refine card_group_le (y := (1 - 3 * c) * α / 8) hc0 hL0 hα hB₀low (G b)
      ⟨b, (hGmem b b).2 ⟨hS₀ hb, by simpa using hr⟩⟩ (fun a ha => ?_) (fun a ha a' ha' => ?_)
      (fun ρ hρ => ?_)
    · obtain ⟨h1, h2, -⟩ := hS a ((hGmem b a).1 ha).1
      exact ⟨h1, h2⟩
    · have h1 := ((hGmem b a).1 ha).2
      have h2 := ((hGmem b a').1 ha').2
      have h3 : |(a : ℂ).im - (a' : ℂ).im| ≤ |(a : ℂ).im - (b : ℂ).im| + |(a' : ℂ).im - (b : ℂ).im| := by
        rw [abs_sub_comm (a' : ℂ).im]
        exact abs_sub_le _ _ _
      have e : 2 / (5 * (c * Real.log T)) =
          1 / (5 * (c * Real.log T)) + 1 / (5 * (c * Real.log T)) := by ring
      rw [e]
      linarith
    · obtain ⟨-, -, -, -, hprod⟩ := hS ρ ((hGmem b ρ).1 hρ).1
      refine hprod (G b) hρ fun ρ' hρ' => ?_
      obtain ⟨h1, -⟩ := hS ρ' ((hGmem b ρ').1 hρ').1
      refine le_trans (div_le_div_of_nonneg_right hαx hL0.le) h1
  have hcard : (S.card : ℝ) ≤ S₀.card * (1 + (1 - 3 * c) * α / 8) := by
    have h1 : S.card ≤ ∑ b ∈ S₀, (G b).card :=
      (Finset.card_le_card hcover).trans Finset.card_biUnion_le
    have h2 : (S.card : ℝ) ≤ ∑ b ∈ S₀, ((G b).card : ℝ) := by exact_mod_cast h1
    refine h2.trans ?_
    calc ∑ b ∈ S₀, ((G b).card : ℝ) ≤ ∑ _b ∈ S₀, (1 + (1 - 3 * c) * α / 8) := Finset.sum_le_sum hgroup
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hfac : 1 + (1 - 3 * c) * α / 8 ≤ α + 1 := by nlinarith
  have hS₀0 : (0 : ℝ) ≤ S₀.card := Nat.cast_nonneg _
  calc (S.card : ℝ) ≤ S₀.card * (α + 1) := hcard.trans (mul_le_mul_of_nonneg_left hfac hS₀0)
    _ ≤ (C * (α + 1) * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) / B₀ ^ 2 +
          C * (Real.log T ^ 3 * T ^ ((1 : ℝ) / 2))) * (α + 1) :=
        mul_le_mul_of_nonneg_right hcount (by linarith)
    _ = _ := by ring

/-- **Zeros with a normal derivative, without separation.** Under the conditions of `exists_card_hyperbolic_zeros_unseparated_le`, zeros with `N(ρ) ≥ B₀` number
`≪_c (α+1)² T L e^{−2x}/B₀² + (α+1) L³ T^{1/2}`. -/
theorem exists_card_zeros_with_normal_derivative_unseparated_le (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ 1 / 28800) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α B₀ : ℝ, 2 * (1 + 1 / c) ≤ α →
      (1 - 3 * c) * α ≤ 3 / 2 * (c * Real.log T) →
      Real.exp (-((1 - 3 * c) * α / 8)) ≤ B₀ → B₀ ≤ 1 →
      ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S, α / Real.log T ≤ (ρ : ℂ).re - 1 / 2 ∧ (ρ : ℂ).re - 1 / 2 ≤ (α + 1) / Real.log T ∧
        T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧ B₀ ≤ normalDerivative (ρ : ℂ)) →
      (S.card : ℝ) ≤ C * (α + 1) ^ 2 * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) / B₀ ^ 2 +
        C * ((α + 1) * (Real.log T ^ 3 * T ^ ((1 : ℝ) / 2))) := by
  obtain ⟨C, hC, hmain⟩ := exists_card_hyperbolic_zeros_unseparated_le hv hsupp hv0 hI hc0 hc
  refine ⟨C, hC, ?_⟩
  filter_upwards [hmain, Real.tendsto_log_atTop.eventually_gt_atTop 0] with T hT hL0 α B₀ hα hxL hB₀low hB₀1 S hS
  have hw : 0 < 1 / c := by positivity
  have hα0 : 0 < α := by linarith
  have h13 : 0 ≤ 1 - 3 * c := by linarith
  refine hT α B₀ hα hxL hB₀low hB₀1 S fun ρ hρ => ?_
  obtain ⟨h1, h2, h3, h4, h5⟩ := hS ρ hρ
  refine ⟨h1, h2, h3, h4, fun D hρD hD => ?_⟩
  have hb0 : 0 < α / Real.log T := by positivity
  have hre : 1 / 2 < (ρ : ℂ).re := by linarith
  refine h5.trans (normalDerivative_le_prod_carrier ρ hre D fun a ha => ?_)
  have h6 : 0 ≤ (1 - 3 * c) * α / 2 / Real.log T := by positivity
  have h7 := hD a ha
  linarith

end GaloisForLFunctions.MultiscaleMollifiedZetaField
