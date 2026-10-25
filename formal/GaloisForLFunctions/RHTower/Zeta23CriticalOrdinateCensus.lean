import GaloisForLFunctions.RHTower.Zeta23OffLineMultipleExclusionMontgomeryTaylor
import GaloisForLFunctions.RHTower.ZetaOffLineMomentMontgomeryTaylor

/-!
# Four fifths of the zero ordinates of `ζ` carry a critical zero

An *ordinate* of the window `(T₁, T₂]` is a height `γ` at which some nontrivial zero lies.  A
critical ordinate carries a zero on the critical line.  Every non-critical ordinate carries an
off-line zero and its reflection `1 − ρ̄`, so it absorbs at least two zero copies of `N − N₀`:

`2·#ordinates ≤ 2·#critical ordinates + (N − N₀)`        (`two_mul_card_ordinates_le`).

Distinct critical zeros have distinct ordinates, so `#critical ordinates ≥ N₀ˢ`.  With the
two-thirds theorem `N₀ˢ ≥ (2/3 − ε)N`, unconditionally, for all large `T`,

`#critical ordinates in (T, 2T] ≥ (4/5 − ε)·#ordinates in (T, 2T]`   (`four_fifths_critical_ordinates`).

At the Montgomery–Taylor constant the proportion is `2HD(1)/(1 + HD(1)) = 0.8042…`
(`critical_ordinates_montgomeryTaylor`).  For zero copies the same certificate gives only `HD(1)`:
three quarters of the copies is the statement in which each off-line ordinate is charged twice.
-/

open Finset Filter

noncomputable section

namespace RHTower

open Zeta23

section Window

variable (Z : ZeroConfig)

/-- The ordinates of the zeros in the window `(T₁, T₂]`. -/
def zeroOrdinates (T₁ T₂ : ℝ) : Finset ℝ := (zeroWindowFinset Z T₁ T₂).image Complex.im

/-- The ordinates carrying a zero on the critical line. -/
def criticalOrdinates (T₁ T₂ : ℝ) : Finset ℝ :=
  ((zeroWindowFinset Z T₁ T₂).filter (fun ρ => ρ.re = 1 / 2)).image Complex.im

/-- Critical zeros are determined by their ordinates. -/
theorem card_criticalOrdinates (T₁ T₂ : ℝ) :
    (criticalOrdinates Z T₁ T₂).card =
      ((zeroWindowFinset Z T₁ T₂).filter (fun ρ => ρ.re = 1 / 2)).card := by
  refine Finset.card_image_of_injOn fun ρ hρ ρ' hρ' him => ?_
  simp only [Finset.coe_filter, Set.mem_setOf_eq] at hρ hρ'
  exact Complex.ext (hρ.2.trans hρ'.2.symm) him

/-- Each simple critical zero contributes its own critical ordinate. -/
theorem N0s_le_card_criticalOrdinates (T₁ T₂ : ℝ) :
    Z.N0s T₁ T₂ ≤ (criticalOrdinates Z T₁ T₂).card := by
  rw [card_criticalOrdinates, N0s_eq_card_zeroWindowFinset]
  exact Finset.card_le_card fun ρ hρ => by
    simp only [Finset.mem_filter] at hρ ⊢
    exact ⟨hρ.1, hρ.2.1⟩

/-- **Ordinate census**: every non-critical ordinate absorbs at least two off-line zero copies. -/
theorem two_mul_card_ordinates_le (T₁ T₂ : ℝ) :
    2 * (zeroOrdinates Z T₁ T₂).card + Z.N0 T₁ T₂ ≤
      2 * (criticalOrdinates Z T₁ T₂).card + Z.N T₁ T₂ := by
  classical
  set W := zeroWindowFinset Z T₁ T₂
  have hreflW : ∀ ρ ∈ W, reflect ρ ∈ W := by
    intro ρ hρ
    rw [mem_zeroWindowFinset] at hρ ⊢
    refine ⟨Z.reflect_mem ρ hρ.1, ?_⟩
    have him : (reflect ρ).im = ρ.im := by simp [reflect]
    rw [Set.mem_setOf_eq, him]
    exact hρ.2
  have hre : ∀ ρ : ℂ, (reflect ρ).re = 1 - ρ.re := fun ρ => by simp [reflect]
  have him : ∀ ρ : ℂ, (reflect ρ).im = ρ.im := fun ρ => by simp [reflect]
  have hinv : ∀ ρ : ℂ, reflect (reflect ρ) = ρ := fun ρ => by simp [reflect]
  set R := W.filter (fun ρ => 1 / 2 < ρ.re)
  -- every ordinate is critical or carries a zero right of the line
  have hcover : zeroOrdinates Z T₁ T₂ ⊆ criticalOrdinates Z T₁ T₂ ∪ R.image Complex.im := by
    intro γ hγ
    obtain ⟨ρ, hρW, rfl⟩ := Finset.mem_image.mp hγ
    rcases lt_trichotomy ρ.re (1 / 2) with h | h | h
    · refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨reflect ρ, ?_, him ρ⟩)
      exact Finset.mem_filter.mpr ⟨hreflW ρ hρW, by rw [hre]; linarith⟩
    · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hρW, h⟩, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨ρ, Finset.mem_filter.mpr ⟨hρW, h⟩, rfl⟩)
  have hcard : (zeroOrdinates Z T₁ T₂).card ≤ (criticalOrdinates Z T₁ T₂).card + R.card :=
    (Finset.card_le_card hcover).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left Finset.card_image_le _))
  have hRmult : R.card ≤ ∑ ρ ∈ R, Z.mult ρ := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun ρ hρ =>
      Z.one_le_mult ρ ((mem_zeroWindowFinset Z).mp (Finset.mem_filter.mp hρ).1).1
  -- the reflection carries the zeros left of the line onto those right of it
  have hrefl : ∑ ρ ∈ W.filter (fun ρ => ρ.re < 1 / 2), Z.mult ρ = ∑ ρ ∈ R, Z.mult ρ := by
    refine Finset.sum_nbij' reflect reflect ?_ ?_ ?_ ?_ ?_
    · intro ρ hρ
      simp only [R, Finset.mem_filter] at hρ ⊢
      exact ⟨hreflW ρ hρ.1, by rw [hre]; linarith [hρ.2]⟩
    · intro ρ hρ
      simp only [R, Finset.mem_filter] at hρ ⊢
      exact ⟨hreflW ρ hρ.1, by rw [hre]; linarith [hρ.2]⟩
    · intro ρ _; exact hinv ρ
    · intro ρ _; exact hinv ρ
    · intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      rw [Z.mult_reflect ρ ((mem_zeroWindowFinset Z).mp hρ.1).1]
  -- `N − N₀` is the off-line mass, twice the right half
  have hoff : Z.N T₁ T₂ = Z.N0 T₁ T₂ + (∑ ρ ∈ W.filter (fun ρ => ρ.re < 1 / 2), Z.mult ρ) +
      ∑ ρ ∈ R, Z.mult ρ := by
    rw [N_eq_sum_zeroWindowFinset, N0_eq_sum_zeroWindowFinset,
      ← Finset.sum_filter_add_sum_filter_not W (fun ρ => ρ.re = 1 / 2),
      ← Finset.sum_filter_add_sum_filter_not (W.filter fun ρ => ¬ρ.re = 1 / 2)
        (fun ρ => ρ.re < 1 / 2), Finset.filter_filter, Finset.filter_filter, add_assoc]
    congr 2
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext ρ
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hW, -, h⟩; exact ⟨hW, h⟩
      · rintro ⟨hW, h⟩; exact ⟨hW, by linarith, h⟩
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext ρ
      simp only [Finset.mem_filter, R]
      constructor
      · rintro ⟨hW, h1, h2⟩
        exact ⟨hW, lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)⟩
      · rintro ⟨hW, h⟩; exact ⟨hW, by linarith, by linarith⟩
  omega

end Window

/-! ## ζ -/

/-- **Four fifths of the zero ordinates carry a critical zero**, unconditional: for every `ε > 0`
and all large `T`, at least a proportion `4/5 − ε` of the heights `γ ∈ (T, 2T]` at which `ζ`
vanishes in the critical strip carry a zero of `ζ` on the critical line. -/
theorem four_fifths_critical_ordinates :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 / 5 - ε) * ((zeroOrdinates zetaZeroConfig T (2 * T)).card : ℝ) ≤
        (criticalOrdinates zetaZeroConfig T (2 * T)).card := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := two_thirds_add_offLineMultipleMass_le_N0simple (ε / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  have hcensus := two_mul_card_ordinates_le zetaZeroConfig T (2 * T)
  have hs := N0s_le_card_criticalOrdinates zetaZeroConfig T (2 * T)
  have hsN0 := N0s_le_N0 zetaZeroConfig T (2 * T)
  rw [zetaZeroConfig_N] at hcensus
  rw [zetaZeroConfig_N0s] at hs hsN0
  have hcensus' : 2 * ((zeroOrdinates zetaZeroConfig T (2 * T)).card : ℝ)
      + (zetaZeroConfig.N0 T (2 * T) : ℝ)
      ≤ 2 * ((criticalOrdinates zetaZeroConfig T (2 * T)).card : ℝ) + (Ncount T (2 * T) : ℝ) := by
    exact_mod_cast hcensus
  have hs' : (N0simple T (2 * T) : ℝ) ≤ (criticalOrdinates zetaZeroConfig T (2 * T)).card := by
    exact_mod_cast hs
  have hsN0' : (N0simple T (2 * T) : ℝ) ≤ zetaZeroConfig.N0 T (2 * T) := by exact_mod_cast hsN0
  set o : ℝ := ((zeroOrdinates zetaZeroConfig T (2 * T)).card : ℝ)
  set c : ℝ := ((criticalOrdinates zetaZeroConfig T (2 * T)).card : ℝ)
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have ho : 0 ≤ o := Nat.cast_nonneg _
  by_cases hεbig : 4 / 5 ≤ ε
  · nlinarith
  have h23 := hT₀ T hT
  have hM : (0 : ℝ) ≤ offLineMultipleMass zetaZeroConfig T (2 * T) := Nat.cast_nonneg _
  -- with `h = 2/3 − ε/2`: `2h·o ≤ (1 + h)·c`
  set h : ℝ := 2 / 3 - ε / 2 with hdef
  have hh : 0 < h := by rw [hdef]; linarith
  have hhN : h * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by linarith
  have hkey : 2 * h * o ≤ (1 + h) * c := by
    nlinarith [mul_le_mul_of_nonneg_left hcensus' hh.le, mul_le_mul_of_nonneg_left hs' hh.le]
  have hcoef : (4 / 5 - ε) * (1 + h) ≤ 2 * h := by rw [hdef]; nlinarith
  have h1h : 0 < 1 + h := by linarith
  have : (4 / 5 - ε) * o * (1 + h) ≤ c * (1 + h) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoef ho]
  exact le_of_mul_le_mul_right this h1h

/-- `HD(1) ≤ 1`: from `HD(1) = 3/2 − s cot s` at `s = 1/√2`, `sin s ≤ s` and `cos s ≥ 1 − s²/2`. -/
theorem HD_one_le_one : Zeta23.ThmD.HD 1 ≤ 1 := by
  rw [Zeta23.ThmD.HD_one]
  set s : ℝ := (Real.sqrt 2)⁻¹ with hs
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < s := inv_pos.mpr hsqrt0
  have hs2 : s ^ 2 = 1 / 2 := by rw [hs, inv_pow, hsq, one_div]
  have hsin : Real.sin s ≤ s := Real.sin_le hs0.le
  have hsinpos : 0 < Real.sin s := by
    have := Zeta23.ThmD.sin_theta_pos one_pos le_rfl
    rwa [Zeta23.ThmD.theta_one] at this
  have hcos : 1 - s ^ 2 / 2 ≤ Real.cos s := Real.one_sub_sq_div_two_le_cos
  rw [mul_div_assoc', sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hsinpos]
  nlinarith

/-- **Critical ordinates at the Montgomery–Taylor constant**: for every `ε > 0` and all large `T`, at
least `2HD(1)/(1 + HD(1)) − ε = 0.8042…` of the zero ordinates in `(T, 2T]` carry a critical zero. -/
theorem critical_ordinates_montgomeryTaylor :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (2 * Zeta23.ThmD.HD 1 / (1 + Zeta23.ThmD.HD 1) - ε)
          * ((zeroOrdinates zetaZeroConfig T (2 * T)).card : ℝ) ≤
        (criticalOrdinates zetaZeroConfig T (2 * T)).card := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := HD_one_add_offLineMultipleMass_le_N0simple (ε / 2) (by linarith)
  refine ⟨T₀, fun T hT => ?_⟩
  set H := Zeta23.ThmD.HD 1 with hHdef
  have hH := HD_one_ge
  rw [← hHdef] at hH
  have hcensus := two_mul_card_ordinates_le zetaZeroConfig T (2 * T)
  have hs := N0s_le_card_criticalOrdinates zetaZeroConfig T (2 * T)
  rw [zetaZeroConfig_N] at hcensus
  rw [zetaZeroConfig_N0s] at hs
  have hcensus' : 2 * ((zeroOrdinates zetaZeroConfig T (2 * T)).card : ℝ)
      + (zetaZeroConfig.N0 T (2 * T) : ℝ)
      ≤ 2 * ((criticalOrdinates zetaZeroConfig T (2 * T)).card : ℝ) + (Ncount T (2 * T) : ℝ) := by
    exact_mod_cast hcensus
  have hs' : (N0simple T (2 * T) : ℝ) ≤ (criticalOrdinates zetaZeroConfig T (2 * T)).card := by
    exact_mod_cast hs
  have hsN0' : (N0simple T (2 * T) : ℝ) ≤ zetaZeroConfig.N0 T (2 * T) := by
    have := N0s_le_N0 zetaZeroConfig T (2 * T)
    rw [zetaZeroConfig_N0s] at this
    exact_mod_cast this
  have hMT := hT₀ T hT
  have hM : (0 : ℝ) ≤ offLineMultipleMass zetaZeroConfig T (2 * T) := Nat.cast_nonneg _
  set o : ℝ := ((zeroOrdinates zetaZeroConfig T (2 * T)).card : ℝ)
  set c : ℝ := ((criticalOrdinates zetaZeroConfig T (2 * T)).card : ℝ)
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have ho : 0 ≤ o := Nat.cast_nonneg _
  set q := 2 * H / (1 + H) with hq
  have hq1 : q * (1 + H) = 2 * H := by rw [hq]; field_simp
  by_cases hneg : q - ε ≤ 0
  · nlinarith
  -- with `h = HD(1) − ε/2`: `2h·o ≤ (1 + h)·c`
  set h : ℝ := H - ε / 2 with hdef
  have hhN : h * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T) := by linarith
  have hεq : ε < q := by linarith
  have hqpos : 0 ≤ q := by rw [hq]; exact div_nonneg (by linarith) (by linarith)
  have hq0 : q ≤ 2 * H := by nlinarith [hq1, hqpos, hH]
  have hh : 0 < h := by rw [hdef]; nlinarith
  have hh1 : 0 ≤ 1 - h := by rw [hdef]; nlinarith [HD_one_le_one]
  have hkey : 2 * h * o ≤ (1 + h) * c := by
    nlinarith [mul_le_mul_of_nonneg_left hcensus' hh.le, mul_le_mul_of_nonneg_left hsN0' hh.le,
      mul_le_mul_of_nonneg_left hs' hh1]
  have hcoef : (q - ε) * (1 + h) ≤ 2 * h := by rw [hdef]; nlinarith
  have h1h : 0 < 1 + h := by linarith
  have : (q - ε) * o * (1 + h) ≤ c * (1 + h) := by
    nlinarith [mul_le_mul_of_nonneg_right hcoef ho]
  exact le_of_mul_le_mul_right this h1h

/-! ## Cumulative form over `(0, T]` -/

/-- Adjacent windows partition the zero finset. -/
lemma zeroWindowFinset_union (Z : ZeroConfig) {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    zeroWindowFinset Z a d = zeroWindowFinset Z a b ∪ zeroWindowFinset Z b d := by
  ext ρ
  simp only [Finset.mem_union, mem_zeroWindowFinset, Zeta23.Assembly.window_union Z hab hbd,
    Set.mem_union]

/-- Ordinates of adjacent windows are disjoint. -/
lemma disjoint_image_im_window (Z : ZeroConfig) {a b d : ℝ} (s t : Finset ℂ)
    (hs : s ⊆ zeroWindowFinset Z a b) (ht : t ⊆ zeroWindowFinset Z b d) :
    Disjoint (s.image Complex.im) (t.image Complex.im) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨ρ', hρ', hρρ'⟩ := Finset.mem_image.mp hx'
  have h1 := ((mem_zeroWindowFinset Z).mp (hs hρ)).2
  have h2 := ((mem_zeroWindowFinset Z).mp (ht hρ')).2
  simp only [Set.mem_setOf_eq] at h1 h2
  linarith [h1.2, h2.1, hρρ']

theorem card_zeroOrdinates_add (Z : ZeroConfig) {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    (zeroOrdinates Z a d).card = (zeroOrdinates Z a b).card + (zeroOrdinates Z b d).card := by
  classical
  unfold zeroOrdinates
  rw [zeroWindowFinset_union Z hab hbd, Finset.image_union,
    Finset.card_union_of_disjoint (disjoint_image_im_window Z _ _ subset_rfl subset_rfl)]

theorem card_criticalOrdinates_add (Z : ZeroConfig) {a b d : ℝ} (hab : a ≤ b) (hbd : b ≤ d) :
    (criticalOrdinates Z a d).card =
      (criticalOrdinates Z a b).card + (criticalOrdinates Z b d).card := by
  classical
  unfold criticalOrdinates
  rw [zeroWindowFinset_union Z hab hbd, Finset.filter_union, Finset.image_union,
    Finset.card_union_of_disjoint (disjoint_image_im_window Z _ _ (Finset.filter_subset _ _)
      (Finset.filter_subset _ _))]

/-- **Cumulative ordinate census**: at least `4/5 − ε` of the zero ordinates in `(0, T]` carry a
critical zero, for all large `T`. -/
theorem four_fifths_critical_ordinates_cumulative :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      (4 / 5 - ε) * ((zeroOrdinates zetaZeroConfig 0 T).card : ℝ) ≤
        (criticalOrdinates zetaZeroConfig 0 T).card := by
  -- the ordinate count tends to infinity: it dominates `N₀ˢ(0, T) ≥ (HD(1) − ½)N(0, T)`
  have htop : Tendsto (fun T => ((zeroOrdinates zetaZeroConfig 0 T).card : ℝ)) atTop atTop := by
    obtain ⟨T₀, hT₀⟩ := HD_one_add_offLineMultipleMass_le_N0simple_cumulative (1 / 10) (by norm_num)
    have hN := tendsto_Ncount_zero_atTop zetaSeam paperInputs_zeta.RvM
    have hH := HD_one_ge
    refine tendsto_atTop_mono' atTop ?_ (hN.const_mul_atTop (show (0 : ℝ) < 1 / 2 by norm_num))
    filter_upwards [eventually_ge_atTop T₀] with T hT
    have h := hT₀ T hT
    have hs := N0s_le_card_criticalOrdinates zetaZeroConfig 0 T
    rw [zetaZeroConfig_N0s] at hs
    have hco : (criticalOrdinates zetaZeroConfig 0 T).card ≤ (zeroOrdinates zetaZeroConfig 0 T).card :=
      Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))
    have hM : (0 : ℝ) ≤ offLineMultipleMass zetaZeroConfig 0 T := Nat.cast_nonneg _
    have hN0 : (0 : ℝ) ≤ Ncount 0 T := Nat.cast_nonneg _
    have hs' : (N0simple 0 T : ℝ) ≤ (criticalOrdinates zetaZeroConfig 0 T).card := by exact_mod_cast hs
    have hco' : ((criticalOrdinates zetaZeroConfig 0 T).card : ℝ) ≤
        (zeroOrdinates zetaZeroConfig 0 T).card := by exact_mod_cast hco
    nlinarith
  exact Zeta23.Assembly.dyadic
    (f := fun a b => ((criticalOrdinates zetaZeroConfig a b).card : ℝ))
    (g := fun a b => ((zeroOrdinates zetaZeroConfig a b).card : ℝ))
    (fun a b d hab hbd => by rw [card_criticalOrdinates_add zetaZeroConfig hab hbd]; push_cast; ring)
    (fun a b d hab hbd => by rw [card_zeroOrdinates_add zetaZeroConfig hab hbd]; push_cast; ring)
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _) htop
    four_fifths_critical_ordinates

end RHTower

end
