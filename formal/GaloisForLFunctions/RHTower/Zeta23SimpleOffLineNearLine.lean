import GaloisForLFunctions.RHTower.Zeta23OffLineMultipleExclusionMontgomeryTaylor
import GaloisForLFunctions.RHTower.ZetaDyadicWindowMomentTwoThirds

/-!
# The simple off-line core of three quarters lies within `O(1/log T)` of the critical line

`RHTower.three_quarters_or_simple_offLine_HD_one` shows that if fewer than three quarters of the zero
copies in `(T, 2T]` lie on the critical line, at least `(HD(1) − 1/2 − ε)N` of them are simple
off-line zeros.  The off-line moment `Σ m_ρ (Re ρ − ½)⁺ ≤ (67/1000)T` on dyadic windows
(`eventually_dyadicWindowTail_le_sixtySeven_thousandths`) and the reflection `ρ ↦ 1 − ρ̄` bound the
off-line zero copies at displacement `> A/log T` by `N/A`.  Hence, unconditionally,

either `N₀(T,2T) ≥ (3/4)N(T,2T)`, or at least `(HD(1) − 1/2 − 1/A − ε)N(T,2T)` simple off-line zeros
lie within `A/log T` of the critical line.
-/

open Filter Topology Real Finset Asymptotics

noncomputable section

namespace RHTower

open Zeta23

/-! ## Displacement-graded off-line counts -/

section Window

variable (Z : ZeroConfig)

/-- The right off-line moment `Σ_{Re ρ > ½} m_ρ (Re ρ − ½)` of the window. -/
def offLineRightMoment (T₁ T₂ : ℝ) : ℝ :=
  ∑ ρ ∈ (zeroWindowFinset Z T₁ T₂).filter (fun ρ => 1 / 2 < ρ.re), (Z.mult ρ : ℝ) * (ρ.re - 1 / 2)

/-- Zero copies of the window at displacement `|Re ρ − ½| > d`. -/
def offLineFarMass (d T₁ T₂ : ℝ) : ℕ :=
  ∑ ρ ∈ (zeroWindowFinset Z T₁ T₂).filter (fun ρ => d < |ρ.re - 1 / 2|), Z.mult ρ

/-- Zero copies of the window within displacement `d` of the critical line. -/
def nearLineMass (d T₁ T₂ : ℝ) : ℕ :=
  ∑ ρ ∈ (zeroWindowFinset Z T₁ T₂).filter (fun ρ => |ρ.re - 1 / 2| ≤ d), Z.mult ρ

/-- Every zero copy is near the line or far from it. -/
theorem N_eq_nearLineMass_add_offLineFarMass (d T₁ T₂ : ℝ) :
    Z.N T₁ T₂ = nearLineMass Z d T₁ T₂ + offLineFarMass Z d T₁ T₂ := by
  classical
  rw [N_eq_sum_zeroWindowFinset, nearLineMass, offLineFarMass,
    ← Finset.sum_filter_add_sum_filter_not (zeroWindowFinset Z T₁ T₂)
      (fun ρ => |ρ.re - 1 / 2| ≤ d)]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext ρ
  simp only [Finset.mem_filter, not_le]

/-- Simple off-line zeros of the window within displacement `d` of the critical line. -/
def offLineSimpleNear (d T₁ T₂ : ℝ) : ℕ :=
  ((zeroWindowFinset Z T₁ T₂).filter
    (fun ρ => ρ.re ≠ 1 / 2 ∧ |ρ.re - 1 / 2| ≤ d ∧ Z.mult ρ = 1)).card

/-- Simple off-line zeros are near the line or carried by the far mass. -/
theorem offLineSimpleCount_le_near_add_far (d T₁ T₂ : ℝ) :
    offLineSimpleCount Z T₁ T₂ ≤ offLineSimpleNear Z d T₁ T₂ + offLineFarMass Z d T₁ T₂ := by
  classical
  unfold offLineSimpleCount offLineSimpleNear offLineFarMass
  set W := zeroWindowFinset Z T₁ T₂
  have h1 : (W.filter (fun ρ => ρ.re ≠ 1 / 2 ∧ Z.mult ρ = 1)).card ≤
      (W.filter (fun ρ => ρ.re ≠ 1 / 2 ∧ |ρ.re - 1 / 2| ≤ d ∧ Z.mult ρ = 1)).card +
        (W.filter (fun ρ => d < |ρ.re - 1 / 2|)).card := by
    calc (W.filter (fun ρ => ρ.re ≠ 1 / 2 ∧ Z.mult ρ = 1)).card
        ≤ ((W.filter (fun ρ => ρ.re ≠ 1 / 2 ∧ |ρ.re - 1 / 2| ≤ d ∧ Z.mult ρ = 1)) ∪
            (W.filter (fun ρ => d < |ρ.re - 1 / 2|))).card := by
          apply Finset.card_le_card
          intro ρ hρ
          simp only [Finset.mem_filter, Finset.mem_union] at hρ ⊢
          by_cases h : |ρ.re - 1 / 2| ≤ d
          · exact Or.inl ⟨hρ.1, hρ.2.1, h, hρ.2.2⟩
          · exact Or.inr ⟨hρ.1, lt_of_not_ge h⟩
      _ ≤ _ := Finset.card_union_le _ _
  have h2 : (W.filter (fun ρ => d < |ρ.re - 1 / 2|)).card ≤
      ∑ ρ ∈ W.filter (fun ρ => d < |ρ.re - 1 / 2|), Z.mult ρ := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun ρ hρ => ?_
    exact Z.one_le_mult ρ ((mem_zeroWindowFinset Z).mp (Finset.mem_filter.mp hρ).1).1
  omega

/-- **Reflection bound**: zero copies at displacement `> d` are at most `2/d` times the right
off-line moment, since `ρ ↦ 1 − ρ̄` maps the far-left zeros onto the far-right ones. -/
theorem offLineFarMass_le (d T₁ T₂ : ℝ) (hd : 0 < d) :
    (offLineFarMass Z d T₁ T₂ : ℝ) ≤ 2 * offLineRightMoment Z T₁ T₂ / d := by
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
  have hinv : ∀ ρ : ℂ, reflect (reflect ρ) = ρ := fun ρ => by simp [reflect]
  -- split the far mass into its right and left halves
  have hsplit : (offLineFarMass Z d T₁ T₂ : ℝ) =
      (∑ ρ ∈ W.filter (fun ρ => 1 / 2 + d < ρ.re), (Z.mult ρ : ℝ)) +
        ∑ ρ ∈ W.filter (fun ρ => ρ.re < 1 / 2 - d), (Z.mult ρ : ℝ) := by
    unfold offLineFarMass
    push_cast
    rw [← Finset.sum_union]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext ρ
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hW, h⟩
        rcases lt_abs.mp h with h | h
        · exact Or.inl ⟨hW, by linarith⟩
        · exact Or.inr ⟨hW, by linarith⟩
      · rintro (⟨hW, h⟩ | ⟨hW, h⟩)
        · exact ⟨hW, lt_abs.mpr (Or.inl (by linarith))⟩
        · exact ⟨hW, lt_abs.mpr (Or.inr (by linarith))⟩
    · rw [Finset.disjoint_left]
      intro ρ h1 h2
      simp only [Finset.mem_filter] at h1 h2
      linarith [h1.2, h2.2]
  -- the reflection carries the far-left half onto the far-right half
  have hrefl : ∑ ρ ∈ W.filter (fun ρ => ρ.re < 1 / 2 - d), (Z.mult ρ : ℝ) =
      ∑ ρ ∈ W.filter (fun ρ => 1 / 2 + d < ρ.re), (Z.mult ρ : ℝ) := by
    refine Finset.sum_nbij' reflect reflect ?_ ?_ ?_ ?_ ?_
    · intro ρ hρ
      simp only [Finset.mem_filter] at hρ ⊢
      exact ⟨hreflW ρ hρ.1, by rw [hre]; linarith [hρ.2]⟩
    · intro ρ hρ
      simp only [Finset.mem_filter] at hρ ⊢
      exact ⟨hreflW ρ hρ.1, by rw [hre]; linarith [hρ.2]⟩
    · intro ρ _; exact hinv ρ
    · intro ρ _; exact hinv ρ
    · intro ρ hρ
      simp only [Finset.mem_filter] at hρ
      have hc := ((mem_zeroWindowFinset Z).mp hρ.1).1
      rw [Z.mult_reflect ρ hc]
  -- the far-right half is bounded by the moment
  have hright : ∑ ρ ∈ W.filter (fun ρ => 1 / 2 + d < ρ.re), (Z.mult ρ : ℝ) ≤
      offLineRightMoment Z T₁ T₂ / d := by
    rw [le_div_iff₀ hd, Finset.sum_mul]
    unfold offLineRightMoment
    calc ∑ ρ ∈ W.filter (fun ρ => 1 / 2 + d < ρ.re), (Z.mult ρ : ℝ) * d
        ≤ ∑ ρ ∈ W.filter (fun ρ => 1 / 2 + d < ρ.re), (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          have h := (Finset.mem_filter.mp hρ).2
          exact mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
      _ ≤ ∑ ρ ∈ W.filter (fun ρ => 1 / 2 < ρ.re), (Z.mult ρ : ℝ) * (ρ.re - 1 / 2) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ρ hρ _ => ?_
          · intro ρ hρ
            simp only [Finset.mem_filter] at hρ ⊢
            exact ⟨hρ.1, by linarith [hρ.2]⟩
          · have h := (Finset.mem_filter.mp hρ).2
            exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  rw [hsplit, hrefl]
  have : 2 * offLineRightMoment Z T₁ T₂ / d = 2 * (offLineRightMoment Z T₁ T₂ / d) := by ring
  rw [this]
  linarith

end Window

/-! ## ζ: the dyadic off-line moment in Zeta23 coordinates -/

section Zeta

/-- The Zeta23 window of `ζ` is the completed-Xi window. -/
lemma zeroWindowFinset_zeta_eq {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) :
    zeroWindowFinset zetaZeroConfig T₁ T₂ = stripFinsetPos T₂ \ stripFinsetPos T₁ := by
  rw [← zeta23_zerosIn_toFinset_eq_window hT₁]
  ext ρ
  rw [mem_zeroWindowFinset, Set.Finite.mem_toFinset]
  exact Iff.of_eq (congrArg (ρ ∈ ·) (zetaZeros_window zetaSeam T₁ T₂))

/-- The right off-line moment of `ζ` is the corpus window tail at displacement `0`. -/
theorem zeta_offLineRightMoment_eq_windowTail {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT : T₁ ≤ T₂) :
    offLineRightMoment zetaZeroConfig T₁ T₂ = windowTail 0 T₁ T₂ := by
  classical
  rw [windowTail_eq_sum hT, offLineRightMoment, zeroWindowFinset_zeta_eq hT₁, Finset.sum_filter]
  refine Finset.sum_congr rfl fun z hz => ?_
  have hstrip := (Finset.mem_sdiff.mp hz).1
  have horder := xi_analyticOrderAt_eq_riemannZeta_of_mem_strip
    ⟨(mem_stripFinsetPos.mp hstrip).1, (mem_stripFinsetPos.mp hstrip).2.1⟩
  have hm : (zetaZeroConfig.mult z : ℝ) = ((analyticOrderAt xi z).toNat : ℝ) := by
    rw [zetaZeroConfig_mult, horder]; rfl
  rw [hm]
  split_ifs with h
  · rw [max_eq_left (by linarith)]; ring
  · rw [max_eq_right (by linarith)]; ring

/-- A window tail at displacement `0` is at most half the zero copies of its window. -/
theorem windowTail_zero_le_half_Ncount {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    windowTail 0 a b ≤ 1 / 2 * (Ncount a b : ℝ) := by
  rw [windowTail_eq_sum hab, zeta23_Ncount_window_eq ha, Finset.mul_sum]
  refine Finset.sum_le_sum fun z hz => ?_
  have hstrip := (Finset.mem_sdiff.mp hz).1
  have hre1 := (mem_stripFinsetPos.mp hstrip).2.1
  have hm : (0 : ℝ) ≤ ((analyticOrderAt xi z).toNat : ℝ) := Nat.cast_nonneg _
  have hmax : max (z.re - 1 / 2 - 0) 0 ≤ 1 / 2 := max_le (by linarith) (by norm_num)
  nlinarith

/-- **The dyadic right off-line moment of `ζ`**: `≤ (67/1000)T + A₀ log(2T + 2)` eventually. -/
theorem eventually_zeta_offLineRightMoment_le :
    ∃ A₀ : ℝ, 0 ≤ A₀ ∧ ∀ᶠ T in atTop,
      offLineRightMoment zetaZeroConfig T (2 * T) ≤ 67 / 1000 * T + A₀ * Real.log (2 * T + 2) := by
  obtain ⟨A₀, hA₀, hloc⟩ := paperInputs_zeta.RvM.local_count
  refine ⟨A₀, by linarith, ?_⟩
  filter_upwards [eventually_dyadicWindowTail_le_sixtySeven_thousandths,
    eventually_ge_atTop (2 : ℝ)] with T hmid hT2
  have hT0 : (0 : ℝ) ≤ T := by linarith
  rw [zeta_offLineRightMoment_eq_windowTail hT0 (by linarith)]
  -- `(T, 2T] = (T, T+1] ∪ (T+1, 2T−1] ∪ (2T−1, 2T]`
  have hsplit : windowTail 0 T (2 * T) =
      windowTail 0 T (T + 1) + windowTail 0 (T + 1) (2 * T - 1) + windowTail 0 (2 * T - 1) (2 * T) := by
    unfold windowTail; ring
  have hl : windowTail 0 T (T + 1) ≤ 1 / 2 * (Ncount T (T + 1) : ℝ) :=
    windowTail_zero_le_half_Ncount hT0 (by linarith)
  have hr : windowTail 0 (2 * T - 1) (2 * T) ≤ 1 / 2 * (Ncount (2 * T - 1) (2 * T) : ℝ) :=
    windowTail_zero_le_half_Ncount (by linarith) (by linarith)
  have hc1 : (Ncount T (T + 1) : ℝ) ≤ A₀ * Real.log (|T| + 3) := by
    have := hloc T; rwa [zetaZeroConfig_N] at this
  have hc2 : (Ncount (2 * T - 1) (2 * T) : ℝ) ≤ A₀ * Real.log (|2 * T - 1| + 3) := by
    have := hloc (2 * T - 1)
    rw [zetaZeroConfig_N, show 2 * T - 1 + 1 = 2 * T by ring] at this
    exact this
  have hlog1 : Real.log (|T| + 3) ≤ Real.log (2 * T + 2) := by
    rw [abs_of_nonneg hT0]
    exact Real.log_le_log (by positivity) (by linarith)
  have hlog2 : Real.log (|2 * T - 1| + 3) ≤ Real.log (2 * T + 2) := by
    rw [abs_of_nonneg (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hA : 0 ≤ A₀ := by linarith
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_left hlog1 hA, mul_le_mul_of_nonneg_left hlog2 hA]

/-- **Far zero copies are at most `N/A`**: at displacement `> A/log T` the window `(T, 2T]` holds at
most `N(T,2T)/A` zero copies of `ζ`, for all large `T`. -/
theorem eventually_offLineFarMass_le (A : ℝ) (hA : 0 < A) :
    ∀ᶠ T in atTop,
      (offLineFarMass zetaZeroConfig (A / Real.log T) T (2 * T) : ℝ) ≤ 1 / A * (Ncount T (2 * T) : ℝ) := by
  obtain ⟨A₀, hA₀, hmom⟩ := eventually_zeta_offLineRightMoment_le
  obtain ⟨C, T₁, hRvM⟩ := paperInputs_zeta.RvM.main
  -- `log T = o(T)` supplies the room between `0.134·2π = 0.842` and `1`
  have hlo := Real.isLittleO_log_id_atTop.bound (c := 1 / (1000 * (|C| + 2 * A₀ + 1)))
    (by positivity)
  filter_upwards [hmom, hlo, eventually_ge_atTop T₁, eventually_ge_atTop (Real.exp 100)]
    with T hm hlog hT₁ hTe
  have hTpos : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hTe
  have hT2 : 2 ≤ T := le_trans (by linarith [Real.add_one_le_exp (100 : ℝ)]) hTe
  have hL100 : 100 ≤ Real.log T := by
    rw [← Real.log_exp 100]; exact Real.log_le_log (Real.exp_pos _) hTe
  set L := Real.log T with hLdef
  have hLpos : 0 < L := by linarith
  have hlogT : L ≤ 1 / (1000 * (|C| + 2 * A₀ + 1)) * T := by
    simp only [Real.norm_eq_abs, id] at hlog
    rwa [abs_of_pos hLpos, abs_of_pos hTpos] at hlog
  have hd : 0 < A / L := div_pos hA hLpos
  have hfar := offLineFarMass_le zetaZeroConfig (A / L) T (2 * T) hd
  rw [div_div_eq_mul_div] at hfar
  -- the moment bound with `log(2T+2) ≤ L + 2`
  have hlog2 : Real.log (2 * T + 2) ≤ L + 2 := by
    have h4 : 2 * T + 2 ≤ Real.exp 2 * T := by
      have := Real.add_one_le_exp (2 : ℝ)
      nlinarith
    calc Real.log (2 * T + 2) ≤ Real.log (Real.exp 2 * T) := Real.log_le_log (by positivity) h4
      _ = L + 2 := by rw [Real.log_mul (Real.exp_pos 2).ne' hTpos.ne', Real.log_exp]; ring
  have hmom' : offLineRightMoment zetaZeroConfig T (2 * T) ≤ 67 / 1000 * T + A₀ * (L + 2) :=
    hm.trans (by nlinarith [mul_le_mul_of_nonneg_left hlog2 hA₀])
  -- Riemann–von Mangoldt from below: `N ≥ (T/2π)(L − 6) − |C| L`
  have hN : T / (2 * Real.pi) * (L - 6) - |C| * L ≤ (Ncount T (2 * T) : ℝ) := by
    have h := (abs_le.mp (hRvM T hT₁)).1
    rw [zetaZeroConfig_N] at h
    have hell : L - 6 ≤ ell1 T := by
      have hl : l T = L - Real.log (2 * Real.pi) := by
        rw [l, Real.log_div hTpos.ne' (by positivity)]
      have hpi : Real.log (2 * Real.pi) ≤ 2 * Real.pi - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have h2 : (0 : ℝ) ≤ 2 * Real.log 2 - 1 := by
        have := Real.log_two_gt_d9; linarith
      have := Real.pi_lt_d2
      rw [ell1, hl]; linarith
    have hpi : 0 < T / (2 * Real.pi) := by positivity
    have hCabs : C * Real.log T ≤ |C| * L := by
      rw [← hLdef]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hLpos.le
    nlinarith [mul_le_mul_of_nonneg_left hell hpi.le]
  -- assemble: `2(0.067T + A₀(L+2))L/A ≤ (1/A)N`, since `0.134 < 0.15 < 1/(2π)`
  have hpiT : T / (2 * Real.pi) ≥ 3 / 20 * T := by
    rw [ge_iff_le, le_div_iff₀ (by positivity)]
    have := Real.pi_lt_d2; nlinarith
  have hkey : 2 * (67 / 1000 * T + A₀ * (L + 2)) * L ≤ T / (2 * Real.pi) * (L - 6) - |C| * L := by
    have hK : 0 < |C| + 2 * A₀ + 1 := by positivity
    have h1 : (|C| + 2 * A₀ + 1) * L ≤ 1 / 1000 * T := by
      have := mul_le_mul_of_nonneg_left hlogT hK.le
      calc (|C| + 2 * A₀ + 1) * L ≤ (|C| + 2 * A₀ + 1) * (1 / (1000 * (|C| + 2 * A₀ + 1)) * T) :=
            this
        _ = 1 / 1000 * T := by field_simp
    have hsmall : (|C| + 2 * A₀ + 1) * (L + 2) * L ≤ 1 / 500 * T * L := by
      have h2 : (|C| + 2 * A₀ + 1) * (L + 2) ≤ 1 / 500 * T := by nlinarith
      exact mul_le_mul_of_nonneg_right h2 hLpos.le
    have hlow : |C| * L + 2 * A₀ * (L + 2) * L ≤ (|C| + 2 * A₀ + 1) * (L + 2) * L := by
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg C) hLpos.le) (by linarith : (0 : ℝ) ≤ L + 1)]
    have hpi' : T / (2 * Real.pi) * (L - 6) ≥ 3 / 20 * T * (L - 6) :=
      mul_le_mul_of_nonneg_right hpiT (by linarith)
    nlinarith [mul_nonneg hTpos.le (by linarith : (0 : ℝ) ≤ 14 / 1000 * L - 9 / 10)]
  have hfinal : 2 * offLineRightMoment zetaZeroConfig T (2 * T) * L / A
      ≤ 1 / A * (Ncount T (2 * T) : ℝ) := by
    rw [div_le_iff₀ hA]
    have : 1 / A * (Ncount T (2 * T) : ℝ) * A = (Ncount T (2 * T) : ℝ) := by field_simp
    rw [this]
    nlinarith [mul_le_mul_of_nonneg_right hmom' hLpos.le]
  linarith

/-- **The simple off-line core of three quarters lies near the line**, unconditional: in every large
dyadic window either at least three quarters of the zero copies of `ζ` lie on the critical line, or
at least `(HD(1) − 1/2 − 1/A − ε)N(T,2T)` simple off-line zeros lie within `A/log T` of the line. -/
theorem three_quarters_or_simple_offLine_near_line (A : ℝ) (hA : 0 < A) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀,
      3 / 4 * (Ncount T (2 * T) : ℝ) ≤ N0 T (2 * T) ∨
        (Zeta23.ThmD.HD 1 - 1 / 2 - 1 / A - ε) * (Ncount T (2 * T) : ℝ)
          ≤ offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := three_quarters_or_simple_offLine_HD_one ε hε
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp (eventually_offLineFarMass_le A hA)
  refine ⟨max T₀ T₁, fun T hT => ?_⟩
  rcases hT₀ T (le_of_max_le_left hT) with h | h
  · exact Or.inl h
  · right
    have hfar := hT₁ T (le_of_max_le_right hT)
    have hsplit : (offLineSimpleCount zetaZeroConfig T (2 * T) : ℝ) ≤
        offLineSimpleNear zetaZeroConfig (A / Real.log T) T (2 * T) +
          offLineFarMass zetaZeroConfig (A / Real.log T) T (2 * T) := by
      exact_mod_cast offLineSimpleCount_le_near_add_far zetaZeroConfig (A / Real.log T) T (2 * T)
    nlinarith

/-- **Three quarters of the zeros lie within `4/log T` of the critical line**, unconditional: for all
large `T`, at least `3/4` of the zero copies of `ζ` in `(T, 2T]` satisfy `|Re ρ − ½| ≤ 4/log T`.
This is a statement about distance to the line, not about zeros on it. -/
theorem three_quarters_within_four_div_log :
    ∀ᶠ T in atTop, 3 / 4 * (Ncount T (2 * T) : ℝ) ≤
      nearLineMass zetaZeroConfig (4 / Real.log T) T (2 * T) := by
  filter_upwards [eventually_offLineFarMass_le 4 (by norm_num)] with T hT
  have h := N_eq_nearLineMass_add_offLineFarMass zetaZeroConfig (4 / Real.log T) T (2 * T)
  rw [zetaZeroConfig_N] at h
  have h' : (Ncount T (2 * T) : ℝ) = (nearLineMass zetaZeroConfig (4 / Real.log T) T (2 * T) : ℝ)
      + (offLineFarMass zetaZeroConfig (4 / Real.log T) T (2 * T) : ℝ) := by exact_mod_cast h
  linarith

end Zeta

end RHTower

end
