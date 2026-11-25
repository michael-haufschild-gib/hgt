import GaloisForLFunctions.RHTower.XiWindowNonrealBudget
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.ExplicitFormula.PerronBoundaryBounds

/-! Simultaneous separation of the upper and lower horizontal Perron edges from primitive zeros. -/

open Complex DirichletCharacter Finset Metric

noncomputable section

namespace QH.PrimeProgressions

private theorem exists_separated_height (S : Finset ℝ) (T : ℝ) :
    ∃ U : ℝ, T ≤ U ∧ U ≤ T + 1 ∧
      ∀ y ∈ S, 1 / (8 * ((S.card : ℝ) + 1)) ≤ |y - U| := by
  let d : ℝ := 1 / (4 * ((S.card : ℝ) + 1))
  have hd : 0 < d := by dsimp only [d]; positivity
  let A := S.val.map (fun y : ℝ => (y : ℂ))
  have hA : A.card ≤ S.card := by simp [A]
  obtain ⟨i, hi⟩ := RHTower.WindowNonrealBudget.exists_far_basePoint (a := T) hd A hA
  let U : ℝ := T + (2 * (i : ℕ) + 1) * d
  refine ⟨U, le_add_of_nonneg_right (by positivity), ?_, ?_⟩
  · have hic : (i : ℕ) ≤ S.card := Nat.le_of_lt_succ i.isLt
    have hi' : (i : ℝ) ≤ S.card := by exact_mod_cast hic
    have hu : (2 * (i : ℕ) + 1 : ℝ) * d ≤ 1 := by
      dsimp only [d]
      rw [mul_one_div, div_le_one (by positivity)]
      linarith only [hi', Nat.cast_nonneg (α := ℝ) S.card]
    dsimp only [U]
    linarith only [hu]
  · intro y hy
    have hyA : (y : ℂ) ∈ A := Multiset.mem_map.mpr ⟨y, hy, rfl⟩
    have h := hi (y : ℂ) hyA
    rw [← ofReal_sub, norm_real, Real.norm_eq_abs] at h
    convert h using 1
    dsimp only [d]
    field_simp [show (S.card : ℝ) + 1 ≠ 0 by positivity] <;> ring

private theorem one_le_entireCharacterL_order {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {ρ : ℂ} (hρ : entireCharacterL χ ρ = 0) : 1 ≤ analyticOrderNatAt (entireCharacterL χ) ρ := by
  have ha := (differentiable_entireCharacterL χ).analyticAt
  have ht : analyticOrderAt (entireCharacterL χ) ρ ≠ ⊤ := entireCharacterL_order_ne_top
  have hz : analyticOrderAt (entireCharacterL χ) ρ ≠ 0 := (ha ρ).analyticOrderAt_ne_zero.mpr hρ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp ht
  have hn₀ : n ≠ 0 := fun e => hz (by rw [← hn, e]; rfl)
  unfold analyticOrderNatAt
  rw [← hn]
  simpa using Nat.one_le_iff_ne_zero.mpr hn₀

private theorem log_conductor_height_le {N : ℕ} [NeZero N] {t T : ℝ}
    (hT : 2 ≤ T) (ht : |t| ≤ T + 1) :
    Real.log ((N : ℝ) * (|t| + 2)) ≤ 3 * Real.log ((N : ℝ) * T) := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hNT : (2 : ℝ) ≤ (N : ℝ) * T := hT.trans (le_mul_of_one_le_left (by linarith only [hT]) hN)
  have hp : (N : ℝ) * (|t| + 2) ≤ 4 * ((N : ℝ) * T) := by
    rw [mul_left_comm]
    exact mul_le_mul_of_nonneg_left (by linarith only [hT, ht]) (Nat.cast_nonneg _)
  refine (Real.log_le_log (mul_pos (Nat.cast_pos.mpr (NeZero.pos N)) (by positivity)) hp).trans ?_
  rw [Real.log_mul (by norm_num) (ne_of_gt (by linarith only [hNT])),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have hL := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hNT
  norm_num only [Nat.cast_ofNat]
  linarith only [hL]

private theorem mem_wide_disk_of_ordinate {ρ : ℂ} {t : ℝ} (h₀ : 0 ≤ ρ.re) (h₁ : ρ.re ≤ 1)
    (ht : |ρ.im - t| ≤ 7 / 10) : ρ ∈ closedBall (2 + t * I) (341 / 125) := by
  rw [mem_closedBall, Complex.dist_eq]
  have h := norm_le_abs_re_add_abs_im (ρ - (2 + t * I))
  have hr : (ρ - (2 + t * I)).re = ρ.re - 2 := by simp
  have hi : (ρ - (2 + t * I)).im = ρ.im - t := by simp
  rw [hr, hi, abs_of_nonpos (by linarith only [h₁])] at h
  linarith only [h, h₀, ht]

/-- A height in each interval of length one controls both horizontal logarithmic derivatives. -/
theorem primitive_logDeriv_good_height :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ T : ℝ, 2 ≤ T → ∃ U : ℝ, T ≤ U ∧ U ≤ T + 1 ∧
        ∀ s : ℂ, -(1 / 2 : ℝ) ≤ s.re → s.re ≤ 3 → |s.im| = U →
          χ.LFunction s ≠ 0 ∧ ‖logDeriv χ.LFunction s‖ ≤ C * Real.log ((N : ℝ) * T) ^ 2 := by
  obtain ⟨C, hC, H⟩ := entireCharacterL_partial_fraction
  refine ⟨144 * C ^ 2 + 54 * C + 2, by positivity, ?_⟩
  intro N _ χ hχ T hT
  classical
  let t := T + 1 / 2
  let L := Real.log ((N : ℝ) * T)
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hL : (1 / 2 : ℝ) ≤ L :=
    (by linarith only [Real.log_two_gt_d9] : (1 / 2 : ℝ) ≤ Real.log 2).trans
      (Real.log_le_log (by norm_num) (hT.trans (le_mul_of_one_le_left (by linarith only [hT]) hN)))
  have ht : |t| ≤ T + 1 := by dsimp only [t]; rw [abs_of_nonneg (by linarith only [hT])]; linarith
  obtain ⟨A, hA, hAm, -⟩ := H N χ t
  obtain ⟨B, hB, hBm, -⟩ := H N χ (-t)
  let S := A.image (fun ρ => |ρ.im|) ∪ B.image (fun ρ => |ρ.im|)
  have hcard (Z : Finset ℂ) (w : ℝ) (hZ : (Z : Set ℂ) =
      {ρ ∈ closedBall (2 + w * I) (341 / 125) | entireCharacterL χ ρ = 0})
      (hm : (∑ ρ ∈ Z, (analyticOrderNatAt (entireCharacterL χ) ρ : ℝ)) ≤
        C * Real.log ((N : ℝ) * (|w| + 2))) (hw : |w| ≤ T + 1) : (Z.card : ℝ) ≤ 3 * C * L := by
    calc
      (Z.card : ℝ) = ∑ _ρ ∈ Z, (1 : ℝ) := by simp
      _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt (entireCharacterL χ) ρ : ℝ) := by
        apply sum_le_sum
        intro ρ hρ
        change ρ ∈ (Z : Set ℂ) at hρ
        rw [hZ] at hρ
        exact_mod_cast one_le_entireCharacterL_order hρ.2
      _ ≤ _ := hm
      _ ≤ 3 * C * L := (mul_le_mul_of_nonneg_left (log_conductor_height_le (N := N) hT hw)
        hC.le).trans_eq (by ring)
  have hS : (S.card : ℝ) ≤ 6 * C * L := by
    have hc : (S.card : ℝ) ≤ A.card + B.card := by
      exact_mod_cast (card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)
    have ha := hcard A t hA hAm ht
    have hb := hcard B (-t) hB hBm (by simpa only [abs_neg] using ht)
    linarith only [hc, ha, hb]
  obtain ⟨U, hU₀, hU₁, hU⟩ := exists_separated_height S T
  let d := 1 / (8 * ((S.card : ℝ) + 1))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hdc : d ≤ 1 / 5 := by
    dsimp only [d]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 5)
    linarith only [Nat.cast_nonneg (α := ℝ) S.card]
  refine ⟨U, hU₀, hU₁, ?_⟩
  intro s hs₀ hs₁ hsU
  have hs := mem_entireCharacterL_eval_disc hs₀ hs₁
  obtain ⟨Z, hZ, hm, hpf⟩ := H N χ s.im
  have hsep : ∀ ρ ∈ Z, d ≤ ‖s - ρ‖ := by
    intro ρ hρ
    change ρ ∈ (Z : Set ℂ) at hρ
    rw [hZ] at hρ
    by_cases hfar : (1 / 5 : ℝ) ≤ |ρ.im - s.im|
    · refine hdc.trans (hfar.trans ?_)
      simpa only [sub_im, abs_sub_comm] using abs_im_le_norm (s - ρ)
    have hre : 0 ≤ ρ.re ∧ ρ.re ≤ 1 := by
      rcases entireCharacterL_zero_mem_strip_or_zero hχ hρ.1 hρ.2 with h | rfl
      · exact ⟨h.1.le, h.2.le⟩
      · norm_num
    have htclose : |U - t| ≤ 1 / 2 := abs_le.mpr
      ⟨by dsimp only [t]; linarith only [hU₀], by dsimp only [t]; linarith only [hU₁]⟩
    have hmem : |ρ.im| ∈ S := by
      rcases le_or_gt 0 s.im with hp | hn
      · have e : s.im = U := (abs_of_nonneg hp).symm.trans hsU
        have htρ : |ρ.im - t| ≤ 7 / 10 := by
          have h := abs_add_le (ρ.im - s.im) (s.im - t)
          rw [sub_add_sub_cancel, show |s.im - t| = |U - t| by rw [e]] at h
          linarith only [h, lt_of_not_ge hfar, htclose]
        have hρA : ρ ∈ (A : Set ℂ) := by
          rw [hA]
          exact ⟨mem_wide_disk_of_ordinate hre.1 hre.2 htρ, hρ.2⟩
        exact mem_union_left _ (mem_image_of_mem _ hρA)
      · have e : s.im = -U := by
          have h := (abs_of_neg hn).symm.trans hsU
          linarith only [h]
        have htρ : |ρ.im - -t| ≤ 7 / 10 := by
          have h := abs_add_le (ρ.im - s.im) (s.im - -t)
          have hst : |s.im - -t| = |U - t| := by rw [e, neg_sub_neg, abs_sub_comm]
          rw [sub_add_sub_cancel, hst] at h
          linarith only [h, lt_of_not_ge hfar, htclose]
        have hρB : ρ ∈ (B : Set ℂ) := by
          rw [hB]
          exact ⟨mem_wide_disk_of_ordinate hre.1 hre.2 htρ, hρ.2⟩
        exact mem_union_right _ (mem_image_of_mem _ hρB)
    refine (hU _ hmem).trans ?_
    rw [← hsU]
    exact (abs_abs_sub_abs_le_abs_sub ρ.im s.im).trans (by
      simpa only [sub_im, abs_sub_comm] using abs_im_le_norm (s - ρ))
  have hLog := log_conductor_height_le (N := N) hT (hsU.trans_le hU₁)
  have hcoef : C * Real.log ((N : ℝ) * (|s.im| + 2)) ≤ 3 * C * L :=
    (mul_le_mul_of_nonneg_left hLog hC.le).trans_eq (by dsimp only [L]; ring)
  obtain ⟨hzero, hb⟩ := norm_logDeriv_le_of_local_zero_separation hd hs hZ
    (hm.trans hcoef) (fun h => (hpf s hs h).trans hcoef) hsep
  have hsne : s ≠ 1 := by
    intro e
    have hu : 2 ≤ U := hT.trans hU₀
    norm_num [e] at hsU
    linarith only [hu, hsU]
  have hLzero : χ.LFunction s ≠ 0 := fun e => hzero ((entireCharacterL_eq_zero_iff hsne).2 e)
  refine ⟨hLzero, ?_⟩
  have hp : ‖if χ = 1 then 1 / (s - 1) else (0 : ℂ)‖ ≤ 1 / 2 := by
    split_ifs
    · have h : (2 : ℝ) ≤ ‖s - 1‖ := by
        refine (hT.trans (hU₀.trans_eq hsU.symm)).trans ?_
        simpa only [sub_im, one_im, sub_zero] using abs_im_le_norm (s - 1)
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le (by norm_num) h
    · norm_num
  have hinv : d⁻¹ ≤ 48 * C * L + 8 := by
    dsimp only [d]
    rw [one_div, inv_inv]
    linarith only [hS]
  have hb' : ‖logDeriv (entireCharacterL χ) s‖ ≤ 3 * C * L + (3 * C * L) * (48 * C * L + 8) := by
    rw [div_eq_mul_inv] at hb
    exact hb.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hinv
      (by positivity [show 0 ≤ L by linarith only [hL]])))
  have hL₀ : 0 ≤ L := by linarith only [hL]
  have hL₁ : L ≤ 2 * L ^ 2 := by nlinarith only [mul_nonneg hL₀ (sub_nonneg.mpr hL)]
  have hL₂ : (1 / 2 : ℝ) ≤ 2 * L ^ 2 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hL 2
    linarith only [h]
  calc
    ‖logDeriv χ.LFunction s‖ =
        ‖logDeriv (entireCharacterL χ) s - if χ = 1 then 1 / (s - 1) else 0‖ := by
      rw [logDeriv_entireCharacterL hsne hLzero, add_sub_cancel_right]
    _ ≤ 3 * C * L + (3 * C * L) * (48 * C * L + 8) + 1 / 2 :=
      (norm_sub_le _ _).trans (add_le_add hb' hp)
    _ ≤ (144 * C ^ 2 + 54 * C + 2) * L ^ 2 := by
      nlinarith only [mul_le_mul_of_nonneg_left hL₁ hC.le, hL₂]

end QH.PrimeProgressions
