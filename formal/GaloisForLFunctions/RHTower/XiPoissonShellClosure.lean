import GaloisForLFunctions.RHTower.XiPoissonShellSplit

/-!
# The bottom shell lies on the critical line

Assembling the real-variable converse.  If every moment trace is nonnegative on the positive real
axis, then the bottom shell carries no displacement.

The chain: pick a displacement `l` of maximal modulus; split the shell into the class at `l`, its
mirror, and a remainder of strictly smaller modulus; align the class at arbitrarily large times so
that the two classes contribute `-2 ‖A‖`; transfer through the asymptotic identity, whose tail is
negligible; and observe that `‖A‖ = (class size) * sqrt(g_1^(2 : ℕ)+l^(2 : ℕ))^n` outgrows the remainder's
`(card) * d^n` because `d < sqrt(g_1^(2 : ℕ)+l^(2 : ℕ))`.
-/

open Complex Filter
open scoped BigOperators

namespace RHTower

noncomputable section

theorem xiPoissonShellPoly_eq (n : ℕ) (t : ℝ) :
    xiPoissonShellPoly n t =
      ∑ q ∈ xiPoissonBottomShell,
        xiPoissonPoint q ^ n *
          Complex.exp (((-(t * (xiPoissonPoint q).im) : ℝ) : ℂ) * I) := by
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 2
  push_cast
  ring

/-- The weighted above-bottom tail can be made uniformly small beyond some time. -/
theorem exists_tail_bound (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      ‖((Real.exp (xiPoissonBottomHeight * t) : ℝ) : ℂ) *
        xiPoissonAboveMomentSum n ((t : ℝ) : ℂ)‖ ≤ ε := by
  classical
  rcases Set.eq_empty_or_nonempty xiPoissonAboveBottom with hE | hNE
  · refine ⟨1, fun t _ => ?_⟩
    have hempty : IsEmpty (xiPoissonAboveBottom : Set XiZeroCopy) := by
      rw [hE]; exact Set.isEmpty_coe_sort.mpr rfl
    have : xiPoissonAboveMomentSum n ((t : ℝ) : ℂ) = 0 := by
      rw [xiPoissonAboveMomentSum]
      exact tsum_empty
    rw [this, mul_zero, norm_zero]
    exact hε.le
  · have hlim := tendsto_exp_bottomHeight_mul_aboveBottom_moment_tail
      (σ := 1) one_pos n hNE
    have hev := (hlim.eventually (ge_mem_nhds
      (by positivity : (0 : ℝ) < ε / Real.exp xiPoissonBottomHeight))).exists_forall_of_atTop
    obtain ⟨V, hV⟩ := hev
    refine ⟨1 + max V 0, fun t ht => ?_⟩
    have hv : 0 ≤ t - 1 := by
      have : (0 : ℝ) ≤ max V 0 := le_max_right _ _
      linarith
    have hVle : V ≤ t - 1 := by
      have : V ≤ max V 0 := le_max_left _ _
      linarith
    have hb := norm_exp_bottomHeight_mul_aboveMomentSum_le (σ := 1) one_pos n hv
    have hrw : (1 : ℝ) + (t - 1) = t := by ring
    rw [hrw] at hb
    refine le_trans hb ?_
    have hkey := hV (t - 1) hVle
    rw [show (1 : ℝ) + (t - 1) = t from by ring] at hkey
    have hpos : (0 : ℝ) < Real.exp xiPoissonBottomHeight := Real.exp_pos _
    have hsplit : Real.exp (xiPoissonBottomHeight * t) =
        Real.exp xiPoissonBottomHeight * Real.exp (xiPoissonBottomHeight * (t - 1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hsplit, mul_assoc]
    calc Real.exp xiPoissonBottomHeight *
          (Real.exp (xiPoissonBottomHeight * (t - 1)) *
            ∑' q : xiPoissonAboveBottom,
              ‖xiPoissonPoint (q : XiZeroCopy)‖ ^ n * xiPoissonWeight t (q : XiZeroCopy))
        ≤ Real.exp xiPoissonBottomHeight * (ε / Real.exp xiPoissonBottomHeight) :=
          mul_le_mul_of_nonneg_left hkey hpos.le
      _ = ε := by field_simp

/-- **The bottom shell lies on the critical line**, granted nonnegativity of every moment trace. -/
theorem xiPoissonPoint_im_eq_zero_of_forall_moment_nonneg
    (hmom : ∀ (n : ℕ) (t : ℝ), 0 < t → 0 ≤ (xiPoissonMomentTraceC n ((t : ℝ) : ℂ)).re) :
    ∀ q ∈ xiPoissonBottomShell, (xiPoissonPoint q).im = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨q₁, hq₁mem, hq₁ne⟩ := hcon
  obtain ⟨qs, hqsmem, hmax⟩ := Finset.exists_max_image xiPoissonBottomShell
    (fun q => |(xiPoissonPoint q).im|) ⟨q₁, hq₁mem⟩
  set l : ℝ := (xiPoissonPoint qs).im with hldef
  have hlne : l ≠ 0 := by
    intro h0
    have hb := hmax q₁ hq₁mem
    rw [h0, abs_zero] at hb
    exact hq₁ne (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))
  have hmax' : ∀ q ∈ xiPoissonBottomShell, |(xiPoissonPoint q).im| ≤ |l| := hmax
  set M : ℝ := Real.sqrt (xiPoissonBottomHeight ^ (2 : ℕ) + l ^ (2 : ℕ)) with hMdef
  have hMpos : 0 < M := by
    rw [hMdef]
    refine Real.sqrt_pos.mpr ?_
    have hg : 0 < xiPoissonBottomHeight ^ (2 : ℕ) := pow_pos xiPoissonBottomHeight_pos 2
    linarith [sq_nonneg l]
  have hqsclass : qs ∈ xiShellClass l := mem_xiShellClass.mpr ⟨hqsmem, rfl⟩
  have hcardpos : 0 < ((xiShellClass l).card : ℝ) := by
    have : 0 < (xiShellClass l).card := Finset.card_pos.mpr ⟨qs, hqsclass⟩
    exact_mod_cast this
  have hbase : (((xiPoissonBottomHeight : ℝ) : ℂ) + (l : ℂ) * I) ≠ 0 := by
    intro h
    have hre : (((xiPoissonBottomHeight : ℝ) : ℂ) + (l : ℂ) * I).re = xiPoissonBottomHeight := by
      simp [Complex.mul_re]
    rw [h] at hre
    simp only [Complex.zero_re] at hre
    linarith [xiPoissonBottomHeight_pos, hre]
  have hAne : ∀ n : ℕ, (∑ q ∈ xiShellClass l, xiPoissonPoint q ^ n) ≠ 0 := by
    intro n
    rw [xiShellClass_sum]
    exact mul_ne_zero (by exact_mod_cast (ne_of_gt hcardpos)) (pow_ne_zero n hbase)
  obtain ⟨d, hd0, hdM, hdb⟩ : ∃ d : ℝ, 0 ≤ d ∧ d < M ∧
      ∀ q ∈ xiShellRest l, ‖xiPoissonPoint q‖ ≤ d := by
    rcases (xiShellRest l).eq_empty_or_nonempty with hE | hNE
    · exact ⟨0, le_refl 0, hMpos, by simp [hE]⟩
    · obtain ⟨qd, hqd, hmaxd⟩ := Finset.exists_max_image _ (fun q => ‖xiPoissonPoint q‖) hNE
      exact ⟨‖xiPoissonPoint qd‖, norm_nonneg _,
        norm_lt_of_mem_xiShellRest hmax' hqd, hmaxd⟩
  have hkey : ∀ n : ℕ,
      2 * ((xiShellClass l).card : ℝ) * M ^ n ≤ ((xiShellRest l).card : ℝ) * d ^ n := by
    intro n
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨T, hT⟩ := exists_tail_bound n hε
    obtain ⟨t, htT, hshell⟩ := HTGeometry.exists_ge_re_sum_exp_le_of_split
      xiPoissonBottomShell (xiShellClass l) (xiShellClass (-l)) (xiShellRest l)
      (fun q => (xiPoissonPoint q).im) (fun q => xiPoissonPoint q ^ n) hlne
      (xiPoissonBottomShell_split hlne)
      (fun q hq => (mem_xiShellClass.mp hq).2)
      (fun q hq => (mem_xiShellClass.mp hq).2)
      (hAne n) (xiShellClass_sum_neg l n) (max T 1)
    have ht1 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right T 1) htT)
    have htail := hT t (le_trans (le_max_left T 1) htT)
    have hid := exp_bottomHeight_mul_momentTraceC_eq ht1 n
    have hre : (((Real.exp (xiPoissonBottomHeight * t) : ℝ) : ℂ) *
        xiPoissonMomentTraceC n ((t : ℝ) : ℂ)).re =
        Real.exp (xiPoissonBottomHeight * t) *
          (xiPoissonMomentTraceC n ((t : ℝ) : ℂ)).re :=
      Complex.re_ofReal_mul _ _
    have hnn : 0 ≤ (((Real.exp (xiPoissonBottomHeight * t) : ℝ) : ℂ) *
        xiPoissonMomentTraceC n ((t : ℝ) : ℂ)).re := by
      rw [hre]
      exact mul_nonneg (Real.exp_pos _).le (hmom n t ht1)
    rw [hid, Complex.add_re] at hnn
    have htailre : (((Real.exp (xiPoissonBottomHeight * t) : ℝ) : ℂ) *
        xiPoissonAboveMomentSum n ((t : ℝ) : ℂ)).re ≤ ε :=
      le_trans (Complex.re_le_norm _) htail
    have hpoly : (xiPoissonShellPoly n t).re ≤
        -2 * ‖∑ q ∈ xiShellClass l, xiPoissonPoint q ^ n‖ +
          ∑ q ∈ xiShellRest l, ‖xiPoissonPoint q ^ n‖ := by
      rw [xiPoissonShellPoly_eq]
      exact hshell
    have hAnorm : ‖∑ q ∈ xiShellClass l, xiPoissonPoint q ^ n‖ =
        ((xiShellClass l).card : ℝ) * M ^ n := by
      rw [norm_xiShellClass_sum, hMdef]
    have hrest : ∑ q ∈ xiShellRest l, ‖xiPoissonPoint q ^ n‖ ≤
        ((xiShellRest l).card : ℝ) * d ^ n := by
      have hterm : ∀ q ∈ xiShellRest l, ‖xiPoissonPoint q ^ n‖ ≤ d ^ n := by
        intro q hq
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hdb q hq) n
      calc ∑ q ∈ xiShellRest l, ‖xiPoissonPoint q ^ n‖
          ≤ ∑ _q ∈ xiShellRest l, d ^ n := Finset.sum_le_sum hterm
        _ = ((xiShellRest l).card : ℝ) * d ^ n := by
            rw [Finset.sum_const, nsmul_eq_mul]
    rw [hAnorm] at hpoly
    linarith
  exact HTGeometry.not_forall_mul_pow_le_pow hd0 hdM (by linarith [hcardpos]) hkey

end

end RHTower
