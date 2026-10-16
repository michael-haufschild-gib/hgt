import GaloisForLFunctions.RHTower.DeningerMeyerXiContourSeries

/-! # Full Xi germs partitioned by the actual contour exhaustion -/

open Complex Set Filter Topology
open HTGeometry
open scoped Classical

namespace RHTower
noncomputable section

theorem deningerMeyerXiBand_jet {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {l h : ℝ} (hlh : l ≤ h)
    (hnz : ∀ z ∈ RectangleBorder (deningerXiContourLeft l) (deningerXiContourRight h), xi z ≠ 0)
    (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) :
    iteratedDeriv j (deningerMeyerXiContour F (deningerXiContourLeft l) (deningerXiContourRight h))
      (rho : ℂ) = if l < (rho : ℂ).im ∧ (rho : ℂ).im < h then iteratedDeriv j F (rho : ℂ) else 0 := by
  classical
  have hr := xi_divisor_support_re_mem_open_unit rho
  by_cases hwin : l < (rho : ℂ).im ∧ (rho : ℂ).im < h
  · rw [if_pos hwin]
    apply deningerMeyerXiContour_inside_jet hF (by norm_num) (by simpa using hlh) hnz rho
    apply rectangle_mem_nhds_iff.mpr
    change (rho : ℂ).re ∈ uIoo (deningerXiContourLeft l).re (deningerXiContourRight h).re ∧
      (rho : ℂ).im ∈ uIoo (deningerXiContourLeft l).im (deningerXiContourRight h).im
    simpa only [deningerXiContourLeft_re, deningerXiContourRight_re,
      deningerXiContourLeft_im, deningerXiContourRight_im,
      uIoo_of_le (by norm_num : (-1 : ℝ) ≤ 2), uIoo_of_le hlh, mem_Ioo] using
      (show (-1 < (rho : ℂ).re ∧ (rho : ℂ).re < 2) ∧
        (l < (rho : ℂ).im ∧ (rho : ℂ).im < h) from ⟨⟨by linarith [hr.1], by linarith [hr.2]⟩, hwin⟩)
  · rw [if_neg hwin]
    apply deningerMeyerXiContour_outside_jet hF (by norm_num) (by simpa using hlh) hnz rho
    intro hrect
    obtain ⟨hre, him⟩ := hrect
    have hi : l ≤ (rho : ℂ).im ∧ (rho : ℂ).im ≤ h := by
      simpa [uIcc_of_le hlh] using him
    have he : (rho : ℂ).im = l ∨ (rho : ℂ).im = h := by
      by_cases hlo : l < (rho : ℂ).im
      · right
        have hhi : ¬ (rho : ℂ).im < h := fun hh => hwin ⟨hlo, hh⟩
        linarith
      · left
        linarith
    have hb : (rho : ℂ) ∈ RectangleBorder (deningerXiContourLeft l) (deningerXiContourRight h) := by
      rcases he with he | he
      · exact Or.inl (Or.inl (Or.inl ⟨hre, by simpa using he⟩))
      · exact Or.inl (Or.inr ⟨hre, by simpa using he⟩)
    exact hnz _ hb (xi_eq_zero_of_mem_divisor_support rho)

namespace DeningerMeyerXiContourSchedule

variable (S : DeningerMeyerXiContourSchedule)

theorem height_strictMono : StrictMono S.height := by
  intro i j hij
  have hij' : (i : ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hij
  linarith [S.upper i, S.lower j]

def xiBlockWindow : ℕ → ℝ → Prop
  | 0, y => |y| < S.height 0
  | n+1, y => S.height n < |y| ∧ |y| < S.height (n+1)

theorem xiBlock_jet {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) (n : ℕ) :
    iteratedDeriv j (S.xiBlock F n) (rho : ℂ) =
      if S.xiBlockWindow n (rho : ℂ).im then iteratedDeriv j F (rho : ℂ) else 0 := by
  classical
  cases n with
  | zero =>
      rw [xiBlock, deningerMeyerXiBand_jet hF (by linarith [S.height_pos 0]) S.central_nonzero]
      simp only [xiBlockWindow, abs_lt]
  | succ n =>
      have hgap : S.height n ≤ S.height (n+1) := (S.height_strictMono (Nat.lt_succ_self n)).le
      have hu := differentiable_deningerMeyerXiContour hF
        (a := deningerXiContourLeft (S.height n)) (b := deningerXiContourRight (S.height (n+1)))
        (by norm_num) (by simpa using hgap) (S.upper_nonzero n)
      have hl := differentiable_deningerMeyerXiContour hF
        (a := deningerXiContourLeft (-S.height (n+1))) (b := deningerXiContourRight (-S.height n))
        (by norm_num) (by simpa using neg_le_neg hgap) (S.lower_nonzero n)
      change iteratedDeriv j
        (deningerMeyerXiContour F (deningerXiContourLeft (S.height n)) (deningerXiContourRight (S.height (n+1)))+
         deningerMeyerXiContour F (deningerXiContourLeft (-S.height (n+1))) (deningerXiContourRight (-S.height n)))
        (rho : ℂ) = _
      rw [iteratedDeriv_add (hu.contDiff.contDiffAt) (hl.contDiff.contDiffAt),
        deningerMeyerXiBand_jet hF hgap (S.upper_nonzero n),
        deningerMeyerXiBand_jet hF (neg_le_neg hgap) (S.lower_nonzero n)]
      by_cases hy : 0 ≤ (rho : ℂ).im
      · have hlow : ¬(-S.height (n+1) < (rho : ℂ).im ∧ (rho : ℂ).im < -S.height n) := by
          intro h
          linarith [h.2, S.height_pos n]
        simp only [xiBlockWindow, abs_of_nonneg hy, if_neg hlow, add_zero]
      · have hupp : ¬(S.height n < (rho : ℂ).im ∧ (rho : ℂ).im < S.height (n+1)) := by
          intro h
          linarith [h.1, S.height_pos n]
        have he : (-S.height (n+1) < (rho : ℂ).im ∧ (rho : ℂ).im < -S.height n) ↔
            (S.height n < -(rho : ℂ).im ∧ -(rho : ℂ).im < S.height (n+1)) := by
          constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
        simp only [xiBlockWindow, abs_of_neg (lt_of_not_ge hy), if_neg hupp, zero_add, he]

theorem xiBlockWindow_upper {n : ℕ} {y : ℝ} (h : S.xiBlockWindow n y) : |y| < S.height n := by
  cases n with
  | zero => exact h
  | succ n => exact h.2

theorem xiBlockWindow_disjoint {i j : ℕ} (hij : i < j) {y : ℝ}
    (hi : S.xiBlockWindow i y) (hj : S.xiBlockWindow j y) : False := by
  cases j with
  | zero => omega
  | succ n =>
      have hin : i ≤ n := by omega
      have hh := S.height_strictMono.monotone hin
      have hi' := S.xiBlockWindow_upper hi
      have hj' : S.height n < |y| := hj.1
      linarith

/-- Every actual Xi root belongs to exactly one full-germ block. -/
theorem exists_xiBlockWindow (rho : XiDivisorSupport) :
    ∃ j : ℕ, S.xiBlockWindow j (rho : ℂ).im ∧
      ∀ i : ℕ, S.xiBlockWindow i (rho : ℂ).im ↔ i = j := by
  classical
  have hr := xi_divisor_support_re_mem_open_unit rho
  have hnot : ∀ n, |(rho : ℂ).im| ≠ S.height n := by
    intro n hn
    exact S.horizontal_ne_zero n (by linarith [hr.1]) (by linarith [hr.2]) hn
      (xi_eq_zero_of_mem_divisor_support rho)
  have hex : ∃ n : ℕ, |(rho : ℂ).im| < S.height n := by
    obtain ⟨n, hn⟩ := exists_nat_gt |(rho : ℂ).im|
    exact ⟨n, by linarith [S.height_ge n, Nat.cast_nonneg (α := ℝ) n]⟩
  let j := Nat.find hex
  have hj : S.xiBlockWindow j (rho : ℂ).im := by
    have hs : |(rho : ℂ).im| < S.height j := Nat.find_spec hex
    cases he : j with
    | zero => simpa only [he, xiBlockWindow] using hs
    | succ n =>
        have hmin : ¬ |(rho : ℂ).im| < S.height n := Nat.find_min hex (by change n < j; omega)
        have hne := hnot n
        exact ⟨lt_of_not_ge (fun hle => hne (le_antisymm hle (le_of_not_gt hmin))),
          by simpa only [he] using hs⟩
  refine ⟨j, hj, fun i => ⟨fun hi => ?_, fun he => by subst i; exact hj⟩⟩
  rcases lt_trichotomy i j with h | h | h
  · exact (S.xiBlockWindow_disjoint h hi hj).elim
  · exact h
  · exact (S.xiBlockWindow_disjoint h hj hi).elim

end DeningerMeyerXiContourSchedule

end
end RHTower
