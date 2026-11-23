import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.OccupationGaps

/-! # Fourth-root control of a partially occupied reciprocal spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Set

private def rootWeight (k : ℕ) : ℝ := occupationWeight k^(1/4:ℝ)

private theorem root_pos (k : ℕ) : 0 < rootWeight k := Real.rpow_pos_of_pos (occupationWeight_pos k) _

private theorem root_anti : Antitone rootWeight := fun _ _ h =>
  Real.rpow_le_rpow (occupationWeight_pos _).le (occupationWeight_antitone h) (by norm_num)

private theorem root_four (k : ℕ) : rootWeight k^4 = occupationWeight k := by
  rw [rootWeight,← Real.rpow_mul_natCast (occupationWeight_pos k).le]
  norm_num

private theorem root_five (k : ℕ) : rootWeight k^5 = occupationWeight k^(5/4:ℝ) := by
  rw [rootWeight,← Real.rpow_mul_natCast (occupationWeight_pos k).le]
  norm_num

private theorem reciprocal_gap (k : ℕ) : occupationWeight k^2 ≤ 2*(occupationWeight k-occupationWeight (k+1)) := by
  let w := (k:ℝ)+1
  have hw : 1 ≤ w := le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hp : 0 < w := zero_lt_one.trans_le hw
  have hp' := add_pos hp zero_lt_one
  have ha : occupationWeight k = 1/w := by rw [occupationWeight_eq,one_div]
  have hb : occupationWeight (k+1) = 1/(w+1) := by simp only [occupationWeight_eq,Nat.cast_add,Nat.cast_one,w,one_div]
  have hd : 1/w-1/(w+1) = (1/w)*(1/(w+1)) := by field_simp; ring
  have hratio : 1/w ≤ 2/(w+1) := (div_le_div_iff₀ hp hp').mpr (by linarith only [hw])
  rw [ha,hb,hd]
  calc
    (1/w)^2 ≤ (1/w)*(2/(w+1)) := by rw [sq]; exact mul_le_mul_of_nonneg_left hratio (one_div_pos.mpr hp).le
    _ = _ := by ring

private theorem root_gap (k : ℕ) : rootWeight k^5 ≤ 8*(rootWeight k-rootWeight (k+1)) := by
  let x := rootWeight k
  let y := rootWeight (k+1)
  have hx : 0 < x := root_pos k
  have hy : 0 ≤ y := (root_pos _).le
  have hxy : y ≤ x := root_anti (Nat.le_succ k)
  have hf : (x+y)*(x^2+y^2) ≤ (2*x)*(2*x^2) := by
    apply mul_le_mul (by linarith only [hxy]) _ (add_nonneg (sq_nonneg x) (sq_nonneg y)) (by positivity)
    linarith only [pow_le_pow_left₀ hy hxy 2]
  have hg := reciprocal_gap k
  rw [← root_four k,← root_four (k+1)] at hg
  change x^5 ≤ 8*(x-y)
  apply le_of_mul_le_mul_right (a := x^3) _ (pow_pos hx 3)
  calc
    x^5*x^3 = (x^4)^2 := by ring
    _ ≤ 2*(x^4-y^4) := hg
    _ = (2*(x-y))*((x+y)*(x^2+y^2)) := by ring
    _ ≤ (2*(x-y))*((2*x)*(2*x^2)) := mul_le_mul_of_nonneg_left hf (by linarith only [hxy])
    _ = _ := by ring

/-- Clipping a decreasing sequence makes its total variation below a given height telescope. -/
private theorem capped_variation (F : Finset ℕ) {h : ℝ} (hh : 0 ≤ h) :
    (∑ k ∈ F, (min h (rootWeight k)-min h (rootWeight (k+1)))) ≤ h := by
  obtain ⟨N,hN⟩ := F.exists_nat_subset_range
  refine (sum_le_sum_of_subset_of_nonneg hN (fun k _ _ => sub_nonneg.mpr
    (min_le_min le_rfl (root_anti (Nat.le_succ k))))).trans ?_
  rw [sum_range_sub' (fun k => min h (rootWeight k))]
  exact (sub_le_self _ (le_min hh (root_pos N).le)).trans (min_le_left _ _)

private theorem capped_term (k : ℕ) {h m : ℝ} (hh : 0 ≤ h) (hm : m ∈ Icc (0:ℝ) 1) :
    h^3*(rootWeight k^5*m) ≤ occupationWeight k^2*m +
      (8*h^3)*(min h (rootWeight k)-min h (rootWeight (k+1))) := by
  let x := rootWeight k
  let y := rootWeight (k+1)
  have hxy : y ≤ x := root_anti (Nat.le_succ k)
  rcases le_total h x with hle | hle
  · have he := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hh hle 3) (mul_nonneg (pow_nonneg (root_pos k).le 5) hm.1)
    have hw : x^3*(x^5*m) = occupationWeight k^2*m := by rw [← root_four k]; dsimp only [x]; ring
    exact (he.trans_eq hw).trans (le_add_of_nonneg_right (mul_nonneg (by positivity)
      (sub_nonneg.mpr (min_le_min le_rfl hxy))))
  · rw [min_eq_right hle,min_eq_right (hxy.trans hle)]
    have he := (mul_le_of_le_one_right (pow_nonneg (root_pos k).le 5) hm.2).trans (root_gap k)
    have hb := mul_le_mul_of_nonneg_left he (pow_nonneg hh 3)
    rw [show h^3*(8*(rootWeight k-rootWeight (k+1))) = (8*h^3)*(x-y) by dsimp only [x,y]; ring] at hb
    exact hb.trans (le_add_of_nonneg_left (mul_nonneg (sq_nonneg _) hm.1))

/-- Fractional occupation at exponent five quarters is controlled by the fourth root of its quadratic mass. -/
theorem quarter_root_occupation_bound (F : Finset ℕ) (m : ℕ → ℝ) (hm : ∀ k ∈ F, m k ∈ Icc (0:ℝ) 1) :
    (∑ k ∈ F, occupationWeight k^(5/4:ℝ)*m k) ≤ 9*(∑ k ∈ F, occupationWeight k^2*m k)^(1/4:ℝ) := by
  let D := ∑ k ∈ F, occupationWeight k^2*m k
  have hD : 0 ≤ D := sum_nonneg (fun k hk => mul_nonneg (sq_nonneg _) (hm k hk).1)
  by_cases hzero : D = 0
  · have he := (sum_eq_zero_iff_of_nonneg (fun k hk => mul_nonneg (sq_nonneg (occupationWeight k)) (hm k hk).1)).mp hzero
    have hm₀ (k) (hk : k ∈ F) : m k = 0 := (mul_eq_zero.mp (he k hk)).resolve_left (sq_pos_of_pos (occupationWeight_pos k)).ne'
    change _ ≤ 9*D^_
    rw [hzero,Real.zero_rpow (by norm_num : (1/4:ℝ) ≠ 0),mul_zero]
    exact (sum_eq_zero (fun k hk => by rw [hm₀ k hk,mul_zero])).le
  let h := D^(1/4:ℝ)
  have hh : 0 < h := Real.rpow_pos_of_pos (lt_of_le_of_ne hD (Ne.symm hzero)) _
  have hh₄ : h^4 = D := by rw [show h^4 = D^((1/4:ℝ)*(4:ℕ)) from (Real.rpow_mul_natCast hD _ _).symm]; norm_num
  have hs := sum_le_sum (fun k hk => capped_term k hh.le (hm k hk))
  rw [← mul_sum,sum_add_distrib,← mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left (capped_variation F hh.le) (show 0 ≤ 8*h^3 by positivity)
  change h^3*_ ≤ D+_ at hs
  simp only [root_five] at hs
  apply le_of_mul_le_mul_left (a := h^3) _ (pow_pos hh 3)
  exact (hs.trans (add_le_add le_rfl ht)).trans_eq (by rw [← hh₄]; change h^4+8*h^3*h=h^3*(9*h); ring)

#print axioms quarter_root_occupation_bound

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
