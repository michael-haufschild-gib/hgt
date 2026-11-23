import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.DetectorError

/-! # A rank budget for the square-root response

The clipped square compares an amplitude discrepancy with its Born
discrepancy. Interlacing makes the correction telescope.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology

def doubleExponent (β : GibbsExponent) : GibbsExponent := ⟨β.val*2,mul_pos β.property (by norm_num : (0:ℝ) < 2)⟩

theorem power_doubleExponent (β : GibbsExponent) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (doubleExponent β).val = (x ^ β.val)^2 := by
  change x ^ (β.val * (2:ℝ)) = (x ^ β.val)^2
  rw [Real.rpow_mul hx,Real.rpow_two]

private def clippedSquare (L x : ℝ) := (max (L-x) 0)^2

private theorem clipped_antitone (L : ℝ) : Antitone (clippedSquare L) := fun _ _ h =>
  pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right _ (sub_le_sub_left h L)) 2

private theorem clipped_gap (L : ℝ) {x y : ℝ} (h : y ≤ x) :
    2*L*(x-y) ≤ x^2-y^2 + (clippedSquare L y - clippedSquare L x) := by
  unfold clippedSquare
  by_cases hx : x ≤ L
  · rw [max_eq_left (sub_nonneg.mpr (h.trans hx)),max_eq_left (sub_nonneg.mpr hx)]
    nlinarith only []
  · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hx))]
    by_cases hy : y ≤ L
    · rw [max_eq_left (sub_nonneg.mpr hy)]
      nlinarith only [sq_nonneg (x-L)]
    · rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hy))]
      have hp : 0 ≤ x+y-2*L := by linarith only [le_of_not_ge hx,le_of_not_ge hy]
      nlinarith only [mul_nonneg (sub_nonneg.mpr h) hp]

private theorem ordered_clipped_gap (L : ℝ) {a y x b : ℝ} (hay : a ≤ y) (h : y ≤ x) (hxb : x ≤ b) :
    2*L*(x-y) ≤ x^2-y^2 + (clippedSquare L a - clippedSquare L b) :=
  (clipped_gap L h).trans (add_le_add le_rfl (sub_le_sub (clipped_antitone L hay) (clipped_antitone L hxb)))

private def clippedDrop (β : GibbsExponent) (L : ℝ) (r n : ℕ) :=
  clippedSquare L (occupationWeight (n+r)^β.val) - clippedSquare L (occupationWeight n^β.val)

private theorem coordinate_budget (β : GibbsExponent) {r : ℕ} (b c : SpectralBand r) (L : ℝ) (n : ℕ) :
    2*L * levelError (powerResponse β) b c n ≤ levelError (powerResponse (doubleExponent β)) b c n + clippedDrop β L r n := by
  let x := (b n).val^β.val
  let y := (c n).val^β.val
  have hx : 0 ≤ x := Real.rpow_nonneg (band_in_unit b n).1 _
  have hy : 0 ≤ y := Real.rpow_nonneg (band_in_unit c n).1 _
  have hband (v : SpectralBand r) :
      occupationWeight (n+r)^β.val ≤ (v n).val^β.val ∧ (v n).val^β.val ≤ occupationWeight n^β.val :=
    ⟨Real.rpow_le_rpow (occupationWeight_pos _).le (v n).property.1 β.property.le,
      Real.rpow_le_rpow (band_in_unit v n).1 (v n).property.2 β.property.le⟩
  change 2*L*|x-y| ≤ |(b n).val^(doubleExponent β).val-(c n).val^(doubleExponent β).val| + _
  rw [power_doubleExponent β (band_in_unit b n).1,power_doubleExponent β (band_in_unit c n).1]
  change 2*L*|x-y| ≤ |x^2-y^2| + _
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hy h 2))]
    exact ordered_clipped_gap L (hband c).1 h (hband b).2
  · rw [abs_sub_comm x y,abs_sub_comm (x^2) (y^2),abs_of_nonneg (sub_nonneg.mpr h),
      abs_of_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hx h 2))]
    exact ordered_clipped_gap L (hband b).1 h (hband c).2

private theorem clipped_budget_sum (β : GibbsExponent) (r : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    ∃ T ≤ (r:ℝ)*L^2, HasSum (clippedDrop β L r) T := by
  let a (n : ℕ) := L^2 - clippedSquare L (occupationWeight n^β.val)
  have ha : Antitone a := fun i j hij => sub_le_sub_left
    (clipped_antitone L (Real.rpow_le_rpow (occupationWeight_pos j).le (occupationWeight_antitone hij) β.property.le)) _
  have ht : Tendsto (fun n => occupationWeight n^β.val) atTop (𝓝 ((0:ℝ)^β.val)) :=
    ((Real.continuous_rpow_const β.property.le).tendsto 0).comp occupationWeight_tendsto
  rw [Real.zero_rpow β.property.ne'] at ht
  have hc : Continuous (fun x : ℝ => L^2 - clippedSquare L x) :=
    continuous_const.sub (((continuous_const.sub continuous_id).max continuous_const).pow 2)
  have hz : Tendsto a atTop (𝓝 0) := by
    have h₀ : L^2 - clippedSquare L 0 = 0 := by simp only [clippedSquare,sub_zero,max_eq_left hL,sub_self]
    have ht' : Tendsto a atTop (𝓝 (L^2 - clippedSquare L 0)) := (hc.tendsto 0).comp ht
    rwa [h₀] at ht'
  refine ⟨∑ n ∈ Finset.range r, a n,?_,?_⟩
  · calc
      _ ≤ ∑ _n ∈ Finset.range r, L^2 := Finset.sum_le_sum (fun n _ => sub_le_self _ (sq_nonneg _))
      _ = _ := by simp
  · apply (hasSum_shift_drop ha hz r).congr_fun
    intro n
    unfold clippedDrop a
    abel

/-- Each rank contributes at most one clipped-square budget, independently of the locations of the omissions. -/
theorem amplitude_linear_budget (β : GibbsExponent) {r : ℕ} (b c : SpectralBand r) {L : ℝ} (hL : 0 ≤ L) :
    2*L*detectorError (powerResponse β) b c ≤ detectorError (powerResponse (doubleExponent β)) b c + (r:ℝ)*L^2 := by
  obtain ⟨T,hT,hs⟩ := clipped_budget_sum β r hL
  have hB := summable_levelError (powerResponse (doubleExponent β)) b c
  have h := ((summable_levelError (powerResponse β) b c).mul_left (2*L)).tsum_le_tsum
    (coordinate_budget β b c L) (hB.add hs.summable)
  rw [tsum_mul_left,hB.tsum_add hs.summable,hs.tsum_eq] at h
  exact h.trans (add_le_add le_rfl hT)

#print axioms amplitude_linear_budget

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
