import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.ClippedTangent
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockStability.DetectorError

/-! # Interlacing pays the clipped tangent once per missing direction -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set

/-- Exponent of the qth power of a positive-temperature response. -/
def scaledExponent (β : GibbsExponent) (q : Ici (1:ℝ)) : GibbsExponent :=
  ⟨β.val*q.val,show 0 < β.val*q.val from mul_pos β.property (zero_lt_one.trans_le q.property)⟩

theorem power_scaledExponent (β : GibbsExponent) (q : Ici (1:ℝ)) {x : ℝ} (hx : 0 ≤ x) :
    x^(scaledExponent β q).val = (x^β.val)^q.val := by
  change x^(β.val*q.val) = (x^β.val)^q.val
  exact Real.rpow_mul hx _ _

private theorem abs_gap {q h a x y b : ℝ} (hq : 1 ≤ q) (hh : 0 < h) (ha : 0 ≤ a)
    (hax : a ≤ x) (hay : a ≤ y) (hxb : x ≤ b) (hyb : y ≤ b) :
    tangentSlope q h * |x-y| ≤ |x^q-y^q| + (tangentCap q h b-tangentCap q h a) := by
  have ord {u v : ℝ} (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
      tangentSlope q h * (v-u) ≤ v^q-u^q + (tangentCap q h b-tangentCap q h a) :=
    (tangentCap_gap hq hh (ha.trans hau) huv).trans (add_le_add le_rfl (sub_le_sub
      (tangentCap_mono hq hh ((ha.trans hau).trans huv) hvb) (tangentCap_mono hq hh ha hau)))
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h),abs_of_nonneg (sub_nonneg.mpr
      (Real.rpow_le_rpow (ha.trans hay) h (zero_le_one.trans hq)))]
    exact ord hay h hxb
  · rw [abs_sub_comm x y,abs_sub_comm (x^q) (y^q),abs_of_nonneg (sub_nonneg.mpr h),
      abs_of_nonneg (sub_nonneg.mpr (Real.rpow_le_rpow (ha.trans hax) h (zero_le_one.trans hq)))]
    exact ord hax h hyb

private def capEdge (β : GibbsExponent) (q h : ℝ) (n : ℕ) :=
  tangentCap q h (occupationWeight n^β.val)

private theorem capEdge_telescope (β : GibbsExponent) (q : Ici (1:ℝ)) (r : ℕ) {h : ℝ} (hh : 0 < h) :
    ∃ T ≤ (r:ℝ)*((q.val-1)*h^q.val),
      HasSum (fun n => capEdge β q.val h n - capEdge β q.val h (n+r)) T := by
  have ha : Antitone (capEdge β q.val h) := fun i j hij =>
    tangentCap_mono q.property hh (Real.rpow_nonneg (occupationWeight_pos j).le _)
      (Real.rpow_le_rpow (occupationWeight_pos j).le (occupationWeight_antitone hij) β.property.le)
  have ht : Tendsto (fun n => occupationWeight n^β.val) atTop (𝓝 0) := by
    have hn : Tendsto (fun n => occupationWeight n^β.val) atTop (𝓝 ((0:ℝ)^β.val)) :=
      ((Real.continuous_rpow_const β.property.le).tendsto 0).comp occupationWeight_tendsto
    rwa [Real.zero_rpow β.property.ne'] at hn
  have hn : Tendsto (capEdge β q.val h) atTop (𝓝 (tangentCap q.val h 0)) :=
    ((continuous_tangentCap q.property h).tendsto 0).comp ht
  rw [tangentCap_zero q.property hh.le] at hn
  refine ⟨_,?_,hasSum_shift_drop ha hn r⟩
  calc
    _ ≤ ∑ _j ∈ Finset.range r, (q.val-1)*h^q.val := Finset.sum_le_sum (fun j _ =>
      tangentCap_le q.property hh (Real.rpow_nonneg (occupationWeight_pos j).le _))
    _ = _ := by simp

/-- At any positive cutoff the real-power discrepancy obeys the summed tangent inequality. -/
theorem detector_tangent_budget (β : GibbsExponent) (q : Ici (1:ℝ)) {r : ℕ} (b c : SpectralBand r)
    {h : ℝ} (hh : 0 < h) : tangentSlope q.val h * detectorError (powerResponse β) b c ≤
      detectorError (powerResponse (scaledExponent β q)) b c + (r:ℝ)*((q.val-1)*h^q.val) := by
  have hn (n : ℕ) : tangentSlope q.val h * levelError (powerResponse β) b c n ≤
      levelError (powerResponse (scaledExponent β q)) b c n + (capEdge β q.val h n-capEdge β q.val h (n+r)) := by
    have hb (v : SpectralBand r) : occupationWeight (n+r)^β.val ≤ (v n).val^β.val ∧
        (v n).val^β.val ≤ occupationWeight n^β.val :=
      ⟨Real.rpow_le_rpow (occupationWeight_pos _).le (v n).property.1 β.property.le,
       Real.rpow_le_rpow (band_in_unit v n).1 (v n).property.2 β.property.le⟩
    change _ ≤ |(b n).val^(scaledExponent β q).val-(c n).val^(scaledExponent β q).val| + _
    rw [power_scaledExponent β q (band_in_unit b n).1,power_scaledExponent β q (band_in_unit c n).1]
    exact abs_gap q.property hh (Real.rpow_nonneg (occupationWeight_pos _).le _) (hb b).1 (hb c).1 (hb b).2 (hb c).2
  obtain ⟨T,hT,hs⟩ := capEdge_telescope β q r hh
  have hY := summable_levelError (powerResponse (scaledExponent β q)) b c
  have he := ((summable_levelError (powerResponse β) b c).mul_left (tangentSlope q.val h)).tsum_le_tsum hn (hY.add hs.summable)
  rw [tsum_mul_left,hY.tsum_add hs.summable,hs.tsum_eq] at he
  exact he.trans (add_le_add le_rfl hT)

#print axioms detector_tangent_budget

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
