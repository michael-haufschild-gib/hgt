import GaloisForLFunctions.BiScaleUncertainty.ZeroDensityFilteredCriticalDeficitLaw
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw
import GaloisForLFunctions.RHTower.PrimeShortIntervalsSevenTwelfths

/-!
# Prime mass below the rightmost zero exponent

Split the height census where its total-count bound meets the tilted
density bound. The census vanishes to the right of the last possible
abscissa. Together these facts force positive prime mass on intervals
with exponent strictly below every off-line supremum.
-/

noncomputable section
open Filter
open _root_.RHTower
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem total_box_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {β T : ℝ}, 1/2 ≤ β → 4 ≤ T →
      ((zeroHeightBox β T).ncard : ℝ) ≤ C*(1+Real.log T)*T := by
  obtain ⟨c,hc,h⟩ := exists_ncard_zeroHeightBox_le_global
  refine ⟨21*c,by positivity,fun {β T} hβ hT => (h hβ (by linarith)).trans ?_⟩
  have ht : 0 < T := by linarith
  have hl := Real.log_nonneg (by linarith : 1 ≤ T)
  have hlog := Real.log_le_log (by linarith : 0 < 2*T+5) (by linarith : 2*T+5 ≤ 7*T)
  rw [Real.log_mul (by norm_num) ht.ne'] at hlog
  have h7 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<7)
  have hp := mul_le_mul (mul_le_mul_of_nonneg_left (by linarith : 2*T+4 ≤ 3*T) hc.le)
    (by linarith only [hlog,h7,hl] : Real.log (2*T+5) ≤ 7*(1+Real.log T))
    (Real.log_nonneg (by linarith)) (by positivity)
  linarith only [hp]

/-- A strip through z forces prime mass at every exponent above the
intersection of the linear density slope and the all-zero count. -/
theorem prime_window_from_truncated_density {z s α : ℝ}
    (hz : zetaZeroAbscissa ≤ z) (hz0 : 1/2 < z) (hz1 : z ≤ 3/4)
    (hs : 1 ≤ s) (hs1 : s < 4/3)
    (ha : 1-(1-z)/(1-s*(z-1/2)) < α) (ha1 : α < 1) :
    ∀ᶠ x : ℝ in atTop, x^α/2/2 ≤ Chebyshev.theta (x+x^α/2)-Chebyshev.theta x := by
  let A := (1-s*(z-1/2))/(1-z)
  have hzpos : 0 < 1-z := by linarith
  have hA2 : 2 < A := by
    apply (lt_div_iff₀ hzpos).2
    nlinarith only [mul_pos (by linarith only [hs1] : 0 < 2-s) (sub_pos.mpr hz0)]
  have hA0 : 0 < A := by linarith
  have hA4 : A < 4 := by
    apply (div_lt_iff₀ hzpos).2
    nlinarith only [hz1,mul_pos (by linarith only [hs] : 0 < s) (sub_pos.mpr hz0)]
  have hcut : A*(1-z) = 1-s*(z-1/2) := div_mul_cancel₀ _ hzpos.ne'
  let g := 1-1/A
  have hg : 1/2 < g := by
    have : 1/A < 1/2 := (div_lt_iff₀ hA0).2 (by linarith only [hA2])
    dsimp only [g]; linarith
  have hg1 : g < 1 := sub_lt_self _ (one_div_pos.mpr hA0)
  have hga : g < α := by simpa only [g,A,one_div_div] using ha
  obtain ⟨D,hD,B,T₀,_,hbox⟩ := exists_zeroHeightBox_ncard_le_one_sub_four_thirds_uniform
    (θ := g-1/2) (δ := 4/3-s) (by linarith only [hg]) (by linarith only [hg1])
    (sub_pos.mpr hs1)
  obtain ⟨C,hC,htotal⟩ := total_box_bound
  have hdens (T : ℝ) (hT : max T₀ 4 ≤ T) (β : ℝ) (hβ : 1/2 ≤ β) (hβ1 : β ≤ 1) :
      ((zeroHeightBox β T).ncard : ℝ) ≤ (C+D)*(1+Real.log T)^(B+1)*T^(A*(1-β)) := by
    have hT4 := (le_max_right T₀ 4).trans hT
    have ht : 1 ≤ T := by linarith only [hT4]
    have hL : 1 ≤ 1+Real.log T := by linarith only [Real.log_nonneg ht]
    have hp0 := Real.rpow_nonneg (zero_le_one.trans ht) (A*(1-β))
    by_cases hlow : β ≤ g
    · have hb : 1/A ≤ 1-β := by dsimp only [g] at hlow; linarith
      have he := (div_le_iff₀ hA0).mp hb
      have hpow := Real.rpow_le_rpow_of_exponent_le ht (by linarith only [he] : 1 ≤ A*(1-β))
      rw [Real.rpow_one] at hpow
      have hlog := pow_le_pow_right₀ hL (show 1 ≤ B+1 by omega)
      rw [pow_one] at hlog
      exact (htotal hβ hT4).trans (mul_le_mul
        (mul_le_mul (by linarith only [hD] : C ≤ C+D) hlog (by linarith) (by linarith))
        hpow (by linarith) (by positivity))
    by_cases hend : β ≤ z
    · have hb := hbox T ((le_max_left _ _).trans hT) β (by linarith only [not_le.mp hlow]) hβ1
      rw [show 4/3-(4/3-s)=s by ring] at hb
      have he : 1-s*(β-1/2) ≤ A*(1-β) := by
        nlinarith only [hcut,mul_nonneg (by linarith only [hA2,hs1] : 0 ≤ A-s) (sub_nonneg.mpr hend)]
      exact hb.trans (mul_le_mul
        (mul_le_mul (by linarith only [hC] : D ≤ C+D) (pow_le_pow_right₀ hL (Nat.le_succ B))
          (pow_nonneg (by linarith) _) (by linarith))
        (Real.rpow_le_rpow_of_exponent_le ht he) (Real.rpow_nonneg (by linarith) _) (by positivity))
    · have hem : zeroHeightBox β T = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun q hq => by
        have hre := (abs_le.mp (xiZeroCopy_abs_re_sub_half_le_zetaZeroAbscissa q)).2
        have hb : β ≤ (q.1 : ℂ).re := hq.1
        linarith only [hre,hb,hz,not_le.mp hend]
      rw [hem,Set.ncard_empty,Nat.cast_zero]
      positivity
  have hu : 1-α < 1/A := by dsimp only [g] at hga; linarith
  exact eventually_theta_short_window_of_tendsto (hg.trans hga) ha1
    (tendsto_tsum_zeroShortWeight_of_density hA0.le hA4 (sub_pos.mpr ha1)
      (by linarith only [hg.trans hga]) ((lt_div_iff₀ hA0).mp hu) (by norm_num) (add_nonneg hC hD) hdens)

/-- If the outer edge lies off the critical line, every sufficiently
large interval of some strictly smaller exponent carries prime mass. -/
theorem prime_windows_strictly_below_abscissa (h : 1/2 < zetaZeroAbscissa) :
    ∃ g : ℝ, 1/2 ≤ g ∧ g < zetaZeroAbscissa ∧ ∀ α : ℝ, g < α → α < 1 →
      ∀ᶠ x : ℝ in atTop, x^α/2/2 ≤ Chebyshev.theta (x+x^α/2)-Chebyshev.theta x := by
  by_cases hh : 7/12 < zetaZeroAbscissa
  · exact ⟨7/12,by norm_num,hh,fun α hα hα1 =>
      eventually_theta_short_window_of_tendsto (by linarith) hα1
        (tendsto_tsum_zeroShortWeight_seven_twelfths (by linarith) (by linarith) (by norm_num))⟩
  let z := zetaZeroAbscissa
  have hz : z ≤ 7/12 := le_of_not_gt hh
  have hp : 0 < 3/2-z := by linarith only [hz]
  have he : 1-(1-z)/(1-1*(z-1/2)) = (1/2)/(3/2-z) := by
    rw [show 1-1*(z-1/2)=3/2-z by ring]
    calc 1-(1-z)/(3/2-z) = (3/2-z)/(3/2-z)-(1-z)/(3/2-z) := by rw [div_self hp.ne']
         _ = _ := by rw [←sub_div,show 3/2-z-(1-z)=(1/2:ℝ) by ring]
  refine ⟨(1/2)/(3/2-z),(le_div_iff₀ hp).2 (by dsimp only [z]; linarith only [h]),?_,?_⟩
  · apply (div_lt_iff₀ hp).2
    have hz0 : 1/2 < z := h
    nlinarith only [mul_pos (sub_pos.mpr hz0) (by linarith only [hz] : 0 < 1-z)]
  · intro α hα hα1
    exact prime_window_from_truncated_density (z:=z) (s:=1) le_rfl h
      (by linarith only [hz]) le_rfl (by norm_num) (he.trans_lt hα) hα1

#print axioms prime_window_from_truncated_density
#print axioms prime_windows_strictly_below_abscissa

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
