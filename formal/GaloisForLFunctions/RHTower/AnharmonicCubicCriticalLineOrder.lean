import GaloisForLFunctions.RHTower.AnharmonicCubicCriticalLine
import Mathlib.Topology.Order.IntermediateValue

open Filter

namespace RHTower

private theorem chebyshevCriticalLineCoordinate_sub (a b : ℝ) :
    chebyshevCriticalLineCoordinate b - chebyshevCriticalLineCoordinate a =
      (b - a) * ((4 * a * b - 3) ^ 2 + 4 * (b - a) ^ 2) /
        ((4 * a ^ 2 + 1) * (4 * b ^ 2 + 1)) := by
  have ha : 4 * a ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
  have hb : 4 * b ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
  unfold chebyshevCriticalLineCoordinate
  field_simp [ha, hb]
  ring

theorem chebyshevCriticalLineCoordinate_strictMono :
    StrictMono chebyshevCriticalLineCoordinate := by
  intro a b hab
  have hnum : 0 < (4 * a * b - 3) ^ 2 + 4 * (b - a) ^ 2 := by
    have hsq : 0 < (b - a) ^ 2 := sq_pos_of_pos (sub_pos.mpr hab)
    nlinarith [sq_nonneg (4 * a * b - 3)]
  have hden : 0 < (4 * a ^ 2 + 1) * (4 * b ^ 2 + 1) := by positivity
  apply sub_pos.mp
  rw [chebyshevCriticalLineCoordinate_sub]
  exact div_pos (mul_pos (sub_pos.mpr hab) hnum) hden

theorem chebyshevCriticalLineCoordinate_continuous :
    Continuous chebyshevCriticalLineCoordinate := by
  unfold chebyshevCriticalLineCoordinate
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro t
    positivity

theorem chebyshevCriticalLineCoordinate_deriv (t : ℝ) :
    deriv chebyshevCriticalLineCoordinate t =
      ((4 * t ^ 2 - 3) / (4 * t ^ 2 + 1)) ^ 2 := by
  have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
    have h := (hasDerivAt_id t).pow 2
    change HasDerivAt (fun x : ℝ => x ^ 2) _ t at h
    exact h.congr_deriv (by norm_num)
  have hfour : HasDerivAt (fun x : ℝ => 4 * x ^ 2 + 9) (8 * t) t := by
    have h := (hpow.const_mul 4).add_const 9
    change HasDerivAt (fun x : ℝ => 4 * x ^ 2 + 9) _ t at h
    exact h.congr_deriv (by ring)
  have hone : HasDerivAt (fun x : ℝ => 4 * x ^ 2 + 1) (8 * t) t := by
    have h := (hpow.const_mul 4).add_const 1
    change HasDerivAt (fun x : ℝ => 4 * x ^ 2 + 1) _ t at h
    exact h.congr_deriv (by ring)
  have hnum : HasDerivAt (fun x : ℝ => x * (4 * x ^ 2 + 9))
      (4 * t ^ 2 + 9 + t * (8 * t)) t := by
    have h := (hasDerivAt_id t).mul hfour
    change HasDerivAt (fun x : ℝ => x * (4 * x ^ 2 + 9)) _ t at h
    exact h.congr_deriv (by simp only [id_eq, one_mul])
  have hden : 4 * t ^ 2 + 1 ≠ 0 := ne_of_gt (by positivity)
  have hq := hnum.div hone hden
  have hder : deriv chebyshevCriticalLineCoordinate t =
      ((4 * t ^ 2 + 9 + t * (8 * t)) * (4 * t ^ 2 + 1) -
          t * (4 * t ^ 2 + 9) * (8 * t)) / (4 * t ^ 2 + 1) ^ 2 := by
    change HasDerivAt chebyshevCriticalLineCoordinate _ t at hq
    exact hq.deriv
  rw [hder]
  field_simp
  ring

theorem chebyshevCriticalLineCoordinate_deriv_nonneg (t : ℝ) :
    0 ≤ deriv chebyshevCriticalLineCoordinate t := by
  rw [chebyshevCriticalLineCoordinate_deriv]
  exact sq_nonneg _

private theorem chebyshevCriticalLineCoordinate_ge_self {t : ℝ} (ht : 0 ≤ t) :
    t ≤ chebyshevCriticalLineCoordinate t := by
  have hden : 0 < 4 * t ^ 2 + 1 := by positivity
  rw [chebyshevCriticalLineCoordinate]
  apply (le_div_iff₀ hden).2
  nlinarith

private theorem chebyshevCriticalLineCoordinate_le_self {t : ℝ} (ht : t ≤ 0) :
    chebyshevCriticalLineCoordinate t ≤ t := by
  have hden : 0 < 4 * t ^ 2 + 1 := by positivity
  rw [chebyshevCriticalLineCoordinate]
  apply (div_le_iff₀ hden).2
  nlinarith

theorem chebyshevCriticalLineCoordinate_tendsto_atTop :
    Tendsto chebyshevCriticalLineCoordinate atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (max b 0)] with t ht
  exact (le_max_left b 0).trans (ht.trans
    (chebyshevCriticalLineCoordinate_ge_self ((le_max_right b 0).trans ht)))

theorem chebyshevCriticalLineCoordinate_tendsto_atBot :
    Tendsto chebyshevCriticalLineCoordinate atBot atBot := by
  refine tendsto_atBot.2 ?_
  intro b
  filter_upwards [eventually_le_atBot (min b 0)] with t ht
  exact (chebyshevCriticalLineCoordinate_le_self (ht.trans (min_le_right b 0))).trans
    (ht.trans (min_le_left b 0))

theorem chebyshevCriticalLineCoordinate_surjective :
    Function.Surjective chebyshevCriticalLineCoordinate :=
  chebyshevCriticalLineCoordinate_continuous.surjective
    chebyshevCriticalLineCoordinate_tendsto_atTop
    chebyshevCriticalLineCoordinate_tendsto_atBot

theorem chebyshevCriticalLineCoordinate_bijective :
    Function.Bijective chebyshevCriticalLineCoordinate :=
  ⟨chebyshevCriticalLineCoordinate_strictMono.injective,
    chebyshevCriticalLineCoordinate_surjective⟩

theorem chebyshevCriticalLineCoordinate_neg_sq_range :
    Set.range (fun t : ℝ => -chebyshevCriticalLineCoordinate t ^ 2) =
      Set.Iic (0 : ℝ) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    change -chebyshevCriticalLineCoordinate t ^ 2 ≤ 0
    exact neg_nonpos.mpr (sq_nonneg _)
  · intro hx
    obtain ⟨t, ht⟩ :=
      chebyshevCriticalLineCoordinate_surjective (Real.sqrt (-x))
    refine ⟨t, ?_⟩
    change -chebyshevCriticalLineCoordinate t ^ 2 = x
    rw [ht, Real.sq_sqrt (neg_nonneg.mpr hx)]
    ring

theorem chebyshevAnharmonicQ_criticalLine_sq_range :
    Set.range (fun t : ℝ =>
      chebyshevAnharmonicQ ((1 / 2 : ℂ) + (t : ℂ) * Complex.I) ^ 2) =
      (fun x : ℝ => (x : ℂ)) '' Set.Iic (0 : ℝ) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨-chebyshevCriticalLineCoordinate t ^ 2, ?_, ?_⟩
    · change -chebyshevCriticalLineCoordinate t ^ 2 ≤ 0
      exact neg_nonpos.mpr (sq_nonneg _)
    · exact (chebyshevAnharmonicQ_criticalLine_sq t).symm
  · rintro ⟨x, hx, rfl⟩
    have hxrange : x ∈ Set.range
        (fun t : ℝ => -chebyshevCriticalLineCoordinate t ^ 2) := by
      rw [chebyshevCriticalLineCoordinate_neg_sq_range]
      exact hx
    obtain ⟨t, ht⟩ := hxrange
    refine ⟨t, ?_⟩
    rw [← ht]
    exact chebyshevAnharmonicQ_criticalLine_sq t

end RHTower
