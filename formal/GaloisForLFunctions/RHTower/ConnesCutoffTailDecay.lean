import GaloisForLFunctions.RHTower.ConnesCutoffCommutator
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Rapid decay of the cutoff tail integral

§VII (47) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The commutator bound (46) leaves the tail integral

  `∫_{|x| ≥ Λ} |x|^{-α} sup_{|ε| ≤ 1} |η(x+ε)| dx`,

which is `O(Λ^{-N})` for every `N` because `η` is Schwartz: the thickened supremum is still
`O(|x|^{-m})` for every `m` (a unit shift moves `|x|` by at most a factor two), and
`∫_Λ^∞ x^{-α-m} dx = Λ^{1-α-m}/(α+m-1)`.  The negative half-line is the mirror image under
`x ↦ -x`.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

instance connesUnitIntervalNonempty : Nonempty ↥(Set.Icc (-1 : ℝ) 1) :=
  ⟨⟨0, Set.mem_Icc.mpr ⟨by norm_num, by norm_num⟩⟩⟩

/-- The supremum of `‖η‖` over the unit neighbourhood of a point. -/
def connesUnitSup (η : ℝ → ℂ) (x : ℝ) : ℝ :=
  ⨆ ε : ↥(Set.Icc (-1 : ℝ) 1), ‖η (x + (ε : ℝ))‖

theorem connesUnitSup_nonneg (η : ℝ → ℂ) (x : ℝ) : 0 ≤ connesUnitSup η x :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem connesUnitSup_le {η : ℝ → ℂ} {x C : ℝ}
    (h : ∀ ε : ℝ, |ε| ≤ 1 → ‖η (x + ε)‖ ≤ C) : connesUnitSup η x ≤ C := by
  refine ciSup_le fun ε => h (ε : ℝ) ?_
  have h1 := ε.2.1
  have h2 := ε.2.2
  exact abs_le.mpr ⟨h1, h2⟩

/-- **The thickened Schwartz bound.**  A unit shift changes `|x|` by at most a factor two, so the
supremum over the unit neighbourhood still decays like every power. -/
theorem connesUnitSup_schwartz_le (η : SchwartzMap ℝ ℂ) (m : ℕ) {x : ℝ} (hx : 2 ≤ |x|) :
    connesUnitSup (η : ℝ → ℂ) x ≤ 2 ^ m * (SchwartzMap.seminorm ℂ m 0) η / |x| ^ m := by
  set S : ℝ := (SchwartzMap.seminorm ℂ m 0) η with hS
  have hS0 : (0 : ℝ) ≤ S := apply_nonneg _ η
  refine connesUnitSup_le fun ε hε => ?_
  have hxpos : (0 : ℝ) < |x| := lt_of_lt_of_le (by norm_num) hx
  have hlow : |x| / 2 ≤ |x + ε| := by
    have h1 : |x| - |ε| ≤ |x + ε| := by
      have := abs_sub_abs_le_abs_sub x (-ε)
      simp only [sub_neg_eq_add, abs_neg] at this
      linarith
    linarith
  have hxe0 : x + ε ≠ 0 := by
    intro h
    rw [h] at hlow
    simp only [abs_zero] at hlow
    linarith
  have hxe : (0 : ℝ) < |x + ε| := abs_pos.mpr hxe0
  have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ η m (x + ε)
  have hpowpos : (0 : ℝ) < |x + ε| ^ m := pow_pos hxe m
  have hle : ‖η (x + ε)‖ ≤ S / |x + ε| ^ m := by
    rw [le_div_iff₀ hpowpos]
    have : ‖x + ε‖ ^ m * ‖η (x + ε)‖ ≤ S := hsem
    rw [Real.norm_eq_abs] at this
    linarith [this]
  refine le_trans hle ?_
  have hmono : (|x| / 2) ^ m ≤ |x + ε| ^ m :=
    pow_le_pow_left₀ (by positivity) hlow m
  have hdiv : S / |x + ε| ^ m ≤ S / (|x| / 2) ^ m := by
    refine div_le_div_of_nonneg_left hS0 (by positivity) hmono
  refine le_trans hdiv (le_of_eq ?_)
  rw [div_pow]
  field_simp

/-- **§VII (47).**  The cutoff tail integral decays faster than every power of the cutoff. -/
theorem connes_cutoff_tail_rapidDecay (η : SchwartzMap ℝ ℂ) {α : ℝ} (hα0 : 0 < α) (N : ℕ) :
    Tendsto (fun L : ℝ => L ^ N *
        ∫ x in Ioi L, x ^ (-α) * connesUnitSup (η : ℝ → ℂ) x) atTop (𝓝 0) := by
  set m : ℕ := N + 2 with hm
  set S : ℝ := (SchwartzMap.seminorm ℂ m 0) η with hS
  have hS0 : (0 : ℝ) ≤ S := apply_nonneg _ η
  set p : ℝ := α + (m : ℝ) with hp
  have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hp1 : 1 < p := by
    rw [hp, hm]
    push_cast
    linarith
  set K : ℝ := 2 ^ m * S / (p - 1) with hK
  have hK0 : 0 ≤ K := by
    have : (0 : ℝ) < p - 1 := by linarith
    positivity
  -- the tail integral of the pure power
  have htail : ∀ L : ℝ, 0 < L → (∫ x in Ioi L, x ^ (-p)) = L ^ (1 - p) / (p - 1) := by
    intro L hL
    have hlt : (-p : ℝ) < -1 := by linarith
    rw [integral_Ioi_rpow_of_lt hlt hL]
    have h1 : (-p + 1 : ℝ) = -(p - 1) := by ring
    rw [h1, div_neg, neg_div, neg_neg, show -(p - 1) = 1 - p by ring]
  -- the majorant bound
  have hbound : ∀ L : ℝ, 2 ≤ L →
      (∫ x in Ioi L, x ^ (-α) * connesUnitSup (η : ℝ → ℂ) x) ≤ K * L ^ (1 - p) := by
    intro L hL
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) hL
    have hmajint : IntegrableOn (fun x : ℝ => 2 ^ m * S * x ^ (-p)) (Ioi L) volume := by
      have hint : IntegrableOn (fun x : ℝ => x ^ (-p)) (Ioi L) volume :=
        integrableOn_Ioi_rpow_of_lt (by linarith) hL0
      exact hint.const_mul _
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioi L)]
        fun x : ℝ => x ^ (-α) * connesUnitSup (η : ℝ → ℂ) x := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans hL0 hx
      have h1 : (0 : ℝ) ≤ x ^ (-α) := Real.rpow_nonneg hx0.le _
      exact mul_nonneg h1 (connesUnitSup_nonneg _ _)
    have hle : (fun x : ℝ => x ^ (-α) * connesUnitSup (η : ℝ → ℂ) x)
        ≤ᵐ[volume.restrict (Ioi L)] fun x : ℝ => 2 ^ m * S * x ^ (-p) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hxL : L < x := hx
      have hx0 : (0 : ℝ) < x := lt_trans hL0 hxL
      have hxabs : |x| = x := abs_of_pos hx0
      have hx2 : 2 ≤ |x| := by rw [hxabs]; linarith
      have hsup := connesUnitSup_schwartz_le η m hx2
      rw [hxabs] at hsup
      have h1 : (0 : ℝ) ≤ x ^ (-α) := Real.rpow_nonneg hx0.le _
      have hstep : x ^ (-α) * connesUnitSup (η : ℝ → ℂ) x
          ≤ x ^ (-α) * (2 ^ m * S / x ^ m) := mul_le_mul_of_nonneg_left hsup h1
      refine le_trans hstep (le_of_eq ?_)
      have hxm : (x : ℝ) ^ m = x ^ ((m : ℝ)) := (Real.rpow_natCast x m).symm
      have hxa : (x : ℝ) ^ α ≠ 0 := (Real.rpow_pos_of_pos hx0 α).ne'
      have hxmm : (x : ℝ) ^ ((m : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hx0 _).ne'
      rw [hxm, hp, Real.rpow_neg hx0.le α, Real.rpow_neg hx0.le (α + (m : ℝ)),
        Real.rpow_add hx0 α ((m : ℝ))]
      field_simp
    refine le_trans (integral_mono_of_nonneg hnn hmajint hle) (le_of_eq ?_)
    rw [integral_const_mul, htail L hL0, hK]
    field_simp
  -- the limit
  have hlim : Tendsto (fun L : ℝ => K * (L ^ N * L ^ (1 - p))) atTop (𝓝 0) := by
    have hexp : ∀ L : ℝ, 0 < L →
        L ^ N * L ^ (1 - p) = L ^ (-(p - (N : ℝ) - 1)) := by
      intro L hL
      rw [← Real.rpow_natCast L N, ← Real.rpow_add hL]
      congr 1
      ring
    have hmcast : ((m : ℕ) : ℝ) = (N : ℝ) + 2 := by rw [hm]; push_cast; ring
    have hq : (0 : ℝ) < p - (N : ℝ) - 1 := by
      rw [hp, hmcast]
      linarith
    have h0 : Tendsto (fun L : ℝ => L ^ (-(p - (N : ℝ) - 1))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop hq
    have h1 : Tendsto (fun L : ℝ => L ^ N * L ^ (1 - p)) atTop (𝓝 0) := by
      refine h0.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
      exact (hexp L hL).symm
    simpa using h1.const_mul K
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) hL
    refine mul_nonneg (by positivity) ?_
    refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
    have hxL : L < x := hx
    have hx0 : (0 : ℝ) < x := lt_trans hL0 hxL
    exact mul_nonneg (Real.rpow_nonneg hx0.le _) (connesUnitSup_nonneg _ _)
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with L hL
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by norm_num) hL
    have := hbound L hL
    calc L ^ N * ∫ x in Ioi L, x ^ (-α) * connesUnitSup (η : ℝ → ℂ) x
        ≤ L ^ N * (K * L ^ (1 - p)) := by
          refine mul_le_mul_of_nonneg_left this (by positivity)
      _ = K * (L ^ N * L ^ (1 - p)) := by ring

end

end GaloisForLFunctions.RHTower
