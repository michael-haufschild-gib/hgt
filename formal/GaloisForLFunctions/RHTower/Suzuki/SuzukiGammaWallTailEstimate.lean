import GaloisForLFunctions.HTGeometry.WeightedHardyInequality

/-!
# The remaining tail of the two-fold integration by parts is square integrable

After two integrations by parts the surviving integrand carries the amplitude `t^{-2}` against the
propagator ratio `(1+t)^p(1+x)^{-p}`.  Reading that as a Hardy average with density

`h(t) = (1+t)^p t^{-1-p}`

turns the tail into the weighted Hardy inequality, whose hypothesis is square integrability of `h`;
and on a terminal ray `1 + t ≤ 2t`, so `h(t) ≤ 2^p t^{-1}`, whose square is integrable.  Hence the
tail is square integrable for *every* `p > 1/2` — the three separate regimes `p < 1`, `p = 1`,
`p > 1` of the classical computation collapse into one statement, because the Hardy inequality has
already absorbed the propagator.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The scalar density that turns the surviving tail into a Hardy average. -/
def wallTailDensity (p t : ℝ) : ℝ := (1 + t) ^ p * t ^ (-1 - p)

theorem wallTailDensity_le {p t : ℝ} (hp : 0 ≤ p) (ht : 1 < t) :
    wallTailDensity p t ≤ 2 ^ p * t⁻¹ := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have h2t : (1 : ℝ) + t ≤ 2 * t := by linarith
  have hmono : (1 + t) ^ p ≤ (2 * t) ^ p :=
    Real.rpow_le_rpow (by linarith) h2t hp
  have hsplit : (2 * t) ^ p = 2 ^ p * t ^ p :=
    Real.mul_rpow (by norm_num) ht0.le
  have hexp : t ^ p * t ^ (-1 - p) = t⁻¹ := by
    rw [← Real.rpow_add ht0]
    rw [show p + (-1 - p) = -1 by ring, Real.rpow_neg_one]
  calc wallTailDensity p t = (1 + t) ^ p * t ^ (-1 - p) := rfl
    _ ≤ (2 * t) ^ p * t ^ (-1 - p) :=
        mul_le_mul_of_nonneg_right hmono (Real.rpow_nonneg ht0.le _)
    _ = 2 ^ p * (t ^ p * t ^ (-1 - p)) := by rw [hsplit]; ring
    _ = 2 ^ p * t⁻¹ := by rw [hexp]

theorem wallTailDensity_nonneg {p t : ℝ} (ht : 0 < t) : 0 ≤ wallTailDensity p t :=
  mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg ht.le _)

/-- **The Hardy density is square integrable on the terminal ray.** -/
theorem lintegral_sq_wallTailDensity_lt_top {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (wallTailDensity p t) ^ 2) < ⊤ := by
  have hmaj : ∀ t ∈ Ioi (1 : ℝ),
      ENNReal.ofReal (wallTailDensity p t) ^ 2
        ≤ ENNReal.ofReal (4 ^ p * t ^ (-(2 : ℝ))) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
    have hbase := wallTailDensity_le hp ht
    have hnn := wallTailDensity_nonneg (p := p) ht0
    have hsq : wallTailDensity p t ^ 2 ≤ 4 ^ p * t ^ (-(2 : ℝ)) := by
      have hstep : wallTailDensity p t ^ 2 ≤ (2 ^ p * t⁻¹) ^ 2 :=
        pow_le_pow_left₀ hnn hbase 2
      refine hstep.trans (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast ((2 : ℝ) ^ p) 2, ← Real.rpow_mul (by norm_num),
        show p * ((2 : ℕ) : ℝ) = ((2 : ℝ) * p) by push_cast; ring,
        Real.rpow_mul (by norm_num), Real.rpow_two]
      congr 1
      · norm_num
      · rw [← Real.rpow_neg_one t, ← Real.rpow_natCast (t ^ (-1 : ℝ)) 2,
          ← Real.rpow_mul ht0.le]
        congr 1
        push_cast
        ring
    calc ENNReal.ofReal (wallTailDensity p t) ^ 2
        = ENNReal.ofReal (wallTailDensity p t ^ 2) := by
          rw [← ENNReal.ofReal_pow hnn]
      _ ≤ ENNReal.ofReal (4 ^ p * t ^ (-(2 : ℝ))) := ENNReal.ofReal_le_ofReal hsq
  have hint : IntegrableOn (fun t : ℝ => 4 ^ p * t ^ (-(2 : ℝ))) (Ioi (1 : ℝ)) volume :=
    ((integrableOn_Ioi_rpow_iff (by norm_num : (0:ℝ) < 1)).mpr (by norm_num)).const_mul _
  have hfin : (∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (4 ^ p * t ^ (-(2 : ℝ)))) ≠ ⊤ := by
    have hnn : ∀ᵐ t ∂(volume.restrict (Ioi (1 : ℝ))), 0 ≤ 4 ^ p * t ^ (-(2 : ℝ)) := by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
    exact ENNReal.ofReal_ne_top
  exact lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi hmaj) (lt_top_iff_ne_top.mpr hfin)

/-! ## The tail estimate -/

variable {X : Type*} [NormedAddCommGroup X]

/-- **The surviving tail is square integrable.**  A profile obeying the propagated bound with an
amplitude dominated by the Hardy density is square integrable on the terminal ray, for every
`p > 1/2`. -/
theorem lintegral_enorm_sq_lt_top_of_wallTailBound {p : ℝ} (hp : 1 / 2 < p)
    {f h : ℝ → X} {K κ C : ℝ} (hK : 0 ≤ K) (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    (hbound : ∀ x : ℝ, 1 < x →
      ‖f x‖ₑ ≤ ENNReal.ofReal (K * x ^ (-p))
        * (ENNReal.ofReal κ + ∫⁻ t in Ioc (1 : ℝ) x, ENNReal.ofReal (t ^ (p - 1)) * ‖h t‖ₑ))
    (hmeas : AEMeasurable (fun t => ‖h t‖ₑ) (volume.restrict (Ioi (1 : ℝ))))
    (hh : ∀ t : ℝ, 1 < t → ‖h t‖ ≤ C * wallTailDensity p t) :
    ∫⁻ x in Ioi (1 : ℝ), ‖f x‖ₑ ^ 2 < ⊤ := by
  have hp0 : (0 : ℝ) ≤ p := by linarith
  have hfin : ∫⁻ t in Ioi (1 : ℝ), ‖h t‖ₑ ^ 2 < ⊤ := by
    have hmaj : ∀ t ∈ Ioi (1 : ℝ), ‖h t‖ₑ ^ 2
        ≤ ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (wallTailDensity p t) ^ 2 := by
      intro t ht
      have hnn := wallTailDensity_nonneg (p := p) (lt_trans zero_lt_one ht)
      have hstep : ‖h t‖ₑ ≤ ENNReal.ofReal C * ENNReal.ofReal (wallTailDensity p t) := by
        rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
        exact ENNReal.ofReal_le_ofReal (hh t ht)
      calc ‖h t‖ₑ ^ 2 ≤ (ENNReal.ofReal C * ENNReal.ofReal (wallTailDensity p t)) ^ 2 :=
            pow_le_pow_left' hstep 2
        _ = ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (wallTailDensity p t) ^ 2 := by
            rw [mul_pow, ← ENNReal.ofReal_pow hC]
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi hmaj) ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lintegral_sq_wallTailDensity_lt_top hp0)
  exact HTGeometry.lintegral_enorm_sq_lt_top_of_hardyBound hp hK hκ hbound hmeas hfin

end GaloisForLFunctions.RHTower
