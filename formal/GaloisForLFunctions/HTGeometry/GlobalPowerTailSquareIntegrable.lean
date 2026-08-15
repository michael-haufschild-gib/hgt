import GaloisForLFunctions.HTGeometry.PowerTailSquareIntegrable

/-!
# A global power tail past the square-root threshold has finite mass

A profile bounded on the whole line by `C(1+|x|)^{-p}` with `p > 1/2` has finite squared mass on
`ℝ`, not merely on a terminal ray.  The weight `(1+|x|)^{-2p}` is even, so the line integral is
twice the ray integral; on the unit window it is bounded by the window length, and past the unit
window it is dominated by `x^{-2p}`, whose exponent is below `−1` exactly when `p > 1/2`.

This is what puts the homogeneous component of a shifted-line solution in `L²(ℝ)`: the Gamma
propagator decays at `p = 1/2 + σ`, and `2p > 1` for every `σ > 0`.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The even power weight of the line. -/
def oneAddAbsWeight (s x : ℝ) : ℝ≥0∞ := ENNReal.ofReal ((1 + |x|) ^ (-s))

theorem oneAddAbsWeight_neg (s x : ℝ) : oneAddAbsWeight s (-x) = oneAddAbsWeight s x := by
  rw [oneAddAbsWeight, oneAddAbsWeight, abs_neg]

theorem measurable_oneAddAbsWeight (s : ℝ) : Measurable (oneAddAbsWeight s) := by
  unfold oneAddAbsWeight
  fun_prop

/-- The two half-lines carry the same mass. -/
theorem lintegral_oneAddAbsWeight_Iic (s : ℝ) :
    (∫⁻ x in Iic (0 : ℝ), oneAddAbsWeight s x)
      = ∫⁻ x in Ioi (0 : ℝ), oneAddAbsWeight s x := by
  have hind : (∫⁻ x in Iic (0 : ℝ), oneAddAbsWeight s x)
      = ∫⁻ x : ℝ, (Iic (0 : ℝ)).indicator (oneAddAbsWeight s) x :=
    (lintegral_indicator measurableSet_Iic _).symm
  have hrefl : (∫⁻ x : ℝ, (Iic (0 : ℝ)).indicator (oneAddAbsWeight s) x)
      = ∫⁻ x : ℝ, (Iic (0 : ℝ)).indicator (oneAddAbsWeight s) (-x) :=
    (lintegral_neg_eq_self _).symm
  have hswap : ∀ x : ℝ, (Iic (0 : ℝ)).indicator (oneAddAbsWeight s) (-x)
      = (Ici (0 : ℝ)).indicator (oneAddAbsWeight s) x := by
    intro x
    by_cases hx : (0 : ℝ) ≤ x
    · rw [Set.indicator_of_mem (by simpa using hx), Set.indicator_of_mem (by simpa using hx),
        oneAddAbsWeight_neg]
    · rw [not_le] at hx
      rw [Set.indicator_of_notMem (by simp; linarith),
        Set.indicator_of_notMem (by simp; linarith)]
  have hIci : (∫⁻ x : ℝ, (Ici (0 : ℝ)).indicator (oneAddAbsWeight s) x)
      = ∫⁻ x in Ici (0 : ℝ), oneAddAbsWeight s x :=
    lintegral_indicator measurableSet_Ici _
  have hae : (∫⁻ x in Ici (0 : ℝ), oneAddAbsWeight s x)
      = ∫⁻ x in Ioi (0 : ℝ), oneAddAbsWeight s x :=
    setLIntegral_congr Ioi_ae_eq_Ici.symm
  rw [hind, hrefl, lintegral_congr hswap, hIci, hae]

/-- **The line mass is finite past exponent one.** -/
theorem lintegral_oneAddAbsWeight_ne_top {s : ℝ} (hs : 1 < s) :
    (∫⁻ x : ℝ, oneAddAbsWeight s x) ≠ ⊤ := by
  have hray : (∫⁻ x in Ioi (0 : ℝ), oneAddAbsWeight s x) ≠ ⊤ := by
    have hsplit : Ioi (0 : ℝ) = Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) := by
      ext x
      simp only [mem_Ioi, mem_union, mem_Ioc]
      constructor
      · intro hx
        rcases le_or_gt x 1 with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr h
      · rintro (⟨hx, _⟩ | hx)
        · exact hx
        · linarith
    have hbox : (∫⁻ x in Ioc (0 : ℝ) 1, oneAddAbsWeight s x) ≠ ⊤ := by
      have hle : ∀ x ∈ Ioc (0 : ℝ) 1, oneAddAbsWeight s x ≤ 1 := by
        intro x hx
        rw [oneAddAbsWeight, ← ENNReal.ofReal_one]
        refine ENNReal.ofReal_le_ofReal ?_
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ (by linarith)
        have := abs_nonneg x
        linarith
      have hmass : (∫⁻ x in Ioc (0 : ℝ) 1, oneAddAbsWeight s x) ≤ volume (Ioc (0 : ℝ) 1) := by
        calc (∫⁻ x in Ioc (0 : ℝ) 1, oneAddAbsWeight s x)
            ≤ ∫⁻ _ in Ioc (0 : ℝ) 1, (1 : ℝ≥0∞) := setLIntegral_mono' measurableSet_Ioc hle
          _ = volume (Ioc (0 : ℝ) 1) := setLIntegral_one _
      refine ne_top_of_le_ne_top ?_ hmass
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    have htail : (∫⁻ x in Ioi (1 : ℝ), oneAddAbsWeight s x) ≠ ⊤ := by
      have hle : ∀ x ∈ Ioi (1 : ℝ), oneAddAbsWeight s x ≤ ENNReal.ofReal (x ^ (-s)) := by
        intro x hx
        have hx0 : (0 : ℝ) < x := lt_trans zero_lt_one hx
        rw [oneAddAbsWeight]
        refine ENNReal.ofReal_le_ofReal ?_
        refine Real.rpow_le_rpow_of_nonpos hx0 ?_ (by linarith)
        rw [abs_of_pos hx0]
        linarith
      have hint : IntegrableOn (fun x : ℝ => x ^ (-s)) (Ioi (1 : ℝ)) volume :=
        (integrableOn_Ioi_rpow_iff (by norm_num : (0 : ℝ) < 1)).mpr (by linarith)
      have hfin : (∫⁻ x in Ioi (1 : ℝ), ENNReal.ofReal (x ^ (-s))) ≠ ⊤ := by
        have hnn : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))), 0 ≤ x ^ (-s) := by
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
          exact Real.rpow_nonneg (le_of_lt (lt_trans zero_lt_one hx)) _
        rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
        exact ENNReal.ofReal_ne_top
      exact ne_top_of_le_ne_top hfin (setLIntegral_mono' measurableSet_Ioi hle)
    rw [hsplit]
    refine ne_top_of_le_ne_top ?_ (lintegral_union_le _ _ _)
    exact ENNReal.add_ne_top.mpr ⟨hbox, htail⟩
  have htotal : (∫⁻ x : ℝ, oneAddAbsWeight s x)
      = (∫⁻ x in Ioi (0 : ℝ), oneAddAbsWeight s x)
        + ∫⁻ x in (Ioi (0 : ℝ))ᶜ, oneAddAbsWeight s x :=
    (lintegral_add_compl _ measurableSet_Ioi).symm
  rw [htotal, compl_Ioi, lintegral_oneAddAbsWeight_Iic]
  exact ENNReal.add_ne_top.mpr ⟨hray, hray⟩

variable {A : Type*} [NormedAddCommGroup A]

/-- **A global power tail past the square-root threshold is square integrable on the line.** -/
theorem lintegral_sq_globalPowerTail_ne_top {f : ℝ → A} {C p : ℝ} (hp : 1 / 2 < p)
    (hf : ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ (-p)) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2) ≠ ⊤ := by
  have hmaj : ∀ x : ℝ, ‖f x‖ₑ ^ 2
      ≤ ENNReal.ofReal (C ^ 2) * oneAddAbsWeight (2 * p) x := by
    intro x
    have hx0 : (0 : ℝ) < 1 + |x| := by positivity
    have hbase := hf x
    have hnn : (0 : ℝ) ≤ C * (1 + |x|) ^ (-p) := le_trans (norm_nonneg _) hbase
    have hsq : ‖f x‖ ^ 2 ≤ C ^ 2 * (1 + |x|) ^ (-(2 * p)) := by
      refine (pow_le_pow_left₀ (norm_nonneg _) hbase 2).trans (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast ((1 + |x|) ^ (-p)) 2, ← Real.rpow_mul hx0.le]
      congr 2
      push_cast
      ring
    calc ‖f x‖ₑ ^ 2 = ENNReal.ofReal (‖f x‖ ^ 2) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (C ^ 2 * (1 + |x|) ^ (-(2 * p))) := ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal (C ^ 2) * oneAddAbsWeight (2 * p) x := by
          rw [oneAddAbsWeight, ← ENNReal.ofReal_mul (by positivity)]
  refine ne_top_of_le_ne_top ?_ (lintegral_mono hmaj)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (lintegral_oneAddAbsWeight_ne_top (by linarith))

/-- **The quantitative global power tail.**  The squared line mass is at most `C²` times the mass of
the weight, an explicit finite constant for `p > 1/2`. -/
theorem lintegral_sq_globalPowerTail_le {f : ℝ → A} {C p : ℝ}
    (hf : ∀ x : ℝ, ‖f x‖ ≤ C * (1 + |x|) ^ (-p)) :
    (∫⁻ x : ℝ, ‖f x‖ₑ ^ 2)
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ x : ℝ, oneAddAbsWeight (2 * p) x := by
  have hmaj : ∀ x : ℝ, ‖f x‖ₑ ^ 2
      ≤ ENNReal.ofReal (C ^ 2) * oneAddAbsWeight (2 * p) x := by
    intro x
    have hx0 : (0 : ℝ) < 1 + |x| := by positivity
    have hbase := hf x
    have hsq : ‖f x‖ ^ 2 ≤ C ^ 2 * (1 + |x|) ^ (-(2 * p)) := by
      refine (pow_le_pow_left₀ (norm_nonneg _) hbase 2).trans (le_of_eq ?_)
      rw [mul_pow, ← Real.rpow_natCast ((1 + |x|) ^ (-p)) 2, ← Real.rpow_mul hx0.le]
      congr 2
      push_cast
      ring
    calc ‖f x‖ₑ ^ 2 = ENNReal.ofReal (‖f x‖ ^ 2) := by
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      _ ≤ ENNReal.ofReal (C ^ 2 * (1 + |x|) ^ (-(2 * p))) := ENNReal.ofReal_le_ofReal hsq
      _ = ENNReal.ofReal (C ^ 2) * oneAddAbsWeight (2 * p) x := by
          rw [oneAddAbsWeight, ← ENNReal.ofReal_mul (by positivity)]
  refine le_trans (lintegral_mono hmaj) (le_of_eq ?_)
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end GaloisForLFunctions.HTGeometry
