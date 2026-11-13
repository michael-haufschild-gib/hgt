import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventKernels

/-!
# Size of the resolvent kernels and the difference kernels

* `k_s(u) ≤ C u^{−s}` and `k_s(u) ≤ C u^{−¼}` for `u > 0` (`exists_resKernel_le_rpow_neg`,
  `exists_resKernel_le_rpow_quarter`): from `F_s(w) ≤ w^{−½}(1 + w)^{−s}`.
* For `½ < a ≤ s` the density difference `G = F_a − F_s` is nonnegative and bounded by
  `C (1 + w)^{−a−½}` (`greenDiff_le`): near `0` the logarithmic singularities cancel, since
  `ρ^{2a−1} − ρ^{2s−1} ≤ max(1, 2(s − a)) (1 − ρ)` and `1 − ρ(w) ≤ √w`.
* The **difference kernel** `D_{a,s}(u) = (1/4π) ∫_{t>0} G(u⁺ + t) t^{−½} dt` is continuous on `ℝ`
  (`continuous_diffKernel`), satisfies `D_{a,s} + k_s = k_a` on `u > 0` (`diffKernel_add_resKernel`),
  and `𝒜D_{a,s}(τ) = e^{−(a−½)|τ|}/(2a − 1) − e^{−(s−½)|τ|}/(2s − 1)` (`abelL_diffKernel`).
-/

open MeasureTheory Set Filter Real
open scoped ENNReal

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

/-- `t^{−α}(1 + t)^{−β}` is integrable on `(0, ∞)` when `0 ≤ α < 1 < α + β`. -/
theorem integrableOn_rpow_mul_one_add_rpow {α β : ℝ} (hα : α < 1)
    (hαβ : 1 < α + β) : IntegrableOn (fun t : ℝ => t ^ (-α) * (1 + t) ^ (-β)) (Ioi 0) := by
  have hβ : 0 < β := by linarith
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-α) * (1 + t) ^ (-β)) (Ioi 0) :=
    (continuousOn_id.rpow_const fun t ht => Or.inl (ne_of_gt ht)).mul
      ((continuousOn_const.add continuousOn_id).rpow_const fun t ht =>
        Or.inl (ne_of_gt (show (0:ℝ) < 1 + t by have : (0:ℝ) < t := ht; linarith)))
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
    refine h1.mono' ((hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := ht.1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (1 + t) ^ (-β) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
    calc t ^ (-α) * (1 + t) ^ (-β) ≤ t ^ (-α) * 1 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = t ^ (-α) := mul_one _
  · have h2 : IntegrableOn (fun t : ℝ => t ^ (-(α + β))) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine h2.mono' ((hcont.mono fun t (ht : 1 < t) => show (0:ℝ) < t by linarith)
      |>.aestronglyMeasurable measurableSet_Ioi) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : 0 < t := lt_trans one_pos ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), neg_add, Real.rpow_add ht0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ht0 (by linarith) (by linarith))
      (by positivity)

theorem lintegral_rpow_mul_one_add_rpow_lt_top {α β : ℝ} (hα : α < 1)
    (hαβ : 1 < α + β) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-α) * (1 + t) ^ (-β)) < ∞ :=
  (integrableOn_rpow_mul_one_add_rpow hα hαβ).lintegral_lt_top

/-- Shifting a half-line integral to `(0, ∞)`. -/
theorem lintegral_indicator_Ioi_eq (u : ℝ) (g : ℝ → ℝ≥0∞) :
    ∫⁻ w : ℝ, (Ioi u).indicator g w = ∫⁻ t in Ioi (0 : ℝ), g (u + t) := by
  rw [← lintegral_add_left_eq_self _ u, ← lintegral_indicator measurableSet_Ioi]
  refine lintegral_congr fun t => ?_
  simp only [indicator_apply, mem_Ioi, lt_add_iff_pos_right]

theorem resKernel_eq_lintegral_Ioi (s u : ℝ) :
    resKernel s u = ENNReal.ofReal (1 / (4 * π)) *
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (greenDensity s (u + t) * (Real.sqrt t)⁻¹) := by
  rw [resKernel, lintegral_indicator_Ioi_eq]
  congr 1
  refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [add_sub_cancel_left]

/-- `F_s(w) ≤ w^{−(s+½)}`. -/
theorem greenDensity_le_rpow {s : ℝ} (hs : 1 / 2 < s) {w : ℝ} (hw : 0 < w) :
    greenDensity s w ≤ w ^ (-(s + 1 / 2)) := by
  refine (greenDensity_le hs hw).trans ?_
  rw [show -(s + 1 / 2) = -(1 / 2 : ℝ) + -s by ring, Real.rpow_add hw]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hw (by linarith) (by linarith))
    (by positivity)

/-- **Decay.**  `k_s(u) ≤ C u^{−s}` for `u > 0`. -/
theorem exists_resKernel_le_rpow_neg {s : ℝ} (hs : 1 / 2 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u → resKernel s u ≤ ENNReal.ofReal (C * u ^ (-s)) := by
  set I : ℝ := ∫ r in Ioi (0 : ℝ), r ^ (-(1 / 2 : ℝ)) * (1 + r) ^ (-(s + 1 / 2))
  have hI : IntegrableOn (fun r : ℝ => r ^ (-(1 / 2 : ℝ)) * (1 + r) ^ (-(s + 1 / 2))) (Ioi 0) :=
    integrableOn_rpow_mul_one_add_rpow (by norm_num) (by linarith)
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun r hr => by
    have : (0:ℝ) < r := hr; positivity
  refine ⟨1 / (4 * π) * I, by positivity, fun u hu => ?_⟩
  rw [resKernel_eq_lintegral_Ioi]
  have hb : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (greenDensity s (u + t) * (Real.sqrt t)⁻¹) ≤
      ENNReal.ofReal ((u + t) ^ (-(s + 1 / 2)) * t ^ (-(1 / 2 : ℝ))) := by
    intro t ht
    have ht0 : 0 < t := ht
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht0.le]
    exact mul_le_mul_of_nonneg_right (greenDensity_le_rpow hs (by linarith)) (by positivity)
  have hscale : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((u + t) ^ (-(s + 1 / 2)) * t ^ (-(1 / 2 : ℝ))) =
      ENNReal.ofReal (u ^ (-s)) * ∫⁻ r in Ioi (0 : ℝ),
        ENNReal.ofReal (r ^ (-(1 / 2 : ℝ)) * (1 + r) ^ (-(s + 1 / 2))) := by
    rw [← lintegral_indicator measurableSet_Ioi,
      lintegral_eq_ofReal_mul_lintegral_comp_mul _ hu, ← lintegral_indicator measurableSet_Ioi,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun r => ?_
    simp only [indicator_apply, mem_Ioi]
    by_cases hr : 0 < r
    · have hur : 0 < u * r := mul_pos hu hr
      rw [if_pos hur, if_pos hr, ← ENNReal.ofReal_mul hu.le, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show u + u * r = u * (1 + r) by ring, Real.mul_rpow hu.le (by linarith),
        Real.mul_rpow hu.le hr.le]
      have h1 : u * (u ^ (-(s + 1 / 2)) * u ^ (-(1 / 2 : ℝ))) = u ^ (-s) := by
        rw [← Real.rpow_add hu, ← Real.rpow_one_add' hu.le (by linarith)]
        congr 1; ring
      calc u * (u ^ (-(s + 1 / 2)) * (1 + r) ^ (-(s + 1 / 2)) * (u ^ (-(1 / 2 : ℝ)) *
            r ^ (-(1 / 2 : ℝ))))
          = (u * (u ^ (-(s + 1 / 2)) * u ^ (-(1 / 2 : ℝ)))) *
              (r ^ (-(1 / 2 : ℝ)) * (1 + r) ^ (-(s + 1 / 2))) := by ring
        _ = _ := by rw [h1]
    · have hur : ¬ 0 < u * r := fun h => hr (pos_of_mul_pos_right h hu.le)
      rw [if_neg hur, if_neg hr]; simp
  calc ENNReal.ofReal (1 / (4 * π)) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (greenDensity s (u + t) * (Real.sqrt t)⁻¹)
      ≤ ENNReal.ofReal (1 / (4 * π)) * ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal ((u + t) ^ (-(s + 1 / 2)) * t ^ (-(1 / 2 : ℝ))) := by
        exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi hb) _
    _ = ENNReal.ofReal (1 / (4 * π)) * (ENNReal.ofReal (u ^ (-s)) * ENNReal.ofReal I) := by
        rw [hscale, ofReal_integral_eq_lintegral_ofReal hI
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => by
            have : (0:ℝ) < r := hr; positivity))]
    _ = ENNReal.ofReal (1 / (4 * π) * I * u ^ (-s)) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

/-- **Local size.**  `k_s(u) ≤ C u^{−¼}` for `u > 0`. -/
theorem exists_resKernel_le_rpow_quarter {s : ℝ} (hs : 1 / 2 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, 0 < u → resKernel s u ≤ ENNReal.ofReal (C * u ^ (-(1 / 4 : ℝ))) := by
  set I : ℝ := ∫ t in Ioi (0 : ℝ), t ^ (-(3 / 4 : ℝ)) * (1 + t) ^ (-s)
  have hI : IntegrableOn (fun t : ℝ => t ^ (-(3 / 4 : ℝ)) * (1 + t) ^ (-s)) (Ioi 0) :=
    integrableOn_rpow_mul_one_add_rpow (by norm_num) (by linarith)
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have : (0:ℝ) < t := ht; positivity
  refine ⟨1 / (4 * π) * I, by positivity, fun u hu => ?_⟩
  rw [resKernel_eq_lintegral_Ioi]
  have hb : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal (greenDensity s (u + t) * (Real.sqrt t)⁻¹) ≤
      ENNReal.ofReal (u ^ (-(1 / 4 : ℝ))) * ENNReal.ofReal (t ^ (-(3 / 4 : ℝ)) * (1 + t) ^ (-s)) := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := greenDensity_le hs (show 0 < u + t by linarith)
    have h2 : (u + t) ^ (-(1 / 2 : ℝ)) ≤ u ^ (-(1 / 4 : ℝ)) * t ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.mul_rpow hu.le ht0.le, show (-(1 / 2 : ℝ)) = 2 * (-(1 / 4 : ℝ)) by norm_num,
        Real.rpow_mul (by linarith)]
      refine Real.rpow_le_rpow_of_nonpos (mul_pos hu ht0) ?_ (by norm_num)
      rw [Real.rpow_two]; nlinarith [sq_nonneg (u - t)]
    have h3 : (1 + (u + t)) ^ (-s) ≤ (1 + t) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
    have h4 : (Real.sqrt t)⁻¹ = t ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht0.le]
    rw [h4]
    calc greenDensity s (u + t) * t ^ (-(1 / 2 : ℝ))
        ≤ (u + t) ^ (-(1 / 2 : ℝ)) * (1 + (u + t)) ^ (-s) * t ^ (-(1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (u ^ (-(1 / 4 : ℝ)) * t ^ (-(1 / 4 : ℝ))) * (1 + t) ^ (-s) * t ^ (-(1 / 2 : ℝ)) := by
          gcongr
      _ = u ^ (-(1 / 4 : ℝ)) * (t ^ (-(3 / 4 : ℝ)) * (1 + t) ^ (-s)) := by
          rw [show t ^ (-(3 / 4 : ℝ)) = t ^ (-(1 / 4 : ℝ)) * t ^ (-(1 / 2 : ℝ)) by
            rw [← Real.rpow_add ht0]; norm_num]
          ring
  calc ENNReal.ofReal (1 / (4 * π)) *
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (greenDensity s (u + t) * (Real.sqrt t)⁻¹)
      ≤ ENNReal.ofReal (1 / (4 * π)) * ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (-(1 / 4 : ℝ))) * ENNReal.ofReal (t ^ (-(3 / 4 : ℝ)) * (1 + t) ^ (-s)) := by
        exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioi hb) _
    _ = ENNReal.ofReal (1 / (4 * π)) * (ENNReal.ofReal (u ^ (-(1 / 4 : ℝ))) * ENNReal.ofReal I) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ofReal_integral_eq_lintegral_ofReal hI
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => by
            have : (0:ℝ) < r := hr; positivity))]
    _ = ENNReal.ofReal (1 / (4 * π) * I * u ^ (-(1 / 4 : ℝ))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

theorem resKernel_lt_top {s : ℝ} (hs : 1 / 2 < s) {u : ℝ} (hu : 0 < u) : resKernel s u < ∞ := by
  obtain ⟨C, -, hC⟩ := exists_resKernel_le_rpow_neg hs
  exact (hC u hu).trans_lt ENNReal.ofReal_lt_top

/-! ### The difference kernels -/

/-- The density difference `G_{a,s} = F_a − F_s`. -/
def greenDiff (a s w : ℝ) : ℝ := greenDensity a w - greenDensity s w

theorem rho_le_one {w : ℝ} (hw : 0 ≤ w) : rho w ≤ 1 := by
  rw [rho_eq_inv hw]
  exact inv_le_one_of_one_le₀ (le_add_of_le_of_nonneg (Real.one_le_sqrt.mpr (by linarith))
    (Real.sqrt_nonneg _))

theorem greenDiff_nonneg {a s : ℝ} (has : a ≤ s) {w : ℝ} (hw : 0 ≤ w) : 0 ≤ greenDiff a s w := by
  rw [greenDiff, sub_nonneg, greenDensity, greenDensity]
  exact div_le_div_of_nonneg_right (Real.rpow_le_rpow_of_exponent_ge (rho_pos hw) (rho_le_one hw)
    (by linarith)) (Real.sqrt_nonneg _)

theorem one_sub_rho_le {w : ℝ} (hw : 0 ≤ w) : 1 - rho w ≤ Real.sqrt w := by
  have : 1 ≤ Real.sqrt (1 + w) := Real.one_le_sqrt.mpr (by linarith)
  rw [rho]; linarith

/-- `1 − x^m ≤ max(1, m)(1 − x)` on `0 < x ≤ 1`, `m ≥ 0`. -/
theorem one_sub_rpow_le {x m : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    1 - x ^ m ≤ max 1 m * (1 - x) := by
  rcases le_total m 1 with h | h
  · have : x ≤ x ^ m := by
      have := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 h
      rwa [Real.rpow_one] at this
    have h1 : (1 : ℝ) ≤ max 1 m := le_max_left _ _
    nlinarith
  · have hb := one_add_mul_self_le_rpow_one_add (s := x - 1) (by linarith) h
    rw [show 1 + (x - 1) = x by ring] at hb
    rw [max_eq_right h]
    nlinarith

/-- `G_{a,s}(w) ≤ max(1, 2(s − a))` for `w > 0`: the singularities of `F_a` and `F_s` cancel. -/
theorem greenDiff_le_const {a s : ℝ} (ha : 1 / 2 < a) (has : a ≤ s) {w : ℝ} (hw : 0 < w) :
    greenDiff a s w ≤ max 1 (2 * (s - a)) := by
  have hρ0 := rho_pos hw.le
  have hρ1 := rho_le_one hw.le
  have hsplit : rho w ^ (2 * s - 1) = rho w ^ (2 * a - 1) * rho w ^ (2 * (s - a)) := by
    rw [← Real.rpow_add hρ0]; congr 1; ring
  have hnum : rho w ^ (2 * a - 1) - rho w ^ (2 * s - 1) ≤ max 1 (2 * (s - a)) * Real.sqrt w := by
    rw [hsplit]
    have h1 : rho w ^ (2 * a - 1) ≤ 1 := Real.rpow_le_one hρ0.le hρ1 (by linarith)
    have h2 := one_sub_rpow_le hρ0 hρ1 (m := 2 * (s - a))
    have h3 := one_sub_rho_le hw.le
    have h4 : 0 ≤ 1 - rho w ^ (2 * (s - a)) := by
      have := Real.rpow_le_one hρ0.le hρ1 (show 0 ≤ 2 * (s - a) by linarith); linarith
    have h5 : 0 ≤ rho w ^ (2 * a - 1) := Real.rpow_nonneg hρ0.le _
    calc rho w ^ (2 * a - 1) - rho w ^ (2 * a - 1) * rho w ^ (2 * (s - a))
        = rho w ^ (2 * a - 1) * (1 - rho w ^ (2 * (s - a))) := by ring
      _ ≤ 1 * (1 - rho w ^ (2 * (s - a))) := mul_le_mul_of_nonneg_right h1 h4
      _ ≤ max 1 (2 * (s - a)) * (1 - rho w) := by rw [one_mul]; exact h2
      _ ≤ max 1 (2 * (s - a)) * Real.sqrt w :=
          mul_le_mul_of_nonneg_left h3 (le_trans zero_le_one (le_max_left _ _))
  have hden : Real.sqrt w ≤ Real.sqrt (w * (1 + w)) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw
  rw [greenDiff, greenDensity, greenDensity, ← sub_div, div_le_iff₀ (lt_of_lt_of_le hsw hden)]
  calc rho w ^ (2 * a - 1) - rho w ^ (2 * s - 1) ≤ max 1 (2 * (s - a)) * Real.sqrt w := hnum
    _ ≤ max 1 (2 * (s - a)) * Real.sqrt (w * (1 + w)) :=
        mul_le_mul_of_nonneg_left hden (le_trans zero_le_one (le_max_left _ _))

/-- `G_{a,s}(w) ≤ C (1 + w)^{−(a+½)}` for `w > 0`. -/
theorem exists_greenDiff_le {a s : ℝ} (ha : 1 / 2 < a) (has : a ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ, 0 < w → greenDiff a s w ≤ C * (1 + w) ^ (-(a + 1 / 2)) := by
  set M := max 1 (2 * (s - a))
  refine ⟨M * 2 ^ (a + 1 / 2) + Real.sqrt 2, by positivity, fun w hw => ?_⟩
  have hw1 : 0 < 1 + w := by linarith
  have hpos : 0 < (1 + w) ^ (-(a + 1 / 2)) := Real.rpow_pos_of_pos hw1 _
  rcases le_total w 1 with h | h
  · have hb : 2 ^ (-(a + 1 / 2)) ≤ (1 + w) ^ (-(a + 1 / 2)) :=
      Real.rpow_le_rpow_of_nonpos hw1 (by linarith) (by linarith)
    have hM : 0 ≤ M := le_trans zero_le_one (le_max_left _ _)
    calc greenDiff a s w ≤ M := greenDiff_le_const ha has hw
      _ = M * 2 ^ (a + 1 / 2) * 2 ^ (-(a + 1 / 2)) := by
          rw [mul_assoc, ← Real.rpow_add (by norm_num)]; simp
      _ ≤ M * 2 ^ (a + 1 / 2) * (1 + w) ^ (-(a + 1 / 2)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ ≤ (M * 2 ^ (a + 1 / 2) + Real.sqrt 2) * (1 + w) ^ (-(a + 1 / 2)) := by
          nlinarith [Real.sqrt_nonneg 2]
  · have h1 : greenDiff a s w ≤ greenDensity a w := by
      have := greenDensity_nonneg s hw.le; rw [greenDiff]; linarith
    have h2 := greenDensity_le ha hw
    have h3 : w ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt 2 * (1 + w) ^ (-(1 / 2 : ℝ)) := by
      have h2w : 1 + w ≤ 2 * w := by linarith
      have := Real.rpow_le_rpow_of_nonpos hw1 h2w (show (-(1 / 2 : ℝ)) ≤ 0 by norm_num)
      rw [Real.mul_rpow (by norm_num) hw.le] at this
      have h4 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt 2 = 1 := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num)]; norm_num
      have h5 : 0 < (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
      calc w ^ (-(1 / 2 : ℝ)) = (2 : ℝ) ^ (-(1 / 2 : ℝ)) * Real.sqrt 2 * w ^ (-(1 / 2 : ℝ)) := by
            rw [h4, one_mul]
        _ = Real.sqrt 2 * ((2 : ℝ) ^ (-(1 / 2 : ℝ)) * w ^ (-(1 / 2 : ℝ))) := by ring
        _ ≤ Real.sqrt 2 * (1 + w) ^ (-(1 / 2 : ℝ)) :=
            mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
    calc greenDiff a s w ≤ w ^ (-(1 / 2 : ℝ)) * (1 + w) ^ (-a) := h1.trans h2
      _ ≤ (Real.sqrt 2 * (1 + w) ^ (-(1 / 2 : ℝ))) * (1 + w) ^ (-a) :=
          mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = Real.sqrt 2 * (1 + w) ^ (-(a + 1 / 2)) := by
          rw [mul_assoc, ← Real.rpow_add hw1]; congr 2; ring
      _ ≤ (M * 2 ^ (a + 1 / 2) + Real.sqrt 2) * (1 + w) ^ (-(a + 1 / 2)) := by
          have hM : 0 ≤ M * 2 ^ (a + 1 / 2) :=
            mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (by positivity)
          nlinarith

theorem continuousOn_greenDensity {s : ℝ} (hs : 1 / 2 < s) :
    ContinuousOn (greenDensity s) (Ioi 0) := by
  refine ((Real.continuous_rpow_const (by linarith)).comp continuous_rho).continuousOn.div
    (by fun_prop) fun w hw => ?_
  have : (0:ℝ) < w := hw
  exact (Real.sqrt_pos.mpr (by positivity)).ne'

/-- The **difference kernel** `D_{a,s}(u) = (1/4π) ∫_{t>0} G_{a,s}(u⁺ + t) t^{−½} dt`. -/
def diffKernel (a s u : ℝ) : ℝ :=
  1 / (4 * π) * ∫ t in Ioi (0 : ℝ), greenDiff a s (max u 0 + t) * (Real.sqrt t)⁻¹

section diff

variable {a s : ℝ} (ha : 1 / 2 < a) (has : a ≤ s)
include ha has

theorem exists_diffKernel_bound : ∃ B : ℝ → ℝ, Integrable B (volume.restrict (Ioi 0)) ∧
    ∀ u t : ℝ, 0 < t → ‖greenDiff a s (max u 0 + t) * (Real.sqrt t)⁻¹‖ ≤ B t := by
  obtain ⟨C, hC0, hC⟩ := exists_greenDiff_le ha has
  refine ⟨fun t => C * (t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-(a + 1 / 2))),
    (integrableOn_rpow_mul_one_add_rpow (by norm_num) (by linarith)).const_mul C,
    fun u t ht => ?_⟩
  have hw : 0 < max u 0 + t := by have := le_max_right u 0; linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (greenDiff_nonneg has hw.le) (by positivity)),
    show (Real.sqrt t)⁻¹ = t ^ (-(1 / 2 : ℝ)) by rw [Real.sqrt_eq_rpow, ← Real.rpow_neg ht.le]]
  have h1 := hC _ hw
  have h2 : (1 + (max u 0 + t)) ^ (-(a + 1 / 2)) ≤ (1 + t) ^ (-(a + 1 / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by have := le_max_right u 0; linarith) (by linarith)
  calc greenDiff a s (max u 0 + t) * t ^ (-(1 / 2 : ℝ))
      ≤ C * (1 + (max u 0 + t)) ^ (-(a + 1 / 2)) * t ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ C * (1 + t) ^ (-(a + 1 / 2)) * t ^ (-(1 / 2 : ℝ)) := by gcongr
    _ = C * (t ^ (-(1 / 2 : ℝ)) * (1 + t) ^ (-(a + 1 / 2))) := by ring

theorem integrableOn_greenDiff_shift (u : ℝ) :
    IntegrableOn (fun t => greenDiff a s (max u 0 + t) * (Real.sqrt t)⁻¹) (Ioi 0) := by
  obtain ⟨B, hB, hBle⟩ := exists_diffKernel_bound ha has
  refine hB.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => hBle u t ht))
  exact (((measurable_greenDensity a).sub (measurable_greenDensity s)).comp
    (measurable_const.add measurable_id)).mul (by fun_prop) |>.aestronglyMeasurable

/-- The difference kernel is continuous. -/
theorem continuous_diffKernel : Continuous (diffKernel a s) := by
  obtain ⟨B, hB, hBle⟩ := exists_diffKernel_bound ha has
  refine continuous_const.mul (continuous_of_dominated (fun u => ?_) (fun u => ?_) hB ?_)
  · exact (((measurable_greenDensity a).sub (measurable_greenDensity s)).comp
      (measurable_const.add measurable_id)).mul (by fun_prop) |>.aestronglyMeasurable
  · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => hBle u t ht)
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht0 : (0:ℝ) < t := ht
    have hG : ContinuousOn (greenDiff a s) (Ioi 0) :=
      (continuousOn_greenDensity ha).sub (continuousOn_greenDensity (by linarith))
    refine Continuous.mul ?_ continuous_const
    refine hG.comp_continuous (by fun_prop) fun u => ?_
    show (0:ℝ) < max u 0 + t
    have := le_max_right u 0; linarith

omit ha in
theorem diffKernel_nonneg (u : ℝ) : 0 ≤ diffKernel a s u :=
  mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun t ht => by
    have ht0 : (0:ℝ) < t := ht
    exact mul_nonneg (greenDiff_nonneg has (by have := le_max_right u 0; linarith)) (by positivity))

/-- `D_{a,s} + k_s = k_a` on `u > 0`. -/
theorem diffKernel_add_resKernel {u : ℝ} (hu : 0 < u) :
    ENNReal.ofReal (diffKernel a s u) + resKernel s u = resKernel a u := by
  have hmax : max u 0 = u := max_eq_left hu.le
  have hint : IntegrableOn (fun t => greenDiff a s (u + t) * (Real.sqrt t)⁻¹) (Ioi 0) := by
    have := integrableOn_greenDiff_shift ha has u
    rwa [hmax] at this
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] fun t => greenDiff a s (u + t) * (Real.sqrt t)⁻¹ :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => by
      have ht0 : (0:ℝ) < t := ht
      exact mul_nonneg (greenDiff_nonneg has (by linarith)) (by positivity))
  rw [diffKernel, hmax, ENNReal.ofReal_mul (by positivity),
    ofReal_integral_eq_lintegral_ofReal hint hnn, resKernel_eq_lintegral_Ioi, resKernel_eq_lintegral_Ioi, ← mul_add, ← lintegral_add_left' ?_]
  · congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (0:ℝ) < t := ht
    have hw : 0 < u + t := by linarith
    rw [← ENNReal.ofReal_add (mul_nonneg (greenDiff_nonneg has hw.le) (by positivity))
      (mul_nonneg (greenDensity_nonneg s hw.le) (by positivity))]
    congr 1
    rw [greenDiff]; ring
  · exact (ENNReal.measurable_ofReal.comp ((((measurable_greenDensity a).sub
      (measurable_greenDensity s)).comp (measurable_const.add measurable_id)).mul
      (by fun_prop))).aemeasurable

theorem ofReal_diffKernel_le {u : ℝ} (hu : 0 < u) :
    ENNReal.ofReal (diffKernel a s u) ≤ resKernel a u := by
  rw [← diffKernel_add_resKernel ha has hu]; exact le_self_add

/-- **The Abel transform of the difference kernel.** -/
theorem abelL_diffKernel (τ : ℝ) :
    abelL (fun u => ENNReal.ofReal (diffKernel a s u)) τ =
      ENNReal.ofReal (Real.exp (-((a - 1 / 2) * |τ|)) / (2 * a - 1) -
        Real.exp (-((s - 1 / 2) * |τ|)) / (2 * s - 1)) := by
  have hs : 1 / 2 < s := lt_of_lt_of_le ha has
  have hsum : abelL (fun u => ENNReal.ofReal (diffKernel a s u)) τ + abelL (resKernel s) τ =
      abelL (resKernel a) τ := by
    rw [abelL, abelL, abelL, ← lintegral_add_left' ?_]
    · refine lintegral_congr_ae ?_
      have hne : ∀ᵐ η : ℝ, η ≠ 0 := by
        rw [ae_iff]; simp only [ne_eq, not_not, setOf_eq_eq_singleton]; exact Real.volume_singleton
      filter_upwards [hne] with η hη
      exact diffKernel_add_resKernel ha has (by positivity)
    · exact (ENNReal.measurable_ofReal.comp ((continuous_diffKernel ha has).measurable.comp
        (by fun_prop))).aemeasurable
  rw [abelL_resKernel ha, abelL_resKernel hs] at hsum
  have hfin : ENNReal.ofReal (Real.exp (-((s - 1 / 2) * |τ|)) / (2 * s - 1)) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  rw [ENNReal.eq_sub_of_add_eq hfin hsum, ← ENNReal.ofReal_sub _
    (div_nonneg (Real.exp_pos _).le (by linarith))]

end diff

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
