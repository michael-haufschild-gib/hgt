import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.OddPrimeFreeGammaJumpCount

/-!
# Even correlation moments

The first lag moment records the mean and centered primitive mass.
The quadratic lag moment couples the mean to the quadratic position moment.
Both identities retain the even charges in the Gamma comparison.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.LatticeSectionTheory

private theorem even_source_position_zero {F : ℝ → ℝ} (he : ∀ x, F (-x) = F x) :
    (∫ x, x * F x) = 0 := by
  have h := integral_neg_eq_self (fun x => x * F x) volume
  have hf : (fun x => (-x) * F (-x)) = fun x => -(x * F x) := by
    funext x
    rw [he, neg_mul]
  rw [hf, integral_neg] at h
  linarith only [h]

private theorem weighted_correlation_integrable {F : ℝ → ℝ} (hF : Continuous F)
    {W : ℝ → ℝ} (hW : Continuous W) {a : ℝ}
    (hs : tsupport F ⊆ Icc (-a) a) :
    Integrable (fun p : ℝ × ℝ => W p.1 * F p.2 * F (p.2 + p.1))
      (volume.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ => W p.1 * F p.2 * F (p.2 + p.1)) := by
    fun_prop
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc (-2 * a) (2 * a) ×ˢ Icc (-a) a)
    (isCompact_Icc.prod isCompact_Icc)
  intro p hp
  by_cases hx : F p.2 = 0
  · simp only [hx, mul_zero, zero_mul]
  by_cases hy : F (p.2 + p.1) = 0
  · simp only [hy, mul_zero]
  have hxi : p.2 ∈ Icc (-a) a := by
    by_contra h
    exact hx (image_eq_zero_of_notMem_tsupport fun ht => h (hs ht))
  have hyi : p.2 + p.1 ∈ Icc (-a) a := by
    by_contra h
    exact hy (image_eq_zero_of_notMem_tsupport fun ht => h (hs ht))
  exact False.elim (hp (show p ∈ Icc (-2 * a) (2 * a) ×ˢ Icc (-a) a from
    ⟨⟨by linarith only [hxi.2, hyi.1], by linarith only [hxi.1, hyi.2]⟩, hxi⟩))

private theorem whole_second_correlation {F : ℝ → ℝ} (hF : Continuous F)
    (hcs : HasCompactSupport F) {a : ℝ} (hs : tsupport F ⊆ Icc (-a) a)
    (heven : ∀ x, F (-x) = F x) :
    (∫ t, t ^ 2 * autocorr F t) = 2 * (∫ x, F x) * (∫ x, x ^ 2 * F x) := by
  have hi0 : Integrable F := hF.integrable_of_hasCompactSupport hcs
  have hi1 : Integrable (fun x : ℝ => x * F x) :=
    (continuous_id.mul hF).integrable_of_hasCompactSupport hcs.mul_left
  have hi2 : Integrable (fun x : ℝ => x ^ 2 * F x) :=
    ((continuous_pow 2).mul hF).integrable_of_hasCompactSupport hcs.mul_left
  have hrow (x : ℝ) : (∫ t, t ^ 2 * F x * F (x + t)) =
      F x * ((∫ y, y ^ 2 * F y) - 2 * x * (∫ y, y * F y) +
        x ^ 2 * (∫ y, F y)) := by
    have hshift : (∫ t, t ^ 2 * F x * F (x + t)) =
        ∫ y, (y - x) ^ 2 * F x * F y := by
      calc
        _ = ∫ t, (x + t - x) ^ 2 * F x * F (x + t) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun t => by ring
        _ = _ := integral_add_left_eq_self (fun y : ℝ => (y - x) ^ 2 * F x * F y) x
    have he : (fun y => (y - x) ^ 2 * F x * F y) =
        fun y => F x * ((y ^ 2 * F y - (2 * x) * (y * F y)) + x ^ 2 * F y) := by
      funext y
      ring
    have hiSub : Integrable (fun y => y ^ 2 * F y - (2 * x) * (y * F y)) :=
      hi2.sub (hi1.const_mul (2 * x))
    have hiLast : Integrable (fun y => x ^ 2 * F y) := hi0.const_mul (x ^ 2)
    rw [hshift, he, integral_const_mul, integral_add hiSub hiLast,
      integral_sub (f := fun y => y ^ 2 * F y) (g := fun y => (2 * x) * (y * F y))
        hi2 (hi1.const_mul (2 * x)), integral_const_mul, integral_const_mul]
  have hl (t : ℝ) : t ^ 2 * autocorr F t = ∫ x, t ^ 2 * F x * F (x + t) := by
    unfold autocorr
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  simp_rw [hl]
  rw [integral_integral_swap (weighted_correlation_integrable hF (continuous_pow 2) hs)]
  simp_rw [hrow, even_source_position_zero heven, mul_zero, sub_zero]
  have he : (fun x => F x * ((∫ y, y ^ 2 * F y) + x ^ 2 * (∫ y, F y))) =
      fun x => (∫ y, y ^ 2 * F y) * F x + (∫ y, F y) * (x ^ 2 * F x) := by
    funext x
    ring
  rw [he, integral_add (hi0.const_mul _) (hi2.const_mul _),
    integral_const_mul, integral_const_mul]
  ring

/-- For an even source, the quadratic correlation moment is the product of two even moments. -/
theorem even_autocorr_second_moment {F : ℝ → ℝ} (hF : Continuous F)
    {a : ℝ} (hs : tsupport F ⊆ Icc (-a) a)
    (heven : ∀ x, F (-x) = F x) :
    (∫ t in Ioc (0 : ℝ) (2 * a), t ^ 2 * autocorr F t) =
      (∫ x, F x) * (∫ x, x ^ 2 * F x) := by
  have hcs : HasCompactSupport F :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hs
  have hwhole := whole_second_correlation hF hcs hs heven
  have heven : (fun t => |t| ^ 2 * autocorr F |t|) =
      fun t => t ^ 2 * autocorr F t := by
    funext t
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, neg_sq, autocorr_neg]
  have hhalf := integral_comp_abs (f := fun t => t ^ 2 * autocorr F t)
  rw [heven] at hhalf
  have hcut : (∫ t in Ioi (0 : ℝ), t ^ 2 * autocorr F t) =
      ∫ t in Ioc (0 : ℝ) (2 * a), t ^ 2 * autocorr F t := by
    have he : ∀ t ∈ Ioi (0 : ℝ), t ^ 2 * autocorr F t =
        (Iic (2 * a)).indicator (fun t => t ^ 2 * autocorr F t) t := by
      intro t _ht
      by_cases ht : t ≤ 2 * a
      · exact (Set.indicator_of_mem (show t ∈ Iic (2 * a) from ht)
          (fun t => t ^ 2 * autocorr F t)).symm
      · rw [Set.indicator_of_notMem (show t ∉ Iic (2 * a) from ht),
          autocorr_eq_zero_of_support hs (lt_of_not_ge ht), mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic,
      Ioi_inter_Iic]
  rw [hcut] at hhalf
  linarith only [hwhole, hhalf]

private theorem weighted_window_integral {F : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hs : tsupport F ⊆ Icc (-a) a) (K : ℝ → ℝ) :
    (∫ x in (-a)..a, K x * F x) = ∫ x, K x * F x := by
  rw [intervalIntegral.integral_of_le (by linarith only [ha] : -a ≤ a),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero]

private theorem whole_first_correlation {F : ℝ → ℝ} (hF : Continuous F)
    {a : ℝ} (ha : 0 < a)
    (hs : tsupport F ⊆ Icc (-a) a) (heven : ∀ x, F (-x) = F x) :
    (∫ t, |t| * autocorr F t) =
      a * (∫ x, F x) ^ 2 - 2 * ∫ x in (-a)..a, (∫ y in (0 : ℝ)..x, F y) ^ 2 := by
  let H : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..x, F y
  let P : ℝ → ℝ := fun x => ∫ y in (-a)..x, H y
  let m : ℝ := ∫ x, F x
  have hD (x : ℝ) : HasDerivAt H (F x) x := (hF.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hH : Continuous H := continuous_iff_continuousAt.mpr fun x => (hD x).continuousAt
  have hDP (x : ℝ) : HasDerivAt P (H x) x := (hH.integral_hasStrictDerivAt (-a) x).hasDerivAt
  have hP : Continuous P := continuous_iff_continuousAt.mpr fun x => (hDP x).continuousAt
  have hHo (x : ℝ) : H (-x) = -H x := by
    have h := intervalIntegral.integral_comp_neg (f := F) (a := (0 : ℝ)) (b := x)
    simp only [heven, neg_zero] at h
    dsimp [H]
    rw [intervalIntegral.integral_symm, ← h]
  have hHa : H a = m / 2 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hD x)
      (hF.intervalIntegrable (-a) a)
    have hm := weighted_window_integral ha hs (fun _ => (1 : ℝ))
    simp only [one_mul] at hm
    rw [hHo] at h
    dsimp [m]
    linarith only [h, hm]
  have hHna : H (-a) = -m / 2 := by rw [hHo, hHa]; ring
  have hPna : P (-a) = 0 := by simp [P]
  have hPa : P a = 0 := by
    have h := intervalIntegral.integral_comp_neg (f := H) (a := -a) (b := a)
    simp only [hHo, intervalIntegral.integral_neg, neg_neg] at h
    change (∫ x in (-a)..a, H x) = 0
    linarith only [h]
  have hpair : (∫ x in (-a)..a, F x * P x) = -(∫ x in (-a)..a, H x ^ 2) := by
    have hd (x : ℝ) : HasDerivAt (fun x => H x * P x) (F x * P x + H x ^ 2) x := by
      exact ((hD x).mul (hDP x)).congr_deriv (by ring)
    have hi1 : IntervalIntegrable (fun x => F x * P x) volume (-a) a :=
      (hF.mul hP).intervalIntegrable (-a) a
    have hi2 : IntervalIntegrable (fun x => H x ^ 2) volume (-a) a :=
      (hH.pow 2).intervalIntegrable (-a) a
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x) (hi1.add hi2)
    rw [intervalIntegral.integral_add hi1 hi2, hPa, hPna, mul_zero, mul_zero, sub_self] at h
    linarith only [h]
  have hrow (x : ℝ) (hx : x ∈ Icc (-a) a) :
      (∫ y, |y - x| * F y) = a * m + 2 * P x := by
    have hdL (y : ℝ) : HasDerivAt (fun y => (x - y) * H y + P y) ((x - y) * F y) y := by
      exact ((((hasDerivAt_id y).const_sub x).mul (hD y)).add (hDP y)).congr_deriv (by simp only [id_eq]; ring)
    have hdR (y : ℝ) : HasDerivAt (fun y => (y - x) * H y - P y) ((y - x) * F y) y := by
      exact ((((hasDerivAt_id y).sub_const x).mul (hD y)).sub (hDP y)).congr_deriv (by simp only [id_eq]; ring)
    have hL := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hdL y)
      (((continuous_const.sub continuous_id).mul hF).intervalIntegrable (-a) x)
    have hR := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hdR y)
      (((continuous_id.sub continuous_const).mul hF).intervalIntegrable x a)
    have hc : Continuous (fun y => |y - x| * F y) := by fun_prop
    rw [← weighted_window_integral ha hs (fun y => |y - x|),
      ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-a) x)
        (hc.intervalIntegrable x a)]
    have hleft : (∫ y in (-a)..x, |y - x| * F y) = ∫ y in (-a)..x, (x - y) * F y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hx.1] at hy
      dsimp only
      rw [abs_of_nonpos (sub_nonpos.mpr hy.2)]
      ring
    have hright : (∫ y in x..a, |y - x| * F y) = ∫ y in x..a, (y - x) * F y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [uIcc_of_le hx.2] at hy
      dsimp only
      rw [abs_of_nonneg (sub_nonneg.mpr hy.1)]
    rw [hleft, hright, hL, hR, hPna, hPa, hHa, hHna]
    ring
  have hl (t : ℝ) : |t| * autocorr F t = ∫ x, |t| * F x * F (x + t) := by
    unfold autocorr
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  have hshift (x : ℝ) : (∫ t, |t| * F x * F (x + t)) = F x * ∫ y, |y - x| * F y := by
    have he : (∫ t, |t| * F x * F (x + t)) = ∫ y, |y - x| * F x * F y := by
      calc
        _ = ∫ t, |x + t - x| * F x * F (x + t) := by
          simp only [add_sub_cancel_left]
        _ = _ := integral_add_left_eq_self (fun y : ℝ => |y - x| * F x * F y) x
    rw [he, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun y => by ring
  simp_rw [hl]
  rw [integral_integral_swap (weighted_correlation_integrable hF continuous_abs hs)]
  simp_rw [hshift]
  have hcut : (∫ x in (-a)..a, F x * ∫ y, |y - x| * F y) =
      ∫ x, F x * ∫ y, |y - x| * F y := by
    simpa only [mul_comm] using weighted_window_integral ha hs (fun x => ∫ y, |y - x| * F y)
  rw [← hcut]
  have he : (∫ x in (-a)..a, F x * ∫ y, |y - x| * F y) =
      ∫ x in (-a)..a, a * m * F x + 2 * (F x * P x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by linarith only [ha] : -a ≤ a)] at hx
    dsimp only
    rw [hrow x hx]
    ring
  rw [he, intervalIntegral.integral_add (f := fun x => a * m * F x)
    (g := fun x => 2 * (F x * P x))
    ((continuous_const.mul hF).intervalIntegrable (-a) a)
    ((continuous_const.mul (hF.mul hP)).intervalIntegrable (-a) a),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hpair]
  have hm := weighted_window_integral ha hs (fun _ => (1 : ℝ))
  simp only [one_mul] at hm
  rw [hm]
  dsimp [H, m]
  ring

/-- The first even correlation moment retains the mean and the centered primitive mass. -/
theorem even_autocorr_first_moment {F : ℝ → ℝ} (hF : Continuous F)
    {a : ℝ} (ha : 0 < a)
    (hs : tsupport F ⊆ Icc (-a) a) (heven : ∀ x, F (-x) = F x) :
    (∫ t in Ioc (0 : ℝ) (2 * a), t * autocorr F t) =
      a * (∫ x, F x) ^ 2 / 2 - ∫ x in (-a)..a, (∫ y in (0 : ℝ)..x, F y) ^ 2 := by
  have hwhole := whole_first_correlation hF ha hs heven
  have habs : (fun t => |t| * autocorr F |t|) = fun t => |t| * autocorr F t := by
    funext t
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, autocorr_neg]
  have hhalf := integral_comp_abs (f := fun t => t * autocorr F t)
  rw [habs] at hhalf
  have hcut : (∫ t in Ioi (0 : ℝ), t * autocorr F t) =
      ∫ t in Ioc (0 : ℝ) (2 * a), t * autocorr F t := by
    have he : ∀ t ∈ Ioi (0 : ℝ), t * autocorr F t =
        (Iic (2 * a)).indicator (fun t => t * autocorr F t) t := by
      intro t _
      by_cases ht : t ≤ 2 * a
      · exact (Set.indicator_of_mem (show t ∈ Iic (2 * a) from ht)
          (fun t => t * autocorr F t)).symm
      · rw [Set.indicator_of_notMem (show t ∉ Iic (2 * a) from ht),
          autocorr_eq_zero_of_support hs (lt_of_not_ge ht), mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic,
      Ioi_inter_Iic]
  rw [hcut] at hhalf
  linarith only [hwhole, hhalf]

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.even_autocorr_second_moment
#print axioms GaloisForLFunctions.LatticeSectionTheory.even_autocorr_first_moment
