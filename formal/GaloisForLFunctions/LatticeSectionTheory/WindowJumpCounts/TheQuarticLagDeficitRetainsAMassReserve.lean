import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.EvenCorrelationMoments
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.RegionalLogarithmicChargedGaps

/-!
# A mass reserve in the quartic lag deficit

The fourth correlation moment depends only on the first five position moments.
Legendre orthogonality and rational square completions bound it by `17/10`
times mass on the unit window, or `1/10` for odd sources. Scaling retains
explicit positive quartic reserves at every aperture.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.LatticeSectionTheory
open SelectivePositivityAndThresholdLaws

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

private theorem whole_fourth_correlation {F : ℝ → ℝ} (hF : Continuous F)
    {a : ℝ} (hs : tsupport F ⊆ Icc (-a) a) :
    let m := fun n : ℕ => ∫ x, x ^ n * F x
    (∫ t, t ^ 4 * autocorr F t) = 2 * m 0 * m 4 - 8 * m 1 * m 3 + 6 * m 2 ^ 2 := by
  intro m
  have hcs : HasCompactSupport F :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hs
  have hi (n : ℕ) : Integrable (fun x : ℝ => x ^ n * F x) :=
    ((continuous_pow n).mul hF).integrable_of_hasCompactSupport hcs.mul_left
  have hrow (x : ℝ) : (∫ t, t ^ 4 * F x * F (x + t)) =
      F x * (m 4 - (4 * x) * m 3 + (6 * x ^ 2) * m 2 -
        (4 * x ^ 3) * m 1 + x ^ 4 * m 0) := by
    have hshift : (∫ t, t ^ 4 * F x * F (x + t)) =
        ∫ y, (y - x) ^ 4 * F x * F y := by
      calc
        _ = ∫ t, (x + t - x) ^ 4 * F x * F (x + t) := by
          apply integral_congr_ae
          exact Eventually.of_forall fun t => by ring
        _ = _ := integral_add_left_eq_self (fun y : ℝ => (y - x) ^ 4 * F x * F y) x
    have he : (fun y => (y - x) ^ 4 * F x * F y) = fun y =>
        F x * (y ^ 4 * F y - (4 * x) * (y ^ 3 * F y) +
          (6 * x ^ 2) * (y ^ 2 * F y) - (4 * x ^ 3) * (y ^ 1 * F y) +
            x ^ 4 * (y ^ 0 * F y)) := by funext y; ring
    rw [hshift, he, integral_const_mul]
    rw [integral_add ((hi 4).sub ((hi 3).const_mul _)) ((hi 2).const_mul _),
      integral_sub (hi 4) ((hi 3).const_mul _),
      integral_sub (((hi 4).sub ((hi 3).const_mul _)).add ((hi 2).const_mul _))
        ((hi 1).const_mul _),
      integral_add ((((hi 4).sub ((hi 3).const_mul _)).add ((hi 2).const_mul _)).sub
        ((hi 1).const_mul _)) ((hi 0).const_mul _), integral_const_mul]
    rfl
  have hl (t : ℝ) : t ^ 4 * autocorr F t = ∫ x, t ^ 4 * F x * F (x + t) := by
    unfold autocorr
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  simp_rw [hl]
  rw [integral_integral_swap (weighted_correlation_integrable hF (continuous_pow 4) hs)]
  simp_rw [hrow]
  have he : (fun x => F x * (m 4 - (4 * x) * m 3 + (6 * x ^ 2) * m 2 -
      (4 * x ^ 3) * m 1 + x ^ 4 * m 0)) = fun x =>
      m 4 * (x ^ 0 * F x) - (4 * m 3) * (x ^ 1 * F x) +
        (6 * m 2) * (x ^ 2 * F x) - (4 * m 1) * (x ^ 3 * F x) +
          m 0 * (x ^ 4 * F x) := by funext x; ring
  rw [he]
  rw [integral_add ((((hi 0).const_mul _).sub ((hi 1).const_mul _)).add
      ((hi 2).const_mul _)|>.sub ((hi 3).const_mul _)) ((hi 4).const_mul _),
    integral_sub ((((hi 0).const_mul _).sub ((hi 1).const_mul _)).add
      ((hi 2).const_mul _)) ((hi 3).const_mul _),
    integral_add (((hi 0).const_mul _).sub ((hi 1).const_mul _)) ((hi 2).const_mul _),
    integral_sub ((hi 0).const_mul _) ((hi 1).const_mul _), integral_const_mul]
  change m 4 * m 0 - 4 * m 3 * m 1 + 6 * m 2 * m 2 - 4 * m 1 * m 3 + m 0 * m 4 = _
  ring

/-- The fourth lag moment is an exact quadratic form in position moments. -/
theorem autocorr_fourth_moment {F : ℝ → ℝ} (hF : Continuous F)
    {a : ℝ} (hs : tsupport F ⊆ Icc (-a) a) :
    let m := fun n : ℕ => ∫ x, x ^ n * F x
    (∫ t in Ioc (0 : ℝ) (2 * a), t ^ 4 * autocorr F t) =
      m 0 * m 4 - 4 * m 1 * m 3 + 3 * m 2 ^ 2 := by
  intro m
  have hwhole := whole_fourth_correlation hF hs
  have heven : (fun t => |t| ^ 4 * autocorr F |t|) =
      fun t => t ^ 4 * autocorr F t := by
    funext t
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, autocorr_neg]; ring
  have hhalf := integral_comp_abs (f := fun t => t ^ 4 * autocorr F t)
  rw [heven] at hhalf
  have hcut : (∫ t in Ioi (0 : ℝ), t ^ 4 * autocorr F t) =
      ∫ t in Ioc (0 : ℝ) (2 * a), t ^ 4 * autocorr F t := by
    have he : ∀ t ∈ Ioi (0 : ℝ), t ^ 4 * autocorr F t =
        (Iic (2 * a)).indicator (fun t => t ^ 4 * autocorr F t) t := by
      intro t _ht
      by_cases ht : t ≤ 2 * a
      · exact (Set.indicator_of_mem (show t ∈ Iic (2 * a) from ht)
          (fun t => t ^ 4 * autocorr F t)).symm
      · rw [Set.indicator_of_notMem (show t ∉ Iic (2 * a) from ht),
          autocorr_eq_zero_of_support hs (lt_of_not_ge ht), mul_zero]
    rw [setIntegral_congr_fun measurableSet_Ioi he, setIntegral_indicator measurableSet_Iic,
      Ioi_inter_Iic]
  rw [hcut] at hhalf
  dsimp only at hwhole
  change _ = m 0 * m 4 - 4 * m 1 * m 3 + 3 * m 2 ^ 2
  linarith only [hwhole, hhalf]

private theorem supported_weighted_integral {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-1 : ℝ) 1) (W : ℝ → ℝ) :
    (∫ x in Icc (-1 : ℝ) 1, W x * F x) = ∫ x, W x * F x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hs ht)), mul_zero]

private theorem legendre_position_moments {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-1 : ℝ) 1) :
    let m := fun n : ℕ => ∫ x, x ^ n * F x
    let r := regionalLegendreMoment F
    m 0 = r 0 ∧ m 1 = r 1 ∧ m 2 = (r 0 + 2 * r 2) / 3 ∧
      m 3 = (3 * r 1 + 2 * r 3) / 5 ∧
        m 4 = (7 * r 0 + 20 * r 2 + 8 * r 4) / 35 := by
  intro m r
  have hcs : HasCompactSupport F :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hs
  have hi (n : ℕ) : Integrable (fun x : ℝ => x ^ n * F x) :=
    ((continuous_pow n).mul hF).integrable_of_hasCompactSupport hcs.mul_left
  have hr (n : ℕ) : r n = ∫ x, legP n x * F x := by
    change (∫ x in Icc (-1 : ℝ) 1, F x * legP n x) = _
    simp_rw [mul_comm (F _) (legP n _)]
    exact supported_weighted_integral hs (legP n)
  have h0 : r 0 = m 0 := by rw [hr]; simp only [legP, pow_zero, one_mul, m]
  have h1 : r 1 = m 1 := by rw [hr]; simp only [legP, pow_one, m]
  have h2 : r 2 = (3 * m 2 - m 0) / 2 := by
    rw [hr]
    have he : (fun x => legP 2 x * F x) =
        fun x => (3 * (x ^ 2 * F x) - x ^ 0 * F x) / 2 := by
      funext x; norm_num [legP]; ring
    rw [he, integral_div, integral_sub ((hi 2).const_mul _) (hi 0), integral_const_mul]
    rfl
  have h3 : r 3 = (5 * m 3 - 3 * m 1) / 2 := by
    rw [hr]
    have he : (fun x => legP 3 x * F x) =
        fun x => (5 * (x ^ 3 * F x) - 3 * (x ^ 1 * F x)) / 2 := by
      funext x; norm_num [legP]; ring
    rw [he, integral_div, integral_sub ((hi 3).const_mul _) ((hi 1).const_mul _),
      integral_const_mul, integral_const_mul]
    rfl
  have h4 : r 4 = (35 * m 4 - 30 * m 2 + 3 * m 0) / 8 := by
    rw [hr]
    have he : (fun x => legP 4 x * F x) = fun x =>
        (35 * (x ^ 4 * F x) - 30 * (x ^ 2 * F x) + 3 * (x ^ 0 * F x)) / 8 := by
      funext x; norm_num [legP]; ring
    rw [he, integral_div,
      integral_add (((hi 4).const_mul _).sub ((hi 2).const_mul _)) ((hi 0).const_mul _),
      integral_sub ((hi 4).const_mul _) ((hi 2).const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
    rfl
  exact ⟨h0.symm, h1.symm, by linarith only [h0, h2],
    by linarith only [h1, h3], by linarith only [h0, h2, h4]⟩

/-- The unit-window fourth correlation moment splits into even and odd Legendre blocks. -/
theorem unit_autocorr_fourth_moment {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-1 : ℝ) 1) :
    let r := regionalLegendreMoment F
    (∫ t in Ioc (0 : ℝ) 2, t ^ 4 * autocorr F t) =
      (8 / 15) * r 0 ^ 2 + (40 / 21) * r 0 * r 2 + (8 / 35) * r 0 * r 4 +
        (4 / 3) * r 2 ^ 2 - (12 / 5) * r 1 ^ 2 - (8 / 5) * r 1 * r 3 := by
  intro r
  have h := autocorr_fourth_moment hF hs
  obtain ⟨h0, h1, h2, h3, h4⟩ := legendre_position_moments hF hs
  dsimp only at h h0 h1 h2 h3 h4
  norm_num only [mul_one] at h
  rw [h0, h1, h2, h3, h4] at h
  rw [h]
  dsimp only [r]
  ring

private theorem fourth_moment_algebra (r : ℕ → ℝ) :
    (8 / 15) * r 0 ^ 2 + (40 / 21) * r 0 * r 2 + (8 / 35) * r 0 * r 4 +
        (4 / 3) * r 2 ^ 2 - (12 / 5) * r 1 ^ 2 - (8 / 5) * r 1 * r 3 ≤
      (17 / 10) * ((1 / 2) * r 0 ^ 2 + (3 / 2) * r 1 ^ 2 +
        (5 / 2) * r 2 ^ 2 + (7 / 2) * r 3 ^ 2 + (9 / 2) * r 4 ^ 2) := by
  have hc : (0 : ℝ) ≤ 19 / 60 - (35 / 12) * (16 / 49) ^ 2 -
      (153 / 20) * (16 / 1071) ^ 2 := by norm_num
  have hp := mul_nonneg hc (sq_nonneg (r 0))
  nlinarith only [hp, sq_nonneg (r 2 - (16 / 49) * r 0),
    sq_nonneg (r 4 - (16 / 1071) * r 0), sq_nonneg (r 1 + r 3),
    sq_nonneg (r 1), sq_nonneg (r 3)]

/-- A quartic correlation consumes at most `17/10` times mass on the unit window. -/
theorem unit_autocorr_fourth_moment_le_mass {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-1 : ℝ) 1) :
    (∫ t in Ioc (0 : ℝ) 2, t ^ 4 * autocorr F t) ≤
      (17 / 10) * ∫ x, F x ^ 2 := by
  have hb := regionalMass_ge_low_moments hF 5
  norm_num [Finset.sum_range_succ] at hb
  have hcut : (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) = ∫ x, F x ^ 2 := by
    simpa only [pow_two] using supported_weighted_integral hs F
  rw [hcut] at hb
  rw [unit_autocorr_fourth_moment hF hs]
  exact (fourth_moment_algebra _).trans (mul_le_mul_of_nonneg_left hb (by norm_num))

/-- Oddness improves the quartic correlation bound to `1/10` times mass. -/
theorem unit_odd_autocorr_fourth_moment_le_mass {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-1 : ℝ) 1) (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 2, t ^ 4 * autocorr F t) ≤
      (1 / 10) * ∫ x, F x ^ 2 := by
  have hz (n : ℕ) (hn : (-1 : ℝ) ^ n = 1) : regionalLegendreMoment F n = 0 := by
    have h := intervalIntegral.integral_comp_neg
      (f := fun x => F x * legP n x) (a := (-1 : ℝ)) (b := 1)
    simp only [ho, legP_neg, hn, one_mul, neg_mul, intervalIntegral.integral_neg,
      neg_neg] at h
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc] at h
    unfold regionalLegendreMoment
    linarith only [h]
  have h0 := hz 0 (by norm_num)
  have h2 := hz 2 (by norm_num)
  have h4 := hz 4 (by norm_num)
  have hb := regionalMass_ge_low_moments hF 4
  norm_num [Finset.sum_range_succ, h0, h2] at hb
  have hcut : (∫ x in Icc (-1 : ℝ) 1, F x ^ 2) = ∫ x, F x ^ 2 := by
    simpa only [pow_two] using supported_weighted_integral hs F
  rw [hcut] at hb
  rw [unit_autocorr_fourth_moment hF hs, h0, h2, h4]
  nlinarith only [hb, sq_nonneg (regionalLegendreMoment F 1 +
    (16 / 51) * regionalLegendreMoment F 3), sq_nonneg (regionalLegendreMoment F 3)]

private theorem autocorr_dilation (F : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    autocorr (fun x => F (a * x)) t = a⁻¹ * autocorr F (a * t) := by
  unfold autocorr
  have h := Measure.integral_comp_mul_left (fun x => F x * F (x + a * t)) a
  rw [abs_of_pos (inv_pos.mpr ha), smul_eq_mul] at h
  simpa only [mul_add] using h

/-- Scaling a source scales its `n`th lag moment by the `(n+2)`nd power. -/
theorem autocorr_moment_dilation (F : ℝ → ℝ) {a : ℝ} (ha : 0 < a) (n : ℕ) :
    (∫ t in Ioc (0 : ℝ) (2 * a), t ^ n * autocorr F t) =
      a ^ (n + 2) * ∫ t in Ioc (0 : ℝ) 2,
        t ^ n * autocorr (fun x => F (a * x)) t := by
  have hc (t : ℝ) : autocorr F (a * t) =
      a * autocorr (fun x => F (a * x)) t := by
    rw [autocorr_dilation F ha]
    field_simp [ha.ne']
  have he (t : ℝ) : (a * t) ^ n * autocorr F (a * t) =
      a ^ (n + 1) * (t ^ n * autocorr (fun x => F (a * x)) t) := by
    rw [hc, mul_pow, pow_succ]
    ring
  have h := intervalIntegral.mul_integral_comp_add_mul
    (f := fun t => t ^ n * autocorr F t) (a := (0 : ℝ)) (b := 2) (c := a) (d := 0)
  simp only [zero_add, mul_zero] at h
  simp_rw [he] at h
  rw [intervalIntegral.integral_const_mul, ← mul_assoc,
    show a * a ^ (n + 1) = a ^ (n + 2) by simp only [pow_add, pow_one, pow_two]; ring,
    show a * 2 = 2 * a by ring,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2),
    intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * a)] at h
  exact h.symm

private theorem dilation_support {F : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hs : tsupport F ⊆ Icc (-a) a) :
    tsupport (fun x => F (a * x)) ⊆ Icc (-1 : ℝ) 1 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hxF : F (a * x) ≠ 0 := hx
  have hxS : a * x ∈ Icc (-a) a := by
    by_contra h
    exact hxF (image_eq_zero_of_notMem_tsupport fun ht => h (hs ht))
  constructor <;> nlinarith only [hxS.1, hxS.2, ha]

private theorem dilated_fourth_bound {F : ℝ → ℝ} {a c : ℝ} (ha : 0 < a)
    (hb : (∫ t in Ioc (0 : ℝ) 2,
      t ^ 4 * autocorr (fun x => F (a * x)) t) ≤ c * ∫ x, F (a * x) ^ 2) :
    (∫ t in Ioc (0 : ℝ) (2 * a), t ^ 4 * autocorr F t) ≤
      c * a ^ 5 * ∫ x, F x ^ 2 := by
  have hM := Measure.integral_comp_mul_left (fun x => F x ^ 2) a
  rw [abs_of_pos (inv_pos.mpr ha), smul_eq_mul] at hM
  rw [autocorr_moment_dilation F ha 4]
  calc
    _ ≤ a ^ (4 + 2) * (c * ∫ x, F (a * x) ^ 2) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg ha.le _)
    _ = c * a ^ 5 * ∫ x, F x ^ 2 := by
      rw [hM]
      field_simp [ha.ne']
      ring

/-- The fourth correlation moment scales with the fifth power of the aperture. -/
theorem autocorr_fourth_moment_le_mass {F : ℝ → ℝ} (hF : Continuous F)
    {a : ℝ} (ha : 0 < a) (hs : tsupport F ⊆ Icc (-a) a) :
    (∫ t in Ioc (0 : ℝ) (2 * a), t ^ 4 * autocorr F t) ≤
      (17 / 10) * a ^ 5 * ∫ x, F x ^ 2 := by
  apply dilated_fourth_bound ha
  exact unit_autocorr_fourth_moment_le_mass
    (hF.comp (continuous_const.mul continuous_id)) (dilation_support ha hs)

/-- Odd sources retain the smaller fourth-correlation constant at every aperture. -/
theorem odd_autocorr_fourth_moment_le_mass {F : ℝ → ℝ} (hF : Continuous F)
    {a : ℝ} (ha : 0 < a) (hs : tsupport F ⊆ Icc (-a) a)
    (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) (2 * a), t ^ 4 * autocorr F t) ≤
      (1 / 10) * a ^ 5 * ∫ x, F x ^ 2 := by
  apply dilated_fourth_bound ha
  exact unit_odd_autocorr_fourth_moment_le_mass
    (hF.comp (continuous_const.mul continuous_id)) (dilation_support ha hs)
    (fun x => by rw [mul_neg, ho])

end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.autocorr_fourth_moment
#print axioms GaloisForLFunctions.LatticeSectionTheory.unit_autocorr_fourth_moment_le_mass
#print axioms GaloisForLFunctions.LatticeSectionTheory.unit_odd_autocorr_fourth_moment_le_mass
#print axioms GaloisForLFunctions.LatticeSectionTheory.autocorr_fourth_moment_le_mass
#print axioms GaloisForLFunctions.LatticeSectionTheory.odd_autocorr_fourth_moment_le_mass
