import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.OddPrimeFreeGammaJumpCount

/-!
# The second odd correlation moment

The quadratic lag moment is minus the square of the first position moment.
This exact identity sharpens the polynomial error in the Gamma jump comparison.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
namespace GaloisForLFunctions.LatticeSectionTheory

private theorem odd_source_integral_zero {F : ℝ → ℝ} (ho : ∀ x, F (-x) = -F x) :
    (∫ x, F x) = 0 := by
  have h := integral_neg_eq_self F volume
  rw [integral_congr_ae (Eventually.of_forall ho), integral_neg] at h
  linarith only [h]

private theorem weighted_correlation_integrable {F : ℝ → ℝ} (hF : Continuous F) {a : ℝ}
    (hs : tsupport F ⊆ Icc (-a) a) :
    Integrable (fun p : ℝ × ℝ => p.1 ^ 2 * F p.2 * F (p.2 + p.1))
      (volume.prod volume) := by
  have hc : Continuous (fun p : ℝ × ℝ => p.1 ^ 2 * F p.2 * F (p.2 + p.1)) := by
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
    (ho : ∀ x, F (-x) = -F x) :
    (∫ t, t ^ 2 * autocorr F t) = -2 * (∫ x, x * F x) ^ 2 := by
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
  rw [integral_integral_swap (weighted_correlation_integrable hF hs)]
  simp_rw [hrow, odd_source_integral_zero ho, mul_zero, add_zero]
  have he : (fun x => F x * ((∫ y, y ^ 2 * F y) - 2 * x * (∫ y, y * F y))) =
      fun x => (∫ y, y ^ 2 * F y) * F x -
        (2 * (∫ y, y * F y)) * (x * F x) := by funext x; ring
  rw [he, integral_sub (hi0.const_mul _) (hi1.const_mul _),
    integral_const_mul, integral_const_mul, odd_source_integral_zero ho]
  ring

/-- Oddness turns the quadratic correlation moment into a negative position square. -/
theorem odd_autocorr_second_moment {F : ℝ → ℝ} (hF : Continuous F)
    (hcs : HasCompactSupport F) {a : ℝ} (hs : tsupport F ⊆ Icc (-a) a)
    (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) (2 * a), t ^ 2 * autocorr F t) =
      -(∫ x, x * F x) ^ 2 := by
  have hwhole := whole_second_correlation hF hcs hs ho
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

/-- The unit-window quadratic jump cost is its mass term plus a position square. -/
theorem unit_odd_jump_second_moment {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hcs : HasCompactSupport F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, t ^ 2 * (autocorr F 0 - autocorr F t)) =
      autocorr F 0 / 3 + (∫ x, x * F x) ^ 2 := by
  have hc := continuous_autocorr hF hcs
  have h2 := odd_autocorr_second_moment hF.continuous hcs hs ho
  norm_num at h2
  have hp : (∫ t in Ioc (0 : ℝ) 1, t ^ 2) = (1 / 3 : ℝ) := by
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_pow]
    norm_num
  have hi0 : IntegrableOn (fun t : ℝ => t ^ 2 * autocorr F 0) (Ioc (0 : ℝ) 1) :=
    ((continuous_pow 2).mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi1 : IntegrableOn (fun t : ℝ => t ^ 2 * autocorr F t) (Ioc (0 : ℝ) 1) :=
    ((continuous_pow 2).mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  simp_rw [mul_sub]
  rw [integral_sub hi0 hi1, integral_mul_const, hp, h2]
  ring


private theorem unit_supported_pair_integral {F : ℝ → ℝ}
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) (H : ℝ → ℝ) :
    (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), H x * F x) = ∫ x, H x * F x := by
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)
  · rw [Set.indicator_of_mem hx]
  · have hz : F x = 0 := image_eq_zero_of_notMem_tsupport fun ht => hx (hs ht)
    rw [Set.indicator_of_notMem hx, hz, mul_zero]

/-- The first position moment has squared norm at most `1/12` on a unit window. -/
theorem unit_position_moment_square_le {F : ℝ → ℝ} (hF : Continuous F)
    (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2)) :
    (∫ x, x * F x) ^ 2 ≤ (∫ x, F x ^ 2) / 12 := by
  let m := ∫ x, x * F x
  have hE : (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), F x ^ 2) = ∫ x, F x ^ 2 := by
    simpa only [pow_two] using unit_supported_pair_integral hs F
  have hm : (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), x * F x) = m :=
    unit_supported_pair_integral hs id
  have hx2 : (∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), x ^ 2) = (1 / 12 : ℝ) := by
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2), integral_pow]
    norm_num
  have hiE : IntegrableOn (fun x => F x ^ 2) (Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    (hF.pow 2).integrableOn_Icc
  have hiM : IntegrableOn (fun x => x * F x) (Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    (continuous_id.mul hF).integrableOn_Icc
  have hiX : IntegrableOn (fun x : ℝ => x ^ 2) (Icc (-(1 / 2 : ℝ)) (1 / 2)) :=
    (continuous_pow 2).integrableOn_Icc
  have hpos : 0 ≤ ∫ x in Icc (-(1 / 2 : ℝ)) (1 / 2), (F x - 12 * m * x) ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have he : (fun x => (F x - 12 * m * x) ^ 2) =
      fun x => (F x ^ 2 - (24 * m) * (x * F x)) + (144 * m ^ 2) * x ^ 2 := by
    funext x
    ring
  have hiSub : IntegrableOn (fun x => F x ^ 2 - (24 * m) * (x * F x))
      (Icc (-(1 / 2 : ℝ)) (1 / 2)) := hiE.sub (hiM.const_mul (24 * m))
  have hiLast : IntegrableOn (fun x => (144 * m ^ 2) * x ^ 2)
      (Icc (-(1 / 2 : ℝ)) (1 / 2)) := hiX.const_mul (144 * m ^ 2)
  rw [he, integral_add hiSub hiLast,
    integral_sub (f := fun x => F x ^ 2) (g := fun x => (24 * m) * (x * F x))
      hiE (hiM.const_mul (24 * m)), integral_const_mul, integral_const_mul,
    hE, hm, hx2] at hpos
  change m ^ 2 ≤ _
  nlinarith only [hpos]

/-- Exact odd moment cancellation improves the quadratic lag cost to `5/12` of the mass. -/
theorem unit_odd_jump_second_moment_le {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hcs : HasCompactSupport F) (hs : tsupport F ⊆ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (ho : ∀ x, F (-x) = -F x) :
    (∫ t in Ioc (0 : ℝ) 1, t ^ 2 * (autocorr F 0 - autocorr F t)) ≤
      (5 / 12 : ℝ) * (∫ x, F x ^ 2) := by
  rw [unit_odd_jump_second_moment hF hcs hs ho, autocorr_zero_eq]
  have h := unit_position_moment_square_le hF.continuous hs
  linarith only [h]


end GaloisForLFunctions.LatticeSectionTheory

#print axioms GaloisForLFunctions.LatticeSectionTheory.odd_autocorr_second_moment
#print axioms GaloisForLFunctions.LatticeSectionTheory.unit_odd_jump_second_moment

#print axioms GaloisForLFunctions.LatticeSectionTheory.unit_odd_jump_second_moment_le
