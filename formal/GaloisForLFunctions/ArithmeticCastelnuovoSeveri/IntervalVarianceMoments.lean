import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.GammaMeanZeroCoupling

/-!
# Interval variance under positive exponential weights

Subtracting each interval's actual average isolates its oscillation. A positive
weight pays its minimum times that variance, independently of the average.
-/

noncomputable section
open MeasureTheory Set Real

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVariance
open HTGeometry.CauchyDifference

/-- Average of the source on a nonempty interval. -/
def intervalMean (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  (∫ x in Ioo a b, f x) / (b - a)

/-- Unnormalized variance on an interval. -/
def intervalVariance (a b : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x in Ioo a b, (f x - intervalMean a b f) ^ 2

theorem intervalVariance_nonneg (a b : ℝ) (f : ℝ → ℝ) :
    0 ≤ intervalVariance a b f := integral_nonneg fun _ => sq_nonneg _

theorem integral_sub_intervalMean {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) :
    ∫ x in Ioo a b, (f x - intervalMean a b f) = 0 := by
  rw [integral_sub (hf.integrable one_le_two)
    (integrableOn_Ioo_of_continuous continuous_const), setIntegral_const,
    Real.volume_real_Ioo_of_le hab.le, smul_eq_mul, intervalMean]
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

/-- The actual interval mean minimizes the square distance to a constant. -/
theorem intervalVariance_le_sub_const {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (t : ℝ) :
    intervalVariance a b f ≤ ∫ x in Ioo a b, (f x - t) ^ 2 := by
  have hc : MemLp (fun x => f x - intervalMean a b f) 2 (volume.restrict (Ioo a b)) :=
    hf.sub (memLp_const _)
  have he := setIntegral_sub_const_sq (v := t - intervalMean a b f) hab.le hc
    (integral_sub_intervalMean hab hf)
  have hfun : (fun x => (f x - intervalMean a b f - (t - intervalMean a b f)) ^ 2) =
      fun x => (f x - t) ^ 2 := by funext x; ring
  rw [hfun] at he
  rw [he]
  exact le_add_of_nonneg_right (mul_nonneg (sub_pos.mpr hab).le (sq_nonneg _))

/-- Removing the minimum-weight variance leaves a positive quadratic moment matrix. -/
theorem weighted_variance_moments {a b m : ℝ} (hab : a < b) (hm : 0 ≤ m)
    {f w : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hw : Continuous w) (hmin : ∀ x ∈ Ioo a b, m ≤ w x) :
    0 ≤ (∫ x in Ioo a b, f x ^ 2 * w x) - m * intervalVariance a b f ∧
      (∫ x in Ioo a b, f x * w x) ^ 2 ≤
        (∫ x in Ioo a b, w x) *
          ((∫ x in Ioo a b, f x ^ 2 * w x) - m * intervalVariance a b f) := by
  have hwi := integrableOn_Ioo_of_continuous hw (a := a) (b := b)
  have hfwi := integrableOn_Ioo_mul_continuous (hf.integrable one_le_two) hw
  have hf2wi := integrableOn_Ioo_mul_continuous hf.integrable_sq hw
  have key : ∀ t : ℝ, 0 ≤ (∫ x in Ioo a b, w x) * (t * t) +
      (-2 * ∫ x in Ioo a b, f x * w x) * t +
      ((∫ x in Ioo a b, f x ^ 2 * w x) - m * intervalVariance a b f) := by
    intro t
    have hsq : MemLp (fun x => f x - t) 2 (volume.restrict (Ioo a b)) :=
      hf.sub (memLp_const _)
    have hsqw := integrableOn_Ioo_mul_continuous hsq.integrable_sq hw
    have hlow : m * intervalVariance a b f ≤ ∫ x in Ioo a b, (f x - t) ^ 2 * w x := by
      calc
        _ ≤ m * ∫ x in Ioo a b, (f x - t) ^ 2 :=
          mul_le_mul_of_nonneg_left (intervalVariance_le_sub_const hab hf t) hm
        _ = ∫ x in Ioo a b, m * (f x - t) ^ 2 := (integral_const_mul _ _).symm
        _ ≤ _ := setIntegral_mono_on (hsq.integrable_sq.const_mul m) hsqw measurableSet_Ioo
          fun x hx => by nlinarith only [hmin x hx, sq_nonneg (f x - t)]
    have hfun : (fun x => (f x - t) ^ 2 * w x) =
        fun x => (f x ^ 2 * w x - (2 * t) * (f x * w x)) + t ^ 2 * w x := by
      funext x; ring
    rw [hfun, integral_add (hf2wi.sub (hfwi.const_mul (2 * t))) (hwi.const_mul (t ^ 2)),
      integral_sub hf2wi (hfwi.const_mul (2 * t)), integral_const_mul, integral_const_mul] at hlow
    nlinarith only [hlow]
  have hzero := key 0
  have hd := discrim_le_zero key
  unfold discrim at hd
  constructor
  · simpa only [mul_zero, zero_add] using hzero
  · nlinarith only [hd]

/-- Both local variances are paid by a positive product kernel. -/
theorem productWeight_twoInterval_variance_le {a b c d m n : ℝ}
    (hab : a < b) (hcd : c < d) (hm : 0 ≤ m) (hn : 0 ≤ n)
    {f g w v : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo c d)))
    (hw : Continuous w) (hv : Continuous v)
    (hwmin : ∀ x ∈ Ioo a b, m ≤ w x) (hvmin : ∀ y ∈ Ioo c d, n ≤ v y) :
    m * (∫ y in Ioo c d, v y) * intervalVariance a b f +
        n * (∫ x in Ioo a b, w x) * intervalVariance c d g ≤
      ∫ x in Ioo a b, ∫ y in Ioo c d, (f x - g y) ^ 2 * (w x * v y) := by
  have hwi := integrableOn_Ioo_of_continuous hw (a := a) (b := b)
  have hvi := integrableOn_Ioo_of_continuous hv (a := c) (b := d)
  have hfwi := integrableOn_Ioo_mul_continuous (hf.integrable one_le_two) hw
  have hf2wi := integrableOn_Ioo_mul_continuous hf.integrable_sq hw
  have hgvi := integrableOn_Ioo_mul_continuous (hg.integrable one_le_two) hv
  have hg2vi := integrableOn_Ioo_mul_continuous hg.integrable_sq hv
  set W := ∫ x in Ioo a b, w x
  set V := ∫ y in Ioo c d, v y
  set P := ∫ x in Ioo a b, f x ^ 2 * w x
  set Q := ∫ y in Ioo c d, g y ^ 2 * v y
  set F := ∫ x in Ioo a b, f x * w x
  set G := ∫ y in Ioo c d, g y * v y
  have hinner (x : ℝ) :
      (∫ y in Ioo c d, (f x - g y) ^ 2 * (w x * v y)) =
        V * (f x ^ 2 * w x) - (2 * G) * (f x * w x) + Q * w x := by
    have hfun : (fun y => (f x - g y) ^ 2 * (w x * v y)) =
        fun y => (f x ^ 2 * w x) * v y - (2 * (f x * w x)) * (g y * v y) +
          w x * (g y ^ 2 * v y) := by funext y; ring
    rw [hfun, integral_add ((hvi.const_mul (f x ^ 2 * w x)).sub
        (hgvi.const_mul (2 * (f x * w x)))) (hg2vi.const_mul (w x)),
      integral_sub (hvi.const_mul (f x ^ 2 * w x)) (hgvi.const_mul (2 * (f x * w x))),
      integral_const_mul, integral_const_mul, integral_const_mul]
    change _ = V * (f x ^ 2 * w x) - (2 * G) * (f x * w x) + Q * w x
    ring
  have hdouble :
      (∫ x in Ioo a b, ∫ y in Ioo c d, (f x - g y) ^ 2 * (w x * v y)) =
        V * P - 2 * G * F + Q * W := by
    simp_rw [hinner]
    rw [integral_add ((hf2wi.const_mul V).sub (hfwi.const_mul (2 * G))) (hwi.const_mul Q),
      integral_sub (hf2wi.const_mul V) (hfwi.const_mul (2 * G)),
      integral_const_mul, integral_const_mul, integral_const_mul]
  have hW : 0 ≤ W := setIntegral_nonneg measurableSet_Ioo fun x hx => hm.trans (hwmin x hx)
  have hV : 0 ≤ V := setIntegral_nonneg measurableSet_Ioo fun y hy => hn.trans (hvmin y hy)
  have hfm := weighted_variance_moments hab hm hf hw hwmin
  have hgm := weighted_variance_moments hcd hn hg hv hvmin
  set A := P - m * intervalVariance a b f
  set B := Q - n * intervalVariance c d g
  have hA : 0 ≤ A := hfm.1
  have hB : 0 ≤ B := hgm.1
  have hF : F ^ 2 ≤ W * A := hfm.2
  have hG : G ^ 2 ≤ V * B := hgm.2
  have hprod : (F * G) ^ 2 ≤ (W * A) * (V * B) := by
    rw [mul_pow]
    exact mul_le_mul hF hG (sq_nonneg G) (mul_nonneg hW hA)
  have hsq : (2 * (F * G)) ^ 2 ≤ (V * A + W * B) ^ 2 := by
    nlinarith only [hprod, sq_nonneg (V * A - W * B)]
  have hcross := (abs_le_of_sq_le_sq' hsq
    (add_nonneg (mul_nonneg hV hA) (mul_nonneg hW hB))).2
  rw [hdouble]
  change m * V * intervalVariance a b f + n * W * intervalVariance c d g ≤ _
  dsimp only [A, B] at hcross
  nlinarith only [hcross]

/-- An exponential slice pays both interval variances without restrictions on their means. -/
theorem rankOne_twoInterval_variance_le {α α' β β' u : ℝ}
    (hα : α < α') (hβ : β < β') (hu : 0 ≤ u) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo α α')))
    (hg : MemLp g 2 (volume.restrict (Ioo β β'))) :
    (∫ y in Ioo β β', exp (-(u * (y - α)))) * intervalVariance α α' f +
        (∫ x in Ioo α α', exp (-(u * (β' - x)))) * intervalVariance β β' g ≤
      ∫ x in Ioo α α', ∫ y in Ioo β β', (f x - g y) ^ 2 * exp (-(u * (y - x))) := by
  let w : ℝ → ℝ := fun x => exp (u * (x - α))
  let v : ℝ → ℝ := fun y => exp (-(u * (y - α)))
  let m : ℝ := exp (-(u * (β' - α)))
  have hkernel (x y : ℝ) : w x * v y = exp (-(u * (y - x))) := by
    dsimp only [w, v]
    rw [← Real.exp_add]
    congr 1
    ring
  have hcharge : m * (∫ x in Ioo α α', w x) =
      ∫ x in Ioo α α', exp (-(u * (β' - x))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only [m, w]
      rw [← Real.exp_add]
      congr 1
      ring
  have h := productWeight_twoInterval_variance_le hα hβ zero_le_one
    (show 0 ≤ m from (exp_pos _).le) hf hg (by fun_prop : Continuous w)
    (by fun_prop : Continuous v)
    (fun x hx => Real.one_le_exp (mul_nonneg hu (sub_pos.mpr hx.1).le))
    (fun y hy => Real.exp_le_exp.mpr (by
      nlinarith only [mul_nonneg hu (sub_pos.mpr hy.2).le]))
  simpa only [one_mul, hcharge, hkernel] using h

#print axioms intervalVariance_le_sub_const
#print axioms weighted_variance_moments
#print axioms productWeight_twoInterval_variance_le
#print axioms rankOne_twoInterval_variance_le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVariance
