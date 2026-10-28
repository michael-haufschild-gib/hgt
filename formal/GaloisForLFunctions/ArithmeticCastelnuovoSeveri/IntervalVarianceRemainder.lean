import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVarianceMoments

/-!
# The mean remainder of a positive product kernel

Splitting each weight into its minimum and its nonnegative remainder preserves
both interval variance charges and a square of the difference of actual means.
-/

noncomputable section
open MeasureTheory Set Real

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVariance
open HTGeometry.CauchyDifference

/-- The square distance to any constant is variance plus the mean displacement. -/
theorem integral_sub_const_sq_eq_variance {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (t : ℝ) :
    (∫ x in Ioo a b, (f x - t) ^ 2) =
      intervalVariance a b f + (b - a) * (intervalMean a b f - t) ^ 2 := by
  have hc : MemLp (fun x => f x - intervalMean a b f) 2 (volume.restrict (Ioo a b)) :=
    hf.sub (memLp_const _)
  have h := setIntegral_sub_const_sq (v := t - intervalMean a b f) hab.le hc
    (integral_sub_intervalMean hab hf)
  have he : (fun x => (f x - intervalMean a b f - (t - intervalMean a b f)) ^ 2) =
      fun x => (f x - t) ^ 2 := by funext x; ring
  rw [he] at h
  change _ = intervalVariance a b f + _ at h
  rw [h]
  ring

private theorem integral_eq_width_mean {a b : ℝ} (hab : a < b) (f : ℝ → ℝ) :
    (∫ x in Ioo a b, f x) = (b - a) * intervalMean a b f := by
  unfold intervalMean
  field_simp [ne_of_gt (sub_pos.mpr hab)]

private def productMoment (a b c d : ℝ) (f g w v : ℝ → ℝ) : ℝ :=
  (∫ y in Ioo c d, v y) * (∫ x in Ioo a b, f x ^ 2 * w x) -
    2 * (∫ y in Ioo c d, g y * v y) * (∫ x in Ioo a b, f x * w x) +
    (∫ y in Ioo c d, g y ^ 2 * v y) * (∫ x in Ioo a b, w x)

private theorem productMoment_eq_integral {a b c d : ℝ} {f g w v : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo c d))) (hw : Continuous w) (hv : Continuous v) :
    productMoment a b c d f g w v =
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
    have hi : IntegrableOn (fun y => (f x ^ 2 * w x) * v y -
        (2 * (f x * w x)) * (g y * v y)) (Ioo c d) :=
      (hvi.const_mul (f x ^ 2 * w x)).sub (hgvi.const_mul (2 * (f x * w x)))
    rw [hfun, integral_add hi (hg2vi.const_mul (w x)),
      integral_sub (hvi.const_mul (f x ^ 2 * w x)) (hgvi.const_mul (2 * (f x * w x))),
      integral_const_mul, integral_const_mul, integral_const_mul]
    change _ = V * (f x ^ 2 * w x) - (2 * G) * (f x * w x) + Q * w x
    ring
  simp_rw [hinner]
  have hi : IntegrableOn (fun x => V * (f x ^ 2 * w x) - (2 * G) * (f x * w x)) (Ioo a b) :=
    (hf2wi.const_mul V).sub (hfwi.const_mul (2 * G))
  rw [integral_add hi (hwi.const_mul Q),
    integral_sub (hf2wi.const_mul V) (hfwi.const_mul (2 * G)),
    integral_const_mul, integral_const_mul, integral_const_mul]
  rfl

private theorem integral_mul_add_weight {a b : ℝ} {f w v : ℝ → ℝ}
    (hf : IntegrableOn f (Ioo a b)) (hw : Continuous w) (hv : Continuous v) :
    (∫ x in Ioo a b, f x * (w x + v x)) =
      (∫ x in Ioo a b, f x * w x) + ∫ x in Ioo a b, f x * v x := by
  simp_rw [mul_add]
  exact integral_add (integrableOn_Ioo_mul_continuous hf hw)
    (integrableOn_Ioo_mul_continuous hf hv)

private theorem productMoment_add_left {a b c d : ℝ} {f g w v z : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b))) (hw : Continuous w) (hv : Continuous v) :
    productMoment a b c d f g (fun x => w x + v x) z =
      productMoment a b c d f g w z + productMoment a b c d f g v z := by
  unfold productMoment
  rw [integral_mul_add_weight hf.integrable_sq hw hv,
    integral_mul_add_weight (hf.integrable one_le_two) hw hv,
    integral_add (integrableOn_Ioo_of_continuous hw) (integrableOn_Ioo_of_continuous hv)]
  ring

private theorem productMoment_swap (a b c d : ℝ) (f g w v : ℝ → ℝ) :
    productMoment a b c d f g w v = productMoment c d a b g f v w := by
  unfold productMoment
  ring

private theorem productMoment_add_right {a b c d : ℝ} {f g w v z : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Ioo c d))) (hw : Continuous w) (hv : Continuous v) :
    productMoment a b c d f g z (fun x => w x + v x) =
      productMoment a b c d f g z w + productMoment a b c d f g z v := by
  rw [productMoment_swap, productMoment_add_left hg hw hv]
  rw [productMoment_swap c d a b g f w z, productMoment_swap c d a b g f v z]

private theorem productMoment_constants {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {f g : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo c d))) (m n : ℝ) :
    productMoment a b c d f g (fun _ => m) (fun _ => n) =
      m * n * ((d - c) * intervalVariance a b f + (b - a) * intervalVariance c d g +
        (b - a) * (d - c) * (intervalMean a b f - intervalMean c d g) ^ 2) := by
  have hfs := integral_sub_const_sq_eq_variance hab hf 0
  have hgs := integral_sub_const_sq_eq_variance hcd hg 0
  simp only [sub_zero] at hfs hgs
  simp only [productMoment, integral_mul_const, setIntegral_const,
    Real.volume_real_Ioo_of_le hab.le, Real.volume_real_Ioo_of_le hcd.le, smul_eq_mul]
  rw [hfs, hgs, integral_eq_width_mean hab f, integral_eq_width_mean hcd g]
  ring

/-- The minimum product kernel preserves the square difference of the actual interval means. -/
theorem productWeight_twoInterval_mean_variance_le {a b c d m n : ℝ}
    (hab : a < b) (hcd : c < d) (hm : 0 ≤ m) (hn : 0 ≤ n)
    {f g w v : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo c d)))
    (hw : Continuous w) (hv : Continuous v)
    (hwmin : ∀ x ∈ Ioo a b, m ≤ w x) (hvmin : ∀ y ∈ Ioo c d, n ≤ v y) :
    m * (∫ y in Ioo c d, v y) * intervalVariance a b f +
        n * (∫ x in Ioo a b, w x) * intervalVariance c d g +
        m * n * (b - a) * (d - c) * (intervalMean a b f - intervalMean c d g) ^ 2 ≤
      ∫ x in Ioo a b, ∫ y in Ioo c d, (f x - g y) ^ 2 * (w x * v y) := by
  let wr : ℝ → ℝ := fun x => w x - m
  let vr : ℝ → ℝ := fun y => v y - n
  have hwr : Continuous wr := hw.sub continuous_const
  have hvr : Continuous vr := hv.sub continuous_const
  have hwr0 : ∀ x ∈ Ioo a b, 0 ≤ wr x := fun x hx => sub_nonneg.mpr (hwmin x hx)
  have hvr0 : ∀ y ∈ Ioo c d, 0 ≤ vr y := fun y hy => sub_nonneg.mpr (hvmin y hy)
  have hsplit : productMoment a b c d f g w v =
      productMoment a b c d f g (fun _ => m) (fun _ => n) +
      productMoment a b c d f g (fun _ => m) vr +
      productMoment a b c d f g wr (fun _ => n) + productMoment a b c d f g wr vr := by
    have hew : w = fun x => m + wr x := by funext x; dsimp only [wr]; ring
    have hev : v = fun y => n + vr y := by funext y; dsimp only [vr]; ring
    calc
      _ = productMoment a b c d f g (fun x => m + wr x) (fun y => n + vr y) := by
        rw [← hew, ← hev]
      _ = _ := by
        rw [productMoment_add_left hf continuous_const hwr,
          productMoment_add_right hg continuous_const hvr,
          productMoment_add_right hg continuous_const hvr]
        ring
  have hM := productWeight_twoInterval_variance_le hab hcd hm (le_refl (0 : ℝ)) hf hg
    (continuous_const : Continuous (fun _ : ℝ => m)) hvr (fun _ _ => le_rfl) hvr0
  have hN := productWeight_twoInterval_variance_le hab hcd (le_refl (0 : ℝ)) hn hf hg
    hwr (continuous_const : Continuous (fun _ : ℝ => n)) hwr0 (fun _ _ => le_rfl)
  simp only [zero_mul, add_zero, zero_add] at hM hN
  rw [← productMoment_eq_integral hf hg continuous_const hvr] at hM
  rw [← productMoment_eq_integral hf hg hwr continuous_const] at hN
  have hR : 0 ≤ productMoment a b c d f g wr vr := by
    rw [productMoment_eq_integral hf hg hwr hvr]
    exact setIntegral_nonneg measurableSet_Ioo fun x hx =>
      setIntegral_nonneg measurableSet_Ioo fun y hy =>
        mul_nonneg (sq_nonneg _) (mul_nonneg (hwr0 x hx) (hvr0 y hy))
  have hW : (∫ x in Ioo a b, wr x) = (∫ x in Ioo a b, w x) - (b - a) * m := by
    rw [show wr = fun x => w x - m from rfl,
      integral_sub (integrableOn_Ioo_of_continuous hw)
        (integrableOn_Ioo_of_continuous continuous_const),
      setIntegral_const, Real.volume_real_Ioo_of_le hab.le, smul_eq_mul]
  have hV : (∫ y in Ioo c d, vr y) = (∫ y in Ioo c d, v y) - (d - c) * n := by
    rw [show vr = fun y => v y - n from rfl,
      integral_sub (integrableOn_Ioo_of_continuous hv)
        (integrableOn_Ioo_of_continuous continuous_const),
      setIntegral_const, Real.volume_real_Ioo_of_le hcd.le, smul_eq_mul]
  rw [← productMoment_eq_integral hf hg hw hv, hsplit,
    productMoment_constants hab hcd hf hg m n]
  rw [hW] at hN
  rw [hV] at hM
  nlinarith only [hM, hN, hR]

/-- An exponential slice retains both variances and the far-end mean square. -/
theorem rankOne_twoInterval_mean_variance_le {α α' β β' u : ℝ}
    (hα : α < α') (hβ : β < β') (hu : 0 ≤ u) {f g : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioo α α')))
    (hg : MemLp g 2 (volume.restrict (Ioo β β'))) :
    (∫ y in Ioo β β', exp (-(u * (y - α)))) * intervalVariance α α' f +
        (∫ x in Ioo α α', exp (-(u * (β' - x)))) * intervalVariance β β' g +
        exp (-(u * (β' - α))) * (α' - α) * (β' - β) *
          (intervalMean α α' f - intervalMean β β' g) ^ 2 ≤
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
  have h := productWeight_twoInterval_mean_variance_le hα hβ zero_le_one
    (show 0 ≤ m from (exp_pos _).le) hf hg (by fun_prop : Continuous w)
    (by fun_prop : Continuous v)
    (fun x hx => Real.one_le_exp (mul_nonneg hu (sub_pos.mpr hx.1).le))
    (fun y hy => Real.exp_le_exp.mpr (by
      nlinarith only [mul_nonneg hu (sub_pos.mpr hy.2).le]))
  simpa only [one_mul, hcharge, hkernel] using h

#print axioms integral_sub_const_sq_eq_variance
#print axioms productWeight_twoInterval_mean_variance_le
#print axioms rankOne_twoInterval_mean_variance_le

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.IntervalVariance
