import GaloisForLFunctions.RHTower.EisensteinUnfoldedRowSum
import GaloisForLFunctions.RHTower.EisensteinHyperbolicChart

/-!
# The two one-dimensional integrals of the Maass–Selberg unfolding

After unfolding, the Maass–Selberg pairing reduces to two integrals of the constant term
`c_v(y) = B(v) y^{½−v} + A(v) y^{½+v}` against powers of `y`:

* the cusp integral `∫_{𝒟 ∩ {y > Y}} y^{½−u} E_v dμ = ∫_Y^∞ y^{−3/2−u} c_v(y) dy
    = B(v) Y^{−u−v}/(u+v) + A(v) Y^{v−u}/(u−v)`, and
* the slab integral `∫_{strip ∩ {y ≤ Y}} y^{½+u} E_v dμ = ∫_0^Y y^{u−3/2} c_v(y) dy
    = B(v) Y^{u−v}/(u−v) + A(v) Y^{u+v}/(u+v)`,

both for `Re u > Re v > ½` (with `Im v > 0` for the slab, where integrability comes from the
unfolding module).  The `x`-integration uses the zero mean of the cusp tail over a period.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Period means over `[−½, ½]` -/

theorem periodic_cuspLeg (u : ℂ) (Y : ℝ) :
    Function.Periodic (fun x => d4BMCompletedEisensteinCuspLeg .scalar u x Y) 1 :=
  fun x => cuspLeg_add_one u x Y

theorem setIntegral_unitIcc_cuspLeg {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    ∫ x in unitIcc, d4BMCompletedEisensteinCuspLeg .scalar u x Y =
      d4BMCompletedEisensteinCuspConstantPart .scalar u Y := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)]
  have h := (periodic_cuspLeg u Y).intervalIntegral_add_eq (-(1 / 2)) 0
  norm_num at h
  rw [h, intervalIntegral.integral_of_le zero_le_one]
  exact setIntegral_Ioc_cuspLeg hY u

theorem setIntegral_unitIcc_cuspTailPart {Y : ℝ} (hY : 0 < Y) (u : ℂ) :
    ∫ x in unitIcc, d4BMCompletedEisensteinCuspTailPart .scalar u x Y = 0 := by
  have h := setIntegral_unitIcc_cuspLeg hY u
  unfold d4BMCompletedEisensteinCuspLeg at h
  have hc : Integrable (fun _ : ℝ => d4BMCompletedEisensteinCuspConstantPart .scalar u Y)
      (volume.restrict unitIcc) := integrableOn_const (by simp)
  rw [integral_add hc (continuous_cuspTailPart_x' hY u).integrableOn_Icc] at h
  have hvol : ∫ _ in unitIcc, d4BMCompletedEisensteinCuspConstantPart .scalar u Y =
      d4BMCompletedEisensteinCuspConstantPart .scalar u Y := by
    simp [unitIcc]; norm_num
  rw [hvol] at h
  linear_combination h

/-! ## Bounds in coordinates -/

theorem norm_cuspLeg_le' {v : ℂ} (hv : 1 / 2 ≤ v.re) {y : ℝ} (hy : 1 / 2 ≤ y) (x : ℝ) :
    ‖d4BMCompletedEisensteinCuspLeg .scalar v x y‖ ≤ lineBoundConst v * (1 + y ^ (1 / 2 + v.re)) := by
  have hy0 : 0 < y := by linarith
  let z : ℍ := ⟨⟨x, y⟩, hy0⟩
  have hz : 1 / 2 ≤ z.im := hy
  have := norm_eisensteinLineModel_le' hv hz
  exact this

/-- `y^a y^b / y² = y^{a+b−2}` for a positive real base. -/
theorem cpow_mul_cpow_div_sq {y : ℝ} (hy : 0 < y) (a b : ℂ) :
    ((y : ℝ) : ℂ) ^ a * ((y : ℝ) : ℂ) ^ b / ((y : ℝ) : ℂ) ^ 2 = ((y : ℝ) : ℂ) ^ (a + b - 2) := by
  have hne : ((y : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
  rw [← Complex.cpow_add _ _ hne, Complex.cpow_sub _ _ hne]
  congr 1
  exact (Complex.cpow_natCast _ 2).symm ▸ rfl

/-! ## The cusp integral -/

/-- The cusp integrand `y^{½−u} E_v(x + iy)`. -/
def cuspIntegrand (u v : ℂ) (p : ℝ × ℝ) : ℂ :=
  ((p.2 : ℝ) : ℂ) ^ (1 / 2 - u) * d4BMCompletedEisensteinCuspLeg .scalar v p.1 p.2

theorem continuousOn_cuspIntegrand_div (u v : ℂ) :
    ContinuousOn (fun p : ℝ × ℝ => cuspIntegrand u v p / ((p.2 : ℝ) : ℂ) ^ 2)
      {p : ℝ × ℝ | 0 < p.2} := by
  unfold cuspIntegrand
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ)) {p : ℝ × ℝ | 0 < p.2} :=
    (Complex.continuous_ofReal.comp continuous_snd).continuousOn
  have hslit : ∀ p ∈ {p : ℝ × ℝ | 0 < p.2}, ((p.2 : ℝ) : ℂ) ∈ Complex.slitPlane :=
    fun p hp => Complex.ofReal_mem_slitPlane.mpr hp
  refine ((hc.cpow_const hslit).mul (continuousOn_cuspLeg_pair v)).div (hc.pow 2) ?_
  intro p hp
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hp))

theorem norm_cuspIntegrand_div_le {u v : ℂ} (hv : 1 / 2 ≤ v.re) {p : ℝ × ℝ} (hp : 1 ≤ p.2) :
    ‖cuspIntegrand u v p / ((p.2 : ℝ) : ℂ) ^ 2‖ ≤
      2 * lineBoundConst v * p.2 ^ (v.re - u.re - 1) := by
  have hy0 : 0 < p.2 := by linarith
  unfold cuspIntegrand
  rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hy0, re_half_sub]
  have hE := norm_cuspLeg_le' hv (by linarith : 1 / 2 ≤ p.2) p.1
  have hone : (1 : ℝ) ≤ p.2 ^ (1 / 2 + v.re) := Real.one_le_rpow hp (by linarith)
  have hL := lineBoundConst_nonneg v
  have hE2 : ‖d4BMCompletedEisensteinCuspLeg .scalar v p.1 p.2‖ ≤
      2 * lineBoundConst v * p.2 ^ (1 / 2 + v.re) := by
    refine hE.trans ?_
    have : (1 : ℝ) + p.2 ^ (1 / 2 + v.re) ≤ 2 * p.2 ^ (1 / 2 + v.re) := by linarith
    calc lineBoundConst v * (1 + p.2 ^ (1 / 2 + v.re))
        ≤ lineBoundConst v * (2 * p.2 ^ (1 / 2 + v.re)) := mul_le_mul_of_nonneg_left this hL
      _ = _ := by ring
  have hpow : 0 ≤ p.2 ^ (1 / 2 - u.re) := Real.rpow_nonneg hy0.le _
  have hsq : 0 < p.2 ^ 2 := by positivity
  calc p.2 ^ (1 / 2 - u.re) * ‖d4BMCompletedEisensteinCuspLeg .scalar v p.1 p.2‖ / p.2 ^ 2
      ≤ p.2 ^ (1 / 2 - u.re) * (2 * lineBoundConst v * p.2 ^ (1 / 2 + v.re)) / p.2 ^ 2 := by
        gcongr
    _ = 2 * lineBoundConst v * (p.2 ^ (1 / 2 - u.re) * p.2 ^ (1 / 2 + v.re) / p.2 ^ 2) := by ring
    _ = 2 * lineBoundConst v * p.2 ^ (v.re - u.re - 1) := by
        congr 1
        rw [← Real.rpow_add hy0, ← Real.rpow_natCast, ← Real.rpow_sub hy0]
        congr 1
        push_cast
        ring

theorem integrableOn_rpow_cuspRect {β : ℝ} (hβ : β < -1) {Y : ℝ} (hY : 0 < Y) (C : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => C * p.2 ^ β) (cuspRect Y) := by
  have hy : Integrable (fun y : ℝ => C * y ^ β) (volume.restrict (Ioi Y)) :=
    (integrableOn_Ioi_rpow_of_lt hβ hY).const_mul C
  have h := hy.comp_snd (volume.restrict unitIcc)
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at h
  exact h

theorem integrableOn_cuspIntegrand_div {u v : ℂ} (hv : 1 / 2 ≤ v.re) (huv : v.re < u.re) {Y : ℝ}
    (hY : 1 ≤ Y) :
    IntegrableOn (fun p : ℝ × ℝ => cuspIntegrand u v p / ((p.2 : ℝ) : ℂ) ^ 2) (cuspRect Y) := by
  refine Integrable.mono' (integrableOn_rpow_cuspRect (β := v.re - u.re - 1) (by linarith)
    (by linarith : 0 < Y) (2 * lineBoundConst v)) ?_ ?_
  · exact ((continuousOn_cuspIntegrand_div u v).mono fun p hp => cuspRect_pos (by linarith) hp)
      |>.aestronglyMeasurable (measurableSet_cuspRect Y)
  · refine (ae_restrict_iff' (measurableSet_cuspRect Y)).mpr (Filter.Eventually.of_forall fun p hp => ?_)
    have hp2 : 1 ≤ p.2 := by
      have := hp.2
      simp only [mem_Ioi] at this
      linarith
    exact norm_cuspIntegrand_div_le hv hp2

/-- **The cusp integral.** -/
theorem setIntegral_cusp_eq {u v : ℂ} (hv1 : 1 / 2 < v.re) (huv : v.re < u.re) {Y : ℝ}
    (hY : 1 ≤ Y) :
    ∫ z in fd ∩ {z : ℍ | Y < z.im}, ((z.im : ℝ) : ℂ) ^ (1 / 2 - u) * eisensteinLineModel v z =
      msB v * (Y : ℂ) ^ (-u - v) / (u + v) + msA v * (Y : ℂ) ^ (v - u) / (u - v) := by
  have hYpos : 0 < Y := by linarith
  have huv0 : u - v ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hupv : u + v ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1 : (∫ z in fd ∩ {z : ℍ | Y < z.im},
      ((z.im : ℝ) : ℂ) ^ (1 / 2 - u) * eisensteinLineModel v z) =
      ∫ z in fd ∩ {z : ℍ | Y < z.im}, cuspIntegrand u v (z.re, z.im) := rfl
  rw [h1, setIntegral_fd_above_eq hY, cuspRect,
    setIntegral_prod_eq_iterated (integrableOn_cuspIntegrand_div hv1.le huv hY)]
  -- inner integral
  have hinner : ∀ y ∈ Ioi Y, (∫ x in unitIcc, cuspIntegrand u v (x, y) / ((y : ℝ) : ℂ) ^ 2) =
      msB v * ((y : ℝ) : ℂ) ^ (-1 - u - v) + msA v * ((y : ℝ) : ℂ) ^ (-1 - u + v) := by
    intro y hy
    have hy0 : 0 < y := by simp only [mem_Ioi] at hy; linarith
    have : (fun x => cuspIntegrand u v (x, y) / ((y : ℝ) : ℂ) ^ 2) =
        fun x => (((y : ℝ) : ℂ) ^ (1 / 2 - u) / ((y : ℝ) : ℂ) ^ 2) *
          d4BMCompletedEisensteinCuspLeg .scalar v x y := by
      funext x; unfold cuspIntegrand; ring
    rw [this, integral_const_mul, setIntegral_unitIcc_cuspLeg hy0, cuspConstantPart_eq_msAB]
    have e1 : ((y : ℝ) : ℂ) ^ (1 / 2 - u) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ (1 / 2 - v) =
        ((y : ℝ) : ℂ) ^ (-1 - u - v) := by
      rw [div_mul_eq_mul_div, cpow_mul_cpow_div_sq hy0]; congr 1; ring
    have e2 : ((y : ℝ) : ℂ) ^ (1 / 2 - u) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ (1 / 2 + v) =
        ((y : ℝ) : ℂ) ^ (-1 - u + v) := by
      rw [div_mul_eq_mul_div, cpow_mul_cpow_div_sq hy0]; congr 1; ring
    calc ((y : ℝ) : ℂ) ^ (1 / 2 - u) / ((y : ℝ) : ℂ) ^ 2 *
          (msB v * ((y : ℝ) : ℂ) ^ (1 / 2 - v) + msA v * ((y : ℝ) : ℂ) ^ (1 / 2 + v))
        = msB v * (((y : ℝ) : ℂ) ^ (1 / 2 - u) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ (1 / 2 - v)) +
          msA v * (((y : ℝ) : ℂ) ^ (1 / 2 - u) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ (1 / 2 + v)) := by
          ring
      _ = _ := by rw [e1, e2]
  rw [setIntegral_congr_fun measurableSet_Ioi hinner]
  have hi1 : IntegrableOn (fun y : ℝ => msB v * ((y : ℝ) : ℂ) ^ (-1 - u - v)) (Ioi Y) :=
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) hYpos).const_mul _
  have hi2 : IntegrableOn (fun y : ℝ => msA v * ((y : ℝ) : ℂ) ^ (-1 - u + v)) (Ioi Y) :=
    (integrableOn_Ioi_cpow_of_lt (by simp; linarith) hYpos).const_mul _
  rw [integral_add hi1 hi2, integral_const_mul, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) hYpos, integral_Ioi_cpow_of_lt (by simp; linarith) hYpos]
  have e3 : -1 - u - v + 1 = -u - v := by ring
  have e4 : -1 - u + v + 1 = v - u := by ring
  rw [e3, e4]
  have hn1 : -u - v ≠ 0 := by intro h; apply hupv; linear_combination -h
  have hn2 : v - u ≠ 0 := by intro h; apply huv0; linear_combination -h
  field_simp
  ring

/-! ## The slab integral -/

/-- The slab integrand `y^{½+u} E_v(x + iy)`. -/
def slabIntegrand (u v : ℂ) (p : ℝ × ℝ) : ℂ :=
  ((p.2 : ℝ) : ℂ) ^ (1 / 2 + u) * d4BMCompletedEisensteinCuspLeg .scalar v p.1 p.2

theorem integrableOn_slabIntegrand_div {u v : ℂ} (hu : 1 / 2 < u.re) (hv1 : 1 / 2 < v.re)
    (huv : v.re < u.re) (hv : v ∈ eisensteinLineDomain) {Y : ℝ} (hY : 1 ≤ Y) :
    IntegrableOn (fun p : ℝ × ℝ => slabIntegrand u v p / ((p.2 : ℝ) : ℂ) ^ 2) (stripSlab Y) := by
  have hint := integrableOn_unfoldedIntegrand_strip hu hv1 huv hv hY
  have hset := setOf_coord_stripSlab Y
  have hS : IntegrableOn (fun z : ℍ => ((z.im : ℝ) : ℂ) ^ (1 / 2 + u) * eisensteinLineModel v z)
      (modularStrip ∩ {z : ℍ | z.im ≤ Y}) volume := by
    refine (hint.mono_set inter_subset_left).congr_fun (fun z hz => ?_)
      (measurableSet_strip_inter_below Y)
    unfold unfoldedIntegrand slabWeight
    rw [if_pos (show z.im ≤ Y from hz.2)]
  rw [← hset] at hS
  exact (integrableOn_coord_iff (measurableSet_stripSlab Y) (fun _ hp => stripSlab_pos hp)
    (slabIntegrand u v)).mp hS

/-- **The slab integral.** -/
theorem setIntegral_slab_eq {u v : ℂ} (hu : 1 / 2 < u.re) (hv1 : 1 / 2 < v.re)
    (huv : v.re < u.re) (hv : v ∈ eisensteinLineDomain) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ z in modularStrip ∩ {z : ℍ | z.im ≤ Y},
        ((z.im : ℝ) : ℂ) ^ (1 / 2 + u) * eisensteinLineModel v z =
      msB v * (Y : ℂ) ^ (u - v) / (u - v) + msA v * (Y : ℂ) ^ (u + v) / (u + v) := by
  have hYpos : 0 < Y := by linarith
  have huv0 : u - v ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hupv : u + v ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h1 : (∫ z in modularStrip ∩ {z : ℍ | z.im ≤ Y},
      ((z.im : ℝ) : ℂ) ^ (1 / 2 + u) * eisensteinLineModel v z) =
      ∫ z in modularStrip ∩ {z : ℍ | z.im ≤ Y}, slabIntegrand u v (z.re, z.im) := rfl
  rw [h1, setIntegral_strip_below_eq Y (slabIntegrand u v), stripSlab,
    setIntegral_prod_eq_iterated (integrableOn_slabIntegrand_div hu hv1 huv hv hY)]
  have hinner : ∀ y ∈ Ioc (0 : ℝ) Y,
      (∫ x in Ico (0 : ℝ) 1, slabIntegrand u v (x, y) / ((y : ℝ) : ℂ) ^ 2) =
      msB v * ((y : ℝ) : ℂ) ^ (u - v - 1) + msA v * ((y : ℝ) : ℂ) ^ (u + v - 1) := by
    intro y hy
    have hy0 : 0 < y := hy.1
    have : (fun x => slabIntegrand u v (x, y) / ((y : ℝ) : ℂ) ^ 2) =
        fun x => (((y : ℝ) : ℂ) ^ (1 / 2 + u) / ((y : ℝ) : ℂ) ^ 2) *
          d4BMCompletedEisensteinCuspLeg .scalar v x y := by
      funext x; unfold slabIntegrand; ring
    rw [this, integral_const_mul, integral_Ico_eq_integral_Ioc, setIntegral_Ioc_cuspLeg hy0 v,
      cuspConstantPart_eq_msAB]
    have e1 : ((y : ℝ) : ℂ) ^ (1 / 2 + u) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ (1 / 2 - v) =
        ((y : ℝ) : ℂ) ^ (u - v - 1) := by
      rw [div_mul_eq_mul_div, cpow_mul_cpow_div_sq hy0]; congr 1; ring
    have e2 : ((y : ℝ) : ℂ) ^ (1 / 2 + u) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ (1 / 2 + v) =
        ((y : ℝ) : ℂ) ^ (u + v - 1) := by
      rw [div_mul_eq_mul_div, cpow_mul_cpow_div_sq hy0]; congr 1; ring
    calc ((y : ℝ) : ℂ) ^ (1 / 2 + u) / ((y : ℝ) : ℂ) ^ 2 *
          (msB v * ((y : ℝ) : ℂ) ^ (1 / 2 - v) + msA v * ((y : ℝ) : ℂ) ^ (1 / 2 + v))
        = msB v * (((y : ℝ) : ℂ) ^ (1 / 2 + u) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ (1 / 2 - v)) +
          msA v * (((y : ℝ) : ℂ) ^ (1 / 2 + u) / ((y : ℝ) : ℂ) ^ 2 * ((y : ℝ) : ℂ) ^ (1 / 2 + v)) := by
          ring
      _ = _ := by rw [e1, e2]
  rw [setIntegral_congr_fun measurableSet_Ioc hinner, ← intervalIntegral.integral_of_le hYpos.le]
  have hi1 : IntervalIntegrable (fun y : ℝ => msB v * ((y : ℝ) : ℂ) ^ (u - v - 1)) volume 0 Y :=
    (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)).const_mul _
  have hi2 : IntervalIntegrable (fun y : ℝ => msA v * ((y : ℝ) : ℂ) ^ (u + v - 1)) volume 0 Y :=
    (intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)).const_mul _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cpow (Or.inl (by simp; linarith)),
    integral_cpow (Or.inl (by simp; linarith))]
  have e3 : u - v - 1 + 1 = u - v := by ring
  have e4 : u + v - 1 + 1 = u + v := by ring
  rw [e3, e4]
  simp only [Complex.ofReal_zero, Complex.zero_cpow huv0, Complex.zero_cpow hupv, sub_zero]
  ring

end

end RHTower
