import GaloisForLFunctions.HTGeometry.BesselArgumentDerivative

/-!
# Pólya's theorem: the zeros of `K_ν(a)` in the order are purely imaginary

For `a > 0` let `K_ν(a) = ∫₀^∞ e^{−a cosh t} cosh(νt) dt` (`modifiedBesselKOrder a ν`).

**Theorem** (`re_eq_zero_of_modifiedBesselKOrder_eq_zero`). If `K_ν(a) = 0` then `Re ν = 0`.
Equivalently, for every `a > 0` the entire function `z ↦ ∫₀^∞ e^{−a cosh t} cos(zt) dt` has only
real zeros.

**Proof (self-adjointness in the argument).** Write `f(x) = K_ν(x)` and `g(x) = K_{ν+1}(x)`.
- The argument derivative and the order recurrence give the first-order system
  `f' = (ν/x) f − g` and `g' = −f − ((ν+1)/x) g`, i.e. Bessel's equation
  `(x f')' = (x + ν²/x) f`.
- Put `h(x) = x f'(x) conj(f(x))`. Then `h' = (x + ν²/x)|f|² + x|f'|²`.
- If `f(a) = 0`, integrate from `a` to `R` and let `R → ∞` (`|f|, |g| ≤ C e^{−x}`):
  `ν² ∫_a^R |f|²/x + ∫_a^R x(|f|² + |f'|²) = h(R) → 0`.
- Since `f` is not identically zero on `(a, ∞)`, `ν²` is real and negative, so `Re ν = 0`.
- Nonvanishing: `Re K_ν(x) > 0` for large `x`. The window `t ≤ δ` contributes at least
  `(δ/4) e^{−x cosh(δ/2)}`, while the tail `t ≥ δ` is at most `B e^{−(x−1) cosh δ}`.
-/

open Complex Real MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The argument derivative of `K_ν` in system form: `∂ₓ K_ν(x) = (ν/x) K_ν(x) − K_{ν+1}(x)`. -/
theorem hasDerivAt_modifiedBesselKOrder_arg {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    HasDerivAt (fun q : ℝ => modifiedBesselKOrder q ν)
      (ν / x * modifiedBesselKOrder x ν - modifiedBesselKOrder x (ν + 1)) x := by
  have h := RHTower.d4BM_hasDerivAt_modifiedBesselKOrder_argument hx ν
  have hrec := modifiedBesselKOrder_add_one hx ν
  convert h using 1
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [hrec]
  field_simp
  ring

/-- The companion derivative: `∂ₓ K_{ν+1}(x) = −K_ν(x) − ((ν+1)/x) K_{ν+1}(x)`. -/
theorem hasDerivAt_modifiedBesselKOrder_arg_succ {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    HasDerivAt (fun q : ℝ => modifiedBesselKOrder q (ν + 1))
      (-modifiedBesselKOrder x ν - (ν + 1) / x * modifiedBesselKOrder x (ν + 1)) x := by
  have h := hasDerivAt_modifiedBesselKOrder_arg hx (ν + 1)
  have hrec := modifiedBesselKOrder_add_one hx (ν + 1)
  convert h using 1
  have e : ν + 1 - 1 = ν := by ring
  rw [hrec, e]
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  field_simp
  ring

/-- The order-independent Schlaefli mass at argument one. -/
def besselOrderUnitMass (ν : ℂ) : ℝ := ∫ t in Ioi (0 : ℝ), ‖besselOrderKernel 1 ν t‖

theorem besselOrderUnitMass_nonneg (ν : ℂ) : 0 ≤ besselOrderUnitMass ν :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => norm_nonneg _

/-- Pointwise exponential comparison of the Schlaefli integrand in the argument. -/
theorem norm_besselOrderKernel_le_exp_mul {x c t : ℝ} (hx : 1 ≤ x)
    (ht : c ≤ Real.cosh t) (ν : ℂ) :
    ‖besselOrderKernel x ν t‖ ≤ Real.exp (-(x - 1) * c) * ‖besselOrderKernel 1 ν t‖ := by
  simp only [besselOrderKernel, norm_mul]
  have e1 : ‖Complex.exp (-(x : ℂ) * Complex.cosh (t : ℂ))‖ = Real.exp (-x * Real.cosh t) := by
    rw [Complex.norm_exp, ← Complex.ofReal_cosh]
    congr 1
    simp
  have e2 : ‖Complex.exp (-((1 : ℝ) : ℂ) * Complex.cosh (t : ℂ))‖ = Real.exp (-Real.cosh t) := by
    rw [Complex.norm_exp, ← Complex.ofReal_cosh]
    congr 1
    simp
  rw [e1, e2, ← mul_assoc, ← Real.exp_add]
  gcongr
  nlinarith

/-- Exponential decay in the argument: `‖K_ν(x)‖ ≤ e^{1−x} · B(ν)` for `x ≥ 1`. -/
theorem norm_modifiedBesselKOrder_le_exp {x : ℝ} (hx : 1 ≤ x) (ν : ℂ) :
    ‖modifiedBesselKOrder x ν‖ ≤ Real.exp (1 - x) * besselOrderUnitMass ν := by
  have hint := (integrableOn_besselOrderKernel one_pos ν).norm
  calc ‖modifiedBesselKOrder x ν‖ ≤ ∫ t in Ioi (0 : ℝ), ‖besselOrderKernel x ν t‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (1 - x) * ‖besselOrderKernel 1 ν t‖ := by
        refine setIntegral_mono_on (integrableOn_besselOrderKernel (by linarith) ν).norm
          (hint.const_mul _) measurableSet_Ioi fun t _ => ?_
        have := norm_besselOrderKernel_le_exp_mul hx (Real.one_le_cosh t) ν
        rwa [show -(x - 1) * 1 = 1 - x by ring] at this
    _ = Real.exp (1 - x) * besselOrderUnitMass ν := by
        rw [MeasureTheory.integral_const_mul]; rfl

/-- `‖cosh w − 1‖ ≤ 2‖w‖` for `‖w‖ ≤ 1`. -/
theorem norm_cosh_sub_one_le {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖Complex.cosh w - 1‖ ≤ 2 * ‖w‖ := by
  have h1 := Complex.norm_exp_sub_one_le hw
  have h2 := Complex.norm_exp_sub_one_le (x := -w) (by rwa [norm_neg])
  rw [norm_neg] at h2
  have e : Complex.cosh w - 1 = ((Complex.exp w - 1) + (Complex.exp (-w) - 1)) / 2 := by
    rw [Complex.cosh]; ring
  rw [e, norm_div, Complex.norm_two]
  have := norm_add_le (Complex.exp w - 1) (Complex.exp (-w) - 1)
  linarith

/-- The Schlaefli integrand is a positive real weight times `cosh(νt)`. -/
theorem besselOrderKernel_eq_ofReal_mul (x : ℝ) (ν : ℂ) (t : ℝ) :
    besselOrderKernel x ν t = ((Real.exp (-x * Real.cosh t) : ℝ) : ℂ) * Complex.cosh (ν * t) := by
  rw [besselOrderKernel, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_cosh]

/-- **`K_ν(x)` has positive real part for large `x`.** -/
theorem eventually_re_modifiedBesselKOrder_pos (ν : ℂ) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → 0 < (modifiedBesselKOrder x ν).re := by
  set δ : ℝ := min 1 (1 / (4 * (‖ν‖ + 1))) with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδν : ‖ν‖ * δ ≤ 1 / 4 := by
    have h := min_le_right 1 (1 / (4 * (‖ν‖ + 1)))
    rw [← hδ] at h
    calc ‖ν‖ * δ ≤ (‖ν‖ + 1) * (1 / (4 * (‖ν‖ + 1))) :=
          mul_le_mul (by linarith) h hδ0.le (by positivity)
      _ = 1 / 4 := by field_simp
  set c₁ : ℝ := Real.cosh (δ / 2) with hc₁
  set c₂ : ℝ := Real.cosh δ with hc₂
  have hc12 : c₁ < c₂ := by
    rw [hc₁, hc₂, Real.cosh_lt_cosh, abs_of_pos (by linarith), abs_of_pos hδ0]; linarith
  set B := besselOrderUnitMass ν with hB
  have hB0 : 0 ≤ B := besselOrderUnitMass_nonneg ν
  set X : ℝ := max 1 (Real.log (4 * (B + 1) * Real.exp c₂ / δ) / (c₂ - c₁)) with hX
  refine ⟨X, le_max_left _ _, fun x hxX => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hxX
  have hx0 : 0 < x := by linarith
  have hint := integrableOn_besselOrderKernel hx0 ν
  -- the real part as an integral
  have hre : (modifiedBesselKOrder x ν).re = ∫ t in Ioi (0 : ℝ), (besselOrderKernel x ν t).re := by
    rw [modifiedBesselKOrder]
    exact (integral_re hint).symm
  have hsplit : Ioi (0 : ℝ) = Ioc 0 δ ∪ Ioi δ := (Ioc_union_Ioi_eq_Ioi hδ0.le).symm
  have hintre : IntegrableOn (fun t => (besselOrderKernel x ν t).re) (Ioi 0) := hint.re
  rw [hre, hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hintre.mono_set (by rw [hsplit]; exact subset_union_left))
    (hintre.mono_set (by rw [hsplit]; exact subset_union_right))]
  -- the window `0 < t ≤ δ`
  have hwin : ∀ t ∈ Ioc (0 : ℝ) δ, Real.exp (-x * Real.cosh t) / 2 ≤
      (besselOrderKernel x ν t).re := by
    intro t ht
    rw [besselOrderKernel_eq_ofReal_mul, Complex.re_ofReal_mul]
    have hsmall : ‖ν * (t : ℂ)‖ ≤ 1 / 4 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      calc ‖ν‖ * t ≤ ‖ν‖ * δ := mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)
        _ ≤ 1 / 4 := hδν
    have hc := norm_cosh_sub_one_le (le_trans hsmall (by norm_num))
    have hre1 : 1 / 2 ≤ (Complex.cosh (ν * t)).re := by
      have h := Complex.abs_re_le_norm (Complex.cosh (ν * t) - 1)
      rw [Complex.sub_re, Complex.one_re] at h
      have := abs_le.mp (h.trans (hc.trans (by linarith : 2 * ‖ν * (t : ℂ)‖ ≤ 1 / 2)))
      linarith [this.1]
    have he := Real.exp_pos (-x * Real.cosh t)
    nlinarith
  have hhead : δ / 4 * Real.exp (-x * c₁) ≤
      ∫ t in Ioc (0 : ℝ) δ, (besselOrderKernel x ν t).re := by
    have hint1 : IntegrableOn (fun t => (besselOrderKernel x ν t).re) (Ioc 0 δ) :=
      hintre.mono_set Ioc_subset_Ioi_self
    calc δ / 4 * Real.exp (-x * c₁) = ∫ _t in Ioc (0 : ℝ) (δ / 2), Real.exp (-x * c₁) / 2 := by
          rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith),
            smul_eq_mul]; ring
      _ ≤ ∫ t in Ioc (0 : ℝ) (δ / 2), (besselOrderKernel x ν t).re := by
          refine setIntegral_mono_on (integrableOn_const (by simp))
            (hint1.mono_set (Ioc_subset_Ioc_right (by linarith))) measurableSet_Ioc fun t ht => ?_
          refine le_trans ?_ (hwin t ⟨ht.1, by linarith [ht.2]⟩)
          have hcosh : Real.cosh t ≤ c₁ := by
            rw [hc₁, Real.cosh_le_cosh, abs_of_pos ht.1, abs_of_pos (by linarith)]; exact ht.2
          have hm : -x * c₁ ≤ -x * Real.cosh t := by nlinarith
          exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hm) (by norm_num)
      _ ≤ ∫ t in Ioc (0 : ℝ) δ, (besselOrderKernel x ν t).re := by
          refine setIntegral_mono_set hint1 ?_ (Ioc_subset_Ioc_right (by linarith)).eventuallyLE
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact le_trans (by positivity) (hwin t ht)
  -- the tail `t > δ`
  have htail : -(B * Real.exp (-(x - 1) * c₂)) ≤
      ∫ t in Ioi δ, (besselOrderKernel x ν t).re := by
    have hint2 : IntegrableOn (besselOrderKernel x ν) (Ioi δ) :=
      hint.mono_set (Ioi_subset_Ioi hδ0.le)
    have hnorm : ‖∫ t in Ioi δ, (besselOrderKernel x ν t).re‖ ≤ B * Real.exp (-(x - 1) * c₂) := by
      calc ‖∫ t in Ioi δ, (besselOrderKernel x ν t).re‖
          ≤ ∫ t in Ioi δ, ‖(besselOrderKernel x ν t).re‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ t in Ioi δ, Real.exp (-(x - 1) * c₂) * ‖besselOrderKernel 1 ν t‖ := by
            refine setIntegral_mono_on hint2.re.norm
              (((integrableOn_besselOrderKernel one_pos ν).mono_set
                (Ioi_subset_Ioi hδ0.le)).norm.const_mul _) measurableSet_Ioi fun t ht => ?_
            refine le_trans ?_ (norm_besselOrderKernel_le_exp_mul hx1 ?_ ν)
            · rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
            · rw [hc₂, Real.cosh_le_cosh, abs_of_pos hδ0, abs_of_pos (lt_trans hδ0 ht)]
              exact ht.le
        _ = Real.exp (-(x - 1) * c₂) * ∫ t in Ioi δ, ‖besselOrderKernel 1 ν t‖ :=
            MeasureTheory.integral_const_mul _ _
        _ ≤ Real.exp (-(x - 1) * c₂) * B := by
            refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
            exact setIntegral_mono_set (integrableOn_besselOrderKernel one_pos ν).norm
              (Eventually.of_forall fun _ => norm_nonneg _)
              (Ioi_subset_Ioi hδ0.le).eventuallyLE
        _ = B * Real.exp (-(x - 1) * c₂) := mul_comm _ _
    rw [Real.norm_eq_abs] at hnorm
    linarith [(abs_le.mp hnorm).1]
  -- the head beats the tail
  have hgap : 0 < c₂ - c₁ := by linarith
  have hxlog : Real.log (4 * (B + 1) * Real.exp c₂ / δ) ≤ x * (c₂ - c₁) := by
    have h := le_trans (le_max_right _ _) hxX
    rw [div_le_iff₀ hgap] at h
    linarith [le_max_right 1 (Real.log (4 * (B + 1) * Real.exp c₂ / δ) / (c₂ - c₁))]
  have hexp : 4 * (B + 1) * Real.exp c₂ / δ ≤ Real.exp (x * (c₂ - c₁)) := by
    rw [← Real.log_le_iff_le_exp (by positivity)]; exact hxlog
  have hkey : B * Real.exp (-(x - 1) * c₂) < δ / 4 * Real.exp (-x * c₁) := by
    have e1 : Real.exp (-(x - 1) * c₂) = Real.exp c₂ * Real.exp (-(x * c₂)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-x * c₁) = Real.exp (x * (c₂ - c₁)) * Real.exp (-(x * c₂)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e1, e2]
    have hpos := Real.exp_pos (-(x * c₂))
    have hc2pos := Real.exp_pos c₂
    rw [div_le_iff₀ hδ0] at hexp
    nlinarith
  linarith

/-- The energy density `h(x) = x · ∂ₓK_ν(x) · conj K_ν(x)`, written through the system. -/
def besselEnergyFlux (ν : ℂ) (x : ℝ) : ℂ :=
  (ν * modifiedBesselKOrder x ν - x * modifiedBesselKOrder x (ν + 1)) *
    (starRingEnd ℂ) (modifiedBesselKOrder x ν)

/-- The argument derivative `∂ₓK_ν(x) = (ν/x) K_ν(x) − K_{ν+1}(x)`, as a function. -/
def besselArgDeriv (ν : ℂ) (x : ℝ) : ℂ :=
  ν / x * modifiedBesselKOrder x ν - modifiedBesselKOrder x (ν + 1)

/-- **Energy identity.** `h' = ν² |K_ν|²/x + x(|K_ν|² + |∂ₓK_ν|²)`. -/
theorem hasDerivAt_besselEnergyFlux {x : ℝ} (hx : 0 < x) (ν : ℂ) :
    HasDerivAt (besselEnergyFlux ν)
      (ν ^ 2 * (((‖modifiedBesselKOrder x ν‖ ^ 2 / x : ℝ)) : ℂ) +
        (((x * ‖modifiedBesselKOrder x ν‖ ^ 2 + x * ‖besselArgDeriv ν x‖ ^ 2 : ℝ)) : ℂ)) x := by
  have hf := hasDerivAt_modifiedBesselKOrder_arg hx ν
  have hg := hasDerivAt_modifiedBesselKOrder_arg_succ hx ν
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hid : HasDerivAt (fun q : ℝ => (q : ℂ)) 1 x := by
    simpa using (hasDerivAt_id x).ofReal_comp
  have h1 : HasDerivAt (fun q : ℝ => ν * modifiedBesselKOrder q ν - (q : ℂ) * modifiedBesselKOrder q (ν + 1))
      (ν * (ν / x * modifiedBesselKOrder x ν - modifiedBesselKOrder x (ν + 1)) -
        (1 * modifiedBesselKOrder x (ν + 1) + (x : ℂ) *
          (-modifiedBesselKOrder x ν - (ν + 1) / x * modifiedBesselKOrder x (ν + 1)))) x :=
    (hf.const_mul ν).sub (hid.mul hg)
  have h2 := hf.star
  have h : HasDerivAt (besselEnergyFlux ν) _ x := h1.mul h2
  refine h.congr_deriv ?_
  set f := modifiedBesselKOrder x ν
  set g := modifiedBesselKOrder x (ν + 1)
  have hstar : star (ν / x * f - g) = (starRingEnd ℂ) (besselArgDeriv ν x) := rfl
  rw [hstar]
  push_cast
  rw [← Complex.mul_conj', ← Complex.mul_conj']
  simp only [besselArgDeriv, map_sub, map_mul, map_div₀, Complex.conj_ofReal]
  field_simp
  ring

/-- **Pólya's theorem.** For `a > 0`, every zero `ν` of `K_ν(a)` is purely imaginary. -/
theorem re_eq_zero_of_modifiedBesselKOrder_eq_zero {a : ℝ} (ha : 0 < a) {ν : ℂ}
    (h0 : modifiedBesselKOrder a ν = 0) : ν.re = 0 := by
  -- continuity of the pieces on `(0, ∞)`
  have hfc : ∀ x : ℝ, 0 < x → ContinuousAt (fun q : ℝ => modifiedBesselKOrder q ν) x :=
    fun x hx => (hasDerivAt_modifiedBesselKOrder_arg hx ν).continuousAt
  have hgc : ∀ x : ℝ, 0 < x → ContinuousAt (fun q : ℝ => modifiedBesselKOrder q (ν + 1)) x :=
    fun x hx => (hasDerivAt_modifiedBesselKOrder_arg_succ hx ν).continuousAt
  have hDc : ∀ x : ℝ, 0 < x → ContinuousAt (besselArgDeriv ν) x := by
    intro x hx
    unfold besselArgDeriv
    refine ((continuousAt_const.div (Complex.continuous_ofReal.continuousAt)
      (by exact_mod_cast hx.ne')).mul (hfc x hx)).sub (hgc x hx)
  set φ : ℝ → ℝ := fun x => ‖modifiedBesselKOrder x ν‖ ^ 2 / x with hφ
  set ψ : ℝ → ℝ := fun x => x * ‖modifiedBesselKOrder x ν‖ ^ 2 + x * ‖besselArgDeriv ν x‖ ^ 2
    with hψ
  have hφc : ∀ x : ℝ, 0 < x → ContinuousAt φ x := fun x hx =>
    ((hfc x hx).norm.pow 2).div continuousAt_id hx.ne'
  have hψc : ∀ x : ℝ, 0 < x → ContinuousAt ψ x := fun x hx =>
    (continuousAt_id.mul ((hfc x hx).norm.pow 2)).add (continuousAt_id.mul ((hDc x hx).norm.pow 2))
  -- the integrated energy identity
  have hFTC : ∀ R : ℝ, a ≤ R →
      besselEnergyFlux ν R = ν ^ 2 * ((∫ x in a..R, φ x : ℝ) : ℂ) + ((∫ x in a..R, ψ x : ℝ) : ℂ) := by
    intro R haR
    have hpos : ∀ x ∈ uIcc a R, 0 < x := fun x hx => by
      rw [uIcc_of_le haR] at hx; linarith [hx.1]
    have hφi : IntervalIntegrable (fun x => ((φ x : ℝ) : ℂ)) volume a R :=
      (ContinuousOn.intervalIntegrable fun x hx =>
        (Complex.continuous_ofReal.continuousAt.comp (hφc x (hpos x hx))).continuousWithinAt)
    have hψi : IntervalIntegrable (fun x => ((ψ x : ℝ) : ℂ)) volume a R :=
      (ContinuousOn.intervalIntegrable fun x hx =>
        (Complex.continuous_ofReal.continuousAt.comp (hψc x (hpos x hx))).continuousWithinAt)
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hasDerivAt_besselEnergyFlux (hpos x hx) ν)
      ((hφi.const_mul (ν ^ 2)).add hψi)
    have hfa : besselEnergyFlux ν a = 0 := by rw [besselEnergyFlux, h0]; simp
    rw [hfa, sub_zero] at h
    rw [← h, intervalIntegral.integral_add (hφi.const_mul (ν ^ 2)) hψi,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      intervalIntegral.integral_ofReal]
  -- decay of the flux
  have hdecay : Tendsto (besselEnergyFlux ν) atTop (𝓝 0) := by
    set M := besselOrderUnitMass ν
    set M' := besselOrderUnitMass (ν + 1)
    have hM := besselOrderUnitMass_nonneg ν
    have hM' := besselOrderUnitMass_nonneg (ν + 1)
    have hbound : ∀ R : ℝ, 1 ≤ R → ‖besselEnergyFlux ν R‖ ≤
        (‖ν‖ * M * M * Real.exp 2) * Real.exp (-R) + (M' * M * Real.exp 2) * (R * Real.exp (-R)) := by
      intro R hR
      have hf := norm_modifiedBesselKOrder_le_exp hR ν
      have hg := norm_modifiedBesselKOrder_le_exp hR (ν + 1)
      have he : Real.exp (1 - R) * Real.exp (1 - R) ≤ Real.exp 2 * Real.exp (-R) := by
        rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
      have hR0 : (0 : ℝ) ≤ R := by linarith
      have hE := Real.exp_pos (1 - R)
      rw [besselEnergyFlux, norm_mul, Complex.norm_conj]
      calc ‖ν * modifiedBesselKOrder R ν - (R : ℂ) * modifiedBesselKOrder R (ν + 1)‖ *
            ‖modifiedBesselKOrder R ν‖
          ≤ (‖ν‖ * ‖modifiedBesselKOrder R ν‖ + R * ‖modifiedBesselKOrder R (ν + 1)‖) *
              ‖modifiedBesselKOrder R ν‖ := by
            gcongr
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0]
        _ ≤ (‖ν‖ * (Real.exp (1 - R) * M) + R * (Real.exp (1 - R) * M')) *
              (Real.exp (1 - R) * M) := by gcongr
        _ = (‖ν‖ * M * M + R * M' * M) * (Real.exp (1 - R) * Real.exp (1 - R)) := by ring
        _ ≤ (‖ν‖ * M * M + R * M' * M) * (Real.exp 2 * Real.exp (-R)) := by gcongr
        _ = _ := by ring
    have h1 : Tendsto (fun R : ℝ => Real.exp (-R)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
    have h2 : Tendsto (fun R : ℝ => R * Real.exp (-R)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hsum : Tendsto (fun R : ℝ => (‖ν‖ * M * M * Real.exp 2) * Real.exp (-R) +
        (M' * M * Real.exp 2) * (R * Real.exp (-R))) atTop (𝓝 0) := by
      simpa using (h1.const_mul _).add (h2.const_mul _)
    refine squeeze_zero_norm' ?_ hsum
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR using hbound R hR
  -- a point where `K_ν` does not vanish
  obtain ⟨X, hX1, hXpos⟩ := eventually_re_modifiedBesselKOrder_pos ν
  set x₀ : ℝ := max X (a + 1) with hx₀
  have hx₀a : a < x₀ := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hx₀0 : 0 < x₀ := by linarith
  have hfx₀ : modifiedBesselKOrder x₀ ν ≠ 0 := fun h => by
    have := hXpos x₀ (le_max_left _ _); rw [h, Complex.zero_re] at this; exact lt_irrefl 0 this
  set R₁ : ℝ := x₀ + 1 with hR₁
  have hA₀ : 0 < ∫ x in a..R₁, φ x := by
    refine intervalIntegral.integral_pos (by linarith) (fun x hx => (hφc x (by linarith [hx.1])).continuousWithinAt)
      (fun x hx => div_nonneg (sq_nonneg _) (by linarith [hx.1])) ⟨x₀, ⟨hx₀a.le, by linarith⟩, ?_⟩
    simp only [hφ]
    exact div_pos (pow_pos (norm_pos_iff.mpr hfx₀) 2) hx₀0
  have hB₀ : 0 < ∫ x in a..R₁, ψ x := by
    refine intervalIntegral.integral_pos (by linarith) (fun x hx => (hψc x (by linarith [hx.1])).continuousWithinAt)
      (fun x hx => by
        have : 0 < x := by linarith [hx.1]
        show 0 ≤ x * ‖modifiedBesselKOrder x ν‖ ^ 2 + x * ‖besselArgDeriv ν x‖ ^ 2
        positivity) ⟨x₀, ⟨hx₀a.le, by linarith⟩, ?_⟩
    simp only [hψ]
    have := mul_pos hx₀0 (pow_pos (norm_pos_iff.mpr hfx₀) 2)
    nlinarith [mul_nonneg hx₀0.le (sq_nonneg ‖besselArgDeriv ν x₀‖)]
  have hAmono : ∀ R : ℝ, R₁ ≤ R → (∫ x in a..R₁, φ x) ≤ ∫ x in a..R, φ x := by
    intro R hR
    refine intervalIntegral.integral_mono_interval le_rfl (by linarith) hR ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have : 0 < x := by linarith [hx.1]
      exact div_nonneg (sq_nonneg _) this.le
    · exact ContinuousOn.intervalIntegrable fun x hx => (hφc x (by
        rw [uIcc_of_le (by linarith)] at hx; linarith [hx.1])).continuousWithinAt
  have hBmono : ∀ R : ℝ, R₁ ≤ R → (∫ x in a..R₁, ψ x) ≤ ∫ x in a..R, ψ x := by
    intro R hR
    refine intervalIntegral.integral_mono_interval le_rfl (by linarith) hR ?_ ?_
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have : 0 < x := by linarith [hx.1]
      show 0 ≤ x * ‖modifiedBesselKOrder x ν‖ ^ 2 + x * ‖besselArgDeriv ν x‖ ^ 2
      positivity
    · exact ContinuousOn.intervalIntegrable fun x hx => (hψc x (by
        rw [uIcc_of_le (by linarith)] at hx; linarith [hx.1])).continuousWithinAt
  -- `ν²` is real
  have him : (ν ^ 2).im = 0 := by
    by_contra hne
    have hc : 0 < |(ν ^ 2).im| * (∫ x in a..R₁, φ x) := mul_pos (abs_pos.mpr hne) hA₀
    obtain ⟨R, hR⟩ := (Metric.tendsto_atTop.mp hdecay) _ hc
    have hRR := hR (max R R₁) (le_max_left _ _)
    rw [dist_zero_right, hFTC (max R R₁) (by linarith [le_max_right R R₁])] at hRR
    have hle := Complex.abs_im_le_norm (ν ^ 2 * ((∫ x in a..max R R₁, φ x : ℝ) : ℂ) +
      ((∫ x in a..max R R₁, ψ x : ℝ) : ℂ))
    rw [Complex.add_im, Complex.im_mul_ofReal, Complex.ofReal_im, add_zero, abs_mul,
      abs_of_nonneg (le_trans hA₀.le (hAmono _ (le_max_right _ _)))] at hle
    have := mul_le_mul_of_nonneg_left (hAmono _ (le_max_right R R₁)) (abs_nonneg (ν ^ 2).im)
    linarith
  -- `ν²` is negative
  have hre : (ν ^ 2).re < 0 := by
    by_contra hge
    push Not at hge
    obtain ⟨R, hR⟩ := (Metric.tendsto_atTop.mp hdecay) _ hB₀
    have hRR := hR (max R R₁) (le_max_left _ _)
    rw [dist_zero_right, hFTC (max R R₁) (by linarith [le_max_right R R₁])] at hRR
    have hle := Complex.re_le_norm (ν ^ 2 * ((∫ x in a..max R R₁, φ x : ℝ) : ℂ) +
      ((∫ x in a..max R R₁, ψ x : ℝ) : ℂ))
    rw [Complex.add_re, Complex.re_mul_ofReal, Complex.ofReal_re] at hle
    have hA := le_trans hA₀.le (hAmono _ (le_max_right R R₁))
    have := mul_nonneg hge hA
    linarith [hBmono _ (le_max_right R R₁)]
  -- conclusion
  have e1 : (ν ^ 2).im = 2 * ν.re * ν.im := by rw [sq, Complex.mul_im]; ring
  have e2 : (ν ^ 2).re = ν.re ^ 2 - ν.im ^ 2 := by rw [sq, Complex.mul_re]; ring
  rw [e1] at him
  rw [e2] at hre
  rcases mul_eq_zero.mp him with h | h
  · linarith
  · rw [h] at hre; nlinarith [sq_nonneg ν.re]

/-- **Pólya's real-zero theorem, Fourier form.** For `a > 0`, every zero of
`z ↦ ∫₀^∞ e^{−a cosh t} cos(zt) dt = K_{iz}(a)` is real. -/
theorem im_eq_zero_of_modifiedBesselKOrder_I_mul_eq_zero {a : ℝ} (ha : 0 < a) {z : ℂ}
    (h0 : modifiedBesselKOrder a (Complex.I * z) = 0) : z.im = 0 := by
  have := re_eq_zero_of_modifiedBesselKOrder_eq_zero ha h0
  simpa using this

end

end GaloisForLFunctions.HTGeometry
