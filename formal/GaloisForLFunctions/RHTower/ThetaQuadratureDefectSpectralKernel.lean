import GaloisForLFunctions.RHTower.ThetaDeletionInversionCommutator

/-!
# The Gaussian quadrature defect and the spectral form of the commutator kernel

With `y = e^{|t|}`, the quadrature defect
`B(t) = e^{-|t|/4} - e^{|t|/4}(Θ(y) - 1) = 2 y^{1/4} [∫₀^∞ e^{-πyx²} dx - Σ_{n≥1} e^{-πyn²}]
      = 4π y^{5/4} ∫₀^∞ {x} x e^{-πyx²} dx`
(per-interval integration by parts against `-d/dx e^{-πyx²}`) is even, continuous, strictly
positive and bounded by `e^{-|t|/4}`.  The profile `P(t) = e^{t/4} Θ(e^t)` equals
`2 cosh(t/4) - B(t)`, so the commutator kernel is
`K(a, b) = 4 sinh(a/4) sinh(b/4) + B(a - b) - B(a + b)`; in particular
`K(A+x, A+y) = 4 sinh((A+x)/4) sinh((A+y)/4) + B(x - y) - B(2A + x + y)`.

The Laplace transform of the tail is the Ward Mellin integral, `∫₀^∞ e^{-st} R(t) dt = M_{2is}`,
and with `Ξ(z) = 1/2 - ((z² + 1/4)/4)(M_z + M_{-z})` this gives
`B̂(τ) = ∫ B(t) e^{-iτt} dt = Ξ(2τ)/(τ² + 1/16)`.  The weight `w(τ) = Ξ(2τ)/(τ² + 1/16)` is
continuous and integrable (`|Ξ(x)| ≤ ∫ k`), and Fourier inversion gives
`B(t) = (1/π) ∫₀^∞ w(τ) cos(τt) dτ`, hence
`K(a, b) = 4 sinh(a/4) sinh(b/4) + (2/π) ∫₀^∞ w(τ) sin(aτ) sin(bτ) dτ`,
the finite quadratic form
`Σ c_j c_k K(a_j, a_k) = 4 (Σ c_j sinh(a_j/4))² + (2/π) ∫₀^∞ w(τ) (Σ c_j sin(a_j τ))² dτ`,
and its continuum version for continuous compactly supported test functions.
-/
open Complex Filter Topology Set MeasureTheory HurwitzZeta

noncomputable section

namespace RHTower

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The Gaussian quadrature defect -/

/-- The quadrature defect `B(t) = e^{-|t|/4} - e^{|t|/4} (Θ(e^{|t|}) - 1)`. -/
def quadratureDefect (t : ℝ) : ℝ := Real.exp (-(|t| / 4)) - thetaLogTail |t|

theorem quadratureDefect_neg (t : ℝ) : quadratureDefect (-t) = quadratureDefect t := by
  simp only [quadratureDefect, abs_neg]

theorem continuous_quadratureDefect : Continuous quadratureDefect := by
  have := continuous_thetaLogTail
  unfold quadratureDefect
  fun_prop

/-- `P(t) = 2 cosh(t/4) - B(t)`. -/
theorem thetaLogProfile_eq_cosh_sub (t : ℝ) :
    thetaLogProfile t = 2 * Real.cosh (t / 4) - quadratureDefect t := by
  rw [← thetaLogProfile_abs_eq, thetaLogProfile_eq_add, quadratureDefect, Real.cosh_eq]
  rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; ring_nf
  · rw [h]; ring_nf

/-- `K(a, b) = 4 sinh(a/4) sinh(b/4) + B(a - b) - B(a + b)`. -/
theorem deletionInversionKernel_eq_sinh (a b : ℝ) :
    deletionInversionKernel a b =
      4 * Real.sinh (a / 4) * Real.sinh (b / 4) + quadratureDefect (a - b) -
        quadratureDefect (a + b) := by
  rw [deletionInversionKernel, thetaLogProfile_eq_cosh_sub, thetaLogProfile_eq_cosh_sub,
    show (a + b) / 4 = a / 4 + b / 4 by ring, show (a - b) / 4 = a / 4 - b / 4 by ring,
    Real.cosh_add, Real.cosh_sub]
  ring

/-- **Translated kernel (16).** `K(A+x, A+y) = 4 sinh((A+x)/4) sinh((A+y)/4) + B(x-y) - B(2A+x+y)`. -/
theorem deletionInversionKernel_translate (A x y : ℝ) :
    deletionInversionKernel (A + x) (A + y) =
      4 * Real.sinh ((A + x) / 4) * Real.sinh ((A + y) / 4) + quadratureDefect (x - y) -
        quadratureDefect (2 * A + x + y) := by
  rw [deletionInversionKernel_eq_sinh, show A + x - (A + y) = x - y by ring,
    show A + x + (A + y) = 2 * A + x + y by ring]

theorem quadratureDefect_le (t : ℝ) : quadratureDefect t ≤ Real.exp (-(|t| / 4)) := by
  have := thetaLogTail_pos |t|
  rw [quadratureDefect]; linarith

/-! ## Continuum-minus-lattice form -/

/-- `∫₀^∞ h = Σ_n ∫_n^{n+1} h` for integrable `h ≥ 0`. -/
theorem hasSum_intervalIntegral_of_nonneg {h : ℝ → ℝ} (hint : IntegrableOn h (Ioi 0))
    (hnn : ∀ x, 0 ≤ x → 0 ≤ h x) :
    HasSum (fun n : ℕ => ∫ x in (n : ℝ)..(n + 1), h x) (∫ x in Ioi 0, h x) := by
  have hII : ∀ k : ℕ, IntervalIntegrable h volume (k : ℝ) ((k : ℝ) + 1) := by
    intro k
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hint.mono_set fun x hx => lt_of_le_of_lt (Nat.cast_nonneg k) hx.1
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun k => intervalIntegral.integral_nonneg (by linarith) fun x hx =>
      hnn x ((Nat.cast_nonneg k).trans hx.1))]
  have hsum : ∀ n : ℕ, (∑ k ∈ Finset.range n, ∫ x in (k : ℝ)..(k + 1), h x) =
      ∫ x in (0 : ℝ)..(n : ℝ), h x := by
    intro n
    have := intervalIntegral.sum_integral_adjacent_intervals (f := h) (μ := volume)
      (a := fun k : ℕ => (k : ℝ)) (n := n) (fun k _ => by simpa using hII k)
    simpa using this
  simp only [hsum]
  exact intervalIntegral_tendsto_integral_Ioi 0 hint tendsto_natCast_atTop_atTop

/-- Per-interval integration by parts:
`∫_n^{n+1} (x - n) · 2πy x e^{-πyx²} dx = ∫_n^{n+1} e^{-πyx²} dx - e^{-πy(n+1)²}`. -/
theorem integral_sub_mul_gaussian_deriv (y : ℝ) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1), (x - n) * (2 * Real.pi * y * x * Real.exp (-(Real.pi * y) * x ^ 2)) =
      (∫ x in (n : ℝ)..(n + 1), Real.exp (-(Real.pi * y) * x ^ 2)) -
        Real.exp (-(Real.pi * y) * ((n : ℝ) + 1) ^ 2) := by
  have hu : ∀ x ∈ uIcc (n : ℝ) (n + 1), HasDerivAt (fun x : ℝ => x - n) 1 x :=
    fun x _ => (hasDerivAt_id x).sub_const _
  have hv : ∀ x ∈ uIcc (n : ℝ) (n + 1),
      HasDerivAt (fun x : ℝ => -Real.exp (-(Real.pi * y) * x ^ 2))
        (2 * Real.pi * y * x * Real.exp (-(Real.pi * y) * x ^ 2)) x := by
    intro x _
    have h := (((hasDerivAt_pow 2 x).const_mul (-(Real.pi * y))).exp).neg
    refine h.congr_deriv ?_
    ring
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (intervalIntegrable_const) ((by fun_prop : Continuous fun x : ℝ =>
      2 * Real.pi * y * x * Real.exp (-(Real.pi * y) * x ^ 2)).intervalIntegrable _ _)
  rw [h]
  simp only [one_mul, sub_self, zero_mul, intervalIntegral.integral_neg]
  ring

theorem integral_fract_eq_sub_on (h : ℝ → ℝ) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1), Int.fract x * h x = ∫ x in (n : ℝ)..(n + 1), (x - n) * h x := by
  rw [intervalIntegral.integral_of_le (by linarith), intervalIntegral.integral_of_le (by linarith),
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
  have hfl : Int.floor x = (n : ℤ) := by
    rw [Int.floor_eq_iff]; push_cast; exact ⟨hx.1.le, hx.2⟩
  rw [Int.fract, hfl]
  push_cast
  ring

/-- **Continuum minus lattice.** For `y > 0`,
`∫₀^∞ e^{-πyx²} dx - Σ_{n≥1} e^{-πyn²} = 2πy ∫₀^∞ {x} x e^{-πyx²} dx`. -/
theorem integral_gaussian_sub_tsum_eq_fract {y : ℝ} (hy : 0 < y) :
    (∫ x in Ioi 0, Real.exp (-(Real.pi * y) * x ^ 2)) -
        ∑' n : ℕ, Real.exp (-(Real.pi * y) * ((n : ℝ) + 1) ^ 2) =
      2 * Real.pi * y * ∫ x in Ioi 0, Int.fract x * x * Real.exp (-(Real.pi * y) * x ^ 2) := by
  have hb : 0 < Real.pi * y := mul_pos Real.pi_pos hy
  have hf : IntegrableOn (fun x => Real.exp (-(Real.pi * y) * x ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have hg : IntegrableOn (fun x => Int.fract x * (2 * Real.pi * y * x *
      Real.exp (-(Real.pi * y) * x ^ 2))) (Ioi 0) := by
    have hdom : Integrable (fun x => 2 * Real.pi * y * (x * Real.exp (-(Real.pi * y) * x ^ 2))) :=
      (integrable_mul_exp_neg_mul_sq hb).const_mul _
    refine hdom.integrableOn.mono' ?_ ?_
    · exact (measurable_fract.mul (by fun_prop : Continuous fun x : ℝ =>
        2 * Real.pi * y * x * Real.exp (-(Real.pi * y) * x ^ 2)).measurable).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
      have hx0 : (0 : ℝ) < x := hx
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Int.fract_nonneg x),
        abs_of_nonneg (by positivity)]
      calc Int.fract x * (2 * Real.pi * y * x * Real.exp (-(Real.pi * y) * x ^ 2))
          ≤ 1 * (2 * Real.pi * y * x * Real.exp (-(Real.pi * y) * x ^ 2)) :=
            mul_le_mul_of_nonneg_right (Int.fract_lt_one x).le (by positivity)
        _ = _ := by ring
  have h1 := hasSum_intervalIntegral_of_nonneg hg fun x hx =>
    mul_nonneg (Int.fract_nonneg x) (by positivity)
  have h2 := hasSum_intervalIntegral_of_nonneg hf fun x _ => (Real.exp_pos _).le
  have h3 : HasSum (fun n : ℕ => Real.exp (-(Real.pi * y) * ((n : ℝ) + 1) ^ 2))
      (∑' n : ℕ, Real.exp (-(Real.pi * y) * ((n : ℝ) + 1) ^ 2)) := by
    have := (hasSum_evenKernel_zero_sub_one hy).summable.div_const 2
    refine (this.congr fun n => ?_).hasSum
    rw [neg_mul]; ring_nf
  have h4 := h2.sub h3
  have h5 : HasSum (fun n : ℕ => ∫ x in (n : ℝ)..(n + 1), Int.fract x *
      (2 * Real.pi * y * x * Real.exp (-(Real.pi * y) * x ^ 2)))
      ((∫ x in Ioi 0, Real.exp (-(Real.pi * y) * x ^ 2)) -
        ∑' n : ℕ, Real.exp (-(Real.pi * y) * ((n : ℝ) + 1) ^ 2)) := by
    refine h4.congr_fun fun n => ?_
    rw [integral_fract_eq_sub_on, integral_sub_mul_gaussian_deriv]
  rw [h5.unique h1, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring

/-- **Gaussian quadrature defect (11).** With `y = e^{|t|}`,
`B(t) = 2 y^{1/4} [∫₀^∞ e^{-πyx²} dx - Σ_{n≥1} e^{-πyn²}] = 4π y^{5/4} ∫₀^∞ {x} x e^{-πyx²} dx`. -/
theorem quadratureDefect_eq_gaussian (t : ℝ) :
    quadratureDefect t = 2 * Real.exp (|t| / 4) *
      ((∫ x in Ioi 0, Real.exp (-(Real.pi * Real.exp |t|) * x ^ 2)) -
        ∑' n : ℕ, Real.exp (-(Real.pi * Real.exp |t|) * ((n : ℝ) + 1) ^ 2)) := by
  have hy := Real.exp_pos |t|
  have hint := integral_gaussian_Ioi (Real.pi * Real.exp |t|)
  have hsq : Real.sqrt (Real.pi / (Real.pi * Real.exp |t|)) = Real.exp (-(|t| / 2)) := by
    rw [div_mul_cancel_left₀ Real.pi_ne_zero, ← Real.exp_neg, Real.sqrt_eq_rpow,
      ← Real.exp_mul]
    ring_nf
  rw [hsq] at hint
  have hsum := (hasSum_evenKernel_zero_sub_one hy).tsum_eq
  rw [tsum_mul_left] at hsum
  have hsum' : (∑' n : ℕ, Real.exp (-(Real.pi * Real.exp |t|) * ((n : ℝ) + 1) ^ 2)) =
      (Θ (Real.exp |t|) - 1) / 2 := by
    rw [← hsum]
    have : (fun n : ℕ => Real.exp (-(Real.pi * Real.exp |t|) * ((n : ℝ) + 1) ^ 2)) =
        fun n : ℕ => Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp |t|)) := by
      funext n; congr 1; ring
    rw [this]; ring
  rw [hint, hsum', quadratureDefect, thetaLogTail]
  have he : Real.exp (|t| / 4) * Real.exp (-(|t| / 2)) = Real.exp (-(|t| / 4)) := by
    rw [← Real.exp_add]; ring_nf
  rw [← he]
  ring

theorem quadratureDefect_eq_fract (t : ℝ) :
    quadratureDefect t = 4 * Real.pi * Real.exp (5 * |t| / 4) *
      ∫ x in Ioi 0, Int.fract x * x * Real.exp (-(Real.pi * Real.exp |t|) * x ^ 2) := by
  rw [quadratureDefect_eq_gaussian, integral_gaussian_sub_tsum_eq_fract (Real.exp_pos _)]
  have he : Real.exp (|t| / 4) * Real.exp |t| = Real.exp (5 * |t| / 4) := by
    rw [← Real.exp_add]; ring_nf
  rw [← he]
  ring

/-- The quadrature defect is strictly positive. -/
theorem quadratureDefect_pos (t : ℝ) : 0 < quadratureDefect t := by
  rw [quadratureDefect_eq_fract]
  refine mul_pos (by positivity) ?_
  set y := Real.exp |t|
  have hy : 0 < y := Real.exp_pos _
  have hb : 0 < Real.pi * y := mul_pos Real.pi_pos hy
  have hint : IntegrableOn (fun x => Int.fract x * x * Real.exp (-(Real.pi * y) * x ^ 2))
      (Ioi 0) := by
    refine (integrable_mul_exp_neg_mul_sq hb).integrableOn.mono' ?_ ?_
    · exact ((measurable_fract.mul measurable_id).mul (by fun_prop : Continuous fun x : ℝ =>
        Real.exp (-(Real.pi * y) * x ^ 2)).measurable).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
      have hx0 : (0 : ℝ) < x := hx
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Int.fract_nonneg x), abs_of_pos hx0,
        abs_of_pos (Real.exp_pos _)]
      calc Int.fract x * x * Real.exp (-(Real.pi * y) * x ^ 2)
          ≤ 1 * x * Real.exp (-(Real.pi * y) * x ^ 2) := by
            gcongr; exact (Int.fract_lt_one x).le
        _ = _ := by ring
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun x => Int.fract x * x * Real.exp (-(Real.pi * y) * x ^ 2) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx =>
      mul_nonneg (mul_nonneg (Int.fract_nonneg x) (le_of_lt hx)) (Real.exp_pos _).le)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsub : Ioo (0 : ℝ) 1 ⊆ Function.support
      (fun x => Int.fract x * x * Real.exp (-(Real.pi * y) * x ^ 2)) ∩ Ioi 0 := by
    intro x hx
    refine ⟨?_, hx.1⟩
    have hfr : Int.fract x = x := by
      rw [Int.fract_eq_iff]; exact ⟨hx.1.le, hx.2, 0, by simp⟩
    simp only [Function.mem_support, hfr]
    exact (mul_pos (mul_pos hx.1 hx.1) (Real.exp_pos _)).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  norm_num

theorem abs_quadratureDefect_le (t : ℝ) : |quadratureDefect t| ≤ Real.exp (-(|t| / 4)) := by
  rw [abs_of_pos (quadratureDefect_pos t)]
  exact quadratureDefect_le t

theorem integrable_exp_neg_abs_div_four : Integrable fun t : ℝ => Real.exp (-(|t| / 4)) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 4) 0).congr_fun
      (fun t ht => ?_) measurableSet_Iic
    rw [abs_of_nonpos ht]; ring_nf
  · refine (integrableOn_exp_mul_Ioi (by norm_num : (-(1 / 4) : ℝ) < 0) 0).congr_fun
      (fun t ht => ?_) measurableSet_Ioi
    rw [abs_of_pos ht]; ring_nf

theorem integrable_quadratureDefect : Integrable quadratureDefect :=
  integrable_exp_neg_abs_div_four.mono' continuous_quadratureDefect.aestronglyMeasurable
    (Eventually.of_forall fun t => by rw [Real.norm_eq_abs]; exact abs_quadratureDefect_le t)

/-! ## The Fourier transform of the defect -/

/-- `R(t) ≤ 3 e^{-(11/4) t}` for `t ≥ 0`. -/
theorem thetaLogTail_le_exp {t : ℝ} (ht : 0 ≤ t) : thetaLogTail t ≤ 3 * Real.exp (-(11 / 4 * t)) := by
  have h1 : 1 ≤ Real.exp t := Real.one_le_exp ht
  have hk := evenKernel_zero_sub_one_le h1
  have h2 : Real.exp (-Real.pi * Real.exp t) ≤ Real.exp (-(3 * t)) := by
    refine Real.exp_le_exp.mpr ?_
    have := Real.add_one_le_exp t
    nlinarith [Real.pi_gt_three]
  rw [thetaLogTail]
  calc Real.exp (t / 4) * (Θ (Real.exp t) - 1) ≤ Real.exp (t / 4) * (3 * Real.exp (-(3 * t))) :=
        mul_le_mul_of_nonneg_left (hk.trans (by linarith)) (Real.exp_pos _).le
    _ = 3 * Real.exp (-(11 / 4 * t)) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf

theorem integrableOn_cexp_mul_thetaLogTail {s : ℂ} (hs : -2 < s.re) :
    IntegrableOn (fun t : ℝ => cexp (-(s * t)) * (thetaLogTail t : ℂ)) (Ioi 0) := by
  have hdom : IntegrableOn (fun t : ℝ => 3 * Real.exp ((-(3 / 4)) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num) 0).const_mul 3
  refine hdom.mono' ((by fun_prop : Continuous fun t : ℝ =>
    cexp (-(s * t))).mul (Complex.continuous_ofReal.comp continuous_thetaLogTail)
      |>.aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thetaLogTail_pos t)]
  have hre : (-(s * (t : ℂ))).re = -(s.re * t) := by simp
  rw [hre]
  calc Real.exp (-(s.re * t)) * thetaLogTail t ≤ Real.exp (2 * t) * (3 * Real.exp (-(11 / 4 * t))) :=
        mul_le_mul (Real.exp_le_exp.mpr (by nlinarith)) (thetaLogTail_le_exp ht0.le)
          (thetaLogTail_pos t).le (Real.exp_pos _).le
    _ = 3 * Real.exp ((-(3 / 4)) * t) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf

/-- **Complex Laplace transform of the tail.** `∫₀^∞ e^{-st} R(t) dt = M_{2is}`. -/
theorem integral_cexp_mul_thetaLogTail (s : ℂ) :
    (∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (thetaLogTail t : ℂ)) = wardMellin (2 * I * s) := by
  rw [wardMellin, ← integral_Ioi_exp_smul_comp]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have hw : wardExponent (2 * I * s) = -s - 3 / 4 := by
    rw [wardExponent]; linear_combination s * I_sq
  rw [hw, jacobiThetaSum_ofReal_eq_evenKernel, Complex.ofReal_exp,
    cpow_cexp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]), Complex.real_smul,
    Complex.ofReal_exp, thetaLogTail]
  push_cast
  rw [show (-(s * (t : ℂ))) = (t : ℂ) + (t : ℂ) * (-s - 3 / 4) - (t : ℂ) / 4 by ring,
    Complex.exp_sub, Complex.exp_add]
  have : cexp ((t : ℂ) / 4) ≠ 0 := Complex.exp_ne_zero _
  field_simp

theorem integral_Ioi_cexp_mul_exp_neg_quarter (s : ℂ) (hs : -(1 / 4) < s.re) :
    (∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (Real.exp (-(t / 4)) : ℂ)) = 1 / (s + 1 / 4) := by
  have ha : (-(s + 1 / 4)).re < 0 := by simp; linarith [hs]
  have h := integral_exp_mul_complex_Ioi ha 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
  rw [← show (∫ t in Ioi (0 : ℝ), cexp (-(s + 1 / 4) * t)) =
      ∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (Real.exp (-(t / 4)) : ℂ) from
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by
      rw [Complex.ofReal_exp, ← Complex.exp_add]; push_cast; ring_nf, h]
  have hne : s + 1 / 4 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this; linarith
  field_simp

theorem integrableOn_cexp_mul_exp_neg_quarter {s : ℂ} (hs : -(1 / 4) < s.re) :
    IntegrableOn (fun t : ℝ => cexp (-(s * t)) * (Real.exp (-(t / 4)) : ℂ)) (Ioi 0) := by
  have ha : (-(s + 1 / 4)).re < 0 := by simp; linarith
  refine (integrableOn_exp_mul_complex_Ioi ha 0).congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [Complex.ofReal_exp, ← Complex.exp_add]; push_cast; ring_nf

/-- `∫₀^∞ e^{-st} B(t) dt = 1/(s + 1/4) - M_{2is}` for `Re s > -1/4`. -/
theorem integral_Ioi_cexp_mul_quadratureDefect {s : ℂ} (hs : -(1 / 4) < s.re) :
    (∫ t in Ioi (0 : ℝ), cexp (-(s * t)) * (quadratureDefect t : ℂ)) =
      1 / (s + 1 / 4) - wardMellin (2 * I * s) := by
  have h1 := integrableOn_cexp_mul_exp_neg_quarter hs
  have h2 := integrableOn_cexp_mul_thetaLogTail (s := s) (by linarith)
  rw [← integral_Ioi_cexp_mul_exp_neg_quarter s hs, ← integral_cexp_mul_thetaLogTail,
    ← integral_sub h1 h2]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : (0 : ℝ) < t := ht
  rw [quadratureDefect, abs_of_pos ht0]
  push_cast
  ring

theorem integrableOn_Ioi_cexp_mul_quadratureDefect {s : ℂ} (hs : -(1 / 4) < s.re) :
    IntegrableOn (fun t : ℝ => cexp (-(s * t)) * (quadratureDefect t : ℂ)) (Ioi 0) := by
  have h1 := integrableOn_cexp_mul_exp_neg_quarter hs
  have h2 := integrableOn_cexp_mul_thetaLogTail (s := s) (by linarith)
  refine (h1.sub h2).congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : (0 : ℝ) < t := ht
  simp only [Pi.sub_apply]
  rw [quadratureDefect, abs_of_pos ht0]
  push_cast
  ring

theorem integrable_cexp_mul_quadratureDefect (τ : ℝ) :
    Integrable fun t : ℝ => cexp (-((τ : ℂ) * t * I)) * (quadratureDefect t : ℂ) := by
  refine (integrable_quadratureDefect.ofReal (𝕜 := ℂ)).bdd_mul (c := 1)
    (by fun_prop : Continuous fun t : ℝ => cexp (-((τ : ℂ) * t * I))).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [Complex.norm_exp]
  simp

/-- **Fourier transform of the defect (12).** `B̂(τ) = ∫ B(t) e^{-iτt} dt = Ξ(2τ)/(τ² + 1/16)`. -/
theorem fourier_quadratureDefect (τ : ℝ) :
    (∫ t : ℝ, cexp (-((τ : ℂ) * t * I)) * (quadratureDefect t : ℂ)) =
      XiC (2 * τ) / ((τ : ℂ) ^ 2 + 1 / 16) := by
  have hint := integrable_cexp_mul_quadratureDefect τ
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn]
  have hneg : (∫ t in Iic (0 : ℝ), cexp (-((τ : ℂ) * t * I)) * (quadratureDefect t : ℂ)) =
      ∫ t in Ioi (0 : ℝ), cexp (-((-(τ : ℂ) * I) * t)) * (quadratureDefect t : ℂ) := by
    have h := integral_comp_neg_Iic (0 : ℝ)
      (fun u : ℝ => cexp (-((-(τ : ℂ) * I) * u)) * (quadratureDefect u : ℂ))
    simp only [neg_zero] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    simp only [quadratureDefect_neg, Complex.ofReal_neg]
    ring_nf
  have hpos : (∫ t in Ioi (0 : ℝ), cexp (-((τ : ℂ) * t * I)) * (quadratureDefect t : ℂ)) =
      ∫ t in Ioi (0 : ℝ), cexp (-(((τ : ℂ) * I) * t)) * (quadratureDefect t : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring_nf
  have hre1 : -(1 / 4 : ℝ) < (-(τ : ℂ) * I).re := by simp
  have hre2 : -(1 / 4 : ℝ) < ((τ : ℂ) * I).re := by simp
  rw [hneg, hpos, integral_Ioi_cexp_mul_quadratureDefect hre1,
    integral_Ioi_cexp_mul_quadratureDefect hre2, XiC_eq_wardMellin]
  have hden : (τ : ℂ) ^ 2 + 1 / 16 ≠ 0 := by
    have : (0 : ℝ) < τ ^ 2 + 1 / 16 := by positivity
    have hc : (τ : ℂ) ^ 2 + 1 / 16 = ((τ ^ 2 + 1 / 16 : ℝ) : ℂ) := by push_cast; ring
    rw [hc]
    exact_mod_cast this.ne'
  have h1 : -(τ : ℂ) * I + 1 / 4 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have h2 : (τ : ℂ) * I + 1 / 4 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have hsum : 1 / (-(τ : ℂ) * I + 1 / 4) + 1 / ((τ : ℂ) * I + 1 / 4) =
      (1 / 2) / ((τ : ℂ) ^ 2 + 1 / 16) := by
    rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) hden]
    linear_combination ((1 / 2) * (τ : ℂ) ^ 2) * I_sq
  rw [show 2 * I * (-(τ : ℂ) * I) = 2 * τ by linear_combination (-2 * (τ : ℂ)) * I_sq,
    show 2 * I * ((τ : ℂ) * I) = -(2 * τ) by linear_combination (2 * (τ : ℂ)) * I_sq]
  rw [show 1 / (-(τ : ℂ) * I + 1 / 4) - wardMellin (2 * τ) +
      (1 / ((τ : ℂ) * I + 1 / 4) - wardMellin (-(2 * τ))) =
      (1 / (-(τ : ℂ) * I + 1 / 4) + 1 / ((τ : ℂ) * I + 1 / 4)) -
        (wardMellin (2 * τ) + wardMellin (-(2 * τ))) by ring, hsum, eq_div_iff hden, sub_mul,
    div_mul_cancel₀ _ hden]
  ring

/-! ## Fourier inversion and the signed spectral channel -/

/-- The signed spectral weight `w(τ) = Ξ(2τ)/(τ² + 1/16)`. -/
def commutatorSpectralWeight (τ : ℝ) : ℝ := Xi (2 * τ) / (τ ^ 2 + 1 / 16)

/-- The total theta-source mass `Ξ(0) = ∫ k`. -/
def thetaSourceMass : ℝ := ∫ t, ‖thetaSourceC t‖

theorem abs_Xi_le_thetaSourceMass (x : ℝ) : |Xi x| ≤ thetaSourceMass := by
  have h := sourceTransform_thetaSourceC (x : ℂ)
  rw [XiC_ofReal] at h
  have habs : |Xi x| = ‖((Xi x : ℝ) : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [habs, ← h, sourceTransform, thetaSourceMass]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext t
  rw [norm_mul, show -I * (x : ℂ) * (t : ℂ) = ((-(x * t) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul]

theorem continuous_commutatorSpectralWeight : Continuous commutatorSpectralWeight := by
  unfold commutatorSpectralWeight
  exact (continuous_Xi.comp (continuous_const.mul continuous_id)).div (by fun_prop)
    fun τ => by positivity

theorem abs_commutatorSpectralWeight_le (τ : ℝ) :
    |commutatorSpectralWeight τ| ≤ 16 * thetaSourceMass * (1 + (4 * τ) ^ 2)⁻¹ := by
  rw [commutatorSpectralWeight, abs_div, abs_of_pos (by positivity : (0 : ℝ) < τ ^ 2 + 1 / 16)]
  have h := abs_Xi_le_thetaSourceMass (2 * τ)
  rw [div_le_iff₀ (by positivity)]
  have hpos : 0 < 1 + (4 * τ) ^ 2 := by positivity
  calc |Xi (2 * τ)| ≤ thetaSourceMass := h
    _ = 16 * thetaSourceMass * (1 + (4 * τ) ^ 2)⁻¹ * (τ ^ 2 + 1 / 16) := by
        field_simp; ring

theorem integrable_commutatorSpectralWeight : Integrable commutatorSpectralWeight := by
  have hdom : Integrable fun τ : ℝ => 16 * thetaSourceMass * (1 + (4 * τ) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_mul_left' (by norm_num : (4 : ℝ) ≠ 0)).const_mul _
  exact hdom.mono' continuous_commutatorSpectralWeight.aestronglyMeasurable
    (Eventually.of_forall fun τ => by
      rw [Real.norm_eq_abs]; exact abs_commutatorSpectralWeight_le τ)

theorem fourier_quadratureDefect_eq_weight (τ : ℝ) :
    (∫ t : ℝ, cexp (-((τ : ℂ) * t * I)) * (quadratureDefect t : ℂ)) =
      (commutatorSpectralWeight τ : ℂ) := by
  rw [fourier_quadratureDefect, commutatorSpectralWeight, show (2 : ℂ) * τ = ((2 * τ : ℝ) : ℂ) by
    push_cast; ring, XiC_ofReal]
  push_cast
  ring

/-- **Fourier inversion.** `B(t) = (1/2π) ∫ w(τ) cos(τt) dτ`. -/
theorem quadratureDefect_eq_inverse (t : ℝ) :
    quadratureDefect t = (2 * Real.pi)⁻¹ * ∫ τ, commutatorSpectralWeight τ * Real.cos (τ * t) := by
  set f : ℝ → ℂ := fun t => (quadratureDefect t : ℂ)
  have hc : Continuous f := Complex.continuous_ofReal.comp continuous_quadratureDefect
  have hf : Integrable f := integrable_quadratureDefect.ofReal
  have hin : ∀ v w : ℝ, inner ℝ v w = w * v := fun v w => by simp
  have hF : ∀ w, FourierTransform.fourier f w = (commutatorSpectralWeight (2 * Real.pi * w) : ℂ) := by
    intro w
    rw [Real.fourier_eq', ← fourier_quadratureDefect_eq_weight]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [hin, smul_eq_mul, f]
    push_cast
    ring_nf
  have hFi : Integrable (FourierTransform.fourier f) := by
    have h := (integrable_commutatorSpectralWeight.comp_mul_left'
      (by positivity : (2 * Real.pi) ≠ 0)).ofReal (𝕜 := ℂ)
    exact h.congr (Eventually.of_forall fun w => (hF w).symm)
  have hinv := congrFun (hc.fourierInv_fourier_eq hf hFi) t
  rw [Real.fourierInv_eq'] at hinv
  simp only [hF, hin, smul_eq_mul] at hinv
  have hsub := Measure.integral_comp_mul_left
    (fun y : ℝ => cexp (((y * t : ℝ) : ℂ) * I) * (commutatorSpectralWeight y : ℂ)) (2 * Real.pi)
  have hcomp : (∫ x : ℝ, cexp (((2 * Real.pi * (t * x) : ℝ) : ℂ) * I) *
      (commutatorSpectralWeight (2 * Real.pi * x) : ℂ)) =
      ∫ x : ℝ, cexp ((((2 * Real.pi * x) * t : ℝ) : ℂ) * I) *
        (commutatorSpectralWeight (2 * Real.pi * x) : ℂ) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring_nf
  rw [hcomp, hsub] at hinv
  have hint : Integrable fun y : ℝ => cexp (((y * t : ℝ) : ℂ) * I) *
      (commutatorSpectralWeight y : ℂ) :=
    (integrable_commutatorSpectralWeight.ofReal (𝕜 := ℂ)).bdd_mul (c := 1)
      (by fun_prop : Continuous fun y : ℝ => cexp (((y * t : ℝ) : ℂ) * I)).aestronglyMeasurable
      (Eventually.of_forall fun y => by rw [Complex.norm_exp_ofReal_mul_I])
  have hre := congrArg Complex.re hinv
  simp only [f, Complex.ofReal_re, Complex.real_smul, Complex.re_ofReal_mul] at hre
  have hRe := integral_re hint
  simp only [RCLike.re_to_complex] at hRe
  rw [← hre, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), ← hRe]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  rw [mul_comm, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem integral_even_eq_two_mul_Ioi {g : ℝ → ℝ} (hg : Integrable g) (heven : ∀ x, g (-x) = g x) :
    ∫ x, g x = 2 * ∫ x in Ioi 0, g x := by
  rw [← intervalIntegral.integral_Iic_add_Ioi hg.integrableOn hg.integrableOn]
  have h := integral_comp_neg_Iic (0 : ℝ) g
  simp only [neg_zero, heven] at h
  rw [h]
  ring

theorem commutatorSpectralWeight_neg (τ : ℝ) :
    commutatorSpectralWeight (-τ) = commutatorSpectralWeight τ := by
  rw [commutatorSpectralWeight, commutatorSpectralWeight, mul_neg, Xi_neg, neg_sq]

theorem integrable_commutatorSpectralWeight_mul_cos (t : ℝ) :
    Integrable fun τ => commutatorSpectralWeight τ * Real.cos (τ * t) :=
  integrable_commutatorSpectralWeight.mul_bdd (c := 1)
    (by fun_prop : Continuous fun τ : ℝ => Real.cos (τ * t)).aestronglyMeasurable
    (Eventually.of_forall fun τ => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)

/-- `B(t) = (1/π) ∫₀^∞ w(τ) cos(τt) dτ`. -/
theorem quadratureDefect_eq_integral_cos (t : ℝ) :
    quadratureDefect t = Real.pi⁻¹ * ∫ τ in Ioi 0, commutatorSpectralWeight τ * Real.cos (τ * t) := by
  rw [quadratureDefect_eq_inverse, integral_even_eq_two_mul_Ioi
    (integrable_commutatorSpectralWeight_mul_cos t) fun τ => by
      rw [commutatorSpectralWeight_neg, neg_mul, Real.cos_neg]]
  rw [← mul_assoc, show (2 * Real.pi)⁻¹ * 2 = Real.pi⁻¹ by field_simp]

/-- **Rank-one boundary channel plus signed spectral channel (13).**
`K(a, b) = 4 sinh(a/4) sinh(b/4) + (2/π) ∫₀^∞ w(τ) sin(aτ) sin(bτ) dτ`. -/
theorem deletionInversionKernel_eq_spectral (a b : ℝ) :
    deletionInversionKernel a b = 4 * Real.sinh (a / 4) * Real.sinh (b / 4) +
      2 / Real.pi * ∫ τ in Ioi 0, commutatorSpectralWeight τ * (Real.sin (a * τ) * Real.sin (b * τ)) := by
  rw [deletionInversionKernel_eq_sinh, quadratureDefect_eq_integral_cos,
    quadratureDefect_eq_integral_cos, add_sub_assoc, ← mul_sub,
    ← integral_sub (integrable_commutatorSpectralWeight_mul_cos _).integrableOn
      (integrable_commutatorSpectralWeight_mul_cos _).integrableOn]
  have hid : ∀ τ : ℝ, commutatorSpectralWeight τ * Real.cos (τ * (a - b)) -
      commutatorSpectralWeight τ * Real.cos (τ * (a + b)) =
        2 * (commutatorSpectralWeight τ * (Real.sin (a * τ) * Real.sin (b * τ))) := by
    intro τ
    rw [show τ * (a - b) = a * τ - b * τ by ring, show τ * (a + b) = a * τ + b * τ by ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp only [hid, integral_const_mul]
  have := Real.pi_pos
  field_simp

theorem integrable_commutatorSpectralWeight_mul_bdd {h : ℝ → ℝ} (hh : Continuous h) {M : ℝ}
    (hM : ∀ τ, |h τ| ≤ M) : Integrable fun τ => commutatorSpectralWeight τ * h τ :=
  integrable_commutatorSpectralWeight.mul_bdd (c := M) hh.aestronglyMeasurable
    (Eventually.of_forall fun τ => by rw [Real.norm_eq_abs]; exact hM τ)

/-- **Finite quadratic form (14).** For real coefficients `c_j` and scales `a_j`,
`Σ c_j c_k K(a_j, a_k) = 4 (Σ c_j sinh(a_j/4))² + (2/π) ∫₀^∞ w(τ) (Σ c_j sin(a_j τ))² dτ`. -/
theorem quadraticForm_deletionInversionKernel {ι : Type*} (s : Finset ι) (c a : ι → ℝ) :
    ∑ j ∈ s, ∑ k ∈ s, c j * c k * deletionInversionKernel (a j) (a k) =
      4 * (∑ j ∈ s, c j * Real.sinh (a j / 4)) ^ 2 +
        2 / Real.pi * ∫ τ in Ioi 0, commutatorSpectralWeight τ *
          (∑ j ∈ s, c j * Real.sin (a j * τ)) ^ 2 := by
  have hint : ∀ j k, IntegrableOn (fun τ => commutatorSpectralWeight τ *
      (Real.sin (a j * τ) * Real.sin (a k * τ))) (Ioi 0) := fun j k =>
    (integrable_commutatorSpectralWeight_mul_bdd (M := 1) (by fun_prop) fun τ => by
      rw [abs_mul]
      exact mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_sin_le_one _)).integrableOn
  have hexp : (fun τ => commutatorSpectralWeight τ * (∑ j ∈ s, c j * Real.sin (a j * τ)) ^ 2) =
      fun τ => ∑ j ∈ s, ∑ k ∈ s, c j * c k *
        (commutatorSpectralWeight τ * (Real.sin (a j * τ) * Real.sin (a k * τ))) := by
    funext τ
    rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
    (hint j k).const_mul _]
  simp_rw [integral_finsetSum _ fun k _ => (hint _ k).const_mul _, integral_const_mul]
  have hL : ∀ j k, c j * c k * deletionInversionKernel (a j) (a k) =
      4 * ((c j * Real.sinh (a j / 4)) * (c k * Real.sinh (a k / 4))) +
        2 / Real.pi * (c j * c k * ∫ τ in Ioi 0, commutatorSpectralWeight τ *
          (Real.sin (a j * τ) * Real.sin (a k * τ))) := by
    intro j k; rw [deletionInversionKernel_eq_spectral]; ring
  calc ∑ j ∈ s, ∑ k ∈ s, c j * c k * deletionInversionKernel (a j) (a k) =
      ∑ j ∈ s, ∑ k ∈ s, (4 * ((c j * Real.sinh (a j / 4)) * (c k * Real.sinh (a k / 4))) +
        2 / Real.pi * (c j * c k * ∫ τ in Ioi 0, commutatorSpectralWeight τ *
          (Real.sin (a j * τ) * Real.sin (a k * τ)))) :=
        Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hL j k
    _ = 4 * ∑ j ∈ s, ∑ k ∈ s, (c j * Real.sinh (a j / 4)) * (c k * Real.sinh (a k / 4)) +
        2 / Real.pi * ∑ j ∈ s, ∑ k ∈ s, c j * c k * ∫ τ in Ioi 0, commutatorSpectralWeight τ *
          (Real.sin (a j * τ) * Real.sin (a k * τ)) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [sq, Finset.sum_mul_sum]

/-- **Continuum form (15).** For a continuous compactly supported real `g`,
`∫∫ g(a) g(b) K(a,b) = 4 (∫ g(a) sinh(a/4))² + (2/π) ∫₀^∞ w(τ) (∫ g(a) sin(aτ) da)² dτ`. -/
theorem integral_deletionInversionKernel_quadratic {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    (∫ a, ∫ b, g a * g b * deletionInversionKernel a b) =
      4 * (∫ a, g a * Real.sinh (a / 4)) ^ 2 +
        2 / Real.pi * ∫ τ in Ioi 0, commutatorSpectralWeight τ * (∫ a, g a * Real.sin (a * τ)) ^ 2 := by
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hgs : Integrable fun a => g a * Real.sinh (a / 4) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  set W := commutatorSpectralWeight
  have hWI : IntegrableOn W (Ioi 0) := integrable_commutatorSpectralWeight.integrableOn
  -- the spectral part as a function of `(a, b)`
  set S : ℝ → ℝ → ℝ := fun a b => ∫ τ in Ioi 0, W τ * (Real.sin (a * τ) * Real.sin (b * τ))
  have hK : ∀ a b, g a * g b * deletionInversionKernel a b =
      4 * (g a * Real.sinh (a / 4)) * (g b * Real.sinh (b / 4)) + 2 / Real.pi * (g a * g b * S a b) := by
    intro a b
    rw [deletionInversionKernel_eq_spectral]
    ring
  -- Fubini for the spectral part
  set G : ℝ → ℝ := fun τ => ∫ a, g a * Real.sin (a * τ)
  have hGb : ∀ τ, |G τ| ≤ ∫ a, |g a| := by
    intro τ
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun a => abs_nonneg _) hgi.abs (Eventually.of_forall fun a => ?_))
    show |g a * Real.sin (a * τ)| ≤ |g a|
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have hmeas3 : ∀ a : ℝ, Continuous fun p : ℝ × ℝ => g p.1 * (W p.2 * (Real.sin (a * p.2) *
      Real.sin (p.1 * p.2))) := fun a => by
    have := continuous_commutatorSpectralWeight
    fun_prop
  have hprod : ∀ a : ℝ, Integrable (fun p : ℝ × ℝ => g p.1 * (W p.2 * (Real.sin (a * p.2) *
      Real.sin (p.1 * p.2)))) (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    intro a
    have hbig := hgi.norm.mul_prod hWI.norm
    refine hbig.mono' (hmeas3 a).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := Real.abs_sin_le_one (a * p.2)
    have h2 := Real.abs_sin_le_one (p.1 * p.2)
    have h3 : |Real.sin (a * p.2)| * |Real.sin (p.1 * p.2)| ≤ 1 :=
      mul_le_one₀ h1 (abs_nonneg _) h2
    calc |g p.1| * (|W p.2| * (|Real.sin (a * p.2)| * |Real.sin (p.1 * p.2)|))
        ≤ |g p.1| * (|W p.2| * 1) := by gcongr
      _ = |g p.1| * |W p.2| := by ring
  have hinner : ∀ a, (∫ b, g a * g b * S a b) =
      g a * ∫ τ in Ioi 0, W τ * Real.sin (a * τ) * G τ := by
    intro a
    have hswap := integral_integral_swap
      (f := fun b τ => g b * (W τ * (Real.sin (a * τ) * Real.sin (b * τ)))) (hprod a)
    calc (∫ b, g a * g b * S a b) = g a * ∫ b, ∫ τ in Ioi 0,
          g b * (W τ * (Real.sin (a * τ) * Real.sin (b * τ))) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun b => ?_)
          simp only [S]
          rw [← integral_const_mul, ← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
          ring
      _ = g a * ∫ τ in Ioi 0, ∫ b, g b * (W τ * (Real.sin (a * τ) * Real.sin (b * τ))) := by
          rw [hswap]
      _ = g a * ∫ τ in Ioi 0, W τ * Real.sin (a * τ) * G τ := by
          congr 1
          refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
          simp only [G]
          rw [← integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall fun b => ?_)
          ring
  have hmeas2 : Continuous fun p : ℝ × ℝ => g p.1 * (W p.2 * Real.sin (p.1 * p.2)) := by
    have := continuous_commutatorSpectralWeight
    fun_prop
  have hprod2 : Integrable (fun p : ℝ × ℝ => g p.1 * (W p.2 * Real.sin (p.1 * p.2) * G p.2))
      (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hbig := (hgi.norm.mul_prod hWI.norm).const_mul (∫ a, |g a|)
    have hGm : AEStronglyMeasurable (fun p : ℝ × ℝ => G p.2)
        (volume.prod (volume.restrict (Ioi (0 : ℝ)))) := by
      have hGc : Continuous G := by
        simp only [G]
        refine continuous_iff_continuousAt.2 fun τ => ?_
        refine continuousAt_of_dominated (bound := fun a => |g a|)
          (Eventually.of_forall fun τ' => ((by fun_prop : Continuous fun a =>
            g a * Real.sin (a * τ')).aestronglyMeasurable))
          (Eventually.of_forall fun τ' => Eventually.of_forall fun a => ?_) hgi.abs
          (Eventually.of_forall fun a => (by fun_prop : Continuous fun τ' =>
            g a * Real.sin (a * τ')).continuousAt)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
      exact (hGc.comp continuous_snd).aestronglyMeasurable
    refine hbig.mono' ((hmeas2.aestronglyMeasurable).mul hGm |>.congr
      (Eventually.of_forall fun p => by simp only [Pi.mul_apply]; ring)) (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := Real.abs_sin_le_one (p.1 * p.2)
    have h2 := hGb p.2
    calc |g p.1| * (|W p.2| * |Real.sin (p.1 * p.2)| * |G p.2|)
        ≤ |g p.1| * (|W p.2| * 1 * (∫ a, |g a|)) := by gcongr
      _ = (∫ a, |g a|) * (|g p.1| * |W p.2|) := by ring
  have hswap2 := integral_integral_swap
    (f := fun a τ => g a * (W τ * Real.sin (a * τ) * G τ)) hprod2
  have hsplit : (∫ a, ∫ b, g a * g b * deletionInversionKernel a b) =
      4 * (∫ a, g a * Real.sinh (a / 4)) ^ 2 + 2 / Real.pi * ∫ a, ∫ b, g a * g b * S a b := by
    have hint1 : ∀ a, Integrable fun b => 4 * (g a * Real.sinh (a / 4)) * (g b * Real.sinh (b / 4)) :=
      fun a => hgs.const_mul _
    have hint2 : ∀ a, Integrable fun b => g a * g b * S a b := by
      intro a
      have hSb : ∀ b, |S a b| ≤ ∫ τ in Ioi 0, |W τ| := by
        intro b
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun τ => abs_nonneg _) hWI.abs (Eventually.of_forall fun τ => ?_))
        show |W τ * (Real.sin (a * τ) * Real.sin (b * τ))| ≤ |W τ|
        rw [abs_mul, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_sin_le_one _))
      have hSc : Continuous (S a) := by
        simp only [S]
        refine continuous_iff_continuousAt.2 fun b => ?_
        refine continuousAt_of_dominated (bound := fun τ => |W τ|)
          (Eventually.of_forall fun b' => ((by
            have := continuous_commutatorSpectralWeight
            fun_prop : Continuous fun τ => W τ * (Real.sin (a * τ) * Real.sin (b' * τ)))
            |>.aestronglyMeasurable)) (Eventually.of_forall fun b' => Eventually.of_forall
              fun τ => ?_) hWI.abs (Eventually.of_forall fun τ => (by fun_prop :
                Continuous fun b' => W τ * (Real.sin (a * τ) * Real.sin (b' * τ))).continuousAt)
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _)
          (mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_sin_le_one _))
      refine ((hgi.const_mul (g a)).mul_bdd (c := ∫ τ in Ioi 0, |W τ|) hSc.aestronglyMeasurable
        (Eventually.of_forall fun b => by rw [Real.norm_eq_abs]; exact hSb b)).congr
          (Eventually.of_forall fun b => by ring)
    have hA : Integrable fun a => ∫ b, 4 * (g a * Real.sinh (a / 4)) * (g b * Real.sinh (b / 4)) := by
      simp_rw [integral_const_mul]
      exact (hgs.const_mul 4).mul_const _
    have hB : Integrable fun a => ∫ b, g a * g b * S a b := by
      simp_rw [hinner]
      exact hprod2.integral_prod_left.congr (Eventually.of_forall fun a => by
        simp only
        rw [← integral_const_mul])
    calc (∫ a, ∫ b, g a * g b * deletionInversionKernel a b) =
        ∫ a, ((∫ b, 4 * (g a * Real.sinh (a / 4)) * (g b * Real.sinh (b / 4))) +
          2 / Real.pi * ∫ b, g a * g b * S a b) := by
          refine integral_congr_ae (Eventually.of_forall fun a => ?_)
          simp only [hK]
          rw [integral_add (hint1 a) ((hint2 a).const_mul _), integral_const_mul (2 / Real.pi)]
      _ = 4 * (∫ a, g a * Real.sinh (a / 4)) ^ 2 + 2 / Real.pi * ∫ a, ∫ b, g a * g b * S a b := by
          rw [integral_add hA (hB.const_mul _), integral_const_mul (2 / Real.pi)]
          congr 1
          calc (∫ a, ∫ b, 4 * (g a * Real.sinh (a / 4)) * (g b * Real.sinh (b / 4))) =
              ∫ a, (4 * (g a * Real.sinh (a / 4))) * ∫ b, g b * Real.sinh (b / 4) :=
                integral_congr_ae (Eventually.of_forall fun a => integral_const_mul _ _)
            _ = (∫ a, 4 * (g a * Real.sinh (a / 4))) * ∫ b, g b * Real.sinh (b / 4) :=
                integral_mul_const _ _
            _ = 4 * (∫ a, g a * Real.sinh (a / 4)) ^ 2 := by rw [integral_const_mul]; ring
  rw [hsplit]
  congr 2
  calc (∫ a, ∫ b, g a * g b * S a b) = ∫ a, ∫ τ in Ioi 0, g a * (W τ * Real.sin (a * τ) * G τ) := by
        refine integral_congr_ae (Eventually.of_forall fun a => ?_)
        simp only
        rw [hinner, integral_const_mul]
    _ = ∫ τ in Ioi 0, ∫ a, g a * (W τ * Real.sin (a * τ) * G τ) := hswap2
    _ = ∫ τ in Ioi 0, W τ * G τ ^ 2 := by
        refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
        simp only [G]
        rw [sq, ← integral_mul_const, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun a => ?_)
        ring

end RHTower
