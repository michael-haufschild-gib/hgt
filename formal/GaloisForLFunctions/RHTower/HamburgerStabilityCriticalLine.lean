import GaloisForLFunctions.HTGeometry.HamburgerCriticalLineEvenDefect
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import GaloisForLFunctions.RHTower.ZetaMassSublinearRigidity

/-!
# Hamburger stability: a sublinear defect on the critical line

Hamburger's theorem says that a Dirichlet series with Riemann's functional equation is a multiple
of `ζ`.  Here the functional equation may fail on the critical line by a defect whose `L¹` mass,
weighted by the Gamma factor, grows sublinearly.  The conclusion is unchanged.

Let `f(s) = Σ a_n n^{-s}` and `E(s) = Γ_ℝ(s) f(s) - β Γ_ℝ(s - 1)`, continuous on
`1/2 ≤ Re s ≤ 3/2`, holomorphic inside and `O(1/(1 + t²))`.  Suppose that on the critical line

`E(s) - E(1 - s) = -β (Γ_ℝ(s - 1) - Γ_ℝ(-s)) + Γ_ℝ(s) g(Im s / 2)`,

where `g` is measurable, polynomially bounded, and Abel-sublinear:
`δ ∫ ‖g(t)‖ e^{-δ|t|} dt → 0` as `δ → 0⁺` (this holds when `∫_{-T}^{T} ‖g‖ = o(T)`).

**Theorem** (`coeff_eq_of_critical_line_even_sublinear_defect`).  Then every coefficient equals
`2β`: `f = 2β ζ`.

**Proof.**
* The even theta relation with a defect (`critical_line_even_theta_relation_defect`):
  `θ(x) - x^{-1/2} θ(1/x) = β(x^{-1/2} - 1) + K(x)`,
  `K(x) = (1/2π) ∫ x^{-(1/4+it)} Γ_ℝ(1/2 + 2it) g(t) dt`.
* The Laplace transform of `K` is `J(τ) = (1/2π) ∫ g(t) k(2t, τ) dt`, with the kernel
  `k(v, τ) = π^{-ρ/2} Γ(ρ/2) Γ(1 - ρ/2) · τ (πτ²)^{-(1-ρ/2)}`, `ρ = 1/2 + iv`.
  By the reflection formula `‖k(v, τ)‖ ≤ 3 ‖τ‖^{-1/2} e^{-|v| Re τ/‖τ‖}`
  (`norm_pairKernel_le`), so `J` is holomorphic on `Re τ > 0`.
* On the ray `τ = ε + i m` the damping rate is at least `ε/(m + 1)`, so `ε J(ε + i m) → 0` under
  the Abel condition.  Hamburger's residue comparison needs only these radial limits
  (`tendsto_sub_mul_defect_of_radial`).
-/

open Complex Metric Set Filter Topology MeasureTheory

namespace RHTower

namespace HamburgerStability

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The critical-line point `ρ = 1/2 + iv`. -/
def linePt (v : ℝ) : ℂ := (1 / 2 : ℂ) + (v : ℂ) * I

/-- The Gamma pair `π^{-ρ/2} Γ(ρ/2) Γ(1 - ρ/2)` at `ρ = 1/2 + iv`. -/
def gammaPair (v : ℝ) : ℂ :=
  (Real.pi : ℂ) ^ (-(linePt v) / 2) *
    (Complex.Gamma (linePt v / 2) * Complex.Gamma (1 - linePt v / 2))

/-- The Laplace kernel `k(v, τ) = π^{-ρ/2} Γ(ρ/2) Γ(1-ρ/2) · τ (πτ²)^{-(1-ρ/2)}`. -/
def pairKernel (v : ℝ) (τ : ℂ) : ℂ :=
  gammaPair v * (τ * ((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - linePt v / 2)))

/-- The derivative kernel `π^{-ρ/2} Γ(ρ/2) Γ(1-ρ/2) (ρ - 1) (πτ²)^{-(1-ρ/2)}`. -/
def pairKernelDeriv (v : ℝ) (τ : ℂ) : ℂ :=
  gammaPair v * ((linePt v - 1) * ((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - linePt v / 2)))

theorem linePt_re (v : ℝ) : (linePt v).re = 1 / 2 := by simp [linePt]

/-- `‖π^{-ρ/2} Γ(ρ/2) Γ(1-ρ/2)‖ ≤ π^{3/4} (4/√2) e^{-π|v|/2}`. -/
theorem norm_gammaPair_le (v : ℝ) :
    ‖gammaPair v‖ ≤ Real.pi ^ (-(1 / 4 : ℝ)) * (Real.pi * (4 / Real.sqrt 2)) *
      (Real.exp (Real.pi * |v| / 2))⁻¹ := by
  have hpi := Real.pi_pos
  set ρ := linePt v with hρ
  have hρre : ρ.re = 1 / 2 := linePt_re v
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (ρ / 2)
  have hsinarg : (Real.pi : ℂ) * (ρ / 2) =
      ((Real.pi / 4 : ℝ) : ℂ) + ((Real.pi * v / 2 : ℝ) : ℂ) * I := by
    rw [hρ, linePt]; push_cast; ring
  have hsin := norm_sin_quarter_add_ge (Real.pi * v / 2)
  rw [← hsinarg] at hsin
  have habs : |Real.pi * v / 2| = Real.pi * |v| / 2 := by
    rw [abs_div, abs_mul, abs_of_pos hpi, abs_two]
  rw [habs] at hsin
  have hsinpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ :=
    lt_of_lt_of_le (by positivity) hsin
  have hπρ : ‖(Real.pi : ℂ) ^ (-ρ / 2)‖ = Real.pi ^ (-(1 / 4 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    congr 1
    simp [hρre]; norm_num
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set E := Real.exp (Real.pi * |v| / 2) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hinvsin : Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ ≤
      Real.pi * (4 / Real.sqrt 2) * E⁻¹ := by
    rw [div_le_iff₀ hsinpos]
    calc Real.pi = Real.pi * (4 / Real.sqrt 2) * E⁻¹ * (Real.sqrt 2 / 4 * E) := by
          field_simp
      _ ≤ Real.pi * (4 / Real.sqrt 2) * E⁻¹ * ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ := by
          gcongr
  unfold gammaPair
  rw [← hρ, hrefl, norm_mul, hπρ, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  calc Real.pi ^ (-(1 / 4 : ℝ)) * (Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖)
      ≤ Real.pi ^ (-(1 / 4 : ℝ)) * (Real.pi * (4 / Real.sqrt 2) * E⁻¹) :=
        mul_le_mul_of_nonneg_left hinvsin (by positivity)
    _ = _ := by ring

/-- `‖(πτ²)^{-(1-ρ/2)}‖ ≤ π^{-3/4} ‖τ‖^{-3/2} e^{π|v|/2} e^{-|v| Re τ/‖τ‖}` on `Re τ > 0`. -/
theorem norm_pow_pi_mul_sq_le (v : ℝ) {τ : ℂ} (hτre : 0 < τ.re) :
    ‖((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - linePt v / 2))‖ ≤
      Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) *
        (Real.exp (Real.pi * |v| / 2) * Real.exp (-(|v| * (τ.re / ‖τ‖)))) := by
  have hτ : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hpi := Real.pi_pos
  set ρ := linePt v with hρ
  have hρre : ρ.re = 1 / 2 := linePt_re v
  set w : ℂ := -(1 - ρ / 2) with hw
  have hwre : w.re = -(3 / 4) := by rw [hw]; simp [hρre]; norm_num
  have hwim : w.im = v / 2 := by rw [hw, hρ, linePt]; simp
  have hz0 : (Real.pi : ℂ) * τ ^ 2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hpi.ne') (pow_ne_zero 2 hτ)
  have hτpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  set δ : ℝ := τ.re / ‖τ‖ with hδ
  set D : ℝ := Real.exp (-(|v| * δ)) with hD
  set E := Real.exp (Real.pi * |v| / 2) with hE
  rw [Complex.norm_cpow_of_ne_zero hz0, hwre, hwim]
  have hnorm : ‖(Real.pi : ℂ) * τ ^ 2‖ = Real.pi * ‖τ‖ ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  rw [hnorm, Real.mul_rpow hpi.le (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hτpos.le]
  have harg := abs_arg_pi_mul_sq_le hτre
  have hexp : Real.exp (((Real.pi : ℂ) * τ ^ 2).arg * (v / 2)) ≥ (E * D)⁻¹ := by
    rw [hE, hD, ← Real.exp_add, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have h1 := neg_abs_le (((Real.pi : ℂ) * τ ^ 2).arg * (v / 2))
    rw [abs_mul, abs_div, abs_two] at h1
    have h2 : |((Real.pi : ℂ) * τ ^ 2).arg| * (|v| / 2) ≤ (Real.pi - 2 * δ) * (|v| / 2) :=
      mul_le_mul_of_nonneg_right harg (by positivity)
    nlinarith
  have hA : 0 < Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ ((2 : ℕ) * (-(3 / 4 : ℝ))) := by positivity
  rw [div_le_iff₀ (Real.exp_pos _)]
  have e2 : ((2 : ℕ) : ℝ) * (-(3 / 4 : ℝ)) = -(3 / 2 : ℝ) := by norm_num
  rw [e2] at hA ⊢
  have hED : 0 < E * D := by positivity
  calc Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ))
      = Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * (E * D) * (E * D)⁻¹ := by
        rw [mul_assoc _ (E * D), mul_inv_cancel₀ hED.ne', mul_one]
    _ ≤ Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * (E * D) *
        Real.exp (((Real.pi : ℂ) * τ ^ 2).arg * (v / 2)) := by gcongr

/-- The two Gamma estimates combine to a pure damping factor. -/
theorem norm_gammaPair_mul_pow_le (v : ℝ) {τ : ℂ} (hτre : 0 < τ.re) :
    ‖gammaPair v‖ * ‖((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - linePt v / 2))‖ ≤
      3 * ‖τ‖ ^ (-(3 / 2 : ℝ)) * Real.exp (-(|v| * (τ.re / ‖τ‖))) := by
  have hpi := Real.pi_pos
  have h1 := norm_gammaPair_le v
  have h2 := norm_pow_pi_mul_sq_le v hτre
  set E := Real.exp (Real.pi * |v| / 2) with hE
  set D := Real.exp (-(|v| * (τ.re / ‖τ‖))) with hD
  have hEpos : 0 < E := Real.exp_pos _
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hπ1 : Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(3 / 4 : ℝ)) = Real.pi⁻¹ := by
    rw [← Real.rpow_add hpi]; norm_num; exact Real.rpow_neg_one _
  calc ‖gammaPair v‖ * ‖((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - linePt v / 2))‖
      ≤ (Real.pi ^ (-(1 / 4 : ℝ)) * (Real.pi * (4 / Real.sqrt 2)) * E⁻¹) *
        (Real.pi ^ (-(3 / 4 : ℝ)) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * (E * D)) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (Real.pi ^ (-(1 / 4 : ℝ)) * Real.pi ^ (-(3 / 4 : ℝ))) * Real.pi * (4 / Real.sqrt 2) *
        (E⁻¹ * E) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * D := by ring
    _ = (4 / Real.sqrt 2) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * D := by
        rw [hπ1, inv_mul_cancel₀ hEpos.ne', inv_mul_cancel₀ hpi.ne']; ring
    _ ≤ 3 * ‖τ‖ ^ (-(3 / 2 : ℝ)) * D := by
        gcongr
        rw [div_le_iff₀ hsqrt0]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]

/-- **The Laplace kernel is damped off the imaginary axis.**
`‖k(v, τ)‖ ≤ 3 ‖τ‖^{-1/2} e^{-|v| Re τ/‖τ‖}` on `Re τ > 0`. -/
theorem norm_pairKernel_le (v : ℝ) {τ : ℂ} (hτre : 0 < τ.re) :
    ‖pairKernel v τ‖ ≤ 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-(|v| * (τ.re / ‖τ‖))) := by
  have hτ : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hτpos : 0 < ‖τ‖ := norm_pos_iff.mpr hτ
  have h := norm_gammaPair_mul_pow_le v hτre
  have hτ1 : ‖τ‖ * ‖τ‖ ^ (-(3 / 2 : ℝ)) = ‖τ‖ ^ (-(1 / 2 : ℝ)) := by
    rw [show ‖τ‖ ^ (-(1 / 2 : ℝ)) = ‖τ‖ ^ ((1 : ℝ) + (-(3 / 2 : ℝ))) by norm_num,
      Real.rpow_add hτpos, Real.rpow_one]
  unfold pairKernel
  rw [norm_mul, norm_mul]
  calc ‖gammaPair v‖ * (‖τ‖ * ‖((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - linePt v / 2))‖)
      = ‖τ‖ * (‖gammaPair v‖ * ‖((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - linePt v / 2))‖) := by ring
    _ ≤ ‖τ‖ * (3 * ‖τ‖ ^ (-(3 / 2 : ℝ)) * Real.exp (-(|v| * (τ.re / ‖τ‖)))) :=
        mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = 3 * (‖τ‖ * ‖τ‖ ^ (-(3 / 2 : ℝ))) * Real.exp (-(|v| * (τ.re / ‖τ‖))) := by ring
    _ = _ := by rw [hτ1]

/-- The derivative kernel obeys the same damping, with a linear factor. -/
theorem norm_pairKernelDeriv_le (v : ℝ) {τ : ℂ} (hτre : 0 < τ.re) :
    ‖pairKernelDeriv v τ‖ ≤
      3 * (1 + |v|) * ‖τ‖ ^ (-(3 / 2 : ℝ)) * Real.exp (-(|v| * (τ.re / ‖τ‖))) := by
  have h := norm_gammaPair_mul_pow_le v hτre
  have hρ : ‖linePt v - 1‖ ≤ 1 + |v| := by
    have : linePt v - 1 = ((-(1 / 2) : ℝ) : ℂ) + (v : ℂ) * I := by
      rw [linePt]; push_cast; ring
    rw [this]
    calc ‖((-(1 / 2) : ℝ) : ℂ) + (v : ℂ) * I‖ ≤ ‖((-(1 / 2) : ℝ) : ℂ)‖ + ‖(v : ℂ) * I‖ :=
          norm_add_le _ _
      _ = 1 / 2 + |v| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]; norm_num
      _ ≤ 1 + |v| := by linarith
  unfold pairKernelDeriv
  rw [norm_mul, norm_mul]
  calc ‖gammaPair v‖ * (‖linePt v - 1‖ * ‖((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - linePt v / 2))‖)
      = ‖linePt v - 1‖ * (‖gammaPair v‖ * ‖((Real.pi : ℂ) * τ ^ 2) ^ (-(1 - linePt v / 2))‖) := by
        ring
    _ ≤ (1 + |v|) * (3 * ‖τ‖ ^ (-(3 / 2 : ℝ)) * Real.exp (-(|v| * (τ.re / ‖τ‖)))) :=
        mul_le_mul hρ h (by positivity) (by positivity)
    _ = _ := by ring

/-- **The kernel's `τ`-derivative.** -/
theorem hasDerivAt_pairKernel (v : ℝ) {τ : ℂ} (hτre : 0 < τ.re) :
    HasDerivAt (pairKernel v) (pairKernelDeriv v τ) τ := by
  have hτ : τ ≠ 0 := by intro h; rw [h] at hτre; simp at hτre
  have hpi := Real.pi_pos
  set w : ℂ := -(1 - linePt v / 2) with hw
  have hz0 : (Real.pi : ℂ) * τ ^ 2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast hpi.ne') (pow_ne_zero 2 hτ)
  have hslit := mem_slitPlane_pi_mul_sq hτre
  have hinner : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * z ^ 2) ((Real.pi : ℂ) * (2 * τ)) τ := by
    have := (hasDerivAt_pow 2 τ).const_mul (Real.pi : ℂ)
    simpa using this
  have hcpow : HasDerivAt (fun z : ℂ => ((Real.pi : ℂ) * z ^ 2) ^ w)
      (w * ((Real.pi : ℂ) * τ ^ 2) ^ (w - 1) * ((Real.pi : ℂ) * (2 * τ))) τ :=
    hinner.cpow_const hslit
  have hprod := (hasDerivAt_id τ).mul hcpow
  have hfull := hprod.const_mul (gammaPair v)
  unfold pairKernel pairKernelDeriv
  refine hfull.congr_deriv ?_
  have hsub : ((Real.pi : ℂ) * τ ^ 2) ^ (w - 1) = ((Real.pi : ℂ) * τ ^ 2) ^ w /
      ((Real.pi : ℂ) * τ ^ 2) := by
    rw [Complex.cpow_sub _ _ hz0, Complex.cpow_one]
  rw [hsub]
  simp only [id]
  field_simp
  rw [hw]
  ring_nf

theorem differentiableAt_pairKernel (v : ℝ) {τ : ℂ} (hτre : 0 < τ.re) :
    DifferentiableAt ℂ (pairKernel v) τ :=
  (hasDerivAt_pairKernel v hτre).differentiableAt

theorem continuousAt_Gamma_linePt_half (v : ℝ) : ContinuousAt Complex.Gamma (linePt v / 2) := by
  refine Complex.continuousAt_Gamma _ fun m hm => ?_
  have h := congrArg Complex.re hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  simp [linePt] at h
  linarith

theorem continuousAt_Gamma_one_sub_linePt_half (v : ℝ) :
    ContinuousAt Complex.Gamma (1 - linePt v / 2) := by
  refine Complex.continuousAt_Gamma _ fun m hm => ?_
  have h := congrArg Complex.re hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  simp [linePt] at h
  linarith

theorem continuous_linePt : Continuous linePt := by unfold linePt; fun_prop

theorem continuous_gammaPair : Continuous gammaPair := by
  have hl := continuous_linePt
  unfold gammaPair
  refine Continuous.mul ?_ (Continuous.mul ?_ ?_)
  · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  · exact continuous_iff_continuousAt.mpr fun v =>
      ContinuousAt.comp (g := Complex.Gamma) (f := fun v : ℝ => linePt v / 2)
        (continuousAt_Gamma_linePt_half v) (hl.continuousAt.div_const 2)
  · exact continuous_iff_continuousAt.mpr fun v =>
      ContinuousAt.comp (g := Complex.Gamma) (f := fun v : ℝ => 1 - linePt v / 2)
        (continuousAt_Gamma_one_sub_linePt_half v)
        (continuousAt_const.sub (hl.continuousAt.div_const 2))

theorem continuous_pairKernel {τ : ℂ} (hτ : τ ≠ 0) : Continuous fun v : ℝ => pairKernel v τ := by
  have hz0 : (Real.pi : ℂ) * τ ^ 2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (pow_ne_zero 2 hτ)
  have hl := continuous_linePt
  unfold pairKernel
  exact continuous_gammaPair.mul
    (continuous_const.mul (Continuous.const_cpow (by fun_prop) (Or.inl hz0)))

theorem continuous_pairKernelDeriv {τ : ℂ} (hτ : τ ≠ 0) :
    Continuous fun v : ℝ => pairKernelDeriv v τ := by
  have hz0 : (Real.pi : ℂ) * τ ^ 2 ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) (pow_ne_zero 2 hτ)
  have hl := continuous_linePt
  unfold pairKernelDeriv
  exact continuous_gammaPair.mul
    ((by fun_prop : Continuous fun v : ℝ => linePt v - 1).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl hz0)))

/-! ### The Laplace transform of the defect -/

/-- `(1 + |t|)^n e^{-δ|t|}` is integrable for `δ > 0`. -/
theorem integrable_one_add_abs_pow_mul_exp {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    Integrable (fun t : ℝ => (1 + |t|) ^ n * Real.exp (-(δ * |t|))) := by
  have h0 := _root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 hδ
  have hn := _root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs n hδ
  refine ((h0.add hn).const_mul (2 ^ n)).mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
  have ht := abs_nonneg t
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp : (1 + |t|) ^ n ≤ 2 ^ n * (1 + |t| ^ n) := by
    rcases le_total |t| 1 with h | h
    · calc (1 + |t|) ^ n ≤ 2 ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
        _ ≤ 2 ^ n * (1 + |t| ^ n) := le_mul_of_one_le_right (by positivity)
            (by linarith [pow_nonneg ht n])
    · calc (1 + |t|) ^ n ≤ (2 * |t|) ^ n := pow_le_pow_left₀ (by positivity) (by linarith) n
        _ = 2 ^ n * |t| ^ n := mul_pow _ _ _
        _ ≤ 2 ^ n * (1 + |t| ^ n) := by gcongr; linarith
  have he : Real.exp (-(δ * |t|)) = Real.exp (-δ * |t|) := by ring_nf
  calc (1 + |t|) ^ n * Real.exp (-(δ * |t|)) ≤ 2 ^ n * (1 + |t| ^ n) * Real.exp (-(δ * |t|)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
    _ = 2 ^ n * (|t| ^ 0 * Real.exp (-δ * |t|) + |t| ^ n * Real.exp (-δ * |t|)) := by
        rw [he]; ring

/-- A polynomially bounded function times a polynomially weighted exponential is integrable. -/
theorem integrable_mul_of_poly_damped {g h : ℝ → ℂ} {Cg A δ : ℝ} {N M : ℕ}
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hhm : AEStronglyMeasurable h volume) (hδ : 0 < δ)
    (hhb : ∀ t, ‖h t‖ ≤ A * (1 + |t|) ^ M * Real.exp (-(δ * |t|))) :
    Integrable (fun t => g t * h t) := by
  have hCg : 0 ≤ Cg := by
    have := (norm_nonneg _).trans (hgb 0)
    simpa using this
  refine ((integrable_one_add_abs_pow_mul_exp hδ (N + M)).const_mul (Cg * A)).mono'
    (hgm.mul hhm) (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  have hA : 0 ≤ A * (1 + |t|) ^ M * Real.exp (-(δ * |t|)) := (norm_nonneg _).trans (hhb t)
  calc ‖g t‖ * ‖h t‖ ≤ (Cg * (1 + |t|) ^ N) * (A * (1 + |t|) ^ M * Real.exp (-(δ * |t|))) :=
        mul_le_mul (hgb t) (hhb t) (norm_nonneg _) (mul_nonneg hCg (by positivity))
    _ = Cg * A * ((1 + |t|) ^ (N + M) * Real.exp (-(δ * |t|))) := by ring

/-- The Abel mass `∫ ‖g(t)‖ e^{-δ|t|} dt`. -/
def abelMass (g : ℝ → ℂ) (δ : ℝ) : ℝ := ∫ t : ℝ, ‖g t‖ * Real.exp (-(δ * |t|))

theorem integrable_abelMass {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : AEStronglyMeasurable g volume)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) {δ : ℝ} (hδ : 0 < δ) :
    Integrable fun t : ℝ => ‖g t‖ * Real.exp (-(δ * |t|)) := by
  refine ((integrable_one_add_abs_pow_mul_exp hδ N).const_mul Cg).mono'
    (hgm.norm.mul (by fun_prop : Continuous fun t : ℝ => Real.exp (-(δ * |t|))).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖g t‖ * Real.exp (-(δ * |t|)) ≤ Cg * (1 + |t|) ^ N * Real.exp (-(δ * |t|)) :=
        mul_le_mul_of_nonneg_right (hgb t) (by positivity)
    _ = Cg * ((1 + |t|) ^ N * Real.exp (-(δ * |t|))) := by ring

theorem abelMass_antitone {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : AEStronglyMeasurable g volume)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) {δ₁ δ₂ : ℝ} (hδ₁ : 0 < δ₁) (h12 : δ₁ ≤ δ₂) :
    abelMass g δ₂ ≤ abelMass g δ₁ := by
  refine integral_mono (integrable_abelMass hgm hgb (hδ₁.trans_le h12))
    (integrable_abelMass hgm hgb hδ₁) fun t => ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  nlinarith [abs_nonneg t]

/-- The Laplace transform of the defect, `J(τ) = (1/2π) ∫ g(t) k(2t, τ) dt`. -/
def defectLaplace (g : ℝ → ℂ) (τ : ℂ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, g t * pairKernel (2 * t) τ

theorem norm_pairKernel_two_mul_le (t : ℝ) {τ : ℂ} (hτ : 0 < τ.re) :
    ‖pairKernel (2 * t) τ‖ ≤
      3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-((2 * (τ.re / ‖τ‖)) * |t|)) := by
  have h := norm_pairKernel_le (2 * t) hτ
  have e : |2 * t| * (τ.re / ‖τ‖) = (2 * (τ.re / ‖τ‖)) * |t| := by
    rw [abs_mul, abs_two]; ring
  rwa [e] at h

theorem pos_re_div_norm {τ : ℂ} (hτ : 0 < τ.re) : 0 < τ.re / ‖τ‖ := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  exact div_pos hτ (norm_pos_iff.mpr hτ0)

theorem integrable_defectLaplace_integrand {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    {τ : ℂ} (hτ : 0 < τ.re) :
    Integrable fun t : ℝ => g t * pairKernel (2 * t) τ := by
  have hτ0 : τ ≠ 0 := by intro h; rw [h] at hτ; simp at hτ
  refine integrable_mul_of_poly_damped (M := 0) (A := 3 * ‖τ‖ ^ (-(1 / 2 : ℝ))) hgm hgb
    ((continuous_pairKernel hτ0).comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    (mul_pos two_pos (pos_re_div_norm hτ)) fun t => ?_
  rw [pow_zero, mul_one]
  exact norm_pairKernel_two_mul_le t hτ

/-- `‖J(τ)‖ ≤ (3/2π) ‖τ‖^{-1/2} M(2 Re τ/‖τ‖)`, with `M` the Abel mass. -/
theorem norm_defectLaplace_le {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    {τ : ℂ} (hτ : 0 < τ.re) :
    ‖defectLaplace g τ‖ ≤
      3 / (2 * Real.pi) * ‖τ‖ ^ (-(1 / 2 : ℝ)) * abelMass g (2 * (τ.re / ‖τ‖)) := by
  have hpi := Real.pi_pos
  have hδ : 0 < 2 * (τ.re / ‖τ‖) := mul_pos two_pos (pos_re_div_norm hτ)
  have hint := (integrable_abelMass hgm hgb hδ).const_mul (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)))
  have hle := norm_integral_le_of_norm_le (f := fun t => g t * pairKernel (2 * t) τ) hint
    (Eventually.of_forall fun t => by
    rw [norm_mul]
    calc ‖g t‖ * ‖pairKernel (2 * t) τ‖ ≤ ‖g t‖ *
          (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) * Real.exp (-((2 * (τ.re / ‖τ‖)) * |t|))) :=
          mul_le_mul_of_nonneg_left (norm_pairKernel_two_mul_le t hτ) (norm_nonneg _)
      _ = 3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
          (‖g t‖ * Real.exp (-((2 * (τ.re / ‖τ‖)) * |t|))) := by ring)
  rw [integral_const_mul] at hle
  unfold defectLaplace abelMass
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  calc 1 / (2 * Real.pi) * ‖∫ t : ℝ, g t * pairKernel (2 * t) τ‖
      ≤ 1 / (2 * Real.pi) * (3 * ‖τ‖ ^ (-(1 / 2 : ℝ)) *
        ∫ t : ℝ, ‖g t‖ * Real.exp (-((2 * (τ.re / ‖τ‖)) * |t|))) := by gcongr
    _ = _ := by ring

/-- **`J` is holomorphic on the right half-plane.** -/
theorem differentiableOn_defectLaplace {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) :
    DifferentiableOn ℂ (defectLaplace g) {τ : ℂ | 0 < τ.re} := by
  intro τ₀ hτ₀
  have hτ₀' : 0 < τ₀.re := hτ₀
  have hCg : 0 ≤ Cg := by
    have := (norm_nonneg _).trans (hgb 0)
    simpa using this
  set r : ℝ := τ₀.re / 2 with hr
  have hr0 : 0 < r := half_pos hτ₀'
  set δ₀ : ℝ := r / (‖τ₀‖ + r) with hδ₀def
  have hδ₀ : 0 < δ₀ := div_pos hr0 (add_pos_of_nonneg_of_pos (norm_nonneg _) hr0)
  have hball : ∀ τ ∈ ball τ₀ r, r < τ.re ∧ ‖τ‖ ≤ ‖τ₀‖ + r ∧ r < ‖τ‖ := by
    intro τ hτ
    have hd : ‖τ - τ₀‖ < r := mem_ball_iff_norm.mp hτ
    have h1 : |τ.re - τ₀.re| ≤ ‖τ - τ₀‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have h2 : ‖τ‖ ≤ ‖τ₀‖ + ‖τ - τ₀‖ := by
      have := norm_add_le τ₀ (τ - τ₀)
      simpa using this
    have h3 : τ.re ≤ ‖τ‖ := Complex.re_le_norm τ
    have h4 := abs_lt.mp (h1.trans_lt hd)
    refine ⟨by linarith [h4.1], by linarith, by linarith [h4.1]⟩
  set bound : ℝ → ℝ := fun t => 6 * Cg * r ^ (-(3 / 2 : ℝ)) *
    ((1 + |t|) ^ (N + 1) * Real.exp (-((2 * δ₀) * |t|))) with hbound
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (bound := bound)
    (F := fun τ t => g t * pairKernel (2 * t) τ)
    (F' := fun τ t => g t * pairKernelDeriv (2 * t) τ) (x₀ := τ₀) (ball_mem_nhds τ₀ hr0)
    (Filter.eventually_of_mem (ball_mem_nhds τ₀ hr0) fun τ hτ => by
      have hτ0 : τ ≠ 0 := by
        intro h; have := (hball τ hτ).1; rw [h] at this; simp at this; linarith
      exact hgm.mul ((continuous_pairKernel hτ0).comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable)
    (integrable_defectLaplace_integrand hgm hgb hτ₀')
    (hgm.mul ((continuous_pairKernelDeriv (by
        intro h; rw [h] at hτ₀'; simp at hτ₀')).comp
      (continuous_const.mul continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun t τ hτ => by
      obtain ⟨hre, hnle, hrn⟩ := hball τ hτ
      have hτre : 0 < τ.re := hr0.trans hre
      have e1 : 1 + |2 * t| ≤ 2 * (1 + |t|) := by rw [abs_mul, abs_two]; linarith [abs_nonneg t]
      have e2 : ‖τ‖ ^ (-(3 / 2 : ℝ)) ≤ r ^ (-(3 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hr0 hrn.le (by norm_num)
      have hq : δ₀ ≤ τ.re / ‖τ‖ :=
        div_le_div₀ (hr0.trans hre).le hre.le (hr0.trans hrn) hnle
      have e3 : Real.exp (-(|2 * t| * (τ.re / ‖τ‖))) ≤ Real.exp (-((2 * δ₀) * |t|)) := by
        apply Real.exp_le_exp.mpr
        rw [abs_mul, abs_two]
        nlinarith [abs_nonneg t]
      have hk := norm_pairKernelDeriv_le (2 * t) hτre
      rw [norm_mul]
      calc ‖g t‖ * ‖pairKernelDeriv (2 * t) τ‖
          ≤ (Cg * (1 + |t|) ^ N) * (3 * (1 + |2 * t|) * ‖τ‖ ^ (-(3 / 2 : ℝ)) *
            Real.exp (-(|2 * t| * (τ.re / ‖τ‖)))) :=
            mul_le_mul (hgb t) hk (norm_nonneg _) (mul_nonneg hCg (by positivity))
        _ ≤ (Cg * (1 + |t|) ^ N) * (3 * (2 * (1 + |t|)) * r ^ (-(3 / 2 : ℝ)) *
            Real.exp (-((2 * δ₀) * |t|))) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hCg (by positivity))
            gcongr
        _ = bound t := by rw [hbound]; ring)
    ((integrable_one_add_abs_pow_mul_exp (mul_pos two_pos hδ₀) (N + 1)).const_mul _)
    (Eventually.of_forall fun t τ hτ =>
      (hasDerivAt_pairKernel (2 * t) (hr0.trans (hball τ hτ).1)).const_mul (g t))
  have hd : HasDerivAt (defectLaplace g) (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      ∫ t : ℝ, g t * pairKernelDeriv (2 * t) τ₀) τ₀ := key.2.const_mul _
  exact hd.differentiableAt.differentiableWithinAt

/-- **Radial vanishing.**  If the Abel mass is `o(1/δ)`, then `ε J(ε + i m) → 0` as `ε → 0⁺`, for
every `m ≥ 0`. -/
theorem tendsto_mul_defectLaplace_radial {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hA : Tendsto (fun δ => δ * abelMass g δ) (𝓝[>] 0) (𝓝 0)) (m : ℕ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace g ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
  have hpi := Real.pi_pos
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    refine squeeze_zero_norm'
      (a := fun ε : ℝ => 3 / (2 * Real.pi) * abelMass g (2 * 1) * ε ^ (1 / 2 : ℝ)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : 0 < ε := hε
      simp only [Nat.cast_zero, zero_mul, add_zero]
      have hre : 0 < ((ε : ℂ)).re := by simpa using hε'
      have hb := norm_defectLaplace_le hgm hgb hre
      have hn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
      rw [hn, Complex.ofReal_re, div_self hε'.ne'] at hb
      rw [norm_mul, hn]
      have e : ε * ε ^ (-(1 / 2 : ℝ)) = ε ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_one_add' hε'.le (by norm_num)]; norm_num
      calc ε * ‖defectLaplace g ε‖
          ≤ ε * (3 / (2 * Real.pi) * ε ^ (-(1 / 2 : ℝ)) * abelMass g (2 * 1)) := by gcongr
        _ = 3 / (2 * Real.pi) * abelMass g (2 * 1) * (ε * ε ^ (-(1 / 2 : ℝ))) := by ring
        _ = 3 / (2 * Real.pi) * abelMass g (2 * 1) * ε ^ (1 / 2 : ℝ) := by rw [e]
    · have h := (Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))).tendsto
      rw [Real.zero_rpow (by norm_num)] at h
      simpa using (h.mono_left nhdsWithin_le_nhds).const_mul
        (3 / (2 * Real.pi) * abelMass g (2 * 1))
  · set κ : ℝ := (m : ℝ) + 1 with hκdef
    have hκ : 0 < κ := by positivity
    have hA' : Tendsto (fun ε : ℝ => 2 * ε / κ * abelMass g (2 * ε / κ)) (𝓝[>] 0) (𝓝 0) := by
      have hmap : Tendsto (fun ε : ℝ => 2 * ε / κ) (𝓝[>] 0) (𝓝[>] 0) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have := ((continuous_const.mul continuous_id).div_const κ).tendsto (0 : ℝ)
            (f := fun ε : ℝ => 2 * ε / κ)
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with ε hε
          exact div_pos (mul_pos two_pos hε) hκ
      exact hA.comp hmap
    refine squeeze_zero_norm'
      (a := fun ε : ℝ => 3 / (2 * Real.pi) * (κ / 2) * (2 * ε / κ * abelMass g (2 * ε / κ)))
      ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with
        ε hε hε1
      have hε' : 0 < ε := hε
      set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
      have hre : τ.re = ε := by simp [hτ]
      have him : τ.im = m := by simp [hτ]
      have hτre : 0 < τ.re := by rw [hre]; exact hε'
      have hb := norm_defectLaplace_le hgm hgb hτre
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hn1 : 1 ≤ ‖τ‖ := by
        have := Complex.abs_im_le_norm τ
        rw [him, abs_of_nonneg (by positivity)] at this
        linarith
      have hn2 : ‖τ‖ ≤ κ := by
        have h := norm_add_le (ε : ℂ) ((m : ℂ) * I)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε', norm_mul, Complex.norm_natCast,
          Complex.norm_I, mul_one] at h
        have := hε1.2
        rw [hκdef]
        linarith
      have hpow : ‖τ‖ ^ (-(1 / 2 : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
      have hδ : 2 * ε / κ ≤ 2 * (τ.re / ‖τ‖) := by
        rw [hre, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hε'.le (by linarith) hn2)
          (by norm_num)
      have hmono := abelMass_antitone hgm hgb (div_pos (mul_pos two_pos hε') hκ) hδ
      have hM0 : 0 ≤ abelMass g (2 * (τ.re / ‖τ‖)) :=
        integral_nonneg fun t => by positivity
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
      calc ε * ‖defectLaplace g τ‖
          ≤ ε * (3 / (2 * Real.pi) * ‖τ‖ ^ (-(1 / 2 : ℝ)) * abelMass g (2 * (τ.re / ‖τ‖))) := by
            gcongr
        _ ≤ ε * (3 / (2 * Real.pi) * 1 * abelMass g (2 * ε / κ)) := by gcongr
        _ = 3 / (2 * Real.pi) * (κ / 2) * (2 * ε / κ * abelMass g (2 * ε / κ)) := by
            field_simp
    · simpa using hA'.const_mul (3 / (2 * Real.pi) * (κ / 2))

/-! ### The defect kernel -/

theorem continuous_Gamma_quarter_line :
    Continuous fun t : ℝ => Complex.Gamma (((1 / 4 : ℝ) : ℂ) + t * I) := by
  refine continuous_iff_continuousAt.mpr fun t => ?_
  refine ContinuousAt.comp (g := Complex.Gamma) (f := fun t : ℝ => ((1 / 4 : ℝ) : ℂ) + t * I)
    (Complex.continuousAt_Gamma _ fun m hm => ?_) (by fun_prop)
  have h := congrArg Complex.re hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  simp at h
  linarith

theorem Gammaℝ_quarter_line (t : ℝ) :
    Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) =
      (Real.pi : ℂ) ^ (-(2 * (((1 / 4 : ℝ) : ℂ) + t * I)) / 2) *
        Complex.Gamma (((1 / 4 : ℝ) : ℂ) + t * I) := by
  rw [Complex.Gammaℝ_def, show 2 * (((1 / 4 : ℝ) : ℂ) + t * I) / 2 =
    ((1 / 4 : ℝ) : ℂ) + t * I by ring]

theorem continuous_Gammaℝ_quarter_line :
    Continuous fun t : ℝ => Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) := by
  simp_rw [Gammaℝ_quarter_line]
  exact (Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Real.pi_ne_zero))).mul
    continuous_Gamma_quarter_line

/-- `Γ_ℝ(1/2 + 2it)` decays exponentially. -/
theorem exists_bound_Gammaℝ_quarter_line :
    ∃ C : ℝ, ∃ M : ℕ, 0 ≤ C ∧ ∀ t : ℝ,
      ‖Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I))‖ ≤
        C * (1 + |t|) ^ M * Real.exp (-(1 * |t|)) := by
  obtain ⟨Cs, M, hCs, hs⟩ := exists_sharp_bound_norm_Gamma_strip (1 / 4) (1 / 4)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    continuous_Gamma_quarter_line.continuousOn
  set C₀ : ℝ := max Cs (max B 0 * Real.exp 1) with hC₀
  have hC₀0 : 0 ≤ C₀ := le_trans hCs (le_max_left _ _)
  refine ⟨Real.pi ^ (-(1 / 4 : ℝ)) * C₀, M, by positivity, fun t => ?_⟩
  have hπ : ‖(Real.pi : ℂ) ^ (-(2 * (((1 / 4 : ℝ) : ℂ) + t * I)) / 2)‖ =
      Real.pi ^ (-(1 / 4 : ℝ)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
      show -(2 * (((1 / 4 : ℝ) : ℂ) + t * I)) / 2 = ((-(1 / 4) : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I by
        push_cast; ring]
    simp
  have ht := abs_nonneg t
  have key : ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + t * I)‖ ≤
      C₀ * (1 + |t|) ^ M * Real.exp (-(1 * |t|)) := by
    rcases le_or_gt 1 |t| with h1 | h1
    · have him : (((1 / 4 : ℝ) : ℂ) + t * I).im = t := by simp
      have h := hs (((1 / 4 : ℝ) : ℂ) + t * I) (by simp) (by simp) (by rw [him]; exact h1)
      rw [him] at h
      have hexp : Real.exp (-(Real.pi * |t| / 2)) ≤ Real.exp (-(1 * |t|)) := by
        apply Real.exp_le_exp.mpr
        nlinarith [Real.pi_gt_three]
      calc ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + t * I)‖
          ≤ Cs * |t| ^ M * Real.exp (-(Real.pi * |t| / 2)) := h
        _ ≤ C₀ * (1 + |t|) ^ M * Real.exp (-(1 * |t|)) :=
            mul_le_mul (mul_le_mul (le_max_left _ _)
              (pow_le_pow_left₀ ht (by linarith) M) (by positivity) hC₀0) hexp
              (by positivity) (by positivity)
    · have hmem : t ∈ Icc (-1 : ℝ) 1 := by
        rw [abs_lt] at h1; exact ⟨h1.1.le, h1.2.le⟩
      have hb := (hB t hmem).trans (le_max_left B 0)
      have hexp : Real.exp (-1) ≤ Real.exp (-(1 * |t|)) := by
        apply Real.exp_le_exp.mpr; linarith
      have hB0 : 0 ≤ max B 0 := le_max_right _ _
      calc ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + t * I)‖ ≤ max B 0 := hb
        _ = max B 0 * Real.exp 1 * 1 * Real.exp (-1) := by
            rw [mul_one, mul_assoc, ← Real.exp_add]; simp
        _ ≤ C₀ * (1 + |t|) ^ M * Real.exp (-(1 * |t|)) :=
            mul_le_mul (mul_le_mul (le_max_right _ _) (one_le_pow₀ (by linarith)) zero_le_one
              hC₀0) hexp (by positivity) (by positivity)
  rw [Gammaℝ_quarter_line, norm_mul, hπ]
  calc Real.pi ^ (-(1 / 4 : ℝ)) * ‖Complex.Gamma (((1 / 4 : ℝ) : ℂ) + t * I)‖
      ≤ Real.pi ^ (-(1 / 4 : ℝ)) * (C₀ * (1 + |t|) ^ M * Real.exp (-(1 * |t|))) := by gcongr
    _ = _ := by ring

theorem integrable_Gammaℝ_mul {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : AEStronglyMeasurable g volume)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) :
    Integrable fun t : ℝ => Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * g t := by
  obtain ⟨CΓ, M, -, hΓ⟩ := exists_bound_Gammaℝ_quarter_line
  exact (integrable_mul_of_poly_damped hgm hgb continuous_Gammaℝ_quarter_line.aestronglyMeasurable
    one_pos hΓ).congr (Eventually.of_forall fun t => mul_comm _ _)

/-- The defect kernel `K(x) = (1/2π) ∫ x^{-(1/4+it)} Γ_ℝ(1/2 + 2it) g(t) dt`. -/
def defectKernel (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
    (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * g t)

/-- **The Laplace transform of the defect kernel.**  For real `τ > 0`, `K(x) e^{-πτ²x}` is
integrable on `(0, ∞)` and `τ ∫₀^∞ K(x) e^{-πτ²x} dx = J(τ)`. -/
theorem defectKernel_laplace {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ} (hgm : Measurable g)
    (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) {τ : ℝ} (hτ : 0 < τ) :
    IntegrableOn (fun x : ℝ => defectKernel g x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)) (Ioi 0) ∧
    defectLaplace g τ = τ * ∫ x in Ioi (0 : ℝ), defectKernel g x *
      ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ) := by
  have hpi := Real.pi_pos
  set c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ) with hc
  have hGint := integrable_Gammaℝ_mul hgm.aestronglyMeasurable hgb
  have hGm : Measurable fun t : ℝ => Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * g t :=
    continuous_Gammaℝ_quarter_line.measurable.mul hgm
  set F : ℝ × ℝ → ℂ := fun z => (z.1 : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + z.2 * I)) *
    (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + z.2 * I)) * g z.2) *
      ((Real.exp (-(Real.pi * τ ^ 2) * z.1) : ℝ) : ℂ) with hF
  have hreal : IntegrableOn (fun x : ℝ => x ^ (-(1 / 4 : ℝ)) *
      Real.exp (-(Real.pi * τ ^ 2) * x)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := -(1 / 4 : ℝ)) (p := 1)
      (by norm_num) le_rfl (show 0 < Real.pi * τ ^ 2 by positivity)
    simpa [Real.rpow_one] using h
  have hFint : Integrable F ((volume.restrict (Ioi 0)).prod volume) := by
    have hmaj := Integrable.mul_prod (μ := volume.restrict (Ioi 0)) (ν := volume) hreal hGint.norm
    refine hmaj.mono' ?_ ?_
    · have h1 : Measurable fun z : ℝ × ℝ => (z.1 : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + z.2 * I)) :=
        (Complex.measurable_ofReal.comp measurable_fst).pow
          ((measurable_const.add ((Complex.measurable_ofReal.comp measurable_snd).mul
            measurable_const)).neg)
      have h3 : Measurable fun z : ℝ × ℝ => ((Real.exp (-(Real.pi * τ ^ 2) * z.1) : ℝ) : ℂ) :=
        (by fun_prop : Continuous fun x : ℝ =>
          ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ)).measurable.comp measurable_fst
      exact ((h1.mul (hGm.comp measurable_snd)).mul h3).aestronglyMeasurable
    · have hpos : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ)),
          z.1 ∈ Ioi (0 : ℝ) :=
        (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioi (0 : ℝ)))
          (ν := (volume : Measure ℝ))).ae (p := fun x => x ∈ Ioi (0 : ℝ))
          (ae_restrict_mem measurableSet_Ioi)
      filter_upwards [hpos] with z hz
      have hz0 : (0 : ℝ) < z.1 := hz
      have hre : (-(((1 / 4 : ℝ) : ℂ) + z.2 * I)).re = -(1 / 4) := by simp
      simp only [hF]
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz0, hre, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact le_of_eq (by ring)
  have hKe : ∀ x : ℝ, defectKernel g x * ((Real.exp (-(Real.pi * τ ^ 2) * x) : ℝ) : ℂ) =
      c * ∫ t : ℝ, F (x, t) := by
    intro x
    unfold defectKernel
    rw [mul_assoc, ← integral_mul_const]
  refine ⟨(hFint.integral_prod_left.const_mul c).congr
    (Eventually.of_forall fun x => (hKe x).symm), ?_⟩
  have hswap : ∫ x in Ioi (0 : ℝ), ∫ t : ℝ, F (x, t) = ∫ t : ℝ, ∫ x in Ioi (0 : ℝ), F (x, t) :=
    integral_integral_swap (f := fun x t => F (x, t)) hFint
  have hinner : ∀ t : ℝ, ∫ x in Ioi (0 : ℝ), F (x, t) =
      Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * g t *
        (Complex.Gamma (1 - linePt (2 * t) / 2) *
          ((Real.pi : ℂ) * (τ : ℂ) ^ 2) ^ (-(1 - linePt (2 * t) / 2))) := by
    intro t
    have hρ : ((1 / 4 : ℝ) : ℂ) + t * I = linePt (2 * t) / 2 := by
      unfold linePt; push_cast; ring
    rw [← (laplace_cpow_neg_half (linePt_re (2 * t)) hτ).2.2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF]
    rw [hρ]
    ring
  simp_rw [hKe]
  rw [integral_const_mul, hswap]
  simp_rw [hinner]
  have hfin : (∫ t : ℝ, g t * pairKernel (2 * t) τ) = (τ : ℂ) *
      ∫ t : ℝ, Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) * g t *
        (Complex.Gamma (1 - linePt (2 * t) / 2) *
          ((Real.pi : ℂ) * (τ : ℂ) ^ 2) ^ (-(1 - linePt (2 * t) / 2))) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    have h2 : 2 * (((1 / 4 : ℝ) : ℂ) + t * I) = linePt (2 * t) := by
      unfold linePt; push_cast; ring
    simp only [pairKernel, gammaPair]
    rw [h2, Complex.Gammaℝ_def]
    ring
  unfold defectLaplace
  rw [← hc, hfin]
  ring

/-! ### Hamburger stability -/

/-- **Hamburger stability on the critical line.**  Let `Σ |a_n| n^{-σ} < ∞` for `σ > 1`, and let
`E` be continuous on `1/2 ≤ Re s ≤ 3/2`, holomorphic inside, `O(1/(1 + t²))`, with
`Γ_ℝ(s) Σ a_n n^{-s} = E(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2` and, on `Re s = 1/2`,
`E(s) - E(1 - s) = -β (Γ_ℝ(s - 1) - Γ_ℝ(-s)) + Γ_ℝ(s) g(Im s / 2)`.  If `g` is measurable,
polynomially bounded and Abel-sublinear (`δ ∫ ‖g(t)‖ e^{-δ|t|} dt → 0` as `δ → 0⁺`), then every
coefficient equals `2β`. -/
theorem coeff_eq_of_critical_line_even_sublinear_defect {a : ℕ → ℂ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    {E : ℂ → ℂ} {β : ℂ} {C : ℝ} {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * coeffDirichlet a s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 → E s - E (1 - s) =
      -(β * (Complex.Gammaℝ (s - 1) - Complex.Gammaℝ (-s))) + Complex.Gammaℝ s * g (s.im / 2))
    (hgm : Measurable g) (hgb : ∀ t : ℝ, ‖g t‖ ≤ Cg * (1 + |t|) ^ N)
    (hA : Tendsto (fun δ : ℝ => δ * ∫ t : ℝ, ‖g t‖ * Real.exp (-(δ * |t|))) (𝓝[>] 0) (𝓝 0))
    (n : ℕ) : a (n + 1) = 2 * β := by
  have hgm' := hgm.aestronglyMeasurable (μ := volume)
  have hθc : ContinuousOn (coeffTheta a) (Ioi 0) := continuousOn_coeffTheta a (ha 2 (by norm_num))
  have hθm : MellinConvergent (coeffTheta a) (3 / 4) :=
    mellinConvergent_coeffTheta a ha (by norm_num) (by norm_num)
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      mellin (coeffTheta a) (s / 2) = E s + β * Complex.Gammaℝ (s - 1) := by
    intro s hs
    rw [mellin_coeffTheta a ha (by rw [hs]; norm_num)]
    exact hR s hs
  have him : ∀ t : ℝ, (2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2 = t := fun t => by simp
  have hdint : Integrable fun t : ℝ => Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) *
      g ((2 * (((1 / 4 : ℝ) : ℂ) + t * I)).im / 2) := by
    simp only [him]
    exact integrable_Gammaℝ_mul hgm' hgb
  have htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      1 * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + -β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) +
        defectKernel g x := by
    intro x hx
    have h := critical_line_even_theta_relation_defect
      (d := fun s => Complex.Gammaℝ s * g (s.im / 2)) hθc hθm hEc hEd hdecay hR' hC hdint hx
    simp only [him] at h
    unfold defectKernel
    linear_combination h
  have ha2 : Summable fun n : ℕ => ‖a (n + 1)‖ / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    have := summable_sq_of_forall_rpow ha
    simpa using this
  have hL : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a τ =
      1 * ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ)) +
        -β / (Real.pi * τ) + β + defectLaplace g τ := fun τ hτ =>
    hamburgerSeries_eq_of_coeffTheta_relation_defect a a ha ha htheta
      (fun τ hτ => (defectKernel_laplace hgm hgb hτ).1)
      (differentiableOn_defectLaplace hgm' hgb)
      (fun τ hτ => (defectKernel_laplace hgm hgb hτ).2) hτ
  have hper : ∀ τ : ℂ, 0 < τ.re → hamburgerSeries a (τ + I) - hamburgerSeries a τ =
      -β / Real.pi / (τ + I) - -β / Real.pi / τ +
        (defectLaplace g (τ + I) - defectLaplace g τ) := by
    intro τ hτ
    have hτ' : 0 < (τ + I).re := by simpa using hτ
    rw [hL τ hτ, hL (τ + I) hτ']
    have hexp : ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * (τ + I))) =
        ∑' n : ℕ, a (n + 1) * cexp (-(2 * Real.pi * ((n : ℂ) + 1) * τ)) := by
      refine tsum_congr fun n => ?_
      rw [show -(2 * (Real.pi : ℂ) * ((n : ℂ) + 1) * (τ + I)) =
        -(2 * Real.pi * ((n : ℂ) + 1) * τ) + ((-((n : ℤ) + 1) : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hexp, div_div, div_div]
    ring
  have hK : ∀ n₀ : ℕ, Tendsto (fun τ => (τ - (n₀ : ℂ) * I) *
      (defectLaplace g (τ + I) - defectLaplace g τ))
      (𝓝[{τ : ℂ | 0 < τ.re}] ((n₀ : ℂ) * I)) (𝓝 0) := by
    intro n₀
    refine tendsto_sub_mul_defect_of_radial ha2 (-β / Real.pi)
      (fun τ => defectLaplace g (τ + I) - defectLaplace g τ) hper n₀ ?_
    have h1 := tendsto_mul_defectLaplace_radial hgm' hgb hA (n₀ + 1)
    have h0 := tendsto_mul_defectLaplace_radial hgm' hgb hA n₀
    have := h1.sub h0
    rw [sub_zero] at this
    refine this.congr' (Eventually.of_forall fun ε => ?_)
    push_cast
    ring_nf
  have h := coeff_eq_of_hamburgerSeries_periodic_re_pos_of_defect ha2 (-β / Real.pi)
    (fun τ => defectLaplace g (τ + I) - defectLaplace g τ) hper hK n
  rw [h]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

end

end HamburgerStability

end RHTower
