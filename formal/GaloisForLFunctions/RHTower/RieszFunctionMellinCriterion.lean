import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# The Riesz function and its Mellin transform

Riesz's function is `F(x) = Σ_{k ≥ 1} (-1)^{k+1} x^k / ((k-1)! ζ(2k))`.  Expanding `1/ζ(2k)` as a
Möbius series and summing over `k` first gives `F(x) = x R(x)` with
`R(x) = Σ_n μ(n) n^{-2} e^{-x/n²}`, which is bounded on `[0, ∞)`.

For `0 < Re s < ½` the Mellin transform is `∫_0^∞ R(t) t^{s-1} dt = Γ(s) Σ_n μ(n) n^{2s-2}
= Γ(s)/ζ(2 - 2s)`, obtained termwise from `∫_0^∞ t^{s-1} e^{-t/n²} dt = n^{2s} Γ(s)`.  If
`R(x) = O(x^{-β})` at infinity, the transform is holomorphic on `0 < Re s < β`, and the identity
`mellin R (s) · (w - 1)ζ(w) = Γ(s)(1 - 2s)`, `w = 2 - 2s`, extends there by the identity theorem.
A zeta zero `ρ` with `Re ρ > 2 - 2β` would make the left side vanish at `s = 1 - ρ/2` while the
right side does not.  So `F(x) = O(x^b)` forces every zeta zero to have `Re ρ ≤ 2b`; in particular
`F` is never `O(x^b)` with `b < ¼`.
-/

open Complex Filter MeasureTheory Set Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- The weight `h_x(u) = u e^{-x u}`; the Riesz term at `n` is `μ(n) h_x(1/n²)`. -/
def rieszExpWeight (x u : ℝ) : ℝ := u * Real.exp (-(x * u))

/-- The `n`-th term `μ(n) n^{-2} e^{-x/n²}` of the Riesz series. -/
def rieszTerm (x : ℝ) (n : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) * rieszExpWeight x ((n : ℝ) ^ 2)⁻¹

/-- The Riesz series `R(x) = Σ_n μ(n) n^{-2} e^{-x/n²}`. -/
def rieszSeries (x : ℝ) : ℝ := ∑' n : ℕ, rieszTerm x n

theorem abs_rieszTerm_le {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    |rieszTerm x n| ≤ ((n : ℝ) ^ 2)⁻¹ := by
  unfold rieszTerm rieszExpWeight
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hu : 0 ≤ ((n : ℝ) ^ 2)⁻¹ := by positivity
  have he : Real.exp (-(x * ((n : ℝ) ^ 2)⁻¹)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hx hu])
  rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_pos (Real.exp_pos _)]
  calc |(ArithmeticFunction.moebius n : ℝ)| * (((n : ℝ) ^ 2)⁻¹ * Real.exp _)
      ≤ 1 * (((n : ℝ) ^ 2)⁻¹ * 1) := by gcongr
    _ = ((n : ℝ) ^ 2)⁻¹ := by ring

theorem summable_natCast_sq_inv : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by
  exact Real.summable_nat_pow_inv.mpr (by norm_num)

theorem summable_rieszTerm {x : ℝ} (hx : 0 ≤ x) : Summable (rieszTerm x) :=
  Summable.of_norm_bounded summable_natCast_sq_inv fun n => by
    rw [Real.norm_eq_abs]; exact abs_rieszTerm_le hx n

theorem abs_rieszSeries_le {x : ℝ} (hx : 0 ≤ x) :
    |rieszSeries x| ≤ ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
  unfold rieszSeries
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm (summable_rieszTerm hx).norm).trans ?_
  exact (summable_rieszTerm hx).norm.tsum_le_tsum (fun n => by
    rw [Real.norm_eq_abs]; exact abs_rieszTerm_le hx n) summable_natCast_sq_inv

theorem continuousOn_rieszSeries : ContinuousOn rieszSeries (Ici 0) := by
  refine continuousOn_tsum (u := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) (fun n => ?_)
    summable_natCast_sq_inv (fun n x hx => ?_)
  · unfold rieszTerm rieszExpWeight
    fun_prop
  · rw [Real.norm_eq_abs]; exact abs_rieszTerm_le hx n

/-- `∫_0^∞ t^{s-1} e^{-rt} dt = r^{-s} Γ(s)` makes the integrand integrable. -/
theorem integrableOn_cpow_mul_exp_neg_mul {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * cexp (-((r : ℂ) * t))) (Ioi 0) := by
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_cpow_mul_exp_neg_mul_Ioi hs hr]
  refine mul_ne_zero (fun h => ?_) (Complex.Gamma_ne_zero_of_re_pos hs)
  have := ((cpow_eq_zero_iff _ _).mp h).1
  simp [hr.ne'] at this

/-- The complexified Riesz term as a constant multiple of `e^{-rt}`, `r = n^{-2}`. -/
theorem ofReal_rieszTerm (t : ℝ) (n : ℕ) :
    ((rieszTerm t n : ℝ) : ℂ) = ((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      (((n : ℝ) ^ 2)⁻¹ : ℝ) * cexp (-(((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * t)) := by
  unfold rieszTerm rieszExpWeight
  push_cast
  rw [mul_comm (t : ℂ)]
  ring

theorem integral_cpow_mul_rieszTerm {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * ((rieszTerm t n : ℝ) : ℂ) =
      Complex.Gamma s * LSeries.term (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        (2 - 2 * s) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [rieszTerm]
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hr : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := by positivity
  simp_rw [ofReal_rieszTerm]
  have hrw : ∀ t : ℝ, (t : ℂ) ^ (s - 1) * (((ArithmeticFunction.moebius n : ℤ) : ℂ) *
      (((n : ℝ) ^ 2)⁻¹ : ℝ) * cexp (-(((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * t))) =
      (((ArithmeticFunction.moebius n : ℤ) : ℂ) * (((n : ℝ) ^ 2)⁻¹ : ℝ)) *
        ((t : ℂ) ^ (s - 1) * cexp (-(((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * t))) := fun t => by ring
  simp_rw [hrw]
  rw [integral_const_mul, integral_cpow_mul_exp_neg_mul_Ioi hs hr,
    LSeries.term_of_ne_zero hn]
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have h1 : (1 / ((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) = (n : ℂ) ^ 2 := by push_cast; simp
  have h2 : ((n : ℂ) ^ 2) ^ s = (n : ℂ) ^ (2 * s) := by
    rw [← Complex.natCast_cpow_natCast_mul]; norm_num
  have h3 : (n : ℂ) ^ (2 - 2 * s) = (n : ℂ) ^ 2 / (n : ℂ) ^ (2 * s) := by
    rw [Complex.cpow_sub _ _ hnc]; norm_cast
  rw [h1, h2, h3]
  have h4 : (n : ℂ) ^ (2 * s) ≠ 0 := by
    intro h; exact hnc ((cpow_eq_zero_iff _ _).mp h).1
  push_cast
  field_simp

theorem integral_norm_cpow_mul_rieszTerm_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * ((rieszTerm t n : ℝ) : ℂ)‖ ≤
      Real.Gamma s.re * (n : ℝ) ^ (2 * s.re - 2) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have h0 : ∀ t : ℝ, rieszTerm t 0 = 0 := fun t => by simp [rieszTerm]
    simp only [h0, Complex.ofReal_zero, mul_zero, norm_zero, integral_zero]
    exact mul_nonneg (Real.Gamma_pos_of_pos hs).le (Real.rpow_nonneg (Nat.cast_nonneg 0) _)
  have hn' : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set r : ℝ := ((n : ℝ) ^ 2)⁻¹ with hr_def
  have hr : 0 < r := by positivity
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * ((rieszTerm t n : ℝ) : ℂ)‖ =
      |(ArithmeticFunction.moebius n : ℝ)| * r * (t ^ (s.re - 1) * Real.exp (-(r * t))) := by
    intro t ht
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real, Real.norm_eq_abs]
    unfold rieszTerm rieszExpWeight
    rw [abs_mul, abs_mul, abs_of_pos hr, abs_of_pos (Real.exp_pos _), Complex.sub_re,
      Complex.one_re, mul_comm t r]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi hs hr]
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hpow : r * (1 / r) ^ s.re = (n : ℝ) ^ (2 * s.re - 2) := by
    rw [hr_def, one_div, inv_inv, Real.rpow_sub hn', Real.rpow_mul hn'.le]
    norm_cast
    ring
  have hG := (Real.Gamma_pos_of_pos hs).le
  calc |(ArithmeticFunction.moebius n : ℝ)| * r * ((1 / r) ^ s.re * Real.Gamma s.re)
      ≤ 1 * r * ((1 / r) ^ s.re * Real.Gamma s.re) := by gcongr
    _ = Real.Gamma s.re * (n : ℝ) ^ (2 * s.re - 2) := by rw [← hpow]; ring

theorem integrable_cpow_mul_rieszTerm {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((rieszTerm t n : ℝ) : ℂ)) (Ioi 0) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [rieszTerm]
  have hr : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹ := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  have h := (integrableOn_cpow_mul_exp_neg_mul hs hr).const_mul
    (((ArithmeticFunction.moebius n : ℤ) : ℂ) * (((n : ℝ) ^ 2)⁻¹ : ℝ))
  have hfun : (fun t : ℝ => (t : ℂ) ^ (s - 1) * ((rieszTerm t n : ℝ) : ℂ)) =
      fun t : ℝ => ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (((n : ℝ) ^ 2)⁻¹ : ℝ) *
        ((t : ℂ) ^ (s - 1) * cexp (-(((((n : ℝ) ^ 2)⁻¹ : ℝ) : ℂ) * t))) := by
    funext t
    rw [ofReal_rieszTerm]
    ring
  rw [hfun]
  exact h

/-- **The Mellin transform of the Riesz series.**  For `0 < Re s < ½`,
`∫_0^∞ R(t) t^{s-1} dt = Γ(s) Σ_n μ(n) n^{2s-2}`. -/
theorem mellin_rieszSeries {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    mellin (fun t => ((rieszSeries t : ℝ) : ℂ)) s =
      Complex.Gamma s * LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
        (2 - 2 * s) := by
  unfold mellin
  have hpt : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • ((rieszSeries t : ℝ) : ℂ) =
      ∑' n : ℕ, (t : ℂ) ^ (s - 1) * ((rieszTerm t n : ℝ) : ℂ) := by
    intro t _
    rw [smul_eq_mul, rieszSeries, Complex.ofReal_tsum, tsum_mul_left]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hsum : Summable fun n : ℕ =>
      ∫ t in Ioi (0 : ℝ), ‖(t : ℂ) ^ (s - 1) * ((rieszTerm t n : ℝ) : ℂ)‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _)
      (integral_norm_cpow_mul_rieszTerm_le hs0) ?_
    exact (Real.summable_nat_rpow.mpr (by linarith)).mul_left _
  rw [← integral_tsum_of_summable_integral_norm (integrable_cpow_mul_rieszTerm hs0) hsum]
  simp_rw [integral_cpow_mul_rieszTerm hs0]
  rw [tsum_mul_left]
  rfl

/-- `Σ μ(n) n^{-w} · ζ(w) = 1` for `Re w > 1`. -/
theorem LSeries_moebius_mul_riemannZeta {w : ℂ} (hw : 1 < w.re) :
    LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) w * riemannZeta w = 1 := by
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hw, mul_comm]
  exact ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hw

/-- On the strip `0 < Re s < ½`, `mellin R (s) · (w - 1)ζ(w) = Γ(s)(1 - 2s)` with `w = 2 - 2s`. -/
theorem mellin_rieszSeries_mul_zetaResidueUnit {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1 / 2) :
    mellin (fun t => ((rieszSeries t : ℝ) : ℂ)) s * zetaResidueUnit (2 - 2 * s) =
      Complex.Gamma s * (1 - 2 * s) := by
  have hw : 1 < (2 - 2 * s).re := by simp; linarith
  have hw1 : (2 - 2 * s) ≠ 1 := by
    intro h; rw [h, Complex.one_re] at hw; exact lt_irrefl _ hw
  rw [mellin_rieszSeries hs0 hs1, zetaResidueUnit, Function.update_of_ne hw1]
  have hL := LSeries_moebius_mul_riemannZeta hw
  calc Complex.Gamma s * LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 - 2 * s) *
        ((2 - 2 * s - 1) * riemannZeta (2 - 2 * s))
      = Complex.Gamma s * (1 - 2 * s) *
          (LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 - 2 * s) *
            riemannZeta (2 - 2 * s)) := by ring
    _ = Complex.Gamma s * (1 - 2 * s) := by rw [hL, mul_one]

/-- The open strip `0 < Re s < β`. -/
def rieszStrip (β : ℝ) : Set ℂ := {s : ℂ | 0 < s.re ∧ s.re < β}

theorem isOpen_rieszStrip (β : ℝ) : IsOpen (rieszStrip β) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

theorem isPreconnected_rieszStrip (β : ℝ) : IsPreconnected (rieszStrip β) :=
  (convex_halfSpace_re_gt 0 |>.inter (convex_halfSpace_re_lt β)).isPreconnected

/-- **Decay of the Riesz series continues its Mellin transform.**  If `R(x) = O(x^{-β})` at
infinity, the Mellin transform of `R` is holomorphic on `0 < Re s < β`. -/
theorem differentiableOn_mellin_rieszSeries {β C X : ℝ}
    (hbound : ∀ x : ℝ, X ≤ x → |rieszSeries x| ≤ C * x ^ (-β)) :
    DifferentiableOn ℂ (mellin fun t => ((rieszSeries t : ℝ) : ℂ)) (rieszStrip β) := by
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  refine mellin_differentiableAt_of_isBigO_rpow (a := β) (b := 0) ?_ ?_ hs.2 ?_ hs.1
  · refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    exact (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_rieszSeries.mono Ioi_subset_Ici_self))
  · refine Asymptotics.IsBigO.of_bound C ?_
    filter_upwards [eventually_ge_atTop (max X 1)] with x hx
    have hx0 : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx)
    rw [Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    exact hbound x ((le_max_left _ _).trans hx)
  · refine Asymptotics.IsBigO.of_bound (∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [Complex.norm_real, Real.norm_eq_abs, neg_zero, Real.rpow_zero, norm_one, mul_one]
    exact abs_rieszSeries_le hx0.le

/-- **Riesz decay pushes zeta zeros left.**  If `|R(x)| ≤ C x^{-β}` for large `x`, then `ζ` has no
zero with `Re ρ > 2 - 2β`.  The Mellin transform of `R` continues holomorphically to
`0 < Re s < β`, where `mellin R (s) · (w - 1)ζ(w) = Γ(s)(1 - 2s)`, `w = 2 - 2s`, persists by the
identity theorem; at `s = 1 - ρ/2` the left side vanishes and the right side does not. -/
theorem riemannZeta_ne_zero_of_rieszSeries_le {β C X : ℝ}
    (hbound : ∀ x : ℝ, X ≤ x → |rieszSeries x| ≤ C * x ^ (-β)) {ρ : ℂ}
    (hρ : 2 - 2 * β < ρ.re) : riemannZeta ρ ≠ 0 := by
  intro hzero
  have hρ1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hzero
  set U := rieszStrip β
  set f : ℂ → ℂ := fun s =>
    mellin (fun t => ((rieszSeries t : ℝ) : ℂ)) s * zetaResidueUnit (2 - 2 * s)
  set g : ℂ → ℂ := fun s => Complex.Gamma s * (1 - 2 * s)
  have hf : AnalyticOnNhd ℂ f U := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_rieszStrip β)
    refine (differentiableOn_mellin_rieszSeries hbound).mul ?_
    intro s _
    exact ((analyticAt_zetaResidueUnit _).differentiableAt.comp s
      ((differentiableAt_const _).sub ((differentiableAt_const _).mul
        differentiableAt_id))).differentiableWithinAt
  have hg : AnalyticOnNhd ℂ g U := by
    refine DifferentiableOn.analyticOnNhd ?_ (isOpen_rieszStrip β)
    intro s hs
    refine DifferentiableAt.differentiableWithinAt ?_
    refine (Complex.differentiableAt_Gamma s fun m hm => ?_).mul
      ((differentiableAt_const _).sub ((differentiableAt_const _).mul differentiableAt_id))
    have : s.re = -(m : ℝ) := by rw [hm]; simp
    have := hs.1
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hs₀ : ((1 / 4 : ℝ) : ℂ) ∈ U := ⟨by norm_num, by simp; linarith⟩
  have hfg : f =ᶠ[𝓝 ((1 / 4 : ℝ) : ℂ)] g := by
    have hopen : IsOpen (rieszStrip (1 / 2)) := isOpen_rieszStrip _
    have hmem : ((1 / 4 : ℝ) : ℂ) ∈ rieszStrip (1 / 2) := ⟨by norm_num, by norm_num⟩
    filter_upwards [hopen.mem_nhds hmem] with s hs
    exact mellin_rieszSeries_mul_zetaResidueUnit hs.1 hs.2
  have heq := hf.eqOn_of_preconnected_of_eventuallyEq hg (isPreconnected_rieszStrip β) hs₀ hfg
  set s : ℂ := 1 - ρ / 2 with hs_def
  have hsre : s.re = 1 - ρ.re / 2 := by simp [hs_def]
  have hsU : s ∈ U := ⟨by rw [hsre]; linarith, by rw [hsre]; linarith⟩
  have h2s : 2 - 2 * s = ρ := by rw [hs_def]; ring
  have hfs : f s = 0 := by
    simp only [f, h2s]
    have hne : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hρ1; exact lt_irrefl _ hρ1
    rw [zetaResidueUnit, Function.update_of_ne hne, hzero, mul_zero, mul_zero]
  have hgs : g s ≠ 0 := by
    refine mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos hsU.1) ?_
    intro h
    have : ρ = 1 := by
      have h' : 1 - 2 * s = 0 := h
      rw [hs_def] at h'
      linear_combination h'
    rw [this, Complex.one_re] at hρ1
    exact lt_irrefl _ hρ1
  exact hgs (heq hsU ▸ hfs)

/-- The Riesz function `F(x) = x R(x) = Σ_n μ(n) (x/n²) e^{-x/n²}`. -/
def rieszFunction (x : ℝ) : ℝ := x * rieszSeries x

/-- **Lower half of the Riesz exponent law.**  If `|F(x)| ≤ C x^b` for all large `x`, then every
zeta zero has `Re ρ ≤ 2b`. -/
theorem zetaZeroAbscissa_le_of_rieszFunction_le {b C X : ℝ}
    (h : ∀ x : ℝ, X ≤ x → |rieszFunction x| ≤ C * x ^ b) :
    zetaZeroAbscissa ≤ 2 * b := by
  by_contra hcon
  obtain ⟨ρ, hzero, hρ⟩ := exists_zetaZero_lt_re (not_le.mp hcon)
  refine riemannZeta_ne_zero_of_rieszSeries_le (β := 1 - b) (C := C) (X := max X 1)
    (fun x hx => ?_) (by linarith) hzero
  have hx0 : 0 < x := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hx)
  have hF := h x ((le_max_left _ _).trans hx)
  rw [rieszFunction, abs_mul, abs_of_pos hx0] at hF
  rw [show -(1 - b) = b - 1 by ring, Real.rpow_sub_one hx0.ne', mul_div_assoc']
  rw [le_div_iff₀ hx0]
  linarith

/-- The Riesz function is not `O(x^b)` for any `b < ¼`: there are zeta zeros with `Re ρ ≥ ½`. -/
theorem not_rieszFunction_le_of_lt_quarter {b : ℝ} (hb : b < 1 / 4) (C X : ℝ) :
    ¬ ∀ x : ℝ, X ≤ x → |rieszFunction x| ≤ C * x ^ b := fun h => by
  have := zetaZeroAbscissa_le_of_rieszFunction_le h
  have := half_le_zetaZeroAbscissa
  linarith

/-- The exponential series `e^y = Σ y^k / k!` in `ℝ`. -/
theorem tsum_pow_div_factorial_eq_exp (y : ℝ) :
    ∑' k : ℕ, y ^ k / (k.factorial : ℝ) = Real.exp y := by
  rw [Real.exp_eq_exp_ℝ]
  exact (NormedSpace.expSeries_div_hasSum_exp y).tsum_eq

/-- The double series behind Riesz's power series: `μ(n) n^{-2} (-x/n²)^k / k!`. -/
def rieszDoubleTerm (x : ℝ) (n k : ℕ) : ℝ :=
  (ArithmeticFunction.moebius n : ℝ) * ((n : ℝ) ^ 2)⁻¹ * (-(x * ((n : ℝ) ^ 2)⁻¹)) ^ k /
    (k.factorial : ℝ)

theorem summable_uncurry_rieszDoubleTerm {x : ℝ} (hx : 0 ≤ x) :
    Summable (Function.uncurry (rieszDoubleTerm x)) := by
  set b : ℕ × ℕ → ℝ := fun p => ((p.1 : ℝ) ^ 2)⁻¹ *
    ((x * ((p.1 : ℝ) ^ 2)⁻¹) ^ p.2 / (p.2.factorial : ℝ))
  have hb0 : 0 ≤ b := fun p => by positivity
  have hb : Summable b := by
    refine (summable_prod_of_nonneg hb0).mpr ⟨fun n => ?_, ?_⟩
    · exact (Real.summable_pow_div_factorial (x * ((n : ℝ) ^ 2)⁻¹)).mul_left ((n : ℝ) ^ 2)⁻¹
    · have hrow : ∀ n : ℕ, ∑' k : ℕ, b (n, k) =
          ((n : ℝ) ^ 2)⁻¹ * Real.exp (x * ((n : ℝ) ^ 2)⁻¹) := fun n => by
        simp only [b]
        rw [tsum_mul_left, tsum_pow_div_factorial_eq_exp]
      simp_rw [hrow]
      refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
        (summable_natCast_sq_inv.mul_right (Real.exp x))
      have hu : ((n : ℝ) ^ 2)⁻¹ ≤ 1 := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · exact inv_le_one_of_one_le₀ (by
            have : (1 : ℝ) ≤ n := by exact_mod_cast hn
            nlinarith)
      gcongr
      calc x * ((n : ℝ) ^ 2)⁻¹ ≤ x * 1 := by gcongr
        _ = x := mul_one x
  refine Summable.of_norm_bounded hb fun p => ?_
  obtain ⟨n, k⟩ := p
  simp only [Function.uncurry_apply_pair, rieszDoubleTerm, b, Real.norm_eq_abs]
  have hμ : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤
    ((n : ℝ) ^ 2)⁻¹), abs_of_nonneg (by positivity : (0 : ℝ) ≤ x * ((n : ℝ) ^ 2)⁻¹),
    abs_of_pos (by positivity : (0 : ℝ) < (k.factorial : ℝ))]
  calc |(ArithmeticFunction.moebius n : ℝ)| * ((n : ℝ) ^ 2)⁻¹ * (x * ((n : ℝ) ^ 2)⁻¹) ^ k /
        (k.factorial : ℝ)
      ≤ 1 * ((n : ℝ) ^ 2)⁻¹ * (x * ((n : ℝ) ^ 2)⁻¹) ^ k / (k.factorial : ℝ) := by gcongr
    _ = ((n : ℝ) ^ 2)⁻¹ * ((x * ((n : ℝ) ^ 2)⁻¹) ^ k / (k.factorial : ℝ)) := by ring

theorem tsum_rieszDoubleTerm_eq_rieszTerm (x : ℝ) (n : ℕ) :
    ∑' k : ℕ, rieszDoubleTerm x n k = rieszTerm x n := by
  unfold rieszDoubleTerm rieszTerm rieszExpWeight
  simp_rw [mul_div_assoc]
  rw [tsum_mul_left, tsum_pow_div_factorial_eq_exp]
  ring

theorem tsum_rieszDoubleTerm_eq_LSeries (x : ℝ) (k : ℕ) :
    ((∑' n : ℕ, rieszDoubleTerm x n k : ℝ) : ℂ) = (-x : ℂ) ^ k / (k.factorial : ℂ) *
      LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 * k + 2) := by
  rw [Complex.ofReal_tsum, LSeries, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [rieszDoubleTerm]
  rw [LSeries.term_of_ne_zero hn, show (2 * (k : ℂ) + 2) = ((2 * k + 2 : ℕ) : ℂ) by push_cast; ring,
    Complex.cpow_natCast]
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  unfold rieszDoubleTerm
  push_cast
  have e : (n : ℂ) ^ (2 * k + 2) = (n : ℂ) ^ 2 * ((n : ℂ) ^ 2) ^ k := by ring
  rw [e, neg_pow, mul_pow, inv_pow]
  field_simp
  rw [neg_pow]
  ring

/-- **Riesz's power series.**  `F(x) = Σ_{k ≥ 0} (-1)^k x^{k+1} / (k! ζ(2k+2))` for `x ≥ 0`, which
is Riesz's `Σ_{k ≥ 1} (-1)^{k+1} x^k / ((k-1)! ζ(2k))`. -/
theorem rieszFunction_eq_tsum {x : ℝ} (hx : 0 ≤ x) :
    ((rieszFunction x : ℝ) : ℂ) = ∑' k : ℕ,
      (-1) ^ k * (x : ℂ) ^ (k + 1) / ((k.factorial : ℂ) * riemannZeta (2 * k + 2)) := by
  have hswap := (summable_uncurry_rieszDoubleTerm hx).tsum_comm
  have hR : rieszSeries x = ∑' k : ℕ, ∑' n : ℕ, rieszDoubleTerm x n k := by
    rw [hswap, rieszSeries]
    exact tsum_congr fun n => (tsum_rieszDoubleTerm_eq_rieszTerm x n).symm
  rw [rieszFunction, Complex.ofReal_mul, hR, Complex.ofReal_tsum, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [tsum_rieszDoubleTerm_eq_LSeries]
  have hw : 1 < (2 * (k : ℂ) + 2).re := by
    rw [show (2 * (k : ℂ) + 2) = ((2 * k + 2 : ℕ) : ℂ) by push_cast; ring, Complex.natCast_re]
    exact_mod_cast (by omega : 1 < 2 * k + 2)
  have hL := LSeries_moebius_mul_riemannZeta hw
  have hζ : riemannZeta (2 * k + 2) ≠ 0 := right_ne_zero_of_mul_eq_one hL
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  rw [eq_div_iff (mul_ne_zero hfac hζ)]
  calc (x : ℂ) * ((-x : ℂ) ^ k / (k.factorial : ℂ) *
        LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)) (2 * k + 2)) *
        ((k.factorial : ℂ) * riemannZeta (2 * k + 2))
      = (x : ℂ) * (-x : ℂ) ^ k * (LSeries (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ))
          (2 * k + 2) * riemannZeta (2 * k + 2)) := by field_simp
    _ = (-1) ^ k * (x : ℂ) ^ (k + 1) := by rw [hL, neg_pow]; ring

end

end RHTower
