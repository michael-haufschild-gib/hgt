import GaloisForLFunctions.RHTower.BarnesMellinRemainder

/-!
# Euler derivatives of the Mellin representation

Differentiating `x^{-w}` in `x` multiplies the integrand by `-w/x`, so

```text
d/dx (1/2πi)∫_{(σ)} F_m = x^{-1} · (1/2πi)∫_{(σ)} F_{m+1} ,
```

that is, the Euler operator `D = x d/dx` raises the weight `m` by one.  The exponential decay of the
kernel dominates the differentiated integrand uniformly on a neighbourhood of `x`, so the
differentiation under the integral sign is legitimate.  Consequently the Barnes expansion is
term-by-term differentiable: the `m`-th Euler derivative has the expansion whose `k`-th coefficient
is `(-k)^m` times the `k`-th coefficient of the original.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

noncomputable section

/-- The parameter derivative of `x^{-w}` along the positive reals. -/
theorem hasDerivAt_ofReal_cpow_neg (w : ℂ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun v : ℝ => ((v : ℝ) : ℂ) ^ (-w))
      ((((y : ℝ)⁻¹ : ℝ) : ℂ) * ((-w) * ((y : ℝ) : ℂ) ^ (-w))) y := by
  have hexpr : ∀ v : ℝ, 0 < v →
      ((v : ℝ) : ℂ) ^ (-w) = Complex.exp ((-w) * ((Real.log v : ℝ) : ℂ)) := by
    intro v hv
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt hv)),
      ← Complex.ofReal_log (le_of_lt hv)]
    ring_nf
  have hlog : HasDerivAt (fun v : ℝ => ((Real.log v : ℝ) : ℂ)) (((y⁻¹ : ℝ) : ℂ)) y :=
    (Real.hasDerivAt_log (ne_of_gt hy)).ofReal_comp
  have hmul : HasDerivAt (fun v : ℝ => (-w) * ((Real.log v : ℝ) : ℂ))
      ((-w) * ((y⁻¹ : ℝ) : ℂ)) y := hlog.const_mul (-w)
  have hexp := hmul.cexp
  have hcongr : (fun v : ℝ => ((v : ℝ) : ℂ) ^ (-w))
      =ᶠ[nhds y] fun v : ℝ => Complex.exp ((-w) * ((Real.log v : ℝ) : ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show y ∈ Set.Ioi (0 : ℝ) from hy)] with v hv
    exact hexpr v hv
  have hval : Complex.exp ((-w) * ((Real.log y : ℝ) : ℂ)) * ((-w) * ((y⁻¹ : ℝ) : ℂ))
      = (((y : ℝ)⁻¹ : ℝ) : ℂ) * ((-w) * ((y : ℝ) : ℂ) ^ (-w)) := by
    rw [← hexpr y hy]
    ring
  rw [← hval]
  exact hexp.congr_of_eventuallyEq hcongr

/-- The parameter derivative of the weighted integrand. -/
theorem hasDerivAt_barnesIntegrandPow_param {s σ t : ℝ} (m : ℕ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun v : ℝ => barnesIntegrandPow s v m ((σ : ℂ) + (t : ℂ) * I))
      ((((y : ℝ)⁻¹ : ℝ) : ℂ) * barnesIntegrandPow s y (m + 1) ((σ : ℂ) + (t : ℂ) * I)) y := by
  set w : ℂ := (σ : ℂ) + (t : ℂ) * I with hw
  have h0 := hasDerivAt_ofReal_cpow_neg w hy
  have h1 := (h0.mul_const (riemannZeta (-(s : ℂ) * w))).mul_const
    (-((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w)))
  have h2 := h1.const_mul ((-w) ^ m)
  have hval : ((-w) ^ m *
      ((((((y : ℝ)⁻¹ : ℝ) : ℂ) * ((-w) * ((y : ℝ) : ℂ) ^ (-w)))
        * riemannZeta (-(s : ℂ) * w))
        * -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * w))))
      = (((y : ℝ)⁻¹ : ℝ) : ℂ) * barnesIntegrandPow s y (m + 1) w := by
    simp only [barnesIntegrandPow, barnesIntegrand, pow_succ]
    ring
  rw [← hval]
  exact h2

/-- **Differentiating the vertical integral in the parameter.** -/
theorem hasDerivAt_integral_barnesIntegrandPow {s σ : ℝ} (hs : 0 < s) (m : ℕ)
    (hζ : -(s : ℝ) * σ ≠ 1) (hsin : Real.sin (Real.pi * σ) ≠ 0) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => ∫ t : ℝ, barnesIntegrandPow s y m ((σ : ℂ) + (t : ℂ) * I))
      (((x⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, barnesIntegrandPow s x (m + 1) ((σ : ℂ) + (t : ℂ) * I)) x := by
  classical
  set S : Set ℝ := Set.Ioo (x / 2) (2 * x) with hS
  have hSmem : S ∈ nhds x := by
    rw [hS]
    exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  -- a uniform bound for `y ^ (-σ)` on the surrounding compact interval
  have hcontpow : ContinuousOn (fun y : ℝ => y ^ (-σ)) (Set.Icc (x / 2) (2 * x)) := by
    intro y hy
    have hypos : (0 : ℝ) < y := lt_of_lt_of_le (by linarith) hy.1
    exact (Real.continuousAt_rpow_const y (-σ) (Or.inl (ne_of_gt hypos))).continuousWithinAt
  obtain ⟨Kmax, hKmax⟩ := (isCompact_Icc (a := x / 2) (b := 2 * x)).exists_bound_of_continuousOn
    hcontpow
  have hK0 : 0 ≤ max Kmax 0 := le_max_right _ _
  set F : ℝ → ℝ → ℂ := fun y t => barnesIntegrandPow s y m ((σ : ℂ) + (t : ℂ) * I) with hF
  set F' : ℝ → ℝ → ℂ :=
    fun y t => (((y : ℝ)⁻¹ : ℝ) : ℂ) * barnesIntegrandPow s y (m + 1) ((σ : ℂ) + (t : ℂ) * I)
    with hF'
  set bound : ℝ → ℝ := fun t => (2 / x) * (max Kmax 0)
    * ‖barnesIntegrandPow s 1 (m + 1) ((σ : ℂ) + (t : ℂ) * I)‖ with hbound
  have hbase1 := integrable_barnesIntegrandPow_vertical hs one_pos (m + 1) hζ hsin
  have hboundint : Integrable bound := by
    rw [hbound]
    exact hbase1.norm.const_mul (2 / x * max Kmax 0)
  have hFmeas : ∀ᶠ y : ℝ in nhds x, AEStronglyMeasurable (F y) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show x ∈ Set.Ioi (0 : ℝ) from hx)] with y hy
    exact (continuous_barnesIntegrandPow_vertical hy m hζ hsin).aestronglyMeasurable
  have hFint : Integrable (F x) := integrable_barnesIntegrandPow_vertical hs hx m hζ hsin
  have hF'meas : AEStronglyMeasurable (F' x) := by
    rw [hF']
    exact ((continuous_barnesIntegrandPow_vertical hx (m + 1) hζ hsin).const_mul
      (((x : ℝ)⁻¹ : ℝ) : ℂ)).aestronglyMeasurable
  have hbnd : ∀ᵐ t : ℝ, ∀ y ∈ S, ‖F' y t‖ ≤ bound t := by
    refine Filter.Eventually.of_forall fun t y hy => ?_
    obtain ⟨hy1, hy2⟩ := hy
    have hypos : (0 : ℝ) < y := by linarith
    have hyinv : y⁻¹ ≤ 2 / x := by
      rw [inv_eq_one_div, div_le_div_iff₀ hypos hx]
      linarith
    have hpow : y ^ (-σ) ≤ max Kmax 0 := by
      have h := hKmax y ⟨le_of_lt hy1, le_of_lt hy2⟩
      exact (le_abs_self _).trans (h.trans (le_max_left _ _))
    have hfac := norm_barnesIntegrandPow_factor (s := s) (σ := σ) (t := t) (m + 1) hypos
    rw [hF', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), hfac,
      hbound]
    have hnn : (0 : ℝ) ≤ ‖barnesIntegrandPow s 1 (m + 1) ((σ : ℂ) + (t : ℂ) * I)‖ := norm_nonneg _
    have hstep : y⁻¹ * (y ^ (-σ)
        * ‖barnesIntegrandPow s 1 (m + 1) ((σ : ℂ) + (t : ℂ) * I)‖)
        ≤ (2 / x) * ((max Kmax 0)
          * ‖barnesIntegrandPow s 1 (m + 1) ((σ : ℂ) + (t : ℂ) * I)‖) := by
      refine mul_le_mul hyinv ?_ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hpow hnn
    calc y⁻¹ * (y ^ (-σ) * ‖barnesIntegrandPow s 1 (m + 1) ((σ : ℂ) + (t : ℂ) * I)‖)
        ≤ (2 / x) * ((max Kmax 0)
            * ‖barnesIntegrandPow s 1 (m + 1) ((σ : ℂ) + (t : ℂ) * I)‖) := hstep
      _ = 2 / x * max Kmax 0 * ‖barnesIntegrandPow s 1 (m + 1) ((σ : ℂ) + (t : ℂ) * I)‖ := by ring
  have hdiff : ∀ᵐ t : ℝ, ∀ y ∈ S, HasDerivAt (fun y : ℝ => F y t) (F' y t) y := by
    refine Filter.Eventually.of_forall fun t y hy => ?_
    obtain ⟨hy1, -⟩ := hy
    exact hasDerivAt_barnesIntegrandPow_param m (by linarith)
  obtain ⟨-, hres⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le hSmem hFmeas hFint
    hF'meas hbnd hboundint hdiff
  have hcm : (∫ t : ℝ, F' x t)
      = ((x⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, barnesIntegrandPow s x (m + 1) ((σ : ℂ) + (t : ℂ) * I) := by
    rw [hF']
    exact MeasureTheory.integral_const_mul _ _
  rw [hcm] at hres
  exact hres


/-! ### The Euler operator on the contour representation -/

/-- The Euler operator `D = x d/dx`. -/
def eulerDeriv (f : ℝ → ℂ) : ℝ → ℂ := fun x => ((x : ℝ) : ℂ) * deriv f x

/-- **The Euler operator raises the weight.** -/
theorem eulerDeriv_barnes {s σ : ℝ} (hs : 0 < s) (m : ℕ)
    (hζ : -(s : ℝ) * σ ≠ 1) (hsin : Real.sin (Real.pi * σ) ≠ 0) {x : ℝ} (hx : 0 < x) :
    eulerDeriv (fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y m) σ) x
      = VerticalIntegral' (barnesIntegrandPow s x (m + 1)) σ := by
  have hbase := hasDerivAt_integral_barnesIntegrandPow hs m hζ hsin hx
  have hscaled := hbase.const_mul (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
  have hfun : (fun y : ℝ => (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
      * ∫ t : ℝ, barnesIntegrandPow s y m ((σ : ℂ) + (t : ℂ) * I))
      = fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y m) σ := by
    funext y
    rw [verticalIntegral'_eq_smul, Complex.real_smul]
  rw [hfun] at hscaled
  have hderiv := hscaled.deriv
  rw [eulerDeriv, hderiv, verticalIntegral'_eq_smul, Complex.real_smul]
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hinv : ((x : ℝ) : ℂ) * (((x⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [Complex.ofReal_inv]
    exact mul_inv_cancel₀ hxne
  calc ((x : ℝ) : ℂ) * ((((2 * Real.pi)⁻¹ : ℝ) : ℂ)
        * (((x⁻¹ : ℝ) : ℂ) * ∫ t : ℝ, barnesIntegrandPow s x (m + 1) ((σ : ℂ) + (t : ℂ) * I)))
      = (((x : ℝ) : ℂ) * (((x⁻¹ : ℝ) : ℂ))) * ((((2 * Real.pi)⁻¹ : ℝ) : ℂ)
          * ∫ t : ℝ, barnesIntegrandPow s x (m + 1) ((σ : ℂ) + (t : ℂ) * I)) := by ring
    _ = (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
          * ∫ t : ℝ, barnesIntegrandPow s x (m + 1) ((σ : ℂ) + (t : ℂ) * I) := by
        rw [hinv, one_mul]

/-- **Every Euler derivative of the contour representation is again a contour representation.** -/
theorem eulerIterate_barnes {s σ : ℝ} (hs : 0 < s)
    (hζ : -(s : ℝ) * σ ≠ 1) (hsin : Real.sin (Real.pi * σ) ≠ 0) (m : ℕ) :
    Set.EqOn (eulerDeriv^[m] (fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y 0) σ))
      (fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y m) σ) (Set.Ioi (0 : ℝ)) := by
  induction m with
  | zero => intro y _; rfl
  | succ k ih =>
      intro y hy
      have hypos : (0 : ℝ) < y := hy
      rw [Function.iterate_succ_apply']
      have hev : (eulerDeriv^[k] (fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y 0) σ))
          =ᶠ[nhds y] (fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y k) σ) :=
        Filter.eventuallyEq_of_mem (isOpen_Ioi.mem_nhds hy) ih
      have hderiv : deriv (eulerDeriv^[k]
          (fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y 0) σ)) y
          = deriv (fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y k) σ) y :=
        hev.deriv_eq
      rw [eulerDeriv, hderiv]
      have := eulerDeriv_barnes hs k hζ hsin hypos
      rw [eulerDeriv] at this
      exact this


/-! ### The termwise-differentiable Barnes expansion -/

/-- Iterating the Euler operator respects agreement on an open set. -/
theorem eulerDeriv_iterate_congr {f g : ℝ → ℂ} {U : Set ℝ} (hU : IsOpen U) (h : Set.EqOn f g U)
    (m : ℕ) : Set.EqOn (eulerDeriv^[m] f) (eulerDeriv^[m] g) U := by
  induction m with
  | zero => exact h
  | succ k ih =>
      intro y hy
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', eulerDeriv, eulerDeriv]
      have hev : (eulerDeriv^[k] f) =ᶠ[nhds y] (eulerDeriv^[k] g) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hy) ih
      rw [hev.deriv_eq]

/-- The Euler sum of the canonical product. -/
def barnesEulerSum (s : ℝ) : ℝ → ℂ :=
  fun x => ∑' n : ℕ, ((x : ℝ) : ℂ) / (((((n : ℝ) + 1) ^ s : ℝ) : ℂ) + ((x : ℝ) : ℂ))

/-- The initial abscissa of the ladder. -/
def barnesStart (s : ℝ) : ℝ := -(1 + 1 / s) / 2

theorem barnesStart_mem {s : ℝ} (hs1 : 1 < s) : -1 < barnesStart s ∧ barnesStart s < 0 := by
  have hs : (0 : ℝ) < s := lt_trans zero_lt_one hs1
  have hinv0 : (0 : ℝ) < 1 / s := by positivity
  have hinv1 : 1 / s < 1 := by rw [div_lt_one hs]; exact hs1
  constructor
  · rw [barnesStart]; linarith
  · rw [barnesStart]; linarith

theorem barnesStart_sin {s : ℝ} (hs1 : 1 < s) : Real.sin (Real.pi * barnesStart s) ≠ 0 := by
  obtain ⟨h1, h2⟩ := barnesStart_mem hs1
  exact GaloisForLFunctions.HTGeometry.sin_pi_ne_zero_of_mem_strip h1 h2

theorem barnesStart_zeta {s : ℝ} (hs1 : 1 < s) : -(s : ℝ) * barnesStart s ≠ 1 := by
  have hs : (0 : ℝ) < s := lt_trans zero_lt_one hs1
  rw [barnesStart]
  intro hcon
  have hval : -(s : ℝ) * (-(1 + 1 / s) / 2) = (s + 1) / 2 := by field_simp
  rw [hval] at hcon
  have : s = 1 := by linarith
  exact absurd this (ne_of_gt hs1)

/-- On the positive axis the Euler sum is the contour representation. -/
theorem barnesEulerSum_eqOn {s : ℝ} (hs1 : 1 < s) :
    Set.EqOn (barnesEulerSum s)
      (fun y : ℝ => VerticalIntegral' (barnesIntegrandPow s y 0) (barnesStart s))
      (Set.Ioi (0 : ℝ)) := by
  have hs : (0 : ℝ) < s := lt_trans zero_lt_one hs1
  have hinv0 : (0 : ℝ) < 1 / s := by positivity
  have hinv1 : 1 / s < 1 := by rw [div_lt_one hs]; exact hs1
  intro x hx
  have hxpos : (0 : ℝ) < x := hx
  obtain ⟨h1, h2⟩ := barnesStart_mem hs1
  have hsσ : s * barnesStart s < -1 := by
    rw [barnesStart]
    have hval : s * (-(1 + 1 / s) / 2) = -(s + 1) / 2 := by field_simp
    rw [hval]
    linarith
  have hbase := hasSum_barnes_verticalIntegral' (s := s) (x := x) (σ := barnesStart s)
    hxpos h1 h2 hsσ
  have hval := hbase.tsum_eq
  rw [barnesEulerSum]
  rw [hval]
  exact congrArg (fun f => VerticalIntegral' f (barnesStart s))
    (funext fun w => (barnesIntegrandPow_zero s x w).symm)

/-- **The Barnes expansion is termwise differentiable.**  For every Euler derivative `D^m` and every
truncation `K` the error after the leading term and the first `K+1` descending powers — each
weighted by `(-k)^m` — is `O(x^{-(K+1/2)})`. -/
theorem barnes_poincare_expansion_euler {s : ℝ} (hs1 : 1 < s) (m K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖(eulerDeriv^[m] (barnesEulerSum s)) x
          + barnesLeadingResidue s x m
          + ∑ k ∈ Finset.range (K + 1), barnesTailResidue s x m k‖
        ≤ C * x ^ (-((K : ℝ) + 1 / 2)) := by
  have hs : (0 : ℝ) < s := lt_trans zero_lt_one hs1
  obtain ⟨C, hC0, hC⟩ := exists_bound_barnes_remainder s m K
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hxmem : x ∈ Set.Ioi (0 : ℝ) := hx
  have hcongr := eulerDeriv_iterate_congr isOpen_Ioi (barnesEulerSum_eqOn hs1) m hxmem
  have hiter := eulerIterate_barnes hs (barnesStart_zeta hs1) (barnesStart_sin hs1) m hxmem
  have hval : (eulerDeriv^[m] (barnesEulerSum s)) x
      = VerticalIntegral' (barnesIntegrandPow s x m) (barnesStart s) := by
    rw [hcongr, hiter]
  rw [hval, barnesStart]
  rw [verticalIntegral'_barnes_finite_expansion hs1 hx m (K + 1)]
  have hshape : VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s (K + 1))
      - barnesLeadingResidue s x m
      - (∑ k ∈ Finset.range (K + 1), barnesTailResidue s x m k)
      + barnesLeadingResidue s x m
      + ∑ k ∈ Finset.range (K + 1), barnesTailResidue s x m k
      = VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s (K + 1)) := by ring
  rw [hshape]
  exact hC x hx

end

end RHTower
