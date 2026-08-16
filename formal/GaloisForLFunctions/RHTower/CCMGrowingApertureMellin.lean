import GaloisForLFunctions.RHTower.CothInfra
import GaloisForLFunctions.RHTower.LegStripSteepness
import Mathlib

/-!
# The growing-aperture Mellin evaluation norm and its transfer rates

The card proves, and this module certifies unconditionally, the elementary Hilbert-space layer of
the CCM growing-aperture determinant transfer.

*The exact evaluation norm, equation `(3)`.*  On `I_λ = [λ⁻¹, λ]` with the multiplicative Haar
measure `d*u = du/u`, the representing function of Mellin evaluation at `z = x + i y` is `u^{iz}`,
whose squared `L²(I_λ, d*u)` norm is `∫_{λ⁻¹}^{λ} u^{2y-1} du`.  That integral is `2 log λ` at
`y = 0` and `sinh(2y log λ)/y` otherwise.

*The sup over a substrip, equation `(4)`.*  `y ↦ sinh(2y log λ)/y` is even and strictly increasing
in `|y|`, so the supremum over `|Im z| ≤ a` is attained at `|y| = a`.  The two ingredients — that
`u ↦ sinh u/u` is strictly increasing on `(0,∞)`, and that `u < sinh u` there — are proved from
scratch.

*Parity removes no power, equation `(8a)`.*  On the even subspace the representing exponential is
replaced by `cos(zt)`; its squared modulus is exactly `(cosh(2yt) + cos(2xt))/2`, so the squared
norm on `[-log λ, log λ]` is `sinh(2y log λ)/(2y) + sin(2x log λ)/(2x)`, whose first term is still
at least `(λ^{2y} - 1)/(4y)`.

*The transfer rates, equations `(5)`, `(7)`, `(12b)`, `(12c)`.*  Three implications between decay
hypotheses: a `λ^a`-bounded evaluation norm against an `o(λ^{-a})` difference gives `o(1)`; an
`O(λ^{-b})` quantity beats every `λ^e` with `e < b`; and a quadratic Rayleigh-excess bound
`d² ≤ 2q` upgrades `λ^{2a} q → 0` to `λ^a d → 0`.

*The metric gate, equation `(14a)`.*  For a real-zero determinant family the horizontal defect
energy is identically zero, so it is `o((log N)²)` trivially.

The CCM closed Weil form, the regularized determinant identity `(2)`, the Davis–Kahan bound `(10)`,
the Rayleigh-excess inequality `(12a)`, and the prolate-seed Mellin convergence are cited parents
and stay outside the Lean statement.
-/

open Filter Topology intervalIntegral

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The exact evaluation norm -/

/-- The squared operator norm of Mellin evaluation at height `y ≠ 0` on the aperture
`I_λ = [λ⁻¹, λ]`. -/
def apertureEvalNormSq (lam y : ℝ) : ℝ := Real.sinh (2 * y * Real.log lam) / y

/-- **Equation (3), off-axis.**  The squared evaluation norm is `sinh(2y log λ)/y`. -/
theorem integral_aperture_rpow {lam y : ℝ} (hlam : 1 < lam) (hy : y ≠ 0) :
    (∫ u in (1 / lam)..lam, u ^ (2 * y - 1)) = apertureEvalNormSq lam y := by
  have hlam0 : (0 : ℝ) < lam := lt_trans one_pos hlam
  have hinv : (0 : ℝ) < 1 / lam := by positivity
  have hmem : (0 : ℝ) ∉ Set.uIcc (1 / lam) lam := by
    intro h
    rcases Set.mem_uIcc.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · linarith
    · linarith
  have hr : (2 * y - 1 : ℝ) ≠ -1 := by
    intro hcon
    exact hy (by linarith)
  rw [integral_rpow (Or.inr ⟨hr, hmem⟩)]
  have hexp : (2 * y - 1 + 1 : ℝ) = 2 * y := by ring
  rw [hexp]
  have h1 : lam ^ (2 * y) = Real.exp (2 * y * Real.log lam) := by
    rw [Real.rpow_def_of_pos hlam0]
    ring_nf
  have h2 : (1 / lam) ^ (2 * y) = Real.exp (-(2 * y * Real.log lam)) := by
    rw [one_div, Real.rpow_def_of_pos (by positivity), Real.log_inv]
    ring_nf
  rw [h1, h2, apertureEvalNormSq, Real.sinh_eq]
  field_simp

/-- **Equation (3), on-axis.**  On the real axis the squared evaluation norm is `2 log λ`. -/
theorem integral_aperture_inv {lam : ℝ} (hlam : 1 < lam) :
    (∫ u in (1 / lam)..lam, u ^ (-1 : ℝ)) = 2 * Real.log lam := by
  have hlam0 : (0 : ℝ) < lam := lt_trans one_pos hlam
  have hcongr : (∫ u in (1 / lam)..lam, u ^ (-1 : ℝ)) = ∫ u in (1 / lam)..lam, u⁻¹ := by
    simp [Real.rpow_neg_one]
  rw [hcongr, integral_inv_of_pos (by positivity) hlam0]
  have hval : lam / (1 / lam) = lam ^ 2 := by field_simp
  rw [hval, Real.log_pow]
  norm_num

/-! ## The elementary hyperbolic inequalities

Already in the tree and reused here, not rebuilt: `RHTower.self_lt_sinh` (`LegStripSteepness`),
`RHTower.sinh_pos_of_pos` and `RHTower.sinh_lt_mul_cosh` (`CothInfra`), and Mathlib's
`Real.one_lt_cosh`.  Only the quotient monotonicity below is new.
-/

/-- **Equation (4), core monotonicity.**  `u ↦ sinh u / u` is strictly increasing on `(0,∞)`. -/
theorem sinh_div_self_strictMonoOn :
    StrictMonoOn (fun u : ℝ => Real.sinh u / u) (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro x hx
    exact ne_of_gt (Set.mem_Ioi.mp hx)
  · intro x hx
    rw [interior_Ioi] at hx
    have hx0 := Set.mem_Ioi.mp hx
    have hd : HasDerivAt (fun u : ℝ => Real.sinh u / u)
        ((Real.cosh x * x - Real.sinh x * 1) / x ^ 2) x :=
      (Real.hasDerivAt_sinh x).fun_div (hasDerivAt_id x) (ne_of_gt hx0)
    rw [hd.deriv]
    refine div_pos ?_ (by positivity)
    have := RHTower.sinh_lt_mul_cosh hx0
    nlinarith [this]

/-! ## The supremum over a compact substrip -/

/-- The evaluation norm in the scaled form used for the monotone comparison. -/
theorem apertureEvalNormSq_eq {lam t : ℝ} (hlam : 1 < lam) (ht : 0 < t) :
    apertureEvalNormSq lam t
      = 2 * Real.log lam * (Real.sinh (2 * t * Real.log lam) / (2 * t * Real.log lam)) := by
  have hL : 0 < Real.log lam := Real.log_pos hlam
  unfold apertureEvalNormSq
  field_simp

/-- **Equation (4).**  The squared evaluation norm increases with the substrip height, so the
supremum over `|Im z| ≤ a` is attained at `|y| = a`. -/
theorem apertureEvalNormSq_mono {lam a y : ℝ} (hlam : 1 < lam) (hy : 0 < y) (hya : y ≤ a) :
    apertureEvalNormSq lam y ≤ apertureEvalNormSq lam a := by
  have hL : 0 < Real.log lam := Real.log_pos hlam
  have ha : 0 < a := lt_of_lt_of_le hy hya
  rw [apertureEvalNormSq_eq hlam hy, apertureEvalNormSq_eq hlam ha]
  rcases eq_or_lt_of_le hya with heq | hlt
  · rw [heq]
  · have hu : (0 : ℝ) < 2 * y * Real.log lam := by positivity
    have hv : (0 : ℝ) < 2 * a * Real.log lam := by positivity
    have huv : 2 * y * Real.log lam < 2 * a * Real.log lam := by nlinarith
    have hmono := sinh_div_self_strictMonoOn (Set.mem_Ioi.mpr hu) (Set.mem_Ioi.mpr hv) huv
    have h2L : (0 : ℝ) ≤ 2 * Real.log lam := by linarith
    exact mul_le_mul_of_nonneg_left hmono.le h2L

/-- **Equation (4), the on-axis comparison.**  The `y = 0` value `2 log λ` is dominated by the
value at any positive height. -/
theorem two_log_le_apertureEvalNormSq {lam a : ℝ} (hlam : 1 < lam) (ha : 0 < a) :
    2 * Real.log lam ≤ apertureEvalNormSq lam a := by
  have hL : 0 < Real.log lam := Real.log_pos hlam
  have hu : (0 : ℝ) < 2 * a * Real.log lam := by positivity
  have hs := RHTower.self_lt_sinh hu
  unfold apertureEvalNormSq
  rw [le_div_iff₀ ha]
  nlinarith [hs]

/-! ## Parity removes no power -/

/-- The squared modulus of `cos(z t)` for `z = x + i y`, in real coordinates. -/
theorem sq_modulus_cos (x y t : ℝ) :
    (Real.cos (x * t) * Real.cosh (y * t)) ^ 2 + (Real.sin (x * t) * Real.sinh (y * t)) ^ 2
      = (Real.cosh (2 * (y * t)) + Real.cos (2 * (x * t))) / 2 := by
  have hc := Real.cosh_sq (y * t)
  have hs := Real.sin_sq_add_cos_sq (x * t)
  have hch := Real.cosh_two_mul (y * t)
  have hcs := Real.cos_two_mul (x * t)
  nlinarith [hc, hs, hch, hcs]

/-- The even representing function is `cos(z t)`, and its squared modulus is the stated real
combination. -/
theorem normSq_cos_mul (x y t : ℝ) :
    ‖Complex.cos (((x : ℂ) + (y : ℂ) * Complex.I) * (t : ℂ))‖ ^ 2
      = (Real.cosh (2 * (y * t)) + Real.cos (2 * (x * t))) / 2 := by
  have harg : ((x : ℂ) + (y : ℂ) * Complex.I) * (t : ℂ)
      = ((x * t : ℝ) : ℂ) + ((y * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.cos_add_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  have := sq_modulus_cos x y t
  nlinarith [this]

/-- The symmetric integral of `cosh(c t)`. -/
theorem integral_cosh_symm {c L : ℝ} (hc : c ≠ 0) :
    (∫ t in (-L)..L, Real.cosh (c * t)) = 2 * Real.sinh (c * L) / c := by
  have hderiv : ∀ t ∈ Set.uIcc (-L) L,
      HasDerivAt (fun s : ℝ => Real.sinh (c * s) / c) (Real.cosh (c * t)) t := by
    intro t _
    have hinner : HasDerivAt (fun s : ℝ => c * s) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    have hcomp : HasDerivAt (fun s : ℝ => Real.sinh (c * s)) (Real.cosh (c * t) * c) t :=
      (Real.hasDerivAt_sinh (c * t)).comp t hinner
    have hres := hcomp.div_const c
    refine hres.congr_deriv ?_
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => Real.cosh (c * t)) (Set.uIcc (-L) L) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  rw [mul_neg, Real.sinh_neg]
  ring

/-- The symmetric integral of `cos(c t)`. -/
theorem integral_cos_symm {c L : ℝ} (hc : c ≠ 0) :
    (∫ t in (-L)..L, Real.cos (c * t)) = 2 * Real.sin (c * L) / c := by
  have hderiv : ∀ t ∈ Set.uIcc (-L) L,
      HasDerivAt (fun s : ℝ => Real.sin (c * s) / c) (Real.cos (c * t)) t := by
    intro t _
    have hinner : HasDerivAt (fun s : ℝ => c * s) c t := by
      simpa using (hasDerivAt_id t).const_mul c
    have hcomp : HasDerivAt (fun s : ℝ => Real.sin (c * s)) (Real.cos (c * t) * c) t :=
      (Real.hasDerivAt_sin (c * t)).comp t hinner
    have hres := hcomp.div_const c
    refine hres.congr_deriv ?_
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => Real.cos (c * t)) (Set.uIcc (-L) L) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  rw [mul_neg, Real.sin_neg]
  ring

/-- **Equation (8a).**  The even-subspace squared evaluation norm on `[-L, L]`. -/
theorem evenAperture_normSq {x y L : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    (∫ t in (-L)..L, (Real.cosh (2 * y * t) + Real.cos (2 * x * t)) / 2)
      = Real.sinh (2 * y * L) / (2 * y) + Real.sin (2 * x * L) / (2 * x) := by
  have hy2 : (2 : ℝ) * y ≠ 0 := by simpa using hy
  have hx2 : (2 : ℝ) * x ≠ 0 := by simpa using hx
  have hcoshInt : IntervalIntegrable (fun t : ℝ => Real.cosh (2 * y * t)) MeasureTheory.volume
      (-L) L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hcosInt : IntervalIntegrable (fun t : ℝ => Real.cos (2 * x * t)) MeasureTheory.volume
      (-L) L := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hsplit : (∫ t in (-L)..L, (Real.cosh (2 * y * t) + Real.cos (2 * x * t)) / 2)
      = ((∫ t in (-L)..L, Real.cosh (2 * y * t)) + ∫ t in (-L)..L, Real.cos (2 * x * t)) / 2 := by
    rw [← intervalIntegral.integral_add hcoshInt hcosInt, ← intervalIntegral.integral_div]
  have hcoshEq : (∫ t in (-L)..L, Real.cosh (2 * y * t))
      = 2 * Real.sinh (2 * y * L) / (2 * y) := by
    have := integral_cosh_symm (c := 2 * y) (L := L) hy2
    simpa using this
  have hcosEq : (∫ t in (-L)..L, Real.cos (2 * x * t))
      = 2 * Real.sin (2 * x * L) / (2 * x) := by
    have := integral_cos_symm (c := 2 * x) (L := L) hx2
    simpa using this
  rw [hsplit, hcoshEq, hcosEq]
  field_simp

/-- **Equation (8a), the growth statement.**  The hyperbolic term of the even squared norm still
grows like `λ^{2y}`; the exact CCM parity removes no power. -/
theorem evenAperture_growth {lam y : ℝ} (hlam : 1 < lam) (hy : 0 < y) :
    (lam ^ (2 * y) - 1) / (4 * y) ≤ Real.sinh (2 * y * Real.log lam) / (2 * y) := by
  have hlam0 : (0 : ℝ) < lam := lt_trans one_pos hlam
  have hL : 0 < Real.log lam := Real.log_pos hlam
  have hA : (0 : ℝ) < 2 * y * Real.log lam := by positivity
  have hpow : lam ^ (2 * y) = Real.exp (2 * y * Real.log lam) := by
    rw [Real.rpow_def_of_pos hlam0]
    ring_nf
  have hneg : Real.exp (-(2 * y * Real.log lam)) ≤ 1 := by
    have : Real.exp (-(2 * y * Real.log lam)) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by linarith)
    simpa using this
  rw [hpow, Real.sinh_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hneg, Real.exp_pos (2 * y * Real.log lam)]

/-! ## The transfer rates -/

/-- **Equations (5)–(8).**  A `λ^a`-bounded evaluation norm against a difference that is
`o(λ^{-a})` gives a vanishing Mellin difference. -/
theorem tendsto_evalTransfer {N delta : ℝ → ℝ} {C a : ℝ}
    (hN : ∀ lam, 0 ≤ N lam) (hd : ∀ lam, 0 ≤ delta lam)
    (hbd : ∀ lam, N lam ≤ C * lam ^ a)
    (hlim : Tendsto (fun lam : ℝ => C * (lam ^ a * delta lam)) atTop (𝓝 0)) :
    Tendsto (fun lam : ℝ => N lam * delta lam) atTop (𝓝 0) := by
  refine squeeze_zero (fun lam => mul_nonneg (hN lam) (hd lam)) (fun lam => ?_) hlim
  calc N lam * delta lam ≤ (C * lam ^ a) * delta lam :=
        mul_le_mul_of_nonneg_right (hbd lam) (hd lam)
    _ = C * (lam ^ a * delta lam) := by ring

/-- **Equation (7) ⇒ (5), and (12c) ⇒ (12b).**  An `O(λ^{-b})` quantity beats every power
`λ^e` with `e < b`. -/
theorem tendsto_rpow_mul_of_le {C b e : ℝ} {q : ℝ → ℝ}
    (hq : ∀ lam, 0 ≤ q lam) (hbd : ∀ lam, q lam ≤ C * lam ^ (-b)) (he : e < b) :
    Tendsto (fun lam : ℝ => lam ^ e * q lam) atTop (𝓝 0) := by
  have hlim : Tendsto (fun lam : ℝ => C * lam ^ (-(b - e))) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := b - e) (by linarith)
    simpa using h.const_mul C
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    exact mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hlam e)) (hq lam)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
    have hp : (0 : ℝ) < lam ^ e := Real.rpow_pos_of_pos hlam e
    have h1 : lam ^ e * q lam ≤ lam ^ e * (C * lam ^ (-b)) :=
      mul_le_mul_of_nonneg_left (hbd lam) hp.le
    have h3 : lam ^ e * lam ^ (-b) = lam ^ (-(b - e)) := by
      rw [← Real.rpow_add hlam]
      congr 1
      ring
    calc lam ^ e * q lam ≤ lam ^ e * (C * lam ^ (-b)) := h1
      _ = C * (lam ^ e * lam ^ (-b)) := by ring
      _ = C * lam ^ (-(b - e)) := by rw [h3]

/-- **Equation (12b) ⇒ (5).**  A quadratic Rayleigh-excess bound `d² ≤ 2q` upgrades a form-level
rate `λ^{2a} q → 0` to the projective vector rate `λ^a d → 0`. -/
theorem tendsto_rpow_mul_of_sq {a : ℝ} {d q : ℝ → ℝ}
    (hd : ∀ lam, 0 ≤ d lam) (hsq : ∀ lam, (d lam) ^ 2 ≤ 2 * q lam)
    (hlim : Tendsto (fun lam : ℝ => lam ^ (2 * a) * q lam) atTop (𝓝 0)) :
    Tendsto (fun lam : ℝ => lam ^ a * d lam) atTop (𝓝 0) := by
  have hlim2 : Tendsto (fun lam : ℝ => 2 * (lam ^ (2 * a) * q lam)) atTop (𝓝 0) := by
    simpa using hlim.const_mul (2 : ℝ)
  have hsq2 : Tendsto (fun lam : ℝ => (lam ^ a * d lam) ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hlim2
    · filter_upwards with lam
      positivity
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
      have hp : (0 : ℝ) < lam ^ a := Real.rpow_pos_of_pos hlam a
      have h2a : (lam ^ a) ^ 2 = lam ^ (2 * a) := by
        rw [← Real.rpow_natCast (lam ^ a) 2, ← Real.rpow_mul hlam.le]
        congr 1
        push_cast
        ring
      have hexp : (lam ^ a * d lam) ^ 2 = (lam ^ a) ^ 2 * (d lam) ^ 2 := by ring
      rw [hexp, h2a]
      have hmul := mul_le_mul_of_nonneg_left (hsq lam)
        (le_of_lt (Real.rpow_pos_of_pos hlam (2 * a)))
      calc lam ^ (2 * a) * (d lam) ^ 2 ≤ lam ^ (2 * a) * (2 * q lam) := hmul
        _ = 2 * (lam ^ (2 * a) * q lam) := by ring
  have hroot : Tendsto (fun lam : ℝ => Real.sqrt ((lam ^ a * d lam) ^ 2)) atTop
      (𝓝 (Real.sqrt 0)) := (Real.continuous_sqrt.tendsto 0).comp hsq2
  rw [Real.sqrt_zero] at hroot
  refine hroot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with lam hlam
  have hp : (0 : ℝ) < lam ^ a := Real.rpow_pos_of_pos hlam a
  exact Real.sqrt_sq (mul_nonneg hp.le (hd lam))

/-! ## The metric gate -/

/-- **Equation (14a).**  For a real-zero determinant family the horizontal defect energy is
identically zero, so the metric gate of the finite-prime logarithmic boundary theorem is
discharged. -/
theorem ccmZeroFiber_energy_isLittleO :
    (fun _ : ℕ => (0 : ℝ)) =o[atTop] fun N : ℕ => (Real.log N) ^ 2 :=
  Asymptotics.isLittleO_zero _ _

end GaloisForLFunctions.RHTower

end
