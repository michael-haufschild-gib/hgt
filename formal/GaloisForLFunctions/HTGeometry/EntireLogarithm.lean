import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

/-!
# The logarithm of a nonvanishing entire function

A nonvanishing entire function is the exponential of an entire function.  The logarithmic derivative
`f'/f` is entire, hence has a global primitive `g`; then `f · exp(-g)` has vanishing derivative and
is therefore constant.

This is the first step of the Hadamard argument: with a logarithm in hand, growth bounds on `f`
become bounds on the real part of `g`, which Borel--Carathéodory converts into bounds on `g` itself.
-/

open Complex

namespace GaloisForLFunctions.HTGeometry

/-- **Entire logarithm.**  A nonvanishing entire function is `f 0` times the exponential of an
entire function vanishing at the origin. -/
theorem exists_entire_log_of_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 = 0 ∧ ∀ z, f z = f 0 * Complex.exp (g z) := by
  have hderiv : Differentiable ℂ (deriv f) := fun z =>
    ((Differentiable.analyticAt hf z).deriv).differentiableAt
  have hquot : Differentiable ℂ fun z => deriv f z / f z := fun z =>
    ((hderiv z).div (hf z) (hne z))
  obtain ⟨g, hg0, hg⟩ := (hquot.isExactOn_univ).with_val_at 0 0
  have hgdiff : Differentiable ℂ g := fun z =>
    (hg z (Set.mem_univ z)).differentiableAt
  refine ⟨g, hgdiff, hg0, ?_⟩
  -- `f · exp (-g)` has vanishing derivative, hence is constant.
  set F : ℂ → ℂ := fun z => f z * Complex.exp (-g z) with hF
  have hFdiff : Differentiable ℂ F := fun z =>
    (hf z).mul (((hgdiff z).neg).cexp)
  have hFderiv : ∀ z, deriv F z = 0 := by
    intro z
    have hgz : HasDerivAt g (deriv f z / f z) z := hg z (Set.mem_univ z)
    have hexp : HasDerivAt (fun w => Complex.exp (-g w))
        (-(Complex.exp (-g z) * (deriv f z / f z))) z := by
      simpa using (hgz.neg).cexp
    have hprod : HasDerivAt F
        (deriv f z * Complex.exp (-g z) +
          f z * (-(Complex.exp (-g z) * (deriv f z / f z)))) z :=
      (hf z).hasDerivAt.mul hexp
    rw [hprod.deriv]
    field_simp
    rw [div_self (hne z)]
    ring
  have hconst : ∀ z, F z = F 0 := by
    intro z
    exact is_const_of_deriv_eq_zero hFdiff hFderiv z 0
  intro z
  have h0 : F 0 = f 0 := by
    rw [hF]
    simp [hg0]
  have hz := hconst z
  rw [h0, hF] at hz
  have hexpne : Complex.exp (-g z) ≠ 0 := Complex.exp_ne_zero _
  field_simp at hz
  rw [← hz, mul_assoc, ← Complex.exp_add]
  simp

/-! ### Polynomial growth bounds the Taylor degree -/

open Filter Topology Metric

/-- **Cauchy estimate at infinity.**  An entire function whose growth exponent is strictly below `n`
has vanishing `n`-th derivative everywhere: the Cauchy estimate on the circle of radius `R` bounds
the `n`-th derivative by `n! · C (2R)^a / R^n`, which tends to zero when `a < n`. -/
theorem iteratedDeriv_eq_zero_of_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {C a : ℝ} {n : ℕ} (ha0 : 0 ≤ a) (han : a < n) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ C * (1 + ‖z‖) ^ a) (c : ℂ) :
    iteratedDeriv n g c = 0 := by
  have hkey : ∀ R : ℝ, 1 + ‖c‖ ≤ R → 0 < R →
      ‖iteratedDeriv n g c‖ ≤ (n.factorial : ℝ) * (C * (3 * R) ^ a) / R ^ n := by
    intro R hRc hR
    refine norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
      hg.diffContOnCl fun z hz => ?_
    have hz' : ‖z - c‖ = R := by simpa [Complex.dist_eq] using mem_sphere_iff_norm.1 hz
    have hzc : ‖z‖ ≤ 1 + ‖c‖ + R := by
      have hsub : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by simpa using norm_add_le (z - c) c
      rw [hz'] at hsub
      linarith
    have hR1 : (1 : ℝ) ≤ R := le_trans (by simp) hRc
    have hle : (1 : ℝ) + ‖z‖ ≤ 3 * R := by linarith
    have h1 : (0 : ℝ) ≤ 1 + ‖z‖ := by positivity
    calc ‖g z‖ ≤ C * (1 + ‖z‖) ^ a := hbound z
      _ ≤ C * (3 * R) ^ a := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow h1 hle ha0) hC
  have hrw : ∀ R : ℝ, 0 < R →
      (n.factorial : ℝ) * (C * (3 * R) ^ a) / R ^ n =
        ((n.factorial : ℝ) * C * 3 ^ a) * R ^ (a - (n : ℝ)) := by
    intro R hR
    rw [Real.mul_rpow (by norm_num) hR.le, Real.rpow_sub hR, ← Real.rpow_natCast R n]
    field_simp
  have hpow : Tendsto (fun R : ℝ => R ^ (a - (n : ℝ))) atTop (𝓝 0) := by
    have hy : 0 < (n : ℝ) - a := by linarith
    simpa using tendsto_rpow_neg_atTop hy
  have hlim : Tendsto (fun R : ℝ => ((n.factorial : ℝ) * C * 3 ^ a) * R ^ (a - (n : ℝ)))
      atTop (𝓝 0) := by
    simpa using hpow.const_mul ((n.factorial : ℝ) * C * 3 ^ a)
  refine norm_eq_zero.mp (le_antisymm ?_ (norm_nonneg _))
  refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim ?_
  filter_upwards [eventually_ge_atTop (1 + ‖c‖), eventually_gt_atTop (0 : ℝ)] with R hRc hR
  rw [← hrw R hR]
  exact hkey R hRc hR

/-- An entire function of growth exponent below `2` is affine: its second derivative vanishes. -/
theorem iteratedDeriv_two_eq_zero_of_growth {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    {C a : ℝ} (ha0 : 0 ≤ a) (ha2 : a < 2) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖g z‖ ≤ C * (1 + ‖z‖) ^ a) (c : ℂ) :
    iteratedDeriv 2 g c = 0 :=
  iteratedDeriv_eq_zero_of_growth hg ha0 (by exact_mod_cast ha2) hC hbound c

/-! ### Order-one growth forces an exponential-affine form -/

/-- An entire function with vanishing second derivative is affine. -/
theorem eq_affine_of_iteratedDeriv_two_eq_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (h2 : ∀ c, iteratedDeriv 2 g c = 0) (z : ℂ) :
    g z = g 0 + deriv g 0 * z := by
  have hderiv : Differentiable ℂ (deriv g) := fun w =>
    ((Differentiable.analyticAt hg w).deriv).differentiableAt
  have hdd : ∀ c, deriv (deriv g) c = 0 := by
    intro c
    have hc := h2 c
    rwa [iteratedDeriv_succ, iteratedDeriv_one] at hc
  have hconstDeriv : ∀ c, deriv g c = deriv g 0 :=
    fun c => is_const_of_deriv_eq_zero hderiv hdd c 0
  set F : ℂ → ℂ := fun w => g w - deriv g 0 * w with hF
  have hFdiff : Differentiable ℂ F := fun w =>
    (hg w).sub ((differentiable_const (deriv g 0)).mul differentiable_id w)
  have hFderiv : ∀ w, deriv F w = 0 := by
    intro w
    have hd : HasDerivAt F (deriv g w - deriv g 0 * 1) w :=
      (hg w).hasDerivAt.sub ((hasDerivAt_id w).const_mul (deriv g 0))
    rw [hd.deriv, hconstDeriv w, mul_one, sub_self]
  have hc := is_const_of_deriv_eq_zero hFdiff hFderiv z 0
  rw [hF] at hc
  simp only [mul_zero, sub_zero] at hc
  linear_combination hc

/-- **Order-one growth with no zeros forces an exponential.**  An entire nonvanishing function whose
norm is bounded by `exp (C (1+‖z‖)^a)` with `a < 2` equals `f 0 · exp (B z)` for some `B`.  Its
logarithmic growth is therefore at most linear along every ray. -/
theorem exists_linear_of_ne_zero_of_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∀ z, f z ≠ 0) {C a : ℝ} (ha0 : 0 ≤ a) (ha2 : a < 2) (hC : 0 ≤ C)
    (hgrow : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ a)) :
    ∃ B : ℂ, ∀ z, f z = f 0 * Complex.exp (B * z) := by
  obtain ⟨g, hgdiff, hg0, hfg⟩ := exists_entire_log_of_ne_zero hf hne
  have hf0pos : 0 < ‖f 0‖ := norm_pos_iff.mpr (hne 0)
  set K : ℝ := |Real.log ‖f 0‖| with hK
  have hK0 : 0 ≤ K := abs_nonneg _
  have hre : ∀ z, (g z).re ≤ C * (1 + ‖z‖) ^ a + K := by
    intro z
    have h1 : ‖f 0‖ * Real.exp ((g z).re) = ‖f z‖ := by
      rw [hfg z, norm_mul, Complex.norm_exp]
    have h2 : Real.exp ((g z).re) ≤ Real.exp (C * (1 + ‖z‖) ^ a) / ‖f 0‖ := by
      rw [le_div_iff₀ hf0pos, mul_comm, h1]
      exact hgrow z
    have h3 : (g z).re ≤ Real.log (Real.exp (C * (1 + ‖z‖) ^ a) / ‖f 0‖) := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      exact h2
    rw [Real.log_div (Real.exp_ne_zero _) (ne_of_gt hf0pos), Real.log_exp] at h3
    have hneg : -Real.log ‖f 0‖ ≤ K := by rw [hK]; exact neg_le_abs _
    linarith
  set C₂ : ℝ := 2 * C * 3 ^ a + 2 * K + 2 with hC₂
  have hC₂0 : 0 ≤ C₂ := by
    have : (0 : ℝ) ≤ 2 * C * 3 ^ a := by positivity
    rw [hC₂]; linarith
  have hgbound : ∀ z : ℂ, ‖g z‖ ≤ C₂ * (1 + ‖z‖) ^ a := by
    intro z
    set r : ℝ := ‖z‖ + 1 with hr
    have hr0 : 0 < r := by positivity
    set M : ℝ := C * (1 + 2 * r) ^ a + K + 1 with hM
    have hM0 : 0 < M := by
      have : (0 : ℝ) ≤ C * (1 + 2 * r) ^ a := by positivity
      rw [hM]; linarith
    have hmaps : Set.MapsTo g (Metric.ball 0 (2 * r)) {w : ℂ | w.re ≤ M} := by
      intro w hw
      have hwr : ‖w‖ < 2 * r := by simpa using mem_ball_zero_iff.mp hw
      have h1w : (0 : ℝ) ≤ 1 + ‖w‖ := by positivity
      have hmono : (1 + ‖w‖) ^ a ≤ (1 + 2 * r) ^ a :=
        Real.rpow_le_rpow h1w (by linarith) ha0
      have hw' := hre w
      simp only [Set.mem_setOf_eq, hM]
      nlinarith [hmono, hC]
    have hzball : z ∈ Metric.ball (0 : ℂ) (2 * r) := by
      rw [mem_ball_zero_iff, hr]
      linarith [norm_nonneg z]
    have hbc := Complex.borelCaratheodory_zero hM0
      hgdiff.differentiableOn hmaps (by linarith) hzball hg0
    have hposden : 0 < 2 * r - ‖z‖ := by rw [hr]; linarith [norm_nonneg z]
    have hstep : 2 * M * ‖z‖ / (2 * r - ‖z‖) ≤ 2 * M := by
      rw [div_le_iff₀ hposden]
      have hzr : ‖z‖ ≤ 2 * r - ‖z‖ := by rw [hr]; linarith [norm_nonneg z]
      nlinarith [hM0.le, norm_nonneg z]
    have h2r : (1 + 2 * r) ^ a ≤ 3 ^ a * (1 + ‖z‖) ^ a := by
      have hle : (1 : ℝ) + 2 * r ≤ 3 * (1 + ‖z‖) := by rw [hr]; linarith [norm_nonneg z]
      have := Real.rpow_le_rpow (by positivity) hle ha0
      rwa [Real.mul_rpow (by norm_num) (by positivity)] at this
    have hone : (1 : ℝ) ≤ (1 + ‖z‖) ^ a :=
      Real.one_le_rpow (by linarith [norm_nonneg z]) ha0
    have hfinal : 2 * M ≤ C₂ * (1 + ‖z‖) ^ a := by
      rw [hM, hC₂]
      nlinarith [h2r, hone, hC, hK0]
    linarith [hbc, hstep, hfinal]
  have h2 : ∀ c, iteratedDeriv 2 g c = 0 :=
    iteratedDeriv_two_eq_zero_of_growth hgdiff ha0 ha2 hC₂0 hgbound
  refine ⟨deriv g 0, fun z => ?_⟩
  rw [hfg z, eq_affine_of_iteratedDeriv_two_eq_zero hgdiff h2 z, hg0, zero_add]

/-! ### Zero existence from super-linear growth on a ray -/

/-- **Zero existence.**  An entire function with order-one growth whose logarithm grows faster than
any linear function along the positive real axis must vanish somewhere.

If it did not, it would be `f 0 · exp (B z)`, whose logarithm grows exactly linearly along the real
axis with slope `Re B`; the super-linear hypothesis at slope `Re B + |log ‖f 0‖| + 1` then fails. -/
theorem exists_zero_of_superlinear_ray_growth {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {C a : ℝ} (ha0 : 0 ≤ a) (ha2 : a < 2) (hC : 0 ≤ C)
    (hgrow : ∀ z, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ a))
    (hsuper : ∀ A : ℝ, ∃ σ : ℝ, 1 ≤ σ ∧ A * σ < Real.log ‖f (σ : ℂ)‖) :
    ∃ z : ℂ, f z = 0 := by
  by_contra hcon
  have hne : ∀ z, f z ≠ 0 := by
    intro z hz
    exact hcon ⟨z, hz⟩
  obtain ⟨B, hB⟩ := exists_linear_of_ne_zero_of_growth hf hne ha0 ha2 hC hgrow
  have hf0pos : 0 < ‖f 0‖ := norm_pos_iff.mpr (hne 0)
  set L : ℝ := Real.log ‖f 0‖ with hL
  have hlog : ∀ σ : ℝ, Real.log ‖f (σ : ℂ)‖ = L + B.re * σ := by
    intro σ
    have hval : ‖f (σ : ℂ)‖ = ‖f 0‖ * Real.exp (B.re * σ) := by
      rw [hB (σ : ℂ), norm_mul, Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
    rw [hval, Real.log_mul (ne_of_gt hf0pos) (Real.exp_ne_zero _), Real.log_exp, hL]
  obtain ⟨σ, hσ1, hσ⟩ := hsuper (B.re + |L| + 1)
  rw [hlog σ] at hσ
  have hLabs : L ≤ |L| := le_abs_self L
  have hpos : 0 < |L| + 1 := by positivity
  nlinarith [hσ, hσ1, hLabs, hpos]

end GaloisForLFunctions.HTGeometry
