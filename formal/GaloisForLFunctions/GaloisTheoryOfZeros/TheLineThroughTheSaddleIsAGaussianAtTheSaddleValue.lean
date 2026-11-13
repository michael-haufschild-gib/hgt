import GaloisForLFunctions.GaloisTheoryOfZeros.TheSegmentThroughTheOriginIsAGaussianAtTheCentreValue
import GaloisForLFunctions.GaloisTheoryOfZeros.TheGaussianAtTheSaddleOfTheKernel

/-!
# The line through the saddle is a Gaussian at the saddle value

Parametrize the time by its saddle `a`: `P(a) = πe^{2a}`, `τ(a) = P/a`, `f(a) = P(a − 1)`. Then `a`
is the critical point of `x ↦ τx² − πe^{2x}`, and with `ψ(v) = 1 + 2v − e^{2v}`

`τ(a+v)² − πe^{2(a+v)} = f(a) + Pψ(v) + τv²` (`saddle_exponent_eq`).

On the horizontal line through `a`, the leading term `4π²e^{9x/2}e^{−πe^{2x}}` of the kernel gives
the integrand `4π²e^{9a/2 + f(a) + iza} e^{κv + Pψ(v) + τv²}`, `κ = 9/2 + iz`.

* `norm_kernelC_sub_kernelLead_le`: the kernel is its leading term up to a relative `e^{−2 Re x}`
  (lower term of `n = 1`) and the terms `n ≥ 2`.
* `norm_integral_Ioi_stripIntegrand_sub_le`: the part `Re x ≥ Re a − 1` of the line is
  `4π²e^{9a/2+f(a)+iza}(π/(2P − τ))^{1/2}` up to the Laplace error and the remainder of the kernel.
* `norm_integral_left_le`: on `0 ≤ Re x ≤ Re a − 1` the function `Re(τx²)` is a convex quadratic,
  so the integrand is at most its values at the two ends.
* `norm_lineHalf_sub_le` (**saddle term**): the line integral is `S₀(a)e^{iza}` up to
  `leftErr a + e^{Re f(a) − Im(za)} saddleErr a`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real Interval

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The kernel and its leading term -/

theorem natDegree_riemannCuspPoly : riemannCuspPoly.natDegree = 2 :=
  le_antisymm natDegree_riemannCuspPoly_le
    (Polynomial.le_natDegree_of_ne_zero (by rw [coeff_riemannCuspPoly_two]; positivity))

/-- `R(w) − 4π²w²` has degree at most one. -/
theorem norm_aeval_riemannCuspPoly_sub_le (w : ℂ) :
    ‖Polynomial.aeval w riemannCuspPoly - 4 * (π : ℂ) ^ 2 * w ^ 2‖ ≤
      polyAbsBound riemannCuspPoly * (1 + ‖w‖) := by
  have h : Polynomial.aeval w riemannCuspPoly - 4 * (π : ℂ) ^ 2 * w ^ 2 =
      (riemannCuspPoly.coeff 0 : ℂ) + (riemannCuspPoly.coeff 1 : ℂ) * w := by
    rw [Polynomial.aeval_eq_sum_range, natDegree_riemannCuspPoly]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one,
      Complex.real_smul, coeff_riemannCuspPoly_two, mul_one]
    push_cast
    ring
  have hB : |riemannCuspPoly.coeff 0| + |riemannCuspPoly.coeff 1| ≤
      polyAbsBound riemannCuspPoly := by
    unfold polyAbsBound
    rw [natDegree_riemannCuspPoly]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have := abs_nonneg (riemannCuspPoly.coeff 2)
    linarith
  have h0 := abs_nonneg (riemannCuspPoly.coeff 0)
  have h1 := abs_nonneg (riemannCuspPoly.coeff 1)
  have hw := norm_nonneg w
  rw [h]
  calc ‖(riemannCuspPoly.coeff 0 : ℂ) + (riemannCuspPoly.coeff 1 : ℂ) * w‖
      ≤ |riemannCuspPoly.coeff 0| + |riemannCuspPoly.coeff 1| * ‖w‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (|riemannCuspPoly.coeff 0| + |riemannCuspPoly.coeff 1|) * (1 + ‖w‖) := by
        nlinarith [mul_nonneg h0 hw]
    _ ≤ polyAbsBound riemannCuspPoly * (1 + ‖w‖) :=
        mul_le_mul_of_nonneg_right hB (by linarith)

/-- The leading term of the kernel: `4π² e^{9x/2} e^{−πe^{2x}}`. -/
def kernelLead (x : ℂ) : ℂ := 4 * (π : ℂ) ^ 2 * cexp (9 * x / 2) * cexp (-(π * cexp (2 * x)))

/-- The constant of the remainder of the kernel beyond its leading term, at the height `η`. -/
def leadConst (η : ℝ) : ℝ :=
  2 * polyAbsBound riemannCuspPoly + termConst riemannCuspPoly (π * Real.cos (2 * η) / 2)

theorem norm_cexp_neg_pi_mul (x : ℂ) :
    ‖cexp (-(π * cexp (2 * x)))‖ =
      Real.exp (-(π * Real.exp (2 * x.re) * Real.cos (2 * x.im))) := by
  have e : -((π : ℂ) * cexp (2 * x)) = ((-π : ℝ) : ℂ) * cexp (2 * x) := by push_cast; ring
  rw [Complex.norm_exp, e, Complex.re_ofReal_mul, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, add_zero]
  congr 1
  ring

/-- The term `n = 1` of the kernel beyond its leading term. -/
theorem norm_cterm_one_sub_kernelLead_le {x : ℂ} (hre : 0 ≤ x.re) :
    ‖KernelStrip.cterm riemannCuspPoly 1 x - kernelLead x‖ ≤
      2 * polyAbsBound riemannCuspPoly * Real.exp (5 * x.re / 2) *
        ‖cexp (-(π * cexp (2 * x)))‖ := by
  have hB := polyAbsBound_nonneg riemannCuspPoly
  have e9 : cexp (9 * x / 2) = cexp (x / 2) * cexp (2 * x) ^ 2 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have e : KernelStrip.cterm riemannCuspPoly 1 x - kernelLead x =
      cexp (x / 2) * (Polynomial.aeval (cexp (2 * x)) riemannCuspPoly -
        4 * (π : ℂ) ^ 2 * cexp (2 * x) ^ 2) * cexp (-(π * cexp (2 * x))) := by
    rw [KernelStrip.cterm, kernelLead, e9]
    simp only [Nat.cast_one, one_pow, one_mul, neg_mul]
    ring
  have h1 : ‖cexp (x / 2)‖ = Real.exp (x.re / 2) := by rw [Complex.norm_exp]; simp
  have h3 : ‖cexp (2 * x)‖ = Real.exp (2 * x.re) := by rw [Complex.norm_exp]; simp
  have h2 := norm_aeval_riemannCuspPoly_sub_le (cexp (2 * x))
  rw [h3] at h2
  have h4 : Real.exp (x.re / 2) * (1 + Real.exp (2 * x.re)) ≤ 2 * Real.exp (5 * x.re / 2) := by
    have h5 : Real.exp (x.re / 2) * Real.exp (2 * x.re) = Real.exp (5 * x.re / 2) := by
      rw [← Real.exp_add]; ring_nf
    have h6 : Real.exp (x.re / 2) ≤ Real.exp (5 * x.re / 2) := Real.exp_le_exp.mpr (by linarith)
    rw [mul_add, mul_one, h5]
    linarith
  have hE := norm_nonneg (cexp (-(π * cexp (2 * x))))
  rw [e, norm_mul, norm_mul, h1]
  calc Real.exp (x.re / 2) * ‖Polynomial.aeval (cexp (2 * x)) riemannCuspPoly -
          4 * (π : ℂ) ^ 2 * cexp (2 * x) ^ 2‖ * ‖cexp (-(π * cexp (2 * x)))‖
      ≤ Real.exp (x.re / 2) * (polyAbsBound riemannCuspPoly * (1 + Real.exp (2 * x.re))) *
          ‖cexp (-(π * cexp (2 * x)))‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le) hE
    _ = polyAbsBound riemannCuspPoly * (Real.exp (x.re / 2) * (1 + Real.exp (2 * x.re))) *
          ‖cexp (-(π * cexp (2 * x)))‖ := by ring
    _ ≤ polyAbsBound riemannCuspPoly * (2 * Real.exp (5 * x.re / 2)) *
          ‖cexp (-(π * cexp (2 * x)))‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h4 hB) hE
    _ = 2 * polyAbsBound riemannCuspPoly * Real.exp (5 * x.re / 2) *
          ‖cexp (-(π * cexp (2 * x)))‖ := by ring

/-- The terms `n ≥ 2` of the kernel, where `(π/2)cos(2 Im x) e^{2 Re x} ≥ 1`: each is at most
`K e^{Re x/2}|e^{−πe^{2x}}|` times a geometric factor. -/
theorem norm_kernelC_sub_cterm_one_le {x : ℂ} (hcos : 0 < Real.cos (2 * x.im))
    (hbig : 1 ≤ π * Real.cos (2 * x.im) / 2 * Real.exp (2 * x.re)) :
    ‖kernelC x - KernelStrip.cterm riemannCuspPoly 1 x‖ ≤
      termConst riemannCuspPoly (π * Real.cos (2 * x.im) / 2) * Real.exp (x.re / 2) *
        ‖cexp (-(π * cexp (2 * x)))‖ := by
  have hπ := Real.pi_pos
  set a' : ℝ := π * Real.cos (2 * x.im) / 2 with ha'
  have ha0 : 0 < a' := by positivity
  set E : ℝ := a' * Real.exp (2 * x.re) with hE
  have hE0 : 0 < E := by positivity
  set K₀ : ℝ := termConst riemannCuspPoly a' with hK₀
  have hK : 0 ≤ K₀ := termConst_nonneg riemannCuspPoly ha0
  set ρ : ℝ := Real.exp (-E) with hρ
  have hρ0 : 0 ≤ ρ := (Real.exp_pos _).le
  have hρ2 : ρ ≤ 1 / 2 := by
    have h1 : ρ ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (-1) ≤ 1 / 2 := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp 1])
    linarith
  have hρ1 : ρ < 1 := by linarith
  have hnormE : ‖cexp (-(π * cexp (2 * x)))‖ = Real.exp (-(2 * E)) := by
    rw [norm_cexp_neg_pi_mul, hE, ha']
    congr 1
    ring
  -- each term against a geometric sequence
  have hterm : ∀ m : ℕ, ‖KernelStrip.cterm riemannCuspPoly (m + 1 + 1) x‖ ≤
      K₀ * Real.exp (x.re / 2) * Real.exp (-(2 * E)) * (ρ * ρ ^ m) := by
    intro m
    refine (norm_cterm_le riemannCuspPoly (m + 1 + 1) ha0
      (le_of_eq (by rw [ha']; ring))).trans ?_
    have hpow : ρ * ρ ^ m = Real.exp (-(E * ((m : ℝ) + 1))) := by
      rw [← pow_succ', hρ, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hR : K₀ * Real.exp (x.re / 2) * Real.exp (-(2 * E)) * (ρ * ρ ^ m) =
        K₀ * Real.exp (x.re / 2) * Real.exp (-(2 * E) + -(E * ((m : ℝ) + 1))) := by
      rw [hpow, Real.exp_add]
      ring
    rw [hR]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hx : a' * ((((m + 1 + 1 : ℕ) : ℝ)) ^ 2 * Real.exp (2 * x.re)) =
        E * ((m : ℝ) + 2) ^ 2 := by
      rw [hE]
      push_cast
      ring
    rw [hx]
    nlinarith [mul_nonneg hE0.le hm, mul_nonneg hE0.le (mul_nonneg hm hm)]
  have hgeom : Summable fun m : ℕ =>
      K₀ * Real.exp (x.re / 2) * Real.exp (-(2 * E)) * (ρ * ρ ^ m) :=
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left ρ).mul_left _
  have hnorm : Summable fun m : ℕ => ‖KernelStrip.cterm riemannCuspPoly (m + 1 + 1) x‖ :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm hgeom
  have hsum1 : Summable fun n : ℕ => KernelStrip.cterm riemannCuspPoly (n + 1) x :=
    (summable_nat_add_iff (f := fun n : ℕ => KernelStrip.cterm riemannCuspPoly (n + 1) x) 1).mp hnorm.of_norm
  have hsplit : kernelC x - KernelStrip.cterm riemannCuspPoly 1 x =
      ∑' m : ℕ, KernelStrip.cterm riemannCuspPoly (m + 1 + 1) x := by
    rw [kernelC, cseries, hsum1.tsum_eq_zero_add, zero_add, add_sub_cancel_left]
  rw [hsplit, hnormE]
  calc ‖∑' m : ℕ, KernelStrip.cterm riemannCuspPoly (m + 1 + 1) x‖
      ≤ ∑' m : ℕ, ‖KernelStrip.cterm riemannCuspPoly (m + 1 + 1) x‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' m : ℕ, K₀ * Real.exp (x.re / 2) * Real.exp (-(2 * E)) * (ρ * ρ ^ m) :=
        Summable.tsum_le_tsum hterm hnorm hgeom
    _ = K₀ * Real.exp (x.re / 2) * Real.exp (-(2 * E)) * (ρ * (1 - ρ)⁻¹) := by
        rw [tsum_mul_left, tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    _ ≤ K₀ * Real.exp (x.re / 2) * Real.exp (-(2 * E)) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← div_eq_mul_inv, div_le_one (by linarith)]
        linarith
    _ = K₀ * Real.exp (x.re / 2) * Real.exp (-(2 * E)) := mul_one _

/-- **The kernel near its leading term.** For `Re x ≥ 0` and `(π/2)cos(2 Im x)e^{2 Re x} ≥ 1`,
`|Φ(x) − 4π²e^{9x/2}e^{−πe^{2x}}| ≤ C e^{5 Re x/2} |e^{−πe^{2x}}|`. -/
theorem norm_kernelC_sub_kernelLead_le {x : ℂ} (hre : 0 ≤ x.re)
    (hcos : 0 < Real.cos (2 * x.im))
    (hbig : 1 ≤ π * Real.cos (2 * x.im) / 2 * Real.exp (2 * x.re)) :
    ‖kernelC x - kernelLead x‖ ≤
      leadConst x.im * Real.exp (5 * x.re / 2) * ‖cexp (-(π * cexp (2 * x)))‖ := by
  have hπ := Real.pi_pos
  have h1 := norm_cterm_one_sub_kernelLead_le hre
  have h2 := norm_kernelC_sub_cterm_one_le hcos hbig
  have h3 : Real.exp (x.re / 2) ≤ Real.exp (5 * x.re / 2) := Real.exp_le_exp.mpr (by linarith)
  have hK := termConst_nonneg riemannCuspPoly
    (by positivity : 0 < π * Real.cos (2 * x.im) / 2)
  have hE := norm_nonneg (cexp (-(π * cexp (2 * x))))
  calc ‖kernelC x - kernelLead x‖
      = ‖(kernelC x - KernelStrip.cterm riemannCuspPoly 1 x) +
          (KernelStrip.cterm riemannCuspPoly 1 x - kernelLead x)‖ := by congr 1; ring
    _ ≤ ‖kernelC x - KernelStrip.cterm riemannCuspPoly 1 x‖ + ‖KernelStrip.cterm riemannCuspPoly 1 x - kernelLead x‖ :=
        norm_add_le _ _
    _ ≤ termConst riemannCuspPoly (π * Real.cos (2 * x.im) / 2) * Real.exp (x.re / 2) *
          ‖cexp (-(π * cexp (2 * x)))‖ +
        2 * polyAbsBound riemannCuspPoly * Real.exp (5 * x.re / 2) *
          ‖cexp (-(π * cexp (2 * x)))‖ := add_le_add h2 h1
    _ ≤ termConst riemannCuspPoly (π * Real.cos (2 * x.im) / 2) * Real.exp (5 * x.re / 2) *
          ‖cexp (-(π * cexp (2 * x)))‖ +
        2 * polyAbsBound riemannCuspPoly * Real.exp (5 * x.re / 2) *
          ‖cexp (-(π * cexp (2 * x)))‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hK) hE) le_rfl
    _ = leadConst x.im * Real.exp (5 * x.re / 2) * ‖cexp (-(π * cexp (2 * x)))‖ := by
        rw [leadConst]; ring

theorem leadConst_nonneg {η : ℝ} (h0 : 0 ≤ η) (hη : η < π / 4) : 0 ≤ leadConst η := by
  have hπ := Real.pi_pos
  have hκ : 0 < Real.cos (2 * η) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have h1 := termConst_nonneg riemannCuspPoly (by positivity : 0 < π * Real.cos (2 * η) / 2)
  have h2 := polyAbsBound_nonneg riemannCuspPoly
  unfold leadConst
  linarith

/-! ## The saddle parametrization of the time -/

/-- `P(a) = πe^{2a}`. -/
def saddleP (a : ℂ) : ℂ := π * cexp (2 * a)

/-- The time `τ(a) = πe^{2a}/a` whose phase `τx² − πe^{2x}` has the saddle `a`. -/
def saddleTime (a : ℂ) : ℂ := saddleP a / a

/-- The value `f(a) = πe^{2a}(a − 1)` of the phase at its saddle. -/
def saddleValue (a : ℂ) : ℂ := saddleP a * (a - 1)

/-- The amplitude `4π² e^{9a/2 + f(a) + iza}` of the line integral. -/
def saddleAmp (a z : ℂ) : ℂ := 4 * (π : ℂ) ^ 2 * cexp (9 * a / 2 + saddleValue a + I * z * a)

/-- The saddle term `S₀(a) = 4π² e^{9a/2 + f(a)} (π/(2P − τ))^{1/2}`. -/
def saddleTerm (a : ℂ) : ℂ :=
  4 * (π : ℂ) ^ 2 * cexp (9 * a / 2 + saddleValue a) *
    ((π : ℂ) / (2 * saddleP a - saddleTime a)) ^ (1 / 2 : ℂ)

theorem saddleP_re (a : ℂ) :
    (saddleP a).re = π * Real.exp (2 * a.re) * Real.cos (2 * a.im) := by
  rw [saddleP, Complex.re_ofReal_mul, Complex.exp_re]
  simp only [Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, add_zero]
  ring

theorem saddleP_im (a : ℂ) :
    (saddleP a).im = π * Real.exp (2 * a.re) * Real.sin (2 * a.im) := by
  rw [saddleP, Complex.im_ofReal_mul, Complex.exp_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero, add_zero]
  ring

theorem norm_saddleP (a : ℂ) : ‖saddleP a‖ = π * Real.exp (2 * a.re) := by
  rw [saddleP, norm_mul, Complex.norm_real, Complex.norm_exp, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]

theorem saddleTime_mul {a : ℂ} (ha : a ≠ 0) : saddleTime a * a = saddleP a :=
  div_mul_cancel₀ _ ha

/-- **The phase at its saddle.** `τ(a+v)² + iz(a+v) − πe^{2(a+v)} = f(a) + iza + izv + Pψ(v) + τv²`. -/
theorem saddle_exponent_eq {a : ℂ} (ha : a ≠ 0) (z : ℂ) (v : ℝ) :
    saddleTime a * (a + v) ^ 2 + I * z * (a + v) - π * cexp (2 * (a + v)) =
      (saddleValue a + I * z * a) +
        (I * z * v + saddleP a * ((saddlePhase v : ℝ) : ℂ) + saddleTime a * (v : ℂ) ^ 2) := by
  have h := saddleTime_mul ha
  have he : cexp (2 * (a + v)) = cexp (2 * a) * cexp (2 * v) := by rw [mul_add, Complex.exp_add]
  have hψ : ((saddlePhase v : ℝ) : ℂ) = 1 + 2 * v - cexp (2 * v) := by simp [saddlePhase]
  rw [he, hψ, saddleValue]
  rw [saddleP] at h ⊢
  linear_combination (a + 2 * v) * h

/-- `τ(a − 1)² = f(a) − P + τ`: the value of the phase one unit to the left of the saddle. -/
theorem saddleTime_mul_sub_one_sq {a : ℂ} (ha : a ≠ 0) :
    saddleTime a * (a - 1) ^ 2 = saddleValue a - saddleP a + saddleTime a := by
  have h := saddleTime_mul ha
  rw [saddleValue]
  linear_combination (a - 2) * h

theorem norm_saddleAmp (a z : ℂ) :
    ‖saddleAmp a z‖ =
      4 * π ^ 2 * Real.exp (9 * a.re / 2 + ((saddleValue a).re - (z * a).im)) := by
  have h1 : ‖(4 : ℂ) * (π : ℂ) ^ 2‖ = 4 * π ^ 2 := by
    rw [show (4 : ℂ) * (π : ℂ) ^ 2 = ((4 * π ^ 2 : ℝ) : ℂ) by simp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h2 : (9 * a / 2 + saddleValue a + I * z * a).re =
      9 * a.re / 2 + ((saddleValue a).re - (z * a).im) := by
    have h3 : (9 * a / 2).re = 9 * a.re / 2 := by simp
    rw [mul_assoc I z a, Complex.add_re, Complex.add_re, Complex.I_mul_re, h3]
    ring
  rw [saddleAmp, norm_mul, h1, Complex.norm_exp, h2]

/-- The leading term of the kernel on the line through the saddle. -/
theorem kernelLead_mul_cexp_eq {a : ℂ} (ha : a ≠ 0) (z : ℂ) (v : ℝ) :
    kernelLead (a + v) * cexp (saddleTime a * (a + v) ^ 2 + I * z * (a + v)) =
      saddleAmp a z * saddleIntegrand (saddleP a) (saddleTime a) (9 / 2 + I * z) v := by
  have h := saddle_exponent_eq ha z v
  have e : 9 * (a + v) / 2 + -(π * cexp (2 * (a + v))) +
        (saddleTime a * (a + v) ^ 2 + I * z * (a + v)) =
      (9 * a / 2 + saddleValue a + I * z * a) +
        ((9 / 2 + I * z) * v + saddleP a * ((saddlePhase v : ℝ) : ℂ) +
          saddleTime a * (v : ℂ) ^ 2) := by
    linear_combination h
  calc kernelLead (a + v) * cexp (saddleTime a * (a + v) ^ 2 + I * z * (a + v))
      = 4 * (π : ℂ) ^ 2 * cexp (9 * (a + v) / 2 + -(π * cexp (2 * (a + v))) +
          (saddleTime a * (a + v) ^ 2 + I * z * (a + v))) := by
        rw [kernelLead, Complex.exp_add (9 * (a + v) / 2 + -(π * cexp (2 * (a + v)))) _,
          Complex.exp_add (9 * (a + v) / 2) _]
        ring
    _ = 4 * (π : ℂ) ^ 2 * cexp ((9 * a / 2 + saddleValue a + I * z * a) +
          ((9 / 2 + I * z) * v + saddleP a * ((saddlePhase v : ℝ) : ℂ) +
            saddleTime a * (v : ℂ) ^ 2)) := by rw [e]
    _ = saddleAmp a z * saddleIntegrand (saddleP a) (saddleTime a) (9 / 2 + I * z) v := by
        rw [saddleAmp, saddleIntegrand, Complex.exp_add (9 * a / 2 + saddleValue a + I * z * a) _]
        ring

/-! ## The part of the line at the saddle -/

/-- Translation of a half line. -/
theorem setIntegral_Ioi_comp_sub (G : ℝ → ℂ) (c σ : ℝ) :
    ∫ s in Ioi (c + σ), G (s - σ) = ∫ v in Ioi c, G v := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_sub_right_eq_self (fun v => (Ioi c).indicator G v) σ]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  have hiff : s - σ ∈ Ioi c ↔ s ∈ Ioi (c + σ) := by
    simp only [mem_Ioi]
    constructor <;> intro h <;> linarith
  simp only [Set.indicator_apply, hiff]

/-- The error of the line integral at the saddle, relative to `e^{Re f(a) − Im(za)}`: the Laplace
error of the leading term and the remainder of the kernel. -/
def saddleErr (a : ℂ) : ℝ :=
  4 * π ^ 2 * Real.exp (9 * a.re / 2) *
      (64 * Real.exp 4 * (1 + ‖saddleP a‖ / (saddleP a).re) / (saddleP a).re) +
    leadConst a.im * Real.exp (5 * a.re / 2) *
      (Real.exp 4 * (4 * (1 / Real.sqrt (saddleP a).re)))

/-- **The line at the saddle.** With `P = P(a)`, `τ = τ(a)`: if `Re a ≥ 1`, `0 ≤ Im a < π/4`,
`Re P ≥ 18`, `8 Re τ ≤ Re P` and `|z| ≤ 1`, the part `Re x ≥ Re a − 1` of the line integral is
`4π²e^{9a/2+f(a)+iza}(π/(2P−τ))^{1/2}` up to `e^{Re f(a) − Im(za)} saddleErr a`. -/
theorem norm_integral_Ioi_stripIntegrand_sub_le {a z : ℂ} (ha1 : 1 ≤ a.re) (hη0 : 0 ≤ a.im)
    (hη : a.im < π / 4) (hp : 18 ≤ (saddleP a).re)
    (hτ : 8 * (saddleTime a).re ≤ (saddleP a).re) (hz : ‖z‖ ≤ 1) :
    ‖(∫ s in Ioi (a.re - 1), stripIntegrand (saddleTime a) z (s + a.im * I)) -
        saddleAmp a z * ((π : ℂ) / (2 * saddleP a - saddleTime a)) ^ (1 / 2 : ℂ)‖ ≤
      Real.exp ((saddleValue a).re - (z * a).im) * saddleErr a := by
  have hπ := Real.pi_pos
  have ha : a ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at ha1
    linarith
  have hp0 : 0 < (saddleP a).re := by linarith
  have hcos : 0 < Real.cos (2 * a.im) := Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hpe : (saddleP a).re = π * Real.exp (2 * a.re) * Real.cos (2 * a.im) := saddleP_re a
  have hC1 : 0 ≤ leadConst a.im := leadConst_nonneg hη0 hη
  have hκ : ‖(9 / 2 : ℂ) + I * z‖ ≤ 6 := by
    have h1 : ‖(9 / 2 : ℂ)‖ = 9 / 2 := by
      rw [show (9 / 2 : ℂ) = ((9 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by norm_num)]
    have h2 : ‖I * z‖ = ‖z‖ := by rw [norm_mul, Complex.norm_I, one_mul]
    calc ‖(9 / 2 : ℂ) + I * z‖ ≤ ‖(9 / 2 : ℂ)‖ + ‖I * z‖ := norm_add_le _ _
      _ ≤ 6 := by rw [h1, h2]; linarith
  -- translation to the saddle
  have htrans : ∫ s in Ioi (a.re - 1), stripIntegrand (saddleTime a) z (s + a.im * I) =
      ∫ v in Ioi (-1 : ℝ), stripIntegrand (saddleTime a) z (a + v) := by
    rw [← setIntegral_Ioi_comp_sub (fun v : ℝ => stripIntegrand (saddleTime a) z (a + v)) (-1) a.re,
      show (-1 : ℝ) + a.re = a.re - 1 by ring]
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    have hx : (s : ℂ) + a.im * I = a + ((s - a.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    simp only [hx]
  -- the remainder of the kernel
  set rest : ℝ → ℂ := fun v => (kernelC (a + v) - kernelLead (a + v)) *
    cexp (saddleTime a * (a + v) ^ 2 + I * z * (a + v)) with hrest
  have hFv : ∀ v : ℝ, stripIntegrand (saddleTime a) z (a + v) =
      saddleAmp a z * saddleIntegrand (saddleP a) (saddleTime a) (9 / 2 + I * z) v + rest v := by
    intro v
    rw [← kernelLead_mul_cexp_eq ha z v, stripIntegrand]
    simp only [hrest]
    ring
  set D : ℝ := leadConst a.im *
    Real.exp (5 * a.re / 2 + ((saddleValue a).re - (z * a).im) + 4) with hD
  have hD0 : 0 ≤ D := by positivity
  have hrestle : ∀ v ∈ Ioi (-1 : ℝ),
      ‖rest v‖ ≤ D * Real.exp (-((saddleP a).re / 4) * v ^ 2) := by
    intro v hv
    have hv1 : -1 ≤ v := le_of_lt hv
    have hxre : (a + (v : ℂ)).re = a.re + v := by simp
    have hxim : (a + (v : ℂ)).im = a.im := by simp
    have hbig : 1 ≤ π * Real.cos (2 * (a + (v : ℂ)).im) / 2 *
        Real.exp (2 * (a + (v : ℂ)).re) := by
      rw [hxim, hxre]
      have he : Real.exp (2 * (a.re + v)) = Real.exp (2 * a.re) * Real.exp (2 * v) := by
        rw [← Real.exp_add]; ring_nf
      have h9 : (1 : ℝ) / 9 ≤ Real.exp (2 * v) := by
        have h2 : Real.exp (-2) ≤ Real.exp (2 * v) := Real.exp_le_exp.mpr (by linarith)
        have h3 : (1 : ℝ) / 9 ≤ Real.exp (-2) := by
          rw [Real.exp_neg, one_div]
          refine inv_anti₀ (Real.exp_pos 2) ?_
          have h4 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
            rw [← Real.exp_add]; norm_num
          have h5 := Real.exp_one_lt_d9
          have h6 := Real.exp_pos 1
          rw [h4]
          nlinarith
        linarith
      have h7 : π * Real.cos (2 * a.im) / 2 * (Real.exp (2 * a.re) * Real.exp (2 * v)) =
          (saddleP a).re / 2 * Real.exp (2 * v) := by rw [hpe]; ring
      rw [he, h7]
      nlinarith [mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr h9)]
    have h1 := norm_kernelC_sub_kernelLead_le (x := a + v) (by rw [hxre]; linarith)
      (by rw [hxim]; exact hcos) hbig
    rw [hxim, hxre] at h1
    -- the modulus of the phase
    have hnorm_prod : ‖cexp (-(π * cexp (2 * (a + v))))‖ *
        ‖cexp (saddleTime a * (a + v) ^ 2 + I * z * (a + v))‖ =
        Real.exp ((saddleValue a).re - (z * a).im +
          (I * z * v + saddleP a * ((saddlePhase v : ℝ) : ℂ) +
            saddleTime a * (v : ℂ) ^ 2).re) := by
      have h := saddle_exponent_eq ha z v
      have e : -(π * cexp (2 * (a + v))) + (saddleTime a * (a + v) ^ 2 + I * z * (a + v)) =
          (saddleValue a + I * z * a) + (I * z * v + saddleP a * ((saddlePhase v : ℝ) : ℂ) +
            saddleTime a * (v : ℂ) ^ 2) := by linear_combination h
      rw [← norm_mul, ← Complex.exp_add, Complex.norm_exp, e, Complex.add_re,
        Complex.add_re (saddleValue a), mul_assoc I z a, Complex.I_mul_re]
      congr 1
    have hB : (I * z * v + saddleP a * ((saddlePhase v : ℝ) : ℂ) +
        saddleTime a * (v : ℂ) ^ 2).re ≤ |v| - 7 / 8 * (saddleP a).re * v ^ 2 := by
      have h2 := re_saddle_exponent_le hp0.le hτ hv1
      have h3 : (I * z * (v : ℂ)).re ≤ |v| := by
        have h4 : (z * (v : ℂ)).im = z.im * v := by simp
        rw [mul_assoc, Complex.I_mul_re, h4]
        have h5 : |z.im * v| ≤ 1 * |v| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm z).trans hz) (abs_nonneg v)
        have h6 := neg_abs_le (z.im * v)
        linarith
      rw [add_assoc, Complex.add_re]
      linarith
    have h6v : 6 * |v| ≤ (saddleP a).re / 8 * v ^ 2 + 4 := by
      nlinarith [sq_nonneg (3 * |v| / 2 - 2), sq_abs v,
        mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg v)]
    have hvabs : v ≤ |v| := le_abs_self v
    have hprod : leadConst a.im * Real.exp (5 * (a.re + v) / 2) *
          ‖cexp (-(π * cexp (2 * (a + v))))‖ *
          ‖cexp (saddleTime a * (a + v) ^ 2 + I * z * (a + v))‖ =
        leadConst a.im * (Real.exp (5 * (a.re + v) / 2) *
          (‖cexp (-(π * cexp (2 * (a + v))))‖ *
            ‖cexp (saddleTime a * (a + v) ^ 2 + I * z * (a + v))‖)) := by ring
    calc ‖rest v‖
        = ‖kernelC (a + v) - kernelLead (a + v)‖ *
            ‖cexp (saddleTime a * (a + v) ^ 2 + I * z * (a + v))‖ := by
          simp only [hrest]
          rw [norm_mul]
      _ ≤ leadConst a.im * Real.exp (5 * (a.re + v) / 2) *
            ‖cexp (-(π * cexp (2 * (a + v))))‖ *
            ‖cexp (saddleTime a * (a + v) ^ 2 + I * z * (a + v))‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = leadConst a.im * Real.exp (5 * (a.re + v) / 2 + ((saddleValue a).re - (z * a).im +
            (I * z * v + saddleP a * ((saddlePhase v : ℝ) : ℂ) +
              saddleTime a * (v : ℂ) ^ 2).re)) := by
          rw [hprod, hnorm_prod, ← Real.exp_add]
      _ ≤ leadConst a.im * Real.exp (5 * a.re / 2 + ((saddleValue a).re - (z * a).im) + 4 +
            -((saddleP a).re / 4) * v ^ 2) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC1
          nlinarith [mul_nonneg hp0.le (sq_nonneg v)]
      _ = D * Real.exp (-((saddleP a).re / 4) * v ^ 2) := by
          rw [hD, Real.exp_add]
          ring
  -- integrability
  have hgi : Integrable fun v : ℝ => Real.exp (-((saddleP a).re / 4) * v ^ 2) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hkc : Continuous fun v : ℝ => kernelC (a + v) := by
    refine continuous_iff_continuousAt.2 fun v => ?_
    have him : (a + (v : ℂ)).im = a.im := by simp
    have hd : DifferentiableAt ℂ kernelC (a + v) :=
      differentiableAt_kernelC (by rw [him, abs_of_nonneg hη0]; exact hη)
    exact hd.continuousAt.comp (f := fun v : ℝ => a + (v : ℂ)) (by fun_prop)
  have hrc : Continuous rest := by
    have h1 : Continuous fun v : ℝ => kernelLead (a + v) := by unfold kernelLead; fun_prop
    simp only [hrest]
    exact (hkc.sub h1).mul (by fun_prop)
  have hrest_int : IntegrableOn rest (Ioi (-1 : ℝ)) :=
    Integrable.mono' (hgi.const_mul D).integrableOn hrc.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hrestle))
  have hsplit : ∫ v in Ioi (-1 : ℝ), stripIntegrand (saddleTime a) z (a + v) =
      saddleAmp a z *
          (∫ v in Ioi (-1 : ℝ), saddleIntegrand (saddleP a) (saddleTime a) (9 / 2 + I * z) v) +
        ∫ v in Ioi (-1 : ℝ), rest v := by
    have h1 := integral_add
      ((integrableOn_saddleIntegrand hp hτ hκ).const_mul (saddleAmp a z)) hrest_int
    rw [integral_const_mul] at h1
    rw [← h1]
    exact setIntegral_congr_fun measurableSet_Ioi fun v _ => hFv v
  have hlap := norm_integral_saddleIntegrand_sub_le hp hτ hκ
  have hrest_norm : ‖∫ v in Ioi (-1 : ℝ), rest v‖ ≤
      D * (4 * (1 / Real.sqrt (saddleP a).re)) := by
    have h1 : ‖∫ v in Ioi (-1 : ℝ), rest v‖ ≤
        ∫ v in Ioi (-1 : ℝ), D * Real.exp (-((saddleP a).re / 4) * v ^ 2) :=
      norm_integral_le_of_norm_le (hgi.const_mul D).integrableOn
        ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hrestle))
    have h2 : (∫ v in Ioi (-1 : ℝ), D * Real.exp (-((saddleP a).re / 4) * v ^ 2)) ≤
        D * ∫ v : ℝ, Real.exp (-((saddleP a).re / 4) * v ^ 2) := by
      rw [← integral_const_mul]
      exact setIntegral_le_integral (hgi.const_mul D)
        (Eventually.of_forall fun v => mul_nonneg hD0 (Real.exp_pos _).le)
    exact h1.trans (h2.trans
      (mul_le_mul_of_nonneg_left (integral_exp_neg_quarter_mul_sq_le hp0) hD0))
  have e1 : Real.exp (9 * a.re / 2 + ((saddleValue a).re - (z * a).im)) =
      Real.exp (9 * a.re / 2) * Real.exp ((saddleValue a).re - (z * a).im) := Real.exp_add _ _
  have e2 : Real.exp (5 * a.re / 2 + ((saddleValue a).re - (z * a).im) + 4) =
      Real.exp (5 * a.re / 2) * Real.exp ((saddleValue a).re - (z * a).im) * Real.exp 4 := by
    rw [Real.exp_add, Real.exp_add]
  rw [htrans, hsplit]
  calc ‖saddleAmp a z *
          (∫ v in Ioi (-1 : ℝ), saddleIntegrand (saddleP a) (saddleTime a) (9 / 2 + I * z) v) +
        (∫ v in Ioi (-1 : ℝ), rest v) -
        saddleAmp a z * ((π : ℂ) / (2 * saddleP a - saddleTime a)) ^ (1 / 2 : ℂ)‖
      = ‖saddleAmp a z *
          ((∫ v in Ioi (-1 : ℝ), saddleIntegrand (saddleP a) (saddleTime a) (9 / 2 + I * z) v) -
            ((π : ℂ) / (2 * saddleP a - saddleTime a)) ^ (1 / 2 : ℂ)) +
          ∫ v in Ioi (-1 : ℝ), rest v‖ := by congr 1; ring
    _ ≤ ‖saddleAmp a z‖ *
          ‖(∫ v in Ioi (-1 : ℝ), saddleIntegrand (saddleP a) (saddleTime a) (9 / 2 + I * z) v) -
            ((π : ℂ) / (2 * saddleP a - saddleTime a)) ^ (1 / 2 : ℂ)‖ +
          ‖∫ v in Ioi (-1 : ℝ), rest v‖ := by
        refine (norm_add_le _ _).trans (le_of_eq ?_)
        rw [norm_mul]
    _ ≤ ‖saddleAmp a z‖ *
          (64 * Real.exp 4 * (1 + ‖saddleP a‖ / (saddleP a).re) / (saddleP a).re) +
          D * (4 * (1 / Real.sqrt (saddleP a).re)) :=
        add_le_add (mul_le_mul_of_nonneg_left hlap (norm_nonneg _)) hrest_norm
    _ = Real.exp ((saddleValue a).re - (z * a).im) * saddleErr a := by
        rw [norm_saddleAmp, hD, e1, e2, saddleErr]
        ring

/-! ## The part of the line to the left of the saddle -/

theorem re_mul_line_sq (τ : ℂ) (s η : ℝ) :
    (τ * ((s : ℂ) + η * I) ^ 2).re = τ.re * (s ^ 2 - η ^ 2) - 2 * τ.im * s * η := by
  have h : ((s : ℂ) + η * I) ^ 2 = ((s ^ 2 - η ^ 2 : ℝ) : ℂ) + ((2 * s * η : ℝ) : ℂ) * I := by
    push_cast
    linear_combination (η : ℂ) ^ 2 * Complex.I_sq
  rw [h, Complex.mul_re]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero,
    zero_add]
  ring

/-- A convex quadratic without constant term is at most its values at the ends. -/
theorem line_quadratic_le_max {A B : ℝ} (hA : 0 ≤ A) {s s₁ : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ s₁) :
    A * s ^ 2 + B * s ≤ max 0 (A * s₁ ^ 2 + B * s₁) := by
  rcases le_total (A * s + B) 0 with h | h
  · refine le_max_of_le_left ?_
    nlinarith [mul_nonneg hs0 (neg_nonneg.mpr h)]
  · refine le_max_of_le_right ?_
    have h1 : A * s + B ≤ A * s₁ + B := by nlinarith [mul_le_mul_of_nonneg_left hs hA]
    nlinarith [mul_le_mul hs h1 h (hs0.trans hs)]

/-- The error of the line integral to the left of the saddle: the larger of the two ends, the
origin (`e^{−(Im a)² Re τ}`) and the point one unit before the saddle (`e^{Re f − Re P + Re τ}`). -/
def leftErr (a : ℂ) : ℝ :=
  a.re * (stripConst a.im * Real.exp (a.re / 2) * Real.exp 8 *
    (Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
      Real.exp ((saddleValue a).re - (saddleP a).re + (saddleTime a).re)))

/-- **The line to the left of the saddle.** -/
theorem norm_integral_left_le {a z : ℂ} (ha1 : 1 ≤ a.re) (hη0 : 0 ≤ a.im) (hη : a.im < π / 4)
    (hτ : 0 ≤ (saddleTime a).re) (hz : ‖z‖ * a.re ≤ 8) :
    ‖∫ s in (0 : ℝ)..(a.re - 1), stripIntegrand (saddleTime a) z (s + a.im * I)‖ ≤
      leftErr a := by
  have hπ := Real.pi_lt_d2
  have ha : a ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at ha1
    linarith
  have hK := stripConst_nonneg hη0 hη
  have hline : ∀ r : ℝ, (saddleTime a * ((r : ℂ) + a.im * I) ^ 2).re =
      (saddleTime a).re * r ^ 2 + -(2 * (saddleTime a).im * a.im) * r -
        a.im ^ 2 * (saddleTime a).re := by
    intro r
    rw [re_mul_line_sq]
    ring
  have ha1' : (((a.re - 1 : ℝ)) : ℂ) + a.im * I = a - 1 := by
    apply Complex.ext <;> simp
  have hend : (saddleTime a).re * (a.re - 1) ^ 2 + -(2 * (saddleTime a).im * a.im) * (a.re - 1) -
      a.im ^ 2 * (saddleTime a).re =
        (saddleValue a).re - (saddleP a).re + (saddleTime a).re := by
    rw [← hline (a.re - 1), ha1', saddleTime_mul_sub_one_sq ha]
    simp only [Complex.add_re, Complex.sub_re]
  set C : ℝ := stripConst a.im * Real.exp (a.re / 2) * Real.exp 8 *
    (Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
      Real.exp ((saddleValue a).re - (saddleP a).re + (saddleTime a).re)) with hC
  have hC0 : 0 ≤ C := by positivity
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) (a.re - 1),
      ‖stripIntegrand (saddleTime a) z (s + a.im * I)‖ ≤ C := by
    intro s hs
    rw [uIoc_of_le (by linarith)] at hs
    obtain ⟨hs0, hs1⟩ := hs
    have hre : ((s : ℂ) + a.im * I).re = s := by simp
    have him : ((s : ℂ) + a.im * I).im = a.im := by simp
    have hk := norm_kernelC_le_stripConst hη (x := s + a.im * I)
      (by rw [him, abs_of_nonneg hη0]) (by rw [hre]; exact hs0.le)
    rw [hre] at hk
    -- the Gaussian factor: a convex quadratic in `s`
    have hq := line_quadratic_le_max hτ (B := -(2 * (saddleTime a).im * a.im)) hs0.le hs1
    have hQ : (saddleTime a * ((s : ℂ) + a.im * I) ^ 2).re ≤
        max (-(a.im ^ 2 * (saddleTime a).re))
          ((saddleValue a).re - (saddleP a).re + (saddleTime a).re) := by
      rw [hline s, ← hend]
      rcases le_max_iff.mp hq with h | h
      · exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right (by linarith)
    -- the oscillating factor
    have hosc : (I * z * ((s : ℂ) + a.im * I)).re ≤ 8 := by
      rw [mul_assoc, Complex.I_mul_re]
      have h1 : -(z * ((s : ℂ) + a.im * I)).im ≤ ‖z * ((s : ℂ) + a.im * I)‖ :=
        (neg_le_abs _).trans (Complex.abs_im_le_norm _)
      have h2 : ‖(s : ℂ) + a.im * I‖ ≤ a.re := by
        refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
        rw [hre, him, abs_of_pos hs0, abs_of_nonneg hη0]
        linarith
      rw [norm_mul] at h1
      have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg z)
      linarith
    have hexp : Real.exp ((saddleTime a * ((s : ℂ) + a.im * I) ^ 2).re +
        (I * z * ((s : ℂ) + a.im * I)).re) ≤
        Real.exp 8 * (Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
          Real.exp ((saddleValue a).re - (saddleP a).re + (saddleTime a).re)) := by
      have h1 := Real.exp_le_exp.mpr hQ
      have h2 : Real.exp (max (-(a.im ^ 2 * (saddleTime a).re))
            ((saddleValue a).re - (saddleP a).re + (saddleTime a).re)) ≤
          Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
            Real.exp ((saddleValue a).re - (saddleP a).re + (saddleTime a).re) := by
        have p1 := Real.exp_pos (-(a.im ^ 2 * (saddleTime a).re))
        have p2 := Real.exp_pos ((saddleValue a).re - (saddleP a).re + (saddleTime a).re)
        rcases max_cases (-(a.im ^ 2 * (saddleTime a).re))
          ((saddleValue a).re - (saddleP a).re + (saddleTime a).re) with ⟨h, _⟩ | ⟨h, _⟩ <;>
          rw [h] <;> linarith
      rw [Real.exp_add, mul_comm]
      exact mul_le_mul (Real.exp_le_exp.mpr hosc) (h1.trans h2) (Real.exp_pos _).le
        (Real.exp_pos _).le
    rw [stripIntegrand, norm_mul, Complex.norm_exp, Complex.add_re]
    calc ‖kernelC ((s : ℂ) + a.im * I)‖ *
          Real.exp ((saddleTime a * ((s : ℂ) + a.im * I) ^ 2).re +
            (I * z * ((s : ℂ) + a.im * I)).re)
        ≤ (stripConst a.im * Real.exp (s / 2)) *
            (Real.exp 8 * (Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
              Real.exp ((saddleValue a).re - (saddleP a).re + (saddleTime a).re))) :=
          mul_le_mul hk hexp (Real.exp_pos _).le (by positivity)
      _ ≤ (stripConst a.im * Real.exp (a.re / 2)) *
            (Real.exp 8 * (Real.exp (-(a.im ^ 2 * (saddleTime a).re)) +
              Real.exp ((saddleValue a).re - (saddleP a).re + (saddleTime a).re))) := by
          have h5 : Real.exp (s / 2) ≤ Real.exp (a.re / 2) := Real.exp_le_exp.mpr (by linarith)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 hK) (by positivity)
      _ = C := by rw [hC]; ring
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  refine h.trans ?_
  rw [sub_zero, abs_of_nonneg (by linarith), leftErr]
  nlinarith

/-! ## The saddle term -/

/-- **The saddle term.** For `Re a ≥ 1`, `0 ≤ Im a < π/4`, `Re P ≥ 18`, `0 ≤ 8 Re τ ≤ Re P`,
`|z| ≤ 1` and `|z| Re a ≤ 8`, the line integral through the saddle is `S₀(a)e^{iza}` up to
`leftErr a + e^{Re f(a) − Im(za)} saddleErr a`. -/
theorem norm_lineHalf_sub_le {a z : ℂ} (ha1 : 1 ≤ a.re) (hη0 : 0 ≤ a.im) (hη : a.im < π / 4)
    (hp : 18 ≤ (saddleP a).re) (hτ0 : 0 ≤ (saddleTime a).re)
    (hτ : 8 * (saddleTime a).re ≤ (saddleP a).re) (hz : ‖z‖ ≤ 1) (hza : ‖z‖ * a.re ≤ 8) :
    ‖lineHalf (saddleTime a) a.im z - saddleTerm a * cexp (I * z * a)‖ ≤
      leftErr a + Real.exp ((saddleValue a).re - (z * a).im) * saddleErr a := by
  have hint := integrableOn_stripIntegrand_line (saddleTime a) z hη0 hη
  have hint1 : IntegrableOn (fun s : ℝ => stripIntegrand (saddleTime a) z (s + a.im * I))
      (Ioi (a.re - 1)) := hint.mono_set (Ioi_subset_Ioi (by linarith))
  have hsplit := intervalIntegral.integral_interval_add_Ioi hint hint1
  have hS : saddleTerm a * cexp (I * z * a) =
      saddleAmp a z * ((π : ℂ) / (2 * saddleP a - saddleTime a)) ^ (1 / 2 : ℂ) := by
    rw [saddleTerm, saddleAmp, Complex.exp_add (9 * a / 2 + saddleValue a) _]
    ring
  have h1 := norm_integral_left_le ha1 hη0 hη hτ0 hza
  have h2 := norm_integral_Ioi_stripIntegrand_sub_le ha1 hη0 hη hp hτ hz
  rw [lineHalf, ← hsplit, hS]
  calc ‖(∫ s in (0 : ℝ)..(a.re - 1), stripIntegrand (saddleTime a) z (s + a.im * I)) +
          (∫ s in Ioi (a.re - 1), stripIntegrand (saddleTime a) z (s + a.im * I)) -
          saddleAmp a z * ((π : ℂ) / (2 * saddleP a - saddleTime a)) ^ (1 / 2 : ℂ)‖
      = ‖(∫ s in (0 : ℝ)..(a.re - 1), stripIntegrand (saddleTime a) z (s + a.im * I)) +
          ((∫ s in Ioi (a.re - 1), stripIntegrand (saddleTime a) z (s + a.im * I)) -
            saddleAmp a z * ((π : ℂ) / (2 * saddleP a - saddleTime a)) ^ (1 / 2 : ℂ))‖ := by
        congr 1; ring
    _ ≤ leftErr a + Real.exp ((saddleValue a).re - (z * a).im) * saddleErr a :=
        (norm_add_le _ _).trans (add_le_add h1 h2)

end

end GaloisForLFunctions.GaloisTheoryOfZeros
