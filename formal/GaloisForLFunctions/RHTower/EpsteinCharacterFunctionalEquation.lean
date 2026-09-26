import GaloisForLFunctions.RHTower.HalfWeightTwistedThetaInversion
import GaloisForLFunctions.RHTower.GL3TernaryTheta
import GaloisForLFunctions.RHTower.SelbergPoincareSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.LSeries.AbstractFuncEq

/-!
# The Epstein zeta function with a Dirichlet character and its functional equation

For `z ∈ ℍ`, `A > 0` and a weight `w : ℤ² → ℂ` with `|w| ≤ 1`, let
`Θ_w(t) = Σ_{(m,n)} w(m,n) exp(-π t |mAz + n|²/y)` (`thetaW`). The form satisfies
`|mAz + n|² ≥ (δ/2) n² + (A²y²/2) m²` with `δ = y²/(2x² + y²)` (`qfA_ge`). This gives absolute convergence,
continuity on `(0, ∞)`, exponential decay when `w` vanishes where the form is small
(`thetaW_isBigO`), and the Mellin transform
`∫₀^∞ t^{s-1} Θ_w(t) dt = (π/y)^{-s} Γ(s) Σ w(m,n) |mAz + n|^{-2s}` for `Re s > 1` (`mellin_thetaW`).

For `ψ ≠ 1` mod a prime `q`, Poisson summation in each residue class (`char_poisson`), and then in
the other variable, gives the theta inversion (`thetaQ_inversion`)
`Σ_{m,n} ψ(n) e^{-πt|mqBz+n|²/y} = τ(ψ)/(t q² B) · Σ_{k,l} ψ̄(k) e^{-π|kBz+l|²/(t q²B² y)}`.
Both sides vanish at `∞` (`ψ(0) = 0`), so they form a strong Mellin FE-pair of weight `1` and root
number `τ(ψ)/(q²B)` (`epsFEPair`). Hence the completed function
`Λ(s) = (π/y)^{-s} Γ(s) Σ_{(m,n)} ψ(n) |mqBz + n|^{-2s}`   (`epsΛ_eq`, `Re s > 1`)
is **entire** (`differentiable_epsΛ`) and satisfies the **functional equation**
`Λ(1 - s) = τ(ψ)/(q²B) · (q²B²)^s (π/y)^{-s} Γ(s) Σ_{(k,l)} ψ̄(k) |kBz + l|^{-2s}`
(`epstein_char_functional_equation`).

This is the Eisenstein series of `Γ₀(q²B)` at `∞` with nebentypus `ψ` (times `L(2s, ψ)`), and its
partner, where the character acts on the lower-left entry. It is the weight-0 input to the
twisted Rankin–Selberg functional equation.
-/

open Complex Real Filter Asymptotics Set MeasureTheory

namespace GaloisForLFunctions.RHTower.EpsteinCharacter

open GaloisForLFunctions.RHTower.HalfWeight

noncomputable section


/-! ### The binary quadratic form `|mAz + n|²` -/

/-- `Q_A(z; m, n) = (mAx + n)² + (mAy)² = |mAz + n|²`. -/
def qfA (A : ℝ) (z : UpperHalfPlane) (p : ℤ × ℤ) : ℝ :=
  ((p.1 : ℝ) * A * z.re + p.2) ^ 2 + ((p.1 : ℝ) * A * z.im) ^ 2

/-- The constant `δ = y²/(2x² + y²)`. -/
def delA (z : UpperHalfPlane) : ℝ := z.im ^ 2 / (2 * z.re ^ 2 + z.im ^ 2)

theorem delA_pos (z : UpperHalfPlane) : 0 < delA z := by
  have := z.im_pos; unfold delA; positivity

theorem delA_le_one (z : UpperHalfPlane) : delA z ≤ 1 := by
  have := z.im_pos
  unfold delA
  rw [div_le_one (by positivity)]
  nlinarith [sq_nonneg z.re]

/-- **Positive definiteness**: `Q_A(m,n) ≥ (δ/2) n² + (A²y²/2) m²`. -/
theorem qfA_ge (A : ℝ) (z : UpperHalfPlane) (p : ℤ × ℤ) :
    delA z / 2 * (p.2 : ℝ) ^ 2 + A ^ 2 * z.im ^ 2 / 2 * (p.1 : ℝ) ^ 2 ≤ qfA A z p := by
  have hy := z.im_pos
  have hd := delA_pos z
  have hd1 := delA_le_one z
  set x := z.re; set y := z.im
  set m : ℝ := (p.1 : ℝ); set n : ℝ := (p.2 : ℝ)
  have hδ : delA z * x ^ 2 ≤ y ^ 2 / 2 := by
    unfold delA
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg (x * y)]
  unfold qfA
  have h1 : (m * A * x + n) ^ 2 ≥ delA z * (m * A * x + n) ^ 2 := by
    nlinarith [sq_nonneg (m * A * x + n)]
  have h2 : delA z * (m * A * x + n) ^ 2 ≥ delA z * (n ^ 2 / 2 - (m * A * x) ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hd.le
    nlinarith [sq_nonneg (n + 2 * (m * A * x))]
  have h3 : delA z * (m * A * x) ^ 2 ≤ (m * A) ^ 2 * (y ^ 2 / 2) := by
    rw [show delA z * (m * A * x) ^ 2 = (m * A) ^ 2 * (delA z * x ^ 2) by ring]
    exact mul_le_mul_of_nonneg_left hδ (sq_nonneg _)
  nlinarith

theorem qfA_nonneg (A : ℝ) (z : UpperHalfPlane) (p : ℤ × ℤ) : 0 ≤ qfA A z p := by
  unfold qfA; positivity

/-! ### Theta functions of the lattice `ℤ Az + ℤ` with a bounded weight -/

section Weighted

variable (w : ℤ × ℤ → ℂ) (A : ℝ) (z : UpperHalfPlane)

/-- `Θ_w(t) = Σ_{(m,n)} w(m,n) exp(-π t |mAz + n|²/y)`. -/
def thetaW (t : ℝ) : ℂ := ∑' p : ℤ × ℤ, w p * ((Real.exp (-π * t * qfA A z p / z.im) : ℝ) : ℂ)

theorem exp_qfA_le {t : ℝ} (ht : 0 ≤ t) (p : ℤ × ℤ) :
    Real.exp (-π * t * qfA A z p / z.im) ≤
      Real.exp (-π * (t * A ^ 2 * z.im / 2) * ((p.1 : ℝ) + 0) ^ 2) *
        Real.exp (-π * (t * delA z / (2 * z.im)) * ((p.2 : ℝ) + 0) ^ 2) := by
  have hy := z.im_pos
  rw [← Real.exp_add, Real.exp_le_exp]
  have h := qfA_ge A z p
  have hpi := Real.pi_pos
  have key : π * t / z.im * (delA z / 2 * (p.2 : ℝ) ^ 2 + A ^ 2 * z.im ^ 2 / 2 * (p.1 : ℝ) ^ 2) ≤
      π * t / z.im * qfA A z p := mul_le_mul_of_nonneg_left h (by positivity)
  have e1 : -π * t * qfA A z p / z.im = -(π * t / z.im * qfA A z p) := by ring
  have e2 : -π * (t * A ^ 2 * z.im / 2) * ((p.1 : ℝ) + 0) ^ 2 +
      -π * (t * delA z / (2 * z.im)) * ((p.2 : ℝ) + 0) ^ 2 =
      -(π * t / z.im * (delA z / 2 * (p.2 : ℝ) ^ 2 + A ^ 2 * z.im ^ 2 / 2 * (p.1 : ℝ) ^ 2)) := by
    field_simp; ring
  rw [e1, e2]
  linarith

theorem summable_exp_qfA {t : ℝ} (ht : 0 < t) (hA : A ≠ 0) :
    Summable fun p : ℤ × ℤ => Real.exp (-π * t * qfA A z p / z.im) := by
  have hy := z.im_pos
  have hd := delA_pos z
  have h1 := GL3.summable_realGauss (by positivity : 0 < t * A ^ 2 * z.im / 2) 0
  have h2 := GL3.summable_realGauss (by positivity : 0 < t * delA z / (2 * z.im)) 0
  refine Summable.of_nonneg_of_le (fun p => (Real.exp_pos _).le) (exp_qfA_le A z ht.le)
    (h1.mul_of_nonneg h2 (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))

variable {w}

theorem summable_thetaW_terms (hw : ∀ p, ‖w p‖ ≤ 1) {t : ℝ} (ht : 0 < t) (hA : A ≠ 0) :
    Summable fun p : ℤ × ℤ => w p * ((Real.exp (-π * t * qfA A z p / z.im) : ℝ) : ℂ) := by
  refine Summable.of_norm_bounded (summable_exp_qfA A z ht hA) fun p => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (hw p)

theorem continuousOn_thetaW (hw : ∀ p, ‖w p‖ ≤ 1) (hA : A ≠ 0) :
    ContinuousOn (thetaW w A z) (Ioi 0) := by
  intro t0 ht0
  have ht0' : 0 < t0 / 2 := by have := ht0.out; linarith
  have hs : ContinuousOn (thetaW w A z) (Ioi (t0 / 2)) := by
    refine continuousOn_tsum (u := fun p => Real.exp (-π * (t0 / 2) * qfA A z p / z.im))
      (fun p => by fun_prop) (summable_exp_qfA A z ht0' hA) fun p t ht => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine (mul_le_of_le_one_left (Real.exp_pos _).le (hw p)).trans ?_
    rw [Real.exp_le_exp]
    have hq := qfA_nonneg A z p
    have hy := z.im_pos
    have h3 : t0 / 2 ≤ t := (mem_Ioi.1 ht).le
    have : π * (t0 / 2) * qfA A z p / z.im ≤ π * t * qfA A z p / z.im := by
      apply div_le_div_of_nonneg_right _ hy.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 Real.pi_pos.le) hq
    have e1 : -π * (t0 / 2) * qfA A z p / z.im = -(π * (t0 / 2) * qfA A z p / z.im) := by ring
    have e2 : -π * t * qfA A z p / z.im = -(π * t * qfA A z p / z.im) := by ring
    rw [e1, e2]
    linarith
  exact (hs.continuousAt (Ioi_mem_nhds (by linarith [ht0.out] : t0 / 2 < t0))).continuousWithinAt

/-- **Exponential decay** when the weight vanishes near the origin of the form. -/
theorem norm_thetaW_le (hw : ∀ p, ‖w p‖ ≤ 1) (hA : A ≠ 0) {c₀ : ℝ}
    (hsupp : ∀ p, w p ≠ 0 → c₀ ≤ qfA A z p) {t : ℝ} (ht : 1 ≤ t) :
    ‖thetaW w A z t‖ ≤ Real.exp (-(π * c₀ / z.im) * (t - 1)) *
      ∑' p : ℤ × ℤ, Real.exp (-π * 1 * qfA A z p / z.im) := by
  have ht0 : 0 < t := by linarith
  have hy := z.im_pos
  have hsR := summable_exp_qfA A z one_pos hA
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact (summable_thetaW_terms A z hw ht0 hA).norm
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun p => ?_) (summable_thetaW_terms A z hw ht0 hA).norm
    (hsR.mul_left _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  by_cases hp : w p = 0
  · rw [hp, norm_zero, zero_mul]; positivity
  have hq := hsupp p hp
  have hq0 := qfA_nonneg A z p
  refine (mul_le_of_le_one_left (Real.exp_pos _).le (hw p)).trans ?_
  rw [← Real.exp_add, Real.exp_le_exp]
  have hpi := Real.pi_pos
  have h1 : π * c₀ / z.im * (t - 1) ≤ π * (t - 1) * qfA A z p / z.im := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hy]
    nlinarith [mul_nonneg hpi.le (sub_nonneg.2 ht)]
  have e : -π * t * qfA A z p / z.im = -(π * (t - 1) * qfA A z p / z.im) - π * qfA A z p / z.im := by
    ring
  rw [e]
  have e2 : -(π * c₀ / z.im) * (t - 1) + -π * 1 * qfA A z p / z.im =
      -(π * c₀ / z.im * (t - 1)) - π * qfA A z p / z.im := by ring
  rw [e2]
  linarith

theorem thetaW_isBigO (hw : ∀ p, ‖w p‖ ≤ 1) (hA : A ≠ 0) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hsupp : ∀ p, w p ≠ 0 → c₀ ≤ qfA A z p) (r : ℝ) :
    (fun t => thetaW w A z t - 0) =O[atTop] (· ^ r) := by
  have hy := z.im_pos
  set c := π * c₀ / z.im
  have hc : 0 < c := by positivity
  set S := ∑' p : ℤ × ℤ, Real.exp (-π * 1 * qfA A z p / z.im)
  have h1 : (fun t => thetaW w A z t - 0) =O[atTop] fun t => Real.exp (-c * t) := by
    refine IsBigO.of_bound (Real.exp c * S) ?_
    filter_upwards [eventually_ge_atTop 1] with t ht
    rw [sub_zero]
    refine (norm_thetaW_le A z hw hA hsupp ht).trans (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), show -c * (t - 1) = c + -c * t by ring,
      Real.exp_add]
    ring
  exact h1.trans (isLittleO_exp_neg_mul_rpow_atTop hc r).isBigO

/-! ### The Mellin transform -/

theorem qfA_eq_norm (p : ℤ × ℤ) :
    qfA A z p = ‖(p.1 : ℂ) * ((A : ℂ) * z) + p.2‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  unfold qfA
  simp
  ring

theorem summable_qfA_rpow (hA : 0 < A) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun p : ℤ × ℤ => qfA A z p ^ (-σ) := by
  set z' : UpperHalfPlane := ⟨(A : ℂ) * z, by simp [hA, z.im_pos]⟩
  have h := SelbergPoincare.summable_norm_rpow z' hσ
  have h' := (finTwoArrowEquiv ℤ).symm.summable_iff.2 h
  refine h'.congr fun p => ?_
  simp only [Function.comp_apply, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [qfA_eq_norm, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  push_cast; ring

theorem integrable_gammaKernel {σ r : ℝ} (hσ : 0 < σ) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := σ - 1) (p := 1) (by linarith) le_rfl hr
  refine this.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp [Real.rpow_one]

/-- The weighted Epstein zeta function `Σ_{(m,n)} w(m,n) |mAz + n|^{-2s}`. -/
def epsW (s : ℂ) : ℂ := ∑' p : ℤ × ℤ, w p * ((qfA A z p : ℝ) : ℂ) ^ (-s)

/-- The Mellin summand. -/
def mellinTermW (s : ℂ) (p : ℤ × ℤ) (t : ℝ) : ℂ :=
  w p * ((t : ℂ) ^ (s - 1) * cexp (-((π * qfA A z p / z.im : ℝ) : ℂ) * t))

theorem integral_mellinTermW {s : ℂ} (hs : 0 < s.re) {p : ℤ × ℤ} (hq : 0 < qfA A z p) :
    ∫ t in Ioi 0, mellinTermW (w := w) A z s p t =
      w p * ((1 / ((π * qfA A z p / z.im : ℝ) : ℂ)) ^ s * Complex.Gamma s) := by
  have hy := z.im_pos
  unfold mellinTermW
  rw [integral_const_mul]
  congr 1
  have := Complex.integral_cpow_mul_exp_neg_mul_Ioi hs (by positivity : 0 < π * qfA A z p / z.im)
  refine (setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_).trans this
  congr 2
  ring

theorem norm_mellinTermW (s : ℂ) (p : ℤ × ℤ) {t : ℝ} (ht : 0 < t) :
    ‖mellinTermW (w := w) A z s p t‖ =
      ‖w p‖ * (t ^ (s.re - 1) * Real.exp (-((π * qfA A z p / z.im) * t))) := by
  simp only [mellinTermW, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  rw [show -((π * qfA A z p / z.im : ℝ) : ℂ) * t = ((-((π * qfA A z p / z.im) * t) : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_exp_ofReal]
  simp

theorem continuousOn_mellinTermW (s : ℂ) (p : ℤ × ℤ) :
    ContinuousOn (mellinTermW (w := w) A z s p) (Ioi 0) := by
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  unfold mellinTermW
  exact continuousAt_const.mul
    ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (mem_Ioi.1 ht).ne')).mul (by fun_prop))

theorem integrable_mellinTermW {s : ℂ} (hs : 0 < s.re) (hsupp : ∀ p, w p ≠ 0 → 0 < qfA A z p)
    (p : ℤ × ℤ) : IntegrableOn (mellinTermW (w := w) A z s p) (Ioi 0) := by
  by_cases hp : w p = 0
  · have e : mellinTermW (w := w) A z s p = fun _ => 0 := by funext t; simp [mellinTermW, hp]
    rw [e]; exact integrableOn_zero
  have hq := hsupp p hp
  have hy := z.im_pos
  have hint := (integrable_gammaKernel hs (by positivity : 0 < π * qfA A z p / z.im)).const_mul ‖w p‖
  refine Integrable.mono' hint
    ((continuousOn_mellinTermW A z s p).aestronglyMeasurable measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht => ?_)
  rw [norm_mellinTermW A z s p ht]

theorem integral_norm_mellinTermW {s : ℂ} (hs : 0 < s.re) (hsupp : ∀ p, w p ≠ 0 → 0 < qfA A z p)
    (p : ℤ × ℤ) :
    ∫ t in Ioi 0, ‖mellinTermW (w := w) A z s p t‖ =
      if w p = 0 then 0 else ‖w p‖ * ((1 / (π * qfA A z p / z.im)) ^ s.re * Real.Gamma s.re) := by
  by_cases hp : w p = 0
  · simp [mellinTermW, hp]
  have hq := hsupp p hp
  have hy := z.im_pos
  simp only [hp, if_false]
  rw [← Real.integral_rpow_mul_exp_neg_mul_Ioi hs (by positivity : 0 < π * qfA A z p / z.im),
    ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht => norm_mellinTermW A z s p ht

/-- **Mellin transform of the weighted theta series**: for `Re s > 1`,
`∫₀^∞ t^{s-1} Θ_w(t) dt = (π/y)^{-s} Γ(s) Σ w(m,n) |mAz + n|^{-2s}`. -/
theorem mellin_thetaW (hw : ∀ p, ‖w p‖ ≤ 1) (hA : 0 < A) (hsupp : ∀ p, w p ≠ 0 → 0 < qfA A z p)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (thetaW w A z) s = ((π / z.im : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * epsW (w := w) A z s := by
  have hs0 : 0 < s.re := by linarith
  have hy := z.im_pos
  have hsumR := summable_qfA_rpow A z hA hs
  have hint : ∀ t ∈ Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) • thetaW w A z t =
      ∑' p : ℤ × ℤ, mellinTermW (w := w) A z s p t := by
    intro t ht
    rw [thetaW, smul_eq_mul, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    simp only [mellinTermW]
    rw [Complex.ofReal_exp]
    push_cast
    ring_nf
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi hint,
    ← integral_tsum_of_summable_integral_norm (fun p => integrable_mellinTermW A z hs0 hsupp p)]
  · rw [epsW, ← tsum_mul_left]
    refine tsum_congr fun p => ?_
    by_cases hp : w p = 0
    · simp [mellinTermW, hp]
    have hq := hsupp p hp
    rw [integral_mellinTermW A z hs0 hq]
    have e : (1 / ((π * qfA A z p / z.im : ℝ) : ℂ)) ^ s =
        ((π / z.im : ℝ) : ℂ) ^ (-s) * ((qfA A z p : ℝ) : ℂ) ^ (-s) := by
      have hx : (((π * qfA A z p / z.im : ℝ)) : ℂ).arg ≠ π := by
        rw [Complex.arg_ofReal_of_nonneg (by positivity)]; exact Real.pi_pos.ne
      rw [one_div, Complex.inv_cpow _ _ hx,
        show ((π * qfA A z p / z.im : ℝ) : ℂ) = ((π / z.im : ℝ) : ℂ) * ((qfA A z p : ℝ) : ℂ) by
          push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg (by positivity) hq.le, Complex.cpow_neg, Complex.cpow_neg,
        mul_inv]
    rw [e]; ring
  · simp only [integral_norm_mellinTermW A z hs0 hsupp]
    refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
      (hsumR.mul_left ((π / z.im) ^ (-s.re) * Real.Gamma s.re))
    · split_ifs
      · exact le_rfl
      · have hq0 := qfA_nonneg A z p
        exact mul_nonneg (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (Real.Gamma_pos_of_pos hs0).le)
    · by_cases hp : w p = 0
      · simp only [hp, if_true]
        exact mul_nonneg (mul_nonneg (by positivity) (Real.Gamma_pos_of_pos hs0).le)
          (Real.rpow_nonneg (qfA_nonneg A z p) _)
      have hq := hsupp p hp
      simp only [hp, if_false]
      have hG := (Real.Gamma_pos_of_pos hs0).le
      have e : (1 / (π * qfA A z p / z.im)) ^ s.re =
          (π / z.im) ^ (-s.re) * qfA A z p ^ (-s.re) := by
        rw [one_div, Real.inv_rpow (by positivity), show π * qfA A z p / z.im = (π / z.im) * qfA A z p by ring,
          Real.mul_rpow (by positivity) hq.le, Real.rpow_neg (by positivity), Real.rpow_neg hq.le, mul_inv]
      rw [e]
      have h1 := hw p
      have h2 : 0 ≤ (π / z.im) ^ (-s.re) * qfA A z p ^ (-s.re) * Real.Gamma s.re :=
        mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg hq.le _)) hG
      nlinarith

end Weighted


section Character


variable {q : ℕ} [hq : Fact q.Prime] (ψ : DirichletCharacter ℂ q)

/-- **Poisson summation for a character-weighted shifted Gaussian**: for `ψ ≠ 1` mod a prime `q`,
`Σ_n ψ(n) e^{-πd(n+a)²} = τ(ψ)/(q√d) Σ_k ψ̄(k) e^{-πk²/(q²d)} e(ak/q)`. -/
theorem char_poisson (hψ : ψ ≠ 1) {d : ℝ} (hd : 0 < d) (a : ℝ) :
    ∑' n : ℤ, ψ (n : ZMod q) * cexp (-π * d * ((n : ℂ) + a) ^ 2) =
      gaussSum ψ ZMod.stdAddChar / (q * Real.sqrt d) *
        ∑' k : ℤ, ψ⁻¹ (k : ZMod q) * cexp (-π * (k : ℂ) ^ 2 / (q ^ 2 * d) + 2 * π * I * a * k / q) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hdq : 0 < d * (q : ℝ) ^ 2 := by positivity
  have hsum : Summable fun n : ℤ => ψ (n : ZMod q) * cexp (-π * d * ((n : ℂ) + a) ^ 2) := by
    refine Summable.of_norm_bounded (summable_norm_iff.2 (GL3.summable_gauss hd a 0)) fun n => ?_
    rw [norm_mul, GL3.norm_gauss]
    have h1 := DirichletCharacter.norm_le_one ψ (n : ZMod q)
    have h2 : ‖cexp (-π * d * ((n : ℂ) + a) ^ 2)‖ = Real.exp (-π * d * (n + a) ^ 2) := by
      rw [show -π * (d : ℂ) * ((n : ℂ) + a) ^ 2 = ((-π * d * (n + a) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_exp_ofReal]
    rw [h2]
    exact mul_le_of_le_one_left (Real.exp_pos _).le h1
  rw [tsum_int_split_residue (q := q) hsum]
  -- each residue class
  have hclass : ∀ r : Fin q, ∑' m : ℤ, ψ (((m * q + ((r : ℕ) : ℤ) : ℤ)) : ZMod q) *
      cexp (-π * d * ((((m * q + ((r : ℕ) : ℤ) : ℤ)) : ℂ) + a) ^ 2) =
      ψ ((r : ℕ) : ZMod q) * (1 / (Real.sqrt (d * q ^ 2) : ℂ) *
        ∑' k : ℤ, cexp (-π * ((k : ℂ) - ((0 : ℝ) : ℂ)) ^ 2 / ((d * q ^ 2 : ℝ) : ℂ) +
          2 * π * I * ((((r : ℕ) + a) / q : ℝ) : ℂ) * ((k : ℂ) - ((0 : ℝ) : ℂ)))) := by
    intro r
    have hψr : ∀ m : ℤ, ψ (((m * q + ((r : ℕ) : ℤ) : ℤ)) : ZMod q) = ψ ((r : ℕ) : ZMod q) := by
      intro m; congr 1; push_cast; rw [ZMod.natCast_self]; ring
    have hexp : ∀ m : ℤ, cexp (-π * d * ((((m * q + ((r : ℕ) : ℤ) : ℤ)) : ℂ) + a) ^ 2) =
        cexp (-π * ((d * q ^ 2 : ℝ) : ℂ) * ((m : ℂ) + ((((r : ℕ) + a) / q : ℝ) : ℂ)) ^ 2 +
          2 * π * I * ((0 : ℝ) : ℂ) * m) := by
      intro m
      congr 1
      push_cast
      field_simp
      ring
    simp_rw [hψr, hexp]
    rw [tsum_mul_left, GL3.poisson1 hdq]
  simp_rw [hclass]
  set E : ℤ → ℂ := fun k => cexp (-π * (k : ℂ) ^ 2 / (q ^ 2 * d) + 2 * π * I * a * k / q) with hE
  have hsplit : ∀ (r : Fin q) (k : ℤ),
      cexp (-π * ((k : ℂ) - ((0 : ℝ) : ℂ)) ^ 2 / ((d * q ^ 2 : ℝ) : ℂ) +
        2 * π * I * ((((r : ℕ) + a) / q : ℝ) : ℂ) * ((k : ℂ) - ((0 : ℝ) : ℂ))) =
      cexp (2 * π * I * ((r : ℕ) : ℂ) * k / q) * E k := by
    intro r k
    simp only [hE]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    field_simp
    ring
  simp_rw [hsplit]
  have hEs : Summable E := by
    have hd' : 0 < 1 / (q ^ 2 * d) := by positivity
    refine (GL3.summable_gauss hd' 0 (a / q)).congr fun k => ?_
    simp only [hE]
    congr 1
    push_cast
    field_simp
    ring
  have hsd : ∀ r : Fin q, Summable fun k : ℤ =>
      ψ ((r : ℕ) : ZMod q) * (1 / (Real.sqrt (d * q ^ 2) : ℂ) *
        (cexp (2 * π * I * ((r : ℕ) : ℂ) * k / q) * E k)) := by
    intro r
    refine ((hEs.norm.mul_left (‖ψ ((r : ℕ) : ZMod q)‖ * ‖(1 / (Real.sqrt (d * q ^ 2) : ℂ))‖))).of_norm_bounded
      fun k => ?_
    rw [norm_mul, norm_mul, norm_mul, norm_cexp_rat_phase]
    apply le_of_eq; ring
  have e1 : ∀ r : Fin q, ψ ((r : ℕ) : ZMod q) * (1 / (Real.sqrt (d * q ^ 2) : ℂ) *
      ∑' k : ℤ, cexp (2 * π * I * ((r : ℕ) : ℂ) * k / q) * E k) =
      ∑' k : ℤ, ψ ((r : ℕ) : ZMod q) * (1 / (Real.sqrt (d * q ^ 2) : ℂ) *
        (cexp (2 * π * I * ((r : ℕ) : ℂ) * k / q) * E k)) := by
    intro r; rw [tsum_mul_left, tsum_mul_left]
  simp_rw [e1]
  rw [← Summable.tsum_finsetSum (fun r _ => hsd r), ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hg := sum_char_cexp ψ hψ k
  have hsq : Real.sqrt (d * q ^ 2) = q * Real.sqrt d := by
    rw [Real.sqrt_mul hd.le, Real.sqrt_sq (Nat.cast_nonneg q), mul_comm]
  calc ∑ r : Fin q, ψ ((r : ℕ) : ZMod q) * (1 / (Real.sqrt (d * q ^ 2) : ℂ) *
        (cexp (2 * π * I * ((r : ℕ) : ℂ) * k / q) * E k))
      = 1 / (Real.sqrt (d * q ^ 2) : ℂ) * E k *
          ∑ r : Fin q, ψ ((r : ℕ) : ZMod q) * cexp (2 * π * I * ((r : ℕ) : ℂ) * k / q) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun r _ => by ring
    _ = _ := by
        rw [hg, hsq]
        push_cast
        ring

/-! ### The two theta functions of the lattice `ℤ Bz + ℤ` -/

/-- `Θ(t) = Σ_{m,n} ψ(n) exp(-π t |mqBz + n|²/y)`, as an iterated sum. -/
def thetaQ (B : ℕ) (z : UpperHalfPlane) (t : ℝ) : ℂ :=
  ∑' m : ℤ, ∑' n : ℤ, ψ (n : ZMod q) *
    cexp (-π * ((t / z.im : ℝ) : ℂ) * ((((m * q * B : ℤ) : ℝ) * z.re + n : ℝ) ^ 2 +
      (((m * q * B : ℤ) : ℝ) * z.im) ^ 2 : ℝ))

/-- `Θ̂(t) = Σ_{k,l} ψ̄(k) exp(-π t |kBz + l|²/y)`, as an iterated sum. -/
def thetaD (B : ℕ) (z : UpperHalfPlane) (t : ℝ) : ℂ :=
  ∑' k : ℤ, ∑' l : ℤ, ψ⁻¹ (k : ZMod q) *
    cexp (-π * ((t / z.im : ℝ) : ℂ) * ((((k * B : ℤ) : ℝ) * z.re + l : ℝ) ^ 2 +
      (((k * B : ℤ) : ℝ) * z.im) ^ 2 : ℝ))

/-- The inner sum of `Θ` by `char_poisson`. -/
theorem thetaQ_inner (hψ : ψ ≠ 1) (B : ℕ) (z : UpperHalfPlane) {t : ℝ} (ht : 0 < t) (m : ℤ) :
    ∑' n : ℤ, ψ (n : ZMod q) *
      cexp (-π * ((t / z.im : ℝ) : ℂ) * ((((m * q * B : ℤ) : ℝ) * z.re + n : ℝ) ^ 2 +
        (((m * q * B : ℤ) : ℝ) * z.im) ^ 2 : ℝ)) =
      gaussSum ψ ZMod.stdAddChar / (q * Real.sqrt (t / z.im)) *
        ∑' k : ℤ, ψ⁻¹ (k : ZMod q) * cexp (-π * ((t * q ^ 2 * B ^ 2 * z.im : ℝ) : ℂ) * (m : ℂ) ^ 2 -
          π * (k : ℂ) ^ 2 / (q ^ 2 * ((t / z.im : ℝ) : ℂ)) + 2 * π * I * (B * z.re * k : ℝ) * m) := by
  have hy := z.im_pos
  have hd : 0 < t / z.im := div_pos ht hy
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hyC : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have htC : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hsplit : ∀ n : ℤ, ψ (n : ZMod q) *
      cexp (-π * ((t / z.im : ℝ) : ℂ) * ((((m * q * B : ℤ) : ℝ) * z.re + n : ℝ) ^ 2 +
        (((m * q * B : ℤ) : ℝ) * z.im) ^ 2 : ℝ)) =
      cexp (-π * ((t * q ^ 2 * B ^ 2 * z.im : ℝ) : ℂ) * (m : ℂ) ^ 2) *
        (ψ (n : ZMod q) * cexp (-π * (t / z.im : ℝ) * ((n : ℂ) + (((m * q * B : ℤ) : ℝ) * z.re : ℝ)) ^ 2)) := by
    intro n
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  simp_rw [hsplit]
  rw [tsum_mul_left, char_poisson ψ hψ hd, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [mul_left_comm (cexp _), mul_left_comm (cexp _), ← Complex.exp_add]
  congr 3
  push_cast
  field_simp
  ring

/-- **Theta inversion for the lattice `ℤ qBz + ℤ` with a character**:
`Θ(t) = τ(ψ)/(t q² B) · Θ̂(1/(t q² B²))`. -/
theorem thetaQ_inversion (hψ : ψ ≠ 1) {B : ℕ} (hB : 0 < B) (z : UpperHalfPlane) {t : ℝ} (ht : 0 < t) :
    thetaQ ψ B z t = gaussSum ψ ZMod.stdAddChar / (t * q ^ 2 * B) *
      thetaD ψ B z (1 / (t * q ^ 2 * B ^ 2)) := by
  have hy := z.im_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.out.pos
  have hB0 : (0 : ℝ) < B := by exact_mod_cast hB
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hBC : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hyC : ((z.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have htC : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  set D : ℝ := t * q ^ 2 * B ^ 2 * z.im with hD
  have hDp : 0 < D := by positivity
  unfold thetaQ
  simp_rw [thetaQ_inner ψ hψ B z ht]
  rw [tsum_mul_left]
  set F : ℤ → ℤ → ℂ := fun m k => ψ⁻¹ (k : ZMod q) * cexp (-π * ((D : ℝ) : ℂ) * (m : ℂ) ^ 2 -
      π * (k : ℂ) ^ 2 / (q ^ 2 * ((t / z.im : ℝ) : ℂ)) + 2 * π * I * (B * z.re * k : ℝ) * m) with hF
  have hbound : ∀ m k, ‖F m k‖ ≤ Real.exp (-π * D * ((m : ℝ) + 0) ^ 2) *
      Real.exp (-π * (z.im / (q ^ 2 * t)) * ((k : ℝ) + 0) ^ 2) := by
    intro m k
    simp only [hF]
    have hsplitE : -π * ((D : ℝ) : ℂ) * (m : ℂ) ^ 2 - π * (k : ℂ) ^ 2 / (q ^ 2 * ((t / z.im : ℝ) : ℂ)) +
        2 * π * I * (B * z.re * k : ℝ) * m =
        ((-π * D * ((m : ℝ) + 0) ^ 2 + -π * (z.im / (q ^ 2 * t)) * ((k : ℝ) + 0) ^ 2 : ℝ) : ℂ) +
          ((2 * π * (B * z.re * k) * m : ℝ) : ℂ) * I := by
      push_cast; field_simp; ring
    rw [hsplitE, Complex.exp_add, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
      Complex.norm_exp_ofReal, Real.exp_add]
    have h1 := DirichletCharacter.norm_le_one ψ⁻¹ (k : ZMod q)
    exact mul_le_of_le_one_left (by positivity) h1
  have hA : Summable fun m : ℤ => Real.exp (-π * D * ((m : ℝ) + 0) ^ 2) := GL3.summable_realGauss hDp 0
  have hBs : Summable fun k : ℤ => Real.exp (-π * (z.im / (q ^ 2 * t)) * ((k : ℝ) + 0) ^ 2) :=
    GL3.summable_realGauss (by positivity) 0
  rw [GL3.tsum_comm_of_le hA hBs (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le) hbound]
  -- the `m`-sum by Poisson
  have hm : ∀ k : ℤ, ∑' m : ℤ, F m k = ψ⁻¹ (k : ZMod q) *
      cexp (-π * (k : ℂ) ^ 2 / (q ^ 2 * ((t / z.im : ℝ) : ℂ))) *
      (1 / (Real.sqrt D : ℂ) * ∑' l : ℤ, cexp (-π * ((l : ℂ) - ((B * z.re * k : ℝ) : ℂ)) ^ 2 / (D : ℂ) +
        2 * π * I * ((0 : ℝ) : ℂ) * ((l : ℂ) - ((B * z.re * k : ℝ) : ℂ)))) := by
    intro k
    rw [← GL3.poisson1 hDp 0 (B * z.re * k), ← tsum_mul_left]
    refine tsum_congr fun m => ?_
    simp only [hF]
    rw [mul_assoc (ψ⁻¹ (k : ZMod q)) (cexp _) (cexp _), ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hm]
  unfold thetaD
  conv_lhs => rw [← tsum_mul_left]
  conv_rhs => rw [← tsum_mul_left]
  refine tsum_congr fun k => ?_
  conv_rhs => rw [← (Equiv.neg ℤ).tsum_eq]
  set E : ℤ → ℂ := fun l => cexp (-π * ((l : ℂ) - ((B * z.re * k : ℝ) : ℂ)) ^ 2 / (D : ℂ) +
    2 * π * I * ((0 : ℝ) : ℂ) * ((l : ℂ) - ((B * z.re * k : ℝ) : ℂ))) with hE
  have hL : gaussSum ψ ZMod.stdAddChar / (q * Real.sqrt (t / z.im)) *
      (ψ⁻¹ (k : ZMod q) * cexp (-π * (k : ℂ) ^ 2 / (q ^ 2 * ((t / z.im : ℝ) : ℂ))) *
        (1 / (Real.sqrt D : ℂ) * ∑' l : ℤ, E l)) =
      ∑' l : ℤ, gaussSum ψ ZMod.stdAddChar / (q * Real.sqrt (t / z.im)) *
        (ψ⁻¹ (k : ZMod q) * cexp (-π * (k : ℂ) ^ 2 / (q ^ 2 * ((t / z.im : ℝ) : ℂ))) *
          (1 / (Real.sqrt D : ℂ) * E l)) := by
    rw [tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rw [hL, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  simp only [Equiv.neg_apply, hE]
  have hsq : Real.sqrt (t / z.im) * Real.sqrt D = t * q * B := by
    rw [← Real.sqrt_mul (by positivity), hD]
    rw [show t / z.im * (t * q ^ 2 * B ^ 2 * z.im) = (t * q * B) ^ 2 by field_simp]
    exact Real.sqrt_sq (by positivity)
  have hsqC : (Real.sqrt (t / z.im) : ℂ) * (Real.sqrt D : ℂ) = t * q * B := by
    exact_mod_cast hsq
  have hsd : (Real.sqrt (t / z.im) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 (div_pos ht hy)).ne'
  have hsD : (Real.sqrt D : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hDp).ne'
  have hexp : -π * (k : ℂ) ^ 2 / (q ^ 2 * ((t / z.im : ℝ) : ℂ)) +
      (-π * ((l : ℂ) - ((B * z.re * k : ℝ) : ℂ)) ^ 2 / (D : ℂ) +
        2 * π * I * ((0 : ℝ) : ℂ) * ((l : ℂ) - ((B * z.re * k : ℝ) : ℂ))) =
      -π * (((1 / (t * q ^ 2 * B ^ 2)) / z.im : ℝ) : ℂ) *
        ((((k * B : ℤ) : ℝ) * z.re + ((-l : ℤ) : ℝ) : ℝ) ^ 2 + (((k * B : ℤ) : ℝ) * z.im) ^ 2 : ℝ) := by
    rw [hD]; push_cast; field_simp; ring
  rw [← hexp]
  conv_rhs => rw [Complex.exp_add]
  have hC : gaussSum ψ ZMod.stdAddChar / (q * Real.sqrt (t / z.im)) * (1 / (Real.sqrt D : ℂ)) =
      gaussSum ψ ZMod.stdAddChar / ((t : ℂ) * q ^ 2 * B) := by
    rw [div_mul_div_comm, mul_one, mul_assoc, hsqC]
    ring
  rw [← hC]
  ring


/-! ### The functional-equation pair -/

/-- The weight `ψ(n)` of `Θ`. -/
def wQ (p : ℤ × ℤ) : ℂ := ψ (p.2 : ZMod q)

/-- The weight `ψ̄(k)` of `Θ̂`. -/
def wD (p : ℤ × ℤ) : ℂ := ψ⁻¹ (p.1 : ZMod q)

theorem norm_wQ_le (p : ℤ × ℤ) : ‖wQ ψ p‖ ≤ 1 := DirichletCharacter.norm_le_one _ _

theorem norm_wD_le (p : ℤ × ℤ) : ‖wD ψ p‖ ≤ 1 := DirichletCharacter.norm_le_one _ _

theorem ne_zero_of_char_ne_zero {χ : DirichletCharacter ℂ q} {n : ℤ} (h : χ (n : ZMod q) ≠ 0) :
    n ≠ 0 := by
  rintro rfl
  apply h
  simp only [Int.cast_zero]
  exact MulChar.map_zero χ

theorem wQ_supp (A : ℝ) (z : UpperHalfPlane) (p : ℤ × ℤ) (h : wQ ψ p ≠ 0) :
    delA z / 2 ≤ qfA A z p := by
  have hn := ne_zero_of_char_ne_zero h
  have h1 : (1 : ℝ) ≤ (p.2 : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ p.2 ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs p.2]
    exact_mod_cast this
  have := qfA_ge A z p
  have hd := delA_pos z
  have h2 : 0 ≤ A ^ 2 * z.im ^ 2 / 2 * (p.1 : ℝ) ^ 2 := by positivity
  have h3 : delA z / 2 ≤ delA z / 2 * (p.2 : ℝ) ^ 2 := by nlinarith
  linarith

theorem wD_supp (A : ℝ) (z : UpperHalfPlane) (p : ℤ × ℤ) (h : wD ψ p ≠ 0) :
    A ^ 2 * z.im ^ 2 / 2 ≤ qfA A z p := by
  have hn := ne_zero_of_char_ne_zero h
  have h1 : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ p.1 ^ 2 := by nlinarith [Int.one_le_abs hn, sq_abs p.1]
    exact_mod_cast this
  have := qfA_ge A z p
  have hd := delA_pos z
  have h2 : 0 ≤ delA z / 2 * (p.2 : ℝ) ^ 2 := by positivity
  have h0 : 0 ≤ A ^ 2 * z.im ^ 2 / 2 := by positivity
  have h3 : A ^ 2 * z.im ^ 2 / 2 ≤ A ^ 2 * z.im ^ 2 / 2 * (p.1 : ℝ) ^ 2 := by nlinarith
  linarith

theorem thetaW_wQ_eq (B : ℕ) (z : UpperHalfPlane) {t : ℝ} (ht : 0 < t) (hA : ((q * B : ℕ) : ℝ) ≠ 0) :
    thetaW (wQ ψ) ((q * B : ℕ) : ℝ) z t = thetaQ ψ B z t := by
  have hs := summable_thetaW_terms (w := wQ ψ) ((q * B : ℕ) : ℝ) z (norm_wQ_le ψ) ht hA
  rw [thetaW, hs.tsum_prod' (fun m => hs.prod_factor m)]
  refine tsum_congr fun m => tsum_congr fun n => ?_
  simp only [wQ, qfA]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem thetaW_wD_eq (B : ℕ) (z : UpperHalfPlane) {t : ℝ} (ht : 0 < t) (hA : (B : ℝ) ≠ 0) :
    thetaW (wD ψ) (B : ℝ) z t = thetaD ψ B z t := by
  have hs := summable_thetaW_terms (w := wD ψ) (B : ℝ) z (norm_wD_le ψ) ht hA
  rw [thetaW, hs.tsum_prod' (fun m => hs.prod_factor m)]
  refine tsum_congr fun m => tsum_congr fun n => ?_
  simp only [wD, qfA]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

variable {B : ℕ} (hB : 0 < B) (z : UpperHalfPlane)

include hB in
theorem qB_ne_zero : ((q * B : ℕ) : ℝ) ≠ 0 := by
  have := hq.out.ne_zero; positivity

include hB in
theorem B_ne_zero : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'

/-- **The Mellin functional-equation pair of the Epstein zeta function with a character**:
`f = Θ` on `ℤ qBz + ℤ` with weight `ψ(n)`, `g(x) = Θ̂(x/(q²B²))` on `ℤ Bz + ℤ` with weight `ψ̄(k)`,
weight `1`, root number `τ(ψ)/(q²B)`; both vanish at `∞`. -/
def epsFEPair (hψ : ψ ≠ 1) : WeakFEPair ℂ where
  f := thetaW (wQ ψ) ((q * B : ℕ) : ℝ) z
  g := fun x => thetaW (wD ψ) (B : ℝ) z (x / (q ^ 2 * B ^ 2))
  k := 1
  ε := gaussSum ψ ZMod.stdAddChar / (q ^ 2 * B)
  f₀ := 0
  g₀ := 0
  hf_int := (continuousOn_thetaW _ z (norm_wQ_le ψ) (qB_ne_zero hB)).locallyIntegrableOn measurableSet_Ioi
  hg_int := by
    have hc : (0 : ℝ) < q ^ 2 * B ^ 2 := by have := hq.out.pos; positivity
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    exact (continuousOn_thetaW _ z (norm_wD_le ψ) (B_ne_zero hB)).comp (continuousOn_id.div_const _)
      fun x hx => mem_Ioi.2 (div_pos (mem_Ioi.1 hx) hc)
  hk := one_pos
  hε := by
    have h1 := tauG_ne_zero ψ hψ
    have h2 : ((q : ℂ) ^ 2 * B) ≠ 0 := by
      have := hq.out.ne_zero; have := hB.ne'; exact_mod_cast (by positivity : (q : ℝ) ^ 2 * B ≠ 0)
    exact div_ne_zero h1 h2
  h_feq x hx := by
    have hx0 : (0 : ℝ) < x := hx
    have hx' : (0 : ℝ) < 1 / x := one_div_pos.2 hx0
    have hc : (0 : ℝ) < q ^ 2 * B ^ 2 := by have := hq.out.pos; positivity
    rw [thetaW_wQ_eq ψ B z hx' (qB_ne_zero hB), thetaQ_inversion ψ hψ hB z hx',
      thetaW_wD_eq ψ B z (div_pos hx0 hc) (B_ne_zero hB), smul_eq_mul]
    have e : 1 / (1 / x * q ^ 2 * B ^ 2) = x / (q ^ 2 * B ^ 2) := by
      have := hq.out.pos; field_simp
    rw [e, Real.rpow_one]
    have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
    have hB0 : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    push_cast
    field_simp
  hf_top r := thetaW_isBigO _ z (norm_wQ_le ψ) (qB_ne_zero hB) (half_pos (delA_pos z))
    (wQ_supp ψ _ z) r
  hg_top r := by
    have hc : (0 : ℝ) < q ^ 2 * B ^ 2 := by have := hq.out.pos; positivity
    have hy := z.im_pos
    have hB' : (0 : ℝ) < B := by exact_mod_cast hB
    have hA2 : 0 < (B : ℝ) ^ 2 * z.im ^ 2 / 2 := by positivity
    have h1 := (thetaW_isBigO _ z (norm_wD_le ψ) (B_ne_zero hB) hA2 (wD_supp ψ _ z) r).comp_tendsto
      (tendsto_id.atTop_div_const hc)
    refine h1.trans ?_
    have h2 : (fun x : ℝ => (x / (q ^ 2 * B ^ 2)) ^ r) =ᶠ[atTop]
        fun x => ((q ^ 2 * B ^ 2 : ℝ) ^ r)⁻¹ * x ^ r := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [Real.div_rpow hx.le hc.le]; ring
    exact h2.trans_isBigO (isBigO_const_mul_self _ _ _)

theorem isStrong_epsFEPair (hψ : ψ ≠ 1) : IsStrongFEPair (epsFEPair ψ hB z hψ) := ⟨rfl, rfl⟩

/-- **The completed Epstein function with a character is entire.** -/
theorem differentiable_epsΛ (hψ : ψ ≠ 1) : Differentiable ℂ (epsFEPair ψ hB z hψ).Λ :=
  (isStrong_epsFEPair ψ hB z hψ).differentiable_Λ

/-- **Functional equation**: `Λ(1 - s) = τ(ψ)/(q²B) · Λ̂(s)`. -/
theorem epsΛ_functional_equation (hψ : ψ ≠ 1) (s : ℂ) :
    (epsFEPair ψ hB z hψ).Λ (1 - s) =
      gaussSum ψ ZMod.stdAddChar / (q ^ 2 * B) * (epsFEPair ψ hB z hψ).symm.Λ s := by
  have := (epsFEPair ψ hB z hψ).functional_equation s
  simpa [epsFEPair] using this

theorem wQ_pos_supp (p : ℤ × ℤ) (h : wQ ψ p ≠ 0) : 0 < qfA ((q * B : ℕ) : ℝ) z p :=
  lt_of_lt_of_le (half_pos (delA_pos z)) (wQ_supp ψ _ z p h)

include hB in
theorem wD_pos_supp (p : ℤ × ℤ) (h : wD ψ p ≠ 0) : 0 < qfA (B : ℝ) z p := by
  have hy := z.im_pos
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  exact lt_of_lt_of_le (by positivity) (wD_supp ψ _ z p h)

/-- For `Re s > 1`: `Λ(s) = (π/y)^{-s} Γ(s) Σ_{(m,n)} ψ(n) |mqBz + n|^{-2s}`. -/
theorem epsΛ_eq (hψ : ψ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    (epsFEPair ψ hB z hψ).Λ s =
      ((π / z.im : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * epsW (w := wQ ψ) ((q * B : ℕ) : ℝ) z s := by
  rw [(isStrong_epsFEPair ψ hB z hψ).Λ_eq]
  have hA : (0 : ℝ) < ((q * B : ℕ) : ℝ) := by have := hq.out.pos; positivity
  exact mellin_thetaW _ z (norm_wQ_le ψ) hA (wQ_pos_supp ψ z) hs

/-- For `Re s > 1`: `Λ̂(s) = (q²B²)^s (π/y)^{-s} Γ(s) Σ_{(k,l)} ψ̄(k) |kBz + l|^{-2s}`. -/
theorem epsΛ_symm_eq (hψ : ψ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    (epsFEPair ψ hB z hψ).symm.Λ s =
      (((q ^ 2 * B ^ 2 : ℝ)) : ℂ) ^ s *
        (((π / z.im : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * epsW (w := wD ψ) (B : ℝ) z s) := by
  have hc : (0 : ℝ) < q ^ 2 * B ^ 2 := by have := hq.out.pos; positivity
  rw [(isStrong_epsFEPair ψ hB z hψ).symm_Λ_eq]
  simp only [epsFEPair]
  have e : (fun x : ℝ => thetaW (wD ψ) (B : ℝ) z (x / (q ^ 2 * B ^ 2))) =
      fun x => (thetaW (wD ψ) (B : ℝ) z) ((1 / (q ^ 2 * B ^ 2)) * x) := by
    funext x; congr 1; ring
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  rw [e, mellin_comp_mul_left (thetaW (wD ψ) (B : ℝ) z) s (by positivity : (0 : ℝ) < 1 / (q ^ 2 * B ^ 2)),
    mellin_thetaW _ z (norm_wD_le ψ) hB' (wD_pos_supp ψ hB z) hs, smul_eq_mul]
  congr 1
  rw [one_div, Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hc.le]; exact Real.pi_pos.ne), Complex.cpow_neg, inv_inv]

/-- **The functional equation of the Epstein zeta function with a character**: for `ψ ≠ 1` mod a
prime `q`, `B ≥ 1` and `Re s > 1`, the entire continuation `Λ` of
`(π/y)^{-s} Γ(s) Σ_{(m,n)} ψ(n) |mqBz + n|^{-2s}` satisfies
`Λ(1 - s) = τ(ψ)/(q²B) · (q²B²)^s (π/y)^{-s} Γ(s) Σ_{(k,l)} ψ̄(k) |kBz + l|^{-2s}`. -/
theorem epstein_char_functional_equation (hψ : ψ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    (epsFEPair ψ hB z hψ).Λ (1 - s) =
      gaussSum ψ ZMod.stdAddChar / (q ^ 2 * B) * ((((q ^ 2 * B ^ 2 : ℝ)) : ℂ) ^ s *
        (((π / z.im : ℝ) : ℂ) ^ (-s) * Complex.Gamma s * epsW (w := wD ψ) (B : ℝ) z s)) := by
  rw [epsΛ_functional_equation ψ hB z hψ, epsΛ_symm_eq ψ hB z hψ hs]

end Character

end

end GaloisForLFunctions.RHTower.EpsteinCharacter
