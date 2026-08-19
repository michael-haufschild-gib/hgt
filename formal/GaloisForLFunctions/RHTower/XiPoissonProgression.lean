import GaloisForLFunctions.RHTower.XiCSchwartzRestriction
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# The Poisson trace of `Xi` over an arithmetic progression

`Xi` is the Fourier transform of the theta-cusp source, which is a Schwartz function and is
strictly positive.  Poisson summation therefore turns the values of `Xi` along a two-sided
arithmetic progression `a + hℤ` into the periodisation of the source at scale `2π/h`:

```
∑_{n ∈ ℤ} Xi(a + n h)  =  ∑_{n ∈ ℤ} (1/h) · S(n/h) · e^{-2πina/h} ,      S = 𝓕⁻¹ Xi .
```

The right-hand side has a distinguished term at `n = 0`, namely `S(0)/h`, which is a strictly
positive multiple of `1/h`, while all the other terms are `O(h)` by the Schwartz decay of `S`.
Consequently the trace cannot vanish once the step is small, and no such progression can consist
entirely of zeros of `Xi`.

Positivity of the source enters only through `S(0) ≠ 0`; the decay of `S` does the rest.  The
argument is height-uniform in the phase `a` but not in the step `h`, and the reason is recorded in
the accompanying programme note: the periodisation loses its dominant term once `2π/h` is small.
-/

open Complex MeasureTheory Filter Asymptotics
open scoped FourierTransform SchwartzMap Real

noncomputable section

namespace RHTower

/-- Schwartz decay survives an affine reparametrisation. -/
theorem isBigO_schwartz_affine (F : 𝓢(ℝ, ℂ)) {c d : ℝ} (hc : c ≠ 0) :
    (fun y : ℝ => F (d + c * y)) =O[Filter.cocompact ℝ] fun y : ℝ => |y| ^ (-2 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := F.decay 2 0
  have hcabs : (0 : ℝ) < |c| := abs_pos.mpr hc
  set R : ℝ := max 1 (2 * |d| / |c|) with hR
  have hR1 : (1 : ℝ) ≤ R := le_max_left _ _
  have hR2 : 2 * |d| / |c| ≤ R := le_max_right _ _
  refine Asymptotics.isBigO_iff.mpr ⟨4 * C / c ^ 2, ?_⟩
  filter_upwards [(tendsto_norm_cocompact_atTop (E := ℝ)).eventually_ge_atTop R] with y hy
  have hy1 : (1 : ℝ) ≤ |y| := by
    rw [Real.norm_eq_abs] at hy
    linarith
  have hypos : (0 : ℝ) < |y| := by linarith
  have hd : |d| ≤ |c| * |y| / 2 := by
    have h1 : 2 * |d| / |c| ≤ |y| := by
      rw [Real.norm_eq_abs] at hy
      linarith
    rw [div_le_iff₀ hcabs] at h1
    linarith
  have hlow : |c| * |y| / 2 ≤ |d + c * y| := by
    have := abs_sub_abs_le_abs_sub (c * y) (-d)
    have habs : |c * y| = |c| * |y| := abs_mul c y
    have h2 : |d + c * y| = |c * y - (-d)| := by
      congr 1
      ring
    rw [h2]
    have h3 : |(-d : ℝ)| = |d| := abs_neg d
    rw [h3] at this
    linarith
  have hkey := hb (d + c * y)
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hkey
  have hpos : (0 : ℝ) < |d + c * y| := lt_of_lt_of_le (by positivity) hlow
  have hFbound : ‖F (d + c * y)‖ ≤ C / |d + c * y| ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hkey]
  have hsq : (|c| * |y| / 2) ^ 2 ≤ |d + c * y| ^ 2 := by
    nlinarith [hlow, abs_nonneg (d + c * y), mul_pos hcabs hypos]
  have hnorm : ‖|y| ^ (-2 : ℝ)‖ = (|y| ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _)]
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg (abs_nonneg y),
      Real.rpow_natCast]
  rw [hnorm]
  have hcy : (|c| * |y| / 2) ^ 2 = c ^ 2 * |y| ^ 2 / 4 := by
    rw [div_pow, mul_pow, sq_abs]
    ring
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hy2 : (0 : ℝ) < |y| ^ 2 := by positivity
  have h1 : c ^ 2 * |y| ^ 2 / 4 ≤ |d + c * y| ^ 2 := by
    rw [← hcy]
    exact hsq
  have hfinal : C / |d + c * y| ^ 2 ≤ 4 * C / c ^ 2 * (|y| ^ 2)⁻¹ := by
    have hstep : C / |d + c * y| ^ 2 ≤ C / (c ^ 2 * |y| ^ 2 / 4) :=
      div_le_div_of_nonneg_left hC.le (by positivity) h1
    have heq : C / (c ^ 2 * |y| ^ 2 / 4) = 4 * C / c ^ 2 * (|y| ^ 2)⁻¹ := by
      field_simp
    linarith [hstep, heq.le, heq.ge]
  linarith [hFbound, hfinal]

/-- The scaled and modulated theta source whose Fourier transform samples `Xi` along the
arithmetic progression `a + h ℤ`. -/
def xiProgressionKernel (a h : ℝ) (u : ℝ) : ℂ :=
  (h : ℂ)⁻¹ * (Complex.exp ((↑(-2 * π * u * a / h) : ℂ) * Complex.I) *
    xiThetaSchwartzSource (u / h))

theorem fourier_xiProgressionKernel {a h : ℝ} (hh : 0 < h) (y : ℝ) :
    𝓕 (xiProgressionKernel a h) y = XiC ((a + h * y : ℝ) : ℂ) := by
  have hh0 : (h : ℝ) ≠ 0 := ne_of_gt hh
  have hhC : (h : ℂ) ≠ 0 := by exact_mod_cast hh0
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hstep : ∀ x : ℝ,
      Complex.exp ((↑(-2 * π * (h * x) * y) : ℂ) * Complex.I) •
          xiProgressionKernel a h (h * x)
        = (h : ℂ)⁻¹ * (Complex.exp ((↑(-2 * π * x * (a + h * y)) : ℂ) * Complex.I) *
            xiThetaSchwartzSource x) := by
    intro x
    rw [xiProgressionKernel, smul_eq_mul]
    have hdiv : h * x / h = x := by field_simp
    rw [hdiv]
    have hexp : Complex.exp ((↑(-2 * π * (h * x) * y) : ℂ) * Complex.I) *
        Complex.exp ((↑(-2 * π * (h * x) * a / h) : ℂ) * Complex.I)
        = Complex.exp ((↑(-2 * π * x * (a + h * y)) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      have hcast : ((-2 * π * (h * x) * a / h : ℝ) : ℂ) = ((-2 * π * x * a : ℝ) : ℂ) := by
        congr 1
        field_simp
      rw [hcast]
      push_cast
      ring
    calc Complex.exp ((↑(-2 * π * (h * x) * y) : ℂ) * Complex.I) *
          ((h : ℂ)⁻¹ * (Complex.exp ((↑(-2 * π * (h * x) * a / h) : ℂ) * Complex.I) *
            xiThetaSchwartzSource x))
        = (h : ℂ)⁻¹ * ((Complex.exp ((↑(-2 * π * (h * x) * y) : ℂ) * Complex.I) *
            Complex.exp ((↑(-2 * π * (h * x) * a / h) : ℂ) * Complex.I)) *
              xiThetaSchwartzSource x) := by ring
      _ = (h : ℂ)⁻¹ * (Complex.exp ((↑(-2 * π * x * (a + h * y)) : ℂ) * Complex.I) *
            xiThetaSchwartzSource x) := by rw [hexp]
  have hG := MeasureTheory.Measure.integral_comp_mul_left
    (fun v : ℝ => Complex.exp ((↑(-2 * π * v * y) : ℂ) * Complex.I) *
      xiProgressionKernel a h v) h
  have habs : |h⁻¹| = h⁻¹ := abs_of_pos (by positivity)
  rw [habs] at hG
  have hinner : ∫ x : ℝ, Complex.exp ((↑(-2 * π * (h * x) * y) : ℂ) * Complex.I) *
      xiProgressionKernel a h (h * x)
      = (h : ℂ)⁻¹ * ∫ x : ℝ, Complex.exp ((↑(-2 * π * x * (a + h * y)) : ℂ) * Complex.I) *
          xiThetaSchwartzSource x := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hx := hstep x
    rw [smul_eq_mul] at hx
    exact hx
  have hFS : ∫ x : ℝ, Complex.exp ((↑(-2 * π * x * (a + h * y)) : ℂ) * Complex.I) *
      xiThetaSchwartzSource x = XiC ((a + h * y : ℝ) : ℂ) := by
    have h1 := Real.fourier_real_eq_integral_exp_smul (⇑xiThetaSchwartzSource) (a + h * y)
    have h2 := fourier_xiThetaSchwartzSource (a + h * y)
    have h3 : (𝓕 (⇑xiThetaSchwartzSource)) (a + h * y) = XiC ((a + h * y : ℝ) : ℂ) := h2
    rw [h1] at h3
    rw [← h3]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rfl
  rw [hinner, hFS] at hG
  rw [Complex.real_smul] at hG
  have hcast : ((h⁻¹ : ℝ) : ℂ) = (h : ℂ)⁻¹ := by push_cast; ring
  rw [hcast] at hG
  have hfinal : ∫ v : ℝ, Complex.exp ((↑(-2 * π * v * y) : ℂ) * Complex.I) *
      xiProgressionKernel a h v = XiC ((a + h * y : ℝ) : ℂ) :=
    (mul_left_cancel₀ (inv_ne_zero hhC) hG).symm
  refine Eq.trans ?_ hfinal
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  rfl

/-- The theta-cusp source is strictly positive at the origin: the `n = 1` term already is. -/
theorem thetaCuspFullSource_pos_zero : 0 < thetaCuspFullSource 0 := by
  have hpi := Real.pi_gt_three
  rw [thetaCuspFullSource]
  refine (summable_thetaCuspSourceTerm 0).tsum_pos ?_ 1 ?_
  · intro n
    rcases n with _ | n
    · simp [thetaCuspSourceTerm, thetaCuspSeed]
    · refine mul_nonneg (Real.exp_pos _).le (thetaCuspSeed_pos ?_).le
      have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      have hexp : ((n + 1 : ℕ) : ℝ) * Real.exp 0 = ((n + 1 : ℕ) : ℝ) := by simp
      rw [hexp]
      nlinarith [hn, hpi]
  · refine mul_pos (Real.exp_pos _) (thetaCuspSeed_pos ?_)
    have hone : ((1 : ℕ) : ℝ) * Real.exp 0 = 1 := by simp
    rw [hone]
    nlinarith [hpi]

/-- Reciprocal squares are summable over the integers. -/
theorem summable_one_add_sq_inv_int : Summable (fun n : ℤ => (1 + (n : ℝ) ^ 2)⁻¹) := by
  have hnat : Summable (fun n : ℕ => (1 + (n : ℝ) ^ 2)⁻¹) := by
    have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℝ)) :=
      Real.summable_one_div_nat_rpow.mpr (by norm_num)
    have hshift : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ)) ^ (2 : ℝ)) :=
      (summable_nat_add_iff 1).mpr hp
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (hshift.mul_left 2)
    have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; ring
    rw [hcast, Real.rpow_two]
    have hpos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 := by positivity
    have h1 : (0 : ℝ) < 1 + (n : ℝ) ^ 2 := by positivity
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [inv_le_iff_one_le_mul₀ h1]
    have hrw : 2 * (1 / ((n : ℝ) + 1) ^ 2) * (1 + (n : ℝ) ^ 2)
        = (2 * (1 + (n : ℝ) ^ 2)) / ((n : ℝ) + 1) ^ 2 := by
      field_simp
    rw [hrw, le_div_iff₀ hpos]
    nlinarith [hn0, sq_nonneg ((n : ℝ) - 1)]
  refine Summable.of_nat_of_neg hnat ?_
  simpa using hnat
theorem continuous_xiProgressionKernel (a h : ℝ) : Continuous (xiProgressionKernel a h) := by
  refine continuous_const.mul (Continuous.mul ?_ ?_)
  · exact Complex.continuous_exp.comp (by fun_prop)
  · exact xiThetaSchwartzSource.continuous.comp (by fun_prop)

theorem norm_xiProgressionKernel {a h : ℝ} (hh : 0 < h) (u : ℝ) :
    ‖xiProgressionKernel a h u‖ = h⁻¹ * ‖xiThetaSchwartzSource (u / h)‖ := by
  rw [xiProgressionKernel, norm_mul, norm_mul]
  have hexp : ‖Complex.exp ((↑(-2 * π * u * a / h) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  rw [hexp, one_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]

theorem isBigO_xiProgressionKernel {a h : ℝ} (hh : 0 < h) :
    (fun u : ℝ => xiProgressionKernel a h u) =O[Filter.cocompact ℝ]
      fun y : ℝ => |y| ^ (-2 : ℝ) := by
  have hinv : (h⁻¹ : ℝ) ≠ 0 := inv_ne_zero (ne_of_gt hh)
  have hbase := isBigO_schwartz_affine xiThetaSchwartzSource (c := h⁻¹) (d := 0) hinv
  refine Asymptotics.IsBigO.trans ?_ hbase
  refine Asymptotics.isBigO_iff.mpr ⟨h⁻¹, Filter.Eventually.of_forall fun u => ?_⟩
  rw [norm_xiProgressionKernel hh u]
  have harg : u / h = 0 + h⁻¹ * u := by
    rw [zero_add]
    field_simp
  rw [harg]

theorem isBigO_fourier_xiProgressionKernel {a h : ℝ} (hh : 0 < h) :
    (𝓕 (xiProgressionKernel a h)) =O[Filter.cocompact ℝ] fun y : ℝ => |y| ^ (-2 : ℝ) := by
  have hbase := isBigO_schwartz_affine xiCSchwartz (c := h) (d := a) (ne_of_gt hh)
  refine Asymptotics.IsBigO.trans ?_ hbase
  refine Asymptotics.isBigO_iff.mpr ⟨1, Filter.Eventually.of_forall fun y => ?_⟩
  rw [fourier_xiProgressionKernel hh y, one_mul]
  have hx : xiCSchwartz (a + h * y) = XiC ((a + h * y : ℝ) : ℂ) := xiCSchwartz_apply _
  rw [show ‖(fun y : ℝ => xiCSchwartz (a + h * y)) y‖ = ‖xiCSchwartz (a + h * y)‖ from rfl, hx]

/-- **The Poisson trace of `Xi` along an arithmetic progression.** -/
theorem tsum_xiProgressionKernel_eq {a h : ℝ} (hh : 0 < h) :
    ∑' n : ℤ, xiProgressionKernel a h (n : ℝ) = ∑' n : ℤ, XiC ((a + h * n : ℝ) : ℂ) := by
  have hp := Real.tsum_eq_tsum_fourier_of_rpow_decay (continuous_xiProgressionKernel a h)
    (b := 2) (by norm_num) (isBigO_xiProgressionKernel hh)
    (isBigO_fourier_xiProgressionKernel hh) 0
  simp only [zero_add] at hp
  rw [hp]
  refine tsum_congr fun n => ?_
  rw [fourier_xiProgressionKernel hh (n : ℝ)]
  simp

theorem summable_xiProgressionKernel {a h : ℝ} (hh : 0 < h) :
    Summable (fun n : ℤ => xiProgressionKernel a h (n : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := xiThetaSchwartzSource.decay 2 0
  obtain ⟨C₀, hC₀, hb₀⟩ := xiThetaSchwartzSource.decay 0 0
  have hh0 : h ≠ 0 := ne_of_gt hh
  refine Summable.of_norm_bounded
    (g := fun n : ℤ => (h⁻¹ * (C₀ + 2 * C * h ^ 2)) * (1 + (n : ℝ) ^ 2)⁻¹)
    (summable_one_add_sq_inv_int.mul_left _) (fun n => ?_)
  rw [norm_xiProgressionKernel hh (n : ℝ)]
  have harg : (n : ℝ) / h = (n : ℝ) / h := rfl
  rw [harg]
  have hbound : ‖xiThetaSchwartzSource ((n : ℝ) / h)‖
      ≤ (C₀ + 2 * C * h ^ 2) * (1 + (n : ℝ) ^ 2)⁻¹ := by
    rcases eq_or_ne n 0 with rfl | hn
    · have h0 := hb₀ ((0 : ℝ) / h)
      rw [norm_iteratedFDeriv_zero] at h0
      simp only [Int.cast_zero, zero_div] at h0 ⊢
      have hCpos : (0 : ℝ) ≤ 2 * C * h ^ 2 := by positivity
      have h1 : (1 : ℝ) + (0 : ℝ) ^ 2 = 1 := by norm_num
      rw [h1, inv_one, mul_one]
      simp only [pow_zero, one_mul] at h0
      linarith
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ n ^ 2 := by
          rcases lt_or_gt_of_ne hn with hlt | hgt <;> nlinarith
        exact_mod_cast this
      have hkey := hb ((n : ℝ) / h)
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hkey
      have habs : |(n : ℝ) / h| ^ 2 = (n : ℝ) ^ 2 / h ^ 2 := by
        rw [abs_div, abs_of_pos hh, div_pow, sq_abs]
      rw [habs] at hkey
      have hpos2 : (0 : ℝ) < (n : ℝ) ^ 2 / h ^ 2 := by
        have : (0 : ℝ) < (n : ℝ) ^ 2 := by linarith
        positivity
      have hh2 : (0 : ℝ) < h ^ 2 := by positivity
      have hb1 : ‖xiThetaSchwartzSource ((n : ℝ) / h)‖ ≤ C * h ^ 2 / (n : ℝ) ^ 2 := by
        rw [le_div_iff₀ (by linarith)]
        have hmul := mul_le_mul_of_nonneg_right hkey hh2.le
        have heq : (n : ℝ) ^ 2 / h ^ 2 * ‖xiThetaSchwartzSource ((n : ℝ) / h)‖ * h ^ 2
            = ‖xiThetaSchwartzSource ((n : ℝ) / h)‖ * (n : ℝ) ^ 2 := by
          field_simp
        rw [heq] at hmul
        linarith
      have hcmp : C * h ^ 2 / (n : ℝ) ^ 2 ≤ (C₀ + 2 * C * h ^ 2) * (1 + (n : ℝ) ^ 2)⁻¹ := by
        have hrw : (C₀ + 2 * C * h ^ 2) * (1 + (n : ℝ) ^ 2)⁻¹
            = (C₀ + 2 * C * h ^ 2) / (1 + (n : ℝ) ^ 2) := by
          rw [div_eq_mul_inv]
        rw [hrw, div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [hC₀.le, hn1, mul_pos hC hh2]
      linarith
  have hinvpos : (0 : ℝ) < h⁻¹ := by positivity
  calc h⁻¹ * ‖xiThetaSchwartzSource ((n : ℝ) / h)‖
      ≤ h⁻¹ * ((C₀ + 2 * C * h ^ 2) * (1 + (n : ℝ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hbound hinvpos.le
    _ = (h⁻¹ * (C₀ + 2 * C * h ^ 2)) * (1 + (n : ℝ) ^ 2)⁻¹ := by ring

theorem norm_xiThetaSchwartzSource_zero_pos : 0 < ‖xiThetaSchwartzSource (0 : ℝ)‖ := by
  rw [norm_pos_iff]
  rw [xiThetaSchwartzSource_apply]
  have hz : (2 : ℝ) * π * (0 : ℝ) = 0 := by ring
  rw [hz]
  have hpos := thetaCuspFullSource_pos_zero
  have hpi : (0 : ℝ) < π := Real.pi_pos
  intro hzero
  rw [mul_eq_zero] at hzero
  rcases hzero with h1 | h2
  · have : (2 : ℝ) * π = 0 := by exact_mod_cast h1
    linarith
  · have : thetaCuspFullSource 0 = 0 := by exact_mod_cast h2
    linarith

/-- **No arithmetic progression of small step lies entirely in the real `Xi` divisor.**  The
Poisson trace of `Xi` along the progression is the periodisation of the strictly positive theta
source, whose central term dominates once the step is small. -/
theorem exists_ne_zero_along_progression :
    ∃ h₀ : ℝ, 0 < h₀ ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ a : ℝ,
      ∃ n : ℤ, XiC ((a + h * n : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨C, hC, hb⟩ := xiThetaSchwartzSource.decay 2 0
  set A : ℝ := ∑' n : ℤ, (1 + (n : ℝ) ^ 2)⁻¹ with hA
  have hA0 : 0 ≤ A := tsum_nonneg fun n => by positivity
  have hS0 := norm_xiThetaSchwartzSource_zero_pos
  refine ⟨Real.sqrt (‖xiThetaSchwartzSource (0 : ℝ)‖ / (4 * C * (A + 1))), ?_, ?_⟩
  · exact Real.sqrt_pos.mpr (by positivity)
  intro h hh hle a
  by_contra hcon
  simp only [not_exists, not_not] at hcon
  -- the progression sum vanishes
  have hzeroRHS : ∑' n : ℤ, XiC ((a + h * n : ℝ) : ℂ) = 0 := by
    have : (fun n : ℤ => XiC ((a + h * n : ℝ) : ℂ)) = fun _ : ℤ => (0 : ℂ) := by
      funext n
      exact hcon n
    rw [this, tsum_zero]
  have hsum := summable_xiProgressionKernel (a := a) hh
  have hzero : ∑' n : ℤ, xiProgressionKernel a h (n : ℝ) = 0 := by
    rw [tsum_xiProgressionKernel_eq hh, hzeroRHS]
  -- the tail bound
  have htail : ∀ n : ℤ, ‖(if n = 0 then (0 : ℂ) else xiProgressionKernel a h (n : ℝ))‖
      ≤ (2 * C * h) * (1 + (n : ℝ) ^ 2)⁻¹ := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [if_pos rfl, norm_zero]
      positivity
    · rw [if_neg hn, norm_xiProgressionKernel hh (n : ℝ)]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : (1 : ℤ) ≤ n ^ 2 := by
          rcases lt_or_gt_of_ne hn with hlt | hgt <;> nlinarith
        exact_mod_cast this
      have hh2 : (0 : ℝ) < h ^ 2 := by positivity
      have hkey := hb ((n : ℝ) / h)
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hkey
      have habs : |(n : ℝ) / h| ^ 2 = (n : ℝ) ^ 2 / h ^ 2 := by
        rw [abs_div, abs_of_pos hh, div_pow, sq_abs]
      rw [habs] at hkey
      have hb1 : ‖xiThetaSchwartzSource ((n : ℝ) / h)‖ ≤ C * h ^ 2 / (n : ℝ) ^ 2 := by
        rw [le_div_iff₀ (by linarith)]
        have hmul := mul_le_mul_of_nonneg_right hkey hh2.le
        have heq : (n : ℝ) ^ 2 / h ^ 2 * ‖xiThetaSchwartzSource ((n : ℝ) / h)‖ * h ^ 2
            = ‖xiThetaSchwartzSource ((n : ℝ) / h)‖ * (n : ℝ) ^ 2 := by
          field_simp
        rw [heq] at hmul
        linarith
      have hinvpos : (0 : ℝ) < h⁻¹ := by positivity
      have hstep : h⁻¹ * ‖xiThetaSchwartzSource ((n : ℝ) / h)‖
          ≤ h⁻¹ * (C * h ^ 2 / (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hb1 hinvpos.le
      have hfin : h⁻¹ * (C * h ^ 2 / (n : ℝ) ^ 2) ≤ (2 * C * h) * (1 + (n : ℝ) ^ 2)⁻¹ := by
        have hrw : h⁻¹ * (C * h ^ 2 / (n : ℝ) ^ 2) = (C * h) / (n : ℝ) ^ 2 := by
          field_simp
        have hrw2 : (2 * C * h) * (1 + (n : ℝ) ^ 2)⁻¹ = (2 * C * h) / (1 + (n : ℝ) ^ 2) := by
          rw [div_eq_mul_inv]
        rw [hrw, hrw2, div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [hn1, mul_pos hC hh]
      linarith
  have hsumTail : Summable (fun n : ℤ =>
      ‖(if n = 0 then (0 : ℂ) else xiProgressionKernel a h (n : ℝ))‖) := by
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) htail
      (summable_one_add_sq_inv_int.mul_left _)
  have hsplit := hsum.tsum_eq_add_tsum_ite (0 : ℤ)
  rw [hzero] at hsplit
  have hnormle : ‖xiProgressionKernel a h ((0 : ℤ) : ℝ)‖
      ≤ ∑' n : ℤ, ‖(if n = 0 then (0 : ℂ) else xiProgressionKernel a h (n : ℝ))‖ := by
    have heq : xiProgressionKernel a h ((0 : ℤ) : ℝ)
        = -∑' n : ℤ, (if n = 0 then (0 : ℂ) else xiProgressionKernel a h (n : ℝ)) := by
      linear_combination -hsplit
    rw [heq, norm_neg]
    exact norm_tsum_le_tsum_norm hsumTail
  have hAbound : ∑' n : ℤ, ‖(if n = 0 then (0 : ℂ) else xiProgressionKernel a h (n : ℝ))‖
      ≤ (2 * C * h) * A := by
    have := hsumTail.tsum_le_tsum htail (summable_one_add_sq_inv_int.mul_left (2 * C * h))
    rwa [tsum_mul_left] at this
  have hK0 : ‖xiProgressionKernel a h ((0 : ℤ) : ℝ)‖
      = h⁻¹ * ‖xiThetaSchwartzSource (0 : ℝ)‖ := by
    have hz : ((0 : ℤ) : ℝ) = 0 := by norm_num
    rw [hz, norm_xiProgressionKernel hh 0]
    congr 2
    simp
  rw [hK0] at hnormle
  have hfinal : ‖xiThetaSchwartzSource (0 : ℝ)‖ ≤ 2 * C * A * h ^ 2 := by
    have hstep : h⁻¹ * ‖xiThetaSchwartzSource (0 : ℝ)‖ ≤ 2 * C * h * A := le_trans hnormle hAbound
    have hmul := mul_le_mul_of_nonneg_left hstep (le_of_lt hh)
    have heq : h * (h⁻¹ * ‖xiThetaSchwartzSource (0 : ℝ)‖) = ‖xiThetaSchwartzSource (0 : ℝ)‖ := by
      field_simp
    rw [heq] at hmul
    calc ‖xiThetaSchwartzSource (0 : ℝ)‖ ≤ h * (2 * C * h * A) := hmul
      _ = 2 * C * A * h ^ 2 := by ring
  have hh2le : h ^ 2 ≤ ‖xiThetaSchwartzSource (0 : ℝ)‖ / (4 * C * (A + 1)) := by
    have hsq := Real.sq_sqrt (le_of_lt (show (0:ℝ) <
      ‖xiThetaSchwartzSource (0 : ℝ)‖ / (4 * C * (A + 1)) by positivity))
    nlinarith [hle, hh, Real.sqrt_nonneg (‖xiThetaSchwartzSource (0 : ℝ)‖ / (4 * C * (A + 1)))]
  have hcontra : ‖xiThetaSchwartzSource (0 : ℝ)‖ < ‖xiThetaSchwartzSource (0 : ℝ)‖ := by
    calc ‖xiThetaSchwartzSource (0 : ℝ)‖ ≤ 2 * C * A * h ^ 2 := hfinal
      _ ≤ 2 * C * A * (‖xiThetaSchwartzSource (0 : ℝ)‖ / (4 * C * (A + 1))) := by
          have : (0 : ℝ) ≤ 2 * C * A := by positivity
          exact mul_le_mul_of_nonneg_left hh2le this
      _ < ‖xiThetaSchwartzSource (0 : ℝ)‖ := by
          rw [mul_div_assoc']
          rw [div_lt_iff₀ (by positivity)]
          nlinarith [hS0, hC, hA0, mul_pos hS0 hC,
            mul_nonneg (mul_nonneg hS0.le hC.le) hA0]
  exact absurd hcontra (lt_irrefl _)

end RHTower

end
