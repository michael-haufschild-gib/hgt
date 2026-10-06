import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Separation of the variables in `e(A√(mn))`

For `u = log m + log n` the phase `e(A√(mn)) = e(A e^{u/2})` is the restriction to the window
`[a, a + 2 log 2]` (`a = 2 log N`, `m, n ∈ (N, 2N]`) of the smooth compactly supported function
`g(u) = ρ(u − a) e(A e^{u/2})`, `ρ` a fixed bump equal to `1` on `[0, 2 log 2]`.  Fourier inversion gives

`e(A√(mn)) = ∫ ĝ(t) m^{2πit} n^{2πit} dt`,

and two integrations by parts give `(1 + (t/T)²)|ĝ(t)| ≤ C₀` with `T = 1 + |A| e^{a/2}`, so
`∫ |ĝ| ≤ C (1 + |A| e^{a/2})` with an absolute constant `C` (`exists_sqrt_phase_separation`).
-/

open MeasureTheory Set Filter Complex
open scoped FourierTransform

namespace GaloisForLFunctions.RHTower.KuznetsovSeparation

noncomputable section

/-- The fixed cutoff: `1` on `[0, 2 log 2]`, supported in `(−1, 2 log 2 + 1)`. -/
def sepBump : ContDiffBump (Real.log 2) :=
  ⟨Real.log 2, Real.log 2 + 1, Real.log_pos (by norm_num), by linarith⟩

/-- The cutoff as a function. -/
def bumpFn (x : ℝ) : ℝ := sepBump x

theorem bumpFn_eq_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 2 * Real.log 2) : bumpFn x = 1 := by
  refine sepBump.one_of_mem_closedBall ?_
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
  change -Real.log 2 ≤ x - Real.log 2 ∧ x - Real.log 2 ≤ Real.log 2
  constructor <;> linarith

theorem bumpFn_eq_zero {x : ℝ} (h : x < -1 ∨ 2 * Real.log 2 + 1 < x) : bumpFn x = 0 := by
  by_contra hne
  have hs : x ∈ Function.support (sepBump : ℝ → ℝ) := hne
  rw [sepBump.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  change -(Real.log 2 + 1) < x - Real.log 2 ∧ x - Real.log 2 < Real.log 2 + 1 at hs
  rcases h with h | h <;> linarith [hs.1, hs.2]

theorem bumpFn_nonneg (x : ℝ) : 0 ≤ bumpFn x := sepBump.nonneg
theorem bumpFn_le_one (x : ℝ) : bumpFn x ≤ 1 := sepBump.le_one

theorem contDiff_bumpFn : ContDiff ℝ (⊤ : ℕ∞) bumpFn := sepBump.contDiff

/-- `ρ'` and `ρ''`. -/
def bump1 : ℝ → ℝ := deriv bumpFn
def bump2 : ℝ → ℝ := deriv bump1

theorem contDiff_bump1 : ContDiff ℝ (⊤ : ℕ∞) bump1 := (contDiff_infty_iff_deriv.1 contDiff_bumpFn).2
theorem contDiff_bump2 : ContDiff ℝ (⊤ : ℕ∞) bump2 := (contDiff_infty_iff_deriv.1 contDiff_bump1).2

theorem hasDerivAt_bumpFn (x : ℝ) : HasDerivAt bumpFn (bump1 x) x :=
  ((contDiff_bumpFn.differentiable (by simp)) x).hasDerivAt

theorem hasDerivAt_bump1 (x : ℝ) : HasDerivAt bump1 (bump2 x) x :=
  ((contDiff_bump1.differentiable (by simp)) x).hasDerivAt

theorem bumpFn_eventually_zero {x : ℝ} (h : x < -1 ∨ 2 * Real.log 2 + 1 < x) :
    bumpFn =ᶠ[nhds x] fun _ => 0 := by
  rcases h with h | h
  · filter_upwards [Iio_mem_nhds h] with y hy using bumpFn_eq_zero (Or.inl hy)
  · filter_upwards [Ioi_mem_nhds h] with y hy using bumpFn_eq_zero (Or.inr hy)

theorem bump1_eq_zero {x : ℝ} (h : x < -1 ∨ 2 * Real.log 2 + 1 < x) : bump1 x = 0 := by
  rw [bump1, (bumpFn_eventually_zero h).deriv_eq]; simp

theorem bump2_eq_zero {x : ℝ} (h : x < -1 ∨ 2 * Real.log 2 + 1 < x) : bump2 x = 0 := by
  have h1 : bump1 =ᶠ[nhds x] fun _ => 0 := by
    rcases h with h | h
    · filter_upwards [Iio_mem_nhds h] with y hy using bump1_eq_zero (Or.inl hy)
    · filter_upwards [Ioi_mem_nhds h] with y hy using bump1_eq_zero (Or.inr hy)
  rw [bump2, h1.deriv_eq]; simp

theorem exists_bound_bump1 : ∃ C, ∀ x, |bump1 x| ≤ C := by
  obtain ⟨C, hC⟩ := (contDiff_bump1.continuous).bounded_above_of_compact_support
    (sepBump.hasCompactSupport.deriv)
  exact ⟨C, fun x => by simpa using hC x⟩

theorem exists_bound_bump2 : ∃ C, ∀ x, |bump2 x| ≤ C := by
  obtain ⟨C, hC⟩ := (contDiff_bump2.continuous).bounded_above_of_compact_support
    (sepBump.hasCompactSupport.deriv.deriv)
  exact ⟨C, fun x => by simpa using hC x⟩

/-! ## The phase and its derivatives -/

/-- `E(u) = e(A e^{u/2})`. -/
def sepPhase (A u : ℝ) : ℂ := cexp (((2 * Real.pi * A * Real.exp (u / 2) : ℝ) : ℂ) * Complex.I)

/-- `E'(u) = E(u) · i π A e^{u/2}`. -/
def sepPhase1 (A u : ℝ) : ℂ := sepPhase A u * (((Real.pi * A * Real.exp (u / 2) : ℝ) : ℂ) * Complex.I)

/-- `E''(u) = E(u) ((iπA e^{u/2})² + iπA e^{u/2}/2)`. -/
def sepPhase2 (A u : ℝ) : ℂ := sepPhase A u *
  ((((Real.pi * A * Real.exp (u / 2) : ℝ) : ℂ) * Complex.I) ^ 2 +
    ((Real.pi * A * Real.exp (u / 2) / 2 : ℝ) : ℂ) * Complex.I)

theorem hasDerivAt_sepPhase (A u : ℝ) : HasDerivAt (sepPhase A) (sepPhase1 A u) u := by
  have h : HasDerivAt (fun u : ℝ => 2 * Real.pi * A * Real.exp (u / 2))
      (Real.pi * A * Real.exp (u / 2)) u := by
    have := ((Real.hasDerivAt_exp (u / 2)).comp u ((hasDerivAt_id u).div_const 2)).const_mul
      (2 * Real.pi * A)
    exact this.congr_deriv (by simp; ring)
  exact ((h.ofReal_comp).mul_const Complex.I).cexp

theorem hasDerivAt_sepPhase1 (A u : ℝ) : HasDerivAt (sepPhase1 A) (sepPhase2 A u) u := by
  have h : HasDerivAt (fun u : ℝ => Real.pi * A * Real.exp (u / 2))
      (Real.pi * A * Real.exp (u / 2) / 2) u := by
    have := ((Real.hasDerivAt_exp (u / 2)).comp u ((hasDerivAt_id u).div_const 2)).const_mul
      (Real.pi * A)
    exact this.congr_deriv (by simp; ring)
  refine ((hasDerivAt_sepPhase A u).mul ((h.ofReal_comp).mul_const Complex.I)).congr_deriv ?_
  rw [sepPhase2, sepPhase1]
  push_cast
  ring

theorem norm_sepPhase (A u : ℝ) : ‖sepPhase A u‖ = 1 := by
  rw [sepPhase, Complex.norm_exp_ofReal_mul_I]

theorem norm_sepPhase1 (A u : ℝ) : ‖sepPhase1 A u‖ = Real.pi * |A| * Real.exp (u / 2) := by
  rw [sepPhase1, norm_mul, norm_sepPhase, one_mul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos,
    abs_of_pos (Real.exp_pos _)]

theorem norm_sepPhase2_le (A u : ℝ) :
    ‖sepPhase2 A u‖ ≤ (Real.pi * |A| * Real.exp (u / 2)) ^ 2 + Real.pi * |A| * Real.exp (u / 2) := by
  rw [sepPhase2, norm_mul, norm_sepPhase, one_mul]
  refine (norm_add_le _ _).trans ?_
  rw [norm_pow, norm_mul, norm_mul, Complex.norm_I, mul_one, mul_one, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_mul,
    abs_mul, abs_of_pos Real.pi_pos, abs_of_pos (Real.exp_pos _)]
  have : 0 ≤ Real.pi * |A| * Real.exp (u / 2) := by positivity
  norm_num
  linarith

/-- `g(u) = ρ(u − a) e(A e^{u/2})`. -/
def sepFun (a A u : ℝ) : ℂ := (bumpFn (u - a) : ℂ) * sepPhase A u

/-- `g'`. -/
def sepFun1 (a A u : ℝ) : ℂ := (bump1 (u - a) : ℂ) * sepPhase A u + (bumpFn (u - a) : ℂ) * sepPhase1 A u

/-- `g''`. -/
def sepFun2 (a A u : ℝ) : ℂ := (bump2 (u - a) : ℂ) * sepPhase A u +
  2 * ((bump1 (u - a) : ℂ) * sepPhase1 A u) + (bumpFn (u - a) : ℂ) * sepPhase2 A u

theorem hasDerivAt_sepFun (a A u : ℝ) : HasDerivAt (sepFun a A) (sepFun1 a A u) u := by
  have hρ : HasDerivAt (fun u : ℝ => (bumpFn (u - a) : ℂ)) (bump1 (u - a)) u :=
    ((hasDerivAt_bumpFn (u - a)).comp_sub_const u a).ofReal_comp
  exact (hρ.mul (hasDerivAt_sepPhase A u)).congr_deriv (by rw [sepFun1])

theorem hasDerivAt_sepFun1 (a A u : ℝ) : HasDerivAt (sepFun1 a A) (sepFun2 a A u) u := by
  have hρ : HasDerivAt (fun u : ℝ => (bumpFn (u - a) : ℂ)) (bump1 (u - a)) u :=
    ((hasDerivAt_bumpFn (u - a)).comp_sub_const u a).ofReal_comp
  have hρ1 : HasDerivAt (fun u : ℝ => (bump1 (u - a) : ℂ)) (bump2 (u - a)) u :=
    ((hasDerivAt_bump1 (u - a)).comp_sub_const u a).ofReal_comp
  exact ((hρ1.mul (hasDerivAt_sepPhase A u)).add (hρ.mul (hasDerivAt_sepPhase1 A u))).congr_deriv
    (by rw [sepFun2]; ring)

theorem continuous_sepFun (a A : ℝ) : Continuous (sepFun a A) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_sepFun a A u).continuousAt

theorem continuous_sepFun1 (a A : ℝ) : Continuous (sepFun1 a A) :=
  continuous_iff_continuousAt.2 fun u => (hasDerivAt_sepFun1 a A u).continuousAt

theorem continuous_sepFun2 (a A : ℝ) : Continuous (sepFun2 a A) := by
  unfold sepFun2 sepPhase2 sepPhase1 sepPhase
  have h0 := contDiff_bumpFn.continuous
  have h1 := contDiff_bump1.continuous
  have h2 := contDiff_bump2.continuous
  fun_prop

theorem sepFun_eq_phase {a A u : ℝ} (h0 : a ≤ u) (h1 : u ≤ a + 2 * Real.log 2) :
    sepFun a A u = sepPhase A u := by
  rw [sepFun, bumpFn_eq_one (by linarith) (by linarith), Complex.ofReal_one, one_mul]

theorem outside_window {a u : ℝ} (h : u ∉ Icc (a - 1) (a + 2 * Real.log 2 + 1)) :
    u - a < -1 ∨ 2 * Real.log 2 + 1 < u - a := by
  rw [mem_Icc, not_and_or, not_le, not_le] at h
  rcases h with h | h
  · left; linarith
  · right; linarith

theorem sepFun_eq_zero {a A u : ℝ} (h : u ∉ Icc (a - 1) (a + 2 * Real.log 2 + 1)) :
    sepFun a A u = 0 := by
  rw [sepFun, bumpFn_eq_zero (outside_window h)]; simp

theorem sepFun1_eq_zero {a A u : ℝ} (h : u ∉ Icc (a - 1) (a + 2 * Real.log 2 + 1)) :
    sepFun1 a A u = 0 := by
  rw [sepFun1, bumpFn_eq_zero (outside_window h), bump1_eq_zero (outside_window h)]; simp

theorem sepFun2_eq_zero {a A u : ℝ} (h : u ∉ Icc (a - 1) (a + 2 * Real.log 2 + 1)) :
    sepFun2 a A u = 0 := by
  rw [sepFun2, bumpFn_eq_zero (outside_window h), bump1_eq_zero (outside_window h),
    bump2_eq_zero (outside_window h)]; simp

theorem hasCompactSupport_of_window {f : ℝ → ℂ} {a : ℝ}
    (hf : ∀ u, u ∉ Icc (a - 1) (a + 2 * Real.log 2 + 1) → f u = 0) : HasCompactSupport f :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc fun u hu => by
    by_contra h; exact hu (hf u h)

theorem integrable_sepFun (a A : ℝ) : Integrable (sepFun a A) :=
  (continuous_sepFun a A).integrable_of_hasCompactSupport
    (hasCompactSupport_of_window fun _ h => sepFun_eq_zero h)

theorem integrable_sepFun1 (a A : ℝ) : Integrable (sepFun1 a A) :=
  (continuous_sepFun1 a A).integrable_of_hasCompactSupport
    (hasCompactSupport_of_window fun _ h => sepFun1_eq_zero h)

theorem integrable_sepFun2 (a A : ℝ) : Integrable (sepFun2 a A) :=
  (continuous_sepFun2 a A).integrable_of_hasCompactSupport
    (hasCompactSupport_of_window fun _ h => sepFun2_eq_zero h)

/-! ## Size of `g` and `g''` -/

theorem exp_half_le_of_window {a u : ℝ} (h : u ≤ a + 2 * Real.log 2 + 1) :
    Real.exp (u / 2) ≤ 2 * Real.exp (1 / 2) * Real.exp (a / 2) := by
  have h2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  calc Real.exp (u / 2) ≤ Real.exp (Real.log 2 + 1 / 2 + a / 2) := Real.exp_le_exp.2 (by linarith)
    _ = 2 * Real.exp (1 / 2) * Real.exp (a / 2) := by rw [Real.exp_add, Real.exp_add, h2]

theorem norm_sepFun_le (a A u : ℝ) : ‖sepFun a A u‖ ≤ 1 := by
  rw [sepFun, norm_mul, norm_sepPhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (bumpFn_nonneg _)]
  exact bumpFn_le_one _

/-- The window scale `X = 2π e^{1/2} |A| e^{a/2}`. -/
def sepScale (a A : ℝ) : ℝ := Real.pi * |A| * (2 * Real.exp (1 / 2) * Real.exp (a / 2))

theorem sepScale_nonneg (a A : ℝ) : 0 ≤ sepScale a A := by unfold sepScale; positivity

theorem norm_sepFun2_le {C1 C2 : ℝ} (hC1 : ∀ x, |bump1 x| ≤ C1) (hC2 : ∀ x, |bump2 x| ≤ C2)
    (a A u : ℝ) :
    ‖sepFun2 a A u‖ ≤ C2 + 2 * C1 * sepScale a A + sepScale a A ^ 2 + sepScale a A := by
  have hC1' : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  have hC2' : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0)
  have hX := sepScale_nonneg a A
  by_cases hw : u ∈ Icc (a - 1) (a + 2 * Real.log 2 + 1)
  · have he := exp_half_le_of_window hw.2
    have hY : Real.pi * |A| * Real.exp (u / 2) ≤ sepScale a A := by
      unfold sepScale; gcongr
    have hY0 : 0 ≤ Real.pi * |A| * Real.exp (u / 2) := by positivity
    rw [sepFun2]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_sepPhase, norm_sepPhase1, Complex.norm_real,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (bumpFn_nonneg _), Complex.norm_two]
    have h2 := norm_sepPhase2_le A u
    have hb := bumpFn_le_one (u - a)
    have hb0 := bumpFn_nonneg (u - a)
    calc |bump2 (u - a)| * 1 + 2 * (|bump1 (u - a)| * (Real.pi * |A| * Real.exp (u / 2))) +
          bumpFn (u - a) * ‖sepPhase2 A u‖
        ≤ C2 * 1 + 2 * (C1 * sepScale a A) + 1 * (sepScale a A ^ 2 + sepScale a A) := by
          gcongr
          · exact hC2 _
          · exact hC1 _
          · exact h2.trans (by gcongr)
      _ = _ := by ring
  · rw [sepFun2_eq_zero hw, norm_zero]
    positivity

theorem integral_norm_le_of_window {f : ℝ → ℂ} {a M : ℝ} (hint : Integrable f)
    (hf : ∀ u, u ∉ Icc (a - 1) (a + 2 * Real.log 2 + 1) → f u = 0) (hM : ∀ u, ‖f u‖ ≤ M) :
    ∫ u, ‖f u‖ ≤ (2 * Real.log 2 + 2) * M := by
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (a - 1) (a + 2 * Real.log 2 + 1))
    fun u hu => by rw [hf u hu, norm_zero]]
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  calc ∫ u in Icc (a - 1) (a + 2 * Real.log 2 + 1), ‖f u‖
      ≤ ∫ u in Icc (a - 1) (a + 2 * Real.log 2 + 1), M :=
        setIntegral_mono_on hint.norm.integrableOn (integrableOn_const (by simp) (by simp))
          measurableSet_Icc fun u _ => hM u
    _ = (2 * Real.log 2 + 2) * M := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]
        ring

/-! ## The Fourier transform -/

theorem norm_fourier_le_integral_norm (f : ℝ → ℂ) (t : ℝ) : ‖𝓕 f t‖ ≤ ∫ u, ‖f u‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
    (innerₗ ℝ) f t

theorem continuous_fourier_of_integrable {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (by exact continuous_inner) hf

theorem deriv_sepFun (a A : ℝ) : deriv (sepFun a A) = sepFun1 a A :=
  funext fun u => (hasDerivAt_sepFun a A u).deriv

theorem deriv_sepFun1 (a A : ℝ) : deriv (sepFun1 a A) = sepFun2 a A :=
  funext fun u => (hasDerivAt_sepFun1 a A u).deriv

theorem fourier_sepFun2 (a A t : ℝ) :
    𝓕 (sepFun2 a A) t = (2 * Real.pi * Complex.I * t) ^ 2 * 𝓕 (sepFun a A) t := by
  have h1 := Real.fourier_deriv (integrable_sepFun a A)
    (fun u => (hasDerivAt_sepFun a A u).differentiableAt)
    (by rw [deriv_sepFun]; exact integrable_sepFun1 a A)
  have h2 := Real.fourier_deriv (integrable_sepFun1 a A)
    (fun u => (hasDerivAt_sepFun1 a A u).differentiableAt)
    (by rw [deriv_sepFun1]; exact integrable_sepFun2 a A)
  rw [deriv_sepFun] at h1
  rw [deriv_sepFun1] at h2
  rw [h2, h1]
  simp only [smul_eq_mul]
  ring

/-- `(1 + (t/T)²) |ĝ(t)| ≤ ∫|g| + ∫|g''|/(4π²T²)`. -/
theorem one_add_sq_mul_norm_fourier_le (a A t : ℝ) {T : ℝ} (hT : 0 < T) :
    (1 + (t / T) ^ 2) * ‖𝓕 (sepFun a A) t‖ ≤
      (∫ u, ‖sepFun a A u‖) + (∫ u, ‖sepFun2 a A u‖) / (4 * Real.pi ^ 2 * T ^ 2) := by
  have h0 := norm_fourier_le_integral_norm (sepFun a A) t
  have h2 := norm_fourier_le_integral_norm (sepFun2 a A) t
  have hn : ‖(2 * Real.pi * Complex.I * t) ^ 2 * 𝓕 (sepFun a A) t‖ =
      (2 * Real.pi * |t|) ^ 2 * ‖𝓕 (sepFun a A) t‖ := by
    rw [norm_mul, norm_pow, show (2 * (Real.pi : ℂ) * Complex.I * t) =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
  rw [fourier_sepFun2, hn] at h2
  have hπ := Real.pi_pos
  have key : (t / T) ^ 2 * ‖𝓕 (sepFun a A) t‖ ≤ (∫ u, ‖sepFun2 a A u‖) / (4 * Real.pi ^ 2 * T ^ 2) := by
    rw [le_div_iff₀ (by positivity), div_pow]
    have : (2 * Real.pi * |t|) ^ 2 = 4 * Real.pi ^ 2 * t ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [this] at h2
    calc t ^ 2 / T ^ 2 * ‖𝓕 (sepFun a A) t‖ * (4 * Real.pi ^ 2 * T ^ 2)
        = 4 * Real.pi ^ 2 * t ^ 2 * ‖𝓕 (sepFun a A) t‖ := by field_simp
      _ ≤ _ := h2
  nlinarith

/-- **Separation of the variables in `e(A e^{u/2})`.** -/
theorem exists_sqrt_phase_separation : ∃ C : ℝ, 0 < C ∧ ∀ a A : ℝ,
    Integrable (𝓕 (sepFun a A)) ∧ (∫ t, ‖𝓕 (sepFun a A) t‖) ≤ C * (1 + |A| * Real.exp (a / 2)) ∧
      ∀ u, a ≤ u → u ≤ a + 2 * Real.log 2 →
        sepPhase A u = ∫ t, cexp (((2 * Real.pi * t * u : ℝ) : ℂ) * Complex.I) * 𝓕 (sepFun a A) t := by
  obtain ⟨C1, hC1⟩ := exists_bound_bump1
  obtain ⟨C2, hC2⟩ := exists_bound_bump2
  have hC1' : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  have hC2' : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0)
  have hlog := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  set ℓ := 2 * Real.log 2 + 2
  have hℓ : 0 < ℓ := by positivity
  set K₀ := C2 + 2 * C1 + 2
  have hK₀ : 0 < K₀ := by positivity
  have hπ := Real.pi_pos
  set D := ℓ * (1 + K₀ / (4 * Real.pi ^ 2))
  have hD : 0 < D := by positivity
  have he : 1 ≤ 2 * Real.pi * Real.exp (1 / 2) := by
    have := Real.one_le_exp (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    nlinarith [Real.pi_gt_three]
  refine ⟨D * Real.pi * (2 * Real.pi * Real.exp (1 / 2)), by positivity, fun a A => ?_⟩
  set X := sepScale a A
  have hX := sepScale_nonneg a A
  set T := 1 + X
  have hT : 0 < T := by positivity
  have hI0 : (∫ u, ‖sepFun a A u‖) ≤ ℓ * 1 :=
    integral_norm_le_of_window (integrable_sepFun a A) (fun u h => sepFun_eq_zero h)
      (norm_sepFun_le a A)
  have hI2 : (∫ u, ‖sepFun2 a A u‖) ≤ ℓ * (K₀ * T ^ 2) := by
    refine (integral_norm_le_of_window (integrable_sepFun2 a A) (fun u h => sepFun2_eq_zero h)
      (norm_sepFun2_le hC1 hC2 a A)).trans ?_
    gcongr
    simp only [K₀, T]
    nlinarith [sq_nonneg X]
  have hbound : ∀ t, ‖𝓕 (sepFun a A) t‖ ≤ D * (1 + (t / T) ^ 2)⁻¹ := fun t => by
    have h := one_add_sq_mul_norm_fourier_le a A t hT
    have hpos : 0 < 1 + (t / T) ^ 2 := by positivity
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
    refine h.trans ?_
    have hdiv : (∫ u, ‖sepFun2 a A u‖) / (4 * Real.pi ^ 2 * T ^ 2) ≤ ℓ * K₀ / (4 * Real.pi ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    simp only [D]
    have : ℓ * (1 + K₀ / (4 * Real.pi ^ 2)) = ℓ * 1 + ℓ * K₀ / (4 * Real.pi ^ 2) := by ring
    rw [this]
    linarith
  have hmaj : Integrable fun t : ℝ => D * (1 + (t / T) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_div hT.ne').const_mul D
  have hint : Integrable (𝓕 (sepFun a A)) :=
    hmaj.mono' (continuous_fourier_of_integrable (integrable_sepFun a A)).aestronglyMeasurable
      (Eventually.of_forall hbound)
  refine ⟨hint, ?_, ?_⟩
  · calc (∫ t, ‖𝓕 (sepFun a A) t‖) ≤ ∫ t, D * (1 + (t / T) ^ 2)⁻¹ :=
          integral_mono hint.norm hmaj hbound
      _ = D * (T * Real.pi) := by
          rw [integral_const_mul, Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) T,
            integral_univ_inv_one_add_sq, abs_of_pos hT, smul_eq_mul]
      _ ≤ D * Real.pi * (2 * Real.pi * Real.exp (1 / 2)) * (1 + |A| * Real.exp (a / 2)) := by
          have hTle : T ≤ 2 * Real.pi * Real.exp (1 / 2) * (1 + |A| * Real.exp (a / 2)) := by
            simp only [T, X, sepScale]
            have : 0 ≤ |A| * Real.exp (a / 2) := by positivity
            nlinarith
          calc D * (T * Real.pi) = D * Real.pi * T := by ring
            _ ≤ D * Real.pi * (2 * Real.pi * Real.exp (1 / 2) * (1 + |A| * Real.exp (a / 2))) := by
                gcongr
            _ = _ := by ring
  · intro u hu1 hu2
    have hinv := congrFun (Continuous.fourierInv_fourier_eq (continuous_sepFun a A)
      (integrable_sepFun a A) hint) u
    rw [← sepFun_eq_phase hu1 hu2, ← hinv, Real.fourierInv_eq']
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [Real.inner_apply, smul_eq_mul]
    ring_nf

end

end GaloisForLFunctions.RHTower.KuznetsovSeparation
