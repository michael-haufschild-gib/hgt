import GaloisForLFunctions.ConstituentTheoryOfTheZeros.NoAbsolutelyConvergentDirichletSeriesIsAConstituent
import GaloisForLFunctions.HTGeometry.DirichletBohrSpectrum
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.PSeries

/-!
# A bounded constituent lives in the Bohr strip

Let `F` be bounded and holomorphic on `Re s > x` and given by an absolutely convergent Dirichlet
series `Σ a(n) n^{−s}` far to the right.

* **Bohr coefficients on every line** (`bohrCoefficient_line_of_bounded`): for `σ > x` the mean
  value of `F(σ + it) n^{it}` is `a(n) n^{−σ}`; the mean is carried from a line of absolute
  convergence by Cauchy's theorem on rectangles, whose horizontal sides are bounded.
* **Bessel** (`sum_norm_sq_le_of_bounded`): `Σ_{n ≤ N} ‖a(n)‖² n^{−2σ} ≤ sup ‖F‖²`.
* **Bohr's inequality** (`lSeriesSummable_of_bounded`, `eq_LSeries_of_bounded`): the series
  converges absolutely, to `F`, on `Re s > x + ½`.

With the theorem on absolutely convergent series: **if `x < 0`, a bounded Dirichlet series on
`Re s > x` whose zeros there are zeros of `ξ` has no zero** (`ne_zero_of_bounded_of_zeros_subset_xi`).
So a constituent of the bounded class with a zero can be bounded only on half-planes `Re s > x`
with `0 ≤ x < ½`, and its series cannot converge absolutely at any point left of the critical
line: it lives in the strip between its abscissa of boundedness and its abscissa of absolute
convergence.
-/

open Complex Filter Topology Set MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.InfiniteRankPurityTheory

variable {a : ℕ → ℂ} {F : ℂ → ℂ} {x u₀ M : ℝ}

/-! ### Vertical lines -/

theorem re_line (σ t : ℝ) : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp

theorem continuous_line_of_differentiableOn (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re})
    {σ : ℝ} (hσ : x < σ) : Continuous fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * I) := by
  have hopen : IsOpen {z : ℂ | x < z.re} := isOpen_lt continuous_const continuous_re
  refine continuous_iff_continuousAt.mpr fun t => ?_
  have hmem : ((σ : ℂ) + (t : ℂ) * I) ∈ {z : ℂ | x < z.re} := by
    show x < ((σ : ℂ) + (t : ℂ) * I).re
    rw [re_line]
    exact hσ
  have hca : ContinuousAt F ((σ : ℂ) + (t : ℂ) * I) :=
    (hF.differentiableAt (hopen.mem_nhds hmem)).continuousAt
  exact ContinuousAt.comp (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) hca
    (by fun_prop : Continuous fun t : ℝ => (σ : ℂ) + (t : ℂ) * I).continuousAt

/-- A bounded Dirichlet series is almost periodic on every vertical line of its half-plane. -/
theorem isBohrAlmostPeriodic_line_of_bounded (hsum : LSeriesSummable a u₀)
    (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re}) (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M)
    (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries a z) {σ : ℝ} (hσ : x < σ) :
    _root_.HTGeometry.IsBohrAlmostPeriodic fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * I) := by
  have hu : σ ≤ max σ u₀ + 1 := by linarith [le_max_left σ u₀]
  have hu₀ : u₀ < max σ u₀ + 1 := by linarith [le_max_right σ u₀]
  have h := isStripAlmostPeriodicOn_of_bounded_LSeries (l' := σ) (u := max σ u₀ + 1) hσ hu hu₀
    hsum hF hM hFL
  intro ε hε
  obtain ⟨L, hL, hτ⟩ := h ε hε
  refine ⟨L, hL, fun y => ?_⟩
  obtain ⟨τ, hτm, hτz⟩ := hτ y
  refine ⟨τ, hτm, fun t => ?_⟩
  have hz := hτz ((σ : ℂ) + (t : ℂ) * I) (by
    rw [re_line, abs_le]
    constructor <;> linarith)
  have e : (σ : ℂ) + ((t + τ : ℝ) : ℂ) * I = (σ : ℂ) + (t : ℂ) * I + (τ : ℂ) * I := by
    push_cast
    ring
  rw [e]
  exact hz

/-! ### Bohr coefficients -/

theorem log_succ_injective : Function.Injective fun k : ℕ => Real.log ((k : ℝ) + 1) :=
  fun m n h => by
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h' := Real.log_injOn_pos hm hn h
    exact_mod_cast add_right_cancel h'

/-- A term of the series as a multiple of an exponential. -/
theorem term_succ_eq_exp (a : ℕ → ℂ) (z : ℂ) (k : ℕ) :
    LSeries.term a z (k + 1) =
      a (k + 1) * Complex.exp (-((Real.log ((k : ℝ) + 1) : ℝ) : ℂ) * z) := by
  have hk : (((k + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast k.succ_ne_zero
  have hlog : Complex.log ((k + 1 : ℕ) : ℂ) = ((Real.log ((k : ℝ) + 1) : ℝ) : ℂ) := by
    rw [show (((k + 1 : ℕ) : ℂ)) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_log (by positivity)]
  rw [LSeries.term_of_ne_zero k.succ_ne_zero, Complex.cpow_def_of_ne_zero hk, hlog, div_eq_mul_inv,
    ← Complex.exp_neg]
  congr 2
  ring

/-- **The Bohr coefficients on a line of absolute convergence.** -/
theorem bohrCoefficient_line_of_summable (hsum : LSeriesSummable a u₀)
    (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re}) (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M)
    (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries a z) {u₁ : ℝ} (hx : x < u₁) (hu : u₀ < u₁)
    (n : ℕ) :
    bohrCoefficient (fun t : ℝ => F ((u₁ : ℂ) + (t : ℂ) * I)) (-Real.log ((n : ℝ) + 1)) =
      a (n + 1) * ((Real.exp (-Real.log ((n : ℝ) + 1) * u₁) : ℝ) : ℂ) := by
  refine bohrCoefficient_dirichlet_line (fun k => a (k + 1)) (fun k => Real.log ((k : ℝ) + 1)) F
    log_succ_injective (continuous_line_of_differentiableOn hF hx)
    (isBohrAlmostPeriodic_line_of_bounded hsum hF hM hFL hx) n fun ε hε => ?_
  -- the tail of the series at `u₀` bounds the tail on the line
  set g : ℕ → ℝ := fun k => ‖LSeries.term a u₀ (k + 1)‖ with hg
  have hgs : Summable g := (summable_nat_add_iff 1).mpr hsum.norm
  obtain ⟨N, hN⟩ := ((tendsto_sum_nat_add g).eventually (ge_mem_nhds hε)).exists_forall_of_atTop
  refine ⟨max N n + 1, by omega, fun t => ?_⟩
  set z : ℂ := (u₁ : ℂ) + (t : ℂ) * I with hz
  have hzre : ((u₀ : ℂ)).re ≤ z.re := by
    rw [hz, re_line, ofReal_re]
    exact hu.le
  have hzs : LSeriesSummable a z := hsum.of_re_le_re hzre
  have hz1 : Summable fun k : ℕ => LSeries.term a z (k + 1) := (summable_nat_add_iff 1).mpr hzs
  have hLS : LSeries a z = ∑' k : ℕ, LSeries.term a z (k + 1) := by
    unfold LSeries
    rw [hzs.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  have hsplit := hz1.sum_add_tsum_nat_add (max N n + 1)
  have hfin : (∑ k ∈ Finset.range (max N n + 1),
      a (k + 1) * Complex.exp (-((Real.log ((k : ℝ) + 1) : ℝ) : ℂ) * z)) =
      ∑ k ∈ Finset.range (max N n + 1), LSeries.term a z (k + 1) :=
    Finset.sum_congr rfl fun k _ => (term_succ_eq_exp a z k).symm
  rw [hFL z (by rw [hz, re_line]; exact hu), hLS, hfin, ← hsplit, add_sub_cancel_left]
  have htail : Summable fun k : ℕ => ‖LSeries.term a z (k + (max N n + 1) + 1)‖ :=
    ((summable_nat_add_iff (max N n + 1)).mpr hz1).norm
  have hgt : Summable fun k : ℕ => g (k + (max N n + 1)) :=
    (summable_nat_add_iff (max N n + 1)).mpr hgs
  refine (norm_tsum_le_tsum_norm htail).trans ((htail.tsum_le_tsum (fun k => ?_) hgt).trans
    (hN (max N n + 1) (by omega)))
  exact LSeries.norm_term_le_of_re_le_re a hzre _

/-- The window averages of `F(s) e^{Ls}` on two vertical lines of the half-plane of boundedness
have the same limit: Cauchy's theorem on the rectangle between them. -/
theorem tendsto_windowAverage_line_sub (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re})
    (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M) {σ u₁ : ℝ} (hσ : x < σ) (hσu : σ ≤ u₁) {L : ℝ}
    (hL : 0 ≤ L) :
    Tendsto (fun T : ℝ =>
      windowAverage (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * I) *
        Complex.exp ((L : ℂ) * ((σ : ℂ) + (t : ℂ) * I))) T -
      windowAverage (fun t : ℝ => F ((u₁ : ℂ) + (t : ℂ) * I) *
        Complex.exp ((L : ℂ) * ((u₁ : ℂ) + (t : ℂ) * I))) T) atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (σ : ℂ) (by rwa [ofReal_re]))
  set G : ℂ → ℂ := fun s => F s * Complex.exp ((L : ℂ) * s) with hG
  have hGd : DifferentiableOn ℂ G {z : ℂ | x < z.re} :=
    hF.mul (Differentiable.differentiableOn (by fun_prop))
  -- the bound on the strip between the lines
  have hGb : ∀ z : ℂ, σ ≤ z.re → z.re ≤ u₁ → ‖G z‖ ≤ M * Real.exp (L * u₁) := by
    intro z h1 h2
    rw [hG, norm_mul, Complex.norm_exp]
    have hre : ((L : ℂ) * z).re = L * z.re := by simp
    rw [hre]
    exact mul_le_mul (hM z (by linarith)) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h2 hL))
      (Real.exp_pos _).le hM0
  set C : ℝ := M * Real.exp (L * u₁) with hC
  -- for `T > 0` the difference of the vertical integrals is the difference of the horizontal ones
  have hkey : ∀ T : ℝ, 0 < T →
      ‖(∫ t in (0 : ℝ)..T, G ((σ : ℂ) + (t : ℂ) * I)) -
        ∫ t in (0 : ℝ)..T, G ((u₁ : ℂ) + (t : ℂ) * I)‖ ≤ 2 * (C * (u₁ - σ)) := by
    intro T hT
    have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G (σ : ℂ)
      ((u₁ : ℂ) + (T : ℂ) * I) (hGd.mono fun z hz => by
        have h1 : z.re ∈ Set.uIcc ((σ : ℂ)).re (((u₁ : ℂ) + (T : ℂ) * I)).re := hz.1
        rw [ofReal_re, re_line, Set.uIcc_of_le hσu] at h1
        show x < z.re
        linarith [h1.1])
    rw [re_line, ofReal_re, ofReal_im] at hrect
    have him : ((u₁ : ℂ) + (T : ℂ) * I).im = T := by simp
    rw [him] at hrect
    have hb1 : ‖∫ r in σ..u₁, G ((r : ℂ) + ((0 : ℝ) : ℂ) * I)‖ ≤ C * |u₁ - σ| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => by
        rw [Set.uIoc_of_le hσu] at hr
        exact hGb _ (by simp; exact hr.1.le) (by simp; exact hr.2)
    have hb2 : ‖∫ r in σ..u₁, G ((r : ℂ) + (T : ℂ) * I)‖ ≤ C * |u₁ - σ| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => by
        rw [Set.uIoc_of_le hσu] at hr
        exact hGb _ (by simp; exact hr.1.le) (by simp; exact hr.2)
    rw [abs_of_nonneg (sub_nonneg.mpr hσu)] at hb1 hb2
    have hsolve : (∫ t in (0 : ℝ)..T, G ((σ : ℂ) + (t : ℂ) * I)) -
        ∫ t in (0 : ℝ)..T, G ((u₁ : ℂ) + (t : ℂ) * I) =
        -I * ((∫ r in σ..u₁, G ((r : ℂ) + ((0 : ℝ) : ℂ) * I)) -
          ∫ r in σ..u₁, G ((r : ℂ) + (T : ℂ) * I)) := by
      have h := hrect
      simp only [smul_eq_mul] at h
      have hI : I * I = -1 := I_mul_I
      linear_combination (-I) * h + ((∫ t in (0 : ℝ)..T, G ((σ : ℂ) + (t : ℂ) * I)) -
        ∫ t in (0 : ℝ)..T, G ((u₁ : ℂ) + (t : ℂ) * I)) * hI
    rw [hsolve, norm_mul, norm_neg, norm_I, one_mul]
    exact (norm_sub_le _ _).trans (by linarith)
  -- divide by `T`
  refine squeeze_zero_norm' (a := fun T : ℝ => T⁻¹ * (2 * (C * (u₁ - σ)))) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hsub : windowAverage (fun t : ℝ => G ((σ : ℂ) + (t : ℂ) * I)) T -
        windowAverage (fun t : ℝ => G ((u₁ : ℂ) + (t : ℂ) * I)) T =
        T⁻¹ • ((∫ t in (0 : ℝ)..T, G ((σ : ℂ) + (t : ℂ) * I)) -
          ∫ t in (0 : ℝ)..T, G ((u₁ : ℂ) + (t : ℂ) * I)) := by
      unfold windowAverage
      rw [smul_sub]
    show ‖windowAverage (fun t : ℝ => G ((σ : ℂ) + (t : ℂ) * I)) T -
      windowAverage (fun t : ℝ => G ((u₁ : ℂ) + (t : ℂ) * I)) T‖ ≤ _
    rw [hsub, norm_smul, Real.norm_of_nonneg (inv_pos.mpr hT).le]
    exact mul_le_mul_of_nonneg_left (hkey T hT) (inv_pos.mpr hT).le
  · have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).mul_const (2 * (C * (u₁ - σ)))
    rwa [zero_mul] at h

/-- The window average of `F(σ + it) e^{L(σ + it)}` is `e^{Lσ}` times the modulated window
average of the line function. -/
theorem windowAverage_line_eq (σ L T : ℝ) :
    windowAverage (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * I) *
      Complex.exp ((L : ℂ) * ((σ : ℂ) + (t : ℂ) * I))) T =
    ((Real.exp (L * σ) : ℝ) : ℂ) *
      windowAverage (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * I) * bohrChar (-L) t) T := by
  unfold windowAverage
  rw [← intervalIntegral.integral_const_mul, Complex.real_smul, Complex.real_smul, ← mul_assoc,
    mul_comm ((Real.exp (L * σ) : ℝ) : ℂ), mul_assoc, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  show F ((σ : ℂ) + (t : ℂ) * I) * Complex.exp ((L : ℂ) * ((σ : ℂ) + (t : ℂ) * I)) =
    ((Real.exp (L * σ) : ℝ) : ℂ) * (F ((σ : ℂ) + (t : ℂ) * I) * bohrChar (-L) t)
  unfold bohrChar
  rw [Complex.ofReal_exp, mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- **The Bohr coefficients on every line of the half-plane of boundedness.** For `σ > x` the
mean value of `F(σ + it) n^{it}` is `a(n) n^{−σ}`. -/
theorem bohrCoefficient_line_of_bounded (hsum : LSeriesSummable a u₀)
    (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re}) (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M)
    (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries a z) {σ : ℝ} (hσ : x < σ) (n : ℕ) :
    bohrCoefficient (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * I)) (-Real.log ((n : ℝ) + 1)) =
      a (n + 1) * ((Real.exp (-Real.log ((n : ℝ) + 1) * σ) : ℝ) : ℂ) := by
  set L : ℝ := Real.log ((n : ℝ) + 1) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) n])
  set u₁ : ℝ := max σ u₀ + 1 with hu₁
  have hσu : σ ≤ u₁ := by linarith [le_max_left σ u₀]
  have hxu : x < u₁ := lt_of_lt_of_le hσ hσu
  have hu₀u : u₀ < u₁ := by linarith [le_max_right σ u₀]
  -- the limits of the two modulated window averages
  have hlimσ := tendsto_windowAverage_bohrCoefficient (continuous_line_of_differentiableOn hF hσ)
    (isBohrAlmostPeriodic_line_of_bounded hsum hF hM hFL hσ) (-L)
  have hlimu := tendsto_windowAverage_bohrCoefficient (continuous_line_of_differentiableOn hF hxu)
    (isBohrAlmostPeriodic_line_of_bounded hsum hF hM hFL hxu) (-L)
  have hdiff := tendsto_windowAverage_line_sub hF hM hσ hσu hL0
  simp only [windowAverage_line_eq] at hdiff
  have hlim := (hlimσ.const_mul ((Real.exp (L * σ) : ℝ) : ℂ)).sub
    (hlimu.const_mul ((Real.exp (L * u₁) : ℝ) : ℂ))
  have heq := tendsto_nhds_unique hlim hdiff
  rw [bohrCoefficient_line_of_summable hsum hF hM hFL hxu hu₀u n] at heq
  have hσne : ((Real.exp (L * σ) : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hprod : ((Real.exp (L * u₁) : ℝ) : ℂ) * ((Real.exp (-L * u₁) : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.exp_add]
    simp
  have hprodσ : ((Real.exp (L * σ) : ℝ) : ℂ) * ((Real.exp (-L * σ) : ℝ) : ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.exp_add]
    simp
  refine mul_left_cancel₀ hσne ?_
  linear_combination heq + a (n + 1) * hprod - a (n + 1) * hprodσ

/-! ### Bessel's inequality and Bohr's inequality -/

/-- **Bessel's inequality for a bounded Dirichlet series.** -/
theorem sum_norm_sq_le_of_bounded (hsum : LSeriesSummable a u₀)
    (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re}) (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M)
    (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries a z) {σ : ℝ} (hσ : x < σ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (‖a (n + 1)‖ * Real.exp (-Real.log ((n : ℝ) + 1) * σ)) ^ 2 ≤ M ^ 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (σ : ℂ) (by rwa [ofReal_re]))
  have hfc := continuous_line_of_differentiableOn hF hσ
  have hfa := isBohrAlmostPeriodic_line_of_bounded hsum hF hM hFL hσ
  have hinj : Set.InjOn (fun n : ℕ => -Real.log ((n : ℝ) + 1)) (Finset.range N) :=
    fun m _ n _ h => log_succ_injective (neg_injective h)
  have hbessel := bohr_bessel hfc hfa ((Finset.range N).image fun n : ℕ => -Real.log ((n : ℝ) + 1))
  rw [Finset.sum_image hinj] at hbessel
  have hterm : ∀ n ∈ Finset.range N,
      ‖bohrCoefficient (fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * I)) (-Real.log ((n : ℝ) + 1))‖ ^ 2 =
        (‖a (n + 1)‖ * Real.exp (-Real.log ((n : ℝ) + 1) * σ)) ^ 2 := fun n _ => by
    rw [bohrCoefficient_line_of_bounded hsum hF hM hFL hσ n, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  rw [Finset.sum_congr rfl hterm] at hbessel
  refine hbessel.trans ?_
  -- the mean of `‖F‖²` is at most `M²`
  set h : ℝ → ℂ := fun t => F ((σ : ℂ) + (t : ℂ) * I) *
    (starRingEnd ℂ) (F ((σ : ℂ) + (t : ℂ) * I)) with hh
  have hconjc : Continuous fun t : ℝ => (starRingEnd ℂ) (F ((σ : ℂ) + (t : ℂ) * I)) :=
    Complex.continuous_conj.comp hfc
  have hconja : _root_.HTGeometry.IsBohrAlmostPeriodic
      fun t : ℝ => (starRingEnd ℂ) (F ((σ : ℂ) + (t : ℂ) * I)) := by
    intro ε hε
    obtain ⟨L, hL, hτ⟩ := hfa ε hε
    refine ⟨L, hL, fun y => ?_⟩
    obtain ⟨τ, hτm, hτb⟩ := hτ y
    refine ⟨τ, hτm, fun t => ?_⟩
    rw [← map_sub, RCLike.norm_conj]
    exact hτb t
  have hhc : Continuous h := hfc.mul hconjc
  have hha : _root_.HTGeometry.IsBohrAlmostPeriodic h :=
    isBohrAlmostPeriodic_mul hfc hfa hconjc hconja
  have hlim := tendsto_windowAverage_bohrMean hhc hha
  have hbound : ∀ᶠ T : ℝ in atTop, ‖windowAverage h T‖ ≤ M ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    unfold windowAverage
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.mpr hT).le]
    have hint : ‖∫ t in (0 : ℝ)..T, h t‖ ≤ M ^ 2 * |T - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => by
        rw [hh, norm_mul, RCLike.norm_conj, sq]
        have hb := hM ((σ : ℂ) + (t : ℂ) * I) (by rw [re_line]; exact hσ)
        exact mul_le_mul hb hb (norm_nonneg _) hM0
    rw [sub_zero, abs_of_pos hT] at hint
    calc T⁻¹ * ‖∫ t in (0 : ℝ)..T, h t‖ ≤ T⁻¹ * (M ^ 2 * T) :=
          mul_le_mul_of_nonneg_left hint (inv_pos.mpr hT).le
      _ = M ^ 2 := by
          field_simp
  exact (re_le_norm _).trans (le_of_tendsto hlim.norm hbound)

/-- **Bohr's inequality.** A Dirichlet series bounded on `Re s > x` converges absolutely on
`Re s > x + ½`. -/
theorem lSeriesSummable_of_bounded (hsum : LSeriesSummable a u₀)
    (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re}) (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M)
    (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries a z) {y : ℝ} (hy : x + 1 / 2 < y) :
    LSeriesSummable a y := by
  -- a line `σ₀` with `x < σ₀` and `σ₀ + ½ < y`
  set σ₀ : ℝ := (x + y - 1 / 2) / 2 with hσ₀
  have hσx : x < σ₀ := by rw [hσ₀]; linarith
  set δ : ℝ := y - σ₀ with hδ
  have hδ2 : 1 / 2 < δ := by rw [hδ, hσ₀]; linarith
  set f : ℕ → ℝ := fun n => ‖a (n + 1)‖ * Real.exp (-Real.log ((n : ℝ) + 1) * σ₀) with hf
  set g : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ (-δ) with hg
  have hf0 : ∀ n, 0 ≤ f n := fun n => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  have hg0 : ∀ n, 0 ≤ g n := fun n => Real.rpow_nonneg (by positivity) _
  have hfs : Summable fun n => f n ^ (2 : ℝ) := by
    refine summable_of_sum_range_le (fun n => Real.rpow_nonneg (hf0 n) _) (c := M ^ 2) fun N => ?_
    have h := sum_norm_sq_le_of_bounded hsum hF hM hFL hσx N
    simpa only [Real.rpow_two] using h
  have hgs : Summable fun n => g n ^ (2 : ℝ) := by
    have h : Summable fun n : ℕ => ((n : ℝ)) ^ (-(2 * δ)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have h' := (summable_nat_add_iff 1).mpr h
    refine h'.congr fun n => ?_
    rw [hg, ← Real.rpow_mul (by positivity)]
    push_cast
    congr 1
    ring
  have hfg := Real.summable_mul_of_Lp_Lq_of_nonneg Real.HolderConjugate.two_two hf0 hg0 hfs hgs
  -- the terms of the series at `y`
  rw [LSeriesSummable, ← summable_nat_add_iff 1]
  refine Summable.of_norm (hfg.congr fun n => ?_)
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [LSeries.norm_term_eq, if_neg n.succ_ne_zero, ofReal_re, hf, hg]
  have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by push_cast; rfl
  have hexp : Real.exp (-Real.log ((n : ℝ) + 1) * σ₀) = ((n : ℝ) + 1) ^ (-σ₀) := by
    rw [Real.rpow_def_of_pos hn]
    congr 1
    ring
  rw [hcast, hexp, div_eq_mul_inv, ← Real.rpow_neg hn.le, mul_assoc, ← Real.rpow_add hn]
  congr 2
  rw [hδ]
  ring

/-- Right of `x + ½` the bounded function is its Dirichlet series. -/
theorem eq_LSeries_of_bounded (hsum : LSeriesSummable a u₀)
    (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re}) (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M)
    (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries a z) {s : ℂ} (hs : x + 1 / 2 < s.re) :
    F s = LSeries a s := by
  set y : ℝ := (x + 1 / 2 + s.re) / 2 with hy
  have hy1 : x + 1 / 2 < y := by rw [hy]; linarith
  have hy2 : y < s.re := by rw [hy]; linarith
  have hsumy := lSeriesSummable_of_bounded hsum hF hM hFL hy1
  have hUo : IsOpen {z : ℂ | y < z.re} := isOpen_lt continuous_const continuous_re
  have hUc : IsPreconnected {z : ℂ | y < z.re} := (convex_halfSpace_re_gt y).isPreconnected
  have hFd : DifferentiableOn ℂ F {z : ℂ | y < z.re} := hF.mono fun z hz => by
    show x < z.re
    have : y < z.re := hz
    linarith
  have hLd := differentiableOn_LSeries_of_summable hsumy
  set z₀ : ℂ := ((max y u₀ + 1 : ℝ) : ℂ) with hz₀
  have hz₀re : z₀.re = max y u₀ + 1 := by rw [hz₀, ofReal_re]
  have hz₀U : z₀ ∈ {z : ℂ | y < z.re} := by
    show y < z₀.re
    rw [hz₀re]
    linarith [le_max_left y u₀]
  have hev : F =ᶠ[𝓝 z₀] LSeries a := by
    have hopen : {z : ℂ | u₀ < z.re} ∈ 𝓝 z₀ :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by
        show u₀ < z₀.re
        rw [hz₀re]
        linarith [le_max_right y u₀])
    filter_upwards [hopen] with z hz
    exact hFL z hz
  exact (hFd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq (hLd.analyticOnNhd hUo) hUc
    hz₀U hev hy2

/-! ### Constituents of the bounded class -/

/-- **A bounded Dirichlet series on a half-plane `Re s > x`, `x < 0`, is no constituent with a
zero.** If `F` is bounded and holomorphic on `Re s > x` with `x < 0`, is given by an absolutely
convergent Dirichlet series far to the right, does not vanish identically, and every zero of `F`
in `Re s > x` is a zero of `ξ`, then `F` has no zero in `Re s > x`. -/
theorem ne_zero_of_bounded_of_zeros_subset_xi (hsum : LSeriesSummable a u₀)
    (hF : DifferentiableOn ℂ F {z : ℂ | x < z.re}) (hM : ∀ z : ℂ, x < z.re → ‖F z‖ ≤ M)
    (hFL : ∀ z : ℂ, u₀ < z.re → F z = LSeries a z) (hx : x < 0) {n : ℕ} (hn : a (n + 1) ≠ 0)
    (hzero : ∀ s : ℂ, x < s.re → F s = 0 → xi s = 0) {s : ℂ} (hs : x < s.re) : F s ≠ 0 := by
  intro h0
  -- the zeros lie on the critical line
  obtain ⟨z₁, hz₁re, hz₁⟩ := exists_LSeries_ne_zero hsum hn (y := max u₀ x + 1)
    (by linarith [le_max_left u₀ x])
  have hz₁u : u₀ < z₁.re := by rw [hz₁re]; linarith [le_max_left u₀ x]
  have hz₁x : x < z₁.re := by rw [hz₁re]; linarith [le_max_right u₀ x]
  have hre : s.re = 1 / 2 := re_eq_half_of_zeros_subset_xi hsum hF hM hFL
    ⟨z₁, hz₁x, by rw [hFL z₁ hz₁u]; exact hz₁⟩ hzero hs h0
  -- absolute convergence at a point left of the line
  set y : ℝ := x / 2 + 1 / 2 with hy
  have hy1 : x + 1 / 2 < y := by rw [hy]; linarith
  have hy2 : y < 1 / 2 := by rw [hy]; linarith
  have hsumy := lSeriesSummable_of_bounded hsum hF hM hFL hy1
  have hne := LSeries_ne_zero_of_zeros_subset_xi hsumy hn
    (fun z hz hz0 => hzero z (by linarith) (by
      rw [eq_LSeries_of_bounded hsum hF hM hFL (by linarith)]
      exact hz0)) (s := s) (by rw [hre]; exact hy2)
  exact hne (by rw [← eq_LSeries_of_bounded hsum hF hM hFL (by rw [hre]; linarith)]; exact h0)

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
