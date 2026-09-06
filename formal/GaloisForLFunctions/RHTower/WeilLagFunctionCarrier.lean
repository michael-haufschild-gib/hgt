import GaloisForLFunctions.RHTower.WeilLagFunctionGram

/-!
# The lag kernel as the reflection-twisted form on the zero carrier

On the carrier of functions on the zero copies, put the Frobenius vectors `v_x(ρ) = x^{ρ−½}` and
the reflection-twisted bilinear form `B(f, g) = Σ_ρ f(ρ) g(1−ρ)/(ρ(1−ρ))`.  Unconditionally
`B(v_x, v_y) = Φ(log x − log y)`: the lag kernel is the Gram form of the Frobenius orbit under
`B`.  RH is equivalent to `B` being positive semidefinite on the span of the Frobenius orbit,
and under RH the reflection `ρ ↦ 1 − ρ` is complex conjugation, so `B` is the Hermitian form
`Σ_ρ |f(ρ)|²/|ρ|²`.  This is the exact shape of the Hodge/positivity datum a geometric producer
must supply, expressed on the carrier the corpus's Deninger lane uses.
-/

open Real Filter Topology

namespace RHTower

noncomputable section

/-- The Frobenius vector at scale `x`: `ρ ↦ x^{ρ−½}`. -/
def frobeniusVector (x : ℝ) (q : XiZeroCopy) : ℂ := (x : ℂ) ^ ((q.1 : ℂ) - 1 / 2)

/-- The reflection-twisted form `B(f, g) = Σ_ρ f(ρ) g(1−ρ)/(ρ(1−ρ))`. -/
def reflectForm (f g : XiZeroCopy → ℂ) : ℂ :=
  ∑' q : XiZeroCopy, lagWeight q * f q * g (xiZeroCopyReflectEquiv q)

theorem frobeniusVector_eq_exp {x : ℝ} (hx : 0 < x) (q : XiZeroCopy) :
    frobeniusVector x q = Complex.exp ((Real.log x : ℂ) * ((q.1 : ℂ) - 1 / 2)) := by
  unfold frobeniusVector
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]

theorem frobeniusVector_reflect {y : ℝ} (hy : 0 < y) (q : XiZeroCopy) :
    frobeniusVector y (xiZeroCopyReflectEquiv q)
      = Complex.exp (-(Real.log y : ℂ) * ((q.1 : ℂ) - 1 / 2)) := by
  rw [frobeniusVector_eq_exp hy, xiZeroCopy_reflect_val]
  congr 1
  ring

/-- **The lag kernel is the Gram form of the Frobenius orbit.** -/
theorem reflectForm_frobeniusVector {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    reflectForm (frobeniusVector x) (frobeniusVector y)
      = weilLagFunction (Real.log x - Real.log y) := by
  unfold reflectForm weilLagFunction
  congr 1
  funext q
  rw [frobeniusVector_eq_exp hx, frobeniusVector_reflect hy]
  unfold lagWeight
  rw [mul_assoc, ← Complex.exp_add]
  have : (Real.log x : ℂ) * ((q.1 : ℂ) - 1 / 2) + -(Real.log y : ℂ) * ((q.1 : ℂ) - 1 / 2)
      = ((Real.log x - Real.log y : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2) := by
    push_cast; ring
  rw [this]
  ring

theorem norm_frobeniusVector_le {x : ℝ} (hx : 0 < x) (q : XiZeroCopy) :
    ‖frobeniusVector x q‖ ≤ Real.exp (|Real.log x| / 2) := by
  rw [frobeniusVector_eq_exp hx, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : ((Real.log x : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = Real.log x * ((q.1 : ℂ).re - 1 / 2) := by
    simp [Complex.mul_re]
  rw [hre]
  have h1 := xiZeroCopy_re_pos q
  have h2 := xiZeroCopy_re_lt_one q
  have h3 : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  calc Real.log x * ((q.1 : ℂ).re - 1 / 2) ≤ |Real.log x * ((q.1 : ℂ).re - 1 / 2)| := le_abs_self _
    _ = |Real.log x| * |(q.1 : ℂ).re - 1 / 2| := abs_mul _ _
    _ ≤ |Real.log x| * (1 / 2) := by gcongr
    _ = |Real.log x| / 2 := by ring

theorem summable_reflectForm_term {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (a b : ℂ) :
    Summable fun q : XiZeroCopy =>
      lagWeight q * (a * frobeniusVector x q) * (b * frobeniusVector y (xiZeroCopyReflectEquiv q)) := by
  have hy' : 0 < y := hy
  refine (summable_norm_lagWeight.mul_left
    (‖a‖ * ‖b‖ * (Real.exp (|Real.log x| / 2) * Real.exp (|Real.log y| / 2)))).of_norm_bounded
    fun q => ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  have h1 := norm_frobeniusVector_le hx q
  have h2 : ‖frobeniusVector y (xiZeroCopyReflectEquiv q)‖ ≤ Real.exp (|Real.log y| / 2) := by
    rw [frobeniusVector_reflect hy', Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : ((-(Real.log y : ℂ)) * ((q.1 : ℂ) - 1 / 2)).re
        = -Real.log y * ((q.1 : ℂ).re - 1 / 2) := by simp [Complex.mul_re]
    rw [hre]
    have h1 := xiZeroCopy_re_pos q
    have h2 := xiZeroCopy_re_lt_one q
    have h3 : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    calc -Real.log y * ((q.1 : ℂ).re - 1 / 2) ≤ |(-Real.log y) * ((q.1 : ℂ).re - 1 / 2)| :=
          le_abs_self _
      _ = |Real.log y| * |(q.1 : ℂ).re - 1 / 2| := by rw [abs_mul, abs_neg]
      _ ≤ |Real.log y| * (1 / 2) := by gcongr
      _ = |Real.log y| / 2 := by ring
  calc ‖lagWeight q‖ * (‖a‖ * ‖frobeniusVector x q‖) *
        (‖b‖ * ‖frobeniusVector y (xiZeroCopyReflectEquiv q)‖)
      ≤ ‖lagWeight q‖ * (‖a‖ * Real.exp (|Real.log x| / 2)) * (‖b‖ * Real.exp (|Real.log y| / 2)) := by
        gcongr
    _ = ‖a‖ * ‖b‖ * (Real.exp (|Real.log x| / 2) * Real.exp (|Real.log y| / 2)) * ‖lagWeight q‖ := by
        ring

/-- A finite combination of Frobenius vectors. -/
def frobeniusCombination (S : Finset ℝ) (c : ℝ → ℝ) (q : XiZeroCopy) : ℂ :=
  ∑ x ∈ S, (c x : ℂ) * frobeniusVector x q

/-- The form on a Frobenius combination is the lag Gram form. -/
theorem reflectForm_frobeniusCombination (S : Finset ℝ) (hS : ∀ x ∈ S, 0 < x) (c : ℝ → ℝ) :
    reflectForm (frobeniusCombination S c) (frobeniusCombination S c) = (lagGramForm S c : ℂ) := by
  classical
  unfold reflectForm frobeniusCombination lagGramForm lagGramKernel
  have hterm : ∀ q : XiZeroCopy, lagWeight q * (∑ x ∈ S, (c x : ℂ) * frobeniusVector x q) *
      (∑ y ∈ S, (c y : ℂ) * frobeniusVector y (xiZeroCopyReflectEquiv q))
      = ∑ x ∈ S, ∑ y ∈ S, lagWeight q * ((c x : ℂ) * frobeniusVector x q) *
          ((c y : ℂ) * frobeniusVector y (xiZeroCopyReflectEquiv q)) := by
    intro q
    rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  simp_rw [hterm]
  rw [Summable.tsum_finsetSum fun x hx => summable_sum fun y hy =>
    summable_reflectForm_term (hS x hx) (hS y hy) _ _]
  push_cast
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Summable.tsum_finsetSum fun y hy => summable_reflectForm_term (hS x hx) (hS y hy) _ _]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [← weilLagFunction_eq_ofReal, ← reflectForm_frobeniusVector (hS x hx) (hS y hy)]
  unfold reflectForm
  rw [← tsum_mul_left]
  congr 1
  funext q
  ring

/-- **RH ⟺ the reflection-twisted form is positive semidefinite on the Frobenius orbit** (points
of the positive reals; the positive rationals, the principal divisors of `Spec ℤ`, suffice). -/
theorem riemannHypothesis_iff_reflectForm_nonneg :
    RiemannHypothesis ↔ ∀ (S : Finset ℝ) (c : ℝ → ℝ), (∀ x ∈ S, 0 < x) →
      0 ≤ (reflectForm (frobeniusCombination S c) (frobeniusCombination S c)).re := by
  constructor
  · intro h S c hS
    rw [reflectForm_frobeniusCombination S hS c, Complex.ofReal_re]
    exact lagGramForm_nonneg_of_riemannHypothesis h S c
  · intro h
    rw [riemannHypothesis_iff_integerLag_le_sharp]
    intro n hn
    have hne : (1 : ℝ) ≠ (n : ℝ) := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hS : ∀ x ∈ ({(1 : ℝ), (n : ℝ)} : Finset ℝ), 0 < x := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact one_pos
      · exact_mod_cast (by omega : 0 < n)
    have := h {(1 : ℝ), (n : ℝ)} (fun x => if x = 1 then 1 else -1) hS
    rw [reflectForm_frobeniusCombination _ hS _, Complex.ofReal_re,
      lagGramForm_pair hn (by simp) (by simp [hne.symm])] at this
    linarith

end

end RHTower
