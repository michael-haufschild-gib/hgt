import GaloisForLFunctions.RHTower.SquareRootAbelSqrtContinuation
import GaloisForLFunctions.RHTower.SquareRootAbelDirichletTransfer
import GaloisForLFunctions.RHTower.ZetaPoleSplit
import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldResidualODEClosure
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeHeadAsymptotic
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The complete signed divisor source cannot have square-root growth

A hypothetical `O(sqrt M)` bound continues the actual Chebyshev-error
L-series to the positive half-plane. The entire pole-filled zeta would then
satisfy a holomorphic first-order ODE there. Its unconditional nontrivial
zero and its value one at one contradict analytic zero propagation.

The conclusion is a closed obstruction to the smaller growth bound, not a
proof or falsification of RH, whose route requires a linear bound.
-/

noncomputable section
open Filter Topology Finset Complex
namespace RHTower

/-- The Chebyshev error coefficients, without the constant Euler edge. -/
def chebyshevDefectDirichletCoefficient (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) - 1

private theorem source_summable {s : ℂ} (hs : 1<s.re) :
    LSeriesSummable chebyshevDefectDirichletCoefficient s := by
  exact (ArithmeticFunction.LSeriesSummable_vonMangoldt hs).sub
    (LSeriesSummable_one_iff.mpr hs)

/-- The literal arithmetic series is the pole-cancelled logarithmic derivative. -/
theorem LSeries_chebyshevDefectDirichletCoefficient {s : ℂ} (hs : 1<s.re) :
    LSeries chebyshevDefectDirichletCoefficient s =
      -(deriv riemannZeta s / riemannZeta s)-riemannZeta s := by
  change LSeries ((fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) - 1) s = _
  rw [LSeries_sub (ArithmeticFunction.LSeriesSummable_vonMangoldt hs)
    (LSeriesSummable_one_iff.mpr hs),
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    LSeries_one_eq_riemannZeta hs, neg_div]

/-- A nontrivial zero unconditionally obstructs analytic continuation of the actual
Chebyshev error L-series to the entire positive half-plane. -/
theorem not_exists_analytic_chebyshevDefect_positive_extension :
    ¬ ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F {s : ℂ | 0<s.re} ∧
      ∀ s : ℂ, 2<s.re → F s=LSeries chebyshevDefectDirichletCoefficient s := by
  rintro ⟨F,hF,hFar⟩
  let U : Set ℂ := {s : ℂ | 0<s.re}
  let G : ℂ → ℂ := fun s => F s+zetaRegularized s
  let H : ℂ → ℂ := fun s => deriv zetaPoleUnit s+G s*zetaPoleUnit s
  have hG : AnalyticOnNhd ℂ G U := fun s hs =>
    (hF s hs).add (differentiable_zetaRegularized.analyticAt s)
  have hZ : AnalyticOnNhd ℂ zetaPoleUnit U := fun s _ =>
    differentiable_zetaPoleUnit.analyticAt s
  have hH : AnalyticOnNhd ℂ H U := by
    intro s hs
    exact ((differentiable_zetaPoleUnit.analyticAt s).deriv).add
      ((hG s hs).mul (hZ s hs))
  have hHzero : ∀ s : ℂ, 2<s.re → H s=0 := by
    intro s hs
    have hs1 : 1<s.re := by linarith
    have hsne : s≠1 := by intro he; subst s; norm_num at hs
    have hz := riemannZeta_ne_zero_of_one_lt_re hs1
    have hZne := zetaPoleUnit_ne_zero hsne hz
    have hGs : G s = -(deriv zetaPoleUnit s / zetaPoleUnit s) := by
      dsimp [G]
      rw [hFar s hs,LSeries_chebyshevDefectDirichletCoefficient hs1,
        zetaRegularized_of_ne hsne,neg_zeta_logDeriv_eq hsne hz]
      ring
    dsimp [H]
    rw [hGs,neg_mul,div_mul_cancel₀ _ hZne,add_neg_cancel]
  have hfreq : ∃ᶠ s in 𝓝[≠] (3:ℂ), H s=0 := by
    have hnear : ∀ᶠ s in 𝓝 (3:ℂ), 2<s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    exact (Eventually.filter_mono nhdsWithin_le_nhds
      (hnear.mono (fun s hs => hHzero s hs))).frequently
  have hzero := hH.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_halfSpace_re_gt (0:ℝ)).isPreconnected
    (show (3:ℂ)∈U by norm_num [U]) hfreq
  have hODE : ∀ s ∈ U, deriv zetaPoleUnit s = -G s*zetaPoleUnit s := by
    intro s hs
    have hh := hzero hs
    change deriv zetaPoleUnit s+G s*zetaPoleUnit s=0 at hh
    rw [neg_mul]
    exact eq_neg_of_add_eq_zero_left hh
  obtain ⟨ρ,hρ0,hρ1,hρzero⟩ := exists_riemannZeta_zero_mem_openStrip
  have hρne : ρ≠1 := by intro he; subst ρ; norm_num at hρ1
  exact false_of_analytic_firstOrderODE_zero_and_nonzero
    (isOpen_lt continuous_const Complex.continuous_re)
    (convex_halfSpace_re_gt (0:ℝ)).isPreconnected hZ hG hODE hρ0
    (show (1:ℂ)∈U by norm_num [U])
    (by rw [zetaPoleUnit_of_ne hρne,hρzero,mul_zero])
    (by rw [zetaPoleUnit_one]; exact one_ne_zero)

/-- The actual square-root Abel prefixes cannot have square-root growth. -/
theorem not_exists_sqrt_bound_squareRootAbelPrefix_chebyshevDefect :
    ¬ ∃ C : ℝ, ∀ n : ℕ,
      ‖squareRootAbelPrefix chebyshevDefectDirichletCoefficient n‖ ≤
        C*Real.sqrt ((n:ℝ)+1) := by
  rintro ⟨C,hC⟩
  let D : ℝ := max C 0
  have hD : 0≤D := le_max_right _ _
  have hA : ∀ n, ‖squareRootAbelPrefix chebyshevDefectDirichletCoefficient n‖ ≤
      D*Real.sqrt ((n:ℝ)+1) := fun n =>
    (hC n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))
  have hlin : ∀ n, ‖squareRootAbelPrefix chebyshevDefectDirichletCoefficient n‖ ≤
      D*((n:ℝ)+1) := by
    intro n
    apply (hA n).trans
    apply mul_le_mul_of_nonneg_left _ hD
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have hn := Nat.cast_nonneg (α:=ℝ) n
    nlinarith
  apply not_exists_analytic_chebyshevDefect_positive_extension
  refine ⟨squareRootAbelDirichletSum (squareRootAbelPrefix chebyshevDefectDirichletCoefficient),
    analyticOnNhd_squareRootAbelDirichletSum_of_sqrt_bound hD hA,?_⟩
  intro s hs
  exact squareRootAbelDirichletSum_eq_LSeries hD hlin (by linarith)
    (source_summable (by linarith))

private theorem source_partial (k : ℕ) :
    (∑ n ∈ Icc 1 k,chebyshevDefectDirichletCoefficient n) =
      ((chebyshevPsi k-(k:ℝ):ℝ):ℂ) := by
  simp [chebyshevDefectDirichletCoefficient,chebyshevPsi,sum_sub_distrib]

/-- The generic analytic prefix is exactly the actual complete divisor source,
with its explicit Euler edge removed. -/
theorem squareRootAbelPrefix_chebyshevDefect_eq_source (N : ℕ) :
    squareRootAbelPrefix chebyshevDefectDirichletCoefficient N =
      (((∑ d ∈ Icc 1 (N+1),mobiusDivisorDilationChannel (N+1) d)-
        2*Real.eulerMascheroniConstant*(Real.sqrt ((N:ℝ)+1)-1):ℝ):ℂ) := by
  have htel : (∑ k ∈ Icc 1 N,(Real.sqrt (k+1:ℕ)-Real.sqrt k)) =
      Real.sqrt ((N:ℝ)+1)-1 := by
    rcases Nat.eq_zero_or_pos N with rfl|hN
    · simp
    · simpa using sum_sqrt_succ_sub_sqrt_Icc_general hN
  have hreal : (∑ k ∈ Icc 1 N,(Real.sqrt (k+1:ℕ)-Real.sqrt k)*(chebyshevPsi k-k)) =
      (∑ d ∈ Icc 1 (N+1),mobiusDivisorDilationChannel (N+1) d)-
        2*Real.eulerMascheroniConstant*(Real.sqrt ((N:ℝ)+1)-1) := by
    rw [sum_mobiusDivisorDilationChannel_eq_psiDefect_abel,Ico_add_one_right_eq_Icc]
    simp only [psiDefect,mul_add,sum_add_distrib]
    rw [← sum_mul,htel]
    ring
  rw [← hreal]
  unfold squareRootAbelPrefix
  simp_rw [source_partial]
  push_cast
  rfl

/-- Unconditionally, the complete signed arithmetic source is not O(sqrt M).
This does not exclude the O(M) bound needed by the RH route. -/
theorem not_exists_sqrt_bound_sum_mobiusDivisorDilationChannel :
    ¬ ∃ C : ℝ, ∀ M : ℕ,
      |∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d| ≤ C*Real.sqrt M := by
  rintro ⟨C,hC⟩
  apply not_exists_sqrt_bound_squareRootAbelPrefix_chebyshevDefect
  refine ⟨|C|+2*|Real.eulerMascheroniConstant|,?_⟩
  intro n
  rw [squareRootAbelPrefix_chebyshevDefect_eq_source,Complex.norm_real,Real.norm_eq_abs]
  have hroot : 1≤Real.sqrt ((n:ℝ)+1) := by
    have hn := Nat.cast_nonneg (α:=ℝ) n
    calc
      1 = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have hs : |∑ d ∈ Icc 1 (n+1),mobiusDivisorDilationChannel (n+1) d| ≤
      |C| *Real.sqrt ((n:ℝ)+1) := by
    have hc := (hC (n+1)).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _))
    simpa using hc
  calc
    _ ≤ |∑ d ∈ Icc 1 (n+1),mobiusDivisorDilationChannel (n+1) d|+
        |2*Real.eulerMascheroniConstant*(Real.sqrt ((n:ℝ)+1)-1)| := abs_sub _ _
    _ ≤ _ := by
      rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2),
        abs_of_nonneg (sub_nonneg.mpr hroot)]
      nlinarith [abs_nonneg Real.eulerMascheroniConstant]

end RHTower
