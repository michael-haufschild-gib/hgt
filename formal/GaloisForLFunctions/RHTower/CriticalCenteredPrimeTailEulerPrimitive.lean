import GaloisForLFunctions.RHTower.CriticalPrimeTailEulerLogPositiveDefinite
import GaloisForLFunctions.RHTower.AnalyticDividedDifference
import GaloisForLFunctions.RHTower.XiCollapseDirichletLeg
import GaloisForLFunctions.RHTower.CompletedPrimeFluxFittingAttachment

/-!
# The pole-cancelled centered prime-tail Euler primitive

The uncentered positive prime-tail source has an exact absolute-convergence wall.  Subtracting the
Lebesgue-density atom `1` at every integer `n ≥ 2` changes the derivative of its Euler primitive to

`ζ'/ζ + ζ - 1`.

This is not a formal cancellation of divergent symbols.  Writing
`G(s) = (s - 1) ζ(s)` with its removable value at `1`, the expression is exactly

`G'/G + dslope G 1 - 1`.

Both terms on the right are holomorphic near `1`; the two opposite pole residues have disappeared.
The value at the former pole is `2γ - 1`.
-/

open Complex Filter Topology LSeries ArithmeticFunction

namespace RHTower

noncomputable section

/-- Coefficient of the zeta tail `ζ(s) - 1`: zero at `0,1`, one from `2` onward. -/
def zetaTailDirichletCoeff (n : ℕ) : ℂ := if 2 ≤ n then 1 else 0

@[simp] theorem zetaTailDirichletCoeff_zero : zetaTailDirichletCoeff 0 = 0 := by
  simp [zetaTailDirichletCoeff]

@[simp] theorem zetaTailDirichletCoeff_one : zetaTailDirichletCoeff 1 = 0 := by
  simp [zetaTailDirichletCoeff]

/-- Divided-log primitive coefficient of the zeta tail. -/
def zetaTailEulerPrimitiveCoeff (n : ℕ) : ℂ :=
  if 2 ≤ n then (Complex.log n)⁻¹ else 0

/-- Exact centered coefficient `(Λ(n)-1)/log n` for `n ≥ 2`. -/
def centeredPrimeTailEulerCoeff (n : ℕ) : ℂ :=
  eulerLogDirichletCoeff n - zetaTailEulerPrimitiveCoeff n

/-- The differentiated centered coefficient is exactly `Λ(n)-1` on `n ≥ 2`. -/
theorem logMul_centeredPrimeTailEulerCoeff (n : ℕ) :
    LSeries.logMul centeredPrimeTailEulerCoeff n =
      (ArithmeticFunction.vonMangoldt n : ℂ) - zetaTailDirichletCoeff n := by
  by_cases hn : 2 ≤ n
  · have hn0 : n ≠ 0 := by omega
    have hlogR : Real.log n ≠ 0 :=
      ne_of_gt (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn)))
    have hlogC : Complex.log n ≠ 0 := by
      rw [← Complex.natCast_log]
      exact Complex.ofReal_ne_zero.mpr hlogR
    rw [LSeries.logMul, centeredPrimeTailEulerCoeff, eulerLogDirichletCoeff,
      zetaTailEulerPrimitiveCoeff, zetaTailDirichletCoeff, if_pos hn, if_pos hn]
    field_simp
  · have hnlt : n < 2 := Nat.lt_of_not_ge hn
    interval_cases n <;>
      simp [LSeries.logMul, centeredPrimeTailEulerCoeff, zetaTailEulerPrimitiveCoeff,
        zetaTailDirichletCoeff, eulerLogDirichletCoeff,
        ArithmeticFunction.vonMangoldt_apply_one]

/-- The divided-log zeta-tail coefficient is uniformly bounded by `2`. -/
theorem norm_zetaTailEulerPrimitiveCoeff_le_two (n : ℕ) :
    ‖zetaTailEulerPrimitiveCoeff n‖ ≤ 2 := by
  rw [zetaTailEulerPrimitiveCoeff]
  split_ifs with hn
  · have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hlogle : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hnR
    have hinv2 : 1 / Real.log 2 < 2 := by
      nth_rewrite 2 [← one_div_one_div 2]
      rw [one_div_lt_one_div]
      · exact lt_of_le_of_lt (by norm_num) Real.log_two_gt_d9
      · exact Real.log_pos (by norm_num)
      · norm_num
    rw [← Complex.natCast_log, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hlogn]
    simpa [one_div] using
      (one_div_le_one_div_of_le (Real.log_pos (by norm_num)) hlogle).trans hinv2.le
  · norm_num

/-- The centered primitive coefficient is uniformly bounded. -/
theorem norm_centeredPrimeTailEulerCoeff_le_three (n : ℕ) :
    ‖centeredPrimeTailEulerCoeff n‖ ≤ 3 := by
  calc
    ‖centeredPrimeTailEulerCoeff n‖
        ≤ ‖eulerLogDirichletCoeff n‖ + ‖zetaTailEulerPrimitiveCoeff n‖ := norm_sub_le _ _
    _ ≤ 1 + 2 := add_le_add (norm_eulerLogDirichletCoeff_le_one n)
      (norm_zetaTailEulerPrimitiveCoeff_le_two n)
    _ = 3 := by norm_num

/-- Absolute-convergence abscissa of the centered primitive is at most `1`. -/
theorem abscissaOfAbsConv_centeredPrimeTailEulerCoeff_le_one :
    LSeries.abscissaOfAbsConv centeredPrimeTailEulerCoeff ≤ 1 := by
  exact LSeries.abscissaOfAbsConv_le_of_le_const
    ⟨3, fun n _ => norm_centeredPrimeTailEulerCoeff_le_three n⟩

/-- Centered prime-tail Euler primitive. -/
def centeredPrimeTailEulerPrimitive (s : ℂ) : ℂ :=
  LSeries centeredPrimeTailEulerCoeff s

/-- The coefficient series obtained by differentiating the centered primitive is summable on
`Re s > 1`. -/
theorem centeredPrimeTailCurrentCoeff_summable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) - zetaTailDirichletCoeff n) s := by
  have habs : LSeries.abscissaOfAbsConv centeredPrimeTailEulerCoeff < (s.re : EReal) :=
    abscissaOfAbsConv_centeredPrimeTailEulerCoeff_le_one.trans_lt (by exact_mod_cast hs)
  have hsum := LSeriesSummable_logMul_of_lt_re habs
  have hcoeff : LSeries.logMul centeredPrimeTailEulerCoeff =
      fun n => (ArithmeticFunction.vonMangoldt n : ℂ) - zetaTailDirichletCoeff n := by
    funext n
    exact logMul_centeredPrimeTailEulerCoeff n
  rw [hcoeff] at hsum
  exact hsum

/-- The zeta-tail Dirichlet series is exactly `ζ(s)-1`. -/
theorem LSeries_zetaTailDirichletCoeff_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries zetaTailDirichletCoeff s = riemannZeta s - 1 := by
  have hone : LSeriesSummable (1 : ℕ → ℂ) s := LSeriesSummable_one_iff.mpr hs
  have hdelta : LSeriesSummable LSeries.delta s := by
    rw [LSeriesSummable]
    apply (summable_congr (fun n => LSeries.term_delta s n)).mpr
    exact (hasSum_ite_eq 1 (1 : ℂ)).summable
  have htail : LSeriesSummable ((1 : ℕ → ℂ) - LSeries.delta) s := hone.sub hdelta
  calc
    LSeries zetaTailDirichletCoeff s = LSeries ((1 : ℕ → ℂ) - LSeries.delta) s := by
      apply LSeries_congr
      intro n hn
      simp only [Pi.sub_apply, Pi.one_apply]
      rcases n with _ | n
      · simp at hn
      · rcases n with _ | n
        · simp [zetaTailDirichletCoeff, LSeries.delta]
        · simp [zetaTailDirichletCoeff, LSeries.delta]
    _ = LSeries (1 : ℕ → ℂ) s - LSeries LSeries.delta s := LSeries_sub hone hdelta
    _ = riemannZeta s - 1 := by rw [LSeries_one_eq_riemannZeta hs, LSeries_delta]; simp

/-- Differentiated centered series equals the difference between the von Mangoldt current and the
zeta tail. -/
theorem LSeries_logMul_centeredPrimeTailEulerCoeff_eq {s : ℂ} (hs : 1 < s.re) :
    LSeries (LSeries.logMul centeredPrimeTailEulerCoeff) s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s - (riemannZeta s - 1) := by
  have hvm : LSeriesSummable (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s :=
    LSeriesSummable_vonMangoldt hs
  have htail : LSeriesSummable zetaTailDirichletCoeff s := by
    have hc := centeredPrimeTailCurrentCoeff_summable hs
    have hsum := hvm.sub hc
    have hcoeff :
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) -
            (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) - zetaTailDirichletCoeff n) =
          zetaTailDirichletCoeff := by
      funext n
      simp
    rw [hcoeff] at hsum
    exact hsum
  rw [show LSeries.logMul centeredPrimeTailEulerCoeff =
      (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) - zetaTailDirichletCoeff by
        funext n
        exact logMul_centeredPrimeTailEulerCoeff n]
  rw [LSeries_sub hvm htail, LSeries_zetaTailDirichletCoeff_eq hs]

/-- Safe-half-plane derivative identity for the centered primitive. -/
theorem hasDerivAt_centeredPrimeTailEulerPrimitive {s : ℂ} (hs : 1 < s.re) :
    HasDerivAt centeredPrimeTailEulerPrimitive
      (logDeriv riemannZeta s + riemannZeta s - 1) s := by
  have habs : LSeries.abscissaOfAbsConv centeredPrimeTailEulerCoeff < (s.re : EReal) :=
    abscissaOfAbsConv_centeredPrimeTailEulerCoeff_le_one.trans_lt (by exact_mod_cast hs)
  have hL := LSeries_hasDerivAt habs
  change HasDerivAt (LSeries centeredPrimeTailEulerCoeff)
    (logDeriv riemannZeta s + riemannZeta s - 1) s
  convert hL using 1
  rw [LSeries_logMul_centeredPrimeTailEulerCoeff_eq hs,
    ← infinitePrimeFlux_eq_vonMangoldtLSeries hs, infinitePrimeFlux]
  ring

/-- Pole-cancelled continuation of the centered current. -/
def centeredPrimeTailCurrentContinuation (s : ℂ) : ℂ :=
  logDeriv zetaResidueUnit s + dslope zetaResidueUnit 1 s - 1

/-- The centered current continuation is holomorphic at the former zeta pole. -/
theorem analyticAt_centeredPrimeTailCurrentContinuation_one :
    AnalyticAt ℂ centeredPrimeTailCurrentContinuation 1 := by
  have hGne : zetaResidueUnit 1 ≠ 0 := by rw [zetaResidueUnit_one]; norm_num
  have hlog : AnalyticAt ℂ (logDeriv zetaResidueUnit) 1 := by
    simpa [logDeriv_apply] using!
      zetaResidueUnit_analyticAt.deriv.div zetaResidueUnit_analyticAt hGne
  have hslope : AnalyticAt ℂ (dslope zetaResidueUnit 1) 1 :=
    analyticAt_dslope_of_analyticAt zetaResidueUnit_analyticAt zetaResidueUnit_analyticAt
  exact (hlog.add hslope).sub analyticAt_const

/-- Exact finite value left by cancellation of the two opposite residues. -/
theorem centeredPrimeTailCurrentContinuation_one :
    centeredPrimeTailCurrentContinuation 1 =
      2 * (Real.eulerMascheroniConstant : ℂ) - 1 := by
  rw [centeredPrimeTailCurrentContinuation, dslope_same, logDeriv_zetaResidueUnit_one,
    deriv_zetaResidueUnit_one]
  ring

/-- On the safe half-plane the continuation is the differentiated centered Euler primitive. -/
theorem centeredPrimeTailCurrentContinuation_eq {s : ℂ} (hs : 1 < s.re) :
    centeredPrimeTailCurrentContinuation s =
      logDeriv riemannZeta s + riemannZeta s - 1 := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hG : zetaResidueUnit s ≠ 0 := by
    rw [zetaResidueUnit, Function.update_of_ne hs1]
    exact mul_ne_zero (sub_ne_zero.mpr hs1) (riemannZeta_ne_zero_of_one_lt_re hs)
  rw [centeredPrimeTailCurrentContinuation, dslope_of_ne _ hs1, slope_def_field,
    zetaResidueUnit_one, logDeriv_zeta_eq hs1 hG]
  have hunit : zetaResidueUnit s = (s - 1) * riemannZeta s := by
    simp [zetaResidueUnit, Function.update_of_ne hs1]
  rw [hunit]
  field_simp [sub_ne_zero.mpr hs1]
  ring

/-- The centered Euler primitive differentiates to the pole-cancelled continuation. -/
theorem hasDerivAt_centeredPrimeTailEulerPrimitive_eq_continuation {s : ℂ}
    (hs : 1 < s.re) :
    HasDerivAt centeredPrimeTailEulerPrimitive (centeredPrimeTailCurrentContinuation s) s := by
  rw [centeredPrimeTailCurrentContinuation_eq hs]
  exact hasDerivAt_centeredPrimeTailEulerPrimitive hs

end

end RHTower
