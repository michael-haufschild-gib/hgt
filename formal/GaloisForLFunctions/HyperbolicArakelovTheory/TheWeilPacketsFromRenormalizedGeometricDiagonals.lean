import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeilSymbolFromTheGeometricScatteringTower
import GaloisForLFunctions.RHTower.WeilLineIntegralAnyAbscissa

/-!
# Weil packets from renormalized geometric diagonals

The finite energies below use the actual Maass–Selberg pairings, a scalar
archimedean subtraction, and the two boundary poles. Their limit is the
full Weil functional on compactly supported C² autocorrelations. The
identification uses an integrable error bound, not a positivity assumption.
-/

open Complex Filter Topology MeasureTheory Set
open RHTower Zeta23 Zeta23.WeilEF
open RHTower.WeilLineIntegral RHTower.WeilLineAnyAbscissa

namespace GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower

noncomputable section

/-- The packet energy of the finite geometric tower on the line `Re s = 3/2`. -/
def geometricWeilEnergy (f : ℝ → ℂ) (N : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
    lineF (EF.weilTest f f) (3 / 2) t * renormalizedTower ((3 / 2 : ℂ) + t * I) N

private theorem lamC_mangoldt :
    WeilHerglotz.lamC (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) =
      fun n => (ArithmeticFunction.vonMangoldt n : ℂ) := by
  funext n
  unfold WeilHerglotz.lamC
  split_ifs with hn
  · rfl
  · have h : ArithmeticFunction.vonMangoldt n = 0 := by interval_cases n <;> simp
    simp [h]

private theorem summable_mangoldt (σ : ℝ) (hσ : 1 < σ) :
    Summable fun n : ℕ => |(ArithmeticFunction.vonMangoldt n : ℝ)| / (n : ℝ) ^ σ := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σ : ℂ))
    (by simpa using hσ)
  refine h.norm.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, Complex.norm_real, Real.norm_eq_abs]

private theorem weilFunction_mangoldt {s : ℂ} (hs : 1 < s.re) :
    WeilHerglotz.weilFunction (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) s =
      logDeriv xi s := by
  rw [weilFunction_eq _ (lt_trans zero_lt_one hs), lamC_mangoldt,
    logDeriv_xi_eq_arithmetic hs, gPair]
  simp only [sub_zero, one_div]
  ring

private theorem continuous_xi_symbol {c : ℝ} (hc : 1 < c) :
    Continuous (fun t : ℝ => logDeriv xi ((c : ℂ) + t * I)) := by
  have hpath : Continuous (fun t : ℝ => (c : ℂ) + t * I) := by fun_prop
  have hd : Continuous (deriv xi) :=
    (xi_differentiable.contDiff (n := 1)).continuous_deriv le_rfl
  simp only [logDeriv_apply]
  exact (hd.comp hpath).div (xi_differentiable.continuous.comp hpath)
    (fun t => xi_ne_zero_of_one_lt_re (by simpa using hc))

/-- An analytic expression used only to prove measurability of the geometric energy. -/
private def analyticTower (s : ℂ) (N : ℕ) : ℂ :=
  logDeriv xi s - logDeriv xi (s + N) + robinCounterterm (s.re + N) +
    1 / (s + N) + 1 / (s + N - 1)

private theorem renormalizedTower_eq_analytic {s : ℂ} (hs : 1 < s.re)
    (him : s.im ≠ 0) (N : ℕ) : renormalizedTower s N = analyticTower s N := by
  have hsN : 1 < (s + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  have h := renormalizedTower_sub_symbol hs him N
  rw [analyticTower, logDeriv_xi_eq_arithmetic hsN]
  simp only [one_div] at h ⊢
  linear_combination h

private theorem continuous_analyticTower {c : ℝ} (hc : 1 < c) (N : ℕ) :
    Continuous (fun t : ℝ => analyticTower ((c : ℂ) + t * I) N) := by
  have hcN : 1 < c + N := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hshift : ∀ t : ℝ, ((c : ℂ) + t * I) + N = ((c + N : ℝ) : ℂ) + t * I := by
    intro t
    push_cast
    ring
  unfold analyticTower
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  simp_rw [hshift]
  refine (((continuous_xi_symbol hc).sub (continuous_xi_symbol hcN)).add
    continuous_const |>.add ?_).add ?_
  · refine continuous_const.div (by fun_prop) fun t h => ?_
    have hh := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero,
      Complex.zero_re] at hh
    linarith
  · refine continuous_const.div (by fun_prop) fun t h => ?_
    have hh := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero,
      add_zero, Complex.one_re, Complex.zero_re] at hh
    linarith

end

end GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
