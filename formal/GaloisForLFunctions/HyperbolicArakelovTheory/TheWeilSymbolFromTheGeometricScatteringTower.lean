import GaloisForLFunctions.RHTower.EisensteinMaassSelbergLineModel
import GaloisForLFunctions.RHTower.EisensteinResonantStateNorm
import GaloisForLFunctions.RHTower.ArchimedeanGammaModule
import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.HTGeometry.LSeriesRightLimit
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic

/-!
# The completed symbol from truncated geometric diagonals

At cusp height one, the Maass–Selberg diagonal determines a difference of
completed logarithmic derivatives. Its shifted tower has a canonical
archimedean counterterm; the remaining error is a vanishing Euler tail.
The diagonal is defined by the actual truncated Eisenstein integral and
its cusp coefficients, independently of the zero divisor.
-/

open Complex Filter Topology MeasureTheory
open scoped BigOperators
open RHTower GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower

noncomputable section

/-- The finite part of the truncated geometric pairing at cusp height one. -/
def geometricDiagonal (u : ℂ) : ℂ :=
  (msA u ^ 2 - msB u ^ 2) / (4 * u * msA u * msB u) -
    truncatedPairing 1 u u / (2 * msA u * msB u)

private theorem msB_ne_zero {u : ℂ} (hu : 1 / 2 < u.re) : msB u ≠ 0 := by
  unfold msB reflectedCompletedLambda
  apply mul_ne_zero
  · exact Complex.Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  · exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)

/-- The actual geometric diagonal is the unit difference of the completed symbol. -/
theorem geometricDiagonal_eq_of_im_pos {u : ℂ} (hre : 1 / 2 < u.re) (him : 0 < u.im) :
    geometricDiagonal u = logDeriv reflectedCompletedLambda (2 * u) -
      logDeriv reflectedCompletedLambda (1 + 2 * u) := by
  have hu := mem_eisensteinLineDomain_of_re hre him
  have hu0 := ne_zero_of_mem_eisensteinLineDomain hu
  have hA := msA_ne_zero_of_re hre
  have hB := msB_ne_zero hre
  rw [geometricDiagonal, truncatedPairing_diag hu (le_refl 1)]
  simp only [msDiag, Complex.ofReal_one, Complex.one_cpow, Complex.log_one,
    mul_one, mul_zero, sub_zero, logDeriv_apply]
  change _ = deriv reflectedCompletedLambda (2 * u) / msB u -
    deriv reflectedCompletedLambda (1 + 2 * u) / msA u
  field_simp
  ring

theorem geometricDiagonal_conj (u : ℂ) :
    geometricDiagonal (starRingEnd ℂ u) = starRingEnd ℂ (geometricDiagonal u) := by
  have hP : truncatedPairing 1 (starRingEnd ℂ u) (starRingEnd ℂ u) =
      starRingEnd ℂ (truncatedPairing 1 u u) := by
    unfold truncatedPairing
    rw [← integral_conj]
    simp only [map_mul, truncatedLineModel_conj]
  simp only [geometricDiagonal, map_sub, map_div₀, map_mul, map_pow, map_ofNat,
    msA_conj, msB_conj, hP]

private theorem completedLogDeriv_conj {s : ℂ} (hs : s.im ≠ 0) :
    logDeriv reflectedCompletedLambda (starRingEnd ℂ s) =
      starRingEnd ℂ (logDeriv reflectedCompletedLambda s) := by
  simp only [logDeriv_apply, deriv_reflectedCompletedLambda_conj hs,
    reflectedCompletedLambda_conj, map_div₀]

/-- Schwarz symmetry extends the geometric identity to both nonreal chambers. -/
theorem geometricDiagonal_eq {u : ℂ} (hre : 1 / 2 < u.re) (him : u.im ≠ 0) :
    geometricDiagonal u = logDeriv reflectedCompletedLambda (2 * u) -
      logDeriv reflectedCompletedLambda (1 + 2 * u) := by
  rcases lt_or_gt_of_ne him with hi | hi
  · have hc := geometricDiagonal_eq_of_im_pos (u := starRingEnd ℂ u)
      (by simpa using hre) (by simpa using neg_pos.mpr hi)
    have hi2 : (2 * u).im ≠ 0 := by simp [him]
    have hi1 : (1 + 2 * u).im ≠ 0 := by simp [him]
    rw [geometricDiagonal_conj,
      show (2 : ℂ) * starRingEnd ℂ u = starRingEnd ℂ (2 * u) by simp,
      show (1 : ℂ) + 2 * starRingEnd ℂ u = starRingEnd ℂ (1 + 2 * u) by simp,
      completedLogDeriv_conj hi2, completedLogDeriv_conj hi1, ← map_sub] at hc
    exact (starRingEnd ℂ).injective hc
  · exact geometricDiagonal_eq_of_im_pos hre hi

/-- The finite tower of actual geometric diagonals. -/
def geometricTower (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, geometricDiagonal ((s + n) / 2)

theorem geometricTower_eq {s : ℂ} (hs : 1 < s.re) (him : s.im ≠ 0) (N : ℕ) :
    geometricTower s N = logDeriv reflectedCompletedLambda s -
      logDeriv reflectedCompletedLambda (s + N) := by
  induction N with
  | zero => simp [geometricTower]
  | succ N ih =>
    have hre : 1 / 2 < ((s + N) / 2).re := by
      simp only [Complex.div_ofNat_re, Complex.add_re, Complex.natCast_re]
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have hi : ((s + N) / 2).im ≠ 0 := by simpa using div_ne_zero him (by norm_num : (2 : ℝ) ≠ 0)
    rw [geometricTower, Finset.sum_range_succ]
    change geometricTower s N + geometricDiagonal ((s + N) / 2) = _
    rw [ih, geometricDiagonal_eq hre hi]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [show (2 : ℂ) * ((s + N) / 2) = s + N by ring,
      show (1 : ℂ) + (s + N) = s + (N + 1) by ring]
    ring

theorem completedLogDeriv_eq {s : ℂ} (hs : 1 < s.re) :
    logDeriv reflectedCompletedLambda s = logDeriv Complex.Gammaℝ s -
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  have hs0 : 0 < s.re := lt_trans zero_lt_one hs
  have hs1 : s ≠ 1 := by
    intro h
    simp [h] at hs
  unfold reflectedCompletedLambda
  rw [logDeriv_mul s (Complex.Gammaℝ_ne_zero_of_re_pos hs0)
    (riemannZeta_ne_zero_of_one_lt_re hs)
    (GaloisForLFunctions.differentiableAt_Gammaℝ hs0)
    (differentiableAt_riemannZeta hs1), logDeriv_riemannZeta_eq_neg_LSeries hs]
  rfl

/-- Gamma normalization leaves exactly the shifted Euler tail. -/
theorem gammaNormalizedTower_eq {s : ℂ} (hs : 1 < s.re) (him : s.im ≠ 0) (N : ℕ) :
    geometricTower s N + logDeriv Complex.Gammaℝ (s + N) =
      logDeriv reflectedCompletedLambda s +
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + N) := by
  have hsN : 1 < (s + N).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [Nat.cast_nonneg (α := ℝ) N]
  rw [geometricTower_eq hs him, completedLogDeriv_eq hsN]
  ring

/-- Uniform horizontal decay of the Euler error, with no restriction on imaginary parts. -/
theorem tendsto_eulerTail {α : Type*} {l : Filter α} {w : α → ℂ}
    (hw : Tendsto (fun a => (w a).re) l atTop) :
    Tendsto (fun a => LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (w a))
      l (𝓝 0) := by
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (2 : ℂ)) (by norm_num)
  simpa using tendsto_LSeries_of_re_atTop (σ₀ := 2) hsum.norm hw

/-- The absolute Euler mass on a line of absolute convergence. -/
def eulerMajorant (c : ℝ) : ℝ :=
  ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖

theorem eulerMajorant_nonneg (c : ℝ) : 0 ≤ eulerMajorant c :=
  tsum_nonneg fun _ => norm_nonneg _

/-- Exponential control of the entire Euler tail, uniform on every vertical line. -/
theorem norm_eulerTail_le {c : ℝ} (hc : 1 < c) {s : ℂ} (hs : c ≤ s.re) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ ≤
      (2 : ℝ) ^ (c - s.re) * eulerMajorant c := by
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ))
    (by simpa using hc)
  have hsum' := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := s) (hc.trans_le hs)
  have hb : ∀ n : ℕ,
      ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ ≤
        (2 : ℝ) ^ (c - s.re) *
          ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ := by
    intro n
    rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | hn
    · simp
    · simp
    · exact norm_term_le_two_pow hs hn
  calc ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖
      ≤ ∑' n, ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖ :=
        norm_tsum_le_tsum_norm hsum'.norm
    _ ≤ ∑' n, (2 : ℝ) ^ (c - s.re) *
        ‖LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (c : ℂ) n‖ :=
      hsum'.norm.tsum_le_tsum hb (hsum.norm.mul_left _)
    _ = (2 : ℝ) ^ (c - s.re) * eulerMajorant c := by rw [tsum_mul_left]; rfl

/-- The infinite geometric tower recovers the completed symbol after Gamma normalization. -/
theorem tendsto_gammaNormalizedTower {s : ℂ} (hs : 1 < s.re) (him : s.im ≠ 0) :
    Tendsto (fun N : ℕ => geometricTower s N + logDeriv Complex.Gammaℝ (s + N))
      atTop (𝓝 (logDeriv reflectedCompletedLambda s)) := by
  have hr : Tendsto (fun N : ℕ => (s + N).re) atTop atTop := by
    simp only [Complex.add_re, Complex.natCast_re]
    exact Filter.tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have h := (tendsto_eulerTail hr).const_add (logDeriv reflectedCompletedLambda s)
  rw [add_zero] at h
  exact h.congr fun N => (gammaNormalizedTower_eq hs him N).symm

/-- The archimedean logarithmic symbol fixed by the real Gamma factor. -/
def archimedeanSymbol (s : ℂ) : ℂ :=
  -((Real.log Real.pi : ℝ) : ℂ) / 2 + Complex.log (s / 2) / 2

/-- A scalar subtraction on each vertical line, independent of its spectral height. -/
def robinCounterterm (x : ℝ) : ℂ := archimedeanSymbol (x : ℂ)

private theorem norm_log_sub_log_re {s : ℂ} (hs : 0 < s.re) :
    ‖Complex.log s - Complex.log (s.re : ℂ)‖ ≤ |s.im| / s.re := by
  have hslit : ∀ z : ℂ, s.re ≤ z.re → z ∈ Complex.slitPlane :=
    fun z hz => Complex.mem_slitPlane_iff.mpr (Or.inl (hs.trans_le hz))
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := {z : ℂ | s.re ≤ z.re}) (f := Complex.log) (C := 1 / s.re)
    (fun z hz => Complex.differentiableAt_log (hslit z hz))
    (fun z hz => by
      rw [Complex.deriv_log (hslit z hz), norm_inv, one_div]
      exact inv_le_inv₀ hs (hz.trans ((le_abs_self z.re).trans (Complex.abs_re_le_norm z))))
    (convex_halfSpace_re_ge s.re)
    (x := (s.re : ℂ)) (y := s) (by simp) le_rfl
  have hdist : ‖s - (s.re : ℂ)‖ = |s.im| := by
    rw [show s - (s.re : ℂ) = (s.im : ℂ) * I by
      conv_lhs => rw [← Complex.re_add_im s]
      ring, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hdist] at h
  simpa only [one_div, div_eq_mul_inv, mul_comm] using h

theorem norm_gamma_sub_archimedeanSymbol {s : ℂ} (hs : 4 ≤ s.re) :
    ‖logDeriv Complex.Gammaℝ s - archimedeanSymbol s‖ ≤ 3 / s.re := by
  have hre : 0 < s.re := by linarith
  have hn : s.re ≤ ‖s‖ := (le_abs_self _).trans (Complex.abs_re_le_norm s)
  have hh : 2 ≤ ‖s / 2‖ := by rw [norm_div, Complex.norm_ofNat]; linarith
  have h := norm_digamma_sub_log_le_of_re_pos
    (s := s / 2) (by simp; linarith) hh
  rw [GaloisForLFunctions.logDeriv_Gammaℝ hre, gammaRealLogConnection, archimedeanSymbol]
  rw [show -((Real.log Real.pi : ℝ) : ℂ) / 2 + Complex.digamma (s / 2) / 2 -
      (-((Real.log Real.pi : ℝ) : ℂ) / 2 + Complex.log (s / 2) / 2) =
      (Complex.digamma (s / 2) - Complex.log (s / 2)) / 2 by ring]
  rw [norm_div, Complex.norm_ofNat]
  calc ‖Complex.digamma (s / 2) - Complex.log (s / 2)‖ / 2
      ≤ (3 / ‖s / 2‖) / 2 := div_le_div_of_nonneg_right h (by norm_num)
    _ = 3 / ‖s‖ := by rw [norm_div, Complex.norm_ofNat]; ring
    _ ≤ 3 / s.re := div_le_div_of_nonneg_left (by norm_num) hre hn

/-- The only spectral-height dependence of the scalar subtraction is a controlled error. -/
theorem norm_gamma_sub_robinCounterterm {s : ℂ} (hs : 4 ≤ s.re) :
    ‖logDeriv Complex.Gammaℝ s - robinCounterterm s.re‖ ≤
      (3 + |s.im| / 2) / s.re := by
  have hlog := norm_log_sub_log_re (s := s / 2) (by simp; linarith)
  have harch : ‖archimedeanSymbol s - robinCounterterm s.re‖ ≤ |s.im| / (2 * s.re) := by
    rw [archimedeanSymbol, robinCounterterm, archimedeanSymbol]
    rw [show -((Real.log Real.pi : ℝ) : ℂ) / 2 + Complex.log (s / 2) / 2 -
        (-((Real.log Real.pi : ℝ) : ℂ) / 2 + Complex.log ((s.re : ℂ) / 2) / 2) =
        (Complex.log (s / 2) - Complex.log ((s.re : ℂ) / 2)) / 2 by ring]
    simp only [Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.ofReal_div,
      Complex.ofReal_ofNat, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hlog
    rw [norm_div, Complex.norm_ofNat]
    calc ‖Complex.log (s / 2) - Complex.log ((s.re : ℂ) / 2)‖ / 2
        ≤ (|s.im| / 2 / (s.re / 2)) / 2 := div_le_div_of_nonneg_right hlog (by norm_num)
      _ = |s.im| / (2 * s.re) := by ring
  calc ‖logDeriv Complex.Gammaℝ s - robinCounterterm s.re‖
      ≤ ‖logDeriv Complex.Gammaℝ s - archimedeanSymbol s‖ +
        ‖archimedeanSymbol s - robinCounterterm s.re‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 3 / s.re + |s.im| / (2 * s.re) :=
      add_le_add (norm_gamma_sub_archimedeanSymbol hs) harch
    _ = (3 + |s.im| / 2) / s.re := by ring

/-- The geometrically defined tower with its scalar Robin term and two boundary poles. -/
def renormalizedTower (s : ℂ) (N : ℕ) : ℂ :=
  geometricTower s N + robinCounterterm (s.re + N) + 1 / s + 1 / (s - 1)

/-- The error splits into the shifted Euler tail and the archimedean normalization error. -/
theorem renormalizedTower_sub_symbol {s : ℂ} (hs : 1 < s.re) (him : s.im ≠ 0) (N : ℕ) :
    renormalizedTower s N - logDeriv xi s =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + N) -
        (logDeriv Complex.Gammaℝ (s + N) - robinCounterterm (s.re + N)) := by
  have h := gammaNormalizedTower_eq hs him N
  rw [completedLogDeriv_eq hs] at h
  rw [renormalizedTower, logDeriv_xi_eq_arithmetic hs]
  simp only [one_div]
  linear_combination h

end

end GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower
