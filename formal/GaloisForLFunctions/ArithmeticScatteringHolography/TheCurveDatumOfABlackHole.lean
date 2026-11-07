import GaloisForLFunctions.ArithmeticScatteringHolography.TheKreinFluxLaw
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheCurveChainOfTheInnerFactor
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheDefectOfAGraphIsTwiceItsDegree

/-!
# The curve datum of a black hole

A black hole with `(q, t)` has a curve datum of rank two, whether it comes from a curve or not
(`genusOneDatum`). So the corpus of curve data speaks about it, and two identifications follow.

* **The Krein square is the degree form.** `𝒬(x, y) = deg(y - x F)`, the norm of the Frobenius endomorphism
  (`kreinSquare_eq_endDeg`), and half the Castelnuovo–Severi defect of the graph class
  (`krein_eq_half_defect`). So the proof of Hasse's bound by the positivity of the degree is the statement that
  `𝒬` is a Lyapunov functional for the ringdown. On a fake, the degree form is indefinite: the same algebra with no
  geometry to force the sign.
* **The Bode integral.** The mean of `log |P|` on the universal circle is the inner mass, the sum of the excess
  rates: `log⁺ |a/√q| = 2 log q · (¼ - rate(a))⁺` (`bode_integral`, `posLog_eq_rate_deficit`). So the log-mean
  has a bulk reading: it is the total deficit of damping below the universal rate, and it vanishes exactly under
  universal damping (`bode_eq_zero_iff`).
-/

open Complex Finset Filter Topology MeasureTheory
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

open ArithmeticCastelnuovoSeveri ArithmeticInnerFunctionTheory

/-- The curve datum with two given eigenvalues `a, b`, closed under conjugation with `ab = q`. -/
def datumOfRoots (q : ℝ) (hq : 1 < q) (a b : ℂ) (hp : a * b = q)
    (hconj : (conj a = a ∧ conj b = b) ∨ (conj a = b ∧ conj b = a)) : CurveDatum (Fin 2) := by
  classical
  have hr : (Real.sqrt q : ℂ) * (Real.sqrt q : ℂ) = (q : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hr0 : (Real.sqrt q : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
    exact_mod_cast this.ne'
  exact
    { q := q
      one_lt_q := hq
      β := ![a / Real.sqrt q, b / Real.sqrt q]
      conjPerm := if conj a = a ∧ conj b = b then 1 else Equiv.swap 0 1
      β_conjPerm := by
        intro i
        by_cases h : conj a = a ∧ conj b = b
        · rw [if_pos h]
          fin_cases i <;> simp [h.1, h.2, Complex.conj_ofReal]
        · rw [if_neg h]
          obtain ⟨h1, h2⟩ := hconj.resolve_left h
          fin_cases i <;> simp [h1, h2, Complex.conj_ofReal]
      fePerm := Equiv.swap 0 1
      β_fePerm := by
        intro i
        fin_cases i
        · simp
          field_simp
          rw [mul_comm b a, hp, pow_two, hr]
        · simp
          field_simp
          rw [hp, pow_two, hr] }

variable {q : ℝ} (hq : 1 < q) {a b : ℂ} (hp : a * b = q)
  (hconj : (conj a = a ∧ conj b = b) ∨ (conj a = b ∧ conj b = a))

theorem datumOfRoots_q : (datumOfRoots q hq a b hp hconj).q = q := rfl

theorem datumOfRoots_β : (datumOfRoots q hq a b hp hconj).β = ![a / Real.sqrt q, b / Real.sqrt q] := rfl

/-- The inner mass of the datum: the Bode integral. -/
theorem innerMass_datumOfRoots :
    innerMass (datumOfRoots q hq a b hp hconj) =
      Real.posLog ‖a / Real.sqrt q‖ + Real.posLog ‖b / Real.sqrt q‖ := by
  unfold innerMass
  rw [Fin.sum_univ_two, datumOfRoots_β]
  simp

/-- The polynomial `P` on the universal circle: with `v = √q w`, `P(w) = 1 - (t/√q) v + v²`. -/
theorem lPoly_datumOfRoots {t : ℝ} (hs : a + b = t) (v : ℂ) :
    lPoly (datumOfRoots q hq a b hp hconj) v = 1 - (t / Real.sqrt q) * v + v ^ 2 := by
  have hr : (Real.sqrt q : ℂ) * (Real.sqrt q : ℂ) = (q : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hr0 : (Real.sqrt q : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
    exact_mod_cast this.ne'
  unfold lPoly
  rw [Fin.prod_univ_two, datumOfRoots_β]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [← hs]
  field_simp
  linear_combination (v * v) * hp - (v * v) * hr

include hq hp hconj in
/-- **The Bode integral.** The mean of `log |P|` on the universal circle is the inner mass. -/
theorem bode_integral {t : ℝ} (hs : a + b = t) :
    Real.circleAverage (fun v : ℂ => Real.log ‖1 - (t / Real.sqrt q) * v + v ^ 2‖) 0 1 =
      Real.posLog ‖a / Real.sqrt q‖ + Real.posLog ‖b / Real.sqrt q‖ := by
  rw [← innerMass_datumOfRoots hq hp hconj, ← circleAverage_log_norm_lPoly]
  congr 1
  funext v
  rw [lPoly_datumOfRoots hq hp hconj hs]

/-- The excess of a mode, in terms of its rate: `log⁺ |a/√q| = 2 log q · (¼ - rate)⁺`. -/
theorem posLog_eq_rate_deficit {a : ℂ} (hq : 1 < q) (ha : a ≠ 0) :
    Real.posLog ‖a / Real.sqrt q‖ =
      2 * Real.log q * max (1 / 4 - dampingRate q a) 0 := by
  have hq0 : 0 < q := by linarith
  have hlog : 0 < Real.log q := Real.log_pos hq
  have hrpos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hn : ‖a / (Real.sqrt q : ℂ)‖ = ‖a‖ / Real.sqrt q := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  have hlogsqrt : Real.log (Real.sqrt q) = Real.log q / 2 := Real.log_sqrt hq0.le
  have hdiff : Real.log (‖a‖ / Real.sqrt q) = 2 * Real.log q * (1 / 4 - dampingRate q a) := by
    rw [Real.log_div hna.ne' hrpos.ne', hlogsqrt]
    unfold dampingRate
    field_simp
    ring
  have h2 : (0 : ℝ) ≤ 2 * Real.log q := by positivity
  rw [hn, Real.posLog, hdiff, mul_max_of_nonneg _ _ h2, mul_zero, max_comm]

/-- `log⁺ x = 0` for `x ≥ 0` means `x ≤ 1`. -/
theorem posLog_eq_zero_iff_le_one {x : ℝ} (hx : 0 ≤ x) : Real.posLog x = 0 ↔ x ≤ 1 := by
  rw [Real.posLog, max_eq_left_iff]
  constructor
  · intro h
    by_contra hc
    have := Real.log_pos (not_le.mp hc)
    linarith
  · exact Real.log_nonpos hx

/-- **The Bode integral vanishes exactly under universal damping.** -/
theorem bode_eq_zero_iff {q t : ℝ} (hq : 1 < q) {a b : ℂ} (hp : a * b = q) (hs : a + b = t)
    (hroots : ∀ z : ℂ, z ^ 2 - t * z + q = 0 → z = a ∨ z = b) :
    Real.posLog ‖a / Real.sqrt q‖ + Real.posLog ‖b / Real.sqrt q‖ = 0 ↔ t ^ 2 ≤ 4 * q := by
  have hq0 : 0 < q := by linarith
  have hrpos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
  have hrsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq0.le
  have hnprod : ‖a‖ * ‖b‖ = q := by
    rw [← norm_mul, hp, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hq0]
  have hn (z : ℂ) : ‖z / (Real.sqrt q : ℂ)‖ = ‖z‖ / Real.sqrt q := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hrpos]
  have hpos (x : ℝ) : 0 ≤ Real.posLog x := Real.posLog_nonneg
  rw [← modes_on_circle_iff hq0]
  constructor
  · intro h z hz
    have h1 : Real.posLog ‖a / (Real.sqrt q : ℂ)‖ = 0 := by
      linarith [hpos ‖a / (Real.sqrt q : ℂ)‖, hpos ‖b / (Real.sqrt q : ℂ)‖]
    have h2 : Real.posLog ‖b / (Real.sqrt q : ℂ)‖ = 0 := by
      linarith [hpos ‖a / (Real.sqrt q : ℂ)‖, hpos ‖b / (Real.sqrt q : ℂ)‖]
    rw [posLog_eq_zero_iff_le_one (norm_nonneg _), hn, div_le_one hrpos] at h1 h2
    have hA : 0 ≤ ‖a‖ := norm_nonneg a
    have hB : 0 ≤ ‖b‖ := norm_nonneg b
    have ha : ‖a‖ = Real.sqrt q := by
      by_contra hne
      have hlt := lt_of_le_of_ne h1 hne
      nlinarith
    have hb : ‖b‖ = Real.sqrt q := by
      by_contra hne
      have hlt := lt_of_le_of_ne h2 hne
      nlinarith
    rcases hroots z hz with rfl | rfl
    · rw [Complex.normSq_eq_norm_sq, ha, hrsq]
    · rw [Complex.normSq_eq_norm_sq, hb, hrsq]
  · intro h
    have hroot1 : a ^ 2 - t * a + q = 0 := by
      rw [← hs, ← hp]
      ring
    have hroot2 : b ^ 2 - t * b + q = 0 := by
      rw [← hs, ← hp]
      ring
    have h1 := h a hroot1
    have h2 := h b hroot2
    rw [Complex.normSq_eq_norm_sq] at h1 h2
    have ha : ‖a‖ = Real.sqrt q := by
      rw [← h1, Real.sqrt_sq (norm_nonneg a)]
    have hb : ‖b‖ = Real.sqrt q := by
      rw [← h2, Real.sqrt_sq (norm_nonneg b)]
    rw [hn, hn, ha, hb, div_self hrpos.ne', Real.posLog, Real.log_one]
    simp

/-! ### The Krein square is the degree form -/

/-- The trace of the datum is the trace of the black hole. -/
theorem frobTrace_datumOfRoots {t : ℝ} (hs : a + b = t) :
    (datumOfRoots q hq a b hp hconj).frobTrace = t := by
  have hrpos : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  unfold CurveDatum.frobTrace CurveDatum.trace CurveDatum.powerSum CurveDatum.sqrtq
  rw [Fin.sum_univ_two, datumOfRoots_q, datumOfRoots_β]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pow_one]
  rw [← add_div, hs, Complex.div_ofReal_re, Complex.ofReal_re]
  field_simp

/-- **The Krein square is the degree form**: `𝒬(x, y) = deg(y - x F)`. -/
theorem kreinSquare_eq_endDeg {t : ℝ} (hs : a + b = t) (x y : ℝ) :
    kreinSquare q t x y = (datumOfRoots q hq a b hp hconj).endDeg y x := by
  unfold CurveDatum.endDeg kreinSquare
  rw [frobTrace_datumOfRoots hq hp hconj hs, datumOfRoots_q]
  ring

/-- **The Krein square is half the Castelnuovo–Severi defect** of the graph class of `y - x F`. -/
theorem krein_eq_half_defect {t : ℝ} (hs : a + b = t) (x y : ℝ) :
    ((datumOfRoots q hq a b hp hconj).windowSurface {0, 1}).defect
        ((datumOfRoots q hq a b hp hconj).graphCycle y x)
        ((datumOfRoots q hq a b hp hconj).graphCycle y x) = 2 * kreinSquare q t x y := by
  rw [kreinSquare_eq_endDeg hq hp hconj hs]
  exact ((datumOfRoots q hq a b hp hconj).defect_graphCycle_of_genusOne (by simp) y x).1

/-- The fixed points of Frobenius are the cusps: `N₁ = q + 1 - t`. -/
theorem pointCount_datumOfRoots {t : ℝ} (hs : a + b = t) :
    (datumOfRoots q hq a b hp hconj).pointCount 1 = q + 1 - t := by
  rw [CurveDatum.pointCount_one_eq, frobTrace_datumOfRoots hq hp hconj hs, datumOfRoots_q]

end GaloisForLFunctions.ArithmeticScatteringHolography

end
