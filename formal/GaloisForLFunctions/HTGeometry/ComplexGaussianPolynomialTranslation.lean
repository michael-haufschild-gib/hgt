import GaloisForLFunctions.HTGeometry.HermitePolynomialDerivativeEnergy
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Coefficient-uniform complex translation of Gaussian polynomials

Route U's prime-aperture estimate completes a square and moves a Gaussian contour in the imaginary
direction.  Its missing finite-dimensional theorem is not merely a derivative estimate: the
literal complex translate of every real degree-`d` polynomial must be controlled uniformly over
its coefficients.

This file closes that gap.  The finite Hasse--Taylor expansion defines the translated polynomial
times the fixed Gaussian as an actual Schwartz map.  The pointwise theorem identifies it with
`P(x + z) exp(-πx²)`.  Iterating the sharp Hermite derivative-energy estimate and summing the
factorial series proves the unconditional bound

`‖P(· + z) exp(-π·²)‖₂ ≤ exp (‖z‖ sqrt(4π natDegree(P))) ‖P exp(-π·²)‖₂`.

No coefficient norm, numerical certificate, nonvanishing premise, or RH assumption occurs.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-- Norm form of the sharp Gaussian derivative-energy theorem. -/
theorem gaussianPolynomialDerivativeNorm_le (P : Polynomial ℝ) :
    ‖(polyGaussSchwartz P.derivative).toLp 2 (volume : Measure ℝ)‖ ≤
      Real.sqrt (4 * π * P.natDegree) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 4 * π * (P.natDegree : ℝ))]
  exact gaussianPolynomialDerivativeEnergy_le P

/-- Every iterated derivative obeys the same top-degree oscillator ceiling.  This retains the
square-root degree scale needed by the parabolic Route U horizon. -/
theorem gaussianPolynomialIterateDerivativeNorm_le (P : Polynomial ℝ) (k : ℕ) :
    ‖(polyGaussSchwartz (Polynomial.derivative^[k] P)).toLp 2
        (volume : Measure ℝ)‖ ≤
      Real.sqrt (4 * π * P.natDegree) ^ k *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have hstep := gaussianPolynomialDerivativeNorm_le
        (Polynomial.derivative^[k] P)
      have hdeg : (Polynomial.derivative^[k] P).natDegree ≤ P.natDegree :=
        (Polynomial.natDegree_iterate_derivative P k).trans (Nat.sub_le _ _)
      have hsqrt :
          Real.sqrt (4 * π * (Polynomial.derivative^[k] P).natDegree) ≤
            Real.sqrt (4 * π * P.natDegree) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hdeg) (by positivity)
      calc
        ‖(polyGaussSchwartz (Polynomial.derivative^[k] P).derivative).toLp 2
            (volume : Measure ℝ)‖
            ≤ Real.sqrt (4 * π * (Polynomial.derivative^[k] P).natDegree) *
                ‖(polyGaussSchwartz (Polynomial.derivative^[k] P)).toLp 2
                  (volume : Measure ℝ)‖ := hstep
        _ ≤ Real.sqrt (4 * π * P.natDegree) *
                ‖(polyGaussSchwartz (Polynomial.derivative^[k] P)).toLp 2
                  (volume : Measure ℝ)‖ :=
          mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
        _ ≤ Real.sqrt (4 * π * P.natDegree) *
                (Real.sqrt (4 * π * P.natDegree) ^ k *
                  ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖) :=
          mul_le_mul_of_nonneg_left ih (Real.sqrt_nonneg _)
        _ = Real.sqrt (4 * π * P.natDegree) ^ (k + 1) *
                ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
          rw [pow_succ']
          ring

/-- Hasse differentiation commutes with the real-to-complex coefficient embedding. -/
theorem hasseDeriv_map_real_complex (P : Polynomial ℝ) (k : ℕ) :
    Polynomial.hasseDeriv k (P.map (algebraMap ℝ ℂ)) =
      (Polynomial.hasseDeriv k P).map (algebraMap ℝ ℂ) := by
  ext n
  simp [Polynomial.hasseDeriv_coeff]

/-- Finite complex Taylor formula for a real polynomial, expressed in the real Hasse derivatives
consumed by `polyGaussSchwartz`. -/
theorem eval₂_add_eq_sum_hasseDeriv (P : Polynomial ℝ) (x : ℝ) (z : ℂ) :
    Polynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ) + z) P =
      ∑ k ∈ Finset.range (P.natDegree + 1),
        z ^ k * (((Polynomial.hasseDeriv k P).eval x : ℝ) : ℂ) := by
  let PC : Polynomial ℂ := P.map (algebraMap ℝ ℂ)
  have hdegPC : PC.natDegree = P.natDegree :=
    Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective P
  have ht := Polynomial.taylor_eval (x : ℂ) PC z
  rw [add_comm] at ht
  rw [Polynomial.eval_eq_sum_range' (p := Polynomial.taylor (x : ℂ) PC)
    (n := P.natDegree + 1) (by rw [Polynomial.natDegree_taylor, hdegPC]; omega)] at ht
  rw [← Polynomial.eval_map]
  change PC.eval ((x : ℂ) + z) = _
  rw [← ht]
  simp_rw [Polynomial.taylor_coeff]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show Polynomial.hasseDeriv k PC =
      (Polynomial.hasseDeriv k P).map (algebraMap ℝ ℂ) from
    hasseDeriv_map_real_complex P k]
  have heval := Polynomial.eval_map_apply (f := algebraMap ℝ ℂ)
    (p := Polynomial.hasseDeriv k P) x
  change ((Polynomial.hasseDeriv k P).map (algebraMap ℝ ℂ)).eval
      ((algebraMap ℝ ℂ) x) * z ^ k = _
  rw [heval]
  change (((Polynomial.hasseDeriv k P).eval x : ℝ) : ℂ) * z ^ k = _
  ring

/-- Literal complex translate of a real polynomial factor, times the fixed self-dual Gaussian.
The finite Hasse expansion makes Schwartz regularity structural. -/
def complexTranslatedPolyGauss (P : Polynomial ℝ) (z : ℂ) : SchwartzMap ℝ ℂ :=
  ∑ k ∈ Finset.range (P.natDegree + 1),
    z ^ k • polyGaussSchwartz (Polynomial.hasseDeriv k P)

/-- `complexTranslatedPolyGauss` is pointwise the actual evaluation `P(x+z) exp(-πx²)`, not an
abstract translation predicate. -/
theorem complexTranslatedPolyGauss_apply (P : Polynomial ℝ) (z : ℂ) (x : ℝ) :
    complexTranslatedPolyGauss P z x =
      Polynomial.eval₂ (algebraMap ℝ ℂ) ((x : ℂ) + z) P * gaussReal x := by
  rw [complexTranslatedPolyGauss, _root_.sum_apply]
  change (∑ k ∈ Finset.range (P.natDegree + 1),
      z ^ k * (((Polynomial.hasseDeriv k P).eval x * gaussReal x : ℝ) : ℂ)) = _
  rw [eval₂_add_eq_sum_hasseDeriv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  push_cast
  ring

/-- The Hasse derivative gains exactly the factorial needed by the Taylor series, while retaining
the coefficient-free oscillator bound. -/
theorem gaussianHasseDerivativeFactorialNorm_le (P : Polynomial ℝ) (k : ℕ) :
    (k.factorial : ℝ) *
        ‖(polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2
          (volume : Measure ℝ)‖ ≤
      Real.sqrt (4 * π * P.natDegree) ^ k *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  have hfun := congrFun (Polynomial.factorial_smul_hasseDeriv (R := ℝ) k) P
  have hnorm :
      ‖(polyGaussSchwartz (Polynomial.derivative^[k] P)).toLp 2
          (volume : Measure ℝ)‖ =
        (k.factorial : ℝ) *
          ‖(polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2
            (volume : Measure ℝ)‖ := by
    rw [← hfun, LinearMap.smul_apply, ← Nat.cast_smul_eq_nsmul ℝ,
      polyGaussSchwartz_smul]
    have hmap := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).map_smul
      ((k.factorial : ℝ) : ℂ) (polyGaussSchwartz (Polynomial.hasseDeriv k P))
    rw [SchwartzMap.toLpCLM_apply] at hmap
    have hmap' :
        ((↑k.factorial : ℝ) • polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2
            (volume : Measure ℝ) =
          ((k.factorial : ℂ) •
            (polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2
              (volume : Measure ℝ)) := by
      exact hmap
    rw [hmap', norm_smul]
    simp only [Complex.norm_natCast]
  rw [← hnorm]
  exact gaussianPolynomialIterateDerivativeNorm_le P k

/-- **Coefficient-uniform complex Gaussian translation.**  Every complex translate of every real
polynomial has the sharp square-root-degree exponential envelope in Gaussian `L²`.  Statement is
closed for all `P` and `z`, including zero and constant polynomials. -/
theorem norm_complexTranslatedPolyGauss_le (P : Polynomial ℝ) (z : ℂ) :
    ‖(complexTranslatedPolyGauss P z).toLp 2 (volume : Measure ℝ)‖ ≤
      Real.exp (‖z‖ * Real.sqrt (4 * π * P.natDegree)) *
        ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  let A : ℝ := Real.sqrt (4 * π * P.natDegree)
  let N : ℝ := ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖
  have hterm (k : ℕ) :
      ‖(z ^ k • polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2
          (volume : Measure ℝ)‖ ≤
        ((‖z‖ * A) ^ k / (k.factorial : ℝ)) * N := by
    have hfac : (0 : ℝ) < k.factorial := by positivity
    have hh := gaussianHasseDerivativeFactorialNorm_le P k
    have hh' :
        ‖(polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2
            (volume : Measure ℝ)‖ ≤ A ^ k * N / (k.factorial : ℝ) := by
      rw [le_div_iff₀ hfac]
      simpa only [A, N, mul_comm] using hh
    rw [toLp_smul, norm_smul, norm_pow]
    calc
      ‖z‖ ^ k * ‖(polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2
          (volume : Measure ℝ)‖
          ≤ ‖z‖ ^ k * (A ^ k * N / (k.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hh' (by positivity)
      _ = ((‖z‖ * A) ^ k / (k.factorial : ℝ)) * N := by ring
  have hexp : HasSum
      (fun k : ℕ => (‖z‖ * A) ^ k / (k.factorial : ℝ))
      (Real.exp (‖z‖ * A)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (‖z‖ * A)
  have hpartial :
      (∑ k ∈ Finset.range (P.natDegree + 1),
          (‖z‖ * A) ^ k / (k.factorial : ℝ)) ≤ Real.exp (‖z‖ * A) := by
    calc
      _ ≤ ∑' k : ℕ, (‖z‖ * A) ^ k / (k.factorial : ℝ) :=
        hexp.summable.sum_le_tsum _ (fun k hk => by positivity)
      _ = _ := hexp.tsum_eq
  calc
    ‖(complexTranslatedPolyGauss P z).toLp 2 (volume : Measure ℝ)‖
        ≤ ∑ k ∈ Finset.range (P.natDegree + 1),
            ‖(z ^ k • polyGaussSchwartz (Polynomial.hasseDeriv k P)).toLp 2
              (volume : Measure ℝ)‖ := by
          unfold complexTranslatedPolyGauss
          change ‖(SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ))
              (∑ k ∈ Finset.range (P.natDegree + 1),
                z ^ k • polyGaussSchwartz (Polynomial.hasseDeriv k P))‖ ≤ _
          rw [map_sum]
          exact norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (P.natDegree + 1),
          (((‖z‖ * A) ^ k / (k.factorial : ℝ)) * N) := by
        exact Finset.sum_le_sum fun k hk => hterm k
    _ = (∑ k ∈ Finset.range (P.natDegree + 1),
          (‖z‖ * A) ^ k / (k.factorial : ℝ)) * N := by
        rw [Finset.sum_mul]
    _ ≤ Real.exp (‖z‖ * A) * N :=
      mul_le_mul_of_nonneg_right hpartial (norm_nonneg _)
    _ = _ := rfl

/-! ## Even-polynomial specialization used by Route U -/

/-- The even polynomial `x ↦ P(x²)` appearing in the completed-source heat filter. -/
def evenSquarePolynomial (P : Polynomial ℝ) : Polynomial ℝ :=
  P.comp (Polynomial.X ^ 2)

@[simp] theorem natDegree_evenSquarePolynomial (P : Polynomial ℝ) :
    (evenSquarePolynomial P).natDegree = 2 * P.natDegree := by
  rw [evenSquarePolynomial, Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
  omega

/-- Literal evaluation of the translated even heat-filter polynomial. -/
theorem complexTranslatedEvenPolyGauss_apply
    (P : Polynomial ℝ) (z : ℂ) (x : ℝ) :
    complexTranslatedPolyGauss (evenSquarePolynomial P) z x =
      Polynomial.eval₂ (algebraMap ℝ ℂ) (((x : ℂ) + z) ^ 2) P * gaussReal x := by
  rw [complexTranslatedPolyGauss_apply, evenSquarePolynomial, Polynomial.eval₂_comp,
    Polynomial.eval₂_pow, Polynomial.eval₂_X]

/-- Route U specialization: composing with `X²` doubles degree and gives the exact
`sqrt(8π deg(P))` complex-translation exponent. -/
theorem norm_complexTranslatedEvenPolyGauss_le (P : Polynomial ℝ) (z : ℂ) :
    ‖(complexTranslatedPolyGauss (evenSquarePolynomial P) z).toLp 2
        (volume : Measure ℝ)‖ ≤
      Real.exp (‖z‖ * Real.sqrt (8 * π * P.natDegree)) *
        ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2
          (volume : Measure ℝ)‖ := by
  have h := norm_complexTranslatedPolyGauss_le (evenSquarePolynomial P) z
  rw [natDegree_evenSquarePolynomial] at h
  have harg : 4 * π * ((2 * P.natDegree : ℕ) : ℝ) =
      8 * π * (P.natDegree : ℝ) := by
    push_cast
    ring
  rwa [harg] at h

end GaloisForLFunctions
