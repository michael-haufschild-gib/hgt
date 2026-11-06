import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheModulatedPrimeSumIsAPolynomialAverage
import GaloisForLFunctions.BiScaleUncertainty.BandLimitedLaplaceEnergy
import GaloisForLFunctions.RHTower.ZetaFiniteMeanSquare

/-!
# Most heights are Weil-positive at small aperture

For `δ, M` and `A = δ/(64M²) · log T`, outside a set of heights of measure `δT` in `[T, 2T]`, the local Weil
form is positive for every real test `F₀ ∈ C²_c([−A, A])` of shape `‖F₀‖²_A ≤ M² A ∫ F₀²`:

`Q_γ(F₀) = Q(F₀ cos γ·) + Q(F₀ sin γ·) > 0`
(`exists_weilPositive_quadrature`, and for a fixed profile `g(·/A)` the constant `M` is scale invariant).

The aperture is a fixed multiple of `log T`, the exceptional set does not depend on the test, and no
information on the zeros enters.

**Mechanism.**  The archimedean part of `Q_γ` is at least `½ log T ∫ F₀²` for every test.  The prime part is
the average `(1/π) ∫ Φ(t) D_N(γ + t) dt` of the Dirichlet polynomial `D_N`, `N ≈ e^{2A} = T^{2λ}`, against
`Φ = |F̂₀|²`.  The shape bound gives `Φ(t) ≤ S² /(1 + A²t²)`, so the prime part is at most
`S² × primeField(γ)/π`, where `primeField(γ) = ∫ |D_N(γ + t)| (1 + A²t²)⁻¹ dt` no longer depends on the test.
The mean value theorem gives `∫_T^{2T} primeField ≤ T κ π/A`, `κ = log N + O(1)`, and Markov's inequality
selects the heights.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real
open Zeta23 RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section

/-! ### The mean square of the polynomial -/

/-- The coefficients of the polynomial, indexed from `k + 1`. -/
def atomCoeff (N : ℕ) (k : Fin N) : ℂ := ((vonMangoldtAtom ((k : ℕ) + 1) : ℝ) : ℂ)

theorem continuous_primeCosine (N : ℕ) : Continuous (primeCosine N) := by
  unfold primeCosine
  fun_prop

/-- `D_N` is the real part of `dirPoly`. -/
theorem abs_primeCosine_le_norm_dirPoly (N : ℕ) (y : ℝ) :
    |primeCosine N y| ≤ ‖Sieve.dirPoly N (atomCoeff N) y‖ := by
  have hre : primeCosine N y = (Sieve.dirPoly N (atomCoeff N) y).re := by
    unfold primeCosine Sieve.dirPoly atomCoeff
    rw [Complex.re_sum, ← Fin.sum_univ_eq_sum_range (fun k =>
      vonMangoldtAtom (k + 1) * Real.cos (y * Real.log ((k + 1 : ℕ) : ℝ))) N]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
    push_cast
    rfl
  rw [hre]
  exact Complex.abs_re_le_norm _

/-- `Σ_{n ≤ N} Λ(n)/n ≤ log N + log 4 + 4`. -/
theorem sum_range_vonMangoldt_div_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.range N, ArithmeticFunction.vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) ≤
      Real.log N + (Real.log 4 + 4) := by
  have h := Mertens.sum_mangoldt_div_eq_log (x := (N : ℝ)) (by exact_mod_cast hN)
  rw [Nat.floor_natCast] at h
  have hIoc : Finset.Ioc 0 N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hIoc, sum_Icc_one_eq_sum_range] at h
  have := (abs_le.1 h).2
  linarith

theorem vonMangoldtAtom_sq_le (k : ℕ) :
    vonMangoldtAtom (k + 1) ^ 2 ≤
      ArithmeticFunction.vonMangoldt (k + 1) * Real.log ((k + 1 : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  have hΛ : ArithmeticFunction.vonMangoldt (k + 1) ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
    ArithmeticFunction.vonMangoldt_le_log
  have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt (k + 1) := ArithmeticFunction.vonMangoldt_nonneg
  unfold vonMangoldtAtom
  split_ifs with h2
  · rw [div_pow, Real.sq_sqrt hn.le]
    refine div_le_div_of_nonneg_right ?_ hn.le
    nlinarith
  · have hk : k = 0 := by omega
    simp [hk]

theorem log_cast_le {k N : ℕ} (hk : k < N) : Real.log ((k + 1 : ℕ) : ℝ) ≤ Real.log N :=
  Real.log_le_log (by positivity) (by exact_mod_cast hk)

theorem log_cast_nonneg (k : ℕ) : 0 ≤ Real.log ((k + 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _

/-- The constant `c` of `κ = log N + c`. -/
def fieldConstant : ℝ := 209 * (Real.log 4 + 4)

theorem fieldConstant_pos : 0 < fieldConstant := by
  have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold fieldConstant
  positivity

/-- **Mean square of the polynomial on any interval of length `T ≥ N`.** -/
theorem integral_norm_sq_dirPoly_le {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hNT : (N : ℝ) ≤ T) (a : ℝ) :
    ∫ y in a..(a + T), ‖Sieve.dirPoly N (atomCoeff N) y‖ ^ 2 ≤
      T * (Real.log N + fieldConstant) ^ 2 := by
  have hT0 : 0 < T := lt_of_lt_of_le (by exact_mod_cast hN) hNT
  have hl0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hmv := Sieve.dirichlet_meanValue_sharp_window N (atomCoeff N) a (a + T)
  have hupper := (abs_le.1 hmv).2
  rw [add_sub_cancel_left] at hupper
  have hnorm : ∀ k : Fin N, ‖atomCoeff N k‖ ^ 2 = vonMangoldtAtom ((k : ℕ) + 1) ^ 2 := fun k => by
    rw [atomCoeff, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- the diagonal
  have hS₂ : ∑ k : Fin N, ‖atomCoeff N k‖ ^ 2 ≤
      Real.log N * (Real.log N + (Real.log 4 + 4)) := by
    calc ∑ k : Fin N, ‖atomCoeff N k‖ ^ 2
        = ∑ k ∈ Finset.range N, vonMangoldtAtom (k + 1) ^ 2 := by
          simp only [hnorm]
          exact Fin.sum_univ_eq_sum_range (fun k => vonMangoldtAtom (k + 1) ^ 2) N
      _ ≤ ∑ k ∈ Finset.range N, Real.log N *
            (ArithmeticFunction.vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun k hk => (vonMangoldtAtom_sq_le k).trans ?_
          have hkN := Finset.mem_range.mp hk
          have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt (k + 1) :=
            ArithmeticFunction.vonMangoldt_nonneg
          have hn : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
          rw [mul_div_assoc', mul_comm (Real.log N)]
          refine div_le_div_of_nonneg_right ?_ hn.le
          exact mul_le_mul_of_nonneg_left (log_cast_le hkN) hΛ0
      _ = Real.log N * ∑ k ∈ Finset.range N,
            ArithmeticFunction.vonMangoldt (k + 1) / ((k + 1 : ℕ) : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_range_vonMangoldt_div_le hN) hl0
  -- the off-diagonal weight
  have hS₃ : ∑ k : Fin N, ((k : ℝ) + 1) * ‖atomCoeff N k‖ ^ 2 ≤
      Real.log N * ((Real.log 4 + 4) * N) := by
    calc ∑ k : Fin N, ((k : ℝ) + 1) * ‖atomCoeff N k‖ ^ 2
        = ∑ k ∈ Finset.range N, ((k : ℝ) + 1) * vonMangoldtAtom (k + 1) ^ 2 := by
          simp only [hnorm]
          exact Fin.sum_univ_eq_sum_range (fun k => ((k : ℝ) + 1) * vonMangoldtAtom (k + 1) ^ 2) N
      _ ≤ ∑ k ∈ Finset.range N, Real.log N * ArithmeticFunction.vonMangoldt (k + 1) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkN := Finset.mem_range.mp hk
          have hΛ0 : 0 ≤ ArithmeticFunction.vonMangoldt (k + 1) :=
            ArithmeticFunction.vonMangoldt_nonneg
          have hn : (0 : ℝ) < (k : ℝ) + 1 := by positivity
          have h := mul_le_mul_of_nonneg_left (vonMangoldtAtom_sq_le k) hn.le
          refine h.trans ?_
          have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; rfl
          rw [hcast, mul_div_cancel₀ _ hn.ne', mul_comm (Real.log N), hcast.symm]
          exact mul_le_mul_of_nonneg_left (log_cast_le hkN) hΛ0
      _ = Real.log N * ∑ k ∈ Finset.range N, ArithmeticFunction.vonMangoldt (k + 1) := by
          rw [Finset.mul_sum]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hl0
          have h := Mertens.sum_vonMangoldt_Icc_le N
          rwa [sum_Icc_one_eq_sum_range] at h
  have hsum : T * ((Real.log N + (Real.log 4 + 4)) * Real.log N) +
      208 * (Real.log N * ((Real.log 4 + 4) * N)) ≤ T * (Real.log N + fieldConstant) ^ 2 := by
    have h1 : 208 * (Real.log N * ((Real.log 4 + 4) * N)) ≤
        T * (Real.log N * (208 * (Real.log 4 + 4))) := by
      have hq : 0 ≤ Real.log N * (208 * (Real.log 4 + 4)) := by positivity
      calc 208 * (Real.log N * ((Real.log 4 + 4) * N))
          = (N : ℝ) * (Real.log N * (208 * (Real.log 4 + 4))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hNT hq
    have h2 : (Real.log N + (Real.log 4 + 4)) * Real.log N +
        Real.log N * (208 * (Real.log 4 + 4)) ≤ (Real.log N + fieldConstant) ^ 2 := by
      unfold fieldConstant
      nlinarith [mul_nonneg hl0 (add_nonneg hl4 (by norm_num : (0 : ℝ) ≤ 4)),
        sq_nonneg (209 * (Real.log 4 + 4))]
    calc _ ≤ T * ((Real.log N + (Real.log 4 + 4)) * Real.log N) +
          T * (Real.log N * (208 * (Real.log 4 + 4))) := by gcongr
      _ = T * ((Real.log N + (Real.log 4 + 4)) * Real.log N +
          Real.log N * (208 * (Real.log 4 + 4))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hT0.le
  have hS₂' := mul_le_mul_of_nonneg_left hS₂ hT0.le
  have hS₃' := mul_le_mul_of_nonneg_left hS₃ (by norm_num : (0 : ℝ) ≤ 208)
  nlinarith

/-- **Mean value on an interval.**  `∫_{a}^{a+T} |D_N| ≤ T κ`. -/
theorem integral_abs_primeCosine_le {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hNT : (N : ℝ) ≤ T) (a : ℝ) :
    ∫ y in a..(a + T), |primeCosine N y| ≤ T * (Real.log N + fieldConstant) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by exact_mod_cast hN) hNT
  have hl0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  set κ : ℝ := Real.log N + fieldConstant with hκ
  have hκ0 : 0 < κ := by
    have := fieldConstant_pos
    rw [hκ]
    linarith
  have hP : Continuous fun y => ‖Sieve.dirPoly N (atomCoeff N) y‖ ^ 2 := by
    unfold Sieve.dirPoly
    fun_prop
  have hcD : Continuous fun y => |primeCosine N y| := (continuous_primeCosine N).abs
  have hpt : ∀ y, |primeCosine N y| ≤
      (‖Sieve.dirPoly N (atomCoeff N) y‖ ^ 2 / κ + κ) / 2 := by
    intro y
    have hle := abs_primeCosine_le_norm_dirPoly N y
    have h0 := abs_nonneg (primeCosine N y)
    have hsq : |primeCosine N y| ^ 2 ≤ ‖Sieve.dirPoly N (atomCoeff N) y‖ ^ 2 :=
      pow_le_pow_left₀ h0 hle 2
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hdiv : |primeCosine N y| ^ 2 / κ ≤ ‖Sieve.dirPoly N (atomCoeff N) y‖ ^ 2 / κ :=
      div_le_div_of_nonneg_right hsq hκ0.le
    have hamgm : |primeCosine N y| * 2 ≤ |primeCosine N y| ^ 2 / κ + κ := by
      rw [← sub_nonneg]
      have : |primeCosine N y| ^ 2 / κ + κ - |primeCosine N y| * 2
          = (|primeCosine N y| - κ) ^ 2 / κ := by
        field_simp
        ring
      rw [this]
      positivity
    linarith
  have hIntU : IntervalIntegrable (fun y =>
      (‖Sieve.dirPoly N (atomCoeff N) y‖ ^ 2 / κ + κ) / 2) volume a (a + T) :=
    (((hP.div_const κ).add continuous_const).div_const 2).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by linarith : a ≤ a + T)
    (hcD.intervalIntegrable _ _) hIntU (fun y _ => hpt y)
  refine hmono.trans ?_
  have hval : ∫ y in a..(a + T), (‖Sieve.dirPoly N (atomCoeff N) y‖ ^ 2 / κ + κ) / 2
      = ((∫ y in a..(a + T), ‖Sieve.dirPoly N (atomCoeff N) y‖ ^ 2) / κ + T * κ) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      ((hP.div_const κ).intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_div, intervalIntegral.integral_const, add_sub_cancel_left,
      smul_eq_mul]
  rw [hval]
  have hb := integral_norm_sq_dirPoly_le hN hNT a
  have hdiv : (∫ y in a..(a + T), ‖Sieve.dirPoly N (atomCoeff N) y‖ ^ 2) / κ ≤ T * κ := by
    rw [div_le_iff₀ hκ0]
    calc _ ≤ T * κ ^ 2 := hb
      _ = T * κ * κ := by ring
  linarith

/-! ### The prime field -/

/-- The weight `(1 + R²t²)⁻¹`. -/
def fieldWeight (R t : ℝ) : ℝ := (1 + (R * t) ^ 2)⁻¹

theorem fieldWeight_pos (R t : ℝ) : 0 < fieldWeight R t := by
  unfold fieldWeight
  positivity

theorem integrable_fieldWeight {R : ℝ} (hR : 0 < R) : Integrable (fieldWeight R) :=
  integrable_inv_one_add_sq.comp_mul_left' hR.ne'

theorem integral_fieldWeight {R : ℝ} (hR : 0 < R) : ∫ t, fieldWeight R t = π / R := by
  have h := Measure.integral_comp_mul_left (fun x : ℝ => (1 + x ^ 2)⁻¹) R
  simp only [integral_univ_inv_one_add_sq] at h
  unfold fieldWeight
  rw [h, abs_of_pos (inv_pos.mpr hR), smul_eq_mul]
  field_simp

/-- The test-independent field at a height. -/
def primeField (N : ℕ) (R γ : ℝ) : ℝ := ∫ t, |primeCosine N (γ + t)| * fieldWeight R t

/-- A uniform bound for `D_N`. -/
def primeCosineBound (N : ℕ) : ℝ := ∑ k ∈ Finset.range N, |vonMangoldtAtom (k + 1)|

theorem abs_primeCosine_le (N : ℕ) (y : ℝ) : |primeCosine N y| ≤ primeCosineBound N := by
  unfold primeCosine primeCosineBound
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

theorem primeCosineBound_nonneg (N : ℕ) : 0 ≤ primeCosineBound N :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem primeField_nonneg (N : ℕ) (R γ : ℝ) : 0 ≤ primeField N R γ :=
  integral_nonneg fun t => mul_nonneg (abs_nonneg _) (fieldWeight_pos R t).le

theorem continuous_primeField (N : ℕ) {R : ℝ} (hR : 0 < R) : Continuous (primeField N R) := by
  unfold primeField
  refine continuous_of_dominated (bound := fun t => primeCosineBound N * fieldWeight R t)
    (fun γ => ?_) (fun γ => Eventually.of_forall fun t => ?_)
    ((integrable_fieldWeight hR).const_mul _) (Eventually.of_forall fun t => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have hw : Continuous (fieldWeight R) := by
      unfold fieldWeight
      refine Continuous.inv₀ (by fun_prop) fun t => ?_
      positivity
    exact ((continuous_primeCosine N).comp (continuous_const.add continuous_id)).abs.mul hw
  · rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (fieldWeight_pos R t).le)]
    exact mul_le_mul_of_nonneg_right (abs_primeCosine_le N _) (fieldWeight_pos R t).le
  · exact (((continuous_primeCosine N).comp (continuous_id.add continuous_const)).abs.mul
      continuous_const)

/-- **The mean of the field.**  `∫_T^{2T} primeField ≤ T κ π/R`. -/
theorem integral_primeField_le {N : ℕ} (hN : 1 ≤ N) {T R : ℝ} (hNT : (N : ℝ) ≤ T) (hR : 0 < R) :
    ∫ γ in Icc T (2 * T), primeField N R γ ≤ T * (Real.log N + fieldConstant) * (π / R) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by exact_mod_cast hN) hNT
  have hw := integrable_fieldWeight hR
  have hwc : Continuous (fieldWeight R) := by
    unfold fieldWeight
    refine Continuous.inv₀ (by fun_prop) fun t => ?_
    positivity
  -- Fubini
  have hprod : Integrable (Function.uncurry fun γ t : ℝ =>
      |primeCosine N (γ + t)| * fieldWeight R t) ((volume.restrict (Icc T (2 * T))).prod volume) := by
    have hdom : Integrable (fun z : ℝ × ℝ => primeCosineBound N * fieldWeight R z.2)
        ((volume.restrict (Icc T (2 * T))).prod volume) := by
      have hone : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc T (2 * T))) :=
        integrable_const_iff.mpr (Or.inr (by
          rw [isFiniteMeasure_restrict]
          exact (isCompact_Icc.measure_lt_top).ne))
      have h := hone.mul_prod (hw.const_mul (primeCosineBound N))
      simpa only [one_mul] using h
    refine hdom.mono' ?_ (Eventually.of_forall fun z => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact ((continuous_primeCosine N).comp (continuous_fst.add continuous_snd)).abs.mul
        (hwc.comp continuous_snd)
    · simp only [Function.uncurry]
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (fieldWeight_pos R _).le)]
      exact mul_le_mul_of_nonneg_right (abs_primeCosine_le N _) (fieldWeight_pos R _).le
  have hswap := integral_integral_swap hprod
  unfold primeField
  rw [hswap]
  -- the inner integral
  have hinner : ∀ t : ℝ, ∫ γ in Icc T (2 * T), |primeCosine N (γ + t)| * fieldWeight R t ≤
      T * (Real.log N + fieldConstant) * fieldWeight R t := by
    intro t
    have hc : Continuous fun y : ℝ => |primeCosine N y| := (continuous_primeCosine N).abs
    have hin : ∫ γ in Icc T (2 * T), |primeCosine N (γ + t)| * fieldWeight R t
        = (∫ y in (T + t)..(T + t + T), |primeCosine N y|) * fieldWeight R t := by
      rw [integral_mul_const, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : T ≤ 2 * T),
        intervalIntegral.integral_comp_add_right (fun y => |primeCosine N y|) t]
      congr 2
      ring
    rw [hin]
    exact mul_le_mul_of_nonneg_right (integral_abs_primeCosine_le hN hNT _) (fieldWeight_pos R t).le
  have hmono : ∫ t, ∫ γ in Icc T (2 * T), |primeCosine N (γ + t)| * fieldWeight R t ≤
      ∫ t, T * (Real.log N + fieldConstant) * fieldWeight R t := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => ?_) (hw.const_mul _)
      (Eventually.of_forall hinner)
    exact integral_nonneg fun γ => mul_nonneg (abs_nonneg _) (fieldWeight_pos R t).le
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_fieldWeight hR]

/-- **The bad heights are rare.** -/
theorem volume_primeField_ge_le {N : ℕ} (hN : 1 ≤ N) {T R y : ℝ} (hNT : (N : ℝ) ≤ T) (hR : 0 < R)
    (hy : 0 < y) :
    volume {γ | γ ∈ Icc T (2 * T) ∧ y ≤ primeField N R γ} ≤
      ENNReal.ofReal (T * (Real.log N + fieldConstant) * (π / R) / y) := by
  have hc := continuous_primeField N hR
  have hint : Integrable (primeField N R) (volume.restrict (Icc T (2 * T))) :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  have hmeas : MeasurableSet {γ | y ≤ primeField N R γ} :=
    (isClosed_le continuous_const hc).measurableSet
  have hfin : volume.restrict (Icc T (2 * T)) {γ | y ≤ primeField N R γ} ≠ ⊤ := by
    rw [Measure.restrict_apply hmeas]
    exact ((measure_mono inter_subset_right).trans_lt isCompact_Icc.measure_lt_top).ne
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Icc T (2 * T)))
    (Eventually.of_forall (primeField_nonneg N R)) hint y
  have hmean := integral_primeField_le hN hNT hR
  have hset : {γ | γ ∈ Icc T (2 * T) ∧ y ≤ primeField N R γ}
      = {γ | y ≤ primeField N R γ} ∩ Icc T (2 * T) := by
    ext γ
    simp only [mem_setOf_eq, mem_inter_iff]
    tauto
  rw [hset, ← Measure.restrict_apply hmeas, ← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hy, mul_comm]
  exact (hmarkov.trans hmean)

/-! ### The prime part against the field -/

/-- `Φ(t) ≤ S² (1 + R²t²)⁻¹`. -/
theorem norm_sq_paperFT_le_fieldWeight {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) (R t : ℝ) :
    ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 ≤ shapeNorm R F₀ ^ 2 * fieldWeight R t := by
  have h := one_add_mul_norm_paperFT_le hF₀ hF₀c R t
  have hS := shapeNorm_nonneg R F₀
  have hp : 0 < 1 + R ^ 2 * t ^ 2 := by positivity
  have hn := norm_nonneg (paperFT (fun u => (F₀ u : ℂ)) (t : ℂ))
  have hbound : ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ≤ shapeNorm R F₀ / (1 + R ^ 2 * t ^ 2) := by
    rw [le_div_iff₀ hp, mul_comm]
    exact h
  have hsq := pow_le_pow_left₀ hn hbound 2
  unfold fieldWeight
  rw [mul_pow R t, ← div_eq_mul_inv]
  refine hsq.trans ?_
  rw [div_pow]
  have h1 : (1 : ℝ) ≤ 1 + R ^ 2 * t ^ 2 := by nlinarith [mul_nonneg (sq_nonneg R) (sq_nonneg t)]
  exact div_le_div_of_nonneg_left (sq_nonneg _) hp (le_self_pow₀ h1 two_ne_zero)

/-- The prime part of `Q_γ` is at most `S²` times the field. -/
theorem abs_integral_mul_primeCosine_le {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) (N : ℕ) {R : ℝ} (hR : 0 < R) (γ : ℝ) :
    |∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * primeCosine N (γ + t)| ≤
      shapeNorm R F₀ ^ 2 * primeField N R γ := by
  have hwc : Continuous (fieldWeight R) := by
    unfold fieldWeight
    refine Continuous.inv₀ (by fun_prop) fun t => ?_
    positivity
  have hdom : Integrable fun t => shapeNorm R F₀ ^ 2 * (|primeCosine N (γ + t)| * fieldWeight R t) := by
    refine Integrable.const_mul ?_ _
    refine ((integrable_fieldWeight hR).const_mul (primeCosineBound N)).mono'
      (((continuous_primeCosine N).comp (continuous_const.add continuous_id)).abs.mul
        hwc).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (fieldWeight_pos R t).le)]
    exact mul_le_mul_of_nonneg_right (abs_primeCosine_le N _) (fieldWeight_pos R t).le
  rw [← Real.norm_eq_abs, primeField, ← integral_const_mul]
  refine norm_integral_le_of_norm_le hdom (Eventually.of_forall fun t => ?_)
  rw [norm_mul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs]
  have h := norm_sq_paperFT_le_fieldWeight hF₀ hF₀c R t
  have ha := abs_nonneg (primeCosine N (γ + t))
  nlinarith [mul_le_mul_of_nonneg_right h ha]

/-! ### The main theorems -/

/-- **Quantitative local Weil positivity.**  Outside a set of measure `δT` independent of the test, the
form exceeds its archimedean main term minus `(κ/(Rδ)) S_R(F₀)²` and a negligible pole term. -/
theorem exists_bad_heights {T δ R : ℝ} {N : ℕ} (hN : 1 ≤ N) (hNT : (N : ℝ) ≤ T) (hδ : 0 < δ)
    (hR : 0 < R) :
    ∃ B : Set ℝ, volume B ≤ ENNReal.ofReal (δ * T) ∧
      ∀ γ ∈ Icc T (2 * T), γ ∉ B → ∀ A : ℝ, 0 ≤ A → Real.exp (2 * A) ≤ N →
        ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ → (∀ u : ℝ, A < |u| → F₀ u = 0) →
          (Real.log (2 + |γ|) / 2 - (10 + Real.log 4)) * (∫ u, F₀ u ^ 2)
              - (Real.log N + fieldConstant) / (R * δ) * shapeNorm R F₀ ^ 2
              - 4 * (Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + γ ^ 2)) ^ 2 ≤
            fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by exact_mod_cast hN) hNT
  have hl0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  set κ : ℝ := Real.log N + fieldConstant with hκ
  have hκ0 : 0 < κ := by
    have := fieldConstant_pos
    rw [hκ]
    linarith
  set y : ℝ := κ * π / (R * δ) with hy
  have hy0 : 0 < y := by
    rw [hy]
    have := Real.pi_pos
    positivity
  refine ⟨{γ | γ ∈ Icc T (2 * T) ∧ y ≤ primeField N R γ}, ?_, ?_⟩
  · refine (volume_primeField_ge_le hN hNT hR hy0).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
    rw [hy]
    have hπ := Real.pi_ne_zero
    field_simp
  · intro γ hγ hbad A hA hNA F₀ hF₀ hF₀c hsupp
    have hlt : primeField N R γ < y := by
      by_contra hge
      exact hbad ⟨hγ, not_lt.mp hge⟩
    have hbase := fullZeroForm_quadrature_ge hF₀ hF₀c hA hsupp γ hNA
    have hP := abs_integral_mul_primeCosine_le hF₀ hF₀c N hR γ
    have hS2 : 0 ≤ shapeNorm R F₀ ^ 2 := sq_nonneg _
    have hπ : 0 < 1 / π := by
      have := Real.pi_pos
      positivity
    have hfield : 1 / π * |∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 *
        primeCosine N (γ + t)| ≤ κ / (R * δ) * shapeNorm R F₀ ^ 2 := by
      have h1 : shapeNorm R F₀ ^ 2 * primeField N R γ ≤ shapeNorm R F₀ ^ 2 * y :=
        mul_le_mul_of_nonneg_left hlt.le hS2
      have h2 := mul_le_mul_of_nonneg_left (hP.trans h1) hπ.le
      refine h2.trans (le_of_eq ?_)
      rw [hy]
      have hπ' := Real.pi_ne_zero
      field_simp
    linarith only [hbase, hfield]

/-- `envelopeWindowNorm ≤ shapeNorm` at scale `R ≥ 1`. -/
theorem envelopeWindowNorm_le_shapeNorm {R : ℝ} (hR : 1 ≤ R) (F₀ : ℝ → ℝ) :
    envelopeWindowNorm F₀ ≤ shapeNorm R F₀ := by
  unfold envelopeWindowNorm shapeNorm
  have h : 0 ≤ ∫ u, |deriv (deriv F₀) u| := integral_nonneg fun _ => abs_nonneg _
  have hR2 : 1 ≤ R ^ 2 := one_le_pow₀ hR
  nlinarith

/-- **Local Weil positivity at small aperture on density `1 − δ` of the heights, for all tests of
bounded shape.**  With `A = δ/(64M²) · log T`, outside a set of heights of measure `δT`, independent of
the test, every real `F₀ ∈ C²_c([−A, A])` with `S_A(F₀)² ≤ M² A ∫ F₀²` and `F₀ ≠ 0` has `Q_γ(F₀) > 0`. -/
theorem exists_weilPositive_quadrature {δ M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 1 ≤ M) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∃ B : Set ℝ, volume B ≤ ENNReal.ofReal (δ * T) ∧
      ∀ γ ∈ Icc T (2 * T), γ ∉ B → ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
        (∀ u : ℝ, δ / (64 * M ^ 2) * Real.log T < |u| → F₀ u = 0) →
        shapeNorm (δ / (64 * M ^ 2) * Real.log T) F₀ ^ 2 ≤
          M ^ 2 * (δ / (64 * M ^ 2) * Real.log T) * (∫ u, F₀ u ^ 2) →
        0 < ∫ u, F₀ u ^ 2 →
        0 < fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  set lam : ℝ := δ / (64 * M ^ 2) with hlam
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hlam0 : 0 < lam := by
    rw [hlam]
    positivity
  have hlamM : M ^ 2 * lam = δ / 64 := by
    rw [hlam]
    field_simp
  have hlam1 : lam ≤ 1 / 64 := by
    rw [hlam, div_le_iff₀ (by positivity)]
    nlinarith
  set C₁ : ℝ := 10 + Real.log 4 with hC₁
  have hC₁0 : 0 < C₁ := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [hC₁]
    linarith
  have hc0 := fieldConstant_pos
  -- the size of `T`
  set L₀ : ℝ := max (8 * C₁ + 8) ((1 + fieldConstant + 2) / lam + 8) with hL₀
  refine ⟨Real.exp L₀, fun T hT => ?_⟩
  have hexp0 := Real.exp_pos L₀
  have hT0 : 0 < T := lt_of_lt_of_le hexp0 hT
  have hL : L₀ ≤ Real.log T := by
    have := Real.log_le_log hexp0 hT
    rwa [Real.log_exp] at this
  have hLC : 8 * C₁ + 8 ≤ Real.log T := (le_max_left _ _).trans hL
  have hLA : (1 + fieldConstant + 2) / lam + 8 ≤ Real.log T := (le_max_right _ _).trans hL
  set A : ℝ := lam * Real.log T with hA
  have hA0 : 0 < A := by
    have : 0 < Real.log T := by linarith
    rw [hA]
    positivity
  have hAbig : 1 + fieldConstant + 2 ≤ A := by
    have h := (div_le_iff₀ hlam0).mp (show (1 + fieldConstant + 2) / lam ≤ Real.log T by linarith)
    rw [hA, mul_comm]
    exact h
  have hA1 : 1 ≤ A := by linarith
  -- the length of the polynomial
  set N : ℕ := ⌈Real.exp (2 * A)⌉₊ with hNdef
  have hNA : Real.exp (2 * A) ≤ N := Nat.le_ceil _
  have hN1 : 1 ≤ N := by
    have h1 : (1 : ℝ) ≤ Real.exp (2 * A) := Real.one_le_exp (by positivity)
    exact_mod_cast h1.trans hNA
  have hNlt : (N : ℝ) < Real.exp (2 * A) + 1 := Nat.ceil_lt_add_one (Real.exp_pos _).le
  have hNle2 : (N : ℝ) ≤ 2 * Real.exp (2 * A) := by
    have h1 : (1 : ℝ) ≤ Real.exp (2 * A) := Real.one_le_exp (by positivity)
    linarith
  have hlogN : Real.log N ≤ 2 * A + 1 := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have h := Real.log_le_log hN0 hNle2
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    linarith
  have hNT : (N : ℝ) ≤ T := by
    have hA4 : 2 * A ≤ Real.log T / 32 := by
      rw [hA]
      nlinarith
    have hTbig : Real.log T / 32 + 1 ≤ Real.log T := by linarith
    have hle : Real.log 2 + 2 * A ≤ Real.log T := by
      have h2 : Real.log 2 ≤ 1 := by
        have := Real.log_two_lt_d9
        linarith
      linarith
    have h := Real.exp_le_exp.mpr hle
    rw [Real.exp_log hT0, Real.exp_add, Real.exp_log (by norm_num)] at h
    linarith
  obtain ⟨B, hB, hgood⟩ := exists_bad_heights hN1 hNT hδ hA0
  refine ⟨B, hB, fun γ hγ hγB F₀ hF₀ hF₀c hsupp hshape hpos => ?_⟩
  have hbase := hgood γ hγ hγB A hA0.le hNA F₀ hF₀ hF₀c hsupp
  set I₂ : ℝ := ∫ u, F₀ u ^ 2 with hI₂
  set S : ℝ := shapeNorm A F₀ with hS
  have hS0 : 0 ≤ S := shapeNorm_nonneg A F₀
  -- the archimedean main term
  have hγT : T ≤ γ := hγ.1
  have hγ0 : 0 < γ := lt_of_lt_of_le hT0 hγT
  have hlogγ : Real.log T ≤ Real.log (2 + |γ|) := by
    rw [abs_of_pos hγ0]
    exact Real.log_le_log hT0 (by linarith)
  -- the field term
  have hκA : (Real.log N + fieldConstant) / (A * δ) ≤ 3 / δ := by
    rw [div_le_div_iff₀ (by positivity) hδ]
    nlinarith
  have hfield : (Real.log N + fieldConstant) / (A * δ) * S ^ 2 ≤ 3 / 64 * Real.log T * I₂ := by
    have h1 := mul_le_mul_of_nonneg_right hκA (sq_nonneg S)
    refine h1.trans ?_
    have h2 := mul_le_mul_of_nonneg_left hshape (by positivity : 0 ≤ 3 / δ)
    refine h2.trans (le_of_eq ?_)
    rw [hA]
    have e : M ^ 2 * (lam * Real.log T) = δ / 64 * Real.log T := by
      rw [← mul_assoc, hlamM]
    rw [e]
    field_simp
  -- the pole term
  have hexpA : Real.exp A ≤ T := by
    have hle : A ≤ Real.log T := by
      rw [hA]
      nlinarith
    have h := Real.exp_le_exp.mpr hle
    rwa [Real.exp_log hT0] at h
  have hT1 : 1 ≤ T := by
    have : (1 : ℝ) ≤ Real.exp L₀ := Real.one_le_exp (by
      have : 0 ≤ 8 * C₁ + 8 := by positivity
      exact this.trans (le_max_left _ _))
    linarith
  have hpole : 4 * (Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + γ ^ 2)) ^ 2 ≤
      1 / 64 * Real.log T * I₂ := by
    have hN0 := envelopeWindowNorm_nonneg F₀
    have hNS := envelopeWindowNorm_le_shapeNorm hA1 F₀
    have h1γ : T ^ 2 ≤ 1 + γ ^ 2 := by nlinarith
    have hexp2 : Real.exp (A / 2) ^ 2 = Real.exp A := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have hnum : (Real.exp (A / 2) * envelopeWindowNorm F₀) ^ 2 ≤ T * S ^ 2 := by
      rw [mul_pow, hexp2]
      exact mul_le_mul hexpA (pow_le_pow_left₀ hN0 hNS 2) (sq_nonneg _) hT0.le
    have hden : (T ^ 2) ^ 2 ≤ (1 + γ ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) h1γ 2
    have hfrac : (Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + γ ^ 2)) ^ 2 ≤ T * S ^ 2 / T ^ 4 := by
      rw [div_pow]
      refine div_le_div₀ (by positivity) hnum (by positivity) ?_
      calc T ^ 4 = (T ^ 2) ^ 2 := by ring
        _ ≤ _ := hden
    have hT4 : T * S ^ 2 / T ^ 4 ≤ S ^ 2 / 4 := by
      have hT64 : (4 : ℝ) ≤ T ^ 3 := by
        have hL8 : 8 ≤ Real.log T := by linarith
        have hexp8 : Real.exp 2 ≤ T := by
          have h := Real.exp_le_exp.mpr (show (2 : ℝ) ≤ Real.log T by linarith)
          rwa [Real.exp_log hT0] at h
        have h2 : (2 : ℝ) ≤ Real.exp 2 := by
          have := Real.add_one_le_exp (2 : ℝ)
          linarith
        have h2T : (2 : ℝ) ≤ T := h2.trans hexp8
        nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2T 3]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : T * S ^ 2 * 4 ≤ T * S ^ 2 * T ^ 3 :=
        mul_le_mul_of_nonneg_left hT64 (by positivity)
      calc T * S ^ 2 * 4 ≤ T * S ^ 2 * T ^ 3 := this
        _ = S ^ 2 * T ^ 4 := by ring
    have hS2 : S ^ 2 ≤ δ / 64 * Real.log T * I₂ := by
      refine hshape.trans (le_of_eq ?_)
      rw [hA]
      have e : M ^ 2 * (lam * Real.log T) = δ / 64 * Real.log T := by
        rw [← mul_assoc, hlamM]
      rw [e]
    have hδI : δ / 64 * Real.log T * I₂ ≤ 1 / 64 * Real.log T * I₂ := by
      have hLI : 0 ≤ Real.log T * I₂ := mul_nonneg (by linarith) hpos.le
      nlinarith
    calc 4 * (Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + γ ^ 2)) ^ 2
        ≤ 4 * (S ^ 2 / 4) := by
          exact mul_le_mul_of_nonneg_left (hfrac.trans hT4) (by norm_num)
      _ = S ^ 2 := by ring
      _ ≤ _ := hS2.trans hδI
  -- combine
  have hmain : (Real.log T / 2 - C₁) * I₂ ≤ (Real.log (2 + |γ|) / 2 - C₁) * I₂ :=
    mul_le_mul_of_nonneg_right (by linarith) hpos.le
  have hfinal : 0 < (Real.log T / 2 - C₁) * I₂ - 3 / 64 * Real.log T * I₂ -
      1 / 64 * Real.log T * I₂ := by
    have hval : (Real.log T / 2 - C₁) * I₂ - 3 / 64 * Real.log T * I₂ -
        1 / 64 * Real.log T * I₂ = (7 / 16 * Real.log T - C₁) * I₂ := by ring
    rw [hval]
    exact mul_pos (by linarith) hpos
  linarith only [hbase, hfield, hpole, hmain, hfinal]

end

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
