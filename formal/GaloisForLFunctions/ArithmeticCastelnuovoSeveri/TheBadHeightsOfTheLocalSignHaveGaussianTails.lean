import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MostHeightsAreWeilPositiveAtSmallAperture
import GaloisForLFunctions.RHTower.Sieve.DirichletPowerPrimeSupport
import GaloisForLFunctions.RHTower.VonMangoldtNonPrimeSqrtSum

/-!
# The bad heights of the local Weil sign have Gaussian tails

`MostHeightsAreWeilPositiveAtSmallAperture` proves local Weil positivity `Q_γ(F₀) > 0` at aperture
`A = δ/(64M²) · log T` for every test of shape `M`, outside a set of heights of measure `δT`, by
Markov's inequality on the prime field `∫ |D_N(γ + t)| (1 + A²t²)⁻¹ dt`. Replacing the first moment
by the `2k`-th moment of the prime part of `D_N` gives

* **Gaussian tails** (`exists_weilPositive_quadrature_moment`): for `δ ≤ 1/4`, `kδ ≤ 8M²`, the
  bad heights have measure `≤ 209 (4kδ²)^k T` (with `k^k (4δ²)^k = (4kδ²)^k`);
* **exponential rarity** (`exists_weilPositive_quadrature_exp_rare`): for `δ ≤ 1/(64M²)`, measure
  `≤ 418 e^{−5M²/δ} T`, against `δT` from Markov.

**Mechanism.** Split `D_N = Re P_N + H_N`: `P_N` carries the primes, the proper prime powers give
`|H_N| ≤ 2 log N + 4 log 4 + 16` (`abs_primeCosine_le_primePart`). The power `P_N^k` is the
polynomial of the `k`-fold convolution, whose coefficient mass is `≤ k^k (Σ_p Λ(p)²/p)^k`, so the
mean value theorem gives `∫_a^{a+T} |P_N|^{2k} ≤ (T + 208 N^k) k^k S^k`
(`integral_norm_primePart_pow_le`). Bernoulli's inequality `(m+1)s^m x ≤ x^{m+1} + m s^{m+1}` moves
the moment inside the field without Jensen (`pow_le_primePartMoment_of_le`), and Markov's
inequality on the moment field does the rest.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real
open Zeta23 RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section

/-! ### The prime part and the prime powers -/

/-- The prime coefficients of `D_N`. -/
def primeAtomCoeff (N : ℕ) (k : Fin N) : ℂ := if ((k : ℕ) + 1).Prime then atomCoeff N k else 0

/-- The proper prime-power coefficients of `D_N`. -/
def powerAtomCoeff (N : ℕ) (k : Fin N) : ℂ := if ((k : ℕ) + 1).Prime then 0 else atomCoeff N k

/-- The prime part `P_N(y) = Σ_{p ≤ N} Λ(p) p^{−1/2} e^{iy log p}`. -/
def primePart (N : ℕ) (y : ℝ) : ℂ := Sieve.dirPoly N (primeAtomCoeff N) y

/-- The bound `2 log N + 4 log 4 + 16` of the proper prime powers. -/
def powerBound (N : ℕ) : ℝ := 2 * Real.log N + 4 * Real.log 4 + 16

theorem dirPoly_atomCoeff_eq (N : ℕ) (y : ℝ) :
    Sieve.dirPoly N (atomCoeff N) y = primePart N y + Sieve.dirPoly N (powerAtomCoeff N) y := by
  unfold primePart Sieve.dirPoly
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold primeAtomCoeff powerAtomCoeff
  split_ifs <;> ring

theorem norm_dirPoly_le_sum (N : ℕ) (a : Fin N → ℂ) (y : ℝ) :
    ‖Sieve.dirPoly N a y‖ ≤ ∑ k : Fin N, ‖a k‖ := by
  unfold Sieve.dirPoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

theorem vonMangoldtAtom_eq_div_sqrt {n : ℕ} (hn : 1 ≤ n) :
    vonMangoldtAtom n = ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
  unfold vonMangoldtAtom
  split_ifs with h
  · rfl
  · obtain rfl : n = 1 := by omega
    simp

theorem sum_norm_powerAtomCoeff_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ k : Fin N, ‖powerAtomCoeff N k‖ ≤ powerBound N := by
  classical
  set g : ℕ → ℝ := fun n =>
    if n.Prime then 0 else ArithmeticFunction.vonMangoldt n / Real.sqrt n with hg
  have hterm : ∀ k : Fin N, ‖powerAtomCoeff N k‖ = g ((k : ℕ) + 1) := by
    intro k
    unfold powerAtomCoeff atomCoeff
    simp only [hg]
    split_ifs with hp
    · simp
    · rw [Complex.norm_real, Real.norm_eq_abs, vonMangoldtAtom_eq_div_sqrt (by omega),
        abs_of_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))]
  have hsum : ∑ k : Fin N, ‖powerAtomCoeff N k‖ =
      ∑ n ∈ Finset.Ioc 0 N with ¬ n.Prime, ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
    rw [Finset.sum_congr rfl fun k _ => hterm k, Fin.sum_univ_eq_sum_range (fun k => g (k + 1)) N,
      ← sum_Icc_one_eq_sum_range, Finset.sum_filter]
    have hIoc : Finset.Icc 1 N = Finset.Ioc 0 N := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hIoc]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hg]
    split_ifs <;> simp_all
  rw [hsum]
  exact sum_nonprime_vonMangoldt_div_sqrt_le hN

/-- `|D_N(y)| ≤ |P_N(y)| + 2 log N + 4 log 4 + 16`. -/
theorem abs_primeCosine_le_primePart {N : ℕ} (hN : 1 ≤ N) (y : ℝ) :
    |primeCosine N y| ≤ ‖primePart N y‖ + powerBound N := by
  refine (abs_primeCosine_le_norm_dirPoly N y).trans ?_
  rw [dirPoly_atomCoeff_eq]
  refine (norm_add_le _ _).trans ?_
  gcongr
  exact (norm_dirPoly_le_sum N _ y).trans (sum_norm_powerAtomCoeff_le hN)

/-- The diagonal `Σ_{n ≤ N} Λ(n)²/n ≤ log N (log N + log 4 + 4)`. -/
theorem sum_norm_sq_atomCoeff_le {N : ℕ} (hN : 1 ≤ N) :
    ∑ k : Fin N, ‖atomCoeff N k‖ ^ 2 ≤ Real.log N * (Real.log N + (Real.log 4 + 4)) := by
  have hl0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hnorm : ∀ k : Fin N, ‖atomCoeff N k‖ ^ 2 = vonMangoldtAtom ((k : ℕ) + 1) ^ 2 := fun k => by
    rw [atomCoeff, Complex.norm_real, Real.norm_eq_abs, sq_abs]
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

/-- The prime coefficient mass `S = Σ_{p ≤ N} Λ(p)²/p`. -/
def primeMass (N : ℕ) : ℝ := ∑ k : Fin N, ‖primeAtomCoeff N k‖ ^ 2

theorem primeMass_nonneg (N : ℕ) : 0 ≤ primeMass N :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem primeMass_le {N : ℕ} (hN : 1 ≤ N) :
    primeMass N ≤ Real.log N * (Real.log N + (Real.log 4 + 4)) := by
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) (sum_norm_sq_atomCoeff_le hN)
  unfold primeAtomCoeff
  split_ifs
  · exact le_rfl
  · rw [norm_zero, zero_pow two_ne_zero]
    exact sq_nonneg _

/-! ### High moments of the prime part -/

/-- **The `2k`-th moment of the prime part on any interval of length `T`.** -/
theorem integral_norm_primePart_pow_le (N k : ℕ) (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    ∫ y in a..(a + T), ‖primePart N y‖ ^ (2 * k) ≤
      (T + 208 * (N : ℝ) ^ k) * ((k : ℝ) ^ k * primeMass N ^ k) := by
  set b := Sieve.dirichletPowerConvolutionConvPow k N (primeAtomCoeff N) with hb
  have hpt : ∀ y, ‖primePart N y‖ ^ (2 * k) = ‖Sieve.dirPoly (N ^ k) b y‖ ^ 2 := by
    intro y
    rw [hb, Sieve.dirichletPowerConvolutionDirPoly_convPow, norm_pow, ← pow_mul]
    unfold primePart
    ring_nf
  have hsupp : ∀ n : Fin N, primeAtomCoeff N n ≠ 0 → Nat.Prime ((n : ℕ) + 1) := by
    intro n hn
    unfold primeAtomCoeff at hn
    split_ifs at hn with hp
    · exact hp
    · exact absurd rfl hn
  have hmass := Sieve.sum_normSq_convPow_le_of_prime_support k N (primeAtomCoeff N) hsupp
  have hmv := Sieve.dirichlet_meanValue_sharp_window (N ^ k) b a (a + T)
  have hupper := (abs_le.1 hmv).2
  rw [add_sub_cancel_left] at hupper
  have hweight : ∑ j : Fin (N ^ k), ((j : ℝ) + 1) * ‖b j‖ ^ 2 ≤
      (N : ℝ) ^ k * ∑ j : Fin (N ^ k), ‖b j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    have hj : (j : ℕ) + 1 ≤ N ^ k := j.isLt
    exact_mod_cast hj
  have hS0 : 0 ≤ ∑ j : Fin (N ^ k), ‖b j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [intervalIntegral.integral_congr (fun y _ => hpt y)]
  calc ∫ y in a..(a + T), ‖Sieve.dirPoly (N ^ k) b y‖ ^ 2
      ≤ T * ∑ j : Fin (N ^ k), ‖b j‖ ^ 2 + 208 * ∑ j : Fin (N ^ k), ((j : ℝ) + 1) * ‖b j‖ ^ 2 := by
        linarith
    _ ≤ (T + 208 * (N : ℝ) ^ k) * ∑ j : Fin (N ^ k), ‖b j‖ ^ 2 := by nlinarith
    _ ≤ _ := mul_le_mul_of_nonneg_left hmass (by positivity)

/-! ### The prime-part field and its moments -/

/-- The prime-part field `∫ |P_N(γ + t)| w_R(t) dt`. -/
def primePartField (N : ℕ) (R γ : ℝ) : ℝ := ∫ t, ‖primePart N (γ + t)‖ * fieldWeight R t

/-- The moment field `∫ |P_N(γ + t)|ⁿ w_R(t) dt`. -/
def primePartMoment (N n : ℕ) (R γ : ℝ) : ℝ := ∫ t, ‖primePart N (γ + t)‖ ^ n * fieldWeight R t

/-- The uniform bound `Σ_p Λ(p)/√p` of the prime part. -/
def primePartBound (N : ℕ) : ℝ := ∑ k : Fin N, ‖primeAtomCoeff N k‖

theorem norm_primePart_le (N : ℕ) (y : ℝ) : ‖primePart N y‖ ≤ primePartBound N :=
  norm_dirPoly_le_sum N _ y

theorem continuous_primePart (N : ℕ) : Continuous (primePart N) := by
  unfold primePart Sieve.dirPoly
  fun_prop

theorem continuous_fieldWeight (R : ℝ) : Continuous (fieldWeight R) := by
  unfold fieldWeight
  refine Continuous.inv₀ (by fun_prop) fun t => ?_
  positivity

theorem integrable_primePart_pow_mul_fieldWeight (N n : ℕ) {R : ℝ} (hR : 0 < R) (γ : ℝ) :
    Integrable fun t => ‖primePart N (γ + t)‖ ^ n * fieldWeight R t := by
  refine ((integrable_fieldWeight hR).const_mul (primePartBound N ^ n)).mono'
    ((((continuous_primePart N).comp (continuous_const.add continuous_id)).norm.pow n).mul
      (continuous_fieldWeight R)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (fieldWeight_pos R t).le)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_primePart_le N _) n)
    (fieldWeight_pos R t).le

theorem integrable_primePart_mul_fieldWeight (N : ℕ) {R : ℝ} (hR : 0 < R) (γ : ℝ) :
    Integrable fun t => ‖primePart N (γ + t)‖ * fieldWeight R t := by
  simpa only [pow_one] using integrable_primePart_pow_mul_fieldWeight N 1 hR γ

/-- The field of `D_N` is at most the prime-part field plus the prime powers. -/
theorem primeField_le_primePartField {N : ℕ} (hN : 1 ≤ N) {R : ℝ} (hR : 0 < R) (γ : ℝ) :
    primeField N R γ ≤ primePartField N R γ + powerBound N * (π / R) := by
  have hi1 := integrable_primePart_mul_fieldWeight N hR γ
  have hi2 : Integrable fun t => powerBound N * fieldWeight R t :=
    (integrable_fieldWeight hR).const_mul _
  have hi0 : Integrable fun t => |primeCosine N (γ + t)| * fieldWeight R t := by
    refine ((integrable_fieldWeight hR).const_mul (primeCosineBound N)).mono'
      (((continuous_primeCosine N).comp (continuous_const.add continuous_id)).abs.mul
        (continuous_fieldWeight R)).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (fieldWeight_pos R t).le)]
    exact mul_le_mul_of_nonneg_right (abs_primeCosine_le N _) (fieldWeight_pos R t).le
  unfold primeField primePartField
  rw [← integral_fieldWeight hR, ← integral_const_mul, ← integral_add hi1 hi2]
  refine integral_mono hi0 (hi1.add hi2) fun t => ?_
  have h := abs_primeCosine_le_primePart hN (γ + t)
  have hw := (fieldWeight_pos R t).le
  calc |primeCosine N (γ + t)| * fieldWeight R t
      ≤ (‖primePart N (γ + t)‖ + powerBound N) * fieldWeight R t :=
        mul_le_mul_of_nonneg_right h hw
    _ = ‖primePart N (γ + t)‖ * fieldWeight R t + powerBound N * fieldWeight R t := by ring

/-- Bernoulli in Young form: `(m + 1) s^m x ≤ x^{m+1} + m s^{m+1}` for `x ≥ 0 < s`. -/
theorem bernoulli_young {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) (m : ℕ) :
    ((m : ℝ) + 1) * s ^ m * x ≤ x ^ (m + 1) + m * s ^ (m + 1) := by
  have ha : (-2 : ℝ) ≤ x / s - 1 := by
    have : 0 ≤ x / s := div_nonneg hx hs.le
    linarith
  have hb := one_add_mul_le_pow ha (m + 1)
  rw [show (1 : ℝ) + (x / s - 1) = x / s by ring, div_pow] at hb
  have hsp : 0 < s ^ (m + 1) := pow_pos hs _
  rw [le_div_iff₀ hsp] at hb
  have hexp : (1 + ((m + 1 : ℕ) : ℝ) * (x / s - 1)) * s ^ (m + 1) =
      ((m : ℝ) + 1) * s ^ m * x - m * s ^ (m + 1) := by
    rw [pow_succ]
    push_cast
    field_simp
    ring
  linarith

theorem young_primePartField (N : ℕ) {R : ℝ} (hR : 0 < R) {s : ℝ} (hs : 0 < s) (m : ℕ)
    (γ : ℝ) :
    ((m : ℝ) + 1) * s ^ m * primePartField N R γ ≤
      primePartMoment N (m + 1) R γ + m * s ^ (m + 1) * (π / R) := by
  have hi1 := integrable_primePart_mul_fieldWeight N hR γ
  have hi2 := integrable_primePart_pow_mul_fieldWeight N (m + 1) hR γ
  have hi3 : Integrable fun t => (m : ℝ) * s ^ (m + 1) * fieldWeight R t :=
    (integrable_fieldWeight hR).const_mul _
  unfold primePartField primePartMoment
  rw [← integral_fieldWeight hR, ← integral_const_mul, ← integral_const_mul, ← integral_add hi2 hi3]
  refine integral_mono (hi1.const_mul _) (hi2.add hi3) fun t => ?_
  have h := bernoulli_young (norm_nonneg (primePart N (γ + t))) hs m
  have hw := (fieldWeight_pos R t).le
  calc ((m : ℝ) + 1) * s ^ m * (‖primePart N (γ + t)‖ * fieldWeight R t)
      = (((m : ℝ) + 1) * s ^ m * ‖primePart N (γ + t)‖) * fieldWeight R t := by ring
    _ ≤ (‖primePart N (γ + t)‖ ^ (m + 1) + m * s ^ (m + 1)) * fieldWeight R t :=
        mul_le_mul_of_nonneg_right h hw
    _ = _ := by ring

/-- **The moment inside the field.** `Y ≤ ∫ |P_N| w` forces `Y^{m+1} (R/π)^m ≤ ∫ |P_N|^{m+1} w`. -/
theorem pow_le_primePartMoment_of_le {N : ℕ} {R Y γ : ℝ} (hR : 0 < R) (hY : 0 < Y) (m : ℕ)
    (hle : Y ≤ primePartField N R γ) :
    Y ^ (m + 1) * (R / π) ^ m ≤ primePartMoment N (m + 1) R γ := by
  set s := Y * (R / π) with hs_def
  have hs : 0 < s := by positivity
  have h := young_primePartField N hR hs m γ
  have h1 : ((m : ℝ) + 1) * s ^ m * Y ≤ ((m : ℝ) + 1) * s ^ m * primePartField N R γ :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  set Z := s ^ m * Y with hZ
  have h2 : (m : ℝ) * s ^ (m + 1) * (π / R) = m * Z := by
    rw [hZ, hs_def, pow_succ]
    field_simp
  have h3 : Y ^ (m + 1) * (R / π) ^ m = Z := by
    rw [hZ, hs_def, mul_pow, pow_succ]
    ring
  have key : (m : ℝ) * Z + Z ≤ primePartMoment N (m + 1) R γ + m * Z := by
    have : (m : ℝ) * Z + Z = ((m : ℝ) + 1) * s ^ m * Y := by rw [hZ]; ring
    rw [this, ← h2]
    exact h1.trans h
  rw [h3]
  linarith

theorem continuous_primePartMoment (N n : ℕ) {R : ℝ} (hR : 0 < R) :
    Continuous (primePartMoment N n R) := by
  unfold primePartMoment
  refine continuous_of_dominated (bound := fun t => primePartBound N ^ n * fieldWeight R t)
    (fun γ => ?_) (fun γ => Eventually.of_forall fun t => ?_)
    ((integrable_fieldWeight hR).const_mul _) (Eventually.of_forall fun t => ?_)
  · exact ((((continuous_primePart N).comp (continuous_const.add continuous_id)).norm.pow n).mul
      (continuous_fieldWeight R)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (fieldWeight_pos R t).le)]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_primePart_le N _) n)
      (fieldWeight_pos R t).le
  · exact (((continuous_primePart N).comp (continuous_id.add continuous_const)).norm.pow n).mul
      continuous_const

theorem primePartMoment_nonneg (N n : ℕ) (R γ : ℝ) : 0 ≤ primePartMoment N n R γ :=
  integral_nonneg fun t => mul_nonneg (pow_nonneg (norm_nonneg _) _) (fieldWeight_pos R t).le

/-- **The mean of the moment field.** `∫_T^{2T} ∫ |P_N(γ+t)|^{2k} w = (π/R)(T + 208N^k) k^k S^k`. -/
theorem integral_primePartMoment_le (N k : ℕ) {T R : ℝ} (hT : 0 < T) (hR : 0 < R) :
    ∫ γ in Icc T (2 * T), primePartMoment N (2 * k) R γ ≤
      (π / R) * ((T + 208 * (N : ℝ) ^ k) * ((k : ℝ) ^ k * primeMass N ^ k)) := by
  have hw := integrable_fieldWeight hR
  have hprod : Integrable (Function.uncurry fun γ t : ℝ =>
      ‖primePart N (γ + t)‖ ^ (2 * k) * fieldWeight R t)
      ((volume.restrict (Icc T (2 * T))).prod volume) := by
    have hdom : Integrable (fun z : ℝ × ℝ => primePartBound N ^ (2 * k) * fieldWeight R z.2)
        ((volume.restrict (Icc T (2 * T))).prod volume) := by
      have hone : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc T (2 * T))) :=
        integrable_const_iff.mpr (Or.inr (by
          rw [isFiniteMeasure_restrict]
          exact (isCompact_Icc.measure_lt_top).ne))
      have h := hone.mul_prod (hw.const_mul (primePartBound N ^ (2 * k)))
      simpa only [one_mul] using h
    refine hdom.mono' ?_ (Eventually.of_forall fun z => ?_)
    · exact ((((continuous_primePart N).comp (continuous_fst.add continuous_snd)).norm.pow
        (2 * k)).mul ((continuous_fieldWeight R).comp continuous_snd)).aestronglyMeasurable
    · simp only [Function.uncurry]
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (norm_nonneg _) _) (fieldWeight_pos R _).le)]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (norm_primePart_le N _) _)
        (fieldWeight_pos R _).le
  unfold primePartMoment
  rw [integral_integral_swap hprod]
  have hinner : ∀ t : ℝ, ∫ γ in Icc T (2 * T), ‖primePart N (γ + t)‖ ^ (2 * k) * fieldWeight R t ≤
      ((T + 208 * (N : ℝ) ^ k) * ((k : ℝ) ^ k * primeMass N ^ k)) * fieldWeight R t := by
    intro t
    have hin : ∫ γ in Icc T (2 * T), ‖primePart N (γ + t)‖ ^ (2 * k) * fieldWeight R t
        = (∫ y in (T + t)..(T + t + T), ‖primePart N y‖ ^ (2 * k)) * fieldWeight R t := by
      rw [integral_mul_const, integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : T ≤ 2 * T),
        intervalIntegral.integral_comp_add_right (fun y => ‖primePart N y‖ ^ (2 * k)) t]
      congr 2
      ring
    rw [hin]
    exact mul_le_mul_of_nonneg_right (integral_norm_primePart_pow_le N k _ hT.le)
      (fieldWeight_pos R t).le
  have hmono : ∫ t, ∫ γ in Icc T (2 * T), ‖primePart N (γ + t)‖ ^ (2 * k) * fieldWeight R t ≤
      ∫ t, ((T + 208 * (N : ℝ) ^ k) * ((k : ℝ) ^ k * primeMass N ^ k)) * fieldWeight R t := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun t => ?_) (hw.const_mul _)
      (Eventually.of_forall hinner)
    exact integral_nonneg fun γ => mul_nonneg (pow_nonneg (norm_nonneg _) _) (fieldWeight_pos R t).le
  refine hmono.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_fieldWeight hR]
  ring

/-- **Markov on the moment field.** -/
theorem volume_primePartMoment_ge_le (N k : ℕ) {T R Z : ℝ} (hT : 0 < T) (hR : 0 < R)
    (hZ : 0 < Z) :
    volume {γ | γ ∈ Icc T (2 * T) ∧ Z ≤ primePartMoment N (2 * k) R γ} ≤
      ENNReal.ofReal ((π / R) * ((T + 208 * (N : ℝ) ^ k) * ((k : ℝ) ^ k * primeMass N ^ k)) / Z) := by
  have hc := continuous_primePartMoment N (2 * k) hR
  have hint : Integrable (primePartMoment N (2 * k) R) (volume.restrict (Icc T (2 * T))) :=
    hc.continuousOn.integrableOn_compact isCompact_Icc
  have hmeas : MeasurableSet {γ | Z ≤ primePartMoment N (2 * k) R γ} :=
    (isClosed_le continuous_const hc).measurableSet
  have hfin : volume.restrict (Icc T (2 * T)) {γ | Z ≤ primePartMoment N (2 * k) R γ} ≠ ⊤ := by
    rw [Measure.restrict_apply hmeas]
    exact ((measure_mono inter_subset_right).trans_lt isCompact_Icc.measure_lt_top).ne
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Icc T (2 * T)))
    (Eventually.of_forall (primePartMoment_nonneg N (2 * k) R)) hint Z
  have hmean := integral_primePartMoment_le N k hT hR
  have hset : {γ | γ ∈ Icc T (2 * T) ∧ Z ≤ primePartMoment N (2 * k) R γ}
      = {γ | Z ≤ primePartMoment N (2 * k) R γ} ∩ Icc T (2 * T) := by
    ext γ
    simp only [mem_setOf_eq, mem_inter_iff]
    tauto
  rw [hset, ← Measure.restrict_apply hmeas, ← ENNReal.ofReal_toReal hfin]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ hZ, mul_comm]
  exact hmarkov.trans hmean

/-! ### Gaussian tails of the bad heights -/

theorem powerBound_le_two_mul (N : ℕ) :
    powerBound N ≤ 2 * (Real.log N + fieldConstant) := by
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold powerBound fieldConstant
  nlinarith

/-- **Local positivity with Gaussian bad heights.** Outside a set of measure
`(T + 208 N^k) k^k (4δ²)^k`, independent of the test, the form exceeds its archimedean main term minus
`(κ/(Rδ)) S_R(F₀)²` and the pole term. -/
theorem exists_bad_heights_moment {T δ R : ℝ} {N k : ℕ} (hN : 1 ≤ N) (hk : 1 ≤ k) (hT : 0 < T)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (hR : 0 < R) :
    ∃ B : Set ℝ,
      volume B ≤ ENNReal.ofReal ((T + 208 * (N : ℝ) ^ k) * ((k : ℝ) ^ k * (4 * δ ^ 2) ^ k)) ∧
      ∀ γ ∈ Icc T (2 * T), γ ∉ B → ∀ A : ℝ, 0 ≤ A → Real.exp (2 * A) ≤ N →
        ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ → (∀ u : ℝ, A < |u| → F₀ u = 0) →
          (Real.log (2 + |γ|) / 2 - (10 + Real.log 4)) * (∫ u, F₀ u ^ 2)
              - (Real.log N + fieldConstant) / (R * δ) * shapeNorm R F₀ ^ 2
              - 4 * (Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + γ ^ 2)) ^ 2 ≤
            fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
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
  · -- every bad height has a large moment field
    set m := 2 * k - 1 with hm
    have hm1 : m + 1 = 2 * k := by omega
    set Y : ℝ := y / 2 with hYdef
    have hY0 : 0 < Y := by positivity
    have hpow : powerBound N * (π / R) ≤ Y := by
      have h1 := powerBound_le_two_mul N
      have h2 : 2 * κ ≤ κ / (2 * δ) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have h3 : powerBound N * (π / R) ≤ κ / (2 * δ) * (π / R) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) (by positivity)
      refine h3.trans (le_of_eq ?_)
      rw [hYdef, hy]
      field_simp
    set Z : ℝ := Y ^ (m + 1) * (R / π) ^ m with hZdef
    have hZ0 : 0 < Z := by positivity
    have hsub : {γ | γ ∈ Icc T (2 * T) ∧ y ≤ primeField N R γ} ⊆
        {γ | γ ∈ Icc T (2 * T) ∧ Z ≤ primePartMoment N (2 * k) R γ} := by
      rintro γ ⟨hγ, hbad⟩
      refine ⟨hγ, ?_⟩
      have hfield : Y ≤ primePartField N R γ := by
        have := primeField_le_primePartField hN hR γ
        have hyY : y = 2 * Y := by rw [hYdef]; ring
        linarith
      rw [← hm1]
      exact pow_le_primePartMoment_of_le hR hY0 m hfield
    refine (measure_mono hsub).trans ((volume_primePartMoment_ge_le N k hT hR hZ0).trans
      (ENNReal.ofReal_le_ofReal ?_))
    -- the arithmetic: `(π/R)/Y = 2δ/κ` and `S ≤ κ²`
    set q : ℝ := π / (R * Y) with hq
    have hq0 : 0 < q := by positivity
    have hqval : q = 2 * δ / κ := by
      rw [hq, hYdef, hy]
      field_simp
    have hqY : q * Y = π / R := by
      rw [hq]
      field_simp
    have hprod : q ^ (m + 1) * Z = π / R := by
      calc q ^ (m + 1) * Z = (q * Y) ^ (m + 1) * (R / π) ^ m := by rw [hZdef, mul_pow]; ring
        _ = (π / R) * ((π / R) * (R / π)) ^ m := by rw [hqY, mul_pow]; ring
        _ = π / R := by
          rw [show π / R * (R / π) = 1 by field_simp, one_pow, mul_one]
    have hratio : (π / R) / Z = q ^ (2 * k) := by
      rw [← hm1, div_eq_iff hZ0.ne', hprod]
    have hS := primeMass_le hN
    have hSκ : primeMass N ≤ κ ^ 2 := by
      refine hS.trans ?_
      have hc := fieldConstant_pos
      have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      rw [hκ]
      unfold fieldConstant at hc ⊢
      nlinarith
    have hSq : primeMass N * q ^ 2 ≤ 4 * δ ^ 2 := by
      rw [hqval, div_pow]
      have hκ2 : 0 < κ ^ 2 := by positivity
      rw [mul_div_assoc', div_le_iff₀ hκ2]
      have := mul_le_mul_of_nonneg_left hSκ (by positivity : (0 : ℝ) ≤ (2 * δ) ^ 2)
      nlinarith
    have hT208 : 0 ≤ T + 208 * (N : ℝ) ^ k := by positivity
    have hS0 := primeMass_nonneg N
    calc (π / R) * ((T + 208 * (N : ℝ) ^ k) * ((k : ℝ) ^ k * primeMass N ^ k)) / Z
        = (T + 208 * (N : ℝ) ^ k) * ((k : ℝ) ^ k * (primeMass N * q ^ 2) ^ k) := by
          rw [mul_div_right_comm, hratio, mul_pow, pow_mul]
          ring
      _ ≤ (T + 208 * (N : ℝ) ^ k) * ((k : ℝ) ^ k * (4 * δ ^ 2) ^ k) := by
          gcongr
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

/-- **Local Weil positivity with Gaussian bad heights, explicit form.** With `A = δ/(64M²) log T`,
`δ ≤ 1/4`, `1 ≤ k`, `kδ ≤ 8M²`, once `log T` exceeds the aperture threshold and `2k`, the heights in
`[T, 2T]` where some test of shape `M` fails positivity have measure `≤ 209 k^k (4δ²)^k T`. -/
theorem weilPositive_quadrature_moment_of_le {δ M T : ℝ} {k : ℕ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hM : 1 ≤ M) (hk : 1 ≤ k) (hkδ : (k : ℝ) * δ ≤ 8 * M ^ 2)
    (hT0 : 0 < T) (hTA : apertureThreshold (δ / (64 * M ^ 2)) ≤ Real.log T)
    (hTk : 2 * (k : ℝ) ≤ Real.log T) :
    ∃ B : Set ℝ, volume B ≤ ENNReal.ofReal (209 * ((k : ℝ) ^ k * (4 * δ ^ 2) ^ k) * T) ∧
      ∀ γ ∈ Icc T (2 * T), γ ∉ B → ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
        (∀ u : ℝ, δ / (64 * M ^ 2) * Real.log T < |u| → F₀ u = 0) →
        shapeNorm (δ / (64 * M ^ 2) * Real.log T) F₀ ^ 2 ≤
          M ^ 2 * (δ / (64 * M ^ 2) * Real.log T) * (∫ u, F₀ u ^ 2) →
        0 < ∫ u, F₀ u ^ 2 →
        0 < fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  have hM0 : M ≠ 0 := by linarith
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hlam0 : 0 < δ / (64 * M ^ 2) := by positivity
  have hC₁0 : 0 < 10 + Real.log 4 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  have hc0 := fieldConstant_pos
  have hLC : 8 * (10 + Real.log 4) + 8 ≤ Real.log T := (le_max_left _ _).trans hTA
  have hLA : (1 + fieldConstant + 2) / (δ / (64 * M ^ 2)) + 8 ≤ Real.log T :=
    (le_max_right _ _).trans hTA
  have hL0 : 0 < Real.log T := by linarith
  obtain ⟨A, hAeq⟩ : ∃ A : ℝ, A = δ / (64 * M ^ 2) * Real.log T := ⟨_, rfl⟩
  have hA0 : 0 < A := by
    rw [hAeq]
    positivity
  have hAbig : 1 + fieldConstant + 2 ≤ A := by
    have h := (div_le_iff₀ hlam0).mp
      (show (1 + fieldConstant + 2) / (δ / (64 * M ^ 2)) ≤ Real.log T by linarith)
    rw [hAeq, mul_comm]
    exact h
  have hAT : A ≤ Real.log T / 64 := by
    rw [hAeq]
    have : δ / (64 * M ^ 2) ≤ 1 / 64 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  obtain ⟨N, hN1, hNA, hNT, hlogN⟩ :=
    exists_polynomial_length hA0.le hT0 (show 2 * A + 1 ≤ Real.log T by linarith)
  -- `N^k ≤ T`: `k log N ≤ 2kA + k ≤ log T/4 + log T/2`
  have hNk : (N : ℝ) ^ k ≤ T := by
    have hkA : 2 * (k : ℝ) * A ≤ Real.log T / 4 := by
      rw [hAeq]
      have h := mul_le_mul_of_nonneg_right hkδ (by positivity : (0 : ℝ) ≤ Real.log T / (32 * M ^ 2))
      have hrw : 2 * (k : ℝ) * (δ / (64 * M ^ 2) * Real.log T) =
          (k : ℝ) * δ * (Real.log T / (32 * M ^ 2)) := by ring
      rw [hrw]
      refine h.trans (le_of_eq ?_)
      field_simp
      ring
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hlogk : (k : ℝ) * Real.log N ≤ Real.log T := by
      have := mul_le_mul_of_nonneg_left hlogN hk0
      nlinarith
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    calc (N : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log N) := by
          rw [← Real.log_pow, Real.exp_log (by positivity)]
      _ ≤ Real.exp (Real.log T) := Real.exp_le_exp.mpr hlogk
      _ = T := Real.exp_log hT0
  obtain ⟨B, hB, hgood⟩ := exists_bad_heights_moment hN1 hk hT0 hδ hδ4 hA0
  refine ⟨B, hB.trans (ENNReal.ofReal_le_ofReal ?_), fun γ hγ hγB F₀ hF₀ hF₀c hsupp hshape hpos => ?_⟩
  · have hK : 0 ≤ (k : ℝ) ^ k * (4 * δ ^ 2) ^ k := by positivity
    nlinarith
  rw [← hAeq] at hsupp hshape
  have hbase := hgood γ hγ hγB A hA0.le hNA F₀ hF₀ hF₀c hsupp
  have hγT : T ≤ γ := hγ.1
  have hγ0 : 0 < γ := lt_of_lt_of_le hT0 hγT
  have hlogγ : Real.log T ≤ Real.log (2 + |γ|) := by
    rw [abs_of_pos hγ0]
    exact Real.log_le_log hT0 (by linarith)
  have hfield := field_term_le hδ hM0 hL0 hA0 (show Real.log N + fieldConstant ≤ 3 * A by linarith)
    hAeq hshape
  have hexpA : Real.exp A ≤ T := by
    have h := Real.exp_le_exp.mpr (show A ≤ Real.log T by linarith)
    rwa [Real.exp_log hT0] at h
  have hT2 : 2 ≤ T := by
    have h := Real.exp_le_exp.mpr (show (1 : ℝ) ≤ Real.log T by linarith)
    rw [Real.exp_log hT0] at h
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    linarith
  have hpole₀ := pole_term_le hT2 hγT hexpA (envelopeWindowNorm_nonneg F₀)
    (envelopeWindowNorm_le_shapeNorm (show 1 ≤ A by linarith) F₀)
  have hshape' : shapeNorm A F₀ ^ 2 ≤ 1 / 64 * Real.log T * ∫ u, F₀ u ^ 2 := by
    refine hshape.trans ?_
    rw [hAeq, shape_scale_eq hM0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (by linarith) hL0.le) hpos.le
  have hmain : (Real.log T / 2 - (10 + Real.log 4)) * (∫ u, F₀ u ^ 2) ≤
      (Real.log (2 + |γ|) / 2 - (10 + Real.log 4)) * ∫ u, F₀ u ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) hpos.le
  exact closing_inequality hpos hLC hC₁0 hfield (hpole₀.trans hshape') (by linarith only [hbase, hmain])

/-- **Local Weil positivity with Gaussian bad heights.** For `δ ≤ 1/4`, `1 ≤ k`, `kδ ≤ 8M²` and
`A = δ/(64M²) log T`: eventually, outside a set of heights of measure `209 k^k (4δ²)^k T`, independent
of the test, every real `F₀ ∈ C²_c([−A, A])` of shape `M` has `Q_γ(F₀) > 0`. -/
theorem exists_weilPositive_quadrature_moment {δ M : ℝ} {k : ℕ} (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4)
    (hM : 1 ≤ M) (hk : 1 ≤ k) (hkδ : (k : ℝ) * δ ≤ 8 * M ^ 2) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∃ B : Set ℝ,
      volume B ≤ ENNReal.ofReal (209 * ((k : ℝ) ^ k * (4 * δ ^ 2) ^ k) * T) ∧
      ∀ γ ∈ Icc T (2 * T), γ ∉ B → ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
        (∀ u : ℝ, δ / (64 * M ^ 2) * Real.log T < |u| → F₀ u = 0) →
        shapeNorm (δ / (64 * M ^ 2) * Real.log T) F₀ ^ 2 ≤
          M ^ 2 * (δ / (64 * M ^ 2) * Real.log T) * (∫ u, F₀ u ^ 2) →
        0 < ∫ u, F₀ u ^ 2 →
        0 < fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  refine ⟨Real.exp (max (apertureThreshold (δ / (64 * M ^ 2))) (2 * k)), fun T hT => ?_⟩
  have hexp0 := Real.exp_pos (max (apertureThreshold (δ / (64 * M ^ 2))) (2 * k))
  have hL : max (apertureThreshold (δ / (64 * M ^ 2))) (2 * k) ≤ Real.log T := by
    have := Real.log_le_log hexp0 hT
    rwa [Real.log_exp] at this
  exact weilPositive_quadrature_moment_of_le hδ hδ4 hM hk hkδ (hexp0.trans_le hT)
    ((le_max_left _ _).trans hL) ((le_max_right _ _).trans hL)

/-- **Exponentially rare bad heights.** For `δ ≤ 1/(64M²)` the bad heights of local Weil positivity at
aperture `A = δ/(64M²) log T` have measure `≤ 418 e^{−5M²/δ} T`; Markov gives `δT`. -/
theorem exists_weilPositive_quadrature_exp_rare {δ M : ℝ} (hδ : 0 < δ) (hM : 1 ≤ M)
    (hδM : δ ≤ 1 / (64 * M ^ 2)) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∃ B : Set ℝ,
      volume B ≤ ENNReal.ofReal (418 * Real.exp (-(5 * M ^ 2 / δ)) * T) ∧
      ∀ γ ∈ Icc T (2 * T), γ ∉ B → ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
        (∀ u : ℝ, δ / (64 * M ^ 2) * Real.log T < |u| → F₀ u = 0) →
        shapeNorm (δ / (64 * M ^ 2) * Real.log T) F₀ ^ 2 ≤
          M ^ 2 * (δ / (64 * M ^ 2) * Real.log T) * (∫ u, F₀ u ^ 2) →
        0 < ∫ u, F₀ u ^ 2 →
        0 < fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hM2p : 0 < M ^ 2 := by positivity
  have hδ64 : δ * (64 * M ^ 2) ≤ 1 := (le_div_iff₀ (by positivity)).mp hδM
  have hδ1 : δ ≤ 1 / 64 := by nlinarith [mul_le_mul_of_nonneg_left hM2 hδ.le]
  have hδ4 : δ ≤ 1 / 4 := by linarith
  set k : ℕ := ⌊8 * M ^ 2 / δ⌋₊ with hk_def
  have hk_le : (k : ℝ) ≤ 8 * M ^ 2 / δ := Nat.floor_le (by positivity)
  have hk_gt : 8 * M ^ 2 / δ < k + 1 := by
    rw [hk_def]
    exact Nat.lt_floor_add_one _
  have hratio : 8 ≤ 8 * M ^ 2 / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hk1 : 1 ≤ k := by
    have : (0 : ℝ) < k := by linarith
    exact_mod_cast this
  have hkδ : (k : ℝ) * δ ≤ 8 * M ^ 2 := by
    have := mul_le_mul_of_nonneg_right hk_le hδ.le
    rwa [div_mul_cancel₀ _ hδ.ne'] at this
  set T₀ := Real.exp (max (apertureThreshold (δ / (64 * M ^ 2))) (2 * k)) with hT₀
  refine ⟨T₀, fun T hT => ?_⟩
  have hexp0 : 0 < T₀ := Real.exp_pos _
  have hL : max (apertureThreshold (δ / (64 * M ^ 2))) (2 * k) ≤ Real.log T := by
    have := Real.log_le_log hexp0 hT
    rwa [hT₀, Real.log_exp] at this
  obtain ⟨B, hB, hgood⟩ := weilPositive_quadrature_moment_of_le hδ hδ4 hM hk1 hkδ
    (hexp0.trans_le hT) ((le_max_left _ _).trans hL) ((le_max_right _ _).trans hL)
  refine ⟨B, hB.trans (ENNReal.ofReal_le_ofReal ?_), hgood⟩
  have hT0 : 0 ≤ T := hexp0.le.trans hT
  -- `k^k (4δ²)^k = (4kδ²)^k ≤ (1/2)^k ≤ 2 e^{−5M²/δ}`
  have hbase : (k : ℝ) * (4 * δ ^ 2) ≤ 1 / 2 := by
    have h1 : (k : ℝ) * (4 * δ ^ 2) = 4 * δ * ((k : ℝ) * δ) := by ring
    have h2 : 4 * δ * ((k : ℝ) * δ) ≤ 4 * δ * (8 * M ^ 2) :=
      mul_le_mul_of_nonneg_left hkδ (by positivity)
    have h3 : 4 * δ * (8 * M ^ 2) = (δ * (64 * M ^ 2)) / 2 := by ring
    linarith
  have hhalf : ((k : ℝ) ^ k * (4 * δ ^ 2) ^ k) ≤ (1 / 2 : ℝ) ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hbase k
  have hlog2 : (5 : ℝ) / 8 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hexp : (1 / 2 : ℝ) ^ k ≤ 2 * Real.exp (-(5 * M ^ 2 / δ)) := by
    have hk2 : (1 / 2 : ℝ) ^ k = Real.exp ((k : ℝ) * -Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    have h2 : (2 : ℝ) * Real.exp (-(5 * M ^ 2 / δ)) = Real.exp (Real.log 2 - 5 * M ^ 2 / δ) := by
      rw [Real.exp_sub, Real.exp_log (by norm_num), Real.exp_neg]
      field_simp
    rw [hk2, h2]
    refine Real.exp_le_exp.mpr ?_
    have hq : 0 ≤ 8 * M ^ 2 / δ := by positivity
    have h3 : 5 * M ^ 2 / δ = (5 / 8) * (8 * M ^ 2 / δ) := by ring
    have h4 : (5 / 8) * (8 * M ^ 2 / δ) ≤ Real.log 2 * ((k : ℝ) + 1) := by
      have := mul_le_mul hlog2 hk_gt.le hq (Real.log_nonneg (by norm_num))
      linarith
    nlinarith
  have hfin : 209 * ((k : ℝ) ^ k * (4 * δ ^ 2) ^ k) ≤ 418 * Real.exp (-(5 * M ^ 2 / δ)) := by
    linarith
  exact mul_le_mul_of_nonneg_right hfin hT0

/-! ### Power-saving bad heights at aperture `K log log T` -/

/-- **Power-saving bad heights at aperture `K log log T`.** For `K, M ≥ 1`, eventually in `T`, outside a
set of heights of measure `≤ T^{1 − 1/(64K)}`, every real `F₀ ∈ C²_c([−A, A])`, `A = K log log T`, of
shape `M` has `Q_γ(F₀) > 0`. Markov gives `T · O(log log T / log T)` at this aperture.
The choice is `δ = 64M²K log log T / log T` and `k = ⌊log T / (8K log log T)⌋`. -/
theorem eventually_weilPositive_loglog_aperture {K M : ℝ} (hK : 1 ≤ K) (hM : 1 ≤ M) :
    ∀ᶠ T : ℝ in atTop, ∃ B : Set ℝ,
      volume B ≤ ENNReal.ofReal (T * Real.exp (-(Real.log T / (64 * K)))) ∧
      ∀ γ ∈ Icc T (2 * T), γ ∉ B → ∀ F₀ : ℝ → ℝ, ContDiff ℝ 2 F₀ → HasCompactSupport F₀ →
        (∀ u : ℝ, K * Real.log (Real.log T) < |u| → F₀ u = 0) →
        shapeNorm (K * Real.log (Real.log T)) F₀ ^ 2 ≤
          M ^ 2 * (K * Real.log (Real.log T)) * (∫ u, F₀ u ^ 2) →
        0 < ∫ u, F₀ u ^ 2 →
        0 < fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  have hK0 : 0 < K := by linarith
  have hM2 : 1 ≤ M ^ 2 := one_le_pow₀ hM
  have hM2p : 0 < M ^ 2 := by positivity
  have hc0 := fieldConstant_pos
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  set C₁ : ℝ := max (max (8 * (10 + Real.log 4) + 8) 16) (64 * K * Real.log 209) with hC₁
  set C₂ : ℝ := max (2 * (3 + fieldConstant)) 1 with hC₂
  set C₃ : ℝ := 256 * M ^ 2 * K + 16 * K with hC₃
  set C₄ : ℝ := 2048 * M ^ 4 * K with hC₄
  have hC₃0 : 0 < C₃ := by positivity
  have hC₄0 : 0 < C₄ := by positivity
  -- the eventual inequalities in `L = log T`
  have hE : ∀ᶠ L : ℝ in atTop, C₁ ≤ L ∧ C₂ ≤ Real.log L ∧ C₃ * Real.log L ≤ L ∧
      C₄ * Real.log L ≤ Real.sqrt L := by
    have h1 := eventually_ge_atTop C₁
    have h2 := Real.tendsto_log_atTop.eventually_ge_atTop C₂
    have h3 := (Real.isLittleO_log_id_atTop.bound (inv_pos.mpr hC₃0))
    have h4 := ((Real.isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).bound (inv_pos.mpr hC₄0))
    filter_upwards [h1, h2, h3, h4, eventually_gt_atTop (1 : ℝ)] with L hL1 hL2 hL3 hL4 hL5
    have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL5.le
    refine ⟨hL1, hL2, ?_, ?_⟩
    · rw [Real.norm_of_nonneg hlogL, id, Real.norm_of_nonneg (by linarith)] at hL3
      have := mul_le_mul_of_nonneg_left hL3 hC₃0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hC₃0.ne', one_mul] at this
    · rw [Real.norm_of_nonneg hlogL, Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)] at hL4
      have := mul_le_mul_of_nonneg_left hL4 hC₄0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hC₄0.ne', one_mul, ← Real.sqrt_eq_rpow] at this
  filter_upwards [Real.tendsto_log_atTop.eventually hE, eventually_gt_atTop (0 : ℝ)] with T hT hT0
  obtain ⟨hL1, hL2, hL3, hL4⟩ := hT
  set L := Real.log T with hLdef
  set ℓ := Real.log L with hℓdef
  have hL16 : 16 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hL1)
  have hL0 : 0 < L := by linarith
  have hℓ1 : 1 ≤ ℓ := (le_max_right _ _).trans hL2
  have hℓ0 : 0 < ℓ := by linarith
  have hKℓ : 0 < K * ℓ := by positivity
  set δ : ℝ := 64 * M ^ 2 * K * ℓ / L with hδdef
  have hδ0 : 0 < δ := by positivity
  have hA : δ / (64 * M ^ 2) * L = K * ℓ := by
    rw [hδdef]
    field_simp
  have hlam : δ / (64 * M ^ 2) = K * ℓ / L := by
    rw [hδdef]
    field_simp
  have hδ4 : δ ≤ 1 / 4 := by
    rw [hδdef, div_le_iff₀ hL0]
    have : 256 * M ^ 2 * K * ℓ ≤ L := by nlinarith
    linarith
  set k : ℕ := ⌊L / (8 * K * ℓ)⌋₊ with hk_def
  have hk_le : (k : ℝ) ≤ L / (8 * K * ℓ) := Nat.floor_le (by positivity)
  have hk_gt : L / (8 * K * ℓ) < k + 1 := by
    rw [hk_def]
    exact Nat.lt_floor_add_one _
  have hk1 : 1 ≤ k := by
    refine Nat.le_floor ?_
    rw [Nat.cast_one, le_div_iff₀ (by positivity)]
    nlinarith
  have hkδ : (k : ℝ) * δ ≤ 8 * M ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hk_le hδ0.le
    refine h.trans (le_of_eq ?_)
    rw [hδdef]
    field_simp
    ring
  have hTA : apertureThreshold (δ / (64 * M ^ 2)) ≤ Real.log T := by
    rw [hlam]
    unfold apertureThreshold
    refine max_le ((le_max_left _ _).trans ((le_max_left _ _).trans hL1)) ?_
    have hfc : 3 + fieldConstant ≤ K * ℓ / 2 := by
      have := (le_max_left _ _).trans hL2
      nlinarith
    rw [div_div_eq_mul_div]
    have h1 : (1 + fieldConstant + 2) * L / (K * ℓ) ≤ L / 2 := by
      rw [div_le_div_iff₀ hKℓ (by norm_num)]
      nlinarith
    linarith
  have hTk : 2 * (k : ℝ) ≤ Real.log T := by
    have h : L / (8 * K * ℓ) ≤ L / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  obtain ⟨B, hB, hgood⟩ := weilPositive_quadrature_moment_of_le hδ0 hδ4 hM hk1 hkδ hT0 hTA hTk
  refine ⟨B, hB.trans (ENNReal.ofReal_le_ofReal ?_), fun γ hγ hγB F₀ hF₀ hF₀c hsupp hshape hpos =>
    hgood γ hγ hγB F₀ hF₀ hF₀c (by rwa [← hLdef, hA]) (by rwa [← hLdef, hA]) hpos⟩
  -- the measure: `209 (4kδ²)^k ≤ 209 e^{−kℓ/2} ≤ e^{−L/(64K)}`
  have hq : (k : ℝ) * (4 * δ ^ 2) ≤ C₄ * ℓ / L := by
    have h := mul_le_mul_of_nonneg_right hk_le (by positivity : (0 : ℝ) ≤ 4 * δ ^ 2)
    refine h.trans (le_of_eq ?_)
    rw [hδdef, hC₄]
    field_simp
    ring
  have hsqrt : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
  have hsq0 : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hexpℓ : Real.exp (-(ℓ / 2)) = 1 / Real.sqrt L := by
    rw [Real.sqrt_eq_rpow, Real.exp_neg, hℓdef, div_eq_mul_inv, Real.exp_mul, Real.exp_log hL0,
      one_div, Real.rpow_inv_natCast_pow] <;> first | rfl | norm_num
  have hqsmall : C₄ * ℓ / L ≤ Real.exp (-(ℓ / 2)) := by
    rw [hexpℓ, div_le_div_iff₀ hL0 hsq0, one_mul]
    calc C₄ * ℓ * Real.sqrt L ≤ Real.sqrt L * Real.sqrt L :=
          mul_le_mul_of_nonneg_right hL4 hsq0.le
      _ = L := hsqrt
  have hpowk : (k : ℝ) ^ k * (4 * δ ^ 2) ^ k ≤ Real.exp (-((k : ℝ) * ℓ / 2)) := by
    rw [← mul_pow]
    calc ((k : ℝ) * (4 * δ ^ 2)) ^ k ≤ Real.exp (-(ℓ / 2)) ^ k :=
          pow_le_pow_left₀ (by positivity) (hq.trans hqsmall) k
      _ = Real.exp (-((k : ℝ) * ℓ / 2)) := by
          rw [← Real.exp_nat_mul]
          ring_nf
  have hkℓ : L / (16 * K) - ℓ / 2 ≤ (k : ℝ) * ℓ / 2 := by
    have h1 : L / (8 * K * ℓ) * ℓ = L / (8 * K) := by field_simp
    have h2 : (L / (8 * K * ℓ) - 1) * ℓ ≤ (k : ℝ) * ℓ :=
      mul_le_mul_of_nonneg_right (by linarith) hℓ0.le
    have h3 : (L / (8 * K * ℓ) - 1) * ℓ = L / (8 * K) - ℓ := by rw [sub_mul, h1, one_mul]
    have h4 : L / (16 * K) = L / (8 * K) / 2 := by field_simp; ring
    linarith
  have hfinal : 209 * Real.exp (-((k : ℝ) * ℓ / 2)) ≤ Real.exp (-(L / (64 * K))) := by
    have h209 : (209 : ℝ) = Real.exp (Real.log 209) := (Real.exp_log (by norm_num)).symm
    rw [h209, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hlog209 : Real.log 209 ≤ L / (64 * K) := by
      rw [le_div_iff₀ (by positivity)]
      have := (le_max_right _ _).trans hL1
      linarith
    have hℓL : ℓ / 2 ≤ L / (32 * K) := by
      rw [le_div_iff₀ (by positivity)]
      have : 16 * K * ℓ ≤ L := by
        have : 16 * K * ℓ ≤ C₃ * ℓ := mul_le_mul_of_nonneg_right (by nlinarith) hℓ0.le
        linarith
      linarith
    have hsplit : L / (16 * K) = L / (64 * K) + L / (32 * K) + L / (64 * K) := by
      field_simp; ring
    linarith
  have hT0' : 0 ≤ T := hT0.le
  calc 209 * ((k : ℝ) ^ k * (4 * δ ^ 2) ^ k) * T ≤ 209 * Real.exp (-((k : ℝ) * ℓ / 2)) * T := by
        gcongr
    _ ≤ Real.exp (-(L / (64 * K))) * T := mul_le_mul_of_nonneg_right hfinal hT0'
    _ = T * Real.exp (-(Real.log T / (64 * K))) := by rw [hLdef]; ring

end

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
