import GaloisForLFunctions.RHTower.ZetaThreeQuartersOfPrimeSurplus
import Zeta23.Final

/-!
# Anatomy of the bandwidth-`4/3` prime-pair surplus

For an even test transform `Φ`, the half-line trigonometric moments of `Φ²` satisfy
`C⁻(y) = C⁺(y)` and `S⁻(y) = −S⁺(y)` (`Cm_eq_Cp_of_even`, `Sm_eq_neg_Sp_of_even`).  Substituting
these parity relations into `sub_mul_Aminus_eq` splits the off-diagonal difference-frequency kernel
`A⁻(y, y')` into a symmetric cosine-moment term and an antisymmetric sine-moment term
(`Aminus_eq_AminusCos_add_AminusSin`, `ppOffDiag_eq_cos_add_sin`):

`A⁻(y, y') = (C⁺(y) + C⁺(y')) (sin 2Tθ − sin Tθ) / θ + (S⁺(y') − S⁺(y)) (cos 2Tθ + cos Tθ) / θ`,
`θ = y − y'`.

This decomposition exposes three unconditional structural properties of `ppOffDiag`:

1. **Nonsingularity of the sine-moment kernel (`abs_AminusSin_le`):** Because `S⁺(y)` is Lipschitz
   with constant `∫₀ᵀ Φ(x)² |x| dx ≤ ∫_ℝ Φ(x)² |x| dx` (`abs_Sp_sub_Sp_le`), the factor `θ = y − y'`
   cancels in `AminusSin`, giving the uniform pointwise bound `|AminusSin Φ T y y'| ≤ 2 ∫_ℝ Φ(x)² |x| dx`
   for all `y, y' ∈ ℝ` with no close-pair pole.
2. **Second-moment reduction of the cosine-moment kernel (`abs_ppOffDiagCos_sub_fourier_le`):**
   Since `2 C⁺(y) = ∫_{−T}^T Φ(x)² cos(xy) dx` and `∫_ℝ Φ(x)² cos(xy) dx = 2π g(y)`, the tail
   `|C⁺(y) − π g(y)|` is at most `(2 T²)⁻¹ ∫_ℝ Φ(x)² x² dx` (`abs_Cp_sub_pi_mul_g_le`).  Applying the
   Montgomery–Vaughan Hilbert inequality to this tail replaces `C⁺(log n)` by `π g(log n)` across
   all off-diagonal prime pairs with total error
   `≤ (4 C / T²) (∫ Φ(x)² x²) Σ_{n≤X} Λ(n)² = O(T^{−2/3} log T)` at bandwidth `λ = 4/3`.
3. **Exact Dirichlet-polynomial mean-value identity (`ppOffDiagFourier_eq_primeDirichlet_integral`):**
   The Fourier-weighted cosine off-diagonal sum `ppOffDiagFourier g T X` equals
   `2π ∫_T^{2T} Re(P_g(τ) conj(P(τ))) dτ − 2π T Σ_{n≤X} a_n² g(log n)`.
-/

open MeasureTheory Real Set Finset Filter
open scoped BigOperators ArithmeticFunction
open Zeta23 Zeta23.PrimeSide

noncomputable section

namespace RHTower

/-! ## Parity of the half-line moments and the C145 split of `Aminus` -/

variable {Φ : ℝ → ℝ} {T : ℝ}

/-- For an even profile `Φ`, the left and right half-line cosine moments of `Φ²` coincide. -/
theorem Cm_eq_Cp_of_even (hΦe : ∀ x, Φ (-x) = Φ x) (T y : ℝ) :
    Cm Φ T y = Cp Φ T y := by
  unfold Cm Cp
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T)
    (fun x => Φ x ^ 2 * Real.cos (x * y))
  simp only [neg_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [hΦe, neg_mul, Real.cos_neg]

/-- For an even profile `Φ`, the left half-line sine moment of `Φ²` is the negation of the right. -/
theorem Sm_eq_neg_Sp_of_even (hΦe : ∀ x, Φ (-x) = Φ x) (T y : ℝ) :
    Sm Φ T y = -Sp Φ T y := by
  unfold Sm Sp
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := T)
    (fun x => Φ x ^ 2 * Real.sin (x * y))
  simp only [neg_zero] at h
  rw [← h, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [hΦe, neg_mul, Real.sin_neg, mul_neg]

/-- **Symmetric–antisymmetric identity for `(y − y') A⁻(y, y')`** when `Φ` is even. -/
theorem sub_mul_Aminus_eq_of_even (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦe : ∀ x, Φ (-x) = Φ x)
    {y y' : ℝ} (hθ : y - y' ≠ 0) :
    (y - y') * Aminus Φ T y y'
      = (Cp Φ T y + Cp Φ T y') * (Real.sin (2 * T * (y - y')) - Real.sin (T * (y - y')))
        + (Sp Φ T y' - Sp Φ T y) * (Real.cos (2 * T * (y - y')) + Real.cos (T * (y - y'))) := by
  rw [sub_mul_Aminus_eq hT hΦ hθ, Cm_eq_Cp_of_even hΦe, Cm_eq_Cp_of_even hΦe,
    Sm_eq_neg_Sp_of_even hΦe, Sm_eq_neg_Sp_of_even hΦe,
    show (y - y') * (2 * T) = 2 * T * (y - y') by ring,
    show (y - y') * T = T * (y - y') by ring]
  ring

/-- The cosine-moment part of the off-diagonal difference kernel `A⁻(y, y')`. -/
def AminusCos (Φ : ℝ → ℝ) (T y y' : ℝ) : ℝ :=
  (Cp Φ T y + Cp Φ T y') * (Real.sin (2 * T * (y - y')) - Real.sin (T * (y - y'))) / (y - y')

/-- The sine-moment part of the off-diagonal difference kernel `A⁻(y, y')`. -/
def AminusSin (Φ : ℝ → ℝ) (T y y' : ℝ) : ℝ :=
  (Sp Φ T y' - Sp Φ T y) * (Real.cos (2 * T * (y - y')) + Real.cos (T * (y - y'))) / (y - y')

/-- For `y ≠ y'` and even `Φ`, `A⁻(y, y')` splits into `AminusCos` and `AminusSin`. -/
theorem Aminus_eq_AminusCos_add_AminusSin (hT : 0 ≤ T) (hΦ : Continuous Φ)
    (hΦe : ∀ x, Φ (-x) = Φ x) {y y' : ℝ} (hθ : y - y' ≠ 0) :
    Aminus Φ T y y' = AminusCos Φ T y y' + AminusSin Φ T y y' := by
  unfold AminusCos AminusSin
  rw [← add_div, eq_div_iff hθ, mul_comm, sub_mul_Aminus_eq_of_even hT hΦ hΦe hθ]

/-- The cosine-moment part of the prime-pair off-diagonal sum `ppOffDiag`. -/
def ppOffDiagCos (Φ : ℝ → ℝ) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if n = m then 0 else acoef n * acoef m * AminusCos Φ T (Real.log n) (Real.log m)

/-- The sine-moment part of the prime-pair off-diagonal sum `ppOffDiag`. -/
def ppOffDiagSin (Φ : ℝ → ℝ) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if n = m then 0 else acoef n * acoef m * AminusSin Φ T (Real.log n) (Real.log m)

/-- **Exact split of `ppOffDiag` into cosine-moment and sine-moment off-diagonal sums.** -/
theorem ppOffDiag_eq_cos_add_sin (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦe : ∀ x, Φ (-x) = Φ x)
    (X : ℝ) :
    ppOffDiag Φ T X = ppOffDiagCos Φ T X + ppOffDiagSin Φ T X := by
  unfold ppOffDiag ppOffDiagCos ppOffDiagSin
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  by_cases hnm : n = m
  · simp [hnm]
  · simp only [if_neg hnm]
    have hθ : Real.log n - Real.log m ≠ 0 := by
      have hn1 := one_le_of_mem_primeRange hn
      have hm1 := one_le_of_mem_primeRange hm
      rcases lt_or_gt_of_ne hnm with hlt | hgt
      · exact sub_ne_zero.mpr (ne_of_lt (Real.log_lt_log (by exact_mod_cast hn1) (by exact_mod_cast hlt)))
      · exact sub_ne_zero.mpr (ne_of_gt (Real.log_lt_log (by exact_mod_cast hm1) (by exact_mod_cast hgt)))
    rw [Aminus_eq_AminusCos_add_AminusSin hT hΦ hΦe hθ]
    ring

/-! ## Lipschitz regularity of `Sp` and nonsingularity of `AminusSin` -/

/-- `|sin a − sin b| ≤ |a − b|` for all real `a, b`. -/
theorem abs_sin_sub_sin_le (a b : ℝ) : |Real.sin a - Real.sin b| ≤ |a - b| := by
  rw [Real.sin_sub_sin, abs_mul, abs_mul, Nat.abs_ofNat]
  have h1 : |Real.sin ((a - b) / 2)| ≤ |(a - b) / 2| := Real.abs_sin_le_abs
  have h2 : |Real.cos ((a + b) / 2)| ≤ 1 := Real.abs_cos_le_one _
  have h3 : |(a - b) / 2| = |a - b| / 2 := by rw [abs_div, Nat.abs_ofNat]
  nlinarith [abs_nonneg (Real.sin ((a - b) / 2)), abs_nonneg (a - b)]

/-- **Lipschitz continuity of the half-line sine moment `S⁺(y)`.** -/
theorem abs_Sp_sub_Sp_le (hT : 0 ≤ T) (hΦ : Continuous Φ)
    (hΦabs : Integrable fun x => Φ x ^ 2 * |x|) (y y' : ℝ) :
    |Sp Φ T y' - Sp Φ T y| ≤ |y - y'| * ∫ x, Φ x ^ 2 * |x| := by
  unfold Sp
  have h1 : Continuous fun x => Φ x ^ 2 * Real.sin (x * y') := by fun_prop
  have h2 : Continuous fun x => Φ x ^ 2 * Real.sin (x * y) := by fun_prop
  rw [← intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
    intervalIntegral.integral_of_le hT]
  have hsub : Continuous fun x => Φ x ^ 2 * Real.sin (x * y') - Φ x ^ 2 * Real.sin (x * y) :=
    h1.sub h2
  calc |∫ x in Ioc 0 T, (Φ x ^ 2 * Real.sin (x * y') - Φ x ^ 2 * Real.sin (x * y))|
      ≤ ∫ x in Ioc 0 T, |Φ x ^ 2 * Real.sin (x * y') - Φ x ^ 2 * Real.sin (x * y)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x in Ioc 0 T, |y - y'| * (Φ x ^ 2 * |x|) := by
        apply setIntegral_mono_on ((hsub.integrableOn_Icc.mono_set Ioc_subset_Icc_self).abs)
          (hΦabs.integrableOn.const_mul _) measurableSet_Ioc
        intro x _
        rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
        have hsin : |Real.sin (x * y') - Real.sin (x * y)| ≤ |x| * |y - y'| := by
          refine (abs_sin_sub_sin_le _ _).trans ?_
          rw [show x * y' - x * y = -(x * (y - y')) by ring, abs_neg, abs_mul]
        nlinarith [sq_nonneg (Φ x)]
    _ = |y - y'| * ∫ x in Ioc 0 T, Φ x ^ 2 * |x| := by rw [integral_const_mul]
    _ ≤ |y - y'| * ∫ x, Φ x ^ 2 * |x| := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact setIntegral_le_integral hΦabs (Eventually.of_forall fun x => by positivity)

/-- **Uniform pointwise bound on `AminusSin`:** the `1/(y − y')` factor cancels against the
Lipschitz difference `S⁺(y') − S⁺(y)`, so `AminusSin` has no close-pair singularity. -/
theorem abs_AminusSin_le (hT : 0 ≤ T) (hΦ : Continuous Φ)
    (hΦabs : Integrable fun x => Φ x ^ 2 * |x|) (y y' : ℝ) :
    |AminusSin Φ T y y'| ≤ 2 * ∫ x, Φ x ^ 2 * |x| := by
  unfold AminusSin
  have hI0 : 0 ≤ ∫ x, Φ x ^ 2 * |x| := integral_nonneg fun x => by positivity
  by_cases hθ : y - y' = 0
  · rw [hθ, div_zero, abs_zero]
    linarith
  · have hpos : 0 < |y - y'| := abs_pos.mpr hθ
    rw [abs_div, abs_mul, div_le_iff₀ hpos]
    have hcos : |Real.cos (2 * T * (y - y')) + Real.cos (T * (y - y'))| ≤ 2 := by
      have c1 := Real.abs_cos_le_one (2 * T * (y - y'))
      have c2 := Real.abs_cos_le_one (T * (y - y'))
      linarith [abs_add_le (Real.cos (2 * T * (y - y'))) (Real.cos (T * (y - y')))]
    have hSp := abs_Sp_sub_Sp_le hT hΦ hΦabs y y'
    nlinarith [abs_nonneg (Sp Φ T y' - Sp Φ T y),
      abs_nonneg (Real.cos (2 * T * (y - y')) + Real.cos (T * (y - y')))]

/-- **Unconditional bound on the close-pair part of `ppOffDiagSin`** at any logarithmic separation
threshold `Δ`. -/
theorem abs_ppOffDiagSin_close_le (hT : 0 ≤ T) (hΦ : Continuous Φ)
    (hΦabs : Integrable fun x => Φ x ^ 2 * |x|) (X Δ : ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        if n = m ∨ Δ < |Real.log n - Real.log m| then 0
        else acoef n * acoef m * AminusSin Φ T (Real.log n) (Real.log m)|
      ≤ (2 * ∫ x, Φ x ^ 2 * |x|) * ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          if n = m ∨ Δ < |Real.log n - Real.log m| then 0 else acoef n * acoef m := by
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun m _ => ?_)
  split_ifs with h
  · simp
  · have ha : 0 ≤ acoef n * acoef m := mul_nonneg (acoef_nonneg _) (acoef_nonneg _)
    rw [abs_mul, abs_of_nonneg ha, mul_comm (2 * _)]
    exact mul_le_mul_of_nonneg_left (abs_AminusSin_le hT hΦ hΦabs _ _) ha

/-! ## Second-moment tail of `Cp` and reduction of `ppOffDiagCos` to `ppOffDiagFourier` -/

/-- For an even continuous `Φ` and `T ≥ 0`, `2 C⁺(y) = ∫_{x ∈ [−T, T]} Φ(x)² cos(xy) dx`. -/
theorem two_mul_Cp_eq_setIntegral_Icc (hT : 0 ≤ T) (hΦ : Continuous Φ) (hΦe : ∀ x, Φ (-x) = Φ x)
    (y : ℝ) :
    2 * Cp Φ T y = ∫ x in Icc (-T) T, Φ x ^ 2 * Real.cos (x * y) := by
  have hc : Continuous fun x => Φ x ^ 2 * Real.cos (x * y) := by fun_prop
  have h1 : 2 * Cp Φ T y = Cm Φ T y + Cp Φ T y := by rw [Cm_eq_Cp_of_even hΦe]; ring
  rw [h1]
  unfold Cm Cp
  rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _),
    intervalIntegral.integral_of_le (by linarith : -T ≤ T), integral_Icc_eq_integral_Ioc]

/-- **Second-moment tail bound for the half-line cosine moment:**
`|2 C⁺(y) − ∫_ℝ Φ(x)² cos(xy) dx| ≤ T⁻² ∫_ℝ Φ(x)² x² dx`. -/
theorem abs_two_mul_Cp_sub_integral_le_sq (hT : 0 < T) (hΦ : Continuous Φ)
    (hΦe : ∀ x, Φ (-x) = Φ x) (hΦ2 : Integrable fun x => Φ x ^ 2)
    (hΦsq : Integrable fun x => Φ x ^ 2 * x ^ 2) (y : ℝ) :
    |2 * Cp Φ T y - ∫ x, Φ x ^ 2 * Real.cos (x * y)| ≤ (∫ x, Φ x ^ 2 * x ^ 2) / T ^ 2 := by
  rw [two_mul_Cp_eq_setIntegral_Icc hT.le hΦ hΦe]
  set f : ℝ → ℝ := fun x => Φ x ^ 2 * Real.cos (x * y) with hf
  have hA : Integrable ((Icc (-T) T).indicator f) :=
    (integrable_indicator_iff measurableSet_Icc).mpr
      ((by fun_prop : Continuous f).integrableOn_Icc)
  have hB : Integrable f := by
    refine hΦ2.mul_bdd (c := 1) (by fun_prop) ?_
    exact Eventually.of_forall fun x => by simpa using Real.abs_cos_le_one (x * y)
  rw [← integral_indicator measurableSet_Icc, ← integral_sub hA hB, ← integral_div]
  calc |∫ x, ((Icc (-T) T).indicator f x - f x)|
      ≤ ∫ x, |(Icc (-T) T).indicator f x - f x| := abs_integral_le_integral_abs
    _ ≤ ∫ x, Φ x ^ 2 * x ^ 2 / T ^ 2 := by
        apply integral_mono (hA.sub hB).abs (hΦsq.div_const _)
        intro x
        change |(Icc (-T) T).indicator f x - f x| ≤ Φ x ^ 2 * x ^ 2 / T ^ 2
        by_cases hx : x ∈ Icc (-T) T
        · rw [Set.indicator_of_mem hx, sub_self, abs_zero]
          positivity
        · rw [Set.indicator_of_notMem hx, zero_sub, abs_neg, hf, abs_mul,
            abs_of_nonneg (sq_nonneg _)]
          have hTx : T < |x| := not_mem_Icc_neg hx
          have hsq : T ^ 2 ≤ x ^ 2 := by
            rw [← sq_abs x]
            exact pow_le_pow_left₀ hT.le hTx.le 2
          have hcos := Real.abs_cos_le_one (x * y)
          rw [le_div_iff₀ (by positivity)]
          calc Φ x ^ 2 * |Real.cos (x * y)| * T ^ 2
              ≤ Φ x ^ 2 * 1 * x ^ 2 := by gcongr
            _ = Φ x ^ 2 * x ^ 2 := by ring

/-- Under `LocalHypsCoreW`, `|C⁺(y) − π g(y)| ≤ (2 T²)⁻¹ ∫_ℝ Φ(x)² x² dx`. -/
theorem abs_Cp_sub_pi_mul_g_le {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) (y : ℝ) :
    |Cp F.Phi p.T y - π * F.g y| ≤ (∫ x, F.Phi x ^ 2 * x ^ 2) / (2 * p.T ^ 2) := by
  have h := abs_two_mul_Cp_sub_integral_le_sq hT hF.Phi_contDiff.continuous hF.Phi_even
    hF.Phi_sq_integrable hF.Phi_sq_mul_sq_integrable y
  rw [hF.Phi_sq_fourier y] at h
  have e : Cp F.Phi p.T y - π * F.g y = (2 * Cp F.Phi p.T y - 2 * π * F.g y) / 2 := by ring
  have e2 : (∫ x, F.Phi x ^ 2 * x ^ 2) / (2 * p.T ^ 2)
      = ((∫ x, F.Phi x ^ 2 * x ^ 2) / p.T ^ 2) / 2 := by ring
  rw [e, abs_div, abs_two, e2]
  exact div_le_div_of_nonneg_right h (by norm_num)

/-- The exact Fourier-weighted off-diagonal cosine sum, obtained by replacing `C⁺(y)` by `π g(y)`
in `ppOffDiagCos`. -/
def ppOffDiagFourier (g : ℝ → ℝ) (T X : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    if n = m then 0 else
      acoef n * acoef m * (π * (g (Real.log n) + g (Real.log m)))
        * (Real.sin (2 * T * (Real.log n - Real.log m))
          - Real.sin (T * (Real.log n - Real.log m)))
        / (Real.log n - Real.log m)

/-- **Montgomery–Vaughan bound on the replacement `C⁺(y) ↦ π g(y)` in `ppOffDiagCos`.** -/
theorem abs_ppOffDiagCos_sub_fourier_le {C cϱ : ℝ} (hMV : Zeta23.MVHilbert C) (hC : 0 ≤ C)
    {p : Setting} {F : LocalFun} (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) :
    |ppOffDiagCos F.Phi p.T p.X - ppOffDiagFourier F.g p.T p.X|
      ≤ 4 * C * ((∫ x, F.Phi x ^ 2 * x ^ 2) / p.T ^ 2)
        * ∑ n ∈ primeRange p.X, (Λ n : ℝ) ^ 2 := by
  set δ : ℝ → ℝ := fun y => Cp F.Phi p.T y - π * F.g y with hδ
  set W : ℝ := (∫ x, F.Phi x ^ 2 * x ^ 2) / (2 * p.T ^ 2) with hW
  have hW0 : 0 ≤ W := div_nonneg (integral_nonneg fun x => by positivity) (by positivity)
  have hw : ∀ n ∈ primeRange p.X, |δ (Real.log n)| ≤ W :=
    fun n _ => abs_Cp_sub_pi_mul_g_le hF hT (Real.log n)
  set Λ2 : ℝ := ∑ n ∈ primeRange p.X, (Λ n : ℝ) ^ 2 with hΛ2
  set S1 : ℝ := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X, (if n = m then (0 : ℝ) else
    (fun k => acoef k * δ (Real.log k)) n * acoef m
      * Real.sin ((2 * p.T) * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS1
  set S2 : ℝ := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X, (if n = m then (0 : ℝ) else
    acoef n * (fun k => acoef k * δ (Real.log k)) m
      * Real.sin ((2 * p.T) * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS2
  set S3 : ℝ := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X, (if n = m then (0 : ℝ) else
    (fun k => acoef k * δ (Real.log k)) n * acoef m
      * Real.sin (p.T * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS3
  set S4 : ℝ := ∑ n ∈ primeRange p.X, ∑ m ∈ primeRange p.X, (if n = m then (0 : ℝ) else
    acoef n * (fun k => acoef k * δ (Real.log k)) m
      * Real.sin (p.T * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) with hS4
  have hsplit : ppOffDiagCos F.Phi p.T p.X - ppOffDiagFourier F.g p.T p.X
      = S1 + S2 - S3 - S4 := by
    rw [ppOffDiagCos, ppOffDiagFourier, hS1, hS2, hS3, hS4]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    by_cases hnm : n = m
    · simp [hnm]
    · simp only [if_neg hnm, AminusCos, hδ]
      ring
  have hb1 : |S1| ≤ 2 * C * W * Λ2 :=
    ((MV_real hMV p.X (2 * p.T) (fun k => acoef k * δ (Real.log k)) acoef).2).trans
      (MV_size_le hC p.X hW0 hw).2
  have hb2 : |S2| ≤ 2 * C * W * Λ2 :=
    ((MV_real hMV p.X (2 * p.T) acoef (fun k => acoef k * δ (Real.log k))).2).trans
      (MV_size_le hC p.X hW0 hw).1
  have hb3 : |S3| ≤ 2 * C * W * Λ2 :=
    ((MV_real hMV p.X p.T (fun k => acoef k * δ (Real.log k)) acoef).2).trans
      (MV_size_le hC p.X hW0 hw).2
  have hb4 : |S4| ≤ 2 * C * W * Λ2 :=
    ((MV_real hMV p.X p.T acoef (fun k => acoef k * δ (Real.log k))).2).trans
      (MV_size_le hC p.X hW0 hw).1
  rw [hsplit]
  have t1 := abs_add_le S1 S2
  have t2 := abs_sub (S1 + S2) S3
  have t3 := abs_sub (S1 + S2 - S3) S4
  have htot : |S1 + S2 - S3 - S4| ≤ 8 * C * W * Λ2 := by linarith
  refine htot.trans (le_of_eq ?_)
  rw [hW]
  ring

/-! ## Exact Dirichlet-polynomial mean-value representation of `ppOffDiagFourier` -/

/-- Weighted cosine prime Dirichlet polynomial `Σ_{n≤X} a_n w(log n) cos(τ log n)`. -/
def primeDirichletCos (w : ℝ → ℝ) (X τ : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, acoef n * w (Real.log n) * Real.cos (τ * Real.log n)

/-- Weighted sine prime Dirichlet polynomial `Σ_{n≤X} a_n w(log n) sin(τ log n)`. -/
def primeDirichletSin (w : ℝ → ℝ) (X τ : ℝ) : ℝ :=
  ∑ n ∈ primeRange X, acoef n * w (Real.log n) * Real.sin (τ * Real.log n)

/-- Elementary antiderivative `∫_T^{2T} cos(τ θ) dτ = (sin(2Tθ) − sin(Tθ)) / θ` for `θ ≠ 0`. -/
theorem intervalIntegral_cos_mul_of_ne (T : ℝ) {θ : ℝ} (hθ : θ ≠ 0) :
    ∫ τ in T..(2 * T), Real.cos (τ * θ) = (Real.sin (2 * T * θ) - Real.sin (T * θ)) / θ := by
  have hd : ∀ τ ∈ uIcc T (2 * T),
      HasDerivAt (fun t => Real.sin (t * θ) / θ) (Real.cos (τ * θ)) τ := by
    intro τ _
    have h1 : HasDerivAt (fun t => t * θ) θ τ := by
      simpa using (hasDerivAt_id τ).mul_const θ
    have h2 := ((Real.hasDerivAt_sin (τ * θ)).comp τ h1).div_const θ
    rwa [mul_div_cancel_right₀ _ hθ] at h2
  have hint : IntervalIntegrable (fun τ => Real.cos (τ * θ)) volume T (2 * T) :=
    (by fun_prop : Continuous fun τ => Real.cos (τ * θ)).intervalIntegrable T (2 * T)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint, sub_div]

/-- **Integral representation of `ppOffDiagFourier`:** adding the diagonal `2π T Σ a_n² g(log n)`
completes the off-diagonal difference-frequency sum into the integral over `[T, 2T]` of the full
double sum. -/
theorem ppOffDiagFourier_eq_integral (g : ℝ → ℝ) (T X : ℝ) :
    ppOffDiagFourier g T X
      = (∫ τ in T..(2 * T), ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
          acoef n * acoef m * (π * (g (Real.log n) + g (Real.log m)))
            * Real.cos (τ * (Real.log n - Real.log m)))
        - 2 * π * T * ∑ n ∈ primeRange X, acoef n ^ 2 * g (Real.log n) := by
  set F : ℕ → ℕ → ℝ → ℝ := fun n m τ =>
    acoef n * acoef m * (π * (g (Real.log n) + g (Real.log m)))
      * Real.cos (τ * (Real.log n - Real.log m))
  have hint : ∀ n ∈ primeRange X, ∀ m ∈ primeRange X,
      IntervalIntegrable (F n m) volume T (2 * T) :=
    fun _ _ _ _ => (by fun_prop : Continuous _).intervalIntegrable _ _
  have h1 : (∫ τ in T..(2 * T), ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, F n m τ)
      = ∑ n ∈ primeRange X, ∫ τ in T..(2 * T), ∑ m ∈ primeRange X, F n m τ :=
    intervalIntegral.integral_finsetSum (a := T) (b := 2 * T) (μ := volume)
      (s := primeRange X) (f := fun n τ => ∑ m ∈ primeRange X, F n m τ)
      (fun n _ => (by fun_prop : Continuous fun τ => ∑ m ∈ primeRange X, F n m τ).intervalIntegrable _ _)
  rw [h1]
  have hinner : ∀ n ∈ primeRange X,
      (∫ τ in T..(2 * T), ∑ m ∈ primeRange X, F n m τ)
        = (∑ m ∈ primeRange X, if n = m then 0 else
            acoef n * acoef m * (π * (g (Real.log n) + g (Real.log m)))
              * (Real.sin (2 * T * (Real.log n - Real.log m))
                - Real.sin (T * (Real.log n - Real.log m)))
              / (Real.log n - Real.log m))
          + 2 * π * T * (acoef n ^ 2 * g (Real.log n)) := by
    intro n hn
    rw [intervalIntegral.integral_finsetSum (fun m hm => hint n hn m hm)]
    have hsplit : ∀ m ∈ primeRange X,
        (∫ τ in T..(2 * T), F n m τ)
          = (if n = m then 0 else
              acoef n * acoef m * (π * (g (Real.log n) + g (Real.log m)))
                * (Real.sin (2 * T * (Real.log n - Real.log m))
                  - Real.sin (T * (Real.log n - Real.log m)))
                / (Real.log n - Real.log m))
            + (if n = m then 2 * π * T * (acoef n ^ 2 * g (Real.log n)) else 0) := by
      intro m hm
      simp only [F]
      rw [intervalIntegral.integral_const_mul]
      by_cases hnm : n = m
      · subst hnm
        simp only [if_true, sub_self, mul_zero, Real.cos_zero, intervalIntegral.integral_const,
          smul_eq_mul]
        ring
      · simp only [if_neg hnm, add_zero]
        have hθ : Real.log n - Real.log m ≠ 0 := by
          have hn1 := one_le_of_mem_primeRange hn
          have hm1 := one_le_of_mem_primeRange hm
          rcases lt_or_gt_of_ne hnm with hlt | hgt
          · exact sub_ne_zero.mpr (ne_of_lt (Real.log_lt_log (by exact_mod_cast hn1) (by exact_mod_cast hlt)))
          · exact sub_ne_zero.mpr (ne_of_gt (Real.log_lt_log (by exact_mod_cast hm1) (by exact_mod_cast hgt)))
        rw [intervalIntegral_cos_mul_of_ne T hθ, mul_div_assoc]
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hn]
  rw [Finset.sum_congr rfl hinner, Finset.sum_add_distrib, ← Finset.mul_sum, add_sub_cancel_right]
  rfl

/-- Pointwise factorization of the double sum into products of cosine and sine prime Dirichlet
polynomials. -/
theorem sum_sum_cos_log_sub_eq (g : ℝ → ℝ) (X τ : ℝ) :
    (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        acoef n * acoef m * (π * (g (Real.log n) + g (Real.log m)))
          * Real.cos (τ * (Real.log n - Real.log m)))
      = 2 * π * (primeDirichletCos g X τ * primeDirichletCos (fun _ => 1) X τ
          + primeDirichletSin g X τ * primeDirichletSin (fun _ => 1) X τ) := by
  unfold primeDirichletCos primeDirichletSin
  set S := primeRange X
  have h1 : (∑ n ∈ S, acoef n * g (Real.log n) * Real.cos (τ * Real.log n))
        * (∑ m ∈ S, acoef m * 1 * Real.cos (τ * Real.log m))
      + (∑ n ∈ S, acoef n * g (Real.log n) * Real.sin (τ * Real.log n))
        * (∑ m ∈ S, acoef m * 1 * Real.sin (τ * Real.log m))
      = ∑ n ∈ S, ∑ m ∈ S, acoef n * acoef m * g (Real.log n)
          * Real.cos (τ * (Real.log n - Real.log m)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [show τ * (Real.log n - Real.log m) = τ * Real.log n - τ * Real.log m by ring,
      Real.cos_sub]
    ring
  have h2 : ∑ n ∈ S, ∑ m ∈ S, acoef n * acoef m * g (Real.log m)
        * Real.cos (τ * (Real.log n - Real.log m))
      = ∑ n ∈ S, ∑ m ∈ S, acoef n * acoef m * g (Real.log n)
        * Real.cos (τ * (Real.log n - Real.log m)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [show τ * (Real.log m - Real.log n) = -(τ * (Real.log n - Real.log m)) by ring,
      Real.cos_neg]
    ring
  have h3 : (∑ n ∈ S, ∑ m ∈ S, acoef n * acoef m * (π * (g (Real.log n) + g (Real.log m)))
        * Real.cos (τ * (Real.log n - Real.log m)))
      = π * (∑ n ∈ S, ∑ m ∈ S, acoef n * acoef m * g (Real.log n)
          * Real.cos (τ * (Real.log n - Real.log m)))
        + π * (∑ n ∈ S, ∑ m ∈ S, acoef n * acoef m * g (Real.log m)
          * Real.cos (τ * (Real.log n - Real.log m))) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [h3, h2, h1]
  ring

/-- **Exact mean-value identity for `ppOffDiagFourier`:**
`ppOffDiagFourier g T X = 2π ∫_T^{2T} (C_g(τ) C_1(τ) + S_g(τ) S_1(τ)) dτ − 2π T Σ_{n≤X} a_n² g(log n)`. -/
theorem ppOffDiagFourier_eq_primeDirichlet_integral (g : ℝ → ℝ) (T X : ℝ) :
    ppOffDiagFourier g T X
      = 2 * π * (∫ τ in T..(2 * T),
          (primeDirichletCos g X τ * primeDirichletCos (fun _ => 1) X τ
            + primeDirichletSin g X τ * primeDirichletSin (fun _ => 1) X τ))
        - 2 * π * T * ∑ n ∈ primeRange X, acoef n ^ 2 * g (Real.log n) := by
  rw [ppOffDiagFourier_eq_integral, ← intervalIntegral.integral_const_mul]
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => sum_sum_cos_log_sub_eq g X τ

/-- **Unconditional Montgomery–Vaughan bound on `ppOffDiagCos − ppOffDiagFourier`** (with `MVHilbert`
discharged from `Zeta23.paperInputs_zeta.MV`). -/
theorem exists_abs_ppOffDiagCos_sub_fourier_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {cϱ : ℝ} {p : Setting} {F : LocalFun},
      LocalHypsCoreW cϱ p F → 0 < p.T →
      |ppOffDiagCos F.Phi p.T p.X - ppOffDiagFourier F.g p.T p.X|
        ≤ 4 * C * ((∫ x, F.Phi x ^ 2 * x ^ 2) / p.T ^ 2)
          * ∑ n ∈ primeRange p.X, (Λ n : ℝ) ^ 2 := by
  obtain ⟨C, hC0, hMV⟩ := paperInputs_zeta.MV
  exact ⟨C, hC0, fun hF hT => abs_ppOffDiagCos_sub_fourier_le hMV hC0.le hF hT⟩

/-- **Exact decomposition of `primeSurplus`** into the Fourier-weighted off-diagonal cosine sum
`ppOffDiagFourier`, the cosine-moment tail `ppOffDiagCos − ppOffDiagFourier`, the nonsingular
sine-moment sum `ppOffDiagSin`, the sum-frequency term `ppSumFreq`, and the grid end correction
`endForm`. -/
theorem primeSurplus_eq_fourier_add_rem {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) (hT : 0 ≤ p.T) :
    primeSurplus p F
      = (1 / (2 * π ^ 2)) * ppOffDiagFourier F.g p.T p.X
        + (1 / (2 * π ^ 2)) * (ppOffDiagCos F.Phi p.T p.X - ppOffDiagFourier F.g p.T p.X)
        + (1 / (2 * π ^ 2)) * ppOffDiagSin F.Phi p.T p.X
        + (1 / (2 * π ^ 2)) * ppSumFreq F.Phi p.T p.X
        + endForm p F (Zeta23.nuX p.X) (Zeta23.nuX p.X) := by
  unfold primeSurplus
  rw [ppOffDiag_eq_cos_add_sin hT hF.Phi_contDiff.continuous hF.Phi_even]
  ring

/-- **At bandwidth `4/3`, the cosine-moment replacement error `ppOffDiagCos − ppOffDiagFourier` is
`O(T^{−2/3} log T)` unconditionally** — it vanishes in the limit `T → ∞` even before dividing by
the normalisation `(aL)² T ℓ₁ / 2π`. -/
theorem exists_abs_ppOffDiagCos_sub_fourier_params43_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ T in atTop,
      |ppOffDiagCos (params43.PhiR T) T (params43.X T)
          - ppOffDiagFourier (params43.g T) T (params43.X T)|
        ≤ K * (Real.log T / T ^ (2 / 3 : ℝ)) := by
  have hP := paramsValidFam_params43
  obtain ⟨TL, hTL⟩ := localHypsCoreW_eventually_fam hP
  obtain ⟨C, hC0, hMV⟩ := paperInputs_zeta.MV
  obtain ⟨C₁, hC₁⟩ := paperInputs_zeta.cheb.cheb1d
  set C₁' : ℝ := max C₁ 0
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  set B₂ : ℝ := 8 + 2 * (params43.crho / params43.w) ^ 2
  have hB₂0 : 0 ≤ B₂ := by positivity
  refine ⟨16 / 3 * C * B₂ * C₁', by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop TL, eventually_ge_atTop 1, eventually_l_bounds]
    with T hTL' hT1 ⟨hlog1, hl1, hlo, hhi⟩
  have hF := hTL T hTL'
  set l := Zeta23.l T
  set L := params43.L T
  set X := params43.X T
  have hLl : L = 4 / 3 * l := rfl
  have hXL : X = Real.exp L := rfl
  have hT0 : 0 < T := by linarith
  have hX2 : 2 ≤ X := by
    rw [hXL]
    have h1 : l + 1 ≤ Real.exp l := Real.add_one_le_exp l
    have h2 : Real.exp l ≤ Real.exp L := Real.exp_le_exp.mpr (by rw [hLl]; linarith)
    linarith
  have hlogX : Real.log X ≤ 4 / 3 * Real.log T := by
    rw [hXL, Real.log_exp, hLl]
    linarith
  have hlogX0 : 0 ≤ Real.log X := by
    rw [hXL, Real.log_exp, hLl]
    linarith
  have hXT : X ≤ T ^ (4 / 3 : ℝ) := exp_lam_l_le (lam := 4 / 3) (by norm_num) hT0 hhi
  have hcheb : ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 ≤ C₁' * (T ^ (4 / 3 : ℝ) * (4 / 3 * Real.log T)) := by
    have hc0 : 0 ≤ ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hc1 : ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 ≤ C₁ * X * Real.log X := hC₁ X hX2
    have hc2 : C₁ * X * Real.log X ≤ C₁' * (X * Real.log X) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    have hc3 : X * Real.log X ≤ T ^ (4 / 3 : ℝ) * (4 / 3 * Real.log T) :=
      mul_le_mul hXT hlogX hlogX0 (Real.rpow_nonneg hT0.le _)
    exact (hc1.trans hc2).trans (mul_le_mul_of_nonneg_left hc3 hC₁'0)
  have hmom : ∫ x, params43.PhiR T x ^ 2 * x ^ 2 ≤ B₂ := hF.integral_Phi_sq_mul_sq_le
  have hmain := abs_ppOffDiagCos_sub_fourier_le hMV hC0.le hF hT0
  have hTpow : T ^ (2 : ℝ) = T ^ (4 / 3 : ℝ) * T ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_add hT0]; norm_num
  have hTsq : (T : ℝ) ^ 2 = T ^ (4 / 3 : ℝ) * T ^ (2 / 3 : ℝ) := by
    rw [← hTpow, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hT43 : 0 < T ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have hT23 : 0 < T ^ (2 / 3 : ℝ) := Real.rpow_pos_of_pos hT0 _
  calc |ppOffDiagCos (params43.PhiR T) T X - ppOffDiagFourier (params43.g T) T X|
      ≤ 4 * C * ((∫ x, params43.PhiR T x ^ 2 * x ^ 2) / T ^ 2)
          * ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := hmain
    _ ≤ 4 * C * (B₂ / T ^ 2) * (C₁' * (T ^ (4 / 3 : ℝ) * (4 / 3 * Real.log T))) := by
        have h1 : (∫ x, params43.PhiR T x ^ 2 * x ^ 2) / T ^ 2 ≤ B₂ / T ^ 2 :=
          div_le_div_of_nonneg_right hmom (by positivity)
        have h2 : 0 ≤ ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        have h3 : 0 ≤ 4 * C * ((∫ x, params43.PhiR T x ^ 2 * x ^ 2) / T ^ 2) :=
          mul_nonneg (by positivity) (div_nonneg (integral_nonneg fun _ => by positivity) (by positivity))
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity)) hcheb h2 (by positivity)
    _ = 16 / 3 * C * B₂ * C₁' * (Real.log T / T ^ (2 / 3 : ℝ)) := by
        rw [hTsq]
        field_simp
        ring

end RHTower

