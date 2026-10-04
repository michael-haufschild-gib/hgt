import GaloisForLFunctions.RHTower.LiClockThetaTailInverse

/-!
# Tail counter-inputs: ratio increments and finite literal jets do not orient the inverse

**Ramp inputs.**  For `A, D > 0`, `L ≥ 0` and `n ≥ 1` the input
`f_L = (A - D)K + (D/2)(K + tK') + L K_{n+1}` has odd coefficients `(A + Dm + L·[m ≥ n]) c_{m+1} > 0`,
so its ratios to `K` are at least `A`, increase by at least `D`, and `f_L/K` is strictly increasing
on positive clocks; `f_L'(0) = A K'(0)`.  Its causal inverse `(A - D)r + (D/2)F + L q_{n+1}` lies in
the strict sub-`1/300` class, and at a negative clock of `q_{n+1}` a large `L` makes it negative.
With `A = α₁ = g'(0)/K'(0)` the slope is the literal one.

**Literal jets.**  The input `g + L K_{n+1}` has the same first `n` odd coefficients as `g`, ratios
`α_{m+1} + L·[m ≥ n]` (all increments `> 6047/22725`), and inverse `-S + L q_{n+1}` whose jets of
order `< 2n+1` at the origin are those of `-S`; it too becomes negative for large `L`.  For
`L > 49/909` every ratio `m ≥ n` leaves the actual band `α_j < 2jω² + ν₁`.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ContDiff

noncomputable section

namespace RHTower

private theorem hκ' : GeometricCoeffBound (fun m => liClockThetaGeneratorCoeff (m + 1))
    (1 * (32 / 303)) (32 / 303) := geometricCoeffBound_liClockThetaGeneratorCoeff.shift

private theorem indicator_abs_le (n m : ℕ) : |(if n ≤ m then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

private theorem indicator_mono {n i j : ℕ} (hij : i ≤ j) :
    (if n ≤ i then (1 : ℝ) else 0) ≤ (if n ≤ j then 1 else 0) := by
  by_cases h1 : n ≤ i
  · rw [if_pos h1, if_pos (h1.trans hij)]
  · rw [if_neg h1]; split_ifs <;> norm_num

private theorem tailCoeff_eq (n m : ℕ) : liClockThetaKernelTailCoeff n m =
    (if n ≤ m then 1 else 0) * liClockThetaGeneratorCoeff (m + 1) := by
  unfold liClockThetaKernelTailCoeff; split_ifs <;> ring

private theorem kernelClock_le_one (m : ℕ) :
    (2 * (m : ℝ) + 2) * liClockThetaGeneratorCoeff (m + 1) ≤
      2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) := by
  have := abs_kernelClockCoeff_le_pow (ρ := 1 / 2) (by norm_num) m
  rw [show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_pow, mul_one,
    abs_of_nonneg (by have := liClockThetaGeneratorCoeff_pos (m + 1); positivity)] at this
  exact this

private theorem generatorCoeff_le_one (m : ℕ) : liClockThetaGeneratorCoeff (m + 1) ≤ 1 := by
  refine (liClockThetaGeneratorCoeff_le _).trans ?_
  rw [div_le_one (by exact_mod_cast Nat.factorial_pos _)]
  exact (pow_le_one₀ (by norm_num) (by norm_num)).trans
    (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _))

/-! ## Ramp inputs -/

/-- The ramp input `(A - D)K + (D/2)(K + tK') + L K_{n+1}`. -/
def liClockThetaRampInput (A D L : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (A - D) * liClockThetaKernel t + D / 2 * liClockThetaClockInput t +
    L * liClockThetaKernelTail n t

/-- The ramp response `(A - D)r + (D/2)F + L q_{n+1}`. -/
def liClockThetaRampResponse (A D L : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (A - D) * liClockThetaResolvent t + D / 2 * liEvenCrossActualClockResponse t +
    L * liClockThetaTailInverse n t

/-- The ramp coefficients `(A + Dm + L·[m ≥ n]) c_{m+1}`. -/
def liClockThetaRampCoeff (A D L : ℝ) (n m : ℕ) : ℝ :=
  (A + D * m + L * (if n ≤ m then 1 else 0)) * liClockThetaGeneratorCoeff (m + 1)

private theorem continuous_conv_left {f k : ℝ → ℝ} (c : ℝ) (t : ℝ) :
    volterraConv (fun s => c * f s) k t = c * volterraConv f k t := volterraConv_smul_left c f k t

theorem liClockThetaRampResponse_volterra (A D L : ℝ) (n : ℕ) (t : ℝ) :
    liClockThetaRampResponse A D L n t +
        volterraConv (liClockThetaRampResponse A D L n) liClockThetaKernel t =
      liClockThetaRampInput A D L n t := by
  have hr := continuous_liClockThetaResolvent
  have hF : Continuous liEvenCrossActualClockResponse := continuous_liEvenCrossActualClockResponse
  have hq := (contDiff_liClockThetaTailInverse n).continuous
  have hK := continuous_liClockThetaKernel
  have hlin : volterraConv (liClockThetaRampResponse A D L n) liClockThetaKernel t =
      (A - D) * volterraConv liClockThetaResolvent liClockThetaKernel t +
        D / 2 * volterraConv liEvenCrossActualClockResponse liClockThetaKernel t +
          L * volterraConv (liClockThetaTailInverse n) liClockThetaKernel t := by
    unfold liClockThetaRampResponse
    rw [volterraConv_comm, show (fun s => (A - D) * liClockThetaResolvent s +
      D / 2 * liEvenCrossActualClockResponse s + L * liClockThetaTailInverse n s) =
        ((fun s => (A - D) * liClockThetaResolvent s) +
          fun s => D / 2 * liEvenCrossActualClockResponse s) +
            fun s => L * liClockThetaTailInverse n s from rfl,
      volterraConv_add_right hK ((hr.const_mul _).add (hF.const_mul _)) (hq.const_mul _),
      volterraConv_add_right hK (hr.const_mul _) (hF.const_mul _),
      volterraConv_smul_right, volterraConv_smul_right, volterraConv_smul_right,
      volterraConv_comm liClockThetaKernel, volterraConv_comm liClockThetaKernel,
      volterraConv_comm liClockThetaKernel]
  rw [hlin]
  unfold liClockThetaRampResponse liClockThetaRampInput
  have h1 := liClockThetaResolvent_volterra t
  have h2 := liEvenCrossActualClockResponse_volterra_kernel t
  have h3 := liClockThetaTailInverse_volterra n t
  linear_combination (A - D) * h1 + D / 2 * h2 + L * h3

private theorem hramp (A D L : ℝ) (n : ℕ) : GeometricCoeffBound (liClockThetaRampCoeff A D L n)
    ((|A| + |D| + |L|) * (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) + 1)) 1 := by
  intro m
  have hc := (liClockThetaGeneratorCoeff_pos (m + 1)).le
  have hc1 := generatorCoeff_le_one m
  have hk := kernelClock_le_one m
  have hE : 0 ≤ 2 * (1 / 2 : ℝ) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) := by positivity
  rw [one_pow, mul_one]
  unfold liClockThetaRampCoeff
  rw [abs_mul, abs_of_nonneg hc]
  have hm : (m : ℝ) * liClockThetaGeneratorCoeff (m + 1) ≤
      2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) := by nlinarith
  have hi := indicator_abs_le n m
  calc |A + D * m + L * (if n ≤ m then 1 else 0)| * liClockThetaGeneratorCoeff (m + 1) ≤
      (|A| + |D| * m + |L|) * liClockThetaGeneratorCoeff (m + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ hc
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add le_rfl ?_)) ?_)
        · rw [abs_mul, Nat.abs_cast]
        · rw [abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) hi
    _ = |A| * liClockThetaGeneratorCoeff (m + 1) + |D| * (m * liClockThetaGeneratorCoeff (m + 1)) +
        |L| * liClockThetaGeneratorCoeff (m + 1) := by ring
    _ ≤ |A| * (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) + 1) +
        |D| * (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) + 1) +
        |L| * (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2)) + 1) := by
        gcongr <;> linarith
    _ = _ := by ring

theorem liClockThetaRampInput_eq_oddFactorialSeries (A D L : ℝ) (n : ℕ) :
    liClockThetaRampInput A D L n = oddFactorialSeries (liClockThetaRampCoeff A D L n) := by
  funext t
  have hb : GeometricCoeffBound (fun m => (2 * (m : ℝ) + 2) * liClockThetaGeneratorCoeff (m + 1))
      (2 * (1 / 2) ^ 2 * Real.exp (32 / (303 * (1 / 2) ^ 2))) 1 := fun m => by
    rw [one_pow, mul_one, abs_of_nonneg (by have := liClockThetaGeneratorCoeff_pos (m + 1); positivity)]
    exact kernelClock_le_one m
  have h1 := (summable_oddFactorialSeries_term (by norm_num) hκ' t).hasSum
  have h2 := (summable_oddFactorialSeries_term (by norm_num) hb t).hasSum
  have hτ : GeometricCoeffBound (liClockThetaKernelTailCoeff n) (1 * (32 / 303)) (32 / 303) :=
    fun m => by
      rw [tailCoeff_eq, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (indicator_abs_le n m)).trans (hκ' m)
  have h3 := (summable_oddFactorialSeries_term (by norm_num) hτ t).hasSum
  unfold liClockThetaRampInput
  rw [liClockThetaClockInput_eq_oddFactorialSeries]
  unfold liClockThetaKernel liClockThetaKernelTail oddFactorialSeries
  rw [← (((h1.mul_left (A - D)).add (h2.mul_left (D / 2))).add (h3.mul_left L)).tsum_eq]
  refine tsum_congr fun m => ?_
  unfold liClockThetaRampCoeff
  rw [tailCoeff_eq]
  ring

theorem liClockThetaRampCoeff_div (A D L : ℝ) (n m : ℕ) :
    liClockThetaRampCoeff A D L n m / liClockThetaGeneratorCoeff (m + 1) =
      A + D * m + L * (if n ≤ m then 1 else 0) :=
  mul_div_cancel_right₀ _ (liClockThetaGeneratorCoeff_pos _).ne'

/-- Ramp ratios increase by at least `D`. -/
theorem liClockThetaRampRatio_increment {A D L : ℝ} (hL : 0 ≤ L) (n m : ℕ) :
    D ≤ (A + D * (m + 1 : ℕ) + L * (if n ≤ m + 1 then 1 else 0)) -
      (A + D * m + L * (if n ≤ m then 1 else 0)) := by
  push_cast
  have : L * (if n ≤ m then (1 : ℝ) else 0) ≤ L * (if n ≤ m + 1 then 1 else 0) := by
    apply mul_le_mul_of_nonneg_left _ hL
    exact indicator_mono (by omega)
  linarith

theorem liClockThetaRampRatio_ge {A D L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L) (n m : ℕ) :
    A ≤ A + D * m + L * (if n ≤ m then 1 else 0) := by
  have h1 : 0 ≤ D * (m : ℝ) := mul_nonneg hD (Nat.cast_nonneg m)
  have h2 : 0 ≤ L * (if n ≤ m then (1 : ℝ) else 0) := mul_nonneg hL (by split_ifs <;> norm_num)
  linarith

theorem liClockThetaRampCoeff_pos {A D L : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (hL : 0 ≤ L) (n m : ℕ) :
    0 < liClockThetaRampCoeff A D L n m :=
  mul_pos (lt_of_lt_of_le hA (liClockThetaRampRatio_ge hD hL n m)) (liClockThetaGeneratorCoeff_pos _)

/-- **Strictly increasing pointwise ratio of the ramp input.** -/
theorem liClockThetaRampInput_div_kernel_strictMonoOn {A D L : ℝ} (hD : 0 < D) (hL : 0 ≤ L)
    (n : ℕ) : StrictMonoOn (fun t => liClockThetaRampInput A D L n t / liClockThetaKernel t)
      (Ioi 0) := by
  intro s hs t _ hst
  have hs' : (0 : ℝ) < s := hs
  have hmono : ∀ i j : ℕ, i ≤ j → liClockThetaRampCoeff A D L n i * liClockThetaGeneratorCoeff (j + 1) ≤
      liClockThetaRampCoeff A D L n j * liClockThetaGeneratorCoeff (i + 1) := by
    intro i j hij
    unfold liClockThetaRampCoeff
    have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
    have hind : (if n ≤ i then (1 : ℝ) else 0) ≤ (if n ≤ j then 1 else 0) := by
      exact indicator_mono (by omega)
    have key : A + D * i + L * (if n ≤ i then 1 else 0) ≤ A + D * j + L * (if n ≤ j then 1 else 0) := by
      have := mul_le_mul_of_nonneg_left hind hL
      nlinarith
    have hc := mul_pos (liClockThetaGeneratorCoeff_pos (i + 1)) (liClockThetaGeneratorCoeff_pos (j + 1))
    calc (A + D * i + L * (if n ≤ i then 1 else 0)) * liClockThetaGeneratorCoeff (i + 1) *
          liClockThetaGeneratorCoeff (j + 1) = (A + D * i + L * (if n ≤ i then 1 else 0)) *
            (liClockThetaGeneratorCoeff (i + 1) * liClockThetaGeneratorCoeff (j + 1)) := by ring
      _ ≤ (A + D * j + L * (if n ≤ j then 1 else 0)) *
            (liClockThetaGeneratorCoeff (i + 1) * liClockThetaGeneratorCoeff (j + 1)) :=
          mul_le_mul_of_nonneg_right key hc.le
      _ = _ := by ring
  have hstr : liClockThetaRampCoeff A D L n 0 * liClockThetaGeneratorCoeff (1 + 1) <
      liClockThetaRampCoeff A D L n 1 * liClockThetaGeneratorCoeff (0 + 1) := by
    unfold liClockThetaRampCoeff
    have hind : (if n ≤ 0 then (1 : ℝ) else 0) ≤ (if n ≤ 1 then 1 else 0) := by
      exact indicator_mono (by omega)
    have key : A + D * ((0 : ℕ) : ℝ) + L * (if n ≤ 0 then 1 else 0) <
        A + D * ((1 : ℕ) : ℝ) + L * (if n ≤ 1 then 1 else 0) := by
      have := mul_le_mul_of_nonneg_left hind hL
      push_cast; linarith
    have hc := mul_pos (liClockThetaGeneratorCoeff_pos (0 + 1)) (liClockThetaGeneratorCoeff_pos (1 + 1))
    nlinarith
  have h := oddFactorialSeries_ratio_strictMono (by norm_num) (by norm_num) (hramp A D L n) hκ'
    (fun j => liClockThetaGeneratorCoeff_pos _) hmono (by norm_num : 0 < 1) hstr hs' hst
  have hKs := liClockThetaKernel_pos hs'
  have hKt := liClockThetaKernel_pos (hs'.trans hst)
  simp only [liClockThetaRampInput_eq_oddFactorialSeries]
  rw [div_lt_div_iff₀ hKs hKt]
  exact h

/-- The ramp input dominates `A K` on nonnegative clocks. -/
theorem liClockThetaRampInput_ge {A D L : ℝ} (hA : 0 < A) (hD : 0 ≤ D) (hL : 0 ≤ L) (n : ℕ)
    {t : ℝ} (ht : 0 ≤ t) : A * liClockThetaKernel t ≤ liClockThetaRampInput A D L n t := by
  have hcb : GeometricCoeffBound (fun m => A * liClockThetaGeneratorCoeff (m + 1))
      (A * (1 * (32 / 303))) (32 / 303) := fun m => by
    rw [abs_mul, abs_of_pos hA, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hκ' m) hA.le
  have h := oddFactorialSeries_le_of_le (by norm_num) (by norm_num) hcb (hramp A D L n) (fun m => by
    unfold liClockThetaRampCoeff
    exact mul_le_mul_of_nonneg_right (liClockThetaRampRatio_ge hD hL n m)
      (liClockThetaGeneratorCoeff_pos _).le) ht
  have e : oddFactorialSeries (fun m => A * liClockThetaGeneratorCoeff (m + 1)) t =
      A * liClockThetaKernel t := by
    unfold liClockThetaKernel oddFactorialSeries
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by ring
  rw [e, ← liClockThetaRampInput_eq_oddFactorialSeries] at h
  exact h

theorem hasDerivAt_liClockThetaRampInput_zero (A D L : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (liClockThetaRampInput A D L n) (A * liClockThetaGeneratorCoeff 1) 0 := by
  rw [liClockThetaRampInput_eq_oddFactorialSeries]
  have h := hasDerivAt_oddFactorialSeries (by norm_num) (hramp A D L n) 0
  rw [evenFactorialSeries_zero] at h
  convert h using 1
  unfold liClockThetaRampCoeff
  rw [if_neg (by omega)]
  push_cast; ring

theorem contDiff_liClockThetaRampInput (A D L : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (liClockThetaRampInput A D L n) := by
  rw [liClockThetaRampInput_eq_oddFactorialSeries]
  exact contDiff_oddFactorialSeries (by norm_num) (hramp A D L n)

theorem liClockEveryExpType_liClockThetaRampInput (A D L : ℝ) (n : ℕ) :
    LiClockEveryExpType (liClockThetaRampInput A D L n) := by
  have hK := LiClockEveryExpType.const_mul (A - D) contDiff_liClockThetaKernel
    liClockEveryExpType_liClockThetaKernel
  have hh := LiClockEveryExpType.const_mul (D / 2) contDiff_liClockThetaClockInput
    liClockEveryExpType_liClockThetaClockInput
  have hT := LiClockEveryExpType.const_mul L (contDiff_liClockThetaKernelTail n)
    (liClockEveryExpType_liClockThetaKernelTail n)
  have h1 := LiClockEveryExpType.add (contDiff_const.mul contDiff_liClockThetaKernel)
    (contDiff_const.mul contDiff_liClockThetaClockInput) hK hh
  exact LiClockEveryExpType.add ((contDiff_const.mul contDiff_liClockThetaKernel).add
    (contDiff_const.mul contDiff_liClockThetaClockInput))
    (contDiff_const.mul (contDiff_liClockThetaKernelTail n)) h1 hT

theorem liClockSubGammaClass_liClockThetaRampResponse (A D L : ℝ) (n : ℕ) :
    LiClockSubGammaClass (liClockThetaRampResponse A D L n) := by
  have hcont : Continuous (liClockThetaRampResponse A D L n) := by
    unfold liClockThetaRampResponse
    exact ((continuous_liClockThetaResolvent.const_mul _).add
      (continuous_liEvenCrossActualClockResponse.const_mul _)).add
        ((contDiff_liClockThetaTailInverse n).continuous.const_mul _)
  rw [eq_liClockThetaInverse (y := liClockThetaRampResponse A D L n)
    (contDiff_liClockThetaRampInput A D L n).continuous hcont (liClockThetaRampResponse_volterra A D L n)]
  exact liClockSubGammaClass_liClockThetaInverse (contDiff_liClockThetaRampInput A D L n)
    (liClockEveryExpType_liClockThetaRampInput A D L n)

/-- **Ramp counter-input.**  For every `D > 0` and `n ≥ 1` there are a positive clock `T` and
`L ≥ 0` such that the ramp input with `A = α₁` has the literal slope `g'(0)`, ratios `≥ α₁` with
increments `≥ D`, strictly increasing pointwise ratio to `K`, and its sub-`1/300` inverse is
negative at `T`. -/
theorem exists_liClockThetaRampCounterInput {D : ℝ} (hD : 0 < D) {n : ℕ} (hn : 1 ≤ n) :
    ∃ T : ℝ, 0 < T ∧ ∃ L : ℝ, 0 ≤ L ∧
      liClockThetaRampResponse (liClockThetaForcingRatio 1) D L n T < 0 ∧
      HasDerivAt (liClockThetaRampInput (liClockThetaForcingRatio 1) D L n)
        (liClockThetaForcingInputDeriv 0) 0 ∧
      StrictMonoOn (fun t => liClockThetaRampInput (liClockThetaForcingRatio 1) D L n t /
        liClockThetaKernel t) (Ioi 0) ∧
      (∀ t, 0 ≤ t → liClockThetaForcingRatio 1 * liClockThetaKernel t ≤
        liClockThetaRampInput (liClockThetaForcingRatio 1) D L n t) ∧
      LiClockSubGammaClass (liClockThetaRampResponse (liClockThetaForcingRatio 1) D L n) := by
  obtain ⟨T, hT, hqT⟩ := exists_liClockThetaTailInverse_neg n
  set A := liClockThetaForcingRatio 1
  have hA : 0 < A := liClockThetaForcingRatio_pos le_rfl
  set z := (A - D) * liClockThetaResolvent T + D / 2 * liEvenCrossActualClockResponse T
  set L := (|z| + 1) / (-liClockThetaTailInverse n T) with hLdef
  have hL : 0 ≤ L := div_nonneg (by positivity) (by linarith)
  refine ⟨T, hT, L, hL, ?_, ?_, liClockThetaRampInput_div_kernel_strictMonoOn hD hL n,
    fun t ht => liClockThetaRampInput_ge hA hD.le hL n ht,
    liClockSubGammaClass_liClockThetaRampResponse A D L n⟩
  · change z + L * liClockThetaTailInverse n T < 0
    have hq0 : liClockThetaTailInverse n T ≠ 0 := hqT.ne
    have hLq : L * liClockThetaTailInverse n T = -(|z| + 1) := by
      rw [hLdef]; field_simp
    have hz := le_abs_self z
    linarith
  · have h := hasDerivAt_liClockThetaRampInput_zero A D L hn
    convert h using 1
    unfold liClockThetaForcingInputDeriv
    rw [evenFactorialSeries_zero, zero_add, neg_liClockThetaForcingTaylorCoeff_eq]

/-! ## Literal-jet inputs -/

/-- The jet input `g + L K_{n+1}`. -/
def liClockThetaJetInput (L : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  liClockThetaForcingInput t + L * liClockThetaKernelTail n t

/-- The jet response `-S + L q_{n+1}`. -/
def liClockThetaJetResponse (L : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  -liEvenCrossActualClockMassiveSource t + L * liClockThetaTailInverse n t

theorem liClockThetaJetResponse_volterra (L : ℝ) (n : ℕ) (t : ℝ) :
    liClockThetaJetResponse L n t +
        volterraConv (liClockThetaJetResponse L n) liClockThetaKernel t =
      liClockThetaJetInput L n t := by
  have hS := continuous_liEvenCrossActualClockMassiveSource
  have hq := (contDiff_liClockThetaTailInverse n).continuous
  have hK := continuous_liClockThetaKernel
  have hlin : volterraConv (liClockThetaJetResponse L n) liClockThetaKernel t =
      volterraConv (fun s => -liEvenCrossActualClockMassiveSource s) liClockThetaKernel t +
        L * volterraConv (liClockThetaTailInverse n) liClockThetaKernel t := by
    unfold liClockThetaJetResponse
    rw [volterraConv_comm, show (fun s => -liEvenCrossActualClockMassiveSource s +
      L * liClockThetaTailInverse n s) = (fun s => -liEvenCrossActualClockMassiveSource s) +
        fun s => L * liClockThetaTailInverse n s from rfl,
      volterraConv_add_right hK (show Continuous fun s => -liEvenCrossActualClockMassiveSource s
        from hS.neg) (hq.const_mul _), volterraConv_smul_right,
      volterraConv_comm liClockThetaKernel, volterraConv_comm liClockThetaKernel]
  rw [hlin]
  unfold liClockThetaJetResponse liClockThetaJetInput
  have h1 := neg_liEvenCrossActualClockMassiveSource_volterra t
  rw [volterraConv_comm] at h1
  have h3 := liClockThetaTailInverse_volterra n t
  linear_combination h1 + L * h3

/-- The jet input coefficients `-e_{m+1} + L·[m ≥ n] c_{m+1} = (α_{m+1} + L·[m ≥ n]) c_{m+1}`. -/
def liClockThetaJetCoeff (L : ℝ) (n m : ℕ) : ℝ :=
  (liClockThetaForcingRatio (m + 1) + L * (if n ≤ m then 1 else 0)) *
    liClockThetaGeneratorCoeff (m + 1)

private theorem hjet (L : ℝ) (n : ℕ) : GeometricCoeffBound (liClockThetaJetCoeff L n)
    ((2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1 +
      |L| * (1 * (32 / 303))) 1 := by
  intro m
  have hγ := geometricCoeffBound_liClockThetaForcingTaylorCoeff.shift m
  have hc := hκ' m
  rw [one_pow, mul_one] at hγ ⊢
  unfold liClockThetaJetCoeff
  rw [add_mul, ← neg_liClockThetaForcingTaylorCoeff_eq]
  refine (abs_add_le _ _).trans (add_le_add (by rw [abs_neg]; exact hγ) ?_)
  rw [abs_mul, abs_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg L)
  calc |(if n ≤ m then (1 : ℝ) else 0)| * |liClockThetaGeneratorCoeff (m + 1)| ≤
      1 * (1 * (32 / 303) * (32 / 303) ^ m) := mul_le_mul (indicator_abs_le n m) hc
        (abs_nonneg _) (by norm_num)
    _ ≤ 1 * (32 / 303) := by
        rw [one_mul]
        exact mul_le_of_le_one_right (by norm_num) (pow_le_one₀ (by norm_num) (by norm_num))

theorem liClockThetaJetInput_eq_oddFactorialSeries (L : ℝ) (n : ℕ) :
    liClockThetaJetInput L n = oddFactorialSeries (liClockThetaJetCoeff L n) := by
  funext t
  have hγ : GeometricCoeffBound (fun m => -liClockThetaForcingTaylorCoeff (m + 1))
      ((2 + 2 * liEvenCrossActualClockGreenRate ^ 2 + normalizedPrimeArchMoment 0) * 1) 1 :=
    fun m => by rw [abs_neg]; exact geometricCoeffBound_liClockThetaForcingTaylorCoeff.shift m
  have hτ : GeometricCoeffBound (liClockThetaKernelTailCoeff n) (1 * (32 / 303)) (32 / 303) :=
    fun m => by
      rw [tailCoeff_eq, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (indicator_abs_le n m)).trans (hκ' m)
  have h1 := (summable_oddFactorialSeries_term (by norm_num) hγ t).hasSum
  have h3 := (summable_oddFactorialSeries_term (by norm_num) hτ t).hasSum
  unfold liClockThetaJetInput liClockThetaForcingInput liClockThetaKernelTail oddFactorialSeries
  rw [← (h1.add (h3.mul_left L)).tsum_eq]
  refine tsum_congr fun m => ?_
  unfold liClockThetaJetCoeff
  rw [tailCoeff_eq, neg_liClockThetaForcingTaylorCoeff_eq]
  ring

/-- The first `n` odd coefficients of the jet input are those of the literal `g`. -/
theorem liClockThetaJetCoeff_of_lt {L : ℝ} {n m : ℕ} (hm : m < n) :
    liClockThetaJetCoeff L n m = -liClockThetaForcingTaylorCoeff (m + 1) := by
  unfold liClockThetaJetCoeff
  rw [if_neg (by omega), mul_zero, add_zero, neg_liClockThetaForcingTaylorCoeff_eq]

theorem liClockThetaJetCoeff_div (L : ℝ) (n m : ℕ) :
    liClockThetaJetCoeff L n m / liClockThetaGeneratorCoeff (m + 1) =
      liClockThetaForcingRatio (m + 1) + L * (if n ≤ m then 1 else 0) :=
  mul_div_cancel_right₀ _ (liClockThetaGeneratorCoeff_pos _).ne'

/-- Jet-input ratio increments exceed `6047/22725`. -/
theorem liClockThetaJetRatio_increment {L : ℝ} (hL : 0 ≤ L) (n m : ℕ) :
    6047 / 22725 < (liClockThetaForcingRatio (m + 1 + 1) + L * (if n ≤ m + 1 then 1 else 0)) -
      (liClockThetaForcingRatio (m + 1) + L * (if n ≤ m then 1 else 0)) := by
  have h := liClockThetaForcingRatio_increment_gt (j := m + 1) (by omega)
  have : L * (if n ≤ m then (1 : ℝ) else 0) ≤ L * (if n ≤ m + 1 then 1 else 0) := by
    apply mul_le_mul_of_nonneg_left _ hL
    exact indicator_mono (by omega)
  linarith

theorem liClockThetaJetCoeff_pos {L : ℝ} (hL : 0 ≤ L) (n m : ℕ) : 0 < liClockThetaJetCoeff L n m := by
  unfold liClockThetaJetCoeff
  have h1 := liClockThetaForcingRatio_pos (j := m + 1) (by omega)
  have h2 : 0 ≤ L * (if n ≤ m then (1 : ℝ) else 0) := mul_nonneg hL (by split_ifs <;> norm_num)
  exact mul_pos (by linarith) (liClockThetaGeneratorCoeff_pos _)

/-- **Strictly increasing pointwise ratio of the jet input.** -/
theorem liClockThetaJetInput_div_kernel_strictMonoOn {L : ℝ} (hL : 0 ≤ L) (n : ℕ) :
    StrictMonoOn (fun t => liClockThetaJetInput L n t / liClockThetaKernel t) (Ioi 0) := by
  intro s hs t _ hst
  have hs' : (0 : ℝ) < s := hs
  have hratio : ∀ i j : ℕ, i ≤ j → liClockThetaForcingRatio (i + 1) + L * (if n ≤ i then 1 else 0) ≤
      liClockThetaForcingRatio (j + 1) + L * (if n ≤ j then 1 else 0) := by
    intro i j hij
    have h1 := liClockThetaForcingRatio_strictMono.monotone (by omega : i + 1 ≤ j + 1)
    have hind : (if n ≤ i then (1 : ℝ) else 0) ≤ (if n ≤ j then 1 else 0) := by
      exact indicator_mono (by omega)
    have := mul_le_mul_of_nonneg_left hind hL
    linarith
  have hmono : ∀ i j : ℕ, i ≤ j → liClockThetaJetCoeff L n i * liClockThetaGeneratorCoeff (j + 1) ≤
      liClockThetaJetCoeff L n j * liClockThetaGeneratorCoeff (i + 1) := by
    intro i j hij
    unfold liClockThetaJetCoeff
    have hc := mul_pos (liClockThetaGeneratorCoeff_pos (i + 1)) (liClockThetaGeneratorCoeff_pos (j + 1))
    calc (liClockThetaForcingRatio (i + 1) + L * (if n ≤ i then 1 else 0)) *
          liClockThetaGeneratorCoeff (i + 1) * liClockThetaGeneratorCoeff (j + 1) =
        (liClockThetaForcingRatio (i + 1) + L * (if n ≤ i then 1 else 0)) *
          (liClockThetaGeneratorCoeff (i + 1) * liClockThetaGeneratorCoeff (j + 1)) := by ring
      _ ≤ (liClockThetaForcingRatio (j + 1) + L * (if n ≤ j then 1 else 0)) *
          (liClockThetaGeneratorCoeff (i + 1) * liClockThetaGeneratorCoeff (j + 1)) :=
        mul_le_mul_of_nonneg_right (hratio i j hij) hc.le
      _ = _ := by ring
  have hstr : liClockThetaJetCoeff L n 0 * liClockThetaGeneratorCoeff (1 + 1) <
      liClockThetaJetCoeff L n 1 * liClockThetaGeneratorCoeff (0 + 1) := by
    unfold liClockThetaJetCoeff
    have h := liClockThetaJetRatio_increment hL n 0
    have hc := mul_pos (liClockThetaGeneratorCoeff_pos (0 + 1)) (liClockThetaGeneratorCoeff_pos (1 + 1))
    simp only [zero_add] at h hc ⊢
    nlinarith
  have h := oddFactorialSeries_ratio_strictMono (by norm_num) (by norm_num) (hjet L n) hκ'
    (fun j => liClockThetaGeneratorCoeff_pos _) hmono (by norm_num : 0 < 1) hstr hs' hst
  have hKs := liClockThetaKernel_pos hs'
  have hKt := liClockThetaKernel_pos (hs'.trans hst)
  simp only [liClockThetaJetInput_eq_oddFactorialSeries]
  rw [div_lt_div_iff₀ hKs hKt]
  exact h

theorem hasDerivAt_liClockThetaJetInput_zero (L : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    HasDerivAt (liClockThetaJetInput L n) (liClockThetaForcingInputDeriv 0) 0 := by
  rw [liClockThetaJetInput_eq_oddFactorialSeries]
  have h := hasDerivAt_oddFactorialSeries (by norm_num) (hjet L n) 0
  rw [evenFactorialSeries_zero, liClockThetaJetCoeff_of_lt (by omega)] at h
  convert h using 1
  unfold liClockThetaForcingInputDeriv
  rw [evenFactorialSeries_zero]

theorem contDiff_liEvenCrossActualClockMassiveSource :
    ContDiff ℝ ∞ liEvenCrossActualClockMassiveSource := by
  rw [liEvenCrossActualClockMassiveSource_eq_oddFactorialSeries]
  exact contDiff_oddFactorialSeries (by norm_num) geometricCoeffBound_liClockMassiveSourceCoeff

/-- **The jet response keeps every jet of `-S` of order `< 2n+1`.** -/
theorem iteratedDeriv_liClockThetaJetResponse_zero (L : ℝ) {n k : ℕ} (hk : k < 2 * n + 1) :
    iteratedDeriv k (liClockThetaJetResponse L n) 0 =
      iteratedDeriv k (fun t => -liEvenCrossActualClockMassiveSource t) 0 := by
  have hS : ContDiff ℝ ∞ fun t => -liEvenCrossActualClockMassiveSource t :=
    contDiff_liEvenCrossActualClockMassiveSource.neg
  have hq := contDiff_liClockThetaTailInverse n
  have e : liClockThetaJetResponse L n =
      (fun t => -liEvenCrossActualClockMassiveSource t) + fun t => L * liClockThetaTailInverse n t :=
    rfl
  rw [e, iteratedDeriv_add (hS.contDiffAt.of_le (natCast_lt_infty k).le)
    ((contDiff_const.mul hq).contDiffAt.of_le (natCast_lt_infty k).le),
    iteratedDeriv_const_mul L (hq.contDiffAt.of_le (natCast_lt_infty k).le),
    iteratedDeriv_liClockThetaTailInverse_zero hk, mul_zero, add_zero]

theorem contDiff_liClockThetaJetInput (L : ℝ) (n : ℕ) : ContDiff ℝ ∞ (liClockThetaJetInput L n) := by
  rw [liClockThetaJetInput_eq_oddFactorialSeries]
  exact contDiff_oddFactorialSeries (by norm_num) (hjet L n)

theorem liClockSubGammaClass_liClockThetaJetResponse (L : ℝ) (n : ℕ) :
    LiClockSubGammaClass (liClockThetaJetResponse L n) := by
  have hexp : LiClockEveryExpType (liClockThetaJetInput L n) :=
    LiClockEveryExpType.add contDiff_liClockThetaForcingInput
      (contDiff_const.mul (contDiff_liClockThetaKernelTail n))
      liClockEveryExpType_liClockThetaForcingInput
      (LiClockEveryExpType.const_mul L (contDiff_liClockThetaKernelTail n)
        (liClockEveryExpType_liClockThetaKernelTail n))
  have hcont : Continuous (liClockThetaJetResponse L n) := by
    unfold liClockThetaJetResponse
    exact continuous_liEvenCrossActualClockMassiveSource.neg.add
      ((contDiff_liClockThetaTailInverse n).continuous.const_mul _)
  rw [eq_liClockThetaInverse (y := liClockThetaJetResponse L n)
    (contDiff_liClockThetaJetInput L n).continuous hcont (liClockThetaJetResponse_volterra L n)]
  exact liClockSubGammaClass_liClockThetaInverse (contDiff_liClockThetaJetInput L n) hexp

/-- **Literal-jet counter-input.**  For every `n ≥ 1` some `L ≥ 0` makes the inverse of
`g + L K_{n+1}` negative at a positive clock, while the input keeps the first `n` odd coefficients
and the slope of `g`, all increments `> 6047/22725`, positive coefficients, strictly increasing
pointwise ratio to `K`, and the response keeps every jet of `-S` of order `< 2n+1`. -/
theorem exists_liClockThetaJetCounterInput {n : ℕ} (hn : 1 ≤ n) :
    ∃ T : ℝ, 0 < T ∧ ∃ L : ℝ, 0 ≤ L ∧ liClockThetaJetResponse L n T < 0 ∧
      HasDerivAt (liClockThetaJetInput L n) (liClockThetaForcingInputDeriv 0) 0 ∧
      (∀ m, m < n → liClockThetaJetCoeff L n m = -liClockThetaForcingTaylorCoeff (m + 1)) ∧
      (∀ m, 0 < liClockThetaJetCoeff L n m) ∧
      StrictMonoOn (fun t => liClockThetaJetInput L n t / liClockThetaKernel t) (Ioi 0) ∧
      (∀ k, k < 2 * n + 1 → iteratedDeriv k (liClockThetaJetResponse L n) 0 =
        iteratedDeriv k (fun t => -liEvenCrossActualClockMassiveSource t) 0) ∧
      LiClockSubGammaClass (liClockThetaJetResponse L n) := by
  obtain ⟨T, hT, hqT⟩ := exists_liClockThetaTailInverse_neg n
  set z := -liEvenCrossActualClockMassiveSource T
  set L := (|z| + 1) / (-liClockThetaTailInverse n T) with hLdef
  have hL : 0 ≤ L := div_nonneg (by positivity) (by linarith)
  refine ⟨T, hT, L, hL, ?_, hasDerivAt_liClockThetaJetInput_zero L hn,
    fun m hm => liClockThetaJetCoeff_of_lt hm, liClockThetaJetCoeff_pos hL n,
    liClockThetaJetInput_div_kernel_strictMonoOn hL n,
    fun k hk => iteratedDeriv_liClockThetaJetResponse_zero L hk,
    liClockSubGammaClass_liClockThetaJetResponse L n⟩
  change z + L * liClockThetaTailInverse n T < 0
  have hq0 : liClockThetaTailInverse n T ≠ 0 := hqT.ne
  have hLq : L * liClockThetaTailInverse n T = -(|z| + 1) := by rw [hLdef]; field_simp
  have hz := le_abs_self z
  linarith

/-- **The step leaves the actual upper band.**  If `L > 49/909`, every ratio `m ≥ n` of the jet
input exceeds `2(m+1)ω² + ν₁`. -/
theorem liClockThetaJetRatio_gt_band {L : ℝ} (hL : 49 / 909 < L) {n m : ℕ} (hm : n ≤ m) :
    2 * ((m + 1 : ℕ) : ℝ) * liEvenCrossActualClockGreenRate ^ 2 + thetaCuspNormalizedEvenMoment 1 <
      liClockThetaForcingRatio (m + 1) + L * (if n ≤ m then 1 else 0) := by
  rw [if_pos hm, mul_one]
  have h := liClockThetaMomentRatio_le_of_one_le (j := m + 1) (by omega)
  unfold liClockThetaForcingRatio
  rw [normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment]
  linarith

end RHTower
