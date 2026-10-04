import GaloisForLFunctions.RHTower.LiClockThetaForcingHistoryMajorant

/-!
# Complete theta coefficient tails: inverse sign change and counter-inputs

For `n ≥ 0` let `K_{n+1}(t) = Σ_{m ≥ n} c_{m+1} t^{2m+1}/(2m+1)!` be the complete positive tail of
the literal kernel `K`, `P_{n+1} = K - K_{n+1}` its odd polynomial head, and `q_{n+1} = K_{n+1} -
r ⋆ K_{n+1}` its causal inverse (`q_1 = r`).  Then `q_{n+1} + q_{n+1} ⋆ K = K_{n+1}`,
`q_{n+1} = r - P_{n+1} + r ⋆ P_{n+1}`, `q_{n+1}` lies in the strict sub-`1/300` class, and
`q_{n+1}(t) = c_{n+1} t^{2n+1}/(2n+1)! + O(t^{2n+3})`, so it is positive near the origin.

If `q_{n+1} ≥ 0`, then `q_{n+1} ≤ K_{n+1}` and `1 - q̂_{n+1}(p) = Q(p)/(1 + K̂(p))` with the finite
head `Q(p) = 1 + Σ_{m<n} c_{m+1} p^{-2m-2}`, so `0 ≤ 1 - q̂_{n+1}(p) ≤ C p²` on `0 < p ≤ 1`; this
Laplace deficit contradicts positivity near the origin.  Hence every complete tail inverse is
negative at some positive clock.

Adding `L` times a tail to the ramp input `(A - D)K + (D/2)(K + tK')` (coefficient ratios
`A + D m`), or to the literal forcing `g`, gives inputs whose responses are negative at a chosen
clock, while keeping the slope, all prescribed lower jets, positive coefficients, strictly
increasing ratios to `K` and the strict sub-`1/300` growth class.
-/

open Set Filter Topology MeasureTheory GaloisForLFunctions.HTGeometry
open scoped ContDiff

noncomputable section

namespace RHTower

/-! ## A Laplace-deficit obstruction to nonnegativity -/

/-- A continuous function positive on `(0, ε]` and nonnegative on `[0,∞)` cannot have weighted
masses `L(p) = ∫_0^∞ e^{-pt} y` with `1 - C p² ≤ L(p) ≤ 1` for all `0 < p ≤ 1`. -/
theorem false_of_laplace_deficit {y : ℝ → ℝ} (hy : Continuous y) {ε : ℝ} (hε : 0 < ε)
    (hpos : ∀ t ∈ Ioc (0 : ℝ) ε, 0 < y t) (hnn : ∀ t, 0 ≤ t → 0 ≤ y t)
    (hint : ∀ p, 0 < p → IntegrableOn (fun t => Real.exp (-(p * t)) * y t) (Ioi 0)) {C : ℝ}
    (hC : 0 < C) (hdef : ∀ p, 0 < p → p ≤ 1 →
      1 - C * p ^ 2 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * y t ∧
        ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * y t ≤ 1) : False := by
  have hcont : Continuous fun t => t * y t := continuous_id.mul hy
  set J := ∫ t in (0 : ℝ)..ε, t * y t
  have hJ : 0 < J := intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable _ _)
    (fun x hx => mul_pos hx.1 (hpos x ⟨hx.1, hx.2.le⟩)) hε
  set L : ℝ → ℝ := fun p => ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * y t
  have hlower : ∀ q, 0 < q → q / 2 * Real.exp (-(q * ε)) * J ≤ L (q / 2) - L q := by
    intro q hq
    have hp := half_pos hq
    have hi1 := hint _ hp
    have hi2 := hint _ hq
    have hdiff : L (q / 2) - L q = ∫ t in Ioi (0 : ℝ),
        (Real.exp (-(q / 2 * t)) - Real.exp (-(q * t))) * y t := by
      simp only [L]
      rw [← integral_sub hi1 hi2]
      exact setIntegral_congr_fun measurableSet_Ioi fun t _ => by ring
    have hint' : IntegrableOn (fun t => (Real.exp (-(q / 2 * t)) - Real.exp (-(q * t))) * y t)
        (Ioi 0) :=
      (hi1.sub hi2).congr_fun (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi
    have hnn' : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ (Real.exp (-(q / 2 * t)) - Real.exp (-(q * t))) * y t :=
      fun t ht => by
        have ht' : (0 : ℝ) < t := ht
        refine mul_nonneg ?_ (hnn t ht'.le)
        have : Real.exp (-(q * t)) ≤ Real.exp (-(q / 2 * t)) := Real.exp_le_exp.2 (by nlinarith)
        linarith
    have hmono := setIntegral_mono_set (s := Ioc (0 : ℝ) ε) (t := Ioi 0) hint'
      (ae_restrict_of_forall_mem measurableSet_Ioi hnn')
      (Eventually.of_forall fun x hx => Ioc_subset_Ioi_self hx)
    have hpt : ∀ t ∈ Ioc (0 : ℝ) ε, q / 2 * Real.exp (-(q * ε)) * (t * y t) ≤
        (Real.exp (-(q / 2 * t)) - Real.exp (-(q * t))) * y t := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have hyt := (hpos t ht).le
      have hgap : q / 2 * t * Real.exp (-(q * t)) ≤
          Real.exp (-(q / 2 * t)) - Real.exp (-(q * t)) := by
        have h := Real.add_one_le_exp (q / 2 * t)
        have e : Real.exp (-(q / 2 * t)) = Real.exp (q / 2 * t) * Real.exp (-(q * t)) := by
          rw [← Real.exp_add]; ring_nf
        rw [e]
        nlinarith [Real.exp_pos (-(q * t))]
      have hexp : Real.exp (-(q * ε)) ≤ Real.exp (-(q * t)) :=
        Real.exp_le_exp.2 (by nlinarith [ht.2])
      calc q / 2 * Real.exp (-(q * ε)) * (t * y t) = (q / 2 * t * Real.exp (-(q * ε))) * y t := by
            ring
        _ ≤ (q / 2 * t * Real.exp (-(q * t))) * y t :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (by positivity)) hyt
        _ ≤ _ := mul_le_mul_of_nonneg_right hgap hyt
    have hmono2 := setIntegral_mono_on
      ((hcont.const_mul (q / 2 * Real.exp (-(q * ε)))).integrableOn_Ioc)
      (hint'.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hpt
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hε.le] at hmono2
    rw [hdiff]
    linarith
  set E := Real.exp (-ε)
  have hE : 0 < E := Real.exp_pos _
  set q := min 1 (J * E / (4 * C))
  have hq : 0 < q := lt_min one_pos (by positivity)
  have hq1 : q ≤ 1 := min_le_left _ _
  have hq2 : q ≤ J * E / (4 * C) := min_le_right _ _
  have hEq : E ≤ Real.exp (-(q * ε)) := Real.exp_le_exp.2 (by nlinarith)
  have hlo := hlower q hq
  have hup1 := (hdef (q / 2) (half_pos hq) (by linarith)).2
  have hup2 := (hdef q hq hq1).1
  have h1 : q / 2 * E * J ≤ C * q ^ 2 := by
    have := mul_le_mul_of_nonneg_left hEq (by positivity : (0 : ℝ) ≤ q / 2)
    nlinarith [mul_le_mul_of_nonneg_right this hJ.le]
  have h2 : C * q ^ 2 ≤ q * (J * E / 4) := by
    have : C * q ≤ J * E / 4 := by
      rw [le_div_iff₀ (by positivity)] at hq2; nlinarith
    nlinarith
  nlinarith [mul_pos (mul_pos hq hE) hJ]

/-! ## Complete tails -/

/-- Tail coefficients: `c_{m+1}` for `m ≥ n`, else `0`. -/
def liClockThetaKernelTailCoeff (n m : ℕ) : ℝ :=
  if n ≤ m then liClockThetaGeneratorCoeff (m + 1) else 0

/-- The complete tail `K_{n+1} = Σ_{m ≥ n} c_{m+1} t^{2m+1}/(2m+1)!`. -/
def liClockThetaKernelTail (n : ℕ) (t : ℝ) : ℝ :=
  oddFactorialSeries (liClockThetaKernelTailCoeff n) t

/-- The odd polynomial head `P_{n+1} = Σ_{m < n} c_{m+1} t^{2m+1}/(2m+1)!`. -/
def liClockThetaKernelHead (n : ℕ) (t : ℝ) : ℝ :=
  ∑ m ∈ Finset.range n, liClockThetaGeneratorCoeff (m + 1) * t ^ (2 * m + 1) /
    ((2 * m + 1).factorial : ℝ)

/-- The causal inverse `q_{n+1} = K_{n+1} - r ⋆ K_{n+1}` of the complete tail. -/
def liClockThetaTailInverse (n : ℕ) : ℝ → ℝ := liClockThetaInverse (liClockThetaKernelTail n)

private theorem tailCoeff_nonneg (n m : ℕ) : 0 ≤ liClockThetaKernelTailCoeff n m := by
  unfold liClockThetaKernelTailCoeff
  split_ifs
  · exact (liClockThetaGeneratorCoeff_pos _).le
  · exact le_rfl

private theorem tailCoeff_le (n m : ℕ) :
    liClockThetaKernelTailCoeff n m ≤ liClockThetaGeneratorCoeff (m + 1) := by
  unfold liClockThetaKernelTailCoeff
  split_ifs
  · exact le_rfl
  · exact (liClockThetaGeneratorCoeff_pos _).le

private theorem hτ (n : ℕ) : GeometricCoeffBound (liClockThetaKernelTailCoeff n)
    (1 * (32 / 303)) (32 / 303) := fun m => by
  rw [abs_of_nonneg (tailCoeff_nonneg n m)]
  have := geometricCoeffBound_liClockThetaGeneratorCoeff.shift m
  rw [abs_of_pos (liClockThetaGeneratorCoeff_pos _)] at this
  exact (tailCoeff_le n m).trans this

private theorem hτ_small (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) (k : ℕ) :
    |liClockThetaKernelTailCoeff n k| ≤ (Real.exp (32 / (303 * ρ ^ 2)) * ρ ^ 2) * ρ ^ (2 * k) := by
  rw [abs_of_nonneg (tailCoeff_nonneg n k)]
  have := liClockThetaGeneratorCoeff_le_pow hρ (k + 1)
  rw [show 2 * (k + 1) = 2 + 2 * k by ring, pow_add] at this
  calc _ ≤ liClockThetaGeneratorCoeff (k + 1) := tailCoeff_le n k
    _ ≤ _ := this
    _ = _ := by ring

theorem liClockThetaKernel_eq_head_add_tail (n : ℕ) (t : ℝ) :
    liClockThetaKernel t = liClockThetaKernelHead n t + liClockThetaKernelTail n t := by
  have hs := summable_oddFactorialSeries_term (by norm_num) (hτ n) t
  have hk := summable_oddFactorialSeries_term (by norm_num)
    geometricCoeffBound_liClockThetaGeneratorCoeff.shift t
  unfold liClockThetaKernel liClockThetaKernelHead liClockThetaKernelTail oddFactorialSeries
  rw [← hk.sum_add_tsum_nat_add n, ← hs.sum_add_tsum_nat_add n]
  have h1 : ∑ i ∈ Finset.range n, liClockThetaKernelTailCoeff n i * t ^ (2 * i + 1) /
      ((2 * i + 1).factorial : ℝ) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      simp [liClockThetaKernelTailCoeff, show ¬ n ≤ i by omega]
  have h2 : ∀ i, liClockThetaKernelTailCoeff n (i + n) = liClockThetaGeneratorCoeff (i + n + 1) :=
    fun i => by simp [liClockThetaKernelTailCoeff]
  rw [h1, zero_add]
  simp only [h2]

theorem liClockThetaKernelTail_zero : liClockThetaKernelTail 0 = liClockThetaKernel := by
  funext t
  rw [liClockThetaKernel_eq_head_add_tail 0 t]
  simp [liClockThetaKernelHead]

theorem contDiff_liClockThetaKernelTail (n : ℕ) : ContDiff ℝ ∞ (liClockThetaKernelTail n) :=
  contDiff_oddFactorialSeries (by norm_num) (hτ n)

theorem liClockEveryExpType_liClockThetaKernelTail (n : ℕ) :
    LiClockEveryExpType (liClockThetaKernelTail n) := by
  have e : liClockThetaKernelTail n = borelSeries (oddSpread (liClockThetaKernelTailCoeff n)) := by
    rw [← oddFactorialSeries_eq_borelSeries (by norm_num) (hτ n)]; rfl
  rw [e]
  exact liClockEveryExpType_borelSeries fun R hR =>
    ⟨_, geometricCoeffBound_oddSpread_of_le hR (hτ_small n hR)⟩

theorem liClockThetaKernelTail_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ liClockThetaKernelTail n t := by
  unfold liClockThetaKernelTail oddFactorialSeries
  exact tsum_nonneg fun m => by have := tailCoeff_nonneg n m; positivity

/-! ## The tail inverse -/

theorem liClockThetaTailInverse_volterra (n : ℕ) (t : ℝ) :
    liClockThetaTailInverse n t + volterraConv (liClockThetaTailInverse n) liClockThetaKernel t =
      liClockThetaKernelTail n t :=
  liClockThetaInverse_volterra (contDiff_liClockThetaKernelTail n).continuous t

theorem liClockThetaTailInverse_zero : liClockThetaTailInverse 0 = liClockThetaResolvent := by
  have h := eq_liClockThetaInverse (h := liClockThetaKernelTail 0) (y := liClockThetaResolvent)
    (contDiff_liClockThetaKernelTail 0).continuous continuous_liClockThetaResolvent
    (fun t => by rw [liClockThetaKernelTail_zero]; exact liClockThetaResolvent_volterra t)
  exact h.symm

theorem continuous_liClockThetaKernelHead (n : ℕ) : Continuous (liClockThetaKernelHead n) := by
  unfold liClockThetaKernelHead; fun_prop

/-- **Head decomposition.**  `q_{n+1} = r - P_{n+1} + r ⋆ P_{n+1}`. -/
theorem liClockThetaTailInverse_eq (n : ℕ) (t : ℝ) :
    liClockThetaTailInverse n t = liClockThetaResolvent t - liClockThetaKernelHead n t +
      volterraConv liClockThetaResolvent (liClockThetaKernelHead n) t := by
  have hr := continuous_liClockThetaResolvent
  have hP := continuous_liClockThetaKernelHead n
  have hT := (contDiff_liClockThetaKernelTail n).continuous
  have hK := continuous_liClockThetaKernel
  have htail : liClockThetaKernelTail n = fun s => liClockThetaKernel s - liClockThetaKernelHead n s :=
    funext fun s => by linarith [liClockThetaKernel_eq_head_add_tail n s]
  have hrK : volterraConv liClockThetaResolvent liClockThetaKernel t =
      liClockThetaKernel t - liClockThetaResolvent t := by
    linarith [liClockThetaResolvent_volterra t]
  unfold liClockThetaTailInverse liClockThetaInverse
  rw [htail, volterraConv_sub_right hr hK hP, hrK]
  ring

theorem liClockSubGammaClass_liClockThetaTailInverse (n : ℕ) :
    LiClockSubGammaClass (liClockThetaTailInverse n) :=
  liClockSubGammaClass_liClockThetaInverse (contDiff_liClockThetaKernelTail n)
    (liClockEveryExpType_liClockThetaKernelTail n)

/-! ## Origin order of the tail inverse -/

private theorem hρ : GeometricCoeffBound (fun m => -liClockThetaReciprocalCoeff (m + 1)) 1
    (32 / 303 + 1 / 2) := by
  intro m
  rw [abs_neg]
  refine (abs_liClockThetaReciprocalCoeff_le (m + 1)).trans ?_
  rw [pow_succ', one_mul]
  calc (1 / 2 : ℝ) * (1 / 2) ^ m ≤ (1 / 2) ^ m := by
        have := pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) m; linarith
    _ ≤ (32 / 303 + 1 / 2) ^ m := pow_le_pow_left₀ (by norm_num) (by norm_num) m

private theorem hτ' (n : ℕ) : GeometricCoeffBound (liClockThetaKernelTailCoeff n)
    (1 * (32 / 303)) (32 / 303 + 1 / 2) := fun m =>
  (hτ n m).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by norm_num) (by norm_num) m)
    (by norm_num))

/-- The odd Taylor coefficients of `q_{n+1}`. -/
def liClockThetaTailInverseCoeff (n m : ℕ) : ℝ :=
  liClockThetaKernelTailCoeff n m -
    oddConvCoeff (fun m => -liClockThetaReciprocalCoeff (m + 1)) (liClockThetaKernelTailCoeff n) m

theorem liClockThetaTailInverse_eq_oddFactorialSeries (n : ℕ) :
    liClockThetaTailInverse n = oddFactorialSeries (liClockThetaTailInverseCoeff n) := by
  funext t
  have hconv := volterraConv_oddFactorialSeries hρ (hτ' n) (by norm_num) t
  have hcb : GeometricCoeffBound (oddConvCoeff (fun m => -liClockThetaReciprocalCoeff (m + 1))
      (liClockThetaKernelTailCoeff n)) (1 * (1 * (32 / 303)) / (2 * (32 / 303 + 1 / 2)))
      (2 * (32 / 303 + 1 / 2)) := fun m => by
    rw [oddConvCoeff_eq_borelConvCoeff]
    exact geometricCoeffBound_borelConvCoeff hρ (hτ' n) (by norm_num) m
  unfold liClockThetaTailInverse liClockThetaInverse liClockThetaKernelTail
  rw [show liClockThetaResolvent = oddFactorialSeries fun m => -liClockThetaReciprocalCoeff (m + 1)
    from rfl, hconv]
  unfold oddFactorialSeries liClockThetaTailInverseCoeff
  rw [← Summable.tsum_sub (summable_oddFactorialSeries_term (by norm_num) (hτ n) t)
    (summable_oddFactorialSeries_term (by norm_num) hcb t)]
  exact tsum_congr fun m => by ring

theorem liClockThetaTailInverseCoeff_eq_zero {n m : ℕ} (hm : m < n) :
    liClockThetaTailInverseCoeff n m = 0 := by
  unfold liClockThetaTailInverseCoeff
  have h1 : liClockThetaKernelTailCoeff n m = 0 := by
    simp [liClockThetaKernelTailCoeff, show ¬ n ≤ m by omega]
  rw [h1, zero_sub, neg_eq_zero]
  rcases m with _ | m
  · rfl
  · unfold oddConvCoeff
    refine Finset.sum_eq_zero fun pq hpq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    simp [liClockThetaKernelTailCoeff, show ¬ n ≤ pq.2 by omega]

theorem liClockThetaTailInverseCoeff_self (n : ℕ) :
    liClockThetaTailInverseCoeff n n = liClockThetaGeneratorCoeff (n + 1) := by
  unfold liClockThetaTailInverseCoeff
  have h1 : liClockThetaKernelTailCoeff n n = liClockThetaGeneratorCoeff (n + 1) := by
    simp [liClockThetaKernelTailCoeff]
  rw [h1]
  rcases n with _ | n
  · simp [oddConvCoeff]
  · have h2 : oddConvCoeff (fun m => -liClockThetaReciprocalCoeff (m + 1))
        (liClockThetaKernelTailCoeff (n + 1)) (n + 1) = 0 := by
      show ∑ pq ∈ Finset.HasAntidiagonal.antidiagonal n, _ = 0
      refine Finset.sum_eq_zero fun pq hpq => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hpq
      simp [liClockThetaKernelTailCoeff, show ¬ n + 1 ≤ pq.2 by omega]
    rw [h2, sub_zero]

theorem geometricCoeffBound_liClockThetaTailInverseCoeff (n : ℕ) :
    GeometricCoeffBound (liClockThetaTailInverseCoeff n)
    (1 * (32 / 303) + 1 * (1 * (32 / 303)) / (2 * (32 / 303 + 1 / 2))) (2 * (32 / 303 + 1 / 2)) := by
  intro m
  have h1 := hτ' n m
  have h2 : |oddConvCoeff (fun m => -liClockThetaReciprocalCoeff (m + 1))
      (liClockThetaKernelTailCoeff n) m| ≤ 1 * (1 * (32 / 303)) / (2 * (32 / 303 + 1 / 2)) *
        (2 * (32 / 303 + 1 / 2)) ^ m := by
    rw [oddConvCoeff_eq_borelConvCoeff]
    exact geometricCoeffBound_borelConvCoeff hρ (hτ' n) (by norm_num) m
  have h3 : (32 / 303 + 1 / 2 : ℝ) ^ m ≤ (2 * (32 / 303 + 1 / 2)) ^ m :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) m
  unfold liClockThetaTailInverseCoeff
  calc _ ≤ |liClockThetaKernelTailCoeff n m| + |oddConvCoeff (fun m => -liClockThetaReciprocalCoeff
        (m + 1)) (liClockThetaKernelTailCoeff n) m| := abs_sub _ _
    _ ≤ 1 * (32 / 303) * (2 * (32 / 303 + 1 / 2)) ^ m +
        1 * (1 * (32 / 303)) / (2 * (32 / 303 + 1 / 2)) * (2 * (32 / 303 + 1 / 2)) ^ m :=
        add_le_add (h1.trans (mul_le_mul_of_nonneg_left h3 (by norm_num))) h2
    _ = _ := by ring

theorem contDiff_liClockThetaTailInverse (n : ℕ) : ContDiff ℝ ∞ (liClockThetaTailInverse n) := by
  rw [liClockThetaTailInverse_eq_oddFactorialSeries]
  exact contDiff_oddFactorialSeries (by norm_num) (geometricCoeffBound_liClockThetaTailInverseCoeff n)

/-- `q_{n+1}` vanishes to order `2n+1` at the origin. -/
theorem iteratedDeriv_liClockThetaTailInverse_zero {n k : ℕ} (hk : k < 2 * n + 1) :
    iteratedDeriv k (liClockThetaTailInverse n) 0 = 0 := by
  have hb := geometricCoeffBound_liClockThetaTailInverseCoeff n
  rw [liClockThetaTailInverse_eq_oddFactorialSeries, oddFactorialSeries_eq_borelSeries (by norm_num) hb,
    iteratedDeriv_borelSeries (hb.oddSpread (by norm_num)), borelSeries_zero, zero_add]
  obtain ⟨m, hm | hm⟩ := Nat.even_or_odd' k
  · rw [hm, oddSpread_two_mul]
  · rw [hm, oddSpread_two_mul_add_one]; exact liClockThetaTailInverseCoeff_eq_zero (by omega)

/-- **Origin law.**  `q_{n+1}(t) = c_{n+1} t^{2n+1}/(2n+1)! + O(t^{2n+3})` for `|t| ≤ 1`. -/
theorem abs_liClockThetaTailInverse_sub_le (n : ℕ) {t : ℝ} (ht : |t| ≤ 1) :
    |liClockThetaTailInverse n t - liClockThetaGeneratorCoeff (n + 1) * t ^ (2 * n + 1) /
        ((2 * n + 1).factorial : ℝ)| ≤
      (1 * (32 / 303) + 1 * (1 * (32 / 303)) / (2 * (32 / 303 + 1 / 2))) *
        Real.exp (2 * (32 / 303 + 1 / 2)) * |t| ^ (2 * (n + 1) + 1) := by
  have h := abs_oddFactorialSeries_sub_sum_le (by norm_num)
    (geometricCoeffBound_liClockThetaTailInverseCoeff n) ht (n + 1)
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun m hm => by
    rw [liClockThetaTailInverseCoeff_eq_zero (Finset.mem_range.1 hm)]; ring,
    zero_add, liClockThetaTailInverseCoeff_self] at h
  rw [liClockThetaTailInverse_eq_oddFactorialSeries]
  exact h

theorem exists_liClockThetaTailInverse_pos (n : ℕ) :
    ∃ ε > 0, ∀ t ∈ Ioc (0 : ℝ) ε, 0 < liClockThetaTailInverse n t := by
  set M := (1 * (32 / 303) + 1 * (1 * (32 / 303)) / (2 * (32 / 303 + 1 / 2))) *
    Real.exp (2 * (32 / 303 + 1 / 2))
  set c := liClockThetaGeneratorCoeff (n + 1) / ((2 * n + 1).factorial : ℝ)
  have hc : 0 < c := div_pos (liClockThetaGeneratorCoeff_pos _)
    (by exact_mod_cast Nat.factorial_pos _)
  have hM : 0 < M := by positivity
  refine ⟨min 1 (c / (2 * M)), lt_min one_pos (by positivity), fun t ht => ?_⟩
  have ht0 : 0 < t := ht.1
  have ht1 : t ≤ 1 := ht.2.trans (min_le_left _ _)
  have ht2 : t ≤ c / (2 * M) := ht.2.trans (min_le_right _ _)
  have h := abs_liClockThetaTailInverse_sub_le n (by rw [abs_of_pos ht0]; exact ht1)
  change |_| ≤ M * |t| ^ (2 * (n + 1) + 1) at h
  rw [abs_of_pos ht0] at h
  have hlow := (abs_le.1 h).1
  have hp : 0 < t ^ (2 * n + 1) := pow_pos ht0 _
  have e1 : liClockThetaGeneratorCoeff (n + 1) * t ^ (2 * n + 1) / ((2 * n + 1).factorial : ℝ) =
      c * t ^ (2 * n + 1) := by ring
  have e2 : t ^ (2 * (n + 1) + 1) = t ^ 2 * t ^ (2 * n + 1) := by
    rw [show 2 * (n + 1) + 1 = 2 + (2 * n + 1) by ring, pow_add]
  have htt : t ^ 2 ≤ t := by nlinarith
  have hMt : M * t ≤ c / 2 := by
    rw [le_div_iff₀ (by positivity)] at ht2; linarith
  rw [e1, e2] at hlow
  have : M * (t ^ 2 * t ^ (2 * n + 1)) ≤ c / 2 * t ^ (2 * n + 1) := by
    have := mul_le_mul_of_nonneg_left htt hM.le
    nlinarith
  nlinarith

/-! ## Sign change of every complete tail inverse -/

theorem hasSum_integral_Ioi_liClockThetaKernelTail {n : ℕ} {p : ℝ} (hp : 0 < p) :
    HasSum (fun k : ℕ => liClockThetaKernelTailCoeff n k * (p ^ (2 * k + 2))⁻¹)
      (∫ t in Ioi (0 : ℝ), liClockThetaKernelTail n t * Real.exp (-(p * t))) :=
  hasSum_integral_Ioi_oddFactorialSeries_mul_exp_neg (by norm_num) (hτ n)
    (geometricCoeffBound_oddSpread_of_le (half_pos hp) (hτ_small n (half_pos hp))) (by positivity)
    (by linarith)

private theorem integrableOn_tail {n : ℕ} {p : ℝ} (hp : 0 < p) :
    IntegrableOn (fun t => liClockThetaKernelTail n t * Real.exp (-(p * t))) (Ioi 0) := by
  unfold liClockThetaKernelTail
  rw [oddFactorialSeries_eq_borelSeries (by norm_num) (hτ n)]
  exact integrableOn_borelSeries_mul_exp_neg
    (geometricCoeffBound_oddSpread_of_le (half_pos hp) (hτ_small n (half_pos hp))) (by linarith)

/-- **Every complete tail inverse changes sign.**  For every `n`, `q_{n+1}` is negative at some
positive clock (`n = 0` is the resolvent). -/
theorem exists_liClockThetaTailInverse_neg (n : ℕ) :
    ∃ T > 0, liClockThetaTailInverse n T < 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hq0 : liClockThetaTailInverse n 0 = 0 := by
    rw [liClockThetaTailInverse_eq_oddFactorialSeries, oddFactorialSeries_zero]
  have hnn : ∀ t, 0 ≤ t → 0 ≤ liClockThetaTailInverse n t := fun t ht => by
    rcases ht.eq_or_lt with h | h
    · rw [← h, hq0]
    · exact hcon t h
  obtain ⟨ε, hε, hpos⟩ := exists_liClockThetaTailInverse_pos n
  have hqc : Continuous (liClockThetaTailInverse n) := (contDiff_liClockThetaTailInverse n).continuous
  have hle : ∀ t, 0 ≤ t → liClockThetaTailInverse n t ≤ liClockThetaKernelTail n t := by
    intro t ht
    have h := liClockThetaTailInverse_volterra n t
    have hc : 0 ≤ volterraConv (liClockThetaTailInverse n) liClockThetaKernel t := by
      unfold volterraConv
      exact intervalIntegral.integral_nonneg ht fun s hs =>
        mul_nonneg (hnn _ (by linarith [hs.2])) (liClockThetaKernel_nonneg hs.1)
    linarith
  have hint : ∀ p, 0 < p → IntegrableOn (fun t => Real.exp (-(p * t)) *
      liClockThetaTailInverse n t) (Ioi 0) := by
    intro p hp
    refine (integrableOn_tail (n := n) hp).mono' ((by fun_prop : Continuous fun t : ℝ =>
      Real.exp (-(p * t))).mul hqc).aestronglyMeasurable ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht' : (0 : ℝ) ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg (hnn t ht'),
      mul_comm]
    exact mul_le_mul_of_nonneg_right (hle t ht') (Real.exp_pos _).le
  set Cn : ℝ := 1 + ∑ m ∈ Finset.range n, liClockThetaGeneratorCoeff (m + 1)
  have hCn : 0 < Cn := by
    have : 0 ≤ ∑ m ∈ Finset.range n, liClockThetaGeneratorCoeff (m + 1) :=
      Finset.sum_nonneg fun m _ => (liClockThetaGeneratorCoeff_pos _).le
    linarith
  have hcn := liClockThetaGeneratorCoeff_pos (n + 1)
  refine false_of_laplace_deficit hqc hε hpos hnn hint (C := Cn / liClockThetaGeneratorCoeff (n + 1))
    (by positivity) fun p hp hp1 => ?_
  -- the conditional Laplace identity
  have hKi : IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaKernel t) (Ioi 0) :=
    (integrableOn_liClockThetaKernel_mul_exp_neg hp).congr_fun (fun t _ => mul_comm _ _)
      measurableSet_Ioi
  have hconv := integral_exp_mul_volterraConv_of_nonneg hqc continuous_liClockThetaKernel hnn
    (fun t ht => liClockThetaKernel_nonneg ht) (hint p hp) hKi
  have hTi : IntegrableOn (fun t => Real.exp (-(p * t)) * liClockThetaKernelTail n t) (Ioi 0) :=
    (integrableOn_tail hp).congr_fun (fun t _ => mul_comm _ _) measurableSet_Ioi
  have hsub : (fun t => Real.exp (-(p * t)) *
      volterraConv (liClockThetaTailInverse n) liClockThetaKernel t) =
      fun t => Real.exp (-(p * t)) * liClockThetaKernelTail n t -
        Real.exp (-(p * t)) * liClockThetaTailInverse n t := by
    funext t
    have := liClockThetaTailInverse_volterra n t
    rw [show volterraConv (liClockThetaTailInverse n) liClockThetaKernel t =
      liClockThetaKernelTail n t - liClockThetaTailInverse n t by linarith]
    ring
  rw [hsub, integral_sub hTi (hint p hp)] at hconv
  set Lq := ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaTailInverse n t
  set LK := ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaKernel t
  set LT := ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockThetaKernelTail n t
  -- the head of the transform
  have hKs := hasSum_integral_Ioi_liClockThetaKernel_mul_exp_neg hp
  have hTs := hasSum_integral_Ioi_liClockThetaKernelTail (n := n) hp
  have hLK : LK = ∫ t in Ioi (0 : ℝ), liClockThetaKernel t * Real.exp (-(p * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _
  have hLT : LT = ∫ t in Ioi (0 : ℝ), liClockThetaKernelTail n t * Real.exp (-(p * t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => mul_comm _ _
  have hhead : HasSum (fun k : ℕ => (if k < n then liClockThetaGeneratorCoeff (k + 1) else 0) *
      (p ^ (2 * k + 2))⁻¹) (LK - LT) := by
    rw [hLK, hLT]
    refine (hKs.sub hTs).congr_fun fun k => ?_
    unfold liClockThetaKernelTailCoeff
    by_cases hk : k < n
    · rw [if_pos hk, if_neg (by omega)]; ring
    · rw [if_neg hk, if_pos (by omega)]; ring
  have hfin : LK - LT = ∑ k ∈ Finset.range n, liClockThetaGeneratorCoeff (k + 1) *
      (p ^ (2 * k + 2))⁻¹ := by
    refine hhead.unique ?_
    have h : HasSum (fun k : ℕ => (if k < n then liClockThetaGeneratorCoeff (k + 1) else 0) *
        (p ^ (2 * k + 2))⁻¹) (∑ k ∈ Finset.range n,
          (if k < n then liClockThetaGeneratorCoeff (k + 1) else 0) * (p ^ (2 * k + 2))⁻¹) :=
      hasSum_sum_of_ne_finset_zero fun k hk => by
        rw [Finset.mem_range] at hk; rw [if_neg hk, zero_mul]
    convert h using 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk; rw [if_pos hk]
  have hLKlow : liClockThetaGeneratorCoeff (n + 1) * (p ^ (2 * n + 2))⁻¹ ≤ LK := by
    rw [hLK]
    exact le_hasSum hKs n fun j _ => mul_nonneg (liClockThetaGeneratorCoeff_pos _).le
      (by positivity)
  have hLT0 : 0 ≤ LT := by
    rw [hLT]
    exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (liClockThetaKernelTail_nonneg n (le_of_lt ht)) (Real.exp_pos _).le
  have hLK0 : 0 ≤ LK := le_trans (by positivity) hLKlow
  -- the identity `Lq (1 + LK) = LT`
  have hid : Lq * (1 + LK) = LT := by linarith
  have hQ0 : 0 ≤ ∑ k ∈ Finset.range n, liClockThetaGeneratorCoeff (k + 1) * (p ^ (2 * k + 2))⁻¹ :=
    Finset.sum_nonneg fun k _ => mul_nonneg (liClockThetaGeneratorCoeff_pos _).le (by positivity)
  have hdenom : 0 < 1 + LK := by linarith
  have hgap : 1 - Lq = (1 + (LK - LT)) / (1 + LK) := by
    field_simp; linarith
  have hQup : 1 + (LK - LT) ≤ Cn * (p ^ (2 * n))⁻¹ := by
    rw [hfin]
    have hpn : (1 : ℝ) ≤ (p ^ (2 * n))⁻¹ := one_le_inv₀ (by positivity) |>.2
      (pow_le_one₀ hp.le hp1)
    have hterm : ∀ k ∈ Finset.range n, liClockThetaGeneratorCoeff (k + 1) * (p ^ (2 * k + 2))⁻¹ ≤
        liClockThetaGeneratorCoeff (k + 1) * (p ^ (2 * n))⁻¹ := by
      intro k hk
      rw [Finset.mem_range] at hk
      refine mul_le_mul_of_nonneg_left ?_ (liClockThetaGeneratorCoeff_pos _).le
      exact inv_anti₀ (by positivity) (pow_le_pow_of_le_one hp.le hp1 (by omega))
    have := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul] at this
    calc 1 + ∑ k ∈ Finset.range n, liClockThetaGeneratorCoeff (k + 1) * (p ^ (2 * k + 2))⁻¹ ≤
        1 * (p ^ (2 * n))⁻¹ + (∑ k ∈ Finset.range n, liClockThetaGeneratorCoeff (k + 1)) *
          (p ^ (2 * n))⁻¹ := by linarith
      _ = Cn * (p ^ (2 * n))⁻¹ := by ring
  constructor
  · -- `1 - Lq ≤ (Cn / c_{n+1}) p²`
    have hratio : (1 + (LK - LT)) / (1 + LK) ≤ Cn / liClockThetaGeneratorCoeff (n + 1) * p ^ 2 := by
      rw [div_le_iff₀ hdenom]
      have hlow : liClockThetaGeneratorCoeff (n + 1) * (p ^ (2 * n + 2))⁻¹ ≤ 1 + LK := by linarith
      calc 1 + (LK - LT) ≤ Cn * (p ^ (2 * n))⁻¹ := hQup
        _ = Cn / liClockThetaGeneratorCoeff (n + 1) * p ^ 2 *
            (liClockThetaGeneratorCoeff (n + 1) * (p ^ (2 * n + 2))⁻¹) := by
            rw [show 2 * n + 2 = 2 * n + 2 from rfl, pow_add]
            field_simp
        _ ≤ Cn / liClockThetaGeneratorCoeff (n + 1) * p ^ 2 * (1 + LK) :=
            mul_le_mul_of_nonneg_left hlow (by positivity)
    linarith
  · have : 0 ≤ (1 + (LK - LT)) / (1 + LK) := by
      apply div_nonneg _ hdenom.le
      linarith
    linarith

end RHTower
