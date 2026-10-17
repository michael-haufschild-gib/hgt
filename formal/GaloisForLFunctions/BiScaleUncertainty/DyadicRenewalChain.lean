import GaloisForLFunctions.BiScaleUncertainty.DiscrepancyTransformLaw
import GaloisForLFunctions.HTGeometry.RectangularSchurBound

/-!
# The renewal chain of the causal response: coarse block discrepancies and fine block energies

The causal response `R_N = K ⋆ ν_N` has the Markov property of the exponential kernel: for
`0 ≤ a ≤ t ≤ L`,

`R_N(t) = e^{−(t−a)/2} R_N(a) + e^{−t/2} [(ψ(e^t) − ψ(e^a)) − (e^t − e^a) − (t − a)]`.

Sampling at the block edges `t_k = kh` of a geometric scale ladder `e^{kh}` gives a linear chain

`x_{k+1} = q x_k + r_k`,  `q = e^{−h/2}`,  `x_0 = 0`,

driven by the normalized block discrepancies
`r_k = e^{−(k+1)h/2} [(ψ(e^{(k+1)h}) − ψ(e^{kh})) − (e^{(k+1)h} − e^{kh}) − h]`.
The window energy over `K` blocks is controlled two-sidedly by the chain states and the intra-block
energies `c_k = ∫_{block} (R_N − e^{−(t−t_k)/2} x_k)²`,

`(h e^{−h}/2) Σ x_k² − Σ c_k ≤ ∫_0^{Kh} R_N² ≤ 2h Σ x_k² + 2 Σ c_k`,

and the Schur test for the geometric kernel gives `Σ x_k² ≤ (1−q)^{−2} Σ r_k²`, with the converse
`Σ r_k² ≤ 4 Σ x_k²`.  Thus the Laplace energy up to scale `e^{Kh}` is equivalent, with explicit
constants, to the sum of the squared block discrepancies plus the sum of the fine block energies: the
coarse scale (block totals of `ψ`) and the fine scale (the variation of `ψ` inside a block) are
separated exactly.  For `h = log 2` the blocks are dyadic, `q = 1/√2`, and
`r_k = 2^{−(k+1)/2} (ψ(2^{k+1}) − ψ(2^k) − 2^k − log 2)`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported Real

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## The renewal (Markov) law of the causal response -/

/-- The block response: the normalized block-relative Chebyshev error with its transient. -/
def blockResponse (a t : ℝ) : ℝ :=
  Real.exp (-t / 2) * ((Chebyshev.psi (Real.exp t) - Chebyshev.psi (Real.exp a)) -
    (Real.exp t - Real.exp a) - (t - a))

/-- **The renewal law:** `R_N(t) = e^{−(t−a)/2} R_N(a) + blockResponse a t` for `0 ≤ a ≤ t ≤ L`. -/
theorem causalResponse_renewal (N : ℕ) {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (htL : t ≤ cutoff N) :
    causalResponse N t = Real.exp (-(t - a) / 2) * causalResponse N a + blockResponse a t := by
  rw [causalResponse_eq_on_window N (ha.trans hat) htL,
    causalResponse_eq_on_window N ha (hat.trans htL)]
  unfold blockResponse normalizedLogError logError
  have h : Real.exp (-(t - a) / 2) * Real.exp (-a / 2) = Real.exp (-t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination (-(Chebyshev.psi (Real.exp a) - Real.exp a + (1 - a))) * h

theorem causalResponse_zero (N : ℕ) : causalResponse N 0 = 0 := by
  rw [causalResponse_eq_on_window N le_rfl (cutoff_nonneg N)]
  unfold normalizedLogError logError
  simp [Chebyshev.psi_one]

/-! ## The block chain on a geometric scale ladder -/

/-- The chain state `x_k = R_N(kh)`. -/
def chainState (N : ℕ) (h : ℝ) (k : ℕ) : ℝ := causalResponse N (k * h)

/-- The chain input `r_k`: the normalized discrepancy of the `k`-th block. -/
def chainInput (h : ℝ) (k : ℕ) : ℝ := blockResponse (k * h) ((k + 1) * h)

/-- The fine (intra-block) energy `c_k = ∫_{block k} (R_N − e^{−(t−kh)/2} x_k)²`. -/
def blockEnergy (N : ℕ) (h : ℝ) (k : ℕ) : ℝ :=
  ∫ t in (k * h)..((k + 1) * h),
    (causalResponse N t - Real.exp (-(t - k * h) / 2) * chainState N h k) ^ 2

theorem chainState_zero (N : ℕ) (h : ℝ) : chainState N h 0 = 0 := by
  unfold chainState; simp [causalResponse_zero]

theorem chainState_succ (N : ℕ) {h : ℝ} (hh : 0 ≤ h) {k : ℕ} (hk : (k + 1) * h ≤ cutoff N) :
    chainState N h (k + 1) = Real.exp (-h / 2) * chainState N h k + chainInput h k := by
  unfold chainState chainInput
  have hkh : 0 ≤ (k : ℝ) * h := by positivity
  have hle : (k : ℝ) * h ≤ (k + 1) * h := by nlinarith
  have := causalResponse_renewal N hkh hle (by exact_mod_cast hk)
  rw [show (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 by push_cast; ring, this,
    show -(((k : ℝ) + 1) * h - k * h) / 2 = -h / 2 by ring]

/-- Explicit solution of the chain: `x_k = Σ_{j<k} q^{k−1−j} r_j`. -/
theorem chainState_eq_sum (N : ℕ) {h : ℝ} (hh : 0 ≤ h) {K : ℕ} (hK : K * h ≤ cutoff N) :
    ∀ k ≤ K, chainState N h k =
      ∑ j ∈ Finset.range k, Real.exp (-h / 2) ^ (k - 1 - j) * chainInput h j := by
  intro k
  induction k with
  | zero => intro _; simp [chainState_zero]
  | succ k ih =>
    intro hk1
    have hkK : k ≤ K := by omega
    have hkh : ((k : ℕ) + 1 : ℝ) * h ≤ cutoff N := by
      have : ((k + 1 : ℕ) : ℝ) * h ≤ (K : ℝ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hk1) hh
      push_cast at this
      linarith
    rw [chainState_succ N hh hkh, ih hkK, Finset.sum_range_succ, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun j hj => ?_
      have hj : j < k := Finset.mem_range.mp hj
      rw [show k + 1 - 1 - j = (k - 1 - j) + 1 by omega, pow_succ]
      ring
    · rw [show k + 1 - 1 - k = 0 by omega, pow_zero, one_mul]

/-! ## Two-sided control of the window energy by the chain -/

theorem intervalIntegrable_sq_block (N : ℕ) (h : ℝ) (k : ℕ) :
    IntervalIntegrable
      (fun t => (causalResponse N t - Real.exp (-(t - k * h) / 2) * chainState N h k) ^ 2)
      volume (k * h) ((k + 1) * h) := by
  have hR : IntervalIntegrable (causalResponse N) volume (k * h) ((k + 1) * h) :=
    (integrable_causalResponse N).intervalIntegrable
  have hR2 : IntervalIntegrable (fun t => causalResponse N t ^ 2) volume (k * h) ((k + 1) * h) :=
    (integrable_sq_causalResponse N).intervalIntegrable
  have hg : Continuous fun t : ℝ => Real.exp (-(t - k * h) / 2) * chainState N h k := by fun_prop
  have hRg : IntervalIntegrable
      (fun t => causalResponse N t * (Real.exp (-(t - k * h) / 2) * chainState N h k))
      volume (k * h) ((k + 1) * h) :=
    hR.mul_continuousOn hg.continuousOn
  have hg2 : IntervalIntegrable (fun t => (Real.exp (-(t - k * h) / 2) * chainState N h k) ^ 2)
      volume (k * h) ((k + 1) * h) := (hg.pow 2).intervalIntegrable _ _
  have e : (fun t => (causalResponse N t - Real.exp (-(t - k * h) / 2) * chainState N h k) ^ 2) =
      fun t => causalResponse N t ^ 2 -
        2 * (causalResponse N t * (Real.exp (-(t - k * h) / 2) * chainState N h k)) +
        (Real.exp (-(t - k * h) / 2) * chainState N h k) ^ 2 := by
    funext t; ring
  rw [e]
  exact (hR2.sub (hRg.const_mul 2)).add hg2

/-- Upper block law: `∫_{block} R_N² ≤ 2h x_k² + 2 c_k`. -/
theorem integral_block_sq_le (N : ℕ) {h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    (∫ t in (k * h)..((k + 1) * h), causalResponse N t ^ 2) ≤
      2 * h * chainState N h k ^ 2 + 2 * blockEnergy N h k := by
  have hle : (k : ℝ) * h ≤ (k + 1) * h := by nlinarith
  have hmono : (∫ t in (k * h)..((k + 1) * h), causalResponse N t ^ 2) ≤
      ∫ t in (k * h)..((k + 1) * h), (2 * chainState N h k ^ 2 +
        2 * (causalResponse N t - Real.exp (-(t - k * h) / 2) * chainState N h k) ^ 2) := by
    refine intervalIntegral.integral_mono_on hle (integrable_sq_causalResponse N).intervalIntegrable
      (intervalIntegrable_const.add ((intervalIntegrable_sq_block N h k).const_mul 2))
      fun t ht => ?_
    have he : Real.exp (-(t - k * h) / 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by linarith [ht.1])
    have he0 : 0 ≤ Real.exp (-(t - k * h) / 2) := (Real.exp_pos _).le
    set x := chainState N h k
    set E := Real.exp (-(t - k * h) / 2)
    have : (E * x) ^ 2 ≤ x ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg x) (pow_le_one₀ he0 he)
    nlinarith [sq_nonneg (causalResponse N t - E * x), sq_nonneg (causalResponse N t - 2 * E * x)]
  rw [intervalIntegral.integral_add (by simp) ((intervalIntegrable_sq_block N h k).const_mul 2),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hmono
  unfold blockEnergy
  simp only [smul_eq_mul] at hmono
  nlinarith [hmono]

/-- Lower block law: `(h e^{−h}/2) x_k² − c_k ≤ ∫_{block} R_N²`. -/
theorem le_integral_block_sq (N : ℕ) {h : ℝ} (hh : 0 ≤ h) (k : ℕ) :
    h * Real.exp (-h) / 2 * chainState N h k ^ 2 - blockEnergy N h k ≤
      ∫ t in (k * h)..((k + 1) * h), causalResponse N t ^ 2 := by
  have hle : (k : ℝ) * h ≤ (k + 1) * h := by nlinarith
  have hmono : (∫ t in (k * h)..((k + 1) * h), (Real.exp (-h) / 2 * chainState N h k ^ 2 -
      (causalResponse N t - Real.exp (-(t - k * h) / 2) * chainState N h k) ^ 2)) ≤
      ∫ t in (k * h)..((k + 1) * h), causalResponse N t ^ 2 := by
    refine intervalIntegral.integral_mono_on hle
      (intervalIntegrable_const.sub (intervalIntegrable_sq_block N h k))
      (integrable_sq_causalResponse N).intervalIntegrable fun t ht => ?_
    have he : Real.exp (-h) ≤ Real.exp (-(t - k * h) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      refine Real.exp_le_exp.2 ?_
      push_cast
      linarith [ht.2]
    set x := chainState N h k
    set E := Real.exp (-(t - k * h) / 2)
    have h1 : Real.exp (-h) / 2 * x ^ 2 ≤ E ^ 2 * x ^ 2 / 2 := by
      have := mul_le_mul_of_nonneg_right he (sq_nonneg x)
      linarith
    nlinarith [h1, sq_nonneg (causalResponse N t - E * x / 2)]
  rw [intervalIntegral.integral_sub (by simp) (intervalIntegrable_sq_block N h k),
    intervalIntegral.integral_const] at hmono
  unfold blockEnergy
  simp only [smul_eq_mul] at hmono
  nlinarith [hmono]

theorem sum_integral_block_sq (N : ℕ) (h : ℝ) (K : ℕ) :
    (∑ k ∈ Finset.range K, ∫ t in (k * h)..((k + 1) * h), causalResponse N t ^ 2) =
      ∫ t in (0 : ℝ)..(K * h), causalResponse N t ^ 2 := by
  have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun t => causalResponse N t ^ 2) (a := fun k : ℕ => (k : ℝ) * h) (n := K)
    (fun k _ => (integrable_sq_causalResponse N).intervalIntegrable)
  simp only [Nat.cast_zero, zero_mul] at this
  rw [← this]
  exact Finset.sum_congr rfl fun k _ => by push_cast; rfl

/-- **Upper chain law:** `∫_0^{Kh} R_N² ≤ 2h Σ x_k² + 2 Σ c_k`. -/
theorem integral_sq_causalResponse_le_chain (N : ℕ) {h : ℝ} (hh : 0 ≤ h) (K : ℕ) :
    (∫ t in (0 : ℝ)..(K * h), causalResponse N t ^ 2) ≤
      2 * h * ∑ k ∈ Finset.range K, chainState N h k ^ 2 +
        2 * ∑ k ∈ Finset.range K, blockEnergy N h k := by
  rw [← sum_integral_block_sq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => integral_block_sq_le N hh k

/-- **Lower chain law:** `(h e^{−h}/2) Σ x_k² − Σ c_k ≤ ∫_0^{Kh} R_N²`. -/
theorem chain_le_integral_sq_causalResponse (N : ℕ) {h : ℝ} (hh : 0 ≤ h) (K : ℕ) :
    h * Real.exp (-h) / 2 * ∑ k ∈ Finset.range K, chainState N h k ^ 2 -
        ∑ k ∈ Finset.range K, blockEnergy N h k ≤
      ∫ t in (0 : ℝ)..(K * h), causalResponse N t ^ 2 := by
  rw [← sum_integral_block_sq, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun k _ => le_integral_block_sq N hh k

/-! ## The Schur bound for the geometric chain -/

/-- The geometric kernel of the chain. -/
def chainKernel (q : ℝ) (k j : ℕ) : ℝ := if j < k then q ^ (k - 1 - j) else 0

theorem chainKernel_nonneg {q : ℝ} (hq : 0 ≤ q) (k j : ℕ) : 0 ≤ chainKernel q k j := by
  unfold chainKernel; split_ifs <;> positivity

theorem sum_chainKernel_row {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {K k : ℕ} (hk : k ≤ K) :
    ∑ j ∈ Finset.range K, chainKernel q k j ≤ (1 - q)⁻¹ := by
  have hfilter : (Finset.range K).filter (fun j => j < k) = Finset.range k := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  unfold chainKernel
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hfilter,
    Finset.sum_range_reflect (fun i => q ^ i) k, Finset.range_eq_Ico]
  have := geom_sum_Ico_le_of_lt_one (m := 0) (n := k) hq0.le hq1
  rwa [pow_zero, one_div] at this

theorem sum_chainKernel_col {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (K j : ℕ) :
    ∑ k ∈ Finset.range K, chainKernel q k j ≤ (1 - q)⁻¹ := by
  have hfilter : (Finset.range K).filter (fun k => j < k) = Finset.Ico (j + 1) K := by
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  unfold chainKernel
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hfilter, Finset.sum_Ico_eq_sum_range]
  have : ∀ m ∈ Finset.range (K - (j + 1)), q ^ (j + 1 + m - 1 - j) = q ^ m := fun m _ => by
    rw [show j + 1 + m - 1 - j = m by omega]
  rw [Finset.sum_congr rfl this, Finset.range_eq_Ico]
  have h := geom_sum_Ico_le_of_lt_one (m := 0) (n := K - (j + 1)) hq0.le hq1
  rwa [pow_zero, one_div] at h

theorem chainState_eq_kernel_sum (N : ℕ) {h : ℝ} (hh : 0 ≤ h) {K : ℕ} (hK : K * h ≤ cutoff N)
    {k : ℕ} (hk : k ≤ K) :
    chainState N h k =
      ∑ j ∈ Finset.range K, chainKernel (Real.exp (-h / 2)) k j * chainInput h j := by
  rw [chainState_eq_sum N hh hK k hk]
  have hfilter : (Finset.range K).filter (fun j => j < k) = Finset.range k := by
    ext j; simp only [Finset.mem_filter, Finset.mem_range]; omega
  unfold chainKernel
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, hfilter]

/-- **Schur bound for the chain:** `Σ_{k<K} x_k² ≤ (1−q)^{−2} Σ_{j<K} r_j²`. -/
theorem sum_chainState_sq_le (N : ℕ) {h : ℝ} (hh : 0 < h) {K : ℕ} (hK : K * h ≤ cutoff N) :
    ∑ k ∈ Finset.range K, chainState N h k ^ 2 ≤
      (1 - Real.exp (-h / 2))⁻¹ ^ 2 * ∑ j ∈ Finset.range K, chainInput h j ^ 2 := by
  set q := Real.exp (-h / 2) with hq
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hC : 0 ≤ (1 - q)⁻¹ := inv_nonneg.2 (by linarith)
  have hS := GaloisForLFunctions.weighted_rectangular_sum_sq_le (Finset.range K) (Finset.range K)
    (chainKernel q) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) (chainInput h) hC (fun _ => one_pos)
    (chainKernel_nonneg hq0.le)
    (fun k hk => by
      simp only [mul_one]
      exact sum_chainKernel_row hq0 hq1 (Finset.mem_range.mp hk).le)
    (fun j _ => by
      simp only [mul_one]
      exact sum_chainKernel_col hq0 hq1 K j)
  refine le_trans (le_of_eq ?_) hS
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [chainState_eq_kernel_sum N hh.le hK (Finset.mem_range.mp hk).le]

/-- Converse: `Σ_{k<K} r_k² ≤ 4 Σ_{k≤K} x_k²`. -/
theorem sum_chainInput_sq_le (N : ℕ) {h : ℝ} (hh : 0 ≤ h) {K : ℕ} (hK : K * h ≤ cutoff N) :
    ∑ k ∈ Finset.range K, chainInput h k ^ 2 ≤
      4 * ∑ k ∈ Finset.range (K + 1), chainState N h k ^ 2 := by
  set q := Real.exp (-h / 2) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hterm : ∀ k ∈ Finset.range K, chainInput h k ^ 2 ≤
      2 * chainState N h (k + 1) ^ 2 + 2 * chainState N h k ^ 2 := by
    intro k hk
    have hk' : (k + 1) * h ≤ cutoff N := by
      have : ((k + 1 : ℕ) : ℝ) * h ≤ (K : ℝ) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hk)) hh
      push_cast at this
      linarith
    have hs := chainState_succ N hh hk'
    have hr : chainInput h k = chainState N h (k + 1) - q * chainState N h k := by rw [hs]; ring
    rw [hr]
    have hq2 : (q * chainState N h k) ^ 2 ≤ chainState N h k ^ 2 := by
      rw [mul_pow]
      exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ hq0 hq1)
    nlinarith [sq_nonneg (chainState N h (k + 1) + q * chainState N h k)]
  calc ∑ k ∈ Finset.range K, chainInput h k ^ 2
      ≤ ∑ k ∈ Finset.range K, (2 * chainState N h (k + 1) ^ 2 + 2 * chainState N h k ^ 2) :=
        Finset.sum_le_sum hterm
    _ = 2 * ∑ k ∈ Finset.range K, chainState N h (k + 1) ^ 2 +
          2 * ∑ k ∈ Finset.range K, chainState N h k ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 4 * ∑ k ∈ Finset.range (K + 1), chainState N h k ^ 2 := by
        have h1 : ∑ k ∈ Finset.range K, chainState N h (k + 1) ^ 2 ≤
            ∑ k ∈ Finset.range (K + 1), chainState N h k ^ 2 := by
          rw [Finset.sum_range_succ' (fun k => chainState N h k ^ 2) K]
          linarith [sq_nonneg (chainState N h 0)]
        have h2 : ∑ k ∈ Finset.range K, chainState N h k ^ 2 ≤
            ∑ k ∈ Finset.range (K + 1), chainState N h k ^ 2 := by
          rw [Finset.sum_range_succ]
          linarith [sq_nonneg (chainState N h K)]
        linarith

/-! ## The coarse–fine decomposition of the window energy -/

/-- **The window energy is controlled by the block discrepancies and the fine block energies:**
`∫_0^{Kh} R_N² ≤ 2h (1−q)^{−2} Σ r_k² + 2 Σ c_k`. -/
theorem integral_sq_causalResponse_le_inputs (N : ℕ) {h : ℝ} (hh : 0 < h) {K : ℕ}
    (hK : K * h ≤ cutoff N) :
    (∫ t in (0 : ℝ)..(K * h), causalResponse N t ^ 2) ≤
      2 * h * ((1 - Real.exp (-h / 2))⁻¹ ^ 2 * ∑ j ∈ Finset.range K, chainInput h j ^ 2) +
        2 * ∑ k ∈ Finset.range K, blockEnergy N h k :=
  (integral_sq_causalResponse_le_chain N hh.le K).trans
    (add_le_add (mul_le_mul_of_nonneg_left (sum_chainState_sq_le N hh hK) (by positivity)) le_rfl)

/-- **Conversely the block discrepancies are controlled by the window energy and the fine energies:**
`(h e^{−h}/8) Σ_{k<K} r_k² ≤ ∫_0^{(K+1)h} R_N² + Σ_{k≤K} c_k`. -/
theorem sum_chainInput_sq_le_integral (N : ℕ) {h : ℝ} (hh : 0 ≤ h) {K : ℕ}
    (hK : K * h ≤ cutoff N) :
    h * Real.exp (-h) / 8 * ∑ k ∈ Finset.range K, chainInput h k ^ 2 ≤
      (∫ t in (0 : ℝ)..((K + 1 : ℕ) * h), causalResponse N t ^ 2) +
        ∑ k ∈ Finset.range (K + 1), blockEnergy N h k := by
  have h1 := sum_chainInput_sq_le N hh hK
  have h2 := chain_le_integral_sq_causalResponse N hh (K + 1)
  have h3 : 0 ≤ h * Real.exp (-h) / 8 := by positivity
  have h4 := mul_le_mul_of_nonneg_left h1 h3
  linarith

/-! ## The dyadic ladder -/

theorem exp_neg_half_log_two : Real.exp (-Real.log 2 / 2) = (Real.sqrt 2)⁻¹ := by
  have := exp_neg_half_log_eq (n := 2) (by norm_num)
  simpa using this

theorem exp_nat_mul_log_two (k : ℕ) : Real.exp (k * Real.log 2) = 2 ^ k := by
  rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]

/-- **The dyadic chain input:** `r_k = 2^{−(k+1)/2} (ψ(2^{k+1}) − ψ(2^k) − 2^k − log 2)`. -/
theorem chainInput_log_two (k : ℕ) :
    chainInput (Real.log 2) k =
      (Real.sqrt 2)⁻¹ ^ (k + 1) *
        ((Chebyshev.psi (2 ^ (k + 1)) - Chebyshev.psi (2 ^ k)) - 2 ^ k - Real.log 2) := by
  unfold chainInput blockResponse
  have e1 : Real.exp (-(((k : ℝ) + 1) * Real.log 2) / 2) = (Real.sqrt 2)⁻¹ ^ (k + 1) := by
    rw [← exp_neg_half_log_two, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have e2 : Real.exp (((k : ℝ) + 1) * Real.log 2) = 2 ^ (k + 1) := by
    rw [← exp_nat_mul_log_two]; push_cast; ring_nf
  have e3 : Real.exp ((k : ℝ) * Real.log 2) = 2 ^ k := exp_nat_mul_log_two k
  rw [e1, e2, e3]
  congr 1
  ring

theorem dyadic_ratio : Real.exp (-Real.log 2 / 2) = (Real.sqrt 2)⁻¹ := exp_neg_half_log_two

theorem exp_neg_log_two : Real.exp (-Real.log 2) = 1 / 2 := by
  rw [Real.exp_neg, Real.exp_log (by norm_num)]; ring

/-- **The dyadic coarse–fine law:** with `K log 2 ≤ L`,
`∫_0^{K log 2} R_N² ≤ 2 log 2 (1 − 1/√2)^{−2} Σ_k r_k² + 2 Σ_k c_k`, where
`r_k = 2^{−(k+1)/2}(ψ(2^{k+1}) − ψ(2^k) − 2^k − log 2)`. -/
theorem integral_sq_causalResponse_le_dyadic (N : ℕ) {K : ℕ} (hK : K * Real.log 2 ≤ cutoff N) :
    (∫ t in (0 : ℝ)..(K * Real.log 2), causalResponse N t ^ 2) ≤
      2 * Real.log 2 * ((1 - (Real.sqrt 2)⁻¹)⁻¹ ^ 2 *
        ∑ j ∈ Finset.range K, ((Real.sqrt 2)⁻¹ ^ (j + 1) *
          ((Chebyshev.psi (2 ^ (j + 1)) - Chebyshev.psi (2 ^ j)) - 2 ^ j - Real.log 2)) ^ 2) +
        2 * ∑ k ∈ Finset.range K, blockEnergy N (Real.log 2) k := by
  have := integral_sq_causalResponse_le_inputs N (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hK
  rw [dyadic_ratio] at this
  refine this.trans (le_of_eq ?_)
  congr 3
  exact Finset.sum_congr rfl fun j _ => by rw [chainInput_log_two]

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
