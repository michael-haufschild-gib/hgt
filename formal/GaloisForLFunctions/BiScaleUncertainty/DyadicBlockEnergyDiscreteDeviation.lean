import GaloisForLFunctions.BiScaleUncertainty.GaugeDualNormAndDivisorSampledResponse

/-!
# The fine block energy is the discrete deviation of the integer Chebyshev error

On the dyadic block `[X, 2X)` the block response of the renewal chain is, on the Nyquist cell of
the integer `n`,

`blockResponse (log X) t = e^{−t/2} ((E(n) − E(X) + n) − e^t) − e^{−t/2}(t − log X)`,  `E(n) = ψ(n) − n`,

so the fine block energy `c_k = ∫_{block} blockResponse²` is, up to constants and `O(1)`, the
normalized discrete deviation sum `X^{−2} Σ_{n ∈ [X,2X)} (E(n) − E(X))²`:

`D_X/(16 X²) − 2 ≤ c_k ≤ 4 D_X / X² + 10`,  `D_X = Σ_{n=X}^{2X−1} (E(n) − E(X))²`.

The dyadic chain input is likewise discrete, `r_k = 2^{−(k+1)/2}(E(2^{k+1}) − E(2^k) − log 2)`, so the
window Laplace energy up to scale `2^K` is bounded by purely discrete dyadic statistics of the
integer Chebyshev error: the coarse block jumps `E(2^{k+1}) − E(2^k)` and the fine in-block
deviations `E(n) − E(2^k)`.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators CompactlySupported Real

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section
set_option autoImplicit false

/-! ## The block response as a function of the raw Chebyshev error -/

theorem blockResponse_eq (a t : ℝ) :
    blockResponse a t = Real.exp (-t / 2) * (logError t - logError a - (t - a)) := by
  unfold blockResponse logError; ring

theorem measurable_blockResponse (a : ℝ) : Measurable (blockResponse a) := by
  have : blockResponse a = fun t => Real.exp (-t / 2) * (logError t - logError a - (t - a)) :=
    funext (blockResponse_eq a)
  rw [this]
  exact (Real.measurable_exp.comp (measurable_id.neg.div_const 2)).mul
    ((measurable_logError.sub measurable_const).sub (measurable_id.sub_const a))

theorem abs_blockResponse_le {a u v t : ℝ} (hu : u ≤ t) (htv : t ≤ v) :
    |blockResponse a t| ≤ Real.exp (|u| / 2) *
      ((Chebyshev.psi (Real.exp v) + Real.exp v) + (Chebyshev.psi (Real.exp a) + Real.exp a) +
        (|u| + |v| + |a|)) := by
  rw [blockResponse_eq, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : Real.exp (-t / 2) ≤ Real.exp (|u| / 2) :=
    Real.exp_le_exp.2 (by linarith [neg_abs_le u])
  have h2 : |logError t| ≤ Chebyshev.psi (Real.exp v) + Real.exp v := abs_logError_le htv
  have h3 : |logError a| ≤ Chebyshev.psi (Real.exp a) + Real.exp a := abs_logError_le le_rfl
  have ht : |t| ≤ |u| + |v| :=
    abs_le.2 ⟨by linarith [neg_abs_le u, abs_nonneg v], by linarith [le_abs_self v, abs_nonneg u]⟩
  have h4 : |t - a| ≤ |u| + |v| + |a| := (abs_sub _ _).trans (by linarith)
  have h5 : |logError t - logError a - (t - a)| ≤ |logError t| + |logError a| + |t - a| :=
    (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
  exact mul_le_mul h1 (by linarith) (abs_nonneg _) (Real.exp_pos _).le

theorem intervalIntegrable_blockResponse_sq (a u v : ℝ) :
    IntervalIntegrable (fun t => blockResponse a t ^ 2) volume u v := by
  wlog huv : u ≤ v generalizing u v
  · exact (this v u (le_of_not_le huv)).symm
  rw [intervalIntegrable_iff, uIoc_of_le huv]
  refine Measure.integrableOn_of_bounded (M := (Real.exp (|u| / 2) *
      ((Chebyshev.psi (Real.exp v) + Real.exp v) + (Chebyshev.psi (Real.exp a) + Real.exp a) +
        (|u| + |v| + |a|))) ^ 2)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    ((measurable_blockResponse a).pow_const 2).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun t ht => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_blockResponse_le ht.1.le ht.2) 2

/-- The fine block energy is the integral of the squared block response. -/
theorem blockEnergy_eq_integral_blockResponse_sq (N : ℕ) {h : ℝ} (hh : 0 ≤ h) {k : ℕ}
    (hk : (k + 1) * h ≤ cutoff N) :
    blockEnergy N h k = ∫ t in (k * h)..((k + 1) * h), blockResponse (k * h) t ^ 2 := by
  unfold blockEnergy
  refine intervalIntegral.integral_congr fun t ht => ?_
  have hkh : 0 ≤ (k : ℝ) * h := by positivity
  have hle : (k : ℝ) * h ≤ (k + 1) * h := by nlinarith
  rw [uIcc_of_le hle] at ht
  show (causalResponse N t - Real.exp (-(t - k * h) / 2) * chainState N h k) ^ 2 =
    blockResponse (k * h) t ^ 2
  rw [causalResponse_renewal N hkh ht.1 (ht.2.trans hk)]
  unfold chainState
  ring

/-! ## The integer Chebyshev error and the block deviation sum -/

/-- The integer Chebyshev error `E(n) = ψ(n) − n`. -/
def cellError (n : ℕ) : ℝ := Chebyshev.psi (n : ℝ) - n

/-- The deviation sum of the integer Chebyshev error over the dyadic block `[X, 2X)`. -/
def blockDeviationSum (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico X (2 * X), (cellError n - cellError X) ^ 2

theorem blockDeviationSum_nonneg (X : ℕ) : 0 ≤ blockDeviationSum X :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- On the cell of `n ∈ [X, 2X)` the block response is explicit in the integer errors. -/
theorem blockResponse_log_eq_on_cell {X n : ℕ} (hX : 1 ≤ X) (hn : X ≤ n) {t : ℝ}
    (ht : t ∈ Ico (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1))) :
    blockResponse (Real.log X) t =
      Real.exp (-t / 2) * ((cellError n - cellError X + n) - Real.exp t) -
        Real.exp (-t / 2) * (t - Real.log X) := by
  have hn1 : 1 ≤ n := hX.trans hn
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  rw [blockResponse_eq]
  unfold logError cellError
  rw [Chebyshev.psi_eq_psi_coe_floor (Real.exp t), floor_exp_eq_of_mem_cell hn1 ht,
    Real.exp_log hX0]
  ring

theorem integral_cell_exp_neg {n : ℕ} (hn : 1 ≤ n) :
    (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), Real.exp (-t)) =
      1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : ∀ t : ℝ, HasDerivAt (fun t => -Real.exp (-t)) (Real.exp (-t)) t := fun t => by
    have h0 : HasDerivAt (fun t : ℝ => -Real.exp (-t)) (-(Real.exp (-t) * -1)) t :=
      ((hasDerivAt_neg t).exp).neg
    exact h0.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _)]
  rw [Real.exp_neg, Real.exp_neg, Real.exp_log hn0, Real.exp_log (by positivity)]
  field_simp
  ring

/-- **Two-sided cell law for the block response.** -/
theorem integral_cell_blockResponse_sq_bounds {X n : ℕ} (hX : 1 ≤ X) (hn : X ≤ n)
    (hn2 : n + 1 ≤ 2 * X) :
    (cellError n - cellError X) ^ 2 / (16 * (X : ℝ) ^ 2) - 3 / (2 * (X : ℝ) ^ 2) ≤
      (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), blockResponse (Real.log X) t ^ 2) ∧
    (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), blockResponse (Real.log X) t ^ 2) ≤
      4 * (cellError n - cellError X) ^ 2 / (X : ℝ) ^ 2 + 10 / (X : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := hX.trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hXn : (X : ℝ) ≤ n := by exact_mod_cast hn
  have hn2' : (n : ℝ) + 1 ≤ 2 * X := by exact_mod_cast hn2
  have hle : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) := Real.log_le_log hn0 (by linarith)
  set c : ℝ := cellError n - cellError X + n with hc
  set d : ℝ := cellError n - cellError X with hd
  set A : ℝ → ℝ := fun t => Real.exp (-t / 2) * (c - Real.exp t) with hA
  set B : ℝ → ℝ := fun t => Real.exp (-t / 2) * (t - Real.log X) with hB
  have hAc : Continuous A := by rw [hA]; fun_prop
  have hBc : Continuous B := by rw [hB]; fun_prop
  -- the a.e. identity on the cell
  have hcell : (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), blockResponse (Real.log X) t ^ 2) =
      ∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), (A t - B t) ^ 2 := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ Real.log ((n : ℝ) + 1) := by
      rw [ae_iff]; simp
    filter_upwards [hne] with t ht hmem
    rw [uIoc_of_le hle] at hmem
    rw [blockResponse_log_eq_on_cell hX hn ⟨hmem.1.le, lt_of_le_of_ne hmem.2 ht⟩]
  -- the squared main part
  set p : ℝ := 1 / ((n : ℝ) * ((n : ℝ) + 1)) with hp
  have hp0 : 0 < p := by positivity
  have hA2 : (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), A t ^ 2) =
      (c - cellCenter n) ^ 2 * p + cellFloor n := by
    rw [hp, ← div_eq_mul_one_div, ← cell_energy_eq_center_sq_add_floor c hn1,
      ← integral_cell_gauge_sq c hn1]
    refine intervalIntegral.integral_congr fun t _ => ?_
    show (Real.exp (-t / 2) * (c - Real.exp t)) ^ 2 = Real.exp (-t) * (c - Real.exp t) ^ 2
    rw [mul_pow, sq (Real.exp (-t / 2)), ← Real.exp_add]
    congr 2; ring
  -- the squared transient
  have hB2 : (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), B t ^ 2) ≤ p := by
    rw [hp, ← integral_cell_exp_neg hn1]
    refine intervalIntegral.integral_mono_on hle (hBc.pow 2).intervalIntegrable
      ((Real.continuous_exp.comp continuous_neg).intervalIntegrable _ _) fun t ht => ?_
    show (Real.exp (-t / 2) * (t - Real.log X)) ^ 2 ≤ Real.exp (-t)
    have h1 : 0 ≤ t - Real.log X := by linarith [ht.1, Real.log_le_log hX0 hXn]
    have h2 : t - Real.log X ≤ 1 := by
      have hlog2 : Real.log (2 * (X : ℝ)) = Real.log 2 + Real.log X :=
        Real.log_mul (by norm_num) hX0.ne'
      have := ht.2.trans (Real.log_le_log (by positivity) hn2')
      have h22 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have he : Real.exp (-t / 2) ^ 2 = Real.exp (-t) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    rw [mul_pow, he]
    have : (t - Real.log X) ^ 2 ≤ 1 := by nlinarith
    nlinarith [Real.exp_pos (-t)]
  -- centre deviation
  have hm : |(n : ℝ) - cellCenter n| ≤ 1 := by
    rw [abs_le]; constructor <;> linarith [le_cellCenter hn1, cellCenter_le hn1]
  have he2 : ((n : ℝ) - cellCenter n) ^ 2 ≤ 1 := by
    rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) hm
  have hcm : c - cellCenter n = d + ((n : ℝ) - cellCenter n) := by rw [hc, hd]; ring
  have hsq_up : (c - cellCenter n) ^ 2 ≤ 2 * d ^ 2 + 2 := by
    rw [hcm]; nlinarith [sq_nonneg (d - ((n : ℝ) - cellCenter n))]
  have hsq_lo : d ^ 2 / 2 - 1 ≤ (c - cellCenter n) ^ 2 := by
    rw [hcm]; nlinarith [sq_nonneg (d + 2 * ((n : ℝ) - cellCenter n))]
  have hfloor0 : 0 ≤ cellFloor n := cellFloor_nonneg hn1
  have hfloor : cellFloor n ≤ 2 * p := by
    rw [hp]; have := cellFloor_le hn1; linarith [show 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) by ring]
  -- cell size comparisons
  have hpq : p ≤ 1 / (X : ℝ) ^ 2 := by
    rw [hp]; exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by nlinarith)
  have hqp : 1 / (4 * (X : ℝ) ^ 2) ≤ p := by
    rw [hp]; exact div_le_div_of_nonneg_left zero_le_one (by positivity) (by nlinarith)
  -- the two integral comparisons
  have hABi : IntervalIntegrable (fun t => (A t - B t) ^ 2) volume
      (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1)) := ((hAc.sub hBc).pow 2).intervalIntegrable _ _
  have hA2i : IntervalIntegrable (fun t => A t ^ 2) volume
      (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1)) := (hAc.pow 2).intervalIntegrable _ _
  have hB2i : IntervalIntegrable (fun t => B t ^ 2) volume
      (Real.log (n : ℝ)) (Real.log ((n : ℝ) + 1)) := (hBc.pow 2).intervalIntegrable _ _
  have hup : (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), (A t - B t) ^ 2) ≤
      2 * (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), A t ^ 2) +
        2 * ∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), B t ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hA2i.const_mul 2) (hB2i.const_mul 2)]
    exact intervalIntegral.integral_mono_on hle hABi ((hA2i.const_mul 2).add (hB2i.const_mul 2))
      fun t _ => by nlinarith [sq_nonneg (A t + B t)]
  have hlo : (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), A t ^ 2) / 2 -
      (∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), B t ^ 2) ≤
      ∫ t in Real.log (n : ℝ)..Real.log ((n : ℝ) + 1), (A t - B t) ^ 2 := by
    rw [div_eq_mul_one_div, mul_comm, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hA2i.const_mul _) hB2i]
    exact intervalIntegral.integral_mono_on hle ((hA2i.const_mul _).sub hB2i) hABi
      fun t _ => by nlinarith [sq_nonneg (A t - 2 * B t)]
  rw [hcell]
  have hd0 : 0 ≤ d ^ 2 := sq_nonneg d
  have h1 : (c - cellCenter n) ^ 2 * p ≤ (2 * d ^ 2 + 2) * p :=
    mul_le_mul_of_nonneg_right hsq_up hp0.le
  have h2 : (d ^ 2 / 2 - 1) * p ≤ (c - cellCenter n) ^ 2 * p :=
    mul_le_mul_of_nonneg_right hsq_lo hp0.le
  have h3 : d ^ 2 * p ≤ d ^ 2 * (1 / (X : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hpq hd0
  have h4 : d ^ 2 * (1 / (4 * (X : ℝ) ^ 2)) ≤ d ^ 2 * p := mul_le_mul_of_nonneg_left hqp hd0
  have e1 : 4 * d ^ 2 / (X : ℝ) ^ 2 + 10 / (X : ℝ) ^ 2 =
      4 * (d ^ 2 * (1 / (X : ℝ) ^ 2)) + 10 * (1 / (X : ℝ) ^ 2) := by ring
  have e2 : d ^ 2 / (16 * (X : ℝ) ^ 2) - 3 / (2 * (X : ℝ) ^ 2) =
      (d ^ 2 * (1 / (4 * (X : ℝ) ^ 2))) / 4 - 3 / 2 * (1 / (X : ℝ) ^ 2) := by ring
  constructor
  · rw [e2]; nlinarith [hlo, hA2, hB2, h2, h4, hpq, hfloor0]
  · rw [e1]; nlinarith [hup, hA2, hB2, h1, h3, hpq, hfloor]

/-! ## The dyadic block energy -/

theorem log_two_pow (k : ℕ) : (k : ℝ) * Real.log 2 = Real.log (((2 ^ k : ℕ) : ℝ)) := by
  push_cast
  rw [Real.log_pow]

theorem log_two_pow_succ (k : ℕ) :
    ((k : ℝ) + 1) * Real.log 2 = Real.log (((2 * 2 ^ k : ℕ) : ℝ)) := by
  push_cast
  rw [show (2 : ℝ) * 2 ^ k = 2 ^ (k + 1) by ring, Real.log_pow]
  push_cast; ring

/-- **The dyadic fine block energy is the normalized in-block deviation of `E(n) = ψ(n) − n`:**
`D_X/(16X²) − 2 ≤ c_k ≤ 4 D_X/X² + 10` with `X = 2^k`. -/
theorem blockEnergy_log_two_bounds (N : ℕ) {k : ℕ} (hk : (k + 1) * Real.log 2 ≤ cutoff N) :
    blockDeviationSum (2 ^ k) / (16 * (((2 ^ k : ℕ) : ℝ)) ^ 2) - 2 ≤
        blockEnergy N (Real.log 2) k ∧
      blockEnergy N (Real.log 2) k ≤
        4 * blockDeviationSum (2 ^ k) / (((2 ^ k : ℕ) : ℝ)) ^ 2 + 10 := by
  set X : ℕ := 2 ^ k with hXdef
  have hX : 1 ≤ X := Nat.one_le_two_pow
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hXr : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [blockEnergy_eq_integral_blockResponse_sq N hlog2 hk, log_two_pow k, log_two_pow_succ k]
  -- split the block into its Nyquist cells
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun t => blockResponse (Real.log (X : ℝ)) t ^ 2)
    (a := fun j : ℕ => Real.log ((X : ℝ) + j)) (n := X)
    (fun j _ => intervalIntegrable_blockResponse_sq _ _ _)
  have ha0 : Real.log ((X : ℝ) + ((0 : ℕ) : ℝ)) = Real.log (X : ℝ) := by simp
  have haX : Real.log ((X : ℝ) + (X : ℝ)) = Real.log (((2 * X : ℕ) : ℝ)) := by
    congr 1; push_cast; ring
  rw [ha0, haX] at hsum
  rw [← hsum]
  -- the deviation sum over the block
  have hdev : blockDeviationSum X =
      ∑ j ∈ Finset.range X, (cellError (X + j) - cellError X) ^ 2 := by
    unfold blockDeviationSum
    rw [Finset.sum_Ico_eq_sum_range, show 2 * X - X = X by omega]
  -- per-cell bounds
  have hcell : ∀ j ∈ Finset.range X,
      (cellError (X + j) - cellError X) ^ 2 / (16 * (X : ℝ) ^ 2) - 3 / (2 * (X : ℝ) ^ 2) ≤
        (∫ t in Real.log ((X : ℝ) + j)..Real.log ((X : ℝ) + (j + 1 : ℕ)),
          blockResponse (Real.log (X : ℝ)) t ^ 2) ∧
      (∫ t in Real.log ((X : ℝ) + j)..Real.log ((X : ℝ) + (j + 1 : ℕ)),
          blockResponse (Real.log (X : ℝ)) t ^ 2) ≤
        4 * (cellError (X + j) - cellError X) ^ 2 / (X : ℝ) ^ 2 + 10 / (X : ℝ) ^ 2 := by
    intro j hj
    have hjX : j < X := Finset.mem_range.mp hj
    have h := integral_cell_blockResponse_sq_bounds hX (Nat.le_add_right X j)
      (show X + j + 1 ≤ 2 * X by omega)
    have e1 : ((X + j : ℕ) : ℝ) = (X : ℝ) + j := by push_cast; ring
    have e2 : ((X + j : ℕ) : ℝ) + 1 = (X : ℝ) + ((j + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [e1, e2] at h
    exact h
  constructor
  · -- lower bound
    have hs := Finset.sum_le_sum fun j hj => (hcell j hj).1
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_div, ← hdev] at hs
    have hX2 : (X : ℝ) * (3 / (2 * (X : ℝ) ^ 2)) ≤ 2 := by
      rw [show (X : ℝ) * (3 / (2 * (X : ℝ) ^ 2)) = 3 / (2 * X) by field_simp; ring]
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  · -- upper bound
    have hs := Finset.sum_le_sum fun j hj => (hcell j hj).2
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.sum_div, ← Finset.mul_sum, ← hdev] at hs
    have hX2 : (X : ℝ) * (10 / (X : ℝ) ^ 2) ≤ 10 := by
      rw [show (X : ℝ) * (10 / (X : ℝ) ^ 2) = 10 / X by field_simp; ring]
      rw [div_le_iff₀ hX0]; nlinarith
    linarith

/-! ## The dyadic chain input in integer-error form -/

theorem chainInput_log_two_eq_cellError (k : ℕ) :
    chainInput (Real.log 2) k =
      (Real.sqrt 2)⁻¹ ^ (k + 1) * (cellError (2 ^ (k + 1)) - cellError (2 ^ k) - Real.log 2) := by
  rw [chainInput_log_two]
  unfold cellError
  push_cast
  congr 1
  ring

/-- **The window Laplace energy is bounded by discrete dyadic statistics of `E(n) = ψ(n) − n`:**
the coarse jumps `E(2^{k+1}) − E(2^k)` and the fine deviations `E(n) − E(2^k)`. -/
theorem integral_sq_causalResponse_le_discrete (N : ℕ) {K : ℕ}
    (hK : K * Real.log 2 ≤ cutoff N) :
    (∫ t in (0 : ℝ)..(K * Real.log 2), causalResponse N t ^ 2) ≤
      2 * Real.log 2 * ((1 - (Real.sqrt 2)⁻¹)⁻¹ ^ 2 *
        ∑ j ∈ Finset.range K, ((Real.sqrt 2)⁻¹ ^ (j + 1) *
          (cellError (2 ^ (j + 1)) - cellError (2 ^ j) - Real.log 2)) ^ 2) +
        2 * ∑ k ∈ Finset.range K,
          (4 * blockDeviationSum (2 ^ k) / (((2 ^ k : ℕ) : ℝ)) ^ 2 + 10) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h1 := integral_sq_causalResponse_le_inputs N hlog2 hK
  rw [dyadic_ratio] at h1
  refine h1.trans (add_le_add (le_of_eq ?_) ?_)
  · congr 2
    exact Finset.sum_congr rfl fun j _ => by rw [chainInput_log_two_eq_cellError]
  · refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk => ?_) (by norm_num)
    have hkK : k + 1 ≤ K := Finset.mem_range.mp hk
    have hk' : ((k : ℝ) + 1) * Real.log 2 ≤ cutoff N := by
      have : ((k + 1 : ℕ) : ℝ) * Real.log 2 ≤ (K : ℝ) * Real.log 2 :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hkK) hlog2.le
      push_cast at this
      linarith
    exact (blockEnergy_log_two_bounds N hk').2

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
