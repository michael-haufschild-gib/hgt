import GaloisForLFunctions.RHTower.JitteredCellWeilHoeffding
import GaloisForLFunctions.RHTower.LebesgueAtomArchimedeanWeilDensity

/-!
# A discrete Weil-positive system for the archimedean datum of `ζ`

Let `N = 2^26`.  Cut `[1, ∞)` into the cells `[(N+k)/N, (N+k+1)/N)` and place in the `k`-th cell
one atom of mass `1/N` at `x_k = (N+k+u_k)/N`, `u_k ∈ [0, 1]`.  Together with the negative atom
`e^{1/20000} δ_{e^{1/10000}}` of the Lebesgue-minus-atom system, this discrete measure has Weil
function `Φ(s) = ½ψ(s/2+1) − ½ log π + e^{1/20000} e^{−s/10000} − F(s)` with
`F(s) = Σ_k ∫_{cell k} (x_k^{−s} − x^{−s}) dx`, holomorphic on `Re s > 0`.  On the critical line
`Re F(1/2 + it) = cellSum N u t` (`sum_range_cellTerm_eq` exhibits the finite sums as atoms minus
Lebesgue measure on `[1, 1 + K/N)`), so its Weil density is `2 (archDensity t − cellSum N u t)`.

`exists_cellSum_lt_archDensity`: **some configuration `u` makes the density positive at every
height.**  The proof is probabilistic, with the `u_k` independent and uniform:
* for `|t| ≤ 2^15` the deterministic bound `|cellSum| ≤ 1/256 < 1/200 ≤ archDensity`;
* for `2^b ≤ |t| < 2^{b+1}`, `b ≥ 15`, a net of spacing `2^{−(4b+34)}`, the truncation to
  `2^{2b+14}` cells (tail `≤ 2^{−17}`), the Lipschitz bound of the truncated sum (`≤ 1/32` on a
  net step), and Hoeffding's inequality at each net point with variance proxy
  `≤ 4(b+5)/N`, against the level `½(b−1) log 2 − 9/5 ≤ archDensity − 1/5`;
* the union bound over all blocks and net points is at most `1/2 < 1`.

The atoms of different cells are independent and each has mean the Lebesgue measure of its cell,
so the fluctuation of `cellSum` at height `t` has variance about `(1/(2N)) log t`, far below the
archimedean ceiling `½ log t`.
-/

open MeasureTheory ProbabilityTheory Set Real

noncomputable section

namespace RHTower
namespace RandomCellWeil

/-- Half the Weil density of the Lebesgue-minus-atom system at height `t`. -/
def archDensity (t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Complex.digamma (((5 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I)).re
    - (1 / 2 : ℝ) * Real.log Real.pi + Real.cos (t / 10000)

theorem archDensity_ge (t : ℝ) : 1 / 200 ≤ archDensity t := lebesgueAtomWeilDensity_ge t

/-- For `|t| > 4800`, `archDensity t ≥ ½ log(|t|/2) − 8/5`. -/
theorem archDensity_ge_log {t : ℝ} (ht : 4800 < |t|) :
    (1 / 2 : ℝ) * Real.log (|t| / 2) - 8 / 5 ≤ archDensity t := by
  set z : ℂ := ((5 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I with hz
  have hre : z.re = 5 / 4 := by simp [hz]
  have him : z.im = t / 2 := by simp [hz]
  have hnorm : |t| / 2 ≤ ‖z‖ := by
    have h1 := Complex.abs_im_le_norm z
    rw [him, abs_div, abs_two] at h1
    exact h1
  have h2400 : 2400 ≤ ‖z‖ := by linarith
  have hasym := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos
    (z := z) (by rw [hre]; norm_num) (by linarith)
  have hlowre : Real.log ‖z‖ - 3 / ‖z‖ ≤ (Complex.digamma z).re := by
    have h := Complex.abs_re_le_norm (Complex.digamma z - Complex.log z)
    rw [Complex.sub_re, Complex.log_re] at h
    have := abs_le.mp (h.trans hasym)
    linarith [this.1]
  have hlogz : Real.log (|t| / 2) ≤ Real.log ‖z‖ := Real.log_le_log (by linarith) hnorm
  have h3 : 3 / ‖z‖ ≤ 3 / 2400 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2400
  have hpi := log_pi_lt_twentythree_twentieths
  have hcos := Real.neg_one_le_cos (t / 10000)
  unfold archDensity
  rw [← hz]
  nlinarith

/-- The finite cell sums are atoms of mass `1/N` minus Lebesgue measure on `[1, 1 + K/N)`. -/
theorem sum_range_cellTerm_eq {N : ℕ} (hN : 1 ≤ N) (u : ℕ → ℝ) (t : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range K, cellTerm N k (u k) t
      = (N : ℝ)⁻¹ * ∑ k ∈ Finset.range K, wave t (cellLeft N k + u k / N)
        - ∫ x in (1 : ℝ)..cellLeft N K, wave t x := by
  have hadj : ∀ k < K, IntervalIntegrable (wave t) volume (cellLeft N k) (cellLeft N (k + 1)) := by
    intro k _
    have h := intervalIntegrable_wave hN t k
    rwa [cellLeft_add_inv hN k] at h
  have hstep : ∀ k, cellLeft N k + (N : ℝ)⁻¹ = cellLeft N (k + 1) := by
    intro k
    rw [cellLeft_add_inv hN k, cellLeft]
    push_cast
    ring
  have hint := intervalIntegral.sum_integral_adjacent_intervals (f := wave t) (μ := volume)
    (a := cellLeft N) (n := K) hadj
  have h0 : cellLeft N 0 = 1 := by
    unfold cellLeft
    have : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp [this]
  rw [h0] at hint
  simp only [cellTerm, Finset.sum_sub_distrib, ← Finset.mul_sum, hstep]
  rw [hint]

/-! ### The parameters -/

/-- The number of cells per unit length. -/
irreducible_def jitterN : ℕ := 2 ^ 26

theorem jitterN_cast : (jitterN : ℝ) = 2 ^ 26 := by rw [jitterN_def]; push_cast; ring

theorem two_le_jitterN : 2 ≤ jitterN := by rw [jitterN_def]; norm_num

theorem one_le_jitterN : 1 ≤ jitterN := le_trans (by norm_num) two_le_jitterN

theorem sqrt_jitterN : Real.sqrt (jitterN : ℝ) = 2 ^ 13 := by
  rw [jitterN_cast, show (2 : ℝ) ^ 26 = (2 ^ 13) ^ 2 by norm_num, Real.sqrt_sq (by positivity)]

/-- Net spacing in the block `[2^b, 2^{b+1}]`. -/
def netStep (b : ℕ) : ℝ := ((2 : ℝ) ^ (4 * b + 34))⁻¹

/-- Number of net steps in the block `[2^b, 2^{b+1}]`. -/
irreducible_def netCount (b : ℕ) : ℕ := 2 ^ (5 * b + 34)

/-- The net points of the block `[2^b, 2^{b+1}]`. -/
def netPoint (b i : ℕ) : ℝ := 2 ^ b + i * netStep b

/-- Number of cells kept at heights in `[2^b, 2^{b+1}]`. -/
irreducible_def truncLen (b : ℕ) : ℕ := 2 ^ (2 * b + 14)

/-- Cells below this index use the amplitude bound, the others the mean-value bound. -/
irreducible_def splitLen (b : ℕ) : ℕ := jitterN * 2 ^ (b + 2)

/-- The level tested by Hoeffding's inequality in the block `[2^b, 2^{b+1}]`. -/
def level (b : ℕ) : ℝ := (1 / 2 : ℝ) * ((b : ℝ) - 1) * Real.log 2 - 9 / 5

/-- The bound for the `k`-th cell term at heights in `[2^b, 2^{b+1}]`. -/
def radius (b k : ℕ) : ℝ :=
  if k < splitLen b then 2 * (jitterN : ℝ)⁻¹ / Real.sqrt (cellLeft jitterN k)
  else (2 : ℝ) ^ (b + 2) / Real.sqrt jitterN * invPow ((jitterN + k : ℕ) : ℝ)

theorem netStep_pos (b : ℕ) : 0 < netStep b := by unfold netStep; positivity

theorem netCount_mul_netStep (b : ℕ) : (netCount b : ℝ) * netStep b = 2 ^ b := by
  rw [netCount_def]
  unfold netStep
  push_cast
  rw [show 5 * b + 34 = b + (4 * b + 34) by ring, pow_add]
  field_simp

theorem netPoint_mem {b i : ℕ} (hi : i ≤ netCount b) :
    2 ^ b ≤ netPoint b i ∧ netPoint b i ≤ 2 ^ (b + 1) := by
  unfold netPoint
  have hs := netStep_pos b
  have hle : (i : ℝ) * netStep b ≤ 2 ^ b := by
    rw [← netCount_mul_netStep b]
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hi) hs.le
  constructor
  · have : 0 ≤ (i : ℝ) * netStep b := by positivity
    linarith
  · rw [pow_succ]
    linarith

theorem abs_netPoint_add_half_le {b i : ℕ} (hi : i ≤ netCount b) :
    |netPoint b i| + 1 / 2 ≤ 2 ^ (b + 2) := by
  obtain ⟨h1, h2⟩ := netPoint_mem hi
  have hpos : 0 ≤ netPoint b i := le_trans (by positivity) h1
  rw [abs_of_nonneg hpos]
  have : (1 : ℝ) ≤ 2 ^ (b + 1) := one_le_pow₀ (by norm_num)
  rw [show b + 2 = (b + 1) + 1 by ring, pow_succ]
  linarith

theorem radius_nonneg (b k : ℕ) : 0 ≤ radius b k := by
  unfold radius
  split_ifs
  · positivity
  · exact mul_nonneg (by positivity) (invPow_nonneg (Nat.cast_nonneg _))

theorem abs_cellTerm_le_radius {b i : ℕ} (hi : i ≤ netCount b) (k : ℕ) {v : ℝ}
    (hv : v ∈ Icc (0 : ℝ) 1) :
    |cellTerm jitterN k v (netPoint b i)| ≤ radius b k := by
  have hN := one_le_jitterN
  unfold radius
  split_ifs
  · exact abs_cellTerm_le_osc hN k hv _
  · refine (abs_cellTerm_le_invPow hN k hv _).trans ?_
    apply mul_le_mul_of_nonneg_right _ (invPow_nonneg (Nat.cast_nonneg _))
    exact div_le_div_of_nonneg_right (abs_netPoint_add_half_le hi) (Real.sqrt_nonneg _)


/-! ### The variance proxy -/

theorem splitLen_le_truncLen {b : ℕ} (hb : 15 ≤ b) : splitLen b ≤ truncLen b := by
  rw [splitLen_def, truncLen_def, jitterN_def, ← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem splitLen_cast (b : ℕ) : (splitLen b : ℝ) = 2 ^ (b + 28) := by
  rw [splitLen_def, jitterN_def, ← pow_add]
  push_cast
  ring_nf

/-- `log((N + splitLen b − 1)/(N − 1)) ≤ b + 4`. -/
theorem log_split_ratio_le (b : ℕ) :
    Real.log ((((jitterN + splitLen b : ℕ) : ℝ) - 1) / ((jitterN : ℝ) - 1)) ≤ b + 4 := by
  have hN := jitterN_cast
  have hS := splitLen_cast b
  have hNS : ((jitterN + splitLen b : ℕ) : ℝ) = 2 ^ 26 + 2 ^ (b + 28) := by push_cast; rw [hN, hS]
  rw [hNS, hN]
  have hden : (0 : ℝ) < 2 ^ 26 - 1 := by norm_num
  have hnum : (0 : ℝ) < 2 ^ 26 + 2 ^ (b + 28) - 1 := by
    have : (0 : ℝ) < 2 ^ (b + 28) := by positivity
    linarith [show (1 : ℝ) ≤ 2 ^ 26 by norm_num]
  have hratio : (2 ^ 26 + 2 ^ (b + 28) - 1 : ℝ) / (2 ^ 26 - 1) ≤ 2 ^ (b + 4) := by
    rw [div_le_iff₀ hden]
    have h28 : (2 : ℝ) ^ (b + 28) = 2 ^ (b + 4) * 2 ^ 24 := by rw [← pow_add]
    have h4 : (2 : ℝ) ^ 4 ≤ 2 ^ (b + 4) := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [h28]
    norm_num at h4 ⊢
    nlinarith
  calc Real.log ((2 ^ 26 + 2 ^ (b + 28) - 1 : ℝ) / (2 ^ 26 - 1))
      ≤ Real.log (2 ^ (b + 4)) := Real.log_le_log (div_pos hnum hden) hratio
    _ = (b + 4 : ℕ) * Real.log 2 := by rw [Real.log_pow]
    _ ≤ (b + 4 : ℕ) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        have := Real.log_two_lt_d9
        linarith
    _ = b + 4 := by push_cast; ring

/-- `invPow M · 2/√(M − 1) ≤ 2/(M − 1)²` for `M ≥ 2`. -/
theorem invPow_mul_two_div_sqrt_le {M : ℝ} (hM : 2 ≤ M) :
    invPow M * (2 / Real.sqrt (M - 1)) ≤ 2 / (M - 1) ^ 2 := by
  have hm1 : 0 < M - 1 := by linarith
  have hs : 0 < Real.sqrt (M - 1) := Real.sqrt_pos.mpr hm1
  have hsq : Real.sqrt (M - 1) ^ 2 = M - 1 := Real.sq_sqrt hm1.le
  have hinv : invPow M ≤ 1 / ((M - 1) * Real.sqrt (M - 1)) := by
    unfold invPow
    apply one_div_le_one_div_of_le (mul_pos hm1 hs)
    exact mul_le_mul (by linarith) (Real.sqrt_le_sqrt (by linarith)) hs.le (by linarith)
  calc invPow M * (2 / Real.sqrt (M - 1))
      ≤ 1 / ((M - 1) * Real.sqrt (M - 1)) * (2 / Real.sqrt (M - 1)) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)
    _ = 2 / ((M - 1) * Real.sqrt (M - 1) * Real.sqrt (M - 1)) := by field_simp
    _ = 2 / (M - 1) ^ 2 := by rw [mul_assoc, Real.mul_self_sqrt hm1.le, sq]

/-- **Variance proxy.** `Σ_{k < truncLen b} radius b k ² ≤ 4(b + 5)/N` for `b ≥ 15`. -/
theorem sum_radius_sq_le {b : ℕ} (hb : 15 ≤ b) :
    ∑ k ∈ Finset.range (truncLen b), radius b k ^ 2 ≤ 4 * ((b : ℝ) + 5) / jitterN := by
  have hN2 := two_le_jitterN
  have hNpos : (0 : ℝ) < jitterN := by rw [jitterN_cast]; norm_num
  rw [← Finset.sum_range_add_sum_Ico _ (splitLen_le_truncLen hb)]
  -- the oscillatory cells
  have hosc : ∑ k ∈ Finset.range (splitLen b), radius b k ^ 2
      ≤ 4 * (jitterN : ℝ)⁻¹ * (b + 4) := by
    have heq : ∑ k ∈ Finset.range (splitLen b), radius b k ^ 2
        = ∑ k ∈ Finset.range (splitLen b), (2 * (jitterN : ℝ)⁻¹ / Real.sqrt (cellLeft jitterN k)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [radius, if_pos (Finset.mem_range.mp hk)]
    rw [heq]
    refine (sum_osc_sq_le hN2 (splitLen b)).trans ?_
    exact mul_le_mul_of_nonneg_left (log_split_ratio_le b) (by positivity)
  -- the smooth cells
  have hsmooth : ∑ k ∈ Finset.Ico (splitLen b) (truncLen b), radius b k ^ 2
      ≤ (jitterN : ℝ)⁻¹ := by
    have heq : ∑ k ∈ Finset.Ico (splitLen b) (truncLen b), radius b k ^ 2
        = ((2 : ℝ) ^ (b + 2) / Real.sqrt jitterN) ^ 2
          * ∑ k ∈ Finset.range (truncLen b - splitLen b),
              invPow (((jitterN + splitLen b) + k : ℕ) : ℝ) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [radius, if_neg (by omega), mul_pow, show jitterN + (splitLen b + k)
        = (jitterN + splitLen b) + k by ring]
    rw [heq]
    set M := jitterN + splitLen b with hM
    have hM2 : 2 ≤ M := by omega
    have hsum := sum_Ico_invPow_sq_le M hM2 (truncLen b - splitLen b)
    have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM2
    have hbd := invPow_mul_two_div_sqrt_le hMr
    have hcoef : ((2 : ℝ) ^ (b + 2) / Real.sqrt jitterN) ^ 2 = 2 ^ (2 * b + 4) / jitterN := by
      rw [div_pow, Real.sq_sqrt hNpos.le, ← pow_mul]
      ring_nf
    have hMbig : (2 : ℝ) ^ (b + 28) ≤ (M : ℝ) - 1 := by
      rw [hM]
      push_cast
      rw [splitLen_cast, jitterN_cast]
      have : (1 : ℝ) ≤ 2 ^ 26 := by norm_num
      linarith
    have hsq_big : (2 : ℝ) ^ (2 * b + 56) ≤ ((M : ℝ) - 1) ^ 2 := by
      have h := pow_le_pow_left₀ (by positivity) hMbig 2
      rwa [← pow_mul, show (b + 28) * 2 = 2 * b + 56 by ring] at h
    rw [hcoef]
    calc 2 ^ (2 * b + 4) / (jitterN : ℝ)
          * ∑ k ∈ Finset.range (truncLen b - splitLen b), invPow ((M + k : ℕ) : ℝ) ^ 2
        ≤ 2 ^ (2 * b + 4) / (jitterN : ℝ) * (2 / ((M : ℝ) - 1) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact hsum.trans hbd
      _ ≤ 2 ^ (2 * b + 4) / (jitterN : ℝ) * (2 / 2 ^ (2 * b + 56)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq_big
      _ = (jitterN : ℝ)⁻¹ * 2 ^ (2 * b + 5) / 2 ^ (2 * b + 56) := by
          rw [show 2 * b + 5 = (2 * b + 4) + 1 by ring, pow_succ]
          field_simp
          ring
      _ ≤ (jitterN : ℝ)⁻¹ := by
          rw [div_le_iff₀ (by positivity)]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc _ ≤ 4 * (jitterN : ℝ)⁻¹ * (b + 4) + (jitterN : ℝ)⁻¹ := add_le_add hosc hsmooth
    _ ≤ 4 * ((b : ℝ) + 5) / jitterN := by
        rw [div_eq_mul_inv]
        have : (0 : ℝ) < (jitterN : ℝ)⁻¹ := by positivity
        nlinarith

theorem radius_zero_pos (b : ℕ) : 0 < radius b 0 := by
  have h0 : 0 < splitLen b := by rw [splitLen_def, jitterN_def]; positivity
  rw [radius, if_pos h0]
  have := cellLeft_pos (N := jitterN) one_le_jitterN 0
  have : (0 : ℝ) < jitterN := by rw [jitterN_cast]; norm_num
  positivity

theorem sum_radius_sq_pos (b : ℕ) :
    0 < ∑ k ∈ Finset.range (truncLen b), radius b k ^ 2 := by
  have hT : 0 < truncLen b := by rw [truncLen_def]; positivity
  calc (0 : ℝ) < radius b 0 ^ 2 := by have := radius_zero_pos b; positivity
    _ ≤ ∑ k ∈ Finset.range (truncLen b), radius b k ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (radius b k)) (Finset.mem_range.mpr hT)

/-! ### The level and the Hoeffding exponent -/

theorem level_ge {b : ℕ} (hb : 15 ≤ b) : (b : ℝ) / 5 ≤ level b := by
  unfold level
  have hl := Real.log_two_gt_d9
  have hb' : (15 : ℝ) ≤ b := by exact_mod_cast hb
  nlinarith

theorem level_nonneg {b : ℕ} (hb : 15 ≤ b) : 0 ≤ level b :=
  le_trans (by positivity) (level_ge hb)

/-- The Hoeffding bound at level `level b` is at most `exp(−2^17 b)`. -/
theorem hoeffding_exponent_le {b : ℕ} (hb : 15 ≤ b) :
    Real.exp (-(level b) ^ 2 / (2 * ∑ k ∈ Finset.range (truncLen b), radius b k ^ 2))
      ≤ Real.exp (-(2 ^ 17 * (b : ℝ))) := by
  apply Real.exp_le_exp.mpr
  have hV := sum_radius_sq_le hb
  have hVpos := sum_radius_sq_pos b
  have hlev := level_ge hb
  have hb' : (15 : ℝ) ≤ b := by exact_mod_cast hb
  set V := ∑ k ∈ Finset.range (truncLen b), radius b k ^ 2
  have hN := jitterN_cast
  rw [hN] at hV
  -- level² / (2V) ≥ (b/5)² · 2^26 / (8 (b+5)) ≥ 2^17 b
  have hlev2 : ((b : ℝ) / 5) ^ 2 ≤ level b ^ 2 := pow_le_pow_left₀ (by positivity) hlev 2
  rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  calc 2 ^ 17 * (b : ℝ) * (2 * V) ≤ 2 ^ 17 * (b : ℝ) * (2 * (4 * ((b : ℝ) + 5) / 2 ^ 26)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ ≤ ((b : ℝ) / 5) ^ 2 := by
        rw [div_pow]
        field_simp
        nlinarith
    _ ≤ level b ^ 2 := hlev2


/-! ### Deterministic estimates -/

/-- The truncated sum over `K` cells is `2K²`-Lipschitz in the height. -/
theorem abs_sum_range_cellTerm_sub_le {N : ℕ} (hN : 1 ≤ N) {u : ℕ → ℝ}
    (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) (K : ℕ) (t t' : ℝ) :
    |∑ k ∈ Finset.range K, cellTerm N k (u k) t - ∑ k ∈ Finset.range K, cellTerm N k (u k) t'|
      ≤ 2 * (K : ℝ) ^ 2 * |t - t'| := by
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm : ∀ k ∈ Finset.range K,
      |cellTerm N k (u k) t - cellTerm N k (u k) t'| ≤ 2 * K * |t - t'| := by
    intro k hk
    have hkK : (k : ℝ) + 1 ≤ K := by exact_mod_cast Finset.mem_range.mp hk
    refine (abs_cellTerm_sub_param_le hN k (hu k) t t').trans ?_
    have hlog : Real.log (cellLeft N k + (N : ℝ)⁻¹) ≤ K := by
      rw [cellLeft_add_inv hN k]
      have hpos : (0 : ℝ) < ((N + k + 1 : ℕ) : ℝ) / N := by positivity
      refine (Real.log_le_sub_one_of_pos hpos).trans ?_
      have heq : ((N + k + 1 : ℕ) : ℝ) / N - 1 = ((k : ℝ) + 1) / N := by
        push_cast
        field_simp
        ring
      rw [heq]
      refine le_trans ?_ hkK
      exact div_le_self (by positivity) (by exact_mod_cast hN)
    have hlog0 : 0 ≤ Real.log (cellLeft N k + (N : ℝ)⁻¹) :=
      Real.log_nonneg (by linarith [one_le_cellLeft hN k, inv_N_pos hN])
    have hinv := inv_N_le_one hN
    calc 2 * (N : ℝ)⁻¹ * Real.log (cellLeft N k + (N : ℝ)⁻¹) * |t - t'|
        ≤ 2 * 1 * K * |t - t'| := by
          apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
          apply mul_le_mul (mul_le_mul_of_nonneg_left hinv (by norm_num)) hlog hlog0 (by norm_num)
      _ = 2 * K * |t - t'| := by ring
  calc ∑ k ∈ Finset.range K, |cellTerm N k (u k) t - cellTerm N k (u k) t'|
      ≤ ∑ k ∈ Finset.range K, 2 * (K : ℝ) * |t - t'| := Finset.sum_le_sum hterm
    _ = 2 * (K : ℝ) ^ 2 * |t - t'| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem truncLen_cast (b : ℕ) : (truncLen b : ℝ) = 2 ^ (2 * b + 14) := by
  rw [truncLen_def]; push_cast; ring

/-- Tail beyond `truncLen b` cells at heights `0 ≤ τ < 2^{b+1}`: at most `2^{−17}`. -/
theorem abs_cellSum_sub_trunc_le {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) {b : ℕ} {τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ : τ < 2 ^ (b + 1)) :
    |cellSum jitterN u τ - ∑ k ∈ Finset.range (truncLen b), cellTerm jitterN k (u k) τ|
      ≤ 1 / 2 ^ 17 := by
  refine (abs_cellSum_sub_sum_range_le two_le_jitterN hu τ (truncLen b)).trans ?_
  rw [sqrt_jitterN, abs_of_nonneg hτ0]
  have hK : (2 : ℝ) ^ (b + 7) ≤ Real.sqrt (((jitterN + truncLen b : ℕ) : ℝ) - 1) := by
    have hsq : Real.sqrt (((2 : ℝ) ^ (b + 7)) ^ 2) = 2 ^ (b + 7) := Real.sqrt_sq (by positivity)
    rw [← hsq]
    apply Real.sqrt_le_sqrt
    push_cast
    rw [jitterN_cast, truncLen_cast, ← pow_mul, show (b + 7) * 2 = 2 * b + 14 by ring]
    have : (1 : ℝ) ≤ 2 ^ 26 := by norm_num
    linarith
  have hnum : τ + 1 / 2 ≤ 2 ^ (b + 2) := by
    have : (1 : ℝ) ≤ 2 ^ (b + 1) := one_le_pow₀ (by norm_num)
    rw [show b + 2 = (b + 1) + 1 by ring, pow_succ]
    linarith
  calc (τ + 1 / 2) / 2 ^ 13 * (2 / Real.sqrt (((jitterN + truncLen b : ℕ) : ℝ) - 1))
      ≤ 2 ^ (b + 2) / 2 ^ 13 * (2 / 2 ^ (b + 7)) := by
        apply mul_le_mul (div_le_div_of_nonneg_right hnum (by positivity))
          (div_le_div_of_nonneg_left (by norm_num) (by positivity) hK) (by positivity)
          (by positivity)
    _ = 1 / 2 ^ 17 := by
        rw [pow_add, pow_add]
        field_simp

/-- Every height in `[2^b, 2^{b+1})` is within one net step of a net point. -/
theorem exists_netPoint_near {b : ℕ} {τ : ℝ} (h1 : 2 ^ b ≤ τ) (h2 : τ < 2 ^ (b + 1)) :
    ∃ i ≤ netCount b, |τ - netPoint b i| ≤ netStep b := by
  have hs := netStep_pos b
  set x := (τ - 2 ^ b) / netStep b with hx
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hs.le
  have hxlt : x < netCount b := by
    rw [hx, div_lt_iff₀ hs, netCount_mul_netStep, pow_succ] at *
    linarith
  refine ⟨⌊x⌋₊, ?_, ?_⟩
  · have := Nat.floor_le_floor (R := ℝ) hxlt.le
    rwa [Nat.floor_natCast] at this
  · have hfl := Nat.floor_le hx0
    have hlt := Nat.lt_floor_add_one x
    have hτ : τ = 2 ^ b + x * netStep b := by rw [hx]; field_simp; ring
    unfold netPoint
    rw [hτ, abs_le]
    constructor
    · nlinarith
    · nlinarith

/-- **Block estimate.** If the truncated sums stay below `level b` at every net point of the
block, then `cellSum` stays below `½ log(τ/2) − 8/5 − 1/10` on the whole block. -/
theorem cellSum_lt_of_block {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) {b : ℕ}
    (hgood : ∀ i ≤ netCount b,
      ∑ k ∈ Finset.range (truncLen b), cellTerm jitterN k (u k) (netPoint b i) < level b)
    {τ : ℝ} (h1 : 2 ^ b ≤ τ) (h2 : τ < 2 ^ (b + 1)) :
    cellSum jitterN u τ < (1 / 2 : ℝ) * Real.log (τ / 2) - 8 / 5 - 1 / 10 := by
  obtain ⟨i, hi, hnear⟩ := exists_netPoint_near h1 h2
  have hτ0 : 0 ≤ τ := le_trans (by positivity) h1
  have htail := abs_cellSum_sub_trunc_le hu hτ0 h2
  have hlip := abs_sum_range_cellTerm_sub_le one_le_jitterN hu (truncLen b) τ (netPoint b i)
  have hlipval : 2 * (truncLen b : ℝ) ^ 2 * |τ - netPoint b i| ≤ 1 / 32 := by
    calc 2 * (truncLen b : ℝ) ^ 2 * |τ - netPoint b i| ≤ 2 * (truncLen b : ℝ) ^ 2 * netStep b :=
          mul_le_mul_of_nonneg_left hnear (by positivity)
      _ = 1 / 32 := by
          rw [truncLen_cast, netStep, ← pow_mul]
          rw [show (2 * b + 14) * 2 = 4 * b + 28 by ring,
            show 4 * b + 34 = (4 * b + 28) + 6 by ring, pow_add]
          field_simp
          ring
  have hg := hgood i hi
  have hlog : ((b : ℝ) - 1) * Real.log 2 ≤ Real.log (τ / 2) := by
    have hpos : (0 : ℝ) < 2 ^ b / 2 := by positivity
    have hmono : Real.log (2 ^ b / 2) ≤ Real.log (τ / 2) :=
      Real.log_le_log hpos (div_le_div_of_nonneg_right h1 (by norm_num))
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow] at hmono
    linarith
  have habs1 := abs_le.mp htail
  have habs2 := abs_le.mp (hlip.trans hlipval)
  unfold level at hg
  nlinarith [habs1.2, habs2.1, habs2.2]

/-- Small heights: `|cellSum| ≤ 1/256` for `|t| ≤ 2^15`. -/
theorem abs_cellSum_le_small {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) {t : ℝ}
    (ht : |t| ≤ 2 ^ 15) : |cellSum jitterN u t| ≤ 1 / 256 := by
  refine (abs_cellSum_le two_le_jitterN hu t).trans ?_
  rw [sqrt_jitterN]
  have hN1 : (2 : ℝ) ^ 12 ≤ Real.sqrt ((jitterN : ℝ) - 1) := by
    have hsq : Real.sqrt (((2 : ℝ) ^ 12) ^ 2) = 2 ^ 12 := Real.sqrt_sq (by positivity)
    rw [← hsq]
    apply Real.sqrt_le_sqrt
    rw [jitterN_cast]
    norm_num
  have h1 : 2 / Real.sqrt ((jitterN : ℝ) - 1) ≤ 2 / 2 ^ 12 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hN1
  have h2 : (|t| + 1 / 2) / 2 ^ 13 ≤ (2 ^ 15 + 1 / 2) / 2 ^ 13 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  calc (|t| + 1 / 2) / 2 ^ 13 * (2 / Real.sqrt ((jitterN : ℝ) - 1))
      ≤ (2 ^ 15 + 1 / 2) / 2 ^ 13 * (2 / 2 ^ 12) :=
        mul_le_mul h2 h1 (by positivity) (by positivity)
    _ ≤ 1 / 256 := by norm_num


/-! ### The union bound -/

/-- The event that the truncated sum reaches `level b` at the `i`-th net point of block `b`. -/
def badEvent (b i : ℕ) : Set (ℕ → ℝ) :=
  {u | level b ≤ ∑ k ∈ Finset.range (truncLen b), cellTerm jitterN k (u k) (netPoint b i)}

theorem measure_badEvent_le {b i : ℕ} (hb : 15 ≤ b) (hi : i ≤ netCount b) :
    cellLaw (badEvent b i) ≤ ENNReal.ofReal (Real.exp (-(2 ^ 17 * (b : ℝ)))) := by
  have h := measureReal_sum_cellTerm_ge_le one_le_jitterN (netPoint b i) (truncLen b) (radius b)
    (radius_nonneg b) (fun k _ v hv => abs_cellTerm_le_radius hi k hv) (level_nonneg hb)
  rw [← ofReal_measureReal (μ := cellLaw) (s := badEvent b i)]
  exact ENNReal.ofReal_le_ofReal (h.trans (hoeffding_exponent_le hb))

/-- `(2^{5b+34} + 1) e^{−2^17 b} ≤ (1/2)^{b−13}` for `b = j + 15`. -/
theorem netCount_mul_exp_le (j : ℕ) :
    ((netCount (j + 15) : ℝ) + 1) * Real.exp (-(2 ^ 17 * ((j + 15 : ℕ) : ℝ)))
      ≤ (1 / 2 : ℝ) ^ (j + 2) := by
  set b := j + 15 with hbdef
  have hcount : (netCount b : ℝ) + 1 ≤ Real.exp (5 * (b : ℝ) + 35) := by
    rw [netCount_def]
    push_cast
    have h2 : (2 : ℝ) ^ (5 * b + 34) + 1 ≤ 2 ^ (5 * b + 35) := by
      have hs : (2 : ℝ) ^ (5 * b + 35) = 2 ^ (5 * b + 34) * 2 := by
        rw [show 5 * b + 35 = (5 * b + 34) + 1 by ring, pow_succ]
      have : (1 : ℝ) ≤ 2 ^ (5 * b + 34) := one_le_pow₀ (by norm_num)
      rw [hs]
      linarith
    refine h2.trans ?_
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    calc (2 : ℝ) ^ (5 * b + 35) ≤ Real.exp 1 ^ (5 * b + 35) :=
          pow_le_pow_left₀ (by norm_num) he _
      _ = Real.exp (5 * (b : ℝ) + 35) := by
          rw [← Real.exp_nat_mul]
          push_cast
          ring_nf
  have hhalf : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg]
    have : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    linarith
  calc ((netCount b : ℝ) + 1) * Real.exp (-(2 ^ 17 * (b : ℝ)))
      ≤ Real.exp (5 * (b : ℝ) + 35) * Real.exp (-(2 ^ 17 * (b : ℝ))) :=
        mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le
    _ = Real.exp (5 * (b : ℝ) + 35 - 2 ^ 17 * (b : ℝ)) := by
        rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-1 * ((j + 2 : ℕ) : ℝ)) := by
        apply Real.exp_le_exp.mpr
        rw [hbdef]
        push_cast
        nlinarith
    _ = Real.exp (-1) ^ (j + 2) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ (1 / 2 : ℝ) ^ (j + 2) := pow_le_pow_left₀ (Real.exp_pos _).le hhalf _

theorem measure_block_le (j : ℕ) :
    cellLaw (⋃ i ∈ Finset.range (netCount (j + 15) + 1), badEvent (j + 15) i)
      ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 2)) := by
  refine (measure_biUnion_finset_le _ _).trans ?_
  calc ∑ i ∈ Finset.range (netCount (j + 15) + 1), cellLaw (badEvent (j + 15) i)
      ≤ ∑ i ∈ Finset.range (netCount (j + 15) + 1),
          ENNReal.ofReal (Real.exp (-(2 ^ 17 * ((j + 15 : ℕ) : ℝ)))) := by
        apply Finset.sum_le_sum
        intro i hi
        exact measure_badEvent_le (by omega) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    _ = ENNReal.ofReal (((netCount (j + 15) : ℝ) + 1)
          * Real.exp (-(2 ^ 17 * ((j + 15 : ℕ) : ℝ)))) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [ENNReal.ofReal_add (by positivity) (by norm_num)]
        simp
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 2)) := ENNReal.ofReal_le_ofReal (netCount_mul_exp_le j)

theorem tsum_half_pow_add_two : ∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 2) = 1 / 2 := by
  have h : (fun j : ℕ => (1 / 2 : ℝ) ^ (j + 2)) = fun j => (1 / 4 : ℝ) * (1 / 2) ^ j := by
    funext j; rw [pow_add]; ring
  rw [h, tsum_mul_left, tsum_geometric_two]
  norm_num

/-- The set of configurations violating some requirement. -/
def badSet : Set (ℕ → ℝ) :=
  {u | ∃ k, u k ∉ Icc (0 : ℝ) 1} ∪
    ⋃ j : ℕ, ⋃ i ∈ Finset.range (netCount (j + 15) + 1), badEvent (j + 15) i

theorem measure_badSet_le : cellLaw badSet ≤ ENNReal.ofReal (1 / 2) := by
  refine (measure_union_le _ _).trans ?_
  rw [measure_exists_not_mem_Icc, zero_add]
  refine (measure_iUnion_le _).trans ?_
  calc ∑' j : ℕ, cellLaw (⋃ i ∈ Finset.range (netCount (j + 15) + 1), badEvent (j + 15) i)
      ≤ ∑' j : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ (j + 2)) := ENNReal.tsum_le_tsum measure_block_le
    _ = ENNReal.ofReal (∑' j : ℕ, (1 / 2 : ℝ) ^ (j + 2)) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)]
        exact (summable_geometric_two).mul_left (1 / 4) |>.congr (fun j => by rw [pow_add]; ring)
    _ = ENNReal.ofReal (1 / 2) := by rw [tsum_half_pow_add_two]

theorem exists_not_mem_badSet : ∃ u, u ∉ badSet := by
  by_contra h
  push Not at h
  have huniv : badSet = Set.univ := Set.eq_univ_of_forall h
  have := measure_badSet_le
  rw [huniv, measure_univ] at this
  have h2 : ENNReal.ofReal (1 / 2) < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr (by norm_num)
  exact absurd this (not_le.mpr h2)

/-! ### The theorem -/

/-- **A discrete Weil-positive system for the archimedean datum of `ζ`.**  There are positions
`u_k ∈ [0, 1]` such that the system with one atom of mass `1/N` at `(N + k + u_k)/N` in every cell
(`N = 2^26`), minus the atom `e^{1/20000} δ_{e^{1/10000}}`, has positive Weil density
`2 (archDensity t − cellSum N u t)` at every height `t`. -/
theorem exists_cellSum_lt_archDensity :
    ∃ u : ℕ → ℝ, (∀ k, u k ∈ Icc (0 : ℝ) 1) ∧ ∀ t : ℝ, cellSum jitterN u t < archDensity t := by
  obtain ⟨u, hu⟩ := exists_not_mem_badSet
  simp only [badSet, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists,
    Finset.mem_range] at hu
  obtain ⟨hmem, hgood⟩ := hu
  have hmem' : ∀ k, u k ∈ Icc (0 : ℝ) 1 := fun k => by
    have := hmem k
    simpa using this
  refine ⟨u, hmem', fun t => ?_⟩
  rcases le_or_gt |t| (2 ^ 15) with hsmall | hlarge
  · have h1 := abs_cellSum_le_small hmem' hsmall
    have h2 := archDensity_ge t
    have := (abs_le.mp h1).2
    linarith
  · set τ := |t| with hτ
    have hτ1 : (1 : ℝ) ≤ τ := by
      have : (1 : ℝ) ≤ 2 ^ 15 := by norm_num
      linarith
    obtain ⟨b, hb1, hb2⟩ := exists_nat_pow_near hτ1 (by norm_num : (1 : ℝ) < 2)
    have hb : 15 ≤ b := by
      by_contra hlt
      push Not at hlt
      have : (2 : ℝ) ^ (b + 1) ≤ 2 ^ 15 := pow_le_pow_right₀ (by norm_num) (by omega)
      linarith
    obtain ⟨j, rfl⟩ : ∃ j, b = j + 15 := ⟨b - 15, by omega⟩
    have hblock : ∀ i ≤ netCount (j + 15),
        ∑ k ∈ Finset.range (truncLen (j + 15)), cellTerm jitterN k (u k) (netPoint (j + 15) i)
          < level (j + 15) := by
      intro i hi
      have := hgood j i (Nat.lt_succ_of_le hi)
      simpa [badEvent] using this
    have hcs := cellSum_lt_of_block hmem' hblock hb1 hb2
    have hsym : cellSum jitterN u t = cellSum jitterN u τ := by
      rcases le_or_gt 0 t with ht0 | ht0
      · rw [hτ, abs_of_nonneg ht0]
      · rw [hτ, abs_of_neg ht0, cellSum_neg_param]
    have harch := archDensity_ge_log (t := t) (by
      have : (4800 : ℝ) < 2 ^ 15 := by norm_num
      linarith)
    rw [hsym]
    rw [← hτ] at harch
    linarith

end RandomCellWeil
end RHTower
