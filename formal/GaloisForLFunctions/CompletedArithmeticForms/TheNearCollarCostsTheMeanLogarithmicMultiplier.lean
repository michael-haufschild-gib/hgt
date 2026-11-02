import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.RamanujanAutocorrelationWeights
import GaloisForLFunctions.RHTower.Sieve.AbelInequality
import GaloisForLFunctions.HTGeometry.PrimeSieveHarmonicInclusionExclusion
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandPrimeAndCenterBounds
import GaloisForLFunctions.SignedArithmeticHodgeTheory.OneArithmeticRemainderControlsEveryRamanujanResidual

/-!
# The near collar costs the mean logarithmic multiplier

The archimedean collar kernel `1/(2|n − j|)`, `0 < |n − j| ≤ D`, acts on a `k`-periodic function
through the multiplier `M_D(θ) = Σ_{h ≤ D} cos(hθ)/h`. Splitting the sum at `1/|sin(θ/2)|`
(harmonic head, Abel tail) gives `|M_D(θ)| ≤ 3 + log(1/|sin(θ/2)|)`
(`abs_logKernelMultiplier_le`). At the primitive frequencies `2πr/k` this is at most
`3 + log(k/(2 min(r, k−r)))`, and summing the squares over `r` costs `130 k`
(`sum_primitiveRoots_normSq_collar_le`). By the primitive-root Gram identity
`ramanujanAutocorrelationWeight = φ(k)⁻¹ Σ_{z} |Σ_i a_i z^i|²`, the collar autocorrelation weight
of conductor `k ≥ 2` is at most `130 k/φ(k)` (`ramanujanAutocorrelationWeight_collar_le`).

Complete periods of a pair of smoothed Ramanujan sums are diagonal
(`sum_range_smoothedRamanujan_mul`), so over any range the smoothed packet costs its diagonal
plus one period per pair (`sum_range_smoothed_packet_sq_le`). Applied to the near-collar rows
of a packet without the pole conductor this replaces the Schur cost `(20(1 + log R))²/log N` by
`130/log N · Σ b_m² m/φ(m)` up to a boundary term of relative size `R⁶/N`
(`sum_collarRowNear_sq_le_sharp`).
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The truncated logarithmic kernel multiplier `M_D(θ) = Σ_{h=1}^{D} cos(hθ)/h`. -/
def logKernelMultiplier (D : ℕ) (θ : ℝ) : ℝ :=
  ∑ h ∈ Icc 1 D, Real.cos ((h : ℝ) * θ) / h

/-- `2 sin(θ/2) Σ_{μ=1}^{n} cos(μθ) = sin(nθ + θ/2) − sin(θ/2)`. -/
theorem two_sin_half_mul_sum_Icc_cos (θ : ℝ) (n : ℕ) :
    2 * Real.sin (θ / 2) * ∑ μ ∈ Icc 1 n, Real.cos ((μ : ℝ) * θ) =
      Real.sin ((n : ℝ) * θ + θ / 2) - Real.sin (θ / 2) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ k + 1), mul_add, ih]
    have hps : Real.sin (((k : ℝ) + 1) * θ + θ / 2) - Real.sin ((k : ℝ) * θ + θ / 2) =
        2 * Real.sin (θ / 2) * Real.cos (((k : ℝ) + 1) * θ) := by
      rw [Real.sin_sub_sin,
        show ((((k : ℝ) + 1) * θ + θ / 2) - ((k : ℝ) * θ + θ / 2)) / 2 = θ / 2 by ring,
        show ((((k : ℝ) + 1) * θ + θ / 2) + ((k : ℝ) * θ + θ / 2)) / 2 = ((k : ℝ) + 1) * θ by ring]
    push_cast
    linear_combination -hps

/-- Cosine partial sums are bounded by `1/|sin(θ/2)|`. -/
theorem abs_sum_Icc_cos_le {θ : ℝ} (hs : Real.sin (θ / 2) ≠ 0) (n : ℕ) :
    |∑ μ ∈ Icc 1 n, Real.cos ((μ : ℝ) * θ)| ≤ 1 / |Real.sin (θ / 2)| := by
  have h := two_sin_half_mul_sum_Icc_cos θ n
  have hpos : 0 < |Real.sin (θ / 2)| := abs_pos.mpr hs
  rw [le_div_iff₀ hpos]
  have h2 : |Real.sin ((n : ℝ) * θ + θ / 2) - Real.sin (θ / 2)| ≤ 2 := by
    have := abs_sub (Real.sin ((n : ℝ) * θ + θ / 2)) (Real.sin (θ / 2))
    have := Real.abs_sin_le_one ((n : ℝ) * θ + θ / 2)
    have := Real.abs_sin_le_one (θ / 2)
    linarith
  rw [← h, abs_mul, abs_mul, abs_two] at h2
  nlinarith [abs_nonneg (∑ μ ∈ Icc 1 n, Real.cos ((μ : ℝ) * θ))]

private theorem sum_range_cos_shift (θ : ℝ) (H k : ℕ) :
    (∑ j ∈ range k, Real.cos (((H + 1 + j : ℕ) : ℝ) * θ)) =
      (∑ μ ∈ Icc 1 (H + k), Real.cos ((μ : ℝ) * θ)) -
        ∑ μ ∈ Icc 1 H, Real.cos ((μ : ℝ) * θ) := by
  have e1 : (Icc 1 (H + k) : Finset ℕ) = Ico 1 (H + 1 + k) := by
    ext x; simp only [mem_Icc, mem_Ico]; omega
  have e2 : (Icc 1 H : Finset ℕ) = Ico 1 (H + 1) := by
    ext x; simp only [mem_Icc, mem_Ico]; omega
  rw [e1, e2, ← sum_Ico_consecutive _ (by omega : 1 ≤ H + 1) (by omega : H + 1 ≤ H + 1 + k),
    add_sub_cancel_left, sum_Ico_eq_sum_range]
  simp only [add_tsub_cancel_left]

/-- **The logarithmic kernel multiplier.** `|Σ_{h ≤ D} cos(hθ)/h| ≤ 3 + log(1/|sin(θ/2)|)`:
the first `⌊1/|sin(θ/2)|⌋` terms cost a harmonic sum, the rest an Abel tail of size `2`. -/
theorem abs_logKernelMultiplier_le (D : ℕ) {θ : ℝ} (hs : Real.sin (θ / 2) ≠ 0) :
    |logKernelMultiplier D θ| ≤ 3 + Real.log (1 / |Real.sin (θ / 2)|) := by
  set s := |Real.sin (θ / 2)| with hsdef
  have hs0 : 0 < s := abs_pos.mpr hs
  have hs1 : s ≤ 1 := Real.abs_sin_le_one _
  have hinv1 : 1 ≤ 1 / s := by rw [le_div_iff₀ hs0]; linarith
  set H := ⌊1 / s⌋₊ with hHdef
  have hH1 : 1 ≤ H := Nat.le_floor (by exact_mod_cast hinv1)
  have hHle : (H : ℝ) ≤ 1 / s := Nat.floor_le (by positivity)
  have hHlt : 1 / s < (H : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlogH : Real.log H ≤ Real.log (1 / s) :=
    Real.log_le_log (by exact_mod_cast (show 0 < H by omega)) hHle
  -- head: at most the harmonic number `H`
  have hhead : ∀ n ≤ H, |∑ h ∈ Icc 1 n, Real.cos ((h : ℝ) * θ) / h| ≤ 1 + Real.log (1 / s) := by
    intro n hn
    calc |∑ h ∈ Icc 1 n, Real.cos ((h : ℝ) * θ) / h|
        ≤ ∑ h ∈ Icc 1 n, |Real.cos ((h : ℝ) * θ) / h| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ h ∈ Icc 1 H, (1 / (h : ℝ)) := by
          refine (sum_le_sum fun h hh => ?_).trans
            (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl hn) fun _ _ _ => by positivity)
          have hh0 : (0 : ℝ) < h := by exact_mod_cast (mem_Icc.mp hh).1
          rw [abs_div, abs_of_pos hh0, div_le_div_iff_of_pos_right hh0]
          exact Real.abs_cos_le_one _
      _ = harmonic H := by rw [← HTGeometry.sum_Icc_one_div_eq_harmonic]
      _ ≤ 1 + Real.log H := harmonic_le_one_add_log H
      _ ≤ 1 + Real.log (1 / s) := by linarith
  by_cases hDH : D ≤ H
  · unfold logKernelMultiplier
    have := hhead D hDH
    have := Real.log_nonneg hinv1
    linarith
  push Not at hDH
  -- split `Icc 1 D` at `H`
  have hsplit : (∑ h ∈ Icc 1 D, Real.cos ((h : ℝ) * θ) / h) =
      (∑ h ∈ Icc 1 H, Real.cos ((h : ℝ) * θ) / h) +
        ∑ j ∈ range (D - H), (1 / ((H + 1 + j : ℕ) : ℝ)) *
          Real.cos (((H + 1 + j : ℕ) : ℝ) * θ) := by
    have e1 : (Icc 1 D : Finset ℕ) = Ico 1 (D + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
    have e2 : (Icc 1 H : Finset ℕ) = Ico 1 (H + 1) := by ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [e1, e2, ← sum_Ico_consecutive _ (by omega : 1 ≤ H + 1) (by omega : H + 1 ≤ D + 1)]
    congr 1
    rw [sum_Ico_eq_sum_range, show D + 1 - (H + 1) = D - H by omega]
    refine sum_congr rfl fun j _ => ?_
    push_cast; ring
  -- tail: Abel's inequality with partial sums bounded by `2/s`
  have htail : |∑ j ∈ range (D - H), (1 / ((H + 1 + j : ℕ) : ℝ)) *
      Real.cos (((H + 1 + j : ℕ) : ℝ) * θ)| ≤ 2 := by
    have hB : ∀ k, |∑ j ∈ range k, Real.cos (((H + 1 + j : ℕ) : ℝ) * θ)| ≤ 2 / s := by
      intro k
      rw [sum_range_cos_shift]
      have h1 := abs_sum_Icc_cos_le hs (H + k)
      have h2 := abs_sum_Icc_cos_le hs H
      rw [← hsdef] at h1 h2
      have := abs_sub (∑ μ ∈ Icc 1 (H + k), Real.cos ((μ : ℝ) * θ))
        (∑ μ ∈ Icc 1 H, Real.cos ((μ : ℝ) * θ))
      calc _ ≤ _ := this
        _ ≤ 1 / s + 1 / s := add_le_add h1 h2
        _ = 2 / s := by ring
    have habel := RHTower.Sieve.abs_sum_mul_le_of_bounded_partial (D - H) hB
      (w := fun j => 1 / ((H + 1 + j : ℕ) : ℝ)) (fun _ => by positivity)
      (fun i => by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast; linarith)
    refine habel.trans ?_
    simp only [add_zero]
    rw [div_mul_div_comm, mul_one, div_le_iff₀ (by positivity)]
    push_cast
    have : 1 < s * ((H : ℝ) + 1) := by
      rw [div_lt_iff₀ hs0] at hHlt; linarith
    linarith
  unfold logKernelMultiplier
  rw [hsplit]
  have := hhead H le_rfl
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ (1 + Real.log (1 / s)) + 2 := add_le_add this htail
    _ = 3 + Real.log (1 / s) := by ring

/-! ### The collar kernel at primitive frequencies -/

/-- The near-collar source weights on `range (2D+1)`: `1/(2|i − D|)` off the centre `i = D`. -/
def collarSourceWeight (D i : ℕ) : ℝ :=
  if i = D then 0 else 1 / (2 * (Nat.dist i D : ℝ))

/-- At a unit frequency the collar source transform is a phase times the multiplier. -/
theorem sum_collarSourceWeight_mul_exp_pow (D : ℕ) (θ : ℝ) :
    (∑ i ∈ range (2 * D + 1), (collarSourceWeight D i : ℂ) *
        Complex.exp ((θ : ℂ) * Complex.I) ^ i) =
      Complex.exp ((θ : ℂ) * Complex.I) ^ D * (logKernelMultiplier D θ : ℂ) := by
  set z := Complex.exp ((θ : ℂ) * Complex.I) with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hzinv : z⁻¹ = Complex.exp ((-θ : ℝ) * Complex.I) := by
    rw [hz, ← Complex.exp_neg]; push_cast; ring_nf
  -- split `range (2D+1)` into `i < D`, `i = D`, `D < i`
  have hsplit : (∑ i ∈ range (2 * D + 1), (collarSourceWeight D i : ℂ) * z ^ i) =
      (∑ i ∈ range D, (collarSourceWeight D i : ℂ) * z ^ i) +
        ∑ h ∈ range D, (collarSourceWeight D (D + 1 + h) : ℂ) * z ^ (D + 1 + h) := by
    have e0 : (range (2 * D + 1) : Finset ℕ) = Ico 0 (2 * D + 1) := range_eq_Ico (2 * D + 1)
    rw [e0, ← sum_Ico_consecutive _ (Nat.zero_le D) (by omega : D ≤ 2 * D + 1),
      ← sum_Ico_consecutive _ (by omega : D ≤ D + 1) (by omega : D + 1 ≤ 2 * D + 1)]
    rw [show (Ico D (D + 1) : Finset ℕ) = {D} by ext x; simp only [mem_Ico, mem_singleton]; omega,
      sum_singleton, collarSourceWeight, if_pos rfl, ← range_eq_Ico D]
    simp only [Complex.ofReal_zero, zero_mul, zero_add]
    rw [sum_Ico_eq_sum_range, show 2 * D + 1 - (D + 1) = D by omega]
  have hlow : (∑ i ∈ range D, (collarSourceWeight D i : ℂ) * z ^ i) =
      ∑ h ∈ range D, ((1 / (2 * ((h : ℝ) + 1)) : ℝ) : ℂ) * (z ^ D * z⁻¹ ^ (h + 1)) := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun h hh => ?_
    have hh' := mem_range.mp hh
    have hne : D - 1 - h ≠ D := by omega
    have hdist : (Nat.dist (D - 1 - h) D : ℝ) = (h : ℝ) + 1 := by
      rw [Nat.dist_eq_sub_of_le (by omega), show D - (D - 1 - h) = h + 1 by omega]; push_cast; ring
    rw [collarSourceWeight, if_neg hne, hdist]
    congr 1
    rw [← mul_inv_cancel_right₀ (pow_ne_zero (h + 1) hz0) (z ^ (D - 1 - h)), ← pow_add,
      show D - 1 - h + (h + 1) = D by omega, inv_pow]
  have hhigh : (∑ h ∈ range D, (collarSourceWeight D (D + 1 + h) : ℂ) * z ^ (D + 1 + h)) =
      ∑ h ∈ range D, ((1 / (2 * ((h : ℝ) + 1)) : ℝ) : ℂ) * (z ^ D * z ^ (h + 1)) := by
    refine sum_congr rfl fun h _ => ?_
    have hne : D + 1 + h ≠ D := by omega
    have hdist : (Nat.dist (D + 1 + h) D : ℝ) = (h : ℝ) + 1 := by
      rw [Nat.dist_eq_sub_of_le_right (by omega), show D + 1 + h - D = h + 1 by omega]; push_cast; ring
    rw [collarSourceWeight, if_neg hne, hdist, ← pow_add, show D + (h + 1) = D + 1 + h by ring]
  rw [hsplit, hlow, hhigh, ← sum_add_distrib, logKernelMultiplier, Complex.ofReal_sum, mul_sum]
  rw [show (Icc 1 D : Finset ℕ) = (range D).map ⟨(· + 1), add_left_injective 1⟩ by
    ext x; simp only [mem_Icc, mem_map, mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro hx; exact ⟨x - 1, by omega, by omega⟩
    · rintro ⟨y, hy, rfl⟩; omega, sum_map]
  refine sum_congr rfl fun h _ => ?_
  simp only [Function.Embedding.coeFn_mk]
  have hcos : z ^ (h + 1) + z⁻¹ ^ (h + 1) = ((2 * Real.cos (((h + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ) := by
    rw [hz, hzinv, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  calc ((1 / (2 * ((h : ℝ) + 1)) : ℝ) : ℂ) * (z ^ D * z⁻¹ ^ (h + 1)) +
        ((1 / (2 * ((h : ℝ) + 1)) : ℝ) : ℂ) * (z ^ D * z ^ (h + 1))
      = z ^ D * (((1 / (2 * ((h : ℝ) + 1)) : ℝ) : ℂ) * (z ^ (h + 1) + z⁻¹ ^ (h + 1))) := by ring
    _ = _ := by
      rw [hcos]
      congr 1
      push_cast
      field_simp

/-! ### Summing the multiplier over primitive frequencies -/

private theorem sum_Icc_one_div_sqrt_le (k : ℕ) :
    (∑ r ∈ Icc 1 k, 1 / Real.sqrt r) ≤ 2 * Real.sqrt k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_Icc_succ_top (by omega)]
    push_cast
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    set s₁ := Real.sqrt ((k : ℝ) + 1) with hs₁
    set s₀ := Real.sqrt (k : ℝ) with hs₀
    have hs1 : 0 < s₁ := Real.sqrt_pos.mpr hk1
    have hsq1 : s₁ ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt hk1.le
    have hsq0 : s₀ ^ 2 = k := Real.sq_sqrt (Nat.cast_nonneg k)
    have h0 : 0 ≤ s₀ := Real.sqrt_nonneg _
    have key : 1 / s₁ ≤ 2 * (s₁ - s₀) := by
      rw [div_le_iff₀ hs1]
      nlinarith [sq_nonneg (s₁ - s₀)]
    linarith

private theorem log_le_two_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hs := Real.sqrt_pos.mpr hx0
  have h := Real.log_le_sub_one_of_pos hs
  rw [Real.log_sqrt hx0.le] at h
  linarith

private theorem log_sq_le_sixteen_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ^ 2 ≤ 16 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hq : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have h := Real.log_le_sub_one_of_pos hq
  rw [Real.log_rpow hx0] at h
  have hl0 := Real.log_nonneg hx
  have hlog : Real.log x ≤ 4 * x ^ (1 / 4 : ℝ) := by linarith
  have hsq : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, Real.sqrt_eq_rpow]; norm_num
  calc Real.log x ^ 2 ≤ (4 * x ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hl0 hlog 2
    _ = 16 * Real.sqrt x := by rw [mul_pow, hsq]; norm_num

/-- `Σ_{r ≤ k} (3 + log(k/r))² ≤ 65 k`. -/
theorem sum_Icc_three_add_log_sq_le (k : ℕ) :
    (∑ r ∈ Icc 1 k, (3 + Real.log ((k : ℝ) / r)) ^ 2) ≤ 65 * (k : ℝ) := by
  have hterm : ∀ r ∈ Icc 1 k, (3 + Real.log ((k : ℝ) / r)) ^ 2 ≤
      9 + 28 * (Real.sqrt k * (1 / Real.sqrt r)) := by
    intro r hr
    obtain ⟨hr1, hrk⟩ := mem_Icc.mp hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
    have hx : 1 ≤ (k : ℝ) / r := by
      rw [le_div_iff₀ hr0, one_mul]; exact_mod_cast hrk
    have h1 := log_le_two_sqrt hx
    have h2 := log_sq_le_sixteen_sqrt hx
    have hl0 := Real.log_nonneg hx
    have hsq : Real.sqrt ((k : ℝ) / r) = Real.sqrt k * (1 / Real.sqrt r) := by
      rw [Real.sqrt_div' _ hr0.le, div_eq_mul_one_div]
    rw [hsq] at h1 h2
    have hs0 : 0 ≤ Real.sqrt k * (1 / Real.sqrt r) := by positivity
    nlinarith
  calc (∑ r ∈ Icc 1 k, (3 + Real.log ((k : ℝ) / r)) ^ 2)
      ≤ ∑ r ∈ Icc 1 k, (9 + 28 * (Real.sqrt k * (1 / Real.sqrt r))) := sum_le_sum hterm
    _ = 9 * k + 28 * Real.sqrt k * ∑ r ∈ Icc 1 k, 1 / Real.sqrt r := by
        rw [sum_add_distrib, sum_const, Nat.card_Icc, ← mul_sum, ← mul_sum]
        simp only [nsmul_eq_mul, add_tsub_cancel_right]
        ring
    _ ≤ 9 * k + 28 * Real.sqrt k * (2 * Real.sqrt k) := by
        have := sum_Icc_one_div_sqrt_le k
        have : 0 ≤ 28 * Real.sqrt k := by positivity
        nlinarith
    _ = 65 * k := by
        rw [show 28 * Real.sqrt k * (2 * Real.sqrt k) = 56 * (Real.sqrt k) ^ 2 by ring,
          Real.sq_sqrt (Nat.cast_nonneg k)]
        ring

/-- At the primitive frequency `r/k` (`1 ≤ r < k`) the multiplier squared is at most
`(3 + log(k/(2 min(r, k−r))))²`. -/
theorem logKernelMultiplier_sq_le_of_frequency (D : ℕ) {k r : ℕ} (hr1 : 1 ≤ r) (hrk : r < k) :
    logKernelMultiplier D (2 * Real.pi * r / k) ^ 2 ≤
      (3 + Real.log ((k : ℝ) / (2 * (min r (k - r) : ℕ)))) ^ 2 := by
  set m := min r (k - r) with hm
  have hm1 : 1 ≤ m := le_min hr1 (by omega)
  have h2m : 2 * m ≤ k := by have := min_le_left r (k - r); have := min_le_right r (k - r); omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hθ : 2 * Real.pi * r / k / 2 = Real.pi * r / k := by ring
  -- `sin(π r/k) = sin(π m/k) ≥ 2m/k`
  have hsin_eq : Real.sin (Real.pi * r / k) = Real.sin (Real.pi * m / k) := by
    rcases min_choice r (k - r) with h | h
    · rw [hm, h]
    · rw [hm, h, Nat.cast_sub hrk.le,
        show Real.pi * ((k : ℝ) - r) / k = Real.pi - Real.pi * r / k by field_simp]
      exact (Real.sin_pi_sub _).symm
  have hlow : 2 * (m : ℝ) / k ≤ Real.sin (Real.pi * m / k) := by
    have hx0 : 0 ≤ Real.pi * m / k := by positivity
    have hx1 : Real.pi * m / k ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hk0 (by norm_num)]
      have : (2 * m : ℝ) ≤ k := by exact_mod_cast h2m
      nlinarith [Real.pi_pos]
    have := Real.mul_le_sin hx0 hx1
    calc 2 * (m : ℝ) / k = 2 / Real.pi * (Real.pi * m / k) := by field_simp
      _ ≤ _ := this
  have hpos : 0 < 2 * (m : ℝ) / k := by positivity
  have hsinpos : 0 < Real.sin (Real.pi * r / k) := hsin_eq ▸ hpos.trans_le hlow
  have hs : Real.sin (2 * Real.pi * r / k / 2) ≠ 0 := by rw [hθ]; exact hsinpos.ne'
  have hM := abs_logKernelMultiplier_le D hs
  rw [hθ, abs_of_pos hsinpos] at hM
  have hlog : Real.log (1 / Real.sin (Real.pi * r / k)) ≤ Real.log ((k : ℝ) / (2 * m)) := by
    apply Real.log_le_log (by positivity)
    rw [hsin_eq, div_le_div_iff₀ (hpos.trans_le hlow) (by positivity)]
    have := (div_le_iff₀ hk0).mp hlow
    linarith
  have hnn : 0 ≤ 3 + Real.log (1 / Real.sin (Real.pi * r / k)) := by
    have : 0 ≤ Real.log (1 / Real.sin (Real.pi * r / k)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ hsinpos, one_mul]; exact Real.sin_le_one _
    linarith
  have habs : |logKernelMultiplier D (2 * Real.pi * r / k)| ≤
      3 + Real.log ((k : ℝ) / (2 * m)) := by linarith
  have hp := pow_le_pow_left₀ (abs_nonneg _) habs 2
  rw [sq_abs] at hp
  exact hp

/-- `Σ_{1 ≤ r < k} (3 + log(k/(2 min(r, k−r))))² ≤ 130 k`. -/
theorem sum_Icc_frequency_bound_le (k : ℕ) :
    (∑ r ∈ Icc 1 (k - 1), (3 + Real.log ((k : ℝ) / (2 * (min r (k - r) : ℕ)))) ^ 2) ≤
      130 * (k : ℝ) := by
  have hterm : ∀ r ∈ Icc 1 (k - 1),
      (3 + Real.log ((k : ℝ) / (2 * (min r (k - r) : ℕ)))) ^ 2 ≤
        (3 + Real.log ((k : ℝ) / r)) ^ 2 + (3 + Real.log ((k : ℝ) / ((k - r : ℕ) : ℝ))) ^ 2 := by
    intro r hr
    obtain ⟨hr1, hrk⟩ := mem_Icc.mp hr
    set m := min r (k - r) with hm
    have hm1 : 1 ≤ m := le_min hr1 (by omega)
    have h2m : 2 * m ≤ k := by
      have := min_le_left r (k - r); have := min_le_right r (k - r); omega
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hA : 0 ≤ Real.log ((k : ℝ) / (2 * m)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity), one_mul]; exact_mod_cast h2m
    have hB : Real.log ((k : ℝ) / (2 * m)) ≤ Real.log ((k : ℝ) / m) :=
      Real.log_le_log (by positivity) (div_le_div_of_nonneg_left hk0.le hm0 (by linarith))
    have hsq : (3 + Real.log ((k : ℝ) / (2 * m))) ^ 2 ≤ (3 + Real.log ((k : ℝ) / m)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hr0 : 0 ≤ (3 + Real.log ((k : ℝ) / r)) ^ 2 := sq_nonneg _
    have hkr0 : 0 ≤ (3 + Real.log ((k : ℝ) / ((k - r : ℕ) : ℝ))) ^ 2 := sq_nonneg _
    rcases min_choice r (k - r) with h | h
    · have hmr : (m : ℝ) = r := by rw [hm, h]
      rw [hmr] at hsq ⊢; linarith
    · have hmr : (m : ℝ) = ((k - r : ℕ) : ℝ) := by rw [hm, h]
      rw [hmr] at hsq ⊢; linarith
  have hrefl : (∑ r ∈ Icc 1 (k - 1), (3 + Real.log ((k : ℝ) / ((k - r : ℕ) : ℝ))) ^ 2) =
      ∑ r ∈ Icc 1 (k - 1), (3 + Real.log ((k : ℝ) / r)) ^ 2 := by
    refine sum_nbij' (fun r => k - r) (fun r => k - r) ?_ ?_ ?_ ?_ ?_
    · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
    · intro r hr; simp only [Finset.mem_Icc] at hr ⊢; omega
    · intro r hr; simp only [Finset.mem_Icc] at hr; omega
    · intro r hr; simp only [Finset.mem_Icc] at hr; omega
    · intro r _; rfl
  have hsub : (∑ r ∈ Icc 1 (k - 1), (3 + Real.log ((k : ℝ) / r)) ^ 2) ≤
      ∑ r ∈ Icc 1 k, (3 + Real.log ((k : ℝ) / r)) ^ 2 :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (Nat.sub_le k 1))
      fun _ _ _ => sq_nonneg _
  calc _ ≤ ∑ r ∈ Icc 1 (k - 1), ((3 + Real.log ((k : ℝ) / r)) ^ 2 +
        (3 + Real.log ((k : ℝ) / ((k - r : ℕ) : ℝ))) ^ 2) := sum_le_sum hterm
    _ = 2 * ∑ r ∈ Icc 1 (k - 1), (3 + Real.log ((k : ℝ) / r)) ^ 2 := by
        rw [sum_add_distrib, hrefl]; ring
    _ ≤ 2 * (65 * (k : ℝ)) := by
        have := sum_Icc_three_add_log_sq_le k; linarith
    _ = 130 * (k : ℝ) := by ring

/-- **The collar kernel at primitive frequencies.** For `k ≥ 2`, summing the squared collar
transform over the primitive `k`-th roots of unity costs at most `130 k`. -/
theorem sum_primitiveRoots_normSq_collar_le {k : ℕ} (hk : 2 ≤ k) (D : ℕ) :
    (∑ z ∈ primitiveRoots k ℂ, Complex.normSq
      (∑ i ∈ range (2 * D + 1), (collarSourceWeight D i : ℂ) * z ^ i)) ≤ 130 * (k : ℝ) := by
  have hk0 : 0 < k := by omega
  have hkne : k ≠ 0 := by omega
  have hex : ∀ z ∈ primitiveRoots k ℂ, ∃ r, r < k ∧ r.Coprime k ∧
      Complex.exp (2 * Real.pi * Complex.I * (r / k)) = z := by
    intro z hz
    obtain ⟨r, hr, hcop, he⟩ := (Complex.isPrimitiveRoot_iff z k hkne).mp
      ((mem_primitiveRoots hk0).mp hz)
    exact ⟨r, hr, hcop, he⟩
  classical
  let rOf : ℂ → ℕ := fun z => if h : ∃ r, r < k ∧ r.Coprime k ∧
      Complex.exp (2 * Real.pi * Complex.I * (r / k)) = z then Classical.choose h else 0
  have hrOf : ∀ z ∈ primitiveRoots k ℂ, rOf z < k ∧ (rOf z).Coprime k ∧
      Complex.exp (2 * Real.pi * Complex.I * ((rOf z : ℕ) / k)) = z := by
    intro z hz
    have h := hex z hz
    simp only [rOf, dif_pos h]
    exact Classical.choose_spec h
  have hr1 : ∀ z ∈ primitiveRoots k ℂ, 1 ≤ rOf z := by
    intro z hz
    obtain ⟨-, hcop, -⟩ := hrOf z hz
    by_contra h0
    have : rOf z = 0 := by omega
    rw [this, Nat.coprime_zero_left] at hcop
    omega
  set g : ℕ → ℝ := fun r => (3 + Real.log ((k : ℝ) / (2 * (min r (k - r) : ℕ)))) ^ 2 with hg
  have hpoint : ∀ z ∈ primitiveRoots k ℂ, Complex.normSq
      (∑ i ∈ range (2 * D + 1), (collarSourceWeight D i : ℂ) * z ^ i) ≤ g (rOf z) := by
    intro z hz
    obtain ⟨hrk, -, he⟩ := hrOf z hz
    have h1 := hr1 z hz
    obtain ⟨r, hr⟩ : ∃ r, rOf z = r := ⟨_, rfl⟩
    rw [hr] at hrk he h1 ⊢
    have hzθ : z = Complex.exp (((2 * Real.pi * (r : ℕ) / k : ℝ) : ℂ) * Complex.I) := by
      rw [← he]; congr 1; push_cast; ring
    have hL : Complex.normSq (∑ i ∈ range (2 * D + 1), (collarSourceWeight D i : ℂ) * z ^ i) =
        logKernelMultiplier D (2 * Real.pi * r / k) ^ 2 := by
      rw [hzθ, sum_collarSourceWeight_mul_exp_pow, Complex.normSq_mul, Complex.normSq_ofReal,
        map_pow, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
      simp only [one_pow, one_mul, sq]
    rw [hL, hg]
    exact logKernelMultiplier_sq_le_of_frequency D h1 hrk
  have hinj : Set.InjOn rOf (primitiveRoots k ℂ) := by
    intro z hz z' hz' heq
    have h1 := (hrOf z hz).2.2
    have h2 := (hrOf z' hz').2.2
    rw [← h1, ← h2, heq]
  have hsub : (primitiveRoots k ℂ).image rOf ⊆ Icc 1 (k - 1) := by
    intro r hr
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hr
    exact mem_Icc.mpr ⟨hr1 z hz, by have := (hrOf z hz).1; omega⟩
  calc _ ≤ ∑ z ∈ primitiveRoots k ℂ, g (rOf z) := sum_le_sum hpoint
    _ = ∑ r ∈ (primitiveRoots k ℂ).image rOf, g r := (sum_image hinj).symm
    _ ≤ ∑ r ∈ Icc 1 (k - 1), g r :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ ≤ 130 * (k : ℝ) := sum_Icc_frequency_bound_le k

/-- **The collar autocorrelation weight is bounded by `130 k/φ(k)`** at every conductor `k ≥ 2`. -/
theorem ramanujanAutocorrelationWeight_collar_le {k : ℕ} (hk : 2 ≤ k) (D : ℕ) :
    SuccessorShellArithmetic.ramanujanAutocorrelationWeight (range (2 * D + 1))
      (collarSourceWeight D) k ≤ 130 * (k : ℝ) / k.totient := by
  rw [SuccessorShellArithmetic.ramanujanAutocorrelationWeight,
    SuccessorShellArithmetic.sum_ramanujanLagCoefficient_dist_eq_normSq (by omega)]
  exact div_le_div_of_nonneg_right (sum_primitiveRoots_normSq_collar_le hk D) (Nat.cast_nonneg _)

/-! ### Smoothed Ramanujan packets over an arbitrary range -/

open BezoutValuationIncidence SuccessorShellArithmetic

theorem ramanujanLagCoefficient_add_of_dvd {k M : ℕ} (hkM : k ∣ M) (n : ℕ) :
    ramanujanLagCoefficient k (n + M) = ramanujanLagCoefficient k n := by
  unfold ramanujanLagCoefficient
  refine sum_congr rfl fun d hd => ?_
  have hdM : d ∣ M := (Nat.dvd_of_mem_divisors hd).trans hkM
  have hiff : d ∣ n + M ↔ d ∣ n := Nat.dvd_add_left hdM
  by_cases h : d ∣ n
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]

theorem abs_ramanujanLagCoefficient_le_totient {k : ℕ} (hk : 0 < k) (n : ℕ) :
    |ramanujanLagCoefficient k n| ≤ k.totient := by
  have h := SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hk n
  rw [RenormalizedArithmeticPotentialTheory.normalizedRamanujanMode_eq_coefficient hk, abs_div,
    abs_of_pos (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hk)),
    div_le_iff₀ (Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr hk)),
    Real.mul_self_sqrt (Nat.cast_nonneg _)] at h
  exact h

theorem finiteSourceSmoothing_add_of_dvd (S : Finset ℕ) (a : ℕ → ℝ) {k M : ℕ} (hkM : k ∣ M)
    (t : ℕ) :
    finiteSourceSmoothing S a (ramanujanLagCoefficient k) (t + M) =
      finiteSourceSmoothing S a (ramanujanLagCoefficient k) t := by
  unfold finiteSourceSmoothing
  refine sum_congr rfl fun i _ => ?_
  rw [show t + M + i = (t + i) + M by ring, ramanujanLagCoefficient_add_of_dvd hkM]

theorem abs_finiteSourceSmoothing_le (S : Finset ℕ) {a : ℕ → ℝ} (ha : ∀ i, 0 ≤ a i) {k : ℕ}
    (hk : 0 < k) (t : ℕ) :
    |finiteSourceSmoothing S a (ramanujanLagCoefficient k) t| ≤ (∑ i ∈ S, a i) * k.totient := by
  unfold finiteSourceSmoothing
  calc _ ≤ ∑ i ∈ S, |a i * ramanujanLagCoefficient k (t + i)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ S, a i * k.totient := sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (ha i)]
        exact mul_le_mul_of_nonneg_left (abs_ramanujanLagCoefficient_le_totient hk _) (ha i)
    _ = _ := (sum_mul ..).symm

private theorem sum_range_mul_period {f : ℕ → ℝ} {M : ℕ} (hf : ∀ t, f (t + M) = f t) (q : ℕ) :
    (∑ t ∈ range (q * M), f t) = q * ∑ t ∈ range M, f t := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show (q + 1) * M = q * M + M by ring, sum_range_add, ih]
    have hper : ∀ j t, f (j * M + t) = f t := by
      intro j t
      induction j with
      | zero => simp
      | succ j ihj => rw [show (j + 1) * M + t = (j * M + t) + M by ring, hf, ihj]
    simp only [hper q]
    push_cast; ring

/-- **Smoothed pair sums over a range.** Over `t < L` the product of two smoothed Ramanujan
sums is its complete-period mean times the number of complete periods, up to one period of
boundary. -/
theorem abs_sum_range_smoothed_mul_sub_le (S : Finset ℕ) (a : ℕ → ℝ) {k l : ℕ}
    (hk : 0 < k) (hl : 0 < l) {A B : ℝ}
    (hA : ∀ t, |finiteSourceSmoothing S a (ramanujanLagCoefficient k) t| ≤ A)
    (hB : ∀ t, |finiteSourceSmoothing S a (ramanujanLagCoefficient l) t| ≤ B) (L : ℕ) :
    |(∑ t ∈ range L, finiteSourceSmoothing S a (ramanujanLagCoefficient k) t *
        finiteSourceSmoothing S a (ramanujanLagCoefficient l) t) -
      (if k = l then ((L / (k * l) * (k * l) : ℕ) : ℝ) * l.totient *
        ramanujanAutocorrelationWeight S a l else 0)| ≤ (k * l : ℕ) * (A * B) := by
  set M := k * l with hM
  have hM0 : 0 < M := Nat.mul_pos hk hl
  set f : ℕ → ℝ := fun t => finiteSourceSmoothing S a (ramanujanLagCoefficient k) t *
    finiteSourceSmoothing S a (ramanujanLagCoefficient l) t with hf
  have hper : ∀ t, f (t + M) = f t := by
    intro t
    have hkM : k ∣ M := ⟨l, rfl⟩
    have hlM : l ∣ M := ⟨k, by rw [hM]; ring⟩
    simp only [hf]
    rw [finiteSourceSmoothing_add_of_dvd S a hkM, finiteSourceSmoothing_add_of_dvd S a hlM]
  have hsplit : L = L / M * M + L % M := (Nat.div_add_mod' L M).symm
  have hperiod := sum_range_smoothedRamanujan_mul hk hl (dvd_mul_right k l) (dvd_mul_left l k) S a
  have hfull : (∑ t ∈ range (L / M * M), f t) =
      (if k = l then ((L / M * M : ℕ) : ℝ) * l.totient * ramanujanAutocorrelationWeight S a l
        else 0) := by
    rw [sum_range_mul_period hper, hperiod]
    split_ifs
    · rw [hM]; push_cast; ring
    · ring
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hrem : |∑ t ∈ Ico (L / M * M) L, f t| ≤ M * (A * B) := by
    calc _ ≤ ∑ t ∈ Ico (L / M * M) L, |f t| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ t ∈ Ico (L / M * M) L, A * B := sum_le_sum fun t _ => by
          simp only [hf, abs_mul]; exact mul_le_mul (hA t) (hB t) (abs_nonneg _) hA0
      _ = (L % M : ℕ) * (A * B) := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul]; congr 2; omega
      _ ≤ M * (A * B) := mul_le_mul_of_nonneg_right
          (by exact_mod_cast (Nat.mod_lt L hM0).le) (by positivity)
  have hsum : (∑ t ∈ range L, f t) = (∑ t ∈ range (L / M * M), f t) +
      ∑ t ∈ Ico (L / M * M) L, f t := by
    rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le _) (Nat.div_mul_le_self L M),
      ← range_eq_Ico]
  change |(∑ t ∈ range L, f t) - _| ≤ _
  rw [hsum, hfull, add_sub_cancel_left]
  exact hrem

/-- **Smoothed packets over a range.** `Σ_{t<L} (Σ_m β_m s_m(t))² ≤ L Σ_m β_m² φ(m) w_m +
(Σ_m |β_m| m A_m)²`, with `w_m` the autocorrelation weight and `A_m ≥ sup |s_m|`. -/
theorem sum_range_smoothed_packet_sq_le (S : Finset ℕ) (a : ℕ → ℝ) (T : Finset ℕ)
    (hT : ∀ m ∈ T, 0 < m) (β A : ℕ → ℝ)
    (hA : ∀ m ∈ T, ∀ t, |finiteSourceSmoothing S a (ramanujanLagCoefficient m) t| ≤ A m)
    (L : ℕ) :
    (∑ t ∈ range L, (∑ m ∈ T, β m *
        finiteSourceSmoothing S a (ramanujanLagCoefficient m) t) ^ 2) ≤
      L * ∑ m ∈ T, β m ^ 2 * m.totient * ramanujanAutocorrelationWeight S a m +
        (∑ m ∈ T, |β m| * m * A m) ^ 2 := by
  set s : ℕ → ℕ → ℝ := fun m t => finiteSourceSmoothing S a (ramanujanLagCoefficient m) t
  have hexp : (∑ t ∈ range L, (∑ m ∈ T, β m * s m t) ^ 2) =
      ∑ k ∈ T, ∑ l ∈ T, β k * β l * ∑ t ∈ range L, s k t * s l t := by
    simp only [sq, sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun l _ => ?_
    refine sum_congr rfl fun t _ => ?_
    ring
  have hpair : ∀ k ∈ T, ∀ l ∈ T, β k * β l * ∑ t ∈ range L, s k t * s l t ≤
      (if k = l then β k ^ 2 * (L * (k.totient * ramanujanAutocorrelationWeight S a k)) else 0) +
        (|β k| * k * A k) * (|β l| * l * A l) := by
    intro k hk l hl
    have hb := abs_sum_range_smoothed_mul_sub_le S a (hT k hk) (hT l hl) (hA k hk) (hA l hl) L
    set main := (if k = l then ((L / (k * l) * (k * l) : ℕ) : ℝ) * l.totient *
        ramanujanAutocorrelationWeight S a l else 0) with hmain
    have hA0 : 0 ≤ A k := (abs_nonneg _).trans (hA k hk 0)
    have hB0 : 0 ≤ A l := (abs_nonneg _).trans (hA l hl 0)
    have h1 : β k * β l * ∑ t ∈ range L, s k t * s l t ≤
        β k * β l * main + |β k * β l| * ((k * l : ℕ) * (A k * A l)) := by
      have := abs_le.mp hb
      have e : β k * β l * ∑ t ∈ range L, s k t * s l t =
          β k * β l * main + β k * β l * ((∑ t ∈ range L, s k t * s l t) - main) := by ring
      rw [e]
      have h2 : β k * β l * ((∑ t ∈ range L, s k t * s l t) - main) ≤
          |β k * β l| * ((k * l : ℕ) * (A k * A l)) := by
        calc _ ≤ |β k * β l * ((∑ t ∈ range L, s k t * s l t) - main)| := le_abs_self _
          _ = |β k * β l| * |(∑ t ∈ range L, s k t * s l t) - main| := abs_mul _ _
          _ ≤ _ := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      linarith
    refine h1.trans ?_
    have hw0 := ramanujanAutocorrelationWeight_nonneg S a l
    have hmain_le : β k * β l * main ≤
        (if k = l then β k ^ 2 * (L * (k.totient * ramanujanAutocorrelationWeight S a k)) else 0) := by
      rw [hmain]
      split_ifs with hkl
      · subst hkl
        have hq : ((L / (k * k) * (k * k) : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.div_mul_le_self L _
        have hφw : 0 ≤ (k.totient : ℝ) * ramanujanAutocorrelationWeight S a k := by positivity
        have := mul_le_mul_of_nonneg_right hq hφw
        nlinarith [sq_nonneg (β k)]
      · simp
    have hcross : |β k * β l| * ((k * l : ℕ) * (A k * A l)) =
        (|β k| * k * A k) * (|β l| * l * A l) := by rw [abs_mul]; push_cast; ring
    linarith
  rw [hexp]
  calc _ ≤ ∑ k ∈ T, ∑ l ∈ T, ((if k = l then β k ^ 2 * (L * (k.totient *
          ramanujanAutocorrelationWeight S a k)) else 0) +
          (|β k| * k * A k) * (|β l| * l * A l)) := sum_le_sum fun k hk => sum_le_sum fun l hl =>
        hpair k hk l hl
    _ = _ := by
        rw [show (∑ k ∈ T, ∑ l ∈ T, ((if k = l then β k ^ 2 * (L * (k.totient *
            ramanujanAutocorrelationWeight S a k)) else 0) +
            (|β k| * k * A k) * (|β l| * l * A l))) =
            (∑ k ∈ T, β k ^ 2 * (L * (k.totient * ramanujanAutocorrelationWeight S a k))) +
              (∑ k ∈ T, |β k| * k * A k) * (∑ l ∈ T, |β l| * l * A l) by
          simp only [sum_add_distrib, sum_ite_eq, sum_mul_sum]
          congr 1
          refine sum_congr rfl fun k hk => ?_
          rw [if_pos hk]]
        have h1 : (∑ k ∈ T, β k ^ 2 * (L * (k.totient * ramanujanAutocorrelationWeight S a k))) =
            L * ∑ m ∈ T, β m ^ 2 * m.totient * ramanujanAutocorrelationWeight S a m := by
          rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
        rw [h1]
        ring

/-! ### The near collar on a packet of conductors `≥ 2` -/

open RenormalizedArithmeticPotentialTheory

/-- Interior rows: the near-collar row is the collar smoothing at `n − D`. -/
theorem sum_collarNearKernel_eq_smoothing {D N n : ℕ} (hDn : D < n) (hnN : n + D ≤ N)
    (F : ℕ → ℝ) :
    (∑ j ∈ Icc 1 N, collarNearKernel D n j * F j) =
      finiteSourceSmoothing (range (2 * D + 1)) (collarSourceWeight D) F (n - D) := by
  unfold finiteSourceSmoothing
  have hsub : (range (2 * D + 1)).map ⟨fun i => n - D + i, add_right_injective _⟩ ⊆ Icc 1 N := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_map.mp hj
    have := mem_range.mp hi
    simp only [Function.Embedding.coeFn_mk, mem_Icc]; omega
  rw [← sum_subset hsub (fun j hjN hj => ?_), sum_map]
  · refine sum_congr rfl fun i hi => ?_
    have hi' := mem_range.mp hi
    simp only [Function.Embedding.coeFn_mk]
    congr 1
    unfold collarNearKernel collarSourceWeight
    have hcast : ((n - D + i : ℕ) : ℝ) = (n : ℝ) - D + i := by
      rw [Nat.cast_add, Nat.cast_sub hDn.le]
    by_cases hiD : i = D
    · subst hiD
      rw [if_neg (by rw [show n - i + i = n by omega]; simp), if_pos rfl]
    · have hne : n ≠ n - D + i := by omega
      have habs : |(n : ℝ) - ((n - D + i : ℕ) : ℝ)| = (Nat.dist i D : ℝ) := by
        rw [hcast]
        rcases le_total i D with h | h
        · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h,
            show (n : ℝ) - ((n : ℝ) - D + i) = D - i by ring, abs_of_nonneg (by
              have : (i : ℝ) ≤ D := by exact_mod_cast h
              linarith)]
        · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h,
            show (n : ℝ) - ((n : ℝ) - D + i) = -(i - D) by ring, abs_neg, abs_of_nonneg (by
              have : (D : ℝ) ≤ i := by exact_mod_cast h
              linarith)]
      have hle : (Nat.dist i D : ℝ) ≤ D := by
        rcases le_total i D with h | h
        · rw [Nat.dist_eq_sub_of_le h]; exact_mod_cast Nat.sub_le D i
        · rw [Nat.dist_eq_sub_of_le_right h]; exact_mod_cast (show i - D ≤ D by omega)
      rw [if_pos ⟨hne, habs ▸ hle⟩, if_neg hiD, habs]
      ring
  · have hj' : j ∉ Icc (n - D) (n + D) := by
      intro hjI
      apply hj
      refine mem_map.mpr ⟨j - (n - D), mem_range.mpr ?_, ?_⟩
      · have := mem_Icc.mp hjI; omega
      · simp only [Function.Embedding.coeFn_mk]; have := mem_Icc.mp hjI; omega
    unfold collarNearKernel
    rw [if_neg, zero_mul]
    rintro ⟨-, hle⟩
    apply hj'
    rw [mem_Icc]
    have h1 : (n : ℝ) - D ≤ j := by have := (abs_le.mp hle).2; linarith
    have h2 : (j : ℝ) ≤ n + D := by have := (abs_le.mp hle).1; linarith
    constructor
    · have : ((n - D : ℕ) : ℝ) ≤ j := by rw [Nat.cast_sub hDn.le]; exact h1
      exact_mod_cast this
    · exact_mod_cast h2

/-- Every near-collar row has total weight at most the collar source mass. -/
theorem sum_collarNearKernel_le (D N n : ℕ) :
    (∑ j ∈ Icc 1 N, collarNearKernel D n j) ≤
      ∑ i ∈ range (2 * D + 1), collarSourceWeight D i := by
  by_cases hD : D = 0
  · subst hD
    have : ∀ j, collarNearKernel 0 n j = 0 := by
      intro j; unfold collarNearKernel
      split_ifs with h
      · exfalso
        have h1 := h.1
        have h2 := h.2
        have : (n : ℝ) = j := by
          have := abs_nonneg ((n : ℝ) - j)
          have : |(n : ℝ) - j| = 0 := le_antisymm (by simpa using h2) this
          linarith [abs_eq_zero.mp this]
        exact h1 (by exact_mod_cast this)
      · rfl
    simp only [this, sum_const_zero]
    exact sum_nonneg fun i _ => by unfold collarSourceWeight; split_ifs <;> positivity
  -- rows read at most the weights `1/(2|h|)`, `0 < |h| ≤ D`, each once
  have hrow : ∀ j, collarNearKernel D n j =
      if j + D < n ∨ n + D < j then 0 else collarSourceWeight D (j + D - n) := by
    intro j
    unfold collarNearKernel collarSourceWeight
    by_cases hout : j + D < n ∨ n + D < j
    · rw [if_pos hout, if_neg]
      rintro ⟨-, hle⟩
      rcases hout with h | h
      · have : (j : ℝ) + D < n := by exact_mod_cast h
        have := (abs_le.mp hle).2; linarith
      · have : (n : ℝ) + D < j := by exact_mod_cast h
        have := (abs_le.mp hle).1; linarith
    · rw [if_neg hout]
      push Not at hout
      by_cases hjn : j = n
      · subst hjn; simp
      · have hne : j + D - n ≠ D := by omega
        have habs : |(n : ℝ) - j| = (Nat.dist (j + D - n) D : ℝ) := by
          rcases le_total j n with h | h
          · rw [Nat.dist_eq_sub_of_le (by omega), show D - (j + D - n) = n - j by omega,
              Nat.cast_sub h, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
          · rw [Nat.dist_eq_sub_of_le_right (by omega), show j + D - n - D = j - n by omega,
              Nat.cast_sub h, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
        have hle : |(n : ℝ) - j| ≤ D := by
          rw [abs_le]; constructor
          · have : (j : ℝ) ≤ n + D := by exact_mod_cast hout.2
            linarith
          · have : (n : ℝ) ≤ j + D := by exact_mod_cast hout.1
            linarith
        rw [if_pos ⟨fun h => hjn h.symm, hle⟩, if_neg hne, habs]
        ring
  calc (∑ j ∈ Icc 1 N, collarNearKernel D n j)
      ≤ ∑ j ∈ Icc 1 N, (if j + D < n ∨ n + D < j then 0 else
          collarSourceWeight D (j + D - n)) := le_of_eq (sum_congr rfl fun j _ => hrow j)
    _ ≤ ∑ i ∈ range (2 * D + 1), collarSourceWeight D i := by
        rw [show (∑ j ∈ Icc 1 N, (if j + D < n ∨ n + D < j then (0 : ℝ) else
            collarSourceWeight D (j + D - n))) = ∑ j ∈ (Icc 1 N).filter
              (fun j => ¬(j + D < n ∨ n + D < j)), collarSourceWeight D (j + D - n) by
          rw [sum_filter]; exact sum_congr rfl fun j _ => by split_ifs <;> simp_all]
        have hinj : Set.InjOn (fun j => j + D - n)
            ((Icc 1 N).filter (fun j => ¬(j + D < n ∨ n + D < j))) := by
          intro x hx y hy hxy
          simp only [coe_filter, Set.mem_setOf_eq, mem_Icc] at hx hy
          simp only at hxy
          omega
        rw [← sum_image hinj]
        apply sum_le_sum_of_subset_of_nonneg
        · intro i hi
          obtain ⟨j, hj, rfl⟩ := mem_image.mp hi
          simp only [mem_filter, mem_Icc] at hj
          rw [mem_range]; omega
        · intro i _ _; unfold collarSourceWeight; split_ifs <;> positivity

/-- The near-collar row of a packet in the profile `G(j) = Σ_m b_m v̂_m(j)`. -/
theorem collarRowNear_eq {R N : ℕ} (b : ℕ → ℝ) {n : ℕ} :
    collarRowNear R N b n = Real.sqrt ((n : ℝ) / N) / (Real.sqrt N * Real.sqrt (Real.log N)) *
      ∑ j ∈ Icc 1 N, collarNearKernel (R ^ 4) n j *
        ∑ m ∈ Icc 1 R, b m * normalizedRamanujanMode m j := by
  unfold collarRowNear
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
  rw [primeHorizonExtension_coe _ ⟨j, hj⟩]
  change _ * (collarNearKernel (R ^ 4) n j * (Real.sqrt ((j : ℝ) / N) *
    (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨j, hj⟩)
      (∑ m ∈ Icc 1 R, b m • normalizedRamanujanHorizonVector m N))) = _
  rw [map_sum]
  have hterm : ∀ m ∈ Icc 1 R, (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨j, hj⟩)
      (b m • normalizedRamanujanHorizonVector m N) =
        b m * ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode m j / Real.sqrt j)) :=
    fun m _ => rfl
  rw [sum_congr rfl hterm]
  have hsj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
  rw [Real.sqrt_div' _ (Nat.cast_nonneg N)]
  by_cases hN : (N : ℝ) = 0
  · simp [hN]
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (lt_of_le_of_ne (Nat.cast_nonneg N) (Ne.symm hN))
  by_cases hL : Real.log N = 0
  · simp [hL]
  have hsL : Real.sqrt (Real.log N) ≠ 0 := by
    intro h
    rw [Real.sqrt_eq_zero'] at h
    exact hL (le_antisymm h (Real.log_natCast_nonneg N))
  have hinner : Real.sqrt ((j : ℝ) / N) * (∑ x ∈ Icc 1 R, b x *
      ((Real.sqrt (Real.log N))⁻¹ * (normalizedRamanujanMode x j / Real.sqrt j))) =
      (1 / (Real.sqrt N * Real.sqrt (Real.log N))) *
        ∑ m ∈ Icc 1 R, b m * normalizedRamanujanMode m j := by
    rw [Real.sqrt_div' _ (Nat.cast_nonneg N), mul_sum, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    field_simp
  rw [hinner]
  ring

/-- **The sharp near collar.** On a packet without the pole conductor (`b 1 = 0`) the
near-collar rows cost `130/log N · Σ b_m² m/φ(m)` — the mean square of the logarithmic
multiplier over primitive frequencies — up to a boundary term of relative size `R⁶/N`. -/
theorem sum_collarRowNear_sq_le_sharp {R N : ℕ} (hR : 1 ≤ R) (hN : 1 ≤ N) (hL : 0 < Real.log N)
    (b : ℕ → ℝ) (hb1 : b 1 = 0) :
    (∑ n ∈ Icc 1 N, collarRowNear R N b n ^ 2) ≤
      130 / Real.log N * (∑ m ∈ Icc 1 R, b m ^ 2 * ((m : ℝ) / m.totient)) +
        (∑ i ∈ range (2 * R ^ 4 + 1), collarSourceWeight (R ^ 4) i) ^ 2 /
            ((N : ℝ) * Real.log N) *
          ((∑ m ∈ Icc 1 R, |b m| * m * Real.sqrt m.totient) ^ 2 +
            2 * (R : ℝ) ^ 4 * (∑ m ∈ Icc 1 R, |b m| * Real.sqrt m.totient) ^ 2) := by
  set D := R ^ 4 with hD
  set H := ∑ i ∈ range (2 * D + 1), collarSourceWeight D i with hH
  have hw0 : ∀ i, 0 ≤ collarSourceWeight D i := fun i => by
    unfold collarSourceWeight; split_ifs <;> positivity
  have hH0 : 0 ≤ H := sum_nonneg fun i _ => hw0 i
  set G : ℕ → ℝ := fun j => ∑ m ∈ Icc 1 R, b m * normalizedRamanujanMode m j with hG
  set Gc := ∑ m ∈ Icc 1 R, |b m| * Real.sqrt m.totient with hGc
  have hGc0 : 0 ≤ Gc := sum_nonneg fun _ _ => by positivity
  have hGsup : ∀ j, |G j| ≤ Gc := by
    intro j
    calc |G j| ≤ ∑ m ∈ Icc 1 R, |b m * normalizedRamanujanMode m j| := abs_sum_le_sum_abs _ _
      _ ≤ Gc := sum_le_sum fun m hm => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient
            (mem_Icc.mp hm).1 j) (abs_nonneg _)
  set r : ℕ → ℝ := fun n => ∑ j ∈ Icc 1 N, collarNearKernel D n j * G j with hr
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  -- each row is at most `r(n)²/(N log N)`
  have hrow : ∀ n ∈ Icc 1 N, collarRowNear R N b n ^ 2 ≤ r n ^ 2 / ((N : ℝ) * Real.log N) := by
    intro n hn
    rw [collarRowNear_eq, mul_pow, div_pow, Real.sq_sqrt (by positivity), mul_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt hL.le]
    have hnN : (n : ℝ) / N ≤ 1 := by
      rw [div_le_one hN0]; exact_mod_cast (mem_Icc.mp hn).2
    have hr0 : 0 ≤ r n ^ 2 / ((N : ℝ) * Real.log N) := by positivity
    calc (n : ℝ) / N / ((N : ℝ) * Real.log N) * r n ^ 2
        = (n : ℝ) / N * (r n ^ 2 / ((N : ℝ) * Real.log N)) := by ring
      _ ≤ 1 * (r n ^ 2 / ((N : ℝ) * Real.log N)) := mul_le_mul_of_nonneg_right hnN hr0
      _ = _ := one_mul _
  -- split interior and boundary rows
  set I := (Icc 1 N).filter (fun n => D < n ∧ n + D ≤ N) with hI
  set B := (Icc 1 N).filter (fun n => ¬(D < n ∧ n + D ≤ N)) with hB
  have hsplit : (∑ n ∈ Icc 1 N, r n ^ 2) = (∑ n ∈ I, r n ^ 2) + ∑ n ∈ B, r n ^ 2 :=
    (sum_filter_add_sum_filter_not _ _ _).symm
  -- boundary
  have hBcard : (B.card : ℝ) ≤ 2 * D := by
    have hsub : B ⊆ Icc 1 D ∪ Ioc (N - D) N := by
      intro n hn
      simp only [hB, mem_filter, mem_Icc] at hn
      rw [mem_union, mem_Icc, mem_Ioc]; omega
    have := (card_le_card hsub).trans (card_union_le _ _)
    rw [Nat.card_Icc, Nat.card_Ioc] at this
    have h2 : D + 1 - 1 + (N - (N - D)) ≤ 2 * D := by omega
    exact_mod_cast this.trans h2
  have hBrow : ∀ n, r n ^ 2 ≤ (H * Gc) ^ 2 := by
    intro n
    have habs : |r n| ≤ H * Gc := by
      calc |r n| ≤ ∑ j ∈ Icc 1 N, |collarNearKernel D n j * G j| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ j ∈ Icc 1 N, collarNearKernel D n j * Gc := sum_le_sum fun j _ => by
            have hK0 : 0 ≤ collarNearKernel D n j := by
              unfold collarNearKernel; split_ifs <;> positivity
            rw [abs_mul, abs_of_nonneg hK0]
            exact mul_le_mul_of_nonneg_left (hGsup j) hK0
        _ = (∑ j ∈ Icc 1 N, collarNearKernel D n j) * Gc := (sum_mul ..).symm
        _ ≤ H * Gc := mul_le_mul_of_nonneg_right (sum_collarNearKernel_le D N n) hGc0
    have := sq_abs (r n) ▸ pow_le_pow_left₀ (abs_nonneg _) habs 2
    exact this
  have hBsum : (∑ n ∈ B, r n ^ 2) ≤ 2 * D * (H * Gc) ^ 2 := by
    calc (∑ n ∈ B, r n ^ 2) ≤ ∑ n ∈ B, (H * Gc) ^ 2 := sum_le_sum fun n _ => hBrow n
      _ = B.card * (H * Gc) ^ 2 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 2 * D * (H * Gc) ^ 2 := mul_le_mul_of_nonneg_right hBcard (sq_nonneg _)
  -- interior: the collar smoothing of the packet
  set s : ℕ → ℝ := fun t => finiteSourceSmoothing (range (2 * D + 1)) (collarSourceWeight D) G t
    with hs
  have hIrow : ∀ n ∈ I, r n = s (n - D) := by
    intro n hn
    simp only [hI, mem_filter] at hn
    exact sum_collarNearKernel_eq_smoothing hn.2.1 hn.2.2 G
  have hIsum : (∑ n ∈ I, r n ^ 2) ≤ ∑ t ∈ range N, s t ^ 2 := by
    rw [sum_congr rfl fun n hn => by rw [hIrow n hn]]
    have hinj : Set.InjOn (fun n => n - D) I := by
      intro x hx y hy hxy
      simp only [hI, coe_filter, Set.mem_setOf_eq, mem_Icc] at hx hy
      simp only at hxy; omega
    rw [← sum_image hinj (f := fun t => s t ^ 2)]
    apply sum_le_sum_of_subset_of_nonneg
    · intro t ht
      obtain ⟨n, hn, rfl⟩ := mem_image.mp ht
      simp only [hI, mem_filter, mem_Icc] at hn
      have hD1 : 1 ≤ D := by rw [hD]; exact Nat.one_le_pow _ _ hR
      rw [mem_range]; omega
    · intro _ _ _; exact sq_nonneg _
  -- the smoothing is the packet of smoothed Ramanujan sums
  have hslin : ∀ t, s t = ∑ m ∈ Icc 1 R, b m / Real.sqrt m.totient *
      finiteSourceSmoothing (range (2 * D + 1)) (collarSourceWeight D)
        (ramanujanLagCoefficient m) t := by
    intro t
    simp only [hs, hG]
    rw [finiteSourceSmoothing_sum]
    refine sum_congr rfl fun m hm => ?_
    have hm0 := (mem_Icc.mp hm).1
    rw [show (fun k => b m * normalizedRamanujanMode m k) =
        fun k => (b m / Real.sqrt m.totient) * ramanujanLagCoefficient m k by
      funext k
      rw [RenormalizedArithmeticPotentialTheory.normalizedRamanujanMode_eq_coefficient hm0]
      ring, finiteSourceSmoothing_const_mul]
  have hpack := sum_range_smoothed_packet_sq_le (range (2 * D + 1)) (collarSourceWeight D)
    (Icc 1 R) (fun m hm => (mem_Icc.mp hm).1) (fun m => b m / Real.sqrt m.totient)
    (fun m => H * m.totient)
    (fun m hm t => abs_finiteSourceSmoothing_le _ hw0 (mem_Icc.mp hm).1 t) N
  have hmain : (∑ m ∈ Icc 1 R, (b m / Real.sqrt m.totient) ^ 2 * m.totient *
      ramanujanAutocorrelationWeight (range (2 * D + 1)) (collarSourceWeight D) m) ≤
      130 * ∑ m ∈ Icc 1 R, b m ^ 2 * ((m : ℝ) / m.totient) := by
    rw [mul_sum]
    refine sum_le_sum fun m hm => ?_
    have hm0 := (mem_Icc.mp hm).1
    have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
    rw [div_pow, Real.sq_sqrt hφ.le, div_mul_cancel₀ _ hφ.ne']
    rcases eq_or_lt_of_le hm0 with h1 | h2
    · subst h1; rw [hb1]; simp
    · have hw := ramanujanAutocorrelationWeight_collar_le (show 2 ≤ m by omega) D
      have hb2 := sq_nonneg (b m)
      calc b m ^ 2 * ramanujanAutocorrelationWeight _ _ m ≤ b m ^ 2 * (130 * (m : ℝ) / m.totient) :=
            mul_le_mul_of_nonneg_left hw hb2
        _ = 130 * (b m ^ 2 * ((m : ℝ) / m.totient)) := by ring
  have hcross : (∑ m ∈ Icc 1 R, |b m / Real.sqrt m.totient| * m * (H * m.totient)) =
      H * ∑ m ∈ Icc 1 R, |b m| * m * Real.sqrt m.totient := by
    rw [mul_sum]
    refine sum_congr rfl fun m hm => ?_
    have hm0 := (mem_Icc.mp hm).1
    have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm0
    have hsφ := Real.sqrt_pos.mpr hφ
    rw [abs_div, abs_of_pos hsφ]
    calc |b m| / Real.sqrt m.totient * m * (H * m.totient) =
        H * (|b m| * m * ((m.totient : ℝ) / Real.sqrt m.totient)) := by ring
      _ = H * (|b m| * m * Real.sqrt m.totient) := by rw [Real.div_sqrt]
  have hIbound : (∑ t ∈ range N, s t ^ 2) ≤
      N * (130 * ∑ m ∈ Icc 1 R, b m ^ 2 * ((m : ℝ) / m.totient)) +
        (H * ∑ m ∈ Icc 1 R, |b m| * m * Real.sqrt m.totient) ^ 2 := by
    rw [sum_congr rfl fun t _ => by rw [hslin t]]
    refine hpack.trans ?_
    rw [hcross]
    have := mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg N)
    linarith
  -- assemble
  calc (∑ n ∈ Icc 1 N, collarRowNear R N b n ^ 2)
      ≤ ∑ n ∈ Icc 1 N, r n ^ 2 / ((N : ℝ) * Real.log N) := sum_le_sum hrow
    _ = (∑ n ∈ Icc 1 N, r n ^ 2) / ((N : ℝ) * Real.log N) := (sum_div ..).symm
    _ ≤ (N * (130 * ∑ m ∈ Icc 1 R, b m ^ 2 * ((m : ℝ) / m.totient)) +
          (H * ∑ m ∈ Icc 1 R, |b m| * m * Real.sqrt m.totient) ^ 2 + 2 * D * (H * Gc) ^ 2) /
          ((N : ℝ) * Real.log N) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        rw [hsplit]; linarith
    _ = _ := by
        rw [hD]; push_cast
        field_simp
        ring

end GaloisForLFunctions.CompletedArithmeticForms
