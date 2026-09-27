import GaloisForLFunctions.RHTower.MobiusDiscretePacketGeneralOrder

/-!
# Finite packet horizon of the cubic Möbius source

Write `c_k(N) = Σ_{1 ≤ n ≤ N} μ(n) g_k(n)` with the cubic packet kernel
`g_k(x) = x² (x+1)^{-(5+δ)} ((x-1)/(x+1))^k`, so that the cubic Route L source is
`B(N) = 2^{5+δ} Σ_k w_k c_k(N)²` with `w_k = C(4+δ+k, k)`.  For `0 ≤ δ ≤ 1` and `N ≥ 1`:

* `|c_k| ≤ (3/2) e^{-2k/(N+1)}`, since `0 ≤ q_n ≤ e^{-2/(n+1)}` and `Σ n^{-3} ≤ 3/2`;
* `w_k ≤ C(k+5, 5) ≤ (k+5)^5/120` and `w_k ≤ e^5 k^{4+δ}`, from the product
  `w_k = Π_{j<k} (5+δ+j)/(j+1)`;
* the tail beyond `K` is at most `144 (N+1)^6 e^{-2K/(N+1)}`, by comparison with the binomial
  series `Σ_k C(k+5,5) z^k = (1-z)^{-6}` at `z = e^{-2/(N+1)}`.

With `K_P(N) = ⌈((P+6)/2)(N+1) log(N+1)⌉` the tail is `≤ 144 (N+1)^{-P}`, so a cutoff-uniform
bound for `B(N)` is equivalent to the same bound for the finite packet range `k < K_P(N)`.
-/

open Finset Filter
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace RHTower.DiscretePacket

open MobiusPacketDifference MobiusRenewalPacketEnergy

/-! ### The cubic packet in the natural indexing -/

/-- The cubic packet kernel `g_k(x) = x² (x+1)^{-(5+δ)} ((x-1)/(x+1))^k`. -/
def packetKernel (δ : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 * (x + 1) ^ (-(5 + δ)) * ((x - 1) / (x + 1)) ^ k

/-- The literal cubic packet `c_k(N) = Σ_{1 ≤ n ≤ N} μ(n) g_k(n)`. -/
def cubicPacket (δ : ℝ) (N k : ℕ) : ℝ :=
  ∑ n ∈ Ioc 0 N, ((μ n : ℤ) : ℝ) * packetKernel δ k n

theorem sum_Ioc_zero_eq_range_succ (f : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, f n) = ∑ n ∈ range N, f (n + 1) := by
  rw [← Finset.Icc_add_one_left_eq_Ioc, Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 N 1]
  rfl

theorem cubicPacket_eq_sourcePacket (δ : ℝ) (N k : ℕ) :
    cubicPacket δ N k = sourcePacket cubicShiftedCoefficient N (5 + δ) k := by
  unfold cubicPacket sourcePacket
  rw [sum_Ioc_zero_eq_range_succ]
  apply sum_congr rfl
  intro n _
  unfold packetKernel cubicShiftedCoefficient shiftedMobiusRealCoefficient weight node
  push_cast
  rw [show (n : ℝ) + 1 + 1 = (n : ℝ) + 2 by ring, show (n : ℝ) + 1 - 1 = n by ring]
  ring

/-- The cubic packet is the step-two second difference of the order-one packets. -/
theorem cubicPacket_eq_stepTwo (δ : ℝ) (N k : ℕ) :
    cubicPacket δ N k = (packet N (1 + δ) k - 2 * packet N (1 + δ) (k + 2) +
      packet N (1 + δ) (k + 4)) / 16 := by
  rw [cubicPacket_eq_sourcePacket, cubic_sourcePacket_eq_stepTwoDifference]

/-- The cubic Route L source as a weighted square sum of the literal cubic packets. -/
theorem routeLCubicEnergy_eq_cubicPacket (N : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    finiteGeneralReciprocalEnergy (3 + δ) δ N =
      2 ^ (5 + δ) * ∑' k : ℕ, binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2 := by
  rw [routeLCubicEnergy_eq_packetSecondDifference N δ hδ]
  simp_rw [cubicPacket_eq_stepTwo]

/-! ### The binomial weights -/

/-- Product formula `C(r+k-1, k) = Π_{j<k} (r+j)/(j+1)`. -/
theorem inv_factorial_mul_ascPochhammer_eq_prod (r : ℝ) (k : ℕ) :
    (k.factorial : ℝ)⁻¹ * (ascPochhammer ℝ k).eval r = ∏ j ∈ range k, (r + j) / (j + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ascPochhammer_succ_eval, Finset.prod_range_succ, ← ih, Nat.factorial_succ]
    push_cast
    have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp

theorem binomialWeight_eq_prod (r : ℝ) (k : ℕ) :
    binomialWeight r k = ∏ j ∈ range k, (r + j) / (j + 1) := by
  rw [← inv_factorial_mul_ascPochhammer_eq_prod]
  unfold binomialWeight
  rw [← Ring.multichoose_eq r k, ← Polynomial.ascPochhammer_smeval_eq_eval,
    Polynomial.ascPochhammer_smeval_cast]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r k
  simp only [nsmul_eq_mul] at h
  rw [← h, ← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)),
    one_mul]

theorem binomialWeight_pos {r : ℝ} (hr : 0 < r) (k : ℕ) : 0 < binomialWeight r k := by
  rw [binomialWeight_eq_prod]
  exact prod_pos fun j _ => by positivity

/-- The weights increase with the order. -/
theorem binomialWeight_mono {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (k : ℕ) :
    binomialWeight r k ≤ binomialWeight s k := by
  rw [binomialWeight_eq_prod, binomialWeight_eq_prod]
  apply Finset.prod_le_prod
  · intro j _
    positivity
  · intro j _
    gcongr

theorem binomialWeight_six (k : ℕ) : binomialWeight 6 k = ((k + 5).choose 5 : ℝ) := by
  unfold binomialWeight
  rw [show (6 : ℝ) + k - 1 = ((k + 5 : ℕ) : ℝ) by push_cast; ring, Ring.choose_natCast,
    show k + 5 = 5 + k by ring, ← Nat.choose_symm_add, show 5 + k = k + 5 by ring]

/-- `C(4+δ+k, k) ≤ C(k+5, 5) ≤ (k+5)^5/120` for `δ ≤ 1`. -/
theorem binomialWeight_le_choose {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    binomialWeight (5 + δ) k ≤ ((k + 5).choose 5 : ℝ) ∧
      ((k + 5).choose 5 : ℝ) ≤ ((k : ℝ) + 5) ^ 5 / 120 := by
  refine ⟨?_, ?_⟩
  · rw [← binomialWeight_six]
    exact binomialWeight_mono (by linarith) (by linarith) k
  · have h := Nat.choose_le_pow_div (α := ℝ) 5 (k + 5)
    push_cast at h
    simpa [Nat.factorial] using h

/-- `C(4+δ+k, k) ≤ e^5 k^{4+δ}` for `k ≥ 1`, `0 ≤ δ ≤ 1`. -/
theorem binomialWeight_le_rpow {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    binomialWeight (5 + δ) k ≤ Real.exp 5 * (k : ℝ) ^ (4 + δ) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hprod : binomialWeight (5 + δ) k ≤
      Real.exp ((4 + δ) * ∑ j ∈ range k, ((j : ℝ) + 1)⁻¹) := by
    rw [binomialWeight_eq_prod, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_le_prod
    · intro j _
      positivity
    · intro j _
      have h := Real.add_one_le_exp ((4 + δ) * ((j : ℝ) + 1)⁻¹)
      have he : (5 + δ + j) / ((j : ℝ) + 1) = (4 + δ) * ((j : ℝ) + 1)⁻¹ + 1 := by
        field_simp
        ring
      rw [he]
      exact h
  have hharm : ∑ j ∈ range k, ((j : ℝ) + 1)⁻¹ ≤ 1 + Real.log k := by
    have h := harmonic_le_one_add_log k
    unfold harmonic at h
    push_cast at h
    exact h
  calc binomialWeight (5 + δ) k ≤ Real.exp ((4 + δ) * (1 + Real.log k)) :=
        hprod.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hharm (by linarith)))
    _ = Real.exp (4 + δ) * (k : ℝ) ^ (4 + δ) := by
        rw [mul_add, mul_one, Real.exp_add, Real.rpow_def_of_pos hkpos]
        ring_nf
    _ ≤ Real.exp 5 * (k : ℝ) ^ (4 + δ) := by
        gcongr
        linarith

/-- The binomial series `Σ_k C(r+k-1,k) q^k = (1-q)^{-r}` for `|q| < 1`. -/
theorem binomialWeight_hasSum (r : ℝ) {q : ℝ} (hq : |q| < 1) :
    HasSum (fun k : ℕ => binomialWeight r k * q ^ k) (1 / (1 - q) ^ r) := by
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero r).hasSum
    (show q ∈ Metric.eball (0 : ℝ) 1 by
      rw [Metric.mem_eball]
      simpa [edist_dist, Real.dist_eq] using hq)
  simpa [binomialWeight, FormalMultilinearSeries.ofScalars] using h

/-! ### The packet bound (5) -/

theorem node_le_exp {x : ℝ} (hx : 1 ≤ x) : (x - 1) / (x + 1) ≤ Real.exp (-(2 / (x + 1))) := by
  have h := Real.add_one_le_exp (-(2 / (x + 1)))
  have he : (x - 1) / (x + 1) = -(2 / (x + 1)) + 1 := by
    field_simp
    ring
  rw [he]
  exact h

theorem node_nonneg' {x : ℝ} (hx : 1 ≤ x) : 0 ≤ (x - 1) / (x + 1) :=
  div_nonneg (by linarith) (by linarith)

theorem packetKernel_nonneg {δ : ℝ} (k : ℕ) {x : ℝ} (hx : 1 ≤ x) : 0 ≤ packetKernel δ k x := by
  unfold packetKernel
  have := node_nonneg' hx
  have : 0 ≤ (x + 1) ^ (-(5 + δ)) := Real.rpow_nonneg (by linarith) _
  positivity

/-- `0 ≤ g_k(x) ≤ (x+1)^{-3-δ} e^{-2k/(x+1)}` for `x ≥ 1`. -/
theorem packetKernel_le {δ : ℝ} (k : ℕ) {x : ℝ} (hx : 1 ≤ x) :
    packetKernel δ k x ≤ (x + 1) ^ (-(3 + δ)) * Real.exp (-(2 * k / (x + 1))) := by
  have hx1 : 0 < x + 1 := by linarith
  have hsplit : (x + 1) ^ (-(5 + δ)) = (x + 1) ^ (-(3 + δ)) * ((x + 1) ^ 2)⁻¹ := by
    rw [show -(5 + δ) = -(3 + δ) + -((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_add hx1,
      Real.rpow_neg hx1.le ((2 : ℕ) : ℝ), Real.rpow_natCast]
  have hq : ((x - 1) / (x + 1)) ^ k ≤ Real.exp (-(2 * k / (x + 1))) := by
    calc ((x - 1) / (x + 1)) ^ k ≤ Real.exp (-(2 / (x + 1))) ^ k :=
          pow_le_pow_left₀ (node_nonneg' hx) (node_le_exp hx) k
      _ = _ := by rw [← Real.exp_nat_mul]; ring_nf
  have hfac : x ^ 2 * ((x + 1) ^ 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by positivity)]
    nlinarith
  unfold packetKernel
  rw [hsplit]
  have h3 : 0 ≤ (x + 1) ^ (-(3 + δ)) := Real.rpow_nonneg hx1.le _
  calc x ^ 2 * ((x + 1) ^ (-(3 + δ)) * ((x + 1) ^ 2)⁻¹) * ((x - 1) / (x + 1)) ^ k
      = (x + 1) ^ (-(3 + δ)) * (x ^ 2 * ((x + 1) ^ 2)⁻¹) * ((x - 1) / (x + 1)) ^ k := by ring
    _ ≤ (x + 1) ^ (-(3 + δ)) * 1 * Real.exp (-(2 * k / (x + 1))) := by
        gcongr
    _ = _ := by ring

/-- `Σ_{1 ≤ n ≤ N} n^{-3} ≤ 3/2 - 1/(2N²)`. -/
theorem sum_inv_cube_le (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Ioc 0 N, ((n : ℝ) ^ 3)⁻¹ ≤ 3 / 2 - 1 / (2 * (N : ℝ) ^ 2) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top (by omega)]
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    push_cast
    have key : 1 / (2 * (N : ℝ) ^ 2) - 1 / (2 * ((N : ℝ) + 1) ^ 2) - (((N : ℝ) + 1) ^ 3)⁻¹ =
        (3 * (N : ℝ) + 1) / (2 * (N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 3) := by
      field_simp
      ring
    have hpos : 0 ≤ (3 * (N : ℝ) + 1) / (2 * (N : ℝ) ^ 2 * ((N : ℝ) + 1) ^ 3) := by positivity
    linarith

theorem abs_moebius_le_one' (n : ℕ) : |((μ n : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- **Bound (5).**  `|c_k(N)| ≤ (3/2) e^{-2k/(N+1)}` for every `δ ≥ 0`. -/
theorem abs_cubicPacket_le {δ : ℝ} (hδ : 0 ≤ δ) (N k : ℕ) :
    |cubicPacket δ N k| ≤ 3 / 2 * Real.exp (-(2 * k / ((N : ℝ) + 1))) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [cubicPacket]
    positivity
  have hterm : ∀ n ∈ Ioc 0 N, |((μ n : ℤ) : ℝ) * packetKernel δ k n| ≤
      ((n : ℝ) ^ 3)⁻¹ * Real.exp (-(2 * k / ((N : ℝ) + 1))) := by
    intro n hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Ioc.mp hn).2
    have hg0 := packetKernel_nonneg (δ := δ) k hn1
    rw [abs_mul, abs_of_nonneg hg0]
    have hpow : ((n : ℝ) + 1) ^ (-(3 + δ)) ≤ ((n : ℝ) ^ 3)⁻¹ := by
      calc ((n : ℝ) + 1) ^ (-(3 + δ)) ≤ ((n : ℝ) + 1) ^ (-((3 : ℕ) : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by push_cast; linarith)
        _ = (((n : ℝ) + 1) ^ 3)⁻¹ := by rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
        _ ≤ ((n : ℝ) ^ 3)⁻¹ := by
            apply inv_anti₀ (by positivity)
            gcongr
            linarith
    have hexp : Real.exp (-(2 * k / ((n : ℝ) + 1))) ≤ Real.exp (-(2 * k / ((N : ℝ) + 1))) := by
      apply Real.exp_le_exp.mpr
      apply neg_le_neg
      apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    calc |((μ n : ℤ) : ℝ)| * packetKernel δ k n ≤ 1 * packetKernel δ k n :=
          mul_le_mul_of_nonneg_right (abs_moebius_le_one' n) hg0
      _ ≤ ((n : ℝ) + 1) ^ (-(3 + δ)) * Real.exp (-(2 * k / ((n : ℝ) + 1))) := by
          rw [one_mul]; exact packetKernel_le k hn1
      _ ≤ _ := mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
  unfold cubicPacket
  calc |∑ n ∈ Ioc 0 N, ((μ n : ℤ) : ℝ) * packetKernel δ k n|
      ≤ ∑ n ∈ Ioc 0 N, |((μ n : ℤ) : ℝ) * packetKernel δ k n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Ioc 0 N, ((n : ℝ) ^ 3)⁻¹ * Real.exp (-(2 * k / ((N : ℝ) + 1))) :=
        sum_le_sum hterm
    _ = (∑ n ∈ Ioc 0 N, ((n : ℝ) ^ 3)⁻¹) * Real.exp (-(2 * k / ((N : ℝ) + 1))) := by
        rw [Finset.sum_mul]
    _ ≤ 3 / 2 * Real.exp (-(2 * k / ((N : ℝ) + 1))) := by
        gcongr
        have := sum_inv_cube_le N hN
        have : 0 ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
        linarith

/-! ### The tail bound (6) -/

/-- The packet contraction factor `z = e^{-2/(N+1)}`. -/
def contraction (N : ℕ) : ℝ := Real.exp (-(2 / ((N : ℝ) + 1)))

theorem contraction_pos (N : ℕ) : 0 < contraction N := Real.exp_pos _

theorem contraction_lt_one (N : ℕ) : contraction N < 1 := by
  unfold contraction
  have : 0 < 2 / ((N : ℝ) + 1) := by positivity
  calc Real.exp (-(2 / ((N : ℝ) + 1))) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    _ = 1 := Real.exp_zero

theorem contraction_pow (N k : ℕ) :
    contraction N ^ k = Real.exp (-(2 * k / ((N : ℝ) + 1))) := by
  unfold contraction
  rw [← Real.exp_nat_mul]
  ring_nf

/-- `(1 - e^{-2/(N+1)})^{-1} ≤ N+1` for `N ≥ 1`. -/
theorem inv_one_sub_contraction_le {N : ℕ} (hN : 1 ≤ N) :
    (1 - contraction N)⁻¹ ≤ (N : ℝ) + 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hu : 0 < 2 / ((N : ℝ) + 1) := by positivity
  have hexp : contraction N * (1 + 2 / ((N : ℝ) + 1)) ≤ 1 := by
    unfold contraction
    have h := Real.add_one_le_exp (2 / ((N : ℝ) + 1))
    have hprod : Real.exp (-(2 / ((N : ℝ) + 1))) * Real.exp (2 / ((N : ℝ) + 1)) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (-(2 / ((N : ℝ) + 1))) * (1 + 2 / ((N : ℝ) + 1))
        ≤ Real.exp (-(2 / ((N : ℝ) + 1))) * Real.exp (2 / ((N : ℝ) + 1)) := by
          gcongr; linarith
      _ = 1 := hprod
  have hlow : 1 / ((N : ℝ) + 1) ≤ 1 - contraction N := by
    have hz := contraction_pos N
    have : contraction N ≤ ((N : ℝ) + 1) / ((N : ℝ) + 3) := by
      rw [le_div_iff₀ (by positivity)]
      have h2 : 1 + 2 / ((N : ℝ) + 1) = ((N : ℝ) + 3) / ((N : ℝ) + 1) := by
        field_simp; ring
      rw [h2] at hexp
      rw [mul_div_assoc', div_le_one (by positivity)] at hexp
      linarith
    have h3 : 1 / ((N : ℝ) + 1) ≤ 1 - ((N : ℝ) + 1) / ((N : ℝ) + 3) := by
      rw [show 1 - ((N : ℝ) + 1) / ((N : ℝ) + 3) = 2 / ((N : ℝ) + 3) by field_simp; ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  have hpos : 0 < 1 - contraction N := by linarith [contraction_lt_one N]
  rw [inv_le_comm₀ hpos (by positivity), ← one_div]
  exact hlow

/-- Weighted square of a packet: `w_k c_k² ≤ (9/4) C(k+5,5) z^{2k}`. -/
theorem weighted_cubicPacket_sq_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (N k : ℕ) :
    binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2 ≤
      9 / 4 * (binomialWeight 6 k * contraction N ^ k) * contraction N ^ k := by
  have hc := abs_cubicPacket_le hδ0 N k
  rw [← contraction_pow] at hc
  have hsq : cubicPacket δ N k ^ 2 ≤ (3 / 2 * contraction N ^ k) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hc 2
  have hw := binomialWeight_mono (show (0 : ℝ) ≤ 5 + δ by linarith)
    (show 5 + δ ≤ (6 : ℝ) by linarith) k
  have hw0 := binomialWeight_nonneg (show (0 : ℝ) ≤ 5 + δ by linarith) k
  calc binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2
      ≤ binomialWeight 6 k * (3 / 2 * contraction N ^ k) ^ 2 :=
        mul_le_mul hw hsq (sq_nonneg _) (hw0.trans hw)
    _ = _ := by ring

theorem summable_binomialWeight_six (N : ℕ) :
    Summable (fun k : ℕ => binomialWeight 6 k * contraction N ^ k) :=
  (binomialWeight_hasSum 6 (by
    rw [abs_of_pos (contraction_pos N)]; exact contraction_lt_one N)).summable

/-- The packet energy series converges. -/
theorem summable_cubicPacket_energy {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (N : ℕ) :
    Summable (fun k : ℕ => binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (binomialWeight_nonneg (by linarith) k) (sq_nonneg _))
    (fun k => (weighted_cubicPacket_sq_le hδ0 hδ1 N k).trans ?_)
    ((summable_binomialWeight_six N).mul_left (9 / 4))
  have h1 : contraction N ^ k ≤ 1 := pow_le_one₀ (contraction_pos N).le (contraction_lt_one N).le
  have h0 : 0 ≤ binomialWeight 6 k * contraction N ^ k :=
    mul_nonneg (binomialWeight_nonneg (by norm_num) k) (pow_nonneg (contraction_pos N).le k)
  nlinarith

/-- **Tail bound (6).**  For `0 ≤ δ ≤ 1`, `N ≥ 1` and every `K`,
`0 ≤ 2^{5+δ} Σ_{k ≥ K} w_k c_k² ≤ 144 (N+1)^6 e^{-2K/(N+1)}`. -/
theorem cubicPacket_tail_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {N : ℕ} (hN : 1 ≤ N) (K : ℕ) :
    0 ≤ 2 ^ (5 + δ) * ∑' j : ℕ, binomialWeight (5 + δ) (j + K) * cubicPacket δ N (j + K) ^ 2 ∧
    2 ^ (5 + δ) * ∑' j : ℕ, binomialWeight (5 + δ) (j + K) * cubicPacket δ N (j + K) ^ 2 ≤
      144 * ((N : ℝ) + 1) ^ 6 * Real.exp (-(2 * K / ((N : ℝ) + 1))) := by
  have hz0 := (contraction_pos N).le
  have hz1 := (contraction_lt_one N).le
  have hterm0 : ∀ j : ℕ, 0 ≤ binomialWeight (5 + δ) (j + K) * cubicPacket δ N (j + K) ^ 2 :=
    fun j => mul_nonneg (binomialWeight_nonneg (by linarith) _) (sq_nonneg _)
  have h2 : (0 : ℝ) < 2 ^ (5 + δ) := by positivity
  have h2le : (2 : ℝ) ^ (5 + δ) ≤ 64 := by
    calc (2 : ℝ) ^ (5 + δ) ≤ 2 ^ ((6 : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by push_cast; linarith)
      _ = 64 := by rw [Real.rpow_natCast]; norm_num
  let G : ℕ → ℝ := fun k => binomialWeight 6 k * contraction N ^ k
  have hG0 : ∀ k, 0 ≤ G k := fun k =>
    mul_nonneg (binomialWeight_nonneg (by norm_num) k) (pow_nonneg hz0 k)
  have hGs : Summable G := summable_binomialWeight_six N
  have hGsum : ∑' k, G k = 1 / (1 - contraction N) ^ (6 : ℝ) :=
    (binomialWeight_hasSum 6 (by rw [abs_of_pos (contraction_pos N)]; exact contraction_lt_one N)).tsum_eq
  have hbound : ∀ j : ℕ, binomialWeight (5 + δ) (j + K) * cubicPacket δ N (j + K) ^ 2 ≤
      9 / 4 * contraction N ^ K * G (j + K) := by
    intro j
    refine (weighted_cubicPacket_sq_le hδ0 hδ1 N (j + K)).trans ?_
    have hzk : contraction N ^ (j + K) ≤ contraction N ^ K :=
      pow_le_pow_of_le_one hz0 hz1 (by omega)
    have := hG0 (j + K)
    calc 9 / 4 * G (j + K) * contraction N ^ (j + K) ≤ 9 / 4 * G (j + K) * contraction N ^ K := by
          gcongr
      _ = _ := by ring
  have hGshift : Summable (fun j => G (j + K)) := (summable_nat_add_iff K).mpr hGs
  have hsumm : Summable (fun j => binomialWeight (5 + δ) (j + K) * cubicPacket δ N (j + K) ^ 2) :=
    Summable.of_nonneg_of_le hterm0 hbound (hGshift.mul_left _)
  have htail_le : ∑' j, G (j + K) ≤ ∑' k, G k := by
    have h := hGs.sum_add_tsum_nat_add K
    have : 0 ≤ ∑ i ∈ range K, G i := sum_nonneg fun i _ => hG0 i
    linarith
  have hinv : 1 / (1 - contraction N) ^ (6 : ℝ) ≤ ((N : ℝ) + 1) ^ 6 := by
    have hpos : 0 < 1 - contraction N := by linarith [contraction_lt_one N]
    have h6 : (1 - contraction N) ^ (6 : ℝ) = (1 - contraction N) ^ 6 := by
      rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h6, one_div, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (inv_one_sub_contraction_le hN) 6
  refine ⟨mul_nonneg h2.le (tsum_nonneg hterm0), ?_⟩
  calc 2 ^ (5 + δ) * ∑' j, binomialWeight (5 + δ) (j + K) * cubicPacket δ N (j + K) ^ 2
      ≤ 64 * ∑' j, (9 / 4 * contraction N ^ K * G (j + K)) := by
        apply mul_le_mul h2le (hsumm.tsum_le_tsum hbound (hGshift.mul_left _))
          (tsum_nonneg hterm0) (by norm_num)
    _ = 144 * contraction N ^ K * ∑' j, G (j + K) := by rw [tsum_mul_left]; ring
    _ ≤ 144 * contraction N ^ K * ((N : ℝ) + 1) ^ 6 := by
        gcongr
        rw [← hGsum] at hinv
        exact htail_le.trans hinv
    _ = _ := by rw [contraction_pow]; ring

/-- Head plus tail: `B(N) = 2^{5+δ} Σ_{k<K} w_k c_k² + 2^{5+δ} Σ_{k ≥ K} w_k c_k²`. -/
theorem routeLCubicEnergy_eq_head_add_tail {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (N K : ℕ) :
    finiteGeneralReciprocalEnergy (3 + δ) δ N =
      2 ^ (5 + δ) * ∑ k ∈ range K, binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2 +
        2 ^ (5 + δ) * ∑' j : ℕ, binomialWeight (5 + δ) (j + K) * cubicPacket δ N (j + K) ^ 2 := by
  rw [routeLCubicEnergy_eq_cubicPacket N hδ0,
    ← (summable_cubicPacket_energy hδ0 hδ1 N).sum_add_tsum_nat_add K]
  ring

/-- The packet horizon `K_P(N) = ⌈((P+6)/2)(N+1) log(N+1)⌉`. -/
def packetHorizon (P : ℝ) (N : ℕ) : ℕ :=
  ⌈(P + 6) / 2 * ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1)⌉₊

/-- Beyond `K_P(N)` the positive tail is at most `144 (N+1)^{-P}`, uniformly in `0 ≤ δ ≤ 1`. -/
theorem cubicPacket_tail_horizon_le (P : ℝ) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    2 ^ (5 + δ) * ∑' j : ℕ, binomialWeight (5 + δ) (j + packetHorizon P N) *
        cubicPacket δ N (j + packetHorizon P N) ^ 2 ≤ 144 * ((N : ℝ) + 1) ^ (-P) := by
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hlog : 0 ≤ Real.log ((N : ℝ) + 1) := Real.log_nonneg (by linarith)
  refine (cubicPacket_tail_le hδ0 hδ1 hN _).2.trans ?_
  have hK : (P + 6) / 2 * ((N : ℝ) + 1) * Real.log ((N : ℝ) + 1) ≤ packetHorizon P N :=
    Nat.le_ceil _
  have hexp : Real.exp (-(2 * (packetHorizon P N : ℝ) / ((N : ℝ) + 1))) ≤
      ((N : ℝ) + 1) ^ (-(P + 6)) := by
    rw [Real.rpow_def_of_pos hN1]
    apply Real.exp_le_exp.mpr
    rw [mul_neg, neg_le_neg_iff, le_div_iff₀ hN1]
    nlinarith
  have h6 : ((N : ℝ) + 1) ^ 6 * ((N : ℝ) + 1) ^ (-(P + 6)) = ((N : ℝ) + 1) ^ (-P) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hN1]
    congr 1
    push_cast
    ring
  calc 144 * ((N : ℝ) + 1) ^ 6 * Real.exp (-(2 * (packetHorizon P N : ℝ) / ((N : ℝ) + 1)))
      ≤ 144 * ((N : ℝ) + 1) ^ 6 * ((N : ℝ) + 1) ^ (-(P + 6)) := by gcongr
    _ = _ := by rw [mul_assoc, h6]

/-- **Finite horizon equivalence.**  On any set of cutoffs `N ≥ 1`, the cubic source is bounded
if and only if its finite packet range `k < K_P(N)` is bounded. -/
theorem routeLCubicEnergy_bounded_iff_horizon {P : ℝ} (hP : 0 < P) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) (S : Set ℕ) (hS : ∀ N ∈ S, 1 ≤ N) :
    (∃ B : ℝ, ∀ N ∈ S, finiteGeneralReciprocalEnergy (3 + δ) δ N ≤ B) ↔
      ∃ B : ℝ, ∀ N ∈ S, 2 ^ (5 + δ) * ∑ k ∈ range (packetHorizon P N),
        binomialWeight (5 + δ) k * cubicPacket δ N k ^ 2 ≤ B := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun N hN => ?_⟩
    have h := routeLCubicEnergy_eq_head_add_tail hδ0 hδ1 N (packetHorizon P N)
    have ht := (cubicPacket_tail_le hδ0 hδ1 (hS N hN) (packetHorizon P N)).1
    linarith [hB N hN]
  · rintro ⟨B, hB⟩
    refine ⟨B + 144, fun N hN => ?_⟩
    have h := routeLCubicEnergy_eq_head_add_tail hδ0 hδ1 N (packetHorizon P N)
    have ht := cubicPacket_tail_horizon_le P hδ0 hδ1 (hS N hN)
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
    have hpow : ((N : ℝ) + 1) ^ (-P) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
    linarith [hB N hN]

end RHTower.DiscretePacket
