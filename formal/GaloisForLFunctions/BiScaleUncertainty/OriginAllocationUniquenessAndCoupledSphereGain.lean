import GaloisForLFunctions.BiScaleUncertainty.OptimalOriginAllocation
import GaloisForLFunctions.BiScaleUncertainty.MultiChainToeplitzGramCoupling

/-!
# Uniqueness of Optimal Origin Allocation, Square-Root Coupled Sphere Gain & Odd-Dyadic Incommensurability

This module closes the structural characterization problems in `OriginCollarTransport.md`,
`quantitative-constant.md` §2, and `MultiChainGramLedger.md`:

1. **Exact Lagrange Identity & Uniqueness (`↔`) of Optimal Origin Allocation (§1):**
   - For any pair $(W, A)$ and $(a, q)$, the Cauchy–Schwarz deficit satisfies the exact Lagrange
     identity (`origin_pair_lagrange_defect`):
     $$(W^2 + A^2)(a^2 + q^2) - (W a + A q)^2 = (A a - W q)^2.$$
   - Consequently, for $W > 0$, $A > 0$, and $q \ge 0$, equality holds in `origin_pair_support`
     if and only if $A a = W q$ (`origin_pair_support_eq_iff`).
   - Summing over any finite index set $s$, the triangle lower bound
     $\sqrt{(\sum_i a_i)^2 + (\sum_i q_i)^2} \le \sum_i \sqrt{a_i^2 + q_i^2}$ is attained
     ($W = \sum_i a_i > 0$, $A = \sum_i q_i > 0$, $q_i \ge 0$) **if and only if** the origin shares
     are strictly proportional to the block norms: $\forall i \in s,\; A a_i = W q_i$
     (`origin_allocation_cost_eq_lower_iff`, `origin_allocation_unique_minimizer_iff`).

2. **Square-Root Coupled Sphere Gain & Collinearity Characterization (`↔`) (§2):**
   - For any finite family of Hilbert-space packets $p : \iota \to E$ and total origin weight
     $W \ge 0$, the **coupled sphere gain** over the optimal independent partition is
     $$\operatorname{coupledSphereGain}(W, s, p)
       := \sqrt{W^2 + \left(\sum_{i \in s} \|p_i\|\right)^2}
         - \sqrt{W^2 + \left\|\sum_{i \in s} p_i\right\|^2}.$$
   - The difference of squares equals `packetPartitionLoss s p`
     (`coupledSphereGain_sq_diff_eq_packetPartitionLoss`), so `coupledSphereGain W s p ≥ 0`
     (`coupledSphereGain_nonneg`), and **every** independent origin allocation $\sum_{i \in s} a_i = W$
     exceeds the coupled sphere penalty by at least `coupledSphereGain W s p`
     (`coupled_sphere_penalty_le_any_allocation`).
   - Moreover, `coupledSphereGain W s p = 0` **if and only if** all packet pairs are positively
     aligned: $\forall i \in s,\, \forall j \in s,\; \|p_j\| \bullet p_i = \|p_i\| \bullet p_j$
     (`coupledSphereGain_eq_zero_iff`).

3. **Diophantine Odd-Dyadic Incommensurability (§3):**
   - For every $q \in \mathbb{N}$, positive step $k \ge 1$, and integer $n \in \mathbb{N}$,
     $$(2q + 3)^k \ne n \cdot 2^k,$$
     and therefore every non-zero multiple $k \log((2q + 3)/2)$ of an odd-dyadic logarithmic step
     is strictly disjoint from the entire integer logarithmic grid $\{\log n : n \in \mathbb{N}\}$
     (`odd_dyadic_log_progression_ne_log_nat`).
-/

open scoped BigOperators InnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

set_option autoImplicit false

variable {ι : Type*}

/-! ## §1. Exact Lagrange Identity & Uniqueness (`↔`) of Optimal Origin Allocation -/

/-- Two-variable Lagrange identity for the origin-allocation support inequality:
$$(W^2 + A^2)(a^2 + q^2) - (W a + A q)^2 = (A a - W q)^2.$$ -/
theorem origin_pair_lagrange_defect (W A a q : ℝ) :
    (W ^ 2 + A ^ 2) * (a ^ 2 + q ^ 2) - (W * a + A * q) ^ 2 =
      (A * a - W * q) ^ 2 := by
  ring

/-- For `W > 0`, `A > 0`, and `q ≥ 0`, equality holds in `origin_pair_support` if and only if
`A * a = W * q`. -/
theorem origin_pair_support_eq_iff {W A a q : ℝ}
    (hW : 0 < W) (hA : 0 < A) (hq : 0 ≤ q) :
    W * a + A * q = Real.sqrt (W ^ 2 + A ^ 2) * Real.sqrt (a ^ 2 + q ^ 2) ↔
      A * a = W * q := by
  constructor
  · intro heq
    have hsq :
        (W * a + A * q) ^ 2 =
          (W ^ 2 + A ^ 2) * (a ^ 2 + q ^ 2) := by
      calc
        (W * a + A * q) ^ 2 =
            (Real.sqrt (W ^ 2 + A ^ 2) * Real.sqrt (a ^ 2 + q ^ 2)) ^ 2 := by rw [heq]
        _ = Real.sqrt (W ^ 2 + A ^ 2) ^ 2 * Real.sqrt (a ^ 2 + q ^ 2) ^ 2 := by ring
        _ = (W ^ 2 + A ^ 2) * (a ^ 2 + q ^ 2) := by
          rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    have hlag := origin_pair_lagrange_defect W A a q
    have hzero : (A * a - W * q) ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  · intro hprop
    have ha : a = W * q / A := by
      have hAne : A ≠ 0 := hA.ne'
      field_simp [hAne]
      linarith
    have ha_nonneg : 0 ≤ a := by
      rw [ha]
      positivity
    have hWA_nonneg : 0 ≤ W * a + A * q := by positivity
    have hsq :
        (W * a + A * q) ^ 2 =
          (Real.sqrt (W ^ 2 + A ^ 2) * Real.sqrt (a ^ 2 + q ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
      have hlag := origin_pair_lagrange_defect W A a q
      have h0 : A * a - W * q = 0 := sub_eq_zero.mpr hprop
      nlinarith
    have hsqrt := congrArg Real.sqrt hsq
    rwa [Real.sqrt_sq hWA_nonneg,
      Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))] at hsqrt

/-- **Uniqueness (`↔`) of Optimal Origin Allocation:**
For any finite index set `s`, nonnegative block sizes `q i ≥ 0` with positive total
`A = ∑ i ∈ s, q i > 0`, and origin weights `a i` with positive total `W = ∑ i ∈ s, a i > 0`,
the triangle lower bound is attained if and only if `A * a i = W * q i` for every `i ∈ s`. -/
theorem origin_allocation_cost_eq_lower_iff (s : Finset ι) (a q : ι → ℝ)
    (hq : ∀ i ∈ s, 0 ≤ q i)
    (hW : 0 < ∑ i ∈ s, a i) (hA : 0 < ∑ i ∈ s, q i) :
    (∑ i ∈ s, Real.sqrt (a i ^ 2 + q i ^ 2)) =
      Real.sqrt ((∑ i ∈ s, a i) ^ 2 + (∑ i ∈ s, q i) ^ 2) ↔
      ∀ i ∈ s, (∑ k ∈ s, q k) * a i = (∑ k ∈ s, a k) * q i := by
  set W := ∑ i ∈ s, a i
  set A := ∑ i ∈ s, q i
  set S := Real.sqrt (W ^ 2 + A ^ 2)
  have hS_pos : 0 < S := Real.sqrt_pos.mpr (by positivity)
  have hSsq : S ^ 2 = W ^ 2 + A ^ 2 := Real.sq_sqrt (by positivity)
  have hterm_nonneg : ∀ i ∈ s, 0 ≤ S * Real.sqrt (a i ^ 2 + q i ^ 2) - (W * a i + A * q i) :=
    fun i _ => sub_nonneg.mpr (origin_pair_support W A (a i) (q i))
  have hsum_ident :
      (∑ i ∈ s, (S * Real.sqrt (a i ^ 2 + q i ^ 2) - (W * a i + A * q i))) =
        S * ((∑ i ∈ s, Real.sqrt (a i ^ 2 + q i ^ 2)) - S) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have heq : (∑ i ∈ s, (W * a i + A * q i)) = W ^ 2 + A ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      dsimp [W, A]
      ring
    rw [heq, ← hSsq]
    ring
  constructor
  · intro heq i hi
    have hsum0 :
        (∑ j ∈ s, (S * Real.sqrt (a j ^ 2 + q j ^ 2) - (W * a j + A * q j))) = 0 := by
      rw [hsum_ident, heq, sub_self, mul_zero]
    have hterm0 :
        S * Real.sqrt (a i ^ 2 + q i ^ 2) - (W * a i + A * q i) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mp hsum0 i hi
    exact (origin_pair_support_eq_iff hW hA (hq i hi)).mp (sub_eq_zero.mp hterm0).symm
  · intro hall
    have hsum0 :
        (∑ j ∈ s, (S * Real.sqrt (a j ^ 2 + q j ^ 2) - (W * a j + A * q j))) = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg hterm_nonneg).mpr ?_
      intro i hi
      have hpair := (origin_pair_support_eq_iff hW hA (hq i hi)).mpr (hall i hi)
      linarith
    rw [hsum_ident, mul_eq_zero] at hsum0
    rcases hsum0 with hS0 | hdiff0
    · exact absurd hS0 hS_pos.ne'
    · exact sub_eq_zero.mp hdiff0

/-- **Unique Minimizer Characterization for `originAllocationShare` (`↔`):**
When `W > 0` and `∑ i, |q i| > 0`, an allocation `a : Fin (n + 1) → ℝ` with `∑ i, a i = W`
attains the minimum cost `√(W² + (∑ i, |q i|)²)` if and only if
`a i = W * originAllocationShare n q i` for every `i`. -/
theorem origin_allocation_unique_minimizer_iff (n : ℕ) {W : ℝ} (hW : 0 < W)
    (q : Fin (n + 1) → ℝ) (hQ : 0 < ∑ i : Fin (n + 1), |q i|)
    (a : Fin (n + 1) → ℝ) (ha : (∑ i : Fin (n + 1), a i) = W) :
    (∑ i : Fin (n + 1), Real.sqrt (a i ^ 2 + q i ^ 2)) =
      Real.sqrt (W ^ 2 + (∑ i : Fin (n + 1), |q i|) ^ 2) ↔
      ∀ i : Fin (n + 1), a i = W * originAllocationShare n q i := by
  have hW' : 0 < ∑ i : Fin (n + 1), a i := by linarith
  have hiff := origin_allocation_cost_eq_lower_iff Finset.univ a (fun i => |q i|)
    (fun i _ => abs_nonneg (q i)) hW' hQ
  simp only [sq_abs, ha, Finset.mem_univ, true_implies] at hiff
  rw [hiff]
  have hQne : (∑ k : Fin (n + 1), |q k|) ≠ 0 := hQ.ne'
  constructor
  · intro hprop i
    simp only [originAllocationShare, hQne, ↓reduceIte]
    have hi := hprop i
    field_simp [hQne]
    linarith
  · intro hall i
    have hi := hall i
    simp only [originAllocationShare, hQne, ↓reduceIte] at hi
    rw [hi]
    field_simp [hQne]

/-! ## §2. Square-Root Coupled Sphere Gain & Collinearity Characterization -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **square-root coupled sphere gain** achieved by combining a family of Hilbert-space packets
`p : ι → E` before applying the origin-collar sphere penalty at total origin weight `W`:
$$\operatorname{coupledSphereGain}(W, s, p)
  := \sqrt{W^2 + \left(\sum_{i \in s} \|p_i\|\right)^2}
    - \sqrt{W^2 + \left\|\sum_{i \in s} p_i\right\|^2}.$$ -/
def coupledSphereGain (W : ℝ) (s : Finset ι) (p : ι → E) : ℝ :=
  Real.sqrt (W ^ 2 + (∑ i ∈ s, ‖p i‖) ^ 2) -
    Real.sqrt (W ^ 2 + ‖∑ i ∈ s, p i‖ ^ 2)

omit [InnerProductSpace ℝ E] in
/-- Exact identity between the difference of squares of the partitioned and coupled sphere
penalties and `packetPartitionLoss s p`. -/
theorem coupledSphereGain_sq_diff_eq_packetPartitionLoss (W : ℝ) (s : Finset ι) (p : ι → E) :
    Real.sqrt (W ^ 2 + (∑ i ∈ s, ‖p i‖) ^ 2) ^ 2 -
        Real.sqrt (W ^ 2 + ‖∑ i ∈ s, p i‖ ^ 2) ^ 2 =
      packetPartitionLoss s p := by
  rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  unfold packetPartitionLoss
  ring

omit [InnerProductSpace ℝ E] in
/-- Conjugate-radical formula for `coupledSphereGain W s p`. -/
theorem coupledSphereGain_mul_sum_eq_packetPartitionLoss (W : ℝ) (s : Finset ι) (p : ι → E) :
    coupledSphereGain W s p *
        (Real.sqrt (W ^ 2 + (∑ i ∈ s, ‖p i‖) ^ 2) +
          Real.sqrt (W ^ 2 + ‖∑ i ∈ s, p i‖ ^ 2)) =
      packetPartitionLoss s p := by
  unfold coupledSphereGain
  calc
    (Real.sqrt (W ^ 2 + (∑ i ∈ s, ‖p i‖) ^ 2) - Real.sqrt (W ^ 2 + ‖∑ i ∈ s, p i‖ ^ 2)) *
        (Real.sqrt (W ^ 2 + (∑ i ∈ s, ‖p i‖) ^ 2) + Real.sqrt (W ^ 2 + ‖∑ i ∈ s, p i‖ ^ 2)) =
      Real.sqrt (W ^ 2 + (∑ i ∈ s, ‖p i‖) ^ 2) ^ 2 -
        Real.sqrt (W ^ 2 + ‖∑ i ∈ s, p i‖ ^ 2) ^ 2 := by ring
    _ = packetPartitionLoss s p := coupledSphereGain_sq_diff_eq_packetPartitionLoss W s p

/-- The coupled sphere gain is always nonnegative (`0 ≤ coupledSphereGain W s p`). -/
theorem coupledSphereGain_nonneg (W : ℝ) (s : Finset ι) (p : ι → E) :
    0 ≤ coupledSphereGain W s p := by
  unfold coupledSphereGain
  rw [sub_nonneg]
  apply Real.sqrt_le_sqrt
  have hloss := packetPartitionLoss_nonneg s p
  unfold packetPartitionLoss at hloss
  linarith

omit [InnerProductSpace ℝ E] in
/-- **Universal Dominance of Joint Coupling Over Every Independent Origin Allocation:**
For any origin allocation `a : ι → ℝ` with `∑ i ∈ s, a i = W`, the sum of individual block
sphere penalties exceeds the coupled sphere penalty by at least `coupledSphereGain W s p`. -/
theorem coupled_sphere_penalty_le_any_allocation (W : ℝ) (s : Finset ι) (p : ι → E)
    (a : ι → ℝ) (ha : (∑ i ∈ s, a i) = W) :
    Real.sqrt (W ^ 2 + ‖∑ i ∈ s, p i‖ ^ 2) + coupledSphereGain W s p ≤
      ∑ i ∈ s, Real.sqrt (a i ^ 2 + ‖p i‖ ^ 2) := by
  have hadd :
      Real.sqrt (W ^ 2 + ‖∑ i ∈ s, p i‖ ^ 2) + coupledSphereGain W s p =
        Real.sqrt (W ^ 2 + (∑ i ∈ s, ‖p i‖) ^ 2) := by
    unfold coupledSphereGain
    ring
  rw [hadd, ← ha]
  exact origin_allocation_cost_lower s a (fun i => ‖p i‖)

/-- **Exact Zero-Gain Collinearity Equivalence (`↔`):**
The coupled sphere gain vanishes if and only if all packet pairs in `s` are positively aligned
(`∀ i ∈ s, ∀ j ∈ s, ‖p j‖ • p i = ‖p i‖ • p j`). -/
theorem coupledSphereGain_eq_zero_iff (W : ℝ) (s : Finset ι) (p : ι → E) :
    coupledSphereGain W s p = 0 ↔
      ∀ i ∈ s, ∀ j ∈ s, ‖p j‖ • p i = ‖p i‖ • p j := by
  rw [← packetPartitionLoss_eq_zero_iff s p]
  constructor
  · intro h0
    rw [← coupledSphereGain_mul_sum_eq_packetPartitionLoss W s p, h0, zero_mul]
  · intro hloss
    have hmul := coupledSphereGain_mul_sum_eq_packetPartitionLoss W s p
    rw [hloss, mul_eq_zero] at hmul
    rcases hmul with h0 | hsum0
    · exact h0
    · have h1 : 0 ≤ Real.sqrt (W ^ 2 + (∑ i ∈ s, ‖p i‖) ^ 2) := Real.sqrt_nonneg _
      have h2 : 0 ≤ Real.sqrt (W ^ 2 + ‖∑ i ∈ s, p i‖ ^ 2) := Real.sqrt_nonneg _
      unfold coupledSphereGain
      linarith

/-! ## §3. Diophantine Odd-Dyadic Incommensurability -/

/-- Every integer of the form `2 * q + 3` is coprime to `2`. -/
theorem coprime_two_mul_add_three_two (q : ℕ) :
    Nat.Coprime (2 * q + 3) 2 := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  omega

/-- **Diophantine Odd-Dyadic Power Incommensurability:**
For every `q : ℕ`, positive exponent `k ≥ 1`, and integer `n : ℕ`,
$$(2q + 3)^k \ne n \cdot 2^k.$$ -/
theorem odd_pow_ne_mul_two_pow (q : ℕ) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (2 * q + 3) ^ k ≠ n * 2 ^ k := by
  intro heq
  have hcop : Nat.Coprime ((2 * q + 3) ^ k) (2 ^ k) :=
    (coprime_two_mul_add_three_two q).pow k k
  have hdvd : 2 ^ k ∣ (2 * q + 3) ^ k := ⟨n, by linarith⟩
  have hdvd1 : 2 ^ k ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hdvd dvd_rfl
  have hle1 : 2 ^ k ≤ 1 := Nat.le_of_dvd zero_lt_one hdvd1
  have hge2 : 2 ≤ 2 ^ k := by
    calc
      2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  omega

/-- **Logarithmic Incommensurability of Odd-Dyadic Chains and the Integer Logarithmic Grid:**
For every `q : ℕ`, positive step index `k ≥ 1`, and integer `n : ℕ`, the `k`-th multiple of the
odd-dyadic step `log((2q + 3) / 2)` never coincides with `log n`:
$$(k : \mathbb{R}) \cdot \log\!\left(\frac{2q + 3}{2}\right) \ne \log(n : \mathbb{R}).$$ -/
theorem odd_dyadic_log_progression_ne_log_nat (q : ℕ) {k : ℕ} (hk : 1 ≤ k) (n : ℕ) :
    (k : ℝ) * Real.log (((2 * q + 3 : ℕ) : ℝ) / 2) ≠ Real.log (n : ℝ) := by
  have hodd_pos : (0 : ℝ) < ((2 * q + 3 : ℕ) : ℝ) := by positivity
  have hratio_gt_one : (1 : ℝ) < ((2 * q + 3 : ℕ) : ℝ) / 2 := by
    rw [one_lt_div two_pos]
    exact_mod_cast (show 2 < 2 * q + 3 by omega)
  have hratio_pos : (0 : ℝ) < ((2 * q + 3 : ℕ) : ℝ) / 2 := by linarith
  by_cases hn0 : n = 0
  · subst hn0
    rw [Nat.cast_zero, Real.log_zero]
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    exact (mul_pos hk_pos (Real.log_pos hratio_gt_one)).ne'
  · intro heq
    have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hexp := congrArg Real.exp heq
    rw [Real.exp_nat_mul, Real.exp_log hratio_pos, Real.exp_log hn_pos, div_pow] at hexp
    have h2k_ne : (2 : ℝ) ^ k ≠ 0 := pow_ne_zero k two_ne_zero
    have hmul : (((2 * q + 3 : ℕ) : ℝ) ^ k) = (n : ℝ) * (2 : ℝ) ^ k :=
      (div_eq_iff h2k_ne).mp hexp
    have hnat : (2 * q + 3) ^ k = n * 2 ^ k := by exact_mod_cast hmul
    exact odd_pow_ne_mul_two_pow q hk n hnat

end

end GaloisForLFunctions.BiScaleUncertainty
