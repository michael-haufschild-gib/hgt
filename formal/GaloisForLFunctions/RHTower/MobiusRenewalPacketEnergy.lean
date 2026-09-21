import GaloisForLFunctions.RHTower.MobiusPacketDifferenceSign
import Mathlib.Analysis.Analytic.Binomial

/-!
# Exact binomial packet energy of finite Möbius renewal

The finite Gamma--Hankel energy of any real finite source is exactly a positive
binomially weighted sum of squares of its literal additive packets.  Specialising
the source to the Möbius coefficients gives the packet decomposition of the
finite Möbius--Laplace energy.  This is an identity, not an energy estimate:
the unresolved Route E problem is bounding this signed packet square sum in the
critical range.
-/

open Filter Topology Finset
open scoped BigOperators

noncomputable section

namespace RHTower.MobiusRenewalPacketEnergy

/-- Generalised binomial weight in the additive-kernel packet expansion. -/
def binomialWeight (r : ℝ) (k : ℕ) : ℝ := Ring.choose (r + k - 1) k

/-- Generalised binomial weights are nonnegative at every nonnegative order. -/
theorem binomialWeight_nonneg {r : ℝ} (hr : 0 ≤ r) (k : ℕ) :
    0 ≤ binomialWeight r k := by
  unfold binomialWeight
  rw [Ring.choose_eq_smul]
  apply smul_nonneg
  · positivity
  · have h : 0 ≤ (descPochhammer ℝ k).eval (r + k - 1) := by
      apply descPochhammer_nonneg
      linarith
    have heq : (descPochhammer ℤ k).smeval (r + k - 1) =
        (descPochhammer ℝ k).eval (r + k - 1) := by
      rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
      rw [← Polynomial.eval_map, descPochhammer_map]
    rwa [heq]

/-- Literal packet of a finite real source. -/
def sourcePacket (a : ℕ → ℝ) (N : ℕ) (r : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ range N, a n * MobiusPacketDifference.weight r n * MobiusPacketDifference.node n ^ k

/-- Every packet summand has nonnegative energy weight at positive order. -/
theorem packetSquareTerm_nonneg (a : ℕ → ℝ) (N : ℕ) {r : ℝ} (hr : 0 < r) (k : ℕ) :
    0 ≤ Real.Gamma r * 2 ^ r * binomialWeight r k * (sourcePacket a N r k) ^ 2 := by
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (le_of_lt (Real.Gamma_pos_of_pos hr))
        (le_of_lt (Real.rpow_pos_of_pos (by norm_num) r)))
      (binomialWeight_nonneg hr.le k))
    (sq_nonneg _)

private theorem node_nonneg (n : ℕ) : 0 ≤ MobiusPacketDifference.node n := by
  unfold MobiusPacketDifference.node
  positivity

private theorem node_lt_one (n : ℕ) : MobiusPacketDifference.node n < 1 := by
  unfold MobiusPacketDifference.node
  apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)).2
  have h : (n : ℝ) < (n : ℝ) + 2 := by linarith
  exact h

private theorem binomial_hasSum (r q : ℝ) (hq : |q| < 1) :
    HasSum (fun k : ℕ => binomialWeight r k * q ^ k) (1 / (1 - q) ^ r) := by
  have h := (Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero r).hasSum
    (show q ∈ Metric.eball (0 : ℝ) 1 by
      rw [Metric.mem_eball]
      simpa [edist_dist, Real.dist_eq] using hq)
  simpa [binomialWeight, FormalMultilinearSeries.ofScalars] using h

private theorem additive_packet_hasSum (r : ℝ) (m n : ℕ) :
    HasSum (fun k : ℕ => binomialWeight r k *
      (MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ k)
      (1 / (1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ r) := by
  apply binomial_hasSum
  rw [abs_of_nonneg (mul_nonneg (node_nonneg m) (node_nonneg n))]
  calc
    MobiusPacketDifference.node m * MobiusPacketDifference.node n ≤
        1 * MobiusPacketDifference.node n :=
      mul_le_mul_of_nonneg_right (le_of_lt (node_lt_one m)) (node_nonneg n)
    _ = MobiusPacketDifference.node n := one_mul _
    _ < 1 := node_lt_one n

private theorem additive_kernel_factor (m n : ℕ) :
    ((m + n + 2 : ℕ) : ℝ) =
      ((((m : ℝ) + 2) * ((n : ℝ) + 2)) / 2) *
        (1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n) := by
  unfold MobiusPacketDifference.node
  field_simp
  push_cast
  ring

/-- One additive Hankel kernel is its convergent literal-packet expansion. -/
theorem additiveKernel_packetExpansion (r : ℝ) (m n : ℕ) :
    1 / (((m + n + 2 : ℕ) : ℝ) ^ r) =
      2 ^ r * MobiusPacketDifference.weight r m * MobiusPacketDifference.weight r n *
        ∑' k : ℕ, binomialWeight r k *
          (MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ k := by
  rw [(additive_packet_hasSum r m n).tsum_eq]
  rw [additive_kernel_factor]
  have hm : 0 < (m : ℝ) + 2 := by positivity
  have hn : 0 < (n : ℝ) + 2 := by positivity
  have hmn : MobiusPacketDifference.node m * MobiusPacketDifference.node n < 1 := by
    calc
      MobiusPacketDifference.node m * MobiusPacketDifference.node n ≤
          1 * MobiusPacketDifference.node n :=
        mul_le_mul_of_nonneg_right (le_of_lt (node_lt_one m)) (node_nonneg n)
      _ = MobiusPacketDifference.node n := one_mul _
      _ < 1 := node_lt_one n
  have hq : 0 < 1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n := by
    linarith
  unfold MobiusPacketDifference.weight
  rw [Real.mul_rpow (by positivity) hq.le,
    Real.div_rpow (mul_nonneg hm.le hn.le) (by norm_num) r,
    Real.mul_rpow hm.le hn.le]
  have htwo : (2 : ℝ) ^ r ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) r).ne'
  have hmpow : ((m : ℝ) + 2) ^ r ≠ 0 := (Real.rpow_pos_of_pos hm r).ne'
  have hnpow : ((n : ℝ) + 2) ^ r ≠ 0 := (Real.rpow_pos_of_pos hn r).ne'
  have hqpow : (1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ r ≠ 0 :=
    (Real.rpow_pos_of_pos hq r).ne'
  field_simp
  rw [show ((m : ℝ) + 2) ^ r * ((n : ℝ) + 2) ^ r *
      ((m : ℝ) + 2) ^ (-r) * ((n : ℝ) + 2) ^ (-r) =
      ((((m : ℝ) + 2) ^ r * ((m : ℝ) + 2) ^ (-r)) *
        (((n : ℝ) + 2) ^ r * ((n : ℝ) + 2) ^ (-r))) by ring,
    ← Real.rpow_add hm, ← Real.rpow_add hn]
  norm_num

private theorem packet_square_expand (a : ℕ → ℝ) (N : ℕ) (r : ℝ) (k : ℕ) :
    (∑ m ∈ range N, ∑ n ∈ range N,
      a m * a n * 2 ^ r * MobiusPacketDifference.weight r m *
        MobiusPacketDifference.weight r n *
        (binomialWeight r k *
          (MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ k)) =
      2 ^ r * binomialWeight r k * (sourcePacket a N r k) ^ 2 := by
  symm
  unfold sourcePacket
  rw [pow_two, Finset.sum_mul_sum, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_pow]
  ring

private theorem finite_packet_hasSum (a : ℕ → ℝ) (N : ℕ) (r : ℝ) :
    HasSum (fun k : ℕ => 2 ^ r * binomialWeight r k * (sourcePacket a N r k) ^ 2)
      (∑ m ∈ range N, ∑ n ∈ range N,
        a m * a n * 2 ^ r * MobiusPacketDifference.weight r m *
          MobiusPacketDifference.weight r n *
          (1 / (1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ r)) := by
  have hterm (m n : ℕ) :
      HasSum (fun k : ℕ =>
        a m * a n * 2 ^ r * MobiusPacketDifference.weight r m *
          MobiusPacketDifference.weight r n *
          (binomialWeight r k *
            (MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ k))
        (a m * a n * 2 ^ r * MobiusPacketDifference.weight r m *
          MobiusPacketDifference.weight r n *
          (1 / (1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ r)) :=
    (additive_packet_hasSum r m n).mul_left _
  have hrow (m : ℕ) (hm : m ∈ range N) :
      HasSum (fun k : ℕ => ∑ n ∈ range N,
        a m * a n * 2 ^ r * MobiusPacketDifference.weight r m *
          MobiusPacketDifference.weight r n *
          (binomialWeight r k *
            (MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ k))
        (∑ n ∈ range N,
          a m * a n * 2 ^ r * MobiusPacketDifference.weight r m *
            MobiusPacketDifference.weight r n *
            (1 / (1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ r)) := by
    exact hasSum_sum fun n _ => hterm m n
  have hsum := hasSum_sum (s := range N) hrow
  simpa only [packet_square_expand] using hsum

private theorem additive_kernel_packet_factor (r : ℝ) (m n : ℕ) :
    1 / (((m + n + 2 : ℕ) : ℝ) ^ r) =
      2 ^ r * MobiusPacketDifference.weight r m * MobiusPacketDifference.weight r n *
        (1 / (1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ r) := by
  rw [← (additive_packet_hasSum r m n).tsum_eq]
  exact additiveKernel_packetExpansion r m n

/-- Exact positive packet decomposition of any finite real Gamma--Hankel energy. -/
theorem finiteGammaHankelEnergy_packetExpansion (a : ℕ → ℝ) (N : ℕ) (r : ℝ) :
    finiteGammaHankelEnergy a N r = Real.Gamma r * 2 ^ r * ∑' k : ℕ,
      binomialWeight r k * (sourcePacket a N r k) ^ 2 := by
  have hkernel :
      (∑ m ∈ range N, ∑ n ∈ range N,
        a m * a n / (((m + n + 2 : ℕ) : ℝ) ^ r) =
      ∑ m ∈ range N, ∑ n ∈ range N,
        a m * a n *
          (2 ^ r * MobiusPacketDifference.weight r m *
            MobiusPacketDifference.weight r n *
            (1 / (1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ r))) := by
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    rw [div_eq_mul_inv]
    rw [← one_div]
    rw [additive_kernel_packet_factor]
  have hnormal :
      (∑ m ∈ range N, ∑ n ∈ range N,
        a m * a n *
          (2 ^ r * MobiusPacketDifference.weight r m *
            MobiusPacketDifference.weight r n *
            (1 / (1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ r))) =
      ∑ m ∈ range N, ∑ n ∈ range N,
        a m * a n * 2 ^ r * MobiusPacketDifference.weight r m *
          MobiusPacketDifference.weight r n *
          (1 / (1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ r) := by
    apply Finset.sum_congr rfl
    intro m hm
    apply Finset.sum_congr rfl
    intro n hn
    ring
  unfold finiteGammaHankelEnergy
  rw [hkernel, hnormal, ← (finite_packet_hasSum a N r).tsum_eq]
  have hfun : (fun k : ℕ =>
      2 ^ r * binomialWeight r k * (sourcePacket a N r k) ^ 2) =
      (fun k : ℕ => 2 ^ r *
        (binomialWeight r k * (sourcePacket a N r k) ^ 2)) := by
    funext k
    ring
  rw [hfun, tsum_mul_left]
  ring

/-- The generic packet in the preceding theorem is exactly the literal Möbius packet. -/
theorem sourcePacket_eq_mobiusPacket (N : ℕ) (r : ℝ) (k : ℕ) :
    sourcePacket shiftedMobiusRealCoefficient N r k = MobiusPacketDifference.packet N r k := by
  rfl

/-- Exact binomial packet decomposition of finite Möbius--Laplace energy. -/
theorem finiteMobiusGammaHankelEnergy_packetExpansion (N : ℕ) (r : ℝ) :
    finiteMobiusGammaHankelEnergy N r = Real.Gamma r * 2 ^ r * ∑' k : ℕ,
      binomialWeight r k * (MobiusPacketDifference.packet N r k) ^ 2 := by
  simpa only [finiteMobiusGammaHankelEnergy, sourcePacket_eq_mobiusPacket] using
    finiteGammaHankelEnergy_packetExpansion shiftedMobiusRealCoefficient N r

end RHTower.MobiusRenewalPacketEnergy
