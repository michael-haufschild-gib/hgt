import GaloisForLFunctions.RHTower.SquareSampledDivisorLogKernel
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound

set_option autoImplicit false
open scoped BigOperators
open Finset

namespace RHTower

/-- Cutoff geometry retains the fourth-root dependence on the dilation. -/
theorem squareSampledHyperbolaCutoff_geometry (N : ℕ) {q : ℕ} (hq : 0 < q) :
    (q * squareSampledHyperbolaCutoff N q : ℕ) ≤ (N : ℝ) * Real.sqrt q ∧
    ((N : ℝ) + (q * squareSampledHyperbolaCutoff N q : ℕ)) *
        Real.sqrt (squareSampledHyperbolaCutoff N q) ≤
      2 * (N : ℝ) * Real.sqrt N * Real.sqrt (Real.sqrt q) := by
  let D := squareSampledHyperbolaCutoff N q
  have hcut : D * D ≤ (N - 1) ^ 2 / q := Nat.sqrt_le _
  have hbaseNat : q * D ^ 2 ≤ N ^ 2 := by
    have h := (Nat.le_div_iff_mul_le hq).mp hcut
    have hp : N - 1 ≤ N := Nat.sub_le N 1
    nlinarith
  have hbase : (q : ℝ) * (D : ℝ) ^ 2 ≤ (N : ℝ) ^ 2 := by exact_mod_cast hbaseNat
  have hDsq : D * D ≤ N ^ 2 := by
    apply hcut.trans
    exact (Nat.div_le_self _ _).trans (by have := Nat.sub_le N 1; nlinarith)
  have hDN : D ≤ N := by nlinarith
  have hroot : Real.sqrt q * (D : ℝ) ≤ N := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)] using hbase
  have hqD : (q : ℝ) * D ≤ (N : ℝ) * Real.sqrt q := by
    calc
      (q : ℝ) * D = Real.sqrt q * (Real.sqrt q * D) := by
        rw [← mul_assoc, ← pow_two, Real.sq_sqrt (Nat.cast_nonneg q)]
      _ ≤ Real.sqrt q * N := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg _)
      _ = _ := mul_comm _ _
  have hsecond : Real.sqrt q * Real.sqrt D ≤ Real.sqrt N * Real.sqrt (Real.sqrt q) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simpa only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg q),
      Real.sq_sqrt (Nat.cast_nonneg D), Real.sq_sqrt (Nat.cast_nonneg N),
      Real.sq_sqrt (Real.sqrt_nonneg (q : ℝ))] using hqD
  have hlarge : (q : ℝ) * D * Real.sqrt D ≤
      (N : ℝ) * Real.sqrt N * Real.sqrt (Real.sqrt q) := by
    calc
      (q : ℝ) * D * Real.sqrt D =
          (Real.sqrt q * D) * (Real.sqrt q * Real.sqrt D) := by
        calc
          _ = (Real.sqrt q) ^ 2 * D * Real.sqrt D := by rw [Real.sq_sqrt (Nat.cast_nonneg q)]
          _ = _ := by ring
      _ ≤ (N : ℝ) * (Real.sqrt N * Real.sqrt (Real.sqrt q)) :=
        mul_le_mul hroot hsecond (by positivity) (by positivity)
      _ = _ := by ring
  have hqroot : (1 : ℝ) ≤ Real.sqrt (Real.sqrt q) := by
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
    have h1 : (1 : ℝ) ≤ Real.sqrt q := by simpa using Real.sqrt_le_sqrt hq1
    simpa using Real.sqrt_le_sqrt h1
  have hsmall : (N : ℝ) * Real.sqrt D ≤
      (N : ℝ) * Real.sqrt N * Real.sqrt (Real.sqrt q) := by
    calc
      _ ≤ (N : ℝ) * Real.sqrt N :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hDN)) (by positivity)
      _ = ((N : ℝ) * Real.sqrt N) * 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hqroot (by positivity)
  change ((q * D : ℕ) : ℝ) ≤ _ ∧ ((N : ℝ) + (q * D : ℕ)) * Real.sqrt D ≤ _
  push_cast
  exact ⟨hqD, by nlinarith⟩

theorem squareSampledDivisorRemainderBound_le_product_envelope
    (N : ℕ) {q Q : ℕ} (hq : 0 < q) (hqQ : q ≤ Q) :
    squareSampledDivisorRemainderBound N q ≤
      (N : ℝ) * (7 + 2 * Real.log ((N : ℝ) ^ 2 + 1)) +
      32 * (N : ℝ) * Real.sqrt N * Real.sqrt (Real.sqrt Q) *
        (1 + Real.log (1 + (N : ℝ) * Real.sqrt Q)) ^ 4 := by
  have hg := squareSampledHyperbolaCutoff_geometry N hq
  have hqQ' : (q : ℝ) ≤ Q := by exact_mod_cast hqQ
  have hroot := Real.sqrt_le_sqrt hqQ'
  have hroot2 := Real.sqrt_le_sqrt hroot
  have hR : ((q * squareSampledHyperbolaCutoff N q : ℕ) : ℝ) ≤
      (N : ℝ) * Real.sqrt Q :=
    hg.1.trans (mul_le_mul_of_nonneg_left hroot (by positivity))
  have hgeom := hg.2.trans
    (mul_le_mul_of_nonneg_left hroot2 (by positivity : 0 ≤ 2 * (N : ℝ) * Real.sqrt N))
  have hlog : Real.log (q * squareSampledHyperbolaCutoff N q : ℕ) ≤
      Real.log (1 + (N : ℝ) * Real.sqrt Q) := by
    by_cases hzero : q * squareSampledHyperbolaCutoff N q = 0
    · rw [hzero]
      simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_nonneg (by
        have h : (0 : ℝ) ≤ N * Real.sqrt Q := by positivity
        linarith)
    · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hzero) (by linarith)
  have hlog0 := Real.log_natCast_nonneg (q * squareSampledHyperbolaCutoff N q)
  have hpow : (1 + Real.log (q * squareSampledHyperbolaCutoff N q : ℕ)) ^ 4 ≤
      (1 + Real.log (1 + (N : ℝ) * Real.sqrt Q)) ^ 4 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 4
  unfold squareSampledDivisorRemainderBound
  apply add_le_add le_rfl
  apply mul_le_mul _ hpow (by positivity) (by positivity)
  nlinarith

/-- Uniform kernel envelope for positive dilations at most `Q`. -/
noncomputable def mobiusSquareDivisorProductEnvelope (N Q : ℕ) : ℝ :=
  2 * ((N : ℝ) * (7 + 2 * Real.log ((N : ℝ) ^ 2 + 1)) +
      32 * (N : ℝ) * Real.sqrt N * Real.sqrt (Real.sqrt Q) *
        (1 + Real.log (1 + (N : ℝ) * Real.sqrt Q)) ^ 4) *
    (Real.log (Q : ℝ) + Real.log ((N : ℝ) ^ 2 + 1) / 2) +
    (N : ℝ) / 2 * (8 + 2 * Real.log ((N : ℝ) ^ 2 + 1)) *
      Real.log ((N : ℝ) ^ 2 + 1)

theorem mobiusSquareDivisorProductEnvelope_nonneg (N Q : ℕ) :
    0 ≤ mobiusSquareDivisorProductEnvelope N Q := by
  have hL : 0 ≤ Real.log ((N : ℝ) ^ 2 + 1) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (N : ℝ)])
  have hQ := Real.log_natCast_nonneg Q
  unfold mobiusSquareDivisorProductEnvelope
  positivity

theorem abs_mobiusSquareDivisorRemainderKernel_le_product_envelope
    (N : ℕ) {q Q : ℕ} (hq : 0 < q) (hqQ : q ≤ Q) :
    |mobiusSquareDivisorRemainderKernel N q| ≤ mobiusSquareDivisorProductEnvelope N Q := by
  apply (abs_mobiusSquareDivisorRemainderKernel_le N hq).trans
  have hF := squareSampledDivisorRemainderBound_le_product_envelope N hq hqQ
  have hlog := Real.log_le_log (by exact_mod_cast hq : (0 : ℝ) < q)
    (by exact_mod_cast hqQ : (q : ℝ) ≤ Q)
  have hqlog := Real.log_natCast_nonneg q
  have hL : 0 ≤ Real.log ((N : ℝ) ^ 2 + 1) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (N : ℝ)])
  unfold mobiusSquareDivisorProductEnvelope
  apply add_le_add _ le_rfl
  exact mul_le_mul (mul_le_mul_of_nonneg_left hF (by norm_num))
    (by linarith) (by positivity) (by positivity)

/-- Number of positive pairs in any square box with product at most `Q`. -/
theorem sum_product_cutoff_indicator_le (N Q : ℕ) :
    (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, if a * b ≤ Q then (1 : ℝ) else 0) ≤
      (Q : ℝ) * (1 + Real.log (Q : ℝ)) := by
  classical
  have hrow (a : ℕ) (ha : a ∈ Icc 1 N) :
      (∑ b ∈ Icc 1 N, if a * b ≤ Q then (1 : ℝ) else 0) ≤
        if a ≤ Q then ((Q / a : ℕ) : ℝ) else 0 := by
    have ha0 : 0 < a := (mem_Icc.mp ha).1
    by_cases haQ : a ≤ Q
    · rw [if_pos haQ]
      have hsub : (Icc 1 N).filter (fun b => a * b ≤ Q) ⊆ Icc 1 (Q / a) := by
        intro b hb
        obtain ⟨hbN, hab⟩ := mem_filter.mp hb
        exact mem_Icc.mpr ⟨(mem_Icc.mp hbN).1,
          (Nat.le_div_iff_mul_le ha0).mpr (by simpa [Nat.mul_comm] using hab)⟩
      calc
        _ = (((Icc 1 N).filter (fun b => a * b ≤ Q)).card : ℝ) := by
          rw [← sum_filter]
          simp
        _ ≤ ((Icc 1 (Q / a)).card : ℝ) := by exact_mod_cast card_le_card hsub
        _ = _ := by simp
    · rw [if_neg haQ]
      apply le_of_eq
      apply sum_eq_zero
      intro b hb
      have hb1 := (mem_Icc.mp hb).1
      rw [if_neg (by
        intro hab
        have : a ≤ a * b := by nlinarith
        omega)]
  have hsub : (Icc 1 N).filter (fun a => a ≤ Q) ⊆ Icc 1 Q := by
    intro a ha
    obtain ⟨haN, haQ⟩ := mem_filter.mp ha
    exact mem_Icc.mpr ⟨(mem_Icc.mp haN).1, haQ⟩
  calc
    _ ≤ ∑ a ∈ Icc 1 N, if a ≤ Q then ((Q / a : ℕ) : ℝ) else 0 := sum_le_sum hrow
    _ = ∑ a ∈ (Icc 1 N).filter (fun a => a ≤ Q), ((Q / a : ℕ) : ℝ) := (sum_filter _ _).symm
    _ ≤ ∑ a ∈ Icc 1 Q, ((Q / a : ℕ) : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
    _ ≤ ∑ a ∈ Icc 1 Q, (Q : ℝ) / a := sum_le_sum (by intros; exact Nat.cast_div_le)
    _ = (Q : ℝ) * ∑ a ∈ Icc 1 Q, 1 / (a : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intros
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Sieve.sum_Icc_one_div_le_one_add_log Q) (by positivity)

/-- The actual double-Möbius divisor remainder restricted by a product cutoff. -/
noncomputable def mobiusSquareDivisorLowProductRemainder (N Q : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, if a * b ≤ Q then
    (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
      mobiusSquareDivisorRemainderKernel N (a * b) else 0

/-- Complementary signed remainder, retained in the exact RH source. -/
noncomputable def mobiusSquareDivisorHighProductRemainder (N Q : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, if Q < a * b then
    (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
      mobiusSquareDivisorRemainderKernel N (a * b) else 0

theorem abs_mobiusSquareDivisorLowProductRemainder_le (N Q : ℕ) :
    |mobiusSquareDivisorLowProductRemainder N Q| ≤
      (Q : ℝ) * (1 + Real.log (Q : ℝ)) * mobiusSquareDivisorProductEnvelope N Q := by
  have hB := mobiusSquareDivisorProductEnvelope_nonneg N Q
  have hmu (a : ℕ) : |(ArithmeticFunction.moebius a : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := a))
  have hterm (a : ℕ) (ha : a ∈ Icc 1 N) (b : ℕ) (hb : b ∈ Icc 1 N) :
      |if a * b ≤ Q then (ArithmeticFunction.moebius a : ℝ) *
          (ArithmeticFunction.moebius b : ℝ) * mobiusSquareDivisorRemainderKernel N (a * b)
        else 0| ≤ (if a * b ≤ Q then (1 : ℝ) else 0) * mobiusSquareDivisorProductEnvelope N Q := by
    split_ifs with hab
    · have hab0 : 0 < a * b := Nat.mul_pos (mem_Icc.mp ha).1 (mem_Icc.mp hb).1
      rw [abs_mul, abs_mul, one_mul]
      have hcoeff : |(ArithmeticFunction.moebius a : ℝ)| *
          |(ArithmeticFunction.moebius b : ℝ)| ≤ 1 :=
        (mul_le_mul (hmu a) (hmu b) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
      calc
        _ ≤ 1 * |mobiusSquareDivisorRemainderKernel N (a * b)| :=
          mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
        _ ≤ _ := by simpa using abs_mobiusSquareDivisorRemainderKernel_le_product_envelope N hab0 hab
    · simp
  unfold mobiusSquareDivisorLowProductRemainder
  calc
    _ ≤ ∑ a ∈ Icc 1 N, |∑ b ∈ Icc 1 N, if a * b ≤ Q then
        (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
          mobiusSquareDivisorRemainderKernel N (a * b) else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, (if a * b ≤ Q then (1 : ℝ) else 0) *
        mobiusSquareDivisorProductEnvelope N Q := by
      apply sum_le_sum
      intro a ha
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum (hterm a ha))
    _ = (∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N, if a * b ≤ Q then (1 : ℝ) else 0) *
        mobiusSquareDivisorProductEnvelope N Q := by simp only [sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (sum_product_cutoff_indicator_le N Q) hB

/-- Exact product split; no part of the principal counterterm or signed bulk is discarded. -/
theorem mobiusShortBilinearSquareSource_eq_divisor_product_split (N Q : ℕ) :
    mobiusShortBilinearSquareSource N =
      ((∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
        (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ) *
          mobiusSquareDivisorPrincipalKernel N (a * b)) -
        (1 + 2 * ∑ d ∈ Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * Real.log d / d) *
          ∑ s ∈ range N, (s : ℝ) ^ 2) +
      mobiusSquareDivisorLowProductRemainder N Q + mobiusSquareDivisorHighProductRemainder N Q := by
  rw [mobiusShortBilinearSquareSource_eq_divisor_principal_add_remainder]
  rw [add_assoc]
  congr 1
  unfold mobiusSquareDivisorLowProductRemainder mobiusSquareDivisorHighProductRemainder
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro a ha
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro b hb
  by_cases hab : a * b ≤ Q
  · simp [hab, Nat.not_lt.mpr hab]
  · simp [hab, Nat.lt_of_not_ge hab]

end RHTower
