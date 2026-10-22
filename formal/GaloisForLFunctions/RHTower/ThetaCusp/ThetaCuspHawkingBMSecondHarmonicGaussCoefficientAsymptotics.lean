import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicGaussContiguousTransport
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Gauss coefficient asymptotics

Euler's `GammaSeq` limit gives an exact asymptotic normalization of the ordinary hypergeometric
coefficients. For positive real Gauss gap `Re(c-a-b)`, this proves absolute summability and decay of
the contiguous-transport boundary. Consequently both elementary Gauss parameter shifts are
available without separate convergence or tail hypotheses.
-/

open Complex Nat Polynomial Filter Topology

namespace RHTower

noncomputable section

theorem ascPochhammer_eval_eq_prod_range (s : ℂ) (n : ℕ) :
    (ascPochhammer ℂ n).eval s = ∏ j ∈ Finset.range n, (s + (j : ℂ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

theorem normalized_ordinaryHypergeometricCoefficient_eq_gammaSeq_ratio
    (a b c : ℂ) (n : ℕ) (hn : n ≠ 0)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) :
    (n : ℂ) ^ (c - a - b) * (n + 1) *
        ordinaryHypergeometricCoefficient a b c (n + 1) =
      Complex.GammaSeq c n / (Complex.GammaSeq a n * Complex.GammaSeq b n) := by
  have hbase : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hprod (s : ℂ) (hs : ∀ k : ℕ, (k : ℂ) ≠ -s) :
      ∏ j ∈ Finset.range (n + 1), (s + (j : ℂ)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj hjzero
    have hjneg : (j : ℂ) = -s := by linear_combination hjzero
    exact hs j hjneg
  have hPa := hprod a ha
  have hPb := hprod b hb
  have hPc := hprod c hc
  have hfac : ((n.factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have hsucc : ((n + 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hpow :
      (n : ℂ) ^ (c - a - b) * ((n : ℂ) ^ a * (n : ℂ) ^ b) = (n : ℂ) ^ c := by
    rw [← mul_assoc, ← Complex.cpow_add _ _ hbase, ← Complex.cpow_add _ _ hbase]
    congr 1
    ring
  have hcpow (s : ℂ) : (n : ℂ) ^ s ≠ 0 := by
    simp [Complex.cpow_eq_zero_iff, hbase]
  rw [ordinaryHypergeometricCoefficient,
    ascPochhammer_eval_eq_prod_range, ascPochhammer_eval_eq_prod_range,
    ascPochhammer_eval_eq_prod_range]
  simp only [Complex.GammaSeq, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  field_simp
  exact (eq_div_iff (mul_ne_zero (hcpow a) (hcpow b))).2 hpow

theorem tendsto_normalized_ordinaryHypergeometricCoefficient
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c) :
    Tendsto
      (fun n : ℕ =>
        (n : ℂ) ^ (c - a - b) * (n + 1) *
          ordinaryHypergeometricCoefficient a b c (n + 1))
      atTop
      (𝓝 (Complex.Gamma c / (Complex.Gamma a * Complex.Gamma b))) := by
  have hGamma (s : ℂ) (hs : ∀ k : ℕ, (k : ℂ) ≠ -s) : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro k hsk
    apply hs k
    linear_combination hsk
  have hratio : Tendsto
      (fun n : ℕ =>
        Complex.GammaSeq c n / (Complex.GammaSeq a n * Complex.GammaSeq b n))
      atTop
      (𝓝 (Complex.Gamma c / (Complex.Gamma a * Complex.Gamma b))) :=
    (Complex.GammaSeq_tendsto_Gamma c).div
      ((Complex.GammaSeq_tendsto_Gamma a).mul (Complex.GammaSeq_tendsto_Gamma b))
      (mul_ne_zero (hGamma a ha) (hGamma b hb))
  apply hratio.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (normalized_ordinaryHypergeometricCoefficient_eq_gammaSeq_ratio
    a b c n hn ha hb hc).symm

theorem summable_inv_nat_rpow_mul_succ {d : ℝ} (hd : 0 < d) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) ^ d * (n + 1))) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-d - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  · by_cases hn : n = 0
    · simp [hn, Real.zero_rpow hd.ne']
      positivity
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hden : (n : ℝ) ^ d * n = (n : ℝ) ^ (d + 1) := by
        simpa only [Real.rpow_one] using (Real.rpow_add hnpos d 1).symm
      calc
        1 / ((n : ℝ) ^ d * (n + 1)) ≤ 1 / ((n : ℝ) ^ d * n) := by
          gcongr
          exact_mod_cast Nat.le_succ n
        _ = (n : ℝ) ^ (-d - 1) := by
          rw [hden, one_div, ← Real.rpow_neg hnpos.le]
          congr 1
          ring

theorem summable_ordinaryHypergeometricCoefficient_of_re_gap_pos
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hgap : 0 < (c - a - b).re) :
    Summable (ordinaryHypergeometricCoefficient a b c) := by
  let d : ℂ := c - a - b
  have hd : 0 < d.re := by simpa [d] using hgap
  have hlim := tendsto_normalized_ordinaryHypergeometricCoefficient a b c ha hb hc
  obtain ⟨C, hC⟩ := hlim.norm.isBoundedUnder_le
  have hshift : Summable (fun n : ℕ =>
      ordinaryHypergeometricCoefficient a b c (n + 1)) := by
    apply summable_of_isBigO_nat (summable_inv_nat_rpow_mul_succ hd)
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [hC, eventually_ne_atTop 0] with n hnC hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    change ‖(n : ℂ) ^ (c - a - b) * (n + 1) *
      ordinaryHypergeometricCoefficient a b c (n + 1)‖ ≤ C at hnC
    have hnormpow : ‖(n : ℂ) ^ (c - a - b)‖ =
        (n : ℝ) ^ (c - a - b).re := by
      exact Complex.norm_cpow_eq_rpow_re_of_pos hnpos (c - a - b)
    have hnormsucc : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
      rw [← Nat.cast_one, ← Nat.cast_add, norm_natCast]
      push_cast
      rfl
    have hdenpos : 0 < (n : ℝ) ^ d.re * (n + 1) := mul_pos (by positivity) (by positivity)
    have hweighted :
        (n : ℝ) ^ d.re * (n + 1) *
            ‖ordinaryHypergeometricCoefficient a b c (n + 1)‖ ≤ C := by
      simpa only [d, norm_mul, hnormpow, hnormsucc, Nat.cast_add, Nat.cast_one] using hnC
    rw [Real.norm_of_nonneg (by positivity : 0 ≤ 1 / ((n : ℝ) ^ d.re * (n + 1)))]
    rw [mul_one_div]
    exact (le_div_iff₀ hdenpos).2 (by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hweighted)
  exact (summable_nat_add_iff 1).mp (by simpa [Nat.add_comm] using hshift)

theorem tendsto_nat_mul_ordinaryHypergeometricCoefficient_of_re_gap_pos
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hgap : 0 < (c - a - b).re) :
    Tendsto
      (fun n : ℕ => (n : ℂ) * ordinaryHypergeometricCoefficient a b c n)
      atTop (𝓝 0) := by
  let d : ℂ := c - a - b
  have hd : 0 < d.re := by simpa [d] using hgap
  have hlim := tendsto_normalized_ordinaryHypergeometricCoefficient a b c ha hb hc
  obtain ⟨C, hC⟩ := hlim.norm.isBoundedUnder_le
  have hshift : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℂ) *
        ordinaryHypergeometricCoefficient a b c (n + 1))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hdecay : Tendsto (fun n : ℕ => C * (n : ℝ) ^ (-d.re)) atTop (𝓝 0) :=
      by simpa [Function.comp_def] using
        ((tendsto_rpow_neg_atTop hd).comp tendsto_natCast_atTop_atTop).const_mul C
    apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
      _ hdecay
    filter_upwards [hC, eventually_ne_atTop 0] with n hnC hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    change ‖(n : ℂ) ^ (c - a - b) * (n + 1) *
      ordinaryHypergeometricCoefficient a b c (n + 1)‖ ≤ C at hnC
    have hnormpow : ‖(n : ℂ) ^ (c - a - b)‖ =
        (n : ℝ) ^ (c - a - b).re := by
      exact Complex.norm_cpow_eq_rpow_re_of_pos hnpos (c - a - b)
    have hnormsucc : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
      rw [← Nat.cast_one, ← Nat.cast_add, _root_.norm_natCast]
      push_cast
      rfl
    have hweighted :
        (n : ℝ) ^ d.re * (n + 1) *
            ‖ordinaryHypergeometricCoefficient a b c (n + 1)‖ ≤ C := by
      simpa only [d, norm_mul, hnormpow, hnormsucc, Nat.cast_add, Nat.cast_one] using hnC
    rw [norm_mul, _root_.norm_natCast]
    push_cast
    have hpowpos : 0 < (n : ℝ) ^ d.re := Real.rpow_pos_of_pos hnpos d.re
    have hdiv :
        ((n : ℝ) + 1) * ‖ordinaryHypergeometricCoefficient a b c (n + 1)‖ ≤
          C / (n : ℝ) ^ d.re := by
      exact (le_div_iff₀ hpowpos).2 (by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using hweighted)
    calc
      ((n : ℝ) + 1) * ‖ordinaryHypergeometricCoefficient a b c (n + 1)‖ ≤
          C / (n : ℝ) ^ d.re := hdiv
      _ = C * (n : ℝ) ^ (-d.re) := by
        rw [div_eq_mul_inv, Real.rpow_neg hnpos.le]
  exact (tendsto_add_atTop_iff_nat 1).mp (by
    simpa only [Nat.cast_add, Nat.cast_one] using hshift)

/-- Positive real gap discharges every analytic hypothesis in one `(b,c)` Gauss transport step. -/
theorem tsum_ordinaryHypergeometricCoefficient_shift_b_c_of_re_gap_pos
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hgap : 0 < (c - a - b).re) :
    (c - a) / c *
        (∑' j : ℕ, ordinaryHypergeometricCoefficient a (b + 1) (c + 1) j) =
      ∑' j : ℕ, ordinaryHypergeometricCoefficient a b c j := by
  have hb0 : b ≠ 0 := by
    intro hbzero
    apply hb 0
    simp [hbzero]
  have hbshift : ∀ k : ℕ, (k : ℂ) ≠ -(b + 1) := by
    intro k hk
    apply hb (k + 1)
    push_cast
    linear_combination hk
  have hcshift : ∀ k : ℕ, (k : ℂ) ≠ -(c + 1) := by
    intro k hk
    apply hc (k + 1)
    push_cast
    linear_combination hk
  have hgapshift : 0 < ((c + 1) - a - (b + 1)).re := by
    have heq : (c + 1) - a - (b + 1) = c - a - b := by ring
    simpa only [heq] using hgap
  have hsum := summable_ordinaryHypergeometricCoefficient_of_re_gap_pos
    a b c ha hb hc hgap
  have hsumshift := summable_ordinaryHypergeometricCoefficient_of_re_gap_pos
    a (b + 1) (c + 1) ha hbshift hcshift hgapshift
  have htail0 := tendsto_nat_mul_ordinaryHypergeometricCoefficient_of_re_gap_pos
    a b c ha hb hc hgap
  have htail : Tendsto
      (fun N : ℕ => (N : ℂ) / b * ordinaryHypergeometricCoefficient a b c N)
      atTop (𝓝 0) := by
    simpa only [div_mul_eq_mul_div, zero_div] using htail0.div_const b
  exact tsum_ordinaryHypergeometricCoefficient_shift_b_c
    a b c hb0 hc hsum hsumshift htail

/-- Positive real gap discharges every analytic hypothesis in one `(a,c)` Gauss transport step. -/
theorem tsum_ordinaryHypergeometricCoefficient_shift_a_c_of_re_gap_pos
    (a b c : ℂ)
    (ha : ∀ k : ℕ, (k : ℂ) ≠ -a)
    (hb : ∀ k : ℕ, (k : ℂ) ≠ -b)
    (hc : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hgap : 0 < (c - a - b).re) :
    (c - b) / c *
        (∑' j : ℕ, ordinaryHypergeometricCoefficient (a + 1) b (c + 1) j) =
      ∑' j : ℕ, ordinaryHypergeometricCoefficient a b c j := by
  simpa only [ordinaryHypergeometricCoefficient_symm, add_comm] using
    tsum_ordinaryHypergeometricCoefficient_shift_b_c_of_re_gap_pos
      b a c hb ha hc (by
        have heq : c - b - a = c - a - b := by ring
        simpa only [heq] using hgap)

end

end RHTower
