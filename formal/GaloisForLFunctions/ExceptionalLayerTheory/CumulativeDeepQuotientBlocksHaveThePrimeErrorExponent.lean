import GaloisForLFunctions.ExceptionalLayerTheory.DeepQuotientBlocksRecoverWeightedPrimeDivisors
import GaloisForLFunctions.ExceptionalLayerTheory.FiniteDilationsOfArithmeticKernels
import GaloisForLFunctions.ExceptionalLayerTheory.PairedCofactorBoundsForOrdinaryPrimeCounts
import GaloisForLFunctions.HTGeometry.RpowPartialSumBound

/-!
# The exponent retained by complete deep quotient blocks

Weighting a prime divisor by its size shifts the summatory exponent up by
one. At the shifted exponent the divisor convolution and its Möbius inverse
both cost a convergent series. Thus a complete block sum retains exactly
the ordinary prime-error bound at each exponent between zero and one.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev prefix (f : ArithmeticFunction ℝ) (N : ℕ) := ∑ m ∈ Icc 1 N, f m

private abbrev powerBound (f : ArithmeticFunction ℝ) (s : ℝ) :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |prefix f N| ≤ C*(N:ℝ)^s

private def timesIndex (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => (n:ℝ)*f n,by simp⟩

private theorem timesIndex_apply (f : ArithmeticFunction ℝ) (n : ℕ) :
    timesIndex f n = (n:ℝ)*f n := rfl

private theorem bounded_convolution {f g : ArithmeticFunction ℝ} {s : ℝ} (hs : 1 < s)
    (hg : ∀ n, |g n| ≤ 1) (hf : powerBound f s) : powerBound (g*f) s := by
  obtain ⟨C,hC,hf⟩ := hf
  let Z := ∑' n : ℕ, (n:ℝ)^(-s)
  have hZ : 0 ≤ Z := tsum_nonneg fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hz := Real.summable_nat_rpow.mpr (by linarith only [hs] : -s < -1)
  refine ⟨C*Z,mul_nonneg hC hZ,fun N => ?_⟩
  rw [prefix,RHTower.sum_Icc_mul_apply]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (C*(N:ℝ)^s)*(d:ℝ)^(-s) := by
      refine sum_le_sum fun d hd => ?_
      have hd0 : 0 < (d:ℝ) := by exact_mod_cast (mem_Icc.mp hd).1
      rw [abs_mul]
      have h₁ := mul_le_mul (hg d) (hf (N/d)) (abs_nonneg _)
        (by norm_num : (0:ℝ) ≤ 1)
      rw [one_mul] at h₁
      refine h₁.trans ((mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
        (Nat.cast_div_le (m := N) (n := d) (α := ℝ)) (by linarith only [hs])) hC).trans_eq ?_)
      rw [Real.div_rpow (Nat.cast_nonneg _) hd0.le,Real.rpow_neg hd0.le,div_eq_mul_inv,mul_assoc]
    _ ≤ (C*(N:ℝ)^s)*Z := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (hz.sum_le_tsum _ (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _))
        (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    _ = _ := by ring

private theorem zeta_convolution_power_iff (f : ArithmeticFunction ℝ) {s : ℝ} (hs : 1 < s) :
    powerBound ((zeta : ArithmeticFunction ℝ)*f) s ↔ powerBound f s := by
  constructor
  · intro h
    have hμ (n : ℕ) : |(moebius : ArithmeticFunction ℝ) n| ≤ 1 := by
      change |((moebius n : ℤ):ℝ)| ≤ 1
      exact_mod_cast (abs_moebius_le_one (n := n))
    simpa only [← mul_assoc,coe_moebius_mul_coe_zeta,one_mul] using bounded_convolution hs hμ h
  · apply bounded_convolution hs
    intro n
    by_cases hn : n=0 <;> simp [ArithmeticFunction.natCoe_apply,zeta_apply,hn]

private theorem timesIndex_bound (f : ArithmeticFunction ℝ) {b : ℝ} (hb : 0 < b)
    (hf : powerBound f b) : powerBound (timesIndex f) (b+1) := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨3*C,by positivity,fun N => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [prefix,Real.zero_rpow (show b+1 ≠ 0 by linarith)]
  have expand : prefix (timesIndex f) N = prefix f N*((N:ℝ)+1) - ∑ n ∈ Icc 1 N, prefix f n := by
    have he := sum_smul_eq_prefix_differences (fun n => f n) (fun n : ℕ => (n:ℝ)) N
    have hdiff (x : ℝ) : x-(x+1) = -1 := by ring
    simp only [smul_eq_mul,Nat.cast_add,Nat.cast_one,hdiff,mul_neg,mul_one,sum_neg_distrib] at he
    calc
      _ = ∑ n ∈ Icc 1 N, f n*(n:ℝ) := sum_congr rfl fun n _ => mul_comm _ _
      _ = _ := by simpa only [prefix,sub_eq_add_neg] using he
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast hN
  have hsum : |∑ n ∈ Icc 1 N, prefix f n| ≤ N*(C*(N:ℝ)^b) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _n ∈ Icc 1 N, C*(N:ℝ)^b := sum_le_sum fun n hn =>
        (hf n).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _)
          (by exact_mod_cast (mem_Icc.mp hn).2) hb.le) hC)
      _ = _ := by simp
  rw [expand,Real.rpow_add_one hN0.ne']
  apply (abs_sub _ _).trans
  rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (N:ℝ)+1)]
  have hfirst := mul_le_mul_of_nonneg_right (hf N) (by positivity : 0 ≤ (N:ℝ)+1)
  have hNN : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hbig := le_mul_of_one_le_left (mul_nonneg hC (Real.rpow_nonneg hN0.le b)) hNN
  linarith only [hsum,hfirst,hbig]

private theorem withoutIndex_bound (f : ArithmeticFunction ℝ) {b : ℝ} (hb : 0 < b) (hb1 : b < 1)
    (hf : powerBound (timesIndex f) (b+1)) : powerBound f b := by
  obtain ⟨C,hC,hf⟩ := hf
  refine ⟨C+C/b,by positivity,fun N => ?_⟩
  have hrep : prefix f N =
      prefix (timesIndex f) N*((N:ℝ)+1)⁻¹ +
        ∑ n ∈ Icc 1 N, prefix (timesIndex f) n*((n:ℝ)⁻¹-((n:ℝ)+1)⁻¹) := by
    have he := sum_smul_eq_prefix_differences (fun n => timesIndex f n)
      (fun n : ℕ => (n:ℝ)⁻¹) N
    simp only [smul_eq_mul,Nat.cast_add,Nat.cast_one] at he
    rw [← he]
    refine sum_congr rfl fun n hn => ?_
    rw [timesIndex_apply,mul_comm (n:ℝ),mul_assoc,mul_inv_cancel₀
      (by exact_mod_cast (Nat.ne_of_gt (mem_Icc.mp hn).1)),mul_one]
  have head : |prefix (timesIndex f) N*((N:ℝ)+1)⁻¹| ≤ C*(N:ℝ)^b := by
    rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ ((N:ℝ)+1)⁻¹)]
    rcases Nat.eq_zero_or_pos N with rfl | hn
    · simp [prefix,Real.zero_rpow hb.ne']
    have hn0 : 0 < (N:ℝ) := by exact_mod_cast hn
    have h := mul_le_mul (hf N) (inv_anti₀ hn0 (by linarith : (N:ℝ)≤N+1))
      (by positivity) (mul_nonneg hC (Real.rpow_nonneg hn0.le _))
    rwa [Real.rpow_add_one hn0.ne',mul_assoc C, mul_assoc ((N:ℝ)^b),
      mul_inv_cancel₀ hn0.ne',mul_one] at h
  have htail : |∑ n ∈ Icc 1 N, prefix (timesIndex f) n*((n:ℝ)⁻¹-((n:ℝ)+1)⁻¹)| ≤
      C*((N:ℝ)^b/b) := by
    apply (abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ n ∈ Icc 1 N, C*(n:ℝ)^(b-1) := by
        refine sum_le_sum fun n hn => ?_
        have hp : 0 < (n:ℝ) := by exact_mod_cast (mem_Icc.mp hn).1
        have hs : 0 < (n:ℝ)+1 := by positivity
        have he : (n:ℝ)⁻¹-((n:ℝ)+1)⁻¹ = (n:ℝ)⁻¹*((n:ℝ)+1)⁻¹ := by field_simp; ring
        rw [he,abs_mul,abs_of_nonneg (mul_nonneg (inv_nonneg.mpr hp.le) (inv_nonneg.mpr hs.le))]
        have h := mul_le_mul (hf n)
          (mul_le_mul_of_nonneg_left (inv_anti₀ hp (by linarith : (n:ℝ) ≤ n+1)) (inv_nonneg.mpr hp.le))
          (by positivity) (mul_nonneg hC (Real.rpow_nonneg hp.le _))
        refine h.trans_eq ?_
        rw [Real.rpow_add_one hp.ne',Real.rpow_sub_one hp.ne']
        field_simp
      _ ≤ _ := by
        rw [← mul_sum]
        apply mul_le_mul_of_nonneg_left _ hC
        have h := _root_.HTGeometry.sum_rpow_sub_one_le hb hb1 N
        rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range]
        simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ)] using h
  rw [hrep]
  exact (abs_add_le _ _).trans ((add_le_add head htail).trans_eq (by ring))

/-- Cumulative prime excess in complete blocks at a common width. -/
def deepBlockPrimeExcess (q N : ℕ) : ℝ :=
  ∑ M ∈ Icc 1 N, ∑ r ∈ Icc 1 q,
    quotientClassMassOf (fun m => vonMangoldt m-1) q (q*M-r)

private theorem deepBlockPrimeExcess_eq {N q : ℕ} (hq : N < q) :
    deepBlockPrimeExcess q N = prefix ((zeta : ArithmeticFunction ℝ)*
      timesIndex (vonMangoldt - (zeta : ArithmeticFunction ℝ))) N := by
  refine sum_congr rfl fun M hM => ?_
  rw [sum_quotientClassMassOf_deep_block _ (mem_Icc.mp hM).1 ((mem_Icc.mp hM).2.trans_lt hq),
    coe_zeta_mul_apply]
  refine sum_congr rfl fun m hm => ?_
  have hm0 := Nat.pos_of_mem_divisors hm
  change (m:ℝ)*(vonMangoldt m-1) = (m:ℝ)*(vonMangoldt m-(zeta : ArithmeticFunction ℝ) m)
  simp only [ArithmeticFunction.natCoe_apply,zeta_apply,if_neg hm0.ne',Nat.cast_one]

/-- Complete deep blocks retain precisely the ordinary Chebyshev power bound;
the width may vary freely above the base. -/
theorem deepBlockPrimeExcess_power_iff (width : ℕ → ℕ) (hwidth : ∀ N, N < width N)
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |deepBlockPrimeExcess (width N) N| ≤ C*(N:ℝ)^(b+1)) ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |Chebyshev.psi N-N| ≤ C*(N:ℝ)^b := by
  let f := vonMangoldt - (zeta : ArithmeticFunction ℝ)
  simp_rw [deepBlockPrimeExcess_eq (hwidth _),← sum_vonMangoldt_sub_zeta]
  change powerBound ((zeta : ArithmeticFunction ℝ)*timesIndex f) (b+1) ↔ powerBound f b
  rw [zeta_convolution_power_iff _ (by linarith only [hb])]
  exact ⟨withoutIndex_bound f hb hb1,timesIndex_bound f hb⟩

#print axioms deepBlockPrimeExcess_power_iff

end GaloisForLFunctions.ExceptionalLayerTheory
