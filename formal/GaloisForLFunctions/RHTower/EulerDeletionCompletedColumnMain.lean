import GaloisForLFunctions.RHTower.EulerDeletionReducedDenominatorHead
import GaloisForLFunctions.RHTower.EulerDeletionCoprimeColumnCancellation
import Mathlib.Analysis.PSeries

/-!
# Euler main and subpower aggregate error of completed coprime kernel columns

Absolute two-index Möbius inversion identifies the literal complete kernel column
with its exact prime-supported source. Adding half of the reciprocal Euler mass
leaves a nonnegative error with a uniform decaying bound in the reduced denominator.

The sum of absolute errors, with the physical inverse-gcd weight, has arbitrarily
small power growth even on the full modulus rectangle. The finite numerator heads
subtracted by the actual EDQ cutoff remain uncontrolled; this is not an RH proof.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
open RHTower.Sieve
attribute [local instance] Classical.propDecidable
namespace RHTower.DeletionFlux

/-- Complete numerator column with the literal coprimality mask and Möbius coefficients. -/
def coprimeKernelColumn (m b : ℕ) : ℝ :=
  ∑' a : ℕ, if m.Coprime a then ((ArithmeticFunction.moebius a : ℤ) : ℝ) * completeKernel a b else 0

/-- Euler mass of the positive integers supported on the prime divisors of a modulus. -/
def kernelEulerMass (m : ℕ) (α : ℝ) : ℝ :=
  ∏ p ∈ m.primeFactors, (1-(p : ℝ)^(-α))⁻¹

private def pairTerm (m b : ℕ) (p : ℕ × ℕ) : ℝ :=
  if m.Coprime p.1 then ((ArithmeticFunction.moebius p.1 : ℤ) : ℝ) *
    (HTGeometry.centeredModularPrimitive b (p.1*p.2) / ((p.1*p.2 : ℕ) : ℝ)^2) else 0

private theorem pair_summable (m b : ℕ) : Summable (pairTerm m b) := by
  have hs : Summable (fun n : ℕ => (1 : ℝ)/(n : ℝ)^2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hp := (summable_mul_of_summable_norm hs.norm hs.norm).mul_left ((b : ℝ)/8)
  apply Summable.of_norm_bounded hp
  intro p
  rw [Real.norm_eq_abs]
  have hP := HTGeometry.centeredModularPrimitive_bounds b (p.1*p.2)
  have hPa : |HTGeometry.centeredModularPrimitive b (p.1*p.2)| ≤ (b : ℝ)/8 :=
    abs_le.mpr ⟨by linarith [hP.1], by linarith [hP.2]⟩
  have hmu : |((ArithmeticFunction.moebius p.1 : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := p.1))
  unfold pairTerm
  split_ifs with h
  · rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg (((p.1*p.2 : ℕ) : ℝ)))]
    calc _ ≤ 1 * (((b : ℝ)/8) / ((p.1*p.2 : ℕ) : ℝ)^2) := by
               gcongr
        _ = _ := by push_cast; simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]; ring
  · simp only [abs_zero]
    positivity

private theorem pair_inner (m b a : ℕ) :
    (∑' j, pairTerm m b (a,j)) =
      if m.Coprime a then ((ArithmeticFunction.moebius a : ℤ) : ℝ) * completeKernel a b else 0 := by
  have hs := (pair_summable m b).prod_factor a
  rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr hs)]
  by_cases h : m.Coprime a
  · dsimp only [pairTerm]
    simp_rw [if_pos h]
    simp [completeKernel, tsum_mul_left]
  · dsimp only [pairTerm]
    simp_rw [if_neg h]
    simp

private theorem pair_fibre (m b n : ℕ) :
    (∑' p : (fun p : ℕ × ℕ => p.1*p.2) ⁻¹' {n}, pairTerm m b p.val) =
      if primeSupportedOn m n then HTGeometry.centeredModularPrimitive b n/(n : ℝ)^2 else 0 := by
  classical
  by_cases hn : n = 0
  · subst n
    have hz (p : (fun p : ℕ × ℕ => p.1*p.2) ⁻¹' {(0 : ℕ)}) : pairTerm m b p.val = 0 := by
      have hp : p.val.1*p.val.2 = 0 := p.property
      simp [pairTerm, hp]
    simp [hz, HTGeometry.centeredModularPrimitive_zero]
  have heq : (fun p : ℕ × ℕ => p.1*p.2) ⁻¹' {n} = (n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    ext p
    simp [hn]
  rw [heq, Finset.tsum_subtype']
  have hp (p : ℕ × ℕ) (hp : p ∈ n.divisorsAntidiagonal) : pairTerm m b p =
      (if m.Coprime p.1 then ((ArithmeticFunction.moebius p.1 : ℤ) : ℝ) else 0) *
        (HTGeometry.centeredModularPrimitive b n/(n : ℝ)^2) := by
    have hmul := (Nat.mem_divisorsAntidiagonal.mp hp).1
    simp only [pairTerm, hmul]
    split_ifs <;> ring
  rw [sum_congr rfl hp, ← sum_mul]
  have hsum : (∑ p ∈ n.divisorsAntidiagonal,
      if m.Coprime p.1 then ((ArithmeticFunction.moebius p.1 : ℤ) : ℝ) else 0) =
      if primeSupportedOn m n then (1 : ℝ) else 0 := by
    rw [Nat.sum_divisorsAntidiagonal (fun a _ =>
      if m.Coprime a then ((ArithmeticFunction.moebius a : ℤ) : ℝ) else 0)]
    exact_mod_cast DeletionCoprimeColumn.sum_coprime_moebius_divisors m (Nat.pos_of_ne_zero hn)
  rw [hsum]
  split_ifs <;> ring

/-- Absolute two-index Möbius inversion identifies the full column with the prime-supported source. -/
theorem coprimeKernelColumn_eq_supported (m b : ℕ) :
    coprimeKernelColumn m b =
      ∑' n : ℕ, if primeSupportedOn m n then HTGeometry.centeredModularPrimitive b n/(n : ℝ)^2 else 0 := by
  have hs := pair_summable m b
  have hf := hs.hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1*p.2)
  have hf' : HasSum (fun n : ℕ => if primeSupportedOn m n then
      HTGeometry.centeredModularPrimitive b n/(n : ℝ)^2 else 0) (∑' p, pairTerm m b p) :=
    hf.congr_fun (fun n => (pair_fibre m b n).symm)
  rw [hf'.tsum_eq, hs.tsum_prod]
  simp_rw [pair_inner]
  rfl

private theorem supported_hasSum (m b : ℕ) :
    HasSum (fun n : ℕ => if primeSupportedOn m n then
      HTGeometry.centeredModularPrimitive b n/(n : ℝ)^2 else 0) (coprimeKernelColumn m b) := by
  have h := (pair_summable m b).hasSum.tsum_fiberwise (fun p : ℕ × ℕ => p.1*p.2)
  have h' := h.congr_fun (fun n => (pair_fibre m b n).symm)
  rwa [(pair_summable m b).tsum_prod, show (∑' a, ∑' j, pairTerm m b (a,j)) =
    coprimeKernelColumn m b by simp_rw [pair_inner]; rfl] at h'

private theorem primitive_correction_bounds {b : ℕ} (hb : 0 < b) (n : ℕ) :
    0 ≤ HTGeometry.centeredModularPrimitive b n + (n : ℝ)/2 ∧
    HTGeometry.centeredModularPrimitive b n + (n : ℝ)/2 ≤ (n : ℝ)^2/(2*b) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hrn : ((n % b : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mod_le n b
  have hid : HTGeometry.centeredModularPrimitive b n + ((n % b : ℕ) : ℝ)/2 =
      ((n % b : ℕ) : ℝ)^2/(2*b) := by
    unfold HTGeometry.centeredModularPrimitive
    field_simp
    ring
  constructor
  · have hn : 0 ≤ ((n % b : ℕ) : ℝ)^2/(2*b) := by positivity
    linarith
  · by_cases hnb : n < b
    · simpa only [Nat.mod_eq_of_lt hnb] using hid.le
    · have hbn : (b : ℝ) ≤ n := by exact_mod_cast Nat.le_of_not_gt hnb
      calc _ ≤ (n : ℝ)/2 := by linarith [(HTGeometry.centeredModularPrimitive_bounds b n).2]
           _ ≤ (n : ℝ)^2/(2*b) := by
             rw [le_div_iff₀ (by positivity)]
             nlinarith

private theorem correction_weight_bounds {b : ℕ} (hb : 0 < b) {n : ℕ} (hn : 0 < n) :
    0 ≤ HTGeometry.centeredModularPrimitive b n/(n : ℝ)^2 + 1/(2*n) ∧
    HTGeometry.centeredModularPrimitive b n/(n : ℝ)^2 + 1/(2*n) ≤
      min (1/(2*(n : ℝ))) (1/(2*(b : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hid : HTGeometry.centeredModularPrimitive b n/(n : ℝ)^2 + 1/(2*n) =
      (HTGeometry.centeredModularPrimitive b n + (n : ℝ)/2)/(n : ℝ)^2 := by
    field_simp
  rw [hid]
  refine ⟨div_nonneg (primitive_correction_bounds hb n).1 (sq_nonneg _), le_min ?_ ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have heq : 1/(2*(n : ℝ))*(n : ℝ)^2 = (n : ℝ)/2 := by field_simp
    rw [heq]
    linarith [(HTGeometry.centeredModularPrimitive_bounds b n).2]
  · rw [div_le_iff₀ (by positivity)]
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using (primitive_correction_bounds hb n).2

private theorem min_reciprocal_le {b n : ℕ} (hb : 0 < b) (hn : 0 < n)
    {α : ℝ} (ha : 0 < α) (ha1 : α < 1) :
    min (1/(2*(n : ℝ))) (1/(2*(b : ℝ))) ≤
      (b : ℝ)^(α-1)/2 * (n : ℝ)^(-α) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  by_cases hnb : n ≤ b
  · have hnbR : (n : ℝ) ≤ b := by exact_mod_cast hnb
    have hp := Real.rpow_le_rpow_of_nonpos hnR hnbR (by linarith : -α ≤ 0)
    have heq : (b : ℝ)^(α-1)/2 * (b : ℝ)^(-α) = 1/(2*(b : ℝ)) := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hbR]
      rw [show α-1+ -α = (-1 : ℝ) by ring, Real.rpow_neg_one]
      field_simp
    calc _ ≤ 1/(2*(b : ℝ)) := min_le_right _ _
         _ = (b : ℝ)^(α-1)/2 * (b : ℝ)^(-α) := heq.symm
         _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)
  · have hbnR : (b : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hnb))
    have hp := Real.rpow_le_rpow_of_nonpos hbR hbnR (by linarith : α-1 ≤ 0)
    have heq : (n : ℝ)^(α-1)/2 * (n : ℝ)^(-α) = 1/(2*(n : ℝ)) := by
      rw [div_mul_eq_mul_div, ← Real.rpow_add hnR]
      rw [show α-1+ -α = (-1 : ℝ) by ring, Real.rpow_neg_one]
      field_simp
    calc _ ≤ 1/(2*(n : ℝ)) := min_le_left _ _
         _ = (n : ℝ)^(α-1)/2 * (n : ℝ)^(-α) := heq.symm
         _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hp (by norm_num))
           (Real.rpow_nonneg (Nat.cast_nonneg n) _)

private theorem correction_hasSum {m : ℕ} (hm : 0 < m) (b : ℕ) :
    HasSum (fun n : ℕ => if primeSupportedOn m n then
      HTGeometry.centeredModularPrimitive b n/(n : ℝ)^2 + 1/(2*n) else 0)
      (coprimeKernelColumn m b + kernelEulerMass m 1/2) := by
  have hmass := (DeletionCoprimeColumn.hasSum_supportedRpow hm (by norm_num : (0 : ℝ) < 1)).div_const 2
  have hsum := (supported_hasSum m b).add hmass
  apply hsum.congr_fun
  intro n
  simp only [primeSupportedRpowHom, MonoidHom.coe_mk, OneHom.coe_mk, Real.rpow_neg_one]
  split_ifs <;> ring

/-- The literal complete coprime column has an explicit Euler main and a positive, decaying error. -/
theorem coprimeKernelColumn_main_bounds {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    {α : ℝ} (ha : 0 < α) (ha1 : α < 1) :
    0 ≤ coprimeKernelColumn m b + kernelEulerMass m 1/2 ∧
    coprimeKernelColumn m b + kernelEulerMass m 1/2 ≤
      kernelEulerMass m α * (b : ℝ)^(α-1)/2 := by
  have hpoint (n : ℕ) :
      0 ≤ (if primeSupportedOn m n then
        HTGeometry.centeredModularPrimitive b n/(n : ℝ)^2 + 1/(2*n) else 0) ∧
      (if primeSupportedOn m n then
        HTGeometry.centeredModularPrimitive b n/(n : ℝ)^2 + 1/(2*n) else 0) ≤
        (b : ℝ)^(α-1)/2 * primeSupportedRpowHom m α n := by
    by_cases hs : primeSupportedOn m n
    · simp only [if_pos hs, primeSupportedRpowHom, MonoidHom.coe_mk, OneHom.coe_mk]
      rcases n.eq_zero_or_pos with rfl | hn
      · simp [Real.zero_rpow (neg_ne_zero.mpr ha.ne')]
      · exact ⟨(correction_weight_bounds hb hn).1,
          (correction_weight_bounds hb hn).2.trans (min_reciprocal_le hb hn ha ha1)⟩
    · simp [hs, primeSupportedRpowHom]
  refine ⟨HasSum.nonneg (fun n => (hpoint n).1) (correction_hasSum hm b), ?_⟩
  have h := hasSum_le (fun n => (hpoint n).2) (correction_hasSum hm b)
    ((DeletionCoprimeColumn.hasSum_supportedRpow hm ha).mul_left ((b : ℝ)^(α-1)/2))
  simpa only [kernelEulerMass, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

/-- Uniform subpower modulus cost for the error after the completed column's Euler main. -/
theorem exists_coprimeKernelColumn_error_bound {α δ : ℝ}
    (ha : 0 < α) (ha1 : α < 1) (hd : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m b : ℕ, 0 < m → 0 < b →
      |coprimeKernelColumn m b + kernelEulerMass m 1/2| ≤
        C * (m : ℝ)^δ * (b : ℝ)^(α-1) := by
  obtain ⟨C, hC, hbound⟩ := DeletionCoprimeColumn.exists_supportedEulerMass_le ha hd
  refine ⟨C/2, by positivity, ?_⟩
  intro m b hm hb
  have h := coprimeKernelColumn_main_bounds hm hb ha ha1
  rw [abs_of_nonneg h.1]
  calc _ ≤ kernelEulerMass m α * (b : ℝ)^(α-1)/2 := h.2
       _ ≤ (C * (m : ℝ)^δ) * (b : ℝ)^(α-1)/2 := by
         gcongr
         exact hbound m hm
       _ = _ := by ring

/-- The Euler main is the totient ratio at every squarefree modulus. -/
theorem kernelEulerMass_one_eq_totientRatio {m : ℕ} (hm : Squarefree m) :
    kernelEulerMass m 1 = (m : ℝ)/(Nat.totient m : ℝ) := by
  have hs := DeletionCoprimeColumn.hasSum_supportedRpow
    (Nat.pos_of_ne_zero hm.ne_zero) (by norm_num : (0 : ℝ) < 1)
  rw [kernelEulerMass, ← hs.tsum_eq, ← tsum_primeSupportedReciprocal_eq_totientRatio hm]
  apply tsum_congr
  intro n
  by_cases hn : n = 0 <;>
    simp [primeSupportedRpowHom, primeSupportedReciprocal,
      reciprocalNatArithmetic, hn, Real.rpow_neg_one, one_div]

/-- Total absolute completed-column error on the entire modulus rectangle, with its inverse-gcd weight. -/
def completedColumnErrorMass (N : ℕ) : ℝ :=
  ∑ r ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
    |coprimeKernelColumn (r*b) b + kernelEulerMass (r*b) 1/2|/(r : ℝ)

/-- Completing every numerator column costs only an arbitrarily small cutoff power after its Euler main.
This is stronger than the physical triangle, but does not estimate the subtracted finite numerator heads. -/
theorem exists_completedColumnErrorMass_subpower {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, completedColumnErrorMass N ≤ C*(N : ℝ)^ε := by
  let δ : ℝ := min (ε/5) (1/2)
  have hd : 0 < δ := lt_min (by positivity) (by norm_num)
  have hd1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hdε : 5*δ ≤ ε := by have := min_le_left (ε/5) (1/2 : ℝ); dsimp [δ]; linarith
  obtain ⟨A, hA, hbound⟩ := exists_coprimeKernelColumn_error_bound hd hd1 hd
  let D : ℝ := 1+1/δ
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨A*D^2, by positivity, ?_⟩
  intro N
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [completedColumnErrorMass, Real.zero_rpow hε.ne']
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let H : ℝ := 1+Real.log N
  let K : ℝ := A*(N : ℝ)^(3*δ)
  have hH : 0 ≤ H := by dsimp [H]; linarith [Real.log_nonneg hN1]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hpoint (r b : ℕ) (hr : r ∈ Icc 1 N) (hb : b ∈ Icc 1 N) :
      |coprimeKernelColumn (r*b) b + kernelEulerMass (r*b) 1/2|/(r : ℝ) ≤
        K*(1/(r : ℝ))*(1/(b : ℝ)) := by
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (mem_Icc.mp hr).1
    have hb0 : (0 : ℝ) < b := by exact_mod_cast (mem_Icc.mp hb).1
    have hrN : (r : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hr).2
    have hbN : (b : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hb).2
    calc _ ≤ (A*((r*b : ℕ) : ℝ)^δ*(b : ℝ)^(δ-1))/(r : ℝ) :=
             div_le_div_of_nonneg_right
               (hbound (r*b) b (Nat.mul_pos (mem_Icc.mp hr).1 (mem_Icc.mp hb).1)
                 (mem_Icc.mp hb).1) hr0.le
         _ = A*(r : ℝ)^δ*(b : ℝ)^δ*(b : ℝ)^δ/((r : ℝ)*b) := by
             rw [Nat.cast_mul, Real.mul_rpow hr0.le hb0.le, Real.rpow_sub hb0, Real.rpow_one]
             ring
         _ ≤ A*(N : ℝ)^δ*(N : ℝ)^δ*(N : ℝ)^δ/((r : ℝ)*b) := by gcongr
         _ = _ := by
             dsimp [K]
             rw [show 3*δ = δ+δ+δ by ring, Real.rpow_add hN0, Real.rpow_add hN0]
             ring
  have htotal : completedColumnErrorMass N ≤ K*H^2 := by
    unfold completedColumnErrorMass
    calc _ ≤ ∑ r ∈ Icc 1 N, ∑ b ∈ Icc 1 N, K*(1/(r : ℝ))*(1/(b : ℝ)) :=
             Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun b hb => hpoint r b hr hb))
         _ = K*(∑ r ∈ Icc 1 N, 1/(r : ℝ))^2 := by
             simp only [← Finset.mul_sum, ← Finset.sum_mul]
             ring
         _ ≤ K*H^2 := by
             gcongr
             exact sum_Icc_one_div_le_one_add_log N
  have hlog : H ≤ D*(N : ℝ)^δ := by
    have hp := Real.one_le_rpow hN1 hd.le
    have hl := Real.log_le_rpow_div (Nat.cast_nonneg N) hd
    dsimp [H,D]
    calc _ ≤ (N : ℝ)^δ+(N : ℝ)^δ/δ := add_le_add hp hl
         _ = _ := by ring
  calc _ ≤ K*H^2 := htotal
       _ ≤ K*(D*(N : ℝ)^δ)^2 := by gcongr
       _ = A*D^2*(N : ℝ)^(5*δ) := by
         dsimp [K]
         rw [show 5*δ = 3*δ+δ+δ by ring, Real.rpow_add hN0, Real.rpow_add hN0]
         ring
       _ ≤ A*D^2*(N : ℝ)^ε := by
         exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 hdε) (by positivity)

end RHTower.DeletionFlux
