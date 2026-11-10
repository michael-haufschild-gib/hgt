import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRowOfWeilsPairingAtADegreePoint
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheGluingIndexCountsTheZeros

/-!
# The gluing index is the self-energy of the jets

The first `M` graphs of the arithmetic square are glued with index `M!`, a count over the finite
primes. The jets pair the first `M` degree points with the off-diagonal energy

  `E(M) = Σ_{m ≠ n ≤ M} ½(1/|m − n| + 1/(m + n))`,

an archimedean quantity: Weil's archimedean pairing of the flat packet on `[1, M]` with its
diagonal entries left out. This file compares the two.

* **The energy in closed form** (`jetEnergy_eq`): `E(M) = (M + ½)·H_{2M} − (5/4)·H_M − M`.
* **The gluing index is the divergent part of the energy**
  (`tendsto_jetEnergy_sub_log_det_div`): `(E(M) − log det(necklace matrix))/M → γ + log 2`.
  Both terms are `M log M − M + O(M)`; the terms `M log M` and `−M` cancel.
* **Weil's constant** (`tendsto_jetEnergy_sub_counterterm_div`): with the counterterm
  `log(n/2π)` at the degree `n`, `(E(M) − Σ_{n ≤ M} log(n/2π))/M → log 4π + γ`, the constant of
  Weil's archimedean term.

* **Row by row** (`sum_vonMangoldt_div_properDivisors`): `Σ_{m ∣ n, m < n} Λ(n/m) = log n`. In
  Weil's form on a comb the prime kernel pairs `m ∣ n` with the weight `Λ(n/m)`; its row below `n`
  is the divergent part of the counterterm of the jets at `n`.

So the divergence of the archimedean self-energy of the degree points is supplied by the finite
places: the counterterm of `Γ_n` is the logarithm `log n` of its gluing index, up to the constant
`log 2π`.
-/

open Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- The off-diagonal energy of the jets on the first `M` degree points. -/
def jetEnergy (M : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 M, (∑ m ∈ Ico 1 n, jetKernel m n + ∑ m ∈ Ioc n M, jetKernel m n)

/-! ### The energy in closed form -/

/-- `Σ_{j < M} H_j = M·H_M − M`. -/
theorem sum_range_harm (M : ℕ) : ∑ j ∈ range M, harm j = M * harm M - M := by
  induction M with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, harm_succ]
    push_cast
    field_simp
    ring

theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (M : ℕ) :
    ∑ n ∈ Icc 1 M, f n = ∑ k ∈ range M, f (1 + k) := by
  have hI : Icc 1 M = Ico 1 (M + 1) := by
    ext k
    simp only [mem_Icc, mem_Ico]
    omega
  rw [hI, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]

/-- **The off-diagonal energy of the jets** on the first `M` degree points. -/
theorem jetEnergy_eq (M : ℕ) :
    jetEnergy M = ((M : ℝ) + 1 / 2) * harm (2 * M) - 5 / 4 * harm M - M := by
  have hrow : jetEnergy M =
      ∑ n ∈ Icc 1 M, ((harm (M - n) + harm (M + n)) / 2 - 3 / 4 * (1 / (n : ℝ))) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [sum_jetKernel_row (mem_Icc.mp hn).1 (mem_Icc.mp hn).2]
    ring
  have h1 : ∑ n ∈ Icc 1 M, harm (M - n) = M * harm M - M := by
    rw [sum_Icc_one_eq_sum_range, ← sum_range_harm, ← Finset.sum_range_reflect harm M]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.sub_add_eq]
  have h2 : ∑ n ∈ Icc 1 M, harm (M + n) =
      (2 * (M : ℝ) + 1) * harm (2 * M) - ((M : ℝ) + 1) * harm M - M := by
    rw [sum_Icc_one_eq_sum_range]
    have hadd := Finset.sum_range_add harm (M + 1) M
    rw [sum_range_harm, sum_range_harm] at hadd
    have hsum : ∑ k ∈ range M, harm (M + (1 + k)) =
        ((M + 1 + M : ℕ) : ℝ) * harm (M + 1 + M) - ((M + 1 + M : ℕ) : ℝ) -
          (((M + 1 : ℕ) : ℝ) * harm (M + 1) - ((M + 1 : ℕ) : ℝ)) := by
      have e : ∑ k ∈ range M, harm (M + (1 + k)) = ∑ k ∈ range M, harm (M + 1 + k) :=
        Finset.sum_congr rfl fun k _ => by rw [Nat.add_assoc]
      rw [e]
      linarith
    rw [hsum, show M + 1 + M = 2 * M + 1 by ring, harm_succ, harm_succ]
    push_cast
    field_simp
    ring
  have h3 : ∑ n ∈ Icc 1 M, 1 / (n : ℝ) = harm M := by
    rw [sum_Icc_one_eq_sum_range, harm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show ((1 + k : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
  rw [hrow, Finset.sum_sub_distrib, ← Finset.mul_sum, h3, ← Finset.sum_div,
    Finset.sum_add_distrib, h1, h2]
  ring

/-! ### The gluing index as the divergent part -/

theorem tendsto_log_div_nat : Tendsto (fun M : ℕ => Real.log M / (M : ℝ)) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    tendsto_natCast_atTop_atTop
  refine h.congr fun M => ?_
  simp

/-- `log M!/M − (log M − 1) → 0`. -/
theorem tendsto_log_factorial_div_sub :
    Tendsto (fun M : ℕ => Real.log (M.factorial : ℝ) / M - (Real.log M - 1)) atTop (𝓝 0) := by
  have hupp : Tendsto (fun M : ℕ => Real.log M / (M : ℝ) + 1 / (M : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_log_div_nat.add (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    rwa [add_zero] at h
  have key : ∀ M : ℕ, 1 ≤ M → Real.log (M.factorial : ℝ) / M - (Real.log M - 1) =
      (Real.log (M.factorial : ℝ) - ((M : ℝ) * Real.log M - M)) / M := by
    intro M hM
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupp ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    rw [key M hM]
    exact div_nonneg (by linarith [log_factorial_lower M]) hM'.le
  · filter_upwards [eventually_ge_atTop 1] with M hM
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    have h := log_factorial_upper hM
    rw [key M hM, ← add_div]
    gcongr
    linarith

/-- **The gluing index is the divergent part of the energy of the jets**:
`(E(M) − log M!)/M → γ + log 2`. -/
theorem tendsto_jetEnergy_sub_log_factorial_div :
    Tendsto (fun M : ℕ => (jetEnergy M - Real.log (M.factorial : ℝ)) / M) atTop
      (𝓝 (Real.eulerMascheroniConstant + Real.log 2)) := by
  have h2n : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by
      show n ≤ 2 * n
      omega) tendsto_id
  have hA := (tendsto_harm_sub_log.comp h2n).add_const (Real.log 2)
  have hB := tendsto_harm_sub_log
  have hM : Tendsto (fun M : ℕ => (M : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlim := (((hA.sub tendsto_log_factorial_div_sub).add
    (hA.div_atTop (hM.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))).sub
    (tendsto_log_div_nat.const_mul (3 / 4))).sub ((hB.div_atTop hM).const_mul (5 / 4))
  have hval : Real.eulerMascheroniConstant + Real.log 2 - 0 + 0 - 3 / 4 * 0 - 5 / 4 * 0 =
      Real.eulerMascheroniConstant + Real.log 2 := by ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM1
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM1
  simp only [Function.comp_apply]
  rw [jetEnergy_eq, show ((2 * M : ℕ) : ℝ) = 2 * (M : ℝ) by push_cast; ring,
    Real.log_mul (by norm_num) hM'.ne']
  field_simp
  ring

/-- **The gluing index of the first `M` graphs against the jets of the first `M` degree
points.** -/
theorem tendsto_jetEnergy_sub_log_det_div :
    Tendsto (fun M : ℕ => (jetEnergy M - Real.log (((necklaceMatrix M).det : ℤ) : ℝ)) / M) atTop
      (𝓝 (Real.eulerMascheroniConstant + Real.log 2)) := by
  refine tendsto_jetEnergy_sub_log_factorial_div.congr fun M => ?_
  rw [det_necklaceMatrix, Int.cast_natCast]

/-! ### Weil's constant -/

/-- `Σ_{n ≤ M} log(n/2π) = log M! − M log 2π`. -/
theorem sum_log_div_two_pi (M : ℕ) :
    ∑ n ∈ Icc 1 M, Real.log ((n : ℝ) / (2 * Real.pi)) =
      Real.log (M.factorial : ℝ) - M * Real.log (2 * Real.pi) := by
  induction M with
  | zero => simp
  | succ k ih =>
    have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hf : ((k.factorial : ℕ) : ℝ) ≠ 0 := by positivity
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ k + 1), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul hk hf, Real.log_div hk (by positivity)]
    push_cast
    ring

/-- **Weil's archimedean constant on the flat packet**: with the counterterm `log(n/2π)` at the
degree `n`, the energy of the jets per degree point tends to `log 4π + γ`. -/
theorem tendsto_jetEnergy_sub_counterterm_div :
    Tendsto (fun M : ℕ =>
        (jetEnergy M - ∑ n ∈ Icc 1 M, Real.log ((n : ℝ) / (2 * Real.pi))) / M) atTop
      (𝓝 (Real.log (4 * Real.pi) + Real.eulerMascheroniConstant)) := by
  have h := tendsto_jetEnergy_sub_log_factorial_div.add_const (Real.log (2 * Real.pi))
  have h4 : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
    rw [show (4 : ℝ) * Real.pi = 2 * (2 * Real.pi) by ring,
      Real.log_mul (x := 2) (y := 2 * Real.pi) (by norm_num) (by positivity)]
  have hval : Real.eulerMascheroniConstant + Real.log 2 + Real.log (2 * Real.pi) =
      Real.log (4 * Real.pi) + Real.eulerMascheroniConstant := by
    rw [h4]
    ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with M hM1
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM1
  rw [sum_log_div_two_pi]
  field_simp
  ring

/-! ### The contacts below a degree point -/

/-- **The prime kernel below a degree point sums to the logarithm of its gluing index**:
`Σ_{m ∣ n, m < n} Λ(n/m) = log n`, the divergent part of the counterterm of the jets at `n`. -/
theorem sum_vonMangoldt_div_properDivisors {n : ℕ} (hn : 0 < n) :
    ∑ m ∈ n.properDivisors, ArithmeticFunction.vonMangoldt (n / m) = Real.log n := by
  have h := Nat.sum_div_divisors n (fun d => ArithmeticFunction.vonMangoldt d)
  rw [ArithmeticFunction.vonMangoldt_sum, ← Nat.cons_self_properDivisors hn.ne', Finset.sum_cons,
    Nat.div_self hn, ArithmeticFunction.vonMangoldt_apply_one, zero_add] at h
  exact h

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
