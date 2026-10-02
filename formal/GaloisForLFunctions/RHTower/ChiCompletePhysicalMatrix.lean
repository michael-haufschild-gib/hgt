import GaloisForLFunctions.RHTower.ChiPhysicalMatrixMultiplier
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Complete signed physical degree-two matrices

All root saddles of one full integer block lie inside a common physical scale.
The complete actual chi kernel therefore has a simultaneous source error bound.
Finite coefficient-energy aggregation retains its signed stationary matrix, and
exact integral expansion identifies the result with the full physical product integral.
No prime restriction, physical height, or stationary remainder is discarded.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.RHTower

/-- One fixed physical height scale for the complete degree-two integer block. -/
def physicalDegreeTwoScale (N : ℕ) : ℝ := 2 * Real.pi * N

/-- The actual positive saddle for a complete pair of integer coefficients. -/
def physicalDegreeTwoSaddle (N r s : ℕ) : ℝ :=
  2 * Real.pi * Real.sqrt ((N : ℝ) + r) * Real.sqrt ((N : ℝ) + s)

/-- Both full F315 remainders, paid uniformly over this complete physical block. -/
def physicalDegreeTwoEntryBudget (T Cm Ce : ℝ) : ℝ :=
  Cm / (2 * Real.sqrt (2 * T)) + ((6 / Real.sqrt (2 / (100 * T))) * (104 / T)) * Ce

private theorem physicalDegreeTwoScale_ge_four {N : ℕ} (hN : 1 ≤ N) :
    4 ≤ physicalDegreeTwoScale N := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  unfold physicalDegreeTwoScale
  nlinarith only [Real.pi_gt_three, mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hn)]

private theorem physicalDegreeTwoSaddle_mem {N r s : ℕ} (hN : 1 ≤ N)
    (hr : r ∈ Finset.range (N + 1)) (hs : s ∈ Finset.range (N + 1)) :
    physicalDegreeTwoSaddle N r s ∈ Icc (physicalDegreeTwoScale N) (2 * physicalDegreeTwoScale N) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hrN : (r : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hr))
  have hsN : (s : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_lt_succ (Finset.mem_range.mp hs))
  have hl : (N : ℝ) ≤ Real.sqrt ((N : ℝ) + r) * Real.sqrt ((N : ℝ) + s) := by
    calc
      _ = Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) := (Real.mul_self_sqrt hN0).symm
      _ ≤ _ := mul_le_mul (Real.sqrt_le_sqrt (le_add_of_nonneg_right (Nat.cast_nonneg r))) (Real.sqrt_le_sqrt (le_add_of_nonneg_right (Nat.cast_nonneg s)))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hu : Real.sqrt ((N : ℝ) + r) * Real.sqrt ((N : ℝ) + s) ≤ 2 * N := by
    calc
      _ ≤ Real.sqrt (2 * (N : ℝ)) * Real.sqrt (2 * (N : ℝ)) :=
        mul_le_mul (Real.sqrt_le_sqrt (by linarith only [hrN])) (Real.sqrt_le_sqrt (by linarith only [hsN]))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt (by positivity)
  constructor
  · simpa only [physicalDegreeTwoScale, physicalDegreeTwoSaddle, mul_assoc] using
      mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * Real.pi)
  · have h := mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2 * Real.pi)
    dsimp [physicalDegreeTwoSaddle, physicalDegreeTwoScale]
    nlinarith only [h]

private theorem physicalDegreeTwo_frequency {N : ℕ} (hN : 1 ≤ N) (r s : ℕ) :
    2 * Real.log (physicalDegreeTwoSaddle N r s / (2 * Real.pi)) =
      Real.log ((N : ℝ) + r) + Real.log ((N : ℝ) + s) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr : 0 < (N : ℝ) + r := by positivity
  have hs : 0 < (N : ℝ) + s := by positivity
  have heq : physicalDegreeTwoSaddle N r s / (2 * Real.pi) =
      Real.sqrt ((N : ℝ) + r) * Real.sqrt ((N : ℝ) + s) := by
    unfold physicalDegreeTwoSaddle
    field_simp
  rw [heq, Real.log_mul (by positivity) (by positivity), Real.log_sqrt hr.le, Real.log_sqrt hs.le]
  ring

/-- Literal actual chi kernel, with the full fixed physical window. -/
def physicalDegreeTwoKernel (N r s : ℕ) : ℂ :=
  ∫ t in physicalDegreeTwoScale N..2 * physicalDegreeTwoScale N,
    (bagPhysicalHeightWindow (t / physicalDegreeTwoScale N) : ℂ) *
      (_root_.RHTower.zetaChi (_root_.RHTower.linePt t) ^ (2 : ℤ) *
        Complex.exp (((((Real.log ((N : ℝ) + r) + Real.log ((N : ℝ) + s)) * t : ℝ) : ℂ) * I)))

/-- Source constants control every actual entry simultaneously, including physical transitions. -/
theorem exists_physicalDegreeTwoKernel_entry_error :
    ∃ Cm Ce : ℝ, 0 < Cm ∧ 0 < Ce ∧ ∀ N : ℕ, 1 ≤ N →
      ∀ r ∈ Finset.range (N + 1), ∀ s ∈ Finset.range (N + 1),
        ‖physicalDegreeTwoKernel N r s -
          physicalChiStationaryMain (physicalDegreeTwoScale N) (physicalDegreeTwoSaddle N r s) 2‖ ≤
            physicalDegreeTwoEntryBudget (physicalDegreeTwoScale N) Cm Ce := by
  obtain ⟨Cm, Ce, hCm, hCe, hb⟩ := exists_complete_physical_chi_positiveGrade_kernel
  refine ⟨Cm, Ce, hCm, hCe, ?_⟩
  intro N hN r hr s hs
  have hT := physicalDegreeTwoScale_ge_four hN
  have hT0 : 0 < physicalDegreeTwoScale N := by linarith only [hT]
  have ha := physicalDegreeTwoSaddle_mem hN hr hs
  have ha0 : 0 < physicalDegreeTwoSaddle N r s := hT0.trans_le ha.1
  have hratio : physicalDegreeTwoSaddle N r s / physicalDegreeTwoScale N ∈ Icc (1 / 2 : ℝ) 4 := by
    constructor
    · apply (le_div_iff₀ hT0).mpr
      linarith only [ha.1, hT0]
    · apply (div_le_iff₀ hT0).mpr
      linarith only [ha.2, hT0]
  have h := hb _ _ hT ha0 hratio 2 (by norm_num)
  norm_num only [Int.cast_ofNat, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  rw [physicalDegreeTwo_frequency hN] at h
  change ‖physicalDegreeTwoKernel N r s - _‖ ≤ _ at h
  apply h.trans
  unfold physicalDegreeTwoEntryBudget
  have hden : 0 < 2 * Real.sqrt (2 * physicalDegreeTwoScale N) := by positivity
  have hdenle : 2 * Real.sqrt (2 * physicalDegreeTwoScale N) ≤
      2 * Real.sqrt (2 * physicalDegreeTwoSaddle N r s) :=
    mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left ha.1 (by norm_num))) (by norm_num)
  have hc : physicalDegreeTwoSaddle N r s * Cm /
      (2 * physicalDegreeTwoSaddle N r s * Real.sqrt (2 * physicalDegreeTwoSaddle N r s)) =
      Cm / (2 * Real.sqrt (2 * physicalDegreeTwoSaddle N r s)) := by
    field_simp
  rw [hc]
  have hm := div_le_div_of_nonneg_left hCm.le hden hdenle
  linarith only [hm]

private theorem sum_norm_le_sqrt_card_energy (S : Finset ℕ) (c : ℕ → ℂ) :
    ∑ r ∈ S, ‖c r‖ ≤ Real.sqrt (S.card : ℝ) * Real.sqrt (∑ r ∈ S, ‖c r‖ ^ 2) := by
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
    Real.sum_mul_le_sqrt_mul_sqrt S (fun _ => (1 : ℝ)) (fun r => ‖c r‖)

private theorem norm_matrix_error_le (S : Finset ℕ) (K M : ℕ → ℕ → ℂ)
    {E : ℝ} (hE : 0 ≤ E) (hb : ∀ r ∈ S, ∀ s ∈ S, ‖K r s - M r s‖ ≤ E)
    (c d : ℕ → ℂ) :
    ‖(∑ r ∈ S, ∑ s ∈ S, c r * d s * K r s) -
      (∑ r ∈ S, ∑ s ∈ S, c r * d s * M r s)‖ ≤
        E * S.card * Real.sqrt (∑ r ∈ S, ‖c r‖ ^ 2) * Real.sqrt (∑ s ∈ S, ‖d s‖ ^ 2) := by
  have hsum : ‖(∑ r ∈ S, ∑ s ∈ S, c r * d s * K r s) -
      (∑ r ∈ S, ∑ s ∈ S, c r * d s * M r s)‖ ≤
      E * (∑ r ∈ S, ‖c r‖) * (∑ s ∈ S, ‖d s‖) := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← Finset.sum_sub_distrib, ← mul_sub]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ r ∈ S, ∑ s ∈ S, ‖c r‖ * ‖d s‖ * E := by
        apply Finset.sum_le_sum
        intro r hr
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro s hs
        rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_left (hb r hr s hs) (by positivity)
      _ = ∑ r ∈ S, (‖c r‖ * (∑ s ∈ S, ‖d s‖)) * E := by
        apply Finset.sum_congr rfl
        intro r _
        rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ = (∑ r ∈ S, ‖c r‖) * (∑ s ∈ S, ‖d s‖) * E := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ = _ := by ring
  apply hsum.trans
  have hc := sum_norm_le_sqrt_card_energy S c
  have hd := sum_norm_le_sqrt_card_energy S d
  have hm := mul_le_mul hc hd (by positivity) (by positivity)
  have hm' := mul_le_mul_of_nonneg_left hm hE
  have hs : Real.sqrt (S.card : ℝ) * Real.sqrt (S.card : ℝ) = S.card :=
    Real.mul_self_sqrt (by positivity)
  calc
    _ = E * ((∑ r ∈ S, ‖c r‖) * (∑ s ∈ S, ‖d s‖)) := by ring
    _ ≤ _ := hm'
    _ = E * (Real.sqrt (S.card : ℝ) * Real.sqrt (S.card : ℝ)) *
        Real.sqrt (∑ r ∈ S, ‖c r‖ ^ 2) * Real.sqrt (∑ s ∈ S, ‖d s‖ ^ 2) := by ring
    _ = _ := by rw [hs]

/-- Source stationary-matrix budget, keeping the actual physical window's Fourier norm. -/
def physicalDegreeTwoMainBudget (N : ℕ) : ℝ :=
  Real.sqrt (Real.pi * physicalDegreeTwoScale N) * physicalLogWindowFourierBudget *
    Real.sqrt (16 * (N : ℝ) * (1 + Real.log ((N + 1 : ℕ) : ℝ)))

/-- The complete actual degree-two matrix: the signed main retains cancellation, and every
stationary and chi/model remainder is paid in coefficient energy. -/
theorem exists_complete_physicalDegreeTwo_matrix_bound :
    ∃ Cm Ce : ℝ, 0 < Cm ∧ 0 < Ce ∧ ∀ N : ℕ, 1 ≤ N → ∀ c d : ℕ → ℂ,
      ‖∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
        c r * d s * physicalDegreeTwoKernel N r s‖ ≤
        (physicalDegreeTwoMainBudget N +
          physicalDegreeTwoEntryBudget (physicalDegreeTwoScale N) Cm Ce * (N + 1)) *
          Real.sqrt (∑ r ∈ Finset.range (N + 1), ‖c r‖ ^ 2) *
          Real.sqrt (∑ s ∈ Finset.range (N + 1), ‖d s‖ ^ 2) := by
  obtain ⟨Cm, Ce, hCm, hCe, hb⟩ := exists_physicalDegreeTwoKernel_entry_error
  refine ⟨Cm, Ce, hCm, hCe, ?_⟩
  intro N hN c d
  have hT := physicalDegreeTwoScale_ge_four hN
  have hT0 : 0 < physicalDegreeTwoScale N := by linarith only [hT]
  have hE : 0 ≤ physicalDegreeTwoEntryBudget (physicalDegreeTwoScale N) Cm Ce := by
    unfold physicalDegreeTwoEntryBudget
    positivity
  have he := norm_matrix_error_le (Finset.range (N + 1)) (physicalDegreeTwoKernel N)
    (fun r s => physicalChiStationaryMain (physicalDegreeTwoScale N) (physicalDegreeTwoSaddle N r s) 2)
    hE (hb N hN) c d
  have hm := norm_physicalChiStationaryMain_root_form_le hT0 hN c d
  change ‖∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
      c r * d s * physicalChiStationaryMain (physicalDegreeTwoScale N) (physicalDegreeTwoSaddle N r s) 2‖ ≤
    physicalDegreeTwoMainBudget N * _ * _ at hm
  have ht := norm_le_norm_sub_add (∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
    c r * d s * physicalDegreeTwoKernel N r s)
    (∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
      c r * d s * physicalChiStationaryMain (physicalDegreeTwoScale N) (physicalDegreeTwoSaddle N r s) 2)
  apply ht.trans ((add_le_add he hm).trans_eq _)
  simp only [Finset.card_range, Nat.cast_add, Nat.cast_one]
  ring

/-- Complete logarithmic exponential sum on the physical integer block. -/
def physicalDegreeTwoExponentialSum (N : ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ r ∈ Finset.range (N + 1), c r *
    Complex.exp ((((Real.log ((N : ℝ) + r) * t : ℝ) : ℂ) * I))

/-- Exact equality with the literal physical product integral; all entries and heights remain. -/
theorem integral_physicalDegreeTwo_product_eq (N : ℕ) (c d : ℕ → ℂ) :
    (∫ t in physicalDegreeTwoScale N..2 * physicalDegreeTwoScale N,
      (bagPhysicalHeightWindow (t / physicalDegreeTwoScale N) : ℂ) *
        (_root_.RHTower.zetaChi (_root_.RHTower.linePt t) ^ (2 : ℤ)) *
          (physicalDegreeTwoExponentialSum N c t * physicalDegreeTwoExponentialSum N d t)) =
      ∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1),
        c r * d s * physicalDegreeTwoKernel N r s := by
  let f : ℕ → ℕ → ℝ → ℂ := fun r s t => c r * d s *
    ((bagPhysicalHeightWindow (t / physicalDegreeTwoScale N) : ℂ) *
      (_root_.RHTower.zetaChi (_root_.RHTower.linePt t) ^ (2 : ℤ) *
        Complex.exp (((((Real.log ((N : ℝ) + r) + Real.log ((N : ℝ) + s)) * t : ℝ) : ℂ) * I))))
  have hc (r s : ℕ) : Continuous (f r s) :=
    continuous_const.mul ((Complex.continuous_ofReal.comp
      (bagPhysicalHeightWindow.continuous.comp (continuous_id.div_const _))).mul
      (_root_.RHTower.continuous_zetaChiCriticalGradeIntegrand 2 _))
  calc
    _ = ∫ t in physicalDegreeTwoScale N..2 * physicalDegreeTwoScale N,
        ∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1), f r s t := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only [physicalDegreeTwoExponentialSum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      apply Finset.sum_congr rfl
      intro s _
      dsimp only [f]
      rw [add_mul, Complex.ofReal_add, add_mul, Complex.exp_add]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_finsetSum (fun r _ =>
        (continuous_finsetSum _ (fun s _ => hc r s)).intervalIntegrable _ _)]
      apply Finset.sum_congr rfl
      intro r _
      rw [intervalIntegral.integral_finsetSum (fun s _ => (hc r s).intervalIntegrable _ _)]
      simp only [f, intervalIntegral.integral_const_mul, physicalDegreeTwoKernel]

/-- Unconditional source bound for the literal full physical chi-square product integral. -/
theorem exists_complete_physicalDegreeTwo_integral_bound :
    ∃ Cm Ce : ℝ, 0 < Cm ∧ 0 < Ce ∧ ∀ N : ℕ, 1 ≤ N → ∀ c d : ℕ → ℂ,
      ‖∫ t in physicalDegreeTwoScale N..2 * physicalDegreeTwoScale N,
        (bagPhysicalHeightWindow (t / physicalDegreeTwoScale N) : ℂ) *
          (_root_.RHTower.zetaChi (_root_.RHTower.linePt t) ^ (2 : ℤ)) *
            (physicalDegreeTwoExponentialSum N c t * physicalDegreeTwoExponentialSum N d t)‖ ≤
        (physicalDegreeTwoMainBudget N +
          physicalDegreeTwoEntryBudget (physicalDegreeTwoScale N) Cm Ce * (N + 1)) *
          Real.sqrt (∑ r ∈ Finset.range (N + 1), ‖c r‖ ^ 2) *
          Real.sqrt (∑ s ∈ Finset.range (N + 1), ‖d s‖ ^ 2) := by
  obtain ⟨Cm, Ce, hCm, hCe, hb⟩ := exists_complete_physicalDegreeTwo_matrix_bound
  refine ⟨Cm, Ce, hCm, hCe, ?_⟩
  intro N hN c d
  rw [integral_physicalDegreeTwo_product_eq]
  exact hb N hN c d

/-- The literal complete physical integral retains its signed stationary matrix with a
source-derived energy remainder. This preserves phase information needed for the self-target. -/
theorem exists_complete_physicalDegreeTwo_signed_approximation :
    ∃ Cm Ce : ℝ, 0 < Cm ∧ 0 < Ce ∧ ∀ N : ℕ, 1 ≤ N → ∀ c d : ℕ → ℂ,
      ‖(∫ t in physicalDegreeTwoScale N..2 * physicalDegreeTwoScale N,
          (bagPhysicalHeightWindow (t / physicalDegreeTwoScale N) : ℂ) *
            (_root_.RHTower.zetaChi (_root_.RHTower.linePt t) ^ (2 : ℤ)) *
              (physicalDegreeTwoExponentialSum N c t * physicalDegreeTwoExponentialSum N d t)) -
        (∑ r ∈ Finset.range (N + 1), ∑ s ∈ Finset.range (N + 1), c r * d s *
          physicalChiStationaryMain (physicalDegreeTwoScale N) (physicalDegreeTwoSaddle N r s) 2)‖ ≤
        physicalDegreeTwoEntryBudget (physicalDegreeTwoScale N) Cm Ce * (N + 1) *
          Real.sqrt (∑ r ∈ Finset.range (N + 1), ‖c r‖ ^ 2) *
          Real.sqrt (∑ s ∈ Finset.range (N + 1), ‖d s‖ ^ 2) := by
  obtain ⟨Cm, Ce, hCm, hCe, hb⟩ := exists_physicalDegreeTwoKernel_entry_error
  refine ⟨Cm, Ce, hCm, hCe, ?_⟩
  intro N hN c d
  have hT := physicalDegreeTwoScale_ge_four hN
  have hT0 : 0 < physicalDegreeTwoScale N := by linarith only [hT]
  have hE : 0 ≤ physicalDegreeTwoEntryBudget (physicalDegreeTwoScale N) Cm Ce := by
    unfold physicalDegreeTwoEntryBudget
    positivity
  rw [integral_physicalDegreeTwo_product_eq]
  simpa only [Finset.card_range, Nat.cast_add, Nat.cast_one] using
    norm_matrix_error_le (Finset.range (N + 1)) (physicalDegreeTwoKernel N)
      (fun r s => physicalChiStationaryMain (physicalDegreeTwoScale N) (physicalDegreeTwoSaddle N r s) 2)
      hE (hb N hN) c d

end GaloisForLFunctions.RHTower
