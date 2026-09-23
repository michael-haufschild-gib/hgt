import GaloisForLFunctions.RHTower.CCMUnitRieszCoherentOutgoingChargeHankel

/-!
# Signed quarter-dilation flux of the Suzuki prime outgoing charge

The coherent prime outgoing charge is not a local prime-counting observable: when its aperture
changes from `N` to `N + 1`, the newly available prime has exactly zero endpoint weight.  The
entire increment is a signed dilation flux carried by every earlier prime.  Its sign is rigid:
indices through `N / 4` contribute inward debt, while every remaining source index contributes
outward gain.  Thus any SP-E conservation law must compare these two global channels before
attempting a positive-energy estimate.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- One-step dilation weight of the coherent prime outgoing charge. -/
def unitRieszCoherentOutgoingDilationWeight (N k : ℕ) : ℝ :=
  (1 / Real.sqrt ((N + 1 : ℕ) : ℝ) - 1 / Real.sqrt (N : ℝ)) +
    Real.sqrt (k : ℝ) * (1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ))

private theorem exp_neg_log_ratio_half_eq_sqrt_div
    {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    Real.exp (-(Real.log (N : ℝ) - Real.log (k : ℝ)) / 2) =
      Real.sqrt ((k : ℝ) / N) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast lt_of_lt_of_le hk hkN
  have hfull : Real.exp (-(Real.log (N : ℝ) - Real.log (k : ℝ))) = (k : ℝ) / N := by
    rw [neg_sub, Real.exp_sub, Real.exp_log hkR, Real.exp_log hNR]
  have hhalfSq : Real.exp (-(Real.log (N : ℝ) - Real.log (k : ℝ)) / 2) ^ (2 : ℕ) =
      (k : ℝ) / N := by
    rw [pow_two, ← Real.exp_add]
    convert hfull using 1
    ring
  have hratio : 0 ≤ (k : ℝ) / N := div_nonneg hkR.le hNR.le
  have hsqrtSq : Real.sqrt ((k : ℝ) / N) ^ (2 : ℕ) = (k : ℝ) / N :=
    Real.sq_sqrt hratio
  nlinarith [Real.exp_pos (-(Real.log (N : ℝ) - Real.log (k : ℝ)) / 2),
    Real.sqrt_nonneg ((k : ℝ) / N)]

private theorem outgoing_summand_eq_dilation_normalForm
    {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    (ArithmeticFunction.vonMangoldt k / Real.sqrt (N : ℝ)) *
        (1 - Real.exp (-(Real.log (N : ℝ) - Real.log (k : ℝ)) / 2)) =
      ArithmeticFunction.vonMangoldt k *
        (1 / Real.sqrt (N : ℝ) - Real.sqrt (k : ℝ) / N) := by
  rw [exp_neg_log_ratio_half_eq_sqrt_div hk hkN,
    Real.sqrt_div (Nat.cast_nonneg k) (N : ℝ)]
  have hNR : (0 : ℝ) < N := by exact_mod_cast lt_of_lt_of_le hk hkN
  have hsN : Real.sqrt (N : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNR).ne'
  have hsN2 : Real.sqrt (N : ℝ) ^ (2 : ℕ) = N := Real.sq_sqrt hNR.le
  field_simp [hsN]
  calc
    ArithmeticFunction.vonMangoldt k * (Real.sqrt (N : ℝ) - Real.sqrt (k : ℝ)) * N =
        ArithmeticFunction.vonMangoldt k * (Real.sqrt (N : ℝ) - Real.sqrt (k : ℝ)) *
          Real.sqrt (N : ℝ) ^ (2 : ℕ) := by rw [hsN2]
    _ = ArithmeticFunction.vonMangoldt k * Real.sqrt (N : ℝ) *
          (Real.sqrt (N : ℝ) ^ (2 : ℕ) - Real.sqrt (N : ℝ) * Real.sqrt (k : ℝ)) := by ring
    _ = ArithmeticFunction.vonMangoldt k * Real.sqrt (N : ℝ) *
          (N - Real.sqrt (N : ℝ) * Real.sqrt (k : ℝ)) := by rw [hsN2]

/-- Exact square-root dilation form of every coherent prime outgoing charge. -/
theorem unitRieszCoherentPrimeOutgoingCharge_eq_dilation_normalForm
    (N : ℕ) :
    unitRieszCoherentPrimeOutgoingCharge N =
      ∑ k ∈ Finset.Icc 2 N,
        ArithmeticFunction.vonMangoldt k *
          (1 / Real.sqrt (N : ℝ) - Real.sqrt (k : ℝ) / N) := by
  unfold unitRieszCoherentPrimeOutgoingCharge
  apply Finset.sum_congr rfl
  intro k hk
  exact outgoing_summand_eq_dilation_normalForm
    (lt_of_lt_of_le Nat.zero_lt_two (Finset.mem_Icc.mp hk).1)
    (Finset.mem_Icc.mp hk).2

/-- The new endpoint prime has zero outgoing weight.  The full one-step change is therefore a
global signed dilation flux over the preceding prime history. -/
theorem unitRieszCoherentPrimeOutgoingCharge_succ_sub_eq_dilationFlux
    {N : ℕ} (hN : 2 ≤ N) :
    unitRieszCoherentPrimeOutgoingCharge (N + 1) -
        unitRieszCoherentPrimeOutgoingCharge N =
      ∑ k ∈ Finset.Icc 2 N,
        ArithmeticFunction.vonMangoldt k * unitRieszCoherentOutgoingDilationWeight N k := by
  rw [unitRieszCoherentPrimeOutgoingCharge_eq_dilation_normalForm (N + 1),
    unitRieszCoherentPrimeOutgoingCharge_eq_dilation_normalForm N]
  rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ N + 1)]
  have hnew : ArithmeticFunction.vonMangoldt (N + 1) *
      (1 / Real.sqrt ((N + 1 : ℕ) : ℝ) - Real.sqrt ((N + 1 : ℕ) : ℝ) / (N + 1 : ℕ)) = 0 := by
    have hNp : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hsNp : Real.sqrt ((N + 1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNp).ne'
    have hsNp2 : Real.sqrt ((N + 1 : ℕ) : ℝ) ^ (2 : ℕ) = (N : ℝ) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using Real.sq_sqrt hNp.le
    field_simp [hsNp]
    rw [hsNp2]
    norm_num
  rw [hnew, add_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  unfold unitRieszCoherentOutgoingDilationWeight
  ring

private theorem dilation_weight_algebra {a b c n : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ha2 : a ^ (2 : ℕ) = n) (hb2 : b ^ (2 : ℕ) = n + 1) :
    (1 / b - 1 / a) + c * (1 / n - 1 / (n + 1)) =
      (c * (a + b) - a * b) / (n * (n + 1) * (a + b)) := by
  have hab : a + b ≠ 0 := by positivity
  have hn : n ≠ 0 := by nlinarith
  have hnp : n + 1 ≠ 0 := by nlinarith
  have hprod : a ^ (2 : ℕ) * b ^ (2 : ℕ) = n * (n + 1) := by
    rw [ha2, hb2]
  field_simp [ha.ne', hb.ne', hab, hn, hnp]
  linear_combination (2 * b ^ (2 : ℕ) + n + n ^ (2 : ℕ)) * ha2 +
    (n - n ^ (2 : ℕ)) * hb2 - hprod

private theorem outgoingDilationWeight_eq_signedScale
    {N k : ℕ} (hN : 0 < N) :
    unitRieszCoherentOutgoingDilationWeight N k =
      (Real.sqrt (k : ℝ) *
          (Real.sqrt (N : ℝ) + Real.sqrt ((N + 1 : ℕ) : ℝ)) -
        Real.sqrt (N : ℝ) * Real.sqrt ((N + 1 : ℕ) : ℝ)) /
        ((N : ℝ) * ((N + 1 : ℕ) : ℝ) *
          (Real.sqrt (N : ℝ) + Real.sqrt ((N + 1 : ℕ) : ℝ))) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNpR : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hsN2 : Real.sqrt (N : ℝ) ^ (2 : ℕ) = N := Real.sq_sqrt hNR.le
  have hsNp2 : Real.sqrt ((N + 1 : ℕ) : ℝ) ^ (2 : ℕ) = (N : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Real.sq_sqrt hNpR.le
  simpa only [unitRieszCoherentOutgoingDilationWeight, Nat.cast_add, Nat.cast_one] using
    (dilation_weight_algebra (a := Real.sqrt (N : ℝ))
      (b := Real.sqrt ((N + 1 : ℕ) : ℝ)) (c := Real.sqrt (k : ℝ))
      (n := (N : ℝ)) (Real.sqrt_pos.mpr hNR) (Real.sqrt_pos.mpr hNpR)
      hsN2 hsNp2)

/-- The dilation weight is nonpositive at and below the exact quarter threshold. -/
theorem unitRieszCoherentOutgoingDilationWeight_nonpos_of_four_mul_le
    {N k : ℕ} (hN : 0 < N) (hk : 4 * k ≤ N) :
    unitRieszCoherentOutgoingDilationWeight N k ≤ 0 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hfour : (4 : ℝ) * k ≤ N := by exact_mod_cast hk
  have hNNp : (N : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast (Nat.le_succ N)
  have hsN0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hquarter : Real.sqrt (k : ℝ) ≤ Real.sqrt (N : ℝ) / 2 := by
    have hroot : 2 * Real.sqrt (k : ℝ) ≤ Real.sqrt (N : ℝ) := by
      calc
        2 * Real.sqrt (k : ℝ) = Real.sqrt ((4 : ℝ) * k) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
        _ ≤ Real.sqrt (N : ℝ) := Real.sqrt_le_sqrt hfour
    linarith
  rw [outgoingDilationWeight_eq_signedScale hN]
  apply div_nonpos_of_nonpos_of_nonneg
  · have hsum0 : 0 ≤ Real.sqrt (N : ℝ) + Real.sqrt ((N + 1 : ℕ) : ℝ) := by positivity
    have hfirst := mul_le_mul_of_nonneg_right hquarter hsum0
    have hsecond : (Real.sqrt (N : ℝ) / 2) *
        (Real.sqrt (N : ℝ) + Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
        Real.sqrt (N : ℝ) * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
      have hsNNp : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt hNNp
      nlinarith [mul_nonneg hsN0 (sub_nonneg.mpr hsNNp)]
    linarith
  · positivity

/-- The dilation weight is nonnegative from the exact successor-quarter threshold onward. -/
theorem unitRieszCoherentOutgoingDilationWeight_nonneg_of_succ_le_four_mul
    {N k : ℕ} (hN : 0 < N) (hk : N + 1 ≤ 4 * k) :
    0 ≤ unitRieszCoherentOutgoingDilationWeight N k := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNpR : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hfour : (N + 1 : ℕ) ≤ (4 : ℝ) * k := by exact_mod_cast hk
  have hNNp : (N : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast (Nat.le_succ N)
  have hsNp0 : 0 ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) := Real.sqrt_nonneg _
  have hquarter : Real.sqrt ((N + 1 : ℕ) : ℝ) / 2 ≤ Real.sqrt (k : ℝ) := by
    have hroot : Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (k : ℝ) := by
      calc
        Real.sqrt ((N + 1 : ℕ) : ℝ) ≤ Real.sqrt ((4 : ℝ) * k) :=
          Real.sqrt_le_sqrt hfour
        _ = 2 * Real.sqrt (k : ℝ) := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
          norm_num
    linarith
  rw [outgoingDilationWeight_eq_signedScale hN]
  apply div_nonneg
  · have hsum0 : 0 ≤ Real.sqrt (N : ℝ) + Real.sqrt ((N + 1 : ℕ) : ℝ) := by positivity
    have hfirst := mul_le_mul_of_nonneg_right hquarter hsum0
    have hsecond : Real.sqrt (N : ℝ) * Real.sqrt ((N + 1 : ℕ) : ℝ) ≤
        (Real.sqrt ((N + 1 : ℕ) : ℝ) / 2) *
          (Real.sqrt (N : ℝ) + Real.sqrt ((N + 1 : ℕ) : ℝ)) := by
      have hsNNp : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt hNNp
      nlinarith [mul_nonneg hsNp0 (sub_nonneg.mpr hsNNp)]
    linarith
  · positivity

/-- Total nonnegative inward quarter-dilation debt of the outgoing prime charge. -/
def unitRieszCoherentOutgoingQuarterDilationDebt (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (N / 4),
    ArithmeticFunction.vonMangoldt k * (-unitRieszCoherentOutgoingDilationWeight N k)

/-- Total nonnegative outward quarter-dilation gain of the outgoing prime charge. -/
def unitRieszCoherentOutgoingQuarterDilationGain (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (max 2 (N / 4 + 1)) N,
    ArithmeticFunction.vonMangoldt k * unitRieszCoherentOutgoingDilationWeight N k

theorem unitRieszCoherentOutgoingQuarterDilationDebt_nonneg (N : ℕ) :
    0 ≤ unitRieszCoherentOutgoingQuarterDilationDebt N := by
  unfold unitRieszCoherentOutgoingQuarterDilationDebt
  apply Finset.sum_nonneg
  intro k hk
  have hkmem := Finset.mem_Icc.mp hk
  have hkfour : 4 * k ≤ N := by omega
  have hNpos : 0 < N := by omega
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (neg_nonneg.mpr (unitRieszCoherentOutgoingDilationWeight_nonpos_of_four_mul_le
      hNpos hkfour))

theorem unitRieszCoherentOutgoingQuarterDilationGain_nonneg (N : ℕ) :
    0 ≤ unitRieszCoherentOutgoingQuarterDilationGain N := by
  unfold unitRieszCoherentOutgoingQuarterDilationGain
  apply Finset.sum_nonneg
  intro k hk
  have hkmem := Finset.mem_Icc.mp hk
  have hkfour : N + 1 ≤ 4 * k := by
    have hfloor : N / 4 + 1 ≤ k := le_trans (le_max_right _ _) hkmem.1
    omega
  have hNpos : 0 < N := by omega
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (unitRieszCoherentOutgoingDilationWeight_nonneg_of_succ_le_four_mul
      hNpos hkfour)

/-- **Quarter-dilation flux law.**  A one-step aperture change has no local new-prime term:
it is exactly outward prime gain minus inward prime debt, split at `N / 4`. -/
theorem unitRieszCoherentPrimeOutgoingCharge_succ_sub_eq_quarterDilationGain_sub_debt
    {N : ℕ} (hN : 2 ≤ N) :
    unitRieszCoherentPrimeOutgoingCharge (N + 1) -
        unitRieszCoherentPrimeOutgoingCharge N =
      unitRieszCoherentOutgoingQuarterDilationGain N -
        unitRieszCoherentOutgoingQuarterDilationDebt N := by
  rw [unitRieszCoherentPrimeOutgoingCharge_succ_sub_eq_dilationFlux hN]
  let w : ℕ → ℝ := fun k =>
    ArithmeticFunction.vonMangoldt k * unitRieszCoherentOutgoingDilationWeight N k
  have hpartition : Finset.Icc 2 N =
      Finset.Icc 2 (N / 4) ∪ Finset.Icc (max 2 (N / 4 + 1)) N := by
    ext k
    constructor
    · intro hk
      have hkmem := Finset.mem_Icc.mp hk
      by_cases hlow : k ≤ N / 4
      · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hkmem.1, hlow⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Icc.mpr ⟨by
          apply max_le
          · exact hkmem.1
          · omega, hkmem.2⟩)
    · intro hk
      rcases Finset.mem_union.mp hk with hlow | hhigh
      · have hmem := Finset.mem_Icc.mp hlow
        exact Finset.mem_Icc.mpr ⟨hmem.1, hmem.2.trans (Nat.div_le_self N 4)⟩
      · have hmem := Finset.mem_Icc.mp hhigh
        exact Finset.mem_Icc.mpr ⟨by omega, hmem.2⟩
  have hdisj : Disjoint (Finset.Icc 2 (N / 4))
      (Finset.Icc (max 2 (N / 4 + 1)) N) := by
    rw [Finset.disjoint_left]
    intro k hk hhigh
    simp only [Finset.mem_Icc] at hk hhigh
    omega
  change (∑ k ∈ Finset.Icc 2 N, w k) = _
  rw [hpartition, Finset.sum_union hdisj]
  have hlow : (∑ k ∈ Finset.Icc 2 (N / 4), w k) =
      -unitRieszCoherentOutgoingQuarterDilationDebt N := by
    rw [unitRieszCoherentOutgoingQuarterDilationDebt, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only [w]
    ring
  rw [hlow]
  change -unitRieszCoherentOutgoingQuarterDilationDebt N +
      unitRieszCoherentOutgoingQuarterDilationGain N = _
  ring

end GaloisForLFunctions.RHTower
