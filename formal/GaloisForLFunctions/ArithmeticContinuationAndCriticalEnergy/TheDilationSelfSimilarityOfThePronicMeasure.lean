import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ThePronicDilationContractionAndItsThreshold
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheMaxKernelFormOfTheDampingAutocorrelation

/-!
# The dilation self-similarity of the pronic measure

The pronic weight is not an arbitrary choice: it is *exactly* self-similar under integer dilation.
The horizons that a dilation by `j` folds onto one level `m` are `jm, …, jm + j − 1`, and the pronic
mass of that block telescopes:

`Σ_{n = jm}^{jm + j − 1} 1/(n(n+1)) = 1/(j · m(m+1))`
(`sum_Icc_pronic_dilation_fibre`),

exactly `1/j` times the pronic mass of the single level `m`.  So the dilation acts on the pronic
metric as an exact `1/√j` contraction (`pronicNorm_rowDilate_le_sharp`), and the factor is not an
artefact of an estimate: it is the self-similarity ratio of the measure the receiver is built with.

This sharpens the scale analysis of the continuation obstruction.  The off-diagonal dilation form
splits at any scale `J`: the head costs at most the explicit
`Σ_{2 ≤ j ≤ J} j^{-(ε + 1/2)}` times the energy
(`abs_pronicPairing_offDiagonalHead_le`), so the whole obstruction sits in the tail of the dilation
scales — and the head constant itself grows past one as `J` grows whenever `ε ≤ 1/2`, which is the
quantitative form of the wall.
-/

open Finset RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The exact self-similarity of the pronic mass -/

/-- **The pronic mass of a dilation fibre.**  The block of horizons folded onto the level `m` by a
dilation by `j` carries exactly `1/j` of the pronic mass of that level. -/
theorem sum_Icc_pronic_dilation_fibre {j m : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) :
    (∑ n ∈ Icc (j * m) (j * m + j - 1), 1 / ((n : ℝ) * ((n : ℝ) + 1))) =
      1 / ((j : ℝ) * ((m : ℝ) * ((m : ℝ) + 1))) := by
  have hjm : 1 ≤ j * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hle : j * m ≤ (j * m + j - 1) + 1 := by omega
  rw [sum_Icc_pronic_tail_mass hjm hle]
  have hcast : ((j * m + j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) * ((m : ℝ) + 1) := by
    have h : (j * m + j - 1 : ℕ) + 1 = j * m + j := by omega
    have h2 : ((j * m + j : ℕ) : ℝ) = (j : ℝ) * (m : ℝ) + (j : ℝ) := by push_cast; ring
    calc ((j * m + j - 1 : ℕ) : ℝ) + 1 = ((j * m + j - 1 + 1 : ℕ) : ℝ) := by push_cast; ring
      _ = ((j * m + j : ℕ) : ℝ) := by rw [h]
      _ = (j : ℝ) * (m : ℝ) + (j : ℝ) := h2
      _ = (j : ℝ) * ((m : ℝ) + 1) := by ring
  rw [hcast]
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hjmR : ((j * m : ℕ) : ℝ) = (j : ℝ) * (m : ℝ) := by push_cast; ring
  rw [hjmR]
  field_simp
  ring

/-- **The sharp pronic dilation contraction.**  The dilation by `j` contracts the pronic norm by
exactly the self-similarity ratio `1/√j`. -/
theorem pronicNorm_rowDilate_le_sharp {j : ℕ} (hj : 1 ≤ j) (T : ℕ) (v : ℕ → ℝ) (hv0 : v 0 = 0) :
    pronicNorm T (rowDilate j v) ≤ (1 / Real.sqrt (j : ℝ)) * pronicNorm T v := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hsqj : 0 < Real.sqrt (j : ℝ) := Real.sqrt_pos.mpr hj0
  have hsq : pronicNorm T (rowDilate j v) ^ 2 ≤ (1 / (j : ℝ)) * pronicNorm T v ^ 2 := by
    rw [pronicNorm_sq, pronicNorm_sq]
    have hmaps : ∀ n ∈ Icc 1 T, n / j ∈ range (T + 1) := by
      intro n hn
      rw [mem_Icc] at hn
      rw [mem_range]
      have := Nat.div_le_self n j
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun n => rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))]
    have hfiber : ∀ m ∈ range (T + 1),
        (∑ n ∈ (Icc 1 T).filter (fun n => n / j = m),
            rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
          (1 / (j : ℝ)) * (if m = 0 then 0 else v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1))) := by
      intro m _
      rcases Nat.eq_zero_or_pos m with rfl | hm1
      · have hzero : ∀ n ∈ (Icc 1 T).filter (fun n => n / j = 0),
            rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) = 0 := by
          intro n hn
          rw [Finset.mem_filter] at hn
          rw [rowDilate, hn.2, hv0]
          simp
        rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
        simp
      · rw [if_neg (by omega : m ≠ 0)]
        have hsub : (Icc 1 T).filter (fun n => n / j = m) ⊆ Icc (j * m) (j * m + j - 1) := by
          intro n hn
          rw [Finset.mem_filter, mem_Icc] at hn
          rw [mem_Icc]
          have hge : j * m ≤ n := by
            rw [← hn.2]
            exact Nat.mul_div_le n j
          have hlt : n < (m + 1) * j := by
            rw [← Nat.div_lt_iff_lt_mul (by omega : 0 < j)]
            omega
          have heq : (m + 1) * j = j * m + j := by ring
          exact ⟨hge, by omega⟩
        -- on the fibre the dilated row is constant, so the mass identity applies
        have hconst : ∀ n ∈ (Icc 1 T).filter (fun n => n / j = m),
            rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
              v m ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
          intro n hn
          rw [Finset.mem_filter] at hn
          rw [rowDilate, hn.2]
          ring
        rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum]
        have hmass : (∑ n ∈ (Icc 1 T).filter (fun n => n / j = m),
            1 / ((n : ℝ) * ((n : ℝ) + 1))) ≤
            1 / ((j : ℝ) * ((m : ℝ) * ((m : ℝ) + 1))) := by
          rw [← sum_Icc_pronic_dilation_fibre hj hm1]
          exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => by
            have hn1 : 1 ≤ n := by
              rw [mem_Icc] at hn
              have : 1 ≤ j * m := Nat.one_le_iff_ne_zero.mpr
                (Nat.mul_ne_zero (by omega) (by omega))
              omega
            have : (0 : ℝ) < n := by exact_mod_cast hn1
            positivity
        have hv2 : (0 : ℝ) ≤ v m ^ 2 := sq_nonneg _
        have hstep := mul_le_mul_of_nonneg_left hmass hv2
        have hre : v m ^ 2 * (1 / ((j : ℝ) * ((m : ℝ) * ((m : ℝ) + 1)))) =
            1 / (j : ℝ) * (v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1))) := by
          field_simp
        linarith [hstep, hre.le, hre.ge]
    refine le_trans (Finset.sum_le_sum hfiber) ?_
    rw [← Finset.mul_sum]
    have hsplit : (∑ m ∈ range (T + 1),
        (if m = 0 then 0 else v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1)))) =
        ∑ m ∈ Icc 1 T, v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1)) := by
      have hins : (range (T + 1) : Finset ℕ) = insert 0 (Icc 1 T) := by
        ext m
        rw [mem_range, Finset.mem_insert, mem_Icc]
        omega
      rw [hins, Finset.sum_insert (by simp), if_pos rfl, zero_add]
      exact Finset.sum_congr rfl fun m hm => by
        rw [mem_Icc] at hm
        rw [if_neg (by omega : m ≠ 0)]
    rw [hsplit]
  have hA := pronicNorm_nonneg T (rowDilate j v)
  have hB := pronicNorm_nonneg T v
  have hC : 0 ≤ 1 / Real.sqrt (j : ℝ) := by positivity
  have hCsq : (1 / Real.sqrt (j : ℝ)) ^ 2 = 1 / (j : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt hj0.le]
  have hCB : 0 ≤ (1 / Real.sqrt (j : ℝ)) * pronicNorm T v := mul_nonneg hC hB
  have hAB : pronicNorm T (rowDilate j v) ^ 2 ≤
      ((1 / Real.sqrt (j : ℝ)) * pronicNorm T v) ^ 2 := by
    rw [mul_pow, hCsq]
    exact hsq
  exact (pow_le_pow_iff_left₀ hA hCB two_ne_zero).mp hAB

/-! ## §2. The head of the dilation scales is always paid -/

/-- The off-diagonal dilation restricted to the scales below `J`. -/
def offDiagonalUnitDilationHead (ε : ℝ) (J : ℕ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 2 (min J n), (j : ℝ) ^ (-ε) * pmPowerDampedCenteredDivisorPrefix ε (n / j)

/-- **The head is paid by the explicit scale sum.**  Only the tail of the dilation scales can
obstruct: every finite head of the off-diagonal form is bounded by an explicit multiple of the
energy. -/
theorem abs_pronicPairing_offDiagonalHead_le (ε : ℝ) (J T : ℕ) :
    |pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε)
        (offDiagonalUnitDilationHead ε J)| ≤
      (∑ j ∈ Icc 2 J, (j : ℝ) ^ (-ε) * (1 / Real.sqrt (j : ℝ))) * dampedMobiusEnergy ε T := by
  have hE := dampedMobiusEnergy_nonneg ε T
  have hsqrtE : Real.sqrt (dampedMobiusEnergy ε T) ^ 2 = dampedMobiusEnergy ε T :=
    Real.sq_sqrt hE
  have hsqrt0 : 0 ≤ Real.sqrt (dampedMobiusEnergy ε T) := Real.sqrt_nonneg _
  have hS : 0 ≤ ∑ j ∈ Icc 2 J, (j : ℝ) ^ (-ε) * (1 / Real.sqrt (j : ℝ)) :=
    Finset.sum_nonneg fun j _ => by positivity
  -- the head is a finite sum of dilations with the scales capped at `J`
  have hext : ∀ n ∈ Icc 1 T, offDiagonalUnitDilationHead ε J n =
      ∑ j ∈ Icc 2 J, (j : ℝ) ^ (-ε) *
        rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n := by
    intro n hn
    rw [mem_Icc] at hn
    rw [offDiagonalUnitDilationHead]
    have hsub : (Icc 2 (min J n) : Finset ℕ) ⊆ Icc 2 J := by
      intro j hj
      rw [mem_Icc] at hj ⊢
      exact ⟨hj.1, le_trans hj.2 (min_le_left J n)⟩
    rw [← Finset.sum_subset hsub]
    · exact Finset.sum_congr rfl fun j _ => by rw [rowDilate]
    · intro j hjJ hjmin
      rw [mem_Icc] at hjJ hjmin
      have hjn : n < j := by
        by_contra hcon
        exact hjmin ⟨hjJ.1, le_min hjJ.2 (by omega)⟩
      have hzero : n / j = 0 := Nat.div_eq_of_lt hjn
      rw [rowDilate, hzero, pmPowerDampedCenteredDivisorPrefix_zero]
      ring
  have hnorm : pronicNorm T (offDiagonalUnitDilationHead ε J) ≤
      (∑ j ∈ Icc 2 J, (j : ℝ) ^ (-ε) * (1 / Real.sqrt (j : ℝ))) *
        Real.sqrt (dampedMobiusEnergy ε T) := by
    rw [pronicNorm_congr hext]
    refine (pronicNorm_sum_le T (Icc 2 J)
      (fun j n => (j : ℝ) ^ (-ε) *
        rowDilate j (pmPowerDampedCenteredDivisorPrefix ε) n)).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hj1 : 1 ≤ j := by
      rw [mem_Icc] at hj
      omega
    have hrpow : (0 : ℝ) ≤ (j : ℝ) ^ (-ε) := Real.rpow_nonneg (Nat.cast_nonneg j) _
    rw [pronicNorm_const_mul hrpow, ← pronicNorm_centeredPrefix ε T, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (pronicNorm_rowDilate_le_sharp hj1 T _ (pmPowerDampedCenteredDivisorPrefix_zero ε)) hrpow
  have hcs : ∀ u : ℕ → ℝ, pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) u ≤
      Real.sqrt (dampedMobiusEnergy ε T) * pronicNorm T u := by
    intro u
    have h := sum_mul_div_le_pronicNorm T (pmPowerDampedCenteredDivisorPrefix ε) u
    rw [pronicNorm_centeredPrefix] at h
    exact h
  have hpos := hcs (offDiagonalUnitDilationHead ε J)
  have hneg := hcs (fun n => -offDiagonalUnitDilationHead ε J n)
  rw [pronicNorm_neg] at hneg
  have hnegeq : pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε)
      (fun n => -offDiagonalUnitDilationHead ε J n) =
      -pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε)
        (offDiagonalUnitDilationHead ε J) := by
    unfold pronicPairing
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hnegeq] at hneg
  have hbound : Real.sqrt (dampedMobiusEnergy ε T) *
      pronicNorm T (offDiagonalUnitDilationHead ε J) ≤
      (∑ j ∈ Icc 2 J, (j : ℝ) ^ (-ε) * (1 / Real.sqrt (j : ℝ))) * dampedMobiusEnergy ε T := by
    have := mul_le_mul_of_nonneg_left hnorm hsqrt0
    nlinarith [hsqrtE, hS, hsqrt0]
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
