import GaloisForLFunctions.RHTower.WeilPaperPacketOrthogonality
import GaloisForLFunctions.RHTower.WeilWorkPBAPNullRepair

/-!
# Exact positive repair under a controlled covariance change

Actual smooth Gram packet mixtures admit positive finite corrections transporting
all integer logarithmic defects between two coefficient matrices. The Crouzeix
covariance gap pays an explicit bound on the correction's full Weil energy.
-/

open Matrix Complex MeasureTheory Zeta23 GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexConjugate Matrix

noncomputable section

namespace RHTower.WeilWorkPBAP

open WeilOneSided WeilSpectral

/-- The actual smooth packet mixture associated with arbitrary coefficient columns. -/
def packetColumnMixture {N : ℕ} {ι : Type*} [Fintype ι] (L : ℕ)
    (A : Matrix (PacketIndex N) ι ℂ) : WeilTestFn →₀ ℝ :=
  ∑ i, Finsupp.single (gramPacketFn N (L + 1) (packetColumn A i)) 1

theorem packetColumnMixture_nonneg {N : ℕ} {ι : Type*} [Fintype ι] (L : ℕ)
    (A : Matrix (PacketIndex N) ι ℂ) (f : WeilTestFn) :
    0 ≤ packetColumnMixture L A f := by
  have h : 0 ≤ packetColumnMixture L A := Finset.sum_nonneg
    (fun i _ => Finsupp.single_nonneg.mpr (show (0 : ℝ) ≤ 1 by positivity))
  exact h f

theorem energy_packetColumnMixture {N : ℕ} {ι : Type*} [Fintype ι] (L : ℕ)
    (A : Matrix (PacketIndex N) ι ℂ) :
    energy (packetColumnMixture L A) = packetArchEnergy (L + 1) A := by
  rw [packetColumnMixture, map_sum]
  simp only [energy, Finsupp.linearCombination_single, one_smul,
    packetArchEnergy, gramPacketFn]

private theorem packetColumn_rational_sample {N : ℕ} {ι : Type*}
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (i : ι) {n : ℕ} (hn : 1 ≤ n) :
    EF.weilTest (gramPacket N (L + 1) (packetColumn A i))
      (gramPacket N (L + 1) (packetColumn A i)) (Real.log n) =
        (packetMass N (L + 1) : ℂ) * ∑ m : PacketIndex N, ∑ k : PacketIndex N,
          if n * (k : ℕ) = (m : ℕ) then A m i * conj (A k i) else 0 := by
  have h := gramPacket_rational_sample N (L + 1) (packetColumn A i)
    (a := n) (b := 1) hn le_rfl (by omega)
  simp only [Nat.cast_one, Real.log_one, sub_zero, one_mul] at h
  rw [h]
  simp_rw [Finset.sum_subtype (p := fun m : ℕ => m ∈ Finset.Icc 1 N)
    (Finset.Icc 1 N) (fun _ => Iff.rfl)]
  simp only [packetColumn, dif_pos, Subtype.property]

private theorem packetColumnMixture_sample {N : ℕ} {ι : Type*} [Fintype ι]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) {n : ℕ} (hn : 1 ≤ n) :
    (∑ i, EF.weilTest (gramPacket N (L + 1) (packetColumn A i))
      (gramPacket N (L + 1) (packetColumn A i)) (Real.log n)) =
        (packetMass N (L + 1) : ℂ) * divisibilityTrace (A * Aᴴ) n := by
  simp_rw [packetColumn_rational_sample L A _ hn]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  unfold divisibilityTrace
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp [Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- Exact logarithmic defect of the actual packet mixture. -/
theorem defect_packetColumnMixture {N : ℕ} {ι : Type*} [Fintype ι]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (j : LogIndex) :
    defect (packetColumnMixture L A) j =
      (2 * packetMass N (L + 1) / Real.sqrt (j : ℝ)) *
        (divisibilityTrace (A * Aᴴ) j).re := by
  rw [packetColumnMixture, map_sum]
  simp only [defect, Finsupp.linearCombination_single, one_smul,
    Finsupp.finsetSum_apply, logVector_apply]
  change (∑ i, logValue (gramPacket N (L + 1) (packetColumn A i)) j) = _
  simp only [logValue,
    weilTest_self_neg, Complex.add_re, Complex.conj_re]
  simp_rw [← two_mul, ← Finset.sum_div, ← Finset.mul_sum, ← Complex.re_sum]
  rw [packetColumnMixture_sample L A (by omega : 1 ≤ (j : ℕ))]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The finite set that contains every integer defect of an `N`-label packet. -/
def packetLogIndices (N : ℕ) : Finset LogIndex :=
  (Finset.range (N + 1)).subtype (fun n => 2 ≤ n)

@[simp] theorem mem_packetLogIndices (N : ℕ) (j : LogIndex) :
    j ∈ packetLogIndices N ↔ (j : ℕ) ≤ N := by
  simp [packetLogIndices]

theorem defect_packetColumnMixture_eq_zero_above {N : ℕ} {ι : Type*} [Fintype ι]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (j : LogIndex) (hj : N < (j : ℕ)) :
    defect (packetColumnMixture L A) j = 0 := by
  rw [defect_packetColumnMixture, divisibilityTrace_eq_zero_above _ hj]
  simp

/-- The positive correction that makes the first mixture carry the second's integer defects. -/
def packetTransferRepair {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    WeilTestFn →₀ ℝ :=
  packetColumnMixture L A +
    repair (defect (packetColumnMixture L B) - defect (packetColumnMixture L A))

theorem packetTransferRepair_nonneg {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ)
    (f : WeilTestFn) : 0 ≤ packetTransferRepair L A B f :=
  add_nonneg (packetColumnMixture_nonneg L A f) (repair_nonneg _ f)

/-- Every integer defect is transported exactly, without a cutoff premise. -/
theorem defect_packetTransferRepair {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    defect (packetTransferRepair L A B) = defect (packetColumnMixture L B) := by
  rw [packetTransferRepair, map_add, defect_repair, add_sub_cancel]

/-- Exact equality of all integer logarithmic samples after positive repair. -/
theorem logValue_packetTransferRepair {N : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ)
    (n : ℕ) (hn : 2 ≤ n) :
    (packetTransferRepair L A B).sum (fun f t => t * logValue f.1 n) =
      (packetColumnMixture L B).sum (fun f t => t * logValue f.1 n) := by
  have h := congrArg (fun b : LogIndex →₀ ℝ => b ⟨n, hn⟩)
    (defect_packetTransferRepair L A B)
  simpa only [defect, linearCombination_logVector_apply] using h

/-- Energy price per unit of one covariance multiplicative diagonal. -/
def packetRepairWeight (N L : ℕ) (j : LogIndex) : ℝ :=
  (2 * packetMass N (L + 1) / Real.sqrt (j : ℝ)) * atomCost j

theorem packetRepairWeight_nonneg (N L : ℕ) (j : LogIndex) :
    0 ≤ packetRepairWeight N L j := by
  have hm := packetMass_pos N (L + 1)
  have hc := atomCost_nonneg j
  unfold packetRepairWeight
  positivity

/-- Explicit finite sensitivity of positive correction, including its full archimedean costs. -/
def packetRepairSensitivity (N L : ℕ) : ℝ :=
  ∑ j ∈ packetLogIndices N, packetRepairWeight N L j ^ 2 * packetDivisibilityMass N j

theorem packetRepairSensitivity_nonneg (N L : ℕ) : 0 ≤ packetRepairSensitivity N L := by
  unfold packetRepairSensitivity
  exact Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (packetDivisibilityMass_nonneg _ _)

/-- Bound the actual positive correction budget by its weighted covariance traces. -/
theorem packetRepairBudget_le_weighted_trace {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    repairBudget (defect (packetColumnMixture L B) - defect (packetColumnMixture L A)) ≤
      ∑ j ∈ packetLogIndices N, packetRepairWeight N L j *
        ‖divisibilityTrace (A * Aᴴ) j - divisibilityTrace (B * Bᴴ) j‖ := by
  classical
  let d := defect (packetColumnMixture L B) - defect (packetColumnMixture L A)
  let δ (j : LogIndex) := divisibilityTrace (A * Aᴴ) j - divisibilityTrace (B * Bᴴ) j
  have hsupp : d.support ⊆ packetLogIndices N := by
    intro j hj
    by_contra hnot
    have hjN : N < (j : ℕ) := lt_of_not_ge ((mem_packetLogIndices N j).not.mp hnot)
    have hz : d j = 0 := by
      dsimp only [d]
      rw [Finsupp.sub_apply, defect_packetColumnMixture_eq_zero_above L B j hjN,
        defect_packetColumnMixture_eq_zero_above L A j hjN, sub_self]
    exact Finsupp.mem_support_iff.mp hj hz
  have hbudget : repairBudget d ≤
      ∑ j ∈ packetLogIndices N, packetRepairWeight N L j * ‖δ j‖ := by
    rw [repairBudget, Finsupp.sum_of_support_subset d hsupp _ (by intros; simp)]
    apply Finset.sum_le_sum
    intro j _
    have hfactor : 0 ≤ 2 * packetMass N (L + 1) / Real.sqrt (j : ℝ) := by
      have hm := packetMass_pos N (L + 1)
      positivity
    have hd : d j = -(2 * packetMass N (L + 1) / Real.sqrt (j : ℝ) * (δ j).re) := by
      simp only [d, Finsupp.sub_apply, defect_packetColumnMixture, δ, Complex.sub_re]
      ring
    rw [hd, abs_neg, abs_mul, abs_of_nonneg hfactor]
    calc
      _ = packetRepairWeight N L j * |(δ j).re| := by unfold packetRepairWeight; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (packetRepairWeight_nonneg _ _ _)
  exact hbudget

/-- The actual correction budget is bounded by the source covariance gap. -/
theorem packetRepairBudget_sq_le_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    repairBudget (defect (packetColumnMixture L B) - defect (packetColumnMixture L A)) ^ 2 ≤
      (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) * packetRepairSensitivity N L := by
  classical
  let d := defect (packetColumnMixture L B) - defect (packetColumnMixture L A)
  let δ (j : LogIndex) := divisibilityTrace (A * Aᴴ) j - divisibilityTrace (B * Bᴴ) j
  have hb0 : 0 ≤ repairBudget d := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (atomCost_nonneg j)
  have hbudget := packetRepairBudget_le_weighted_trace L A B
  have hw (j : LogIndex) : |packetRepairWeight N L j| = packetRepairWeight N L j :=
    abs_of_nonneg (packetRepairWeight_nonneg N L j)
  calc
    _ ≤ (∑ j ∈ packetLogIndices N, packetRepairWeight N L j * ‖δ j‖) ^ 2 :=
      pow_le_pow_left₀ hb0 hbudget 2
    _ ≤ _ := by
      simpa only [hw, packetRepairSensitivity] using
        divisibilityTrace_weighted_abs_sub_sum_sq_le_crouzeix A B
          (packetLogIndices N) (packetRepairWeight N L)

/-- Positive exact defect transport has an energy cost controlled by the same covariance gap. -/
theorem packetTransferRepair_energy_sub_sq_le_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    (energy (packetTransferRepair L A B) - packetArchEnergy (L + 1) A) ^ 2 ≤
      (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) * packetRepairSensitivity N L := by
  have h := abs_energy_repair_le
    (defect (packetColumnMixture L B) - defect (packetColumnMixture L A))
  have hsq := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at hsq
  rw [packetTransferRepair, map_add, energy_packetColumnMixture, add_sub_cancel_left]
  exact hsq.trans (packetRepairBudget_sq_le_crouzeix L A B)

/-- Compare the repaired packet with its target, paying both analytic and arithmetic changes. -/
theorem packetTransferRepair_target_energy_sq_le_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    (energy (packetTransferRepair L A B) - packetArchEnergy (L + 1) B) ^ 2 ≤
      2 * (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) *
          (packetRepairSensitivity N L + finiteMatrixHilbertSchmidtSq (packetArchKernel N (L + 1))) := by
  have h1 := packetTransferRepair_energy_sub_sq_le_crouzeix L A B
  have h2 := packetArchEnergy_sub_sq_le_crouzeix (L + 1) A B
  have hs := sq_nonneg (energy (packetTransferRepair L A B) -
    2 * packetArchEnergy (L + 1) A + packetArchEnergy (L + 1) B)
  nlinarith

/-- The canonical positive integer-null repair has an unconditional covariance energy budget. -/
theorem nullRepair_packetColumnMixture_energy_sub_sq_le {N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) :
    (energy (nullRepair (packetColumnMixture L A)) - packetArchEnergy (L + 1) A) ^ 2 ≤
      finiteMatrixHilbertSchmidtSq (Aᴴ * A) * packetRepairSensitivity N L := by
  have hd0 : defect (packetColumnMixture L (0 : Matrix (PacketIndex N) ι ℂ)) = 0 := by
    ext j
    simp [defect_packetColumnMixture, divisibilityTrace]
  have hz : finiteMatrixHilbertSchmidtSq (0 : Matrix ι ι ℂ) = 0 := by
    simp [finiteMatrixHilbertSchmidtSq]
  have hb := packetRepairBudget_sq_le_crouzeix L A (0 : Matrix (PacketIndex N) ι ℂ)
  simp only [hd0, zero_sub, Matrix.conjTranspose_zero, Matrix.mul_zero,
    hz, add_zero, mul_zero, sub_zero] at hb
  have h := pow_le_pow_left₀ (abs_nonneg _)
    (abs_energy_nullRepair_sub_le (packetColumnMixture L A)) 2
  rw [sq_abs, energy_packetColumnMixture] at h
  exact h.trans hb

/-- Every packet family yields an actual positive, all-integer-null finite mixture at this cost. -/
theorem exists_packet_integer_null_mixture_with_energy_bound {N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      (∀ n : ℕ, 2 ≤ n → c.sum (fun f t => t * logValue f.1 n) = 0) ∧
      (energy c - packetArchEnergy (L + 1) A) ^ 2 ≤
        finiteMatrixHilbertSchmidtSq (Aᴴ * A) * packetRepairSensitivity N L := by
  exact ⟨nullRepair (packetColumnMixture L A),
    nullRepair_nonneg (packetColumnMixture_nonneg L A),
    logValue_nullRepair (packetColumnMixture L A),
    nullRepair_packetColumnMixture_energy_sub_sq_le L A⟩

end RHTower.WeilWorkPBAP
