import GaloisForLFunctions.ArithmeticDefectRigidity.TheAdmittedCofactorKernelIsUnique
import GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorDiagonalsAreHorizonEnergyRatios
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.IncompleteDilationFibresHaveBoundedPairingCost

/-!
# Contracting horizons produces actual cofactor limits

The bounded terminal-fibre error vanishes at escaping energy scales.
Positive contracted mass then gives a common limit along actual contracted
horizons. Admission gives the same law through exact complete blocks.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Successive integer cofactor operations multiply their indices. -/
theorem rowDilate_compose (p j : ℕ) (u : ℕ → ℝ) :
    rowDilate p (rowDilate j u) = rowDilate (p * j) u := by
  funext n
  simp only [rowDilate, Nat.div_div_eq_div_mul]

namespace ActualCofactorLimit

/-- Admission turns the complete-block identity into exact kernel self-similarity. -/
theorem kernel_mul_mul_of_admits {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (hpaid : Admits dampedMobiusEnergy ε)
    (p j k : ℕ+) :
    L.kernel (p * j) (p * k) = (1 / (p : ℝ)) * L.kernel j k := by
  obtain ⟨e, he, hE⟩ := exists_positive_receiverEnergy_limit_of_admits ε hpaid
  obtain ⟨K, hK⟩ := exists_cofactorGram_full_limit_of_admits ε hpaid
  have hKL (a b : ℕ+) : K a b = L.kernel a b :=
    tendsto_nhds_unique ((hK a b).comp L.strictMono.tendsto_atTop) (L.converges a b)
  let U (N : ℕ) := (p : ℕ) * (N + 2) - 2
  have hU : Tendsto U atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    dsimp only [U]
    have hmul : N + 2 ≤ (p : ℕ) * (N + 2) :=
      Nat.le_mul_of_pos_left _ p.property
    omega
  have hendpoint (N : ℕ) : U N + 1 = (p : ℕ) * ((N + 1) + 1) - 1 := by
    dsimp only [U]
    have hmul : N + 2 ≤ (p : ℕ) * (N + 2) :=
      Nat.le_mul_of_pos_left _ p.property
    rw [show N + 1 + 1 = N + 2 by omega]
    omega
  have hformula (N : ℕ) : cofactorGram ε (U N) (p * j) (p * k) =
      (1 / (p : ℝ)) * cofactorGram ε N j k *
        (dampedMobiusEnergy ε (N + 1) / dampedMobiusEnergy ε (U N + 1)) := by
    unfold cofactorGram
    rw [hendpoint]
    simp only [PNat.mul_coe]
    rw [← rowDilate_compose, ← rowDilate_compose]
    have hblock := pronicPairing_rowDilate_complete_blocks (p := (p : ℕ)) p.property (N + 1)
      (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε))
      (rowDilate k (pmPowerDampedCenteredDivisorPrefix ε)) (by
        simp only [rowDilate, Nat.zero_div,
          ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero])
    calc
      _ = ((1 / (p : ℝ)) * pronicPairing (N + 1)
          (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε))
          (rowDilate k (pmPowerDampedCenteredDivisorPrefix ε))) /
            dampedMobiusEnergy ε ((p : ℕ) * (N + 1 + 1) - 1) :=
        congrArg (fun x : ℝ => x /
          dampedMobiusEnergy ε ((p : ℕ) * (N + 1 + 1) - 1)) hblock
      _ = _ := by
        have hEne := (receiverEnergy_succ_pos ε N).ne'
        field_simp
  have hratio := (hE.comp (tendsto_add_atTop_nat 1)).div
    (hE.comp ((tendsto_add_atTop_nat 1).comp hU)) he.ne'
  rw [div_self he.ne'] at hratio
  have hlim := ((hK j k).const_mul (1 / (p : ℝ))).mul hratio
  simp only [mul_one] at hlim
  have hlim' : Tendsto (fun N => cofactorGram ε (U N) (p * j) (p * k)) atTop
      (𝓝 ((1 / (p : ℝ)) * K j k)) := hlim.congr fun N => (hformula N).symm
  rw [← hKL, ← hKL]
  exact tendsto_nhds_unique ((hK (p * j) (p * k)).comp hU) hlim'

/-- On escape, the contracted unnormalized pairing has the predicted common limit. -/
theorem admits_or_contracted_pairing_tendsto {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) :
    Admits dampedMobiusEnergy ε ∨ ∀ p j k : ℕ+,
      Tendsto (fun m =>
        pronicPairing ((L.subsequence m + 1) / p)
          (rowDilate j (pmPowerDampedCenteredDivisorPrefix ε))
          (rowDilate k (pmPowerDampedCenteredDivisorPrefix ε)) /
            dampedMobiusEnergy ε (L.subsequence m + 1)) atTop
        (𝓝 ((p : ℝ) * L.kernel (p * j) (p * k))) := by
  rcases admits_or_tendsto_atTop (ε : ℝ) with hpaid | hescape
  · exact Or.inl hpaid
  · right
    intro p j k
    let A := pmPowerDampedCenteredDivisorPrefix (ε : ℝ)
    let T (m : ℕ) := L.subsequence m + 1
    let P (m : ℕ) := pronicPairing (T m / p) (rowDilate j A) (rowDilate k A)
    have hET := hescape.comp ((tendsto_add_atTop_nat 1).comp L.strictMono.tendsto_atTop)
    have hrow (a : ℕ+) (n : ℕ) : |rowDilate a A n| ≤ (n : ℝ) := by
      exact (abs_receiver_le_cell ε (n / a)).trans (by exact_mod_cast Nat.div_le_self n (a : ℕ))
    have herror : Tendsto (fun m =>
        cofactorGram ε (L.subsequence m) (p * j) (p * k) -
          (1 / (p : ℝ)) * (P m / dampedMobiusEnergy ε (T m))) atTop (𝓝 0) := by
      have hzero : Tendsto (fun m => (1 / (p : ℝ)) /
          dampedMobiusEnergy ε (T m)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hET
      apply squeeze_zero_norm (fun m => ?_) hzero
      rw [Real.norm_eq_abs]
      have h := abs_pronicPairing_rowDilate_horizon_error p.property (T m)
        (rowDilate j A) (rowDilate k A) (by
          simp only [rowDilate, Nat.zero_div, A,
            ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero])
        (hrow j) (hrow k)
      rw [rowDilate_compose, rowDilate_compose] at h
      have hEpos := receiverEnergy_succ_pos ε (L.subsequence m)
      change |pronicPairing (T m) (rowDilate (p * j) A) (rowDilate (p * k) A) /
        dampedMobiusEnergy ε (T m) - (1 / (p : ℝ)) * (P m / dampedMobiusEnergy ε (T m))| ≤ _
      rw [← mul_div_assoc, ← sub_div, abs_div, abs_of_pos hEpos]
      exact div_le_div_of_nonneg_right h hEpos.le
    have hlim := (L.converges (p * j) (p * k)).sub herror
    simp only [sub_zero, sub_sub_cancel] at hlim
    have hmul := hlim.const_mul (p : ℝ)
    apply hmul.congr
    intro m
    have hpne : (p : ℝ) ≠ 0 := by positivity
    dsimp only [P, T, A]
    field_simp

/-- Every nonzero cofactor produces another actual common limit by contracting horizons. -/
theorem exists_actual_contracted_kernel {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (p : ℕ+) (hp : 0 < L.kernel p p) :
    ∃ M : ActualCofactorLimit ε, ∀ j k,
      M.kernel j k = L.kernel (p * j) (p * k) / L.kernel p p := by
  rcases admits_or_contracted_pairing_tendsto L with hpaid | hpair
  · refine ⟨L, fun j k => ?_⟩
    rw [kernel_mul_mul_of_admits L hpaid, kernel_diag_of_admits L hpaid]
    have hpne : (1 : ℝ) / p ≠ 0 := by positivity
    exact (mul_div_cancel_left₀ _ hpne).symm
  · let N (m : ℕ) := (L.subsequence m + 1) / (p : ℕ)
    have hN : Tendsto N atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [L.strictMono.tendsto_atTop.eventually_ge_atTop (b * (p : ℕ))] with m hm
      exact (Nat.le_div_iff_mul_le p.property).mpr (hm.trans (Nat.le_succ _))
    have hNm : Tendsto (fun m => N m - 1) atTop atTop := by
      refine tendsto_atTop.2 fun b => ?_
      filter_upwards [hN.eventually_ge_atTop (b + 1)] with m hm
      omega
    obtain ⟨φ, hφ, hNmφ⟩ := Filter.strictMono_subseq_of_tendsto_atTop hNm
    have hlim (j k : ℕ+) : Tendsto (fun m => cofactorGram ε (N m - 1) j k) atTop
        (𝓝 (L.kernel (p * j) (p * k) / L.kernel p p)) := by
      have hquot := (hpair p j k).div (contracted_energy_ratio_tendsto L p)
        (mul_pos (by positivity : (0 : ℝ) < p) hp).ne'
      have hcancel : (p : ℝ) * L.kernel (p * j) (p * k) /
          ((p : ℝ) * L.kernel p p) = L.kernel (p * j) (p * k) / L.kernel p p := by
        exact mul_div_mul_left _ _ (by positivity)
      rw [hcancel] at hquot
      apply hquot.congr'
      filter_upwards [hN.eventually_ge_atTop 1] with m hm
      rw [cofactorGram, Nat.sub_add_cancel hm]
      have hEne := (receiverEnergy_succ_pos ε (L.subsequence m)).ne'
      exact div_div_div_cancel_right₀ hEne _ _
    exact ⟨{ subsequence := fun m => N (φ m) - 1
             strictMono := hNmφ
             kernel := fun j k => L.kernel (p * j) (p * k) / L.kernel p p
             converges := fun j k => (hlim j k).comp hφ.tendsto_atTop }, fun _ _ => rfl⟩

end ActualCofactorLimit
end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.kernel_mul_mul_of_admits
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.exists_actual_contracted_kernel
end
