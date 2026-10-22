import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileOddWindowMismatchDivergence
import GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedQuantileLorentzEffectiveResistance

namespace RHTower

/-- Every mismatched actual prime-power atom in a window is one of the
base-prime completed-source mismatches charged by effective resistance. -/
theorem ccmOddLogWindowMismatchMass_le_baseExceptionalMass
    {A B : ℕ} (hA : 3 ≤ A) :
    (∑ n ∈ ccmOddLogWindowMismatchSet A B,
      criticalMellinAtomWeight n) ≤
      ccmActualHeadMatchedQuantileBaseDisplacementExceptionalMass B := by
  classical
  let W := ccmOddLogWindowMismatchSet A B
  let E := ccmActualHeadMatchedQuantileBaseDisplacementExceptionalVertices B
  let f : ℕ → ℕ := fun n => n - 2
  have hinj : ∀ a ∈ W, ∀ b ∈ W, f a = f b → a = b := by
    intro a ha b hb hab
    have haI : a ∈ Finset.Icc A B :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1
    have hbI : b ∈ Finset.Icc A B :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).1
    have ha3 : 3 ≤ a := hA.trans (Finset.mem_Icc.mp haI).1
    have hb3 : 3 ≤ b := hA.trans (Finset.mem_Icc.mp hbI).1
    dsimp only [f] at hab
    omega
  have hsubset : W.image f ⊆ E := by
    intro m hm
    obtain ⟨n, hnW, rfl⟩ := Finset.mem_image.mp hm
    have hnS : n ∈ (Finset.Icc A B).filter IsPrimePow :=
      (Finset.mem_filter.mp hnW).1
    have hnI : n ∈ Finset.Icc A B := (Finset.mem_filter.mp hnS).1
    have hn3 : 3 ≤ n := hA.trans (Finset.mem_Icc.mp hnI).1
    have hnB : n ≤ B := (Finset.mem_Icc.mp hnI).2
    have hnPow : IsPrimePow n := (Finset.mem_filter.mp hnS).2
    have hnDiff : ccmActualHeadMatchedQuantilePolarDisplacement n ≠
        ccmActualHeadMatchedQuantilePolarDisplacement 2 :=
      (Finset.mem_filter.mp hnW).2
    have hshift : f n + 2 = n := by dsimp [f]; omega
    change f n ∈ E
    dsimp [E, ccmActualHeadMatchedQuantileBaseDisplacementExceptionalVertices]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr ?_⟩, ?_⟩
    · dsimp [f]; omega
    · dsimp [f]; omega
    · rw [hshift]
      exact ⟨hnPow, hnDiff.symm⟩
  have hsum :
      (∑ m ∈ W.image f, criticalMellinAtomWeight (m + 2)) =
      ∑ n ∈ W, criticalMellinAtomWeight n := by
    rw [Finset.sum_image hinj]
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    dsimp [f]
    have hnI : n ∈ Finset.Icc A B :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).1
    have hn3 : 3 ≤ n := hA.trans (Finset.mem_Icc.mp hnI).1
    omega
  have hmass :
      (∑ m ∈ W.image f, criticalMellinAtomWeight (m + 2)) ≤
      ∑ m ∈ E, criticalMellinAtomWeight (m + 2) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro m hm _
    have hpow : IsPrimePow (m + 2) :=
      (Finset.mem_filter.mp hm).2.1
    exact (criticalMellinAtomWeight_pos hpow).le
  rw [hsum] at hmass
  exact hmass

/-- Completed-source base mismatch mass diverges on actual canonical
prime-power heads. -/
theorem tendsto_ccmOddLogWindowBaseExceptionalMass_atTop :
    Filter.Tendsto
      (fun t : ℕ =>
        ccmActualHeadMatchedQuantileBaseDisplacementExceptionalMass
          (ccmOddLogWindowUpper t))
      Filter.atTop Filter.atTop := by
  apply Filter.tendsto_atTop_mono
    (fun t : ℕ => ccmOddLogWindowMismatchMass_le_baseExceptionalMass
      (A := ccmOddLogWindowLower t) (B := ccmOddLogWindowUpper t) (by
        have ht1 : (1 : ℝ) ≤ ((2 * t + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ 2 * t + 1 by omega)
        have hx2 : (2 : ℝ) ≤ Real.exp ((2 * t + 1 : ℕ) : ℝ) := by
          calc
            (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
            _ ≤ _ := Real.exp_le_exp.mpr ht1
        have hfloor : 2 ≤ ⌊Real.exp ((2 * t + 1 : ℕ) : ℝ)⌋₊ :=
          Nat.le_floor hx2
        change 3 ≤ ⌊Real.exp ((2 * t + 1 : ℕ) : ℝ)⌋₊ + 1
        omega))
  exact tendsto_ccmOddLogWindowMismatchMass_atTop

/-- Effective Lorentz resistance diverges cofinally on literal actual
heads. Null-edge deletion cannot make the direct positive Cauchy wall
uniform; this theorem does not bound the signed CCM-FU source. -/
theorem tendsto_ccmOddLogWindowEffectiveGraphResistance_atTop :
    Filter.Tendsto
      (fun t : ℕ =>
        ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance
          (ccmOddLogWindowUpper t))
      Filter.atTop Filter.atTop := by
  have hcoeff : 0 < criticalMellinAtomWeight 2 / 2 :=
    div_pos (criticalMellinAtomWeight_pos Nat.prime_two.isPrimePow) (by norm_num)
  have hscaled :=
    tendsto_ccmOddLogWindowBaseExceptionalMass_atTop.const_mul_atTop hcoeff
  exact Filter.tendsto_atTop_mono
    (fun t : ℕ =>
      ccmActualHeadMatchedQuantileParabolicLorentzEffectiveGraphResistance_ge_baseExceptionalMass
        (ccmOddLogWindowUpper t)) hscaled

end RHTower

#print axioms RHTower.tendsto_ccmOddLogWindowMismatchMass_atTop
#print axioms RHTower.ccmOddLogWindowMismatchMass_le_baseExceptionalMass
#print axioms RHTower.tendsto_ccmOddLogWindowBaseExceptionalMass_atTop
#print axioms RHTower.tendsto_ccmOddLogWindowEffectiveGraphResistance_atTop
