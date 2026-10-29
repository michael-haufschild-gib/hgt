import GaloisForLFunctions.TransMetzlerWeilPositivity.TransMetzlerDecomposition
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching

/-!
# A positive prefix gives an exact Schur reduction

The principal block on `1 ≤ n ≤ M` of the complete length-`N` matrix at
overlap `c` is the length-`M` matrix at overlap `cM/N`. Uniform positivity
through touching pays this block whenever `M` is large and `cM ≤ N`.
The resulting Schur complement retains every mixed prime, Gamma, and polar
entry. Its positivity is exactly the remaining full-matrix obligation.
-/

noncomputable section

set_option autoImplicit false

open Finset Filter Topology MeasureTheory Matrix

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis RenormalizedArithmeticPotentialTheory
  CriticalArithmeticCorrelationTheory SelectiveMultiscaleArithmeticPositivity

/-- Inclusion of the initial integer horizon. -/
def horizonPrefixMap {M N : ℕ} (hMN : M ≤ N) (n : PrimeHorizonIndex M) :
    PrimeHorizonIndex N :=
  ⟨n, mem_Icc.mpr ⟨(mem_Icc.mp n.property).1, (mem_Icc.mp n.property).2.trans hMN⟩⟩

/-- The remaining integer coordinates after removing a prefix. -/
abbrev HorizonTail (M N : ℕ) := {n : PrimeHorizonIndex N // M < n.val}

private def horizonSplitMap {M N : ℕ} (hMN : M ≤ N) :
    PrimeHorizonIndex M ⊕ HorizonTail M N → PrimeHorizonIndex N
  | .inl n => horizonPrefixMap hMN n
  | .inr n => n.val

private theorem horizonSplitMap_bijective {M N : ℕ} (hMN : M ≤ N) :
    Function.Bijective (horizonSplitMap hMN) := by
  constructor
  · intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have hval := congrArg Subtype.val hij
        exact congrArg Sum.inl (Subtype.ext hval)
      | inr j =>
        have hval := congrArg Subtype.val hij
        have hi := (mem_Icc.mp i.property).2
        have hj := j.property
        change i.val = j.val.val at hval
        omega
    | inr i =>
      cases j with
      | inl j =>
        have hval := congrArg Subtype.val hij
        have hi := i.property
        have hj := (mem_Icc.mp j.property).2
        change i.val.val = j.val at hval
        omega
      | inr j =>
        exact congrArg Sum.inr (Subtype.ext hij)
  · intro n
    by_cases hn : n.val ≤ M
    · exact ⟨.inl ⟨n.val, mem_Icc.mpr ⟨(mem_Icc.mp n.property).1, hn⟩⟩, rfl⟩
    · exact ⟨.inr ⟨n, not_le.mp hn⟩, rfl⟩

/-- A genuine coordinate decomposition, independent of the signs of matrix entries. -/
def horizonPrefixSplit {M N : ℕ} (hMN : M ≤ N) :
    PrimeHorizonIndex M ⊕ HorizonTail M N ≃ PrimeHorizonIndex N :=
  Equiv.ofBijective (horizonSplitMap hMN) (horizonSplitMap_bijective hMN)

/-- Actual complete Weil matrix restricted to the prefix. -/
def plateauPrefixBlock {M N : ℕ} (hMN : M ≤ N) (c : ℝ) :
    Matrix (PrimeHorizonIndex M) (PrimeHorizonIndex M) ℝ :=
  (completeWeilMatrix transMetzlerProfile c N).submatrix
    (horizonPrefixMap hMN) (horizonPrefixMap hMN)

/-- Actual complete Weil matrix restricted to the remaining coordinates. -/
def plateauTailBlock (M N : ℕ) (c : ℝ) : Matrix (HorizonTail M N) (HorizonTail M N) ℝ :=
  (completeWeilMatrix transMetzlerProfile c N).submatrix Subtype.val Subtype.val

/-- All mixed entries between prefix and tail, with their original signs. -/
def plateauMixedBlock {M N : ℕ} (hMN : M ≤ N) (c : ℝ) :
    Matrix (PrimeHorizonIndex M) (HorizonTail M N) ℝ :=
  (completeWeilMatrix transMetzlerProfile c N).submatrix (horizonPrefixMap hMN) Subtype.val

/-- Principal compression changes overlap, while preserving the physical atom width. -/
theorem plateauPrefixBlock_eq {M N : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N)
    {c : ℝ} (hc : 0 < c) :
    plateauPrefixBlock hMN c = completeWeilMatrix transMetzlerProfile (c * M / N) M := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hM.trans hMN
  have hw : 0 < c / N := div_pos hc hN0
  have hmass : (∫ u, atomDilate transMetzlerProfile (c / N) u ^ 2) ≠ 0 := by
    rw [integral_atomDilate_sq hw]
    exact (mul_pos hw integral_transMetzlerProfile_sq_pos).ne'
  have hwidth : (c * M / N) / M = c / N := by field_simp
  ext n j
  change normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile (c / N)) N
      (horizonPrefixMap hMN n) (horizonPrefixMap hMN j) =
    normalizedFullWeilHorizonMatrix (atomDilate transMetzlerProfile ((c * M / N) / M)) M n j
  rw [hwidth, normalizedFullWeilHorizonMatrix_apply_unconditional hmass,
    normalizedFullWeilHorizonMatrix_apply_unconditional hmass]
  rfl

/-- The explicit plateau has one positive horizon simultaneously for all overlaps through one. -/
theorem eventually_plateau_posDef_uniformly_through_touching :
    ∀ᶠ M : ℕ in atTop, ∀ d : ℝ, 0 < d → d ≤ 1 →
      (completeWeilMatrix transMetzlerProfile d M).PosDef := by
  have henergy := completeWeilAdjunctionEnergy_transMetzlerProfile_gt_one_twentieth
    (c := 1) (m := 1) zero_lt_one (by norm_num) (by norm_num)
  have heq : completeWeilAdjunctionEnergy transMetzlerProfile 1 1 =
      bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) +
        completeWeilPoleShift transMetzlerProfile 1 - Real.log (2 * Real.pi) := by
    rw [completeWeilAdjunctionEnergy, completeWeilSelfFinitePart,
      ramanujanAdjunctionEnergy_one, if_pos rfl, mul_one, one_div, Real.log_inv]
    ring
  rw [heq] at henergy
  have hfloor : (1 : ℝ) / 25 <
      bumpRobin transMetzlerProfile 1 / (∫ u, transMetzlerProfile u ^ 2) +
        completeWeilPoleShift transMetzlerProfile 1 - Real.log (2 * Real.pi) :=
    (by norm_num : (1 : ℝ) / 25 < 1 / 20).trans henergy
  filter_upwards [eventually_completeWeil_eigenvalues_ge_uniformly_at_touching
    contDiff_transMetzlerProfile (fun u hu => transMetzlerProfile_eq_zero hu)
    integral_transMetzlerProfile_sq_pos hfloor] with M hM
  intro d hd hd1
  apply (completeWeilMatrix_isHermitian transMetzlerProfile d M).posDef_iff_eigenvalues_pos.mpr
  intro i
  exact (by norm_num : (0 : ℝ) < 1 / 25).trans_le (hM d hd hd1 i)

/-- A prefix is paid by existing positivity whenever its length is at most inverse width. -/
theorem eventually_plateauPrefixBlock_posDef :
    ∀ᶠ M : ℕ in atTop, ∀ N : ℕ, ∀ hMN : M ≤ N, ∀ c : ℝ,
      0 < c → c * M ≤ N → (plateauPrefixBlock hMN c).PosDef := by
  filter_upwards [eventually_plateau_posDef_uniformly_through_touching,
    eventually_ge_atTop (1 : ℕ)] with M hpos hM
  intro N hMN c hc hcM
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hM.trans hMN
  rw [plateauPrefixBlock_eq hM hMN hc]
  exact hpos (c * M / N) (div_pos (mul_pos hc hM0) hN0) ((div_le_one hN0).mpr hcM)

theorem completeWeilMatrix_prefix_blocks {M N : ℕ} (hMN : M ≤ N) (c : ℝ) :
    (completeWeilMatrix transMetzlerProfile c N).submatrix
        (horizonPrefixSplit hMN) (horizonPrefixSplit hMN) =
      Matrix.fromBlocks (plateauPrefixBlock hMN c) (plateauMixedBlock hMN c)
        (plateauMixedBlock hMN c)ᴴ (plateauTailBlock M N c) := by
  ext i j
  cases i with
  | inl i => cases j <;> rfl
  | inr i =>
    cases j with
    | inl j =>
      exact ((completeWeilMatrix_isHermitian transMetzlerProfile c N).apply
        i.val (horizonPrefixMap hMN j)).symm
    | inr j => rfl

/-- The residual complete form after the paid prefix has been eliminated. -/
def plateauPrefixSchur {M N : ℕ} (hMN : M ≤ N) (c : ℝ) :
    Matrix (HorizonTail M N) (HorizonTail M N) ℝ :=
  plateauTailBlock M N c -
    (plateauMixedBlock hMN c)ᴴ * (plateauPrefixBlock hMN c)⁻¹ * plateauMixedBlock hMN c

/-- All full-matrix positivity beyond the paid prefix is exactly the sign of this actual Schur
complement; no positivity or invertibility premise is imported. -/
theorem eventually_completeWeil_posSemidef_iff_prefixSchur :
    ∀ᶠ M : ℕ in atTop, ∀ N : ℕ, ∀ hMN : M ≤ N, ∀ c : ℝ,
      0 < c → c * M ≤ N →
      ((completeWeilMatrix transMetzlerProfile c N).PosSemidef ↔
        (plateauPrefixSchur hMN c).PosSemidef) := by
  classical
  filter_upwards [eventually_plateauPrefixBlock_posDef] with M hM
  intro N hMN c hc hcM
  have hpaid := hM N hMN c hc hcM
  letI := hpaid.isUnit.invertible
  rw [← Matrix.posSemidef_submatrix_equiv (horizonPrefixSplit hMN),
    completeWeilMatrix_prefix_blocks hMN c]
  exact Matrix.PosDef.fromBlocks₁₁ (plateauMixedBlock hMN c) (plateauTailBlock M N c) hpaid

/-- Eliminating the paid prefix subtracts a positive semidefinite mixed-entry cost. -/
theorem eventually_plateauPrefixSchur_cost_posSemidef :
    ∀ᶠ M : ℕ in atTop, ∀ N : ℕ, ∀ hMN : M ≤ N, ∀ c : ℝ,
      0 < c → c * M ≤ N →
      ((plateauMixedBlock hMN c)ᴴ * (plateauPrefixBlock hMN c)⁻¹ *
        plateauMixedBlock hMN c).PosSemidef := by
  classical
  filter_upwards [eventually_plateauPrefixBlock_posDef] with M hM
  intro N hMN c hc hcM
  exact (hM N hMN c hc hcM).inv.posSemidef.conjTranspose_mul_mul_same _

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.plateauPrefixBlock_eq
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_plateauPrefixBlock_posDef
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_completeWeil_posSemidef_iff_prefixSchur
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_plateauPrefixSchur_cost_posSemidef
