import GaloisForLFunctions.SignedArithmeticHodgeTheory.HighGeneratorTailsAreSmallAcrossAllLevels
import GaloisForLFunctions.SignedArithmeticHodgeTheory.DyadicHaarCoordinatesReadTheOriginalSource
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SmoothFiniteCellArithmeticForm

/-!
# Physical approximation by finitely many complete generator orbits

The cutoff retains the root generator and every detail label below a fixed
threshold, at every translation level. Its actual physical L² error is bounded
by the original source's Gamma energy divided by the logarithmic threshold.
For finite complete-cell sources this is an estimate on the entire source,
not merely on an auxiliary coefficient model.
-/

noncomputable section
open MeasureTheory Set RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "CoordH" => lp (fun _ : ℕ × Option ℕ+ => ℂ) 2

/-- Root and low detail generators, without restricting their translation levels. -/
def retainedLogCellGenerator (A : ℕ) : Option ℕ+ → Prop
  | none => True
  | some a => (a : ℕ) < A

theorem finite_retainedLogCellGenerators (A : ℕ) :
    ({o | retainedLogCellGenerator A o} : Set (Option ℕ+)).Finite := by
  have hinj : Function.Injective (fun a : ℕ+ => (a : ℕ)) := fun _ _ h => PNat.eq h
  have hlabels : ({a : ℕ+ | (a : ℕ) < A} : Set ℕ+).Finite := by
    simpa only [preimage, Finset.mem_coe, Finset.mem_range] using
      (Finset.finite_toSet (Finset.range A)).preimage hinj.injOn
  have he : ({o | retainedLogCellGenerator A o} : Set (Option ℕ+)) =
      {none} ∪ Option.some '' {a : ℕ+ | (a : ℕ) < A} := by
    ext o
    cases o <;> simp [retainedLogCellGenerator]
  rw [he]
  exact (finite_singleton none).union (hlabels.image Option.some)

/-- The original-cell orthogonal cutoff retaining entire low-generator orbits. -/
def logCellGeneratorHead (A : ℕ) : CellH →L[ℂ] CellH :=
  (logCellDyadicCoordinates.symm : CoordH →L[ℂ] CellH) ∘L
    lpCoordinateProjection {i | retainedLogCellGenerator A i.2} ∘L
      (logCellDyadicCoordinates : CellH →L[ℂ] CoordH)

theorem logCellDyadicCoordinates_generatorHead (A : ℕ) (x : CellH) :
    logCellDyadicCoordinates (logCellGeneratorHead A x) =
      lpCoordinateProjection {i | retainedLogCellGenerator A i.2} (logCellDyadicCoordinates x) :=
  logCellDyadicCoordinates.apply_symm_apply _

private theorem coordinates_orbit (i : ℕ × Option ℕ+) :
    logCellDyadicCoordinates (logCellDyadicOrbit i) = (lp.single 2 i (1 : ℂ) : CoordH) := by
  classical
  apply lp.ext
  funext k
  rw [logCellDyadicCoordinates_apply, orthonormal_iff_ite.mp orthonormal_logCellDyadicOrbit]
  by_cases hk : k = i
  · subst k; simp [lp.single_apply]
  · have hk' : i ≠ k := fun h => hk h.symm
    simp [lp.single_apply, hk, hk']

open Classical in
/-- Every retained generator survives the cutoff at every level. -/
theorem logCellGeneratorHead_orbit (A : ℕ) (i : ℕ × Option ℕ+) :
    logCellGeneratorHead A (logCellDyadicOrbit i) =
      if retainedLogCellGenerator A i.2 then logCellDyadicOrbit i else 0 := by
  classical
  apply logCellDyadicCoordinates.injective
  rw [logCellDyadicCoordinates_generatorHead, coordinates_orbit]
  split_ifs with hi
  · rw [coordinates_orbit]
    apply lp.ext
    funext k
    by_cases hk : k = i
    · subst k
      simp only [lpCoordinateProjection_apply, Set.indicator_apply, Set.mem_setOf_eq, if_pos hi]
    · have hk' : i ≠ k := fun h => hk h.symm
      simp [lpCoordinateProjection_apply, indicator_apply, lp.single_apply, hk, hk']
  · rw [map_zero]
    apply lp.ext
    funext k
    by_cases hk : k = i
    · subst k
      simp only [lpCoordinateProjection_apply, Set.indicator_apply, Set.mem_setOf_eq,
        if_neg hi, lp.coeFn_zero, Pi.zero_apply]
    · have hk' : i ≠ k := fun h => hk h.symm
      simp [lpCoordinateProjection_apply, indicator_apply, lp.single_apply, hk, hk']

theorem logCellGeneratorHead_root (A j : ℕ) :
    logCellGeneratorHead A (logCellDyadicOrbit (j, none)) = logCellDyadicOrbit (j, none) := by
  simpa only [retainedLogCellGenerator, if_true] using logCellGeneratorHead_orbit A (j, none)

theorem logCellGeneratorHead_low_detail {A : ℕ} (j : ℕ) (a : ℕ+) (ha : (a : ℕ) < A) :
    logCellGeneratorHead A (logCellDyadicOrbit (j, some a)) =
      logCellDyadicOrbit (j, some a) := by
  simpa only [retainedLogCellGenerator, if_pos ha] using logCellGeneratorHead_orbit A (j, some a)

private theorem physical_coordinate_tail_norm (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) (A : ℕ) :
    ‖physicalLogCellCoordinates f hv hc -
      lpCoordinateProjection {i | retainedLogCellGenerator A i.2}
        (physicalLogCellCoordinates f hv hc)‖ ^ 2 =
      ∑' i : ℕ × ℕ+, if A ≤ (i.2 : ℕ) then logCellHaarReadout 0 i f ^ 2 else 0 := by
  classical
  let z := physicalLogCellCoordinates f hv hc -
    lpCoordinateProjection {i | retainedLogCellGenerator A i.2} (physicalLogCellCoordinates f hv hc)
  have hzNone (j : ℕ) : z (j, none) = 0 := by
    simp only [z, lp.coeFn_sub, Pi.sub_apply, lpCoordinateProjection_apply,
      indicator_apply, mem_setOf_eq, retainedLogCellGenerator, if_true, sub_self]
  have hzSome (j : ℕ) (a : ℕ+) :
      ‖z (j, some a)‖ ^ 2 = if A ≤ (a : ℕ) then logCellHaarReadout 0 (j, a) f ^ 2 else 0 := by
    simp only [z, lp.coeFn_sub, Pi.sub_apply, lpCoordinateProjection_apply,
      indicator_apply, mem_setOf_eq, retainedLogCellGenerator]
    change ‖physicalLogCellCoordinates f hv hc (j, some a) -
      (if (a : ℕ) < A then physicalLogCellCoordinates f hv hc (j, some a) else 0)‖ ^ 2 = _
    rw [physicalLogCellCoordinates_detail]
    by_cases ha : (a : ℕ) < A
    · simp only [if_pos ha, if_neg (by omega : ¬A ≤ (a : ℕ)), sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    · simp only [if_neg ha, if_pos (by omega : A ≤ (a : ℕ)), sub_zero,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
  let ι : ℕ × ℕ+ → ℕ × Option ℕ+ := fun i => (i.1, some i.2)
  have hι : Function.Injective ι := by
    rintro ⟨j, a⟩ ⟨k, b⟩ h
    have hj := congrArg Prod.fst h
    have ha := Option.some.inj (congrArg Prod.snd h)
    exact Prod.ext hj ha
  have hsupp : Function.support (fun i => ‖z i‖ ^ 2) ⊆ range ι := by
    rintro ⟨j, o⟩ hi
    cases o with
    | none =>
      apply False.elim
      apply hi
      change ‖z (j, none)‖ ^ 2 = 0
      rw [hzNone, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    | some a => exact ⟨(j, a), rfl⟩
  change ‖z‖ ^ 2 = _
  rw [HilbertSchmidt.lp_norm_sq_eq, ← hι.tsum_eq hsupp]
  exact tsum_congr (fun i => hzSome i.1 i.2)

/-- Physical tail estimate on the complete-cell component of any compact BV source. -/
theorem norm_physical_cell_component_sub_head_sq_le (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) {A : ℕ} (hA : 1 ≤ A) :
    let x := wholeLineLogCellEmbedding.adjoint (realSourceLp f hv hc)
    ‖wholeLineLogCellEmbedding x - wholeLineLogCellEmbedding (logCellGeneratorHead A x)‖ ^ 2 ≤
      32 * levyEnergy f / (1 + Real.log (A : ℝ)) := by
  dsimp only
  rw [← map_sub, norm_wholeLineLogCellEmbedding]
  rw [← logCellDyadicCoordinates.norm_map
    (wholeLineLogCellEmbedding.adjoint (realSourceLp f hv hc) -
      logCellGeneratorHead A (wholeLineLogCellEmbedding.adjoint (realSourceLp f hv hc))),
    map_sub, logCellDyadicCoordinates_generatorHead]
  change ‖physicalLogCellCoordinates f hv hc -
    lpCoordinateProjection {i | retainedLogCellGenerator A i.2} (physicalLogCellCoordinates f hv hc)‖ ^ 2 ≤ _
  rw [physical_coordinate_tail_norm]
  exact logCellHaar_high_detail_tail_le 0 hA hv hc

private theorem logCellEmbedding_adjoint_self (x : CellH) :
    logCellEmbedding (logCellEmbedding.adjoint (logCellEmbedding x)) = logCellEmbedding x := by
  have h := congrArg (fun T => T x) adjoint_logCellEmbedding_comp
  change logCellEmbedding.adjoint (logCellEmbedding x) = x at h
  rw [h]

private theorem cellSection_fixed_by_cell_projection (c : ℕ → ℝ) (X : ℕ) :
    logCellEmbedding (logCellEmbedding.adjoint (cellSection c 1 X)) = cellSection c 1 X := by
  unfold cellSection
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_smul, map_smul]
  congr 1
  have hapos := (Finset.mem_Icc.mp ha).1
  have he : logCellEmbedding ((Real.sqrt (logCell a) : ℂ) •
      (lp.single 2 (⟨a, hapos⟩ : ℕ+) (1 : ℂ) : CellH)) = cellAtom a :=
    logCellEmbedding_weighted_single ⟨a, hapos⟩
  rw [← he]
  exact logCellEmbedding_adjoint_self _

theorem realSourceLp_wholeCellProfile (c : ℕ → ℝ) (X : ℕ) :
    realSourceLp (wholeCellProfile c X) (wholeCellProfile_regular c X).1
        (wholeCellProfile_regular c X).2 =
      wholeLineLogCellEmbedding (logCellEmbedding.adjoint (cellSection c 1 X)) := by
  change _ = halfLineExtend (logCellEmbedding (logCellEmbedding.adjoint (cellSection c 1 X)))
  rw [cellSection_fixed_by_cell_projection]
  apply Lp.ext
  exact (realSourceLp_coeFn _ _ _).trans (halfLineExtend_wholeCellProfile c X).symm

/-- The entire actual finite cell source is approximated by finitely many full generator orbits. -/
theorem norm_wholeCellSource_sub_generatorHead_sq_le (c : ℕ → ℝ) (X : ℕ)
    {A : ℕ} (hA : 1 ≤ A) :
    ‖realSourceLp (wholeCellProfile c X) (wholeCellProfile_regular c X).1
        (wholeCellProfile_regular c X).2 -
      wholeLineLogCellEmbedding (logCellGeneratorHead A
        (logCellEmbedding.adjoint (cellSection c 1 X)))‖ ^ 2 ≤
      32 * levyEnergy (wholeCellProfile c X) / (1 + Real.log (A : ℝ)) := by
  have h := norm_physical_cell_component_sub_head_sq_le (wholeCellProfile c X)
    (wholeCellProfile_regular c X).1 (wholeCellProfile_regular c X).2 hA
  dsimp only at h
  rw [realSourceLp_wholeCellProfile, wholeLineLogCellEmbedding_adjoint_self] at h
  rw [realSourceLp_wholeCellProfile]
  exact h

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.logCellGeneratorHead_orbit
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.norm_physical_cell_component_sub_head_sq_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.norm_wholeCellSource_sub_generatorHead_sq_le
