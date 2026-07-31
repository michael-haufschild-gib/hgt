import GaloisForLFunctions.HTGeometry.ProjectiveHorizonAffineChartField

/-!
# The chart unipotent group translates the affine coordinates

The observer group of a single covector `e_i^*` is the unipotent group `U_(ker e_i^*)` of the
affine chart whose infinity hyperplane is `ker e_i^*`.  On that chart it acts by translating the
zeroth-order affine coordinates and fixing every jet of positive order.

The computation rests on two facts about a unimodular matrix whose columns outside `i` are
standard: its `(i,i)` entry is one, which follows by induction along the transvection generators,
and the resulting fractional-linear change of the chart has denominator one.  Consequently the
positive-order chart tail is contained in the horizon field of `ker e_i^*`.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-! ## The diagonal entry of a chart unipotent matrix -/

theorem coe_apply_of_mem_chartSubsetStabilizer_singleton {i : n}
    {g : SpecialLinearGroup n K} (hg : g ∈ chartSubsetStabilizer (K := K) {i})
    (a : n) {m : n} (hm : m ≠ i) :
    (g : Matrix n n K) a m = (1 : Matrix n n K) a m :=
  hg m (by simpa using hm) a

/-- A unimodular matrix whose columns away from `i` are standard has `(i,i)` entry one.  The
transvection generators have this property and it is preserved by products and inverses. -/
theorem coe_apply_self_eq_one_of_mem_chartSubsetStabilizer {i : n}
    {g : SpecialLinearGroup n K} (hg : g ∈ chartSubsetStabilizer (K := K) {i}) :
    (g : Matrix n n K) i i = 1 := by
  rw [← closure_chartSubsetTransvectionSet_eq_chartSubsetStabilizer] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨j, hj, y, hy, c, rfl⟩ := hx
      have hji : j = i := hj
      have hyi : y ≠ i := hji ▸ hy
      show Matrix.transvection y j c i i = 1
      rw [Matrix.transvection]
      simp [hyi]
  | one => rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]
  | mul x y hx hy ihx ihy =>
      have hxs : x ∈ chartSubsetStabilizer (K := K) {i} := by
        rwa [closure_chartSubsetTransvectionSet_eq_chartSubsetStabilizer] at hx
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single i]
      · rw [ihx, ihy, one_mul]
      · intro m _ hm
        rw [coe_apply_of_mem_chartSubsetStabilizer_singleton hxs i hm,
          Matrix.one_apply_ne (Ne.symm hm), zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ i) hcon
  | inv x hx ihx =>
      have hxinv : x⁻¹ ∈ chartSubsetStabilizer (K := K) {i} := by
        rw [← closure_chartSubsetTransvectionSet_eq_chartSubsetStabilizer]
        exact inv_mem hx
      have hprod : ((x⁻¹ * x : SpecialLinearGroup n K) : Matrix n n K) i i = 1 := by
        rw [inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq]
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Finset.sum_eq_single i] at hprod
      · rwa [ihx, mul_one] at hprod
      · intro m _ hm
        rw [coe_apply_of_mem_chartSubsetStabilizer_singleton hxinv i hm,
          Matrix.one_apply_ne (Ne.symm hm), zero_mul]
      · intro hcon
        exact absurd (Finset.mem_univ i) hcon

/-! ## Translation of the affine coordinates -/

/-- **Chart translation.**  The observer group of `ker e_i^*` translates the zeroth-order affine
coordinates of the chart at `i` by constants. -/
theorem linearJetAction_affineCoord_of_mem {i k : n} (hk : k ≠ i)
    {g : SpecialLinearGroup n K} (hg : g ∈ chartSubsetStabilizer (K := K) {i}) :
    g • affineCoord (K := K) i k =
      affineCoord i k +
        algebraMap K (HomogeneousJetField n K)
          (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) k i) := by
  have hginv : (g⁻¹ : SpecialLinearGroup n K) ∈ chartSubsetStabilizer (K := K) {i} := inv_mem hg
  have hii : ((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) i i = 1 :=
    coe_apply_self_eq_one_of_mem_chartSubsetStabilizer hginv
  have hcol : ∀ (a m : n), m ≠ i →
      ((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) a m = (1 : Matrix n n K) a m :=
    fun a m hm => coe_apply_of_mem_chartSubsetStabilizer_singleton hginv a hm
  have hden : ∑ m, algebraMap K (HomogeneousJetField n K)
      (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) i m) * affineCoord i m = 1 := by
    rw [Finset.sum_eq_single i]
    · rw [hii, affineCoord_self, map_one, mul_one]
    · intro m _ hm
      rw [hcol i m hm, Matrix.one_apply_ne (Ne.symm hm), map_zero, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ i) hcon
  have hnum : ∑ m, algebraMap K (HomogeneousJetField n K)
      (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) k m) * affineCoord i m =
      affineCoord i k +
        algebraMap K (HomogeneousJetField n K)
          (((g⁻¹ : SpecialLinearGroup n K) : Matrix n n K) k i) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), affineCoord_self, mul_one,
      Finset.sum_eq_single_of_mem k (Finset.mem_erase.2 ⟨hk, Finset.mem_univ k⟩)]
    · rw [hcol k k (by simpa using hk), Matrix.one_apply_eq, map_one, one_mul, add_comm]
    · intro m hm hmk
      rw [hcol k m (Finset.mem_erase.1 hm).1, Matrix.one_apply_ne (Ne.symm hmk), map_zero,
        zero_mul]
  rw [linearJetAction_affineCoord, hnum, hden, div_one]

/-- Every positive-order affine jet of the chart at `i` is fixed by the observer group of
`ker e_i^*`. -/
theorem linearJetAction_affineJet_succ_of_mem {i k : n} (hk : k ≠ i) (l : ℕ)
    {g : SpecialLinearGroup n K} (hg : g ∈ chartSubsetStabilizer (K := K) {i}) :
    g • affineJet (K := K) i k (l + 1) = affineJet i k (l + 1) := by
  induction l with
  | zero =>
      rw [affineJet_succ, linearJetAction_shift, affineJet_zero,
        linearJetAction_affineCoord_of_mem hk hg, map_add, Derivation.map_algebraMap, add_zero]
  | succ l ih =>
      rw [affineJet_succ, linearJetAction_shift, ih]

/-! ## The chart tail field -/

/-- The positive-order affine jets of the chart whose infinity hyperplane is `ker e_i^*`. -/
def chartTailGenerators (i : n) (K : Type*) [Field K] : Set (HomogeneousJetField n K) :=
  {f | ∃ (k : n) (_ : k ≠ i) (l : ℕ), f = affineJet i k (l + 1)}

/-- The derivative horizon of the chart at `i`: the field generated by all positive-order jets of
its affine coordinates. -/
def chartTailField (i : n) (K : Type*) [Field K] :
    IntermediateField K (HomogeneousJetField n K) :=
  IntermediateField.adjoin K (chartTailGenerators i K)

/-- **Chart horizon inclusion.**  The derivative horizon of the chart at `i` is contained in the
horizon field of the covector `e_i^*`: every positive-order affine jet is invariant under the whole
observer group of `ker e_i^*`. -/
theorem chartTailField_le_horizonField (i : n) :
    chartTailField i K ≤ horizonField (K := K) {i} := by
  rw [chartTailField, IntermediateField.adjoin_le_iff]
  rintro f ⟨k, hk, l, rfl⟩ g hg
  exact linearJetAction_affineJet_succ_of_mem hk l hg

end

end GaloisForLFunctions.HTGeometry
