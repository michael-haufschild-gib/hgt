import GaloisForLFunctions.HTGeometry.DiscreteValuationHaar

/-!
# The discrete valuation formula for additive Haar modulus

The residue index computes the uniformizer modulus. A valuation-one unit
preserves the integral ball. Splitting any unit into these two parts identifies
its Haar modulus with the residue-normalized integer-valued valuation.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open MeasureTheory MeasureTheory.Measure
open scoped WithZero WithZeroMulInt Pointwise ENNReal NNReal
open DiscreteValuationHaar
noncomputable section

variable (L : Type*) [Field L] [Valued L ℤᵐ⁰]
variable [(Valued.v : Valuation L ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer L)]
local instance : (Valued.v : Valuation L ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 from one_lt_two)
local instance : NormedField L := Valued.toNormedField L ℤᵐ⁰
local instance : ProperSpace L :=
  Valued.integer.properSpace_iff_compactSpace_integer.mpr inferInstance
local instance : MeasurableSpace L := borel L
local instance : BorelSpace L := ⟨rfl⟩
local instance : IsDiscreteValuationRing (Integer L) :=
  (Valued.v : Valuation L ℤᵐ⁰).valuationSubring_isDiscreteValuationRing

private theorem distribHaarChar_eq_one_of_valuation_one (u : Lˣ)
    (hu : Valued.v (u : L) = 1) : distribHaarChar L u = 1 := by
  have hi : Valued.v ((u⁻¹ : Lˣ) : L) = 1 := by
    have he : ((u⁻¹ : Lˣ) : L) * (u : L) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h := congrArg (Valued.v : Valuation L ℤᵐ⁰) he
    simpa only [map_mul, hu, mul_one, map_one] using h
  have hs : u • ((Valued.v : Valuation L ℤᵐ⁰).integer : Set L) =
      ((Valued.v : Valuation L ℤᵐ⁰).integer : Set L) := by
    ext x
    rw [Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change Valued.v ((u : L) * y) ≤ 1
      rwa [map_mul, hu, one_mul]
    · intro hx
      refine ⟨((u⁻¹ : Lˣ) : L) * x, ?_, ?_⟩
      · change Valued.v (((u⁻¹ : Lˣ) : L) * x) ≤ 1
        rwa [map_mul, hi, one_mul]
      · change (u : L) * (((u⁻¹ : Lˣ) : L) * x) = x
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := normalizedHaar L)
    (s := ((Valued.v : Valuation L ℤᵐ⁰).integer : Set L))
    (by rw [normalizedHaar_integer]; exact one_ne_zero)
    (by rw [normalizedHaar_integer]; exact ENNReal.one_ne_top)
  rw [hs, normalizedHaar_integer]
  simp only [ENNReal.coe_one, one_mul]

private theorem toNNReal_exp {q : ℝ≥0} (hq : q ≠ 0) (m : ℤ) :
    WithZeroMulInt.toNNReal hq (WithZero.exp m) = q ^ m := by
  rw [WithZeroMulInt.toNNReal_neg_apply hq
    (show WithZero.exp m ≠ 0 from WithZero.exp_ne_zero)]
  rfl

omit [CompactSpace (Integer L)] in
/-- A valuation attaining `exp(-1)` has an irreducible integer with exactly that value. -/
theorem exists_irreducible_valuation_exp_neg_one
    (hval : WithZero.exp (-1 : ℤ) ∈ Set.range (Valued.v : Valuation L ℤᵐ⁰)) :
    ∃ π : Integer L, Irreducible π ∧ Valued.v (π : L) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := Integer L)
  refine ⟨π, hπ, ?_⟩
  have h := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (Valued.v : Valuation L ℤᵐ⁰) hπ.maximalIdeal_eq
  change Valued.v (π : L) = _ at h
  exact h.trans (congrArg Units.val
    (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range hval))

/-- The residue-normalized valuation is exactly the additive Haar modulus. -/
theorem distribHaarChar_eq_residueMagnitude
    (hval : WithZero.exp (-1 : ℤ) ∈ Set.range (Valued.v : Valuation L ℤᵐ⁰)) (u : Lˣ) :
    distribHaarChar L u = WithZeroMulInt.toNNReal
      (show (Nat.card (Residue L) : ℝ≥0) ≠ 0 from by
        exact_mod_cast Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩)
      (Valued.v (u : L)) := by
  obtain ⟨π, hπ, hπv⟩ := exists_irreducible_valuation_exp_neg_one L hval
  let P : Lˣ := uniformizerUnit L π hπ
  have hp : Valued.v (P : L) = WithZero.exp (-1 : ℤ) := hπv
  let m : ℤ := WithZero.log (Valued.v (u : L))
  have hu : Valued.v (u : L) = WithZero.exp m :=
    (WithZero.exp_log ((Valued.v : Valuation L ℤᵐ⁰).ne_zero_iff.mpr (Units.ne_zero u))).symm
  let b : Lˣ := u * P ^ m
  have hb : Valued.v (b : L) = 1 := by
    change Valued.v ((u : L) * ((P ^ m : Lˣ) : L)) = 1
    rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, hp, hu,
      ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  have hcharb : distribHaarChar L b = 1 :=
    distribHaarChar_eq_one_of_valuation_one L b hb
  have hdecomp : u = b * P ^ (-m) := by
    dsimp [b]
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  have hcharP : distribHaarChar L P = (Nat.card (Residue L) : ℝ≥0)⁻¹ :=
    uniformizer_distribHaarChar L π hπ
  rw [hu, toNNReal_exp]
  calc
    distribHaarChar L u = distribHaarChar L (b * P ^ (-m)) := congrArg _ hdecomp
    _ = distribHaarChar L b * (distribHaarChar L P) ^ (-m) := by rw [map_mul, map_zpow]
    _ = (Nat.card (Residue L) : ℝ≥0) ^ m := by
      rw [hcharb, hcharP, one_mul, inv_zpow', neg_neg]

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein

#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.distribHaarChar_eq_residueMagnitude
