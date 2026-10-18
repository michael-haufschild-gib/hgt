import GaloisForLFunctions.RHTower.CHMDSignedRadicalQuotient
import GaloisForLFunctions.RHTower.CHMDFullSpectralNullspace
import GaloisForLFunctions.RHTower.CHMDOddBoundStateSignObstructionAndParityQuarterBound

/-!
# The full Weil form on the critical-band quotient

Both polar moments and the complete Weil bilinear form descend to the literal
signed quotient. The remaining Weil radical is exactly the two-pole plane.
Its closed polar-constrained complement has a nondegenerate Weil form, equal
there to the descended signed form. The nonzero ground class rules out strict
coercivity on the entire quotient before imposing the pole constraints.
-/

open MeasureTheory Set Filter Topology Complex Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDPolar

private theorem continuous_quotientPair_at (x : SignedQuotient) :
    Continuous (quotientPair x) :=
  continuous_quotientPair.comp (continuous_const.prodMk continuous_id)

def quotientCoshMoment (x : SignedQuotient) : ℝ :=
  -quotientPair (signedQuotientMk (constantLift 1)) x

def quotientSinhMoment (x : SignedQuotient) : ℝ :=
  quotientPair (signedQuotientMk oddPolarVector) x

@[simp] theorem quotientCoshMoment_mk (p : SourceGraph) :
    quotientCoshMoment (signedQuotientMk p) = ⟪p.val.fst, oneL⟫_ℝ := by
  rw [quotientCoshMoment, quotientPair_mk, sourcePair_ground, neg_neg, real_inner_comm]
  rfl

@[simp] theorem quotientSinhMoment_mk (p : SourceGraph) :
    quotientSinhMoment (signedQuotientMk p) = ⟪p.val.fst, tanhL⟫_ℝ := by
  rw [quotientSinhMoment, quotientPair_mk, sourcePair_oddPolarVector,
    polarSine_eq_inner_tanhL]

theorem quotientCoshMoment_eq_polarCosine (p : SourceGraph) :
    quotientCoshMoment (signedQuotientMk p) = polarCosine p := by
  rw [quotientCoshMoment, quotientPair_mk, sourcePair_ground_eq_polarCosine, neg_neg]

theorem quotientSinhMoment_eq_polarSine (p : SourceGraph) :
    quotientSinhMoment (signedQuotientMk p) = polarSine p := by
  rw [quotientSinhMoment, quotientPair_mk, sourcePair_oddPolarVector]

theorem continuous_quotientCoshMoment : Continuous quotientCoshMoment :=
  (continuous_quotientPair.comp (continuous_const.prodMk continuous_id)).neg

theorem continuous_quotientSinhMoment : Continuous quotientSinhMoment :=
  continuous_quotientPair_at (signedQuotientMk oddPolarVector)

def quotientWeilPair (x y : SignedQuotient) : ℝ :=
  quotientPair x y + 2 * (quotientCoshMoment x * quotientCoshMoment y) -
    2 * (quotientSinhMoment x * quotientSinhMoment y)

def quotientWeilForm (x : SignedQuotient) : ℝ := quotientWeilPair x x

@[simp] theorem quotientWeilPair_mk (p q : SourceGraph) :
    quotientWeilPair (signedQuotientMk p) (signedQuotientMk q) = weilBilin p q := by
  rw [quotientWeilPair, quotientPair_mk, quotientCoshMoment_mk, quotientCoshMoment_mk,
    quotientSinhMoment_mk, quotientSinhMoment_mk, sourcePair_eq_graph_inner]
  rfl

@[simp] theorem quotientWeilForm_mk (p : SourceGraph) :
    quotientWeilForm (signedQuotientMk p) = weilForm p := by
  rw [quotientWeilForm, quotientWeilPair_mk, weilForm_eq_weilBilin]

theorem continuous_quotientWeilForm : Continuous quotientWeilForm := by
  change Continuous (fun x => quotientEnergy x + 2 * (quotientCoshMoment x * quotientCoshMoment x) -
    2 * (quotientSinhMoment x * quotientSinhMoment x))
  exact (continuous_quotientEnergy.add
    ((continuous_quotientCoshMoment.mul continuous_quotientCoshMoment).const_mul 2)).sub
      ((continuous_quotientSinhMoment.mul continuous_quotientSinhMoment).const_mul 2)

theorem quotientWeilForm_representative (x : SignedQuotient) :
    quotientWeilForm x = weilForm (signedQuotientRepresentative x) := by
  rw [← quotientWeilForm_mk, signedQuotientMk_representative]

/-- The actual Weil form of each real compact test factors through the graph quotient. -/
theorem quotientWeilForm_testLift (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) :
    quotientWeilForm (signedQuotientMk (testLift f hf hc)) =
      (zetaZeroConfig.W (fun x => (f x : ℂ)) (fun x => (f x : ℂ))).re := by
  rw [quotientWeilForm_mk, testLift, weilForm_compactLift]
  simp only [phiDoobTest_phiDoobInv]

/-- The two actual pole constraints define a closed subspace of the quotient. -/
def quotientPolarSpace : Submodule ℝ SignedQuotient where
  carrier := {x | quotientCoshMoment x = 0 ∧ quotientSinhMoment x = 0}
  zero_mem' := by simp [quotientCoshMoment, quotientSinhMoment, quotientPair, sourcePair]
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    constructor
    · change -(quotientPair _ (x + y)) = 0
      rw [quotientPair_add_right, neg_add]
      change quotientCoshMoment x + quotientCoshMoment y = 0
      rw [hx, hy, zero_add]
    · change quotientPair _ (x + y) = 0
      rw [quotientPair_add_right]
      change quotientSinhMoment x + quotientSinhMoment y = 0
      rw [hx', hy', zero_add]
  smul_mem' := by
    rintro c x ⟨hx, hx'⟩
    constructor
    · change -(quotientPair _ (c • x)) = 0
      rw [quotientPair_smul_right, ← mul_neg, show -quotientPair _ x = 0 from hx, mul_zero]
    · change quotientPair _ (c • x) = 0
      rw [quotientPair_smul_right, show quotientPair _ x = 0 from hx', mul_zero]

theorem isClosed_quotientPolarSpace : IsClosed (quotientPolarSpace : Set SignedQuotient) :=
  (isClosed_eq continuous_quotientCoshMoment continuous_const).inter
    (isClosed_eq continuous_quotientSinhMoment continuous_const)

instance complete_quotientPolarSpace : CompleteSpace quotientPolarSpace := by
  letI : IsClosed (quotientPolarSpace : Set SignedQuotient) := isClosed_quotientPolarSpace
  exact IsClosed.completeSpace_coe

theorem quotientWeilForm_polar (x : quotientPolarSpace) :
    quotientWeilForm x = quotientEnergy x := by
  unfold quotientWeilForm quotientWeilPair quotientEnergy
  rw [x.property.1, x.property.2]
  ring

theorem signedQuotientMk_mem_polarSpace (p : SourceGraph) :
    signedQuotientMk p ∈ quotientPolarSpace ↔
      ⟪p.val.fst, oneL⟫_ℝ = 0 ∧ ⟪p.val.fst, tanhL⟫_ℝ = 0 := by
  change (quotientCoshMoment _ = 0 ∧ quotientSinhMoment _ = 0) ↔ _
  rw [quotientCoshMoment_mk, quotientSinhMoment_mk]

/-- The signed radical does not remove the nonzero polar ground class. -/
theorem signedQuotientMk_ground_ne_zero : signedQuotientMk (constantLift 1) ≠ 0 := by
  intro h
  have hc := radical_polarCosine_zero ((signedQuotientMk_eq_zero _).mp h)
  rw [polarCosine_ground] at hc
  norm_num at hc

theorem quotientWeilForm_ground : quotientWeilForm (signedQuotientMk (constantLift 1)) = 0 := by
  have hC := quotientCoshMoment_eq_polarCosine (constantLift 1)
  have hS := quotientSinhMoment_eq_polarSine (constantLift 1)
  rw [polarCosine_ground] at hC
  rw [polarSine_ground] at hS
  rw [quotientWeilForm, quotientWeilPair, quotientPair_mk,
    sourcePair_ground_eq_polarCosine, polarCosine_ground, hC, hS]
  norm_num

/-- Full Weil coercivity still needs pole constraints after removing the critical band. -/
theorem not_positive_quotientWeil_coercivity :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ x : SignedQuotient, c * ‖x‖ ^ 2 ≤ quotientWeilForm x := by
  rintro ⟨c, hc, h⟩
  have hg := h (signedQuotientMk (constantLift 1))
  rw [quotientWeilForm_ground] at hg
  exact (not_le_of_gt (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr
    signedQuotientMk_ground_ne_zero)))) hg


theorem quotientPair_sub_left (x y z : SignedQuotient) :
    quotientPair (x - y) z = quotientPair x z - quotientPair y z := by
  simp only [quotientPair, map_sub, sourcePair_sub_left]

theorem quotientPair_sub_right (x y z : SignedQuotient) :
    quotientPair x (y - z) = quotientPair x y - quotientPair x z := by
  rw [quotientPair_symm, quotientPair_sub_left, quotientPair_symm y x, quotientPair_symm z x]

theorem quotientCoshMoment_sub (x y : SignedQuotient) :
    quotientCoshMoment (x - y) = quotientCoshMoment x - quotientCoshMoment y := by
  simp only [quotientCoshMoment, quotientPair_sub_right]
  ring

theorem quotientSinhMoment_sub (x y : SignedQuotient) :
    quotientSinhMoment (x - y) = quotientSinhMoment x - quotientSinhMoment y :=
  quotientPair_sub_right _ _ _

theorem quotientCoshMoment_smul (c : ℝ) (x : SignedQuotient) :
    quotientCoshMoment (c • x) = c * quotientCoshMoment x := by
  simp only [quotientCoshMoment, quotientPair_smul_right]
  ring

theorem quotientSinhMoment_smul (c : ℝ) (x : SignedQuotient) :
    quotientSinhMoment (c • x) = c * quotientSinhMoment x :=
  quotientPair_smul_right _ _ _

@[simp] theorem quotientCoshMoment_ground :
    quotientCoshMoment (signedQuotientMk (constantLift 1)) = 1 / 2 := by
  rw [quotientCoshMoment_eq_polarCosine, polarCosine_ground]

@[simp] theorem quotientSinhMoment_ground :
    quotientSinhMoment (signedQuotientMk (constantLift 1)) = 0 := by
  rw [quotientSinhMoment_eq_polarSine, polarSine_ground]

@[simp] theorem quotientCoshMoment_oddPolar :
    quotientCoshMoment (signedQuotientMk oddPolarVector) = 0 := by
  rw [quotientCoshMoment_eq_polarCosine, polarCosine_oddPolarVector]

@[simp] theorem quotientSinhMoment_oddPolar :
    quotientSinhMoment (signedQuotientMk oddPolarVector) = 1 / 2 := by
  rw [quotientSinhMoment_eq_polarSine, polarSine_oddPolarVector]

/-- Remove the two polar coordinates after the exact critical-band quotient. -/
def quotientPolarReduction (x : SignedQuotient) : SignedQuotient :=
  x - (2 * quotientCoshMoment x) • signedQuotientMk (constantLift 1) -
    (2 * quotientSinhMoment x) • signedQuotientMk oddPolarVector

@[simp] theorem quotientCoshMoment_polarReduction (x : SignedQuotient) :
    quotientCoshMoment (quotientPolarReduction x) = 0 := by
  rw [quotientPolarReduction, quotientCoshMoment_sub, quotientCoshMoment_sub,
    quotientCoshMoment_smul, quotientCoshMoment_smul,
    quotientCoshMoment_ground, quotientCoshMoment_oddPolar]
  ring

@[simp] theorem quotientSinhMoment_polarReduction (x : SignedQuotient) :
    quotientSinhMoment (quotientPolarReduction x) = 0 := by
  rw [quotientPolarReduction, quotientSinhMoment_sub, quotientSinhMoment_sub,
    quotientSinhMoment_smul, quotientSinhMoment_smul,
    quotientSinhMoment_ground, quotientSinhMoment_oddPolar]
  ring

theorem quotientPolarReduction_mem (x : SignedQuotient) :
    quotientPolarReduction x ∈ quotientPolarSpace :=
  ⟨quotientCoshMoment_polarReduction x, quotientSinhMoment_polarReduction x⟩

theorem quotientPolarReduction_eq_self (x : quotientPolarSpace) :
    quotientPolarReduction x = x := by
  simp only [quotientPolarReduction, x.property.1, x.property.2, mul_zero, zero_smul, sub_zero]

theorem quotientWeilPair_symm (x y : SignedQuotient) :
    quotientWeilPair x y = quotientWeilPair y x := by
  unfold quotientWeilPair
  rw [quotientPair_symm]
  ring

theorem quotientPair_polarReduction_left (x y : SignedQuotient) :
    quotientPair (quotientPolarReduction x) y = quotientWeilPair x y := by
  simp only [quotientPolarReduction, quotientPair_sub_left, quotientPair_smul_left,
    quotientWeilPair, quotientCoshMoment, quotientSinhMoment]
  ring

theorem quotientPair_polarReduction_right (x y : SignedQuotient) :
    quotientPair x (quotientPolarReduction y) = quotientWeilPair x y := by
  rw [quotientPair_symm, quotientPair_polarReduction_left, quotientWeilPair_symm]

theorem quotientWeilPair_polar_left (x : quotientPolarSpace) (y : SignedQuotient) :
    quotientWeilPair x y = quotientPair x y := by
  simp only [quotientWeilPair, x.property.1, x.property.2, zero_mul, mul_zero, add_zero, sub_zero]

theorem quotientPair_polarReduction (x y : SignedQuotient) :
    quotientPair (quotientPolarReduction x) (quotientPolarReduction y) = quotientWeilPair x y := by
  rw [quotientPair_polarReduction_right]
  have h := quotientWeilPair_polar_left
    ⟨quotientPolarReduction x, quotientPolarReduction_mem x⟩ y
  exact h.trans (quotientPair_polarReduction_left x y)

/-- The remaining Weil radical is exactly the explicit two-pole plane. -/
theorem quotientWeil_radical_iff_polar_plane (x : SignedQuotient) :
    (∀ y, quotientWeilPair x y = 0) ↔
      x = (2 * quotientCoshMoment x) • signedQuotientMk (constantLift 1) +
        (2 * quotientSinhMoment x) • signedQuotientMk oddPolarVector := by
  have h : (∀ y, quotientWeilPair x y = 0) ↔ quotientPolarReduction x = 0 := by
    simp_rw [← quotientPair_polarReduction_left]
    exact quotientPair_nondegenerate _
  rw [h, quotientPolarReduction, sub_sub, sub_eq_zero]

/-- The full Weil form has no radical on the closed polar-constrained quotient. -/
theorem quotientWeil_polar_nondegenerate (x : quotientPolarSpace) :
    (∀ y : quotientPolarSpace, quotientWeilPair x y = 0) ↔ x = 0 := by
  constructor
  · intro h
    apply Subtype.ext
    apply (quotientPair_nondegenerate x).mp
    intro y
    have hy := h ⟨quotientPolarReduction y, quotientPolarReduction_mem y⟩
    change quotientWeilPair x (quotientPolarReduction y) = 0 at hy
    rw [quotientWeilPair_polar_left, quotientPair_polarReduction_right,
      quotientWeilPair_polar_left] at hy
    exact hy
  · rintro rfl y
    simp [quotientWeilPair, quotientPair, quotientCoshMoment, quotientSinhMoment, sourcePair]

end RHTower.CHMDDoobGraph
