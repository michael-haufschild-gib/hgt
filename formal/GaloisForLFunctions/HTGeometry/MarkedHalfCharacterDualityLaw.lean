import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.FieldTheory.RatFunc.Degree
import Mathlib.CategoryTheory.Groupoid.Basic
import Mathlib.CategoryTheory.CodiscreteCategory
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import GaloisForLFunctions.Bottcher.Pi1CMinusZero
import GaloisForLFunctions.HTGeometry.PairGroupoidBidescentLaw
import GaloisForLFunctions.Hurwitz.ContinuedLadderDeformationBridge

/-!
# Marked half-character duality and soldering

Exact local algebra and marked groupoid-cocycle infrastructure for the Stage-2 card
`marked-half-character-duality-soldering-and-cofinal-diagonal-inverse-obstruction-law.md`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory

/-! ## Marked augmentation cocycle -/

universe u v w v'

variable (R : Type u) [CommRing R]

/-- A linear representation of a groupoid, including strict identity and composition laws. -/
structure LinearGroupoidRepresentation (G : Type v) [Groupoid G] where
  fiber : G → Type w
  addCommGroup : ∀ X, AddCommGroup (fiber X)
  module : ∀ X, Module R (fiber X)
  map : ∀ {X Y : G}, (X ⟶ Y) → fiber X →ₗ[R] fiber Y
  map_id : ∀ X x, map (𝟙 X) x = x
  map_comp : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) x,
    map (f ≫ g) x = map g (map f x)

attribute [instance] LinearGroupoidRepresentation.addCommGroup
attribute [instance] LinearGroupoidRepresentation.module

variable {R}

/-- Marked zero-cochain on a linear groupoid representation. -/
structure MarkedGroupoidSection {G : Type v} [Groupoid G]
    (E : LinearGroupoidRepresentation R G) where
  value : ∀ X, E.fiber X

/-- Marked augmentation cocycle `∇_θ(f)=ρ(f)θ_source-θ_target`. -/
def markedAugmentation {G : Type v} [Groupoid G]
    (E : LinearGroupoidRepresentation R G) (theta : MarkedGroupoidSection E)
    {X Y : G} (f : X ⟶ Y) : E.fiber Y :=
  E.map f (theta.value X) - theta.value Y

/-- Exact twisted one-cocycle law for a marked augmentation. -/
theorem markedAugmentation_comp {G : Type v} [Groupoid G]
    (E : LinearGroupoidRepresentation R G) (theta : MarkedGroupoidSection E)
    {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    markedAugmentation E theta (f ≫ g) =
      E.map g (markedAugmentation E theta f) + markedAugmentation E theta g := by
  rw [markedAugmentation, markedAugmentation, markedAugmentation, E.map_comp, map_sub]
  abel

/-- The marked augmentation is normalized at identity arrows. -/
theorem markedAugmentation_id {G : Type v} [Groupoid G]
    (E : LinearGroupoidRepresentation R G) (theta : MarkedGroupoidSection E) (X : G) :
    markedAugmentation E theta (𝟙 X) = 0 := by
  rw [markedAugmentation, E.map_id, sub_self]

/-- Scaling the marked zero-cochain. -/
def scaleMarkedGroupoidSection {G : Type v} [Groupoid G]
    {E : LinearGroupoidRepresentation R G} (c : R) (theta : MarkedGroupoidSection E) :
    MarkedGroupoidSection E where
  value X := c • theta.value X

/-- Source normalization is load-bearing: scaling the marking scales its cocycle exactly. -/
theorem markedAugmentation_scale {G : Type v} [Groupoid G]
    (E : LinearGroupoidRepresentation R G) (c : R) (theta : MarkedGroupoidSection E)
    {X Y : G} (f : X ⟶ Y) :
    markedAugmentation E (scaleMarkedGroupoidSection c theta) f =
      c • markedAugmentation E theta f := by
  simp [markedAugmentation, scaleMarkedGroupoidSection, smul_sub]

/-- A strict map of marked groupoid representations along a functor. -/
structure MarkedRepresentationMap
    {G : Type v} [Groupoid G] {H : Type v'} [Groupoid H]
    (F : G ⥤ H) (E : LinearGroupoidRepresentation R G)
    (E' : LinearGroupoidRepresentation R H)
    (theta : MarkedGroupoidSection E) (theta' : MarkedGroupoidSection E') where
  fiberMap : ∀ X, E.fiber X →ₗ[R] E'.fiber (F.obj X)
  map_naturality : ∀ {X Y : G} (f : X ⟶ Y) (x : E.fiber X),
    fiberMap Y (E.map f x) = E'.map (F.map f) (fiberMap X x)
  mark_naturality : ∀ X, fiberMap X (theta.value X) = theta'.value (F.obj X)

/-- Marked augmentation is strictly natural when both representation and marking are carried. -/
theorem MarkedRepresentationMap.markedAugmentation_naturality
    {G : Type v} [Groupoid G] {H : Type v'} [Groupoid H]
    {F : G ⥤ H} {E : LinearGroupoidRepresentation R G}
    {E' : LinearGroupoidRepresentation R H}
    {theta : MarkedGroupoidSection E} {theta' : MarkedGroupoidSection E'}
    (Phi : MarkedRepresentationMap F E E' theta theta')
    {X Y : G} (f : X ⟶ Y) :
    Phi.fiberMap Y (markedAugmentation E theta f) =
      markedAugmentation E' theta' (F.map f) := by
  rw [markedAugmentation, markedAugmentation, map_sub, Phi.map_naturality,
    Phi.mark_naturality, Phi.mark_naturality]

/-! ## Duality-root Cartan law -/

/-- Coarse holonomy `z=u²` of a marked half-character. -/
def halfCharacterCoarse (u : ℂˣ) : ℂ := (u : ℂ) ^ 2

/-- Reflection-odd soldering coordinate `S=u-u⁻¹`. -/
def halfCharacterOdd (u : ℂˣ) : ℂ := (u : ℂ) - (u : ℂ)⁻¹

/-- Reflection-even companion `C=u+u⁻¹`. -/
def halfCharacterEven (u : ℂˣ) : ℂ := (u : ℂ) + (u : ℂ)⁻¹

/-- Raw coarse-holonomy defect `κ=z-1`. -/
def coarseHolonomyDefect (z : ℂ) : ℂ := z - 1

/-- Soldering identity `κ=uS`. -/
theorem coarseHolonomyDefect_eq_half_mul_odd (u : ℂˣ) :
    coarseHolonomyDefect (halfCharacterCoarse u) =
      (u : ℂ) * halfCharacterOdd u := by
  rw [coarseHolonomyDefect, halfCharacterCoarse, halfCharacterOdd]
  field_simp [Units.ne_zero u]

/-- Duality-weighted Bianchi identity `κ(z)+zκ(z⁻¹)=0`. -/
theorem coarseHolonomyDefect_duality_bianchi (u : ℂˣ) :
    coarseHolonomyDefect (halfCharacterCoarse u) +
      halfCharacterCoarse u * coarseHolonomyDefect (halfCharacterCoarse u)⁻¹ = 0 := by
  change ((u : ℂ) ^ 2 - 1) +
    (u : ℂ) ^ 2 * (((u : ℂ) ^ 2)⁻¹ - 1) = 0
  field_simp [Units.ne_zero u]
  ring

/-- Reflection-paired energy law `-κ(z)κ(z⁻¹)=S(u)²`. -/
theorem coarseHolonomyDefect_reflection_energy (u : ℂˣ) :
    -(coarseHolonomyDefect (halfCharacterCoarse u) *
        coarseHolonomyDefect (halfCharacterCoarse u)⁻¹) =
      halfCharacterOdd u ^ 2 := by
  change -(((u : ℂ) ^ 2 - 1) * (((u : ℂ) ^ 2)⁻¹ - 1)) =
    ((u : ℂ) - (u : ℂ)⁻¹) ^ 2
  field_simp [Units.ne_zero u]
  ring

/-- Odd/even Cartan product and its unrooted coarse form. -/
theorem halfCharacter_cartan_product (u : ℂˣ) :
    halfCharacterCoarse u - (halfCharacterCoarse u)⁻¹ =
        halfCharacterEven u * halfCharacterOdd u ∧
      halfCharacterEven u * halfCharacterOdd u =
        (1 + (halfCharacterCoarse u)⁻¹) *
          coarseHolonomyDefect (halfCharacterCoarse u) := by
  constructor
  · change (u : ℂ) ^ 2 - ((u : ℂ) ^ 2)⁻¹ =
      ((u : ℂ) + (u : ℂ)⁻¹) * ((u : ℂ) - (u : ℂ)⁻¹)
    field_simp [Units.ne_zero u]
    ring
  · change ((u : ℂ) + (u : ℂ)⁻¹) * ((u : ℂ) - (u : ℂ)⁻¹) =
      (1 + ((u : ℂ) ^ 2)⁻¹) * ((u : ℂ) ^ 2 - 1)
    field_simp [Units.ne_zero u]

/-- Complete four-identity form of the duality-root Cartan theorem. -/
theorem markedHalfCharacter_dualityRootCartan (u : ℂˣ) :
    coarseHolonomyDefect (halfCharacterCoarse u) =
        (u : ℂ) * halfCharacterOdd u ∧
    coarseHolonomyDefect (halfCharacterCoarse u) +
        halfCharacterCoarse u * coarseHolonomyDefect (halfCharacterCoarse u)⁻¹ = 0 ∧
    -(coarseHolonomyDefect (halfCharacterCoarse u) *
        coarseHolonomyDefect (halfCharacterCoarse u)⁻¹) =
        halfCharacterOdd u ^ 2 ∧
    halfCharacterCoarse u - (halfCharacterCoarse u)⁻¹ =
        halfCharacterEven u * halfCharacterOdd u ∧
    halfCharacterEven u * halfCharacterOdd u =
        (1 + (halfCharacterCoarse u)⁻¹) *
          coarseHolonomyDefect (halfCharacterCoarse u) := by
  exact ⟨coarseHolonomyDefect_eq_half_mul_odd u,
    coarseHolonomyDefect_duality_bianchi u,
    coarseHolonomyDefect_reflection_energy u,
    (halfCharacter_cartan_product u).1,
    (halfCharacter_cartan_product u).2⟩

/-- On the split positive-real form, the Laurent square is exactly `4 sinh²(x)` and is
nonnegative. -/
theorem splitReal_halfCharacter_energy (x : ℝ) :
    (Real.exp x - (Real.exp x)⁻¹) ^ 2 = 4 * Real.sinh x ^ 2 ∧
      0 ≤ (Real.exp x - (Real.exp x)⁻¹) ^ 2 := by
  have hinv : (Real.exp x)⁻¹ = Real.exp (-x) := by rw [← Real.exp_neg]
  rw [hinv]
  constructor
  · rw [Real.sinh_eq]
    ring
  · positivity

/-- Concrete half-character away from the compact unit circle. -/
def twoComplexUnit : ℂˣ := Units.mk0 2 (by norm_num)

theorem twoComplexUnit_off_unitCircle : ‖(twoComplexUnit : ℂ)‖ ≠ 1 := by
  norm_num [twoComplexUnit]

/-- The exact Cartan identities do not select the compact unit locus: `u=2` satisfies them. -/
theorem dualityRootCartan_does_not_select_unitCircle :
    ‖(twoComplexUnit : ℂ)‖ ≠ 1 ∧
      coarseHolonomyDefect (halfCharacterCoarse twoComplexUnit) =
        (twoComplexUnit : ℂ) * halfCharacterOdd twoComplexUnit ∧
      coarseHolonomyDefect (halfCharacterCoarse twoComplexUnit) +
        halfCharacterCoarse twoComplexUnit *
          coarseHolonomyDefect (halfCharacterCoarse twoComplexUnit)⁻¹ = 0 ∧
      -(coarseHolonomyDefect (halfCharacterCoarse twoComplexUnit) *
          coarseHolonomyDefect (halfCharacterCoarse twoComplexUnit)⁻¹) =
        halfCharacterOdd twoComplexUnit ^ 2 := by
  exact ⟨twoComplexUnit_off_unitCircle,
    coarseHolonomyDefect_eq_half_mul_odd twoComplexUnit,
    coarseHolonomyDefect_duality_bianchi twoComplexUnit,
    coarseHolonomyDefect_reflection_energy twoComplexUnit⟩

/-! ## Deck parity and one-loop cocycle -/

/-- The coarse defect is even under the root-deck involution. -/
theorem coarseHolonomyDefect_neg_half (u : ℂˣ) :
    coarseHolonomyDefect (halfCharacterCoarse (-u)) =
      coarseHolonomyDefect (halfCharacterCoarse u) := by
  simp [coarseHolonomyDefect, halfCharacterCoarse]

/-- The odd soldering coordinate reverses under the root-deck involution. -/
theorem halfCharacterOdd_neg (u : ℂˣ) :
    halfCharacterOdd (-u) = -halfCharacterOdd u := by
  simp [halfCharacterOdd]
  ring

/-- The even companion also reverses under the root-deck involution. -/
theorem halfCharacterEven_neg (u : ℂˣ) :
    halfCharacterEven (-u) = -halfCharacterEven u := by
  simp [halfCharacterEven]
  ring

/-- Duality reverses the oriented odd coordinate while preserving its square energy. -/
theorem halfCharacterOdd_inv (u : ℂˣ) :
    halfCharacterOdd u⁻¹ = -halfCharacterOdd u ∧
      halfCharacterOdd u⁻¹ ^ 2 = halfCharacterOdd u ^ 2 := by
  have hodd : halfCharacterOdd u⁻¹ = -halfCharacterOdd u := by
    simp only [halfCharacterOdd, Units.val_inv_eq_inv_val, inv_inv]
    ring
  exact ⟨hodd, by rw [hodd, neg_sq]⟩

/-- One-loop marked cocycle `τ(m)=(z^m-1)θ`. -/
def markedLoopCocycle (z : ℂˣ) (theta : ℂ) (m : ℤ) : ℂ :=
  ((z : ℂ) ^ m - 1) * theta

/-- Twisted additivity of the one-loop marked cocycle. -/
theorem markedLoopCocycle_add (z : ℂˣ) (theta : ℂ) (m n : ℤ) :
    markedLoopCocycle z theta (m + n) =
      markedLoopCocycle z theta m + (z : ℂ) ^ m * markedLoopCocycle z theta n := by
  rw [markedLoopCocycle, markedLoopCocycle, markedLoopCocycle, zpow_add₀ (Units.ne_zero z)]
  ring

/-! ## Strict pair-groupoid representative -/

/-- Marking on the two-object pair presentation. -/
def markedPairPotential : Bool → ℂ
  | false => 0
  | true => 1

/-- The marked pair-groupoid coboundary is a genuine nonzero strict cocycle representative. -/
theorem markedPairPotential_coboundary_true_false :
    pairDescentDefect markedPairPotential true false = 1 := by
  simp [pairDescentDefect, markedPairPotential]

/-- The same strict representative takes the opposite value on the reverse arrow. -/
theorem markedPairPotential_coboundary_false_true :
    pairDescentDefect markedPairPotential false true = -1 := by
  simp [pairDescentDefect, markedPairPotential]

/-- The pair representative satisfies the strict one-cocycle identity. -/
theorem markedPairPotential_coboundary_cocycle (x y z : Bool) :
    pairDescentDefect markedPairPotential x z =
      pairDescentDefect markedPairPotential x y +
        pairDescentDefect markedPairPotential y z :=
  pairDescentDefect_cocycle markedPairPotential x y z

/-- Every normalized strict cocycle on the one-object unit presentation is zero. -/
theorem normalizedUnitPresentationCocycle_zero
    (c : PUnit → PUnit → ℂ) (hnormalized : ∀ x, c x x = 0) :
    ∀ x y, c x y = 0 := by
  rintro ⟨⟩ ⟨⟩
  exact hnormalized PUnit.unit

/-- Concrete strict-representative mismatch: unit presentation has only zero normalized values,
while the pair presentation carries the marked nonzero exact cocycle. -/
theorem strictCocycle_pairPresentation_not_unitPresentation :
    (∀ c : PUnit → PUnit → ℂ, (∀ x, c x x = 0) → ∀ x y, c x y = 0) ∧
      pairDescentDefect markedPairPotential true false ≠ 0 := by
  exact ⟨normalizedUnitPresentationCocycle_zero,
    by rw [markedPairPotential_coboundary_true_false]; exact one_ne_zero⟩

/-- Inclusion of the one-object unit presentation into the two-object pair presentation. -/
def unitToPairPresentation :
    Codiscrete PUnit ⥤ Codiscrete Bool :=
  Codiscrete.functorOfFun fun _ => false

/-- Collapse of the two-object pair presentation to the one-object unit presentation. -/
def pairToUnitPresentation :
    Codiscrete Bool ⥤ Codiscrete PUnit :=
  Codiscrete.functorOfFun fun _ => PUnit.unit

/-- Literal categorical (hence Morita) equivalence between unit and pair groupoid presentations. -/
def unitPairPresentationEquivalence :
    Codiscrete PUnit ≌ Codiscrete Bool where
  functor := unitToPairPresentation
  inverse := pairToUnitPresentation
  unitIso := Codiscrete.natIso
  counitIso := Codiscrete.natIso
  functor_unitIso_comp _ := rfl

/-- The Morita-equivalent presentations nevertheless have different strict normalized
representatives: the unit value is forced to zero while the marked pair value is one. -/
theorem moritaEquivalent_presentations_strictCocycle_mismatch :
    Nonempty (Codiscrete PUnit ≌ Codiscrete Bool) ∧
      (∀ c : PUnit → PUnit → ℂ, (∀ x, c x x = 0) → ∀ x y, c x y = 0) ∧
      pairDescentDefect markedPairPotential true false = 1 := by
  exact ⟨⟨unitPairPresentationEquivalence⟩,
    normalizedUnitPresentationCocycle_zero,
    markedPairPotential_coboundary_true_false⟩

/-! ### Literal first cohomology of unit and pair presentations -/

/-- Normalized strict one-cocycles on the complete-relation groupoid presentation. -/
def pairPresentationOneCocycles (X : Type v) :
    Submodule ℂ (X → X → ℂ) where
  carrier := {c | ∀ x y z, c x z = c x y + c y z}
  zero_mem' := by
    intro x y z
    simp
  add_mem' := by
    intro c d hc hd x y z
    change c x z + d x z = (c x y + d x y) + (c y z + d y z)
    rw [hc, hd]
    ring
  smul_mem' := by
    intro a c hc x y z
    change a * c x z = a * c x y + a * c y z
    rw [hc, mul_add]

/-- Exact one-coboundaries inside strict one-cocycles. -/
def pairPresentationOneCoboundaries (X : Type v) :
    Submodule ℂ (pairPresentationOneCocycles X) where
  carrier := {c | ∃ theta : X → ℂ, ∀ x y, c.1 x y = theta x - theta y}
  zero_mem' := by
    refine ⟨0, ?_⟩
    simp
  add_mem' := by
    rintro c d ⟨theta, htheta⟩ ⟨eta, heta⟩
    refine ⟨theta + eta, ?_⟩
    intro x y
    change c.1 x y + d.1 x y =
      (theta x + eta x) - (theta y + eta y)
    rw [htheta, heta]
    ring
  smul_mem' := by
    rintro a c ⟨theta, htheta⟩
    refine ⟨a • theta, ?_⟩
    intro x y
    change a * c.1 x y = a * theta x - a * theta y
    rw [htheta, mul_sub]

/-- Literal strict first cohomology of a complete-relation groupoid presentation. -/
abbrev PairPresentationH1 (X : Type v) :=
  pairPresentationOneCocycles X ⧸ pairPresentationOneCoboundaries X

/-- Every strict one-cocycle on a nonempty pair presentation is an exact coboundary. -/
theorem pairPresentationOneCocycles_mem_coboundaries
    (X : Type v) [Nonempty X] (c : pairPresentationOneCocycles X) :
    c ∈ pairPresentationOneCoboundaries X := by
  let x0 : X := Classical.choice ‹Nonempty X›
  refine ⟨fun x => c.1 x x0, ?_⟩
  intro x y
  have hc := c.2 x y x0
  change c.1 x y = c.1 x x0 - c.1 y x0
  rw [hc]
  ring

theorem pairPresentationOneCoboundaries_eq_top
    (X : Type v) [Nonempty X] :
    pairPresentationOneCoboundaries X = ⊤ := by
  ext c
  simp only [Submodule.mem_top, iff_true]
  exact pairPresentationOneCocycles_mem_coboundaries X c

/-- The literal strict first cohomology of every nonempty pair presentation vanishes. -/
theorem pairPresentationH1_subsingleton (X : Type v) [Nonempty X] :
    Subsingleton (PairPresentationH1 X) := by
  change Subsingleton
    (pairPresentationOneCocycles X ⧸ pairPresentationOneCoboundaries X)
  rw [pairPresentationOneCoboundaries_eq_top X]
  infer_instance

/-- Both one-object unit and two-object pair presentations have zero literal `H¹`. -/
theorem unit_and_pair_presentations_H1_subsingleton :
    Subsingleton (PairPresentationH1 Unit) ∧
      Subsingleton (PairPresentationH1 Bool) := by
  exact ⟨pairPresentationH1_subsingleton Unit,
    pairPresentationH1_subsingleton Bool⟩

/-! ## Free-history relation curvature -/

variable {S V : Type*} [AddCommGroup S] [Module ℂ S]
  [AddCommGroup V] [Module ℂ V]

/-- Free-history one-step cocycle for the conjugation action on a landing. -/
def freeHistoryOneCocycle (T : V →ₗ[ℂ] V) (tauInv : S →ₗ[ℂ] S)
    (L : S →ₗ[ℂ] V) : S →ₗ[ℂ] V :=
  T.comp (L.comp tauInv) - L

/-- Composing the free-history cocycle with `τ` gives the literal dagger defect `TL-Lτ`. -/
theorem freeHistoryOneCocycle_comp_tau
    (T : V →ₗ[ℂ] V) (tau tauInv : S →ₗ[ℂ] S) (L : S →ₗ[ℂ] V)
    (hinv : tauInv.comp tau = LinearMap.id) :
    (freeHistoryOneCocycle T tauInv L).comp tau =
      T.comp L - L.comp tau := by
  ext x
  have hinvApply := LinearMap.congr_fun hinv x
  simp only [freeHistoryOneCocycle, LinearMap.comp_apply, LinearMap.sub_apply,
    LinearMap.id_apply] at hinvApply ⊢
  rw [hinvApply]

/-- Two-step relation curvature `T²L-Lτ²`. -/
def freeHistoryTwoRelationCurvature
    (T : V →ₗ[ℂ] V) (tau : S →ₗ[ℂ] S) (L : S →ₗ[ℂ] V) :
    S →ₗ[ℂ] V :=
  T.comp (T.comp L) - L.comp (tau.comp tau)

/-- If `τ²=1` and `T²=z`, the kernel relation is exactly `(z-1)L`. -/
theorem freeHistoryTwoRelationCurvature_eq
    (T : V →ₗ[ℂ] V) (tau : S →ₗ[ℂ] S) (L : S →ₗ[ℂ] V) (z : ℂ)
    (htau : tau.comp tau = LinearMap.id)
    (hT : T.comp T = z • LinearMap.id) :
    freeHistoryTwoRelationCurvature T tau L = (z - 1) • L := by
  ext x
  have htauApply := LinearMap.congr_fun htau x
  have hTApply := LinearMap.congr_fun hT (L x)
  simp only [freeHistoryTwoRelationCurvature, LinearMap.comp_apply,
    LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply]
    at htauApply hTApply ⊢
  rw [htauApply, hTApply]
  rw [sub_smul, one_smul]

/-- At neutral coarse holonomy the relation curvature vanishes, so the free-history coboundary
descends through the `2ℤ` relation. -/
theorem freeHistoryTwoRelationCurvature_zero_of_neutral_coarseHolonomy
    (T : V →ₗ[ℂ] V) (tau : S →ₗ[ℂ] S) (L : S →ₗ[ℂ] V)
    (htau : tau.comp tau = LinearMap.id)
    (hT : T.comp T = LinearMap.id) :
    freeHistoryTwoRelationCurvature T tau L = 0 := by
  have hT' : T.comp T = (1 : ℂ) • LinearMap.id := by simpa using hT
  rw [freeHistoryTwoRelationCurvature_eq T tau L 1 htau hT']
  simp

/-- Vanishing on the kernel relation forces neutral coarse holonomy for a nonzero landing. -/
theorem coarseHolonomy_eq_one_of_relationCurvature_zero
    (T : V →ₗ[ℂ] V) (tau : S →ₗ[ℂ] S) (L : S →ₗ[ℂ] V) (z : ℂ)
    (htau : tau.comp tau = LinearMap.id)
    (hT : T.comp T = z • LinearMap.id)
    (hL : L ≠ 0)
    (hzero : freeHistoryTwoRelationCurvature T tau L = 0) :
    z = 1 := by
  have hscalar : (z - 1) • L = 0 := by
    rw [← freeHistoryTwoRelationCurvature_eq T tau L z htau hT, hzero]
  obtain ⟨x, hx⟩ : ∃ x, L x ≠ 0 := by
    by_contra hall
    apply hL
    ext x
    simpa using not_exists.mp hall x
  have hpoint := LinearMap.congr_fun hscalar x
  simp only [LinearMap.smul_apply, LinearMap.zero_apply] at hpoint
  exact sub_eq_zero.mp ((smul_eq_zero_iff_left hx).mp hpoint)

/-! ## Root-torsor obstruction -/

/-- Squaring is not surjective on based loop classes of the punctured complex plane. -/
theorem squareLoopClass_not_surjective :
    ¬ Function.Surjective
      (fun p : Path Pi1CMinusZero.one_cs Pi1CMinusZero.one_cs =>
        (⟦Pi1CMinusZero.sqLoop p⟧ :
          Path.Homotopic.Quotient Pi1CMinusZero.one_cs Pi1CMinusZero.one_cs)) := by
  intro hsurj
  obtain ⟨gamma, hgamma⟩ := Pi1CMinusZero.degZ_surjective 1
  obtain ⟨p, rfl⟩ := hsurj gamma
  rw [Pi1CMinusZero.degZ_sqLoop] at hgamma
  omega

/-- A hypothetical continuous square-root section normalizes every based loop to a based
square-root loop.  Division by the root over `1` removes the possible `-1` basepoint. -/
def normalizedSectionRootLoop
    (s : C(Pi1CMinusZero.Cs, Pi1CMinusZero.Cs))
    (p : Path Pi1CMinusZero.one_cs Pi1CMinusZero.one_cs) :
    Path Pi1CMinusZero.one_cs Pi1CMinusZero.one_cs where
  toFun := fun t =>
    ⟨(s (p t) : ℂ) / (s Pi1CMinusZero.one_cs : ℂ),
      div_ne_zero (s (p t)).2 (s Pi1CMinusZero.one_cs).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val.comp (s.continuous.comp p.continuous_toFun)).div_const _
  source' := by
    apply Subtype.ext
    show (s (p 0) : ℂ) / (s Pi1CMinusZero.one_cs : ℂ) = 1
    rw [p.source]
    exact div_self (s Pi1CMinusZero.one_cs).2
  target' := by
    apply Subtype.ext
    show (s (p 1) : ℂ) / (s Pi1CMinusZero.one_cs : ℂ) = 1
    rw [p.target]
    exact div_self (s Pi1CMinusZero.one_cs).2

/-- Normalized loop obtained from a square-root section squares pointwise to the original loop. -/
theorem sqLoop_normalizedSectionRootLoop
    (s : C(Pi1CMinusZero.Cs, Pi1CMinusZero.Cs))
    (hsec : Function.RightInverse s Pi1CMinusZero.sqCs)
    (p : Path Pi1CMinusZero.one_cs Pi1CMinusZero.one_cs) :
    Pi1CMinusZero.sqLoop (normalizedSectionRootLoop s p) = p := by
  apply Path.ext
  funext t
  apply Subtype.ext
  show ((s (p t) : ℂ) / (s Pi1CMinusZero.one_cs : ℂ)) ^ 2 = (p t : ℂ)
  have hp := congrArg Subtype.val (hsec (p t))
  have hone := congrArg Subtype.val (hsec Pi1CMinusZero.one_cs)
  change (s (p t) : ℂ) ^ 2 = (p t : ℂ) at hp
  change (s Pi1CMinusZero.one_cs : ℂ) ^ 2 = 1 at hone
  rw [div_pow, hp, hone, div_one]

/-- The square map on the punctured complex plane has no global continuous section. -/
theorem not_exists_continuous_squareRoot_section :
    ¬ ∃ s : C(Pi1CMinusZero.Cs, Pi1CMinusZero.Cs),
      Function.RightInverse s Pi1CMinusZero.sqCs := by
  rintro ⟨s, hsec⟩
  apply squareLoopClass_not_surjective
  intro gamma
  induction gamma using Quotient.inductionOn with
  | _ p =>
      refine ⟨normalizedSectionRootLoop s p, ?_⟩
      exact congrArg
        (fun q : Path Pi1CMinusZero.one_cs Pi1CMinusZero.one_cs =>
          (⟦q⟧ : Path.Homotopic.Quotient Pi1CMinusZero.one_cs Pi1CMinusZero.one_cs))
        (sqLoop_normalizedSectionRootLoop s hsec p)

/-- There is no Laurent-polynomial square root of the coordinate `T`.  This is the algebraic
no-section obstruction for the square map on `G_m`. -/
theorem not_exists_laurentPolynomial_sq_eq_T_one :
    ¬ ∃ f : LaurentPolynomial ℂ, f ^ 2 = LaurentPolynomial.T 1 := by
  rintro ⟨f, hf⟩
  let Xunit : (RatFunc ℂ)ˣ := Units.mk0 RatFunc.X RatFunc.X_ne_zero
  let ev : LaurentPolynomial ℂ →+* RatFunc ℂ :=
    LaurentPolynomial.eval₂ (algebraMap ℂ (RatFunc ℂ)) Xunit
  let g : RatFunc ℂ := ev f
  have hsq : g * g = RatFunc.X := by
    change ev f * ev f = RatFunc.X
    rw [← map_mul, ← pow_two, hf]
    simp [ev, Xunit]
  have hg0 : g ≠ 0 := by
    intro hg
    rw [hg, zero_mul] at hsq
    exact RatFunc.X_ne_zero hsq.symm
  have hdegree := RatFunc.intDegree_mul hg0 hg0
  rw [hsq, RatFunc.intDegree_X] at hdegree
  omega

/-! ## Literal Hurwitz half-character realization -/

/-- Marked Hurwitz half-character `u(s)=exp(-πis)`. -/
def hurwitzMarkedHalfCharacter (s : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * Complex.I * s)

/-- The marked Hurwitz half-character squares to the actual monodromy scalar. -/
theorem hurwitzMarkedHalfCharacter_sq (s : ℂ) :
    hurwitzMarkedHalfCharacter s ^ 2 = HurwitzOrbit.monoScalar s := by
  rw [hurwitzMarkedHalfCharacter, HurwitzOrbit.monoScalar, ← Complex.exp_nat_mul]
  congr 1
  ring

/-- Integral exponent shift fixes coarse Hurwitz monodromy. -/
theorem hurwitzMonoScalar_add_one (s : ℂ) :
    HurwitzOrbit.monoScalar (s + 1) = HurwitzOrbit.monoScalar s := by
  rw [HurwitzOrbit.monoScalar, HurwitzOrbit.monoScalar]
  have hsplit :
      -(2 * (Real.pi : ℂ) * Complex.I * (s + 1)) =
        -(2 * (Real.pi : ℂ) * Complex.I * s) +
          ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Integral exponent shift flips the marked half-character sheet. -/
theorem hurwitzMarkedHalfCharacter_add_one (s : ℂ) :
    hurwitzMarkedHalfCharacter (s + 1) = -hurwitzMarkedHalfCharacter s := by
  rw [hurwitzMarkedHalfCharacter, hurwitzMarkedHalfCharacter]
  convert Complex.exp_sub_pi_mul_I (-(Real.pi : ℂ) * Complex.I * s) using 1
  all_goals ring

/-- Updating one continued-Hurwitz branch coefficient changes exactly its marked singular term. -/
theorem continuedDmodel_markedBranchIncrement
    (s : ℂ) {M : ℕ} (c : Fin (M + 1) → ℂ) (n : Fin (M + 1))
    (k : ℕ) (z : ℂ) :
    HurwitzLadder.continuedDmodel s M
          (Function.update c n (HurwitzOrbit.monoScalar s * c n)) n k z -
        HurwitzLadder.continuedDmodel s M c n k z =
      (HurwitzOrbit.monoScalar s - 1) * c n *
        Complex.exp (-(s + k) * z) := by
  rw [HurwitzLadder.continuedDmodel, HurwitzLadder.continuedDmodel]
  have hsum :
      (∑ n' : Fin (M + 1),
          (Function.update c n (HurwitzOrbit.monoScalar s * c n) n' - 1) *
            HurwitzLadder.dcorr s k (n : ℕ) (n' : ℕ) (Complex.exp z)) =
        ∑ n' : Fin (M + 1), (c n' - 1) *
          HurwitzLadder.dcorr s k (n : ℕ) (n' : ℕ) (Complex.exp z) := by
    refine Finset.sum_congr rfl (fun n' _ => ?_)
    by_cases h : n' = n
    · subst n'
      simp [HurwitzLadder.dcorr]
    · rw [Function.update_of_ne h]
  rw [hsum, Function.update_self]
  ring

/-- The actual logarithmic monodromy move is the marked augmentation cocycle
`(q-1)θ` on every Hurwitz ladder rung. -/
theorem continuedDmodel_shift_sub_eq_markedAugmentation
    (s : ℂ) {M : ℕ} (c : Fin (M + 1) → ℂ) (n : Fin (M + 1))
    (k : ℕ) (z : ℂ) :
    HurwitzLadder.continuedDmodel s M c n k
          (z + 2 * (Real.pi : ℂ) * Complex.I) -
        HurwitzLadder.continuedDmodel s M c n k z =
      (HurwitzOrbit.monoScalar s - 1) * c n *
        Complex.exp (-(s + k) * z) := by
  rw [HurwitzLadder.continuedDmodel_shift]
  exact continuedDmodel_markedBranchIncrement s c n k z

end GaloisForLFunctions.HTGeometry
