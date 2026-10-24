import GaloisForLFunctions.ArithmeticOrientationTheory.TheWidthDictionary
import GaloisForLFunctions.ArithmeticOrientationTheory.TheEffectivityConeFromSections
import GaloisForLFunctions.ArithmeticOrientationTheory.TheEvenFlipIsReadAtThePrimeTwo
import GaloisForLFunctions.ArithmeticOrientationTheory.NyquistRiemannRochBeyondRankNullity
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhichArithmeticDataForceTheSign
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WittIntegralityIsNotPurity
import GaloisForLFunctions.ArithmeticCriticalityTheory.JumpRateCriticality
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheMagnitudePairIsFaithfulWhereTheSignIsBlind
import GaloisForLFunctions.TransHorizonIncidenceMechanics.SmallDampingMoebiusAndLiouvilleCancellationLaws
import «GaloisForLFunctions».«arithmetic-positivity-theory».CompactCriticalPolynomialWindowAndTemperednessBridge

/-!
# The Width Functor and the Selectivity Battery of Non-Objects

This module resolves Open Problem 11 of the Arithmetic Orientation Theory programme:
> *"Construct a functor from receivers to the width line through which every oriented invariant
> factors. The dictionary would become a theorem about a category of receivers, and the battery of
> §8 a list of its non-objects."*

## Mathematical Overview

1. **The Category of Receivers (`ReceiverObject`) and the Width Functor (`widthFunctor`):**
   - The **width line** `WidthLine := Set.Icc (0 : ℝ) (1 / 2)` is a thin category under the standard
     order `≤`.
   - An object `R : ReceiverObject` packages a receiver's critical threshold `widthVal : ℝ` in
     `[0, 1/2]` together with its graded admissibility predicate `admittedAt : ℝ → Prop` satisfying
     the universal threshold law `∀ σ ≥ 0, R.admittedAt σ ↔ R.widthVal ≤ σ`.
   - Morphisms `R₁ ⟶ R₂` in `ReceiverObject` are threshold dominations `R₁.widthVal ≤ R₂.widthVal`
     (equivalently, `∀ σ ≥ 0, R₂.admittedAt σ → R₁.admittedAt σ`).
   - The **width functor** `widthFunctor : ReceiverObject ⥤ WidthLine` sends `R` to
     `⟨R.widthVal, R.width_nonneg, R.width_le_half⟩` and is **full, faithful, and isomorphism-reflecting**
     (`widthFunctor_full`, `widthFunctor_faithful`, `isIso_iff_widthVal_eq`): two receivers are
     isomorphic in `ReceiverObject` (`R₁ ≅ R₂`) if and only if they have the same width value, and
     if and only if they admit the exact same thresholds `σ ≥ 0`.

2. **Canonical `ζ`-Receivers and Their Categorical Isomorphism:**
   We construct the canonical `ζ`-receivers and model receivers in `ReceiverObject`:
   - `spectralZeroReceiver` (spectral zero width `zetaZeroWidth`),
   - `abscissaReceiver` (zero abscissa excess `zetaZeroAbscissa - 1 / 2`),
   - `moebiusDampingReceiver` (Möbius damping threshold `receiverDampingRate`),
   - `liouvilleDampingReceiver` (Liouville damping threshold
     `sInf (derivedSet {ε | 0 < ε ∧ ReceiverBounded (dampedSignWeight liouvilleR ε)})`),
   - `xiHalfPlaneReceiver` (completed `ξ` half-plane bound `XiZeroHalfPlaneBound`),
   - `suzukiFormationReceiver` (completed Suzuki formation subpower energy),
   - `temperedConfigReceiver Z` (general tempered zero configuration `Z : TemperedZeroConfig`),
   - `nodeSetReceiver 𝒩` (prime-power node set `𝒩 : Set ℕ` with `nodeScale 𝒩`),
   - `scaleDepthReceiver p` (periodic off-line lattice `p : ScaleDepthDatum` with `sdDepth p` and
     `sInf (rateSet p)`).
   All six `ζ`-receivers are **canonically isomorphic** in `ReceiverObject` (`zetaReceivers_widthVal_eq`).

3. **Factorization of Oriented Invariants and the Categorical Width Dictionary:**
   Every graded admissibility predicate `R ↦ R.admittedAt σ` (`σ ≥ 0`) factors uniquely through
   `widthFunctor.obj R` (`admittedAt_factorsThrough_widthFunctor`), and every unit of the width,
   Castelnuovo–Severi, forcing-sign, and section-cone dictionaries factors through the zero-width
   subcategory predicate `IsZeroWidthObject R ↔ (widthFunctor.obj R).1 = 0` applied to the
   isomorphic `ζ`-receivers (`categoricalWidthDictionary_tfae`, `categoricalGradedWidthDictionary_tfae`).

4. **The Selectivity Battery of §8 as Non-Objects (`selectivityBattery_nonObjects`):**
   Every test in the selectivity battery of §8 is formalized as an unconditional theorem proving
   that the countermodel is either a non-object of `IsZeroWidthObject` (`width > 0`) or violates
   the receiver axioms (unitarity, scale-window temperedness, parity-flip payment, node
   completeness, unbounded aperture, full prime jump rate, or `β² L³` deficit precision).
-/

open Set Filter Topology MeasureTheory CategoryTheory
open scoped BigOperators Real ComplexConjugate
open Zeta23 _root_.RHTower
open GaloisForLFunctions.SquareRootThreshold
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.ScaleSignedIncidenceCriticality
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open _root_.RHTower.WeilOneSided _root_.RHTower.WeilSpectral

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ## §1. The Category of Receivers and the Width Functor to `[0, 1/2]` -/

/-- The **width line** `[0, 1/2]`, viewed as a thin category via its standard linear order. -/
abbrev WidthLine : Type := Set.Icc (0 : ℝ) (1 / 2)

/-- The zero point `0 ∈ [0, 1/2]` of the width line. -/
def widthZero : WidthLine := ⟨0, le_rfl, by norm_num⟩

/-- The maximal point `1/2 ∈ [0, 1/2]` of the width line. -/
def widthHalf : WidthLine := ⟨1 / 2, by norm_num, le_rfl⟩

/-- A **receiver object** packages a critical width threshold `widthVal ∈ [0, 1/2]` together with
its graded admissibility predicate `admittedAt : ℝ → Prop` satisfying the universal receiver law
`∀ σ ≥ 0, admittedAt σ ↔ widthVal ≤ σ`. -/
structure ReceiverObject where
  /-- The critical width of the receiver. -/
  widthVal : ℝ
  /-- Nonnegativity of the receiver width. -/
  width_nonneg : 0 ≤ widthVal
  /-- Upper bound `1/2` of the receiver width. -/
  width_le_half : widthVal ≤ 1 / 2
  /-- Graded admissibility predicate at threshold `σ`. -/
  admittedAt : ℝ → Prop
  /-- Universal threshold law: for `σ ≥ 0`, `admittedAt σ` holds iff `widthVal ≤ σ`. -/
  admittedAt_iff : ∀ {σ : ℝ}, 0 ≤ σ → (admittedAt σ ↔ widthVal ≤ σ)

namespace ReceiverObject

/-- Admissibility at threshold `0` is equivalent to vanishing of `widthVal`. -/
theorem admittedAt_zero_iff (R : ReceiverObject) :
    R.admittedAt 0 ↔ R.widthVal = 0 := by
  rw [R.admittedAt_iff le_rfl]
  exact ⟨fun h => le_antisymm h R.width_nonneg, fun h => h.le⟩

/-- Monotonicity of `admittedAt` on nonnegative thresholds. -/
theorem admittedAt_mono (R : ReceiverObject) {σ₁ σ₂ : ℝ} (hσ₁ : 0 ≤ σ₁) (hle : σ₁ ≤ σ₂)
    (h : R.admittedAt σ₁) : R.admittedAt σ₂ := by
  rw [R.admittedAt_iff (hσ₁.trans hle)]
  exact ((R.admittedAt_iff hσ₁).mp h).trans hle

/-- Construct a `ReceiverObject` with the canonical threshold predicate `fun σ => w ≤ σ`. -/
def ofWidth (w : ℝ) (h0 : 0 ≤ w) (hhalf : w ≤ 1 / 2) : ReceiverObject where
  widthVal := w
  width_nonneg := h0
  width_le_half := hhalf
  admittedAt := fun σ => w ≤ σ
  admittedAt_iff := fun _ => Iff.rfl

end ReceiverObject

/-- Preorder on `ReceiverObject` induced by `widthVal`, making `ReceiverObject` a thin category
where morphisms `R₁ ⟶ R₂` are width dominations `R₁.widthVal ≤ R₂.widthVal`. -/
instance : Preorder ReceiverObject :=
  Preorder.lift ReceiverObject.widthVal

/-- In `ReceiverObject`, `R₁ ≤ R₂` is definitionally `R₁.widthVal ≤ R₂.widthVal`. -/
@[simp] theorem receiverObject_le_iff (R₁ R₂ : ReceiverObject) :
    R₁ ≤ R₂ ↔ R₁.widthVal ≤ R₂.widthVal := Iff.rfl

/-- A morphism `R₁ ⟶ R₂` exists if and only if every nonnegative threshold admitted by `R₂` is
admitted by `R₁`. -/
theorem nonempty_receiverHom_iff_forall_admittedAt (R₁ R₂ : ReceiverObject) :
    Nonempty (R₁ ⟶ R₂) ↔ ∀ σ : ℝ, 0 ≤ σ → R₂.admittedAt σ → R₁.admittedAt σ := by
  constructor
  · rintro ⟨f⟩ σ hσ h₂
    rw [R₁.admittedAt_iff hσ]
    exact (show R₁.widthVal ≤ R₂.widthVal from leOfHom f).trans ((R₂.admittedAt_iff hσ).mp h₂)
  · intro h
    refine ⟨homOfLE ?_⟩
    have hR₂ : R₂.admittedAt R₂.widthVal := (R₂.admittedAt_iff R₂.width_nonneg).mpr le_rfl
    exact (R₁.admittedAt_iff R₂.width_nonneg).mp (h R₂.widthVal R₂.width_nonneg hR₂)

/-- **The Width Functor** `widthFunctor : ReceiverObject ⥤ WidthLine` sending each receiver to its
point on the width line `[0, 1/2]`. -/
def widthFunctor : ReceiverObject ⥤ WidthLine where
  obj R := ⟨R.widthVal, R.width_nonneg, R.width_le_half⟩
  map f := homOfLE (leOfHom f)

@[simp] theorem widthFunctor_obj_coe (R : ReceiverObject) :
    (widthFunctor.obj R : ℝ) = R.widthVal := rfl

theorem widthFunctor_obj_ext {R₁ R₂ : ReceiverObject} (h : R₁.widthVal = R₂.widthVal) :
    widthFunctor.obj R₁ = widthFunctor.obj R₂ :=
  Subtype.ext h

/-- `widthFunctor` is faithful. -/
instance widthFunctor_faithful : widthFunctor.Faithful where
  map_injective {_ _} _ _ _ := Subsingleton.elim _ _

/-- `widthFunctor` is full. -/
instance widthFunctor_full : widthFunctor.Full where
  map_surjective {_ _} f := ⟨homOfLE (leOfHom f), Subsingleton.elim _ _⟩

/-- Construct an isomorphism `R₁ ≅ R₂` in `ReceiverObject` from equality of widths. -/
def receiverIsoOfWidthEq {R₁ R₂ : ReceiverObject} (h : R₁.widthVal = R₂.widthVal) : R₁ ≅ R₂ where
  hom := homOfLE h.le
  inv := homOfLE h.ge

/-- Two objects in `ReceiverObject` are isomorphic iff their widths are equal, and iff they admit
the exact same nonnegative thresholds. -/
theorem nonempty_iso_iff_widthVal_eq (R₁ R₂ : ReceiverObject) :
    Nonempty (R₁ ≅ R₂) ↔ R₁.widthVal = R₂.widthVal := by
  constructor
  · rintro ⟨e⟩
    exact le_antisymm (leOfHom e.hom) (leOfHom e.inv)
  · intro h
    exact ⟨receiverIsoOfWidthEq h⟩

theorem nonempty_iso_iff_forall_admittedAt (R₁ R₂ : ReceiverObject) :
    Nonempty (R₁ ≅ R₂) ↔ ∀ σ : ℝ, 0 ≤ σ → (R₁.admittedAt σ ↔ R₂.admittedAt σ) := by
  rw [nonempty_iso_iff_widthVal_eq]
  constructor
  · intro h σ hσ
    rw [R₁.admittedAt_iff hσ, R₂.admittedAt_iff hσ, h]
  · intro h
    refine le_antisymm ?_ ?_
    · exact (R₁.admittedAt_iff R₂.width_nonneg).mp
        ((h R₂.widthVal R₂.width_nonneg).mpr ((R₂.admittedAt_iff R₂.width_nonneg).mpr le_rfl))
    · exact (R₂.admittedAt_iff R₁.width_nonneg).mp
        ((h R₁.widthVal R₁.width_nonneg).mp ((R₁.admittedAt_iff R₁.width_nonneg).mpr le_rfl))

/-! ## §2. The Canonical `ζ`-Receivers, Model Receivers, and Categorical Isomorphism -/

/-- 1. **The Spectral Zero Receiver** (`widthVal = zetaZeroWidth`). -/
def spectralZeroReceiver : ReceiverObject where
  widthVal := zetaZeroWidth
  width_nonneg := zetaZeroWidth_nonneg
  width_le_half := zetaZeroWidth_le_half
  admittedAt σ := ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ
  admittedAt_iff hσ := (zetaZeroWidth_le_iff_re_le hσ).symm

/-- 2. **The Zero-Abscissa Receiver** (`widthVal = zetaZeroAbscissa - 1 / 2`). -/
def abscissaReceiver : ReceiverObject where
  widthVal := zetaZeroAbscissa - 1 / 2
  width_nonneg := by linarith [half_le_zetaZeroAbscissa]
  width_le_half := by
    rw [← zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    exact zetaZeroWidth_le_half
  admittedAt σ := zetaZeroAbscissa ≤ 1 / 2 + σ
  admittedAt_iff _ := ⟨fun h => by linarith, fun h => by linarith⟩

/-- 3. **The Damped Möbius Receiver** (`widthVal = receiverDampingRate`). -/
def moebiusDampingReceiver : ReceiverObject where
  widthVal := receiverDampingRate
  width_nonneg := by
    rw [receiverDampingRate_eq_zetaZeroAbscissa_sub_half]
    linarith [half_le_zetaZeroAbscissa]
  width_le_half := by
    rw [receiverDampingRate_eq_zetaZeroAbscissa_sub_half, ← zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    exact zetaZeroWidth_le_half
  admittedAt σ := ∀ ε : ℝ, σ < ε → ReceiverBounded (pmPowerDampedRealWeight ε)
  admittedAt_iff {σ} hσ := by
    rw [receiverDampingRate_eq_zetaZeroAbscissa_sub_half, ← zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    constructor
    · intro h
      by_contra hlt
      push Not at hlt
      set ε := (σ + zetaZeroWidth) / 2
      have hacc : AccPt ε (𝓟 receiverDampings) := by
        refine accPt_of_Ioo_subset (lt_add_one ε) fun η hη => ?_
        have hη_pos : 0 < η := by dsimp [ε] at hη; linarith [hη.1, zetaZeroWidth_nonneg]
        rw [mem_receiverDampings_iff_receiverBounded hη_pos]
        exact h η (by dsimp [ε] at hη; linarith [hη.1])
      have hrate : receiverDampingRate ≤ ε :=
        csInf_le bddBelow_derivedSet_receiverDampings (mem_derivedSet.mpr hacc)
      rw [receiverDampingRate_eq_zetaZeroAbscissa_sub_half,
        ← zetaZeroWidth_eq_zetaZeroAbscissa_sub_half] at hrate
      dsimp [ε] at hrate
      linarith
    · intro hle ε hε
      exact receiverBounded_moebius_of_zetaZeroAbscissa_sub_half_lt
        (by rw [← zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]; linarith)

/-- 4. **The Damped Liouville Receiver**
(`widthVal = sInf (derivedSet {ε | 0 < ε ∧ ReceiverBounded (dampedSignWeight liouvilleR ε)})`). -/
def liouvilleDampingReceiver : ReceiverObject where
  widthVal := sInf (derivedSet {ε : ℝ | 0 < ε ∧ ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε)})
  width_nonneg := by
    rw [sInf_derivedSet_liouville_dampings_eq_zetaZeroAbscissa_sub_half]
    linarith [half_le_zetaZeroAbscissa]
  width_le_half := by
    rw [sInf_derivedSet_liouville_dampings_eq_zetaZeroAbscissa_sub_half,
      ← zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    exact zetaZeroWidth_le_half
  admittedAt σ := ∀ ε : ℝ, σ < ε → ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε)
  admittedAt_iff {σ} hσ := by
    rw [sInf_derivedSet_liouville_dampings_eq_zetaZeroAbscissa_sub_half]
    have hmoeb := moebiusDampingReceiver.admittedAt_iff hσ
    simp only [moebiusDampingReceiver] at hmoeb
    rw [receiverDampingRate_eq_zetaZeroAbscissa_sub_half] at hmoeb
    refine (forall₂_congr fun ε hε => ?_).trans hmoeb
    exact (receiverBounded_moebius_iff_liouville (by linarith)).symm

/-- 5. **The Completed `ξ` Half-Plane Receiver** (`widthVal = zetaZeroWidth`). -/
def xiHalfPlaneReceiver : ReceiverObject where
  widthVal := zetaZeroWidth
  width_nonneg := zetaZeroWidth_nonneg
  width_le_half := zetaZeroWidth_le_half
  admittedAt σ := XiZeroHalfPlaneBound σ
  admittedAt_iff {_} hσ := (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).symm

/-- 6. **The Completed Suzuki Formation Receiver** (`widthVal = zetaZeroWidth`). -/
def suzukiFormationReceiver : ReceiverObject where
  widthVal := zetaZeroWidth
  width_nonneg := zetaZeroWidth_nonneg
  width_le_half := zetaZeroWidth_le_half
  admittedAt σ := ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
    ∀ N : ℕ, 2 ≤ N → suzukiCompletedFormationEnergy N ≤ B * (N : ℝ) ^ (2 * (1 / 2 + σ) + ε)
  admittedAt_iff {_} hσ := (zetaZeroWidth_le_iff_suzukiCompletedFormationEnergy_subpower hσ).symm

/-- 7. **General Tempered Zero Configuration Receiver** (`widthVal = width Z`). -/
def temperedConfigReceiver (Z : TemperedZeroConfig) : ReceiverObject :=
  ReceiverObject.ofWidth (width Z) (width_nonneg Z) (width_le_half Z)

/-- 8. **Prime-Power Node-Set Receiver** (`widthVal = nodeScale 𝒩`). -/
def nodeSetReceiver (𝒩 : Set ℕ) : ReceiverObject :=
  ReceiverObject.ofWidth (nodeScale 𝒩) (nodeScale_nonneg 𝒩) (nodeScale_le_half 𝒩)

/-- 9. **Scale-Depth Lattice Receiver** (`widthVal = sInf (rateSet p) = sdDepth p`). -/
def scaleDepthReceiver (p : ScaleDepthDatum) : ReceiverObject where
  widthVal := sInf (rateSet p)
  width_nonneg := by rw [sInf_rateSet p]; exact p.2.2.1.le
  width_le_half := by rw [sInf_rateSet p]; exact p.2.2.2
  admittedAt σ := sdDepth p ≤ σ
  admittedAt_iff _ := by rw [sInf_rateSet p]

/-- **All six canonical `ζ`-receivers have the exact same width `zetaZeroWidth` and are
canonically isomorphic in `ReceiverObject`.** -/
theorem zetaReceivers_widthVal_eq :
    abscissaReceiver.widthVal = spectralZeroReceiver.widthVal ∧
    moebiusDampingReceiver.widthVal = spectralZeroReceiver.widthVal ∧
    liouvilleDampingReceiver.widthVal = spectralZeroReceiver.widthVal ∧
    xiHalfPlaneReceiver.widthVal = spectralZeroReceiver.widthVal ∧
    suzukiFormationReceiver.widthVal = spectralZeroReceiver.widthVal :=
  ⟨zetaZeroWidth_eq_zetaZeroAbscissa_sub_half.symm,
   receiverDampingRate_eq_zetaZeroAbscissa_sub_half.trans
     zetaZeroWidth_eq_zetaZeroAbscissa_sub_half.symm,
   sInf_derivedSet_liouville_dampings_eq_zetaZeroAbscissa_sub_half.trans
     zetaZeroWidth_eq_zetaZeroAbscissa_sub_half.symm,
   rfl,
   rfl⟩

/-- Explicit categorical isomorphisms between `spectralZeroReceiver` and all other `ζ`-receivers. -/
def isoSpectralAbscissa : spectralZeroReceiver ≅ abscissaReceiver :=
  receiverIsoOfWidthEq zetaReceivers_widthVal_eq.1.symm

def isoSpectralMoebius : spectralZeroReceiver ≅ moebiusDampingReceiver :=
  receiverIsoOfWidthEq zetaReceivers_widthVal_eq.2.1.symm

def isoSpectralLiouville : spectralZeroReceiver ≅ liouvilleDampingReceiver :=
  receiverIsoOfWidthEq zetaReceivers_widthVal_eq.2.2.1.symm

def isoSpectralXiHalfPlane : spectralZeroReceiver ≅ xiHalfPlaneReceiver :=
  receiverIsoOfWidthEq zetaReceivers_widthVal_eq.2.2.2.1.symm

def isoSpectralSuzukiFormation : spectralZeroReceiver ≅ suzukiFormationReceiver :=
  receiverIsoOfWidthEq zetaReceivers_widthVal_eq.2.2.2.2.symm

/-- `widthFunctor` maps all six `ζ`-receivers to the exact same object on `WidthLine`. -/
theorem widthFunctor_obj_zetaReceivers_eq :
    widthFunctor.obj abscissaReceiver = widthFunctor.obj spectralZeroReceiver ∧
    widthFunctor.obj moebiusDampingReceiver = widthFunctor.obj spectralZeroReceiver ∧
    widthFunctor.obj liouvilleDampingReceiver = widthFunctor.obj spectralZeroReceiver ∧
    widthFunctor.obj xiHalfPlaneReceiver = widthFunctor.obj spectralZeroReceiver ∧
    widthFunctor.obj suzukiFormationReceiver = widthFunctor.obj spectralZeroReceiver := by
  rcases zetaReceivers_widthVal_eq with ⟨h1, h2, h3, h4, h5⟩
  exact ⟨widthFunctor_obj_ext h1, widthFunctor_obj_ext h2, widthFunctor_obj_ext h3,
    widthFunctor_obj_ext h4, widthFunctor_obj_ext h5⟩

/-! ## §3. Factorization of Oriented Invariants Through `widthFunctor` -/

/-- A predicate `P : ReceiverObject → Prop` **factors through `widthFunctor`** if there is a
predicate `Q : WidthLine → Prop` on `[0, 1/2]` such that `P R ↔ Q (widthFunctor.obj R)` for all
receivers `R`. -/
def FactorsThroughWidthFunctor (P : ReceiverObject → Prop) : Prop :=
  ∃ Q : WidthLine → Prop, ∀ R : ReceiverObject, P R ↔ Q (widthFunctor.obj R)

/-- Every predicate factoring through `widthFunctor` is invariant under isomorphism in
`ReceiverObject`. -/
theorem iff_of_iso_of_factorsThroughWidthFunctor {P : ReceiverObject → Prop}
    (hP : FactorsThroughWidthFunctor P) {R₁ R₂ : ReceiverObject} (e : R₁ ≅ R₂) :
    P R₁ ↔ P R₂ := by
  obtain ⟨Q, hQ⟩ := hP
  rw [hQ R₁, hQ R₂]
  have heq : widthFunctor.obj R₁ = widthFunctor.obj R₂ :=
    widthFunctor_obj_ext (le_antisymm (leOfHom e.hom) (leOfHom e.inv))
  rw [heq]

/-- **Universal Factorization of Graded Admissibility (`admittedAt_factorsThrough_widthFunctor`):**
For every threshold `σ ≥ 0`, the admissibility predicate `fun R => R.admittedAt σ` factors through
`widthFunctor` via `fun w => w.1 ≤ σ`. -/
theorem admittedAt_factorsThrough_widthFunctor {σ : ℝ} (hσ : 0 ≤ σ) :
    FactorsThroughWidthFunctor (fun R : ReceiverObject => R.admittedAt σ) :=
  ⟨fun w => w.1 ≤ σ, fun R => by dsimp; exact R.admittedAt_iff hσ⟩

/-- **The Zero-Width Subcategory Predicate (`IsZeroWidthObject`):**
An object `R : ReceiverObject` is a zero-width (critical-line / pure) object if
`widthFunctor.obj R = widthZero` (equivalently `R.admittedAt 0`). -/
def IsZeroWidthObject (R : ReceiverObject) : Prop :=
  widthFunctor.obj R = widthZero

theorem isZeroWidthObject_iff_widthVal_eq_zero (R : ReceiverObject) :
    IsZeroWidthObject R ↔ R.widthVal = 0 :=
  ⟨fun h => by have := congrArg Subtype.val h; exact this,
   fun h => Subtype.ext (by show R.widthVal = 0; exact h)⟩

theorem isZeroWidthObject_iff_admittedAt_zero (R : ReceiverObject) :
    IsZeroWidthObject R ↔ R.admittedAt 0 :=
  (isZeroWidthObject_iff_widthVal_eq_zero R).trans (R.admittedAt_zero_iff).symm

theorem isZeroWidthObject_factorsThrough_widthFunctor :
    FactorsThroughWidthFunctor IsZeroWidthObject :=
  ⟨fun w => w = widthZero, fun _ => Iff.rfl⟩

/-- **The Categorical Width Dictionary (`categoricalWidthDictionary_tfae`):**
Unites the zero-width object conditions `IsZeroWidthObject R` of the six isomorphic `ζ`-receivers
in `ReceiverObject` with the units of the width, Castelnuovo–Severi, forcing-sign, and section-cone
dictionaries into one 15-way equivalence. -/
theorem categoricalWidthDictionary_tfae : List.TFAE [
    RiemannHypothesis,
    IsZeroWidthObject spectralZeroReceiver,
    IsZeroWidthObject abscissaReceiver,
    IsZeroWidthObject moebiusDampingReceiver,
    IsZeroWidthObject liouvilleDampingReceiver,
    IsZeroWidthObject xiHalfPlaneReceiver,
    IsZeroWidthObject suzukiFormationReceiver,
    scalingSurface.HodgeIndex,
    scalingSurface.BezoutAxiom (sectionEffectivityCone scalingSurface),
    ∀ r : ℝ, 0 < r →
      (scalingSubsurface (oddRealTestsAt r)).BezoutAxiom
        (coupledArithmeticCone (oddRealTestsAt r)),
    ∃ E : Set ScalingCycle, scalingSurface.RiemannRochAxiom E ∧ scalingSurface.AmpleAxiom E,
    ∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermPosIndex (intersectionGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) f) = 1,
    ∀ ε : ℝ, 0 < ε → ∃ (N : ℕ) (c : ℕ → ℝ),
      ∑' M : ℕ, (1 + sievePrefixDiscrepancy N M c) ^ 2 / ((M : ℝ) * ((M : ℝ) + 1)) < ε,
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∫ t in Icc 0 L, normalizedLogError t ^ 2 ≤ C * (1 + L),
    ¬ ∃ R : ℝ, Refutes (radiusReading R) WeilPositiveFull
      (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))] := by
  tfae_have 1 ↔ 2 := by
    rw [isZeroWidthObject_iff_widthVal_eq_zero, spectralZeroReceiver,
      riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  tfae_have 2 ↔ 3 :=
    iff_of_iso_of_factorsThroughWidthFunctor isZeroWidthObject_factorsThrough_widthFunctor
      isoSpectralAbscissa
  tfae_have 2 ↔ 4 :=
    iff_of_iso_of_factorsThroughWidthFunctor isZeroWidthObject_factorsThrough_widthFunctor
      isoSpectralMoebius
  tfae_have 2 ↔ 5 :=
    iff_of_iso_of_factorsThroughWidthFunctor isZeroWidthObject_factorsThrough_widthFunctor
      isoSpectralLiouville
  tfae_have 2 ↔ 6 :=
    iff_of_iso_of_factorsThroughWidthFunctor isZeroWidthObject_factorsThrough_widthFunctor
      isoSpectralXiHalfPlane
  tfae_have 2 ↔ 7 :=
    iff_of_iso_of_factorsThroughWidthFunctor isZeroWidthObject_factorsThrough_widthFunctor
      isoSpectralSuzukiFormation
  tfae_have 1 ↔ 8 := scalingSurface_hodgeIndex_iff.symm
  tfae_have 8 ↔ 9 := (sectionEffectivityCone_bezout_iff_hodgeIndex scalingSurface).symm
  tfae_have 1 ↔ 10 := riemannHypothesis_iff_rightZeros_zeta_eq_empty.trans
    (rightZeros_zeta_eq_empty_iff_forall_odd_scalingSubsurface_hodgeIndex.trans
      (forall₂_congr fun r _ =>
        (coupledArithmeticCone_bezout_iff_hodgeIndex (oddRealTestsAt r)).symm))
  tfae_have 1 ↔ 11 := riemannHypothesis_iff_exists_effectivity
  tfae_have 1 ↔ 12 := riemannHypothesis_iff_one_positive_square
  tfae_have 1 ↔ 13 := riemannHypothesis_iff_pronic_prefix_energy
  tfae_have 1 ↔ 14 := riemannHypothesis_iff_meanSquare_band
  tfae_have 1 ↔ 15 := riemannHypothesis_iff_no_radiusReading_refutes
  tfae_finish

/-- **The Categorical Graded Width Dictionary (`categoricalGradedWidthDictionary_tfae`):**
At any nonnegative threshold `σ ≥ 0`, the graded admissibility predicates `R.admittedAt σ` of all
six `ζ`-receivers factor through `(widthFunctor.obj R).1 ≤ σ` and are unconditionally equivalent. -/
theorem categoricalGradedWidthDictionary_tfae {σ : ℝ} (hσ : 0 ≤ σ) : List.TFAE [
    (widthFunctor.obj spectralZeroReceiver).1 ≤ σ,
    spectralZeroReceiver.admittedAt σ,
    abscissaReceiver.admittedAt σ,
    moebiusDampingReceiver.admittedAt σ,
    liouvilleDampingReceiver.admittedAt σ,
    xiHalfPlaneReceiver.admittedAt σ,
    suzukiFormationReceiver.admittedAt σ] := by
  tfae_have 1 ↔ 2 := by
    rw [widthFunctor_obj_coe]
    exact (spectralZeroReceiver.admittedAt_iff hσ).symm
  tfae_have 2 ↔ 3 :=
    iff_of_iso_of_factorsThroughWidthFunctor (admittedAt_factorsThrough_widthFunctor hσ)
      isoSpectralAbscissa
  tfae_have 2 ↔ 4 :=
    iff_of_iso_of_factorsThroughWidthFunctor (admittedAt_factorsThrough_widthFunctor hσ)
      isoSpectralMoebius
  tfae_have 2 ↔ 5 :=
    iff_of_iso_of_factorsThroughWidthFunctor (admittedAt_factorsThrough_widthFunctor hσ)
      isoSpectralLiouville
  tfae_have 2 ↔ 6 :=
    iff_of_iso_of_factorsThroughWidthFunctor (admittedAt_factorsThrough_widthFunctor hσ)
      isoSpectralXiHalfPlane
  tfae_have 2 ↔ 7 :=
    iff_of_iso_of_factorsThroughWidthFunctor (admittedAt_factorsThrough_widthFunctor hσ)
      isoSpectralSuzukiFormation
  tfae_finish

/-! ## §4. The Selectivity Battery of §8 as Non-Objects -/

/-- **Selectivity Test 1 (Golden Datum & Witt Integrality):**
`goldenDatum` has an integral zeta series `Zℤ ∈ 1 + X ℤ⟦X⟧`, integral nonnegative point counts,
and the functional equation `β ↦ β⁻¹`, yet is a **non-object** of the unitary curve class
(`¬ ∀ i, ‖goldenDatum.β i‖ = 1`) and refutes Bézout for `sectionEffectivityCone`. -/
theorem selectivityBattery_goldenDatum_nonObject :
    (∃ Zℤ : PowerSeries ℤ, PowerSeries.constantCoeff Zℤ = 1 ∧
      PowerSeries.map (Int.castRingHom ℂ) Zℤ = goldenDatum.zetaSeries) ∧
    (∀ j, ∃ n : ℤ, goldenDatum.pointCount j = n) ∧
    (∀ i, goldenDatum.β (goldenDatum.fePerm i) * goldenDatum.β i = 1) ∧
    (¬ ∀ i, ‖goldenDatum.β i‖ = 1) ∧
    ¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).BezoutAxiom
        (sectionEffectivityCone (goldenDatum.windowSurface ({0, 1} : Finset ℕ))) :=
  ⟨witt_integral_not_pure.1, witt_integral_not_pure.2.1, witt_integral_not_pure.2.2.1,
   witt_integral_not_pure.2.2.2, goldenDatum_not_bezout_sectionEffectivityCone.1⟩

/-- **Selectivity Test 2 (Shifted Zeta Pair `ζ(s - a) ζ(s + a)`):**
For any non-zero shift `a ≠ 0`, `shiftedPairVonMangoldt a` has the exact same rank-based Dirichlet
section count `h0` as `Λ`, yet is a **non-object** of the scale-window temperedness gate
(`¬ Summable (fun r => shiftedPairVonMangoldt a r / r^{1 + windowDilationExponent L})`) and
strictly inflates the Frobenius mass (`4 * frobeniusMass < frobeniusMass_shiftedPair`). -/
theorem selectivityBattery_shiftedPair_nonObject {a : ℝ} (ha : a ≠ 0) :
    (∀ (N : ℕ) (lam : ℕ → ℝ) (R : ℕ),
      h0 (weightedDirichletSampling N
          (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R) =
        h0 (weightedDirichletSampling N
          (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R)) ∧
    (∀ {L : ℕ}, 1 ≤ L → 1 / |a| - 2 ≤ Real.log L →
      ¬ Summable (fun r : ℕ =>
        shiftedPairVonMangoldt a r / (r : ℝ) ^ (1 + windowDilationExponent L))) ∧
    (∀ {N : ℕ} (_hN : 2 ≤ N) (lam : ℕ → ℝ) (R : ℕ),
      4 * frobeniusMass (weightedDirichletSampling N
          (fun m : Fin N => (ArithmeticFunction.vonMangoldt ((m : ℕ) + 1) : ℂ)) lam R) <
        frobeniusMass (weightedDirichletSampling N
          (fun m : Fin N => (shiftedPairVonMangoldt a ((m : ℕ) + 1) : ℂ)) lam R)) :=
  ⟨fun N lam R => (h0_rank_h1_weightedDirichletSampling_shiftedPair_eq_vonMangoldt N a lam R).1,
   fun hL hLa => not_summable_shiftedPairVonMangoldt_windowDilationExponent ha hL hLa,
   fun hN lam R => (frobeniusMass_weightedDirichletSampling_shiftedPair_gt hN ha lam R).2⟩

/-- **Selectivity Test 3 (Parity Twins — Fermi and Liouville):**
For `0 < ε ≤ 1 / 2`, `fermiWeight ε` and `fermiFlipWeight ε` share identical Ramanujan amplitudes,
yet `fermiWeight ε` is paid (`ReceiverBounded`) while `fermiFlipWeight ε` is an unpaid **non-object**
(`¬ ReceiverBounded`); and for `zetaZeroWidth < ε ≤ 1 / 2`, `dampedSignWeight liouvilleR ε` is paid
while its positive smooth-power twin `liouvilleTwin ε` diverges. -/
theorem selectivityBattery_parityTwins_nonObject :
    (∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
      (∀ e, |weightRamanujanCoeff (fermiFlipWeight ε) e| =
          |weightRamanujanCoeff (fermiWeight ε) e|) ∧
      ReceiverBounded (fermiWeight ε) ∧
      ¬ ReceiverBounded (fermiFlipWeight ε)) ∧
    (∀ {ε : ℝ}, zetaZeroWidth < ε → ε ≤ 1 / 2 →
      (∀ e : ℕ, |weightRamanujanCoeff (liouvilleTwin ε) e| =
          |weightRamanujanCoeff (dampedSignWeight RHTower.liouvilleR ε) e|) ∧
      ReceiverBounded (dampedSignWeight RHTower.liouvilleR ε) ∧
      Tendsto (fun T => weightPronicEnergy (liouvilleTwin ε)
        (∑' d : ℕ, liouvilleTwin ε d / d) T) atTop atTop) := by
  refine ⟨fun hε hε2 => ?_, fun hε hε2 => ?_⟩
  · obtain ⟨-, -, -, hamp, hpaid, hunpaid⟩ := fermi_evenFlip_parityPair hε hε2
    exact ⟨hamp, hpaid, hunpaid⟩
  · rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half] at hε
    obtain ⟨hamp, -, hpaid, hdiv⟩ := liouville_parityPair_of_zetaZeroAbscissa_sub_half_lt hε hε2
    exact ⟨hamp, hpaid, hdiv⟩

/-- **Selectivity Test 4 (Prime-Power Node Completeness in `ReceiverObject`):**
In `ReceiverObject`, the full prime-power node set `nodeSetReceiver {n | IsPrimePow n}` is a
zero-width object (`IsZeroWidthObject`), whereas deleting `2` produces a maximal-width **non-object**
(`widthFunctor.obj = widthHalf`, `¬ IsZeroWidthObject`), deleting `4` refutes zero-pole positivity
on every node set (`¬ ZeroPoleBlindPositiveOn (𝒩 \ {4})`), and deleting `6` is invisible. -/
theorem selectivityBattery_nodes_nonObject :
    IsZeroWidthObject (nodeSetReceiver {n : ℕ | IsPrimePow n}) ∧
    widthFunctor.obj (nodeSetReceiver (deleteNode 2 {n : ℕ | IsPrimePow n})) = widthHalf ∧
    ¬ IsZeroWidthObject (nodeSetReceiver (deleteNode 2 {n : ℕ | IsPrimePow n})) ∧
    (∀ 𝒩 : Set ℕ, ¬ ZeroPoleBlindPositiveOn (𝒩 \ {4})) ∧
    (∀ 𝒩 : Set ℕ, ZeroPoleBlindPositiveOn (𝒩 \ {6}) ↔ ZeroPoleBlindPositiveOn 𝒩) := by
  have h0 : IsZeroWidthObject (nodeSetReceiver {n : ℕ | IsPrimePow n}) := by
    rw [isZeroWidthObject_iff_widthVal_eq_zero]
    exact nodeScale_primePowers
  have h2 : widthFunctor.obj (nodeSetReceiver (deleteNode 2 {n : ℕ | IsPrimePow n})) = widthHalf :=
    Subtype.ext (show nodeScale (deleteNode 2 {n : ℕ | IsPrimePow n}) = 1 / 2 from
      nodeScale_deleteNode_two)
  have hnot : ¬ IsZeroWidthObject (nodeSetReceiver (deleteNode 2 {n : ℕ | IsPrimePow n})) := by
    rw [isZeroWidthObject_iff_widthVal_eq_zero]
    change ¬ nodeScale (deleteNode 2 {n : ℕ | IsPrimePow n}) = 0
    rw [nodeScale_deleteNode_two]
    norm_num
  exact ⟨h0, h2, hnot, not_zeroPoleBlindPositiveOn_diff_four, zeroPoleBlindPositiveOn_diff_six_iff⟩

/-- **Selectivity Test 5 (Finite-Data / Bounded-Aperture Non-Objects in `ReceiverObject`):**
For every bounded aperture `a > 0`, there exists `Z : TemperedZeroConfig` satisfying
`aperturePositivity a Z` whose receiver object `temperedConfigReceiver Z` has maximal width
`widthFunctor.obj (temperedConfigReceiver Z) = widthHalf` and is a **non-object** of
`IsZeroWidthObject`. -/
theorem selectivityBattery_finiteAperture_nonObject {a : ℝ} (ha : 0 < a) :
    ∃ Z : TemperedZeroConfig, aperturePositivity a Z ∧
      widthFunctor.obj (temperedConfigReceiver Z) = widthHalf ∧
      ¬ IsZeroWidthObject (temperedConfigReceiver Z) := by
  obtain ⟨Z, hw, hpos⟩ := exists_width_eq_half_aperturePositivity ha
  refine ⟨Z, hpos, Subtype.ext (show width Z = 1 / 2 from hw), ?_⟩
  rw [isZeroWidthObject_iff_widthVal_eq_zero]
  change ¬ width Z = 0
  rw [hw]
  norm_num

/-- **Selectivity Test 6 (Prime Jump-Rate Criticality and the `β² L³` Precision Law):**
1. *Prime jump-rate criticality:* for every `n ≥ 2`, `RiemannHypothesis` holds iff `vonMangoldtAtom n`
   is the least rate at shift `log n` for which the odd Markov form is nonnegative; no single prime-power
   jump rate can be lowered (`riemannHypothesis_iff_isLeast_primeRate`).
2. *Precision cost (`β² L³`):* on `ScaleDepthDatum`, excluding depth `β` at scale `L` via
   `weilFloorThreshold` requires precision budget `1 / (12 / (β ^ 2 * L ^ 3))` (`theDeficitBudgetLaw`). -/
theorem selectivityBattery_rate_and_precision :
    (∀ {n : ℕ}, 2 ≤ n →
      (RiemannHypothesis ↔
        IsLeast {c : ℝ | ∀ v : ℝ → ℝ, ContDiff ℝ 2 v → HasCompactSupport v → (∀ x, v (-x) = -v x) →
            0 ≤ markovEnergy (fun x => (phiDoobTest v x : ℂ)) +
              (c - vonMangoldtAtom n) * shiftJumpEnergy (Real.log n) v} (vonMangoldtAtom n))) ∧
    (∀ {A η : ℝ → ℝ}, ScaleMatched A η → ∀ {β : ℝ}, 0 ≤ β →
      ∀ {p₀ : ScaleDepthDatum}, adaptiveReading A η p₀ →
        ((∀ L : ℝ, 0 < L → η L ≤ β ^ 2 * L ^ 3) →
          Certifies sdDepth (adaptiveReading A η) p₀ β) ∧
        (∀ L β' : ℝ, 0 < L → 0 < β' → β' ≤ 1 / 2 → β < β' → weilFloorThreshold L β' ≤ η L →
          ¬ Certifies sdDepth (adaptiveReading A η) p₀ β)) := by
  refine ⟨fun hn => riemannHypothesis_iff_isLeast_primeRate hn, ?_⟩
  intro A η h β hβ p₀ hp₀
  exact ⟨(theDeficitBudgetLaw h hβ hp₀).2.1, (theDeficitBudgetLaw h hβ hp₀).2.2⟩

/-! ## §5. Master Synthesis: The Width Functor and the Selectivity Battery -/

/-- **Master Synthesis for Open Problem 11 (`theWidthFunctor_and_selectivityBattery_synthesis`):**
1. *The Width Functor (`widthFunctor : ReceiverObject ⥤ WidthLine`):* full, faithful, and
   isomorphism-reflecting functor from `ReceiverObject` to `WidthLine = [0, 1/2]` through which
   every graded admissibility predicate `R.admittedAt σ` (`σ ≥ 0`) factors;
2. *Isomorphism of the `ζ`-Receivers:* `spectralZeroReceiver`, `abscissaReceiver`,
   `moebiusDampingReceiver`, `liouvilleDampingReceiver`, `xiHalfPlaneReceiver`, and
   `suzukiFormationReceiver` all map to `⟨zetaZeroWidth, ...⟩` under `widthFunctor` and are
   canonically isomorphic in `ReceiverObject`;
3. *Selectivity Battery of Non-Objects:* `goldenDatum` refutes curve unitarity and section-cone
   Bézout despite Witt integrality, `shiftedPairVonMangoldt a` (`a ≠ 0`) refutes scale-window
   temperedness and inflates `frobeniusMass` despite preserving Dirichlet `h0`, `fermiFlipWeight ε`
   refutes `ReceiverBounded` despite sharing all Ramanujan amplitudes with `fermiWeight ε`,
   `deleteNode 2` and `deleteNode 4` refute node-set zero-width/positivity while `deleteNode 6` is
   free, and every bounded aperture `a > 0` admits a maximal-width non-object `widthHalf`. -/
theorem theWidthFunctor_and_selectivityBattery_synthesis :
    (∀ R₁ R₂ : ReceiverObject, Nonempty (R₁ ≅ R₂) ↔ widthFunctor.obj R₁ = widthFunctor.obj R₂) ∧
    (widthFunctor.obj abscissaReceiver = widthFunctor.obj spectralZeroReceiver ∧
      widthFunctor.obj moebiusDampingReceiver = widthFunctor.obj spectralZeroReceiver ∧
      widthFunctor.obj liouvilleDampingReceiver = widthFunctor.obj spectralZeroReceiver ∧
      widthFunctor.obj xiHalfPlaneReceiver = widthFunctor.obj spectralZeroReceiver ∧
      widthFunctor.obj suzukiFormationReceiver = widthFunctor.obj spectralZeroReceiver) ∧
    (∀ {σ : ℝ}, 0 ≤ σ → FactorsThroughWidthFunctor (fun R : ReceiverObject => R.admittedAt σ)) ∧
    (¬ (∀ i, ‖goldenDatum.β i‖ = 1) ∧
      ¬ (goldenDatum.windowSurface ({0, 1} : Finset ℕ)).BezoutAxiom
          (sectionEffectivityCone (goldenDatum.windowSurface ({0, 1} : Finset ℕ)))) ∧
    (∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
      ReceiverBounded (fermiWeight ε) ∧ ¬ ReceiverBounded (fermiFlipWeight ε)) ∧
    (IsZeroWidthObject (nodeSetReceiver {n : ℕ | IsPrimePow n}) ∧
      ¬ IsZeroWidthObject (nodeSetReceiver (deleteNode 2 {n : ℕ | IsPrimePow n}))) ∧
    (∀ {a : ℝ}, 0 < a → ∃ Z : TemperedZeroConfig, aperturePositivity a Z ∧
      ¬ IsZeroWidthObject (temperedConfigReceiver Z)) := by
  refine ⟨fun R₁ R₂ => (nonempty_iso_iff_widthVal_eq R₁ R₂).trans
      ⟨fun h => widthFunctor_obj_ext h, fun h => by have := congrArg Subtype.val h; exact this⟩,
    widthFunctor_obj_zetaReceivers_eq,
    fun hσ => admittedAt_factorsThrough_widthFunctor hσ,
    ⟨selectivityBattery_goldenDatum_nonObject.2.2.2.1,
     selectivityBattery_goldenDatum_nonObject.2.2.2.2⟩,
    fun hε hε2 => ⟨(selectivityBattery_parityTwins_nonObject.1 hε hε2).2.1,
      (selectivityBattery_parityTwins_nonObject.1 hε hε2).2.2⟩,
    ⟨selectivityBattery_nodes_nonObject.1, selectivityBattery_nodes_nonObject.2.2.1⟩,
    fun ha => ?_⟩
  obtain ⟨Z, hpos, _, hnot⟩ := selectivityBattery_finiteAperture_nonObject ha
  exact ⟨Z, hpos, hnot⟩

end

end GaloisForLFunctions.ArithmeticOrientationTheory
