import GaloisForLFunctions.HTGeometry.GammaPhaseCompletion
import GaloisForLFunctions.HTGeometry.MeromorphicGammaReflection

/-!
# Arbitrary-orientation Gamma alien charge

Euler reflection turns every negative real affine Gamma slope into a nonzero differentially
algebraic sine gauge times an inverse positive-slope factor.  This module records the exact
coefficient normalization and joins that reflection step to the arbitrary-positive-scale
finite-shift/alien-charge classifier from `GammaPhaseCompletion`.

The analytic parent inputs remain explicit: the ADH one-shift dichotomy, the scaled-Borel
zero/nonzero charge selector, and reflection invariance enter as hypotheses.  The new theorem is
the unconditional assembly showing that no additional carrier appears when arbitrary orientations
and arbitrary rational commensurability classes occur simultaneously.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

noncomputable section

/-- One affine Gamma factor `Gamma(slope * z + offset)^multiplicity` with nonzero real slope. -/
structure OrientedAffineGammaFactor where
  slope : ℝ
  offset : ℂ
  multiplicity : ℤ
  slope_ne_zero : slope ≠ 0

/-- Reflection-normalized affine Gamma factor with strictly positive scale. -/
structure PositiveAffineGammaFactor where
  scale : ℝ
  offset : ℂ
  multiplicity : ℤ
  scale_pos : 0 < scale

/-- Normalize orientation by Euler reflection.  A negative-slope factor
`Gamma(lambda*z+mu)^m` contributes, modulo a nonzero DA sine gauge, the positive-slope factor
`Gamma((-lambda)*z+(1-mu))^(-m)`. -/
def OrientedAffineGammaFactor.positiveNormalization
    (f : OrientedAffineGammaFactor) : PositiveAffineGammaFactor where
  scale := |f.slope|
  offset := if 0 < f.slope then f.offset else 1 - f.offset
  multiplicity := if 0 < f.slope then f.multiplicity else -f.multiplicity
  scale_pos := abs_pos.mpr f.slope_ne_zero

@[simp] theorem OrientedAffineGammaFactor.positiveNormalization_scale
    (f : OrientedAffineGammaFactor) :
    f.positiveNormalization.scale = |f.slope| := rfl

@[simp] theorem OrientedAffineGammaFactor.positiveNormalization_offset_of_pos
    (f : OrientedAffineGammaFactor) (h : 0 < f.slope) :
    f.positiveNormalization.offset = f.offset := by
  simp [OrientedAffineGammaFactor.positiveNormalization, h]

@[simp] theorem OrientedAffineGammaFactor.positiveNormalization_multiplicity_of_pos
    (f : OrientedAffineGammaFactor) (h : 0 < f.slope) :
    f.positiveNormalization.multiplicity = f.multiplicity := by
  simp [OrientedAffineGammaFactor.positiveNormalization, h]

@[simp] theorem OrientedAffineGammaFactor.positiveNormalization_offset_of_neg
    (f : OrientedAffineGammaFactor) (h : f.slope < 0) :
    f.positiveNormalization.offset = 1 - f.offset := by
  simp [OrientedAffineGammaFactor.positiveNormalization, not_lt_of_ge h.le]

@[simp] theorem OrientedAffineGammaFactor.positiveNormalization_multiplicity_of_neg
    (f : OrientedAffineGammaFactor) (h : f.slope < 0) :
    f.positiveNormalization.multiplicity = -f.multiplicity := by
  simp [OrientedAffineGammaFactor.positiveNormalization, not_lt_of_ge h.le]

/-- Scaled alien charge at the nonzero Borel frequency `t`.  The summand is present exactly when
`t` lies on the factor's nonzero scaled integer lattice. -/
def scaledGammaAlienChargeAt {d : ℕ}
    (a : Fin d → PositiveAffineGammaFactor) (t : ℝ) : ℂ := by
  classical
  exact
    ∑ i, if ∃ k : ℤ, k ≠ 0 ∧ t = (k : ℝ) * (a i).scale then
      ((a i).multiplicity : ℂ) * ((a i).scale : ℂ) *
        Complex.exp
          (-2 * (Real.pi : ℂ) * Complex.I *
            ((t / (a i).scale : ℝ) : ℂ) * (a i).offset)
    else 0

/-- Vanishing of the complete positive-scale alien character. -/
def ScaledGammaAlienChargeZero {d : ℕ}
    (a : Fin d → PositiveAffineGammaFactor) : Prop :=
  ∀ t : ℝ, t ≠ 0 → scaledGammaAlienChargeAt a t = 0

/-- The oriented alien charge is the positive-scale charge after coefficient reflection. -/
def OrientedGammaAlienChargeZero {d : ℕ}
    (a : Fin d → OrientedAffineGammaFactor) : Prop :=
  ScaledGammaAlienChargeZero (fun i => (a i).positiveNormalization)

/-- **Arbitrary-orientation, arbitrary-scale carrier law.**  Suppose the normalized positive-scale
carrier is governed by a finite word of shift differences, the one-shift rational/HT dichotomy,
and an exact scaled-alien-charge rationality selector.  If Euler reflection preserves rationality
and hypertranscendence between the oriented and normalized carriers, then zero oriented charge
forces the rational carrier, nonzero oriented charge forces the HT carrier, and these are the only
two possibilities.

This simultaneously subsumes the positive arbitrary-scale classifier and the arbitrary-orientation
common-scale classifier. -/
theorem orientedGammaAlienCharge_shiftWord_classification
    {X : Type*} {d n : ℕ}
    (orientedCarrier : (Fin d → OrientedAffineGammaFactor) → X)
    (positiveCarrier : (Fin d → PositiveAffineGammaFactor) → X)
    (Delta : Fin n → X → X) (Rational Hypertranscendental : X → Prop)
    (word : List (Fin n)) (a : Fin d → OrientedAffineGammaFactor)
    (reflection_rational :
      Rational (orientedCarrier a) ↔
        Rational (positiveCarrier (fun i => (a i).positiveNormalization)))
    (reflection_hypertranscendental :
      Hypertranscendental (orientedCarrier a) ↔
        Hypertranscendental
          (positiveCarrier (fun i => (a i).positiveNormalization)))
    (oneShiftDichotomy : ∀ (i : Fin n) (g : X),
      Rational (Delta i g) → Rational g ∨ Hypertranscendental g)
    (htDown : ∀ (i : Fin n) (g : X),
      Hypertranscendental (Delta i g) → Hypertranscendental g)
    (word_rational : Rational
      (_root_.HTGeometry.shiftWord Delta word
        (positiveCarrier (fun i => (a i).positiveNormalization))))
    (zeroCharge_rational : OrientedGammaAlienChargeZero a →
      Rational (positiveCarrier (fun i => (a i).positiveNormalization)))
    (nonzeroCharge_excludesRational : ¬ OrientedGammaAlienChargeZero a →
      ¬ Rational (positiveCarrier (fun i => (a i).positiveNormalization))) :
    (OrientedGammaAlienChargeZero a → Rational (orientedCarrier a)) ∧
      (¬ OrientedGammaAlienChargeZero a →
        Hypertranscendental (orientedCarrier a)) ∧
      (Rational (orientedCarrier a) ∨
        Hypertranscendental (orientedCarrier a)) := by
  have hpositive := alienCharge_shiftWord_classification
    Delta Rational Hypertranscendental word
    (positiveCarrier (fun i => (a i).positiveNormalization))
    oneShiftDichotomy htDown word_rational
    (OrientedGammaAlienChargeZero a)
    zeroCharge_rational nonzeroCharge_excludesRational
  refine ⟨fun hzero => reflection_rational.mpr (hpositive.1 hzero), ?_, ?_⟩
  · intro hnonzero
    exact reflection_hypertranscendental.mpr (hpositive.2.1 hnonzero)
  · rcases hpositive.2.2 with hrational | hht
    · exact Or.inl (reflection_rational.mpr hrational)
    · exact Or.inr (reflection_hypertranscendental.mpr hht)

/-- Exact iff form when rationality and hypertranscendence are disjoint, as they are for the
Gamma differential-algebraic application. -/
theorem orientedGammaAlienCharge_shiftWord_exactClassification
    {X : Type*} {d n : ℕ}
    (orientedCarrier : (Fin d → OrientedAffineGammaFactor) → X)
    (positiveCarrier : (Fin d → PositiveAffineGammaFactor) → X)
    (Delta : Fin n → X → X) (Rational Hypertranscendental : X → Prop)
    (word : List (Fin n)) (a : Fin d → OrientedAffineGammaFactor)
    (reflection_rational :
      Rational (orientedCarrier a) ↔
        Rational (positiveCarrier (fun i => (a i).positiveNormalization)))
    (reflection_hypertranscendental :
      Hypertranscendental (orientedCarrier a) ↔
        Hypertranscendental
          (positiveCarrier (fun i => (a i).positiveNormalization)))
    (oneShiftDichotomy : ∀ (i : Fin n) (g : X),
      Rational (Delta i g) → Rational g ∨ Hypertranscendental g)
    (htDown : ∀ (i : Fin n) (g : X),
      Hypertranscendental (Delta i g) → Hypertranscendental g)
    (word_rational : Rational
      (_root_.HTGeometry.shiftWord Delta word
        (positiveCarrier (fun i => (a i).positiveNormalization))))
    (zeroCharge_rational : OrientedGammaAlienChargeZero a →
      Rational (positiveCarrier (fun i => (a i).positiveNormalization)))
    (nonzeroCharge_excludesRational : ¬ OrientedGammaAlienChargeZero a →
      ¬ Rational (positiveCarrier (fun i => (a i).positiveNormalization)))
    (exclusive : ∀ g : X, Rational g → ¬ Hypertranscendental g) :
    (Rational (orientedCarrier a) ↔ OrientedGammaAlienChargeZero a) ∧
      (Hypertranscendental (orientedCarrier a) ↔
        ¬ OrientedGammaAlienChargeZero a) := by
  have hclassification := orientedGammaAlienCharge_shiftWord_classification
    orientedCarrier positiveCarrier Delta Rational Hypertranscendental word a
    reflection_rational reflection_hypertranscendental oneShiftDichotomy htDown
    word_rational zeroCharge_rational nonzeroCharge_excludesRational
  refine ⟨?_, ?_⟩
  · constructor
    · intro hrational
      by_contra hnonzero
      exact exclusive _ hrational (hclassification.2.1 hnonzero)
    · exact hclassification.1
  · constructor
    · intro hht hzero
      exact exclusive _ (hclassification.1 hzero) hht
    · exact hclassification.2.1

end

end GaloisForLFunctions.HTGeometry
