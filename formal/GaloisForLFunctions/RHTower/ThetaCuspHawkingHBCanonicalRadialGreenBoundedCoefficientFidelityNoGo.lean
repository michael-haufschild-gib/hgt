import GaloisForLFunctions.RHTower.ThetaCuspHawkingSchwarzOddDiagonalCausalPropagatorObstruction
import GaloisForLFunctions.RHTower.XiOrderedPositiveRVMRelocation
import GaloisForLFunctions.RHTower.XiOrderedZeroCopyEnumeration
import GaloisForLFunctions.HTGeometry.DiagonalEllTwoIndexed

/-!
# Bounded coefficient-fidelity no-go for the canonical radial HB Green jump

The imaginary part of the canonical BM radial Green-jump coefficient at an Xi copy is the
negative Xi height. Positive Xi heights are unbounded. Hence the canonical coefficients are
unbounded, at every fixed overtone.

This rules out more than a bounded diagonal multiplier. If an arbitrary bounded operator, with
unrestricted cross-fibre mixing, retained every canonical coefficient as a diagonal matrix
element on the Xi-copy coordinate vectors, Cauchy--Schwarz would bound those coefficients by its
operator norm. The unbounded height sequence contradicts that bound.

Thus the bounded-noncompact HB survivor cannot retain the full canonical radial Green jump as
coefficient-faithful diagonal data. An exact realization must be genuinely unbounded (with a
specified domain/topology), or change the coefficient-fidelity requirement before projection.

`[NEW] [HB] [CAUSAL GREEN JUMP] [BOUNDED-OPERATOR NO-GO] [LEAN-PROVED]`
-/

open Complex Set Filter
open scoped InnerProductSpace

namespace RHTower

noncomputable section

/-- Square-summable packets indexed by the multiplicity-aware Xi divisor copies. -/
abbrev HBXiPeierlsHilbertPacket := HTGeometry.IndexedEllTwo XiZeroCopy

/-- A bounded response is coefficient-faithful when every coordinate diagonal matrix element is
the canonical BM radial Green-jump coefficient. No diagonality or restriction on cross-fibre
matrix elements is imposed on the operator. -/
def HBXiPeierlsBoundedRadialCoefficientFaithful
    (n : ℕ) (K : HBXiPeierlsHilbertPacket →L[ℂ] HBXiPeierlsHilbertPacket) : Prop :=
  ∀ q : XiZeroCopy,
    ⟪HTGeometry.ellTwoCoordinateBasis XiZeroCopy q,
      K (HTGeometry.ellTwoCoordinateBasis XiZeroCopy q)⟫_ℂ =
        hbXiPeierlsRadialWeight n q

/-- At every fixed overtone, canonical radial Green-jump coefficients exceed every norm bound. -/
theorem exists_hbXiPeierlsRadialWeight_norm_gt
    (n : ℕ) (C : ℝ) :
    ∃ q : XiZeroCopy, C < ‖hbXiPeierlsRadialWeight n q‖ := by
  have hevent : ∀ᶠ k : ℕ in atTop,
      C < xiOrderedPositiveOrdinate k :=
    tendsto_xiOrderedPositiveOrdinate_atTop.eventually
      (eventually_gt_atTop C)
  obtain ⟨k, hk⟩ := hevent.exists
  refine ⟨xiOrderedPositiveZeroCopy k, ?_⟩
  calc
    C < xiOrderedPositiveOrdinate k := hk
    _ = |(hbXiPeierlsRadialWeight n
        (xiOrderedPositiveZeroCopy k)).im| := by
      rw [hbXiPeierlsRadialWeight_im,
        xiOrderedPositiveZeroCopy_im_eq]
      rw [abs_neg, abs_of_pos (xiOrderedPositiveOrdinate_pos k)]
    _ ≤ ‖hbXiPeierlsRadialWeight n
        (xiOrderedPositiveZeroCopy k)‖ := Complex.abs_im_le_norm _

/-- No bounded operator can retain every canonical radial coefficient as a coordinate diagonal
matrix element. Arbitrary off-diagonal mixing does not weaken the obstruction. -/
theorem not_hbXiPeierlsBoundedRadialCoefficientFaithful
    (n : ℕ) (K : HBXiPeierlsHilbertPacket →L[ℂ] HBXiPeierlsHilbertPacket) :
    ¬ HBXiPeierlsBoundedRadialCoefficientFaithful n K := by
  intro hK
  obtain ⟨q, hq⟩ := exists_hbXiPeierlsRadialWeight_norm_gt n ‖K‖
  have hone :
      ‖(HTGeometry.ellTwoCoordinateBasis XiZeroCopy q :
        HBXiPeierlsHilbertPacket)‖ = 1 := by
    rw [HTGeometry.ellTwoCoordinateBasis_apply,
      lp.norm_single (E := fun _ : XiZeroCopy => ℂ)
        (p := 2) (by norm_num) q (1 : ℂ)]
    simp
  have hbound :
      ‖(⟪HTGeometry.ellTwoCoordinateBasis XiZeroCopy q,
        K (HTGeometry.ellTwoCoordinateBasis XiZeroCopy q)⟫_ℂ : ℂ)‖ ≤ ‖K‖ := by
    calc
      ‖(⟪HTGeometry.ellTwoCoordinateBasis XiZeroCopy q,
          K (HTGeometry.ellTwoCoordinateBasis XiZeroCopy q)⟫_ℂ : ℂ)‖
          ≤ ‖(HTGeometry.ellTwoCoordinateBasis XiZeroCopy q :
              HBXiPeierlsHilbertPacket)‖ *
            ‖K (HTGeometry.ellTwoCoordinateBasis XiZeroCopy q)‖ :=
        norm_inner_le_norm _ _
      _ ≤ ‖(HTGeometry.ellTwoCoordinateBasis XiZeroCopy q :
              HBXiPeierlsHilbertPacket)‖ *
            (‖K‖ * ‖(HTGeometry.ellTwoCoordinateBasis XiZeroCopy q :
              HBXiPeierlsHilbertPacket)‖) := by
        gcongr
        exact K.le_opNorm _
      _ = ‖K‖ := by rw [hone]; ring
  rw [hK q] at hbound
  exact (not_lt_of_ge hbound) hq

/-- Closed route-class certificate: bounded exact coefficient-fidelity for the canonical radial HB
Green jump is impossible at every overtone. -/
def D4HBCanonicalRadialGreenBoundedCoefficientFidelityRouteKilled : Prop :=
  ∀ n : ℕ, ∀ K : HBXiPeierlsHilbertPacket →L[ℂ] HBXiPeierlsHilbertPacket,
    ¬ HBXiPeierlsBoundedRadialCoefficientFaithful n K

/-- Premise-free proof that the bounded coefficient-faithful canonical radial HB route is dead. -/
theorem d4HBCanonicalRadialGreenBoundedCoefficientFidelityRouteKilled :
    D4HBCanonicalRadialGreenBoundedCoefficientFidelityRouteKilled := by
  intro n K
  exact not_hbXiPeierlsBoundedRadialCoefficientFaithful n K

end

end RHTower
