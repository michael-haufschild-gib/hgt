import GaloisForLFunctions.HTGeometry.StokesGlobalPuiseuxWittLaw
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicResidualNegativeOrientation
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicRawMagnitudeOvershoot

/-!
# Cubic wall--Xi Malgrange microlocal Witt-signature rigidity

The first odd prime/Gamma wall--Xi Malgrange residual is strictly negative.  The global
coefficient-generated Stokes--microlocal Witt law has positive terminal and threshold channels
plus one Rees-invariant physical-rank square.  Combining these statements localizes every possible
coefficient-generated realization of the cubic residual to that sole global channel.

More precisely, any landing throughout the nonnegative multi-Rees cone has nonzero common physical
rank, a strictly negative global rank coefficient, rank debt strictly exceeding all positive
microlocal channels, exact negative inertia one, and zero radical.  Thus local microstalk channels
and their Rees deformations cannot carry the missing cubic anomaly.

Conditionally, if one fixed charge lands at both complete threshold contraction and unit Rees scale,
positivity forces every threshold charge to vanish and the landing extends to the entire real
multi-Rees parameter space.  The follow-up diagonal-Rees transversality module uses pendant-cut
faithfulness to prove this fiber empty, so its raw-Euler terminal-energy consequences are vacuous.

This is a classification of every landing charge, not an existence claim for such a charge and not
an RH conclusion.
-/

open GaloisForLFunctions
open GaloisForLFunctions.IrregularStokes
open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

namespace RHTower

noncomputable section

/-- Coefficient-generated global irregular-Stokes charges whose Rees-deformed Witt value is the
canonical cold cubic wall--Xi Malgrange residual. -/
def routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    (genus : ℕ) (d : LocalData p n m K N) (parameter : ReesParameter d) :=
  {x : compatibleCharges d //
    globalReesWittForm genus d parameter x =
      normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4}

theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_value_neg
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber genus d parameter) :
    globalReesWittForm genus d parameter x.1 < 0 := by
  rw [x.2]
  exact normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg

theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_charge_ne_zero
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber genus d parameter) :
    x.1 ≠ 0 := by
  intro hx
  have hneg :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_value_neg x
  have hzero : globalReesWittForm genus d parameter x.1 = 0 := by
    simp [hx]
  rw [hzero] at hneg
  exact (lt_irrefl 0) hneg

/-- No rank-zero local microlocal/Rees channel can carry the negative cubic Xi anomaly. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_commonRank_ne_zero
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber genus d parameter) :
    commonRankLinear d x.1 ≠ 0 := by
  intro hrank
  have hpos := globalReesWittForm_pos_of_commonRank_eq_zero
    genus d parameter hparameter hrank
      (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_charge_ne_zero x)
  have hneg :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_value_neg x
  linarith

/-- Any coefficient-generated irregular-Stokes landing forces the sole global physical-rank
coefficient into the Lorentz chamber. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rankCoefficient_neg
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber genus d parameter) :
    globalRankCoefficient genus d < 0 := by
  by_contra hcoeff
  push Not at hcoeff
  have hpositive := globalReesPositiveForm_nonneg d parameter hparameter x.1
  have hdecomp := globalReesWittForm_eq_positive_add_oneRank
    genus d parameter x.1
  have hnonneg : 0 ≤ globalReesWittForm genus d parameter x.1 := by
    rw [hdecomp]
    exact add_nonneg hpositive (mul_nonneg hcoeff (sq_nonneg _))
  have hneg :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_value_neg x
  linarith

/-- The unique global negative rank square strictly dominates all positive terminal and threshold
microlocal channels at every cubic Xi landing. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rankDebt_gt_positive
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber genus d parameter) :
    globalReesPositiveForm d parameter x.1 <
      -globalRankCoefficient genus d * commonRankLinear d x.1 ^ 2 := by
  have hneg :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_value_neg x
  rw [globalReesWittForm_eq_positive_add_oneRank] at hneg
  linarith

/-- A cubic Xi landing saturates the universal Krein--Langer bound: negative inertia is exactly
one, throughout the nonnegative multi-Rees cone. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sigNeg_eq_one
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber genus d parameter) :
    sigNeg (globalReesWittForm genus d parameter) = 1 := by
  have hpos : 0 < sigNeg (globalReesWittForm genus d parameter) :=
    GaloisForLFunctions.IrregularStokes.sigNeg_pos_of_exists_negativeVector
      (globalReesWittForm genus d parameter)
      (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_charge_ne_zero x)
      (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_value_neg x)
  have hle := globalReesWittForm_sigNeg_le_one genus d parameter hparameter
  omega

/-- The same landing eliminates the alternative null channel: the global Stokes form is
nondegenerate. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_radical_finrank_eq_zero
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber genus d parameter) :
    Module.finrank ℝ (globalReesWittForm genus d parameter).radical = 0 := by
  have hsum := globalReesWittForm_sigNeg_add_radical_finrank_le_one
    genus d parameter hparameter
  have hsig :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sigNeg_eq_one
      hparameter x
  omega

/-- Signature-rigidity capstone for every coefficient-generated irregular microlocal landing of
the first odd wall--Xi Malgrange anomaly. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rigidity
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber genus d parameter) :
    commonRankLinear d x.1 ≠ 0 ∧
      globalRankCoefficient genus d < 0 ∧
      globalReesPositiveForm d parameter x.1 <
        -globalRankCoefficient genus d * commonRankLinear d x.1 ^ 2 ∧
      sigNeg (globalReesWittForm genus d parameter) = 1 ∧
      Module.finrank ℝ (globalReesWittForm genus d parameter).radical = 0 := by
  exact ⟨
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_commonRank_ne_zero
      hparameter x,
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rankCoefficient_neg
      hparameter x,
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rankDebt_gt_positive x,
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sigNeg_eq_one
      hparameter x,
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_radical_finrank_eq_zero
      hparameter x⟩

/-- At every cubic Xi landing, total coefficient-generated root defect strictly exceeds the
topological fusion coefficient.  This is the exact curvature--irregularity cost of entering the
global Lorentz channel. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_fusion_lt_rootDefects
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber genus d parameter) :
    fusionCoefficient genus (p + 1) <
      ∑ a, ((d a).toOrbitCoareaDatum.cuts.root - 1) := by
  have hcoeff :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_rankCoefficient_neg
      hparameter x
  rw [globalRankCoefficient] at hcoeff
  linarith

/-- A one-puncture sphere can carry the cubic Xi anomaly only at genuinely irregular normalized
Puiseux root slope strictly above one. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sphereOnePuncture_root_gt_one
    {n m K N : Fin 1 → ℕ}
    {d : LocalData 0 n m K N} {parameter : ReesParameter d}
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber 0 d parameter) :
    1 < (d 0).toOrbitCoareaDatum.cuts.root := by
  have hroot :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_fusion_lt_rootDefects
      hparameter x
  rw [PuiseuxOrbitCoareaDatum.toOrbit_root]
  simpa [fusionCoefficient] using hroot

/-- Coefficient-level version: for the unique marked point on the sphere, the largest declared
Puiseux numerator plus one must exceed the common cover degree. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sphereOnePuncture_slope_gt_one
    {n m K N : Fin 1 → ℕ}
    {d : LocalData 0 n m K N} {parameter : ReesParameter d}
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber 0 d parameter) :
    1 < (((K 0 + 1 : ℕ) : ℝ) / N 0) := by
  simpa only [PuiseuxOrbitCoareaDatum.toOrbit_root] using
    routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sphereOnePuncture_root_gt_one
      hparameter x

/-- Tame and normalized slope-at-most-one one-puncture sphere models have empty cubic Xi landing
fiber throughout the nonnegative multi-Rees cone. -/
theorem not_nonempty_routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sphereOnePuncture_of_slope_le_one
    {n m K N : Fin 1 → ℕ}
    {d : LocalData 0 n m K N} {parameter : ReesParameter d}
    (hparameter : ∀ a edge, 0 ≤ parameter a edge)
    (hslope : (((K 0 + 1 : ℕ) : ℝ) / N 0) ≤ 1) :
    ¬ Nonempty
      (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber 0 d parameter) := by
  rintro ⟨x⟩
  exact (not_lt_of_ge hslope)
    (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_sphereOnePuncture_slope_gt_one
      hparameter x)

/-- Cubic landing charges for which the unique global physical-rank debt is supplied at identity
scale by the canonical pre-Xi Euler/Gamma--Wold defect.  Both equations are part of the variable
domain; no landing or source-to-Stokes incidence is assumed to exist. -/
def routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    (genus : ℕ) (d : LocalData p n m K N) (parameter : ReesParameter d) :=
  {x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber genus d parameter //
    -globalRankCoefficient genus d * commonRankLinear d x.1 ^ 2 =
      ∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k}

/-- Exact cancellation identity: positive microlocal channels equal raw Euler debt plus the
negative Xi cubic residual. -/
theorem routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_eq
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (x : routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber
      genus d parameter) :
    globalReesPositiveForm d parameter x.1.1 =
      (∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k) +
        (normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4) := by
  have hdecomp := globalReesWittForm_eq_positive_add_oneRank
    genus d parameter x.1.1
  have hlanding := x.1.2
  have hdebt := x.2
  linarith

/-- More than `1999/2000` of the raw source debt must be cancelled by positive terminal and
threshold microlocal channels. -/
theorem routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_gt_fraction
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (x : routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber
      genus d parameter) :
    (1999 / 2000 : ℝ) *
        (∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k) <
      globalReesPositiveForm d parameter x.1.1 := by
  rw [routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_eq x]
  have hgap := twoThousand_mul_neg_xiCubicMalgrangeMagnitude_lt_rawSource
  nlinarith

/-- Cancellation remains strictly incomplete: the surviving negative Xi residual is exactly the
gap below the raw rank debt. -/
theorem routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_lt_rawDebt
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (x : routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber
      genus d parameter) :
    globalReesPositiveForm d parameter x.1.1 <
      ∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k := by
  rw [routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_eq x]
  linarith [normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg]

/-- The positive microlocal cancellation is more than `1999` times the magnitude of the Xi cubic
target itself. -/
theorem routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_gt_target
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (x : routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber
      genus d parameter) :
    1999 * (-(normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 0 ^ 3 / 4)) <
      globalReesPositiveForm d parameter x.1.1 := by
  rw [routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_eq x]
  have hgap := twoThousand_mul_neg_xiCubicMalgrangeMagnitude_lt_rawSource
  nlinarith

/-- Complete raw-Euler/global-Lorentz cancellation aperture. -/
theorem routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_cancellation
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N} {parameter : ReesParameter d}
    (x : routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber
      genus d parameter) :
    globalReesPositiveForm d parameter x.1.1 =
        (∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k) +
          (normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4) ∧
      (1999 / 2000 : ℝ) *
          (∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k) <
        globalReesPositiveForm d parameter x.1.1 ∧
      globalReesPositiveForm d parameter x.1.1 <
        ∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k ∧
      1999 * (-(normalizedPrimeArchMoment 2 -
          normalizedPrimeArchMoment 0 ^ 3 / 4)) <
        globalReesPositiveForm d parameter x.1.1 := by
  exact ⟨
    routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_eq x,
    routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_gt_fraction x,
    routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_lt_rawDebt x,
    routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_gt_target x⟩

/-! ## Conditional Rees-rigid source incidence

The follow-up module `RoutePPrimitiveGammaJuliaStokesCubicDiagonalReesTransversality` proves both
Rees-rigid fibers below empty by using the pendant cuts not yet invoked in this section.
-/

/-- Cubic Xi landing charges that survive both complete contraction and unit specialization of
every irregular threshold channel.  This is a variable-domain condition, not an existence claim. -/
def routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    (genus : ℕ) (d : LocalData p n m K N) :=
  {x : compatibleCharges d //
    globalReesWittForm genus d (fun _ _ => 0) x =
        normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4 ∧
      globalReesWittForm genus d (fun _ _ => 1) x =
        normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4}

/-- Equality of the contracted and unit Xi landings annihilates total threshold coarea. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_total_blockEnergy_eq_zero
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber genus d) :
    (∑ a, (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a)) = 0 := by
  have hzero := x.2.1
  have hone := x.2.2
  have hdecompZero := globalReesWittForm_eq_positive_add_oneRank
    genus d (fun _ _ => 0) x.1
  have hdecompOne := globalReesWittForm_eq_positive_add_oneRank
    genus d (fun _ _ => 1) x.1
  have hpositive :
      globalReesPositiveForm d (fun _ _ => 1) x.1 =
        globalReesPositiveForm d (fun _ _ => 0) x.1 := by
    linarith
  simpa [globalReesPositiveForm, localReesPositiveForm_apply,
    OrbitCoareaDatum.reesBlockEnergy_one,
    OrbitCoareaDatum.reesBlockEnergy, OrbitCoareaDatum.blockEnergy,
    OrbitCoareaDatum.cutCharge, Finset.sum_add_distrib] using hpositive

/-- Every marked-point threshold block vanishes separately. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_local_blockEnergy_eq_zero
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber genus d)
    (a : Fin (p + 1)) :
    (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) = 0 := by
  have htotal :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_total_blockEnergy_eq_zero x
  have hnonneg : 0 ≤ (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) :=
    (d a).toOrbitCoareaDatum.blockEnergy_nonneg (x.1.1 a)
  apply le_antisymm
  · by_contra hnotle
    have hpos : 0 < (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) :=
      lt_of_not_ge hnotle
    have hsumpos :
        0 < ∑ b, (d b).toOrbitCoareaDatum.blockEnergy (x.1.1 b) := by
      apply Finset.sum_pos'
      · intro b _
        exact (d b).toOrbitCoareaDatum.blockEnergy_nonneg (x.1.1 b)
      · exact ⟨a, Finset.mem_univ _, hpos⟩
    linarith
  · exact hnonneg

/-- Every individual irregular threshold charge vanishes. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_cutCharge_eq_zero
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber genus d)
    (a : Fin (p + 1)) (edge : Fin (d a).edgeCount) :
    (d a).toOrbitCoareaDatum.cutCharge (x.1.1 a) edge = 0 := by
  have hblock :=
    routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_local_blockEnergy_eq_zero
      x a
  by_contra hcut
  have hterm :
      0 < (d a).toOrbitCoareaDatum.cuts.length edge *
        (d a).toOrbitCoareaDatum.cutCharge (x.1.1 a) edge ^ 2 :=
    mul_pos ((d a).toOrbitCoareaDatum.cuts.length_pos edge)
      (sq_pos_of_ne_zero hcut)
  have hblockpos : 0 < (d a).toOrbitCoareaDatum.blockEnergy (x.1.1 a) := by
    simp only [OrbitCoareaDatum.blockEnergy]
    apply Finset.sum_pos'
    · intro other _
      exact mul_nonneg
        ((d a).toOrbitCoareaDatum.cuts.length_pos other).le
        (sq_nonneg _)
    · refine ⟨edge, Finset.mem_univ edge, ?_⟩
      simpa [OrbitCoareaDatum.cutCharge] using hterm
  linarith

/-- Threshold neutrality makes the positive part independent of every Rees parameter. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_positive_parameter_eq_zero
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber genus d)
    (parameter : ReesParameter d) :
    globalReesPositiveForm d parameter x.1 =
      globalReesPositiveForm d (fun _ _ => 0) x.1 := by
  have hcut : ∀ a edge,
      (d a).toOrbitCoareaDatum.cutCharge (x.1.1 a) edge = 0 :=
    fun a edge =>
      routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_cutCharge_eq_zero
        x a edge
  have hRees : ∀ a (q : Fin (d a).edgeCount → ℝ),
      (d a).toOrbitCoareaDatum.reesBlockEnergy q (x.1.1 a) = 0 := by
    intro a q
    rw [OrbitCoareaDatum.reesBlockEnergy]
    apply Finset.sum_eq_zero
    intro edge _
    rw [hcut a edge]
    ring
  rw [globalReesPositiveForm, globalReesPositiveForm]
  simp only [QuadraticMap.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  simp only [QuadraticMap.comp_apply, localProjection_apply]
  rw [localReesPositiveForm_apply, localReesPositiveForm_apply]
  rw [hRees a (parameter a), hRees a (fun _ => 0)]

/-- Two Rees specializations suffice: the same charge lands at the Xi cubic residual for every
real multi-Rees parameter, not merely the nonnegative cone. -/
theorem routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_landing_all_parameters
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber genus d)
    (parameter : ReesParameter d) :
    globalReesWittForm genus d parameter x.1 =
      normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4 := by
  calc
    globalReesWittForm genus d parameter x.1 =
        globalReesWittForm genus d (fun _ _ => 0) x.1 := by
      rw [globalReesWittForm_eq_positive_add_oneRank,
        globalReesWittForm_eq_positive_add_oneRank,
        routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_positive_parameter_eq_zero
          x parameter]
    _ = normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 0 ^ 3 / 4 := x.2.1

/-- Rees-rigid cubic Xi landings whose physical-rank debt is the canonical raw Euler/Gamma--Wold
defect at identity scale. -/
def routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    (genus : ℕ) (d : LocalData p n m K N) :=
  {x : routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber genus d //
    -globalRankCoefficient genus d * commonRankLinear d x.1 ^ 2 =
      ∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k}

/-- With all threshold channels annihilated, terminal orbit energy alone obeys the exact raw-source
cancellation identity. -/
theorem routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_eq
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber genus d) :
    (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x.1.1.1 a)) =
      (∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k) +
        (normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4) := by
  let y : routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber
      genus d (fun _ _ => 0) := ⟨⟨x.1.1, x.1.2.1⟩, x.2⟩
  have hpositive :=
    routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtLandingFiber_positive_eq y
  simpa [globalReesPositiveForm, localReesPositiveForm_apply,
    OrbitCoareaDatum.reesBlockEnergy, Finset.sum_add_distrib] using hpositive

/-- Terminal orbit energy must cancel more than `1999/2000` of raw source debt. -/
theorem routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_gt_fraction
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber genus d) :
    (1999 / 2000 : ℝ) *
        (∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k) <
      ∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x.1.1.1 a) := by
  rw [routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_eq x]
  have hgap := twoThousand_mul_neg_xiCubicMalgrangeMagnitude_lt_rawSource
  nlinarith

/-- Terminal cancellation is strict: negative Xi cubic residual remains as exact gap. -/
theorem routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_lt_rawDebt
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber genus d) :
    (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x.1.1.1 a)) <
      ∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k := by
  rw [routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_eq x]
  linarith [normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg]

/-- Terminal orbit energy exceeds `1999` times magnitude of the Xi cubic target. -/
theorem routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_gt_target
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber genus d) :
    1999 * (-(normalizedPrimeArchMoment 2 -
        normalizedPrimeArchMoment 0 ^ 3 / 4)) <
      ∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x.1.1.1 a) := by
  rw [routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_eq x]
  have hgap := twoThousand_mul_neg_xiCubicMalgrangeMagnitude_lt_rawSource
  nlinarith

/-- Capstone Rees-rigid source-incidence law: all irregular threshold charges vanish, landing
extends over the full Rees parameter space, and terminal energy bears the near-total cancellation. -/
theorem routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_rigidity
    {p : ℕ} {n m K N : Fin (p + 1) → ℕ}
    {genus : ℕ} {d : LocalData p n m K N}
    (x : routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber genus d) :
    (∀ a edge,
        (d a).toOrbitCoareaDatum.cutCharge (x.1.1.1 a) edge = 0) ∧
      (∀ parameter : ReesParameter d,
        globalReesWittForm genus d parameter x.1.1 =
          normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4) ∧
      (1999 / 2000 : ℝ) *
          (∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k) <
        ∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x.1.1.1 a) ∧
      (∑ a, (d a).toOrbitCoareaDatum.terminalEnergy (x.1.1.1 a)) <
        ∑' k : ℕ, sourceHorizontalEulerGammaWoldCubicNaturalDefect k := by
  exact ⟨
    fun a edge =>
      routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_cutCharge_eq_zero
        x.1 a edge,
    fun parameter =>
      routePPrimitiveGammaJuliaStokesCubicMalgrangeReesRigidLandingFiber_landing_all_parameters
        x.1 parameter,
    routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_gt_fraction
      x,
    routePPrimitiveGammaJuliaStokesCubicRawEulerRankDebtReesRigidLandingFiber_terminal_lt_rawDebt
      x⟩

end

end RHTower
