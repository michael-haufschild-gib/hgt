import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureSourceAliasBudget
import GaloisForLFunctions.RHTower.HedenmalmCriticalFeatureCanonicalLatticeSummedDisplacement

/-!
# Finite-window source decomposition for the HCF lattice

The sharp Poisson estimate concerns the full integer periodization, while the canonical HCF
covariance uses a finite height lattice and a compact cutoff.  This module connects those two
objects without inserting a zero or divisor index.

On the canonical core `[-n-1,n+1]`, the compact cutoff is identically one.  The actual fused
finite-lattice observable is therefore the full periodized source observable minus an explicit
omitted-center term.  The part of the compact observable outside the core is retained as a second
explicit source tail.  Combining this exact split with the `37/200` Poisson ripple isolates the
three genuinely arithmetic debts: the pole--Gamma zero-mode mismatch, signed source `L¹` mass,
and finite-window leakage.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Uncut real HCF weight of a finite integer feature lattice. -/
def criticalFeatureFiniteRealBoundaryLatticeWeight
    (K : Finset ℤ) (x : ℝ) : ℝ :=
  ∑ k ∈ K, criticalFeatureRealBoundaryWeight (k : ℝ) x

theorem continuous_criticalFeatureFiniteRealBoundaryLatticeWeight
    (K : Finset ℤ) :
    Continuous (criticalFeatureFiniteRealBoundaryLatticeWeight K) := by
  unfold criticalFeatureFiniteRealBoundaryLatticeWeight
  exact continuous_finsetSum K fun k _hk =>
    continuous_criticalFeatureRealBoundaryWeight (k : ℝ)

theorem criticalFeatureFiniteRealBoundaryLatticeWeight_nonnegative
    (K : Finset ℤ) (x : ℝ) :
    0 ≤ criticalFeatureFiniteRealBoundaryLatticeWeight K x := by
  unfold criticalFeatureFiniteRealBoundaryLatticeWeight
  exact Finset.sum_nonneg fun k _hk => by
    unfold criticalFeatureRealBoundaryWeight
    positivity

theorem criticalFeatureFiniteRealBoundaryLatticeWeight_le_nine
    (K : Finset ℤ) (x : ℝ) :
    criticalFeatureFiniteRealBoundaryLatticeWeight K x ≤ 9 := by
  simpa only [criticalFeatureFiniteRealBoundaryLatticeWeight] using
    sum_criticalFeatureRealBoundaryWeight_le_nine K x

private theorem criticalFeatureRealBoundaryWeight_integer_eq_negTranslate
    (k : ℤ) (x : ℝ) :
    criticalFeatureRealBoundaryWeight (k : ℝ) x =
      criticalFeatureRealBoundaryWeight 0 (x + (-k : ℤ)) := by
  unfold criticalFeatureRealBoundaryWeight
  norm_num
  congr 2

theorem summable_criticalFeatureRealBoundaryWeight_integerCenters (x : ℝ) :
    Summable (fun k : ℤ => criticalFeatureRealBoundaryWeight (k : ℝ) x) := by
  have h := (Equiv.neg ℤ).summable_iff.mpr
    (summable_criticalFeatureRealBoundaryWeight_lattice x)
  refine h.congr ?_
  intro k
  rw [Function.comp_apply]
  exact (criticalFeatureRealBoundaryWeight_integer_eq_negTranslate k x).symm

theorem tsum_criticalFeatureRealBoundaryWeight_integerCenters (x : ℝ) :
    (∑' k : ℤ, criticalFeatureRealBoundaryWeight (k : ℝ) x) =
      criticalFeatureRealBoundaryPeriodization x := by
  rw [criticalFeatureRealBoundaryPeriodization]
  calc
    (∑' k : ℤ, criticalFeatureRealBoundaryWeight (k : ℝ) x) =
        ∑' k : ℤ, criticalFeatureRealBoundaryWeight 0 (x + (-k : ℤ)) := by
      apply tsum_congr
      intro k
      exact criticalFeatureRealBoundaryWeight_integer_eq_negTranslate k x
    _ = ∑' k : ℤ, criticalFeatureRealBoundaryWeight 0 (x + k) :=
      (Equiv.neg ℤ).tsum_eq
        (fun k : ℤ => criticalFeatureRealBoundaryWeight 0 (x + k))

/-- A finite HCF lattice is pointwise dominated by the full periodization.  Thus the interior
connector below is literally omitted positive center charge before it is paired with the signed
source. -/
theorem criticalFeatureFiniteRealBoundaryLatticeWeight_le_periodization
    (K : Finset ℤ) (x : ℝ) :
    criticalFeatureFiniteRealBoundaryLatticeWeight K x ≤
      criticalFeatureRealBoundaryPeriodization x := by
  rw [← tsum_criticalFeatureRealBoundaryWeight_integerCenters]
  exact (summable_criticalFeatureRealBoundaryWeight_integerCenters x).sum_le_tsum K
    (fun k _hk => by
      unfold criticalFeatureRealBoundaryWeight
      positivity)

/-- Canonical real height core covered by the padded feature lattice. -/
def criticalFeatureCanonicalCore (n : ℕ) : Set ℝ :=
  Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)

/-- On the canonical core, every selected cutoff `cutoff ≥ n` is one, so the fused compact
weight is exactly the uncut finite-lattice weight. -/
theorem criticalFeatureLatticeBoundaryCutoffWeight_eq_finiteWeight_on_core
    {n cutoff : ℕ} (hcutoff : n ≤ cutoff) {x : ℝ}
    (hx : x ∈ criticalFeatureCanonicalCore n) :
    criticalFeatureLatticeBoundaryCutoffWeight
        (criticalFeatureCanonicalLatticeWindow n) cutoff x =
      criticalFeatureFiniteRealBoundaryLatticeWeight
        (criticalFeatureCanonicalLatticeWindow n) x := by
  have hxabs : |x| ≤ (n : ℝ) + 1 := by
    rw [abs_le]
    simpa only [criticalFeatureCanonicalCore, mem_Icc] using hx
  have hncutoff : (n : ℝ) ≤ cutoff := by exact_mod_cast hcutoff
  have hchi : SchwartzMap.realCompactIntervalCutoff (cutoff : ℝ) x = 1 := by
    apply SchwartzMap.realCompactIntervalCutoff_apply_of_abs_le_add_one
    have hcutoffAbs : |(cutoff : ℝ)| = (cutoff : ℝ) :=
      abs_of_nonneg (Nat.cast_nonneg cutoff)
    rw [hcutoffAbs]
    linarith
  simp only [criticalFeatureLatticeBoundaryCutoffWeight,
    criticalFeatureBoundaryCutoffWeight, hchi, mul_one,
    criticalFeatureFiniteRealBoundaryLatticeWeight]

/-- Finite-lattice pole--Gamma observable restricted to the canonical core. -/
def criticalFeatureCanonicalCoreFinitePoleGammaObservable
    (n : ℕ) (eta : ℝ) : ℝ :=
  ∫ x in criticalFeatureCanonicalCore n,
    criticalFeatureFiniteRealBoundaryLatticeWeight
        (criticalFeatureCanonicalLatticeWindow n) x *
      criticalFeaturePositiveShiftPoleGammaDensity eta x

/-- Full-periodized pole--Gamma observable on the same canonical core. -/
def criticalFeatureCanonicalCoreFullPoleGammaObservable
    (n : ℕ) (eta : ℝ) : ℝ :=
  criticalFeatureFullLatticePoleGammaObservable
    (-((n : ℝ) + 1)) ((n : ℝ) + 1) eta

/-- Exact HCF zero-frequency source observable on the canonical core. -/
def criticalFeatureCanonicalCorePoleGammaZeroMode
    (n : ℕ) (eta : ℝ) : ℝ :=
  criticalFeaturePoleGammaZeroModeObservable
    (-((n : ℝ) + 1)) ((n : ℝ) + 1) eta

/-- Interior charge omitted when the full integer periodization is cut to the canonical finite
lattice.  Definition is source-only and remains signed after pairing. -/
def criticalFeatureCanonicalInteriorOmittedAlias
    (n : ℕ) (eta : ℝ) : ℝ :=
  criticalFeatureCanonicalCoreFullPoleGammaObservable n eta -
    criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta

/-- Part of the actual compact finite-lattice observable lying outside the canonical core. -/
def criticalFeatureCanonicalExteriorPoleGammaTail
    (n cutoff : ℕ) (eta : ℝ) : ℝ :=
  criticalFeatureCompactLatticePoleGammaObservable
      (criticalFeatureCanonicalLatticeWindow n) cutoff eta -
    criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta

/-- The core observable is literally the restriction of the actual fused compact integrand when
the selected cutoff dominates the canonical height. -/
theorem criticalFeatureCanonicalCoreFinitePoleGammaObservable_eq_cutoffWeight
    {n cutoff : ℕ} (hcutoff : n ≤ cutoff) (eta : ℝ) :
    criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta =
      ∫ x in criticalFeatureCanonicalCore n,
        criticalFeatureLatticeBoundaryCutoffWeight
            (criticalFeatureCanonicalLatticeWindow n) cutoff x *
          criticalFeaturePositiveShiftPoleGammaDensity eta x := by
  rw [criticalFeatureCanonicalCoreFinitePoleGammaObservable]
  apply setIntegral_congr_ae measurableSet_Icc
  filter_upwards with x
  intro hx
  rw [criticalFeatureLatticeBoundaryCutoffWeight_eq_finiteWeight_on_core
    hcutoff hx]

/-- Exact integral representation of the omitted-center connector. -/
theorem criticalFeatureCanonicalInteriorOmittedAlias_eq_integral
    (n : ℕ) (eta : ℝ)
    (hsource : IntegrableOn
      (criticalFeaturePositiveShiftPoleGammaDensity eta)
      (criticalFeatureCanonicalCore n)) :
    criticalFeatureCanonicalInteriorOmittedAlias n eta =
      ∫ x in criticalFeatureCanonicalCore n,
        (criticalFeatureRealBoundaryPeriodization x -
            criticalFeatureFiniteRealBoundaryLatticeWeight
              (criticalFeatureCanonicalLatticeWindow n) x) *
          criticalFeaturePositiveShiftPoleGammaDensity eta x := by
  have hfull : IntegrableOn
      (fun x => criticalFeatureRealBoundaryPeriodization x *
        criticalFeaturePositiveShiftPoleGammaDensity eta x)
      (criticalFeatureCanonicalCore n) := by
    have hbound : ∀ x, ‖criticalFeatureRealBoundaryPeriodization x‖ ≤ (9 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg
        (criticalFeatureRealBoundaryPeriodization_nonnegative x)]
      exact criticalFeatureRealBoundaryPeriodization_le_nine x
    exact hsource.bdd_mul
      continuous_criticalFeatureRealBoundaryPeriodization.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have hfinite : IntegrableOn
      (fun x => criticalFeatureFiniteRealBoundaryLatticeWeight
        (criticalFeatureCanonicalLatticeWindow n) x *
          criticalFeaturePositiveShiftPoleGammaDensity eta x)
      (criticalFeatureCanonicalCore n) := by
    have hbound : ∀ x,
        ‖criticalFeatureFiniteRealBoundaryLatticeWeight
          (criticalFeatureCanonicalLatticeWindow n) x‖ ≤ (9 : ℝ) := by
      intro x
      rw [Real.norm_eq_abs, abs_of_nonneg
        (criticalFeatureFiniteRealBoundaryLatticeWeight_nonnegative
          (criticalFeatureCanonicalLatticeWindow n) x)]
      exact criticalFeatureFiniteRealBoundaryLatticeWeight_le_nine
        (criticalFeatureCanonicalLatticeWindow n) x
    exact hsource.bdd_mul
      (continuous_criticalFeatureFiniteRealBoundaryLatticeWeight
        (criticalFeatureCanonicalLatticeWindow n)).aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  rw [criticalFeatureCanonicalInteriorOmittedAlias,
    criticalFeatureCanonicalCoreFullPoleGammaObservable,
    criticalFeatureFullLatticePoleGammaObservable,
    criticalFeatureCanonicalCoreFinitePoleGammaObservable]
  change
    (∫ x in criticalFeatureCanonicalCore n,
        criticalFeatureRealBoundaryPeriodization x *
          criticalFeaturePositiveShiftPoleGammaDensity eta x) -
      ∫ x in criticalFeatureCanonicalCore n,
        criticalFeatureFiniteRealBoundaryLatticeWeight
            (criticalFeatureCanonicalLatticeWindow n) x *
          criticalFeaturePositiveShiftPoleGammaDensity eta x = _
  rw [← MeasureTheory.integral_sub hfull hfinite]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  ring

/-- Sharp core alias budget for the finite canonical lattice.  Only the literal omitted-center
source term is added to the `37/200` full-periodization ripple. -/
theorem abs_criticalFeatureCanonicalCoreFinitePoleGammaObservable_sub_zeroMode_le
    (n : ℕ) (eta : ℝ)
    (hsource : IntegrableOn
      (criticalFeaturePositiveShiftPoleGammaDensity eta)
      (criticalFeatureCanonicalCore n)) :
    |criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta -
        criticalFeatureCanonicalCorePoleGammaZeroMode n eta| ≤
      (37 : ℝ) / 200 *
          (∫ x in criticalFeatureCanonicalCore n,
            |criticalFeaturePositiveShiftPoleGammaDensity eta x|) +
        |criticalFeatureCanonicalInteriorOmittedAlias n eta| := by
  have halias :=
    abs_criticalFeatureFullLatticePoleGammaObservable_sub_zeroMode_le
      (-((n : ℝ) + 1)) ((n : ℝ) + 1) eta hsource
  rw [← criticalFeatureCanonicalCoreFullPoleGammaObservable,
    ← criticalFeatureCanonicalCorePoleGammaZeroMode] at halias
  change
    |criticalFeatureCanonicalCoreFullPoleGammaObservable n eta -
        criticalFeatureCanonicalCorePoleGammaZeroMode n eta| ≤
      (37 : ℝ) / 200 *
        ∫ x in criticalFeatureCanonicalCore n,
          |criticalFeaturePositiveShiftPoleGammaDensity eta x| at halias
  have hid :
      criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta =
        (criticalFeatureCanonicalCoreFullPoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta) -
        criticalFeatureCanonicalInteriorOmittedAlias n eta := by
    rw [criticalFeatureCanonicalInteriorOmittedAlias]
    ring
  rw [hid]
  exact (abs_sub _ _).trans
    (add_le_add halias le_rfl)

/-- Actual finite-displacement covariance bound after finite-window Poisson separation.  Every
term on the right is defined from pole--Gamma source data before divisor scalarization. -/
theorem criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance_le_sourcePieces
    (n cutoff : ℕ) (eta : ℝ)
    (hsource : IntegrableOn
      (criticalFeaturePositiveShiftPoleGammaDensity eta)
      (criticalFeatureCanonicalCore n)) :
    criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance
        (criticalFeatureCanonicalLatticeWindow n) cutoff eta ≤
      (criticalFeaturePoleGammaLatticeBudget
          (criticalFeatureCanonicalLatticeWindow n) -
        criticalFeatureCanonicalCorePoleGammaZeroMode n eta) +
      (37 : ℝ) / 200 *
          (∫ x in criticalFeatureCanonicalCore n,
            |criticalFeaturePositiveShiftPoleGammaDensity eta x|) +
      |criticalFeatureCanonicalInteriorOmittedAlias n eta| +
      |criticalFeatureCanonicalExteriorPoleGammaTail n cutoff eta| := by
  have hcore :=
    abs_criticalFeatureCanonicalCoreFinitePoleGammaObservable_sub_zeroMode_le
      n eta hsource
  have hid :
      criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance
          (criticalFeatureCanonicalLatticeWindow n) cutoff eta =
        (criticalFeaturePoleGammaLatticeBudget
            (criticalFeatureCanonicalLatticeWindow n) -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta) -
        (criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta) -
        criticalFeatureCanonicalExteriorPoleGammaTail n cutoff eta := by
    rw [criticalFeatureFiniteLatticeDisplacementPoleGammaCovariance,
      criticalFeatureCanonicalExteriorPoleGammaTail]
    ring
  rw [hid]
  have hcoreNeg :
      -(criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta) ≤
        |criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta| :=
    neg_le_abs _
  have htailNeg :
      -criticalFeatureCanonicalExteriorPoleGammaTail n cutoff eta ≤
        |criticalFeatureCanonicalExteriorPoleGammaTail n cutoff eta| :=
    neg_le_abs _
  have hcoreBound :
      -(criticalFeatureCanonicalCoreFinitePoleGammaObservable n eta -
          criticalFeatureCanonicalCorePoleGammaZeroMode n eta) ≤
        (37 : ℝ) / 200 *
            (∫ x in criticalFeatureCanonicalCore n,
              |criticalFeaturePositiveShiftPoleGammaDensity eta x|) +
          |criticalFeatureCanonicalInteriorOmittedAlias n eta| :=
    hcoreNeg.trans hcore
  linarith

end

end RHTower
