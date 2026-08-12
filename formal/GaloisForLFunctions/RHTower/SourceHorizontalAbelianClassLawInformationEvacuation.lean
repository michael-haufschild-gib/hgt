import GaloisForLFunctions.RHTower.SourceHorizontalAbelianClassLawApertureEvacuation
import GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveFisherReflectionCurvature

/-!
# Mass-weighted adaptive information evacuates through the exact abelian aperture

The canonical abelian two-class event has conditionals whose reflected Jeffreys work grows
linearly with horizontal scale.  Nevertheless, actual class-law admission decays geometrically.
This module proves their product tends to zero in both orientations.  Thus the exact observer does
not merely become rare: its entire mass-weighted adaptive information current disappears.

This is the positive survivor of a failed conjecture that an information chain rule itself was
missing.  The corpus already contains that chain rule.  What is missing is source renewal that
injects information quickly enough to defeat the theorem below.
-/

open Real Set MeasureTheory Filter Topology

namespace RHTower

open GaloisForLFunctions GaloisForLFunctions.HTGeometry

noncomputable section

/-- Adaptive Jeffreys work is at most its bare linear rapidity scale on the positive half-line. -/
theorem sourceHorizontalPrimeAdaptiveJeffreysWork_le_linear
    (p : Nat.Primes) {u : ℝ} (hu : 0 ≤ u) :
    sourceHorizontalPrimeAdaptiveJeffreysWork p u ≤ 2 * u * Real.log (p : ℝ) := by
  have hgap : sourceHorizontalPrimeAdaptiveOccupation p u -
      sourceHorizontalPrimeAdaptiveOccupation p (-u) ≤ 1 := by
    have hupper := sourceHorizontalPrimeAdaptiveOccupation_lt_one p u
    have hlower := sourceHorizontalPrimeAdaptiveOccupation_pos p (-u)
    linarith
  have hcoef : 0 ≤ 2 * u * Real.log (p : ℝ) := by
    have hlog : 0 ≤ Real.log (p : ℝ) :=
      (Real.log_pos (by exact_mod_cast p.2.one_lt)).le
    positivity
  unfold sourceHorizontalPrimeAdaptiveJeffreysWork
  simpa using mul_le_mul_of_nonneg_left hgap hcoef

theorem sourceHorizontalPrimeAdaptiveJeffreysWork_nonneg
    (p : Nat.Primes) (u : ℝ) :
    0 ≤ sourceHorizontalPrimeAdaptiveJeffreysWork p u := by
  by_cases hu : u = 0
  · subst hu
    simp [sourceHorizontalPrimeAdaptiveJeffreysWork]
  · exact (sourceHorizontalPrimeAdaptiveJeffreysWork_pos_iff p u).2 hu |>.le

private theorem tendsto_natSucc_mul_prime_rpow_neg_succ_zero (p : Nat.Primes) :
    Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) *
      (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1))) atTop (nhds 0) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  let r : ℝ := (p : ℝ)⁻¹
  have hr0 : 0 ≤ r := inv_nonneg.mpr hp.le
  have hr1 : r < 1 := (inv_lt_one₀ hp).2 hp1
  have hbase := tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  have hscaled := hshift.mul_const r
  convert hscaled using 1
  · funext N
    dsimp only [Function.comp_apply]
    rw [show ((N + 1 : ℕ) : ℝ) + 1 = ((N + 2 : ℕ) : ℝ) by
        push_cast
        ring,
      Real.rpow_neg hp.le, Real.rpow_natCast]
    simp only [r]
    rw [pow_succ]
    ring
  · simp

/-- **Forward information evacuation.** Although conditional reflected Jeffreys work grows
linearly, actual forward class-law mass times that work tends to zero. -/
theorem tendsto_sourceHorizontalAbelianForwardAdmission_mul_adaptiveJeffreysWork_zero
    (p : Nat.Primes) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (fun N : ℕ =>
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianForwardParameters a ha0 ha1) p (N + 1) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((N + 1 : ℕ) : ℝ) * a))
      atTop (nhds 0) := by
  let c := ((sourceHorizontalAbelianForwardParameters a ha0 ha1).ennNormalizer).toReal
  have hgeom := tendsto_natSucc_mul_prime_rpow_neg_succ_zero p
  have hupper : Tendsto (fun N : ℕ =>
      (4 * c * a * Real.log (p : ℝ)) *
        (((N + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1))))
      atTop (nhds 0) := by
    convert hgeom.const_mul (4 * c * a * Real.log (p : ℝ)) using 1
    all_goals ring_nf
  have hnonneg : ∀ N : ℕ, 0 ≤
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianForwardParameters a ha0 ha1) p (N + 1) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((N + 1 : ℕ) : ℝ) * a) := by
    intro N
    apply mul_nonneg
    · unfold sourceHorizontalAbelianTwoClassAdmission
      exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    · exact sourceHorizontalPrimeAdaptiveJeffreysWork_nonneg p _
  have hle : ∀ N : ℕ,
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianForwardParameters a ha0 ha1) p (N + 1) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((N + 1 : ℕ) : ℝ) * a) ≤
      (4 * c * a * Real.log (p : ℝ)) *
        (((N + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1))) := by
    intro N
    rw [sourceHorizontalAbelianForwardAdmission_eq p (N + 1) (by omega) ha0 ha1]
    change (c * _) * _ ≤ _
    have hW := sourceHorizontalAbelianForwardUnnormalizedAdmission_le
      p (N + 1) (by omega) ha0 ha1
    have hc : 0 ≤ c := ENNReal.toReal_nonneg
    have hAdmission := mul_le_mul_of_nonneg_left hW hc
    have hWork := sourceHorizontalPrimeAdaptiveJeffreysWork_le_linear p
      (u := (((N + 1 : ℕ) : ℝ) * a)) (mul_nonneg (by positivity) ha0)
    calc
      (c * _) * _ ≤
          (c * (2 * (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1)))) *
            (2 * (((N + 1 : ℕ) : ℝ) * a) * Real.log (p : ℝ)) := by
              exact mul_le_mul hAdmission hWork
                (sourceHorizontalPrimeAdaptiveJeffreysWork_nonneg p _)
                (mul_nonneg hc (by positivity))
      _ = _ := by ring
  exact squeeze_zero hnonneg hle hupper

/-- **Reflected information evacuation.** The reverse class law loses the same mass-weighted
adaptive information current. -/
theorem tendsto_sourceHorizontalAbelianReverseAdmission_mul_adaptiveJeffreysWork_zero
    (p : Nat.Primes) {a : ℝ} (ha0 : 0 ≤ a) :
    Tendsto (fun N : ℕ =>
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianReverseParameters a ha0) p (N + 1) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((N + 1 : ℕ) : ℝ) * a))
      atTop (nhds 0) := by
  let c := ((sourceHorizontalAbelianReverseParameters a ha0).ennNormalizer).toReal
  have hgeom := tendsto_natSucc_mul_prime_rpow_neg_succ_zero p
  have hupper : Tendsto (fun N : ℕ =>
      (4 * c * a * Real.log (p : ℝ)) *
        (((N + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1))))
      atTop (nhds 0) := by
    convert hgeom.const_mul (4 * c * a * Real.log (p : ℝ)) using 1
    all_goals ring_nf
  have hnonneg : ∀ N : ℕ, 0 ≤
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianReverseParameters a ha0) p (N + 1) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((N + 1 : ℕ) : ℝ) * a) := by
    intro N
    apply mul_nonneg
    · unfold sourceHorizontalAbelianTwoClassAdmission
      exact add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    · exact sourceHorizontalPrimeAdaptiveJeffreysWork_nonneg p _
  have hle : ∀ N : ℕ,
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianReverseParameters a ha0) p (N + 1) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((N + 1 : ℕ) : ℝ) * a) ≤
      (4 * c * a * Real.log (p : ℝ)) *
        (((N + 1 : ℕ) : ℝ) * (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1))) := by
    intro N
    rw [sourceHorizontalAbelianReverseAdmission_eq p (N + 1) (by omega) ha0]
    change (c * _) * _ ≤ _
    have hW := sourceHorizontalAbelianReverseUnnormalizedAdmission_le
      p (N + 1) (by omega) ha0
    have hc : 0 ≤ c := ENNReal.toReal_nonneg
    have hAdmission := mul_le_mul_of_nonneg_left hW hc
    have hWork := sourceHorizontalPrimeAdaptiveJeffreysWork_le_linear p
      (u := (((N + 1 : ℕ) : ℝ) * a)) (mul_nonneg (by positivity) ha0)
    calc
      (c * _) * _ ≤
          (c * (2 * (p : ℝ) ^ (-(((N + 1 : ℕ) : ℝ) + 1)))) *
            (2 * (((N + 1 : ℕ) : ℝ) * a) * Real.log (p : ℝ)) := by
              exact mul_le_mul hAdmission hWork
                (sourceHorizontalPrimeAdaptiveJeffreysWork_nonneg p _)
                (mul_nonneg hc (by positivity))
      _ = _ := by ring
  exact squeeze_zero hnonneg hle hupper

/-- Both mass-weighted information currents evacuate for every multiplicity-labelled Xi zero. -/
theorem sourceHorizontalXiAbelianMassWeightedAdaptiveWork_evacuates
    (q : XiZeroCopy) (p : Nat.Primes) :
    let a := |primeDepthBVWoldXiCenteredRate q.1|
    Tendsto (fun N : ℕ =>
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianForwardParameters a (abs_nonneg _)
            (sourceHorizontalXiCenteredRate_abs_lt_one q)) p (N + 1) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((N + 1 : ℕ) : ℝ) * a))
      atTop (nhds 0) ∧
    Tendsto (fun N : ℕ =>
      sourceHorizontalAbelianTwoClassAdmission
          (sourceHorizontalAbelianReverseParameters a (abs_nonneg _)) p (N + 1) *
        sourceHorizontalPrimeAdaptiveJeffreysWork p (((N + 1 : ℕ) : ℝ) * a))
      atTop (nhds 0) := by
  dsimp only
  exact ⟨
    tendsto_sourceHorizontalAbelianForwardAdmission_mul_adaptiveJeffreysWork_zero p
      (abs_nonneg _) (sourceHorizontalXiCenteredRate_abs_lt_one q),
    tendsto_sourceHorizontalAbelianReverseAdmission_mul_adaptiveJeffreysWork_zero p
      (abs_nonneg _)⟩

end

end RHTower
