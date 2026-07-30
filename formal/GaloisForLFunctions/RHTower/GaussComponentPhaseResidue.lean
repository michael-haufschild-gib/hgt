import GaloisForLFunctions.RHTower.GaussComponentMagnitudeResidue
import GaloisForLFunctions.HTGeometry.HarmonicComplexResidueTransfer

/-!
# Phase-weighted Gauss-component magnitude residues
-/

namespace RHTower

open Filter Topology Finset MeasureTheory

noncomputable section

def gaussComponentPhaseRate (m : ℕ) (p : Nat.Primes) : ℝ :=
  1 / ((m : ℝ) * Real.log (p : ℝ))

def gaussComponentPhaseOffset (m : ℕ) (p : Nat.Primes) : ℝ :=
  -Real.log (Real.log (p : ℝ)) / ((m : ℝ) * Real.log (p : ℝ))

def gaussComponentPhasePoint (m : ℕ) (p : Nat.Primes) (n : ℕ) : AddCircle (1 : ℝ) :=
  ((gaussComponentPhaseRate m p * Real.log ((n : ℝ) + 1) +
      gaussComponentPhaseOffset m p : ℝ) : AddCircle (1 : ℝ))

lemma inv_smul_complex_eq_div_ofReal (c : ℝ) (z : ℂ) :
    c⁻¹ • z = z / (c : ℂ) := by
  rw [Complex.real_smul, div_eq_mul_inv, ← Complex.ofReal_inv]
  ring

lemma harmonicLogCircleAverage_eq_smul (β θ : ℝ)
    (f : C(AddCircle (1 : ℝ), ℂ)) (N : ℕ) :
    GaloisForLFunctions.harmonicLogCircleAverage β θ f N =
      (Real.log N)⁻¹ •
        (∑ n ∈ Finset.range N,
          (((n : ℝ) + 1)⁻¹ : ℝ) •
            f ((β * Real.log ((n : ℝ) + 1) + θ : ℝ) : AddCircle (1 : ℝ))) := by
  rw [GaloisForLFunctions.harmonicLogCircleAverage, inv_smul_complex_eq_div_ofReal]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Complex.real_smul, Complex.ofReal_inv]
  push_cast
  norm_num

theorem gaussComponentPhase_harmonicAverage_tendsto
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes)
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun N : ℕ =>
      GaloisForLFunctions.harmonicLogCircleAverage
        (gaussComponentPhaseRate m p) (gaussComponentPhaseOffset m p) f N)
      atTop (nhds (∫ x, f x ∂GaloisForLFunctions.unitCircleHaar)) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlog : 0 < Real.log ((p : Nat.Primes) : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hrate : gaussComponentPhaseRate m p ≠ 0 := by
    rw [gaussComponentPhaseRate]
    positivity
  exact GaloisForLFunctions.harmonicLogCircleAverage_tendsto_haar _ _ hrate f

/-- Phase-weighted version of the exact sampled Gauss magnitude residue. -/
theorem gaussComponentPrimeMagnitudeEnergy_phase_logResidue
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes)
    (f : C(AddCircle (1 : ℝ), ℂ)) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.range N,
          (gaussComponentPrimeMagnitudeEnergy k p n : ℂ) *
            f (gaussComponentPhasePoint m p n)) /
        (Real.log N : ℂ))
      atTop
      (nhds ((Real.log (p : ℝ) : ℂ) *
        ∫ x, f x ∂GaloisForLFunctions.unitCircleHaar)) := by
  let L : ℝ := Real.log (p : ℝ)
  let b : ℕ → ℝ := fun n =>
    gaussComponentPrimeMagnitudeEnergy k p n * ((n : ℝ) + 1)
  let e : ℕ → ℂ := fun n => ((b n - L : ℝ) : ℂ) * f (gaussComponentPhasePoint m p n)
  have hb : Tendsto b atTop (nhds L) := by
    simpa [b, L] using gaussComponentPrimeMagnitudeEnergy_mul_succ_tendsto hm k p
  have hbzero : Tendsto (fun n => ((b n - L : ℝ) : ℂ)) atTop (nhds 0) := by
    have hr : Tendsto (fun n => b n - L) atTop (nhds 0) := tendsto_sub_nhds_zero_iff.mpr hb
    simpa only [Complex.ofReal_zero] using!
      Complex.continuous_ofReal.continuousAt.tendsto.comp hr
  have hfBounded : IsBoundedUnder (· ≤ ·) atTop
      (fun n : ℕ => ‖f (gaussComponentPhasePoint m p n)‖) :=
    by
      refine ⟨‖f‖, ?_⟩
      change ∀ᶠ n : ℕ in atTop, ‖f (gaussComponentPhasePoint m p n)‖ ≤ ‖f‖
      exact Filter.Eventually.of_forall fun n =>
        ContinuousMap.norm_coe_le_norm f (gaussComponentPhasePoint m p n)
  have hezero : Tendsto e atTop (nhds 0) := by
    have h := NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hbzero hfBounded
    simpa [e, Pi.smul_apply, smul_eq_mul] using! h
  have herror := GaloisForLFunctions.tendsto_complexHarmonicWeighted_error_zero hezero
  have haverage := gaussComponentPhase_harmonicAverage_tendsto hm p f
  have hmain := haverage.const_mul (L : ℂ)
  have htotal := hmain.add herror
  have heq : ∀ᶠ N : ℕ in atTop,
      (L : ℂ) * GaloisForLFunctions.harmonicLogCircleAverage
          (gaussComponentPhaseRate m p) (gaussComponentPhaseOffset m p) f N +
        (Real.log N)⁻¹ •
          (∑ n ∈ Finset.range N, (((n : ℝ) + 1)⁻¹ : ℝ) • e n) =
        (∑ n ∈ Finset.range N,
            (gaussComponentPrimeMagnitudeEnergy k p n : ℂ) *
              f (gaussComponentPhasePoint m p n)) /
          (Real.log N : ℂ) := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    rw [harmonicLogCircleAverage_eq_smul]
    simp_rw [inv_smul_complex_eq_div_ofReal]
    rw [← mul_div_assoc, ← add_div]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [e, b, gaussComponentPhasePoint]
    push_cast
    have hnC : (n : ℂ) + 1 ≠ 0 := by
      exact_mod_cast (by omega : n + 1 ≠ 0)
    field_simp [hnC]
    ring
  simpa only [L, add_zero] using htotal.congr' heq

end

end RHTower
