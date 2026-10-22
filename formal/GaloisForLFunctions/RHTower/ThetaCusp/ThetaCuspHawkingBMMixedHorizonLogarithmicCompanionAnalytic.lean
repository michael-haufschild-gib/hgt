import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedHorizonLogarithmicCompanion
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries

/-!
# Analytic resonant logarithmic companion at the mixed BM horizon

The reciprocal tail increments split into three corpus Gauss--digamma series. Their absolute
summability bounds every tail multiplier uniformly and gives the analytic companion radius at
least one. A coefficient-generic formal-to-analytic lift then proves the inhomogeneous Euler pair.
Product rules reconstruct the principal logarithmic solution, its first two actual derivatives,
its homogeneous Gauss equation on the slit disk, and its exact `2πi` deck discontinuity.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex Nat Polynomial

namespace RHTower


noncomputable section

def d4HypergeometricResonantShiftedA (N : ℕ) (a : ℂ) : ℂ := a + ((N + 1 : ℕ) : ℂ)
def d4HypergeometricResonantShiftedC (N : ℕ) : ℂ := ((N + 2 : ℕ) : ℂ)

def d4HypergeometricResonantLogTailIncrement (N : ℕ) (a b : ℂ) (j : ℕ) : ℂ :=
  -gaussDigammaSeriesTerm (d4HypergeometricResonantShiftedA N a) j -
    gaussDigammaSeriesTerm (d4HypergeometricResonantShiftedA N b) j +
    gaussDigammaSeriesTerm (d4HypergeometricResonantShiftedC N) j

theorem d4HypergeometricResonantLogTailMultiplier_eq_sum_increment (N : ℕ) (a b : ℂ) (k : ℕ) :
    d4HypergeometricResonantLogTailMultiplier N a b k =
      ∑ j ∈ Finset.range k, d4HypergeometricResonantLogTailIncrement N a b j := by
  unfold d4HypergeometricResonantLogTailMultiplier d4HypergeometricResonantLogTailIncrement
    gaussDigammaSeriesTerm d4HypergeometricResonantShiftedA d4HypergeometricResonantShiftedC
  apply Finset.sum_congr rfl
  intro j hj
  push_cast
  ring

theorem summable_norm_d4HypergeometricResonantLogTailIncrement (N : ℕ) (a b : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re) (hb : 0 < (d4HypergeometricResonantShiftedA N b).re) :
    Summable (fun j : ℕ => ‖d4HypergeometricResonantLogTailIncrement N a b j‖) := by
  have hC : 0 < (d4HypergeometricResonantShiftedC N).re := by
    simp [d4HypergeometricResonantShiftedC]
    positivity
  have hsa := summable_gaussDigammaSeriesTerm ha
  have hsb := summable_gaussDigammaSeriesTerm hb
  have hsc := summable_gaussDigammaSeriesTerm hC
  exact ((hsa.neg.sub hsb).add hsc).norm

theorem norm_d4HypergeometricResonantLogTailMultiplier_le (N : ℕ) (a b : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re) (hb : 0 < (d4HypergeometricResonantShiftedA N b).re) (k : ℕ) :
    ‖d4HypergeometricResonantLogTailMultiplier N a b k‖ ≤
      ∑' j : ℕ, ‖d4HypergeometricResonantLogTailIncrement N a b j‖ := by
  rw [d4HypergeometricResonantLogTailMultiplier_eq_sum_increment]
  calc
    ‖∑ j ∈ Finset.range k, d4HypergeometricResonantLogTailIncrement N a b j‖ ≤
        ∑ j ∈ Finset.range k, ‖d4HypergeometricResonantLogTailIncrement N a b j‖ := norm_sum_le _ _
    _ ≤ ∑' j : ℕ, ‖d4HypergeometricResonantLogTailIncrement N a b j‖ :=
      Summable.sum_le_tsum _ (fun j _ => norm_nonneg _)
        (summable_norm_d4HypergeometricResonantLogTailIncrement N a b ha hb)

def d4HypergeometricResonantRegularFactorSeries (N : ℕ) (a b : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  ordinaryHypergeometricSeries ℂ (d4HypergeometricResonantShiftedA N a) (d4HypergeometricResonantShiftedA N b) (d4HypergeometricResonantShiftedC N)

def d4HypergeometricResonantLogTailSeries (N : ℕ) (a b : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (d4HypergeometricResonantLogTailCoefficient N a b)

theorem d4HypergeometricResonantRegularFactorSeries_radius_eq_one (N : ℕ) (a b : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re) (hb : 0 < (d4HypergeometricResonantShiftedA N b).re) :
    (d4HypergeometricResonantRegularFactorSeries N a b).radius = 1 := by
  rw [d4HypergeometricResonantRegularFactorSeries]
  apply ordinaryHypergeometricSeries_radius_eq_one
  intro j
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  · intro h
    have hre := congrArg Complex.re h
    simp [d4HypergeometricResonantShiftedC] at hre
    have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hN0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith

theorem d4HypergeometricResonantLogTailSeries_radius_ge_one (N : ℕ) (a b : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re) (hb : 0 < (d4HypergeometricResonantShiftedA N b).re) :
    (1 : ENNReal) ≤ (d4HypergeometricResonantLogTailSeries N a b).radius := by
  let C : ℝ := ‖d4HypergeometricResonantFrobeniusLogCoefficient N a b‖ *
    ∑' j : ℕ, ‖d4HypergeometricResonantLogTailIncrement N a b j‖
  have htsum0 : 0 ≤ ∑' j : ℕ, ‖d4HypergeometricResonantLogTailIncrement N a b j‖ :=
    tsum_nonneg (fun _ => norm_nonneg _)
  have hC0 : 0 ≤ C := mul_nonneg (norm_nonneg _) htsum0
  have hcomp : ∀ j : ℕ,
      ‖d4HypergeometricResonantLogTailSeries N a b j‖ ≤
        ‖((C : ℂ) • d4HypergeometricResonantRegularFactorSeries N a b) j‖ := by
    intro j
    rw [d4HypergeometricResonantLogTailSeries, FormalMultilinearSeries.ofScalars_norm,
      FormalMultilinearSeries.smul_apply, norm_smul,
      d4HypergeometricResonantRegularFactorSeries, ordinaryHypergeometricSeries,
      FormalMultilinearSeries.ofScalars_norm,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC0]
    rw [d4HypergeometricResonantLogTailCoefficient, norm_mul, norm_mul]
    have hR := norm_d4HypergeometricResonantLogTailMultiplier_le N a b ha hb j
    calc
      ‖d4HypergeometricResonantFrobeniusLogCoefficient N a b‖ *
          ‖d4HypergeometricResonantRegularCoefficient N a b j‖ *
            ‖d4HypergeometricResonantLogTailMultiplier N a b j‖ ≤
          ‖d4HypergeometricResonantFrobeniusLogCoefficient N a b‖ *
            ‖d4HypergeometricResonantRegularCoefficient N a b j‖ *
              (∑' i : ℕ, ‖d4HypergeometricResonantLogTailIncrement N a b i‖) := by
        exact mul_le_mul_of_nonneg_left hR
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = C *
          ‖ordinaryHypergeometricCoefficient
            (d4HypergeometricResonantShiftedA N a) (d4HypergeometricResonantShiftedA N b) (d4HypergeometricResonantShiftedC N) j‖ := by
        simp [C, d4HypergeometricResonantRegularCoefficient,
          d4HypergeometricResonantShiftedA, d4HypergeometricResonantShiftedC]
        ring
  calc
    (1 : ENNReal) = (d4HypergeometricResonantRegularFactorSeries N a b).radius := by
      rw [d4HypergeometricResonantRegularFactorSeries_radius_eq_one N a b ha hb]
    _ ≤ ((C : ℂ) • d4HypergeometricResonantRegularFactorSeries N a b).radius :=
      FormalMultilinearSeries.radius_le_smul
    _ ≤ (d4HypergeometricResonantLogTailSeries N a b).radius :=
      FormalMultilinearSeries.radius_le_of_le hcomp

def d4HypergeometricResonantCompanionAnalyticSeries (N : ℕ) (a b : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (d4HypergeometricResonantCompanionAnalyticCoefficient N a b)

theorem d4HypergeometricResonantCompanionAnalyticSeries_radius_ge_one (N : ℕ) (a b : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re) (hb : 0 < (d4HypergeometricResonantShiftedA N b).re) :
    (1 : ENNReal) ≤ (d4HypergeometricResonantCompanionAnalyticSeries N a b).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have hrtail : (r : ENNReal) < (d4HypergeometricResonantLogTailSeries N a b).radius :=
    lt_of_lt_of_le hr (d4HypergeometricResonantLogTailSeries_radius_ge_one N a b ha hb)
  have hsumTail := (d4HypergeometricResonantLogTailSeries N a b).summable_norm_mul_pow hrtail
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  apply (summable_nat_add_iff (N + 1)).mp
  have hmul := hsumTail.mul_left ((r : ℝ) ^ (N + 1))
  apply hmul.congr
  intro k
  rw [Nat.add_comm k (N + 1)]
  rw [d4HypergeometricResonantCompanionAnalyticSeries, FormalMultilinearSeries.ofScalars_norm,
    d4HypergeometricResonantCompanionAnalyticCoefficient_shift,
    d4HypergeometricResonantLogTailSeries, FormalMultilinearSeries.ofScalars_norm]
  rw [pow_add]
  ring

def d4HypergeometricResonantRegularBranchSeries
    (N : ℕ) (a b : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (d4HypergeometricResonantRegularBranchCoefficient N a b)

/-- The shifted regular resonant branch converges throughout the open unit disk. -/
theorem d4HypergeometricResonantRegularBranchSeries_radius_ge_one (N : ℕ) (a b : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re) :
    (1 : ENNReal) ≤ (d4HypergeometricResonantRegularBranchSeries N a b).radius := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro r hr
  have hrfactor :
      (r : ENNReal) < (d4HypergeometricResonantRegularFactorSeries N a b).radius := by
    rw [d4HypergeometricResonantRegularFactorSeries_radius_eq_one N a b ha hb]
    exact hr
  have hsum :=
    (d4HypergeometricResonantRegularFactorSeries N a b).summable_norm_mul_pow hrfactor
  have hfactor_coeff (k : ℕ) :
      ‖d4HypergeometricResonantRegularFactorSeries N a b k‖ =
        ‖d4HypergeometricResonantRegularCoefficient N a b k‖ := by
    rw [d4HypergeometricResonantRegularFactorSeries, ordinaryHypergeometricSeries,
      FormalMultilinearSeries.ofScalars_norm]
    congr 1
  apply FormalMultilinearSeries.le_radius_of_summable_norm
  apply (summable_nat_add_iff (N + 1)).mp
  have hmul := hsum.mul_left ((r : ℝ) ^ (N + 1))
  apply hmul.congr
  intro k
  rw [Nat.add_comm k (N + 1)]
  rw [d4HypergeometricResonantRegularBranchSeries,
    FormalMultilinearSeries.ofScalars_norm,
    d4HypergeometricResonantRegularBranchCoefficient_shift,
    hfactor_coeff]
  rw [pow_add]
  ring

/-- Positive shifted real part excludes every denominator after resonant collision. -/
theorem d4Hypergeometric_add_order_add_ne_zero_of_shiftedA_re_pos
    (N : ℕ) (a : ℂ) (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (k : ℕ) (hk : 0 < k) :
    a + (N : ℂ) + (k : ℂ) ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp [d4HypergeometricResonantShiftedA] at ha hre
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

/-- First derivative-series value of a scalar formal series. -/
def scalarFirstValue (u : ℕ → ℂ) (z : ℂ) : ℂ :=
  (((FormalMultilinearSeries.ofScalars ℂ u).derivSeries.sum z) 1)

/-- Second derivative-series value of a scalar formal series. -/
def scalarSecondValue (u : ℕ → ℂ) (z : ℂ) : ℂ :=
  ((((FormalMultilinearSeries.ofScalars ℂ u).derivSeries.derivSeries.sum z) 1) 1)

theorem scalarSeries_term (u : ℕ → ℂ) (z : ℂ) (j : ℕ) :
    (FormalMultilinearSeries.ofScalars ℂ u j (fun _ => z)) = u j * z ^ j := by
  rw [FormalMultilinearSeries.ofScalars_apply_eq]
  simp

theorem scalarSeries_deriv_term (u : ℕ → ℂ) (z : ℂ) (j : ℕ) :
    ((((FormalMultilinearSeries.ofScalars ℂ u).derivSeries j
      (fun _ => z)) 1)) =
      ((j + 1 : ℕ) : ℂ) * u (j + 1) * z ^ j := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    _root_.smul_apply, FormalMultilinearSeries.derivSeries_coeff_one]
  simp only [FormalMultilinearSeries.coeff_ofScalars, nsmul_eq_mul]
  push_cast
  ring

theorem scalarSeries_secondDeriv_term (u : ℕ → ℂ) (z : ℂ) (j : ℕ) :
    (((((FormalMultilinearSeries.ofScalars ℂ u).derivSeries.derivSeries j
      (fun _ => z)) 1) 1)) =
      ((j + 2 : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) * u (j + 2) * z ^ j := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, _root_.smul_apply]
  simp only [_root_.smul_apply,
    FormalMultilinearSeries.derivSeries_coeff_one]
  simp only [FormalMultilinearSeries.coeff_ofScalars, nsmul_eq_mul]
  push_cast
  ring

/-- Value and first two derivative series represented by scalar coefficient sums in their common
convergence disk. -/
theorem scalarSeries_hasSum_value_first_second
    (u : ℕ → ℂ) (z : ℂ)
    (hz : ‖z‖ₑ < (FormalMultilinearSeries.ofScalars ℂ u).radius) :
    HasSum (fun j => u j * z ^ j)
        ((FormalMultilinearSeries.ofScalars ℂ u).sum z) ∧
      HasSum (fun j => ((j + 1 : ℕ) : ℂ) * u (j + 1) * z ^ j)
        (scalarFirstValue u z) ∧
      HasSum (fun j => ((j + 2 : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) *
          u (j + 2) * z ^ j)
        (scalarSecondValue u z) := by
  let p := FormalMultilinearSeries.ofScalars ℂ u
  let q := p.derivSeries
  let r := q.derivSeries
  have hzq : ‖z‖ₑ < q.radius :=
    lt_of_lt_of_le hz p.radius_le_radius_derivSeries
  have hzr : ‖z‖ₑ < r.radius :=
    lt_of_lt_of_le hzq q.radius_le_radius_derivSeries
  have hzmem : z ∈ Metric.eball (0 : ℂ) p.radius := by
    simpa only [Metric.mem_eball, edist_zero_right] using hz
  have hzqmem : z ∈ Metric.eball (0 : ℂ) q.radius := by
    simpa only [Metric.mem_eball, edist_zero_right] using hzq
  have hzrmem : z ∈ Metric.eball (0 : ℂ) r.radius := by
    simpa only [Metric.mem_eball, edist_zero_right] using hzr
  have hp0 := p.hasSum hzmem
  have hq0 := q.hasSum hzqmem
  have hr0 := r.hasSum hzrmem
  have hq1 := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).hasSum hq0
  have hr1 := (ContinuousLinearMap.apply ℂ (ℂ →L[ℂ] ℂ) (1 : ℂ)).hasSum hr0
  have hr2 := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).hasSum hr1
  change HasSum (fun j => ((p.derivSeries j (fun _ => z)) 1))
    ((p.derivSeries.sum z) 1) at hq1
  change HasSum (fun j => (((p.derivSeries.derivSeries j (fun _ => z)) 1) 1))
    (((p.derivSeries.derivSeries.sum z) 1) 1) at hr2
  constructor
  · simpa only [p, scalarSeries_term] using hp0
  constructor
  · simpa only [p, scalarFirstValue, scalarSeries_deriv_term] using hq1
  · simpa only [p, scalarSecondValue, scalarSeries_secondDeriv_term] using hr2

/-- A convergent scalar formal series differentiates to its derivative-series value. -/
theorem hasDerivAt_scalarSeries_sum (u : ℕ → ℂ) (z : ℂ)
    (hz : ‖z‖ₑ < (FormalMultilinearSeries.ofScalars ℂ u).radius) :
    HasDerivAt (FormalMultilinearSeries.ofScalars ℂ u).sum
      (scalarFirstValue u z) z := by
  let p := FormalMultilinearSeries.ofScalars ℂ u
  change HasDerivAt p.sum ((p.derivSeries.sum z) 1) z
  exact (p.hasFDerivAt_sum hz).hasDerivAt

/-- A scalar derivative-series value differentiates to its second derivative-series value. -/
theorem hasDerivAt_scalarFirstValue (u : ℕ → ℂ) (z : ℂ)
    (hz : ‖z‖ₑ < (FormalMultilinearSeries.ofScalars ℂ u).radius) :
    HasDerivAt (scalarFirstValue u) (scalarSecondValue u z) z := by
  let p := FormalMultilinearSeries.ofScalars ℂ u
  let q := p.derivSeries
  have hzq : ‖z‖ₑ < q.radius :=
    lt_of_lt_of_le hz p.radius_le_radius_derivSeries
  have hq := q.hasFDerivAt_sum hzq
  have heval := hq.clm_apply (hasFDerivAt_const (1 : ℂ) z)
  change HasDerivAt (fun w : ℂ => (q.sum w) 1)
    (((q.derivSeries.sum z) 1) 1) z
  simpa [scalarFirstValue, scalarSecondValue, p, q] using heval.hasDerivAt

def scalarFirstCoeff (u : ℕ → ℂ) (j : ℕ) : ℂ :=
  ((j + 1 : ℕ) : ℂ) * u (j + 1)

def scalarSecondCoeff (u : ℕ → ℂ) (j : ℕ) : ℂ :=
  ((j + 2 : ℕ) : ℂ) * ((j + 1 : ℕ) : ℂ) * u (j + 2)

/-- An exact formal Euler/log-forcing identity lifts to the corresponding analytic identity at
every point lying inside both scalar-series radii. -/
theorem analyticEulerLogPair_eq_zero_of_formal
    (a b c κ z : ℂ) (h u : ℕ → ℂ)
    (hzH : ‖z‖ₑ < (FormalMultilinearSeries.ofScalars ℂ h).radius)
    (hzU : ‖z‖ₑ < (FormalMultilinearSeries.ofScalars ℂ u).radius)
    (hformal :
      d4HypergeometricFormalEulerResidual a b c (PowerSeries.mk h) +
          PowerSeries.C κ * d4HypergeometricFormalLogForcing a b c
            (PowerSeries.mk u) = 0) :
    z ^ 2 * (1 - z) * scalarSecondValue h z +
        (c * z - (a + b + 1) * z ^ 2) * scalarFirstValue h z -
        a * b * z * (FormalMultilinearSeries.ofScalars ℂ h).sum z +
      κ * (2 * z * (1 - z) * scalarFirstValue u z +
        (c - 1 - (a + b) * z) *
          (FormalMultilinearSeries.ofScalars ℂ u).sum z) = 0 := by
  rcases scalarSeries_hasSum_value_first_second h z hzH with
    ⟨hH, hH1, hH2⟩
  rcases scalarSeries_hasSum_value_first_second u z hzU with
    ⟨hU, hU1, hU2⟩
  change HasSum (fun j => scalarFirstCoeff h j * z ^ j) (scalarFirstValue h z) at hH1
  change HasSum (fun j => scalarSecondCoeff h j * z ^ j) (scalarSecondValue h z) at hH2
  change HasSum (fun j => scalarFirstCoeff u j * z ^ j) (scalarFirstValue u z) at hU1
  have hzH2 := HasSum.shiftTwoCoefficient_mul_pow hH2
  have hz3H2 := HasSum.shiftOneCoefficient_mul_pow hzH2
  have hzH1 := HasSum.shiftOneCoefficient_mul_pow hH1
  have hz2H1 := HasSum.shiftTwoCoefficient_mul_pow hH1
  have hzH := HasSum.shiftOneCoefficient_mul_pow hH
  have hzU1 := HasSum.shiftOneCoefficient_mul_pow hU1
  have hz2U1 := HasSum.shiftTwoCoefficient_mul_pow hU1
  have hzU := HasSum.shiftOneCoefficient_mul_pow hU
  have hresH := (((hzH2.sub hz3H2).add (hzH1.mul_left c)).sub
    (hz2H1.mul_left (a + b + 1))).sub (hzH.mul_left (a * b))
  have hresU := (((hzU1.mul_left 2).sub (hz2U1.mul_left 2)).add
    (hU.mul_left (c - 1))).sub (hzU.mul_left (a + b))
  have hres := hresH.add (hresU.mul_left κ)
  have hterm :
      (fun j =>
        shiftOneCoefficient (shiftOneCoefficient (scalarSecondCoeff h)) j * z ^ j -
              shiftOneCoefficient
                (shiftOneCoefficient
                  (shiftOneCoefficient (scalarSecondCoeff h))) j * z ^ j +
            c * (shiftOneCoefficient (scalarFirstCoeff h) j * z ^ j) -
          (a + b + 1) *
            (shiftOneCoefficient (shiftOneCoefficient (scalarFirstCoeff h)) j * z ^ j) -
          a * b * (shiftOneCoefficient h j * z ^ j) +
          κ * (2 * (shiftOneCoefficient (scalarFirstCoeff u) j * z ^ j) -
              2 * (shiftOneCoefficient (shiftOneCoefficient (scalarFirstCoeff u)) j * z ^ j) +
              (c - 1) * (u j * z ^ j) -
              (a + b) * (shiftOneCoefficient u j * z ^ j))) =
        fun _ : ℕ => (0 : ℂ) := by
    funext j
    have hcoeff := congrArg (PowerSeries.coeff j) hformal
    rw [map_add, PowerSeries.coeff_C_mul, map_zero] at hcoeff
    cases j with
    | zero =>
        rw [d4HypergeometricFormalEulerResidual_coeff_zero,
          d4HypergeometricFormalLogForcing_coeff_zero,
          PowerSeries.coeff_mk] at hcoeff
        simp only [shiftOneCoefficient_zero, sub_zero, pow_zero, mul_one]
        simpa using hcoeff
    | succ j =>
        rw [d4HypergeometricFormalEulerResidual_coeff_succ,
          d4HypergeometricFormalLogForcing_coeff_succ] at hcoeff
        simp only [PowerSeries.coeff_mk] at hcoeff
        cases j with
        | zero =>
            simp [scalarFirstCoeff] at hcoeff ⊢
            linear_combination hcoeff * z
        | succ j =>
            cases j with
            | zero =>
                simp [scalarFirstCoeff, scalarSecondCoeff] at hcoeff ⊢
                linear_combination hcoeff * z ^ 2
            | succ j =>
                simp only [shiftOneCoefficient_succ, scalarFirstCoeff,
                  scalarSecondCoeff]
                push_cast at hcoeff ⊢
                ring_nf at hcoeff ⊢
                linear_combination hcoeff * z ^ (j + 3)
  rw [hterm] at hres
  have heq := hres.unique (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  linear_combination heq

def d4HypergeometricResonantCompanionAnalyticValue
    (N : ℕ) (a b z : ℂ) : ℂ :=
  (d4HypergeometricResonantCompanionAnalyticSeries N a b).sum z

def d4HypergeometricResonantCompanionAnalyticFirstDerivative
    (N : ℕ) (a b z : ℂ) : ℂ :=
  scalarFirstValue (d4HypergeometricResonantCompanionAnalyticCoefficient N a b) z

def d4HypergeometricResonantCompanionAnalyticSecondDerivative
    (N : ℕ) (a b z : ℂ) : ℂ :=
  scalarSecondValue (d4HypergeometricResonantCompanionAnalyticCoefficient N a b) z

def d4HypergeometricResonantRegularBranchValue
    (N : ℕ) (a b z : ℂ) : ℂ :=
  (d4HypergeometricResonantRegularBranchSeries N a b).sum z

def d4HypergeometricResonantRegularBranchFirstDerivative
    (N : ℕ) (a b z : ℂ) : ℂ :=
  scalarFirstValue (d4HypergeometricResonantRegularBranchCoefficient N a b) z

def d4HypergeometricResonantRegularBranchSecondDerivative
    (N : ℕ) (a b z : ℂ) : ℂ :=
  scalarSecondValue (d4HypergeometricResonantRegularBranchCoefficient N a b) z

theorem d4HypergeometricResonantRegularCoefficient_eq_formalCoefficient
    (N : ℕ) (a b : ℂ) (j : ℕ) :
    d4HypergeometricResonantRegularCoefficient N a b j =
      ordinaryHypergeometricFormalCoefficient
        (d4HypergeometricResonantShiftedA N a)
        (d4HypergeometricResonantShiftedA N b)
        (d4HypergeometricResonantShiftedC N) j := by
  simp [d4HypergeometricResonantRegularCoefficient,
    ordinaryHypergeometricFormalCoefficient,
    ordinaryHypergeometricCoefficient,
    d4HypergeometricResonantShiftedA, d4HypergeometricResonantShiftedC]

/-- The zero-prepended regular-branch series is exactly the shifted Gauss factor multiplied by its
Frobenius power. -/
theorem d4HypergeometricResonantRegularBranchValue_eq_pow_mul_factor
    (N : ℕ) (a b z : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1) :
    d4HypergeometricResonantRegularBranchValue N a b z =
      z ^ (N + 1) * (d4HypergeometricResonantRegularFactorSeries N a b).sum z := by
  have hzfactor :
      ‖z‖ₑ < (d4HypergeometricResonantRegularFactorSeries N a b).radius := by
    rw [d4HypergeometricResonantRegularFactorSeries_radius_eq_one N a b ha hb]
    exact hz
  have hbase0 :=
    (ordinaryHypergeometric_hasSum_value_first_second
      (d4HypergeometricResonantShiftedA N a)
      (d4HypergeometricResonantShiftedA N b)
      (d4HypergeometricResonantShiftedC N) z hzfactor).1
  have hbase :
      HasSum
        (fun j => d4HypergeometricResonantRegularCoefficient N a b j * z ^ j)
        ((d4HypergeometricResonantRegularFactorSeries N a b).sum z) := by
    simpa only [d4HypergeometricResonantRegularFactorSeries,
      d4HypergeometricResonantRegularCoefficient_eq_formalCoefficient] using hbase0
  have hshift :
      HasSum
        (fun j => d4HypergeometricResonantRegularBranchCoefficient N a b
            (j + (N + 1)) * z ^ (j + (N + 1)))
        (z ^ (N + 1) *
          (d4HypergeometricResonantRegularFactorSeries N a b).sum z) := by
    have hmul := hbase.mul_left (z ^ (N + 1))
    have hterm (j : ℕ) :
        d4HypergeometricResonantRegularBranchCoefficient N a b
              (j + (N + 1)) * z ^ (j + (N + 1)) =
          z ^ (N + 1) *
            (d4HypergeometricResonantRegularCoefficient N a b j * z ^ j) := by
      rw [Nat.add_comm j (N + 1),
        d4HypergeometricResonantRegularBranchCoefficient_shift, pow_add]
      ring
    simpa only [hterm] using hmul
  have hfull0 :=
    (hasSum_nat_add_iff
      (f := fun j => d4HypergeometricResonantRegularBranchCoefficient N a b j * z ^ j)
      (N + 1)).mp hshift
  have hprefix :
      ∑ j ∈ Finset.range (N + 1),
          d4HypergeometricResonantRegularBranchCoefficient N a b j * z ^ j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    rw [d4HypergeometricResonantRegularBranchCoefficient_of_le N a b j (by omega)]
    simp
  rw [hprefix, add_zero] at hfull0
  have hzbranch :
      ‖z‖ₑ < (d4HypergeometricResonantRegularBranchSeries N a b).radius :=
    lt_of_lt_of_le hz
      (d4HypergeometricResonantRegularBranchSeries_radius_ge_one N a b ha hb)
  have hvalue :=
    (scalarSeries_hasSum_value_first_second
      (d4HypergeometricResonantRegularBranchCoefficient N a b) z
      (by simpa [d4HypergeometricResonantRegularBranchSeries] using hzbranch)).1
  exact hvalue.unique hfull0

theorem hasDerivAt_d4HypergeometricResonantCompanionAnalyticValue
    (N : ℕ) (a b z : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4HypergeometricResonantCompanionAnalyticValue N a b)
      (d4HypergeometricResonantCompanionAnalyticFirstDerivative N a b z) z := by
  apply hasDerivAt_scalarSeries_sum
  exact lt_of_lt_of_le hz
    (d4HypergeometricResonantCompanionAnalyticSeries_radius_ge_one N a b ha hb)

theorem hasDerivAt_d4HypergeometricResonantCompanionAnalyticFirstDerivative
    (N : ℕ) (a b z : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4HypergeometricResonantCompanionAnalyticFirstDerivative N a b)
      (d4HypergeometricResonantCompanionAnalyticSecondDerivative N a b z) z := by
  apply hasDerivAt_scalarFirstValue
  exact lt_of_lt_of_le hz
    (d4HypergeometricResonantCompanionAnalyticSeries_radius_ge_one N a b ha hb)

theorem hasDerivAt_d4HypergeometricResonantRegularBranchValue
    (N : ℕ) (a b z : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4HypergeometricResonantRegularBranchValue N a b)
      (d4HypergeometricResonantRegularBranchFirstDerivative N a b z) z := by
  apply hasDerivAt_scalarSeries_sum
  exact lt_of_lt_of_le hz
    (d4HypergeometricResonantRegularBranchSeries_radius_ge_one N a b ha hb)

theorem hasDerivAt_d4HypergeometricResonantRegularBranchFirstDerivative
    (N : ℕ) (a b z : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1) :
    HasDerivAt (d4HypergeometricResonantRegularBranchFirstDerivative N a b)
      (d4HypergeometricResonantRegularBranchSecondDerivative N a b z) z := by
  apply hasDerivAt_scalarFirstValue
  exact lt_of_lt_of_le hz
    (d4HypergeometricResonantRegularBranchSeries_radius_ge_one N a b ha hb)

/-- The normalized resonant analytic pair satisfies its exact inhomogeneous Euler equation on the
open unit disk. This is the analytic realization of the coefficientwise companion identity. -/
theorem d4HypergeometricResonantLogarithmicCompanion_analyticEulerEquation
    (N : ℕ) (a b z : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1) :
    z ^ 2 * (1 - z) *
          d4HypergeometricResonantCompanionAnalyticSecondDerivative N a b z +
        (-(N : ℂ) * z - (a + b + 1) * z ^ 2) *
          d4HypergeometricResonantCompanionAnalyticFirstDerivative N a b z -
        a * b * z * d4HypergeometricResonantCompanionAnalyticValue N a b z +
      d4HypergeometricResonantFrobeniusLogCoefficient N a b *
        (2 * z * (1 - z) *
            d4HypergeometricResonantRegularBranchFirstDerivative N a b z +
          (-(N : ℂ) - 1 - (a + b) * z) *
            d4HypergeometricResonantRegularBranchValue N a b z) = 0 := by
  have hzH :
      ‖z‖ₑ < (d4HypergeometricResonantCompanionAnalyticSeries N a b).radius :=
    lt_of_lt_of_le hz
      (d4HypergeometricResonantCompanionAnalyticSeries_radius_ge_one N a b ha hb)
  have hzU :
      ‖z‖ₑ < (d4HypergeometricResonantRegularBranchSeries N a b).radius :=
    lt_of_lt_of_le hz
      (d4HypergeometricResonantRegularBranchSeries_radius_ge_one N a b ha hb)
  have hformal := d4HypergeometricResonantLogarithmicCompanion_formalEquation
    N a b
    (d4Hypergeometric_add_order_add_ne_zero_of_shiftedA_re_pos N a ha)
    (d4Hypergeometric_add_order_add_ne_zero_of_shiftedA_re_pos N b hb)
  have h := analyticEulerLogPair_eq_zero_of_formal
    a b (-(N : ℂ)) (d4HypergeometricResonantFrobeniusLogCoefficient N a b) z
    (d4HypergeometricResonantCompanionAnalyticCoefficient N a b)
    (d4HypergeometricResonantRegularBranchCoefficient N a b)
    (by simpa [d4HypergeometricResonantCompanionAnalyticSeries] using hzH)
    (by simpa [d4HypergeometricResonantRegularBranchSeries] using hzU)
    (by simpa [d4HypergeometricResonantCompanionAnalyticFormalPowerSeries,
      d4HypergeometricResonantRegularBranchFormalPowerSeries] using hformal)
  simpa [d4HypergeometricResonantCompanionAnalyticValue,
    d4HypergeometricResonantCompanionAnalyticFirstDerivative,
    d4HypergeometricResonantCompanionAnalyticSecondDerivative,
    d4HypergeometricResonantRegularBranchValue,
    d4HypergeometricResonantRegularBranchFirstDerivative,
    d4HypergeometricResonantCompanionAnalyticSeries,
    d4HypergeometricResonantRegularBranchSeries] using h

/-- The regular logarithmic coefficient branch satisfies the homogeneous resonant Euler equation
throughout the open unit disk. -/
theorem d4HypergeometricResonantRegularBranch_analyticEulerEquation
    (N : ℕ) (a b z : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1) :
    z ^ 2 * (1 - z) *
          d4HypergeometricResonantRegularBranchSecondDerivative N a b z +
        (-(N : ℂ) * z - (a + b + 1) * z ^ 2) *
          d4HypergeometricResonantRegularBranchFirstDerivative N a b z -
      a * b * z * d4HypergeometricResonantRegularBranchValue N a b z = 0 := by
  have hzU :
      ‖z‖ₑ < (d4HypergeometricResonantRegularBranchSeries N a b).radius :=
    lt_of_lt_of_le hz
      (d4HypergeometricResonantRegularBranchSeries_radius_ge_one N a b ha hb)
  have hformal :=
    d4HypergeometricResonantRegularBranchFormalPowerSeries_residual_eq_zero N a b
  have h := analyticEulerLogPair_eq_zero_of_formal
    a b (-(N : ℂ)) 0 z
    (d4HypergeometricResonantRegularBranchCoefficient N a b)
    (d4HypergeometricResonantRegularBranchCoefficient N a b)
    (by simpa [d4HypergeometricResonantRegularBranchSeries] using hzU)
    (by simpa [d4HypergeometricResonantRegularBranchSeries] using hzU)
    (by simpa [d4HypergeometricResonantRegularBranchFormalPowerSeries] using hformal)
  simpa [d4HypergeometricResonantRegularBranchValue,
    d4HypergeometricResonantRegularBranchFirstDerivative,
    d4HypergeometricResonantRegularBranchSecondDerivative,
    d4HypergeometricResonantRegularBranchSeries] using h

/-- Principal-sheet value of the normalized logarithmic companion. -/
def d4HypergeometricResonantLogarithmicCompanionValue
    (N : ℕ) (a b : ℂ) : ℂ → ℂ :=
  d4HypergeometricResonantCompanionAnalyticValue N a b + fun z =>
    d4HypergeometricResonantFrobeniusLogCoefficient N a b *
      (d4HypergeometricResonantRegularBranchValue N a b * Complex.log) z

def d4HypergeometricResonantLogarithmicCompanionFirstDerivative
    (N : ℕ) (a b : ℂ) : ℂ → ℂ :=
  d4HypergeometricResonantCompanionAnalyticFirstDerivative N a b + fun z =>
    d4HypergeometricResonantFrobeniusLogCoefficient N a b *
      ((d4HypergeometricResonantRegularBranchFirstDerivative N a b * Complex.log) z +
        d4HypergeometricResonantRegularBranchValue N a b z * z⁻¹)

def d4HypergeometricResonantLogarithmicCompanionSecondDerivative
    (N : ℕ) (a b z : ℂ) : ℂ :=
  d4HypergeometricResonantCompanionAnalyticSecondDerivative N a b z +
    d4HypergeometricResonantFrobeniusLogCoefficient N a b *
      (d4HypergeometricResonantRegularBranchSecondDerivative N a b z * Complex.log z +
        d4HypergeometricResonantRegularBranchFirstDerivative N a b z * z⁻¹ +
        (d4HypergeometricResonantRegularBranchFirstDerivative N a b z * z⁻¹ +
          d4HypergeometricResonantRegularBranchValue N a b z * (-(z ^ 2)⁻¹)))

/-- Principal logarithmic companion differentiates to the explicit product-rule expression. -/
theorem hasDerivAt_d4HypergeometricResonantLogarithmicCompanionValue
    (N : ℕ) (a b z : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1) (hzslit : z ∈ Complex.slitPlane) :
    HasDerivAt (d4HypergeometricResonantLogarithmicCompanionValue N a b)
      (d4HypergeometricResonantLogarithmicCompanionFirstDerivative N a b z) z := by
  have hH := hasDerivAt_d4HypergeometricResonantCompanionAnalyticValue
    N a b z ha hb hz
  have hU := hasDerivAt_d4HypergeometricResonantRegularBranchValue
    N a b z ha hb hz
  have hlog := Complex.hasDerivAt_log hzslit
  have hprod := hU.mul hlog
  have hscaled := hprod.const_mul
    (d4HypergeometricResonantFrobeniusLogCoefficient N a b)
  exact hH.add hscaled

/-- Explicit first derivative of the principal companion differentiates to its second derivative. -/
theorem hasDerivAt_d4HypergeometricResonantLogarithmicCompanionFirstDerivative
    (N : ℕ) (a b z : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1) (hzslit : z ∈ Complex.slitPlane) :
    HasDerivAt (d4HypergeometricResonantLogarithmicCompanionFirstDerivative N a b)
      (d4HypergeometricResonantLogarithmicCompanionSecondDerivative N a b z) z := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp [Complex.slitPlane] at hzslit
  have hH := hasDerivAt_d4HypergeometricResonantCompanionAnalyticFirstDerivative
    N a b z ha hb hz
  have hU := hasDerivAt_d4HypergeometricResonantRegularBranchValue
    N a b z ha hb hz
  have hU1 := hasDerivAt_d4HypergeometricResonantRegularBranchFirstDerivative
    N a b z ha hb hz
  have hlog := Complex.hasDerivAt_log hzslit
  have hleft := hU1.mul hlog
  have hright := hU.mul (hasDerivAt_inv hz0)
  have hscaled := (hleft.add hright).const_mul
    (d4HypergeometricResonantFrobeniusLogCoefficient N a b)
  exact hH.add hscaled

/-- On the principal slit plane, the normalized logarithmic companion satisfies the homogeneous
resonant Gauss equation in Euler form. -/
theorem d4HypergeometricResonantLogarithmicCompanion_analyticEulerODE
    (N : ℕ) (a b z : ℂ)
    (ha : 0 < (d4HypergeometricResonantShiftedA N a).re)
    (hb : 0 < (d4HypergeometricResonantShiftedA N b).re)
    (hz : ‖z‖ₑ < 1) (hzslit : z ∈ Complex.slitPlane) :
    z ^ 2 * (1 - z) *
          d4HypergeometricResonantLogarithmicCompanionSecondDerivative N a b z +
        (-(N : ℂ) * z - (a + b + 1) * z ^ 2) *
          d4HypergeometricResonantLogarithmicCompanionFirstDerivative N a b z -
      a * b * z * d4HypergeometricResonantLogarithmicCompanionValue N a b z = 0 := by
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    simp [Complex.slitPlane] at hzslit
  have hpair := d4HypergeometricResonantLogarithmicCompanion_analyticEulerEquation
    N a b z ha hb hz
  have hregular := d4HypergeometricResonantRegularBranch_analyticEulerEquation
    N a b z ha hb hz
  calc
    _ =
        (z ^ 2 * (1 - z) *
              d4HypergeometricResonantCompanionAnalyticSecondDerivative N a b z +
            (-(N : ℂ) * z - (a + b + 1) * z ^ 2) *
              d4HypergeometricResonantCompanionAnalyticFirstDerivative N a b z -
            a * b * z * d4HypergeometricResonantCompanionAnalyticValue N a b z +
          d4HypergeometricResonantFrobeniusLogCoefficient N a b *
            (2 * z * (1 - z) *
                d4HypergeometricResonantRegularBranchFirstDerivative N a b z +
              (-(N : ℂ) - 1 - (a + b) * z) *
                d4HypergeometricResonantRegularBranchValue N a b z)) +
        d4HypergeometricResonantFrobeniusLogCoefficient N a b * Complex.log z *
          (z ^ 2 * (1 - z) *
                d4HypergeometricResonantRegularBranchSecondDerivative N a b z +
              (-(N : ℂ) * z - (a + b + 1) * z ^ 2) *
                d4HypergeometricResonantRegularBranchFirstDerivative N a b z -
            a * b * z * d4HypergeometricResonantRegularBranchValue N a b z) := by
      simp only [d4HypergeometricResonantLogarithmicCompanionValue,
        d4HypergeometricResonantLogarithmicCompanionFirstDerivative,
        d4HypergeometricResonantLogarithmicCompanionSecondDerivative,
        Pi.add_apply, Pi.mul_apply]
      field_simp [hz0]
      ring
    _ = 0 := by rw [hpair, hregular]; ring

/-- Companion value on an arbitrary logarithm sheet value at a fixed point. -/
def d4HypergeometricResonantLogarithmicCompanionOnSheet
    (N : ℕ) (a b z logSheet : ℂ) : ℂ :=
  d4HypergeometricResonantCompanionAnalyticValue N a b z +
    d4HypergeometricResonantFrobeniusLogCoefficient N a b *
      d4HypergeometricResonantRegularBranchValue N a b z * logSheet

/-- Exact deck jump: sheets differing by `2πi` differ by the normalized regular monodromy mode. -/
theorem d4HypergeometricResonantLogarithmicCompanionOnSheet_sub
    (N : ℕ) (a b z logPlus logMinus : ℂ)
    (hlog : logPlus - logMinus = 2 * Real.pi * Complex.I) :
    d4HypergeometricResonantLogarithmicCompanionOnSheet N a b z logPlus -
        d4HypergeometricResonantLogarithmicCompanionOnSheet N a b z logMinus =
      2 * Real.pi * Complex.I *
        d4HypergeometricResonantFrobeniusLogCoefficient N a b *
          d4HypergeometricResonantRegularBranchValue N a b z := by
  unfold d4HypergeometricResonantLogarithmicCompanionOnSheet
  linear_combination
    d4HypergeometricResonantFrobeniusLogCoefficient N a b *
      d4HypergeometricResonantRegularBranchValue N a b z * hlog

end
end RHTower
