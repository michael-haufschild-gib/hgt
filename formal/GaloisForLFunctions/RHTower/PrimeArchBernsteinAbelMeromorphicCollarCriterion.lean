import GaloisForLFunctions.RHTower.PrimeArchBernsteinAbelSharpSelectionMaster

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- A source-side single-valued meromorphic realization of the susceptibility throughout the
unconditional narrow collar.  Agreement is required only with the interior real Abel germ. -/
def PrimeArchEndpointBernsteinAbelMeromorphicCollar : Prop :=
  ∀ R : ℝ, 250000 / 251001 < R → R < 1 →
    ∃ f : ℂ → ℂ, MeromorphicAt f R ∧
      (fun t : ℝ => f t) =ᶠ[nhdsWithin R (Set.Ico 0 R)]
        (fun t : ℝ =>
          (primeArchEndpointBernsteinAbelSusceptibility t : ℂ))

/-- **Meromorphic-collar RH criterion.**  A single-valued source-side meromorphic realization on
the explicit narrow collar forces the unique Abel radius to reach one, hence RH.  Isolated poles
of arbitrary integer order are allowed; false RH is excluded by the selected half-order parity
obstruction. -/
theorem riemannHypothesis_of_primeArchEndpointBernsteinAbelMeromorphicCollar
    (hcollar : PrimeArchEndpointBernsteinAbelMeromorphicCollar) :
    RiemannHypothesis := by
  by_contra hRH
  obtain ⟨D, B, beta, L, hB, hbeta1, hbeta, hDne, hD, hDsub,
      hL, hLpos, hboundaryPos, hcritical, hboundary, hblowup⟩ :=
    exists_exactRadius_positiveHalfOrder_primeArchEndpointBernsteinAbelBoundary_of_not_rh hRH
  obtain ⟨R, hR, hRunique⟩ := existsUnique_primeArchEndpointBernsteinAbelCriticalRadius
  have hReq : R = 1 / B ^ 2 :=
    primeArchEndpointBernsteinAbelCriticalRadius_unique hR.2.2.1 hcritical
  have hlower : (250000 / 251001 : ℝ) < 1 / B ^ 2 := by
    rw [← hReq]
    exact hR.1
  have hBsq : 1 < B ^ 2 := by nlinarith [sq_pos_of_pos (sub_pos.mpr hB)]
  have hupper : 1 / B ^ 2 < (1 : ℝ) := (div_lt_one (lt_trans zero_lt_one hBsq)).2 hBsq
  obtain ⟨f, hf, hagree⟩ := hcollar (1 / B ^ 2) hlower hupper
  exact
    GaloisForLFunctions.HTGeometry.false_of_meromorphicAt_of_positive_sqrt_scaled_boundary
      (lt_trans zero_lt_one hB) hboundaryPos hf hagree hboundary

/-- RH supplies a holomorphic, hence meromorphic, realization of the endpoint susceptibility
throughout the open unit disk.  The realization is the complex power series with the literal
endpoint-purity coefficients; its agreement with the real Abel germ is exact. -/
theorem primeArchEndpointBernsteinAbelMeromorphicCollar_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    PrimeArchEndpointBernsteinAbelMeromorphicCollar := by
  intro R hRlower hRupper
  let c : ℕ → ℂ := fun n => (primeArchEndpointBernsteinPurity n : ℂ)
  let p : FormalMultilinearSeries ℂ ℂ ℂ :=
    FormalMultilinearSeries.ofScalars ℂ c
  let r : ℝ := (R + 1) / 2
  have hRpos : 0 < R := by
    have : (0 : ℝ) < 250000 / 251001 := by norm_num
    linarith
  have hrpos : 0 < r := by
    dsimp only [r]
    linarith
  have hrone : r < 1 := by
    dsimp only [r]
    linarith
  let rNN : NNReal := ⟨r, hrpos.le⟩
  have hsum : Summable (fun n : ℕ => ‖p n‖ * (rNN : ℝ) ^ n) := by
    have hgeo : Summable (fun n : ℕ => r ^ n) :=
      summable_geometric_of_lt_one hrpos.le hrone
    refine Summable.of_nonneg_of_le
      (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg hrpos.le n))
      (fun n => ?_) (hgeo.mul_left (normalizedPrimeArchMoment 0 ^ 2))
    have hbound :=
      primeArchEndpointBernsteinPurity_le_mass_sq_of_riemannHypothesis hRH n
    have hcoeffnonneg : 0 ≤ primeArchEndpointBernsteinPurity n :=
      bernsteinCoefficientPurity_nonneg _ n
    have hpow : 0 ≤ r ^ n := pow_nonneg hrpos.le n
    dsimp only [p, c, rNN]
    rw [FormalMultilinearSeries.ofScalars_norm]
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg hcoeffnonneg]
    exact mul_le_mul_of_nonneg_right hbound hpow
  have hradius : (rNN : ENNReal) ≤ p.radius :=
    p.le_radius_of_summable_norm hsum
  have hRr : R < r := by
    dsimp only [r]
    linarith
  have hmem : (R : ℂ) ∈ Metric.eball 0 p.radius := by
    rw [mem_eball_zero_iff]
    have hnorm : ‖(R : ℂ)‖₊ = ⟨R, hRpos.le⟩ := by
      apply NNReal.eq
      change ‖(R : ℂ)‖ = R
      rw [norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
    rw [enorm_eq_nnnorm, hnorm]
    exact (ENNReal.coe_lt_coe.mpr hRr).trans_le hradius
  refine ⟨p.sum, (p.analyticOnNhd (R : ℂ) hmem).meromorphicAt, ?_⟩
  filter_upwards with t
  dsimp only [p, c]
  change FormalMultilinearSeries.ofScalarsSum
      (fun n => (primeArchEndpointBernsteinPurity n : ℂ)) (t : ℂ) = _
  rw [FormalMultilinearSeries.ofScalars_sum_eq,
    primeArchEndpointBernsteinAbelSusceptibility, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  simp

/-- **Exact meromorphic-collar RH law.**  The collar is no longer a one-way source interface:
it is precisely equivalent to RH. -/
theorem primeArchEndpointBernsteinAbelMeromorphicCollar_iff_riemannHypothesis :
    PrimeArchEndpointBernsteinAbelMeromorphicCollar ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_primeArchEndpointBernsteinAbelMeromorphicCollar,
    primeArchEndpointBernsteinAbelMeromorphicCollar_of_riemannHypothesis⟩

end

end RHTower
