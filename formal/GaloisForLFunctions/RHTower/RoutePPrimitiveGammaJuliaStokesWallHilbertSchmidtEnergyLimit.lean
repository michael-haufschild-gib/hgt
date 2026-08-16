import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallCubicCoherenceWeakLimit
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallExponentialCubicCoherenceValue

/-!
# P-G105U: exact SP-E Stokes-wall Hilbert--Schmidt energy limit

The literal cofinal child energy factors for every positive aperture as the square of the
oriented first-trace current times the normalized two-prime cubic-coherence expectation.  The
SP-E wall law converges to independent unit exponential clocks, whose exact coherence expectation
is `16/35`; since the current tends to `4`, the child Hilbert--Schmidt energy tends to `256/35`.

This is an exact source-faithful aperture-wall invariant.  It strengthens the previous positive
energy floor to a complete limit law, while leaving determinant convergence and Xi-divisor
identification as separate gates.
-/

open Complex Filter Topology Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

theorem wallCubicCoherence_logCoordinate_eq_primeLog
    {d : ℝ} (hd : 0 < d) (p q : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesWallCubicCoherence
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p)
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d q) =
      routePBaseCauchyCubicNormalizedCoherenceSq
        (Real.log (p : ℝ)) (Real.log (q : ℝ)) 0 := by
  have hlp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hlq : 0 < Real.log (q : ℝ) :=
    Real.log_pos (by exact_mod_cast q.property.one_lt)
  unfold routePPrimitiveGammaJuliaStokesWallCubicCoherence
    routePPrimitiveGammaJuliaStokesWallLogCoordinate
    routePBaseCauchyCubicNormalizedCoherenceSq
  norm_num
  field_simp [hd.ne', hlp.ne', hlq.ne', (add_pos hlp hlq).ne']

theorem integrable_wallCubicCoherence_prod_wallLaw (d : ℝ) :
    Integrable
      (fun z : ℝ × ℝ =>
        routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2)
      ((routePPrimitiveGammaJuliaStokesWallHalfLineLaw d).prod
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    measurable_wallCubicCoherence.aestronglyMeasurable ?_
  filter_upwards
    [GaloisForLFunctions.HTGeometry.ae_nonneg_fst_prod
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
      (wallHalfLineLaw_Iio_zero d),
     GaloisForLFunctions.HTGeometry.ae_nonneg_snd_prod
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)
      (wallHalfLineLaw_Iio_zero d)] with z hz1 hz2
  have h := wallCubicCoherence_zero_le_one hz1 hz2
  rw [Real.norm_eq_abs, abs_of_nonneg h.1]
  exact h.2

theorem integrable_wallCubicCoherence_right_wallRaw
    {d a : ℝ} (hd : 0 < d) (ha : 0 ≤ a) :
    Integrable
      (fun b : ℝ =>
        routePPrimitiveGammaJuliaStokesWallCubicCoherence a b)
      (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) := by
  letI := isProbabilityMeasure_wallHalfLineLawRaw hd
  refine Integrable.mono' (integrable_const (1 : ℝ)) ?_ ?_
  · exact (measurable_wallCubicCoherence.comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  · filter_upwards
      [GaloisForLFunctions.HTGeometry.ae_nonneg_of_Iio_zero
        (wallHalfLineLawRaw_Iio_zero hd)] with b hb
    have h := wallCubicCoherence_zero_le_one ha hb
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2

theorem summable_wallNormalizedCoherencePair
    {d : ℝ} (hd : 0 < d) :
    Summable (fun pq : Nat.Primes × Nat.Primes =>
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.1 *
        routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.2 *
        routePPrimitiveGammaJuliaStokesWallCubicCoherence
          (routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.1)
          (routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.2)) := by
  have hw := summable_wallNormalizedWeight hd
  have hmajor : Summable (fun pq : Nat.Primes × Nat.Primes =>
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.1 *
        routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.2) :=
    summable_mul_of_summable_norm hw.norm hw.norm
  refine Summable.of_nonneg_of_le (fun pq => ?_) (fun pq => ?_) hmajor
  · exact mul_nonneg
      (mul_nonneg (wallNormalizedWeight_nonneg hd _) (wallNormalizedWeight_nonneg hd _))
      (wallCubicCoherence_zero_le_one
        (wallLogCoordinate_pos hd _).le (wallLogCoordinate_pos hd _).le).1
  · exact mul_le_of_le_one_right
      (mul_nonneg (wallNormalizedWeight_nonneg hd _) (wallNormalizedWeight_nonneg hd _))
      (wallCubicCoherence_zero_le_one
        (wallLogCoordinate_pos hd _).le (wallLogCoordinate_pos hd _).le).2

theorem integral_wallCubicCoherence_prod_raw_eq_tsum
    {d : ℝ} (hd : 0 < d) :
    (∫ z : ℝ × ℝ,
      routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2
      ∂((routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d).prod
        (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d))) =
      ∑' pq : Nat.Primes × Nat.Primes,
        routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.1 *
          routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.2 *
          routePPrimitiveGammaJuliaStokesWallCubicCoherence
            (routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.1)
            (routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.2) := by
  letI := isProbabilityMeasure_wallHalfLineLawRaw hd
  have hprod : Integrable
      (fun z : ℝ × ℝ =>
        routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2)
      ((routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d).prod
        (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d)) := by
    have h := integrable_wallCubicCoherence_prod_wallLaw d
    rw [routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_pos hd] at h
    exact h
  have houter : Integrable
      (fun x : ℝ => ∫ y : ℝ,
        routePPrimitiveGammaJuliaStokesWallCubicCoherence x y
          ∂(routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d))
      (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) := by
    simpa only [Prod.fst, Prod.snd] using hprod.integral_prod_left
  rw [integral_prod _ hprod]
  rw [routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw]
  have houter' : Integrable
      (fun x : ℝ => ∫ y : ℝ,
        routePPrimitiveGammaJuliaStokesWallCubicCoherence x y
          ∂(GaloisForLFunctions.HTGeometry.weightedPointLaw
            (routePPrimitiveGammaJuliaStokesWallLogCoordinate d)
            (fun p : Nat.Primes => ENNReal.ofReal
              (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p))))
      (GaloisForLFunctions.HTGeometry.weightedPointLaw
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d)
        (fun p : Nat.Primes => ENNReal.ofReal
          (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p))) := by
    simpa only [routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw] using houter
  rw [GaloisForLFunctions.HTGeometry.integral_weightedPointLaw _ _ houter']
  have hpair := summable_wallNormalizedCoherencePair hd
  rw [hpair.tsum_prod]
  apply tsum_congr
  intro p
  rw [ENNReal.toReal_ofReal (wallNormalizedWeight_nonneg hd p)]
  have hinner : Integrable
      (fun b : ℝ => routePPrimitiveGammaJuliaStokesWallCubicCoherence
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p) b)
      (GaloisForLFunctions.HTGeometry.weightedPointLaw
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d)
        (fun q : Nat.Primes => ENNReal.ofReal
          (routePPrimitiveGammaJuliaStokesWallNormalizedWeight d q))) := by
    simpa only [routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw] using
      (integrable_wallCubicCoherence_right_wallRaw hd
        (wallLogCoordinate_pos hd p).le)
  rw [GaloisForLFunctions.HTGeometry.integral_weightedPointLaw _ _ hinner]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro q
  rw [ENNReal.toReal_ofReal (wallNormalizedWeight_nonneg hd q)]
  ring

theorem wallHilbertSchmidtEnergy_eq_current_sq_mul_expectation
    {d : ℝ} (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergy d =
      gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d ^ 2 *
        (∫ z : ℝ × ℝ,
          routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2
          ∂((routePPrimitiveGammaJuliaStokesWallHalfLineLaw d).prod
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d))) := by
  let W := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d
  let T := fun pq : Nat.Primes × Nat.Primes =>
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.1 *
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.2 *
      routePPrimitiveGammaJuliaStokesWallCubicCoherence
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.1)
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.2)
  have hW : 0 < W := gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd
  have hW0 : gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d ≠ 0 :=
    (gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_pos hd).ne'
  have hterm (pq : Nat.Primes × Nat.Primes) :
      Complex.normSq
          (routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq) =
        W ^ 2 * T pq := by
    rw [normSq_routePPrimitiveGammaJuliaStokesCofinalChildKernel hd,
      ← wallCubicCoherence_logCoordinate_eq_primeLog hd]
    dsimp [T, W]
    rw [routePPrimitiveGammaJuliaStokesWallNormalizedWeight,
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight]
    field_simp [hW0]
  rw [routePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergy]
  calc
    (∑' pq : Nat.Primes × Nat.Primes,
      Complex.normSq
        (routePPrimitiveGammaJuliaStokesCofinalChildKernel d pq)) =
        ∑' pq : Nat.Primes × Nat.Primes, W ^ 2 * T pq := tsum_congr hterm
    _ = W ^ 2 * (∑' pq : Nat.Primes × Nat.Primes, T pq) := by
      rw [tsum_mul_left]
    _ = W ^ 2 *
        (∫ z : ℝ × ℝ,
          routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2
          ∂((routePPrimitiveGammaJuliaStokesWallHalfLineLaw d).prod
            (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d))) := by
      rw [routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_pos hd,
        integral_wallCubicCoherence_prod_raw_eq_tsum hd]

theorem integral_wallCubicCoherence_exp_prod_eq :
    (∫ z : ℝ × ℝ,
      routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2
      ∂((expMeasure 1).prod (expMeasure 1))) = 16 / 35 := by
  calc
    (∫ z : ℝ × ℝ,
      routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2
      ∂((expMeasure 1).prod (expMeasure 1))) =
        ∫ z : ℝ × ℝ, routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence z.1 z.2
          ∂((expMeasure 1).prod (expMeasure 1)) := by
      apply integral_congr_ae
      filter_upwards with z
      unfold routePPrimitiveGammaJuliaStokesWallCubicCoherence
        routePBaseCauchyCubicNormalizedCoherenceSq routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence
      norm_num
      ring
    _ = 16 / 35 := integral_routePPrimitiveGammaJuliaStokesWallExponentialCubicCoherence_exp_prod_eq

theorem tendsto_wallCubicCoherenceExpectation_nhdsGT_zero :
    Tendsto
      (fun d : ℝ => ∫ z : ℝ × ℝ,
        routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2
        ∂((routePPrimitiveGammaJuliaStokesWallHalfLineLaw d).prod
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (16 / 35 : ℝ)) := by
  rw [← integral_wallCubicCoherence_exp_prod_eq]
  exact tendsto_integral_wallCubicCoherence_prod_nhdsGT_zero

theorem tendsto_wallHilbertSchmidtEnergy_nhdsGT_zero :
    Tendsto routePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergy
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (256 / 35 : ℝ)) := by
  have hW :=
    tendsto_gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent_nhdsGT_zero
  have hE := tendsto_wallCubicCoherenceExpectation_nhdsGT_zero
  have hprod := (hW.pow 2).mul hE
  have hlim : Tendsto
      (fun d : ℝ =>
        gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d ^ 2 *
          (∫ z : ℝ × ℝ,
            routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2
            ∂((routePPrimitiveGammaJuliaStokesWallHalfLineLaw d).prod
              (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d))))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (256 / 35 : ℝ)) := by
    convert hprod using 1 <;> norm_num
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  change 0 < d at hd
  exact (wallHilbertSchmidtEnergy_eq_current_sq_mul_expectation hd).symm

end

end RHTower

