import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauBoundaryNoGo
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallAtomicFredholmLimit
import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesWallHilbertSchmidtEnergyLimit
import GaloisForLFunctions.RHTower.LowTemperatureCurvature

/-!
# Prime/Gamma Stokes-wall Xi tau cold-boundary no-go

At large positive aperture, the normalized prime/Gamma Stokes wall is a genuine prime-log Gibbs
state with unique ground label `p = 2`.  Tannery selection forces its prime-2 mass to one.  Hence
the cubic Stokes coherence tends to one and the scale-free logarithmic Fredholm two-jet tends to
`1/2`, while Xi remains below `9/80`.

Together with the wild-wall boundary-neighborhood obstruction, this excludes both ends of the
actual non-scalar aperture family.  Any scalar-rescaled match is confined to a bounded
intermediate aperture regime.  No RH assumption or target-fed parameter enters the proof.
-/

open Complex Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal NNReal Topology

namespace RHTower

noncomputable section

local instance : MeasurableSpace Nat.Primes := ⊤

private def coldPrimeTwo : Nat.Primes := ⟨2, Nat.prime_two⟩

private def primeGammaWallColdCoefficient (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) * (p : ℝ) ^ (-1 : ℝ)

private def primeGammaWallColdEnergy (p : Nat.Primes) : ℝ :=
  2 * Real.log (p : ℝ)

private def primeGammaWallColdTerm (d : ℝ) (p : Nat.Primes) : ℝ :=
  lowTemperatureMomentTerm primeGammaWallColdCoefficient primeGammaWallColdEnergy
    (2 * Real.log 2) 0 d p

private def primeGammaWallColdPartition (d : ℝ) : ℝ :=
  ∑' p : Nat.Primes, primeGammaWallColdTerm d p

private theorem log_two_le_prime_log (p : Nat.Primes) :
    Real.log 2 ≤ Real.log (p : ℝ) := by
  exact Real.strictMonoOn_log.monotoneOn (by norm_num)
    (by simpa only [mem_Ioi] using (by exact_mod_cast p.property.pos : (0 : ℝ) < (p : ℝ)))
    (by exact_mod_cast p.property.two_le)

private theorem coldEnergy_bottom (p : Nat.Primes) :
    2 * Real.log 2 ≤ primeGammaWallColdEnergy p := by
  dsimp [primeGammaWallColdEnergy]
  linarith [log_two_le_prime_log p]

private theorem coldEnergy_eq_bottom_iff (p : Nat.Primes) :
    primeGammaWallColdEnergy p = 2 * Real.log 2 ↔ p = coldPrimeTwo := by
  constructor
  · intro h
    have hlog : Real.log (p : ℝ) = Real.log 2 := by
      dsimp [primeGammaWallColdEnergy] at h
      linarith
    have hp : (p : ℝ) = 2 :=
      Real.strictMonoOn_log.injOn
        (by simpa only [mem_Ioi] using (by exact_mod_cast p.property.pos : (0 : ℝ) < (p : ℝ)))
        (by norm_num) hlog
    apply Subtype.ext
    exact_mod_cast hp
  · rintro rfl
    rfl

private theorem primeGammaWallColdTerm_eq_scaled_weight
    (d : ℝ) (p : Nat.Primes) :
    primeGammaWallColdTerm d p =
      Real.exp (2 * d * Real.log 2) * xiMassPrimeSquareEulerWeight d p := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  rw [xiMassPrimeSquareEulerWeight_eq, Real.rpow_def_of_pos hp]
  dsimp [primeGammaWallColdTerm, lowTemperatureMomentTerm,
    primeGammaWallColdCoefficient, primeGammaWallColdEnergy]
  rw [Real.rpow_def_of_pos hp]
  simp only [pow_zero, mul_one]
  calc
    Real.log (p : ℝ) * Real.exp (Real.log (p : ℝ) * -1) *
          Real.exp (-d * (2 * Real.log (p : ℝ) - 2 * Real.log 2)) =
        Real.log (p : ℝ) * Real.exp
          (Real.log (p : ℝ) * -1 +
            -d * (2 * Real.log (p : ℝ) - 2 * Real.log 2)) := by
      rw [Real.exp_add]
      ring
    _ = Real.log (p : ℝ) * Real.exp
          (2 * d * Real.log 2 + Real.log (p : ℝ) * -(1 + 2 * d)) := by
      congr 2
      ring
    _ = Real.exp (2 * d * Real.log 2) *
          (Real.log (p : ℝ) * Real.exp (Real.log (p : ℝ) * -(1 + 2 * d))) := by
      rw [Real.exp_add]
      ring

private theorem primeGammaWallColdTerm_two (d : ℝ) :
    primeGammaWallColdTerm d coldPrimeTwo = Real.log 2 / 2 := by
  dsimp [primeGammaWallColdTerm, lowTemperatureMomentTerm,
    primeGammaWallColdCoefficient, primeGammaWallColdEnergy, coldPrimeTwo]
  rw [Real.rpow_neg_one]
  norm_num
  ring

private theorem primeGammaWallColdTerm_norm_le_at_one
    {d : ℝ} (hd : 1 ≤ d) (p : Nat.Primes) :
    ‖primeGammaWallColdTerm d p‖ ≤ ‖primeGammaWallColdTerm 1 p‖ := by
  have hgap : 0 ≤ primeGammaWallColdEnergy p - 2 * Real.log 2 :=
    sub_nonneg.mpr (coldEnergy_bottom p)
  have hexp :
      Real.exp (-d * (primeGammaWallColdEnergy p - 2 * Real.log 2)) ≤
        Real.exp (-(primeGammaWallColdEnergy p - 2 * Real.log 2)) := by
    rw [Real.exp_le_exp]
    nlinarith
  dsimp only [primeGammaWallColdTerm, lowTemperatureMomentTerm]
  simp only [pow_zero, mul_one, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  gcongr

private theorem summable_primeGammaWallColdTerm_norm_at_one :
    Summable (fun p : Nat.Primes => ‖primeGammaWallColdTerm 1 p‖) := by
  have hs := (summable_xiMassPrimeSquareEulerWeight (by norm_num : (0 : ℝ) < 1)).norm
  have hscaled := hs.mul_left ‖Real.exp (2 * (1 : ℝ) * Real.log 2)‖
  apply hscaled.congr
  intro p
  rw [primeGammaWallColdTerm_eq_scaled_weight]
  simp only [norm_mul]

/-- Ground-state selection for the rescaled prime/Gamma wall partition. -/
theorem tendsto_primeGammaWallColdPartition_atTop :
    Tendsto primeGammaWallColdPartition atTop (𝓝 (Real.log 2 / 2)) := by
  let bound : Nat.Primes → ℝ := fun p => ‖primeGammaWallColdTerm 1 p‖
  have h := lowTemperatureMoment_tendsto
    primeGammaWallColdCoefficient primeGammaWallColdEnergy coldPrimeTwo
    (2 * Real.log 2) 0 bound coldEnergy_bottom coldEnergy_eq_bottom_iff
    (by simpa [bound] using summable_primeGammaWallColdTerm_norm_at_one)
    (by
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with d hd
      intro p
      exact primeGammaWallColdTerm_norm_le_at_one hd p)
  rw [show primeGammaWallColdCoefficient coldPrimeTwo * (2 * Real.log 2) ^ 0 =
      Real.log 2 / 2 by
    dsimp [primeGammaWallColdCoefficient, coldPrimeTwo]
    rw [Real.rpow_neg_one]
    norm_num
    ring] at h
  exact h

private theorem primeGammaWallColdPartition_eq_scaled_tsum
    {d : ℝ} (hd : 0 < d) :
    primeGammaWallColdPartition d =
      Real.exp (2 * d * Real.log 2) *
        ∑' p : Nat.Primes, xiMassPrimeSquareEulerWeight d p := by
  rw [primeGammaWallColdPartition,
    ← (summable_xiMassPrimeSquareEulerWeight hd).tsum_mul_left]
  exact tsum_congr (primeGammaWallColdTerm_eq_scaled_weight d)

private theorem wallNormalizedWeight_eq_xiMassPrimeSquareEulerWeight_div_tsum
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p =
      xiMassPrimeSquareEulerWeight d p /
        ∑' q : Nat.Primes, xiMassPrimeSquareEulerWeight d q := by
  have hcurrent : gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent d =
      (8 * d) * ∑' q : Nat.Primes, xiMassPrimeSquareEulerWeight d q := by
    rw [gammaSewnMobiusApertureStokesOrientedFirstTraceCurrent,
      ← (summable_xiMassPrimeSquareEulerWeight hd).tsum_mul_left]
    apply tsum_congr
    intro q
    simp [gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm, abs_of_pos hd]
  rw [routePPrimitiveGammaJuliaStokesWallNormalizedWeight,
    routePPrimitiveGammaJuliaStokesTransportedPrimeWeight_eq hd p,
    gammaSewnMobiusApertureStokesOrientedFirstTracePrimeTerm, abs_of_pos hd, hcurrent]
  field_simp [hd.ne']

private theorem wallNormalizedWeight_two_eq_cold_ratio
    {d : ℝ} (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight d coldPrimeTwo =
      (Real.log 2 / 2) / primeGammaWallColdPartition d := by
  rw [wallNormalizedWeight_eq_xiMassPrimeSquareEulerWeight_div_tsum hd,
    ← primeGammaWallColdTerm_two d,
    primeGammaWallColdTerm_eq_scaled_weight,
    primeGammaWallColdPartition_eq_scaled_tsum hd]
  field_simp [Real.exp_ne_zero]

/-- At the cold boundary, normalized wall mass condenses on the unique prime-2 Stokes label. -/
theorem tendsto_routePPrimitiveGammaJuliaStokesWallNormalizedWeight_two_atTop :
    Tendsto (fun d : ℝ =>
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d coldPrimeTwo)
      atTop (𝓝 1) := by
  have hlog : Real.log 2 / 2 ≠ 0 := by
    exact div_ne_zero (Real.log_pos (by norm_num)).ne' (by norm_num)
  have hconst : Tendsto (fun _ : ℝ => Real.log 2 / 2) atTop
      (𝓝 (Real.log 2 / 2)) := tendsto_const_nhds
  have hratio := hconst.div tendsto_primeGammaWallColdPartition_atTop hlog
  have hratio' : Tendsto (fun d : ℝ =>
      (Real.log 2 / 2) / primeGammaWallColdPartition d) atTop (𝓝 1) := by
    convert hratio using 1
    · funext d
      simp only [Pi.div_apply]
    · rw [div_self hlog]
  refine hratio'.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd
  exact (wallNormalizedWeight_two_eq_cold_ratio hd).symm

/-- Exact normalized cubic Stokes coherence of the finite prime/Gamma wall. -/
def routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation
    (d : ℝ) : ℝ :=
  ∫ z : ℝ × ℝ,
    routePPrimitiveGammaJuliaStokesWallCubicCoherence z.1 z.2
    ∂((routePPrimitiveGammaJuliaStokesWallHalfLineLaw d).prod
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d))

private theorem wallCubicCoherence_logCoordinate_diagonal
    {d : ℝ} (hd : 0 < d) (p : Nat.Primes) :
    routePPrimitiveGammaJuliaStokesWallCubicCoherence
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p)
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d p) = 1 := by
  have hx := wallLogCoordinate_pos hd p
  rw [routePPrimitiveGammaJuliaStokesWallCubicCoherence,
    routePBaseCauchyCubicNormalizedCoherenceSq]
  norm_num
  field_simp [hx.ne']
  ring

/-- The prime-2 diagonal mass is a pointwise lower bound for full Stokes coherence. -/
theorem wallNormalizedWeight_two_sq_le_primeGammaWallCoherenceExpectation
    {d : ℝ} (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight d coldPrimeTwo ^ 2 ≤
      routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d := by
  let T : Nat.Primes × Nat.Primes → ℝ := fun pq =>
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.1 *
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.2 *
      routePPrimitiveGammaJuliaStokesWallCubicCoherence
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.1)
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.2)
  have hT : Summable T := by
    simpa [T] using summable_wallNormalizedCoherencePair hd
  have hnonneg : ∀ pq, 0 ≤ T pq := by
    intro pq
    exact mul_nonneg
      (mul_nonneg (wallNormalizedWeight_nonneg hd _) (wallNormalizedWeight_nonneg hd _))
      (wallCubicCoherence_zero_le_one
        (wallLogCoordinate_pos hd _).le (wallLogCoordinate_pos hd _).le).1
  have hsingle : T (coldPrimeTwo, coldPrimeTwo) ≤ ∑' pq, T pq := by
    simpa using hT.sum_le_tsum { (coldPrimeTwo, coldPrimeTwo) }
      (fun pq hp => hnonneg pq)
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation,
    routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_pos hd,
    integral_wallCubicCoherence_prod_raw_eq_tsum hd]
  simpa [T, pow_two, wallCubicCoherence_logCoordinate_diagonal hd coldPrimeTwo]
    using hsingle

/-- Normalized Stokes coherence is at most one at every positive aperture. -/
theorem primeGammaWallCoherenceExpectation_le_one
    {d : ℝ} (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d ≤ 1 := by
  let T : Nat.Primes × Nat.Primes → ℝ := fun pq =>
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.1 *
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.2 *
      routePPrimitiveGammaJuliaStokesWallCubicCoherence
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.1)
        (routePPrimitiveGammaJuliaStokesWallLogCoordinate d pq.2)
  let W : Nat.Primes × Nat.Primes → ℝ := fun pq =>
    routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.1 *
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d pq.2
  have hw := summable_wallNormalizedWeight hd
  have hW : Summable W := by
    exact summable_mul_of_summable_norm hw.norm hw.norm
  have hT : Summable T := by
    simpa [T] using summable_wallNormalizedCoherencePair hd
  have hle : (∑' pq, T pq) ≤ ∑' pq, W pq := by
    exact Summable.tsum_le_tsum
      (fun pq => by
        exact mul_le_of_le_one_right
          (mul_nonneg (wallNormalizedWeight_nonneg hd _) (wallNormalizedWeight_nonneg hd _))
          (wallCubicCoherence_zero_le_one
            (wallLogCoordinate_pos hd _).le (wallLogCoordinate_pos hd _).le).2)
      hT hW
  have hfactor := tsum_mul_tsum_of_summable_norm hw.norm hw.norm
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation,
    routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_pos hd,
    integral_wallCubicCoherence_prod_raw_eq_tsum hd]
  calc
    (∑' pq, T pq) ≤ ∑' pq, W pq := hle
    _ = (∑' p, routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p) *
        ∑' p, routePPrimitiveGammaJuliaStokesWallNormalizedWeight d p := by
      simpa [W] using hfactor.symm
    _ = 1 := by rw [tsum_wallNormalizedWeight hd]; norm_num

/-- Cold prime-2 condensation forces full cubic Stokes coherence to one. -/
theorem tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation_atTop :
    Tendsto routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation
      atTop (𝓝 1) := by
  have hlower :=
    (tendsto_routePPrimitiveGammaJuliaStokesWallNormalizedWeight_two_atTop.pow 2)
  have hlower' : Tendsto (fun d : ℝ =>
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d coldPrimeTwo ^ 2)
      atTop (𝓝 1) := by simpa using hlower
  refine hlower'.squeeze' tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd
    exact wallNormalizedWeight_two_sq_le_primeGammaWallCoherenceExpectation hd
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd
    exact primeGammaWallCoherenceExpectation_le_one hd

private theorem primeLog_pos (p : Nat.Primes) : 0 < Real.log (p : ℝ) := by
  apply Real.log_pos
  exact_mod_cast p.property.one_lt

/-- The one-label Fredholm coefficient of every positive prime/Gamma wall is exactly one. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_one
    {d : ℝ} (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 = 1 := by
  rw [routePPrimitiveGammaJuliaStokesWallFredholmCoefficient,
    routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_pos hd,
    integral_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_eq_positive_pi_wallRaw hd 1,
    integral_routePPrimitiveGammaJuliaStokesWallPositive_pi_wallRaw_eq_primeFredholmIntegrand hd 1]
  norm_num [Nat.factorial_one]
  calc
    (∫ a : Fin 1 → Nat.Primes,
        routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand 1 a
        ∂(routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd 1).toMeasure) =
        ∫ _a : Fin 1 → Nat.Primes, (1 : ℂ)
          ∂(routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd 1).toMeasure := by
      apply integral_congr_ae
      filter_upwards with a
      rw [routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand,
        Matrix.det_fin_one]
      change (routePPrimitiveGammaJuliaStokesWallCubicKernel
        (Real.log (a 0 : ℝ)) (Real.log (a 0 : ℝ)) : ℂ) = 1
      norm_cast
      exact routePPrimitiveGammaJuliaStokesWallCubicKernel_diagonal (primeLog_pos (a 0))
    _ = 1 := by simp

private theorem primeFredholmIntegrand_two_eq_one_sub_coherence
    (a : Fin 2 → Nat.Primes) :
    routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand 2 a =
      ((1 - routePPrimitiveGammaJuliaStokesWallCubicCoherence
        (Real.log (a 0 : ℝ)) (Real.log (a 1 : ℝ)) : ℝ) : ℂ) := by
  rw [routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand, Matrix.det_fin_two]
  change
    (routePPrimitiveGammaJuliaStokesWallCubicKernel
        (Real.log (a 0 : ℝ)) (Real.log (a 0 : ℝ)) : ℂ) *
        routePPrimitiveGammaJuliaStokesWallCubicKernel
          (Real.log (a 1 : ℝ)) (Real.log (a 1 : ℝ)) -
      routePPrimitiveGammaJuliaStokesWallCubicKernel
          (Real.log (a 0 : ℝ)) (Real.log (a 1 : ℝ)) *
        routePPrimitiveGammaJuliaStokesWallCubicKernel
          (Real.log (a 1 : ℝ)) (Real.log (a 0 : ℝ)) = _
  rw [routePPrimitiveGammaJuliaStokesWallCubicKernel_diagonal (primeLog_pos (a 0)),
    routePPrimitiveGammaJuliaStokesWallCubicKernel_diagonal (primeLog_pos (a 1)),
    routePPrimitiveGammaJuliaStokesWallCubicKernel_symmetric
      (Real.log (a 1 : ℝ)) (Real.log (a 0 : ℝ))]
  norm_cast
  rw [show routePPrimitiveGammaJuliaStokesWallCubicKernel
        (Real.log (a 0 : ℝ)) (Real.log (a 1 : ℝ)) *
      routePPrimitiveGammaJuliaStokesWallCubicKernel
        (Real.log (a 0 : ℝ)) (Real.log (a 1 : ℝ)) =
      routePPrimitiveGammaJuliaStokesWallCubicKernel
        (Real.log (a 0 : ℝ)) (Real.log (a 1 : ℝ)) ^ 2 by ring,
    routePPrimitiveGammaJuliaStokesWallCubicKernel_sq
      (primeLog_pos (a 0)).le (primeLog_pos (a 1)).le]
  norm_num

private theorem integral_primeTuplePMF_cubicCoherence_eq_expectation
    {d : ℝ} (hd : 0 < d) :
    (∫ a : Fin 2 → Nat.Primes,
      routePPrimitiveGammaJuliaStokesWallCubicCoherence
        (Real.log (a 0 : ℝ)) (Real.log (a 1 : ℝ))
      ∂(routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd 2).toMeasure) =
      routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d := by
  letI : IsProbabilityMeasure
      (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) :=
    isProbabilityMeasure_wallHalfLineLawRaw hd
  let W : (Fin 2 → Nat.Primes) → (Fin 2 → ℝ) := fun a i =>
    routePPrimitiveGammaJuliaStokesWallLogCoordinate d (a i)
  let C : (Fin 2 → ℝ) → ℝ := fun y =>
    routePPrimitiveGammaJuliaStokesWallCubicCoherence (y 0) (y 1)
  have hW : Measurable W := measurable_of_countable _
  have hC : StronglyMeasurable C := by
    exact (measurable_wallCubicCoherence.comp
      MeasurableEquiv.finTwoArrow.measurable).stronglyMeasurable
  have hmap :
      (∫ a : Fin 2 → Nat.Primes, C (W a)
        ∂(routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd 2).toMeasure) =
      ∫ y : Fin 2 → ℝ, C y
        ∂Measure.pi (fun _ : Fin 2 =>
          routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) := by
    rw [← map_routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF_wallLogCoordinate hd 2]
    exact (integral_map_of_stronglyMeasurable hW hC).symm
  have hpair :=
    (measurePreserving_finTwoArrow
      (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d)).integral_comp'
        (fun pq : ℝ × ℝ =>
          routePPrimitiveGammaJuliaStokesWallCubicCoherence pq.1 pq.2)
  calc
    (∫ a : Fin 2 → Nat.Primes,
      routePPrimitiveGammaJuliaStokesWallCubicCoherence
        (Real.log (a 0 : ℝ)) (Real.log (a 1 : ℝ))
      ∂(routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd 2).toMeasure) =
        ∫ a : Fin 2 → Nat.Primes, C (W a)
          ∂(routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd 2).toMeasure := by
      apply integral_congr_ae
      filter_upwards with a
      dsimp [C, W]
      rw [wallCubicCoherence_logCoordinate_eq_primeLog hd]
      rfl
    _ = ∫ y : Fin 2 → ℝ, C y
        ∂Measure.pi (fun _ : Fin 2 =>
          routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d) := hmap
    _ = ∫ pq : ℝ × ℝ, routePPrimitiveGammaJuliaStokesWallCubicCoherence pq.1 pq.2
        ∂((routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d).prod
          (routePPrimitiveGammaJuliaStokesWallHalfLineLawRaw d)) := by
      simpa [C] using hpair
    _ = routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d := by
      rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation,
        routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_pos hd]

/-- The two-label coefficient is half the defect of exact cubic Stokes coherence. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_two
    {d : ℝ} (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 2 =
      ((1 - routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d) / 2 : ℝ) := by
  let μ := (routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd 2).toMeasure
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let C : (Fin 2 → Nat.Primes) → ℝ := fun a =>
    routePPrimitiveGammaJuliaStokesWallCubicCoherence
      (Real.log (a 0 : ℝ)) (Real.log (a 1 : ℝ))
  have hC_bound : ∀ a, ‖C a‖ ≤ 1 := by
    intro a
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact (wallCubicCoherence_zero_le_one
        (primeLog_pos (a 0)).le (primeLog_pos (a 1)).le).2
    · exact (wallCubicCoherence_zero_le_one
        (primeLog_pos (a 0)).le (primeLog_pos (a 1)).le).1
  have hC_int : Integrable C μ := by
    exact Integrable.of_bound (measurable_of_countable C).aestronglyMeasurable 1
      (Filter.Eventually.of_forall hC_bound)
  have hCC_int : Integrable (fun a => (C a : ℂ)) μ :=
    Complex.ofRealCLM.integrable_comp hC_int
  have hCC : (∫ a, (C a : ℂ) ∂μ) =
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d : ℂ) := by
    calc
      (∫ a, (C a : ℂ) ∂μ) = ((∫ a, C a ∂μ : ℝ) : ℂ) :=
        Complex.ofRealCLM.integral_comp_comm hC_int
      _ = (routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d : ℂ) := by
        rw [integral_primeTuplePMF_cubicCoherence_eq_expectation hd]
  rw [routePPrimitiveGammaJuliaStokesWallFredholmCoefficient,
    routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_pos hd,
    integral_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_eq_positive_pi_wallRaw hd 2,
    integral_routePPrimitiveGammaJuliaStokesWallPositive_pi_wallRaw_eq_primeFredholmIntegrand hd 2]
  norm_num [Nat.factorial_two]
  change (∫ a : Fin 2 → Nat.Primes,
      routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand 2 a ∂μ) =
        1 - (routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d : ℂ)
  calc
    (∫ a : Fin 2 → Nat.Primes,
      routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand 2 a ∂μ) =
        ∫ a : Fin 2 → Nat.Primes, ((1 - C a : ℝ) : ℂ) ∂μ := by
      apply integral_congr_ae
      filter_upwards with a
      exact primeFredholmIntegrand_two_eq_one_sub_coherence a
    _ = 1 - (routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d : ℂ) := by
      push_cast
      rw [integral_sub (integrable_const 1) hCC_int, integral_const, hCC]
      simp [μ]

/-- At positive aperture, projective Stokes curvature is exactly half cubic coherence. -/
theorem routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_eq_half_coherence
    {d : ℝ} (hd : 0 < d) :
    routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d =
      ((routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d / 2 : ℝ) : ℂ) := by
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet]
  change
    (routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 ^ 2 -
        2 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
          (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 2) /
      (2 * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 ^ 2) = _
  rw [routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_one hd,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_two hd]
  push_cast
  ring

/-- Cold prime condensation sends the scale-free wall jet to `1/2`. -/
theorem tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_atTop :
    Tendsto routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet
      atTop (𝓝 (1 / 2 : ℂ)) := by
  have hreal : Tendsto
      (fun d : ℝ =>
        routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation d / 2)
      atTop (𝓝 (1 / 2 : ℝ)) :=
    tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallCoherenceExpectation_atTop.div_const 2
  have hcomplex := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  norm_num at hcomplex
  refine hcomplex.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd
  exact (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_eq_half_coherence hd).symm

/-- Real part of the cold-wall projective jet converges to `1/2`. -/
theorem tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re_atTop :
    Tendsto (fun d : ℝ =>
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d).re)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have h := Complex.continuous_re.continuousAt.tendsto.comp
    tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_atTop
  norm_num at h
  simpa only [Function.comp_def] using h

/-- Sufficiently cold genuine prime/Gamma walls lie above Xi's projective bound. -/
theorem eventually_nine_div_eighty_lt_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re_atTop :
    ∀ᶠ d : ℝ in atTop,
      (9 / 80 : ℝ) <
        (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d).re := by
  exact (tendsto_order.1
    tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re_atTop).1
      (9 / 80 : ℝ) (by norm_num)

/-- No scalar irregular-time rescaling identifies Xi with any sufficiently cold prime/Gamma wall. -/
theorem eventually_not_routePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt_atTop :
    ∀ᶠ d : ℝ in atTop,
      ¬ RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauScalarRescalingAt d := by
  filter_upwards
    [eventually_nine_div_eighty_lt_routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet_re_atTop]
      with d hgap
  rintro ⟨c, hgerm⟩
  have hfirst := hgerm.iteratedDeriv_eq 1
  rw [iteratedDeriv_canonicalXiSeamLog_one,
    iteratedDeriv_routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_one] at hfirst
  change (normalizedPrimeArchMoment 0 : ℂ) / 2 =
    c * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 at hfirst
  have hca : c * routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 ≠ 0 := by
    rw [← hfirst]
    exact div_ne_zero
      (Complex.ofReal_ne_zero.mpr normalizedPrimeArchMoment_zero_pos.ne') (by norm_num)
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hca).1
  have ha : routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
      (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) 1 ≠ 0 :=
    (mul_ne_zero_iff.mp hca).2
  have hprojective :
      routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet canonicalXiSeamLog =
        routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet
          (fun z => Complex.log
            (routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTau d c z)) := by
    unfold routePPrimitiveGammaJuliaStokesTauProjectiveLogTwoJet
    rw [hgerm.iteratedDeriv_eq 1, hgerm.iteratedDeriv_eq 2]
  rw [routePPrimitiveGammaJuliaStokes_canonicalXiSeamLog_projectiveTwoJet,
    routePPrimitiveGammaJuliaStokesPrimeGammaWallScaledTauLog_projectiveTwoJet hc ha]
      at hprojective
  have hre : normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 ^ 2 =
      (routePPrimitiveGammaJuliaStokesPrimeGammaWallProjectiveTwoJet d).re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re hprojective
  have hlt := normalizedPrimeArchMoment_projectiveTauJet_lt_nine_div_eighty
  rw [hre] at hlt
  linarith

end
end RHTower
