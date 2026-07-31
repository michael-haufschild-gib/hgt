import GaloisForLFunctions.RHTower.VonMangoldtGammaFiniteJetOrientation
import GaloisForLFunctions.HTGeometry.MomentFunctionalPositivity

/-!
# A fixed bivariate moment kernel for the von Mangoldt--Gamma anomaly

Taylor's integral remainder turns every reversed finite Gamma-anomaly coordinate into a mixed
moment of two positive variables: the source rate and a unit-interval remainder parameter.  The
kernel does not depend on the jet depth.  Consequently the separate depth packets are triangular
slices of one source-defined bivariate moment array rather than unrelated positive cones.

This is an unconditional source producer.  It does not identify the resulting positive moment
functional with the completed Xi-divisor or endpoint Hausdorff functional; that comparison remains
the orientation bottleneck.
-/

open scoped BigOperators
open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Integral form of the oriented remainder of the exponential Taylor polynomial. -/
theorem expNegOrientedRemainder_eq_unitIntervalIntegral
    {m : ℕ} (hm : 0 < m) {rate : ℝ} (hrate : 0 < rate) :
    expNegOrientedRemainder m rate =
      rate ^ m / ((m - 1).factorial : ℝ) *
        ∫ u in (0 : ℝ)..1, u ^ (m - 1) * Real.exp (-rate * (1 - u)) := by
  let n := m - 1
  have hnm : n + 1 = m := by
    dsimp [n]
    omega
  have ht := taylor_integral_remainder
    (f := fun y : ℝ => Real.exp (-y)) (x := rate) (x₀ := 0) (n := n)
    (by fun_prop : ContDiffOn ℝ (n + 1 : ℕ)
      (fun y : ℝ => Real.exp (-y)) (uIcc 0 rate))
  rw [taylorWithinEval_exp_neg_eq_expNegTruncPoly hrate n] at ht
  simp only [smul_eq_mul] at ht
  have hderiv :
      (∫ t : ℝ in 0..rate,
          ((rate - t) ^ n / (n.factorial : ℝ)) *
            iteratedDerivWithin (n + 1) (fun y : ℝ => Real.exp (-y))
              (uIcc 0 rate) t) =
        ∫ t : ℝ in 0..rate,
          ((rate - t) ^ n / (n.factorial : ℝ)) *
            ((-1 : ℝ) ^ (n + 1) * Real.exp (-t)) := by
    apply intervalIntegral.integral_congr
    intro t htmem
    rw [uIcc_of_le hrate.le]
    dsimp only
    rw [iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc hrate) contDiff_exp_neg.contDiffAt
      (by simpa [uIcc_of_le hrate.le] using htmem)]
    rw [iteratedDeriv_exp_neg]
  rw [hderiv] at ht
  have hbase :
      expNegOrientedRemainder m rate =
        ∫ t : ℝ in 0..rate,
          (rate - t) ^ n / (n.factorial : ℝ) * Real.exp (-t) := by
    rw [expNegOrientedRemainder]
    rw [← hnm]
    have hpair : ((-1 : ℝ) ^ (n + 1)) * ((-1 : ℝ) ^ (n + 1)) = 1 := by
      rw [← pow_add]
      exact Even.neg_one_pow (Even.add_self (n + 1))
    have ht' :
        Real.exp (-rate) - (expNegTruncPoly (n + 1)).eval rate =
          (-1 : ℝ) ^ (n + 1) *
            ∫ t : ℝ in 0..rate,
              (rate - t) ^ n / (n.factorial : ℝ) * Real.exp (-t) := by
      rw [ht]
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    calc
      (-1 : ℝ) ^ (n + 1 + 1) *
          ((expNegTruncPoly (n + 1)).eval rate - Real.exp (-rate)) =
        (-1 : ℝ) ^ (n + 2) *
          (-((-1 : ℝ) ^ (n + 1) *
            ∫ t : ℝ in 0..rate,
              (rate - t) ^ n / (n.factorial : ℝ) * Real.exp (-t))) := by
          rw [show n + 1 + 1 = n + 2 by omega, ← ht']
          ring
      _ = ∫ t : ℝ in 0..rate,
          (rate - t) ^ n / (n.factorial : ℝ) * Real.exp (-t) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        calc
          (-1 : ℝ) ^ (n + 1) * -1 *
              -((-1 : ℝ) ^ (n + 1) *
                ∫ t : ℝ in 0..rate,
                  (rate - t) ^ n / (n.factorial : ℝ) * Real.exp (-t)) =
            (((-1 : ℝ) ^ (n + 1)) * ((-1 : ℝ) ^ (n + 1))) *
              ∫ t : ℝ in 0..rate,
                (rate - t) ^ n / (n.factorial : ℝ) * Real.exp (-t) := by ring
          _ = _ := by rw [hpair, one_mul]
  rw [hbase]
  have hreflect := intervalIntegral.integral_comp_sub_left
    (f := fun v : ℝ => v ^ n / (n.factorial : ℝ) * Real.exp (-(rate - v)))
    (a := 0) (b := rate) rate
  simp only [sub_zero, sub_self] at hreflect
  have hreflect' :
      (∫ t : ℝ in 0..rate,
          (rate - t) ^ n / (n.factorial : ℝ) * Real.exp (-t)) =
        ∫ v : ℝ in 0..rate,
          v ^ n / (n.factorial : ℝ) * Real.exp (-(rate - v)) := by
    convert hreflect using 1
    ring_nf
  have hscale := intervalIntegral.mul_integral_comp_mul_right
    (f := fun v : ℝ => v ^ n / (n.factorial : ℝ) * Real.exp (-(rate - v)))
    (a := 0) (b := 1) rate
  norm_num at hscale
  have hscale' :
      rate * (∫ u : ℝ in 0..1,
          (rate * u) ^ n / (n.factorial : ℝ) * Real.exp (-rate * (1 - u))) =
        ∫ v : ℝ in 0..rate,
          v ^ n / (n.factorial : ℝ) * Real.exp (-(rate - v)) := by
    calc
      rate * (∫ u : ℝ in 0..1,
          (rate * u) ^ n / (n.factorial : ℝ) * Real.exp (-rate * (1 - u))) =
        rate * (∫ u : ℝ in 0..1,
          (u * rate) ^ n / (n.factorial : ℝ) * Real.exp (u * rate - rate)) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro u _
            ring
      _ = ∫ v : ℝ in 0..rate,
          v ^ n / (n.factorial : ℝ) * Real.exp (v - rate) := hscale
      _ = ∫ v : ℝ in 0..rate,
          v ^ n / (n.factorial : ℝ) * Real.exp (-(rate - v)) := by
            apply intervalIntegral.integral_congr
            intro v _
            ring
  rw [hreflect', ← hscale']
  rw [← hnm]
  calc
    rate * (∫ u : ℝ in 0..1,
        (rate * u) ^ n / (n.factorial : ℝ) * Real.exp (-rate * (1 - u))) =
      rate * (∫ u : ℝ in 0..1,
        (rate ^ n / (n.factorial : ℝ)) *
          (u ^ n * Real.exp (-rate * (1 - u)))) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro u _
            dsimp only
            rw [mul_pow]
            ring
    _ = (rate * (rate ^ n / (n.factorial : ℝ))) *
        ∫ u : ℝ in 0..1, u ^ n * Real.exp (-rate * (1 - u)) := by
          rw [intervalIntegral.integral_const_mul]
          ring
    _ = rate ^ (n + 1) / (n.factorial : ℝ) *
        ∫ u : ℝ in 0..1, u ^ n * Real.exp (-rate * (1 - u)) := by
          rw [pow_succ]
          ring

/-- Reversed coordinate `r` in a depth-`N` Gamma-anomaly jet. -/
def gammaAnomalyReverseIndex (N r : ℕ) (hr : r < N) : Fin N :=
  ⟨N - 1 - r, by omega⟩

/-- The bivariate source moment with rate exponent `a` and unit-interval exponent `b`. -/
def finiteExponentialGammaBivariateMoment
    {P : Type*} [Fintype P] (weight rate : P → ℝ) (x : ℝ) (a b : ℕ) : ℝ :=
  ∑ p : P, weight p * Real.exp (-x * rate p) * rate p ^ a *
    ∫ u in (0 : ℝ)..1, u ^ b * Real.exp (-rate p * (1 - u))

/-- A reversed singleton anomaly coordinate is exactly a mixed moment of the fixed kernel. -/
theorem singleton_reverseGammaAnomaly_eq_bivariateMoment
    (weight rate x : ℝ) (hrate : 0 < rate)
    (N r : ℕ) (hr : r < N) :
    (r.factorial : ℝ) * (-1 : ℝ) ^ (N + 1) *
        (finiteExponentialGammaAnomaly
          (fun _ : Fin 1 ↦ (weight : ℂ))
          (fun _ : Fin 1 ↦ (rate : ℂ)) (x : ℂ) N
          (fun _ ↦ 1) (gammaAnomalyReverseIndex N r hr)).re =
      weight * Real.exp (-x * rate) * rate ^ N *
        ∫ u in (0 : ℝ)..1, u ^ r * Real.exp (-rate * (1 - u)) := by
  rw [mul_assoc, finiteExponentialGammaAnomaly_singleton_oriented_re_eq]
  have hresidual : N - (gammaAnomalyReverseIndex N r hr : ℕ) = r + 1 := by
    simp only [gammaAnomalyReverseIndex]
    omega
  rw [hresidual, expNegOrientedRemainder_eq_unitIntervalIntegral
    (by omega) hrate]
  simp only [Nat.add_sub_cancel]
  have hindex : (gammaAnomalyReverseIndex N r hr : ℕ) + (r + 1) = N := by
    simp only [gammaAnomalyReverseIndex]
    omega
  have hfac : (r.factorial : ℝ) ≠ 0 := by positivity
  have hpow :
      rate ^ (gammaAnomalyReverseIndex N r hr : ℕ) * rate ^ (r + 1) =
        rate ^ N := by
    rw [← pow_add, hindex]
  field_simp
  calc
    weight * rate ^ (gammaAnomalyReverseIndex N r hr : ℕ) * rate ^ (r + 1) *
        ∫ u in (0 : ℝ)..1, u ^ r * Real.exp (-(rate * (1 - u))) =
      weight *
        (rate ^ (gammaAnomalyReverseIndex N r hr : ℕ) * rate ^ (r + 1)) *
          ∫ u in (0 : ℝ)..1, u ^ r * Real.exp (-(rate * (1 - u))) := by ring
    _ = _ := by rw [hpow]; ring

/-- The complete finite real-source anomaly is the corresponding bivariate moment. -/
theorem finiteExponentialGammaAnomaly_reverse_eq_bivariateMoment
    {P : Type*} [Fintype P] (weight rate : P → ℝ) (x : ℝ)
    (hrate : ∀ p, 0 < rate p) (N r : ℕ) (hr : r < N) :
    (r.factorial : ℝ) * (-1 : ℝ) ^ (N + 1) *
        (finiteExponentialGammaAnomaly
          (fun p ↦ (weight p : ℂ)) (fun p ↦ (rate p : ℂ))
          (x : ℂ) N (fun _ ↦ 1) (gammaAnomalyReverseIndex N r hr)).re =
      finiteExponentialGammaBivariateMoment weight rate x N r := by
  rw [finiteExponentialGammaAnomaly_real_apply_eq_sum_singleton]
  rw [← Complex.reCLM_apply, map_sum]
  change (r.factorial : ℝ) * (-1 : ℝ) ^ (N + 1) *
      ∑ p : P,
        (finiteExponentialGammaAnomaly
          (fun _ : Fin 1 ↦ (weight p : ℂ))
          (fun _ : Fin 1 ↦ (rate p : ℂ)) (x : ℂ) N
          (fun _ ↦ 1) (gammaAnomalyReverseIndex N r hr)).re = _
  rw [finiteExponentialGammaBivariateMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  exact singleton_reverseGammaAnomaly_eq_bivariateMoment
    (weight p) (rate p) x (hrate p) N r hr

/-- Nonnegative source weights and positive rates make every mixed moment nonnegative. -/
theorem finiteExponentialGammaBivariateMoment_nonneg
    {P : Type*} [Fintype P] (weight rate : P → ℝ) (x : ℝ)
    (hweight : ∀ p, 0 ≤ weight p) (hrate : ∀ p, 0 < rate p)
    (a b : ℕ) :
    0 ≤ finiteExponentialGammaBivariateMoment weight rate x a b := by
  rw [finiteExponentialGammaBivariateMoment]
  apply Finset.sum_nonneg
  intro p hp
  have hint : 0 ≤ ∫ u in (0 : ℝ)..1,
      u ^ b * Real.exp (-rate p * (1 - u)) := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro u hu
    exact mul_nonneg (pow_nonneg hu.1 b) (Real.exp_pos _).le
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (hweight p) (Real.exp_pos _).le)
      (pow_nonneg (hrate p).le a)) hint

/-- The actual finite von Mangoldt source bivariate moment. -/
def finiteVonMangoldtGammaBivariateMoment
    (M : ℕ) (x : ℝ) (a b : ℕ) : ℝ :=
  finiteExponentialGammaBivariateMoment
    (fun p : Fin M ↦
      ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
    (fun p : Fin M ↦ Real.log ((p : ℕ) + 2)) x a b

/-- Every reversed coordinate of the finite von Mangoldt--Gamma anomaly belongs to the same fixed
bivariate moment array. -/
theorem finiteVonMangoldtGammaAnomaly_reverse_eq_bivariateMoment
    (M : ℕ) (x : ℝ) (N r : ℕ) (hr : r < N) :
    (r.factorial : ℝ) * (-1 : ℝ) ^ (N + 1) *
        (finiteVonMangoldtGammaAnomaly M (x : ℂ) N (fun _ ↦ 1)
          (gammaAnomalyReverseIndex N r hr)).re =
      finiteVonMangoldtGammaBivariateMoment M x N r := by
  rw [finiteVonMangoldtGammaAnomaly_apply_eq_sum_singleton]
  rw [← Complex.reCLM_apply, map_sum]
  change (r.factorial : ℝ) * (-1 : ℝ) ^ (N + 1) *
      ∑ p : Fin M,
        (finiteExponentialGammaAnomaly
          (fun _ : Fin 1 ↦
            ((ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2) : ℝ) : ℂ))
          (fun _ : Fin 1 ↦ (Real.log ((p : ℕ) + 2) : ℂ))
          (x : ℂ) N (fun _ ↦ 1) (gammaAnomalyReverseIndex N r hr)).re = _
  rw [finiteVonMangoldtGammaBivariateMoment,
    finiteExponentialGammaBivariateMoment, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  apply singleton_reverseGammaAnomaly_eq_bivariateMoment
  exact Real.log_pos (by exact_mod_cast (show 1 < (p : ℕ) + 2 by omega))

/-- Every entry of the finite von Mangoldt--Gamma bivariate moment array is nonnegative. -/
theorem finiteVonMangoldtGammaBivariateMoment_nonneg
    (M : ℕ) (x : ℝ) (a b : ℕ) :
    0 ≤ finiteVonMangoldtGammaBivariateMoment M x a b := by
  apply finiteExponentialGammaBivariateMoment_nonneg
  · intro p
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  · intro p
    exact Real.log_pos (by exact_mod_cast (show 1 < (p : ℕ) + 2 by omega))

/-! ### Canonical Hausdorff measures and Hankel positivity -/

/-- Positive density of one exponential Taylor-remainder channel on the unit interval. -/
def exponentialRemainderDensity (rate u : ℝ) : NNReal :=
  Real.toNNReal (Real.exp (-rate * (1 - u)))

/-- The compactly supported positive measure of one Taylor-remainder channel. -/
def exponentialRemainderMeasure (rate : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (0 : ℝ) 1)).withDensity
    (fun u ↦ exponentialRemainderDensity rate u)

/-- Monomials against the channel measure are exactly the unit-interval remainder moments. -/
theorem exponentialRemainderMeasure_moment (rate : ℝ) (b : ℕ) :
    (∫ u : ℝ, u ^ b ∂exponentialRemainderMeasure rate) =
      ∫ u in (0 : ℝ)..1, u ^ b * Real.exp (-rate * (1 - u)) := by
  rw [exponentialRemainderMeasure,
    integral_withDensity_eq_integral_smul (by
      unfold exponentialRemainderDensity
      fun_prop)]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  apply intervalIntegral.integral_congr
  intro u hu
  simp only [exponentialRemainderDensity, NNReal.smul_def,
    Real.coe_toNNReal _ (Real.exp_pos _).le]
  ring

theorem integrable_pow_exponentialRemainderMeasure (rate : ℝ) (b : ℕ) :
    Integrable (fun u : ℝ ↦ u ^ b) (exponentialRemainderMeasure rate) := by
  rw [exponentialRemainderMeasure,
    integrable_withDensity_iff_integrable_smul (by
      unfold exponentialRemainderDensity
      fun_prop)]
  have hint : IntervalIntegrable
      (fun u : ℝ ↦ exponentialRemainderDensity rate u • u ^ b) volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold exponentialRemainderDensity
    fun_prop
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp hint

/-- At fixed rate degree `a`, the bivariate source array is represented by this canonical positive
Hausdorff measure.  Varying `a` only size-biases the same source channels by `rate^a`. -/
def finiteExponentialGammaHausdorffMeasure
    {P : Type*} [Fintype P] (weight rate : P → ℝ) (x : ℝ) (a : ℕ) : Measure ℝ :=
  ∑ p : P, ENNReal.ofReal
      (weight p * Real.exp (-x * rate p) * rate p ^ a) •
        exponentialRemainderMeasure (rate p)

theorem integrable_pow_finiteExponentialGammaHausdorffMeasure
    {P : Type*} [Fintype P] (weight rate : P → ℝ) (x : ℝ) (a b : ℕ) :
    Integrable (fun u : ℝ ↦ u ^ b)
      (finiteExponentialGammaHausdorffMeasure weight rate x a) := by
  rw [finiteExponentialGammaHausdorffMeasure]
  apply integrable_finsetSum_measure.2
  intro p hp
  apply Integrable.smul_measure
    (integrable_pow_exponentialRemainderMeasure (rate p) b)
  exact ENNReal.ofReal_ne_top

/-- Representing-measure identity for every row of the fixed bivariate source moment array. -/
theorem finiteExponentialGammaBivariateMoment_eq_integral
    {P : Type*} [Fintype P] (weight rate : P → ℝ) (x : ℝ)
    (hweight : ∀ p, 0 ≤ weight p) (hrate : ∀ p, 0 < rate p)
    (a b : ℕ) :
    finiteExponentialGammaBivariateMoment weight rate x a b =
      ∫ u : ℝ, u ^ b ∂finiteExponentialGammaHausdorffMeasure weight rate x a := by
  rw [finiteExponentialGammaHausdorffMeasure]
  rw [integral_finsetSum_measure]
  · rw [finiteExponentialGammaBivariateMoment]
    apply Finset.sum_congr rfl
    intro p hp
    rw [integral_smul_measure, exponentialRemainderMeasure_moment]
    rw [ENNReal.toReal_ofReal]
    · rfl
    · exact mul_nonneg
        (mul_nonneg (hweight p) (Real.exp_pos _).le)
        (pow_nonneg (hrate p).le a)
  · intro p hp
    apply Integrable.smul_measure
      (integrable_pow_exponentialRemainderMeasure (rate p) b)
    exact ENNReal.ofReal_ne_top

/-- Every fixed-rate-degree row of the source array has positive-semidefinite Hankel matrices of
all finite sizes. -/
theorem finiteExponentialGammaBivariateMoment_hankel_posSemidef
    {P : Type*} [Fintype P] (weight rate : P → ℝ) (x : ℝ)
    (hweight : ∀ p, 0 ≤ weight p) (hrate : ∀ p, 0 < rate p)
    (a n : ℕ) :
    (Matrix.of fun i j : Fin n ↦
      finiteExponentialGammaBivariateMoment weight rate x a
        ((i : ℕ) + (j : ℕ))).PosSemidef := by
  apply HTGeometry.hankelMatrix_posSemidef
    (s := fun b ↦ finiteExponentialGammaBivariateMoment weight rate x a b)
    (finiteExponentialGammaBivariateMoment_eq_integral
      weight rate x hweight hrate a)
    (integrable_pow_finiteExponentialGammaHausdorffMeasure weight rate x a)

/-- The actual finite von Mangoldt--Gamma source therefore supplies an unconditional Hankel-positive
moment row at every source-rate degree and every finite matrix size. -/
theorem finiteVonMangoldtGammaBivariateMoment_hankel_posSemidef
    (M : ℕ) (x : ℝ) (a n : ℕ) :
    (Matrix.of fun i j : Fin n ↦
      finiteVonMangoldtGammaBivariateMoment M x a
        ((i : ℕ) + (j : ℕ))).PosSemidef := by
  apply finiteExponentialGammaBivariateMoment_hankel_posSemidef
  · intro p
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
  · intro p
    exact Real.log_pos (by exact_mod_cast (show 1 < (p : ℕ) + 2 by omega))

end

end RHTower
