import GaloisForLFunctions.RHTower.SoninAllPrimePositiveMomentWeldFrontier
import GaloisForLFunctions.RHTower.SoninCoupledPrimeArchGramTransfer
import GaloisForLFunctions.RHTower.ThetaCuspCassiniCalibratedReciprocalMomentNoGo

/-!
# Aperture lower floor forced by an all-prime Sonin moment weld

The all-prime residual has a quadratic Shannon-area ceiling at small aperture.  Its zeroth trace
moment therefore cannot approach the strictly positive normalized prime--archimedean zeroth
moment along a collapsing aperture section.  This gives a quantitative hostile test for the
proposed exact moment weld: every witnessing aperture sequence is eventually bounded away from
zero.

No Xi zero, RH premise, numerical computation, or unproved asymptotic is used.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

private def soninColumnEnergyEquiv :
    (Nat.Primes × ℕ) × (SoninHilbertIndex × SoninHilbertIndex) ≃
      SoninAllPrimeIndex × SoninHilbertIndex where
  toFun pji := ((pji.1, pji.2.2), pji.2.1)
  invFun z := (z.1.1, (z.2, z.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact energy disintegration of the coupled all-prime column into its prime-power blocks. -/
theorem hsNormSqRect_soninAllPrimeColumnKernel_eq_tsum_block
    (a : ℝ) (ha : 0 < a) :
    HilbertSchmidt.hsNormSqRect (soninAllPrimeColumnKernel a) =
      ∑' pk : Nat.Primes × ℕ,
        ContinuousLinearMap.hsNormSq
          (centralSoninWeightedPrimePowerResidual a pk) := by
  rw [HilbertSchmidt.hsNormSqRect]
  let F : (Nat.Primes × ℕ) × (SoninHilbertIndex × SoninHilbertIndex) → ℝ :=
    fun pji =>
      ‖inner ℂ (ContinuousLinearMap.hsBasis ℂ SoninL2 pji.2.2)
        (centralSoninWeightedPrimePowerResidual a pji.1
          (ContinuousLinearMap.hsBasis ℂ SoninL2 pji.2.1))‖ ^ 2
  have hF : Summable F := by
    simpa only [F] using summable_all_prime_residual_matrix_entries a ha
  calc
    (∑' z : SoninAllPrimeIndex × SoninHilbertIndex,
        ‖soninAllPrimeColumnKernel a z‖ ^ 2) =
        ∑' pji : (Nat.Primes × ℕ) ×
            (SoninHilbertIndex × SoninHilbertIndex), F pji := by
      symm
      exact soninColumnEnergyEquiv.tsum_eq
        (fun z => ‖soninAllPrimeColumnKernel a z‖ ^ 2)
    _ = ∑' pk : Nat.Primes × ℕ,
        ∑' ji : SoninHilbertIndex × SoninHilbertIndex, F (pk, ji) :=
      hF.tsum_prod
    _ = ∑' pk : Nat.Primes × ℕ,
        ContinuousLinearMap.hsNormSq
          (centralSoninWeightedPrimePowerResidual a pk) := by
      apply tsum_congr
      intro pk
      let T := centralSoninWeightedPrimePowerResidual a pk
      have hT : ContinuousLinearMap.IsHilbertSchmidt T :=
        centralSoninWeightedPrimePowerResidual_isHilbertSchmidt a ha pk
      rw [ContinuousLinearMap.hsNormSq_eq hT
        (ContinuousLinearMap.hsBasis ℂ SoninL2)]
      rw [show (∑' ji : SoninHilbertIndex × SoninHilbertIndex, F (pk, ji)) =
          ∑' j : SoninHilbertIndex, ∑' i : SoninHilbertIndex,
            F (pk, (j, i)) by
        have hFpk : Summable (fun ji : SoninHilbertIndex × SoninHilbertIndex =>
            F (pk, ji)) :=
          hF.comp_injective (fun _ _ h => (Prod.mk.inj h).2)
        exact hFpk.tsum_prod]
      apply tsum_congr
      intro j
      simpa only [F, T] using
        tsum_sq_norm_inner_hilbertBasis
          (ContinuousLinearMap.hsBasis ℂ SoninL2) (T
            (ContinuousLinearMap.hsBasis ℂ SoninL2 j))

/-- Quadratic Shannon-area ceiling for the zeroth intrinsic all-prime trace moment. -/
theorem re_soninAllPrimeEnergyMoment_zero_le_area
    (a : ℝ) (ha : 0 < a) :
    (soninAllPrimeEnergyMoment a 0).re ≤
      (128 * a ^ 2) * soninAllPrimeColumnWeightSqMass := by
  rw [soninAllPrimeEnergyMoment, HilbertSchmidt.hsPow,
    trace_soninAllPrimeResidualEnergyKernel a ha, Complex.ofReal_re]
  rw [← hsNormSqRect_soninAllPrimeColumnKernel_eq_residualKernel a ha,
    hsNormSqRect_soninAllPrimeColumnKernel_eq_tsum_block a ha]
  simpa [soninAllPrimeColumnWeightSqMass] using
    tsum_centralSoninWeightedPrimePowerResidual_hsNormSq_le_area a ha

/-- **Weld aperture lower floor.** Any exact Sonin moment coupling has a positive aperture floor.
The proof uses only its zeroth coordinate. -/
theorem soninPrimeArchSingleMomentCoupling_eventually_aperture_boundedBelow
    {aperture : ℕ → ℝ} (h : SoninPrimeArchSingleMomentCoupling aperture) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop, δ < aperture j := by
  let M : ℝ := soninAllPrimeColumnWeightSqMass
  let R : ℝ := 128 * M
  let δ : ℝ := Real.sqrt ((1 / 50 : ℝ) / R)
  have hM : 0 < M := soninAllPrimeColumnWeightSqMass_pos
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  have hratio : 0 < (1 / 50 : ℝ) / R := by positivity
  have hδ : 0 < δ := Real.sqrt_pos.2 hratio
  have htarget : (1 / 50 : ℝ) < normalizedPrimeArchMoment 0 := by
    have hfloor := one_div_twentyFive_lt_normalizedPrimeArchMoment_zero
    linarith
  have hreal : Tendsto
      (fun j => (soninAllPrimeEnergyMoment (aperture j) 0).re) atTop
      (nhds (normalizedPrimeArchMoment 0)) := by
    have hre := (Complex.continuous_re.tendsto
      (((normalizedPrimeArchMoment 0 : ℝ) : ℂ))).comp (h.2 0)
    change Tendsto
      (Complex.re ∘ fun j => soninAllPrimeEnergyMoment (aperture j) 0) atTop
      (nhds (normalizedPrimeArchMoment 0))
    exact hre
  have hevent : ∀ᶠ j in atTop,
      (1 / 50 : ℝ) < (soninAllPrimeEnergyMoment (aperture j) 0).re :=
    hreal.eventually (Ioi_mem_nhds htarget)
  refine ⟨δ, hδ, hevent.mono fun j hj => ?_⟩
  have harea := re_soninAllPrimeEnergyMoment_zero_le_area
    (aperture j) (h.1 j)
  have hbound : (1 / 50 : ℝ) < R * aperture j ^ 2 := by
    have hraw := hj.trans_le harea
    dsimp only [R, M]
    nlinarith
  have hδsq : δ ^ 2 = (1 / 50 : ℝ) / R := by
    dsimp only [δ]
    exact Real.sq_sqrt hratio.le
  have ha : 0 < aperture j := h.1 j
  have hscaled : δ ^ 2 < aperture j ^ 2 := by
    rw [hδsq]
    rw [div_lt_iff₀ hR]
    simpa [mul_comm] using hbound
  nlinarith [hδ.le, ha.le]

/-- A welding aperture section cannot converge to zero. -/
theorem soninPrimeArchSingleMomentCoupling_not_tendsto_aperture_zero
    {aperture : ℕ → ℝ} (h : SoninPrimeArchSingleMomentCoupling aperture) :
    ¬ Tendsto aperture atTop (nhds 0) := by
  intro hzero
  obtain ⟨δ, hδ, hfloor⟩ :=
    soninPrimeArchSingleMomentCoupling_eventually_aperture_boundedBelow h
  have hsmall : ∀ᶠ j in atTop, aperture j < δ :=
    hzero.eventually (Iio_mem_nhds hδ)
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hfloor.and hsmall)
  have hboth := hJ J le_rfl
  linarith [hboth.1, hboth.2]

/-- **Closed small-aperture weld no-go.** No aperture section can both realize the exact
all-prime/prime--archimedean moment coupling and collapse to zero. -/
theorem not_exists_soninPrimeArchSingleMomentCoupling_tendsto_aperture_zero :
    ¬ ∃ aperture : ℕ → ℝ,
      SoninPrimeArchSingleMomentCoupling aperture ∧
        Tendsto aperture atTop (nhds 0) := by
  rintro ⟨aperture, hcoupling, hzero⟩
  exact soninPrimeArchSingleMomentCoupling_not_tendsto_aperture_zero hcoupling hzero

/-- Every exact trace-moment weld therefore has a noncollapsing witnessing aperture section. -/
theorem soninAllPrimeExactTraceMomentWeld_has_aperture_lowerFloor
    (h : SoninAllPrimeExactTraceMomentWeld) :
    ∃ aperture : ℕ → ℝ, SoninPrimeArchSingleMomentCoupling aperture ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ j in atTop, δ < aperture j := by
  rw [soninAllPrimeExactTraceMomentWeld_iff_singleMomentCoupling] at h
  obtain ⟨aperture, haperture⟩ := h
  exact ⟨aperture, haperture,
    soninPrimeArchSingleMomentCoupling_eventually_aperture_boundedBelow haperture⟩

end

end RHTower
