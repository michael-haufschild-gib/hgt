import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.GroundFloorNoCrossing
import GaloisForLFunctions.SquareRootThreshold.TheContactApertureOfTheGroundEnergyPath
import GaloisForLFunctions.ArithmeticCriticalityTheory.ThreeTenthsSharpGaugeWeilPositivity

/-!
# The aperture floor transport from the certified endpoint

On the damping side the transport starts at an unconditionally admitted damping.  The aperture side
has the same shape, and it has its own unconditional endpoint: the ground energy of the restricted
Weil form is at least `1/5000` at the aperture `3/10`, by the all-profile window certificate.  What
is missing there is a transport theorem that does not differentiate the ground energy — the floor is
an infimum over a form domain, and the continuous no-crossing law of `GroundFloorNoCrossing`
assumes a derivative the aperture path is not known to have.

This module supplies the derivative-free transport.  Along any increasing sequence of apertures a
*per-step relative* loss transports the floor multiplicatively,

`μ_{j+1} ≥ (1 − c_j) μ_j`  ⟹  `μ_J ≥ μ_0 ∏_{i<J} (1 − c_i) ≥ μ_0 (1 − Σ_{i<J} c_i)`,

so a total relative loss of at most one half keeps `μ_J ≥ μ_0/2` at every step
(`half_le_of_relative_decay_steps`).  With the certified endpoint this gives a criterion for the
Riemann hypothesis on the aperture face: a half-summable relative decay along an unbounded aperture
sequence forces the nonnegative-ground-energy apertures to be unbounded, which is RH
(`riemannHypothesis_of_groundEnergy_relative_step`), together with the explicit uniform floor
`1/10000` along the sequence (`groundEnergy_ge_of_relative_step`).

The summability is not a formality: the harmonic defect `c_j = 1/(j+2)` already drives the
transported product to zero (`tendsto_prod_one_sub_harmonic_zero`), exactly as unit multipliers
defeat the affine envelope on the damping side.
-/

open Set Filter Finset Topology RHTower
open GaloisForLFunctions.SquareRootThreshold GaloisForLFunctions.ArithmeticCriticalityTheory

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. Multiplicative transport of a floor, without derivatives -/

/-- **Per-step relative transport.**  A floor losing at most the factor `q_j` per step is bounded
below by the initial floor times the product of the factors. -/
theorem mul_prod_le_of_relative_step {μ q : ℕ → ℝ} (hq : ∀ j, 0 ≤ q j)
    (hstep : ∀ j, q j * μ j ≤ μ (j + 1)) (J : ℕ) :
    μ 0 * ∏ i ∈ range J, q i ≤ μ J := by
  induction J with
  | zero => simp
  | succ J ih =>
    have h1 : q J * (μ 0 * ∏ i ∈ range J, q i) ≤ q J * μ J :=
      mul_le_mul_of_nonneg_left ih (hq J)
    have h2 := hstep J
    rw [prod_range_succ]
    calc μ 0 * ((∏ i ∈ range J, q i) * q J) = q J * (μ 0 * ∏ i ∈ range J, q i) := by ring
      _ ≤ q J * μ J := h1
      _ ≤ μ (J + 1) := h2

/-- Weierstrass' inequality: the product of the factors `1 − c_i` is at least `1 − Σ c_i`. -/
theorem one_sub_sum_le_prod_one_sub {c : ℕ → ℝ} (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) (J : ℕ) :
    1 - ∑ i ∈ range J, c i ≤ ∏ i ∈ range J, (1 - c i) := by
  induction J with
  | zero => simp
  | succ J ih =>
    have hprod0 : 0 ≤ ∏ i ∈ range J, (1 - c i) :=
      prod_nonneg fun i _ => by linarith [hc1 i]
    have hsum0 : 0 ≤ ∑ i ∈ range J, c i := sum_nonneg fun i _ => hc0 i
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have hstep : (1 - c J) * (1 - ∑ i ∈ range J, c i) ≤ (1 - c J) * ∏ i ∈ range J, (1 - c i) :=
      mul_le_mul_of_nonneg_left ih (by linarith [hc1 J])
    nlinarith [hc0 J, hc1 J]

/-- **No crossing under a half-summable relative decay.**  The transported floor keeps half of the
initial floor at every step; no differentiability of the floor is used. -/
theorem half_le_of_relative_decay_steps {μ c : ℕ → ℝ} (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hcsum : ∀ J, ∑ i ∈ range J, c i ≤ 1 / 2) (hμ0 : 0 ≤ μ 0)
    (hstep : ∀ j, (1 - c j) * μ j ≤ μ (j + 1)) (J : ℕ) : μ 0 / 2 ≤ μ J := by
  have hprod := mul_prod_le_of_relative_step (q := fun j => 1 - c j)
    (fun j => by linarith [hc1 j]) hstep J
  have hw := one_sub_sum_le_prod_one_sub hc0 hc1 J
  have hhalf : (1 : ℝ) / 2 ≤ ∏ i ∈ range J, (1 - c i) := by
    linarith [hcsum J]
  have := mul_le_mul_of_nonneg_left hhalf hμ0
  linarith

/-- **Summability is not a formality.**  The harmonic defect `c_j = 1/(j+2)` drives the transported
product to zero, so no uniform floor survives it. -/
theorem prod_one_sub_harmonic_eq (J : ℕ) :
    (∏ i ∈ range J, (1 - 1 / ((i : ℝ) + 2))) = 1 / ((J : ℝ) + 1) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.prod_range_succ, ih]
    have h1 : ((J : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((J : ℝ) + 2) ≠ 0 := by positivity
    field_simp
    push_cast
    ring

theorem tendsto_prod_one_sub_harmonic_zero :
    Tendsto (fun J : ℕ => ∏ i ∈ range J, (1 - 1 / ((i : ℝ) + 2))) atTop (𝓝 0) := by
  have h : (fun J : ℕ => ∏ i ∈ range J, (1 - 1 / ((i : ℝ) + 2))) =
      fun J : ℕ => 1 / ((J : ℝ) + 1) :=
    funext prod_one_sub_harmonic_eq
  rw [h]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## §2. The aperture instance, from the certified endpoint -/

/-- **The transported aperture floor.**  Starting at an aperture below `3/10`, where the ground
energy is certified at least `1/5000`, a half-summable relative decay keeps the ground energy above
`1/10000` at every aperture of the sequence. -/
theorem groundEnergy_ge_of_relative_step {A : ℕ → SuzukiPositiveAperture} {c : ℕ → ℝ}
    (hA0 : (A 0).1 ≤ 3 / 10) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hcsum : ∀ J, ∑ i ∈ range J, c i ≤ 1 / 2)
    (hstep : ∀ j, (1 - c j) * ccmRestrictedWeilGroundEnergy (A j) ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1))) (J : ℕ) :
    1 / 10000 ≤ ccmRestrictedWeilGroundEnergy (A J) := by
  have hbase : 1 / 5000 ≤ ccmRestrictedWeilGroundEnergy (A 0) :=
    one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths hA0
  have h := half_le_of_relative_decay_steps (μ := fun j => ccmRestrictedWeilGroundEnergy (A j))
    hc0 hc1 hcsum (by linarith) hstep J
  linarith

/-- **The aperture criterion for the Riemann hypothesis.**  A half-summable relative per-step decay
of the ground energy along an unbounded aperture sequence, starting at the certified endpoint,
makes the nonnegative-ground-energy apertures unbounded — which is RH.  Nothing is differentiated:
the floor is only compared with its own previous value. -/
theorem riemannHypothesis_of_groundEnergy_relative_step {A : ℕ → SuzukiPositiveAperture}
    {c : ℕ → ℝ} (hA0 : (A 0).1 ≤ 3 / 10)
    (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hcsum : ∀ J, ∑ i ∈ range J, c i ≤ 1 / 2)
    (hstep : ∀ j, (1 - c j) * ccmRestrictedWeilGroundEnergy (A j) ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1))) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_not_bddAbove_groundEnergyNonnegApertures]
  rintro ⟨M, hM⟩
  obtain ⟨J, hJ⟩ := (hAtop.eventually_gt_atTop M).exists
  have hmem : (A J).1 ∈ groundEnergyNonnegApertures := by
    refine ⟨(A J).2, ?_⟩
    have h := groundEnergy_ge_of_relative_step hA0 hc0 hc1 hcsum hstep J
    have hcongr : ccmRestrictedWeilGroundEnergy ⟨(A J).1, (A J).2⟩ =
        ccmRestrictedWeilGroundEnergy (A J) := by
      congr 1
    rw [hcongr]
    linarith
  exact absurd (hM hmem) (not_le.mpr hJ)

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
