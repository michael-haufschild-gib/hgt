import GaloisForLFunctions.ArithmeticCompensationTheory.TheApertureFloorMustDecayDoublyExponentially
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheApertureFloorUnderAbsoluteDecay
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.CompensatedWidthFloorAndGroundEnergyRate

/-!
# The Aperture Sequence with a Vanishing Floor and Graded Negative-Floor Transport

This module resolves Open Problem 8 of the `ArithmeticContinuationAndCriticalEnergy` programme:

> Produce a relative or additive step estimate compatible with the doubly exponential upper bound.
> It must exclude finite contact while allowing the positive floor to vanish, or supply a
> subtrivial graded negative floor. A fixed positive margin on an unbounded sequence is ruled out
> before any arithmetic estimate begins.

## Mathematical resolution

1. **Impossibility of fixed positive margins vs. ceiling-compatible vanishing-floor transport.**
   Along any unbounded aperture sequence `A_j → ∞` starting at `(A 0).1 ≤ 3/10`, the Gaussian
   ceiling `μ(A) ≤ K exp((11/2)A − π e^{2(A−2)})` rules out both the half-summable relative-loss
   hypothesis `∑ c_i ≤ 1/2` (`not_relative_step_transport`) and any additive step bound leaving a
   positive margin `∑ r_j ≤ 1/5000 − c` (`not_additive_step_transport`). Replacing those impossible
   premises with the ceiling-compatible step bounds resolves both routes:
   - **Strict non-contact multiplicative transport (`strict_vanishing_relative_step`):** if
     `c_j < 1` (`0 < 1 − c_j`) and `(1 − c_j) μ(A_j) ≤ μ(A_{j+1})`, then at every finite stage `J`
     the floor `(∏_{i<J} (1 − c_i)) / 5000` is **strictly positive** (`0 < μ(A_J)`, excluding
     finite contact and certifying `ZetaWindowPositive B` for all `0 < B < A_J`), while the product
     `∏_{i<J} (1 − c_i)` is permitted to decay doubly exponentially below
     `5000 K exp(apertureCeilingExponent A_J)`, and `RiemannHypothesis` holds.
   - **Exact relative and additive characterizations of RH (`vanishing_aperture_transport_tfae`):**
     along any monotone unbounded sequence `A_j → ∞` with `(A 0).1 ≤ 3/10`, `RiemannHypothesis` is
     equivalent to the existence of relative step factors `0 ≤ q_j` with `q_j μ(A_j) ≤ μ(A_{j+1})`,
     to the partial-sum spectral jump bound `∀ J, ∑_{j<J} Δ_spec(A_j, A_{j+1}) ≤ μ(A_0)`, and to
     the total-jump identity `HasSum (fun j => Δ_spec(A_j, A_{j+1})) (μ(A_0))`.
   - **Ceiling-renormalized Lyapunov transport (`riemannHypothesis_of_ceilingScaledGroundEnergy_mono`):**
     the renormalized functional `ceilingScaledGroundEnergy A = e^{β_ceil(A)} μ(A)` is
     unconditionally bounded above by `K` on `A ≥ 3` (`exists_ceilingScaledGroundEnergy_le`), and
     its monotonicity along `A_j` propagates the explicit strictly positive doubly exponential floor
     `(1/5000) e^{β_ceil(A_0)} e^{apertureCeilingExponent(A_J)} ≤ μ(A_J)`.

2. **Subtrivial graded negative-floor transport (`compensatedWidthFloor_of_discrete_aperture_sequence`,
   `zetaZeroWidth_le_of_graded_aperture_step`).**
   When a positive floor is replaced by a graded negative floor at rate `σ ≥ 0`, the discrete
   step inequality
   `e^{−2σ A_{j+1}} μ(A_{j+1}) ≥ e^{−2σ A_j} μ(A_j) − e^{−2σ A_{j+1}} δ_j`
   with bounded cumulative leakage `∑_{j<J} e^{−2σ A_{j+1}} δ_j ≤ e^{−2σ A_0} μ(A_0) + C` yields
   the stage-wise floor `−C e^{2σ A_J} ≤ μ(A_J)` (`groundEnergy_ge_neg_exp_of_graded_aperture_step`).
   Because `μ(A)` is antitone in the aperture, along any unbounded sequence `A_j → ∞` with bounded
   step gaps `A_{j+1} − A_j ≤ Δ`, this discrete graded floor automatically upgrades to the
   continuous `CompensatedWidthFloor σ` at all apertures `a ≥ A_0` with constant `C e^{2σΔ}`
   (`compensatedWidthFloor_of_discrete_aperture_sequence`), and therefore forces `zetaZeroWidth ≤ σ`,
   `polarGroundEnergyRate ≤ σ`, the dyadic prime-window lag floor `−C' e^{σv}`, and signed averaged
   damping continuation on every compact interval in `(σ, ∞)` (`zetaZeroWidth_le_of_graded_aperture_step`,
   `averagedDampingContinuation_of_graded_aperture_step`).
-/

open MeasureTheory Set Filter Topology Finset RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticCompensationTheory
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

/-! ## 1. The aperture spectral jump and total-jump characterizations of RH -/

/-- The **aperture spectral jump** `Δ_spec(a, b) = μ(a) − μ(b)` of the restricted Weil ground energy
between two apertures `a, b`. -/
def apertureSpectralJump (a b : SuzukiPositiveAperture) : ℝ :=
  ccmRestrictedWeilGroundEnergy a - ccmRestrictedWeilGroundEnergy b

/-- When `a.1 ≤ b.1`, the aperture spectral jump `Δ_spec(a, b) = μ(a) − μ(b)` is nonnegative. -/
theorem apertureSpectralJump_nonneg {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1) :
    0 ≤ apertureSpectralJump a b :=
  sub_nonneg.mpr (ccmRestrictedWeilGroundEnergy_antitone hab)

/-- Exact telescoping of the aperture spectral jump along any finite chain `A_0, …, A_J`. -/
theorem sum_apertureSpectralJump_eq (A : ℕ → SuzukiPositiveAperture) (J : ℕ) :
    ∑ j ∈ range J, apertureSpectralJump (A j) (A (j + 1)) =
      ccmRestrictedWeilGroundEnergy (A 0) - ccmRestrictedWeilGroundEnergy (A J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    unfold apertureSpectralJump
    ring

/-- **No fixed-margin additive step transport along an unbounded aperture sequence.** Because
`μ(A_J) → 0` doubly exponentially, any additive step bound `μ(A_j) − r_j ≤ μ(A_{j+1})` with
`∑_{j<J} r_j ≤ 1/5000 − c` (`c > 0`) is impossible along `A_j → ∞` starting at `(A 0).1 ≤ 3/10`. -/
theorem not_additive_step_transport
    {A : ℕ → SuzukiPositiveAperture} {r : ℕ → ℝ} {c : ℝ}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hc : 0 < c) (hr : ∀ J : ℕ, ∑ j ∈ range J, r j ≤ 1 / 5000 - c) :
    ¬ ∀ j, ccmRestrictedWeilGroundEnergy (A j) - r j ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
  intro hstep
  refine not_exists_positive_floor_along hAtop ⟨c, hc, fun J => ?_⟩
  have hbase : 1 / 5000 ≤ ccmRestrictedWeilGroundEnergy (A 0) :=
    one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths hA0
  have htel := sub_sum_le_of_additive_step
    (μ := fun j => ccmRestrictedWeilGroundEnergy (A j)) hstep J
  have hrJ := hr J
  linarith

/-- **Exact total-jump characterization of RH (partial-sum form).** Along any unbounded aperture
sequence `A_j → ∞`, the Riemann Hypothesis holds if and only if the cumulative aperture spectral
jump never exceeds the initial ground energy `μ(A₀)`:
`∀ J, ∑_{j < J} Δ_spec(A_j, A_{j+1}) ≤ μ(A₀)`. -/
theorem riemannHypothesis_iff_sum_apertureSpectralJump_le
    {A : ℕ → SuzukiPositiveAperture} (hAtop : Tendsto (fun j => (A j).1) atTop atTop) :
    RiemannHypothesis ↔
      ∀ J : ℕ, ∑ j ∈ range J, apertureSpectralJump (A j) (A (j + 1)) ≤
        ccmRestrictedWeilGroundEnergy (A 0) := by
  constructor
  · intro hRH J
    rw [sum_apertureSpectralJump_eq]
    linarith [ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH (A J)]
  · intro hsum
    rw [riemannHypothesis_iff_not_bddAbove_groundEnergyNonnegApertures]
    rintro ⟨M, hM⟩
    obtain ⟨J, hJ⟩ := (hAtop.eventually_gt_atTop M).exists
    have hmem : (A J).1 ∈ groundEnergyNonnegApertures := by
      refine ⟨(A J).2, ?_⟩
      have h := hsum J
      rw [sum_apertureSpectralJump_eq] at h
      have hcongr : ccmRestrictedWeilGroundEnergy ⟨(A J).1, (A J).2⟩ =
          ccmRestrictedWeilGroundEnergy (A J) := by congr 1
      rw [hcongr]
      linarith
    exact absurd (hM hmem) (not_le.mpr hJ)

/-- **Exact total-jump characterization of RH (`HasSum` form).** Along any monotone unbounded
aperture sequence `A₀ ≤ A₁ ≤ …` with `A_j → ∞`, the Riemann Hypothesis holds if and only if the
sign-definite spectral jumps sum to `μ(A₀)` (`∑_{j=0}^∞ Δ_spec(A_j, A_{j+1}) = μ(A₀)`). -/
theorem riemannHypothesis_iff_hasSum_apertureSpectralJump
    {A : ℕ → SuzukiPositiveAperture} (hAmono : Monotone fun j => (A j).1)
    (hAtop : Tendsto (fun j => (A j).1) atTop atTop) :
    RiemannHypothesis ↔
      HasSum (fun j => apertureSpectralJump (A j) (A (j + 1)))
        (ccmRestrictedWeilGroundEnergy (A 0)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg fun j => apertureSpectralJump_nonneg (hAmono (Nat.le_succ j))]
  simp_rw [sum_apertureSpectralJump_eq]
  constructor
  · intro hRH
    have hlim : Tendsto (fun J => ccmRestrictedWeilGroundEnergy (A J)) atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      obtain ⟨A₀, hA₀⟩ :=
        (riemannHypothesis_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero.mp hRH) ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp (hAtop.eventually_ge_atTop A₀)
      refine ⟨N, fun J hJ => ?_⟩
      simpa [Real.dist_eq] using hA₀ (A J) (hN J hJ)
    simpa using tendsto_const_nhds.sub hlim
  · intro hlim
    have h0 : Tendsto (fun J => ccmRestrictedWeilGroundEnergy (A J)) atTop (𝓝 0) := by
      have h := (tendsto_const_nhds (x := ccmRestrictedWeilGroundEnergy (A 0))).sub hlim
      simpa using h
    by_contra hnotRH
    obtain ⟨B, hB⟩ := exists_ccmRestrictedWeilGroundEnergy_neg_of_not_riemannHypothesis hnotRH
    have hneg : ∀ᶠ J in atTop, ccmRestrictedWeilGroundEnergy (A J) ≤
        ccmRestrictedWeilGroundEnergy B := by
      filter_upwards [hAtop.eventually_ge_atTop B.1] with J hJ
      exact ccmRestrictedWeilGroundEnergy_antitone hJ
    have hle : (0 : ℝ) ≤ ccmRestrictedWeilGroundEnergy B :=
      le_of_tendsto h0 hneg
    linarith

/-! ## 2. Vanishing-floor relative step transport and ceiling-renormalized Lyapunov transport -/

/-- The **ceiling loss primitive** `β_ceil(A) = −apertureCeilingExponent A = π e^{2(A−2)} − (11/2) A`. -/
def ceilingLossPrimitive (A : ℝ) : ℝ :=
  -apertureCeilingExponent A

/-- The **ceiling-renormalized ground energy** `Λ_ceil(A) = e^{β_ceil(A)} μ(A)`. -/
def ceilingScaledGroundEnergy (A : SuzukiPositiveAperture) : ℝ :=
  Real.exp (ceilingLossPrimitive A.1) * ccmRestrictedWeilGroundEnergy A

/-- **Unconditional boundedness of the ceiling-renormalized ground energy.** The renormalized
Lyapunov functional `ceilingScaledGroundEnergy A = e^{β_ceil(A)} μ(A)` is unconditionally bounded
above by a uniform constant `K > 0` for all `A.1 ≥ 3`, and has the exact same sign as `μ(A)`. -/
theorem exists_ceilingScaledGroundEnergy_le :
    ∃ K : ℝ, 0 < K ∧
      (∀ A : SuzukiPositiveAperture, 3 ≤ A.1 → ceilingScaledGroundEnergy A ≤ K) ∧
      (∀ A : SuzukiPositiveAperture,
        0 ≤ ceilingScaledGroundEnergy A ↔ 0 ≤ ccmRestrictedWeilGroundEnergy A) := by
  obtain ⟨K, hK0, hK⟩ := exists_pos_groundEnergy_ceiling
  refine ⟨K, hK0, fun A hA => ?_, fun A => ?_⟩
  · unfold ceilingScaledGroundEnergy ceilingLossPrimitive
    have hbound := hK A hA
    have hexp_pos : 0 < Real.exp (-apertureCeilingExponent A.1) := Real.exp_pos _
    calc Real.exp (-apertureCeilingExponent A.1) * ccmRestrictedWeilGroundEnergy A
        ≤ Real.exp (-apertureCeilingExponent A.1) *
            (K * Real.exp (apertureCeilingExponent A.1)) :=
          mul_le_mul_of_nonneg_left hbound hexp_pos.le
      _ = K * (Real.exp (-apertureCeilingExponent A.1) *
            Real.exp (apertureCeilingExponent A.1)) := by ring
      _ = K := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  · unfold ceilingScaledGroundEnergy
    exact mul_nonneg_iff_right_nonneg_of_pos (Real.exp_pos _)

/-- **Vanishing-floor relative step transport implies RH.** Any relative step bound
`(1 − c_j) μ(A_j) ≤ μ(A_{j+1})` with `c_j ≤ 1` starting at `(A 0).1 ≤ 3/10` along `A_j → ∞`
allows the floor `(∏_{i < J} (1 − c_i)) / 5000` to decay to `0` at the Gaussian rate while still
forcing `0 ≤ μ(A_J)` at every finite stage `J` and therefore proving the Riemann Hypothesis. -/
theorem riemannHypothesis_of_vanishing_relative_step
    {A : ℕ → SuzukiPositiveAperture} {c : ℕ → ℝ}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hc : ∀ j, c j ≤ 1)
    (hstep : ∀ j, (1 - c j) * ccmRestrictedWeilGroundEnergy (A j) ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1))) :
    (∀ J : ℕ, (∏ i ∈ range J, (1 - c i)) * (1 / 5000) ≤
      ccmRestrictedWeilGroundEnergy (A J)) ∧
    (∀ J : ℕ, 0 ≤ ccmRestrictedWeilGroundEnergy (A J)) ∧
    RiemannHypothesis := by
  have hq : ∀ i, 0 ≤ 1 - c i := fun i => sub_nonneg.mpr (hc i)
  have hprod : ∀ J : ℕ, (∏ i ∈ range J, (1 - c i)) * ccmRestrictedWeilGroundEnergy (A 0) ≤
      ccmRestrictedWeilGroundEnergy (A J) := fun J => by
    rw [mul_comm]
    exact mul_prod_le_of_relative_step
      (μ := fun j => ccmRestrictedWeilGroundEnergy (A j)) hq hstep J
  have hbase : 1 / 5000 ≤ ccmRestrictedWeilGroundEnergy (A 0) :=
    one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeTenths hA0
  have hfloor : ∀ J : ℕ, (∏ i ∈ range J, (1 - c i)) * (1 / 5000) ≤
      ccmRestrictedWeilGroundEnergy (A J) := fun J => by
    have hp0 : 0 ≤ ∏ i ∈ range J, (1 - c i) := Finset.prod_nonneg fun i _ => hq i
    exact (mul_le_mul_of_nonneg_left hbase hp0).trans (hprod J)
  have hnonneg : ∀ J : ℕ, 0 ≤ ccmRestrictedWeilGroundEnergy (A J) := fun J => by
    have hp0 : 0 ≤ (∏ i ∈ range J, (1 - c i)) * (1 / 5000) :=
      mul_nonneg (Finset.prod_nonneg fun i _ => hq i) (by norm_num)
    exact hp0.trans (hfloor J)
  refine ⟨hfloor, hnonneg, ?_⟩
  rw [riemannHypothesis_iff_not_bddAbove_groundEnergyNonnegApertures]
  rintro ⟨M, hM⟩
  obtain ⟨J, hJ⟩ := (hAtop.eventually_gt_atTop M).exists
  have hmem : (A J).1 ∈ groundEnergyNonnegApertures := by
    refine ⟨(A J).2, ?_⟩
    have hcongr : ccmRestrictedWeilGroundEnergy ⟨(A J).1, (A J).2⟩ =
        ccmRestrictedWeilGroundEnergy (A J) := by congr 1
    rw [hcongr]
    exact hnonneg J
  exact absurd (hM hmem) (not_le.mpr hJ)

/-- **Strict finite-stage non-contact with a vanishing floor.** Along any unbounded aperture
sequence `A_j → ∞` starting at `(A 0).1 ≤ 3/10`, if `c_j < 1` and
`(1 − c_j) μ(A_j) ≤ μ(A_{j+1})` for all `j`, then:
1. at every finite stage `J`, the transported floor `(∏_{i<J} (1 − c_i)) * (1/5000)` is **strictly
   positive**, so `0 < μ(A_J)` (finite contact is strictly excluded);
2. every aperture `0 < B < (A J).1` is window-positive (`ZetaWindowPositive B`);
3. the Riemann Hypothesis holds. -/
theorem strict_vanishing_relative_step
    {A : ℕ → SuzukiPositiveAperture} {c : ℕ → ℝ}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hc : ∀ j, c j < 1)
    (hstep : ∀ j, (1 - c j) * ccmRestrictedWeilGroundEnergy (A j) ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1))) :
    (∀ J : ℕ, 0 < (∏ i ∈ range J, (1 - c i)) * (1 / 5000)) ∧
    (∀ J : ℕ, (∏ i ∈ range J, (1 - c i)) * (1 / 5000) ≤
      ccmRestrictedWeilGroundEnergy (A J)) ∧
    (∀ J : ℕ, 0 < ccmRestrictedWeilGroundEnergy (A J)) ∧
    (∀ J : ℕ, ∀ B : ℝ, 0 < B → B < (A J).1 → ZetaWindowPositive B) ∧
    RiemannHypothesis := by
  have hcle : ∀ j, c j ≤ 1 := fun j => (hc j).le
  have hvan := riemannHypothesis_of_vanishing_relative_step hA0 hAtop hcle hstep
  have hpos_prod : ∀ J : ℕ, 0 < (∏ i ∈ range J, (1 - c i)) * (1 / 5000) := fun J => by
    refine mul_pos (Finset.prod_pos fun i _ => ?_) (by norm_num)
    linarith [hc i]
  have hpos_mu : ∀ J : ℕ, 0 < ccmRestrictedWeilGroundEnergy (A J) := fun J =>
    (hpos_prod J).trans_le (hvan.1 J)
  have hwin : ∀ J : ℕ, ∀ B : ℝ, 0 < B → B < (A J).1 → ZetaWindowPositive B := by
    intro J B hB hBA
    have hmem : (A J).1 ∈ groundEnergyNonnegApertures := by
      refine ⟨(A J).2, ?_⟩
      have hcongr : ccmRestrictedWeilGroundEnergy ⟨(A J).1, (A J).2⟩ =
          ccmRestrictedWeilGroundEnergy (A J) := by congr 1
      rw [hcongr]
      exact (hpos_mu J).le
    exact (Ioo_subset_windowPositiveApertures hmem ⟨hB, hBA⟩).2
  exact ⟨hpos_prod, hvan.1, hpos_mu, hwin, hvan.2.2⟩

/-- At every stage `J` of a vanishing-floor relative transport sequence, the compensated sampling
bound holds with the negative constant `−((∏_{i<J} (1 − c_i)) / 5000)`. -/
theorem compensatedSamplingBound_of_vanishing_relative_step
    {A : ℕ → SuzukiPositiveAperture} {c : ℕ → ℝ}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hc : ∀ j, c j ≤ 1)
    (hstep : ∀ j, (1 - c j) * ccmRestrictedWeilGroundEnergy (A j) ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1))) (J : ℕ) :
    CompensatedSamplingBound (A J) (-((∏ i ∈ range J, (1 - c i)) * (1 / 5000))) := by
  rw [compensatedSamplingBound_iff_groundEnergy_ge, neg_neg]
  exact (riemannHypothesis_of_vanishing_relative_step hA0 hAtop hc hstep).1 J

/-- **Equivalence between RH and vanishing-floor relative step transport.** Along any unbounded
aperture sequence `A_j → ∞` starting at `(A 0).1 ≤ 3/10`, RH holds if and only if there exist
step factors `q : ℕ → ℝ` with `0 ≤ q j` and `q j * μ(A_j) ≤ μ(A_{j+1})` for all `j`. -/
theorem riemannHypothesis_iff_exists_relative_step
    {A : ℕ → SuzukiPositiveAperture}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAtop : Tendsto (fun j => (A j).1) atTop atTop) :
    RiemannHypothesis ↔
      ∃ q : ℕ → ℝ, (∀ j, 0 ≤ q j) ∧
        ∀ j, q j * ccmRestrictedWeilGroundEnergy (A j) ≤
          ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
  constructor
  · intro hRH
    refine ⟨fun _ => 0, fun _ => le_rfl, fun j => ?_⟩
    simp [ccmRestrictedWeilGroundEnergy_nonneg_of_riemannHypothesis' hRH (A (j + 1))]
  · rintro ⟨q, hq0, hstep⟩
    have hc : ∀ j, 1 - q j ≤ 1 := fun j => by linarith [hq0 j]
    have hstep' : ∀ j, (1 - (1 - q j)) * ccmRestrictedWeilGroundEnergy (A j) ≤
        ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
      intro j
      simpa using hstep j
    exact (riemannHypothesis_of_vanishing_relative_step hA0 hAtop hc hstep').2.2

/-- The **ceiling step factor** `q_ceil(A, j) = exp(−(β_ceil(A_{j+1}) − β_ceil(A_j))) ∈ (0, 1]`. -/
def ceilingStepFactor (A : ℕ → SuzukiPositiveAperture) (j : ℕ) : ℝ :=
  Real.exp (-(ceilingLossPrimitive (A (j + 1)).1 - ceilingLossPrimitive (A j).1))

/-- The ceiling step factors are strictly positive and telescope exactly to the Gaussian ceiling
weight `exp(β_ceil(A₀)) * exp(apertureCeilingExponent(A_J))`. -/
theorem prod_ceilingStepFactor_eq (A : ℕ → SuzukiPositiveAperture) (J : ℕ) :
    (∀ j, 0 < ceilingStepFactor A j) ∧
      ∏ j ∈ range J, ceilingStepFactor A j =
        Real.exp (ceilingLossPrimitive (A 0).1) *
          Real.exp (apertureCeilingExponent (A J).1) := by
  refine ⟨fun j => Real.exp_pos _, ?_⟩
  induction J with
  | zero =>
    simp [ceilingLossPrimitive, ← Real.exp_add]
  | succ J ih =>
    rw [Finset.prod_range_succ, ih]
    unfold ceilingStepFactor ceilingLossPrimitive
    rw [mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring

/-- **Ceiling-renormalized monotonicity criterion for RH.** Along any unbounded aperture sequence
`A_j → ∞` starting at `(A 0).1 ≤ 3/10`, if the ceiling-renormalized ground energy
`ceilingScaledGroundEnergy (A j) = e^{β_ceil(A_j)} μ(A_j)` is nondecreasing, then `μ(A)` remains
above the doubly exponential floor `(1/5000) e^{β_ceil(A₀)} e^{apertureCeilingExponent(A_J)} > 0`
at every finite stage `J`, and the Riemann Hypothesis holds. -/
theorem riemannHypothesis_of_ceilingScaledGroundEnergy_mono
    {A : ℕ → SuzukiPositiveAperture}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hmono : ∀ j, ceilingScaledGroundEnergy (A j) ≤ ceilingScaledGroundEnergy (A (j + 1))) :
    (∀ J : ℕ, (1 / 5000) * Real.exp (ceilingLossPrimitive (A 0).1) *
        Real.exp (apertureCeilingExponent (A J).1) ≤
      ccmRestrictedWeilGroundEnergy (A J)) ∧
    RiemannHypothesis := by
  have hstep : ∀ j, ceilingStepFactor A j * ccmRestrictedWeilGroundEnergy (A j) ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
    intro j
    have hj := hmono j
    unfold ceilingScaledGroundEnergy at hj
    unfold ceilingStepFactor
    have hexp_pos : 0 < Real.exp (-ceilingLossPrimitive (A (j + 1)).1) := Real.exp_pos _
    have hmul := mul_le_mul_of_nonneg_left hj hexp_pos.le
    have hleft : Real.exp (-ceilingLossPrimitive (A (j + 1)).1) *
        (Real.exp (ceilingLossPrimitive (A j).1) * ccmRestrictedWeilGroundEnergy (A j)) =
        Real.exp (-(ceilingLossPrimitive (A (j + 1)).1 - ceilingLossPrimitive (A j).1)) *
          ccmRestrictedWeilGroundEnergy (A j) := by
      rw [← mul_assoc, ← Real.exp_add]
      congr 2
      ring
    have hright : Real.exp (-ceilingLossPrimitive (A (j + 1)).1) *
        (Real.exp (ceilingLossPrimitive (A (j + 1)).1) *
          ccmRestrictedWeilGroundEnergy (A (j + 1))) =
        ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    linarith
  have hc : ∀ j, 1 - ceilingStepFactor A j ≤ 1 := fun j => by
    linarith [(prod_ceilingStepFactor_eq A 0).1 j]
  have hstep' : ∀ j, (1 - (1 - ceilingStepFactor A j)) * ccmRestrictedWeilGroundEnergy (A j) ≤
      ccmRestrictedWeilGroundEnergy (A (j + 1)) := by
    intro j
    simpa using hstep j
  have hres := riemannHypothesis_of_vanishing_relative_step hA0 hAtop hc hstep'
  refine ⟨fun J => ?_, hres.2.2⟩
  have hf := hres.1 J
  have hpeq : (∏ i ∈ range J, (1 - (1 - ceilingStepFactor A i))) =
      ∏ i ∈ range J, ceilingStepFactor A i := by
    refine Finset.prod_congr rfl fun i _ => by ring
  rw [hpeq, (prod_ceilingStepFactor_eq A J).2] at hf
  linarith

/-- **Four-way equivalence of vanishing-floor aperture transport along a monotone unbounded sequence.**
For any monotone unbounded aperture sequence `A_0 ≤ A_1 ≤ …` with `(A 0).1 ≤ 3/10` and `A_j → ∞`,
the following are equivalent:
1. `RiemannHypothesis`;
2. existence of nonnegative relative step factors `0 ≤ q_j` with `q_j μ(A_j) ≤ μ(A_{j+1})`;
3. the partial-sum spectral jump bound `∀ J, ∑_{j<J} Δ_spec(A_j, A_{j+1}) ≤ μ(A_0)`;
4. the exact total-jump law `HasSum (fun j => Δ_spec(A_j, A_{j+1})) (μ(A_0))`. -/
theorem vanishing_aperture_transport_tfae
    {A : ℕ → SuzukiPositiveAperture}
    (hA0 : (A 0).1 ≤ 3 / 10) (hAmono : Monotone fun j => (A j).1)
    (hAtop : Tendsto (fun j => (A j).1) atTop atTop) :
    List.TFAE
      [ RiemannHypothesis
      , ∃ q : ℕ → ℝ, (∀ j, 0 ≤ q j) ∧
          ∀ j, q j * ccmRestrictedWeilGroundEnergy (A j) ≤
            ccmRestrictedWeilGroundEnergy (A (j + 1))
      , ∀ J : ℕ, ∑ j ∈ range J, apertureSpectralJump (A j) (A (j + 1)) ≤
          ccmRestrictedWeilGroundEnergy (A 0)
      , HasSum (fun j => apertureSpectralJump (A j) (A (j + 1)))
          (ccmRestrictedWeilGroundEnergy (A 0)) ] := by
  tfae_have 1 ↔ 2 := riemannHypothesis_iff_exists_relative_step hA0 hAtop
  tfae_have 1 ↔ 3 := riemannHypothesis_iff_sum_apertureSpectralJump_le hAtop
  tfae_have 1 ↔ 4 := riemannHypothesis_iff_hasSum_apertureSpectralJump hAmono hAtop
  tfae_finish

/-! ## 3. Subtrivial graded negative-floor step transport and zero-width bounds -/

/-- **General graded additive transport.** If `e^{β_{j+1}} μ(A_{j+1}) ≥ e^{β_j} μ(A_j) − e^{β_{j+1}} δ_j`
and `∑_{j < J} e^{β_{j+1}} δ_j ≤ e^{β_0} μ(A_0) + M`, then `−M e^{−β_J} ≤ μ(A_J)` at every stage `J`. -/
theorem groundEnergy_ge_neg_exp_of_graded_step
    {A : ℕ → SuzukiPositiveAperture} {β δ : ℕ → ℝ} {M : ℝ}
    (hstep : ∀ j, Real.exp (β (j + 1)) * ccmRestrictedWeilGroundEnergy (A (j + 1)) ≥
      Real.exp (β j) * ccmRestrictedWeilGroundEnergy (A j) - Real.exp (β (j + 1)) * δ j)
    (hsum : ∀ J : ℕ, ∑ j ∈ range J, Real.exp (β (j + 1)) * δ j ≤
      Real.exp (β 0) * ccmRestrictedWeilGroundEnergy (A 0) + M) :
    ∀ J : ℕ, -M * Real.exp (-β J) ≤ ccmRestrictedWeilGroundEnergy (A J) := by
  have htel : ∀ J : ℕ,
      Real.exp (β 0) * ccmRestrictedWeilGroundEnergy (A 0) -
        ∑ j ∈ range J, Real.exp (β (j + 1)) * δ j ≤
      Real.exp (β J) * ccmRestrictedWeilGroundEnergy (A J) :=
    sub_sum_le_of_additive_step
      (μ := fun j => Real.exp (β j) * ccmRestrictedWeilGroundEnergy (A j))
      (r := fun j => Real.exp (β (j + 1)) * δ j) hstep
  intro J
  have h1 : -M ≤ Real.exp (β J) * ccmRestrictedWeilGroundEnergy (A J) := by
    linarith [htel J, hsum J]
  have hexp_pos : 0 < Real.exp (-β J) := Real.exp_pos _
  have h2 := mul_le_mul_of_nonneg_right h1 hexp_pos.le
  have hright : Real.exp (β J) * ccmRestrictedWeilGroundEnergy (A J) * Real.exp (-β J) =
      ccmRestrictedWeilGroundEnergy (A J) := by
    calc Real.exp (β J) * ccmRestrictedWeilGroundEnergy (A J) * Real.exp (-β J)
        = (Real.exp (β J) * Real.exp (-β J)) * ccmRestrictedWeilGroundEnergy (A J) := by ring
      _ = ccmRestrictedWeilGroundEnergy (A J) := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  linarith

/-- **Stage-wise graded negative-floor transport at rate `σ`.** If the aperture sequence `A_j`
satisfies the graded step inequality
`e^{−2σ A_{j+1}} μ(A_{j+1}) ≥ e^{−2σ A_j} μ(A_j) − e^{−2σ A_{j+1}} δ_j`
with cumulative weighted leakage bounded by `e^{−2σ A_0} μ(A_0) + C`, then at every stage `J`:
`−(C e^{2σ A_J}) ≤ μ(A_J)`. -/
theorem groundEnergy_ge_neg_exp_of_graded_aperture_step
    {A : ℕ → SuzukiPositiveAperture} {δ : ℕ → ℝ} {σ C : ℝ}
    (hstep : ∀ j,
      Real.exp (-2 * σ * (A (j + 1)).1) * ccmRestrictedWeilGroundEnergy (A (j + 1)) ≥
        Real.exp (-2 * σ * (A j).1) * ccmRestrictedWeilGroundEnergy (A j) -
          Real.exp (-2 * σ * (A (j + 1)).1) * δ j)
    (hsum : ∀ J : ℕ, ∑ j ∈ range J, Real.exp (-2 * σ * (A (j + 1)).1) * δ j ≤
      Real.exp (-2 * σ * (A 0).1) * ccmRestrictedWeilGroundEnergy (A 0) + C) :
    ∀ J : ℕ, -(C * Real.exp (2 * σ * (A J).1)) ≤ ccmRestrictedWeilGroundEnergy (A J) := by
  have h := groundEnergy_ge_neg_exp_of_graded_step
    (A := A) (β := fun j => -2 * σ * (A j).1) (δ := δ) (M := C) hstep hsum
  intro J
  have hJ := h J
  have hexp : Real.exp (-(-2 * σ * (A J).1)) = Real.exp (2 * σ * (A J).1) := by
    congr 1; ring
  rw [hexp] at hJ
  linarith

/-- **Discrete-to-continuous upgrade for graded negative floors.** Because `μ(A)` is antitone in the
aperture, a stage-wise floor `−(C e^{2σ A_j}) ≤ μ(A_j)` along any unbounded sequence `A_j → ∞`
with bounded step gap `A_{j+1} − A_j ≤ Δ` upgrades to the continuous `CompensatedWidthFloor σ`
across all apertures `a ≥ A_0` with constant `C e^{2σΔ}`. -/
theorem compensatedWidthFloor_of_discrete_aperture_sequence
    {A : ℕ → SuzukiPositiveAperture} {σ C Δ : ℝ}
    (hσ : 0 ≤ σ) (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hgap : ∀ j, (A (j + 1)).1 ≤ (A j).1 + Δ)
    (hdisc : ∀ j, -(C * Real.exp (2 * σ * (A j).1)) ≤ ccmRestrictedWeilGroundEnergy (A j)) :
    CompensatedWidthFloor σ := by
  classical
  rw [compensatedWidthFloor_iff_groundEnergy_ge_neg_exp]
  refine ⟨C * Real.exp (2 * σ * Δ), (A 0).1, fun a ha => ?_⟩
  have hex : ∃ k : ℕ, a.1 ≤ (A k).1 := (hAtop.eventually_ge_atTop a.1).exists
  set k := Nat.find hex
  have hak : a.1 ≤ (A k).1 := Nat.find_spec hex
  have hka : (A k).1 ≤ a.1 + Δ := by
    rcases hk : k with _ | j
    · linarith
    · have hj : ¬ a.1 ≤ (A j).1 := Nat.find_min hex (by omega : j < k)
      have hlt : (A j).1 < a.1 := not_le.mp hj
      linarith [hgap j]
  have hant : ccmRestrictedWeilGroundEnergy (A k) ≤ ccmRestrictedWeilGroundEnergy a :=
    ccmRestrictedWeilGroundEnergy_antitone hak
  have hexp : Real.exp (2 * σ * (A k).1) ≤
      Real.exp (2 * σ * Δ) * Real.exp (2 * σ * a.1) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith
  have hmul : C * Real.exp (2 * σ * (A k).1) ≤
      C * Real.exp (2 * σ * Δ) * Real.exp (2 * σ * a.1) := by
    calc C * Real.exp (2 * σ * (A k).1)
        ≤ C * (Real.exp (2 * σ * Δ) * Real.exp (2 * σ * a.1)) :=
          mul_le_mul_of_nonneg_left hexp hC
      _ = C * Real.exp (2 * σ * Δ) * Real.exp (2 * σ * a.1) := by ring
  linarith [hdisc k]

/-- **Subtrivial graded aperture step bounds the zero width and polar ground-energy rate.**
If a sequence `A_j → ∞` with bounded step gaps `A_{j+1} − A_j ≤ Δ` satisfies the graded step
estimates at rate `σ ≥ 0`, then `CompensatedWidthFloor σ`, `zetaZeroWidth ≤ σ`, and
`polarGroundEnergyRate ≤ σ` all hold unconditionally. -/
theorem zetaZeroWidth_le_of_graded_aperture_step
    {A : ℕ → SuzukiPositiveAperture} {δ : ℕ → ℝ} {σ C Δ : ℝ}
    (hσ : 0 ≤ σ) (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hgap : ∀ j, (A (j + 1)).1 ≤ (A j).1 + Δ)
    (hstep : ∀ j,
      Real.exp (-2 * σ * (A (j + 1)).1) * ccmRestrictedWeilGroundEnergy (A (j + 1)) ≥
        Real.exp (-2 * σ * (A j).1) * ccmRestrictedWeilGroundEnergy (A j) -
          Real.exp (-2 * σ * (A (j + 1)).1) * δ j)
    (hsum : ∀ J : ℕ, ∑ j ∈ range J, Real.exp (-2 * σ * (A (j + 1)).1) * δ j ≤
      Real.exp (-2 * σ * (A 0).1) * ccmRestrictedWeilGroundEnergy (A 0) + C) :
    CompensatedWidthFloor σ ∧ zetaZeroWidth ≤ σ ∧ polarGroundEnergyRate ≤ σ := by
  have hdisc := groundEnergy_ge_neg_exp_of_graded_aperture_step hstep hsum
  have hcwf := compensatedWidthFloor_of_discrete_aperture_sequence hσ hC hΔ hAtop hgap hdisc
  exact ⟨hcwf, zetaZeroWidth_le_of_compensatedWidthFloor hσ hcwf,
    polarGroundEnergyRate_le_of_compensatedWidthFloor hσ hcwf⟩

/-- **Graded aperture step implies signed averaged damping continuation.** Under the hypotheses of
`zetaZeroWidth_le_of_graded_aperture_step`, every compact damping interval `[a, c] ⊂ (σ, ∞)`
satisfies `AveragedDampingContinuation a c`. -/
theorem averagedDampingContinuation_of_graded_aperture_step
    {A : ℕ → SuzukiPositiveAperture} {δ : ℕ → ℝ} {σ C Δ a c : ℝ}
    (hσ : 0 ≤ σ) (hC : 0 ≤ C) (hΔ : 0 ≤ Δ)
    (hAtop : Tendsto (fun j => (A j).1) atTop atTop)
    (hgap : ∀ j, (A (j + 1)).1 ≤ (A j).1 + Δ)
    (hstep : ∀ j,
      Real.exp (-2 * σ * (A (j + 1)).1) * ccmRestrictedWeilGroundEnergy (A (j + 1)) ≥
        Real.exp (-2 * σ * (A j).1) * ccmRestrictedWeilGroundEnergy (A j) -
          Real.exp (-2 * σ * (A (j + 1)).1) * δ j)
    (hsum : ∀ J : ℕ, ∑ j ∈ range J, Real.exp (-2 * σ * (A (j + 1)).1) * δ j ≤
      Real.exp (-2 * σ * (A 0).1) * ccmRestrictedWeilGroundEnergy (A 0) + C)
    (ha : σ < a) (hac : a ≤ c) :
    AveragedDampingContinuation a c := by
  have hcwf := (zetaZeroWidth_le_of_graded_aperture_step hσ hC hΔ hAtop hgap hstep hsum).1
  exact averagedDampingContinuation_of_compensatedWidthFloor hσ hcwf ha hac

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
