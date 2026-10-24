import GaloisForLFunctions.ArithmeticCompensationTheory.TheAdaptedEnergyIsExactlyAdmission
import GaloisForLFunctions.ArithmeticCompensationTheory.TheFirstCellCarriesAdverseWork
import GaloisForLFunctions.ArithmeticCompensationTheory.TheCompensatingProjectionMovesSummablyAcrossScales
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.RenormalizationPreservesDampingContinuation

/-!
# Constructing an arithmetic corrector

The corrector architecture (`TheAdaptedEnergyIsExactlyAdmission`) seeks a finite arithmetic cross
term `C_T(ε)` and the adapted energy `H_T(ε) = 1 + E_T(ε) + C_T(ε)` satisfying two independent
obligations on a compact damping interval `[a, c]`, `0 < a ≤ c`:

1. **Horizon-free comparability:** `m (1 + E_T(ε)) ≤ H_T(ε) ≤ M (1 + E_T(ε))` with constants
   `0 < m ≤ M` independent of `T` (proved without assuming admission);
2. **Signed relative loss bound:** `∫_a^c (−∂_ε H_T(ε) / H_T(ε)) dε ≤ L` uniformly in `T`.

This file builds the canonical **Bézout unit-boundary corrector** `bezoutUnitCorrector` from the
first-order pronic cross term between the centred damped divisor prefix `A_ε(n)` and the unit
Bézout boundary `1`, together with its composite extensions by bounded-ratio mixed
large-prime/complement terms:

* **Exact algebraic completion (`bezoutCorrectedEnergy_eq_one_add_residual`):** defining
  `bezoutUnitCorrector ε T = Σ_{1 ≤ n ≤ T} (1 − 2 A_ε(n)) / (n(n+1))`, the corrected energy
  `bezoutCorrectedEnergy ε T = 1 + E_T(ε) + bezoutUnitCorrector ε T` equals
  `1 + pmPowerDampedDualResidual ε T` identically.
* **Unconditional, horizon-free and damping-free comparability (`bezoutCorrectedEnergy_comparison`):**
  for *every* `ε ∈ ℝ` and *every* `T ∈ ℕ`,
  `(1/3) (1 + E_T(ε)) ≤ bezoutCorrectedEnergy ε T ≤ 3 (1 + E_T(ε))`, and
  `|bezoutUnitCorrector ε T| ≤ 2 (1 + E_T(ε))`. Neither admission nor any zero-free hypothesis is
  used.
* **Independently paid derivative (`hasDerivAt_bezoutUnitCorrector`,
  `exists_abs_bezoutUnitCorrectorDeriv_le`):** the damping derivative of `bezoutUnitCorrector` is
  `−2 Σ_{1 ≤ n ≤ T} E_ε(n) / (n(n+1))`, which is bounded in absolute value by `2 K_a` uniformly in
  `T ∈ ℕ` and `ε ≥ a > 0`, and shifts the energy derivative from `2 W_T(ε)` to
  `2 residualDampingWork ε T`.
* **Elimination of the adverse first-cell work (`residualDampingWork_one`,
  `eventually_residualDampingWork_one_pos`):** whereas the uncorrected energy has negative work at
  the first cell (`W_1(ε) → −1/2`), the Bézout-corrected energy has first-cell work
  `residualDampingWork ε 1 = Re(1/ζ(1+ε)) m(ε) / 2`, which is strictly positive for all small
  `ε > 0` and vanishes as `ε ↓ 0`.
* **Composite correctors and the mixed large-prime/complement cross term
  (`abs_pmNormalizedMixedCross_le_one`, `tendsto_pmNormalizedMixedCross_neg_one`,
  `compositeCorrectedEnergy_comparison`, `integral_compositeCorrectedRelativeLoss_le`):** the
  normalized mixed large-prime/complement cross term lies in `[−1, 1]` at every cutoff and tends to
  `−1` for `0 < ε < ½`; adding any `C¹` cross term `C_T(ε)` bounded by
  `θ · bezoutCorrectedEnergy ε T` (`0 ≤ θ < 1`) preserves horizon-free comparability with constants
  `((1 − θ)/3, 3(1 + θ))` and changes the integrated relative loss by at most
  `log((1 + θ)/(1 − θ))`.
* **Unconditional adapted energy above `½`, endpoint transport, and zero-free strips
  (`bezoutCorrected_adaptedEnergy_of_half_le`,
  `zetaZeroAbscissa_le_half_add_of_bezoutCorrected_family`,
  `riemannHypothesis_iff_cofinal_bezoutCorrected_loss`):** on every compact `[a, c]` with `½ ≤ a`,
  `bezoutCorrectedEnergy` is unconditionally an adapted energy with constants `(1/3, 3)`; across
  `[a, c]` with `c` admitted, a horizon-free bound on the Bézout-corrected relative loss is
  equivalent to admission at `a`; a family of such bounds for `a ∈ (a₀, c]` accumulates at `a₀` and
  yields the zero-free strip `Θ ≤ ½ + a₀`; and cofinal bounds on `[a, ½]` as `a ↓ 0` are equivalent
  to the Riemann hypothesis.
-/

open Set Filter Topology Finset MeasureTheory RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## §1. The Bézout unit-boundary corrector -/

/-- **The Bézout unit-boundary corrector** at damping `ε` and horizon `T`: the pronic sum of
`1 − 2 A_ε(n)` over `1 ≤ n ≤ T`, combining the unit pronic mass `1 − 1/(T+1)` with minus twice the
pronic pairing of `A_ε` against the constant unit row. -/
def bezoutUnitCorrector (ε : ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, (1 - 2 * pmPowerDampedCenteredDivisorPrefix ε n) / ((n : ℝ) * ((n : ℝ) + 1))

/-- **The Bézout-corrected energy** `H_T(ε) = 1 + E_T(ε) + C_T(ε)`. -/
def bezoutCorrectedEnergy (ε : ℝ) (T : ℕ) : ℝ :=
  1 + dampedMobiusEnergy ε T + bezoutUnitCorrector ε T

/-- The Bézout unit-boundary corrector splits into the exact pronic mass `1 − 1/(T+1)` minus twice
the scalar pronic moment of the centred divisor prefix. -/
theorem bezoutUnitCorrector_eq_pronicMass_sub_two_mul (ε : ℝ) (T : ℕ) :
    bezoutUnitCorrector ε T =
      (1 - 1 / ((T : ℝ) + 1)) -
        2 * ∑ n ∈ Icc 1 T, pmPowerDampedCenteredDivisorPrefix ε n / ((n : ℝ) * ((n : ℝ) + 1)) := by
  unfold bezoutUnitCorrector
  rw [← sum_Icc_pronic_mass T, mul_sum, ← sum_sub_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- **Exact square completion.** Adding `bezoutUnitCorrector` to `1 + E_T(ε)` produces one plus the
Báez–Duarte dual residual `Σ_{n ≤ T} (A_ε(n) − 1)² / (n(n+1))`. -/
theorem bezoutCorrectedEnergy_eq_one_add_residual (ε : ℝ) (T : ℕ) :
    bezoutCorrectedEnergy ε T = 1 + pmPowerDampedDualResidual ε T := by
  unfold bezoutCorrectedEnergy dampedMobiusEnergy pmPowerDampedDivisorDiscreteEnergy
    bezoutUnitCorrector pmPowerDampedDualResidual
  rw [add_assoc, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  ring

/-- The Bézout-corrected energy is at least `1`, hence strictly positive, at every damping and
horizon. -/
theorem one_le_bezoutCorrectedEnergy (ε : ℝ) (T : ℕ) : 1 ≤ bezoutCorrectedEnergy ε T := by
  rw [bezoutCorrectedEnergy_eq_one_add_residual]
  have h0 : 0 ≤ pmPowerDampedDualResidual ε T :=
    sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (by positivity)
  linarith

theorem bezoutCorrectedEnergy_pos (ε : ℝ) (T : ℕ) : 0 < bezoutCorrectedEnergy ε T :=
  zero_lt_one.trans_le (one_le_bezoutCorrectedEnergy ε T)

/-- **Unconditional horizon-free and damping-free comparability.** For every `ε ∈ ℝ` and `T ∈ ℕ`,
`(1/3) (1 + E_T(ε)) ≤ bezoutCorrectedEnergy ε T ≤ 3 (1 + E_T(ε))`. -/
theorem bezoutCorrectedEnergy_comparison (ε : ℝ) (T : ℕ) :
    (1 / 3 : ℝ) * (1 + dampedMobiusEnergy ε T) ≤ bezoutCorrectedEnergy ε T ∧
      bezoutCorrectedEnergy ε T ≤ 3 * (1 + dampedMobiusEnergy ε T) := by
  rw [bezoutCorrectedEnergy_eq_one_add_residual]
  obtain ⟨h1, h2⟩ := one_add_damped_energy_comparison ε T
  exact ⟨by linarith, h1⟩

/-- The Bézout unit-boundary corrector is bounded in absolute value by `2 (1 + E_T(ε))` at every
damping and horizon. -/
theorem abs_bezoutUnitCorrector_le (ε : ℝ) (T : ℕ) :
    |bezoutUnitCorrector ε T| ≤ 2 * (1 + dampedMobiusEnergy ε T) := by
  obtain ⟨hlow, hhigh⟩ := bezoutCorrectedEnergy_comparison ε T
  have hE : 0 ≤ 1 + dampedMobiusEnergy ε T := by linarith [dampedMobiusEnergy_nonneg ε T]
  unfold bezoutCorrectedEnergy at hlow hhigh
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- The damping derivative of `bezoutUnitCorrector`: minus twice the scalar pronic moment of the
centred damped Chebyshev tangent. -/
def bezoutUnitCorrectorDeriv (T : ℕ) (ε : ℝ) : ℝ :=
  -2 * ∑ n ∈ Icc 1 T, dampedChebyshevError ε n / ((n : ℝ) * ((n : ℝ) + 1))

/-- `bezoutUnitCorrector` is differentiable at every positive damping, with derivative
`bezoutUnitCorrectorDeriv`. -/
theorem hasDerivAt_bezoutUnitCorrector {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    HasDerivAt (fun x => bezoutUnitCorrector x T) (bezoutUnitCorrectorDeriv T ε) ε := by
  unfold bezoutUnitCorrector bezoutUnitCorrectorDeriv
  have h := HasDerivAt.fun_sum (u := Icc 1 T)
    (A := fun n x => (1 - 2 * pmPowerDampedCenteredDivisorPrefix x n) / ((n : ℝ) * ((n : ℝ) + 1)))
    (A' := fun n => -2 * dampedChebyshevError ε n / ((n : ℝ) * ((n : ℝ) + 1)))
    (fun n _ => by
      have hp := (((hasDerivAt_pmPowerDampedCenteredDivisorPrefix hε n).const_mul 2).const_sub
        1).div_const ((n : ℝ) * ((n : ℝ) + 1))
      refine hp.congr_deriv ?_
      ring)
  refine h.congr_deriv ?_
  rw [mul_sum]
  exact sum_congr rfl fun n _ => by ring

/-- **The corrector's derivative is uniformly bounded on every positive half-line.** For every
`a > 0` there is a horizon-free constant `K ≥ 0` such that `|bezoutUnitCorrectorDeriv T ε| ≤ 2 K`
for all `ε ≥ a` and all `T ∈ ℕ`. -/
theorem exists_abs_bezoutUnitCorrectorDeriv_le {a : ℝ} (ha : 0 < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ε : ℝ, a ≤ ε → ∀ T : ℕ,
      |bezoutUnitCorrectorDeriv T ε| ≤ 2 * K := by
  obtain ⟨K, hK, hbound⟩ := exists_uniform_scalar_damping_work_bound ha
  refine ⟨K, hK, fun ε hε T => ?_⟩
  rw [bezoutUnitCorrectorDeriv, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0), neg_neg]
  exact mul_le_mul_of_nonneg_left (hbound ε hε T) (by norm_num)

/-- The damping derivative of `bezoutCorrectedEnergy` is twice the residual damping work. -/
theorem hasDerivAt_bezoutCorrectedEnergy {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    HasDerivAt (fun x => bezoutCorrectedEnergy x T) (2 * residualDampingWork ε T) ε := by
  have h := ((hasDerivAt_dampedMobiusEnergy hε T).const_add 1).add
    (hasDerivAt_bezoutUnitCorrector hε T)
  refine h.congr_deriv ?_
  have hsub := signedDampingWork_sub_residualDampingWork ε T
  unfold bezoutUnitCorrectorDeriv
  linarith

/-- **Elimination of the adverse first-cell work.** At horizon `T = 1`, the Bézout-corrected work
is `Re(1/ζ(1+ε)) m(ε) / 2`, removing the constant `1` that forced `W_1(ε) → −1/2`. -/
theorem residualDampingWork_one (ε : ℝ) :
    residualDampingWork ε 1 =
      (pmPowerDampedDivisorDensity ε).re * dampedReadout ε / 2 := by
  rw [residualDampingWork, show Finset.Icc 1 1 = {1} by rfl, sum_singleton,
    centredPrefix_one, dampedChebyshevError_one]
  push_cast
  ring

/-- For all small positive dampings, the first-cell work of the Bézout-corrected energy is strictly
positive, reversing the negative sign of `eventually_signedDampingWork_one_neg`. -/
theorem eventually_residualDampingWork_one_pos :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < residualDampingWork ε 1 := by
  have hm : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < dampedReadout ε :=
    tendsto_dampedReadout_zero.eventually (lt_mem_nhds one_pos)
  filter_upwards [hm, self_mem_nhdsWithin] with ε hread hε
  rw [residualDampingWork_one]
  have hdens : 0 < (pmPowerDampedDivisorDensity ε).re := RHTower.pmPowerDampedDivisorDensity_re_pos hε
  positivity

/-- The residual damping work equals the signed damping work minus the paid scalar tangent
moment, so `2 * residualDampingWork ε T = 2 * signedDampingWork ε T + bezoutUnitCorrectorDeriv T ε`. -/
theorem residualDampingWork_eq_signedDampingWork_sub_scalar (ε : ℝ) (T : ℕ) :
    residualDampingWork ε T =
      signedDampingWork ε T -
        ∑ n ∈ Finset.Icc 1 T, dampedChebyshevError ε n / ((n : ℝ) * ((n : ℝ) + 1)) := by
  have h1 := signedDampingWork_sub_residualDampingWork ε T
  linarith

/-! ## §2. Composite correctors and the mixed large-prime/complement cross term -/

/-- The normalized mixed large-prime/complement Gram cross term at cutoff `P²`:
`2 ⟪L_P, C_P⟫ / (1 + ‖L_P‖² + ‖C_P‖²)`. -/
def pmNormalizedMixedCross (ε : ℝ) (P : ℕ) : ℝ :=
  2 * pmRamanujanLargePrimeComplementMixedEnergy ε P /
    (1 + pmRamanujanLargePrimeSectorEnergy ε P + pmRamanujanLargePrimeComplementEnergy ε P)

/-- **Cauchy–Schwarz bound for the normalized mixed cross term.** For every damping `ε` and cutoff
`P`, `|pmNormalizedMixedCross ε P| ≤ 1`. -/
theorem abs_pmNormalizedMixedCross_le_one (ε : ℝ) (P : ℕ) :
    |pmNormalizedMixedCross ε P| ≤ 1 := by
  have hL : 0 ≤ pmRamanujanLargePrimeSectorEnergy ε P :=
    pmRamanujanLargePrimeSectorEnergy_nonneg ε P
  have hC : 0 ≤ pmRamanujanLargePrimeComplementEnergy ε P := by
    unfold pmRamanujanLargePrimeComplementEnergy; positivity
  have hcs := pmMixedEnergy_sq_le ε P
  have h2m : (2 * |pmRamanujanLargePrimeComplementMixedEnergy ε P|) ^ 2 ≤
      (pmRamanujanLargePrimeSectorEnergy ε P + pmRamanujanLargePrimeComplementEnergy ε P) ^ 2 := by
    have hsq : |pmRamanujanLargePrimeComplementMixedEnergy ε P| ^ 2 =
        pmRamanujanLargePrimeComplementMixedEnergy ε P ^ 2 := sq_abs _
    nlinarith [sq_nonneg (pmRamanujanLargePrimeSectorEnergy ε P -
      pmRamanujanLargePrimeComplementEnergy ε P)]
  have habs : 2 * |pmRamanujanLargePrimeComplementMixedEnergy ε P| ≤
      pmRamanujanLargePrimeSectorEnergy ε P + pmRamanujanLargePrimeComplementEnergy ε P := by
    nlinarith [Real.sqrt_le_sqrt h2m,
      Real.sqrt_sq (by positivity : 0 ≤ 2 * |pmRamanujanLargePrimeComplementMixedEnergy ε P|),
      Real.sqrt_sq (by positivity :
        0 ≤ pmRamanujanLargePrimeSectorEnergy ε P + pmRamanujanLargePrimeComplementEnergy ε P)]
  have hden : 0 < 1 + pmRamanujanLargePrimeSectorEnergy ε P +
      pmRamanujanLargePrimeComplementEnergy ε P := by linarith
  rw [pmNormalizedMixedCross, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos hden, div_le_one hden]
  linarith

/-- For `0 < ε < ½`, the normalized mixed large-prime/complement cross term tends to `−1` as
`P → ∞`: the mixed interaction carries the full negative of the combined sector and complement
energies. -/
theorem tendsto_pmNormalizedMixedCross_neg_one {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    Tendsto (pmNormalizedMixedCross ε) atTop (𝓝 (-1)) := by
  have hLtop := tendsto_pmRamanujanLargePrimeSectorEnergy_atTop hε hεhalf
  have hinv : Tendsto (fun P => 1 / pmRamanujanLargePrimeSectorEnergy ε P) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hLtop
  have hC := tendsto_pmRamanujanLargePrimeComplementEnergy_ratio_one hε hεhalf
  have hM := tendsto_pmRamanujanLargePrimeComplementMixedEnergy_ratio_neg_one hε hεhalf
  have hquo : Tendsto (fun P =>
      (2 * (pmRamanujanLargePrimeComplementMixedEnergy ε P /
        pmRamanujanLargePrimeSectorEnergy ε P)) /
      (1 / pmRamanujanLargePrimeSectorEnergy ε P + 1 +
        pmRamanujanLargePrimeComplementEnergy ε P /
          pmRamanujanLargePrimeSectorEnergy ε P)) atTop
      (𝓝 ((2 * (-1)) / (0 + 1 + 1))) :=
    (hM.const_mul 2).div ((hinv.add tendsto_const_nhds).add hC) (by norm_num)
  rw [show (2 * (-1 : ℝ)) / (0 + 1 + 1) = -1 by norm_num] at hquo
  refine hquo.congr' ?_
  filter_upwards [hLtop.eventually_gt_atTop 0] with P hLP
  rw [pmNormalizedMixedCross]
  field_simp

/-- **A composite arithmetic corrector** combining the Bézout unit-boundary corrector with an
additional cross-term family `C_T(ε)`. -/
def compositeArithmeticCorrector (C : ℝ → ℕ → ℝ) (ε : ℝ) (T : ℕ) : ℝ :=
  bezoutUnitCorrector ε T + C ε T

/-- **The composite corrected energy** `1 + E_T(ε) + bezoutUnitCorrector ε T + C_T(ε)`. -/
def compositeCorrectedEnergy (C : ℝ → ℕ → ℝ) (ε : ℝ) (T : ℕ) : ℝ :=
  1 + dampedMobiusEnergy ε T + compositeArithmeticCorrector C ε T

theorem compositeCorrectedEnergy_eq_bezout_add (C : ℝ → ℕ → ℝ) (ε : ℝ) (T : ℕ) :
    compositeCorrectedEnergy C ε T = bezoutCorrectedEnergy ε T + C ε T := by
  unfold compositeCorrectedEnergy compositeArithmeticCorrector bezoutCorrectedEnergy
  ring

/-- Sandwich of `compositeCorrectedEnergy C` against `bezoutCorrectedEnergy` when
`|C ε T| ≤ θ · bezoutCorrectedEnergy ε T`. -/
theorem compositeCorrectedEnergy_bezout_sandwich {C : ℝ → ℕ → ℝ} {θ : ℝ}
    (ε : ℝ) (T : ℕ) (hC : |C ε T| ≤ θ * bezoutCorrectedEnergy ε T) :
    (1 - θ) * bezoutCorrectedEnergy ε T ≤ compositeCorrectedEnergy C ε T ∧
      compositeCorrectedEnergy C ε T ≤ (1 + θ) * bezoutCorrectedEnergy ε T := by
  obtain ⟨h1, h2⟩ := abs_le.mp hC
  rw [compositeCorrectedEnergy_eq_bezout_add]
  exact ⟨by linarith, by linarith⟩

/-- **Independent comparability for composite correctors.** Any cross-term family `C_T(ε)` bounded
in magnitude by `θ · bezoutCorrectedEnergy ε T` with `0 ≤ θ ≤ 1` produces a composite energy
comparable to `1 + E_T(ε)` with horizon-free constants `((1 − θ)/3, 3(1 + θ))`. -/
theorem compositeCorrectedEnergy_comparison {C : ℝ → ℕ → ℝ} {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ε : ℝ) (T : ℕ)
    (hC : |C ε T| ≤ θ * bezoutCorrectedEnergy ε T) :
    ((1 - θ) / 3) * (1 + dampedMobiusEnergy ε T) ≤ compositeCorrectedEnergy C ε T ∧
      compositeCorrectedEnergy C ε T ≤ 3 * (1 + θ) * (1 + dampedMobiusEnergy ε T) := by
  obtain ⟨hlow, hhigh⟩ := bezoutCorrectedEnergy_comparison ε T
  obtain ⟨hC1, hC2⟩ := compositeCorrectedEnergy_bezout_sandwich ε T hC
  constructor
  · have h1 : (1 - θ) * ((1 / 3 : ℝ) * (1 + dampedMobiusEnergy ε T)) ≤
        (1 - θ) * bezoutCorrectedEnergy ε T :=
      mul_le_mul_of_nonneg_left hlow (by linarith)
    linarith
  · have h2 : (1 + θ) * bezoutCorrectedEnergy ε T ≤
        (1 + θ) * (3 * (1 + dampedMobiusEnergy ε T)) :=
      mul_le_mul_of_nonneg_left hhigh (by linarith)
    linarith

/-- **The relative loss of the Bézout-corrected energy**:
`−∂_ε log(bezoutCorrectedEnergy ε T) = −2 residualDampingWork ε T / bezoutCorrectedEnergy ε T`. -/
def bezoutCorrectedRelativeLoss (T : ℕ) (ε : ℝ) : ℝ :=
  -(2 * residualDampingWork ε T) / bezoutCorrectedEnergy ε T

theorem continuousOn_residualDampingWork (T : ℕ) :
    ContinuousOn (fun ε => residualDampingWork ε T) (Ioi 0) := by
  unfold residualDampingWork
  refine continuousOn_finsetSum _ fun n _ ε hε => ?_
  have hε0 : (0 : ℝ) < ε := mem_Ioi.mp hε
  have h1 : ContinuousAt (fun x => pmPowerDampedCenteredDivisorPrefix x n - 1) ε :=
    ((hasDerivAt_pmPowerDampedCenteredDivisorPrefix hε0 n).continuousAt).sub continuousAt_const
  have h2 : ContinuousAt (fun x => dampedChebyshevError x n) ε :=
    (continuousOn_dampedChebyshevError n).continuousAt (isOpen_Ioi.mem_nhds hε)
  exact ((h1.mul h2).div_const _).continuousWithinAt

theorem continuousOn_bezoutCorrectedEnergy (T : ℕ) :
    ContinuousOn (fun ε => bezoutCorrectedEnergy ε T) (Ioi 0) := fun _ hε =>
  ((hasDerivAt_bezoutCorrectedEnergy (mem_Ioi.mp hε) T).continuousAt).continuousWithinAt

/-- The Bézout-corrected relative loss is unconditionally integrable on every compact damping
interval `[a, c]` with `0 < a ≤ c`. -/
theorem intervalIntegrable_bezoutCorrectedRelativeLoss {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (T : ℕ) :
    IntervalIntegrable (bezoutCorrectedRelativeLoss T) volume a c := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hac]
  intro ε hε
  have hε0 : (0 : ℝ) < ε := lt_of_lt_of_le ha hε.1
  have hmem : ε ∈ Ioi (0 : ℝ) := mem_Ioi.mpr hε0
  have hW : ContinuousAt (fun x => -(2 * residualDampingWork x T)) ε :=
    (((continuousOn_residualDampingWork T).continuousAt (isOpen_Ioi.mem_nhds hmem)).const_mul 2).neg
  have hH : ContinuousAt (fun x => bezoutCorrectedEnergy x T) ε :=
    (continuousOn_bezoutCorrectedEnergy T).continuousAt (isOpen_Ioi.mem_nhds hmem)
  exact (hW.div hH (bezoutCorrectedEnergy_pos ε T).ne').continuousWithinAt

/-- The integral of `bezoutCorrectedRelativeLoss` across `[a, c]` is the exact logarithmic ratio
`log(bezoutCorrectedEnergy a T) − log(bezoutCorrectedEnergy c T)`. -/
theorem integral_bezoutCorrectedRelativeLoss_eq {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    ∫ ε in a..c, bezoutCorrectedRelativeLoss T ε =
      Real.log (bezoutCorrectedEnergy a T) - Real.log (bezoutCorrectedEnergy c T) := by
  have hlog : ∀ ε ∈ uIcc a c, HasDerivAt (fun x => Real.log (bezoutCorrectedEnergy x T))
      (2 * residualDampingWork ε T / bezoutCorrectedEnergy ε T) ε := by
    intro ε hε
    rw [uIcc_of_le hac] at hε
    exact (hasDerivAt_bezoutCorrectedEnergy (lt_of_lt_of_le ha hε.1) T).log
      (bezoutCorrectedEnergy_pos ε T).ne'
  have hint := intervalIntegrable_bezoutCorrectedRelativeLoss ha hac T
  have hint' : IntervalIntegrable
      (fun ε => 2 * residualDampingWork ε T / bezoutCorrectedEnergy ε T) volume a c := by
    refine hint.neg.congr fun ε _ => ?_
    simp [bezoutCorrectedRelativeLoss, neg_div]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hlog hint'
  have hcongr : (∫ ε in a..c, bezoutCorrectedRelativeLoss T ε) =
      -(∫ ε in a..c, 2 * residualDampingWork ε T / bezoutCorrectedEnergy ε T) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun ε _ => by simp [bezoutCorrectedRelativeLoss, neg_div]
  rw [hcongr, hFTC]
  ring

/-- **Relative-loss stability under composite perturbations.** For any differentiable cross-term
family `C_T(ε)` with continuous derivative `C'_T(ε)` on `[a, c]` (`0 < a ≤ c`) satisfying
`|C_T(ε)| ≤ θ · bezoutCorrectedEnergy ε T` (`0 ≤ θ < 1`), the integrated relative loss of
`compositeCorrectedEnergy C` exceeds that of `bezoutCorrectedEnergy` by at most
`log((1 + θ)/(1 − θ))`. -/
theorem integral_compositeCorrectedRelativeLoss_le {a c θ : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {C : ℝ → ℕ → ℝ} {C' : ℕ → ℝ → ℝ} (T : ℕ)
    (hC : ∀ ε ∈ Icc a c, |C ε T| ≤ θ * bezoutCorrectedEnergy ε T)
    (hCd : ∀ ε ∈ Icc a c, HasDerivAt (fun x => C x T) (C' T ε) ε)
    (hCcont : ContinuousOn (C' T) (Icc a c)) :
    IntervalIntegrable
        (fun ε => -(2 * residualDampingWork ε T + C' T ε) / compositeCorrectedEnergy C ε T)
        volume a c ∧
      (∫ ε in a..c, -(2 * residualDampingWork ε T + C' T ε) / compositeCorrectedEnergy C ε T) ≤
        (∫ ε in a..c, bezoutCorrectedRelativeLoss T ε) + Real.log ((1 + θ) / (1 - θ)) := by
  have hpos : ∀ ε ∈ Icc a c, 0 < compositeCorrectedEnergy C ε T := fun ε hε => by
    have h1 := (compositeCorrectedEnergy_bezout_sandwich ε T (hC ε hε)).1
    have h2 := bezoutCorrectedEnergy_pos ε T
    have h3 : 0 < 1 - θ := by linarith
    nlinarith
  have hderiv : ∀ ε ∈ Icc a c, HasDerivAt (fun x => compositeCorrectedEnergy C x T)
      (2 * residualDampingWork ε T + C' T ε) ε := fun ε hε =>
    ((hasDerivAt_bezoutCorrectedEnergy (lt_of_lt_of_le ha hε.1) T).add
      (hCd ε hε)).congr_of_eventuallyEq
      (Eventually.of_forall fun x => compositeCorrectedEnergy_eq_bezout_add C x T)
  have hint : IntervalIntegrable
      (fun ε => -(2 * residualDampingWork ε T + C' T ε) / compositeCorrectedEnergy C ε T)
      volume a c := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hac]
    have hW : ContinuousOn (fun ε => 2 * residualDampingWork ε T) (Icc a c) :=
      continuousOn_const.mul ((continuousOn_residualDampingWork T).mono fun ε hε =>
        mem_Ioi.mpr (lt_of_lt_of_le ha hε.1))
    have hnum : ContinuousOn (fun ε => -(2 * residualDampingWork ε T + C' T ε)) (Icc a c) :=
      (hW.add hCcont).neg
    have hden : ContinuousOn (fun ε => compositeCorrectedEnergy C ε T) (Icc a c) := fun ε hε =>
      (hderiv ε hε).continuousAt.continuousWithinAt
    exact hnum.div hden fun ε hε => (hpos ε hε).ne'
  refine ⟨hint, ?_⟩
  have hlog : ∀ ε ∈ uIcc a c, HasDerivAt (fun x => Real.log (compositeCorrectedEnergy C x T))
      ((2 * residualDampingWork ε T + C' T ε) / compositeCorrectedEnergy C ε T) ε := by
    intro ε hε
    rw [uIcc_of_le hac] at hε
    exact (hderiv ε hε).log (hpos ε hε).ne'
  have hint' : IntervalIntegrable
      (fun ε => (2 * residualDampingWork ε T + C' T ε) / compositeCorrectedEnergy C ε T)
      volume a c := by
    refine hint.neg.congr fun ε _ => ?_
    dsimp only [Pi.neg_apply]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hlog hint'
  have hcongr : (∫ ε in a..c,
      -(2 * residualDampingWork ε T + C' T ε) / compositeCorrectedEnergy C ε T) =
      Real.log (compositeCorrectedEnergy C a T) - Real.log (compositeCorrectedEnergy C c T) := by
    have hneg : (∫ ε in a..c,
        -(2 * residualDampingWork ε T + C' T ε) / compositeCorrectedEnergy C ε T) =
        -(∫ ε in a..c, (2 * residualDampingWork ε T + C' T ε) / compositeCorrectedEnergy C ε T) := by
      rw [← intervalIntegral.integral_neg]
      exact intervalIntegral.integral_congr fun ε _ => by ring
    rw [hneg, hFTC]
    ring
  rw [hcongr, integral_bezoutCorrectedRelativeLoss_eq ha hac T]
  have ha_mem : a ∈ Icc a c := left_mem_Icc.mpr hac
  have hc_mem : c ∈ Icc a c := right_mem_Icc.mpr hac
  have h1θ : 0 < 1 - θ := by linarith
  have h2θ : 0 < 1 + θ := by linarith
  have hBa := bezoutCorrectedEnergy_pos a T
  have hBc := bezoutCorrectedEnergy_pos c T
  have hsa := (compositeCorrectedEnergy_bezout_sandwich a T (hC a ha_mem)).2
  have hsc := (compositeCorrectedEnergy_bezout_sandwich c T (hC c hc_mem)).1
  have hloga : Real.log (compositeCorrectedEnergy C a T) ≤
      Real.log (1 + θ) + Real.log (bezoutCorrectedEnergy a T) := by
    calc Real.log (compositeCorrectedEnergy C a T)
        ≤ Real.log ((1 + θ) * bezoutCorrectedEnergy a T) :=
          Real.log_le_log (hpos a ha_mem) hsa
      _ = Real.log (1 + θ) + Real.log (bezoutCorrectedEnergy a T) :=
          Real.log_mul h2θ.ne' hBa.ne'
  have hlogc : Real.log (1 - θ) + Real.log (bezoutCorrectedEnergy c T) ≤
      Real.log (compositeCorrectedEnergy C c T) := by
    calc Real.log (1 - θ) + Real.log (bezoutCorrectedEnergy c T)
        = Real.log ((1 - θ) * bezoutCorrectedEnergy c T) :=
          (Real.log_mul h1θ.ne' hBc.ne').symm
      _ ≤ Real.log (compositeCorrectedEnergy C c T) :=
          Real.log_le_log (mul_pos h1θ hBc) hsc
  rw [Real.log_div h2θ.ne' h1θ.ne']
  linarith

/-! ## §3. Unconditional adapted energy above one half, endpoint transport, and zero-free strips -/

/-- **A horizon-free bound on the Bézout-corrected relative loss produces an explicit
`AdaptedEnergy`.** The comparability constants `(1/3, 3)` and all regularity inputs are discharged
unconditionally. -/
theorem adaptedEnergy_of_bezoutCorrected_loss {a c L : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hL : ∀ T : ℕ, ∫ ε in a..c, bezoutCorrectedRelativeLoss T ε ≤ L) :
    AdaptedEnergy dampedMobiusEnergy a c :=
  ⟨bezoutCorrectedEnergy, fun T ε => 2 * residualDampingWork ε T, 1 / 3, 3, L, by norm_num,
    fun T ε _ => bezoutCorrectedEnergy_comparison ε T,
    fun T _ hε => hasDerivAt_bezoutCorrectedEnergy (lt_of_lt_of_le ha hε.1) T,
    fun T => intervalIntegrable_bezoutCorrectedRelativeLoss ha hac T, hL⟩

/-- **A composite corrector with bounded ratio and bounded Bézout-corrected loss is an explicit
`AdaptedEnergy`.** -/
theorem adaptedEnergy_of_compositeCorrector {a c L θ : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    {C : ℝ → ℕ → ℝ} {C' : ℕ → ℝ → ℝ}
    (hC : ∀ T, ∀ ε ∈ Icc a c, |C ε T| ≤ θ * bezoutCorrectedEnergy ε T)
    (hCd : ∀ T, ∀ ε ∈ Icc a c, HasDerivAt (fun x => C x T) (C' T ε) ε)
    (hCcont : ∀ T, ContinuousOn (C' T) (Icc a c))
    (hL : ∀ T : ℕ, ∫ ε in a..c, bezoutCorrectedRelativeLoss T ε ≤ L) :
    AdaptedEnergy dampedMobiusEnergy a c := by
  refine ⟨compositeCorrectedEnergy C, fun T ε => 2 * residualDampingWork ε T + C' T ε,
    (1 - θ) / 3, 3 * (1 + θ), L + Real.log ((1 + θ) / (1 - θ)), by linarith,
    fun T ε hε => compositeCorrectedEnergy_comparison hθ0 hθ1.le ε T (hC T ε hε), ?_, ?_, ?_⟩
  · intro T ε hε
    exact (((hasDerivAt_bezoutCorrectedEnergy (lt_of_lt_of_le ha hε.1) T).add
      (hCd T ε hε)).congr_of_eventuallyEq
      (Eventually.of_forall fun x => compositeCorrectedEnergy_eq_bezout_add C x T))
  · intro T
    exact (integral_compositeCorrectedRelativeLoss_le ha hac hθ0 hθ1 T
      (hC T) (hCd T) (hCcont T)).1
  · intro T
    have hstep := (integral_compositeCorrectedRelativeLoss_le ha hac hθ0 hθ1 T
      (hC T) (hCd T) (hCcont T)).2
    linarith [hL T]

/-- **Backward transport of admission.** If `c` is admitted and the Bézout-corrected relative loss
is bounded by `L` across `[a, c]` (`0 < a ≤ c`), then `a` is admitted. -/
theorem admits_of_bezoutCorrected_loss {a c L : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c)
    (hL : ∀ T : ℕ, ∫ ε in a..c, bezoutCorrectedRelativeLoss T ε ≤ L) :
    Admits dampedMobiusEnergy a :=
  Admits.of_adaptedEnergy hac (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
    (adaptedEnergy_of_bezoutCorrected_loss ha hac hL) hc

/-- **Converse: admission at the left endpoint bounds the Bézout-corrected relative loss.** -/
theorem bezoutCorrected_loss_of_admits {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hadm : Admits dampedMobiusEnergy a) :
    ∃ L : ℝ, ∀ T : ℕ, ∫ ε in a..c, bezoutCorrectedRelativeLoss T ε ≤ L := by
  obtain ⟨B, hB⟩ := hadm
  refine ⟨Real.log (3 * (1 + max B 0)), fun T => ?_⟩
  rw [integral_bezoutCorrectedRelativeLoss_eq ha hac T]
  have hlogc : 0 ≤ Real.log (bezoutCorrectedEnergy c T) :=
    Real.log_nonneg (one_le_bezoutCorrectedEnergy c T)
  have hupper : bezoutCorrectedEnergy a T ≤ 3 * (1 + max B 0) := by
    have h1 := (bezoutCorrectedEnergy_comparison a T).2
    have h2 : 1 + dampedMobiusEnergy a T ≤ 1 + max B 0 := by
      linarith [hB T, le_max_left B 0]
    linarith
  have hloga : Real.log (bezoutCorrectedEnergy a T) ≤ Real.log (3 * (1 + max B 0)) :=
    Real.log_le_log (bezoutCorrectedEnergy_pos a T) hupper
  linarith

/-- **Exact equivalence on `[a, c]`.** With an admitted right endpoint `c`, a horizon-free bound on
the Bézout-corrected relative loss across `[a, c]` (`0 < a ≤ c`) is equivalent to admission at `a`. -/
theorem bezoutCorrected_loss_iff_admits {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    (∃ L : ℝ, ∀ T : ℕ, ∫ ε in a..c, bezoutCorrectedRelativeLoss T ε ≤ L) ↔
      Admits dampedMobiusEnergy a :=
  ⟨fun ⟨_, hL⟩ => admits_of_bezoutCorrected_loss ha hac hc hL,
    bezoutCorrected_loss_of_admits ha hac⟩

/-- **Unconditional Bézout-corrected adapted energy above one half.** On every compact interval
`[a, c]` with `½ ≤ a ≤ c`, `bezoutCorrectedEnergy` satisfies both comparability `(1/3, 3)` and a
horizon-free signed relative loss bound unconditionally. -/
theorem exists_bezoutCorrectedRelativeLoss_le_of_half_le {a c : ℝ} (ha : 1 / 2 ≤ a) (hac : a ≤ c) :
    ∃ L : ℝ, ∀ T : ℕ, ∫ ε in a..c, bezoutCorrectedRelativeLoss T ε ≤ L :=
  bezoutCorrected_loss_of_admits (by linarith) hac (admits_dampedMobiusEnergy_of_half_le ha)

theorem bezoutCorrected_adaptedEnergy_of_half_le {a c : ℝ} (ha : 1 / 2 ≤ a) (hac : a ≤ c) :
    AdaptedEnergy dampedMobiusEnergy a c := by
  obtain ⟨L, hL⟩ := exists_bezoutCorrectedRelativeLoss_le_of_half_le ha hac
  exact adaptedEnergy_of_bezoutCorrected_loss (by linarith) hac hL

/-- **A boundary-accumulating family of adapted energies yields a quantitative zero-free strip.**
If `c` is admitted (`0 ≤ a₀ < c`) and `AdaptedEnergy dampedMobiusEnergy a c` holds for every
`a ∈ (a₀, c]`, then the admitted dampings accumulate at `a₀` and `zetaZeroAbscissa ≤ ½ + a₀`. -/
theorem zetaZeroAbscissa_le_half_add_of_adaptedEnergy_family {a₀ c : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₀c : a₀ < c) (hc : Admits dampedMobiusEnergy c)
    (h : ∀ a : ℝ, a₀ < a → a ≤ c → AdaptedEnergy dampedMobiusEnergy a c) :
    zetaZeroAbscissa ≤ 1 / 2 + a₀ := by
  refine zetaZeroAbscissa_le_of_accPt_receiverDampings (accPt_of_Ioo_subset ha₀c ?_)
  intro a ha
  have ha0 : 0 < a := lt_of_le_of_lt ha₀ ha.1
  exact (mem_receiverDampings_iff_admits ha0).mpr
    (Admits.of_adaptedEnergy ha.2.le (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
      (h a ha.1 ha.2.le) hc)

/-- **A boundary-accumulating family of Bézout-corrected relative-loss bounds yields a quantitative
zero-free strip.** If `c` is admitted (`0 ≤ a₀ < c`) and for every `a ∈ (a₀, c]` the
Bézout-corrected relative loss across `[a, c]` has a horizon-free bound, then
`zetaZeroAbscissa ≤ ½ + a₀`. -/
theorem zetaZeroAbscissa_le_half_add_of_bezoutCorrected_family {a₀ c : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₀c : a₀ < c) (hc : Admits dampedMobiusEnergy c)
    (h : ∀ a : ℝ, a₀ < a → a ≤ c →
      ∃ L : ℝ, ∀ T : ℕ, ∫ ε in a..c, bezoutCorrectedRelativeLoss T ε ≤ L) :
    zetaZeroAbscissa ≤ 1 / 2 + a₀ := by
  refine zetaZeroAbscissa_le_half_add_of_adaptedEnergy_family ha₀ ha₀c hc fun a ha1 ha2 => ?_
  obtain ⟨L, hL⟩ := h a ha1 ha2
  exact adaptedEnergy_of_bezoutCorrected_loss (lt_of_le_of_lt ha₀ ha1) ha2 hL

/-- **The Bézout-corrected relative-loss target is equivalent to the Riemann hypothesis.** Cofinal
horizon-free bounds on `∫_a^{1/2} bezoutCorrectedRelativeLoss T ε dε` as `a ↓ 0` hold if and only
if `RiemannHypothesis` holds. -/
theorem riemannHypothesis_iff_cofinal_bezoutCorrected_loss :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ → ∃ a : ℝ, 0 < a ∧ a < δ ∧
      ∃ L : ℝ, ∀ T : ℕ, ∫ ε in a..(1 / 2 : ℝ), bezoutCorrectedRelativeLoss T ε ≤ L := by
  rw [riemannHypothesis_iff_cofinal_adaptedEnergy]
  constructor
  · intro h δ hδ
    obtain ⟨a, ha, haδ, hAE⟩ := h (min δ (1 / 2)) (lt_min hδ (by norm_num))
    have hac : a ≤ 1 / 2 := (lt_of_lt_of_le haδ (min_le_right _ _)).le
    have hadm := (adaptedEnergy_dampedMobiusEnergy_iff_admits ha hac).mp hAE
    exact ⟨a, ha, lt_of_lt_of_le haδ (min_le_left _ _),
      bezoutCorrected_loss_of_admits ha hac hadm⟩
  · intro h δ hδ
    obtain ⟨a, ha, haδ, L, hL⟩ := h (min δ (1 / 2)) (lt_min hδ (by norm_num))
    have hac : a ≤ 1 / 2 := (lt_of_lt_of_le haδ (min_le_right _ _)).le
    exact ⟨a, ha, lt_of_lt_of_le haδ (min_le_left _ _),
      adaptedEnergy_of_bezoutCorrected_loss ha hac hL⟩

end GaloisForLFunctions.ArithmeticCompensationTheory
