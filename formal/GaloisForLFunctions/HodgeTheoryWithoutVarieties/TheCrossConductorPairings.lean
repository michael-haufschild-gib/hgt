import GaloisForLFunctions.HodgeTheoryWithoutVarieties.TheConductorGramIsGradedByTheLcm
import GaloisForLFunctions.CompletedArithmeticForms.CompleteWeilResidualLevelOfDistribution
import GaloisForLFunctions.CompletedArithmeticForms.RamanujanConductorFrames
import GaloisForLFunctions.CompletedArithmeticForms.CompleteWeilConductorAveragePositivity
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandTopTailBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TelescopedConductorSplitAndOneNinthWeilPositivity
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BilinearConductorResidualsAndOneEighthPackets
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.EveryEighthRootMultipleReceivesTheTiltedSpline

/-!
# The cross-conductor pairings

In the conductor basis (normalized Ramanujan packets `r̂_e`) the complete Weil form `W = W_{c,N}`
has the entries `⟨W r̂_e, r̂_{e'}⟩`. With the completed conductor energies `E_e(c)` and the
quasimode residuals `ρ_e = W r̂_e − E_e(c) r̂_e`, every entry splits into two channels
(`inner_completeWeil_conductors`):

  `⟨W r̂_e, r̂_{e'}⟩ = E_e(c) ⟨r̂_e, r̂_{e'}⟩ + ⟨ρ_e, r̂_{e'}⟩`.

The first is the Gram channel (the packets are not exactly orthogonal), the second the residual
channel. The bounds below depend on the overlap regime; the tilted unit spline has margins
`E_e(c) ≥ κ₀ min(1, (e/c)⁷)`, and its overlap is measured in powers of `log N`.

* **Relative bound up to the eighth root** (`exists_relative_conductorDeviation_sum_le`). Divided
  by the margins `E_e E_{e'}`, the squared residual channels of all pairs of conductors
  `e, e' ≤ Q ≤ (log N)^A` sum to `O((c⁷ + Q²(1 + log Q)²)² (c(1 + log c)²(log N)^{1/k}/log N)²)`
  (bilinear residuals, CriticalArithmeticCorrelationTheory). The cross pairings stay below the
  margins as long as `c⁸ = o((log N)^{1−ε})`: exponent `7` from the margin, `1` from the bilinear
  rate.
* **Whole space below the ninth root** (`eventually_conductorGram_ge_floor`,
  `eventually_lcmCrossPairings_le_margin`). For `1 ≤ c ≤ (log N)^α`, `α < 1/9`, the conductor Gram
  of every finite family of conductors dominates `F/(2c⁷)` times the Euclidean Gram of the
  packets. In lcm form: for every `m ≤ N`, the cross pairings of lcm `m` stay below the Möbius
  combination of the star pole energies by at least `φ(m) F/(2c⁷) ‖r_m‖²`.
* **Every fixed conductor below the eighth root**
  (`eventually_lcmCrossPairings_le_margin_below_one_eighth`): the same lcm margin for each conductor
  `m ≤ M₀`, `α < 1/8`.
* **Quadratic control over all conductors at the eighth root is RH**
  (`riemannHypothesis_iff_conductorGram_nonneg_eighthRoot`). The conductors `e ≤ N` are a basis of
  the horizon, so positivity of their Gram is positivity of the complete form. At every overlap
  `2K(log N)^{1/8}` that is RH. The exponent of the relative bound is therefore the RH exponent;
  at `c⁸ ≍ log N` the relative cross pairings are of order one and only their exact size decides.
* **Mean square, beyond the eighth root** (`sum_sq_conductorDeviation_le`,
  `tendsto_conductorDeviation_rhComplete`). Bessel's inequality for the conductor frame (upper
  Riesz bound `6`) bounds the Hilbert–Schmidt mass of the residual channels by `6 Σ_e ‖ρ_e‖²`. By
  the level of distribution of the residuals this is `o(Σ_e E_e(c)²)` for the conductors
  `e ≤ N^θ`, `θ < 1/2`, at every overlap `2(log N)^α`, `α < 1/2`. Unweighted, the cross pairings
  are small even past the RH exponent. The mean square is carried by the large margins, so it
  cannot see the small ones that positivity must beat.
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.ArithmeticLorentzianGeometry GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.CompletedArithmeticForms (completeWeilConductorResidual conductorSubspace
  mem_conductorSubspace_normalizedRamanujanHorizonVector ramanujanConductor_upper_riesz
  tendsto_tiltedUnitSpline_completeWeil_residual_rhComplete)
open GaloisForLFunctions.CriticalArithmeticCorrelationTheory
  (eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_ninth
    eventually_tiltedUnitSpline_fixed_conductorSubspace_energy_ge_below_one_eighth
    exists_tiltedUnitSpline_bilinear_relative_residual_sum_le oneNinthPowerLogExponent
    oneEighthPowerLogExponent tiltedSplineSpectralFloorConstant)
open GaloisForLFunctions.BezoutValuationIncidence (moebiusReal)

namespace GaloisForLFunctions.HodgeTheoryWithoutVarieties

/-! ### Two channels -/

/-- **Gram channel and residual channel** of a cross-conductor pairing. -/
theorem inner_completeWeil_conductors (φ : ℝ → ℝ) (c : ℝ) (N e e' : ℕ) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector e N),
        normalizedRamanujanHorizonVector e' N⟫ =
      completedConductorEnergy φ c e *
          ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector e' N⟫ +
        ⟪completeWeilConductorResidual φ c N e, normalizedRamanujanHorizonVector e' N⟫ := by
  rw [completeWeilConductorResidual, inner_sub_left, real_inner_smul_left]
  ring

/-- The complete Weil energy of a conductor combination is its conductor Gram. -/
theorem completeWeilEnergy_sum_conductors (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (S : Finset ℕ)
    (b : ℕ → ℝ) :
    completeWeilEnergy φ c N (∑ e ∈ S, b e • normalizedRamanujanHorizonVector e N) =
      ∑ e ∈ S, ∑ e' ∈ S, b e * b e' *
        ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector e N),
          normalizedRamanujanHorizonVector e' N⟫ := by
  rw [completeWeilEnergy, map_sum, sum_inner]
  refine sum_congr rfl fun e _ => ?_
  rw [map_smul, inner_sum, mul_sum]
  refine sum_congr rfl fun e' _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-! ### Relative bound up to the eighth root -/

/-- **The cross pairings below the margins, relative form.** The deviations of the cross pairings
from their Gram channel, squared and divided by `E_e E_{e'}`, sum over all pairs of conductors up
to `Q ≤ (log N)^A` to `O((c⁷ + Q²(1 + log Q)²)² · rate²)`, with the bilinear rate
`c(1 + log c)²(log N)^{1/k}/log N + c⁵ log N/N`. -/
theorem exists_relative_conductorDeviation_sum_le :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.log (N : ℝ) ^ A →
        (∑ e ∈ Icc 1 Q, ∑ e' ∈ Icc 1 Q,
          (⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
                (normalizedRamanujanHorizonVector e N), normalizedRamanujanHorizonVector e' N⟫ -
              completedConductorEnergy tiltedUnitSpline c e *
                ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector e' N⟫) ^ 2 /
            (completedConductorEnergy tiltedUnitSpline c e *
              completedConductorEnergy tiltedUnitSpline c e')) ≤
          K * (c ^ 7 + (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) ^ 2 *
            (c * (1 + Real.log c) ^ 2 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 5 * Real.log N / (N : ℝ)) ^ 2 := by
  obtain ⟨K, hK, h⟩ := exists_tiltedUnitSpline_bilinear_relative_residual_sum_le
  refine ⟨K, hK, fun A hA k hk => ?_⟩
  filter_upwards [h A hA k hk] with N hN c hc hcN Q hQ
  have heq : ∀ e e' : ℕ,
      (⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector e N), normalizedRamanujanHorizonVector e' N⟫ -
          completedConductorEnergy tiltedUnitSpline c e *
            ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector e' N⟫) ^ 2 =
        |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
              (normalizedRamanujanHorizonVector e N) -
            completedConductorEnergy tiltedUnitSpline c e • normalizedRamanujanHorizonVector e N,
          normalizedRamanujanHorizonVector e' N⟫| ^ 2 := by
    intro e e'
    rw [sq_abs, inner_sub_left, real_inner_smul_left]
  simp only [heq]
  exact hN c hc hcN Q hQ

/-! ### Margins in lcm form -/

theorem ramanujanHorizonVector_eq_smul {N : ℕ} (hN : 0 < Real.log N) (m : ℕ) :
    ramanujanHorizonVector m N =
      Real.sqrt (Real.log N) • normalizedRamanujanHorizonVector m N := by
  rw [normalizedRamanujanHorizonVector, smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hN).ne',
    one_smul]

/-- A floor `κ‖r_m‖²` for the energy of the conductor `m` keeps the cross pairings of lcm `m` below
the Möbius combination of the star pole energies by `φ(m) κ ‖r_m‖²`. -/
theorem lcmCrossPairings_le_of_floor {φ : ℝ → ℝ} (hφ : EdgeHodgeTheory.Admissible φ) {c : ℝ}
    (hc : 0 < c) {N m : ℕ} (hm : m ∈ Icc 1 N) {κ : ℝ}
    (hfloor : κ * ‖ramanujanHorizonVector m N‖ ^ 2 ≤
      completeWeilEnergy φ c N (ramanujanHorizonVector m N)) :
    ∑ p ∈ (lcmPairs m).erase (m, m), Real.sqrt (p.1.totient : ℝ) *
        Real.sqrt (p.2.totient : ℝ) * conductorGram (completeWeilMatrix φ c N) p.1 p.2 ≤
      ∑ d ∈ m.divisors, moebiusReal (m / d) *
          ((d : ℝ) * completeWeilEnergy φ (starOverlap c N d) (N / d)
            (horizonPoleVector (N / d))) -
        (m.totient : ℝ) * (κ * ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2) := by
  rw [ramanujanHorizonVector_norm_sq, completeWeilEnergy_eq_qf] at hfloor
  have hG : conductorGram (completeWeilMatrix φ c N) m m =
      qf (completeWeilMatrix φ c N) (fun n => ramanujanHorizonVector m N n) := rfl
  have hid := totient_mul_conductorEnergy_eq_lcm hφ hc (mem_Icc.mp hm).1 (mem_Icc.mp hm).2
  have hlow : (m.totient : ℝ) * (κ * ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2) ≤
      (m.totient : ℝ) * conductorGram (completeWeilMatrix φ c N) m m := by
    rw [hG]
    exact mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg _)
  linarith

/-- **Whole space below the ninth root: every conductor family stays above the floor.** -/
theorem eventually_conductorGram_ge_floor {α : ℝ} (hα0 : 0 < α)
    (hα : α < oneNinthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α → ∀ (S : Finset ℕ) (b : ℕ → ℝ),
      tiltedSplineSpectralFloorConstant / (2 * c ^ 7) *
          ‖∑ e ∈ S, b e • normalizedRamanujanHorizonVector e N‖ ^ 2 ≤
        ∑ e ∈ S, ∑ e' ∈ S, b e * b e' *
          ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector e N), normalizedRamanujanHorizonVector e' N⟫ := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_ninth
    hα0 hα] with N hN c hc1 hc S b
  rw [← completeWeilEnergy_sum_conductors]
  exact hN c hc1 hc _

/-- **Whole space below the ninth root, lcm form.** For every conductor `m ≤ N`, the cross pairings
of lcm `m` stay below the Möbius combination of the star pole energies by `φ(m) F/(2c⁷) ‖r_m‖²`. -/
theorem eventually_lcmCrossPairings_le_margin {α : ℝ} (hα0 : 0 < α)
    (hα : α < oneNinthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α → ∀ m ∈ Icc 1 N,
      ∑ p ∈ (lcmPairs m).erase (m, m), Real.sqrt (p.1.totient : ℝ) *
          Real.sqrt (p.2.totient : ℝ) *
            conductorGram (completeWeilMatrix tiltedUnitSpline c N) p.1 p.2 ≤
        ∑ d ∈ m.divisors, moebiusReal (m / d) *
            ((d : ℝ) * completeWeilEnergy tiltedUnitSpline (starOverlap c N d) (N / d)
              (horizonPoleVector (N / d))) -
          (m.totient : ℝ) * (tiltedSplineSpectralFloorConstant / (2 * c ^ 7) *
            ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2) := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_ninth
    hα0 hα] with N hN c hc1 hc m hm
  exact lcmCrossPairings_le_of_floor EdgeHodgeTheory.admissible_tiltedUnitSpline (by linarith) hm
    (hN c hc1 hc _)

/-- **Every fixed conductor below the eighth root, lcm form.** -/
theorem eventually_lcmCrossPairings_le_margin_below_one_eighth (M₀ : ℕ) {α : ℝ} (hα0 : 0 < α)
    (hα : α < oneEighthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α → ∀ m ∈ Icc 1 M₀,
      ∑ p ∈ (lcmPairs m).erase (m, m), Real.sqrt (p.1.totient : ℝ) *
          Real.sqrt (p.2.totient : ℝ) *
            conductorGram (completeWeilMatrix tiltedUnitSpline c N) p.1 p.2 ≤
        ∑ d ∈ m.divisors, moebiusReal (m / d) *
            ((d : ℝ) * completeWeilEnergy tiltedUnitSpline (starOverlap c N d) (N / d)
              (horizonPoleVector (N / d))) -
          (m.totient : ℝ) * (tiltedSplineSpectralFloorConstant / (2 * c ^ 7) *
            ∑ n ∈ Icc 1 N, ramanujanPoleProfile m n ^ 2) := by
  filter_upwards [eventually_tiltedUnitSpline_fixed_conductorSubspace_energy_ge_below_one_eighth
    M₀ hα0 hα, eventually_ge_atTop M₀, eventually_ge_atTop 2] with N hN hMN hN2 c hc1 hc m hm
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmem : ramanujanHorizonVector m N ∈ conductorSubspace M₀ N := by
    rw [ramanujanHorizonVector_eq_smul hlog]
    exact Submodule.smul_mem _ _ (mem_conductorSubspace_normalizedRamanujanHorizonVector hm)
  exact lcmCrossPairings_le_of_floor EdgeHodgeTheory.admissible_tiltedUnitSpline (by linarith)
    (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hm).2.trans hMN⟩) (hN c hc1 hc _ hmem)

/-! ### Quadratic control over all conductors -/

/-- The complete form is positive semidefinite iff its conductor Gram over all conductors `e ≤ N`
is. -/
theorem forall_completeWeilEnergy_nonneg_iff_conductorGram (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    (∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), 0 ≤ completeWeilEnergy φ c N x) ↔
      ∀ b : ℕ → ℝ, 0 ≤ ∑ e ∈ Icc 1 N, ∑ e' ∈ Icc 1 N,
        b e * b e' * conductorGram (completeWeilMatrix φ c N) e e' := by
  rw [← forall_qf_nonneg_iff_conductorGram]
  constructor
  · intro h x
    have hx := h (WithLp.toLp 2 x)
    rwa [completeWeilEnergy_eq_qf] at hx
  · intro h x
    rw [completeWeilEnergy_eq_qf]
    exact h _

/-- **Quadratic control of all cross pairings at the eighth root is RH.** RH holds iff for every
`K > 0`, eventually, the conductor Gram of the complete form at overlap `2K(log N)^{1/8}` over all
conductors `e ≤ N` is positive semidefinite. -/
theorem riemannHypothesis_iff_conductorGram_nonneg_eighthRoot :
    RiemannHypothesis ↔ ∀ K : ℝ, 0 < K → ∀ᶠ N : ℕ in atTop, ∀ b : ℕ → ℝ,
      0 ≤ ∑ e ∈ Icc 1 N, ∑ e' ∈ Icc 1 N, b e * b e' *
        conductorGram (completeWeilMatrix tiltedUnitSpline (2 * K * Real.log N ^ (1 / 8 : ℝ)) N)
          e e' := by
  rw [riemannHypothesis_iff_tiltedSpline_completeWeil_nonneg_every_eighthRoot_multiple]
  exact forall₂_congr fun K _ => eventually_congr (Eventually.of_forall fun N =>
    forall_completeWeilEnergy_nonneg_iff_conductorGram _ _ N)

/-! ### Mean square -/

/-- **Bessel's inequality for the conductor frame.** -/
theorem sum_inner_normalizedRamanujan_sq_le {M N : ℕ} (hMN : M * M ≤ N)
    (hL : 4 * Real.exp 7 ≤ Real.log N) (v : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ∑ e ∈ Icc 1 M, ⟪v, normalizedRamanujanHorizonVector e N⟫ ^ 2 ≤ 6 * ‖v‖ ^ 2 := by
  have hy : ‖∑ e ∈ Icc 1 M, ⟪v, normalizedRamanujanHorizonVector e N⟫ •
      normalizedRamanujanHorizonVector e N‖ ^ 2 ≤
        6 * ∑ e ∈ Icc 1 M, ⟪v, normalizedRamanujanHorizonVector e N⟫ ^ 2 :=
    ramanujanConductor_upper_riesz hMN hL fun e => ⟪v, normalizedRamanujanHorizonVector e N⟫
  have hSy : ∑ e ∈ Icc 1 M, ⟪v, normalizedRamanujanHorizonVector e N⟫ ^ 2 =
      ⟪v, ∑ e ∈ Icc 1 M, ⟪v, normalizedRamanujanHorizonVector e N⟫ •
        normalizedRamanujanHorizonVector e N⟫ := by
    rw [inner_sum]
    exact sum_congr rfl fun e _ => by rw [real_inner_smul_right, sq]
  have hS0 : 0 ≤ ∑ e ∈ Icc 1 M, ⟪v, normalizedRamanujanHorizonVector e N⟫ ^ 2 :=
    sum_nonneg fun e _ => sq_nonneg _
  generalize ∑ e ∈ Icc 1 M, ⟪v, normalizedRamanujanHorizonVector e N⟫ •
    normalizedRamanujanHorizonVector e N = y at hy hSy
  generalize ∑ e ∈ Icc 1 M, ⟪v, normalizedRamanujanHorizonVector e N⟫ ^ 2 = S at hy hSy hS0 ⊢
  have hle : S ≤ ‖v‖ * ‖y‖ := by
    rw [hSy]
    exact real_inner_le_norm v y
  have key : S * S ≤ 6 * ‖v‖ ^ 2 * S := by
    calc S * S ≤ (‖v‖ * ‖y‖) * (‖v‖ * ‖y‖) := mul_self_le_mul_self hS0 hle
      _ = ‖v‖ ^ 2 * ‖y‖ ^ 2 := by ring
      _ ≤ ‖v‖ ^ 2 * (6 * S) := mul_le_mul_of_nonneg_left hy (sq_nonneg _)
      _ = 6 * ‖v‖ ^ 2 * S := by ring
  rcases hS0.eq_or_lt with h | h
  · rw [← h]
    positivity
  · exact le_of_mul_le_mul_right key h

/-- **The residual channel carries the deviations.** The Hilbert–Schmidt mass of the deviations of
the cross pairings from their Gram channel is at most `6 Σ_e ‖ρ_e‖²`. -/
theorem sum_sq_conductorDeviation_le (φ : ℝ → ℝ) (c : ℝ) {M N : ℕ} (hMN : M * M ≤ N)
    (hL : 4 * Real.exp 7 ≤ Real.log N) :
    ∑ e ∈ Icc 1 M, ∑ e' ∈ Icc 1 M,
        (⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector e N),
            normalizedRamanujanHorizonVector e' N⟫ -
          completedConductorEnergy φ c e *
            ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector e' N⟫) ^ 2 ≤
      6 * ∑ e ∈ Icc 1 M, ‖completeWeilConductorResidual φ c N e‖ ^ 2 := by
  rw [mul_sum]
  refine sum_le_sum fun e _ => ?_
  simp only [inner_completeWeil_conductors, add_sub_cancel_left]
  exact sum_inner_normalizedRamanujan_sq_le hMN hL _

theorem floor_rpow_mul_le {θ : ℝ} (hθ : θ ≤ 1 / 2) {N : ℕ} (hN : 1 ≤ N) :
    ⌊(N : ℝ) ^ θ⌋₊ * ⌊(N : ℝ) ^ θ⌋₊ ≤ N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (by linarith) θ
  have hfl := Nat.floor_le h0
  have h : ((⌊(N : ℝ) ^ θ⌋₊ : ℝ) * ⌊(N : ℝ) ^ θ⌋₊) ≤ N := by
    calc ((⌊(N : ℝ) ^ θ⌋₊ : ℝ) * ⌊(N : ℝ) ^ θ⌋₊) ≤ (N : ℝ) ^ θ * (N : ℝ) ^ θ :=
          mul_le_mul hfl hfl (Nat.cast_nonneg _) h0
      _ = (N : ℝ) ^ (θ + θ) := (Real.rpow_add (by linarith) _ _).symm
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
      _ = N := Real.rpow_one _
  exact_mod_cast h

/-- **Mean square, beyond the eighth root.** At overlap `2(log N)^α`, `α < 1/2`, for the conductors
`e ≤ N^θ`, `θ < 1/2`, the Hilbert–Schmidt mass of the deviations of the cross pairings from their
Gram channel is `o(Σ_e E_e(c)²)`. -/
theorem tendsto_conductorDeviation_rhComplete {α θ : ℝ} (hα0 : 0 < α) (hα : α < 1 / 2)
    (hθ0 : 0 < θ) (hθ : θ < 1 / 2) :
    Tendsto (fun N : ℕ =>
      (∑ e ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊, ∑ e' ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
        (⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (2 * Real.log N ^ α) N)
              (normalizedRamanujanHorizonVector e N), normalizedRamanujanHorizonVector e' N⟫ -
            completedConductorEnergy tiltedUnitSpline (2 * Real.log N ^ α) e *
              ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector e' N⟫) ^ 2) /
      ∑ e ∈ Icc 1 ⌊(N : ℝ) ^ θ⌋₊,
        completedConductorEnergy tiltedUnitSpline (2 * Real.log N ^ α) e ^ 2)
      atTop (𝓝 0) := by
  have hlim :=
    (tendsto_tiltedUnitSpline_completeWeil_residual_rhComplete hα0 hα hθ0 hθ).const_mul 6
  rw [mul_zero] at hlim
  refine squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _)
      (sum_nonneg fun _ _ => sq_nonneg _)) ?_ hlim
  have hlog := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (4 * Real.exp 7)
  filter_upwards [hlog, eventually_ge_atTop 1] with N hL hN
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right
    (sum_sq_conductorDeviation_le _ _ (floor_rpow_mul_le hθ.le hN) hL)
    (sum_nonneg fun _ _ => sq_nonneg _)

end GaloisForLFunctions.HodgeTheoryWithoutVarieties
