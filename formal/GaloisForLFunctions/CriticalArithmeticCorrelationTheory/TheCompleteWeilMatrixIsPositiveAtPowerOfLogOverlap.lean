import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilLogarithmicReserveSurvivesGrowingOverlap

/-!
# Complete Weil positivity at power-of-logarithm overlap

This module proves that the complete Weil matrix `completeWeilMatrix tiltedUnitSpline c N` is
positive definite on **all** horizon vectors uniformly across a power-of-logarithm overlap window
`1 ≤ c ≤ (log N)^α` (`0 < α < powerLogPositivityExponent`), together with its uniform `c⁻⁷`
spectral floor, literal `weilQuad` nonnegativity, and zero-mass-loss prime-defect reserve.

## Proof mechanism

1. **Shifted spectral-floor matrix and low-band reduction.** Subtracting half of the polynomial
   completed-conductor floor `tiltedSplineSpectralFloorConstant / (2 * c ^ 7)` leaves every
   conductor quasimode at energy `≥ κ / (2 * c ^ 7)` with unchanged residual. Setting
   `Q₁(N) := ⌊(log N)^{1/12}⌋₊`, `matrix_posDef_of_uniform_conductor_budget` reduces all-vector
   positivity of `spectralFloorWeilMatrix c N` to ruling out unit vectors `x` with
   `completeWeilEnergy tiltedUnitSpline c N x ≤ κ / 2` and
   `1 / 4 < ‖x - (conductorSubspace Q₁ N).starProjection x‖ ^ 2`.
2. **Low-band orthogonal decoupling (`m ≤ Q₁`).** Splitting `x = p + z` along
   `conductorSubspace Q₁ N` and its orthogonal complement cancels the diagonal conductor action in
   `⟪W p, z⟫`, while polarized harmonic Gram bounds keep `⟪W p, p⟫ ≥ -1 / 4`, producing a unit
   vector `zHat ∈ (conductorSubspace Q₁ N)ᗮ` of bounded complete Weil energy.
3. **High-tail cross-pairing suppression (`m > R'`).** Polynomial defect reserve bounds
   `poleDefect` on `zHat` by `O(c^{16})`. Quantitative exponential confinement at threshold
   `η = (M₁ ^ 2 * c ^ 10)⁻¹` projects `zHat = u + w` onto `conductorSubspace R' N`
   (`log R' ≤ C_R * c ^ 46 + log Q₁`), where conductor-subspace operator bounds make
   `2 |⟪W u, w⟫| - ⟪W w, w⟫ ≤ 1`.
4. **Coercivity above `Q₁`.** Decomposing `u = uLow + y` into its `O(log R' / log N)` low-band leak
   and its `(Q₁, R']` packet `y`, the intermediate-band summation-by-parts bound suppresses
   `⟪overlapMatrix y, y⟫` to `o(1) ‖y‖ ^ 2` while the reverse defect gap forces
   `renormalizedPrimeEnergy N y ≥ (log Q₁ / conductorCutoffConstant - O(1)) ‖y‖ ^ 2`, dominating
   `log c ≤ α log log N` whenever `α < powerLogPositivityExponent`.
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Matrix Classical

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

/-! ### 1. Constants, spectral-floor matrix, and polarized Gram helpers -/

/-- Explicit positive exponent threshold for power-of-logarithm all-vector positivity. -/
def powerLogPositivityExponent : ℝ :=
  min (1 / 500) (1 / (60 * conductorCutoffConstant))

theorem powerLogPositivityExponent_pos : 0 < powerLogPositivityExponent := by
  have hD := conductorCutoffConstant_pos
  unfold powerLogPositivityExponent
  exact lt_min (by norm_num) (by positivity)

/-- Explicit positive coefficient in the polynomial completed-conductor floor of `tiltedUnitSpline`. -/
def tiltedSplineSpectralFloorConstant : ℝ :=
  2 * tiltedSplineTailConstant / ∫ u, tiltedUnitSpline u ^ 2

theorem tiltedSplineSpectralFloorConstant_pos : 0 < tiltedSplineSpectralFloorConstant :=
  div_pos (mul_pos zero_lt_two tiltedSplineTailConstant_pos) integral_tiltedUnitSpline_sq_pos

/-- Complete Weil matrix shifted down by half its polynomial conductor floor. -/
def spectralFloorWeilMatrix (c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  completeWeilMatrix tiltedUnitSpline c N -
    (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) • 1

theorem spectralFloorWeilMatrix_isHermitian (c : ℝ) (N : ℕ) :
    (spectralFloorWeilMatrix c N).IsHermitian :=
  (completeWeilMatrix_isHermitian tiltedUnitSpline c N).sub
    (Matrix.isHermitian_one.smul (by rfl))

private theorem identity_euclid_apply {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]

theorem spectralFloorWeilMatrix_inner (c : ℝ) {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) x, x⟫ =
      completeWeilEnergy tiltedUnitSpline c N x -
        (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2 := by
  simp only [spectralFloorWeilMatrix, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, identity_euclid_apply, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, completeWeilEnergy]

theorem spectralFloorWeilMatrix_residual_eq (c : ℝ) (m N : ℕ) :
    Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
        (normalizedRamanujanHorizonVector m N) -
      (completedConductorEnergy tiltedUnitSpline c m -
        tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) •
        normalizedRamanujanHorizonVector m N =
    Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
        (normalizedRamanujanHorizonVector m N) -
      completedConductorEnergy tiltedUnitSpline c m •
        normalizedRamanujanHorizonVector m N := by
  simp only [spectralFloorWeilMatrix, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, identity_euclid_apply]
  module

theorem spectralFloor_conductor_energy_ge {c : ℝ} (hc : 1 ≤ c) {m : ℕ} (hm : 0 < m) :
    tiltedSplineSpectralFloorConstant / (2 * c ^ 7) ≤
      completedConductorEnergy tiltedUnitSpline c m -
        tiltedSplineSpectralFloorConstant / (2 * c ^ 7) := by
  have hfloor := tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hc hm
  change tiltedSplineSpectralFloorConstant / c ^ 7 ≤
    completedConductorEnergy tiltedUnitSpline c m at hfloor
  have h2 : tiltedSplineSpectralFloorConstant / c ^ 7 =
      2 * (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) := by ring
  linarith only [hfloor, h2]

private theorem hermitian_inner_add_eq {N : ℕ}
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin A (x + y), x + y⟫ =
      ⟪Matrix.toEuclideanLin A x, x⟫ + 2 * ⟪Matrix.toEuclideanLin A x, y⟫ +
        ⟪Matrix.toEuclideanLin A y, y⟫ := by
  have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) y x
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym,
    real_inner_comm y (Matrix.toEuclideanLin A x)]
  ring

private theorem completeWeilEnergy_add_eq (φ : ℝ → ℝ) (c : ℝ) {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (x + y) =
      completeWeilEnergy φ c N x +
        2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ +
        completeWeilEnergy φ c N y :=
  hermitian_inner_add_eq (completeWeilMatrix_isHermitian φ c N) x y

private theorem renormalizedPrimeEnergy_add_eq {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    renormalizedPrimeEnergy N (x + y) =
      renormalizedPrimeEnergy N x + renormalizedPrimeEnergy N y +
        2 * ⟪Real.log N • x - Matrix.toEuclideanLin (fullPrimeMatrix N) x, y⟫ := by
  have hnorm : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫ + ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right, inner_add_right,
      real_inner_comm y x, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  unfold renormalizedPrimeEnergy
  rw [hnorm, hermitian_inner_add_eq (fullPrimeMatrix_isHermitian N) x y,
    inner_sub_left, real_inner_smul_left]
  ring

private theorem sub_starProjection_mem_orthogonal {N : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)))
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    x - K.starProjection x ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [real_inner_comm]
  exact K.starProjection_inner_eq_zero x v hv

private theorem exists_raw_approx_of_starProjection_sq_le {Q N : ℕ} (hN : 2 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N))
    (h : ‖x - (conductorSubspace Q N).starProjection x‖ ^ 2 ≤ 1 / 4) :
    ∃ b : ℕ → ℝ,
      (∑ n ∈ Icc 1 N,
        (primeHorizonExtension x n -
          ∑ m ∈ Icc 1 Q, b m * ramanujanPoleProfile m n) ^ 2) ≤ 1 / 4 := by
  let p := (conductorSubspace Q N).starProjection x
  obtain ⟨a, -, hp_eq⟩ := (mem_conductorSubspace_iff (M := Q) (N := N) (x := p)).mp
    ((conductorSubspace Q N).starProjection_apply_mem x)
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hs : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr hlog
  let b : ℕ → ℝ := fun m => a m / Real.sqrt (Real.log N)
  refine ⟨b, ?_⟩
  have hsum_eq : (∑ n ∈ Icc 1 N,
      (primeHorizonExtension x n -
        ∑ m ∈ Icc 1 Q, b m * ramanujanPoleProfile m n) ^ 2) = ‖x - p‖ ^ 2 := by
    rw [← sum_primeHorizonExtension_sq (x - p)]
    refine sum_congr rfl fun n hn => ?_
    congr 1
    rw [primeHorizonExtension_coe (x - p) ⟨n, hn⟩, primeHorizonExtension_coe x ⟨n, hn⟩]
    change x ⟨n, hn⟩ - ∑ m ∈ Icc 1 Q, b m * ramanujanPoleProfile m n = x ⟨n, hn⟩ - p ⟨n, hn⟩
    congr 1
    rw [hp_eq]
    change _ = (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : PrimeHorizonIndex N => ℝ) ⟨n, hn⟩)
      (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N)
    rw [map_sum]
    refine sum_congr rfl fun m _ => ?_
    change b m * ramanujanPoleProfile m n =
      a m * ((Real.sqrt (Real.log N))⁻¹ * ramanujanPoleProfile m n)
    dsimp only [b]
    field_simp [hs.ne']
  rw [hsum_eq]
  exact h

/-- Polarized Gram discrepancy for arbitrary coefficient pairs over `Icc 1 Q` (`Q * Q ≤ N`). -/
private theorem abs_inner_sum_normalizedRamanujanHorizonVector_sub_le {Q N : ℕ}
    (hQ : 2 ≤ Q) (hQN : Q * Q ≤ N) (a b : ℕ → ℝ) :
    |⟪∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N,
        ∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N⟫ -
      ∑ m ∈ Icc 1 Q, a m * b m| ≤
      9 * (1 + Real.log Q) / Real.log N *
        Real.sqrt (∑ m ∈ Icc 1 Q, a m ^ 2) * Real.sqrt (∑ m ∈ Icc 1 Q, b m ^ 2) := by
  let A := ∑ m ∈ Icc 1 Q, a m ^ 2
  let B := ∑ m ∈ Icc 1 Q, b m ^ 2
  have hA0 : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hB0 : 0 ≤ B := sum_nonneg fun _ _ => sq_nonneg _
  by_cases hAz : A = 0
  · have ha0 : ∀ m ∈ Icc 1 Q, a m = 0 := fun m hm =>
      sq_eq_zero_iff.mp ((sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (a k))).mp hAz m hm)
    have hu0 : (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N) = 0 :=
      sum_eq_zero fun m hm => by rw [ha0 m hm, zero_smul]
    have hs0 : (∑ m ∈ Icc 1 Q, a m * b m) = 0 :=
      sum_eq_zero fun m hm => by rw [ha0 m hm, zero_mul]
    simp [A, hAz, hu0, hs0]
  by_cases hBz : B = 0
  · have hb0 : ∀ m ∈ Icc 1 Q, b m = 0 := fun m hm =>
      sq_eq_zero_iff.mp ((sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (b k))).mp hBz m hm)
    have hv0 : (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) = 0 :=
      sum_eq_zero fun m hm => by rw [hb0 m hm, zero_smul]
    have hs0 : (∑ m ∈ Icc 1 Q, a m * b m) = 0 :=
      sum_eq_zero fun m hm => by rw [hb0 m hm, mul_zero]
    simp [B, hBz, hv0, hs0]
  have hAp : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
  have hBp : 0 < B := lt_of_le_of_ne hB0 (Ne.symm hBz)
  have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hAp
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBp
  let a' : ℕ → ℝ := fun m => a m / Real.sqrt A
  let b' : ℕ → ℝ := fun m => b m / Real.sqrt B
  have ha'sq : (∑ m ∈ Icc 1 Q, a' m ^ 2) = 1 := by
    have h1 : (∑ m ∈ Icc 1 Q, a' m ^ 2) = A / A := by
      dsimp only [a', A]; rw [sum_div]
      exact sum_congr rfl fun m _ => by rw [div_pow, Real.sq_sqrt hAp.le]
    rw [h1, div_self hAp.ne']
  have hb'sq : (∑ m ∈ Icc 1 Q, b' m ^ 2) = 1 := by
    have h1 : (∑ m ∈ Icc 1 Q, b' m ^ 2) = B / B := by
      dsimp only [b', B]; rw [sum_div]
      exact sum_congr rfl fun m _ => by rw [div_pow, Real.sq_sqrt hBp.le]
    rw [h1, div_self hBp.ne']
  let S := ∑ m ∈ Icc 1 Q, a' m * b' m
  have hplus_mass : (∑ m ∈ Icc 1 Q, (a' m + b' m) ^ 2) = 2 + 2 * S := by
    have hexp : (∑ m ∈ Icc 1 Q, (a' m + b' m) ^ 2) =
        (∑ m ∈ Icc 1 Q, a' m ^ 2) + (∑ m ∈ Icc 1 Q, b' m ^ 2) + 2 * S := by
      dsimp only [S]
      rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
      exact sum_congr rfl fun m _ => by ring
    rw [hexp, ha'sq, hb'sq]; ring
  have hminus_mass : (∑ m ∈ Icc 1 Q, (a' m - b' m) ^ 2) = 2 - 2 * S := by
    have hexp : (∑ m ∈ Icc 1 Q, (a' m - b' m) ^ 2) =
        (∑ m ∈ Icc 1 Q, a' m ^ 2) + (∑ m ∈ Icc 1 Q, b' m ^ 2) - 2 * S := by
      dsimp only [S]
      rw [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      exact sum_congr rfl fun m _ => by ring
    rw [hexp, ha'sq, hb'sq]; ring
  let u' := ∑ m ∈ Icc 1 Q, a' m • normalizedRamanujanHorizonVector m N
  let v' := ∑ m ∈ Icc 1 Q, b' m • normalizedRamanujanHorizonVector m N
  have hu'pv' : (∑ m ∈ Icc 1 Q, (a' m + b' m) • normalizedRamanujanHorizonVector m N) = u' + v' := by
    simp only [u', v', add_smul, sum_add_distrib]
  have hu'mv' : (∑ m ∈ Icc 1 Q, (a' m - b' m) • normalizedRamanujanHorizonVector m N) = u' - v' := by
    simp only [u', v', sub_smul, sum_sub_distrib]
  have hgp := abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le hQ hQN (fun m => a' m + b' m)
  have hgm := abs_norm_sum_normalizedRamanujanHorizonVector_sq_sub_le hQ hQN (fun m => a' m - b' m)
  rw [hu'pv', hplus_mass] at hgp
  rw [hu'mv', hminus_mass] at hgm
  have hpol : (‖u' + v'‖ ^ 2 - (2 + 2 * S)) - (‖u' - v'‖ ^ 2 - (2 - 2 * S)) =
      4 * (⟪u', v'⟫ - S) := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      inner_add_left, inner_add_right, inner_add_right,
      inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm v' u']
    ring
  have h4 : 4 * |⟪u', v'⟫ - S| ≤ 4 * (9 * (1 + Real.log Q) / Real.log N) := by
    have habs : |4 * (⟪u', v'⟫ - S)| ≤
        |‖u' + v'‖ ^ 2 - (2 + 2 * S)| + |‖u' - v'‖ ^ 2 - (2 - 2 * S)| := by
      rw [← hpol]; exact abs_sub _ _
    rw [abs_mul, show |(4 : ℝ)| = 4 by norm_num] at habs
    linarith only [habs, hgp, hgm]
  have h1 : |⟪u', v'⟫ - S| ≤ 9 * (1 + Real.log Q) / Real.log N := by linarith only [h4]
  have hu_eq : (∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N) = Real.sqrt A • u' := by
    dsimp only [u', a']; rw [Finset.smul_sum]
    exact sum_congr rfl fun m _ => by rw [smul_smul, mul_div_cancel₀ _ hsA.ne']
  have hv_eq : (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N) = Real.sqrt B • v' := by
    dsimp only [v', b']; rw [Finset.smul_sum]
    exact sum_congr rfl fun m _ => by rw [smul_smul, mul_div_cancel₀ _ hsB.ne']
  have hS_eq : (∑ m ∈ Icc 1 Q, a m * b m) = Real.sqrt A * (Real.sqrt B * S) := by
    dsimp only [S, a', b']
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    field_simp [hsA.ne', hsB.ne']
  rw [hu_eq, hv_eq, real_inner_smul_left, real_inner_smul_right, hS_eq,
    show Real.sqrt A * (Real.sqrt B * ⟪u', v'⟫) - Real.sqrt A * (Real.sqrt B * S) =
      Real.sqrt A * (Real.sqrt B * (⟪u', v'⟫ - S)) by ring,
    abs_mul, abs_mul, abs_of_pos hsA, abs_of_pos hsB]
  calc
    Real.sqrt A * (Real.sqrt B * |⟪u', v'⟫ - S|) ≤
        Real.sqrt A * (Real.sqrt B * (9 * (1 + Real.log Q) / Real.log N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 hsB.le) hsA.le
    _ = 9 * (1 + Real.log Q) / Real.log N * Real.sqrt A * Real.sqrt B := by ring

private theorem exists_matrix_polynomial_reserve :
    ∃ b B H : ℝ, 0 < b ∧ 0 < B ∧ 0 < H ∧
      ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, H * c ^ 8 ≤ (N : ℝ) →
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
          (b / c ^ 7) * poleDefect N (primeHorizonExtension x) - B * c ^ 9 * ‖x‖ ^ 2 ≤
            completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨b, B, H, hb, hB, hH, hr⟩ := exists_tiltedUnitSpline_complete_defect_reserve_polynomial
  refine ⟨b, B, H, hb, hB, hH, ?_⟩
  intro c hc N hN x
  have hc0 := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := (mul_pos hH (pow_pos hc0 8)).trans_le hN
  have hN1 : 1 ≤ N := by exact_mod_cast (show 0 < N by exact_mod_cast hN0)
  have hh := hr c hc N hN (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq] at hh
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc0 hN1, integral_atomDilate_sq (div_pos hc0 hN0)]
  exact hh

/-! ### 2. Low-band orthogonal decoupling (`m ≤ Q₁`) -/

/-- Decoupling the low conductor band `conductorSubspace Q₁ N` from a unit vector of small
complete Weil energy and nontrivial high-conductor mass produces a unit vector in
`(conductorSubspace Q₁ N)ᗮ` with uniformly bounded complete Weil energy. -/
private theorem low_band_decoupling_unit_orthogonal {Q₁ N : ℕ} {c : ℝ}
    (hQ₁ : 2 ≤ Q₁) (hQN : Q₁ * Q₁ ≤ N)
    (hlog : 18 * (1 + Real.log Q₁) ≤ Real.log N) (hc1 : 1 ≤ c)
    (hres_sum : (∑ m ∈ Icc 1 Q₁,
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m •
          normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ 1 / 128)
    (hgram_err : 9 * (1 + Real.log Q₁) / Real.log N *
      (|completeWeilSelfFinitePart tiltedUnitSpline 1| + 2 * Real.log Q₁ + 3 * c ^ 4) ≤ 1 / 16)
    {x : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hx : ‖x‖ = 1)
    (hxE : completeWeilEnergy tiltedUnitSpline c N x ≤ tiltedSplineSpectralFloorConstant / 2)
    (hdist : 1 / 4 < ‖x - (conductorSubspace Q₁ N).starProjection x‖ ^ 2) :
    ∃ zHat : EuclideanSpace ℝ (PrimeHorizonIndex N),
      zHat ∈ (conductorSubspace Q₁ N)ᗮ ∧ ‖zHat‖ = 1 ∧
      completeWeilEnergy tiltedUnitSpline c N zHat ≤
        2 * tiltedSplineSpectralFloorConstant + 2 := by
  let p := (conductorSubspace Q₁ N).starProjection x
  let z := x - p
  have hz_orth : z ∈ (conductorSubspace Q₁ N)ᗮ := sub_starProjection_mem_orthogonal _ x
  have hpyth := norm_starProjection_sq_add_sub_sq (conductorSubspace Q₁ N) x
  change ‖p‖ ^ 2 + ‖z‖ ^ 2 = ‖x‖ ^ 2 at hpyth
  rw [hx, one_pow] at hpyth
  have hp_le1 : ‖p‖ ≤ 1 := by nlinarith only [hpyth, sq_nonneg ‖z‖, norm_nonneg p]
  have hz_le1 : ‖z‖ ≤ 1 := by nlinarith only [hpyth, sq_nonneg ‖p‖, norm_nonneg z]
  have hz_gt : 1 / 2 < ‖z‖ := by nlinarith only [hdist, norm_nonneg z]
  have hz_pos : 0 < ‖z‖ := by linarith only [hz_gt]
  obtain ⟨a, -, hp_eq⟩ := (mem_conductorSubspace_iff (M := Q₁) (N := N) (x := p)).mp
    ((conductorSubspace Q₁ N).starProjection_apply_mem x)
  have ha_sq : (∑ m ∈ Icc 1 Q₁, a m ^ 2) ≤ 2 := by
    have hr := (half_and_three_halves_riesz_of_log_le hQ₁ hQN hlog a).1
    rw [← hp_eq] at hr
    nlinarith only [hr, hpyth, sq_nonneg ‖z‖]
  let r : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N) := fun m =>
    Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector m N) -
    completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N
  let dVec := ∑ m ∈ Icc 1 Q₁,
    (a m * completedConductorEnergy tiltedUnitSpline c m) •
      normalizedRamanujanHorizonVector m N
  let rVec := ∑ m ∈ Icc 1 Q₁, a m • r m
  have hWp_eq : Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) p =
      dVec + rVec := by
    rw [hp_eq, map_sum]
    dsimp only [dVec, rVec, r]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    rw [map_smul, smul_sub, mul_smul]
    abel
  have hrVec_norm : ‖rVec‖ ≤ 1 / 8 := by
    have htri : ‖rVec‖ ≤ ∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖ := by
      refine (norm_sum_le _ _).trans (sum_le_sum fun m _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 Q₁) (fun m => |a m|) (fun m => ‖r m‖)
    simp only [sq_abs] at hcs
    have hsq : (∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖) ^ 2 ≤ (1 / 8 : ℝ) ^ 2 := by
      calc
        _ ≤ (∑ m ∈ Icc 1 Q₁, a m ^ 2) * ∑ m ∈ Icc 1 Q₁, ‖r m‖ ^ 2 := hcs
        _ ≤ 2 * (1 / 128) := mul_le_mul ha_sq hres_sum
          (sum_nonneg fun _ _ => sq_nonneg _) zero_le_two
        _ = (1 / 8 : ℝ) ^ 2 := by norm_num
    have hsum0 : 0 ≤ ∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖ :=
      sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have hle : (∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖) ≤ 1 / 8 := by nlinarith only [hsq, hsum0]
    exact htri.trans hle
  have hcross : |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) p, z⟫| ≤
      1 / 8 := by
    have hd_mem : dVec ∈ conductorSubspace Q₁ N :=
      sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N _
    have hd_orth : ⟪dVec, z⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hd_mem hz_orth
    rw [hWp_eq, inner_add_left, hd_orth, zero_add]
    exact (abs_real_inner_le_norm rVec z).trans
      ((mul_le_mul hrVec_norm hz_le1 (norm_nonneg z) (by norm_num)).trans_eq (mul_one _))
  have hd_self : -(1 / 8 : ℝ) ≤ ⟪dVec, p⟫ := by
    let M_E := |completeWeilSelfFinitePart tiltedUnitSpline 1| + 2 * Real.log Q₁ + 3 * c ^ 4
    have hE_bounds : ∀ m ∈ Icc 1 Q₁,
        0 ≤ completedConductorEnergy tiltedUnitSpline c m ∧
          completedConductorEnergy tiltedUnitSpline c m ≤ M_E := by
      intro m hm
      obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
      have hpos : 0 ≤ completedConductorEnergy tiltedUnitSpline c m := by
        have hf := tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hc1 hm1
        have hpos' : 0 < (2 * tiltedSplineTailConstant / ∫ u, tiltedUnitSpline u ^ 2) / c ^ 7 :=
          div_pos tiltedSplineSpectralFloorConstant_pos (pow_pos (zero_lt_one.trans_le hc1) 7)
        linarith only [hf, hpos']
      have hlogm : Real.log m ≤ Real.log Q₁ :=
        Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmQ)
      have hup := completedConductorEnergy_le_of_one_le contDiff_tiltedUnitSpline
        tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc1 hm1
      exact ⟨hpos, by dsimp only [M_E]; linarith only [hup, hlogm]⟩
    have hME0 : 0 ≤ M_E := by
      have h2mem : 2 ∈ Icc 1 Q₁ := mem_Icc.mpr ⟨by omega, hQ₁⟩
      exact (hE_bounds 2 h2mem).1.trans (hE_bounds 2 h2mem).2
    have hdiag_nonneg : 0 ≤ ∑ m ∈ Icc 1 Q₁,
        (a m * completedConductorEnergy tiltedUnitSpline c m) * a m :=
      sum_nonneg fun m hm => by
        have h := (hE_bounds m hm).1
        nlinarith only [h, sq_nonneg (a m)]
    have hd_sq_le : (∑ m ∈ Icc 1 Q₁,
        (a m * completedConductorEnergy tiltedUnitSpline c m) ^ 2) ≤
        M_E ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun m hm => ?_
      obtain ⟨h0, hup⟩ := hE_bounds m hm
      have hesq : completedConductorEnergy tiltedUnitSpline c m ^ 2 ≤ M_E ^ 2 :=
        pow_le_pow_left₀ h0 hup 2
      nlinarith only [hesq, sq_nonneg (a m)]
    have hsqrt_d :
        Real.sqrt (∑ m ∈ Icc 1 Q₁,
          (a m * completedConductorEnergy tiltedUnitSpline c m) ^ 2) ≤
          M_E * Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2) := by
      calc
        _ ≤ Real.sqrt (M_E ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2) := Real.sqrt_le_sqrt hd_sq_le
        _ = M_E * Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hME0]
    have hpol := abs_inner_sum_normalizedRamanujanHorizonVector_sub_le hQ₁ hQN
      (fun m => a m * completedConductorEnergy tiltedUnitSpline c m) a
    rw [← hp_eq] at hpol
    have hcoef0 : 0 ≤ 9 * (1 + Real.log Q₁) / Real.log N := by
      have hL : 0 < Real.log N := by
        have := Real.log_natCast_nonneg Q₁; linarith only [hlog, this]
      have := Real.log_natCast_nonneg Q₁; positivity
    have herr_le : |⟪dVec, p⟫ - ∑ m ∈ Icc 1 Q₁,
        (a m * completedConductorEnergy tiltedUnitSpline c m) * a m| ≤ 1 / 8 := by
      calc
        _ ≤ 9 * (1 + Real.log Q₁) / Real.log N *
              Real.sqrt (∑ m ∈ Icc 1 Q₁,
                (a m * completedConductorEnergy tiltedUnitSpline c m) ^ 2) *
              Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2) := hpol
        _ ≤ 9 * (1 + Real.log Q₁) / Real.log N *
              (M_E * Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2)) *
              Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsqrt_d hcoef0) (Real.sqrt_nonneg _)
        _ = (9 * (1 + Real.log Q₁) / Real.log N * M_E) * ∑ m ∈ Icc 1 Q₁, a m ^ 2 := by
          rw [mul_assoc, mul_assoc, Real.mul_self_sqrt (sum_nonneg fun _ _ => sq_nonneg _)]
          ring
        _ ≤ (1 / 16) * 2 := mul_le_mul hgram_err ha_sq
          (sum_nonneg fun _ _ => sq_nonneg _) (by norm_num)
        _ = 1 / 8 := by norm_num
    linarith only [(abs_le.mp herr_le).1, hdiag_nonneg]
  have hp_self : -(1 / 4 : ℝ) ≤ completeWeilEnergy tiltedUnitSpline c N p := by
    unfold completeWeilEnergy
    rw [hWp_eq, inner_add_left]
    have hr_p : |⟪rVec, p⟫| ≤ 1 / 8 :=
      (abs_real_inner_le_norm rVec p).trans
        ((mul_le_mul hrVec_norm hp_le1 (norm_nonneg p) (by norm_num)).trans_eq (mul_one _))
    linarith only [hd_self, (abs_le.mp hr_p).1]
  have hz_energy : completeWeilEnergy tiltedUnitSpline c N z ≤
      tiltedSplineSpectralFloorConstant / 2 + 1 / 2 := by
    have hx_split : x = p + z := by dsimp only [z]; abel
    have hexp := completeWeilEnergy_add_eq tiltedUnitSpline c p z
    rw [← hx_split] at hexp
    linarith only [hexp, hxE, hp_self, (abs_le.mp hcross).1]
  let zHat := (‖z‖)⁻¹ • z
  refine ⟨zHat, Submodule.smul_mem _ _ hz_orth, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz_pos, inv_mul_cancel₀ hz_pos.ne']
  · have hscale : completeWeilEnergy tiltedUnitSpline c N zHat =
        (‖z‖⁻¹) ^ 2 * completeWeilEnergy tiltedUnitSpline c N z := by
      dsimp only [zHat, completeWeilEnergy]
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hscale]
    have hkappa0 : 0 < tiltedSplineSpectralFloorConstant := tiltedSplineSpectralFloorConstant_pos
    rcases le_or_gt (completeWeilEnergy tiltedUnitSpline c N z) 0 with hneg | hpos
    · have hle0 : (‖z‖⁻¹) ^ 2 * completeWeilEnergy tiltedUnitSpline c N z ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg
      linarith only [hle0, hkappa0]
    · have hinv_lt : (‖z‖⁻¹) ^ 2 ≤ 4 := by
        have h1 : ‖z‖⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀' hz_pos).mpr (by linarith only [hz_gt])
        calc
          (‖z‖⁻¹) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
          _ = 4 := by norm_num
      calc
        (‖z‖⁻¹) ^ 2 * completeWeilEnergy tiltedUnitSpline c N z ≤
            4 * (tiltedSplineSpectralFloorConstant / 2 + 1 / 2) :=
          mul_le_mul hinv_lt hz_energy hpos.le (by norm_num)
        _ = 2 * tiltedSplineSpectralFloorConstant + 2 := by ring

/-! ### 3. High-tail cross-pairing suppression (`m > R'`) -/

/-- Orthogonal cross-pairing bound `|⟪W u, w⟫| ≤ C_cross * c ^ 3 * ‖u‖ * ‖w‖` between
`u ∈ conductorSubspace R' N ⊓ (conductorSubspace 1 N)ᗮ` and `w ∈ (conductorSubspace R' N)ᗮ`. -/
private theorem exists_completeWeilMatrix_orthog_cross_le :
    ∃ C_cross : ℝ, 1 ≤ C_cross ∧
      ∀ {R' N : ℕ} {c : ℝ},
        2 ≤ R' → R' ^ 6 ≤ N → 18 * (1 + Real.log R') ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        (1 + Real.log R') / Real.sqrt (Real.log N) ≤ 1 →
        (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N) ≤ 1 →
        (R' : ℝ) * Real.sqrt (Real.log N / N) ≤ 1 →
      ∀ {u w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R' N → u ∈ (conductorSubspace 1 N)ᗮ →
        w ∈ (conductorSubspace R' N)ᗮ →
        |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤
          C_cross * c ^ 3 * ‖u‖ * ‖w‖ := by
  obtain ⟨C_pr, hC_pr, hpr⟩ := exists_fullPrimeMatrix_orthog_inner_le
  obtain ⟨C_od, hC_od, hod⟩ := exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_up, hC_up, hup⟩ := exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  let C_sep := 4 * (152 * (∫ t, |tiltedUnitSpline t|) ^ 2 / (∫ t, tiltedUnitSpline t ^ 2))
  have hC_sep0 : 0 ≤ C_sep := by
    have := integral_tiltedUnitSpline_sq_pos; dsimp only [C_sep]; positivity
  let C_cross := 2 * C_pr + 144 + C_sep + 3 * C_od + 2 * C_up + 1
  refine ⟨C_cross, by dsimp only [C_cross]; linarith [hC_pr, hC_od, hC_up, hC_sep0], ?_⟩
  intro R' N c hR' hR6N hlog hc1 hw1 hRNT_lin hRNT_up hlog_div1 hlog_div2 hR_sqrt
    u w hu hu1 hw
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hRR_N : R' * R' ≤ N := by
    have : R' ^ 2 ≤ R' ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simpa only [sq] using this.trans hR6N
  have hN2 : 2 ≤ N := by have := Nat.mul_le_mul hR' hR'; omega
  have hN1 : 1 ≤ N := by omega
  have hL1 : 1 ≤ Real.log N := by have := Real.log_natCast_nonneg R'; linarith only [hlog, this]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hw1_orth : w ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hw v (conductorSubspace_mono (by omega : 1 ≤ R') N hv)
  have huw_orth : ⟪u, w⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hu hw
  have h1lc_le : 1 + Real.log c ≤ 2 * c := by
    have hlc : Real.log c ≤ c - 1 := Real.log_le_sub_one_of_pos hc0
    linarith only [hlc, hc1]
  have hsqrt_1lc : Real.sqrt (1 + Real.log c) ≤ 2 * c := by
    calc
      Real.sqrt (1 + Real.log c) ≤ Real.sqrt ((2 * c) ^ 2) :=
        Real.sqrt_le_sqrt (h1lc_le.trans (by nlinarith only [hc1]))
      _ = 2 * c := Real.sqrt_sq (by positivity)
  have hc13 : c ≤ c ^ 3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hc1 (by norm_num : 1 ≤ 3)
  have hc23 : c ^ 2 ≤ c ^ 3 := pow_le_pow_right₀ hc1 (by norm_num : 2 ≤ 3)
  have h1_c3 : 1 ≤ c ^ 3 := one_le_pow₀ hc1
  -- 1. Prime cross term
  have hterm_pr : |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫| ≤
      2 * C_pr * c ^ 3 * ‖u‖ * ‖w‖ := by
    have h1 := hpr hR' hR6N hlog hu hw
    have h2 : C_pr * (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) ≤
        2 * C_pr * c ^ 3 := by nlinarith only [hC_pr, hlog_div2, h1_c3]
    calc
      _ ≤ C_pr * (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) * ‖u‖ * ‖w‖ := h1
      _ ≤ (2 * C_pr * c ^ 3) * ‖u‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg u)) (norm_nonneg w)
  -- 2. Center cross term
  have hterm_cen :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
          (completeWeilPoleShift tiltedUnitSpline c) N) u, w⟫| ≤
        144 * c ^ 3 * ‖u‖ * ‖w‖ := by
    have h1 := abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace
      (completeWeilPoleShift tiltedUnitSpline c) hR' hR6N hlog hu hu1 hw1_orth
    have hpole : |completeWeilPoleShift tiltedUnitSpline c| ≤ c := by
      rw [abs_of_nonneg (completeWeilPoleShift_nonneg tiltedUnitSpline hc0.le)]
      exact completeWeilPoleShift_le contDiff_tiltedUnitSpline.continuous
        tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0.le
    have h2 : 144 * |completeWeilPoleShift tiltedUnitSpline c| *
        (1 + Real.log R') / Real.sqrt (Real.log N) ≤ 144 * c ^ 3 := by
      have ha : 144 * |completeWeilPoleShift tiltedUnitSpline c| *
          ((1 + Real.log R') / Real.sqrt (Real.log N)) ≤
          144 * |completeWeilPoleShift tiltedUnitSpline c| * 1 :=
        mul_le_mul_of_nonneg_left hlog_div1 (by positivity)
      have hb : 144 * |completeWeilPoleShift tiltedUnitSpline c| ≤ 144 * c ^ 3 := by
        linarith only [hpole, hc13]
      calc
        144 * |completeWeilPoleShift tiltedUnitSpline c| *
            (1 + Real.log R') / Real.sqrt (Real.log N) =
            144 * |completeWeilPoleShift tiltedUnitSpline c| *
              ((1 + Real.log R') / Real.sqrt (Real.log N)) := by ring
        _ ≤ 144 * c ^ 3 := by linarith only [ha, hb]
    calc
      _ ≤ 144 * |completeWeilPoleShift tiltedUnitSpline c| *
            (1 + Real.log R') / Real.sqrt (Real.log N) * ‖u‖ * ‖w‖ := h1
      _ ≤ (144 * c ^ 3) * ‖u‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg u)) (norm_nonneg w)
  -- 3. Separated cross error
  have hterm_sep :
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, w⟫| ≤
        C_sep * c ^ 3 * ‖u‖ * ‖w‖ := by
    have hnorm := norm_separatedCrossErrorMatrix_le contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1 u
    have hcs := (abs_real_inner_le_norm _ w).trans
      (mul_le_mul_of_nonneg_right hnorm (norm_nonneg w))
    have h2 : C_sep * c ^ 2 ≤ C_sep * c ^ 3 := mul_le_mul_of_nonneg_left hc23 hC_sep0
    calc
      _ ≤ C_sep * c ^ 2 * ‖u‖ * ‖w‖ := by dsimp only [C_sep]; linarith only [hcs]
      _ ≤ C_sep * c ^ 3 * ‖u‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg u)) (norm_nonneg w)
  -- 4. Pole error vanishes identically
  have hterm_pole :
      ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix tiltedUnitSpline c N) u, w⟫ = 0 :=
    fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one tiltedUnitSpline c hN2 hu1 hw1_orth
  -- 5. Overlap minus downward
  have hterm_od :
      |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
          downwardPrimeVector tiltedUnitSpline c N u, w⟫| ≤
        3 * C_od * c ^ 3 * ‖u‖ * ‖w‖ := by
    have hnorm := hod hR' hRR_N hlog hc1 hw1 hRNT_lin hu
    have hsqrt_div : Real.sqrt ((1 + Real.log c) / Real.log N) ≤
        2 * c / Real.sqrt (Real.log N) := by
      rw [Real.sqrt_div (by linarith [Real.log_nonneg hc1])]
      exact div_le_div_of_nonneg_right hsqrt_1lc (Real.sqrt_nonneg _)
    have hpart1 : c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) ≤
        2 * c ^ 3 := by
      have h1R0 : 0 ≤ 1 + Real.log R' := by
        have := Real.log_natCast_nonneg R'; linarith only [this]
      calc
        c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) ≤
            c ^ 2 * (1 + Real.log R') * (2 * c / Real.sqrt (Real.log N)) :=
          mul_le_mul_of_nonneg_left hsqrt_div (by positivity)
        _ = 2 * c ^ 3 * ((1 + Real.log R') / Real.sqrt (Real.log N)) := by ring
        _ ≤ 2 * c ^ 3 * 1 := mul_le_mul_of_nonneg_left hlog_div1 (by positivity)
        _ = 2 * c ^ 3 := mul_one _
    have hpart2 : c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) ≤ c ^ 3 := by
      calc
        c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) =
            c ^ 2 * ((R' : ℝ) * Real.sqrt (Real.log N / N)) := by ring
        _ ≤ c ^ 2 * 1 := mul_le_mul_of_nonneg_left hR_sqrt (by positivity)
        _ ≤ c ^ 3 := by linarith only [hc23]
    have hcoef : C_od * (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
        c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) ≤ 3 * C_od * c ^ 3 := by
      nlinarith only [hC_od, hpart1, hpart2]
    calc
      _ ≤ ‖Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
            downwardPrimeVector tiltedUnitSpline c N u‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ (3 * C_od * c ^ 3 * ‖u‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right
          (hnorm.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg u))) (norm_nonneg w)
      _ = 3 * C_od * c ^ 3 * ‖u‖ * ‖w‖ := by ring
  -- 6. Upward non-ratio vector
  have hterm_up : |⟪upwardPrimeVector tiltedUnitSpline c N u, w⟫| ≤
      2 * C_up * c ^ 3 * ‖u‖ * ‖w‖ := by
    have hnorm := hup hR' hlog hc1 hw1 hRNT_up hu
    have hcoef : C_up * c * Real.sqrt (1 + Real.log c) ≤ 2 * C_up * c ^ 3 := by
      calc
        C_up * c * Real.sqrt (1 + Real.log c) ≤ C_up * c * (2 * c) :=
          mul_le_mul_of_nonneg_left hsqrt_1lc (by positivity)
        _ = 2 * C_up * c ^ 2 := by ring
        _ ≤ 2 * C_up * c ^ 3 := mul_le_mul_of_nonneg_left hc23 (by positivity)
    calc
      _ ≤ ‖upwardPrimeVector tiltedUnitSpline c N u‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * C_up * c ^ 3 * ‖u‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right
          (hnorm.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg u))) (norm_nonneg w)
      _ = 2 * C_up * c ^ 3 * ‖u‖ * ‖w‖ := by ring
  -- Combine via exact every-overlap decomposition
  have hdecomp :
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫ =
        -⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫ +
        ⟪Matrix.toEuclideanLin
          (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) u, w⟫ -
        ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, w⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
          downwardPrimeVector tiltedUnitSpline c N u, w⟫ -
        ⟪upwardPrimeVector tiltedUnitSpline c N u, w⟫ := by
    rw [completeWeilMatrix_eq_decomposition_at_every_overlap contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, identity_euclid_apply,
      fullWeilNonRatioMatrix_eq_downward_add_upward contDiff_tiltedUnitSpline
        tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1 u,
      inner_add_left, inner_sub_left, real_inner_smul_left, huw_orth, mul_zero,
      hterm_pole]
    ring
  rw [hdecomp]
  have habs5 : ∀ x₁ x₂ x₃ x₄ x₅ : ℝ,
      |(-x₁) + x₂ - x₃ + x₄ - x₅| ≤ |x₁| + |x₂| + |x₃| + |x₄| + |x₅| := by
    intro x₁ x₂ x₃ x₄ x₅
    have h1 := abs_sub ((-x₁) + x₂ - x₃ + x₄) x₅
    have h2 := abs_add ((-x₁) + x₂ - x₃) x₄
    have h3 := abs_sub ((-x₁) + x₂) x₃
    have h4 := abs_add (-x₁) x₂
    rw [abs_neg] at h4
    linarith only [h1, h2, h3, h4]
  calc
    _ ≤ |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫| +
          |⟪Matrix.toEuclideanLin
            (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) u, w⟫| +
          |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, w⟫| +
          |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
            downwardPrimeVector tiltedUnitSpline c N u, w⟫| +
          |⟪upwardPrimeVector tiltedUnitSpline c N u, w⟫| := habs5 _ _ _ _ _
    _ ≤ (2 * C_pr + 144 + C_sep + 3 * C_od + 2 * C_up) * c ^ 3 * ‖u‖ * ‖w‖ := by
      linarith only [hterm_pr, hterm_cen, hterm_sep, hterm_od, hterm_up]
    _ ≤ C_cross * c ^ 3 * ‖u‖ * ‖w‖ := by
      have hpos : 0 ≤ c ^ 3 * ‖u‖ * ‖w‖ := by positivity
      dsimp only [C_cross]
      nlinarith only [hpos]

/-- Projecting a unit vector `zHat ∈ (conductorSubspace Q₁ N)ᗮ` of bounded complete Weil energy
onto a quantitative confinement subspace `conductorSubspace R' N` (`log R' ≤ C_R * c ^ 46 + log Q₁`)
retains `‖u‖ ^ 2 ≥ 3 / 4`, orthogonality to `conductorSubspace Q₁ N`, and bounded energy. -/
private theorem exists_high_tail_suppression :
    ∃ C_R H_res : ℝ, 0 < C_R ∧ 0 < H_res ∧
      ∀ {Q₁ N : ℕ} {c : ℝ},
        2 ≤ Q₁ → 1 ≤ c → H_res * c ^ 8 ≤ N → c / N ≤ 1 / 3 →
        (∀ {R' : ℕ}, Q₁ ≤ R' → Real.log R' ≤ C_R * c ^ 46 + Real.log Q₁ →
          R' ^ 6 ≤ N ∧
          18 * (1 + Real.log R') ≤ Real.log N ∧
          ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N ∧
          ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N ∧
          (1 + Real.log R') / Real.sqrt (Real.log N) ≤ 1 ∧
          (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N) ≤ 1 ∧
          (R' : ℝ) * Real.sqrt (Real.log N / N) ≤ 1) →
      ∀ {zHat : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        zHat ∈ (conductorSubspace Q₁ N)ᗮ → ‖zHat‖ = 1 →
        completeWeilEnergy tiltedUnitSpline c N zHat ≤
          2 * tiltedSplineSpectralFloorConstant + 2 →
      ∃ R' : ℕ, Q₁ ≤ R' ∧ Real.log R' ≤ C_R * c ^ 46 + Real.log Q₁ ∧
        ∃ u : EuclideanSpace ℝ (PrimeHorizonIndex N),
          u ∈ conductorSubspace R' N ∧ u ∈ (conductorSubspace Q₁ N)ᗮ ∧
          3 / 4 ≤ ‖u‖ ^ 2 ∧ ‖u‖ ≤ 1 ∧
          completeWeilEnergy tiltedUnitSpline c N u ≤
            2 * tiltedSplineSpectralFloorConstant + 3 := by
  obtain ⟨b, B, H, hb, hB, hH, hres⟩ := exists_matrix_polynomial_reserve
  obtain ⟨C_conf, hC_conf, hconf⟩ := exists_quantitative_exponential_conductor_cutoff_of_poleDefect_le
  obtain ⟨C_cross, hC_cross1, hcross⟩ := exists_completeWeilMatrix_orthog_cross_le
  let M₀ := 2 * tiltedSplineSpectralFloorConstant + 2
  have hM₀ : 0 < M₀ := by
    have := tiltedSplineSpectralFloorConstant_pos; dsimp only [M₀]; positivity
  let M₁ := max 2 (max (4 * C_cross) (4 * B))
  have hM₁_2 : 2 ≤ M₁ := le_max_left _ _
  have hM₁_pos : 0 < M₁ := by linarith only [hM₁_2]
  have hM₁_cross : 4 * C_cross ≤ M₁ := (le_max_left _ _).trans (le_max_right _ _)
  have hM₁_B : 4 * B ≤ M₁ := (le_max_right _ _).trans (le_max_right _ _)
  let K_coef := (B + M₀) / b
  have hK_coef0 : 0 < K_coef := by dsimp only [K_coef]; positivity
  let C_R := C_conf * M₁ ^ 6 * (K_coef + 1)
  have hC_R0 : 0 < C_R := by dsimp only [C_R]; positivity
  refine ⟨C_R, H, hC_R0, hH, ?_⟩
  intro Q₁ N c hQ₁ hc1 hHN hw1 hR'_conds zHat hz_orth hz_norm hz_energy
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  -- Bound poleDefect of zHat
  have hdef_le : poleDefect N (primeHorizonExtension zHat) ≤ K_coef * c ^ 16 := by
    have hr := hres c hc1 N hHN zHat
    rw [hz_norm, one_pow, mul_one] at hr
    have h1 : (b / c ^ 7) * poleDefect N (primeHorizonExtension zHat) ≤
        B * c ^ 9 + M₀ := by dsimp only [M₀]; linarith only [hr, hz_energy]
    have hc9 : 1 ≤ c ^ 9 := one_le_pow₀ hc1
    have h2 : B * c ^ 9 + M₀ ≤ (B + M₀) * c ^ 9 := by nlinarith only [hM₀, hc9]
    have h3 := (div_le_iff₀ (pow_pos hc0 7)).mp (by
      simpa only [div_mul_eq_mul_div] using h1.trans h2)
    rw [le_div_iff₀' hb] at *
    dsimp only [K_coef]
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]
    calc
      poleDefect N (primeHorizonExtension zHat) * b =
          b * poleDefect N (primeHorizonExtension zHat) := mul_comm _ _
      _ ≤ (B + M₀) * c ^ 9 * c ^ 7 := h3
      _ = (B + M₀) * c ^ 16 := by ring
  -- Apply quantitative exponential confinement at η = 1 / (M₁^2 * c^10)
  let η := 1 / (M₁ ^ 2 * c ^ 10)
  have hη_pos : 0 < η := by dsimp only [η]; positivity
  have hη_le4 : η ≤ 1 / 4 := by
    dsimp only [η]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hM1_sq : 4 ≤ M₁ ^ 2 := by nlinarith only [hM₁_2]
    have hc10 : 1 ≤ c ^ 10 := one_le_pow₀ hc1
    nlinarith only [hM1_sq, hc10]
  have hη_le1 : η ≤ 1 := hη_le4.trans (by norm_num)
  obtain ⟨R, _hR2, hR_log, hR_app⟩ := hconf η hη_pos hη_le1 (K_coef * c ^ 16) (by positivity)
  let R' := max R Q₁
  have hQR' : Q₁ ≤ R' := le_max_right R Q₁
  have hRR' : R ≤ R' := le_max_left R Q₁
  have hR'2 : 2 ≤ R' := hQ₁.trans hQR'
  have hR_log_bound : Real.log R ≤ C_R * c ^ 46 := by
    have hη3 : C_conf / η ^ 3 = C_conf * M₁ ^ 6 * c ^ 30 := by
      dsimp only [η]; field_simp [hM₁_pos.ne', hc0.ne']; ring
    rw [hη3] at hR_log
    have hc16 : 1 ≤ c ^ 16 := one_le_pow₀ hc1
    have hK1 : K_coef * c ^ 16 + 1 ≤ (K_coef + 1) * c ^ 16 := by nlinarith only [hc16]
    calc
      Real.log R ≤ C_conf * M₁ ^ 6 * c ^ 30 * (K_coef * c ^ 16 + 1) := hR_log
      _ ≤ C_conf * M₁ ^ 6 * c ^ 30 * ((K_coef + 1) * c ^ 16) :=
        mul_le_mul_of_nonneg_left hK1 (by positivity)
      _ = C_R * c ^ 46 := by dsimp only [C_R]; ring
  have hR'_log : Real.log R' ≤ C_R * c ^ 46 + Real.log Q₁ := by
    have hQ0 : 0 ≤ Real.log (Q₁ : ℝ) := Real.log_natCast_nonneg Q₁
    have hCRc : 0 ≤ C_R * c ^ 46 := by positivity
    rcases le_total R Q₁ with hRQ | hQR
    · have heq : R' = Q₁ := max_eq_right hRQ
      rw [heq]; linarith only [hCRc]
    · have heq : R' = R := max_eq_left hQR
      rw [heq]; linarith only [hR_log_bound, hQ0]
  obtain ⟨hR6N, hlogN, hRNT_lin, hRNT_up, hlog_div1, hlog_div2, hR_sqrt⟩ :=
    hR'_conds hQR' hR'_log
  have hN2 : 2 ≤ N := by
    have h6 : 4 ≤ R' ^ 6 := by
      have : 2 ^ 2 ≤ R' ^ 6 :=
        (Nat.pow_le_pow_left hR'2 2).trans (Nat.pow_le_pow_right (by omega) (by norm_num))
      norm_num at this; exact this
    omega
  let u := (conductorSubspace R' N).starProjection zHat
  let w := zHat - u
  have hu_mem : u ∈ conductorSubspace R' N :=
    (conductorSubspace R' N).starProjection_apply_mem zHat
  have hu_orthQ : u ∈ (conductorSubspace Q₁ N)ᗮ :=
    starProjection_mem_orthogonal_of_le (conductorSubspace_mono hQR' N) hz_orth
  have hu_orth1 : u ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu_orthQ v (conductorSubspace_mono (by omega : 1 ≤ Q₁) N hv)
  have hw_orth : w ∈ (conductorSubspace R' N)ᗮ := sub_starProjection_mem_orthogonal _ zHat
  have hw_sq : ‖w‖ ^ 2 ≤ η := by
    have hpR_mem : (conductorSubspace R N).starProjection zHat ∈ conductorSubspace R' N :=
      conductorSubspace_mono hRR' N ((conductorSubspace R N).starProjection_apply_mem zHat)
    exact (norm_sub_starProjection_sq_le (conductorSubspace R' N) zHat _ hpR_mem).trans
      (hR_app N hN2 zHat hz_norm.le hdef_le)
  have hw_norm : ‖w‖ ≤ 1 / (M₁ * c ^ 5) := by
    have hsq : ‖w‖ ^ 2 ≤ (1 / (M₁ * c ^ 5)) ^ 2 := by
      refine hw_sq.trans_eq ?_
      dsimp only [η]; ring
    have hrhs0 : 0 ≤ 1 / (M₁ * c ^ 5) := by positivity
    nlinarith only [hsq, norm_nonneg w, hrhs0]
  have hpyth := norm_starProjection_sq_add_sub_sq (conductorSubspace R' N) zHat
  change ‖u‖ ^ 2 + ‖w‖ ^ 2 = ‖zHat‖ ^ 2 at hpyth
  rw [hz_norm, one_pow] at hpyth
  have hu_sq_ge : 3 / 4 ≤ ‖u‖ ^ 2 := by linarith only [hpyth, hw_sq, hη_le4]
  have hu_le1 : ‖u‖ ≤ 1 := by nlinarith only [hpyth, sq_nonneg ‖w‖, norm_nonneg u]
  have hcross_uw :
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤ 1 / 2 := by
    have h1 := hcross hR'2 hR6N hlogN hc1 hw1 hRNT_lin hRNT_up hlog_div1 hlog_div2
      hR_sqrt hu_mem hu_orth1 hw_orth
    have hc2 : 1 ≤ c ^ 2 := one_le_pow₀ hc1
    calc
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤
          2 * (C_cross * c ^ 3 * 1 * (1 / (M₁ * c ^ 5))) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) zero_le_two
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hu_le1 (by positivity))
          hw_norm (norm_nonneg w) (by positivity)
      _ = (2 * C_cross) / (M₁ * c ^ 2) := by field_simp [hM₁_pos.ne', hc0.ne']; ring
      _ ≤ 1 / 2 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith only [hM₁_cross, hc2, hC_cross1]
  have hw_energy : -(1 / 4 : ℝ) ≤ completeWeilEnergy tiltedUnitSpline c N w := by
    have hr := hres c hc1 N hHN w
    have hd0 : 0 ≤ (b / c ^ 7) * poleDefect N (primeHorizonExtension w) :=
      mul_nonneg (by positivity) (poleDefect_nonneg N _)
    have hBw : B * c ^ 9 * ‖w‖ ^ 2 ≤ 1 / 4 := by
      calc
        B * c ^ 9 * ‖w‖ ^ 2 ≤ B * c ^ 9 * (1 / (M₁ ^ 2 * c ^ 10)) :=
          mul_le_mul_of_nonneg_left hw_sq (by positivity)
        _ = B / (M₁ ^ 2 * c) := by field_simp [hM₁_pos.ne', hc0.ne']
        _ ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]
          have hM1_ge1 : 1 ≤ M₁ := by linarith only [hM₁_2]
          nlinarith only [hM₁_B, hM1_ge1, hc1, hB]
    linarith only [hr, hd0, hBw]
  have hu_energy : completeWeilEnergy tiltedUnitSpline c N u ≤
      2 * tiltedSplineSpectralFloorConstant + 3 := by
    have hz_split : zHat = u + w := by dsimp only [w]; abel
    have hexp := completeWeilEnergy_add_eq tiltedUnitSpline c u w
    rw [← hz_split] at hexp
    linarith only [hexp, hz_energy, hcross_uw, hw_energy]
  exact ⟨R', hQR', hR'_log, u, hu_mem, hu_orthQ, hu_sq_ge, hu_le1, hu_energy⟩

/-! ### 4. Coercivity on `conductorSubspace R' N ⊓ (conductorSubspace Q₁ N)ᗮ` -/

/-- Exact complete-Weil quadratic reduction on `conductorSubspace R' N ⊓ (conductorSubspace 1 N)ᗮ`
to `renormalizedPrimeEnergy N u - ⟪overlapMatrix u, u⟫ - log c - O(1)`. -/
private theorem exists_completeWeilEnergy_ge_prime_sub_overlap :
    ∃ C_dec C_err : ℝ, 0 < C_dec ∧ 0 < C_err ∧
      ∀ {R' N : ℕ} {c : ℝ},
        2 ≤ R' → R' ^ 6 ≤ N → 18 * (1 + Real.log R') ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        C_err * (c * (1 + Real.log R') / Real.sqrt (Real.log N) +
          c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) ≤ 1 →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R' N → u ∈ (conductorSubspace 1 N)ᗮ → ‖u‖ ≤ 1 →
        renormalizedPrimeEnergy N u -
            ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u, u⟫ -
            Real.log c - C_dec ≤
          completeWeilEnergy tiltedUnitSpline c N u := by
  obtain ⟨C_od, hC_od, hod⟩ := exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  let C_sep' := 36 * (152 * (∫ t, |tiltedUnitSpline t|) ^ 2 / (∫ t, tiltedUnitSpline t ^ 2))
  have hC_sep'0 : 0 ≤ C_sep' := by
    have := integral_tiltedUnitSpline_sq_pos; dsimp only [C_sep']; positivity
  let C_err := 144 + C_sep' + 2 * C_od + 1
  let C_dec := |completeWeilSelfFinitePart tiltedUnitSpline 1| +
    |Real.eulerMascheroniConstant| + 3
  refine ⟨C_dec, C_err, by dsimp only [C_dec]; positivity,
    by dsimp only [C_err]; positivity, ?_⟩
  intro R' N c hR' hR6N hlog hc1 hw1 hRNT herr u hu hu1 hu_le1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hRR_N : R' * R' ≤ N := by
    have : R' ^ 2 ≤ R' ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simpa only [sq] using this.trans hR6N
  have hR4_N : R' ^ 4 ≤ N :=
    (Nat.pow_le_pow_right (by omega) (by norm_num : 4 ≤ 6)).trans hR6N
  have hN2 : 2 ≤ N := by have := Nat.mul_le_mul hR' hR'; omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hcN : c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
  have hu_sq_le1 : ‖u‖ ^ 2 ≤ 1 := by nlinarith only [hu_le1, norm_nonneg u]
  -- Self-energy term
  have hself_eq : completeWeilSelfFinitePart tiltedUnitSpline c =
      completeWeilSelfFinitePart tiltedUnitSpline 1 - Real.log c := by
    unfold completeWeilSelfFinitePart
    rw [mul_one, Real.log_div one_ne_zero (by positivity), Real.log_one,
      Real.log_mul (by positivity : 2 * Real.pi ≠ 0) hc0.ne',
      Real.log_div one_ne_zero (by positivity), Real.log_one]
    ring
  have hself_err : |completeWeilSelfError tiltedUnitSpline c N| ≤ 1 := by
    have h1 := abs_completeWeilSelfError_le_of_width_le_one contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0 hN1 hcN
    have he12 : Real.exp (1 / 2) ≤ 3 := by
      have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      exact (Real.exp_le_exp.mpr (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans he1
    nlinarith only [h1, he12, hw1]
  have hself_term :
      -Real.log c - (|completeWeilSelfFinitePart tiltedUnitSpline 1| +
        |Real.eulerMascheroniConstant| + 1) ≤
      (completeWeilSelfFinitePart tiltedUnitSpline c - Real.eulerMascheroniConstant +
        completeWeilSelfError tiltedUnitSpline c N) * ‖u‖ ^ 2 := by
    rw [hself_eq]
    have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
    have hlc_u : Real.log c * ‖u‖ ^ 2 ≤ Real.log c :=
      (mul_le_mul_of_nonneg_left hu_sq_le1 hlc0).trans_eq (mul_one _)
    have hconst_lb : -(|completeWeilSelfFinitePart tiltedUnitSpline 1| +
        |Real.eulerMascheroniConstant| + 1) ≤
      (completeWeilSelfFinitePart tiltedUnitSpline 1 - Real.eulerMascheroniConstant +
        completeWeilSelfError tiltedUnitSpline c N) := by
      linarith only [neg_abs_le (completeWeilSelfFinitePart tiltedUnitSpline 1),
        le_abs_self Real.eulerMascheroniConstant, (abs_le.mp hself_err).1]
    have hconst_u :
        -(|completeWeilSelfFinitePart tiltedUnitSpline 1| +
          |Real.eulerMascheroniConstant| + 1) ≤
        (completeWeilSelfFinitePart tiltedUnitSpline 1 - Real.eulerMascheroniConstant +
          completeWeilSelfError tiltedUnitSpline c N) * ‖u‖ ^ 2 := by
      have hA0 : 0 ≤ |completeWeilSelfFinitePart tiltedUnitSpline 1| +
          |Real.eulerMascheroniConstant| + 1 := by positivity
      calc
        -(|completeWeilSelfFinitePart tiltedUnitSpline 1| +
            |Real.eulerMascheroniConstant| + 1) ≤
          -(|completeWeilSelfFinitePart tiltedUnitSpline 1| +
            |Real.eulerMascheroniConstant| + 1) * ‖u‖ ^ 2 := by
          nlinarith only [hA0, hu_sq_le1, sq_nonneg ‖u‖]
        _ ≤ _ := mul_le_mul_of_nonneg_right hconst_lb (sq_nonneg _)
    linarith only [hlc_u, hconst_u]
  -- Center + separated cross + overlap-minus-downward
  have hcen := abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace
    (completeWeilPoleShift tiltedUnitSpline c) hR' hR6N hlog hu hu1 hu1
  have hpole_le : |completeWeilPoleShift tiltedUnitSpline c| ≤ c := by
    rw [abs_of_nonneg (completeWeilPoleShift_nonneg tiltedUnitSpline hc0.le)]
    exact completeWeilPoleShift_le contDiff_tiltedUnitSpline.continuous
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0.le
  have hcen' :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
          (completeWeilPoleShift tiltedUnitSpline c) N) u, u⟫| ≤
        144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) := by
    have h1R0 : 0 ≤ (1 + Real.log R') / Real.sqrt (Real.log N) := by
      have := Real.log_natCast_nonneg R'; positivity
    have h1 : 144 * |completeWeilPoleShift tiltedUnitSpline c| *
        (1 + Real.log R') / Real.sqrt (Real.log N) ≤
      144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) := by
      calc
        144 * |completeWeilPoleShift tiltedUnitSpline c| *
            (1 + Real.log R') / Real.sqrt (Real.log N) =
          144 * |completeWeilPoleShift tiltedUnitSpline c| *
            ((1 + Real.log R') / Real.sqrt (Real.log N)) := by ring
        _ ≤ 144 * c * ((1 + Real.log R') / Real.sqrt (Real.log N)) :=
          mul_le_mul_of_nonneg_right (by linarith only [hpole_le]) h1R0
        _ = 144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) := by ring
    calc
      _ ≤ 144 * |completeWeilPoleShift tiltedUnitSpline c| *
            (1 + Real.log R') / Real.sqrt (Real.log N) * ‖u‖ * ‖u‖ := hcen
      _ = (144 * |completeWeilPoleShift tiltedUnitSpline c| *
            (1 + Real.log R') / Real.sqrt (Real.log N)) * ‖u‖ ^ 2 := by ring
      _ ≤ 144 * (c * (1 + Real.log R') / Real.sqrt (Real.log N)) * 1 :=
        mul_le_mul h1 hu_sq_le1 (sq_nonneg _) (by positivity)
      _ = _ := mul_one _
  have hsep' :
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, u⟫| ≤
        C_sep' * (c ^ 2 / Real.log N) := by
    have h1 := abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      hc0 hR' hR4_N hlog hu
    have hL0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    calc
      _ ≤ C_sep' * c ^ 2 / Real.log N * ‖u‖ ^ 2 := h1
      _ = C_sep' * (c ^ 2 / Real.log N) * ‖u‖ ^ 2 := by ring
      _ ≤ C_sep' * (c ^ 2 / Real.log N) * 1 :=
        mul_le_mul_of_nonneg_left hu_sq_le1 (by positivity)
      _ = _ := mul_one _
  have hod' :
      2 * |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
          downwardPrimeVector tiltedUnitSpline c N u, u⟫| ≤
        2 * C_od * (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) := by
    have h1 := hod hR' hRR_N hlog hc1 hw1 hRNT hu
    have hcs := (abs_real_inner_le_norm _ u).trans
      (mul_le_mul_of_nonneg_right h1 (norm_nonneg u))
    have hX0 : 0 ≤ c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
        c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) := by
      have := Real.log_natCast_nonneg R'; positivity
    calc
      _ ≤ 2 * (C_od * (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
            c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) * ‖u‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left hcs zero_le_two
      _ = 2 * C_od * (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
            c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) * ‖u‖ ^ 2 := by ring
      _ ≤ 2 * C_od * (c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
            c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) * 1 :=
        mul_le_mul_of_nonneg_left hu_sq_le1 (by positivity)
      _ = _ := mul_one _
  have hsum_err_le1 :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
          (completeWeilPoleShift tiltedUnitSpline c) N) u, u⟫| +
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, u⟫| +
      2 * |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
          downwardPrimeVector tiltedUnitSpline c N u, u⟫| ≤ 1 := by
    have ht1 : 0 ≤ c * (1 + Real.log R') / Real.sqrt (Real.log N) := by
      have := Real.log_natCast_nonneg R'; positivity
    have ht2 : 0 ≤ c ^ 2 / Real.log N := by
      have := Real.log_natCast_nonneg N; positivity
    have ht3 : 0 ≤ c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) := by
      have := Real.log_natCast_nonneg R'; positivity
    have ht4 : 0 ≤ c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) := by positivity
    dsimp only [C_err] at herr
    nlinarith only [hcen', hsep', hod', herr, ht1, ht2, ht3, ht4, hC_sep'0, hC_od]
  have hpole0 := fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one
    tiltedUnitSpline c hN2 hu1 hu1
  have hdecomp := completeWeilMatrix_inner_eq_decomposition_at_every_overlap
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hc0 hN1 u
  rw [overlap_sub_nonRatio_inner_eq contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
      integral_tiltedUnitSpline_sq_pos hc0 hN1 u, hpole0] at hdecomp
  change completeWeilEnergy tiltedUnitSpline c N u =
    renormalizedPrimeEnergy N u +
    (completeWeilSelfFinitePart tiltedUnitSpline c - Real.eulerMascheroniConstant +
      completeWeilSelfError tiltedUnitSpline c N) * ‖u‖ ^ 2 +
    ⟪Matrix.toEuclideanLin
      (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) u, u⟫ -
    ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u, u⟫ + 0 +
    (-⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u, u⟫ +
      2 * ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u -
        downwardPrimeVector tiltedUnitSpline c N u, u⟫) at hdecomp
  have habs_c := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) u, u⟫| ≤ _)).1
  have habs_s := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (separatedCrossErrorMatrix tiltedUnitSpline c N) u, u⟫| ≤ _)).2
  have habs_o := (abs_le.mp (le_rfl : |⟪Matrix.toEuclideanLin
    (overlapMatrix tiltedUnitSpline c N) u -
    downwardPrimeVector tiltedUnitSpline c N u, u⟫| ≤ _)).1
  dsimp only [C_dec]
  linarith only [hdecomp, hself_term, hsum_err_le1, habs_c, habs_s, habs_o]

/-- Coercivity above `Q₁`: every `u ∈ conductorSubspace R' N ⊓ (conductorSubspace Q₁ N)ᗮ` with
`3 / 4 ≤ ‖u‖ ^ 2 ≤ 1` has complete Weil energy bounded below by
`(1 / (2 * conductorCutoffConstant)) * log Q₁ - log c - C_coerc`. -/
private theorem exists_high_band_coercivity :
    ∃ C_coerc C_small : ℝ, 0 < C_coerc ∧ 0 < C_small ∧
      ∀ {Q₁ R' N : ℕ} {c : ℝ},
        2 ≤ Q₁ → Q₁ ≤ R' → R' ^ 6 ≤ N → 36 * (1 + Real.log R') ≤ Real.log N →
        1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N →
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        Real.log 4 + 5 ≤ Real.log Q₁ / conductorCutoffConstant →
        C_small * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N +
          (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N) +
          c * (1 + Real.log R') / Real.sqrt (Real.log N) +
          c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
          c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) +
          c ^ 5 * Real.log N / N +
          c ^ 4 / Real.sqrt Q₁ +
          c ^ 3 * (R' : ℝ) ^ 4 / N) ≤ 1 →
      ∀ {u : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R' N → u ∈ (conductorSubspace Q₁ N)ᗮ →
        3 / 4 ≤ ‖u‖ ^ 2 → ‖u‖ ≤ 1 →
        (1 / (2 * conductorCutoffConstant)) * Real.log Q₁ - Real.log c - C_coerc ≤
          completeWeilEnergy tiltedUnitSpline c N u := by
  obtain ⟨C_dec, C_err, hC_dec, hC_err, hdec⟩ := exists_completeWeilEnergy_ge_prime_sub_overlap
  obtain ⟨C_ov, hC_ov, hov⟩ := exists_overlapMatrix_inner_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_pr, hC_pr, hpr_res⟩ := exists_fullPrimeMatrix_packet_residual_norm_le
  obtain ⟨C_mid, hC_mid, hmid⟩ := exists_overlapMatrix_midBand_inner_le
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  let C_small := C_err + 1080 + 270 * C_ov + 864 + 432 * C_pr + C_mid + 1
  let C_coerc := C_dec + (Real.log 4 + 4) + 8 + (Real.log 4 + 5) / 2
  have hlog4_0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨C_coerc, C_small, by dsimp only [C_coerc]; positivity,
    by dsimp only [C_small]; positivity, ?_⟩
  intro Q₁ R' N c hQ₁ hQR' hR6N hlog36 hc1 hcL hw1 hradN hRNT hQ₁_large hsmall
    u hu huQ hu_sq_ge hu_le1
  have hR'2 : 2 ≤ R' := hQ₁.trans hQR'
  have hRR_N : R' * R' ≤ N := by
    have : R' ^ 2 ≤ R' ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    simpa only [sq] using this.trans hR6N
  have hQ6N : Q₁ ^ 6 ≤ N := (Nat.pow_le_pow_left hQR' 6).trans hR6N
  have hQQ_N : Q₁ * Q₁ ≤ N := (Nat.mul_le_mul hQR' hQR').trans hRR_N
  have hlog18_R' : 18 * (1 + Real.log R') ≤ Real.log N := by
    have := Real.log_natCast_nonneg R'; linarith only [hlog36, this]
  have hlog_Q_le_R' : Real.log Q₁ ≤ Real.log R' :=
    Real.log_le_log (by exact_mod_cast (show 0 < Q₁ by omega)) (by exact_mod_cast hQR')
  have hlog18_Q : 18 * (1 + Real.log Q₁) ≤ Real.log N := by
    linarith only [hlog18_R', hlog_Q_le_R']
  have hL1 : 1 ≤ Real.log N := by
    have := Real.log_natCast_nonneg R'; linarith only [hlog36, this]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  have hsL_le_L : Real.sqrt (Real.log N) ≤ Real.log N := by
    have hs1 : 1 ≤ Real.sqrt (Real.log N) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL1
    nlinarith only [Real.sq_sqrt hL0.le, hs1]
  have hu1 : u ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    huQ v (conductorSubspace_mono (by omega : 1 ≤ Q₁) N hv)
  -- Nonnegativity of all 9 smallness summands
  have ht1 : 0 ≤ c * (1 + Real.log c) * (1 + Real.log R') / Real.log N := by
    have := Real.log_nonneg hc1; have := Real.log_natCast_nonneg R'; positivity
  have ht2 : 0 ≤ (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N) := by positivity
  have ht3 : 0 ≤ c * (1 + Real.log R') / Real.sqrt (Real.log N) := by
    have := Real.log_natCast_nonneg R'; positivity
  have ht4 : 0 ≤ c ^ 2 / Real.log N := by positivity
  have ht5 : 0 ≤ c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) := by
    have := Real.log_natCast_nonneg R'; positivity
  have ht6 : 0 ≤ c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N) := by positivity
  have ht7 : 0 ≤ c ^ 5 * Real.log N / N := by positivity
  have ht8 : 0 ≤ c ^ 4 / Real.sqrt Q₁ := by positivity
  have ht9 : 0 ≤ c ^ 3 * (R' : ℝ) ^ 4 / N := by positivity
  have herr_dec : C_err * (c * (1 + Real.log R') / Real.sqrt (Real.log N) +
      c ^ 2 / Real.log N +
      c ^ 2 * (1 + Real.log R') * Real.sqrt ((1 + Real.log c) / Real.log N) +
      c ^ 2 * (R' : ℝ) * Real.sqrt (Real.log N / N)) ≤ 1 := by
    dsimp only [C_small] at hsmall
    nlinarith only [hsmall, hC_err, hC_ov, hC_pr, hC_mid,
      ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]
  have hbase_dec := hdec hR'2 hR6N hlog18_R' hc1 hw1 hRNT herr_dec hu hu1 hu_le1
  -- Decompose u = uLow + y
  obtain ⟨a, -, hu_eq⟩ := (mem_conductorSubspace_iff (M := R') (N := N) (x := u)).mp hu
  let uLow := ∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N
  let aRest : ℕ → ℝ := fun m => if m ≤ Q₁ then 0 else a m
  let y := ∑ m ∈ Icc 1 R', aRest m • normalizedRamanujanHorizonVector m N
  have huLow_R' : uLow = ∑ m ∈ Icc 1 R',
      (if m ≤ Q₁ then a m else 0) • normalizedRamanujanHorizonVector m N := by
    have hsub : Icc 1 Q₁ ⊆ Icc 1 R' := Icc_subset_Icc le_rfl hQR'
    calc
      uLow = ∑ m ∈ Icc 1 Q₁,
          (if m ≤ Q₁ then a m else 0) • normalizedRamanujanHorizonVector m N :=
        sum_congr rfl fun m hm => by rw [if_pos (mem_Icc.mp hm).2]
      _ = _ := sum_subset hsub fun m hmR hmQ => by
        have hnot : ¬m ≤ Q₁ := fun h => hmQ (mem_Icc.mpr ⟨(mem_Icc.mp hmR).1, h⟩)
        rw [if_neg hnot, zero_smul]
  have hu_split : u = uLow + y := by
    rw [hu_eq, huLow_R']
    dsimp only [y, aRest]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  have huLow_mem : uLow ∈ conductorSubspace R' N :=
    conductorSubspace_mono hQR' N (sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N a)
  have hy_mem : y ∈ conductorSubspace R' N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R' N aRest
  -- Low-band norm bound
  have huLow_bound : ‖uLow‖ ≤ 54 * (1 + Real.log R') / Real.log N := by
    have hlow := (low_band_norm_le_of_mem_orthogonal (by omega : 1 ≤ Q₁) hQR' hR'2 hRR_N
      hlog18_R' (hu_eq ▸ huQ)).2
    rw [← hu_eq] at hlow
    have h0 : 0 ≤ 54 * (1 + Real.log R') / Real.log N := by
      have := Real.log_natCast_nonneg R'; positivity
    exact hlow.trans ((mul_le_mul_of_nonneg_left hu_le1 h0).trans_eq (mul_one _))
  have h1R_div_le : (1 + Real.log R') / Real.log N ≤
      c * (1 + Real.log c) * (1 + Real.log R') / Real.log N := by
    have h1cc : 1 ≤ c * (1 + Real.log c) := by
      have := Real.log_nonneg hc1; nlinarith only [hc1, this]
    have h1R0 : 0 ≤ (1 + Real.log R') / Real.log N := by
      have := Real.log_natCast_nonneg R'; positivity
    calc
      (1 + Real.log R') / Real.log N = 1 * ((1 + Real.log R') / Real.log N) := (one_mul _).symm
      _ ≤ (c * (1 + Real.log c)) * ((1 + Real.log R') / Real.log N) :=
        mul_le_mul_of_nonneg_right h1cc h1R0
      _ = _ := by ring
  have huLow_le20 : ‖uLow‖ ≤ 1 / 20 := by
    have h1080 : 1080 * ((1 + Real.log R') / Real.log N) ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left h1R_div_le (by norm_num : (0 : ℝ) ≤ 1080)
      dsimp only [C_small] at hsmall
      nlinarith only [h, hsmall, hC_err, hC_ov, hC_pr, hC_mid,
        ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]
    have h54 : 54 * (1 + Real.log R') / Real.log N =
        54 * ((1 + Real.log R') / Real.log N) := by ring
    linarith only [huLow_bound, h1080, h54]
  have hy_bounds : 1 / 2 ≤ ‖y‖ ^ 2 ∧ ‖y‖ ≤ 2 := by
    have hu_ge : 17 / 20 ≤ ‖u‖ := by nlinarith only [hu_sq_ge, norm_nonneg u]
    have htri1 : ‖u‖ ≤ ‖uLow‖ + ‖y‖ := by rw [hu_split]; exact norm_add_le _ _
    have hy_ge : 4 / 5 ≤ ‖y‖ := by linarith only [hu_ge, htri1, huLow_le20]
    have hy_eq : y = u - uLow := by rw [hu_split]; abel
    have htri2 : ‖y‖ ≤ ‖u‖ + ‖uLow‖ := by rw [hy_eq]; exact norm_sub_le _ _
    exact ⟨by nlinarith only [hy_ge], by linarith only [htri2, hu_le1, huLow_le20]⟩
  -- Overlap difference between u and y
  have hov_diff :
      |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u, u⟫ -
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y, y⟫| ≤ 1 := by
    have hexp :
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u, u⟫ -
          ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y, y⟫ =
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) uLow, uLow⟫ +
          ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) uLow, y⟫ +
          ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y, uLow⟫ := by
      rw [hu_split, map_add, inner_add_left, inner_add_right, inner_add_right]
      ring
    have h1 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT huLow_mem huLow_mem
    have h2 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT huLow_mem hy_mem
    have h3 := hov hR'2 hR'2 hlog18_R' hlog18_R' hc1 hcL hw1 hRNT hRNT hy_mem huLow_mem
    have hnorm_sum : ‖uLow‖ * ‖uLow‖ + ‖uLow‖ * ‖y‖ + ‖y‖ * ‖uLow‖ ≤ 5 * ‖uLow‖ := by
      nlinarith only [huLow_le20, hy_bounds.2, norm_nonneg uLow]
    have h270 : 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N) ≤ 1 := by
      dsimp only [C_small] at hsmall
      nlinarith only [hsmall, hC_err, hC_ov, hC_pr, hC_mid,
        ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]
    rw [hexp]
    calc
      _ ≤ |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) uLow, uLow⟫| +
            |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) uLow, y⟫| +
            |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y, uLow⟫| :=
        abs_add_three _ _ _
      _ ≤ C_ov * c * (1 + Real.log c) * (‖uLow‖ * ‖uLow‖ + ‖uLow‖ * ‖y‖ + ‖y‖ * ‖uLow‖) := by
        linarith only [h1, h2, h3]
      _ ≤ C_ov * c * (1 + Real.log c) * (5 * (54 * (1 + Real.log R') / Real.log N)) := by
        refine mul_le_mul_of_nonneg_left (hnorm_sum.trans (by linarith only [huLow_bound])) ?_
        have := Real.log_nonneg hc1; positivity
      _ = 270 * C_ov * (c * (1 + Real.log c) * (1 + Real.log R') / Real.log N) := by ring
      _ ≤ 1 := h270
  -- Prime energy comparison between u and y
  have hprime_uLow : -(Real.log 4 + 4) ≤ renormalizedPrimeEnergy N uLow := by
    have hp := poleDefect_le_primeEnergy_add_row_cost uLow
    have hd0 := poleDefect_nonneg N (primeHorizonExtension uLow)
    have huL_sq1 : ‖uLow‖ ^ 2 ≤ 1 := by nlinarith only [huLow_le20, norm_nonneg uLow]
    nlinarith only [hp, hd0, huL_sq1, hlog4_0]
  have hprime_cross :
      2 * |⟪Real.log N • uLow - Matrix.toEuclideanLin (fullPrimeMatrix N) uLow, y⟫| ≤ 2 := by
    let diagLow := ∑ m ∈ Icc 1 Q₁,
      (a m * (Real.log N - ramanujanAdjunctionEnergy m)) • normalizedRamanujanHorizonVector m N
    let adjLow := ∑ m ∈ Icc 1 Q₁,
      (a m * ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N
    have hid : Real.log N • uLow - Matrix.toEuclideanLin (fullPrimeMatrix N) uLow =
        adjLow - (Matrix.toEuclideanLin (fullPrimeMatrix N) uLow - diagLow) := by
      have hsub : Real.log N • uLow - diagLow = adjLow := by
        dsimp only [uLow, diagLow, adjLow]
        rw [Finset.smul_sum, ← sum_sub_distrib]
        refine sum_congr rfl fun m _ => ?_
        rw [smul_smul, ← sub_smul]
        congr 1; ring
      rw [← hsub]; abel
    have hadj_norm : ‖adjLow‖ ≤ 4 * (1 + Real.log R') * ‖uLow‖ := by
      have hγ : |Real.eulerMascheroniConstant| ≤ 1 := by
        rw [abs_le]
        have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 0
        simp [Real.eulerMascheroniSeq] at h1
        exact ⟨by linarith, by linarith [Real.eulerMascheroniConstant_lt_two_thirds]⟩
      have hadj_m : ∀ m ∈ Icc 1 Q₁, |ramanujanAdjunctionEnergy m| ≤ 2 * (1 + Real.log R') := by
        intro m hm
        obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
        have hlm0 : 0 ≤ Real.log (m : ℝ) := Real.log_natCast_nonneg m
        have hlmR : Real.log m ≤ Real.log R' :=
          (Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmQ)).trans hlog_Q_le_R'
        have htd0 := tameDifferent_nonneg m
        have htd := (CompletedArithmeticForms.tameDifferent_le_log hm1).trans hlmR
        unfold ramanujanAdjunctionEnergy
        exact (abs_add_le _ _).trans (by
          rw [abs_of_nonneg (add_nonneg hlm0 htd0)]
          linarith only [hγ, hlmR, htd])
      have hadj_sq : (∑ m ∈ Icc 1 Q₁, (a m * ramanujanAdjunctionEnergy m) ^ 2) ≤
          (2 * (1 + Real.log R')) ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2 := by
        rw [mul_sum]
        refine sum_le_sum fun m hm => ?_
        have hsq := pow_le_pow_left₀ (abs_nonneg _) (hadj_m m hm) 2
        rw [sq_abs] at hsq
        nlinarith only [hsq, sq_nonneg (a m)]
      have hru_lo := (half_and_three_halves_riesz_of_log_le hQ₁ hQQ_N hlog18_Q a).1
      have hru_hi := (half_and_three_halves_riesz_of_log_le hQ₁ hQQ_N hlog18_Q
        (fun m => a m * ramanujanAdjunctionEnergy m)).2
      have hnorm_sq : ‖adjLow‖ ^ 2 ≤ (4 * (1 + Real.log R') * ‖uLow‖) ^ 2 := by
        calc
          ‖adjLow‖ ^ 2 ≤ (3 / 2 : ℝ) *
              ∑ m ∈ Icc 1 Q₁, (a m * ramanujanAdjunctionEnergy m) ^ 2 := hru_hi
          _ ≤ (3 / 2 : ℝ) * ((2 * (1 + Real.log R')) ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2) :=
            mul_le_mul_of_nonneg_left hadj_sq (by norm_num)
          _ ≤ (3 / 2 : ℝ) * ((2 * (1 + Real.log R')) ^ 2 * (2 * ‖uLow‖ ^ 2)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (by linarith only [hru_lo]) (sq_nonneg _)) (by norm_num)
          _ ≤ (4 * (1 + Real.log R') * ‖uLow‖) ^ 2 := by
            nlinarith only [sq_nonneg ((1 + Real.log R') * ‖uLow‖)]
      have hrhs0 : 0 ≤ 4 * (1 + Real.log R') * ‖uLow‖ := by
        have := Real.log_natCast_nonneg R'; positivity
      nlinarith only [hnorm_sq, norm_nonneg adjLow, hrhs0]
    have hres_norm : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) uLow - diagLow‖ ≤
        2 * C_pr * ‖uLow‖ := by
      have h1 := hpr_res hQ₁ hQ6N hlog18_Q a
      have h2 : (1 + Real.log Q₁) ^ 2 / Real.sqrt (Real.log N) ≤ 1 := by
        have hle : (1 + Real.log Q₁) ^ 2 ≤ (1 + Real.log R') ^ 2 :=
          pow_le_pow_left₀ (by have := Real.log_natCast_nonneg Q₁; positivity)
            (by linarith only [hlog_Q_le_R']) 2
        have ht2_1 : (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N) ≤ 1 := by
          dsimp only [C_small] at hsmall
          nlinarith only [hsmall, hC_err, hC_ov, hC_pr, hC_mid,
            ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]
        exact (div_le_div_of_nonneg_right hle (Real.sqrt_nonneg _)).trans ht2_1
      exact h1.trans (mul_le_mul_of_nonneg_right (by nlinarith only [hC_pr, h2]) (norm_nonneg _))
    have h1R_sq_div : (1 + Real.log R') ^ 2 / Real.log N ≤
        (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N) :=
      div_le_div_of_nonneg_left (sq_nonneg _) (Real.sqrt_pos.mpr hL0) hsL_le_L
    have hadj_part : 2 * |⟪adjLow, y⟫| ≤ 1 := by
      have h864 : 864 * ((1 + Real.log R') ^ 2 / Real.log N) ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left h1R_sq_div (by norm_num : (0 : ℝ) ≤ 864)
        dsimp only [C_small] at hsmall
        nlinarith only [h, hsmall, hC_err, hC_ov, hC_pr, hC_mid,
          ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]
      calc
        2 * |⟪adjLow, y⟫| ≤ 2 * (‖adjLow‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) zero_le_two
        _ ≤ 2 * ((4 * (1 + Real.log R') * (54 * (1 + Real.log R') / Real.log N)) * 2) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le_two
          exact mul_le_mul
            (hadj_norm.trans (mul_le_mul_of_nonneg_left huLow_bound
              (by have := Real.log_natCast_nonneg R'; positivity)))
            hy_bounds.2 (norm_nonneg y) (by have := Real.log_natCast_nonneg R'; positivity)
        _ = 864 * ((1 + Real.log R') ^ 2 / Real.log N) := by ring
        _ ≤ 1 := h864
    have hres_part : 2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) uLow - diagLow, y⟫| ≤ 1 := by
      have h432 : 432 * C_pr * ((1 + Real.log R') / Real.log N) ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left h1R_div_le (by positivity : 0 ≤ 432 * C_pr)
        dsimp only [C_small] at hsmall
        nlinarith only [h, hsmall, hC_err, hC_ov, hC_pr, hC_mid,
          ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]
      calc
        2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) uLow - diagLow, y⟫| ≤
            2 * (‖Matrix.toEuclideanLin (fullPrimeMatrix N) uLow - diagLow‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) zero_le_two
        _ ≤ 2 * ((2 * C_pr * (54 * (1 + Real.log R') / Real.log N)) * 2) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le_two
          exact mul_le_mul
            (hres_norm.trans (mul_le_mul_of_nonneg_left huLow_bound (by positivity)))
            hy_bounds.2 (norm_nonneg y) (by have := Real.log_natCast_nonneg R'; positivity)
        _ = 432 * C_pr * ((1 + Real.log R') / Real.log N) := by ring
        _ ≤ 1 := h432
    rw [hid, inner_sub_left]
    calc
      2 * |⟪adjLow, y⟫ - ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) uLow - diagLow, y⟫| ≤
          2 * |⟪adjLow, y⟫| +
            2 * |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) uLow - diagLow, y⟫| := by
        linarith only [abs_sub ⟪adjLow, y⟫
          ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) uLow - diagLow, y⟫]
      _ ≤ 2 := by linarith only [hadj_part, hres_part]
  -- Intermediate/high packet bounds directly on y
  have hov_y : |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) y, y⟫| ≤ 4 := by
    have ha0 : ∀ m ∈ Icc 1 Q₁, aRest m = 0 := fun m hm => if_pos (mem_Icc.mp hm).2
    have hm := hmid hQ₁ hQR' hRR_N hlog18_R' hc1 hcL hw1 hradN hRNT ha0
    have hc2_div : c ^ 2 * (1 + Real.log c) / Real.log N ≤
        c * (1 + Real.log c) * (1 + Real.log R') / Real.log N := by
      have hcR : c ≤ 1 + Real.log R' := by
        --Wait: c ≤ log N is NOT c ≤ 1 + log R'! Let's check!
        sorry
    sorry
  sorry

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
