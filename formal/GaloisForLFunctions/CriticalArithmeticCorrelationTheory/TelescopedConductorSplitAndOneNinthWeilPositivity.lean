import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.AsymmetricTwoRegionConductorReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BilinearConductorResidualsAndOneEighthPackets
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.SharpenedMidBandAndCrossBounds

/-!
# Telescoped four-band conductor split and complete Weil positivity below `1 / 9`

Eliminating unit-sphere sublevel confinement in favor of a homogeneous four-band orthogonal
decomposition

`x = y + u₀ + u₁ + w`,
- `y ∈ conductorSubspace Q₁ N` (`Q₁ = ⌊(log N)^q⌋₊`),
- `u₀ ∈ conductorSubspace R₀ N ∩ (conductorSubspace Q₁ N)ᗮ` (`R₀ = ⌊exp((log N)^(1/2))⌋₊`),
- `u₁ ∈ conductorSubspace R₁ N ∩ (conductorSubspace R₀ N)ᗮ` (`R₁ = ⌊N^θ₁⌋₊`),
- `w ∈ (conductorSubspace R₁ N)ᗮ`,

lifts unconditional all-vector positive definiteness of `completeWeilMatrix tiltedUnitSpline c N`
across `1 ≤ c ≤ (log N)^α` to every `0 < α < 1 / 9`:

1. **Complement coercivity (`eventually_tiltedUnitSpline_complement_coercive_below_one_ninth`).**
   Combining homogeneous `(3 / 4) log Q₁` and `(1 / 4) log R₀` packet coercivity, the asymmetric
   `(V_{R₁})ᗮ` two-region reserve (`c^9` prefix / `c^{-7}` terminal), and `c^9`-scaled split cross
   payments establishes `(κ₀ + 2) ‖z‖^2 ≤ completeWeilEnergy tiltedUnitSpline c N z` on all
   `z ∈ (conductorSubspace Q₁ N)ᗮ` without `O(c^{16} / log N)` terminal-mass confinement.
2. **Global two-block Schur synthesis (`eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_ninth`).**
   Pairing `y ∈ conductorSubspace Q₁ N` against `z ∈ (conductorSubspace Q₁ N)ᗮ` via the bilinear
   polylogarithmic subspace floor (`α < 1 / 8`, `α + 2 q < 1`) and the first-power inverse-energy
   residual sum (`∑_{m ≤ Q₁} ‖r_m‖^2 / E_m(c) ≪ (c^7 + Q₁^2 (1 + log Q₁)^2) c^2 / (log N)^{1-o(1)}`)
   establishes positive definiteness of `spectralFloorWeilMatrix c N` and all-vector positivity of
   `completeWeilMatrix tiltedUnitSpline c N` across `1 ≤ c ≤ (log N)^α` for every `0 < α < 1 / 9`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Finset Filter Topology
open scoped Classical BigOperators RealInnerProductSpace Matrix

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics CriticalScaleArithmeticRigidity

/-- Power-of-logarithm overlap ceiling `1 / 9` achieved by the homogeneous four-band conductor
decomposition and first-power inverse-energy Schur decoupling. -/
def oneNinthPowerLogExponent : ℝ := 1 / 9

theorem oneNinthPowerLogExponent_pos : 0 < oneNinthPowerLogExponent := by
  norm_num [oneNinthPowerLogExponent]

theorem one_div_16_lt_oneNinthPowerLogExponent :
    (1 / 16 : ℝ) < oneNinthPowerLogExponent := by
  norm_num [oneNinthPowerLogExponent]

theorem oneNinthPowerLogExponent_lt_oneEighthPowerLogExponent :
    oneNinthPowerLogExponent < oneEighthPowerLogExponent := by
  norm_num [oneNinthPowerLogExponent, oneEighthPowerLogExponent]

/-! ### 1. Orthogonal three-band decomposition and Hermitian quadratic expansion -/

private theorem identity_euclid_apply_telescoped {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]

private theorem hermitian_inner_add_eq_telescoped {N : ℕ}
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin A (x + y), x + y⟫ =
      ⟪Matrix.toEuclideanLin A x, x⟫ + 2 * ⟪Matrix.toEuclideanLin A x, y⟫ +
        ⟪Matrix.toEuclideanLin A y, y⟫ := by
  have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) y x
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym,
    real_inner_comm y (Matrix.toEuclideanLin A x)]
  ring

private theorem completeWeilEnergy_three_add_ge (φ : ℝ → ℝ) (c : ℝ) {N : ℕ}
    (u₀ u₁ w : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N u₀ + completeWeilEnergy φ c N u₁ + completeWeilEnergy φ c N w -
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) u₀, u₁⟫| -
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) u₀, w⟫| -
      2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) u₁, w⟫| ≤
      completeWeilEnergy φ c N (u₀ + u₁ + w) := by
  have h1 := hermitian_inner_add_eq_telescoped (completeWeilMatrix_isHermitian φ c N) (u₀ + u₁) w
  have h2 := hermitian_inner_add_eq_telescoped (completeWeilMatrix_isHermitian φ c N) u₀ u₁
  unfold completeWeilEnergy
  rw [h1, h2, map_add, inner_add_left]
  have habs01 := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) u₀, u₁⟫
  have habs0w := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) u₀, w⟫
  have habs1w := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) u₁, w⟫
  linarith only [habs01, habs0w, habs1w]

private theorem sub_starProjection_mem_orthogonal_telescoped {N : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)))
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    x - K.starProjection x ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [real_inner_comm]
  exact K.starProjection_inner_eq_zero x v hv

private theorem telescoped_three_band_orthogonal_split {Q₁ R₀ R₁ N : ℕ}
    (hQR₀ : Q₁ ≤ R₀) (hR₀R₁ : R₀ ≤ R₁)
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hz : z ∈ (conductorSubspace Q₁ N)ᗮ) :
    let u₀ := (conductorSubspace R₀ N).starProjection z
    let u₁ := (conductorSubspace R₁ N).starProjection z -
      (conductorSubspace R₀ N).starProjection z
    let w := z - (conductorSubspace R₁ N).starProjection z
    z = u₀ + u₁ + w ∧
    u₀ ∈ conductorSubspace R₀ N ∧
    u₀ ∈ (conductorSubspace Q₁ N)ᗮ ∧
    u₁ ∈ conductorSubspace R₁ N ∧
    u₁ ∈ (conductorSubspace R₀ N)ᗮ ∧
    w ∈ (conductorSubspace R₁ N)ᗮ ∧
    ‖z‖ ^ 2 = ‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 + ‖w‖ ^ 2 := by
  dsimp only
  let p₀ := (conductorSubspace R₀ N).starProjection z
  let p₁ := (conductorSubspace R₁ N).starProjection z
  let u₁ := p₁ - p₀
  let w := z - p₁
  have hz_eq : z = p₀ + u₁ + w := by dsimp only [u₁, w]; abel
  have hp₀_mem : p₀ ∈ conductorSubspace R₀ N :=
    (conductorSubspace R₀ N).starProjection_apply_mem z
  have hp₁_mem : p₁ ∈ conductorSubspace R₁ N :=
    (conductorSubspace R₁ N).starProjection_apply_mem z
  have hp₀_in_R₁ : p₀ ∈ conductorSubspace R₁ N :=
    conductorSubspace_mono hR₀R₁ N hp₀_mem
  have hu₁_mem : u₁ ∈ conductorSubspace R₁ N :=
    Submodule.sub_mem _ hp₁_mem hp₀_in_R₁
  have hz_sub_p₀ : z - p₀ ∈ (conductorSubspace R₀ N)ᗮ :=
    sub_starProjection_mem_orthogonal_telescoped _ z
  have hz_sub_p₁ : w ∈ (conductorSubspace R₁ N)ᗮ :=
    sub_starProjection_mem_orthogonal_telescoped _ z
  have hp₀_orthQ : p₀ ∈ (conductorSubspace Q₁ N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hvR₀ : v ∈ conductorSubspace R₀ N := conductorSubspace_mono hQR₀ N hv
    have hzv : ⟪v, z⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hv hz
    have hdiff : ⟪v, z - p₀⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hvR₀ hz_sub_p₀
    have hp₀_id : p₀ = z - (z - p₀) := by abel
    rw [hp₀_id, inner_sub_right, hzv, hdiff, sub_zero]
  have hu₁_orthR₀ : u₁ ∈ (conductorSubspace R₀ N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hvR₁ : v ∈ conductorSubspace R₁ N := conductorSubspace_mono hR₀R₁ N hv
    have hdiff₀ : ⟪v, z - p₀⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hv hz_sub_p₀
    have hdiff₁ : ⟪v, z - p₁⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hvR₁ hz_sub_p₁
    have hu₁_id : u₁ = (z - p₀) - (z - p₁) := by dsimp only [u₁]; abel
    rw [hu₁_id, inner_sub_right, hdiff₀, hdiff₁, sub_zero]
  have horth01 : ⟪p₀, u₁⟫ = 0 :=
    Submodule.inner_right_of_mem_orthogonal hp₀_mem hu₁_orthR₀
  have hp₁_eq : p₀ + u₁ = p₁ := by dsimp only [u₁]; abel
  have horth1w : ⟪p₀ + u₁, w⟫ = 0 := by
    rw [hp₁_eq]
    exact Submodule.inner_right_of_mem_orthogonal hp₁_mem hz_sub_p₁
  have hnorm : ‖z‖ ^ 2 = ‖p₀‖ ^ 2 + ‖u₁‖ ^ 2 + ‖w‖ ^ 2 := by
    have h1 := norm_add_sq_real (p₀ + u₁) w
    have h2 := norm_add_sq_real p₀ u₁
    rw [← hz_eq] at h1
    rw [horth1w, mul_zero, add_zero, h2, horth01, mul_zero, add_zero] at h1
    exact h1
  exact ⟨hz_eq, hp₀_mem, hp₀_orthQ, hu₁_mem, hu₁_orthR₀, hz_sub_p₁, hnorm⟩

/-! ### 2. Cutoff and horizon geometry for `Q₁`, `R₀`, and `R₁` -/

private theorem eventually_log_nat_le_rpow_36_one_ninth :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).bound zero_lt_one)
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hN _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
    simpa only [Function.comp_def, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN
  exact (le_abs_self _).trans habs

private theorem rpow_horizon_N_bounds_one_ninth {N R' : ℕ} {c : ℝ}
    (hN1 : 1 ≤ N) (hR'2 : 2 ≤ R') (hc1 : 1 ≤ c)
    (hL2000 : 2000 ≤ Real.log (N : ℝ))
    (hLX : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ))
    (hcL : c ≤ Real.log (N : ℝ))
    (hlog36 : 36 * (1 + Real.log (R' : ℝ)) ≤ Real.log (N : ℝ)) :
    linearDefectCutoff c ≤ N ∧
    4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) ∧
    c / (N : ℝ) ≤ 1 / 3 ∧
    4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) ∧
    R' ^ 6 ≤ N ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) ∧
    (R' : ℝ) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 5 * Real.log (N : ℝ) / (N : ℝ) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 3 * (R' : ℝ) ^ 2 * (Real.log (N : ℝ) / (N : ℝ)) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 10 * (R' : ℝ) ^ 2 / (N : ℝ) ≤ 1 / Real.log (N : ℝ) := by
  let L := Real.log (N : ℝ)
  let X := (N : ℝ) ^ (1 / 36 : ℝ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hL0 : 0 < L := by dsimp only [L]; linarith only [hL2000]
  have hX2000 : 2000 ≤ X := hL2000.trans hLX
  have hX1 : 1 ≤ X := by linarith only [hX2000]
  have hX0 : 0 < X := zero_lt_one.trans_le hX1
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcX : c ≤ X := hcL.trans hLX
  have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
    dsimp only [X]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hpowX : ∀ k : ℕ, k ≤ 36 → X ^ k ≤ (N : ℝ) := fun k hk =>
    (pow_le_pow_right₀ hX1 hk).trans_eq hX36
  have hR'X : (R' : ℝ) ≤ X := by
    have hR'0 : (0 : ℝ) < R' := by exact_mod_cast (show 0 < R' by omega)
    have hlog_le : Real.log (R' : ℝ) ≤ Real.log X := by
      have h1 : Real.log X = (1 / 36 : ℝ) * Real.log (N : ℝ) := Real.log_rpow hN0 (1 / 36 : ℝ)
      linarith only [hlog36, h1]
    exact (Real.exp_log hR'0).symm.trans_le
      ((Real.exp_le_exp.mpr hlog_le).trans_eq (Real.exp_log hX0))
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have he2 : Real.exp 2 ≤ 9 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [he1, h2, Real.exp_pos 1]
  have hlin_le : linearNearRowRadius c + 1 ≤ 19 * X := by
    unfold linearNearRowRadius
    nlinarith only [hc1, hcX, he2]
  have hup_le : c * Real.exp 1 + 1 ≤ 4 * X := by nlinarith only [hc0, hc1, hcX, he1]
  have hRR1_le : ((R' * R' : ℕ) + 1 : ℝ) ≤ 2 * X ^ 2 := by
    have hR1 : (1 : ℝ) ≤ R' := by exact_mod_cast (show 1 ≤ R' by omega)
    push_cast
    have hsq : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (by positivity) hR'X 2
    have h1sq : (1 : ℝ) ≤ (R' : ℝ) ^ 2 := one_le_pow₀ hR1
    linarith only [hsq, h1sq]
  have h1 : linearDefectCutoff c ≤ N := by
    have hcut := (linearDefectCutoff_bounds hc1).2.2.2
    have hcoef : 256 * Real.exp 2 + 4 ≤ 2 * X := by nlinarith only [he2, hX2000]
    have hR : (linearDefectCutoff c : ℝ) ≤ (N : ℝ) := by
      calc
        (linearDefectCutoff c : ℝ) ≤ (256 * Real.exp 2 + 4) * c := hcut
        _ ≤ (2 * X) * X := mul_le_mul hcoef hcX hc0.le (by positivity)
        _ = 2 * X ^ 2 := by ring
        _ ≤ X * X ^ 2 := mul_le_mul_of_nonneg_right (by linarith only [hX2000]) (sq_nonneg X)
        _ = X ^ 3 := by ring
        _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
    exact_mod_cast hR
  have h2 : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) := by
    have hc2 : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc0.le hcX 2
    have hconst : 4 * (Real.exp 1 + 3) ^ 2 ≤ X := by
      have : 4 * (Real.exp 1 + 3) ^ 2 ≤ 144 := by nlinarith only [he1, Real.exp_pos 1]
      linarith only [this, hX2000]
    calc
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ X * X ^ 2 :=
        mul_le_mul hconst hc2 (by positivity) hX0.le
      _ = X ^ 3 := by ring
      _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
  have h3 : c / (N : ℝ) ≤ 1 / 3 := by
    rw [div_le_div_iff₀ hN0 (by norm_num)]
    have h3X : 3 * c ≤ X ^ 2 := by nlinarith only [hcX, hX2000]
    exact (by linarith only [h3X] : c * 3 ≤ X ^ 2).trans
      (by simpa only [one_mul] using hpowX 2 (by norm_num))
  have h4 : 4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) := by
    have hsq : (linearNearRowRadius c + 1) ^ 2 ≤ (19 * X) ^ 2 :=
      pow_le_pow_left₀ (by unfold linearNearRowRadius; positivity) hlin_le 2
    have h1444 : 1444 * X ^ 2 ≤ X ^ 3 := by nlinarith only [hX2000, sq_nonneg X]
    calc
      4 * (linearNearRowRadius c + 1) ^ 2 ≤ 4 * (19 * X) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by norm_num)
      _ = 1444 * X ^ 2 := by ring
      _ ≤ X ^ 3 := h1444
      _ ≤ (N : ℝ) := hpowX 3 (by norm_num)
  have h5 : R' ^ 6 ≤ N := by
    have hR6 : (R' : ℝ) ^ 6 ≤ (N : ℝ) :=
      (pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 6).trans (hpowX 6 (by norm_num))
    exact_mod_cast hR6
  have h6 : ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) := by
    have h38 : 38 * X ^ 3 ≤ X ^ 4 := by
      calc
        38 * X ^ 3 ≤ X * X ^ 3 :=
          mul_le_mul_of_nonneg_right (by linarith only [hX2000]) (by positivity)
        _ = X ^ 4 := by ring
    calc
      ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (2 * X ^ 2) * (19 * X) :=
        mul_le_mul hRR1_le hlin_le (by unfold linearNearRowRadius; positivity) (by positivity)
      _ = 38 * X ^ 3 := by ring
      _ ≤ X ^ 4 := h38
      _ ≤ (N : ℝ) := hpowX 4 (by norm_num)
  have h7 : ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) := by
    have h8 : 8 * X ^ 3 ≤ X ^ 4 := by nlinarith only [hX2000, pow_nonneg hX0.le 3]
    calc
      ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (2 * X ^ 2) * (4 * X) :=
        mul_le_mul hRR1_le hup_le (by positivity) (by positivity)
      _ = 8 * X ^ 3 := by ring
      _ ≤ X ^ 4 := h8
      _ ≤ (N : ℝ) := hpowX 4 (by norm_num)
  have h8 : (R' : ℝ) * Real.sqrt (L / (N : ℝ)) ≤ 1 / L := by
    have hprod : (R' : ℝ) ^ 2 * L ^ 3 ≤ (N : ℝ) := by
      have hR2 : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 2
      have hL3 : L ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hL0.le hLX 3
      calc
        (R' : ℝ) ^ 2 * L ^ 3 ≤ X ^ 2 * X ^ 3 := mul_le_mul hR2 hL3 (by positivity) (by positivity)
        _ = X ^ 5 := by ring
        _ ≤ (N : ℝ) := hpowX 5 (by norm_num)
    have hsq : ((R' : ℝ) * Real.sqrt (L / (N : ℝ))) ^ 2 ≤ (1 / L) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), one_div, inv_pow, ← one_div]
      rw [← mul_div_assoc, div_le_div_iff₀ hN0 (sq_pos_of_pos hL0)]
      calc
        (R' : ℝ) ^ 2 * L * L ^ 2 = (R' : ℝ) ^ 2 * L ^ 3 := by ring
        _ ≤ 1 * (N : ℝ) := by rw [one_mul]; exact hprod
    have hlhs0 : 0 ≤ (R' : ℝ) * Real.sqrt (L / (N : ℝ)) := by positivity
    have hrhs0 : 0 ≤ 1 / L := by positivity
    nlinarith only [hsq, hlhs0, hrhs0]
  have h9 : c ^ 5 * L / (N : ℝ) ≤ 1 / L := by
    rw [div_le_div_iff₀ hN0 hL0, one_mul]
    have hc5 : c ^ 5 ≤ X ^ 5 := pow_le_pow_left₀ hc0.le hcX 5
    have hL2 : L ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hL0.le hLX 2
    calc
      c ^ 5 * L * L = c ^ 5 * L ^ 2 := by ring
      _ ≤ X ^ 5 * X ^ 2 := mul_le_mul hc5 hL2 (by positivity) (by positivity)
      _ = X ^ 7 := by ring
      _ ≤ (N : ℝ) := hpowX 7 (by norm_num)
  have h10 : c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) ≤ 1 / L := by
    rw [div_le_div_iff₀ hN0 hL0, one_mul]
    have hc3 : c ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hc0.le hcX 3
    have hR4 : (R' : ℝ) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 4
    calc
      c ^ 3 * (R' : ℝ) ^ 4 * L ≤ (X ^ 3 * X ^ 4) * X :=
        mul_le_mul (mul_le_mul hc3 hR4 (by positivity) (by positivity)) hLX hL0.le (by positivity)
      _ = X ^ 8 := by ring
      _ ≤ (N : ℝ) := hpowX 8 (by norm_num)
  have h11 : c ^ 3 * (R' : ℝ) ^ 2 * (L / (N : ℝ)) ≤ 1 / L := by
    rw [← mul_div_assoc, div_le_div_iff₀ hN0 hL0, one_mul]
    have hc3 : c ^ 3 ≤ X ^ 3 := pow_le_pow_left₀ hc0.le hcX 3
    have hR2 : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 2
    have hL2 : L ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hL0.le hLX 2
    calc
      c ^ 3 * (R' : ℝ) ^ 2 * L * L = (c ^ 3 * (R' : ℝ) ^ 2) * L ^ 2 := by ring
      _ ≤ (X ^ 3 * X ^ 2) * X ^ 2 :=
        mul_le_mul (mul_le_mul hc3 hR2 (by positivity) (by positivity)) hL2 (by positivity)
          (by positivity)
      _ = X ^ 7 := by ring
      _ ≤ (N : ℝ) := hpowX 7 (by norm_num)
  have h12 : c ^ 10 * (R' : ℝ) ^ 2 / (N : ℝ) ≤ 1 / L := by
    rw [div_le_div_iff₀ hN0 hL0, one_mul]
    have hc10 : c ^ 10 ≤ X ^ 10 := pow_le_pow_left₀ hc0.le hcX 10
    have hR2 : (R' : ℝ) ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg R') hR'X 2
    calc
      c ^ 10 * (R' : ℝ) ^ 2 * L ≤ (X ^ 10 * X ^ 2) * X :=
        mul_le_mul (mul_le_mul hc10 hR2 (by positivity) (by positivity)) hLX hL0.le (by positivity)
      _ = X ^ 13 := by ring
      _ ≤ (N : ℝ) := hpowX 13 (by norm_num)
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

private theorem linear_prefix_horizon_bounds_one_ninth {N R : ℕ} {c : ℝ}
    (hN1 : 1 ≤ N) (hR : 2 ≤ R) (hc : 1 ≤ c)
    (hL3000 : 3000 ≤ Real.log N)
    (hLX : Real.log N ≤ (N : ℝ) ^ (1 / 36 : ℝ)) (hcL : c ≤ Real.log N)
    (hlog36 : 36 * (1 + Real.log R) ≤ Real.log N) :
    R * R ≤ N / linearDefectCutoff c ∧
    18 * (1 + Real.log R) ≤ Real.log (N / linearDefectCutoff c : ℕ) ∧
    terminalPacketCost R (N / linearDefectCutoff c) N ≤
      (4 + Real.log (2 * (256 * Real.exp 2 + 4)) + 1) * (1 + Real.log c) ∧
    Real.log N / 2 ≤ Real.log (N / linearDefectCutoff c : ℕ) := by
  let X := (N : ℝ) ^ (1 / 36 : ℝ)
  let Hlin : ℝ := 256 * Real.exp 2 + 4
  let T := linearDefectCutoff c
  let M := N / T
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hX3000 : 3000 ≤ X := hL3000.trans hLX
  have hX1 : 1 ≤ X := by linarith only [hX3000]
  have hX0 := zero_lt_one.trans_le hX1
  have hL : 0 < Real.log N := by linarith only [hL3000]
  have hc0 := zero_lt_one.trans_le hc
  have hcX : c ≤ X := hcL.trans hLX
  have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
  have he2 : Real.exp 2 ≤ 9 := by
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith only [he1, h2, Real.exp_pos 1]
  have hHlin1 : 1 ≤ Hlin := by
    have := Real.exp_pos 2; dsimp only [Hlin]; linarith only [this]
  have hHlinX : Hlin ≤ X := by dsimp only [Hlin]; linarith only [he2, hX3000]
  have hcut : (T : ℝ) ≤ Hlin * c := (linearDefectCutoff_bounds hc).2.2.2
  have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
    dsimp only [X]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
  have hpowX : ∀ j : ℕ, j ≤ 36 → X ^ j ≤ (N : ℝ) := fun j hj =>
    (pow_le_pow_right₀ hX1 hj).trans_eq hX36
  have hRX : (R : ℝ) ≤ X := by
    have hR0 : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
    have hlogX : Real.log X = (1 / 36 : ℝ) * Real.log N := Real.log_rpow hN0 _
    have hh : Real.log R ≤ Real.log X := by linarith only [hlog36, hlogX]
    exact (Real.exp_log hR0).symm.trans_le
      ((Real.exp_le_exp.mpr hh).trans_eq (Real.exp_log hX0))
  have hT3 : 3 ≤ T := (linearDefectCutoff_bounds hc).1
  have hT1 : 1 ≤ T := by omega
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  have hTX : (T : ℝ) ≤ X ^ 2 := by
    calc
      (T : ℝ) ≤ Hlin * c := hcut
      _ ≤ X * X := mul_le_mul hHlinX hcX hc0.le hX0.le
      _ = X ^ 2 := by ring
  have hRRT : R * R * T ≤ N := by
    have hh : (R : ℝ) ^ 2 * T ≤ (N : ℝ) := by
      calc
        _ ≤ X ^ 2 * X ^ 2 := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg R) hRX 2)
          hTX hT0.le (by positivity)
        _ = X ^ 4 := by ring
        _ ≤ _ := hpowX 4 (by norm_num)
    have hhNat : R ^ 2 * T ≤ N := by exact_mod_cast hh
    simpa only [pow_two] using hhNat
  have hRM : R * R ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < T)).mpr hRRT
  have hM2 : 2 ≤ M := (by norm_num : 2 ≤ 2 * 2).trans ((Nat.mul_le_mul hR hR).trans hRM)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hTN : T ≤ N := by
    have hR1 : 1 ≤ R * R := Nat.mul_pos (by omega) (by omega)
    have hmul : T ≤ R * R * T := by
      simpa only [one_mul] using Nat.mul_le_mul_right T hR1
    exact hmul.trans hRRT
  have hfloor : (N : ℝ) < ((M : ℝ) + 1) * T := by
    have hh : N < (M + 1) * T := by
      simpa only [M, Nat.mul_comm] using Nat.lt_mul_div_succ N (show 0 < T by omega)
    exact_mod_cast hh
  have hratio : Real.log N - Real.log M ≤ Real.log (2 * (T : ℝ)) := by
    rw [← Real.log_div hN0.ne' hM0.ne']
    apply Real.log_le_log (div_pos hN0 hM0)
    apply (div_le_iff₀ hM0).mpr
    nlinarith only [hfloor, mul_nonneg (sub_nonneg.mpr hM1) hT0.le]
  have hlogT : Real.log (2 * (T : ℝ)) ≤ Real.log N / 4 + 1 := by
    have hh := Real.log_le_log (by positivity : 0 < 2 * (T : ℝ))
      (mul_le_mul_of_nonneg_left hTX zero_le_two)
    rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hX0.ne'), Real.log_pow,
      show Real.log X = (1 / 36 : ℝ) * Real.log N from Real.log_rpow hN0 _] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hh, h2, hL]
  have hhalf : Real.log N / 2 ≤ Real.log M := by linarith only [hratio, hlogT, hL3000]
  have hlogM : 18 * (1 + Real.log R) ≤ Real.log M := by linarith only [hlog36, hhalf]
  have hterminal :
      terminalPacketCost R M N ≤ (4 + Real.log (2 * Hlin) + 1) * (1 + Real.log c) := by
    have hh := terminalPacketCost_nat_div_le hT1 hTN hRM
    change terminalPacketCost R M N ≤ 4 + Real.log (2 * (T : ℝ)) at hh
    have h2Ht : 0 < 2 * Hlin := by linarith only [hHlin1]
    have ht := Real.log_le_log (by positivity : 0 < 2 * (T : ℝ))
      (mul_le_mul_of_nonneg_left hcut zero_le_two)
    rw [show 2 * (Hlin * c) = (2 * Hlin) * c by ring,
      Real.log_mul h2Ht.ne' hc0.ne'] at ht
    have hlc : 0 ≤ Real.log c := Real.log_nonneg hc
    have hpos : 0 ≤ 4 + Real.log (2 * Hlin) :=
      add_nonneg (by norm_num) (Real.log_nonneg (by linarith only [hHlin1]))
    nlinarith only [hh, ht, hlc, hpos]
  exact ⟨hRM, hlogM, hterminal, hhalf⟩

/-! ### 3. Deterministic cross-band absorption bounds -/

/-- Cross payment between `u₀ ∈ V_{R₀} ∩ (V_1)ᗮ` and `u₁ ∈ (V_{R₀})ᗮ` at `M = N`, spending
`(1 / 16) * (log N)^(1/2) * ‖u₁‖^2` from Band 1's subpolynomial logarithmic reserve. -/
private theorem exists_band0_band1_cross_le :
    ∃ C_cross01 : ℝ, 0 < C_cross01 ∧
      ∀ {R₀ N : ℕ} {c : ℝ},
        2 ≤ R₀ → R₀ ^ 6 ≤ N → 18 * (1 + Real.log R₀) ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R₀ * R₀ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R₀ * R₀ : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        1 + Real.log R₀ ≤ 2 * Real.log N ^ (1 / 2 : ℝ) →
        C_cross01 * (1 / Real.log N ^ (1 / 2 : ℝ) +
          c ^ 2 * (1 + Real.log c) / Real.log N ^ (1 / 2 : ℝ) +
          c ^ 4 * (1 + Real.log c) / Real.log N +
          c ^ 3 * (R₀ : ℝ) ^ 2 * (Real.log N / N)) ≤ 1 →
      ∀ a₀ : ℕ → ℝ,
        (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N) ∈
          (conductorSubspace 1 N)ᗮ →
      ∀ {u₁ : EuclideanSpace ℝ (PrimeHorizonIndex N)}, u₁ ∈ (conductorSubspace R₀ N)ᗮ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N), u₁⟫| ≤
          (1 / 32 : ℝ) * primeAdjunctionMass R₀ a₀ +
            (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
            (1 / 16 : ℝ) * Real.log N ^ (1 / 2 : ℝ) * ‖u₁‖ ^ 2 := by
  obtain ⟨C_pr, C_np, hC_pr, hC_np, hcross⟩ := exists_completeWeil_cross_le_c9_split_reserves
  let C_cross01 := 32768 * (C_pr + C_np + 1)
  refine ⟨C_cross01, by dsimp only [C_cross01]; positivity, ?_⟩
  intro R₀ N c hR₀ hR₀6 hlog hc1 hw1 hsize_near hsize_up hH₀_ub hsmall a₀ hu₀_1 u₁ hu₁
  let L := Real.log (N : ℝ)
  let Lh := L ^ (1 / 2 : ℝ)
  let s := (1 / 32 : ℝ) * Lh
  let u₀ := ∑ m ∈ Icc 1 R₀, a₀ m • normalizedRamanujanHorizonVector m N
  let H₀ := 1 + Real.log (R₀ : ℝ)
  let A₀ := ∑ m ∈ Icc 1 R₀, a₀ m ^ 2
  let E₀ := primeAdjunctionMass R₀ a₀
  let G₀ := ∑ m ∈ Icc 1 R₀, (1 + Real.log m) * a₀ m ^ 2
  have hRR₀ : R₀ * R₀ ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R₀) (by norm_num : 2 ≤ 6)).trans hR₀6
    simpa only [sq] using hh
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [hlog, Real.log_natCast_nonneg R₀]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLh1 : 1 ≤ Lh := Real.one_le_rpow hL1 (by norm_num)
  have hLh0 : 0 < Lh := zero_lt_one.trans_le hLh1
  have hLh_sq : Lh * Lh = L := by
    dsimp only [Lh]
    rw [← Real.rpow_add hL0]
    norm_num [Real.rpow_one]
  have hs0 : 0 < s := by dsimp only [s]; positivity
  have hraw := hcross hR₀ hR₀6 (le_rfl : N ≤ N) hlog hc1 hw1 hsize_near hsize_up a₀ hu₀_1 hu₁
    s s s hs0 hs0 hs0
  rw [sum_primeHorizonExtension_sq u₁, Finset.Ioc_self, sum_empty, mul_zero, add_zero] at hraw
  have hterm_N : terminalPacketCost R₀ N N ≤ 2 := by
    unfold terminalPacketCost
    rw [sub_self, zero_add]
    have hRsq : (R₀ : ℝ) ^ 2 ≤ (N : ℝ) + 1 := by
      have hcast : (R₀ : ℝ) ^ 2 ≤ (N : ℝ) := by
        simpa only [sq, Nat.cast_mul] using (Nat.cast_le (α := ℝ).mpr hRR₀)
      linarith only [hcast]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)).mpr (by linarith only [hRsq])
  have hA₀ : 0 ≤ A₀ := sum_nonneg fun _ _ => sq_nonneg _
  have hE₀ : 0 ≤ E₀ := primeAdjunctionMass_nonneg R₀ a₀
  have hG₀ : 0 ≤ G₀ := sum_nonneg fun m _ => by have := Real.log_natCast_nonneg m; positivity
  have hAU : A₀ ≤ 2 * ‖u₀‖ ^ 2 := by
    have hh := (half_and_three_halves_riesz_of_log_le hR₀ hRR₀ hlog a₀).1
    linarith only [hh]
  have hG_le : G₀ ≤ 2 * ‖u₀‖ ^ 2 + E₀ := by
    have hGE : G₀ ≤ A₀ + E₀ := by
      dsimp only [G₀, A₀, E₀, primeAdjunctionMass]
      rw [← sum_add_distrib]
      refine sum_le_sum fun m _ => ?_
      nlinarith only [mul_nonneg (tameDifferent_nonneg m) (sq_nonneg (a₀ m))]
    linarith only [hGE, hAU]
  let e := 1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
    c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have he_small : (C_pr + C_np + 1) * e ≤ 1 / 32768 := by
    dsimp only [C_cross01, L, Lh] at hsmall
    change 32768 * (C_pr + C_np + 1) * e ≤ 1 at hsmall
    linarith only [hsmall]
  have he1 : 1 / Lh ≤ e := by
    have hh : 0 ≤ c ^ 2 * (1 + Real.log c) / Lh +
        c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) := by positivity
    dsimp only [e]; linarith only [hh]
  have he2 : c ^ 2 * (1 + Real.log c) / Lh ≤ e := by
    have hh : 0 ≤ 1 / Lh + c ^ 4 * (1 + Real.log c) / L +
        c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) := by positivity
    dsimp only [e]; linarith only [hh]
  have he34 : c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ e := by
    have hh : 0 ≤ 1 / Lh + c ^ 2 * (1 + Real.log c) / Lh := by positivity
    dsimp only [e]; linarith only [hh]
  have hinvL_le : 1 / L ≤ 1 / Lh :=
    one_div_le_one_div_of_le hLh0 (by nlinarith only [hLh1, hLh_sq])
  have hc2L_le : c ^ 2 * (1 + Real.log c) / L ≤ c ^ 2 * (1 + Real.log c) / Lh :=
    div_le_div_of_nonneg_left (by positivity) hLh0 (by nlinarith only [hLh1, hLh_sq])
  have hH₀_s : H₀ / (L * s) ≤ 64 * e := by
    have h1 : H₀ / (L * s) ≤ (2 * Lh) / (L * ((1 / 32 : ℝ) * Lh)) :=
      div_le_div_of_nonneg_right hH₀_ub (by positivity)
    have h2 : (2 * Lh) / (L * ((1 / 32 : ℝ) * Lh)) = 64 * (1 / L) := by
      field_simp [hL0.ne', hLh0.ne']; ring
    exact h1.trans (h2.trans_le (mul_le_mul_of_nonneg_left (hinvL_le.trans he1) (by norm_num)))
  have hH₀sq_s : H₀ ^ 2 / (L * s) ≤ 128 * e := by
    have hsq : H₀ ^ 2 ≤ 4 * L := by
      have hp := pow_le_pow_left₀ (by positivity) hH₀_ub 2
      calc
        H₀ ^ 2 ≤ (2 * Lh) ^ 2 := hp
        _ = 4 * (Lh * Lh) := by ring
        _ = 4 * L := by rw [hLh_sq]
    have h1 : H₀ ^ 2 / (L * s) ≤ (4 * L) / (L * ((1 / 32 : ℝ) * Lh)) :=
      div_le_div_of_nonneg_right hsq (by positivity)
    have h2 : (4 * L) / (L * ((1 / 32 : ℝ) * Lh)) = 128 * (1 / Lh) := by
      field_simp [hL0.ne', hLh0.ne']; ring
    exact h1.trans (h2.trans_le (mul_le_mul_of_nonneg_left he1 (by norm_num)))
  have hH₀B_s : H₀ * terminalPacketCost R₀ N N / (L * s) ≤ 128 * e := by
    have hprod : H₀ * terminalPacketCost R₀ N N ≤ 2 * H₀ := by
      have hH0 : 0 ≤ H₀ := by dsimp only [H₀]; positivity
      nlinarith only [hterm_N, hH0]
    calc
      H₀ * terminalPacketCost R₀ N N / (L * s) ≤ (2 * H₀) / (L * s) :=
        div_le_div_of_nonneg_right hprod (by positivity)
      _ = 2 * (H₀ / (L * s)) := by ring
      _ ≤ 2 * (64 * e) := mul_le_mul_of_nonneg_left hH₀_s (by norm_num)
      _ = 128 * e := by ring
  have hG_s : (c ^ 2 * H₀ * (1 + Real.log c) / L) / s ≤ 64 * e := by
    have hnum : c ^ 2 * H₀ * (1 + Real.log c) ≤ 2 * Lh * (c ^ 2 * (1 + Real.log c)) := by
      have hc20 : 0 ≤ c ^ 2 * (1 + Real.log c) := by positivity
      have hm := mul_le_mul_of_nonneg_right hH₀_ub hc20
      linarith only [hm, (by ring : c ^ 2 * H₀ * (1 + Real.log c) = H₀ * (c ^ 2 * (1 + Real.log c))),
        (by ring : (2 * Lh) * (c ^ 2 * (1 + Real.log c)) = 2 * Lh * (c ^ 2 * (1 + Real.log c)))]
    calc
      (c ^ 2 * H₀ * (1 + Real.log c) / L) / s ≤
          (2 * Lh * (c ^ 2 * (1 + Real.log c)) / L) / ((1 / 32 : ℝ) * Lh) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hnum hL0.le) hs0.le
      _ = 64 * (c ^ 2 * (1 + Real.log c) / L) := by field_simp [hL0.ne', hLh0.ne']; ring
      _ ≤ 64 * e := mul_le_mul_of_nonneg_left (hc2L_le.trans he2) (by norm_num)
  have hU_s :
      (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) / s ≤ 64 * e := by
    have hs_ge : (1 / 32 : ℝ) ≤ s := by dsimp only [s]; linarith only [hLh1]
    have hpart1 :
        (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) / s ≤ 32 * e := by
      calc
        _ ≤ (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) / (1 / 32 : ℝ) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hs_ge
        _ = 32 * (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) := by ring
        _ ≤ 32 * e := mul_le_mul_of_nonneg_left he34 (by norm_num)
    have hpart2 : c ^ 2 * (1 + Real.log c) / s ≤ 32 * e := by
      have hid : c ^ 2 * (1 + Real.log c) / ((1 / 32 : ℝ) * Lh) =
          32 * (c ^ 2 * (1 + Real.log c) / Lh) := by field_simp [hLh0.ne']
      dsimp only [s]
      rw [hid]
      exact mul_le_mul_of_nonneg_left he2 (by norm_num)
    rw [add_div]
    linarith only [hpart1, hpart2]
  -- Bound the four u₀-side coefficients by `1 / 128`.
  have hpa : C_pr * (H₀ / (L * s)) + C_pr * (H₀ / (L * s)) ≤ 1 / 128 := by
    have h1 := mul_le_mul_of_nonneg_left hH₀_s hC_pr.le
    have he0 : 0 ≤ e := le_trans (by positivity) he1
    nlinarith only [h1, he_small, mul_nonneg hC_np.le he0, he0]
  have hpe : C_pr * (H₀ ^ 2 / (L * s)) + C_pr * (H₀ * terminalPacketCost R₀ N N / (L * s)) ≤
      1 / 128 := by
    have h1 := mul_le_mul_of_nonneg_left hH₀sq_s hC_pr.le
    have h2 := mul_le_mul_of_nonneg_left hH₀B_s hC_pr.le
    have he0 : 0 ≤ e := le_trans (by positivity) he1
    nlinarith only [h1, h2, he_small, mul_nonneg hC_np.le he0, he0]
  have hng : C_np * ((c ^ 2 * H₀ * (1 + Real.log c) / L) / s) ≤ 1 / 128 := by
    have h1 := mul_le_mul_of_nonneg_left hG_s hC_np.le
    have he0 : 0 ≤ e := le_trans (by positivity) he1
    nlinarith only [h1, he_small, mul_nonneg hC_pr.le he0, he0]
  have hnu :
      C_np * ((c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) +
        c ^ 2 * (1 + Real.log c)) / s) ≤ 1 / 16 := by
    have h1 := mul_le_mul_of_nonneg_left hU_s hC_np.le
    have he0 : 0 ≤ e := le_trans (by positivity) he1
    nlinarith only [h1, he_small, mul_nonneg hC_pr.le he0, he0]
  have hfact :
      C_pr * (H₀ * A₀ + H₀ ^ 2 * E₀) / (L * s) +
        C_pr * (H₀ * A₀ + H₀ * terminalPacketCost R₀ N N * E₀) / (L * s) +
        C_np * ((c ^ 2 * H₀ * (1 + Real.log c) / L) * G₀ +
          (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) +
            c ^ 2 * (1 + Real.log c)) * ‖u₀‖ ^ 2) / s =
      (C_pr * (H₀ / (L * s)) + C_pr * (H₀ / (L * s))) * A₀ +
        (C_pr * (H₀ ^ 2 / (L * s)) + C_pr * (H₀ * terminalPacketCost R₀ N N / (L * s))) * E₀ +
        (C_np * ((c ^ 2 * H₀ * (1 + Real.log c) / L) / s)) * G₀ +
        (C_np * ((c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) / s)) * ‖u₀‖ ^ 2 := by ring
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u₀, u₁⟫| ≤
    C_pr * (H₀ * A₀ + H₀ ^ 2 * E₀) / (L * s) +
      C_pr * (H₀ * A₀ + H₀ * terminalPacketCost R₀ N N * E₀) / (L * s) +
      C_np * ((c ^ 2 * H₀ * (1 + Real.log c) / L) * G₀ +
        (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) * ‖u₀‖ ^ 2) / s +
      s * ‖u₁‖ ^ 2 + s * ‖u₁‖ ^ 2 at hraw
  rw [hfact] at hraw
  have hs_two : s * ‖u₁‖ ^ 2 + s * ‖u₁‖ ^ 2 = (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2 := by
    dsimp only [s]; ring
  have h1 := mul_le_mul_of_nonneg_right hpa hA₀
  have h2 := mul_le_mul_of_nonneg_right hpe hE₀
  have h3 := mul_le_mul_of_nonneg_right hng hG₀
  have h4 := mul_le_mul_of_nonneg_right hnu (sq_nonneg ‖u₀‖)
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u₀, u₁⟫| ≤
    (1 / 32 : ℝ) * E₀ + (1 / 4 : ℝ) * ‖u₀‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2
  linarith only [hraw, hs_two, h1, h2, h3, h4, hAU, hG_le, hE₀, sq_nonneg ‖u₀‖]


/-- Cross payment between a packet `u ∈ V_R ∩ (V_1)ᗮ` (`2 ≤ R ≤ R₁`) and a terminal-complement
vector `w ∈ (V_{R₁})ᗮ` at `M = N / linearDefectCutoff c`, spending a universal fraction of `w`'s
asymmetric two-region reserve (`s_w = k₁ / 32`, `t_w = γ_w = b * k₁ / (32 * c^7)`). -/
private theorem exists_band_terminal_cross_le {b : ℝ} (hb : 0 < b) :
    ∃ θ₁ C_cross_w : ℝ, 0 < θ₁ ∧ θ₁ ≤ 1 / 4096 ∧ 0 < C_cross_w ∧
      ∀ {R R₁ N : ℕ} {c : ℝ},
        2 ≤ R → R ≤ R₁ → R ^ 6 ≤ N → 18 * (1 + Real.log R) ≤ Real.log N →
        1 ≤ c → c ^ 2 ≤ Real.log N → c / N ≤ 1 / 3 →
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        1 + Real.log R₁ ≤ 2 * θ₁ * Real.log N →
        (θ₁ / (4 * explicitConductorCutoffConstant)) * Real.log N ≤
          Real.log R₁ / explicitConductorCutoffConstant - 1 →
        C_cross_w * (c ^ 7 * (1 + terminalPacketCost R (N / linearDefectCutoff c) N) / Real.log N +
          c ^ 9 * (1 + Real.log c) / Real.log N +
          c ^ 10 * (R : ℝ) ^ 2 / N) ≤ 1 →
      ∀ a : ℕ → ℝ,
        (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N) ∈
          (conductorSubspace 1 N)ᗮ →
      ∀ {w : EuclideanSpace ℝ (PrimeHorizonIndex N)}, w ∈ (conductorSubspace R₁ N)ᗮ →
        2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N), w⟫| ≤
          (1 / 32 : ℝ) * primeAdjunctionMass R a +
            (1 / 4 : ℝ) * ‖∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N‖ ^ 2 +
            ((Real.log R₁ / explicitConductorCutoffConstant - 1) / 32) *
              (∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2) +
            (b * (Real.log R₁ / explicitConductorCutoffConstant - 1) / (32 * c ^ 7)) *
              (∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2) +
            (b * (Real.log R₁ / explicitConductorCutoffConstant - 1) / (32 * c ^ 7)) * ‖w‖ ^ 2 := by
  obtain ⟨C_pr, C_np, hC_pr, hC_np, hcross⟩ := exists_completeWeil_cross_le_c9_split_reserves
  let D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  let θ₁ := min (1 / 4096) (1 / (131072 * C_pr * D + 1))
  have hθ₁ : 0 < θ₁ := lt_min (by norm_num) (by positivity)
  have hθ₁_4096 : θ₁ ≤ 1 / 4096 := min_le_left _ _
  have hθ₁_pr : 512 * C_pr * D * θ₁ ≤ 1 / 256 := by
    have hle : θ₁ ≤ 1 / (131072 * C_pr * D + 1) := min_le_right _ _
    have hpos : 0 < 131072 * C_pr * D + 1 := by positivity
    have hm := (le_div_iff₀ hpos).mp hle
    nlinarith only [hm, hθ₁]
  let K_fac := 256 * D + 256 * D / b + 256 * D / (b * θ₁) + 1
  have hK_fac : 0 < K_fac := by dsimp only [K_fac]; positivity
  let C_cross_w := 256 * (2 * C_pr + C_np + 1) * K_fac
  refine ⟨θ₁, C_cross_w, hθ₁, hθ₁_4096, by dsimp only [C_cross_w]; positivity, ?_⟩
  intro R R₁ N c hR hRR₁ hR6 hlog hc1 hc2L hw1 hsize_near hsize_up hH₁_ub hk₁_lb hsmall a hu_1 w hw_R₁
  let L := Real.log (N : ℝ)
  let M := N / linearDefectCutoff c
  let k₁ := Real.log (R₁ : ℝ) / D - 1
  let s_w := k₁ / 32
  let t_w := b * k₁ / (32 * c ^ 7)
  let u := ∑ m ∈ Icc 1 R, a m • normalizedRamanujanHorizonVector m N
  let H := 1 + Real.log (R : ℝ)
  let A := ∑ m ∈ Icc 1 R, a m ^ 2
  let E := primeAdjunctionMass R a
  let G := ∑ m ∈ Icc 1 R, (1 + Real.log m) * a m ^ 2
  let B := terminalPacketCost R M N
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hMN : M ≤ N := Nat.div_le_self N (linearDefectCutoff c)
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hL1 : 1 ≤ L := by dsimp only [L]; linarith only [hlog, Real.log_natCast_nonneg R]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by
    have hN2 : 2 ≤ N := by have hh := Nat.mul_le_mul hR hR; omega
    exact_mod_cast (show 0 < N by omega)
  have hk₁_pos : 0 < k₁ := (mul_pos (div_pos hθ₁ (by positivity)) hL0).trans_le hk₁_lb
  have hs_pos : 0 < s_w := by dsimp only [s_w]; positivity
  have ht_pos : 0 < t_w := by dsimp only [t_w]; positivity
  have hw_R : w ∈ (conductorSubspace R N)ᗮ := fun v hv =>
    hw_R₁ v (conductorSubspace_mono hRR₁ N hv)
  have hraw := hcross hR hR6 hMN hlog hc1 hw1 hsize_near hsize_up a hu_1 hw_R
    s_w t_w t_w hs_pos ht_pos ht_pos
  have hH_ub : H ≤ 2 * θ₁ * L := by
    have hlogR : Real.log (R : ℝ) ≤ Real.log (R₁ : ℝ) :=
      Real.log_le_log (by exact_mod_cast (show 0 < R by omega)) (by exact_mod_cast hRR₁)
    dsimp only [H, L] at hH₁_ub ⊢
    linarith only [hlogR, hH₁_ub]
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity
  have hB0 : 0 ≤ B := terminalPacketCost_nonneg R hMN
  have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
  have hA0 : 0 ≤ A := sum_nonneg fun _ _ => sq_nonneg _
  have hE0 : 0 ≤ E := primeAdjunctionMass_nonneg R a
  have hG0 : 0 ≤ G := sum_nonneg fun m _ => by have := Real.log_natCast_nonneg m; positivity
  have hAU : A ≤ 2 * ‖u‖ ^ 2 := by
    have hh := (half_and_three_halves_riesz_of_log_le hR hRR hlog a).1
    linarith only [hh]
  have hG_le : G ≤ 2 * ‖u‖ ^ 2 + E := by
    have hGE : G ≤ A + E := by
      dsimp only [G, A, E, primeAdjunctionMass]
      rw [← sum_add_distrib]
      refine sum_le_sum fun m _ => ?_
      nlinarith only [mul_nonneg (tameDifferent_nonneg m) (sq_nonneg (a m))]
    linarith only [hGE, hAU]
  let e := c ^ 7 * (1 + B) / L + c ^ 9 * (1 + Real.log c) / L + c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ)
  have he_small : (2 * C_pr + C_np + 1) * K_fac * e ≤ 1 / 256 := by
    dsimp only [C_cross_w, L, M, B] at hsmall
    change 256 * (2 * C_pr + C_np + 1) * K_fac * e ≤ 1 at hsmall
    linarith only [hsmall]
  have hc7_ge1 : (1 : ℝ) ≤ c ^ 7 := one_le_pow₀ hc1
  have he_B : c ^ 7 * (1 + B) / L ≤ e := by
    have hh : 0 ≤ c ^ 9 * (1 + Real.log c) / L + c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ) := by positivity
    dsimp only [e]; linarith only [hh]
  have he_1L : 1 / L ≤ e := by
    have h1 : 1 / L ≤ c ^ 7 * (1 + B) / L :=
      div_le_div_of_nonneg_right (by nlinarith only [hc7_ge1, mul_nonneg (pow_nonneg hc0.le 7) hB0])
        hL0.le
    exact h1.trans he_B
  have he_c7 : c ^ 7 / L ≤ e := by
    have h1 : c ^ 7 / L ≤ c ^ 7 * (1 + B) / L :=
      div_le_div_of_nonneg_right (by nlinarith only [mul_nonneg (pow_nonneg hc0.le 7) hB0]) hL0.le
    exact h1.trans he_B
  have he_c7B : c ^ 7 * B / L ≤ e := by
    have h1 : c ^ 7 * B / L ≤ c ^ 7 * (1 + B) / L :=
      div_le_div_of_nonneg_right (by nlinarith only [pow_nonneg hc0.le 7]) hL0.le
    exact h1.trans he_B
  have he_c9 : c ^ 9 * (1 + Real.log c) / L ≤ e := by
    have hh : 0 ≤ c ^ 7 * (1 + B) / L + c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ) := by positivity
    dsimp only [e]; linarith only [hh]
  have he_c10 : c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ) ≤ e := by
    have hh : 0 ≤ c ^ 7 * (1 + B) / L + c ^ 9 * (1 + Real.log c) / L := by positivity
    dsimp only [e]; linarith only [hh]
  have he0 : 0 ≤ e := le_trans (by positivity) he_1L
  have hs_lb : (θ₁ / (128 * D)) * L ≤ s_w := by
    dsimp only [s_w]
    have hh := div_le_div_of_nonneg_right hk₁_lb (by norm_num : (0 : ℝ) ≤ 32)
    exact (by ring : (θ₁ / (128 * D)) * L = ((θ₁ / (4 * D)) * L) / 32).trans_le hh
  have ht_lb : (b * θ₁ / (128 * D)) * (L / c ^ 7) ≤ t_w := by
    dsimp only [t_w]
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hk₁_lb hb.le)
      (by positivity : 0 ≤ 32 * c ^ 7)
    refine (?_ : (b * θ₁ / (128 * D)) * (L / c ^ 7) =
        b * ((θ₁ / (4 * D)) * L) / (32 * c ^ 7)).trans_le hh
    field_simp [hD.ne', hc0.ne']; ring
  have hs_lb_pos : 0 < (θ₁ / (128 * D)) * L := by positivity
  have ht_lb_pos : 0 < (b * θ₁ / (128 * D)) * (L / c ^ 7) := by positivity
  -- Bound the six u-side ratios.
  have hr_Hs : H / (L * s_w) ≤ K_fac * e := by
    calc
      H / (L * s_w) ≤ (2 * θ₁ * L) / (L * ((θ₁ / (128 * D)) * L)) :=
        (div_le_div_of_nonneg_right hH_ub (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left hs_lb hL0.le))
      _ = 256 * D * (1 / L) := by field_simp [hL0.ne', hθ₁.ne', hD.ne']; ring
      _ ≤ 256 * D * e := mul_le_mul_of_nonneg_left he_1L (by positivity)
      _ ≤ K_fac * e := mul_le_mul_of_nonneg_right
        (by dsimp only [K_fac]; have : 0 ≤ 256 * D / b + 256 * D / (b * θ₁) + 1 := by positivity
            linarith only [this]) he0
  have hr_Ht : H / (L * t_w) ≤ K_fac * e := by
    calc
      H / (L * t_w) ≤ (2 * θ₁ * L) / (L * ((b * θ₁ / (128 * D)) * (L / c ^ 7))) :=
        (div_le_div_of_nonneg_right hH_ub (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left ht_lb hL0.le))
      _ = (256 * D / b) * (c ^ 7 / L) := by
        field_simp [hL0.ne', hθ₁.ne', hD.ne', hb.ne', hc0.ne']; ring
      _ ≤ (256 * D / b) * e := mul_le_mul_of_nonneg_left he_c7 (by positivity)
      _ ≤ K_fac * e := mul_le_mul_of_nonneg_right
        (by dsimp only [K_fac]; have : 0 ≤ 256 * D + 256 * D / (b * θ₁) + 1 := by positivity
            linarith only [this]) he0
  have hr_H2s : C_pr * (H ^ 2 / (L * s_w)) ≤ 1 / 256 := by
    have hH2 : H ^ 2 ≤ (2 * θ₁ * L) ^ 2 := pow_le_pow_left₀ hH0 hH_ub 2
    have hdiv : H ^ 2 / (L * s_w) ≤ 512 * D * θ₁ := by
      calc
        H ^ 2 / (L * s_w) ≤ (2 * θ₁ * L) ^ 2 / (L * ((θ₁ / (128 * D)) * L)) :=
          (div_le_div_of_nonneg_right hH2 (by positivity)).trans
            (div_le_div_of_nonneg_left (by positivity) (by positivity)
              (mul_le_mul_of_nonneg_left hs_lb hL0.le))
        _ = 512 * D * θ₁ := by field_simp [hL0.ne', hθ₁.ne', hD.ne']; ring
    exact (mul_le_mul_of_nonneg_left hdiv hC_pr.le).trans
      ((by ring : C_pr * (512 * D * θ₁) = 512 * C_pr * D * θ₁).trans_le hθ₁_pr)
  have hr_HBt : H * B / (L * t_w) ≤ K_fac * e := by
    have hHB : H * B ≤ 2 * θ₁ * L * B := mul_le_mul_of_nonneg_right hH_ub hB0
    calc
      H * B / (L * t_w) ≤ (2 * θ₁ * L * B) / (L * ((b * θ₁ / (128 * D)) * (L / c ^ 7))) :=
        (div_le_div_of_nonneg_right hHB (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left ht_lb hL0.le))
      _ = (256 * D / b) * (c ^ 7 * B / L) := by
        field_simp [hL0.ne', hθ₁.ne', hD.ne', hb.ne', hc0.ne']; ring
      _ ≤ (256 * D / b) * e := mul_le_mul_of_nonneg_left he_c7B (by positivity)
      _ ≤ K_fac * e := mul_le_mul_of_nonneg_right
        (by dsimp only [K_fac]; have : 0 ≤ 256 * D + 256 * D / (b * θ₁) + 1 := by positivity
            linarith only [this]) he0
  have hr_Gt : (c ^ 2 * H * (1 + Real.log c) / L) / t_w ≤ K_fac * e := by
    have hnum : c ^ 2 * H * (1 + Real.log c) ≤ c ^ 2 * (2 * θ₁ * L) * (1 + Real.log c) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH_ub (sq_nonneg c)) (by positivity)
    calc
      (c ^ 2 * H * (1 + Real.log c) / L) / t_w ≤
          (c ^ 2 * (2 * θ₁ * L) * (1 + Real.log c) / L) /
            ((b * θ₁ / (128 * D)) * (L / c ^ 7)) :=
        (div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hnum hL0.le) ht_pos.le).trans
          (div_le_div_of_nonneg_left (by positivity) ht_lb_pos ht_lb)
      _ = (256 * D / b) * (c ^ 9 * (1 + Real.log c) / L) := by
        field_simp [hL0.ne', hθ₁.ne', hD.ne', hb.ne', hc0.ne']; ring
      _ ≤ (256 * D / b) * e := mul_le_mul_of_nonneg_left he_c9 (by positivity)
      _ ≤ K_fac * e := mul_le_mul_of_nonneg_right
        (by dsimp only [K_fac]; have : 0 ≤ 256 * D + 256 * D / (b * θ₁) + 1 := by positivity
            linarith only [this]) he0
  have hr_Ut :
      (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) / t_w ≤ K_fac * e := by
    have hc4_le : c ^ 4 * (1 + Real.log c) / L ≤ c ^ 2 * (1 + Real.log c) := by
      rw [div_le_iff₀ hL0]
      have hm := mul_le_mul_of_nonneg_left hc2L (show 0 ≤ c ^ 2 * (1 + Real.log c) by positivity)
      linarith only [hm, (by ring : c ^ 4 * (1 + Real.log c) =
        c ^ 2 * (1 + Real.log c) * c ^ 2)]
    have hnum : c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
        c ^ 2 * (1 + Real.log c) ≤
        2 * c ^ 2 * (1 + Real.log c) + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) := by
      linarith only [hc4_le]
    calc
      _ ≤ (2 * c ^ 2 * (1 + Real.log c) + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ))) /
            ((b * θ₁ / (128 * D)) * (L / c ^ 7)) :=
        (div_le_div_of_nonneg_right hnum ht_pos.le).trans
          (div_le_div_of_nonneg_left (by positivity) ht_lb_pos ht_lb)
      _ = (256 * D / (b * θ₁)) * (c ^ 9 * (1 + Real.log c) / L) +
            (128 * D / (b * θ₁)) * (c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ)) := by
        field_simp [hL0.ne', hθ₁.ne', hD.ne', hb.ne', hc0.ne', hN0.ne']; ring
      _ ≤ (256 * D / (b * θ₁)) * e := by
        have h128 : 0 ≤ 128 * D / (b * θ₁) := by positivity
        have hc90 : 0 ≤ c ^ 9 * (1 + Real.log c) / L := by positivity
        have hc100 : 0 ≤ c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ) := by positivity
        have hsum : c ^ 9 * (1 + Real.log c) / L + c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ) ≤ e := by
          dsimp only [e]
          have : 0 ≤ c ^ 7 * (1 + B) / L := by positivity
          linarith only [this]
        have hm := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 256 * D / (b * θ₁) by positivity)
        have hdrop : (128 * D / (b * θ₁)) * (c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ)) ≤
            (256 * D / (b * θ₁)) * (c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ)) := by
          have hd : 128 * D / (b * θ₁) ≤ 256 * D / (b * θ₁) :=
            div_le_div_of_nonneg_right (by linarith only [hD]) (by positivity)
          exact mul_le_mul_of_nonneg_right hd hc100
        linarith only [hm, hdrop]
      _ ≤ K_fac * e := mul_le_mul_of_nonneg_right
        (by dsimp only [K_fac]; have : 0 ≤ 256 * D + 256 * D / b + 1 := by positivity
            linarith only [this]) he0
  have hKe0 : 0 ≤ K_fac * e := mul_nonneg hK_fac.le he0
  have hpa : C_pr * (H / (L * s_w)) + C_pr * (H / (L * t_w)) ≤ 1 / 128 := by
    have h1 := mul_le_mul_of_nonneg_left hr_Hs hC_pr.le
    have h2 := mul_le_mul_of_nonneg_left hr_Ht hC_pr.le
    nlinarith only [h1, h2, he_small, mul_nonneg hC_np.le hKe0, hKe0]
  have hpe : C_pr * (H ^ 2 / (L * s_w)) + C_pr * (H * B / (L * t_w)) ≤ 1 / 128 := by
    have h2 := mul_le_mul_of_nonneg_left hr_HBt hC_pr.le
    have h2' : C_pr * (H * B / (L * t_w)) ≤ 1 / 256 := by
      nlinarith only [h2, he_small, mul_nonneg hC_pr.le hKe0, mul_nonneg hC_np.le hKe0, hKe0]
    linarith only [hr_H2s, h2']
  have hng : C_np * ((c ^ 2 * H * (1 + Real.log c) / L) / t_w) ≤ 1 / 128 := by
    have h1 := mul_le_mul_of_nonneg_left hr_Gt hC_np.le
    nlinarith only [h1, he_small, mul_nonneg hC_pr.le hKe0, hKe0]
  have hnu :
      C_np * ((c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
        c ^ 2 * (1 + Real.log c)) / t_w) ≤ 1 / 16 := by
    have h1 := mul_le_mul_of_nonneg_left hr_Ut hC_np.le
    nlinarith only [h1, he_small, mul_nonneg hC_pr.le hKe0, hKe0]
  have hfact :
      C_pr * (H * A + H ^ 2 * E) / (L * s_w) +
        C_pr * (H * A + H * B * E) / (L * t_w) +
        C_np * ((c ^ 2 * H * (1 + Real.log c) / L) * G +
          (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
            c ^ 2 * (1 + Real.log c)) * ‖u‖ ^ 2) / t_w =
      (C_pr * (H / (L * s_w)) + C_pr * (H / (L * t_w))) * A +
        (C_pr * (H ^ 2 / (L * s_w)) + C_pr * (H * B / (L * t_w))) * E +
        (C_np * ((c ^ 2 * H * (1 + Real.log c) / L) / t_w)) * G +
        (C_np * ((c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) / t_w)) * ‖u‖ ^ 2 := by ring
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤
    C_pr * (H * A + H ^ 2 * E) / (L * s_w) +
      C_pr * (H * A + H * B * E) / (L * t_w) +
      C_np * ((c ^ 2 * H * (1 + Real.log c) / L) * G +
        (c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R : ℝ) ^ 2 * (L / (N : ℝ)) +
          c ^ 2 * (1 + Real.log c)) * ‖u‖ ^ 2) / t_w +
      s_w * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
      t_w * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) + t_w * ‖w‖ ^ 2 at hraw
  rw [hfact] at hraw
  have h1 := mul_le_mul_of_nonneg_right hpa hA0
  have h2 := mul_le_mul_of_nonneg_right hpe hE0
  have h3 := mul_le_mul_of_nonneg_right hng hG0
  have h4 := mul_le_mul_of_nonneg_right hnu (sq_nonneg ‖u‖)
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| ≤
    (1 / 32 : ℝ) * E + (1 / 4 : ℝ) * ‖u‖ ^ 2 +
      s_w * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) +
      t_w * (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2) + t_w * ‖w‖ ^ 2
  linarith only [hraw, h1, h2, h3, h4, hAU, hG_le, hE0, sq_nonneg ‖u‖]

/-! ### 4. Homogeneous `O(c^2 (1 + log c))` coercivity on Band 1 (`V_{R₁} ∩ (V_{R₀})ᗮ`) -/

/-- On `conductorSubspace R₁ N ∩ (conductorSubspace R₀ N)ᗮ` at polynomial scale
`1080 * (1 + log R₁) ≤ log N`, all non-prime quadratic terms are `O(c^2 (1 + log c)) * ‖u₁‖^2`,
which is subdominant to `(1 / 4) * log R₀ ~ (log N)^(1/2)` throughout `1 ≤ c ≤ (log N)^α`
(`α < 1 / 4`). -/
private theorem exists_band1_coercive_homogeneous :
    ∃ C_band1 : ℝ, 0 < C_band1 ∧
      ∀ {R₀ R₁ N : ℕ} {c : ℝ},
        2 ≤ R₀ → R₀ ≤ R₁ → R₁ ^ 6 ≤ N → 1080 * (1 + Real.log R₁) ≤ Real.log N →
        1 ≤ c → c ≤ Real.log N → c / N ≤ 1 / 3 →
        ((R₁ * R₁ : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        (R₁ : ℝ) * Real.sqrt (Real.log N / N) ≤ 1 →
      ∀ a₁ : ℕ → ℝ,
        (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) ∈
          (conductorSubspace R₀ N)ᗮ →
        (1 / 8 : ℝ) * primeAdjunctionMass R₁ a₁ +
          ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * c ^ 2 * (1 + Real.log c)) *
            ‖∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N
          (∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N) := by
  obtain ⟨C_od, hC_od, hod⟩ := exists_overlap_sub_downward_inner_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  obtain ⟨C_ov, hC_ov, hov⟩ := exists_overlapMatrix_inner_le_of_mem_conductorSubspace
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
  let C_sep' := 36 * (152 * (∫ t, |tiltedUnitSpline t|) ^ 2 / (∫ t, tiltedUnitSpline t ^ 2))
  have hC_sep'0 : 0 ≤ C_sep' := by
    have := integral_tiltedUnitSpline_sq_pos; dsimp only [C_sep']; positivity
  let C_self := |completeWeilSelfFinitePart tiltedUnitSpline 1| +
    |Real.eulerMascheroniConstant| + 2
  let C_band1 := (Real.log 4 + 4) + C_self + 600 + C_sep' + 4 * C_od + C_ov
  have hC_band1 : 0 < C_band1 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    dsimp only [C_band1, C_self]; positivity
  refine ⟨C_band1, hC_band1, ?_⟩
  intro R₀ R₁ N c hR₀ hR₀R₁ hR₁6 hlog1080 hc1 hcL hw1 hsize hR₁_tail a₁ hu₁_R₀
  let u₁ := ∑ m ∈ Icc 1 R₁, a₁ m • normalizedRamanujanHorizonVector m N
  have hR₁ : 2 ≤ R₁ := hR₀.trans hR₀R₁
  have hRR₁ : R₁ * R₁ ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R₁) (by norm_num : 2 ≤ 6)).trans hR₁6
    simpa only [sq] using hh
  have hR₁4 : R₁ ^ 4 ≤ N :=
    (Nat.pow_le_pow_right (by omega : 0 < R₁) (by norm_num : 4 ≤ 6)).trans hR₁6
  have hN2 : 2 ≤ N := by have hh := Nat.mul_le_mul hR₁ hR₁; omega
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlogR₁ : 0 ≤ Real.log R₁ := Real.log_natCast_nonneg R₁
  have h18 : 18 * (1 + Real.log R₁) ≤ Real.log N := by linarith only [hlog1080, hlogR₁]
  have hL1 : 1 ≤ Real.log N := by linarith only [hlog1080, hlogR₁]
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL1
  by_cases hu0 : u₁ = 0
  · have hE0 : primeAdjunctionMass R₁ a₁ = 0 := by
      have hr := (half_and_three_halves_riesz_of_log_le hR₁ hRR₁ h18 a₁).1
      change (1 / 2 : ℝ) * (∑ m ∈ Icc 1 R₁, a₁ m ^ 2) ≤ ‖u₁‖ ^ 2 at hr
      rw [hu0, norm_zero, sq, mul_zero] at hr
      have hsum_nonneg : 0 ≤ ∑ m ∈ Icc 1 R₁, a₁ m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
      have hsum0 : (∑ m ∈ Icc 1 R₁, a₁ m ^ 2) = 0 := by linarith only [hr, hsum_nonneg]
      have ha0 : ∀ m ∈ Icc 1 R₁, a₁ m ^ 2 = 0 := fun m hm =>
        (sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (a₁ k)).mp hsum0 m hm
      unfold primeAdjunctionMass
      exact sum_eq_zero fun m hm => by rw [ha0 m hm, mul_zero]
    change (1 / 8 : ℝ) * primeAdjunctionMass R₁ a₁ +
        ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * c ^ 2 * (1 + Real.log c)) * ‖u₁‖ ^ 2 ≤
      completeWeilEnergy tiltedUnitSpline c N u₁
    rw [hE0, hu0, norm_zero]
    unfold completeWeilEnergy
    rw [map_zero, inner_zero_right]
    have hz0 : (1 / 8 : ℝ) * 0 +
        ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * c ^ 2 * (1 + Real.log c)) * (0 : ℝ) ^ 2 = 0 := by
      ring
    linarith only [hz0]
  · have hunorm_pos : 0 < ‖u₁‖ := norm_pos_iff.mpr hu0
    let s := ‖u₁‖⁻¹
    have hs_pos : 0 < s := inv_pos.mpr hunorm_pos
    let a' : ℕ → ℝ := fun m => s * a₁ m
    let u' := ∑ m ∈ Icc 1 R₁, a' m • normalizedRamanujanHorizonVector m N
    have hu'_eq : u' = s • u₁ := by
      dsimp only [u', u₁, a']
      rw [Finset.smul_sum]
      exact sum_congr rfl fun m _ => (smul_smul s (a₁ m) _).symm
    have hu'_unit : ‖u'‖ = 1 := by
      rw [hu'_eq, norm_smul, Real.norm_eq_abs, abs_of_pos hs_pos]
      exact inv_mul_cancel₀ hunorm_pos.ne'
    have hu'_sq : ‖u'‖ ^ 2 = 1 := by rw [hu'_unit, one_pow]
    have hu'_lo : 3 / 4 ≤ ‖u'‖ ^ 2 := by rw [hu'_sq]; norm_num
    have hu'_hi : ‖u'‖ ≤ 1 := hu'_unit.le
    have hu'_R₀ : u' ∈ (conductorSubspace R₀ N)ᗮ := by
      rw [hu'_eq]; exact Submodule.smul_mem _ s hu₁_R₀
    have hu'_1 : u' ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
      hu'_R₀ v (conductorSubspace_mono (by omega : 1 ≤ R₀) N hv)
    have hu'_mem : u' ∈ conductorSubspace R₁ N :=
      sum_normalizedRamanujanHorizonVector_mem_conductorSubspace R₁ N a'
    have hc0 : 0 < c := zero_lt_one.trans_le hc1
    have hcN : c ≤ N := by have := (div_le_iff₀ hN0).mp hw1; linarith only [this, hc0]
    have hlc0 : 0 ≤ Real.log c := Real.log_nonneg hc1
    have hc2_ge1 : 1 ≤ c ^ 2 := one_le_pow₀ hc1
    have hc2_ge_c : c ≤ c ^ 2 := by nlinarith only [hc1]
    let Q_c := c ^ 2 * (1 + Real.log c)
    have hQc_ge1 : 1 ≤ Q_c := by dsimp only [Q_c]; nlinarith only [hc2_ge1, hlc0]
    have hratio_le1 : (1 + Real.log R₁) / Real.log N ≤ 1 :=
      (div_le_one hL0).mpr (by linarith only [hlog1080, hlogR₁])
    -- Prime energy lower bound on unit `u'`.
    have hprime := primePacket_energy_ge_adjunction_and_log_of_orthogonal
      hR₀ hR₀R₁ hRR₁ hlog1080 a' hu'_R₀ hu'_lo hu'_hi
    -- Self-energy term.
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
      calc
        |completeWeilSelfError tiltedUnitSpline c N| ≤ Real.exp (1 / 2) / 2 * (c / N) := h1
        _ ≤ (3 / 2) * (1 / 3) := mul_le_mul (by linarith only [he12]) hw1 (by positivity) (by norm_num)
        _ ≤ 1 := by norm_num
    have hself_lb :
        -C_self * Q_c ≤
          (completeWeilSelfFinitePart tiltedUnitSpline c - Real.eulerMascheroniConstant +
            completeWeilSelfError tiltedUnitSpline c N) * ‖u'‖ ^ 2 := by
      rw [hu'_sq, mul_one, hself_eq]
      have hlc_le : Real.log c ≤ Q_c := by dsimp only [Q_c]; nlinarith only [hc2_ge1, hlc0]
      have hconst_le : |completeWeilSelfFinitePart tiltedUnitSpline 1| +
          |Real.eulerMascheroniConstant| + 1 ≤ (C_self - 1) * Q_c := by
        dsimp only [C_self]
        have hpos : 0 ≤ |completeWeilSelfFinitePart tiltedUnitSpline 1| +
            |Real.eulerMascheroniConstant| + 1 := by positivity
        nlinarith only [hpos, hQc_ge1]
      linarith only [neg_abs_le (completeWeilSelfFinitePart tiltedUnitSpline 1),
        le_abs_self Real.eulerMascheroniConstant, (abs_le.mp hself_err).1, hlc_le, hconst_le]
    -- Center, separated cross, overlap-minus-downward, and overlap bounds.
    have hpole_le : |completeWeilPoleShift tiltedUnitSpline c| ≤ c := by
      rw [abs_of_nonneg (completeWeilPoleShift_nonneg tiltedUnitSpline hc0.le)]
      exact completeWeilPoleShift_le contDiff_tiltedUnitSpline.continuous
        tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc0.le
    have hcen :
        |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
            (completeWeilPoleShift tiltedUnitSpline c) N) u', u'⟫| ≤ 600 * Q_c := by
      have h1 := abs_fullWeilCenterMatrix_self_inner_le_of_mem_conductorSubspace
        (completeWeilPoleShift tiltedUnitSpline c) hR₁ hR₁4 h18 hu'_mem hu'_1
      rw [hu'_sq, mul_one] at h1
      have h2 : 600 * |completeWeilPoleShift tiltedUnitSpline c| * (1 + Real.log R₁) / Real.log N ≤
          600 * c * ((1 + Real.log R₁) / Real.log N) := by
        refine (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpole_le (by norm_num))
            (by positivity)) hL0.le).trans_eq (by ring)
      have h3 : 600 * c * ((1 + Real.log R₁) / Real.log N) ≤ 600 * Q_c := by
        dsimp only [Q_c]
        nlinarith only [hratio_le1, hc2_ge_c, hlc0, hc0]
      exact h1.trans (h2.trans h3)
    have hsep :
        |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u', u'⟫| ≤
          C_sep' * Q_c := by
      have h1 := abs_separatedCrossErrorMatrix_inner_le_of_mem_conductorSubspace
        contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
        hc0 hR₁ hR₁4 h18 hu'_mem
      rw [hu'_sq, mul_one] at h1
      have h2 : c ^ 2 / Real.log N ≤ Q_c := by
        have hd : c ^ 2 / Real.log N ≤ c ^ 2 := div_le_self (sq_nonneg c) hL1
        dsimp only [Q_c]
        nlinarith only [hd, hlc0, sq_nonneg c]
      exact h1.trans ((by ring : C_sep' * c ^ 2 / Real.log N = C_sep' * (c ^ 2 / Real.log N)).trans_le
        (mul_le_mul_of_nonneg_left h2 hC_sep'0))
    have hod' :
        2 * |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u' -
            downwardPrimeVector tiltedUnitSpline c N u', u'⟫| ≤ 4 * C_od * Q_c := by
      have h1 := hod hR₁ hRR₁ h18 hc1 hw1 hsize hu'_mem
      rw [hu'_sq, mul_one] at h1
      have hpart1 : c ^ 2 * (1 + Real.log R₁) * (1 + Real.log c) / Real.log N ≤ Q_c := by
        have heq : c ^ 2 * (1 + Real.log R₁) * (1 + Real.log c) / Real.log N =
            Q_c * ((1 + Real.log R₁) / Real.log N) := by dsimp only [Q_c]; ring
        rw [heq]
        exact mul_le_of_le_one_right (by positivity) hratio_le1
      have hpart2 : c ^ 2 * (R₁ : ℝ) * Real.sqrt (Real.log N / N) ≤ Q_c := by
        have hm := mul_le_mul_of_nonneg_left hR₁_tail (sq_nonneg c)
        have hm' : c ^ 2 * (R₁ : ℝ) * Real.sqrt (Real.log N / N) ≤ c ^ 2 := by
          linarith only [hm, (by ring : c ^ 2 * ((R₁ : ℝ) * Real.sqrt (Real.log N / N)) =
            c ^ 2 * (R₁ : ℝ) * Real.sqrt (Real.log N / N))]
        dsimp only [Q_c]
        nlinarith only [hm', hlc0, sq_nonneg c]
      have hsum : c ^ 2 * (1 + Real.log R₁) * (1 + Real.log c) / Real.log N +
          c ^ 2 * (R₁ : ℝ) * Real.sqrt (Real.log N / N) ≤ 2 * Q_c := by
        linarith only [hpart1, hpart2]
      exact (mul_le_mul_of_nonneg_left
        (h1.trans (mul_le_mul_of_nonneg_left hsum hC_od.le)) zero_le_two).trans_eq (by ring)
    have hov' :
        |⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u', u'⟫| ≤ C_ov * Q_c := by
      have h1 := hov hR₁ hR₁ h18 h18 hc1 hcL hw1 hsize hsize hu'_mem hu'_mem
      rw [hu'_unit, mul_one, mul_one] at h1
      have h2 : c * (1 + Real.log c) ≤ Q_c := by
        dsimp only [Q_c]; nlinarith only [hc2_ge_c, hlc0]
      exact h1.trans ((by ring : C_ov * c * (1 + Real.log c) = C_ov * (c * (1 + Real.log c))).trans_le
        (mul_le_mul_of_nonneg_left h2 hC_ov.le))
    -- Assemble decomposition on `u'`.
    have hpole0 := fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one
      tiltedUnitSpline c hN2 hu'_1 hu'_1
    have hdecomp := completeWeilMatrix_inner_eq_decomposition_at_every_overlap
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      hc0 hN1 u'
    rw [overlap_sub_nonRatio_inner_eq contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero
        integral_tiltedUnitSpline_sq_pos hc0 hN1 u', hpole0] at hdecomp
    change completeWeilEnergy tiltedUnitSpline c N u' =
      renormalizedPrimeEnergy N u' +
      (completeWeilSelfFinitePart tiltedUnitSpline c - Real.eulerMascheroniConstant +
        completeWeilSelfError tiltedUnitSpline c N) * ‖u'‖ ^ 2 +
      ⟪Matrix.toEuclideanLin
        (fullWeilCenterMatrix (completeWeilPoleShift tiltedUnitSpline c) N) u', u'⟫ -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix tiltedUnitSpline c N) u', u'⟫ + 0 +
      (-⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u', u'⟫ +
        2 * ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u' -
          downwardPrimeVector tiltedUnitSpline c N u', u'⟫) at hdecomp
    have hrow_le : Real.log 4 + 4 ≤ (Real.log 4 + 4) * Q_c := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
      nlinarith only [this, hQc_ge1]
    have hod_lb :
        -(4 * C_od * Q_c) ≤
          2 * ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u' -
            downwardPrimeVector tiltedUnitSpline c N u', u'⟫ := by
      linarith only [hod', neg_abs_le
        ⟪Matrix.toEuclideanLin (overlapMatrix tiltedUnitSpline c N) u' -
          downwardPrimeVector tiltedUnitSpline c N u', u'⟫]
    have hunit_ineq :
        (1 / 8 : ℝ) * primeAdjunctionMass R₁ a' +
          ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * Q_c) ≤
        completeWeilEnergy tiltedUnitSpline c N u' := by
      dsimp only [C_band1]
      linarith only [hdecomp, hprime, hrow_le, hself_lb,
        (abs_le.mp hcen).1, (abs_le.mp hsep).2, (abs_le.mp hov').2, hod_lb]
    have hmass_smul : primeAdjunctionMass R₁ a' = s ^ 2 * primeAdjunctionMass R₁ a₁ := by
      dsimp only [a']
      unfold primeAdjunctionMass
      rw [mul_sum]
      exact sum_congr rfl fun m _ => by ring
    have henergy_smul : completeWeilEnergy tiltedUnitSpline c N u' =
        s ^ 2 * completeWeilEnergy tiltedUnitSpline c N u₁ := by
      rw [hu'_eq]
      unfold completeWeilEnergy
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hmass_smul, henergy_smul] at hunit_ineq
    have hmul := mul_le_mul_of_nonneg_left hunit_ineq (sq_nonneg ‖u₁‖)
    have hsu : ‖u₁‖ ^ 2 * s ^ 2 = 1 := by
      dsimp only [s]
      rw [← mul_pow, mul_inv_cancel₀ hunorm_pos.ne', one_pow]
    have hlhs :
        ‖u₁‖ ^ 2 * ((1 / 8 : ℝ) * (s ^ 2 * primeAdjunctionMass R₁ a₁) +
          ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * Q_c)) =
        (1 / 8 : ℝ) * ((‖u₁‖ ^ 2 * s ^ 2) * primeAdjunctionMass R₁ a₁) +
          ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * c ^ 2 * (1 + Real.log c)) * ‖u₁‖ ^ 2 := by
      dsimp only [Q_c]; ring
    have hrhs :
        ‖u₁‖ ^ 2 * (s ^ 2 * completeWeilEnergy tiltedUnitSpline c N u₁) =
          (‖u₁‖ ^ 2 * s ^ 2) * completeWeilEnergy tiltedUnitSpline c N u₁ := by ring
    rw [hlhs, hrhs, hsu, one_mul, one_mul] at hmul
    exact hmul

/-! ### 5. Four-band cutoff ordering and complement coercivity below `1 / 9` -/

private theorem eventually_three_cutoff_bounds_one_ninth {q θ₁ : ℝ}
    (hq : 0 < q) (hqmax : q ≤ 1 / 2) (hθ₁ : 0 < θ₁) (hθ₁_4096 : θ₁ ≤ 1 / 4096) :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (N : ℝ)
      let Q₁ := ⌊L ^ q⌋₊
      let R₀ := ⌊Real.exp (L ^ (1 / 2 : ℝ))⌋₊
      let R₁ := ⌊(N : ℝ) ^ θ₁⌋₊
      2 ≤ Q₁ ∧ Q₁ ≤ R₀ ∧ R₀ ≤ R₁ ∧
      (Q₁ : ℝ) ≤ L ^ q ∧
      (1 / 2 : ℝ) * L ^ (q / 2) ≤ Real.sqrt Q₁ ∧
      q * Real.log L - 1 ≤ Real.log (Q₁ : ℝ) ∧
      1 + Real.log (R₀ : ℝ) ≤ 2 * L ^ (1 / 2 : ℝ) ∧
      L ^ (1 / 2 : ℝ) - 1 ≤ Real.log (R₀ : ℝ) ∧
      36 * (1 + Real.log (R₀ : ℝ)) ≤ L ∧
      1 + Real.log (R₁ : ℝ) ≤ 2 * θ₁ * L ∧
      1080 * (1 + Real.log (R₁ : ℝ)) ≤ L ∧
      (θ₁ / (4 * explicitConductorCutoffConstant)) * L ≤
        Real.log (R₁ : ℝ) / explicitConductorCutoffConstant - 1 := by
  let D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hQlim : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ q) atTop atTop :=
    (tendsto_rpow_atTop hq).comp hLlim
  have hLhlim : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp hLlim
  have hNθlim : Tendsto (fun N : ℕ => (N : ℝ) ^ θ₁) atTop atTop :=
    (tendsto_rpow_atTop hθ₁).comp tendsto_natCast_atTop_atTop
  let M_Lh := max 72 (1 / θ₁ + 1)
  let M_L := max 2000 (max (2 / θ₁) (4 * D / θ₁))
  filter_upwards [hQlim.eventually_ge_atTop 4,
    hLhlim.eventually_ge_atTop M_Lh,
    hLlim.eventually_ge_atTop M_L,
    hNθlim.eventually_ge_atTop 4,
    eventually_ge_atTop 3] with N hQ4 hLh_M hL_M hNθ4 hN3
  dsimp only
  let L := Real.log (N : ℝ)
  let Lh := L ^ (1 / 2 : ℝ)
  let Q₁ := ⌊L ^ q⌋₊
  let R₀ := ⌊Real.exp Lh⌋₊
  let R₁ := ⌊(N : ℝ) ^ θ₁⌋₊
  have hL2000 : 2000 ≤ L := (le_max_left _ _).trans hL_M
  have hL_2θ : 2 / θ₁ ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL_M
  have hL_4Dθ : 4 * D / θ₁ ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL_M
  have hLh72 : 72 ≤ Lh := (le_max_left _ _).trans hLh_M
  have hLh_θ : 1 / θ₁ + 1 ≤ Lh := (le_max_right _ _).trans hLh_M
  have hL1 : 1 ≤ L := by linarith only [hL2000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLh0 : 0 < Lh := by linarith only [hLh72]
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1R
  have hLh_sq : Lh * Lh = L := by
    dsimp only [Lh]; rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
  have hlog2 : Real.log 2 ≤ 1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  -- Q₁ bounds.
  have hQ2 : 2 ≤ Q₁ := Nat.le_floor (by exact_mod_cast (show (2 : ℝ) ≤ L ^ q by linarith only [hQ4]))
  have hQ_le : (Q₁ : ℝ) ≤ L ^ q := Nat.floor_le (by linarith only [hQ4])
  have hQ_gt : L ^ q - 1 < (Q₁ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
  have hQ_quarter : (1 / 4 : ℝ) * L ^ q ≤ (Q₁ : ℝ) := by linarith only [hQ4, hQ_gt]
  have hQ_half : (1 / 2 : ℝ) * L ^ q ≤ (Q₁ : ℝ) := by linarith only [hQ4, hQ_gt]
  have hsqrtQ : (1 / 2 : ℝ) * L ^ (q / 2) ≤ Real.sqrt Q₁ := by
    have hsq : ((1 / 2 : ℝ) * L ^ (q / 2)) ^ 2 = (1 / 4 : ℝ) * L ^ q := by
      rw [mul_pow, ← Real.rpow_natCast (L ^ (q / 2)) 2, ← Real.rpow_mul hL0.le]; norm_num
    have hpos : 0 ≤ (1 / 2 : ℝ) * L ^ (q / 2) := by positivity
    exact (Real.sqrt_sq hpos).symm.trans_le (Real.sqrt_le_sqrt (hsq.trans_le hQ_quarter))
  have hlogQ_lb : q * Real.log L - 1 ≤ Real.log (Q₁ : ℝ) := by
    have hXq_pos : 0 < L ^ q := by linarith only [hQ4]
    have h1 := Real.log_le_log (by positivity) hQ_half
    rw [Real.log_mul (by norm_num) hXq_pos.ne', one_div, Real.log_inv, Real.log_rpow hL0] at h1
    linarith only [h1, hlog2]
  -- Ordering Q₁ ≤ R₀ ≤ R₁.
  have hLq_exp : L ^ q ≤ Real.exp Lh := by
    have h1 : L ^ q ≤ Lh := Real.rpow_le_rpow_of_exponent_le hL1 hqmax
    have h2 : Lh ≤ Real.exp Lh := by linarith [Real.add_one_le_exp Lh]
    exact h1.trans h2
  have hQR₀ : Q₁ ≤ R₀ := Nat.floor_mono hLq_exp
  have hexp_Nθ : Real.exp Lh ≤ (N : ℝ) ^ θ₁ := by
    rw [Real.rpow_def_of_pos hN0]
    apply Real.exp_le_exp.mpr
    have h1 : 1 ≤ θ₁ * Lh := by
      have hh := (div_le_iff₀ hθ₁).mp (show 1 / θ₁ ≤ Lh by linarith only [hLh_θ])
      linarith only [hh]
    have h2 := mul_le_mul_of_nonneg_left h1 hLh0.le
    calc
      Lh = Lh * 1 := (mul_one _).symm
      _ ≤ Lh * (θ₁ * Lh) := h2
      _ = (Lh * Lh) * θ₁ := by ring
      _ = Real.log (N : ℝ) * θ₁ := by rw [hLh_sq]
  have hR₀R₁ : R₀ ≤ R₁ := Nat.floor_mono hexp_Nθ
  -- R₀ bounds.
  have hR₀2 : 2 ≤ R₀ := hQ2.trans hQR₀
  have hR₀_le : (R₀ : ℝ) ≤ Real.exp Lh := Nat.floor_le (Real.exp_pos Lh).le
  have hlogR₀_ub : Real.log (R₀ : ℝ) ≤ Lh :=
    (Real.log_le_log (by exact_mod_cast (show 0 < R₀ by omega)) hR₀_le).trans_eq (Real.log_exp Lh)
  have hH₀_ub : 1 + Real.log (R₀ : ℝ) ≤ 2 * Lh := by linarith only [hlogR₀_ub, hLh72]
  have hexp_ge4 : 4 ≤ Real.exp Lh := by linarith [Real.add_one_le_exp Lh, hLh72]
  have hR₀_half : (1 / 2 : ℝ) * Real.exp Lh ≤ (R₀ : ℝ) := by
    have hgt : Real.exp Lh - 1 < (R₀ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    linarith only [hexp_ge4, hgt]
  have hlogR₀_lb : Lh - 1 ≤ Real.log (R₀ : ℝ) := by
    have h1 := Real.log_le_log (by positivity) hR₀_half
    rw [Real.log_mul (by norm_num) (Real.exp_pos Lh).ne', one_div, Real.log_inv, Real.log_exp] at h1
    linarith only [h1, hlog2]
  have h36_R₀ : 36 * (1 + Real.log (R₀ : ℝ)) ≤ L := by
    have h1 : 36 * (1 + Real.log (R₀ : ℝ)) ≤ 72 * Lh := by linarith only [hH₀_ub]
    have h2 : 72 * Lh ≤ Lh * Lh := mul_le_mul_of_nonneg_right hLh72 hLh0.le
    linarith only [h1, h2, hLh_sq]
  -- R₁ bounds.
  have hR₁2 : 2 ≤ R₁ := hR₀2.trans hR₀R₁
  have hR₁_le : (R₁ : ℝ) ≤ (N : ℝ) ^ θ₁ := Nat.floor_le (by positivity)
  have hlogR₁_ub : Real.log (R₁ : ℝ) ≤ θ₁ * L :=
    (Real.log_le_log (by exact_mod_cast (show 0 < R₁ by omega)) hR₁_le).trans_eq
      (Real.log_rpow hN0 θ₁)
  have h1_le_θL : 1 ≤ θ₁ * L := by
    have hh := (div_le_iff₀ hθ₁).mp hL_2θ; linarith only [hh]
  have hH₁_ub : 1 + Real.log (R₁ : ℝ) ≤ 2 * θ₁ * L := by linarith only [hlogR₁_ub, h1_le_θL]
  have h1080_R₁ : 1080 * (1 + Real.log (R₁ : ℝ)) ≤ L := by
    have h1 : 1080 * (1 + Real.log (R₁ : ℝ)) ≤ 2160 * θ₁ * L := by linarith only [hH₁_ub]
    have h2 : 2160 * θ₁ ≤ 1 := by linarith only [hθ₁_4096]
    have h3 : (2160 * θ₁) * L ≤ 1 * L := mul_le_mul_of_nonneg_right h2 hL0.le
    linarith only [h1, h3]
  have hR₁_half : (1 / 2 : ℝ) * (N : ℝ) ^ θ₁ ≤ (R₁ : ℝ) := by
    have hgt : (N : ℝ) ^ θ₁ - 1 < (R₁ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
    linarith only [hNθ4, hgt]
  have hlogR₁_lb : (θ₁ / 2) * L ≤ Real.log (R₁ : ℝ) := by
    have hpos : 0 < (N : ℝ) ^ θ₁ := by linarith only [hNθ4]
    have h1 := Real.log_le_log (by positivity) hR₁_half
    rw [Real.log_mul (by norm_num) hpos.ne', one_div, Real.log_inv, Real.log_rpow hN0] at h1
    have h2 : 2 ≤ θ₁ * L := by
      have hh := (div_le_iff₀ hθ₁).mp hL_2θ; linarith only [hh]
    linarith only [h1, hlog2, h2]
  have hk₁_lb : (θ₁ / (4 * D)) * L ≤ Real.log (R₁ : ℝ) / D - 1 := by
    have hdiv := div_le_div_of_nonneg_right hlogR₁_lb hD.le
    have h1 : (θ₁ / 2) * L / D = 2 * ((θ₁ / (4 * D)) * L) := by field_simp [hD.ne']; ring
    have h4D : 4 * D ≤ θ₁ * L := by
      have hh := (div_le_iff₀ hθ₁).mp hL_4Dθ; linarith only [hh]
    have h2 : 1 ≤ (θ₁ / (4 * D)) * L := by
      rw [div_mul_eq_mul_div, one_le_div (by positivity)]
      linarith only [h4D]
    linarith only [hdiv, h1, h2]
  exact ⟨hQ2, hQR₀, hR₀R₁, hQ_le, hsqrtQ, hlogQ_lb, hH₀_ub, hlogR₀_lb, h36_R₀,
    hH₁_ub, h1080_R₁, hk₁_lb⟩

/-- **Homogeneous complement coercivity on `(conductorSubspace Q₁ N)ᗮ` below `1 / 9`.**
For every `0 < α < 1 / 9` and every polylogarithmic exponent `3 * α < q ≤ 1 / 2`, eventually in `N`
and uniformly across `1 ≤ c ≤ (log N)^α`, every vector `z ∈ (conductorSubspace ⌊(log N)^q⌋₊ N)ᗮ`
satisfies `(tiltedSplineSpectralFloorConstant + 2) * ‖z‖^2 ≤ completeWeilEnergy tiltedUnitSpline c N z`. -/
theorem eventually_tiltedUnitSpline_complement_coercive_below_one_ninth
    {α q : ℝ} (hα : 0 < α) (hα_lt : α < oneNinthPowerLogExponent)
    (hq_lo : 3 * α < q) (hq_hi : q ≤ 1 / 2) :
    ∀ᶠ N : ℕ in atTop,
      let Q₁ := ⌊Real.log (N : ℝ) ^ q⌋₊
      ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
        ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)},
          z ∈ (conductorSubspace Q₁ N)ᗮ →
          (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 ≤
            completeWeilEnergy tiltedUnitSpline c N z := by
  have hα9 : α < 1 / 9 := hα_lt
  have hq : 0 < q := by linarith only [hα, hq_lo]
  obtain ⟨b, K_two, hb, hb8, hK_two, htwo_res⟩ :=
    exists_completeWeilEnergy_asymmetric_two_region_reserve
  obtain ⟨θ₁, C_cross_w, hθ₁, hθ₁_4096, hC_cross_w, hcross_w⟩ := exists_band_terminal_cross_le hb
  obtain ⟨C_cross01, hC_cross01, hcross01⟩ := exists_band0_band1_cross_le
  obtain ⟨C_coerc0, C_small0, hC_coerc0, hC_small0, hcoerc0⟩ :=
    exists_completeWeilEnergy_ge_three_quarters_log_homogeneous
  obtain ⟨C_band1, hC_band1, hcoerc1⟩ := exists_band1_coercive_homogeneous
  let D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  let κ₀ := tiltedSplineSpectralFloorConstant
  have hκ₀ : 0 < κ₀ := tiltedSplineSpectralFloorConstant_pos
  let Hlin : ℝ := 256 * Real.exp 2 + 4
  have hHlin_pos : 1 ≤ Hlin := by
    have := Real.exp_pos 2; dsimp only [Hlin]; linarith only [this]
  let CB : ℝ := 4 + Real.log (2 * Hlin) + 1
  have hCB_pos : 1 ≤ CB := by
    have := Real.log_nonneg (by linarith only [hHlin_pos] : (1 : ℝ) ≤ 2 * Hlin)
    dsimp only [CB]; linarith only [this]
  let δ := min (1 - 9 * α) (q / 2 - (3 / 2) * α)
  have hδ : 0 < δ := lt_min (by linarith only [hα9]) (by linarith only [hq_lo])
  let ν := δ / 16
  have hν : 0 < ν := by dsimp only [ν]; positivity
  have hgap_q : 0 < (3 / 4) * q - α := by linarith only [hα, hq_lo]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLlim
  let M_ν := max (C_small0 * 18 + 1)
    (max (C_cross01 * 4 + 1)
      (max (C_cross_w * (CB + 3) + 1)
        (max (4 * D * K_two / θ₁ + 1)
          (max (8 * CB / b + 1)
            (max (16 * C_band1 + 1)
              (32 * D * (κ₀ + 2) / (3 * b * θ₁) + 1))))))
  let M_ll := (κ₀ + 3 + C_coerc0 + 3 / 4) / ((3 / 4) * q - α)
  let M_L_floor := max 3000 (max ((16 * (κ₀ + 3)) ^ 2 + 1) (32 * D * (κ₀ + 2) / θ₁ + 1))
  filter_upwards [eventually_three_cutoff_bounds_one_ninth hq hq_hi hθ₁ hθ₁_4096,
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1 hν 1),
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop M_ν,
    hllim.eventually_ge_atTop M_ll,
    hLlim.eventually_ge_atTop M_L_floor,
    eventually_ge_atTop 3] with N hcut hLX hpoly hν_big hll_big hL_big hN3 c hc1 hcup z hz
  obtain ⟨hQ2, hQR₀, hR₀R₁, hQ_le, hsqrtQ, hlogQ_lb, hH₀_ub, hlogR₀_lb, h36_R₀,
    hH₁_ub, h1080_R₁, hk₁_lb⟩ := hcut
  let L := Real.log (N : ℝ)
  let Lh := L ^ (1 / 2 : ℝ)
  let Q₁ := ⌊L ^ q⌋₊
  let R₀ := ⌊Real.exp Lh⌋₊
  let R₁ := ⌊(N : ℝ) ^ θ₁⌋₊
  have hL3000 : 3000 ≤ L := (le_max_left _ _).trans hL_big
  have hL_Lh_gap : (16 * (κ₀ + 3)) ^ 2 + 1 ≤ L :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hL_big
  have hL_w_pre : 32 * D * (κ₀ + 2) / θ₁ + 1 ≤ L :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hL_big
  have hL2000 : 2000 ≤ L := by linarith only [hL3000]
  have hL1 : 1 ≤ L := by linarith only [hL3000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hLh1 : 1 ≤ Lh := Real.one_le_rpow hL1 (by norm_num)
  have hLh0 : 0 < Lh := zero_lt_one.trans_le hLh1
  have hLh_sq : Lh * Lh = L := by
    dsimp only [Lh]; rw [← Real.rpow_add hL0]; norm_num [Real.rpow_one]
  have hN1 : 1 ≤ N := by omega
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcL : c ≤ L := hcup.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα9] : α ≤ 1))
  have hcpow : ∀ j : ℕ, c ^ j ≤ L ^ ((j : ℝ) * α) := fun j => by
    have hp := pow_le_pow_left₀ hc0.le hcup j
    have he : (L ^ α) ^ j = L ^ ((j : ℝ) * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  have hc2L : c ^ 2 ≤ L := by
    calc
      c ^ 2 ≤ L ^ (((2 : ℕ) : ℝ) * α) := hcpow 2
      _ ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by push_cast; linarith only [hα9])
      _ = L := Real.rpow_one L
  have hpoly1 : 1 + Real.log L ≤ L ^ ν := by simpa only [one_mul, pow_one] using hpoly
  have hVc : 1 + Real.log c ≤ L ^ ν := by
    linarith only [Real.log_le_log hc0 hcL, hpoly1]
  have hmul_ν : L ^ ν * L ^ (-ν) = 1 := by
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  have hR₀2 : 2 ≤ R₀ := hQ2.trans hQR₀
  have hR₁2 : 2 ≤ R₁ := hR₀2.trans hR₀R₁
  have h36_R₁ : 36 * (1 + Real.log (R₁ : ℝ)) ≤ L := by
    have hh := Real.log_natCast_nonneg R₁; linarith only [h1080_R₁, hh]
  -- Horizon bounds at R₀ and R₁.
  obtain ⟨hcutN, -, hw1, hrad, hR₀6, hsize_near0, hsize_up0, hR₀_tail, hc5N, hc3R₀4, hc3R₀2, hc10R₀2⟩ :=
    rpow_horizon_N_bounds_one_ninth hN1 hR₀2 hc1 hL2000 hLX hcL h36_R₀
  obtain ⟨-, -, -, -, hR₁6, hsize_near1, hsize_up1, hR₁_tail, -, -, -, hc10R₁2⟩ :=
    rpow_horizon_N_bounds_one_ninth hN1 hR₁2 hc1 hL2000 hLX hcL h36_R₁
  obtain ⟨hRM0, -, hB0_ub, -⟩ :=
    linear_prefix_horizon_bounds_one_ninth hN1 hR₀2 hc1 hL3000 hLX hcL h36_R₀
  obtain ⟨hRM1, hlogM1, hB1_ub, hhalfM⟩ :=
    linear_prefix_horizon_bounds_one_ninth hN1 hR₁2 hc1 hL3000 hLX hcL h36_R₁
  -- Power-of-L decay helper: `L ^ β ≤ L ^ (-ν)` whenever `β ≤ -ν`.
  have hδ1 : δ ≤ 1 - 9 * α := min_le_left _ _
  have hδ2 : δ ≤ q / 2 - (3 / 2) * α := min_le_right _ _
  have hν_le_16 : 16 * ν = δ := by dsimp only [ν]; ring
  have h1_invL : 1 / L ≤ L ^ (-ν) := by
    rw [one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hδ1, hν_le_16, hα])
  have h1_invLh : 1 / Lh ≤ L ^ (-ν) := by
    have h1 : 1 / Lh = L ^ (-(1 / 2 : ℝ)) := by
      dsimp only [Lh]; rw [one_div, ← Real.rpow_neg hL0.le]
    rw [h1]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hδ1, hν_le_16, hα])
  have hν_bound_1 : C_small0 * 18 ≤ L ^ ν :=
    ((le_max_left _ _).trans hν_big).trans' (by linarith)
  have hν_bound_2 : C_cross01 * 4 ≤ L ^ ν :=
    (((le_max_left _ _).trans (le_max_right _ _)).trans hν_big).trans' (by linarith)
  have hν_bound_3 : C_cross_w * (CB + 3) ≤ L ^ ν :=
    (((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hν_big).trans'
      (by linarith)
  have hν_bound_4 : 4 * D * K_two / θ₁ ≤ L ^ ν :=
    (((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _)))).trans hν_big).trans' (by linarith)
  have hν_bound_5 : 8 * CB / b ≤ L ^ ν :=
    (((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _))))).trans hν_big).trans' (by linarith)
  have hν_bound_6 : 16 * C_band1 ≤ L ^ ν :=
    (((le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))).trans hν_big).trans'
        (by linarith)
  have hν_bound_7 : 32 * D * (κ₀ + 2) / (3 * b * θ₁) ≤ L ^ ν :=
    (((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))))).trans hν_big).trans'
        (by linarith)
  -- Orthogonal three-band split of `z ∈ (conductorSubspace Q₁ N)ᗮ`.
  obtain ⟨hz_eq, hu₀_mem, hu₀_orthQ, hu₁_mem, hu₁_orthR₀, hw_orthR₁, hnorm_split⟩ :=
    telescoped_three_band_orthogonal_split hQR₀ hR₀R₁ hz
  let u₀ := (conductorSubspace R₀ N).starProjection z
  let u₁ := (conductorSubspace R₁ N).starProjection z - (conductorSubspace R₀ N).starProjection z
  let w := z - (conductorSubspace R₁ N).starProjection z
  change z = u₀ + u₁ + w at hz_eq
  change ‖z‖ ^ 2 = ‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 + ‖w‖ ^ 2 at hnorm_split
  obtain ⟨a₀, -, ha₀⟩ := (mem_conductorSubspace_iff (M := R₀) (N := N) (x := u₀)).mp hu₀_mem
  obtain ⟨a₁, -, ha₁⟩ := (mem_conductorSubspace_iff (M := R₁) (N := N) (x := u₁)).mp hu₁_mem
  have hu₀_1 : u₀ ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu₀_orthQ v (conductorSubspace_mono (by omega : 1 ≤ Q₁) N hv)
  have hu₁_1 : u₁ ∈ (conductorSubspace 1 N)ᗮ := fun v hv =>
    hu₁_orthR₀ v (conductorSubspace_mono (by omega : 1 ≤ R₀) N hv)
  -- Smallness check 1: Band 0 coercivity (`hcoerc0` at `Q₁, R₀`).
  have hH₀_div : (1 + Real.log (R₀ : ℝ)) / L ≤ 2 / Lh := by
    rw [div_le_div_iff₀ hL0 hLh0]
    calc
      (1 + Real.log (R₀ : ℝ)) * Lh ≤ (2 * Lh) * Lh := mul_le_mul_of_nonneg_right hH₀_ub hLh0.le
      _ = 2 * (Lh * Lh) := by ring
      _ = 2 * L := by rw [hLh_sq]
  have hc2_vc_Lh : c ^ 2 * (1 + Real.log c) / Lh ≤ L ^ (-ν) := by
    have h1 : c ^ 2 * (1 + Real.log c) ≤ L ^ (2 * α + ν) := by
      calc
        c ^ 2 * (1 + Real.log c) ≤ L ^ (((2 : ℕ) : ℝ) * α) * L ^ ν :=
          mul_le_mul (hcpow 2) hVc (by linarith [Real.log_nonneg hc1]) (by positivity)
        _ = L ^ (2 * α + ν) := by rw [← Real.rpow_add hL0]; congr 1; push_cast; ring
    calc
      c ^ 2 * (1 + Real.log c) / Lh ≤ L ^ (2 * α + ν) / L ^ (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_right h1 hLh0.le
      _ = L ^ (2 * α + ν - 1 / 2) := by rw [← Real.rpow_sub hL0]
      _ ≤ L ^ (-ν) := Real.rpow_le_rpow_of_exponent_le hL1
        (by linarith only [hδ1, hν_le_16, hα])
  have hc2_vc_L : c ^ 2 * (1 + Real.log c) / L ≤ L ^ (-ν) := by
    have hd : c ^ 2 * (1 + Real.log c) / L ≤ c ^ 2 * (1 + Real.log c) / Lh :=
      div_le_div_of_nonneg_left (by linarith [Real.log_nonneg hc1]; positivity) hLh0
        (by nlinarith only [hLh1, hLh_sq])
    exact hd.trans hc2_vc_Lh
  have hmid_Q₁ : c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ ≤ 2 * L ^ (-ν) := by
    have hc32 : c * Real.sqrt c ≤ L ^ ((3 / 2 : ℝ) * α) := by
      have hsq : (c * Real.sqrt c) ^ 2 ≤ (L ^ ((3 / 2 : ℝ) * α)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hc0.le, ← pow_add, ← Real.rpow_natCast (L ^ _),
          ← Real.rpow_mul hL0.le]
        exact (hcpow 3).trans_eq (by congr 1; ring)
      have hp1 : 0 ≤ c * Real.sqrt c := by positivity
      have hp2 : 0 ≤ L ^ ((3 / 2 : ℝ) * α) := by positivity
      nlinarith only [hsq, hp1, hp2]
    calc
      c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ ≤
          (L ^ ((3 / 2 : ℝ) * α) * L ^ ν) / ((1 / 2 : ℝ) * L ^ (q / 2)) :=
        (div_le_div_of_nonneg_right
          (mul_le_mul hc32 hVc (by linarith [Real.log_nonneg hc1]) (by positivity))
          (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrtQ)
      _ = 2 * L ^ ((3 / 2 : ℝ) * α + ν - q / 2) := by
        rw [← Real.rpow_add hL0, ← Real.rpow_sub hL0]; ring
      _ ≤ 2 * L ^ (-ν) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hδ2, hν_le_16, hν])) zero_le_two
  have hsmall_band0 : C_small0 * (c * (1 + Real.log c) * (1 + Real.log R₀) / L +
      c * (1 + Real.log R₀) / L + c ^ 2 / L +
      c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
      c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
      c ^ 5 * L / N +
      c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
      c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L) ≤ 1 := by
    have hlc_ge1 : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
    have ht4 : c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L ≤ 2 * L ^ (-ν) := by
      calc
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L =
            c ^ 2 * (1 + Real.log c) * ((1 + Real.log R₀) / L) := by ring
        _ ≤ c ^ 2 * (1 + Real.log c) * (2 / Lh) :=
          mul_le_mul_of_nonneg_left hH₀_div (by positivity)
        _ = 2 * (c ^ 2 * (1 + Real.log c) / Lh) := by ring
        _ ≤ 2 * L ^ (-ν) := mul_le_mul_of_nonneg_left hc2_vc_Lh zero_le_two
    have ht1 : c * (1 + Real.log c) * (1 + Real.log R₀) / L ≤ 2 * L ^ (-ν) := by
      have hm : c * (1 + Real.log c) ≤ c ^ 2 * (1 + Real.log c) := by
        nlinarith only [hc1, hlc_ge1]
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hm (by linarith [Real.log_natCast_nonneg R₀])) hL0.le).trans
        ((by ring : c ^ 2 * (1 + Real.log c) * (1 + Real.log R₀) / L =
          c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L).trans_le ht4)
    have ht2 : c * (1 + Real.log R₀) / L ≤ 2 * L ^ (-ν) := by
      have hm : c * (1 + Real.log R₀) ≤ c * (1 + Real.log c) * (1 + Real.log R₀) := by
        have hH0 : 0 ≤ c * (1 + Real.log R₀) := by
          have := Real.log_natCast_nonneg R₀; positivity
        nlinarith only [hlc_ge1, hH0]
      exact (div_le_div_of_nonneg_right hm hL0.le).trans
        ((by ring : c * (1 + Real.log c) * (1 + Real.log R₀) / L =
          c * (1 + Real.log c) * (1 + Real.log R₀) / L).trans_le ht1)
    have ht3 : c ^ 2 / L ≤ L ^ (-ν) :=
      (div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg c) hlc_ge1) hL0.le).trans
        hc2_vc_L
    have ht5 : c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) ≤ L ^ (-ν) := by
      calc
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) = c ^ 2 * ((R₀ : ℝ) * Real.sqrt (L / N)) := by ring
        _ ≤ c ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hR₀_tail (sq_nonneg c)
        _ = c ^ 2 / L := by ring
        _ ≤ L ^ (-ν) := ht3
    have ht6 : c ^ 5 * L / N ≤ L ^ (-ν) := hc5N.trans h1_invL
    have ht8 : c ^ 3 * (R₀ : ℝ) ^ 4 / N ≤ L ^ (-ν) := hc3R₀4.trans h1_invL
    have hsum18 : c * (1 + Real.log c) * (1 + Real.log R₀) / L +
        c * (1 + Real.log R₀) / L + c ^ 2 / L +
        c ^ 2 * (1 + Real.log R₀) * (1 + Real.log c) / L +
        c ^ 2 * (R₀ : ℝ) * Real.sqrt (L / N) +
        c ^ 5 * L / N +
        c * Real.sqrt c * (1 + Real.log c) / Real.sqrt Q₁ +
        c ^ 3 * (R₀ : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L ≤ 18 * L ^ (-ν) := by
      have : 0 ≤ L ^ (-ν) := by positivity
      linarith only [ht1, ht2, ht3, ht4, ht5, ht6, hmid_Q₁, ht8, hc2_vc_L, this]
    calc
      _ ≤ C_small0 * (18 * L ^ (-ν)) := mul_le_mul_of_nonneg_left hsum18 hC_small0.le
      _ = (C_small0 * 18) * L ^ (-ν) := by ring
      _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_bound_1 (by positivity)
      _ = 1 := hmul_ν
  have hdiag0 := hcoerc0 hQ2 hQR₀ hR₀6 h36_R₀ hc1 hcL hw1 hrad hsize_near0 hsmall_band0
    a₀ (ha₀.symm ▸ hu₀_orthQ)
  rw [ha₀] at hdiag0
  -- Diagonal 1: Band 1 coercivity (`hcoerc1` at `R₀, R₁`).
  have hR₁_tail1 : (R₁ : ℝ) * Real.sqrt (L / N) ≤ 1 :=
    hR₁_tail.trans ((div_le_one hL0).mpr hL1)
  have hdiag1 := hcoerc1 hR₀2 hR₀R₁ hR₁6 h1080_R₁ hc1 hcL hw1 hsize_near1 hR₁_tail1
    a₁ (ha₁.symm ▸ hu₁_orthR₀)
  rw [ha₁] at hdiag1
  -- Diagonal 2: Terminal two-region reserve (`htwo_res` at `R₁`).
  have hc9_vc_L : c ^ 9 * (1 + Real.log c) / L ≤ L ^ (-ν) := by
    calc
      c ^ 9 * (1 + Real.log c) / L ≤ (L ^ (((9 : ℕ) : ℝ) * α) * L ^ ν) / L :=
        div_le_div_of_nonneg_right
          (mul_le_mul (hcpow 9) hVc (by linarith [Real.log_nonneg hc1]) (by positivity)) hL0.le
      _ = L ^ (9 * α + ν - 1) := by
        rw [← Real.rpow_add hL0, Real.rpow_sub hL0, Real.rpow_one]; congr 1; push_cast; ring
      _ ≤ L ^ (-ν) := Real.rpow_le_rpow_of_exponent_le hL1
        (by linarith only [hδ1, hν_le_16, hν])
  have hc9_L : c ^ 9 / L ≤ L ^ (-ν) := by
    have hlc1 : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
    exact (div_le_div_of_nonneg_right (le_mul_of_one_le_right (pow_nonneg hc0.le 9) hlc1) hL0.le).trans
      hc9_vc_L
  have hKc9_gap : K_two * c ^ 9 ≤ Real.log (R₁ : ℝ) / D - 1 := by
    have h1 : (4 * D * K_two / θ₁) * (c ^ 9 / L) ≤ 1 := by
      calc
        (4 * D * K_two / θ₁) * (c ^ 9 / L) ≤ L ^ ν * L ^ (-ν) :=
          mul_le_mul hν_bound_4 hc9_L (by positivity) (by positivity)
        _ = 1 := hmul_ν
    have h2 : K_two * c ^ 9 ≤ (θ₁ / (4 * D)) * L := by
      have hmul := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (θ₁ / (4 * D)) * L by positivity)
      have hlhs_eq : ((θ₁ / (4 * D)) * L) * ((4 * D * K_two / θ₁) * (c ^ 9 / L)) = K_two * c ^ 9 := by
        field_simp [hθ₁.ne', hD.ne', hL0.ne']
      linarith only [hmul, hlhs_eq]
    exact h2.trans hk₁_lb
  have hleak1 : terminalPacketCost R₁ (N / linearDefectCutoff c) N /
      Real.log (N / linearDefectCutoff c : ℕ) ≤ b / (4 * c ^ 7) := by
    have hB0 : 0 ≤ terminalPacketCost R₁ (N / linearDefectCutoff c) N :=
      terminalPacketCost_nonneg R₁ (Nat.div_le_self N _)
    have hdivM : terminalPacketCost R₁ (N / linearDefectCutoff c) N /
        Real.log (N / linearDefectCutoff c : ℕ) ≤ 2 * CB * (1 + Real.log c) / L := by
      have h1 : terminalPacketCost R₁ (N / linearDefectCutoff c) N /
          Real.log (N / linearDefectCutoff c : ℕ) ≤
          terminalPacketCost R₁ (N / linearDefectCutoff c) N / (L / 2) :=
        div_le_div_of_nonneg_left hB0 (half_pos hL0) hhalfM
      have h2 : terminalPacketCost R₁ (N / linearDefectCutoff c) N / (L / 2) =
          2 * terminalPacketCost R₁ (N / linearDefectCutoff c) N / L := by ring
      exact (h1.trans_eq h2).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hB1_ub zero_le_two) hL0.le)
    have hc7_vc : c ^ 7 * (1 + Real.log c) / L ≤ L ^ (-ν) := by
      have hc79 : c ^ 7 ≤ c ^ 9 := pow_le_pow_right₀ hc1 (by norm_num)
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc79 (by linarith [Real.log_nonneg hc1])) hL0.le).trans hc9_vc_L
    have h8CB : (8 * CB / b) * (c ^ 7 * (1 + Real.log c) / L) ≤ 1 := by
      calc
        (8 * CB / b) * (c ^ 7 * (1 + Real.log c) / L) ≤ L ^ ν * L ^ (-ν) :=
          mul_le_mul hν_bound_5 hc7_vc (by positivity) (by positivity)
        _ = 1 := hmul_ν
    have hstep : 2 * CB * (1 + Real.log c) / L ≤ b / (4 * c ^ 7) := by
      rw [div_le_div_iff₀ hL0 (by positivity : 0 < 4 * c ^ 7)]
      have hm := mul_le_mul_of_nonneg_left h8CB (show 0 ≤ b * L by positivity)
      have hid : (b * L) * ((8 * CB / b) * (c ^ 7 * (1 + Real.log c) / L)) =
          2 * CB * (1 + Real.log c) * (4 * c ^ 7) := by
        field_simp [hb.ne', hL0.ne']; ring
      linarith only [hm, hid]
    exact hdivM.trans hstep
  have hdiag2 := htwo_res hc1 hR₁2 hcutN hRM1 hlogM1 hKc9_gap hleak1 hw_orthR₁
  -- Cross 1: `(u₀, u₁)` via `hcross01`.
  have hsmall_cross01 : C_cross01 * (1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
      c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ))) ≤ 1 := by
    have hc4_vc : c ^ 4 * (1 + Real.log c) / L ≤ L ^ (-ν) := by
      have hc49 : c ^ 4 ≤ c ^ 9 := pow_le_pow_right₀ hc1 (by norm_num)
      exact (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hc49 (by linarith [Real.log_nonneg hc1])) hL0.le).trans hc9_vc_L
    have hc3_N : c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ L ^ (-ν) := hc3R₀2.trans h1_invL
    have hsum4 : 1 / Lh + c ^ 2 * (1 + Real.log c) / Lh +
        c ^ 4 * (1 + Real.log c) / L + c ^ 3 * (R₀ : ℝ) ^ 2 * (L / (N : ℝ)) ≤ 4 * L ^ (-ν) := by
      linarith only [h1_invLh, hc2_vc_Lh, hc4_vc, hc3_N]
    calc
      _ ≤ C_cross01 * (4 * L ^ (-ν)) := mul_le_mul_of_nonneg_left hsum4 hC_cross01.le
      _ = (C_cross01 * 4) * L ^ (-ν) := by ring
      _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_bound_2 (by positivity)
      _ = 1 := hmul_ν
  have hcr01 := hcross01 hR₀2 hR₀6 (by linarith only [h36_R₀, Real.log_natCast_nonneg R₀])
    hc1 hw1 hsize_near0 hsize_up0 hH₀_ub hsmall_cross01 a₀ (ha₀.symm ▸ hu₀_1) hu₁_orthR₀
  rw [ha₀] at hcr01
  -- Cross 2 & 3: `(u₀, w)` and `(u₁, w)` via `hcross_w`.
  have hsmall_cross_w : ∀ {R : ℕ},
      terminalPacketCost R (N / linearDefectCutoff c) N ≤ CB * (1 + Real.log c) →
      c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ) ≤ 1 / L →
      C_cross_w * (c ^ 7 * (1 + terminalPacketCost R (N / linearDefectCutoff c) N) / L +
        c ^ 9 * (1 + Real.log c) / L + c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ)) ≤ 1 := by
    intro R hB_ub hc10_ub
    have hlc1 : 1 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
    have h1B : 1 + terminalPacketCost R (N / linearDefectCutoff c) N ≤
        (CB + 1) * (1 + Real.log c) := by nlinarith only [hB_ub, hlc1]
    have hc79 : c ^ 7 ≤ c ^ 9 := pow_le_pow_right₀ hc1 (by norm_num)
    have ht1 : c ^ 7 * (1 + terminalPacketCost R (N / linearDefectCutoff c) N) / L ≤
        (CB + 1) * L ^ (-ν) := by
      have h1 : c ^ 7 * (1 + terminalPacketCost R (N / linearDefectCutoff c) N) / L ≤
          (CB + 1) * (c ^ 9 * (1 + Real.log c) / L) := by
        rw [← mul_div_assoc]
        apply div_le_div_of_nonneg_right _ hL0.le
        have hm1 := mul_le_mul_of_nonneg_left h1B (pow_nonneg hc0.le 7)
        have hm2 := mul_le_mul_of_nonneg_right hc79
          (show 0 ≤ (CB + 1) * (1 + Real.log c) by positivity)
        linarith only [hm1, hm2,
          (by ring : c ^ 7 * ((CB + 1) * (1 + Real.log c)) = c ^ 7 * ((CB + 1) * (1 + Real.log c))),
          (by ring : c ^ 9 * ((CB + 1) * (1 + Real.log c)) = (CB + 1) * (c ^ 9 * (1 + Real.log c)))]
      exact h1.trans (mul_le_mul_of_nonneg_left hc9_vc_L (by positivity))
    have ht3 : c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ) ≤ L ^ (-ν) := hc10_ub.trans h1_invL
    have hsum : c ^ 7 * (1 + terminalPacketCost R (N / linearDefectCutoff c) N) / L +
        c ^ 9 * (1 + Real.log c) / L + c ^ 10 * (R : ℝ) ^ 2 / (N : ℝ) ≤
        (CB + 3) * L ^ (-ν) := by linarith only [ht1, hc9_vc_L, ht3]
    calc
      _ ≤ C_cross_w * ((CB + 3) * L ^ (-ν)) := mul_le_mul_of_nonneg_left hsum hC_cross_w.le
      _ = (C_cross_w * (CB + 3)) * L ^ (-ν) := by ring
      _ ≤ L ^ ν * L ^ (-ν) := mul_le_mul_of_nonneg_right hν_bound_3 (by positivity)
      _ = 1 := hmul_ν
  have hcr0w := hcross_w hR₀2 hR₀R₁ hR₀6 (by linarith only [h36_R₀, Real.log_natCast_nonneg R₀])
    hc1 hc2L hw1 hsize_near0 hsize_up0 hH₁_ub hk₁_lb (hsmall_cross_w hB0_ub hc10R₀2)
    a₀ (ha₀.symm ▸ hu₀_1) hw_orthR₁
  rw [ha₀] at hcr0w
  have hcr1w := hcross_w hR₁2 le_rfl hR₁6 (by linarith only [h36_R₁, Real.log_natCast_nonneg R₁])
    hc1 hc2L hw1 hsize_near1 hsize_up1 hH₁_ub hk₁_lb (hsmall_cross_w hB1_ub hc10R₁2)
    a₁ (ha₁.symm ▸ hu₁_1) hw_orthR₁
  rw [ha₁] at hcr1w
  -- Net floor on Band 0 (`u₀`), Band 1 (`u₁`), and Band 2 (`w`).
  have hfloor0 : (κ₀ + 2) * ‖u₀‖ ^ 2 ≤
      ((3 / 4 : ℝ) * Real.log Q₁ - Real.log c - C_coerc0 - 1 / 2) * ‖u₀‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖u₀‖)
    have hlogc : Real.log c ≤ α * Real.log L :=
      (Real.log_le_log hc0 hcup).trans_eq (Real.log_rpow hL0 α)
    have hq_scaled : (3 / 4 : ℝ) * q * Real.log L - 3 / 4 ≤ (3 / 4 : ℝ) * Real.log Q₁ := by
      have hm := mul_le_mul_of_nonneg_left hlogQ_lb (by norm_num : (0 : ℝ) ≤ 3 / 4)
      linarith only [hm]
    have hll_scaled : κ₀ + 3 + C_coerc0 + 3 / 4 ≤ ((3 / 4 : ℝ) * q - α) * Real.log L :=
      ((div_le_iff₀ hgap_q).mp (show M_ll ≤ Real.log L from hll_big)).trans_eq (mul_comm _ _)
    linarith only [hlogc, hq_scaled, hll_scaled]
  have hfloor1 : (κ₀ + 2) * ‖u₁‖ ^ 2 ≤
      ((1 / 4 : ℝ) * Real.log R₀ - C_band1 * c ^ 2 * (1 + Real.log c) -
        (1 / 16 : ℝ) * Lh - 1 / 4) * ‖u₁‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖u₁‖)
    have hc2_Lh : C_band1 * c ^ 2 * (1 + Real.log c) ≤ (1 / 16 : ℝ) * Lh := by
      have h1 : (16 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) ≤ 1 := by
        calc
          (16 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) ≤ L ^ ν * L ^ (-ν) :=
            mul_le_mul hν_bound_6 hc2_vc_Lh (by positivity) (by positivity)
          _ = 1 := hmul_ν
      have hm := mul_le_mul_of_nonneg_right h1 ((1 / 16 : ℝ) * Lh |> fun _ => by positivity : 0 ≤ (1 / 16 : ℝ) * Lh)
      have hid : (16 * C_band1) * (c ^ 2 * (1 + Real.log c) / Lh) * ((1 / 16 : ℝ) * Lh) =
          C_band1 * c ^ 2 * (1 + Real.log c) := by field_simp [hLh0.ne']; ring
      linarith only [hm, hid]
    have hLh_lb : 16 * (κ₀ + 3) ≤ Lh := by
      have hsq : (16 * (κ₀ + 3)) ^ 2 ≤ Lh ^ 2 := by
        rw [sq Lh, hLh_sq]; linarith only [hL_Lh_gap]
      have hp : 0 ≤ 16 * (κ₀ + 3) := by positivity
      nlinarith only [hsq, hp, hLh0]
    linarith only [hlogR₀_lb, hc2_Lh, hLh_lb]
  let P_w := ∑ n ∈ Icc 1 (N / linearDefectCutoff c), primeHorizonExtension w n ^ 2
  let S_w := ∑ n ∈ Ioc (N / linearDefectCutoff c) N, primeHorizonExtension w n ^ 2
  let k₁ := Real.log (R₁ : ℝ) / D - 1
  have hPw0 : 0 ≤ P_w := sum_nonneg fun _ _ => sq_nonneg _
  have hSw0 : 0 ≤ S_w := sum_nonneg fun _ _ => sq_nonneg _
  have hw_split : ‖w‖ ^ 2 = P_w + S_w := by
    rw [← sum_primeHorizonExtension_sq w]
    dsimp only [P_w, S_w]
    rw [Ioc_eq_Icc_sdiff_Icc (N / linearDefectCutoff c) N, add_comm]
    exact (sum_sdiff (Icc_subset_Icc le_rfl (Nat.div_le_self N _))).symm
  have hk₁_pos : 0 < k₁ := (mul_pos (div_pos hθ₁ (by positivity)) hL0).trans_le hk₁_lb
  have hfloor2 : (κ₀ + 2) * ‖w‖ ^ 2 ≤
      (k₁ / 4) * P_w + (b * k₁ / (2 * c ^ 7)) * S_w -
        2 * ((k₁ / 32) * P_w + (b * k₁ / (32 * c ^ 7)) * S_w +
          (b * k₁ / (32 * c ^ 7)) * ‖w‖ ^ 2) := by
    rw [hw_split]
    have hb_c7 : b / c ^ 7 ≤ 1 / 8 :=
      (div_le_self hb.le (one_le_pow₀ hc1)).trans hb8
    have hP_net : (k₁ / 8) * P_w ≤
        (k₁ / 4 - 2 * (k₁ / 32) - 2 * (b * k₁ / (32 * c ^ 7))) * P_w := by
      apply mul_le_mul_of_nonneg_right _ hPw0
      have hh : b * k₁ / (32 * c ^ 7) ≤ k₁ / 256 := by
        have hm := mul_le_mul_of_nonneg_right hb_c7 (show 0 ≤ k₁ / 32 by positivity)
        exact (by field_simp [hc0.ne']; ring : b * k₁ / (32 * c ^ 7) = (b / c ^ 7) * (k₁ / 32)).trans_le
          (hm.trans_eq (by ring))
      linarith only [hh, hk₁_pos]
    have hP_k : (κ₀ + 2) * P_w ≤ (k₁ / 8) * P_w := by
      apply mul_le_mul_of_nonneg_right _ hPw0
      have h1 : 32 * D * (κ₀ + 2) ≤ θ₁ * L := by
        have hh := (div_le_iff₀ hθ₁).mp (show 32 * D * (κ₀ + 2) / θ₁ ≤ L by linarith only [hL_w_pre])
        linarith only [hh]
      have h2 : κ₀ + 2 ≤ ((θ₁ / (4 * D)) * L) / 8 := by
        rw [div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
        linarith only [h1]
      exact h2.trans (div_le_div_of_nonneg_right hk₁_lb (by norm_num))
    have hS_k : (κ₀ + 2) * S_w ≤ (3 * b * k₁ / (8 * c ^ 7)) * S_w := by
      apply mul_le_mul_of_nonneg_right _ hSw0
      have hc7_L : c ^ 7 / L ≤ L ^ (-ν) := by
        have hc79 : c ^ 7 ≤ c ^ 9 := pow_le_pow_right₀ hc1 (by norm_num)
        exact (div_le_div_of_nonneg_right hc79 hL0.le).trans hc9_L
      have h1 : (32 * D * (κ₀ + 2) / (3 * b * θ₁)) * (c ^ 7 / L) ≤ 1 := by
        calc
          (32 * D * (κ₀ + 2) / (3 * b * θ₁)) * (c ^ 7 / L) ≤ L ^ ν * L ^ (-ν) :=
            mul_le_mul hν_bound_7 hc7_L (by positivity) (by positivity)
          _ = 1 := hmul_ν
      have h2 : κ₀ + 2 ≤ 3 * b * ((θ₁ / (4 * D)) * L) / (8 * c ^ 7) := by
        have hm := mul_le_mul_of_nonneg_right h1
          (show 0 ≤ 3 * b * ((θ₁ / (4 * D)) * L) / (8 * c ^ 7) by positivity)
        have hid : (32 * D * (κ₀ + 2) / (3 * b * θ₁)) * (c ^ 7 / L) *
            (3 * b * ((θ₁ / (4 * D)) * L) / (8 * c ^ 7)) = κ₀ + 2 := by
          field_simp [hb.ne', hθ₁.ne', hD.ne', hL0.ne', hc0.ne']; ring
        linarith only [hm, hid]
      exact h2.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hk₁_lb (by positivity)) (by positivity))
    have hident :
        (k₁ / 4) * P_w + (b * k₁ / (2 * c ^ 7)) * S_w -
          2 * ((k₁ / 32) * P_w + (b * k₁ / (32 * c ^ 7)) * S_w +
            (b * k₁ / (32 * c ^ 7)) * (P_w + S_w)) =
        (k₁ / 4 - 2 * (k₁ / 32) - 2 * (b * k₁ / (32 * c ^ 7))) * P_w +
          (3 * b * k₁ / (8 * c ^ 7)) * S_w := by
      field_simp [hc0.ne']; ring
    rw [hident, mul_add]
    linarith only [hP_net, hP_k, hS_k]
  -- Combine all three diagonal bounds and all three cross bounds!
  have h3add := completeWeilEnergy_three_add_ge tiltedUnitSpline c u₀ u₁ w
  rw [← hz_eq] at h3add
  have hE₀_0 : 0 ≤ primeAdjunctionMass R₀ a₀ := primeAdjunctionMass_nonneg R₀ a₀
  have hE₁_0 : 0 ≤ primeAdjunctionMass R₁ a₁ := primeAdjunctionMass_nonneg R₁ a₁
  rw [hnorm_split]
  change (κ₀ + 2) * (‖u₀‖ ^ 2 + ‖u₁‖ ^ 2 + ‖w‖ ^ 2) ≤ completeWeilEnergy tiltedUnitSpline c N z
  change (k₁ / 4) * P_w + (b * k₁ / (2 * c ^ 7)) * S_w ≤
    completeWeilEnergy tiltedUnitSpline c N w at hdiag2
  change _ ≤ _ + _ + (k₁ / 32) * P_w + (b * k₁ / (32 * c ^ 7)) * S_w +
    (b * k₁ / (32 * c ^ 7)) * ‖w‖ ^ 2 at hcr0w hcr1w
  linarith only [h3add, hdiag0, hdiag1, hdiag2, hcr01, hcr0w, hcr1w,
    hfloor0, hfloor1, hfloor2, hE₀_0, hE₁_0]

/-! ### 6. Global two-block Schur synthesis and all-vector positivity below `1 / 9` -/

private theorem posDef_of_inner_pos_on_ne_zero {N : ℕ}
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (hpos : ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), x ≠ 0 →
      0 < ⟪Matrix.toEuclideanLin A x, x⟫) :
    A.PosDef := by
  classical
  apply hA.posDef_iff_eigenvalues_pos.mpr
  intro i
  let x := hA.eigenvectorBasis i
  have hx_inner : ⟪x, x⟫ = (1 : ℝ) := by
    simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
  have hx_ne : x ≠ 0 := by
    intro h0
    rw [h0, inner_zero_left] at hx_inner
    norm_num at hx_inner
  have hAx : Matrix.toEuclideanLin A x = hA.eigenvalues i • x := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have heig : ⟪Matrix.toEuclideanLin A x, x⟫ = hA.eigenvalues i := by
    rw [hAx, real_inner_smul_left, hx_inner, mul_one]
  exact heig ▸ hpos x hx_ne

private theorem two_block_schur_spectralFloor_pos {Q₁ N : ℕ} {c : ℝ}
    (hc1 : 1 ≤ c) (a : ℕ → ℝ)
    {z : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hz : z ∈ (conductorSubspace Q₁ N)ᗮ)
    (hy_floor :
      (1 / 4 : ℝ) * (∑ m ∈ Icc 1 Q₁, completedConductorEnergy tiltedUnitSpline c m * a m ^ 2) ≤
        ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
            (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N),
          ∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N⟫)
    (hz_floor :
      (tiltedSplineSpectralFloorConstant + 2) * ‖z‖ ^ 2 ≤
        completeWeilEnergy tiltedUnitSpline c N z)
    (hres_budget :
      (∑ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m •
            normalizedRamanujanHorizonVector m N‖ ^ 2 /
          completedConductorEnergy tiltedUnitSpline c m) ≤ 1 / 8)
    (hne : (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + z ≠ 0) :
    0 < ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
          ((∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + z),
        (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + z⟫ := by
  let y := ∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N
  let E : ℕ → ℝ := fun m => completedConductorEnergy tiltedUnitSpline c m
  let r : ℕ → EuclideanSpace ℝ (PrimeHorizonIndex N) := fun m =>
    Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
        (normalizedRamanujanHorizonVector m N) -
      E m • normalizedRamanujanHorizonVector m N
  let S_y := ∑ m ∈ Icc 1 Q₁, E m * a m ^ 2
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hE_pos : ∀ m ∈ Icc 1 Q₁, 0 < E m := by
    intro m hm
    have hs : 0 < tiltedSplineSpectralFloorConstant / (2 * c ^ 7) :=
      div_pos tiltedSplineSpectralFloorConstant_pos (by positivity)
    have hge := spectralFloor_conductor_energy_ge hc1 (mem_Icc.mp hm).1
    dsimp only [E]
    linarith only [hs, hge]
  have hSy_nonneg : 0 ≤ S_y := sum_nonneg fun m hm => mul_nonneg (hE_pos m hm).le (sq_nonneg _)
  -- Block z lower bound on spectralFloorWeilMatrix.
  have hz_A : 2 * ‖z‖ ^ 2 ≤ ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) z, z⟫ := by
    rw [spectralFloorWeilMatrix_inner]
    have hc7 : (1 : ℝ) ≤ c ^ 7 := one_le_pow₀ hc1
    have hshift_le : tiltedSplineSpectralFloorConstant / (2 * c ^ 7) ≤
        tiltedSplineSpectralFloorConstant :=
      div_le_self tiltedSplineSpectralFloorConstant_pos.le (by linarith only [hc7])
    have hm := mul_le_mul_of_nonneg_right hshift_le (sq_nonneg ‖z‖)
    linarith only [hz_floor, hm]
  -- Cross term identity and energy-weighted Cauchy-Schwarz bound.
  have hy_mem : y ∈ conductorSubspace Q₁ N :=
    sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N a
  have hyz0 : ⟪y, z⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hy_mem hz
  have hvm_z0 : ∀ m ∈ Icc 1 Q₁, ⟪normalizedRamanujanHorizonVector m N, z⟫ = 0 := by
    intro m hm
    let b : ℕ → ℝ := fun k => if k = m then 1 else 0
    have hb_eq : (∑ k ∈ Icc 1 Q₁, b k • normalizedRamanujanHorizonVector k N) =
        normalizedRamanujanHorizonVector m N := by
      dsimp only [b]
      rw [sum_eq_single m]
      · simp
      · intro k _ hkm; rw [if_neg hkm, zero_smul]
      · intro hm_not; exact False.elim (hm_not hm)
    have hmem : normalizedRamanujanHorizonVector m N ∈ conductorSubspace Q₁ N := by
      rw [← hb_eq]
      exact sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N b
    exact Submodule.inner_right_of_mem_orthogonal hmem hz
  have hcross_eq :
      ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) y, z⟫ =
        ∑ m ∈ Icc 1 Q₁, a m * ⟪r m, z⟫ := by
    have h1 : ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) y, z⟫ =
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) y, z⟫ := by
      simp only [spectralFloorWeilMatrix, map_sub, map_smul, LinearMap.sub_apply,
        LinearMap.smul_apply, identity_euclid_apply_telescoped, inner_sub_left,
        real_inner_smul_left, hyz0, mul_zero, sub_zero]
    rw [h1]
    dsimp only [y]
    rw [map_sum, sum_inner]
    refine sum_congr rfl fun m hm => ?_
    rw [map_smul, real_inner_smul_left]
    congr 1
    dsimp only [r]
    rw [inner_sub_left, real_inner_smul_left, hvm_z0 m hm, mul_zero, sub_zero]
  let f : ℕ → ℝ := fun m => |a m| * Real.sqrt (E m)
  let g : ℕ → ℝ := fun m => ‖r m‖ / Real.sqrt (E m)
  have hfg_eq : ∀ m ∈ Icc 1 Q₁, f m * g m = |a m| * ‖r m‖ := by
    intro m hm
    have hs : 0 < Real.sqrt (E m) := Real.sqrt_pos.mpr (hE_pos m hm)
    dsimp only [f, g]
    field_simp [hs.ne']
  have hf_sq : (∑ m ∈ Icc 1 Q₁, f m ^ 2) = S_y := by
    dsimp only [S_y]
    refine sum_congr rfl fun m hm => ?_
    dsimp only [f]
    rw [mul_pow, sq_abs, Real.sq_sqrt (hE_pos m hm).le]
    ring
  have hg_sq : (∑ m ∈ Icc 1 Q₁, g m ^ 2) = ∑ m ∈ Icc 1 Q₁, ‖r m‖ ^ 2 / E m := by
    refine sum_congr rfl fun m hm => ?_
    dsimp only [g]
    rw [div_pow, Real.sq_sqrt (hE_pos m hm).le]
  have hcs_sq : (∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖) ^ 2 ≤ (1 / 8 : ℝ) * S_y := by
    have hrew : (∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖) = ∑ m ∈ Icc 1 Q₁, f m * g m :=
      sum_congr rfl fun m hm => (hfg_eq m hm).symm
    rw [hrew]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Icc 1 Q₁) f g
    rw [hf_sq, hg_sq] at hcs
    exact hcs.trans ((mul_le_mul_of_nonneg_left hres_budget hSy_nonneg).trans_eq (mul_comm _ _))
  have hcross_abs :
      2 * |⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) y, z⟫| ≤
        (1 / 8 : ℝ) * S_y + ‖z‖ ^ 2 := by
    rw [hcross_eq]
    have htri : |∑ m ∈ Icc 1 Q₁, a m * ⟪r m, z⟫| ≤
        (∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖) * ‖z‖ := by
      rw [sum_mul]
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m _ => ?_)
      rw [abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (r m) z) (abs_nonneg _)
    let X := ∑ m ∈ Icc 1 Q₁, |a m| * ‖r m‖
    have hyoung : 2 * (X * ‖z‖) ≤ X ^ 2 + ‖z‖ ^ 2 := by
      nlinarith only [sq_nonneg (X - ‖z‖)]
    have h2 := (mul_le_mul_of_nonneg_left htri zero_le_two).trans hyoung
    linarith only [h2, hcs_sq]
  -- Assemble Hermitian quadratic form on `y + z`.
  have hexp := hermitian_inner_add_eq_telescoped (spectralFloorWeilMatrix_isHermitian c N) y z
  have hlb : (1 / 8 : ℝ) * S_y + ‖z‖ ^ 2 ≤
      ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) (y + z), y + z⟫ := by
    rw [hexp]
    have habs := neg_abs_le ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) y, z⟫
    change (1 / 4 : ℝ) * S_y ≤ ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) y, y⟫ at hy_floor
    linarith only [hy_floor, hz_A, hcross_abs, habs]
  -- Strict positivity when `y + z ≠ 0`.
  have hpos_lhs : 0 < (1 / 8 : ℝ) * S_y + ‖z‖ ^ 2 := by
    by_contra hnot
    have hle0 : (1 / 8 : ℝ) * S_y + ‖z‖ ^ 2 ≤ 0 := not_lt.mp hnot
    have hz_sq0 : ‖z‖ ^ 2 = 0 := by linarith only [hle0, hSy_nonneg, sq_nonneg ‖z‖]
    have hSy0 : S_y = 0 := by linarith only [hle0, hSy_nonneg, sq_nonneg ‖z‖]
    have hz0 : z = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz_sq0)
    have hterm0 : ∀ m ∈ Icc 1 Q₁, E m * a m ^ 2 = 0 := fun m hm =>
      (sum_eq_zero_iff_of_nonneg fun k hk => mul_nonneg (hE_pos k hk).le (sq_nonneg _)).mp hSy0 m hm
    have ha0 : ∀ m ∈ Icc 1 Q₁, a m = 0 := by
      intro m hm
      rcases mul_eq_zero.mp (hterm0 m hm) with hEm0 | ham0
      · exact False.elim ((hE_pos m hm).ne' hEm0)
      · exact sq_eq_zero_iff.mp ham0
    have hy0 : y = 0 := by
      dsimp only [y]
      exact sum_eq_zero fun m hm => by rw [ha0 m hm, zero_smul]
    exact hne (by dsimp only [y] at hy0; rw [hy0, hz0, add_zero])
  exact hpos_lhs.trans_le hlb

/-- **Positive definiteness of `spectralFloorWeilMatrix c N` below `1 / 9`.**
For every `0 < α < 1 / 9`, eventually in `N`, `spectralFloorWeilMatrix c N` is positive definite
uniformly across `1 ≤ c ≤ (log N)^α`. -/
theorem eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_ninth
    {α : ℝ} (hα : 0 < α) (hα_lt : α < oneNinthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      (spectralFloorWeilMatrix c N).PosDef := by
  have hα9 : α < 1 / 9 := hα_lt
  have hα8 : α < oneEighthPowerLogExponent :=
    hα_lt.trans oneNinthPowerLogExponent_lt_oneEighthPowerLogExponent
  let q : ℝ := α + 1 / 4
  have hq_pos : 0 < q := by dsimp only [q]; linarith only [hα]
  have hq_lo : 3 * α < q := by dsimp only [q]; linarith only [hα9]
  have hq_hi : q ≤ 1 / 2 := by dsimp only [q]; linarith only [hα9]
  have hα2q : α + 2 * q < 1 := by dsimp only [q]; linarith only [hα9]
  have h2q2α : 2 * q + 2 * α < 1 := by dsimp only [q]; linarith only [hα9]
  let δ := min (1 - 9 * α) (1 - (2 * q + 2 * α))
  have hδ : 0 < δ := lt_min (by linarith only [hα9]) (by linarith only [h2q2α])
  let ν := δ / 20
  have hν : 0 < ν := by dsimp only [ν]; positivity
  let k : ℕ := ⌈1 / (2 * ν)⌉₊ + 1
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hrate_k : 1 / (k : ℝ) ≤ 2 * ν := by
    have hceil := Nat.le_ceil (1 / (2 * ν))
    have h2νk : 1 ≤ (2 * ν) * (k : ℝ) := by
      have hh := (div_le_iff₀ (by positivity : 0 < 2 * ν)).mp hceil
      dsimp only [k]; push_cast; nlinarith only [hh, hν]
    exact (div_le_iff₀ hk0).mpr h2νk
  have hexp_c9 : 9 * α + 3 * ν + 1 / (k : ℝ) - 1 ≤ -ν := by
    have h1 : δ ≤ 1 - 9 * α := min_le_left _ _
    dsimp only [ν] at hrate_k ⊢; linarith only [h1, hrate_k, hδ]
  have hexp_q : 2 * q + 2 * α + 5 * ν + 1 / (k : ℝ) - 1 ≤ -ν := by
    have h2 : δ ≤ 1 - (2 * q + 2 * α) := min_le_right _ _
    dsimp only [ν] at hrate_k ⊢; linarith only [h2, hrate_k, hδ]
  obtain ⟨K_inv, hK_inv, hinv_res⟩ := exists_tiltedUnitSpline_quadratic_inv_energy_residual_sum_le
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_tiltedUnitSpline_polylog_conductorSubspace_energy_ge
      hα hα8 hq_pos hα2q,
    eventually_tiltedUnitSpline_complement_coercive_below_one_ninth hα hα_lt hq_lo hq_hi,
    hinv_res q hq_pos.le k hk,
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1 hν 1),
    ((tendsto_rpow_atTop hq_pos).comp hLlim).eventually_ge_atTop 2,
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop (32 * K_inv + 1),
    hLlim.eventually_ge_atTop 2000,
    eventually_ge_atTop 3] with
      N hlowN hcompN hinvN hLX hpoly hQ_ge2 hν_big hL2000 hN3 c hc1 hcup
  dsimp only [Function.comp_def] at hpoly hQ_ge2 hν_big
  let L := Real.log (N : ℝ)
  let Q₁ := ⌊L ^ q⌋₊
  have hL1 : 1 ≤ L := by linarith only [hL2000]
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 1 ≤ N by omega)
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hcL : c ≤ L := hcup.trans (by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα9] : α ≤ 1))
  have hQ2 : 2 ≤ Q₁ := Nat.le_floor hQ_ge2
  have hQ_le : (Q₁ : ℝ) ≤ L ^ q := Nat.floor_le (by positivity)
  have hQ0 : (0 : ℝ) < Q₁ := by exact_mod_cast (show 0 < Q₁ by omega)
  have hcpow : ∀ j : ℕ, c ^ j ≤ L ^ ((j : ℝ) * α) := fun j => by
    have hp := pow_le_pow_left₀ hc0.le hcup j
    have he : (L ^ α) ^ j = L ^ ((j : ℝ) * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  have hX1 : 1 ≤ (N : ℝ) ^ (1 / 36 : ℝ) := hL1.trans hLX
  have hX36 : ((N : ℝ) ^ (1 / 36 : ℝ)) ^ (36 : ℕ) = (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
  have hwidth : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) := by
    let X := (N : ℝ) ^ (1 / 36 : ℝ)
    have he1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    have hconst : 4 * (Real.exp 1 + 3) ^ 2 ≤ X := by
      have : 4 * (Real.exp 1 + 3) ^ 2 ≤ 144 := by nlinarith only [he1, Real.exp_pos 1]
      linarith only [this, hL2000.trans hLX]
    have hc2 : c ^ 2 ≤ X ^ 2 := pow_le_pow_left₀ hc0.le (hcL.trans hLX) 2
    calc
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ X * X ^ 2 :=
        mul_le_mul hconst hc2 (sq_nonneg c) (by positivity)
      _ = X ^ 3 := by ring
      _ ≤ (N : ℝ) := (pow_le_pow_right₀ hX1 (by norm_num : 3 ≤ 36)).trans_eq hX36
  -- Bound the first-power inverse-energy Schur cross budget by `1 / 8`.
  have hres_budget :
      (∑ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m •
            normalizedRamanujanHorizonVector m N‖ ^ 2 /
          completedConductorEnergy tiltedUnitSpline c m) ≤ 1 / 8 := by
    have hraw := hinvN c hc1 hwidth Q₁ hQ_le
    have hpoly1 : 1 + Real.log L ≤ L ^ ν := by simpa only [one_mul, pow_one] using hpoly
    have hHQ : 1 + Real.log (Q₁ : ℝ) ≤ L ^ ν := by
      have hh := Real.log_le_log hQ0 hQ_le
      rw [Real.log_rpow hL0] at hh
      have hm := mul_le_mul_of_nonneg_right (hq_hi.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
        (Real.log_nonneg hL1)
      linarith only [hh, hm, hpoly1]
    have hHQsq : (1 + Real.log (Q₁ : ℝ)) ^ 2 ≤ L ^ (2 * ν) := by
      have hh := pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg Q₁]) hHQ 2
      have he : (L ^ ν) ^ (2 : ℕ) = L ^ (2 * ν) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
      exact hh.trans_eq he
    have hVc : 1 + Real.log c ≤ L ^ ν := by
      linarith only [Real.log_le_log hc0 hcL, hpoly1]
    have hVccube : (1 + Real.log c) ^ 3 ≤ L ^ (3 * ν) := by
      have hh := pow_le_pow_left₀ (by linarith [Real.log_nonneg hc1]) hVc 3
      have he : (L ^ ν) ^ (3 : ℕ) = L ^ (3 * ν) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
      exact hh.trans_eq he
    let r_lead := c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) / L
    have hr_lead0 : 0 ≤ r_lead := by
      dsimp only [r_lead]
      have : 0 ≤ 1 + Real.log c := by linarith [Real.log_nonneg hc1]
      positivity
    have hr_sub : c ^ 10 * (L / (N : ℝ)) ^ 2 ≤ r_lead := by
      have hc8_N : c ^ 8 * (L / (N : ℝ)) ^ 2 ≤ 1 / L := by
        rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos hN0) hL0, one_mul]
        let X := (N : ℝ) ^ (1 / 36 : ℝ)
        have hL11 : L ^ 11 ≤ X ^ 11 := pow_le_pow_left₀ hL0.le hLX 11
        have hX11 : X ^ 11 ≤ (N : ℝ) :=
          (pow_le_pow_right₀ hX1 (by norm_num : 11 ≤ 36)).trans_eq hX36
        have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
        calc
          c ^ 8 * L ^ 2 * L ≤ L ^ 8 * L ^ 3 := by
            have hc8 : c ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ hc0.le hcL 8
            calc
              c ^ 8 * L ^ 2 * L = c ^ 8 * L ^ 3 := by ring
              _ ≤ L ^ 8 * L ^ 3 := mul_le_mul_of_nonneg_right hc8 (by positivity)
          _ = L ^ 11 := by ring
          _ ≤ (N : ℝ) := hL11.trans hX11
          _ ≤ (N : ℝ) ^ 2 := by nlinarith only [hN1R]
      have h1 : 1 ≤ (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) :=
        one_le_mul_of_one_le_of_one_le
          (one_le_pow₀ (by linarith [Real.log_nonneg hc1]))
          (Real.one_le_rpow hL1 (by positivity))
      calc
        c ^ 10 * (L / (N : ℝ)) ^ 2 = c ^ 2 * (c ^ 8 * (L / (N : ℝ)) ^ 2) := by ring
        _ ≤ c ^ 2 * (1 / L) := mul_le_mul_of_nonneg_left hc8_N (sq_nonneg c)
        _ = c ^ 2 / L := by ring
        _ ≤ c ^ 2 * ((1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ))) / L :=
          div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg c) h1) hL0.le
        _ = r_lead := by dsimp only [r_lead]; ring
    have hr_lead_ub : r_lead ≤ L ^ (2 * α + 3 * ν + 1 / (k : ℝ) - 1) := by
      dsimp only [r_lead]
      have hnum : c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) ≤
          L ^ (((2 : ℕ) : ℝ) * α) * L ^ (3 * ν) * L ^ (1 / (k : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul (hcpow 2) hVccube (pow_nonneg (by linarith [Real.log_nonneg hc1]) 3)
            (by positivity)) (by positivity)
      calc
        c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) / L ≤
            (L ^ (((2 : ℕ) : ℝ) * α) * L ^ (3 * ν) * L ^ (1 / (k : ℝ))) / L :=
          div_le_div_of_nonneg_right hnum hL0.le
        _ = L ^ (2 * α + 3 * ν + 1 / (k : ℝ) - 1) := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, Real.rpow_sub hL0, Real.rpow_one]
          congr 1; push_cast
    have ht1 : c ^ 7 * r_lead ≤ L ^ (-ν) := by
      calc
        c ^ 7 * r_lead ≤ L ^ (((7 : ℕ) : ℝ) * α) * L ^ (2 * α + 3 * ν + 1 / (k : ℝ) - 1) :=
          mul_le_mul (hcpow 7) hr_lead_ub hr_lead0 (by positivity)
        _ = L ^ (9 * α + 3 * ν + 1 / (k : ℝ) - 1) := by
          rw [← Real.rpow_add hL0]; congr 1; push_cast; ring
        _ ≤ L ^ (-ν) := Real.rpow_le_rpow_of_exponent_le hL1 hexp_c9
    have ht2 : (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 * r_lead ≤ L ^ (-ν) := by
      have hQ2_pow : (Q₁ : ℝ) ^ 2 ≤ L ^ (2 * q) := by
        have hp := pow_le_pow_left₀ (Nat.cast_nonneg Q₁) hQ_le 2
        have he : (L ^ q) ^ (2 : ℕ) = L ^ (2 * q) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
        exact hp.trans_eq he
      calc
        (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 * r_lead ≤
            (L ^ (2 * q) * L ^ (2 * ν)) * L ^ (2 * α + 3 * ν + 1 / (k : ℝ) - 1) :=
          mul_le_mul (mul_le_mul hQ2_pow hHQsq (sq_nonneg _) (by positivity))
            hr_lead_ub hr_lead0 (by positivity)
        _ = L ^ (2 * q + 2 * α + 5 * ν + 1 / (k : ℝ) - 1) := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]; congr 1; ring
        _ ≤ L ^ (-ν) := Real.rpow_le_rpow_of_exponent_le hL1 hexp_q
    have hmul_ν : L ^ ν * L ^ (-ν) = 1 := by
      rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
    have h32K : 32 * K_inv ≤ L ^ ν := by linarith only [hν_big]
    let W := c ^ 7 + (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2
    have hW0 : 0 ≤ W := by dsimp only [W]; positivity
    calc
      _ ≤ K_inv * W * (r_lead + c ^ 10 * (L / (N : ℝ)) ^ 2) := hraw
      _ ≤ K_inv * W * (2 * r_lead) :=
        mul_le_mul_of_nonneg_left (by linarith only [hr_sub]) (mul_nonneg hK_inv.le hW0)
      _ = 2 * K_inv * (c ^ 7 * r_lead + (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 * r_lead) := by
        dsimp only [W]; ring
      _ ≤ 2 * K_inv * (L ^ (-ν) + L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) (by positivity)
      _ = (1 / 8 : ℝ) * ((32 * K_inv) * L ^ (-ν)) := by ring
      _ ≤ (1 / 8 : ℝ) * (L ^ ν * L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h32K (by positivity)) (by norm_num)
      _ = 1 / 8 := by rw [hmul_ν, mul_one]
  -- Conclude PosDef on every nonzero vector via the two-block Schur synthesis.
  refine posDef_of_inner_pos_on_ne_zero (spectralFloorWeilMatrix_isHermitian c N) fun x hx_ne => ?_
  let y := (conductorSubspace Q₁ N).starProjection x
  let z := x - y
  have hy_mem : y ∈ conductorSubspace Q₁ N :=
    (conductorSubspace Q₁ N).starProjection_apply_mem x
  have hz_orth : z ∈ (conductorSubspace Q₁ N)ᗮ :=
    sub_starProjection_mem_orthogonal_telescoped _ x
  obtain ⟨a, -, ha⟩ := (mem_conductorSubspace_iff (M := Q₁) (N := N) (x := y)).mp hy_mem
  have hx_eq : x = (∑ m ∈ Icc 1 Q₁, a m • normalizedRamanujanHorizonVector m N) + z := by
    rw [← ha]; dsimp only [z]; abel
  rw [hx_eq]
  exact two_block_schur_spectralFloor_pos hc1 a hz_orth
    (hlowN c hc1 hcup a) (hcompN c hc1 hcup hz_orth) hres_budget (hx_eq ▸ hx_ne)

/-- **Uniform `c⁻⁷` spectral floor below `1 / 9`.**
Throughout `1 ≤ c ≤ (log N)^α` (`0 < α < 1 / 9`), the complete Weil quadratic form of
`tiltedUnitSpline` dominates `(tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2`
for every horizon vector `x`. -/
theorem eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_ninth
    {α : ℝ} (hα : 0 < α) (hα_lt : α < oneNinthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2 ≤
          completeWeilEnergy tiltedUnitSpline c N x := by
  filter_upwards [eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_ninth
    hα hα_lt] with N hpos c hc hcup x
  have hA := spectralFloorWeilMatrix_isHermitian c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp (hpos c hc hcup)
  have hnonneg : 0 ≤ ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) x, x⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [spectralFloorWeilMatrix_inner] at hnonneg
  linarith only [hnonneg]

/-- **All-vector positivity of the complete Weil matrix below `1 / 9` (`Σ-3` closed up to `1 / 9`).**
For every `0 < α < 1 / 9`, eventually in `N`, `completeWeilMatrix tiltedUnitSpline c N`
is positive definite uniformly across `1 ≤ c ≤ (log N)^α`. -/
theorem eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_ninth
    {α : ℝ} (hα : 0 < α) (hα_lt : α < oneNinthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_ninth
    hα hα_lt] with N hfloor c hc hcup
  refine posDef_of_inner_pos_on_ne_zero (completeWeilMatrix_isHermitian tiltedUnitSpline c N)
    fun x hx_ne => ?_
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hpos : 0 < (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2 :=
    mul_pos (div_pos tiltedSplineSpectralFloorConstant_pos (by positivity))
      (sq_pos_of_pos (norm_pos_iff.mpr hx_ne))
  exact hpos.trans_le (hfloor c hc hcup x)

/-- **Explicit one-tenth overlap witness (`α = 1 / 10`).** -/
theorem eventually_tiltedUnitSpline_completeWeilMatrix_posDef_log_one_tenth :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ (1 / 10 : ℝ) →
      (completeWeilMatrix tiltedUnitSpline c N).PosDef :=
  eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_ninth
    (by norm_num) (by norm_num [oneNinthPowerLogExponent])

/-- **Literal Weil quadratic form nonnegativity below `1 / 9`.**
Throughout `1 ≤ c ≤ (log N)^α` (`0 < α < 1 / 9`), `weilQuad` is nonnegative on every atomic
coefficient family `atomicTest N y (atomDilate tiltedUnitSpline (c / N))`. -/
theorem eventually_tiltedUnitSpline_weilQuad_nonneg_below_one_ninth
    {α : ℝ} (hα : 0 < α) (hα_lt : α < oneNinthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ y : ℕ → ℝ,
        0 ≤ weilQuad (atomicTest N y (atomDilate tiltedUnitSpline (c / N))) := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_ninth hα hα_lt,
    eventually_ge_atTop 1] with N hpos hN c hc hcup y
  have hc0 := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc0 hN0
  have hM : 0 < ∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp (hpos c hc hcup)
  have hquad : 0 ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (horizonProfileVector y N), horizonProfileVector y N⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc0 hN] at hquad
  have htest : atomicTest N (primeHorizonExtension (horizonProfileVector y N))
      (atomDilate tiltedUnitSpline (c / N)) =
      atomicTest N y (atomDilate tiltedUnitSpline (c / N)) := by
    funext u
    unfold atomicTest
    apply sum_congr rfl
    intro n hn
    exact congrArg (· * atomDilate tiltedUnitSpline (c / N) (u - Real.log n))
      (primeHorizonExtension_coe (horizonProfileVector y N) ⟨n, hn⟩)
  rw [htest, div_nonneg_iff] at hquad
  rcases hquad with ⟨hq, -⟩ | ⟨-, hneg⟩
  · exact hq
  · linarith only [hM, hneg]

/-- **All-vector `poleDefect N` reserve below `1 / 9`.**
The `c⁻⁷` spectral floor cancels the polynomial mass debit and retains a positive prime-defect
reserve `(b₁ / c ^ 23) * poleDefect N` on every vector throughout `1 ≤ c ≤ (log N)^α`
(`0 < α < 1 / 9`). -/
theorem exists_tiltedUnitSpline_completeWeilEnergy_ge_poleDefect_reserve_below_one_ninth :
    ∃ b₁ : ℝ, 0 < b₁ ∧
      ∀ α : ℝ, 0 < α → α < oneNinthPowerLogExponent →
        ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
          ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
            (b₁ / c ^ 23) * poleDefect N (primeHorizonExtension x) ≤
              completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨b, B, H, hb, hB, hH, hr_poly⟩ := exists_tiltedUnitSpline_complete_defect_reserve_polynomial
  have hres : ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, H * c ^ 8 ≤ (N : ℝ) →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        b / c ^ 7 * poleDefect N (primeHorizonExtension x) - B * c ^ 9 * ‖x‖ ^ 2 ≤
          completeWeilEnergy tiltedUnitSpline c N x := by
    intro c hc N hN x
    have hc0 := zero_lt_one.trans_le hc
    have hN0 : (0 : ℝ) < N := (mul_pos hH (pow_pos hc0 8)).trans_le hN
    have hN1 : 1 ≤ N := by exact_mod_cast (show 0 < N by exact_mod_cast hN0)
    have hh := hr_poly c hc N hN (primeHorizonExtension x)
    rw [sum_primeHorizonExtension_sq] at hh
    rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero hc0 hN1, integral_atomDilate_sq (div_pos hc0 hN0)]
    exact hh
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  let b₁ := κ * b / (2 * B + κ)
  have hdenom : 0 < 2 * B + κ := by positivity
  have hb₁ : 0 < b₁ := div_pos (mul_pos hκ hb) hdenom
  refine ⟨b₁, hb₁, ?_⟩
  intro α hα hα_lt
  have hα_9 : α < 1 / 9 := hα_lt
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_ninth
      hα hα_lt,
    eventually_log_nat_le_rpow_36_one_ninth,
    hLlim.eventually_ge_atTop (max 1 H),
    eventually_ge_atTop 2] with N hfloor hLX hL_max hN2 c hc1 hcup x
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL_max
  have hHL : H ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hL_max
  have hcL : c ≤ Real.log (N : ℝ) :=
    hcup.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα_9] : α ≤ 1))
  have hHN : H * c ^ 8 ≤ (N : ℝ) := by
    let X := (N : ℝ) ^ (1 / 36 : ℝ)
    have hX1 : 1 ≤ X := hL1.trans hLX
    have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
      dsimp only [X]; rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; norm_num
    have hHX : H ≤ X := hHL.trans hLX
    have hc8 : c ^ 8 ≤ X ^ 8 := pow_le_pow_left₀ hc0.le (hcL.trans hLX) 8
    calc
      H * c ^ 8 ≤ X * X ^ 8 := mul_le_mul hHX hc8 (by positivity) (by positivity)
      _ = X ^ 9 := by ring
      _ ≤ (N : ℝ) := (pow_le_pow_right₀ hX1 (by norm_num : 9 ≤ 36)).trans_eq hX36
  have hr := hres c hc1 N hHN x
  have hf := hfloor c hc1 hcup x
  change (κ / (2 * c ^ 7)) * ‖x‖ ^ 2 ≤ completeWeilEnergy tiltedUnitSpline c N x at hf
  have hE0 : 0 ≤ completeWeilEnergy tiltedUnitSpline c N x :=
    (mul_nonneg (by positivity) (sq_nonneg ‖x‖)).trans hf
  have h1 := mul_le_mul_of_nonneg_left hr hκ.le
  have h2 := mul_le_mul_of_nonneg_left hf (by positivity : 0 ≤ 2 * B * c ^ 16)
  have hcancel : (2 * B * c ^ 16) * ((κ / (2 * c ^ 7)) * ‖x‖ ^ 2) =
      κ * (B * c ^ 9 * ‖x‖ ^ 2) := by
    field_simp [hc0.ne']
  rw [hcancel] at h2
  have hcomb : κ * ((b / c ^ 7) * poleDefect N (primeHorizonExtension x)) ≤
      (2 * B * c ^ 16 + κ) * completeWeilEnergy tiltedUnitSpline c N x := by
    linarith only [h1, h2]
  have hc16 : 1 ≤ c ^ 16 := one_le_pow₀ hc1
  have hscale : (2 * B * c ^ 16 + κ) * completeWeilEnergy tiltedUnitSpline c N x ≤
      ((2 * B + κ) * c ^ 16) * completeWeilEnergy tiltedUnitSpline c N x :=
    mul_le_mul_of_nonneg_right (by nlinarith only [hκ, hc16]) hE0
  have hpos_d : 0 < (2 * B + κ) * c ^ 23 := by positivity
  rw [show (b₁ / c ^ 23) * poleDefect N (primeHorizonExtension x) =
      (κ * b * poleDefect N (primeHorizonExtension x)) / ((2 * B + κ) * c ^ 23) by
    dsimp only [b₁]; rw [div_div, div_mul_eq_mul_div]]
  rw [div_le_iff₀ hpos_d]
  have hle := mul_le_mul_of_nonneg_right (hcomb.trans hscale) (pow_nonneg hc0.le 7)
  have h_lhs : κ * (b / c ^ 7 * poleDefect N (primeHorizonExtension x)) * c ^ 7 =
      κ * b * poleDefect N (primeHorizonExtension x) := by
    have hc7_ne : c ^ 7 ≠ 0 := pow_ne_zero 7 hc0.ne'
    calc
      κ * (b / c ^ 7 * poleDefect N (primeHorizonExtension x)) * c ^ 7 =
          (b / c ^ 7 * c ^ 7) * (κ * poleDefect N (primeHorizonExtension x)) := by ring
      _ = b * (κ * poleDefect N (primeHorizonExtension x)) := by rw [div_mul_cancel₀ _ hc7_ne]
      _ = κ * b * poleDefect N (primeHorizonExtension x) := by ring
  have h_rhs : (2 * B + κ) * c ^ 16 * completeWeilEnergy tiltedUnitSpline c N x * c ^ 7 =
      completeWeilEnergy tiltedUnitSpline c N x * ((2 * B + κ) * c ^ 23) := by ring
  rw [h_lhs, h_rhs] at hle
  exact hle

private theorem one_div_log_le_norm_normalizedRamanujanHorizonVector_sq_one_ninth
    {m N : ℕ} (hN2 : 2 ≤ N) (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    1 / Real.log (N : ℝ) ≤ ‖normalizedRamanujanHorizonVector m N‖ ^ 2 := by
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hm0 : 0 < m := by omega
  have hm0R : (0 : ℝ) < m := by exact_mod_cast hm0
  rw [← sum_primeHorizonExtension_sq]
  have hsub : Ioc 0 m ⊆ Icc 1 N := fun n hn => by
    obtain ⟨hn0, hnm⟩ := mem_Ioc.mp hn
    exact mem_Icc.mpr ⟨by omega, hnm.trans hmN⟩
  have hterm : ∀ n ∈ Ioc 0 m,
      (Real.log (N : ℝ))⁻¹ * (normalizedRamanujanMode m n ^ 2 / (m : ℝ)) ≤
        primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2 := by
    intro n hn
    obtain ⟨hn0, hnm⟩ := mem_Ioc.mp hn
    have hn0R : (0 : ℝ) < n := by exact_mod_cast hn0
    have hcoe : primeHorizonExtension (normalizedRamanujanHorizonVector m N) n =
        (Real.sqrt (Real.log (N : ℝ)))⁻¹ * (normalizedRamanujanMode m n / Real.sqrt n) := by
      rw [primeHorizonExtension_coe _ ⟨n, hsub hn⟩]; rfl
    rw [hcoe, mul_pow, inv_pow, Real.sq_sqrt hL0.le, div_pow, Real.sq_sqrt hn0R.le]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (sq_nonneg _) hn0R (by exact_mod_cast hnm))
      (inv_nonneg.mpr hL0.le)
  calc
    1 / Real.log (N : ℝ) =
        (Real.log (N : ℝ))⁻¹ * ((∑ n ∈ Ioc 0 (0 + m), normalizedRamanujanMode m n ^ 2) / (m : ℝ)) := by
      rw [CompletedArithmeticForms.sum_Ioc_normalizedRamanujanMode_sq hm0 0,
        div_self hm0R.ne', mul_one, one_div]
    _ = ∑ n ∈ Ioc 0 m, (Real.log (N : ℝ))⁻¹ * (normalizedRamanujanMode m n ^ 2 / (m : ℝ)) := by
      rw [zero_add, sum_div, mul_sum]
    _ ≤ ∑ n ∈ Ioc 0 m, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2 :=
      sum_le_sum hterm
    _ ≤ ∑ n ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) n ^ 2 :=
      sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _

/-- **Total elimination of nonpositive Ramanujan conductors across `1 ≤ m ≤ N` (`0 < α < 1 / 9`).**
Throughout `1 ≤ c ≤ (log N)^α` (`0 < α < 1 / 9`), every Ramanujan horizon mode
`normalizedRamanujanHorizonVector m N` (`1 ≤ m ≤ N`) has strictly positive complete-Weil energy at
least `tiltedSplineSpectralFloorConstant / (2 * c ^ 7 * log N)`, and the nonpositive conductor set
`{m ∈ Icc 1 N | completeWeilEnergy tiltedUnitSpline c N v_m ≤ 0}` is empty. -/
theorem eventually_tiltedUnitSpline_all_conductors_pos_below_one_ninth
    {α : ℝ} (hα : 0 < α) (hα_lt : α < oneNinthPowerLogExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      (∀ m ∈ Icc 1 N,
        tiltedSplineSpectralFloorConstant / (2 * c ^ 7 * Real.log (N : ℝ)) ≤
          completeWeilEnergy tiltedUnitSpline c N (normalizedRamanujanHorizonVector m N)) ∧
      ((Icc 1 N).filter (fun m =>
        completeWeilEnergy tiltedUnitSpline c N
          (normalizedRamanujanHorizonVector m N) ≤ 0)) = ∅ := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_ninth
      hα hα_lt,
    eventually_ge_atTop 2] with N hfloor hN2 c hc1 hcup
  have hpos_all : ∀ m ∈ Icc 1 N,
      tiltedSplineSpectralFloorConstant / (2 * c ^ 7 * Real.log (N : ℝ)) ≤
        completeWeilEnergy tiltedUnitSpline c N (normalizedRamanujanHorizonVector m N) := by
    intro m hm
    obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
    have hnorm := one_div_log_le_norm_normalizedRamanujanHorizonVector_sq_one_ninth hN2 hm1 hmN
    have hf := hfloor c hc1 hcup (normalizedRamanujanHorizonVector m N)
    calc
      tiltedSplineSpectralFloorConstant / (2 * c ^ 7 * Real.log (N : ℝ)) =
          (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * (1 / Real.log (N : ℝ)) := by ring
      _ ≤ (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) *
            ‖normalizedRamanujanHorizonVector m N‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hnorm
          (div_nonneg tiltedSplineSpectralFloorConstant_pos.le (by positivity))
      _ ≤ completeWeilEnergy tiltedUnitSpline c N (normalizedRamanujanHorizonVector m N) := hf
  refine ⟨hpos_all, Finset.filter_eq_empty_iff.mpr fun m hm hle => ?_⟩
  have hlb := hpos_all m hm
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hgt : 0 < tiltedSplineSpectralFloorConstant / (2 * c ^ 7 * Real.log (N : ℝ)) :=
    div_pos tiltedSplineSpectralFloorConstant_pos (by positivity)
  linarith only [hlb, hle, hgt]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent_pos
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.one_div_16_lt_oneNinthPowerLogExponent
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent_lt_oneEighthPowerLogExponent
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_complement_coercive_below_one_ninth
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_ninth
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_one_ninth
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_ninth
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_log_one_tenth
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_weilQuad_nonneg_below_one_ninth
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completeWeilEnergy_ge_poleDefect_reserve_below_one_ninth
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_all_conductors_pos_below_one_ninth
