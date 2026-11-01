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
    have hzv : ⟪v, z⟫ = 0 := Submodule.mem_orthogonal.mp hz v hv
    have hdiff : ⟪v, z - p₀⟫ = 0 := Submodule.mem_orthogonal.mp hz_sub_p₀ v hvR₀
    have hp₀_id : p₀ = z - (z - p₀) := by abel
    rw [hp₀_id, inner_sub_right, hzv, hdiff, sub_zero]
  have hu₁_orthR₀ : u₁ ∈ (conductorSubspace R₀ N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    have hvR₁ : v ∈ conductorSubspace R₁ N := conductorSubspace_mono hR₀R₁ N hv
    have hdiff₀ : ⟪v, z - p₀⟫ = 0 := Submodule.mem_orthogonal.mp hz_sub_p₀ v hv
    have hdiff₁ : ⟪v, z - p₁⟫ = 0 := Submodule.mem_orthogonal.mp hz_sub_p₁ v hvR₁
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
      have hp := pow_le_pow_left₀ (by dsimp only [H₀]; positivity) hH₀_ub 2
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
          32 * (c ^ 2 * (1 + Real.log c) / Lh) := by field_simp [hLh0.ne']; ring
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
  rw [hs_two] at hraw
  have h1 := mul_le_mul_of_nonneg_right hpa hA₀
  have h2 := mul_le_mul_of_nonneg_right hpe hE₀
  have h3 := mul_le_mul_of_nonneg_right hng hG₀
  have h4 := mul_le_mul_of_nonneg_right hnu (sq_nonneg ‖u₀‖)
  change 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u₀, u₁⟫| ≤
    (1 / 32 : ℝ) * E₀ + (1 / 4 : ℝ) * ‖u₀‖ ^ 2 + (1 / 16 : ℝ) * Lh * ‖u₁‖ ^ 2
  linarith only [hraw, h1, h2, h3, h4, hAU, hG_le, hE₀, sq_nonneg ‖u₀‖]
