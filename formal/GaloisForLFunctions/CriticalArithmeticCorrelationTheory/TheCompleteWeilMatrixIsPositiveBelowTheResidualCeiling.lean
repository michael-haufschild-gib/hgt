import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.HighConductorWeilCoercivity
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ConductorProjectionRetainsAdjunctionCoercivity
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.LinearConductorRelativeResiduals
import GaloisForLFunctions.RHTower.ZetaZeroDensityExponentLemmas

/-!
# Complete Weil positivity below the residual ceiling

The conductor-dependent spectral floor and linear conductor residual leave the
low-band condition `19α < 1`. Cubic lag decay and the prefix/terminal reserve
make every other error smaller throughout this range.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Finset Filter Topology
open scoped Classical RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  ArithmeticElectrostatics CriticalScaleArithmeticRigidity

/-- The residual/floor balance leaves every strict exponent below one nineteenth. -/
def residualPowerLogPositivityExponent : ℝ := 1 / 19

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

/-! ### Low-band orthogonal decoupling (`m ≤ Q₁`) -/

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

private theorem eventually_log_nat_le_rpow_36 :
    ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
  have hsmall := tendsto_natCast_atTop_atTop.eventually
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 36)).bound zero_lt_one)
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hN _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have habs : |Real.log (N : ℝ)| ≤ (N : ℝ) ^ (1 / 36 : ℝ) := by
    simpa only [Function.comp_def, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hN0 _), one_mul] using hN
  exact (le_abs_self _).trans habs

private theorem eventually_floor_log_rpow_bounds {q : ℝ} (hq : 0 < q) (hqmax : q ≤ 1 / 3) :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (N : ℝ)
      let Q₁ := ⌊L ^ q⌋₊
      2 ≤ Q₁ ∧
      (Q₁ : ℝ) ≤ L ^ q ∧
      (1 / 4 : ℝ) * L ^ q ≤ (Q₁ : ℝ) ∧
      q * Real.log L - 1 ≤ Real.log (Q₁ : ℝ) ∧
      Q₁ ^ 4 ≤ N := by
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hQlim : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ q) atTop atTop :=
    (tendsto_rpow_atTop hq).comp hLlim
  filter_upwards [hQlim.eventually_ge_atTop 4,
    hLlim.eventually_ge_atTop 1, eventually_ge_atTop 2, eventually_log_nat_le_rpow_36] with N hX4 hL1 hN2 hLX
  dsimp only
  let L := Real.log (N : ℝ)
  let Xq := L ^ q
  let Q₁ := ⌊Xq⌋₊
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hQ2 : 2 ≤ Q₁ := Nat.le_floor (by exact_mod_cast (show (2 : ℝ) ≤ Xq by linarith only [hX4]))
  have hQ_le : (Q₁ : ℝ) ≤ Xq := Nat.floor_le (by linarith only [hX4])
  have hQ_gt : Xq - 1 < (Q₁ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one Xq)
  have hQ_quarter : (1 / 4 : ℝ) * Xq ≤ (Q₁ : ℝ) := by linarith only [hX4, hQ_gt]
  have hQ_half : (1 / 2 : ℝ) * Xq ≤ (Q₁ : ℝ) := by linarith only [hX4, hQ_gt]
  have hlogQ_lb : q * Real.log L - 1 ≤ Real.log (Q₁ : ℝ) := by
    have hlog2 : Real.log 2 ≤ 1 := by
      linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hXq_pos : 0 < Xq := by linarith only [hX4]
    have h1 := Real.log_le_log (by positivity) hQ_half
    rw [Real.log_mul (by norm_num) hXq_pos.ne', one_div, Real.log_inv,
      show Xq = L ^ q from rfl, Real.log_rpow hL0] at h1
    linarith only [h1, hlog2]
  have hQ4_N : Q₁ ^ 4 ≤ N := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg Q₁) hQ_le 4
    have he : Xq ^ (4 : ℕ) = L ^ (4 * q) := by
      dsimp only [Xq]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 1
      ring
    have hL_le : L ^ (4 * q) ≤ L ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hqmax] : 4 * q ≤ 2)
    have hLN : L ^ (2 : ℝ) ≤ (N : ℝ) := by
      rw [Real.rpow_two]
      have hh := pow_le_pow_left₀ hL0.le hLX 2
      have hid : ((N : ℝ) ^ (1 / 36 : ℝ)) ^ (2 : ℕ) = (N : ℝ) ^ (1 / 18 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        norm_num
      rw [hid] at hh
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      have hbound : (N : ℝ) ^ (1 / 18 : ℝ) ≤ (N : ℝ) := by
        simpa only [Real.rpow_one] using
          (Real.rpow_le_rpow_of_exponent_le hN1R (by norm_num : (1 / 18 : ℝ) ≤ 1))
      exact hh.trans hbound
    exact_mod_cast ((hp.trans_eq he).trans hL_le).trans hLN
  exact ⟨hQ2, hQ_le, hQ_quarter, hlogQ_lb, hQ4_N⟩

private theorem rpow_horizon_N_bounds {N R' : ℕ} {c H_res : ℝ}
    (hN1 : 1 ≤ N) (hR'2 : 2 ≤ R') (hc1 : 1 ≤ c) (_hH0 : 0 < H_res)
    (hL2000 : 2000 ≤ Real.log (N : ℝ)) (hHL : H_res ≤ Real.log (N : ℝ))
    (hLX : Real.log (N : ℝ) ≤ (N : ℝ) ^ (1 / 36 : ℝ))
    (hcL : c ≤ Real.log (N : ℝ))
    (hlog36 : 36 * (1 + Real.log (R' : ℝ)) ≤ Real.log (N : ℝ)) :
    H_res * c ^ 8 ≤ (N : ℝ) ∧
    4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) ∧
    c / (N : ℝ) ≤ 1 / 3 ∧
    4 * (linearNearRowRadius c + 1) ^ 2 ≤ (N : ℝ) ∧
    R' ^ 6 ≤ N ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ (N : ℝ) ∧
    ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ (N : ℝ) ∧
    (R' : ℝ) * Real.sqrt (Real.log (N : ℝ) / (N : ℝ)) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 5 * Real.log (N : ℝ) / (N : ℝ) ≤ 1 / Real.log (N : ℝ) ∧
    c ^ 3 * (R' : ℝ) ^ 4 / (N : ℝ) ≤ 1 / Real.log (N : ℝ) := by
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
    exact (Real.exp_log hR'0).symm.trans_le ((Real.exp_le_exp.mpr hlog_le).trans_eq (Real.exp_log hX0))
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
  have h1 : H_res * c ^ 8 ≤ (N : ℝ) := by
    have hHX : H_res ≤ X := hHL.trans hLX
    have hc8 : c ^ 8 ≤ X ^ 8 := pow_le_pow_left₀ hc0.le hcX 8
    calc
      H_res * c ^ 8 ≤ X * X ^ 8 := mul_le_mul hHX hc8 (by positivity) hX0.le
      _ = X ^ 9 := by ring
      _ ≤ (N : ℝ) := hpowX 9 (by norm_num)
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
    exact (by linarith only [h3X] : c * 3 ≤ X ^ 2).trans (by simpa only [ one_mul] using hpowX 2 (by norm_num))
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
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

private theorem prefix_horizon_bounds {N R : ℕ} {c Hcut : ℝ}
    (hN1 : 1 ≤ N) (hR : 2 ≤ R) (hc : 1 ≤ c) (hHcut : 1 ≤ Hcut)
    (hcut : (growingDefectCutoff c : ℝ) ≤ Hcut * c ^ 8)
    (hL2000 : 2000 ≤ Real.log N) (hHL : Hcut ≤ Real.log N)
    (hLX : Real.log N ≤ (N : ℝ) ^ (1 / 36 : ℝ)) (hcL : c ≤ Real.log N)
    (hlog36 : 36 * (1 + Real.log R) ≤ Real.log N) :
    R * R ≤ N / growingDefectCutoff c ∧
    18 * (1 + Real.log R) ≤ Real.log (N / growingDefectCutoff c : ℕ) ∧
    terminalPacketCost R (N / growingDefectCutoff c) N ≤ 4 + Real.log (2 * Hcut) + 8 * Real.log c ∧
    Real.log N / 2 ≤ Real.log (N / growingDefectCutoff c : ℕ) ∧
    c ^ 11 * (R : ℝ) ^ 2 * (Real.log N / N) ≤ 1 / Real.log N := by
  let X := (N : ℝ) ^ (1 / 36 : ℝ)
  let T := growingDefectCutoff c
  let M := N / T
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hX2000 : 2000 ≤ X := hL2000.trans hLX
  have hX1 : 1 ≤ X := by linarith only [hX2000]
  have hX0 := zero_lt_one.trans_le hX1
  have hL : 0 < Real.log N := by linarith only [hL2000]
  have hc0 := zero_lt_one.trans_le hc
  have hcX : c ≤ X := hcL.trans hLX
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
    exact (Real.exp_log hR0).symm.trans_le ((Real.exp_le_exp.mpr hh).trans_eq (Real.exp_log hX0))
  have hT1 : 1 ≤ T := by unfold T growingDefectCutoff; omega
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  have hTX : (T : ℝ) ≤ X ^ 9 := by
    calc
      _ ≤ Hcut * c ^ 8 := hcut
      _ ≤ X * X ^ 8 := mul_le_mul (hHL.trans hLX)
        (pow_le_pow_left₀ hc0.le hcX 8) (pow_nonneg hc0.le 8) hX0.le
      _ = _ := by ring
  have hRRT : R * R * T ≤ N := by
    have hh : (R : ℝ) ^ 2 * T ≤ (N : ℝ) := by
      calc
        _ ≤ X ^ 2 * X ^ 9 := mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg R) hRX 2) hTX hT0.le (by positivity)
        _ = X ^ 11 := by ring
        _ ≤ _ := hpowX 11 (by norm_num)
    have hhNat : R ^ 2 * T ≤ N := by exact_mod_cast hh
    simpa only [pow_two] using hhNat
  have hRM : R * R ≤ M := (Nat.le_div_iff_mul_le (by omega : 0 < T)).mpr hRRT
  have hM2 : 2 ≤ M := by have hh := Nat.mul_le_mul hR hR; omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hMN : M ≤ N := Nat.div_le_self N T
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
    rw [Real.log_mul (by norm_num) (pow_ne_zero 9 hX0.ne'), Real.log_pow,
      show Real.log X = (1 / 36 : ℝ) * Real.log N from Real.log_rpow hN0 _] at hh
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [hh, h2]
  have hhalf : Real.log N / 2 ≤ Real.log M := by linarith only [hratio, hlogT, hL2000]
  have hlogM : 18 * (1 + Real.log R) ≤ Real.log M := by linarith only [hlog36, hhalf]
  have hterminal : terminalPacketCost R M N ≤ 4 + Real.log (2 * Hcut) + 8 * Real.log c := by
    have hh := terminalPacketCost_nat_div_le hT1 hTN hRM
    change terminalPacketCost R M N ≤ 4 + Real.log (2 * (T : ℝ)) at hh
    have h2Ht : 0 < 2 * Hcut := by linarith only [hHcut]
    have ht := Real.log_le_log (by positivity : 0 < 2 * (T : ℝ))
      (mul_le_mul_of_nonneg_left hcut zero_le_two)
    rw [show 2 * (Hcut * c ^ 8) = (2 * Hcut) * c ^ 8 by ring,
      Real.log_mul h2Ht.ne' (pow_ne_zero 8 hc0.ne'), Real.log_pow] at ht
    norm_num only [Nat.cast_ofNat] at ht
    linarith only [hh, ht]
  have hlast : c ^ 11 * (R : ℝ) ^ 2 * (Real.log N / N) ≤ 1 / Real.log N := by
    rw [← mul_div_assoc, div_le_div_iff₀ hN0 hL, one_mul]
    calc
      c ^ 11 * (R : ℝ) ^ 2 * Real.log N * Real.log N = c ^ 11 * (R : ℝ) ^ 2 * (Real.log N) ^ 2 := by ring
      _ ≤ X ^ 11 * X ^ 2 * X ^ 2 := mul_le_mul
        (mul_le_mul (pow_le_pow_left₀ hc0.le hcX 11)
          (pow_le_pow_left₀ (Nat.cast_nonneg R) hRX 2) (sq_nonneg _) (by positivity))
        (pow_le_pow_left₀ hL.le hLX 2) (sq_nonneg _) (by positivity)
      _ = X ^ 15 := by ring
      _ ≤ _ := hpowX 15 (by norm_num)
  exact ⟨hRM, hlogM, hterminal, hhalf, hlast⟩

private theorem scaled_monomial_le_rpow {L c α ν A U β V ε : ℝ}
    (hL : 1 ≤ L) (hc : 0 ≤ c) (hcup : c ≤ L ^ α) (hA : 0 ≤ A)
    (hU0 : 0 ≤ U) (hU : U ≤ A * L ^ β) (hV0 : 0 ≤ V) (hV : V ≤ L ^ ν)
    (j d : ℕ) (hexp : (j : ℝ) * α + β + (d : ℝ) * ν - 1 ≤ ε) :
    c ^ j * U * V ^ d / L ≤ A * L ^ ε := by
  have hL0 := zero_lt_one.trans_le hL
  have hcj : c ^ j ≤ L ^ ((j : ℝ) * α) := by
    have hh := pow_le_pow_left₀ hc hcup j
    have he : (L ^ α) ^ j = L ^ ((j : ℝ) * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
      congr 1
      ring
    exact hh.trans_eq he
  have hVd : V ^ d ≤ (L ^ ν) ^ d := pow_le_pow_left₀ hV0 hV d
  have hid : (L ^ ν) ^ d = L ^ ((d : ℝ) * ν) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    ring
  calc
    _ ≤ (L ^ ((j : ℝ) * α) * (A * L ^ β) * (L ^ ν) ^ d) / L :=
      div_le_div_of_nonneg_right
        (mul_le_mul (mul_le_mul hcj hU hU0 (Real.rpow_nonneg hL0.le _)) hVd
          (pow_nonneg hV0 d) (by positivity)) hL0.le
    _ = A * L ^ ((j : ℝ) * α + β + (d : ℝ) * ν - 1) := by
      rw [hid, Real.rpow_sub hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hexp) hA

private theorem eventually_powerLog_high_region_conditions
    {α q ν C_R H_res C_abs b C_small Hcut : ℝ}
    (hα : 0 < α) (hq : 0 < q) (hqmax : q ≤ 1 / 3) (hν : 0 < ν) (hνsmall : ν ≤ 1 / 1000)
    (hmain : 18 * α + 3 * ν ≤ 1) (hlag : 3 * α - q / 2 ≤ -ν)
    (hC_R : 0 < C_R) (hH_res : 0 < H_res) (hC_abs : 0 < C_abs) (hb : 0 < b)
    (hC_small : 0 < C_small) (hHcut : 1 ≤ Hcut)
    (hcutoff : ∀ c : ℝ, 1 ≤ c → (growingDefectCutoff c : ℝ) ≤ Hcut * c ^ 8) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log N ^ α →
      ∀ R : ℕ, ⌊Real.log N ^ q⌋₊ ≤ R →
        Real.log R ≤ C_R * c ^ 16 + Real.log (⌊Real.log N ^ q⌋₊ : ℕ) →
        H_res * c ^ 8 ≤ N ∧ c / N ≤ 1 / 3 ∧
        4 * (linearNearRowRadius c + 1) ^ 2 ≤ N ∧ R ^ 6 ≤ N ∧
        R * R ≤ N / growingDefectCutoff c ∧
        18 * (1 + Real.log R) ≤ Real.log (N / growingDefectCutoff c : ℕ) ∧
        terminalPacketCost R (N / growingDefectCutoff c) N /
          Real.log (N / growingDefectCutoff c : ℕ) ≤ b / (4 * c ^ 7) ∧
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N ∧
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N ∧
        C_abs * ((1 + Real.log R) / Real.log N +
          c ^ 7 * (1 + terminalPacketCost R (N / growingDefectCutoff c) N) / Real.log N +
          c ^ 11 * (1 + Real.log c) / Real.log N +
          c ^ 11 * (R : ℝ) ^ 2 * (Real.log N / N)) ≤ 1 ∧
        C_small * (c * (1 + Real.log c) * (1 + Real.log R) / Real.log N +
          c * (1 + Real.log R) / Real.log N + c ^ 2 / Real.log N +
          c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / Real.log N +
          c ^ 2 * (R : ℝ) * Real.sqrt (Real.log N / N) +
          c ^ 5 * Real.log N / N + c ^ 3 / Real.sqrt (⌊Real.log N ^ q⌋₊ : ℕ) +
          c ^ 3 * (R : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / Real.log N) ≤ 1 ∧
        36 * (1 + Real.log R) ≤ Real.log N := by
  let CH := C_R + 2
  let CB := 4 + Real.log (2 * Hcut)
  let K := 36 * CH + C_abs * (CH + CB + 11) + C_small * (3 * CH + 7) + 8 * (CB + 8) / b + 1
  have hCH : 0 < CH := by dsimp only [CH]; positivity
  have hCB : 0 < CB := by
    have hh : 0 ≤ Real.log (2 * Hcut) := Real.log_nonneg (by linarith only [hHcut])
    dsimp only [CB]
    linarith only [hh]
  have hlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpoly := hlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1 hν 1)
  filter_upwards [eventually_floor_log_rpow_bounds hq hqmax, eventually_log_nat_le_rpow_36,
    hpoly, ((tendsto_rpow_atTop hν).comp hlim).eventually_ge_atTop K,
    hlim.eventually_ge_atTop (2000 + H_res + Hcut), eventually_ge_atTop 2] with
      N hQ_all hLX hpolyN hK hLbig hN2 c hc hcup R hQR hRlog
  let L := Real.log (N : ℝ)
  let Q := ⌊L ^ q⌋₊
  have hL2000 : 2000 ≤ L := by
    have hHt0 := zero_lt_one.trans_le hHcut
    dsimp only [L]
    linarith only [hLbig, hH_res, hHt0]
  have hL1 : 1 ≤ L := by linarith only [hL2000]
  have hL0 := zero_lt_one.trans_le hL1
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 := zero_lt_one.trans_le hc
  obtain ⟨hQ2, hQle, hQquarter, -, -⟩ := hQ_all
  change 2 ≤ Q at hQ2
  change (Q : ℝ) ≤ L ^ q at hQle
  change (1 / 4 : ℝ) * L ^ q ≤ (Q : ℝ) at hQquarter
  change Real.log R ≤ C_R * c ^ 16 + Real.log Q at hRlog
  have hR2 : 2 ≤ R := hQ2.trans hQR
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hα1 : α ≤ 1 := by linarith only [hmain, hν, hα]
  have hq1 : q ≤ 1 := hqmax.trans (by norm_num)
  have hcL : c ≤ L := hcup.trans (by
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hL1 hα1))
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hpolyL : 1 + Real.log L ≤ L ^ ν := by
    simpa only [Function.comp_def, one_mul, pow_one] using hpolyN
  have hlogQ : Real.log Q ≤ Real.log L := by
    have hh := Real.log_le_log hQ0 hQle
    rw [Real.log_rpow hL0] at hh
    have hqlog := mul_le_mul_of_nonneg_right hq1 hlogL
    linarith only [hh, hqlog]
  have hHQ : 1 + Real.log Q ≤ L ^ ν := by linarith only [hlogQ, hpolyL]
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hVc : 1 + Real.log c ≤ L ^ ν := by
    linarith only [Real.log_le_log hc0 hcL, hpolyL]
  have hH0 : 0 ≤ 1 + Real.log R := by positivity
  have hVc0 : 0 ≤ 1 + Real.log c := by positivity
  have hHbound : 1 + Real.log R ≤ CH * L ^ (16 * α + ν) := by
    have hc16 : c ^ 16 ≤ L ^ (16 * α) := by
      have hh := pow_le_pow_left₀ hc0.le hcup 16
      have he : (L ^ α) ^ (16 : ℕ) = L ^ (16 * α) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        congr 1
        ring
      exact hh.trans_eq he
    have hp16 : 1 ≤ L ^ (16 * α) := Real.one_le_rpow hL1 (by positivity)
    have hpν : 1 ≤ L ^ ν := Real.one_le_rpow hL1 hν.le
    have h1 := mul_le_mul_of_nonneg_left hc16 hC_R.le
    have h2 := mul_le_mul_of_nonneg_left hpν (show 0 ≤ C_R * L ^ (16 * α) by positivity)
    have h3 := mul_le_mul_of_nonneg_right hp16 (show 0 ≤ 2 * L ^ ν by positivity)
    rw [Real.rpow_add hL0]
    dsimp only [CH]
    nlinarith only [hRlog, hHQ, h1, h2, h3, Real.rpow_nonneg hL0.le ν]
  have hmono (j d : ℕ) (he : (j : ℝ) * α + (16 * α + ν) + (d : ℝ) * ν - 1 ≤ -ν) :
      c ^ j * (1 + Real.log R) * (1 + Real.log c) ^ d / L ≤ CH * L ^ (-ν) :=
    scaled_monomial_le_rpow hL1 hc0.le hcup hCH.le hH0 hHbound hVc0 hVc j d he
  have hmono1 (j d : ℕ) (he : (j : ℝ) * α + 0 + (d : ℝ) * ν - 1 ≤ -ν) :
      c ^ j * (1 + Real.log c) ^ d / L ≤ L ^ (-ν) := by
    have hh := scaled_monomial_le_rpow (U := 1) (A := 1) (β := 0)
      hL1 hc0.le hcup zero_le_one zero_le_one (by norm_num)
      hVc0 hVc j d he
    simpa only [mul_one, one_mul] using hh
  have hbase : (1 + Real.log R) / L ≤ CH * L ^ (-ν) := by
    simpa only [pow_zero, one_mul, mul_one] using hmono 0 0 (by norm_num; linarith only [hmain, hα, hν])
  have hinv : 1 / L ≤ L ^ (-ν) := by
    simpa only [pow_zero, mul_one] using hmono1 0 0 (by norm_num; linarith only [hνsmall])
  have hneg : L ^ (-ν) = 1 / L ^ ν := by rw [Real.rpow_neg hL0.le, one_div]
  have hlarge (v : ℝ) (hv : v ≤ K) : v * L ^ (-ν) ≤ 1 := by
    rw [hneg, one_div, ← div_eq_mul_inv, div_le_one (Real.rpow_pos_of_pos hL0 _)]
    exact hv.trans hK
  have h36 : 36 * CH * L ^ (-ν) ≤ 1 := hlarge _ (by
    have hh : 0 ≤ C_abs * (CH + CB + 11) + C_small * (3 * CH + 7) + 8 * (CB + 8) / b + 1 := by positivity
    dsimp only [K]; linarith only [hh])
  have hlog36 : 36 * (1 + Real.log R) ≤ L := by
    have hh := mul_le_mul_of_nonneg_left hbase (by norm_num : (0 : ℝ) ≤ 36)
    have hh' : 36 * (1 + Real.log R) / L ≤ 1 := by
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith only [hh, h36]
    exact (div_le_one hL0).mp hh'
  have hHL_res : H_res ≤ L := by dsimp only [L]; linarith only [hLbig, hHcut]
  have hHL_cut : Hcut ≤ L := by dsimp only [L]; linarith only [hLbig, hH_res]
  obtain ⟨hHN, -, hwidth, hrad, hR6, hsize, hsize_up, hRtail, hNprime, hNlag⟩ :=
    rpow_horizon_N_bounds hN1 hR2 hc hH_res hL2000 hHL_res hLX hcL hlog36
  obtain ⟨hRM, hlogM, hBbound, hhalf, hNcross⟩ :=
    prefix_horizon_bounds hN1 hR2 hc hHcut (hcutoff c hc) hL2000 hHL_cut hLX hcL hlog36
  let B := terminalPacketCost R (N / growingDefectCutoff c) N
  have hB0 : 0 ≤ B := terminalPacketCost_nonneg R (Nat.div_le_self N _)
  have hB : B ≤ CB + 8 * Real.log c := hBbound
  have hBscale : B ≤ (CB + 8) * (1 + Real.log c) := by
    have hh := mul_nonneg hCB.le hlogc
    nlinarith only [hB, hh]
  have hBscale1 : 1 + B ≤ (CB + 9) * (1 + Real.log c) := by
    have hh := mul_nonneg (show 0 ≤ CB + 1 by positivity) hlogc
    nlinarith only [hB, hh]
  have h7 : c ^ 7 * (1 + Real.log c) / L ≤ L ^ (-ν) := by
    simpa only [pow_one] using hmono1 7 1 (by norm_num; linarith only [hmain, hα, hν])
  have h11 : c ^ 11 * (1 + Real.log c) / L ≤ L ^ (-ν) := by
    simpa only [pow_one] using hmono1 11 1 (by norm_num; linarith only [hmain, hα, hν])
  have hBterm : c ^ 7 * (1 + B) / L ≤ (CB + 9) * L ^ (-ν) := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hBscale1 (pow_nonneg hc0.le 7)) hL0.le
    have hh' := mul_le_mul_of_nonneg_left h7 (show 0 ≤ CB + 9 by positivity)
    simp only [div_eq_mul_inv] at hh hh' ⊢
    nlinarith only [hh, hh']
  have hBleak : 8 * c ^ 7 * B / L ≤ 8 * (CB + 8) * L ^ (-ν) := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hBscale (show 0 ≤ 8 * c ^ 7 by positivity)) hL0.le
    have hh' := mul_le_mul_of_nonneg_left h7 (show 0 ≤ 8 * (CB + 8) by positivity)
    simp only [div_eq_mul_inv] at hh hh' ⊢
    nlinarith only [hh, hh']
  have hleak_large : (8 * (CB + 8) / b) * L ^ (-ν) ≤ 1 := hlarge _ (by
    have hh : 0 ≤ 36 * CH + C_abs * (CH + CB + 11) + C_small * (3 * CH + 7) + 1 := by positivity
    dsimp only [K]; linarith only [hh])
  have hleak : B / Real.log (N / growingDefectCutoff c : ℕ) ≤ b / (4 * c ^ 7) := by
    have hLM : 0 < Real.log (N / growingDefectCutoff c : ℕ) := (half_pos hL0).trans_le hhalf
    have hsmallB : 8 * c ^ 7 * B / L ≤ b := by
      have hh := mul_le_mul_of_nonneg_left hleak_large hb.le
      have he : b * ((8 * (CB + 8) / b) * L ^ (-ν)) = 8 * (CB + 8) * L ^ (-ν) := by field_simp [hb.ne']
      rw [he] at hh
      linarith only [hBleak, hh]
    have hratio : B / Real.log (N / growingDefectCutoff c : ℕ) ≤ 2 * B / L := by
      have hh := div_le_div_of_nonneg_left hB0 (half_pos hL0) hhalf
      exact hh.trans_eq (by ring)
    apply hratio.trans
    rw [div_le_div_iff₀ hL0 (by positivity : 0 < 4 * c ^ 7)]
    have hh := (div_le_iff₀ hL0).mp hsmallB
    nlinarith only [hh]
  have habs_sum : (1 + Real.log R) / L + c ^ 7 * (1 + B) / L +
      c ^ 11 * (1 + Real.log c) / L + c ^ 11 * (R : ℝ) ^ 2 * (L / N) ≤
      (CH + CB + 11) * L ^ (-ν) := by
    linarith only [hbase, hBterm, h11, hNcross.trans hinv]
  have habs_large : C_abs * (CH + CB + 11) * L ^ (-ν) ≤ 1 := hlarge _ (by
    have hh : 0 ≤ 36 * CH + C_small * (3 * CH + 7) + 8 * (CB + 8) / b + 1 := by positivity
    dsimp only [K]; linarith only [hh])
  have habs_small : C_abs * ((1 + Real.log R) / L + c ^ 7 * (1 + B) / L +
      c ^ 11 * (1 + Real.log c) / L + c ^ 11 * (R : ℝ) ^ 2 * (L / N)) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left habs_sum hC_abs.le
    nlinarith only [hh, habs_large]
  have ht1 : c * (1 + Real.log c) * (1 + Real.log R) / L ≤ CH * L ^ (-ν) := by
    have hh := hmono 1 1 (by norm_num; linarith only [hmain, hα])
    simpa only [pow_one, mul_comm (1 + Real.log c), mul_assoc, mul_left_comm] using hh
  have ht2 : c * (1 + Real.log R) / L ≤ CH * L ^ (-ν) := by
    simpa only [pow_one, pow_zero, mul_one] using hmono 1 0
      (by norm_num; linarith only [hmain, hα, hν])
  have ht3 : c ^ 2 / L ≤ L ^ (-ν) := by
    simpa only [pow_zero, mul_one] using hmono1 2 0
      (by norm_num; linarith only [hmain, hα, hν])
  have ht4 : c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / L ≤ CH * L ^ (-ν) := by
    simpa only [pow_one] using hmono 2 1 (by norm_num; linarith only [hmain])
  have ht5 : c ^ 2 * (R : ℝ) * Real.sqrt (L / N) ≤ L ^ (-ν) := by
    have hh := mul_le_mul_of_nonneg_left hRtail (sq_nonneg c)
    calc
      _ = c ^ 2 * ((R : ℝ) * Real.sqrt (L / N)) := by ring
      _ ≤ c ^ 2 * (1 / L) := hh
      _ = c ^ 2 / L := by ring
      _ ≤ _ := ht3
  have ht6 : c ^ 5 * L / N ≤ L ^ (-ν) := hNprime.trans hinv
  have ht7 : c ^ 3 / Real.sqrt Q ≤ 2 * L ^ (-ν) := by
    have hsqrtQ : (1 / 2 : ℝ) * L ^ (q / 2) ≤ Real.sqrt Q := by
      have hsq : ((1 / 2 : ℝ) * L ^ (q / 2)) ^ 2 = (1 / 4 : ℝ) * L ^ q := by
        rw [mul_pow, ← Real.rpow_natCast (L ^ (q / 2)) 2, ← Real.rpow_mul hL0.le]
        norm_num
      have hpos : 0 ≤ (1 / 2 : ℝ) * L ^ (q / 2) := by positivity
      exact (Real.sqrt_sq hpos).symm.trans_le (Real.sqrt_le_sqrt (hsq.trans_le hQquarter))
    have hc3 : c ^ 3 ≤ L ^ (3 * α) := by
      have hp := pow_le_pow_left₀ hc0.le hcup 3
      have heq : (L ^ α) ^ (3 : ℕ) = L ^ (3 * α) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
        congr 1
        ring
      exact hp.trans_eq heq
    calc
      _ ≤ L ^ (3 * α) / ((1 / 2 : ℝ) * L ^ (q / 2)) :=
        (div_le_div_of_nonneg_right hc3 (by positivity)).trans
          (div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrtQ)
      _ = 2 * (L ^ (3 * α) / L ^ (q / 2)) := by ring
      _ = 2 * L ^ (3 * α - q / 2) := by rw [← Real.rpow_sub hL0]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL1 hlag) zero_le_two
  have ht8 : c ^ 3 * (R : ℝ) ^ 4 / N ≤ L ^ (-ν) := hNlag.trans hinv
  have ht9 : c ^ 2 * (1 + Real.log c) / L ≤ L ^ (-ν) := by
    simpa only [pow_one] using hmono1 2 1 (by norm_num; linarith only [hmain, hα, hν])
  have hcoerc_sum : c * (1 + Real.log c) * (1 + Real.log R) / L +
      c * (1 + Real.log R) / L + c ^ 2 / L +
      c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / L +
      c ^ 2 * (R : ℝ) * Real.sqrt (L / N) + c ^ 5 * L / N + c ^ 3 / Real.sqrt Q +
      c ^ 3 * (R : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L ≤
      (3 * CH + 7) * L ^ (-ν) := by
    linarith only [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9]
  have hcoerc_large : C_small * (3 * CH + 7) * L ^ (-ν) ≤ 1 := hlarge _ (by
    have hh : 0 ≤ 36 * CH + C_abs * (CH + CB + 11) + 8 * (CB + 8) / b + 1 := by positivity
    dsimp only [K]; linarith only [hh])
  have hcoerc_small : C_small * (c * (1 + Real.log c) * (1 + Real.log R) / L +
      c * (1 + Real.log R) / L + c ^ 2 / L +
      c ^ 2 * (1 + Real.log R) * (1 + Real.log c) / L +
      c ^ 2 * (R : ℝ) * Real.sqrt (L / N) + c ^ 5 * L / N + c ^ 3 / Real.sqrt Q +
      c ^ 3 * (R : ℝ) ^ 4 / N + c ^ 2 * (1 + Real.log c) / L) ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left hcoerc_sum hC_small.le
    nlinarith only [hh, hcoerc_large]
  exact ⟨hHN, hwidth, hrad, hR6, hRM, hlogM, hleak, hsize, hsize_up,
    habs_small, hcoerc_small, hlog36⟩

private theorem eventually_powerLog_linear_low_band_and_gap
    {K_res K_relative C_coerc α q ν : ℝ} {k : ℕ}
    (hK : 0 < K_res) (hK_relative : 0 < K_relative) (_hC_coerc : 0 < C_coerc)
    (hα : 0 < α) (hq : 0 < q) (hqmax : q ≤ 1 / 3) (hν : 0 < ν) (hk : 1 ≤ k)
    (hmain : 18 * α + 3 * ν ≤ 1)
    (hlow_exp : 19 * α + 1 / (k : ℝ) + 2 * ν - 1 ≤ -ν)
    (hhigh_exp : 2 * q + 5 * α + 1 / (k : ℝ) + 2 * ν - 1 ≤ -ν)
    (hgap_pos : 0 < q / 4 - α) :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (N : ℝ)
      let Q₁ := ⌊L ^ q⌋₊
      ∀ c : ℝ, 1 ≤ c → c ≤ L ^ α →
        9 * (1 + Real.log Q₁) / L *
          (|completeWeilSelfFinitePart tiltedUnitSpline 1| + 2 * Real.log Q₁ + 3 * c ^ 4) ≤ 1 / 16 ∧
        K_res * (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 *
          (c ^ 5 / L + c ^ 10 * (L / N) ^ 2 + c ^ 3 * L ^ (1 / (k : ℝ)) / L) ≤ 1 / 128 ∧
        K_relative * (c ^ 14 + (Q₁ : ℝ) ^ 2) * (1 + Real.log Q₁) ^ 2 *
          (c ^ 5 / L + c ^ 10 * (L / N) ^ 2 + c ^ 3 * L ^ (1 / (k : ℝ)) / L) ≤ 1 / 144 ∧
        2 * tiltedSplineSpectralFloorConstant + 4 + C_coerc ≤ (1 / 4) * Real.log Q₁ - Real.log c := by
  let M_self := |completeWeilSelfFinitePart tiltedUnitSpline 1| + 5
  let M_rate := max (384 * K_res) (864 * K_relative)
  let M_coerc := (2 * tiltedSplineSpectralFloorConstant + 4 + C_coerc + 1 / 4) / (q / 4 - α)
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hllim : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hLlim
  filter_upwards [eventually_floor_log_rpow_bounds hq hqmax, eventually_log_nat_le_rpow_36,
    hLlim.eventually (RHTower.eventually_const_mul_polylog_le_rpow 1 hν 1),
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop (144 * M_self),
    ((tendsto_rpow_atTop hν).comp hLlim).eventually_ge_atTop M_rate,
    hllim.eventually_ge_atTop M_coerc, hLlim.eventually_ge_atTop 1, eventually_ge_atTop 2] with
      N hQ_all hLX hpoly hGramLarge hL50 hll hL1 hN2
  dsimp only [Function.comp_def] at hpoly hGramLarge hL50 hll
  obtain ⟨hQ2, hQ_le, _, hlogQ_lb, _⟩ := hQ_all
  dsimp only
  let L := Real.log (N : ℝ)
  let Q₁ := ⌊L ^ q⌋₊
  change 2 ≤ Q₁ at hQ2
  change (Q₁ : ℝ) ≤ L ^ q at hQ_le
  change q * Real.log L - 1 ≤ Real.log Q₁ at hlogQ_lb
  intro c hc1 hcup
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hc0 := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 1 ≤ N by omega)
  have hα1 : α ≤ 1 := by linarith only [hmain, hα, hν]
  have hcL : c ≤ L := hcup.trans (by
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hL1 hα1))
  have hcpow : ∀ j : ℕ, c ^ j ≤ L ^ ((j : ℝ) * α) := fun j => by
    have hp := pow_le_pow_left₀ hc0.le hcup j
    have he : (L ^ α) ^ j = L ^ ((j : ℝ) * α) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hp.trans_eq he
  have hQ0 : (0 : ℝ) < Q₁ := by exact_mod_cast (show 0 < Q₁ by omega)
  have hlogQ0 : 0 ≤ Real.log Q₁ := Real.log_natCast_nonneg Q₁
  have hlogQ : Real.log Q₁ ≤ Real.log L := by
    have hh := Real.log_le_log hQ0 hQ_le
    rw [Real.log_rpow hL0] at hh
    have hm := mul_le_mul_of_nonneg_right (hqmax.trans (by norm_num : (1 / 3 : ℝ) ≤ 1))
      (Real.log_nonneg hL1)
    linarith only [hh, hm]
  have hHQ : 1 + Real.log Q₁ ≤ L ^ ν := by
    have hh : 1 + Real.log L ≤ L ^ ν := by simpa only [one_mul, pow_one] using hpoly
    linarith only [hlogQ, hh]
  have hHQsq : (1 + Real.log Q₁) ^ 2 ≤ L ^ (2 * ν) := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log Q₁) hHQ 2
    have he : (L ^ ν) ^ (2 : ℕ) = L ^ (2 * ν) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hh.trans_eq he
  have hmul50 : L ^ ν * L ^ (-ν) = 1 := by
    rw [← Real.rpow_add hL0, show ν + (-ν) = 0 by ring, Real.rpow_zero]
  have hgram : 9 * (1 + Real.log Q₁) / L *
      (|completeWeilSelfFinitePart tiltedUnitSpline 1| + 2 * Real.log Q₁ + 3 * c ^ 4) ≤ 1 / 16 := by
    have hlarge : 1 ≤ L ^ (4 * α + ν) := Real.one_le_rpow hL1 (by positivity)
    have hνpow : L ^ ν ≤ L ^ (4 * α + ν) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα])
    have hαpow : L ^ (4 * α) ≤ L ^ (4 * α + ν) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hν])
    have hC := mul_le_mul_of_nonneg_left hlarge (abs_nonneg (completeWeilSelfFinitePart tiltedUnitSpline 1))
    have hbracket : |completeWeilSelfFinitePart tiltedUnitSpline 1| + 2 * Real.log Q₁ + 3 * c ^ 4 ≤
        M_self * L ^ (4 * α + ν) := by
      have hq_bound : Real.log Q₁ ≤ L ^ ν := by linarith only [hHQ]
      have hq' : Real.log Q₁ ≤ L ^ (4 * α + ν) := hq_bound.trans hνpow
      have hc' : c ^ 4 ≤ L ^ (4 * α + ν) := (hcpow 4).trans hαpow
      dsimp only [M_self]
      nlinarith only [hC, hq', hc']
    have hexp : L ^ (4 * α + 2 * ν - 1) ≤ L ^ (-ν) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hmain, hα])
    calc
      _ ≤ (9 * L ^ ν / L) * (M_self * L ^ (4 * α + ν)) :=
        mul_le_mul (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hHQ (by norm_num)) hL0.le)
          hbracket (by positivity) (by positivity)
      _ = 9 * M_self * L ^ (4 * α + 2 * ν - 1) := by
        have he : L ^ (4 * α + 2 * ν - 1) = L ^ ν * L ^ (4 * α + ν) / L := by
          rw [show 4 * α + 2 * ν - 1 = ν + (4 * α + ν) - 1 by ring,
            Real.rpow_sub hL0, Real.rpow_add hL0, Real.rpow_one]
        rw [he]
        ring
      _ ≤ 9 * M_self * L ^ (-ν) := mul_le_mul_of_nonneg_left hexp (by dsimp only [M_self]; positivity)
      _ = (1 / 16 : ℝ) * ((144 * M_self) * L ^ (-ν)) := by ring
      _ ≤ (1 / 16 : ℝ) * (L ^ ν * L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hGramLarge (by positivity)) (by norm_num)
      _ = 1 / 16 := by rw [hmul50, mul_one]
  have hsL : 1 ≤ L ^ (1 / (k : ℝ)) := Real.one_le_rpow hL1 (by positivity)
  have hrate_le : c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 +
      c ^ 3 * L ^ (1 / (k : ℝ)) / L ≤ 3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L := by
    have hLN : c ^ 5 * (L / (N : ℝ)) ^ 2 ≤ 1 / L := by
      rw [div_pow, ← mul_div_assoc,
        div_le_div_iff₀ (sq_pos_of_pos hN0) hL0, one_mul]
      let X := (N : ℝ) ^ (1 / 36 : ℝ)
      have hX1 : 1 ≤ X := hL1.trans hLX
      have hX36 : X ^ (36 : ℕ) = (N : ℝ) := by
        dsimp only [X]
        rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
        norm_num
      have hL8 : L ^ 8 ≤ X ^ 8 := pow_le_pow_left₀ hL0.le hLX 8
      have hX8 : X ^ 8 ≤ (N : ℝ) :=
        (pow_le_pow_right₀ hX1 (by norm_num : 8 ≤ 36)).trans_eq hX36
      have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
      calc
        c ^ 5 * L ^ 2 * L = c ^ 5 * L ^ 3 := by ring
        _ ≤ L ^ 5 * L ^ 3 := mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hc0.le hcL 5) (by positivity)
        _ = L ^ 8 := by ring
        _ ≤ (N : ℝ) := hL8.trans hX8
        _ ≤ (N : ℝ) ^ 2 := by nlinarith only [hN1R]
    have ht1 : c ^ 5 / L ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L :=
      div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (by positivity) hsL) hL0.le
    have ht2 : c ^ 10 * (L / (N : ℝ)) ^ 2 ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L := by
      calc
        _ = c ^ 5 * (c ^ 5 * (L / (N : ℝ)) ^ 2) := by ring
        _ ≤ c ^ 5 * (1 / L) := mul_le_mul_of_nonneg_left hLN (by positivity)
        _ = c ^ 5 / L := by ring
        _ ≤ _ := ht1
    have ht3 : c ^ 3 * L ^ (1 / (k : ℝ)) / L ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hc1 (by norm_num : 3 ≤ 5)) (by positivity)) hL0.le
    calc
      _ ≤ c ^ 5 * L ^ (1 / (k : ℝ)) / L + c ^ 5 * L ^ (1 / (k : ℝ)) / L +
          c ^ 5 * L ^ (1 / (k : ℝ)) / L := add_le_add (add_le_add ht1 ht2) ht3
      _ = 3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L := by ring
  have hQpow : (Q₁ : ℝ) ^ 2 ≤ L ^ (2 * q) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg Q₁) hQ_le 2
    have he : (L ^ q) ^ (2 : ℕ) = L ^ (2 * q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; ring
    exact hh.trans_eq he
  have hc19 : c ^ 19 * (1 + Real.log Q₁) ^ 2 * L ^ (1 / (k : ℝ)) / L ≤ L ^ (-ν) := by
    calc
      _ ≤ L ^ (19 * α) * L ^ (2 * ν) * L ^ (1 / (k : ℝ)) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul (hcpow 19) hHQsq (sq_nonneg _) (by positivity)) (by positivity)) hL0.le
      _ = L ^ (19 * α + 1 / (k : ℝ) + 2 * ν - 1) := by
        rw [show 19 * α + 1 / (k : ℝ) + 2 * ν - 1 = (19 * α + 2 * ν) + 1 / (k : ℝ) - 1 by ring,
          Real.rpow_sub hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 hlow_exp
  have hQ2_c5 : (Q₁ : ℝ) ^ 2 * c ^ 5 * (1 + Real.log Q₁) ^ 2 * L ^ (1 / (k : ℝ)) / L ≤ L ^ (-ν) := by
    calc
      _ ≤ L ^ (2 * q) * L ^ (5 * α) * L ^ (2 * ν) * L ^ (1 / (k : ℝ)) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul (mul_le_mul hQpow (hcpow 5) (by positivity) (by positivity)) hHQsq
            (sq_nonneg _) (by positivity)) (by positivity)) hL0.le
      _ = L ^ (2 * q + 5 * α + 1 / (k : ℝ) + 2 * ν - 1) := by
        rw [show 2 * q + 5 * α + 1 / (k : ℝ) + 2 * ν - 1 =
          ((2 * q + 5 * α) + 2 * ν) + 1 / (k : ℝ) - 1 by ring,
          Real.rpow_sub hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hL1 hhigh_exp
  have hres_sum : K_res * (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 *
      (c ^ 5 / L + c ^ 10 * (L / N) ^ 2 + c ^ 3 * L ^ (1 / (k : ℝ)) / L) ≤ 1 / 128 := by
    have hM1 : 384 * K_res ≤ L ^ ν := (le_max_left _ _).trans hL50
    calc
      _ ≤ K_res * (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 *
          (3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L) :=
        mul_le_mul_of_nonneg_left hrate_le (by positivity)
      _ = (1 / 128 : ℝ) * ((384 * K_res) *
          ((Q₁ : ℝ) ^ 2 * c ^ 5 * (1 + Real.log Q₁) ^ 2 * L ^ (1 / (k : ℝ)) / L)) := by ring
      _ ≤ (1 / 128 : ℝ) * (L ^ ν * L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hM1 hQ2_c5 (by positivity) (by positivity)) (by norm_num)
      _ = 1 / 128 := by rw [hmul50, mul_one]
  have hbudget : K_relative * (c ^ 14 + (Q₁ : ℝ) ^ 2) * (1 + Real.log Q₁) ^ 2 *
      (c ^ 5 / L + c ^ 10 * (L / N) ^ 2 + c ^ 3 * L ^ (1 / (k : ℝ)) / L) ≤ 1 / 144 := by
    have hM2 : 864 * K_relative ≤ L ^ ν := (le_max_right _ _).trans hL50
    calc
      _ ≤ K_relative * (c ^ 14 + (Q₁ : ℝ) ^ 2) * (1 + Real.log Q₁) ^ 2 *
          (3 * c ^ 5 * L ^ (1 / (k : ℝ)) / L) :=
        mul_le_mul_of_nonneg_left hrate_le (by positivity)
      _ = 3 * K_relative * (c ^ 19 * (1 + Real.log Q₁) ^ 2 * L ^ (1 / (k : ℝ)) / L +
          (Q₁ : ℝ) ^ 2 * c ^ 5 * (1 + Real.log Q₁) ^ 2 * L ^ (1 / (k : ℝ)) / L) := by ring
      _ ≤ 3 * K_relative * (L ^ (-ν) + L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (add_le_add hc19 hQ2_c5) (by positivity)
      _ = (1 / 144 : ℝ) * ((864 * K_relative) * L ^ (-ν)) := by ring
      _ ≤ (1 / 144 : ℝ) * (L ^ ν * L ^ (-ν)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hM2 (by positivity)) (by norm_num)
      _ = 1 / 144 := by rw [hmul50, mul_one]
  have hcoerc_gap : 2 * tiltedSplineSpectralFloorConstant + 4 + C_coerc ≤
      (1 / 4) * Real.log (Q₁ : ℝ) - Real.log c := by
    have hlogc : Real.log c ≤ α * Real.log L :=
      (Real.log_le_log hc0 hcup).trans_eq (Real.log_rpow hL0 α)
    have hq_scaled : (q / 4) * Real.log L -
        1 / 4 ≤
        (1 / 4) * Real.log (Q₁ : ℝ) := by
      have hpos : (0 : ℝ) ≤ 1 / 4 := by positivity
      have hm := mul_le_mul_of_nonneg_left hlogQ_lb hpos
      have heq : (1 / 4) * (q * Real.log L - 1) =
          (q / 4) * Real.log L -
            1 / 4 := by ring
      linarith only [hm, heq]
    have hll_scaled : 2 * tiltedSplineSpectralFloorConstant + 4 + C_coerc +
        1 / 4 ≤
        (q / 4 - α) * Real.log L :=
      ((div_le_iff₀ hgap_pos).mp (show M_coerc ≤ Real.log L from hll)).trans_eq (mul_comm _ _)
    linarith only [hlogc, hq_scaled, hll_scaled]
  exact ⟨hgram, hres_sum, hbudget, hcoerc_gap⟩


/-- The complete matrix has a uniform seventh-power spectral floor throughout
any strict power-logarithmic window below the residual ceiling. -/
theorem eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_residual_ceiling
    {α : ℝ} (hα : 0 < α) (hα_lt : α < residualPowerLogPositivityExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      (spectralFloorWeilMatrix c N).PosDef := by
  classical
  have hα19 : α < 1 / 19 := hα_lt
  let τ : ℝ := (1 - 19 * α) / 100
  have hτ : 0 < τ := by dsimp only [τ]; linarith only [hα19]
  have hτeq : 100 * τ = 1 - 19 * α := by dsimp only [τ]; ring
  let q : ℝ := 6 * α + τ
  let ν : ℝ := τ / 10
  have hq : 0 < q := by dsimp only [q]; positivity
  have hqmax : q ≤ 1 / 3 := by dsimp only [q]; linarith only [hτeq, hα19, hτ]
  have hν : 0 < ν := by dsimp only [ν]; positivity
  have hνsmall : ν ≤ 1 / 1000 := by dsimp only [ν]; linarith only [hτeq, hα]
  have hmain : 18 * α + 3 * ν ≤ 1 := by dsimp only [ν]; linarith only [hτeq, hα, hτ]
  have hlag : 3 * α - q / 2 ≤ -ν := by dsimp only [q, ν]; linarith only [hτ]
  let k : ℕ := ⌈1 / τ⌉₊ + 1
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hrate : 1 / (k : ℝ) ≤ τ := by
    have hceil := Nat.le_ceil (1 / τ)
    have hτk : 1 ≤ τ * (k : ℝ) := by
      have h := (div_le_iff₀ hτ).mp hceil
      dsimp only [k]
      push_cast
      nlinarith only [h, hτ]
    exact (div_le_iff₀ hk0).mpr hτk
  have hlow_exp : 19 * α + 1 / (k : ℝ) + 2 * ν - 1 ≤ -ν := by
    dsimp only [ν]
    linarith only [hτeq, hrate, hτ]
  have hhigh_exp : 2 * q + 5 * α + 1 / (k : ℝ) + 2 * ν - 1 ≤ -ν := by
    dsimp only [q, ν]
    linarith only [hτeq, hrate, hτ, hα]
  have hgap : 0 < q / 4 - α := by dsimp only [q]; linarith only [hα, hτ]
  obtain ⟨C_R, H_res, C_abs, b, hC_R, hH_res, hC_abs, hb, hsupp⟩ :=
    exists_conductor_projection_with_adjunction_debit
      (show 0 < 2 * tiltedSplineSpectralFloorConstant + 2 by
        have := tiltedSplineSpectralFloorConstant_pos; positivity)
  obtain ⟨C_coerc, C_small, hC_coerc, hC_small, hcoerc⟩ :=
    exists_completeWeilEnergy_ge_adjunction_and_log
  obtain ⟨K_res, hK_res, hres_unif⟩ := exists_tiltedUnitSpline_linear_conductor_residual_variable_rate
  obtain ⟨K_relative, hK_relative, hrelative⟩ := exists_tiltedUnitSpline_linear_relative_residual_sum_le
  obtain ⟨Hcut, hHcut, hcutoff⟩ := exists_growingDefectCutoff_polynomial_bound
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_floor_log_rpow_bounds hq hqmax,
    eventually_log_nat_le_rpow_36,
    eventually_powerLog_high_region_conditions hα hq hqmax hν hνsmall hmain hlag
      hC_R hH_res hC_abs hb hC_small hHcut hcutoff,
    eventually_powerLog_linear_low_band_and_gap hK_res hK_relative hC_coerc
      hα hq hqmax hν hk hmain hlow_exp hhigh_exp hgap,
    hres_unif q hq.le k hk, hrelative q hq.le k hk,
    hLlim.eventually_ge_atTop (max 2000 H_res), eventually_ge_atTop 2] with
      N hQ_all hLX hhighN hlowN hresN hrelativeN hLmax hN2
  obtain ⟨hQ2, hQ_le, _, _, hQ4_N⟩ := hQ_all
  let L := Real.log (N : ℝ)
  let Q₁ := ⌊L ^ q⌋₊
  intro c hc1 hcup
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hL2000 : 2000 ≤ L := (le_max_left _ _).trans hLmax
  have hL1 : 1 ≤ L := by linarith only [hL2000]
  have hHL : H_res ≤ L := (le_max_right _ _).trans hLmax
  have hα1 : α ≤ 1 := by linarith only [hα19]
  have hcL : c ≤ L := hcup.trans (by
    simpa only [Real.rpow_one] using (Real.rpow_le_rpow_of_exponent_le hL1 hα1))
  obtain ⟨hgram, hres_sum_bound, hbudget, hcoerc_gap⟩ := hlowN c hc1 hcup
  have hQlog : Real.log Q₁ ≤ C_R * c ^ 16 + Real.log Q₁ :=
    le_add_of_nonneg_left (by positivity)
  obtain ⟨hHN, hw1, hradN, _, _, _, _, _, _, _, _, hlog36_Q⟩ :=
    hhighN c hc1 hcup Q₁ le_rfl hQlog
  have hlog18_Q : 18 * (1 + Real.log Q₁) ≤ L := by
    have hh := Real.log_natCast_nonneg Q₁
    linarith only [hlog36_Q, hh]
  obtain ⟨_, hwidth, _, _, _, _, _, _, _, _⟩ :=
    rpow_horizon_N_bounds (by omega : 1 ≤ N) hQ2 hc1 hH_res hL2000 hHL hLX hcL hlog36_Q
  have hQQ_N : Q₁ * Q₁ ≤ N := by
    have hQ2' : 2 ≤ Q₁ := hQ2
    have hh := (Nat.pow_le_pow_right (by omega : 0 < Q₁) (by norm_num : 2 ≤ 4)).trans hQ4_N
    simpa only [sq] using hh
  let rate := c ^ 5 / L + c ^ 10 * (L / (N : ℝ)) ^ 2 + c ^ 3 * L ^ (1 / (k : ℝ)) / L
  have hrate0 : 0 ≤ rate := by
    dsimp only [rate, L]
    have := Real.log_natCast_nonneg N
    positivity
  have hres_sum_Q :
      (∑ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m •
            normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ 1 / 128 := by
    have hterm : ∀ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m •
            normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          K_res * (Q₁ : ℝ) * (1 + Real.log Q₁) ^ 2 * rate := by
      intro m hm
      obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
      have hmQ' : (m : ℝ) ≤ Q₁ := by exact_mod_cast hmQ
      have hmL : (m : ℝ) ≤ L ^ q := hmQ'.trans hQ_le
      have hlogm : Real.log m ≤ Real.log Q₁ := Real.log_le_log hm0 hmQ'
      have hHsq : (1 + Real.log m) ^ 2 ≤ (1 + Real.log Q₁) ^ 2 :=
        pow_le_pow_left₀ (by have := Real.log_natCast_nonneg m; positivity)
          (by linarith only [hlogm]) 2
      have hh := mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_left hmQ' hK_res.le) hHsq
          (sq_nonneg _) (by positivity)) hrate0
      exact (hresN m hm1 hmL c hc1 hwidth).trans (by simpa only [mul_assoc] using hh)
    have hsum := sum_le_sum hterm
    rw [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel] at hsum
    exact (hsum.trans_eq (by ring : (Q₁ : ℝ) *
      (K_res * (Q₁ : ℝ) * (1 + Real.log Q₁) ^ 2 * rate) =
        K_res * (Q₁ : ℝ) ^ 2 * (1 + Real.log Q₁) ^ 2 * rate)).trans hres_sum_bound
  apply matrix_posDef_of_relative_conductor_budget (R := Q₁) (Q := Q₁)
    (spectralFloorWeilMatrix_isHermitian c N)
    (fun m => completedConductorEnergy tiltedUnitSpline c m -
      tiltedSplineSpectralFloorConstant / (2 * c ^ 7))
    (fun m hm => (div_pos tiltedSplineSpectralFloorConstant_pos (by positivity)).trans_le
      (spectralFloor_conductor_energy_ge hc1 (mem_Icc.mp hm).1))
    le_rfl hQ2 hQ4_N
  · intro x hx hneg
    have hxE : completeWeilEnergy tiltedUnitSpline c N x ≤
        tiltedSplineSpectralFloorConstant / 2 := by
      rw [spectralFloorWeilMatrix_inner, hx, one_pow, mul_one] at hneg
      have hc7 : 1 ≤ c ^ 7 := one_le_pow₀ hc1
      have hfloor_le : tiltedSplineSpectralFloorConstant / (2 * c ^ 7) ≤
          tiltedSplineSpectralFloorConstant / 2 :=
        div_le_div_of_nonneg_left tiltedSplineSpectralFloorConstant_pos.le zero_lt_two
          (by linarith only [hc7])
      linarith only [hneg, hfloor_le]
    apply exists_raw_approx_of_starProjection_sq_le hN2 x
    by_contra hdist_not
    have hdist : 1 / 4 < ‖x - (conductorSubspace Q₁ N).starProjection x‖ ^ 2 :=
      lt_of_not_ge hdist_not
    obtain ⟨zHat, hz_orth, hz_norm, hz_energy⟩ :=
      low_band_decoupling_unit_orthogonal hQ2 hQQ_N hlog18_Q hc1 hres_sum_Q hgram hx hxE hdist
    have hRconds := fun {R' : ℕ} (hQR' : Q₁ ≤ R')
        (hRlog : Real.log R' ≤ C_R * c ^ 16 + Real.log Q₁) => by
      obtain ⟨_, _, _, h1, h2, h3, h4, h5, h6, h7, _, _⟩ :=
        hhighN c hc1 hcup R' hQR' hRlog
      exact And.intro h1 (And.intro h2 (And.intro h3 (And.intro h4 (And.intro h5 (And.intro h6 h7)))))
    obtain ⟨R', hQR', hRlog, a, hu_orthQ, hu_sq_ge, hu_le1, hu_energy⟩ :=
      hsupp hQ2 hc1 hHN hw1 hRconds hz_orth hz_norm hz_energy
    obtain ⟨_, _, _, hR6, _, _, _, hRNT, _, _, hsmall, hlog36_R⟩ :=
      hhighN c hc1 hcup R' hQR' hRlog
    have hlb := hcoerc hQ2 hQR' hR6 hlog36_R hc1 hcL hw1 hradN hRNT
      hsmall a hu_orthQ hu_sq_ge hu_le1
    linarith only [hu_energy, hlb, hcoerc_gap]
  · have hrel := hrelativeN c hc1 hwidth Q₁ hQ_le
    have hterm : ∀ m ∈ Icc 1 Q₁,
        ‖Matrix.toEuclideanLin (spectralFloorWeilMatrix c N)
            (normalizedRamanujanHorizonVector m N) -
          (completedConductorEnergy tiltedUnitSpline c m -
            tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) •
              normalizedRamanujanHorizonVector m N‖ ^ 2 /
            (completedConductorEnergy tiltedUnitSpline c m -
              tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) ^ 2 ≤
        4 * (‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline c m •
            normalizedRamanujanHorizonVector m N‖ ^ 2 /
              completedConductorEnergy tiltedUnitSpline c m ^ 2) := by
      intro m hm
      rw [spectralFloorWeilMatrix_residual_eq]
      let E := completedConductorEnergy tiltedUnitSpline c m
      let s := tiltedSplineSpectralFloorConstant / (2 * c ^ 7)
      have hs : 0 < s := div_pos tiltedSplineSpectralFloorConstant_pos (by positivity)
      have hhalf : s ≤ E - s := spectralFloor_conductor_energy_ge hc1 (mem_Icc.mp hm).1
      have hE : 0 < E := by linarith only [hs, hhalf]
      have hshift : E / 2 ≤ E - s := by linarith only [hhalf]
      calc
        _ ≤ ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
            (normalizedRamanujanHorizonVector m N) -
          E • normalizedRamanujanHorizonVector m N‖ ^ 2 / (E / 2) ^ 2 :=
          div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos (half_pos hE))
            (pow_le_pow_left₀ (half_pos hE).le hshift 2)
        _ = _ := by dsimp only [E]; ring
    have hsum := sum_le_sum hterm
    rw [← mul_sum] at hsum
    have hfour := mul_le_mul_of_nonneg_left hrel (show (0 : ℝ) ≤ 4 by norm_num)
    have hlast := mul_le_mul_of_nonneg_left hbudget (show (0 : ℝ) ≤ 4 by norm_num)
    linarith only [hsum, hfour, hlast]

/-- **Uniform `c⁻⁷` spectral floor at power-of-logarithm overlap.** Throughout
`1 ≤ c ≤ (log N)^α` (`0 < α < residualPowerLogPositivityExponent`), the complete Weil quadratic form
of `tiltedUnitSpline` dominates `(tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2`
for every horizon vector `x`. -/
theorem eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_residual_ceiling
    {α : ℝ} (hα : 0 < α) (hα_lt : α < residualPowerLogPositivityExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        (tiltedSplineSpectralFloorConstant / (2 * c ^ 7)) * ‖x‖ ^ 2 ≤
          completeWeilEnergy tiltedUnitSpline c N x := by
  filter_upwards [eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_residual_ceiling hα hα_lt]
    with N hpos c hc hcup x
  have hA := spectralFloorWeilMatrix_isHermitian c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp (hpos c hc hcup)
  have hnonneg : 0 ≤ ⟪Matrix.toEuclideanLin (spectralFloorWeilMatrix c N) x, x⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [spectralFloorWeilMatrix_inner] at hnonneg
  linarith only [hnonneg]

/-- **All-vector positivity of the complete Weil matrix at power-of-logarithm overlap.**
For every `0 < α < residualPowerLogPositivityExponent`, eventually in `N`, `completeWeilMatrix tiltedUnitSpline c N`
is positive definite uniformly across `1 ≤ c ≤ (log N)^α`. -/
theorem eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_residual_ceiling
    {α : ℝ} (hα : 0 < α) (hα_lt : α < residualPowerLogPositivityExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  classical
  filter_upwards [eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_residual_ceiling hα hα_lt]
    with N hfloor c hc hcup
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  apply hA.posDef_iff_eigenvalues_pos.mpr
  intro i
  let x := hA.eigenvectorBasis i
  have hx : ‖x‖ = 1 := by
    have hh : ⟪x, x⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    rw [real_inner_self_eq_norm_sq] at hh
    nlinarith only [hh, norm_nonneg x]
  have heig_eq : completeWeilEnergy tiltedUnitSpline c N x = hA.eigenvalues i := by
    unfold completeWeilEnergy
    have hAx : Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x =
        hA.eigenvalues i • x := by
      ext j
      exact congrFun (hA.mulVec_eigenvectorBasis i) j
    rw [hAx, real_inner_smul_left, real_inner_self_eq_norm_sq, hx, one_pow, mul_one]
  have hf := hfloor c hc hcup x
  rw [hx, one_pow, mul_one, heig_eq] at hf
  have hpos : 0 < tiltedSplineSpectralFloorConstant / (2 * c ^ 7) :=
    div_pos tiltedSplineSpectralFloorConstant_pos (by positivity)
  exact hpos.trans_le hf

/-- **Literal Weil quadratic form nonnegativity at power-of-logarithm overlap.**
Throughout `1 ≤ c ≤ (log N)^α` (`0 < α < residualPowerLogPositivityExponent`), `weilQuad` is nonnegative
on every atomic coefficient family `atomicTest N y (atomDilate tiltedUnitSpline (c / N))`. -/
theorem eventually_tiltedUnitSpline_weilQuad_nonneg_below_residual_ceiling
    {α : ℝ} (hα : 0 < α) (hα_lt : α < residualPowerLogPositivityExponent) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
      ∀ y : ℕ → ℝ,
        0 ≤ weilQuad (atomicTest N y (atomDilate tiltedUnitSpline (c / N))) := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_residual_ceiling hα hα_lt,
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

/-- The spectral floor cancels the polynomial mass debit and retains a positive prime-defect reserve. -/
theorem exists_tiltedUnitSpline_completeWeilEnergy_ge_poleDefect_reserve_below_residual_ceiling :
    ∃ b₁ : ℝ, 0 < b₁ ∧
      ∀ α : ℝ, 0 < α → α < residualPowerLogPositivityExponent →
        ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ α →
          ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
            (b₁ / c ^ 23) * poleDefect N (primeHorizonExtension x) ≤
              completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨b, B, H, hb, hB, hH, hres⟩ := exists_matrix_polynomial_reserve
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  let b₁ := κ * b / (2 * B + κ)
  have hdenom : 0 < 2 * B + κ := by positivity
  have hb₁ : 0 < b₁ := div_pos (mul_pos hκ hb) hdenom
  refine ⟨b₁, hb₁, ?_⟩
  intro α hα hα_lt
  have hα_19 : α < 1 / 19 := hα_lt
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_residual_ceiling hα hα_lt,
    eventually_log_nat_le_rpow_36,
    hLlim.eventually_ge_atTop (max 1 H),
    eventually_ge_atTop 2] with N hfloor hLX hL_max hN2 c hc1 hcup x
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL_max
  have hHL : H ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hL_max
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have hcL : c ≤ Real.log (N : ℝ) :=
    hcup.trans (by simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hL1 (by linarith only [hα_19] : α ≤ 1))
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
  have hfirst : (b₁ / c ^ 23) * poleDefect N (primeHorizonExtension x) ≤
      completeWeilEnergy tiltedUnitSpline c N x := by
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
  exact hfirst

/-- A fixed explicit exponent in the uniform all-vector positivity window. -/
theorem eventually_tiltedUnitSpline_completeWeilMatrix_posDef_log_one_twentieth :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ (1 / 20 : ℝ) →
      (completeWeilMatrix tiltedUnitSpline c N).PosDef :=
  eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_residual_ceiling
    (by norm_num) (by norm_num [residualPowerLogPositivityExponent])

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_residual_ceiling
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_below_residual_ceiling
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_residual_ceiling
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_weilQuad_nonneg_below_residual_ceiling
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completeWeilEnergy_ge_poleDefect_reserve_below_residual_ceiling
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_log_one_twentieth
