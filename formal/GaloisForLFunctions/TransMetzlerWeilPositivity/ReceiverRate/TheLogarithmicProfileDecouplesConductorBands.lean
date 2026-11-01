import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheLogarithmicProfileRetainsThePrimeDefect
import GaloisForLFunctions.CompletedArithmeticForms.ConductorBandOverlapAndNonRatioBounds
import GaloisForLFunctions.CompletedArithmeticForms.PrimePacketCoercivity
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.Conductor.QuadraticConductorConfinement
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.VariableCutoffConductorResiduals

/-!
# Conductor-band decoupling for the logarithmic profile

Small low-conductor residuals separate any nonpositive direction from its low
conductor projection. The orthogonal cross term is bounded by a cubic overlap
cost using the exact completed Weil decomposition.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped BigOperators RealInnerProductSpace Matrix Classical

namespace GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit

open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell CriticalArithmeticCorrelationTheory
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

private theorem smooth_profile : ContDiff ℝ 2 zeroFreeLogProfile :=
  contDiff_zeroFreeLogProfile.of_le (natCast_le_infty 2)

theorem identity_euclid_apply {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]


theorem hermitian_inner_add_eq {N : ℕ}
    {A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ} (hA : A.IsHermitian)
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin A (x + y), x + y⟫ =
      ⟪Matrix.toEuclideanLin A x, x⟫ + 2 * ⟪Matrix.toEuclideanLin A x, y⟫ +
        ⟪Matrix.toEuclideanLin A y, y⟫ := by
  have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) y x
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym,
    real_inner_comm y (Matrix.toEuclideanLin A x)]
  ring

theorem completeWeilEnergy_add_eq (φ : ℝ → ℝ) (c : ℝ) {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (x + y) =
      completeWeilEnergy φ c N x +
        2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ +
        completeWeilEnergy φ c N y :=
  hermitian_inner_add_eq (completeWeilMatrix_isHermitian φ c N) x y

theorem renormalizedPrimeEnergy_add_eq {N : ℕ}
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

theorem sub_starProjection_mem_orthogonal {N : ℕ}
    (K : Submodule ℝ (EuclideanSpace ℝ (PrimeHorizonIndex N)))
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    x - K.starProjection x ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal]
  intro v hv
  rw [real_inner_comm]
  exact K.starProjection_inner_eq_zero x v hv

theorem exists_raw_approx_of_starProjection_sq_le {Q N : ℕ} (hN : 2 ≤ N)
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


/-- A nonpositive unit vector away from the low band yields a bounded-energy orthogonal unit vector. -/
theorem low_band_decoupling_unit_orthogonal {Q₁ N : ℕ} {c : ℝ}
    (hQ₁ : 2 ≤ Q₁) (hQN : Q₁ * Q₁ ≤ N)
    (hlog : 18 * (1 + Real.log Q₁) ≤ Real.log N) (hc1 : 1 ≤ c)
    (hres_sum : (∑ m ∈ Icc 1 Q₁,
      ‖Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy zeroFreeLogProfile c m •
          normalizedRamanujanHorizonVector m N‖ ^ 2) ≤ 1 / 128)
    (hgram_err : 9 * (1 + Real.log Q₁) / Real.log N *
      (|completeWeilSelfFinitePart zeroFreeLogProfile 1| + 2 * Real.log Q₁ + 3 * c ^ 4) ≤ 1 / 16)
    {x : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hx : ‖x‖ = 1)
    (hxE : completeWeilEnergy zeroFreeLogProfile c N x ≤ 0)
    (hdist : 1 / 4 < ‖x - (conductorSubspace Q₁ N).starProjection x‖ ^ 2) :
    ∃ zHat : EuclideanSpace ℝ (PrimeHorizonIndex N),
      zHat ∈ (conductorSubspace Q₁ N)ᗮ ∧ ‖zHat‖ = 1 ∧
      completeWeilEnergy zeroFreeLogProfile c N zHat ≤
        2 := by
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
    Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N)
      (normalizedRamanujanHorizonVector m N) -
    completedConductorEnergy zeroFreeLogProfile c m • normalizedRamanujanHorizonVector m N
  let dVec := ∑ m ∈ Icc 1 Q₁,
    (a m * completedConductorEnergy zeroFreeLogProfile c m) •
      normalizedRamanujanHorizonVector m N
  let rVec := ∑ m ∈ Icc 1 Q₁, a m • r m
  have hWp_eq : Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N) p =
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
  have hcross : |⟪Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N) p, z⟫| ≤
      1 / 8 := by
    have hd_mem : dVec ∈ conductorSubspace Q₁ N :=
      sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q₁ N _
    have hd_orth : ⟪dVec, z⟫ = 0 := Submodule.inner_right_of_mem_orthogonal hd_mem hz_orth
    rw [hWp_eq, inner_add_left, hd_orth, zero_add]
    exact (abs_real_inner_le_norm rVec z).trans
      ((mul_le_mul hrVec_norm hz_le1 (norm_nonneg z) (by norm_num)).trans_eq (mul_one _))
  have hd_self : -(1 / 8 : ℝ) ≤ ⟪dVec, p⟫ := by
    let M_E := |completeWeilSelfFinitePart zeroFreeLogProfile 1| + 2 * Real.log Q₁ + 3 * c ^ 4
    have hE_bounds : ∀ m ∈ Icc 1 Q₁,
        0 ≤ completedConductorEnergy zeroFreeLogProfile c m ∧
          completedConductorEnergy zeroFreeLogProfile c m ≤ M_E := by
      intro m hm
      obtain ⟨hm1, hmQ⟩ := mem_Icc.mp hm
      have hpos : 0 ≤ completedConductorEnergy zeroFreeLogProfile c m :=
        completedConductorEnergy_nonneg smooth_profile zeroFreeLogProfile_eq_zero
          integral_zeroFreeLogProfile_sq_pos (zero_lt_one.trans_le hc1) hm1
      have hlogm : Real.log m ≤ Real.log Q₁ :=
        Real.log_le_log (by exact_mod_cast hm1) (by exact_mod_cast hmQ)
      have hup := completedConductorEnergy_le_of_one_le smooth_profile
        zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos hc1 hm1
      exact ⟨hpos, by dsimp only [M_E]; linarith only [hup, hlogm]⟩
    have hME0 : 0 ≤ M_E := by
      have h2mem : 2 ∈ Icc 1 Q₁ := mem_Icc.mpr ⟨by omega, hQ₁⟩
      exact (hE_bounds 2 h2mem).1.trans (hE_bounds 2 h2mem).2
    have hdiag_nonneg : 0 ≤ ∑ m ∈ Icc 1 Q₁,
        (a m * completedConductorEnergy zeroFreeLogProfile c m) * a m :=
      sum_nonneg fun m hm => by
        have h := (hE_bounds m hm).1
        nlinarith only [h, sq_nonneg (a m)]
    have hd_sq_le : (∑ m ∈ Icc 1 Q₁,
        (a m * completedConductorEnergy zeroFreeLogProfile c m) ^ 2) ≤
        M_E ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2 := by
      rw [mul_sum]
      refine sum_le_sum fun m hm => ?_
      obtain ⟨h0, hup⟩ := hE_bounds m hm
      have hesq : completedConductorEnergy zeroFreeLogProfile c m ^ 2 ≤ M_E ^ 2 :=
        pow_le_pow_left₀ h0 hup 2
      nlinarith only [hesq, sq_nonneg (a m)]
    have hsqrt_d :
        Real.sqrt (∑ m ∈ Icc 1 Q₁,
          (a m * completedConductorEnergy zeroFreeLogProfile c m) ^ 2) ≤
          M_E * Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2) := by
      calc
        _ ≤ Real.sqrt (M_E ^ 2 * ∑ m ∈ Icc 1 Q₁, a m ^ 2) := Real.sqrt_le_sqrt hd_sq_le
        _ = M_E * Real.sqrt (∑ m ∈ Icc 1 Q₁, a m ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hME0]
    have hpol := abs_inner_sum_normalizedRamanujanHorizonVector_sub_le hQ₁ hQN
      (fun m => a m * completedConductorEnergy zeroFreeLogProfile c m) a
    rw [← hp_eq] at hpol
    have hcoef0 : 0 ≤ 9 * (1 + Real.log Q₁) / Real.log N := by
      have hL : 0 < Real.log N := by
        have := Real.log_natCast_nonneg Q₁; linarith only [hlog, this]
      have := Real.log_natCast_nonneg Q₁; positivity
    have herr_le : |⟪dVec, p⟫ - ∑ m ∈ Icc 1 Q₁,
        (a m * completedConductorEnergy zeroFreeLogProfile c m) * a m| ≤ 1 / 8 := by
      calc
        _ ≤ 9 * (1 + Real.log Q₁) / Real.log N *
              Real.sqrt (∑ m ∈ Icc 1 Q₁,
                (a m * completedConductorEnergy zeroFreeLogProfile c m) ^ 2) *
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
  have hp_self : -(1 / 4 : ℝ) ≤ completeWeilEnergy zeroFreeLogProfile c N p := by
    unfold completeWeilEnergy
    rw [hWp_eq, inner_add_left]
    have hr_p : |⟪rVec, p⟫| ≤ 1 / 8 :=
      (abs_real_inner_le_norm rVec p).trans
        ((mul_le_mul hrVec_norm hp_le1 (norm_nonneg p) (by norm_num)).trans_eq (mul_one _))
    linarith only [hd_self, (abs_le.mp hr_p).1]
  have hz_energy : completeWeilEnergy zeroFreeLogProfile c N z ≤
      1 / 2 := by
    have hx_split : x = p + z := by dsimp only [z]; abel
    have hexp := completeWeilEnergy_add_eq zeroFreeLogProfile c p z
    rw [← hx_split] at hexp
    linarith only [hexp, hxE, hp_self, (abs_le.mp hcross).1]
  let zHat := (‖z‖)⁻¹ • z
  refine ⟨zHat, Submodule.smul_mem _ _ hz_orth, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz_pos, inv_mul_cancel₀ hz_pos.ne']
  · have hscale : completeWeilEnergy zeroFreeLogProfile c N zHat =
        (‖z‖⁻¹) ^ 2 * completeWeilEnergy zeroFreeLogProfile c N z := by
      dsimp only [zHat, completeWeilEnergy]
      rw [map_smul, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [hscale]
    rcases le_or_gt (completeWeilEnergy zeroFreeLogProfile c N z) 0 with hneg | hpos
    · have hle0 : (‖z‖⁻¹) ^ 2 * completeWeilEnergy zeroFreeLogProfile c N z ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hneg
      linarith only [hle0]
    · have hinv_lt : (‖z‖⁻¹) ^ 2 ≤ 4 := by
        have h1 : ‖z‖⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀' hz_pos).mpr (by linarith only [hz_gt])
        calc
          (‖z‖⁻¹) ^ 2 ≤ 2 ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
          _ = 4 := by norm_num
      calc
        (‖z‖⁻¹) ^ 2 * completeWeilEnergy zeroFreeLogProfile c N z ≤
            4 * (1 / 2) :=
          mul_le_mul hinv_lt hz_energy hpos.le (by norm_num)
        _ = 2 := by ring


/-- Orthogonal conductor packets have complete-Weil cross pairing bounded by cubic overlap cost. -/
theorem exists_completeWeilMatrix_orthog_cross_le :
    ∃ C_cross : ℝ, 1 ≤ C_cross ∧
      ∀ {R' N : ℕ} {c : ℝ},
        2 ≤ R' → R' ^ 6 ≤ N → 18 * (1 + Real.log R') ≤ Real.log N →
        1 ≤ c → c / N ≤ 1 / 3 →
        ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N →
        ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N →
        (1 + Real.log R') / Real.sqrt (Real.log N) ≤ 1 →
        (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N) ≤ c ^ 3 →
        (R' : ℝ) * Real.sqrt (Real.log N / N) ≤ 1 →
      ∀ {u w : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        u ∈ conductorSubspace R' N → u ∈ (conductorSubspace 1 N)ᗮ →
        w ∈ (conductorSubspace R' N)ᗮ →
        |⟪Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N) u, w⟫| ≤
          C_cross * c ^ 3 * ‖u‖ * ‖w‖ := by
  obtain ⟨C_pr, hC_pr, hpr⟩ := exists_fullPrimeMatrix_orthog_inner_le
  obtain ⟨C_od, hC_od, hod⟩ := exists_overlap_sub_downward_norm_le_of_mem_conductorSubspace
    smooth_profile zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos
  obtain ⟨C_up, hC_up, hup⟩ := exists_upwardPrimeVector_norm_le_of_mem_conductorSubspace
    smooth_profile zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos
  let C_sep := 4 * (152 * (∫ t, |zeroFreeLogProfile t|) ^ 2 / (∫ t, zeroFreeLogProfile t ^ 2))
  have hC_sep0 : 0 ≤ C_sep := by
    have := integral_zeroFreeLogProfile_sq_pos; dsimp only [C_sep]; positivity
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
        2 * C_pr * c ^ 3 := by
      have h := mul_le_mul_of_nonneg_left
        (show 1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N) ≤ 2 * c ^ 3 by
          linarith only [hlog_div2, h1_c3]) hC_pr.le
      nlinarith only [h]
    calc
      _ ≤ C_pr * (1 + (1 + Real.log R') ^ 2 / Real.sqrt (Real.log N)) * ‖u‖ * ‖w‖ := h1
      _ ≤ (2 * C_pr * c ^ 3) * ‖u‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg u)) (norm_nonneg w)
  -- 2. Center cross term
  have hterm_cen :
      |⟪Matrix.toEuclideanLin (fullWeilCenterMatrix
          (completeWeilPoleShift zeroFreeLogProfile c) N) u, w⟫| ≤
        144 * c ^ 3 * ‖u‖ * ‖w‖ := by
    have h1 := abs_fullWeilCenterMatrix_inner_le_of_mem_conductorSubspace
      (completeWeilPoleShift zeroFreeLogProfile c) hR' hR6N hlog hu hu1 hw1_orth
    have hpole : |completeWeilPoleShift zeroFreeLogProfile c| ≤ c := by
      rw [abs_of_nonneg (completeWeilPoleShift_nonneg zeroFreeLogProfile hc0.le)]
      exact completeWeilPoleShift_le smooth_profile.continuous
        zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos hc0.le
    have h2 : 144 * |completeWeilPoleShift zeroFreeLogProfile c| *
        (1 + Real.log R') / Real.sqrt (Real.log N) ≤ 144 * c ^ 3 := by
      have ha : 144 * |completeWeilPoleShift zeroFreeLogProfile c| *
          ((1 + Real.log R') / Real.sqrt (Real.log N)) ≤
          144 * |completeWeilPoleShift zeroFreeLogProfile c| * 1 :=
        mul_le_mul_of_nonneg_left hlog_div1 (by positivity)
      have hb : 144 * |completeWeilPoleShift zeroFreeLogProfile c| ≤ 144 * c ^ 3 := by
        linarith only [hpole, hc13]
      calc
        144 * |completeWeilPoleShift zeroFreeLogProfile c| *
            (1 + Real.log R') / Real.sqrt (Real.log N) =
            144 * |completeWeilPoleShift zeroFreeLogProfile c| *
              ((1 + Real.log R') / Real.sqrt (Real.log N)) := by ring
        _ ≤ 144 * c ^ 3 := by linarith only [ha, hb]
    calc
      _ ≤ 144 * |completeWeilPoleShift zeroFreeLogProfile c| *
            (1 + Real.log R') / Real.sqrt (Real.log N) * ‖u‖ * ‖w‖ := h1
      _ ≤ (144 * c ^ 3) * ‖u‖ * ‖w‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h2 (norm_nonneg u)) (norm_nonneg w)
  -- 3. Separated cross error
  have hterm_sep :
      |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix zeroFreeLogProfile c N) u, w⟫| ≤
        C_sep * c ^ 3 * ‖u‖ * ‖w‖ := by
    have hnorm := norm_separatedCrossErrorMatrix_le smooth_profile
      zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos hc0 hN1 u
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
      ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix zeroFreeLogProfile c N) u, w⟫ = 0 :=
    fullWeilPoleErrorMatrix_inner_eq_zero_of_orthog_one zeroFreeLogProfile c hN2 hu1 hw1_orth
  -- 5. Overlap minus downward
  have hterm_od :
      |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u -
          downwardPrimeVector zeroFreeLogProfile c N u, w⟫| ≤
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
      _ ≤ ‖Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u -
            downwardPrimeVector zeroFreeLogProfile c N u‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ (3 * C_od * c ^ 3 * ‖u‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right
          (hnorm.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg u))) (norm_nonneg w)
      _ = 3 * C_od * c ^ 3 * ‖u‖ * ‖w‖ := by ring
  -- 6. Upward non-ratio vector
  have hterm_up : |⟪upwardPrimeVector zeroFreeLogProfile c N u, w⟫| ≤
      2 * C_up * c ^ 3 * ‖u‖ * ‖w‖ := by
    have hnorm := hup hR' hlog hc1 hw1 hRNT_up hu
    have hcoef : C_up * c * Real.sqrt (1 + Real.log c) ≤ 2 * C_up * c ^ 3 := by
      calc
        C_up * c * Real.sqrt (1 + Real.log c) ≤ C_up * c * (2 * c) :=
          mul_le_mul_of_nonneg_left hsqrt_1lc (by positivity)
        _ = 2 * C_up * c ^ 2 := by ring
        _ ≤ 2 * C_up * c ^ 3 := mul_le_mul_of_nonneg_left hc23 (by positivity)
    calc
      _ ≤ ‖upwardPrimeVector zeroFreeLogProfile c N u‖ * ‖w‖ := abs_real_inner_le_norm _ _
      _ ≤ (2 * C_up * c ^ 3 * ‖u‖) * ‖w‖ :=
        mul_le_mul_of_nonneg_right
          (hnorm.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg u))) (norm_nonneg w)
      _ = 2 * C_up * c ^ 3 * ‖u‖ * ‖w‖ := by ring
  -- Combine via exact every-overlap decomposition
  have hdecomp :
      ⟪Matrix.toEuclideanLin (completeWeilMatrix zeroFreeLogProfile c N) u, w⟫ =
        -⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫ +
        ⟪Matrix.toEuclideanLin
          (fullWeilCenterMatrix (completeWeilPoleShift zeroFreeLogProfile c) N) u, w⟫ -
        ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix zeroFreeLogProfile c N) u, w⟫ +
        ⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u -
          downwardPrimeVector zeroFreeLogProfile c N u, w⟫ -
        ⟪upwardPrimeVector zeroFreeLogProfile c N u, w⟫ := by
    rw [completeWeilMatrix_eq_decomposition_at_every_overlap smooth_profile
      zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos hc0 hN1]
    simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, identity_euclid_apply,
      fullWeilNonRatioMatrix_eq_downward_add_upward smooth_profile
        zeroFreeLogProfile_eq_zero integral_zeroFreeLogProfile_sq_pos hc0 hN1 u,
      inner_add_left, inner_sub_left, real_inner_smul_left, huw_orth, mul_zero,
      hterm_pole]
    ring
  rw [hdecomp]
  have habs5 : ∀ x₁ x₂ x₃ x₄ x₅ : ℝ,
      |(-x₁) + x₂ - x₃ + x₄ - x₅| ≤ |x₁| + |x₂| + |x₃| + |x₄| + |x₅| := by
    intro x₁ x₂ x₃ x₄ x₅
    have h1 := abs_sub ((-x₁) + x₂ - x₃ + x₄) x₅
    have h2 := abs_add_le ((-x₁) + x₂ - x₃) x₄
    have h3 := abs_sub ((-x₁) + x₂) x₃
    have h4 := abs_add_le (-x₁) x₂
    rw [abs_neg] at h4
    linarith only [h1, h2, h3, h4]
  calc
    _ ≤ |⟪Matrix.toEuclideanLin (fullPrimeMatrix N) u, w⟫| +
          |⟪Matrix.toEuclideanLin
            (fullWeilCenterMatrix (completeWeilPoleShift zeroFreeLogProfile c) N) u, w⟫| +
          |⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix zeroFreeLogProfile c N) u, w⟫| +
          |⟪Matrix.toEuclideanLin (overlapMatrix zeroFreeLogProfile c N) u -
            downwardPrimeVector zeroFreeLogProfile c N u, w⟫| +
          |⟪upwardPrimeVector zeroFreeLogProfile c N u, w⟫| := habs5 _ _ _ _ _
    _ ≤ (2 * C_pr + 144 + C_sep + 3 * C_od + 2 * C_up) * c ^ 3 * ‖u‖ * ‖w‖ := by
      linarith only [hterm_pr, hterm_cen, hterm_sep, hterm_od, hterm_up]
    _ ≤ C_cross * c ^ 3 * ‖u‖ * ‖w‖ := by
      have hpos : 0 ≤ c ^ 3 * ‖u‖ * ‖w‖ := by positivity
      dsimp only [C_cross]
      nlinarith only [hpos]

end GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit.low_band_decoupling_unit_orthogonal
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.LogarithmicConductorSplit.exists_completeWeilMatrix_orthog_cross_le
