import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ConductorCrossAbsorption

/-!
# Conductor projection preserves a relative adjunction lower bound

Fixed-error confinement retains three quarters of the norm. Enlarging the cutoff
makes the complementary cross term cost only a fraction of the projected packet's
adjunction energy and a fixed mass debit.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical RealInnerProductSpace
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open SpacingScaleHarmonicAnalysis
open RenormalizedArithmeticPotentialTheory CompletedArithmeticForms CriticalScaleArithmeticRigidity

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

/-- Every bounded-energy unit vector above a low conductor space has a finite
conductor projection with bounded energy after its adjunction debit. -/
theorem exists_conductor_projection_with_adjunction_debit {E0 : ℝ} (hE0 : 0 < E0) :
    ∃ C_R H_res C_abs b : ℝ, 0 < C_R ∧ 0 < H_res ∧ 0 < C_abs ∧ 0 < b ∧
      ∀ {Q₁ N : ℕ} {c : ℝ},
        2 ≤ Q₁ → 1 ≤ c → H_res * c ^ 8 ≤ N → c / N ≤ 1 / 3 →
        (∀ {R' : ℕ}, Q₁ ≤ R' → Real.log R' ≤ C_R * c ^ 16 + Real.log Q₁ →
          R' ^ 6 ≤ N ∧ R' * R' ≤ N / growingDefectCutoff c ∧
          18 * (1 + Real.log R') ≤ Real.log (N / growingDefectCutoff c : ℕ) ∧
          terminalPacketCost R' (N / growingDefectCutoff c) N /
            Real.log (N / growingDefectCutoff c : ℕ) ≤ b / (4 * c ^ 7) ∧
          ((R' * R' : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N ∧
          ((R' * R' : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N ∧
          C_abs * ((1 + Real.log R') / Real.log N +
            c ^ 7 * (1 + terminalPacketCost R' (N / growingDefectCutoff c) N) / Real.log N +
            c ^ 11 * (1 + Real.log c) / Real.log N +
            c ^ 11 * (R' : ℝ) ^ 2 * (Real.log N / N)) ≤ 1) →
      ∀ {zHat : EuclideanSpace ℝ (PrimeHorizonIndex N)},
        zHat ∈ (conductorSubspace Q₁ N)ᗮ → ‖zHat‖ = 1 →
        completeWeilEnergy tiltedUnitSpline c N zHat ≤ E0 →
      ∃ R' : ℕ, Q₁ ≤ R' ∧ Real.log R' ≤ C_R * c ^ 16 + Real.log Q₁ ∧
        ∃ a : ℕ → ℝ,
          (∑ m ∈ Icc 1 R', a m • normalizedRamanujanHorizonVector m N) ∈ (conductorSubspace Q₁ N)ᗮ ∧
          3 / 4 ≤ ‖∑ m ∈ Icc 1 R', a m • normalizedRamanujanHorizonVector m N‖ ^ 2 ∧
          ‖∑ m ∈ Icc 1 R', a m • normalizedRamanujanHorizonVector m N‖ ≤ 1 ∧
          completeWeilEnergy tiltedUnitSpline c N
            (∑ m ∈ Icc 1 R', a m • normalizedRamanujanHorizonVector m N) -
              (1 / 8 : ℝ) * primeAdjunctionMass R' a ≤ E0 + 1 := by
  obtain ⟨b0, B, H0, hb0, -, hB, hH0, hprefix⟩ := exists_completeWeilEnergy_prefix_reserve_polynomial
  obtain ⟨b, K, H1, C_abs, hb, -, hK, hH1, hC_abs, habsorb⟩ :=
    exists_completeWeil_conductor_cross_absorbed
  let H_res := H0 + H1
  let K_coef := (B + E0) / b0
  have hK_coef : 0 < K_coef := by dsimp only [K_coef]; positivity
  let D := explicitConductorCutoffConstant
  have hD : 0 < D := explicitConductorCutoffConstant_pos
  let C_gap := D * (1 + K)
  have hC_gap : 0 < C_gap := by dsimp only [C_gap]; positivity
  let C_app := 16 * quadraticConfinementConstant * (K_coef + 1)
  have hC_app : 0 < C_app := by
    have := quadraticConfinementConstant_pos; dsimp only [C_app]; positivity
  let C_R := C_app + C_gap + 1
  have hC_R : 0 < C_R := by dsimp only [C_R]; positivity
  refine ⟨C_R, H_res, C_abs, b, hC_R, by dsimp only [H_res]; positivity, hC_abs, hb, ?_⟩
  intro Q₁ N c hQ₁ hc1 hHN hw1 hR'_conds zHat hz_orth hz_norm hz_energy
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hc16 : 1 ≤ c ^ 16 := one_le_pow₀ hc1
  have hHN0 : H0 * c ^ 8 ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hH1.le) (pow_nonneg hc0.le 8)).trans hHN
  have hHN1 : H1 * c ^ 8 ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hH0.le) (pow_nonneg hc0.le 8)).trans hHN
  have hdef_le : poleDefect N (primeHorizonExtension zHat) ≤ K_coef * c ^ 16 := by
    have hraw := hprefix c hc1 N hHN0 zHat
    have hDM := poleDefect_nonneg (N / growingDefectCutoff c) (primeHorizonExtension zHat)
    have hr : (b0 / c ^ 7) * poleDefect N (primeHorizonExtension zHat) -
        B * c ^ 9 * ‖zHat‖ ^ 2 ≤ completeWeilEnergy tiltedUnitSpline c N zHat := by
      linarith only [hraw, hDM]
    rw [hz_norm, one_pow, mul_one] at hr
    have h1 : (b0 / c ^ 7) * poleDefect N (primeHorizonExtension zHat) ≤
        B * c ^ 9 + E0 := by linarith only [hr, hz_energy]
    have hc9 : 1 ≤ c ^ 9 := one_le_pow₀ hc1
    have h2 : B * c ^ 9 + E0 ≤ (B + E0) * c ^ 9 := by nlinarith only [hE0, hc9]
    have h3 := (div_le_iff₀ (pow_pos hc0 7)).mp (by
      simpa only [div_mul_eq_mul_div] using h1.trans h2)
    dsimp only [K_coef]
    rw [div_mul_eq_mul_div, le_div_iff₀ hb0]
    calc
      poleDefect N (primeHorizonExtension zHat) * b0 =
          b0 * poleDefect N (primeHorizonExtension zHat) := mul_comm _ _
      _ ≤ (B + E0) * c ^ 9 * c ^ 7 := h3
      _ = (B + E0) * c ^ 16 := by ring
  -- A fixed tolerance retains three quarters of the norm.
  obtain ⟨R₀, hR₀2, hR₀log, happ⟩ := exists_explicit_quadratic_conductor_projection
    (1 / 4) (by norm_num) (by norm_num) (K_coef * c ^ 16) (by positivity)
  have hR₀bound : Real.log R₀ ≤ C_app * c ^ 16 := by
    have hK1 : K_coef * c ^ 16 + 1 ≤ (K_coef + 1) * c ^ 16 := by linarith only [hc16]
    calc
      _ ≤ quadraticConfinementConstant / (1 / 4 : ℝ) ^ 2 * (K_coef * c ^ 16 + 1) := hR₀log
      _ ≤ quadraticConfinementConstant / (1 / 4 : ℝ) ^ 2 * ((K_coef + 1) * c ^ 16) :=
        mul_le_mul_of_nonneg_left hK1 (by have := quadraticConfinementConstant_pos; positivity)
      _ = _ := by dsimp only [C_app]; ring
  -- The enlarged cutoff makes the orthogonal tail itself coercive.
  let G : ℕ := ⌈Real.exp (C_gap * c ^ 16)⌉₊
  have hXpos : 0 < C_gap * c ^ 16 := mul_pos hC_gap (pow_pos hc0 16)
  have hexp1 : 1 < Real.exp (C_gap * c ^ 16) := by
    simpa only [Real.exp_zero] using Real.exp_lt_exp.mpr hXpos
  have hceil : Real.exp (C_gap * c ^ 16) ≤ (G : ℝ) := Nat.le_ceil _
  have hGpos : (0 : ℝ) < G := (zero_lt_one.trans hexp1).trans_le hceil
  have hGlow : C_gap * c ^ 16 ≤ Real.log G := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hceil
  have hGup : Real.log G ≤ C_gap * c ^ 16 + 1 := by
    have hceilUp : (G : ℝ) < Real.exp (C_gap * c ^ 16) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos _).le
    have hdouble : (G : ℝ) ≤ 2 * Real.exp (C_gap * c ^ 16) := by
      linarith only [hceilUp, hexp1]
    have hlog := Real.log_le_log hGpos hdouble
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp] at hlog
    linarith only [hlog, Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  let R := max R₀ G
  let R' := max R Q₁
  have hQR' : Q₁ ≤ R' := le_max_right _ _
  have hR₀R' : R₀ ≤ R' := (le_max_left R₀ G).trans (le_max_left R Q₁)
  have hGR' : G ≤ R' := (le_max_right R₀ G).trans (le_max_left R Q₁)
  have hR'2 : 2 ≤ R' := hQ₁.trans hQR'
  have hRbound : Real.log R ≤ C_R * c ^ 16 := by
    rcases le_total R₀ G with hRG | hGR
    · rw [show R = G from max_eq_right hRG]
      dsimp only [C_R]
      nlinarith only [hGup, hc16, hC_app, pow_nonneg hc0.le 16]
    · rw [show R = R₀ from max_eq_left hGR]
      dsimp only [C_R]
      nlinarith only [hR₀bound, hC_gap, pow_nonneg hc0.le 16]
  have hR'_log : Real.log R' ≤ C_R * c ^ 16 + Real.log Q₁ := by
    have hQlog := Real.log_natCast_nonneg Q₁
    have hCr : 0 ≤ C_R * c ^ 16 := by positivity
    rcases le_total R Q₁ with hRQ | hQR
    · rw [show R' = Q₁ from max_eq_right hRQ]
      linarith only [hCr]
    · rw [show R' = R from max_eq_left hQR]
      linarith only [hRbound, hQlog]
  have hgapLog : C_gap * c ^ 16 ≤ Real.log R' :=
    hGlow.trans (Real.log_le_log hGpos (by exact_mod_cast hGR'))
  obtain ⟨hR6N, hRM, hlogM, hleak, hRNT_lin, hRNT_up, hsmall⟩ :=
    hR'_conds hQR' hR'_log
  have hN2 : 2 ≤ N := by
    have hpow : R' ^ 1 ≤ R' ^ 6 :=
      Nat.pow_le_pow_right (by omega) (by norm_num)
    simp only [pow_one] at hpow
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
  have hw_sq : ‖w‖ ^ 2 ≤ 1 / 4 := by
    have hpR_mem : (conductorSubspace R₀ N).starProjection zHat ∈ conductorSubspace R' N :=
      conductorSubspace_mono hR₀R' N ((conductorSubspace R₀ N).starProjection_apply_mem zHat)
    exact (norm_sub_starProjection_sq_le (conductorSubspace R' N) zHat _ hpR_mem).trans
      (happ N hN2 zHat hz_norm.le hdef_le)
  have hpyth := norm_starProjection_sq_add_sub_sq (conductorSubspace R' N) zHat
  change ‖u‖ ^ 2 + ‖w‖ ^ 2 = ‖zHat‖ ^ 2 at hpyth
  rw [hz_norm, one_pow] at hpyth
  have hu_sq_ge : 3 / 4 ≤ ‖u‖ ^ 2 := by linarith only [hpyth, hw_sq]
  have hu_le1 : ‖u‖ ≤ 1 := by nlinarith only [hpyth, sq_nonneg ‖w‖, norm_nonneg u]
  have hgap : K * c ^ 16 ≤ Real.log R' / D - 1 := by
    have hh : (1 + K) * c ^ 16 ≤ Real.log R' / D := by
      apply (le_div_iff₀ hD).mpr
      exact (show ((1 + K) * c ^ 16) * D = C_gap * c ^ 16 by dsimp only [C_gap]; ring).trans_le hgapLog
    linarith only [hh, hc16]
  obtain ⟨a, -, ha⟩ := (mem_conductorSubspace_iff (x := u)).mp hu_mem
  have hpay := habsorb hc1 hR'2 hR6N hHN1 hw1 hRM hlogM hgap hleak hRNT_lin hRNT_up hsmall
    a (ha ▸ hu_orth1) hw_orth
  rw [← ha] at hpay
  have hu_sq_le1 : ‖u‖ ^ 2 ≤ 1 := by nlinarith only [hu_le1, norm_nonneg u]
  have htail : 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫| -
      completeWeilEnergy tiltedUnitSpline c N w ≤ (1 / 8 : ℝ) * primeAdjunctionMass R' a + 1 / 4 := by
    linarith only [hpay, hu_sq_le1]
  have hu_energy : completeWeilEnergy tiltedUnitSpline c N u -
      (1 / 8 : ℝ) * primeAdjunctionMass R' a ≤ E0 + 1 := by
    have hz_split : zHat = u + w := by dsimp only [w]; abel
    have hexp := completeWeilEnergy_add_eq tiltedUnitSpline c u w
    rw [← hz_split] at hexp
    linarith only [hexp, hz_energy, htail,
      neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) u, w⟫]
  refine ⟨R', hQR', hR'_log, a, ?_⟩
  rw [← ha]
  exact ⟨hu_orthQ, hu_sq_ge, hu_le1, hu_energy⟩

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_conductor_projection_with_adjunction_debit
