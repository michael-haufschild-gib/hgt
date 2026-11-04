import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalLowPacketHasAUniformResidualBudget
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.WindowConductorCoordinatesVanishUniformly
import GaloisForLFunctions.CompletedArithmeticForms.ConductorEnergiesHaveAUniformLogarithmicUpperBound

/-!
# Vanishing inverse-energy mass above overlap

Above the overlap scale the completed conductor energy has a constant
floor. Summing the quadratic residual estimate there avoids the
seventh-power cost of the low conductors. After division by overlap,
the packet of logarithmic exponent `13/32` has vanishing mass.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  ArithmeticHodgeTheoryOfDegenerations SpacingScaleHarmonicAnalysis CompletedArithmeticForms

/-- The part above overlap has no seventh-power inverse-energy loss. -/
theorem exists_above_overlap_normalized_residual_sum_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ k : ℕ, 1 ≤ k → ∀ᶠ N : ℕ in atTop,
      ∀ c : ℝ, 1 ≤ c → 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.log (N : ℝ) ^ A →
        (∑ m ∈ (Icc 1 Q).filter (fun m => c < (m : ℝ)),
          ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
              (normalizedRamanujanHorizonVector m N) -
            completedConductorEnergy tiltedUnitSpline c m •
              normalizedRamanujanHorizonVector m N‖ ^ 2 /
            (c * completedConductorEnergy tiltedUnitSpline c m)) ≤
          K * (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 *
            (c * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
              c ^ 9 * (Real.log (N : ℝ) / N) ^ 2) := by
  obtain ⟨K₀, hK₀, hres⟩ := exists_tiltedUnitSpline_quadratic_conductor_residual_variable_rate
  let κ := tiltedSplineSpectralFloorConstant
  have hκ : 0 < κ := tiltedSplineSpectralFloorConstant_pos
  refine ⟨K₀ / κ, by positivity, ?_⟩
  intro A hA k hk
  filter_upwards [hres A hA k hk] with N hresN
  intro c hc hwidth Q hQ
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  let r := c * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) / Real.log N +
    c ^ 9 * (Real.log (N : ℝ) / N) ^ 2
  have hr : 0 ≤ r := by
    have := Real.log_natCast_nonneg N
    have := Real.log_nonneg hc
    dsimp only [r]
    positivity
  let S := (Icc 1 Q).filter (fun m => c < (m : ℝ))
  have hpoint : ∀ m ∈ S,
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 /
        (c * completedConductorEnergy tiltedUnitSpline c m) ≤
      (K₀ / κ * r) * ((m : ℝ) * (1 + Real.log m) ^ 2) := by
    intro m hmS
    obtain ⟨hmQ, hcm⟩ := mem_filter.mp hmS
    obtain ⟨hm, hmQ⟩ := mem_Icc.mp hmQ
    have hmQ' : (m : ℝ) ≤ Q := by exact_mod_cast hmQ
    have hE : κ ≤ completedConductorEnergy tiltedUnitSpline c m :=
      tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hm hcm.le
    have hE0 := hκ.trans_le hE
    have hb := hresN m hm (hmQ'.trans hQ) c hc hwidth
    have hrate : c ^ 2 * (1 + Real.log c) ^ 3 * Real.log N ^ (1 / (k : ℝ)) /
        Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 = c * r := by
      dsimp only [r]
      ring
    rw [hrate] at hb
    calc
      _ ≤ (K₀ * ((m : ℝ) * (1 + Real.log m) ^ 2) * (c * r)) /
          (c * completedConductorEnergy tiltedUnitSpline c m) :=
        div_le_div_of_nonneg_right hb (mul_pos hc0 hE0).le
      _ = (K₀ * ((m : ℝ) * (1 + Real.log m) ^ 2) * r) /
          completedConductorEnergy tiltedUnitSpline c m := by
        field_simp [hc0.ne', hE0.ne']
      _ ≤ (K₀ * ((m : ℝ) * (1 + Real.log m) ^ 2) * r) / κ :=
        div_le_div_of_nonneg_left (by positivity) hκ hE
      _ = _ := by ring
  have hlin : (∑ m ∈ S, (m : ℝ) * (1 + Real.log m) ^ 2) ≤
      (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 := by
    calc
      _ ≤ ∑ m ∈ Icc 1 Q, (m : ℝ) * (1 + Real.log m) ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => by positivity)
      _ ≤ ∑ _m ∈ Icc 1 Q, (Q : ℝ) * (1 + Real.log Q) ^ 2 := by
        apply sum_le_sum
        intro m hm
        have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
        have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
        exact mul_le_mul hmQ
          (pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg m])
            (add_le_add le_rfl (Real.log_le_log hm0 hmQ)) 2)
          (sq_nonneg _) (Nat.cast_nonneg Q)
      _ = _ := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring
  calc
    _ ≤ ∑ m ∈ S, (K₀ / κ * r) * ((m : ℝ) * (1 + Real.log m) ^ 2) := sum_le_sum hpoint
    _ = (K₀ / κ * r) * ∑ m ∈ S, (m : ℝ) * (1 + Real.log m) ^ 2 := (mul_sum _ _ _).symm
    _ ≤ (K₀ / κ * r) * ((Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) :=
      mul_le_mul_of_nonneg_left hlin (by positivity)
    _ = _ := by ring

/-- The inverse-energy norm mass above overlap vanishes on every positive critical clock. -/
theorem eventually_upper_critical_packet_residual_mass_le {c : ℕ → ℝ}
    (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop,
      (∑ m ∈ (Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊).filter (fun m => c N < (m : ℝ)),
        ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline (c N) m •
            normalizedRamanujanHorizonVector m N‖ ^ 2 /
          (c N * completedConductorEnergy tiltedUnitSpline (c N) m)) ≤
        Real.log N ^ (-1 / 64 : ℝ) := by
  obtain ⟨K, hK, hbudget⟩ := exists_above_overlap_normalized_residual_sum_bound
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hwidth := (criticalCurve_pow_log_div_natCast hc hR hcrit 2 0).const_mul
    (4 * (Real.exp 1 + 3) ^ 2)
  simp only [pow_zero, mul_one, mul_zero] at hwidth
  have hLN := criticalCurve_pow_log_div_natCast hc hR hcrit 0 8
  simp only [pow_zero, one_mul] at hLN
  filter_upwards [hbudget (13 / 32) (by norm_num) 128 (by norm_num),
    hlog.eventually_ge_atTop 1, eventually_ge_atTop 1,
    eventually_criticalCurve_le_log_rpow hc hcrit (by norm_num : (1 / 8 : ℝ) < 2 / 15),
    hwidth.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hLN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hlog.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (-89 / 1920 : ℝ) < -1 / 64) 5 (2 * K)),
    hlog.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (-67 / 16 : ℝ) < -1 / 64) 2 (2 * K))]
    with N hbudgetN hL1 hN hcα hwidthN hL8N hpoly₁ hpoly₂
  let L : ℝ := Real.log N
  let Q : ℕ := ⌊L ^ (13 / 32 : ℝ)⌋₊
  let U : ℝ := 1 + Real.log L
  change 1 ≤ L at hL1
  change c N ≤ L ^ (2 / 15 : ℝ) at hcα
  change 2 * K * L ^ (-89 / 1920 : ℝ) * U ^ 5 ≤ L ^ (-1 / 64 : ℝ) at hpoly₁
  change 2 * K * L ^ (-67 / 16 : ℝ) * U ^ 2 ≤ L ^ (-1 / 64 : ℝ) at hpoly₂
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hU0 : 0 ≤ U := by dsimp only [U]; linarith [Real.log_nonneg hL1]
  have hlarge : 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ N := by
    apply (div_le_one hN0).mp
    simpa only [mul_div_assoc] using hwidthN.le
  have hL8 : L ^ 8 ≤ N := (div_le_one hN0).mp hL8N.le
  have hcL : c N ≤ L := hcα.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (2 / 15 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one L))
  have hQpow : (Q : ℝ) ≤ L ^ (13 / 32 : ℝ) := Nat.floor_le (Real.rpow_nonneg hL0.le _)
  have hQ1 : 1 ≤ Q := Nat.le_floor (by
    exact_mod_cast (Real.one_le_rpow hL1 (by norm_num : (0 : ℝ) ≤ 13 / 32)))
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hQL : (Q : ℝ) ≤ L := hQpow.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (13 / 32 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one L))
  have hQ2 : (Q : ℝ) ^ 2 ≤ L ^ (13 / 16 : ℝ) := by
    calc
      _ ≤ (L ^ (13 / 32 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQpow 2
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
  have hlogQ : (1 + Real.log Q) ^ 2 ≤ U ^ 2 :=
    pow_le_pow_left₀ (by linarith [Real.log_natCast_nonneg Q])
      (add_le_add le_rfl (Real.log_le_log hQ0 hQL)) 2
  have hlogc : (1 + Real.log (c N)) ^ 3 ≤ U ^ 3 :=
    pow_le_pow_left₀ (by linarith [Real.log_nonneg (hc N)])
      (add_le_add le_rfl (Real.log_le_log hc0 hcL)) 3
  have hW : (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 ≤ L ^ (13 / 16 : ℝ) * U ^ 2 :=
    mul_le_mul hQ2 hlogQ (sq_nonneg _) (Real.rpow_nonneg hL0.le _)
  have hratio : L / (N : ℝ) ≤ 1 / L ^ 7 := by
    rw [div_le_div_iff₀ hN0 (pow_pos hL0 7), one_mul]
    exact (by ring : L * L ^ 7 = L ^ 8).le.trans hL8
  have hr₂ : c N ^ 9 * (L / N) ^ 2 ≤ 1 / L ^ 5 := by
    calc
      _ ≤ L ^ 9 * (1 / L ^ 7) ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ hc0.le hcL 9)
          (pow_le_pow_left₀ (div_nonneg hL0.le hN0.le) hratio 2)
          (sq_nonneg _) (pow_nonneg hL0.le _)
      _ = _ := by field_simp [hL0.ne']
  have hr₁ : c N * (1 + Real.log (c N)) ^ 3 * L ^ (1 / 128 : ℝ) / L ≤
      L ^ (2 / 15 : ℝ) * U ^ 3 * L ^ (1 / 128 : ℝ) / L :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul hcα hlogc (pow_nonneg (by linarith [Real.log_nonneg (hc N)]) 3)
          (Real.rpow_nonneg hL0.le _))
        (Real.rpow_nonneg hL0.le _)) hL0.le
  have hfirst : K * (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 *
      (c N * (1 + Real.log (c N)) ^ 3 * L ^ (1 / 128 : ℝ) / L) ≤
        (1 / 2 : ℝ) * L ^ (-1 / 64 : ℝ) := by
    calc
      _ = K * ((Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) *
          (c N * (1 + Real.log (c N)) ^ 3 * L ^ (1 / 128 : ℝ) / L) := by ring
      _ ≤ K * (L ^ (13 / 16 : ℝ) * U ^ 2) *
          (L ^ (2 / 15 : ℝ) * U ^ 3 * L ^ (1 / 128 : ℝ) / L) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hW hK.le) hr₁
          (by have := Real.log_nonneg (hc N); positivity) (by positivity)
      _ = K * (L ^ (13 / 16 : ℝ) * L ^ (2 / 15 : ℝ) *
          L ^ (1 / 128 : ℝ) * L⁻¹) * U ^ 5 := by ring
      _ = K * L ^ (-89 / 1920 : ℝ) * U ^ 5 := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
          ← Real.rpow_add hL0]
        norm_num
      _ ≤ _ := by linarith only [hpoly₁]
  have hsecond : K * (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 *
      (c N ^ 9 * (L / N) ^ 2) ≤ (1 / 2 : ℝ) * L ^ (-1 / 64 : ℝ) := by
    calc
      _ = K * ((Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2) * (c N ^ 9 * (L / N) ^ 2) := by ring
      _ ≤ K * (L ^ (13 / 16 : ℝ) * U ^ 2) * (1 / L ^ 5) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hW hK.le) hr₂ (by positivity) (by positivity)
      _ = K * (L ^ (13 / 16 : ℝ) / L ^ (5 : ℝ)) * U ^ 2 := by
        rw [show L ^ (5 : ℝ) = L ^ (5 : ℕ) by
          simpa only [Nat.cast_ofNat] using Real.rpow_natCast L 5]
        ring
      _ = K * L ^ (-67 / 16 : ℝ) * U ^ 2 := by rw [← Real.rpow_sub hL0]; norm_num
      _ ≤ _ := by linarith only [hpoly₂]
  have hb := hbudgetN (c N) (hc N) hlarge Q hQpow
  change (∑ m ∈ (Icc 1 Q).filter (fun m => c N < (m : ℝ)), _) ≤ L ^ (-1 / 64 : ℝ)
  calc
    _ ≤ K * (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 *
        (c N * (1 + Real.log (c N)) ^ 3 * L ^ (1 / 128 : ℝ) / L +
          c N ^ 9 * (L / N) ^ 2) := hb
    _ ≤ (1 / 2 : ℝ) * L ^ (-1 / 64 : ℝ) + (1 / 2 : ℝ) * L ^ (-1 / 64 : ℝ) := by
      rw [mul_add]
      exact add_le_add hfirst hsecond
    _ = _ := by ring

private theorem tendsto_log_rpow_neg {p : ℝ} (hp : 0 < p) :
    Tendsto (fun N : ℕ => Real.log N ^ (-p)) atTop (𝓝 0) := by
  have ht := tendsto_inv_atTop_zero.comp
    ((tendsto_rpow_atTop hp).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  apply ht.congr
  intro N
  exact (Real.rpow_neg (Real.log_natCast_nonneg N) p).symm

/-- Every bounded terminal receiver sees vanishing residual mass above overlap. -/
theorem tendsto_upper_critical_packet_residual_mixed_mass
    {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      ∑ m ∈ (Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊).filter (fun m => c N < (m : ℝ)),
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
            (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy tiltedUnitSpline (c N) m • normalizedRamanujanHorizonVector m N,
          horizonProfileVector (horizonWeights h N) N⟫ ^ 2 /
          (c N * completedConductorEnergy tiltedUnitSpline (c N) m)) atTop (𝓝 0) := by
  let T := B ^ 2 * Real.exp A
  have ht := (tendsto_log_rpow_neg (by norm_num : (0 : ℝ) < 1 / 64)).const_mul T
  simp only [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · apply Eventually.of_forall
    intro N
    apply sum_nonneg
    intro m hm
    have hm0 := (mem_Icc.mp (mem_filter.mp hm).1).1
    exact div_nonneg (sq_nonneg _) (mul_nonneg (zero_le_one.trans (hc N))
      (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_support
        integral_tiltedUnitSpline_sq_pos (zero_lt_one.trans_le (hc N)) hm0))
  · filter_upwards [eventually_upper_critical_packet_residual_mass_le hc hR hcrit,
      eventually_ge_atTop 1] with N hsum hN
    let S := (Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊).filter (fun m => c N < (m : ℝ))
    let r := fun m => Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        (normalizedRamanujanHorizonVector m N) -
      completedConductorEnergy tiltedUnitSpline (c N) m • normalizedRamanujanHorizonVector m N
    let x := horizonProfileVector (horizonWeights h N) N
    have hnorm : ‖x‖ ^ 2 ≤ T := horizon_window_norm_sq_le hsupp hB hN
    calc
      _ ≤ ∑ m ∈ S, T * (‖r m‖ ^ 2 /
          (c N * completedConductorEnergy tiltedUnitSpline (c N) m)) := by
        apply sum_le_sum
        intro m hm
        have hm0 := (mem_Icc.mp (mem_filter.mp hm).1).1
        have hE := completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_support
          integral_tiltedUnitSpline_sq_pos (zero_lt_one.trans_le (hc N)) hm0
        have hp := (inner_sq_le_norm_sq_mul (r m) x).trans
          (mul_le_mul_of_nonneg_left hnorm (sq_nonneg _))
        exact (div_le_div_of_nonneg_right hp
          (mul_nonneg (zero_le_one.trans (hc N)) hE)).trans_eq (by ring)
      _ = T * ∑ m ∈ S, ‖r m‖ ^ 2 /
          (c N * completedConductorEnergy tiltedUnitSpline (c N) m) := (mul_sum _ _ _).symm
      _ ≤ T * Real.log N ^ (-1 / 64 : ℝ) :=
        mul_le_mul_of_nonneg_left hsum (by dsimp only [T]; positivity)

/-- Restoring the energy diagonal contributes vanishing mixed mass on the whole low packet. -/
theorem tendsto_critical_packet_reference_mixed_mass
    {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) :
    Tendsto (fun N : ℕ => ∑ m ∈ Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊,
      completedConductorEnergy tiltedUnitSpline (c N) m / c N *
        ⟪normalizedRamanujanHorizonVector m N,
          horizonProfileVector (horizonWeights h N) N⟫ ^ 2) atTop (𝓝 0) := by
  let β := |completeWeilSelfFinitePart tiltedUnitSpline 1| + 5
  let α := 2 * B * Real.exp A
  have hβ : 0 < β := by dsimp only [β]; positivity
  have ht := (tendsto_log_rpow_neg (by norm_num : (0 : ℝ) < 3 / 16)).const_mul (β * α ^ 2)
  simp only [mul_zero] at ht
  apply squeeze_zero' _ _ ht
  · apply Eventually.of_forall
    intro N
    apply sum_nonneg
    intro m hm
    exact mul_nonneg (div_nonneg
      (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_support
        integral_tiltedUnitSpline_sq_pos (zero_lt_one.trans_le (hc N)) (mem_Icc.mp hm).1)
      (zero_le_one.trans (hc N))) (sq_nonneg _)
  · filter_upwards [eventually_ge_atTop 1,
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1]
      with N hN hL1
    let L := Real.log (N : ℝ)
    let Q := ⌊L ^ (13 / 32 : ℝ)⌋₊
    change 1 ≤ L at hL1
    have hL0 : 0 < L := zero_lt_one.trans_le hL1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    have hQpow : (Q : ℝ) ≤ L ^ (13 / 32 : ℝ) := Nat.floor_le (Real.rpow_nonneg hL0.le _)
    have hQL : (Q : ℝ) ≤ L := hQpow.trans
      ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (13 / 32 : ℝ) ≤ 1)).trans_eq
        (Real.rpow_one L))
    have hLN : L ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (sub_le_self _ zero_le_one)
    have hQN : Q ≤ N := by exact_mod_cast hQL.trans hLN
    have hQ2 : (Q : ℝ) ^ 2 ≤ L ^ (13 / 16 : ℝ) := by
      calc
        _ ≤ (L ^ (13 / 32 : ℝ)) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg Q) hQpow 2
        _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; norm_num
    have hpoint : ∀ m ∈ Icc 1 Q,
        completedConductorEnergy tiltedUnitSpline (c N) m / c N *
          ⟪normalizedRamanujanHorizonVector m N,
            horizonProfileVector (horizonWeights h N) N⟫ ^ 2 ≤
        β * (Q : ℝ) * (α ^ 2 / L) := by
      intro m hm
      obtain ⟨hm0, hmQ⟩ := mem_Icc.mp hm
      have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm0
      have hmQ' : (m : ℝ) ≤ Q := by exact_mod_cast hmQ
      have he := completedConductorEnergy_le_logarithmic_uniform contDiff_tiltedUnitSpline
        tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (hc N) hm0
      have hl : Real.log (m : ℝ) ≤ m :=
        (Real.log_le_sub_one_of_pos hmR).trans (sub_le_self _ zero_le_one)
      have hb := mul_le_mul_of_nonneg_left hm1
        (by positivity : 0 ≤ |completeWeilSelfFinitePart tiltedUnitSpline 1| + 3)
      have hEm : completedConductorEnergy tiltedUnitSpline (c N) m ≤ β * m := by
        dsimp only [β]
        nlinarith only [he, hl, hb]
      have hEQ : completedConductorEnergy tiltedUnitSpline (c N) m ≤ β * Q :=
        hEm.trans (mul_le_mul_of_nonneg_left hmQ' hβ.le)
      have hEdiv : completedConductorEnergy tiltedUnitSpline (c N) m / c N ≤ β * Q :=
        (div_le_iff₀ hc0).mpr (hEQ.trans
          (le_mul_of_one_le_right (by positivity : 0 ≤ β * (Q : ℝ)) (hc N)))
      have hcoord := abs_horizon_window_conductor_inner_le hsupp hB hm0 (hmQ.trans hQN)
      rw [real_inner_comm] at hcoord
      have hcoordsq := pow_le_pow_left₀ (abs_nonneg _) hcoord 2
      simp only [sq_abs, div_pow, Real.sq_sqrt hL0.le] at hcoordsq
      exact mul_le_mul hEdiv hcoordsq (sq_nonneg _) (by positivity)
    calc
      _ ≤ ∑ _m ∈ Icc 1 Q, β * (Q : ℝ) * (α ^ 2 / L) := sum_le_sum hpoint
      _ = (β * α ^ 2) * ((Q : ℝ) ^ 2 / L) := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring
      _ ≤ (β * α ^ 2) * (L ^ (13 / 16 : ℝ) / L) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hQ2 hL0.le) (by positivity)
      _ = (β * α ^ 2) * (L ^ (13 / 16 : ℝ) / L ^ (1 : ℝ)) := by rw [Real.rpow_one]
      _ = (β * α ^ 2) * L ^ (-3 / 16 : ℝ) := by
        rw [← Real.rpow_sub hL0]
        norm_num

/-- The complete mixed mass above overlap vanishes after restoring its reference diagonal. -/
theorem tendsto_upper_critical_packet_complete_mixed_mass
    {h : ℝ → ℝ} {A B : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hB : ∀ y, |h y| ≤ B)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      ∑ m ∈ (Icc 1 ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊).filter (fun m => c N < (m : ℝ)),
        ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
            (normalizedRamanujanHorizonVector m N),
          horizonProfileVector (horizonWeights h N) N⟫ ^ 2 /
          (c N * completedConductorEnergy tiltedUnitSpline (c N) m)) atTop (𝓝 0) := by
  have ht := ((tendsto_upper_critical_packet_residual_mixed_mass hsupp hB hc hR hcrit).const_mul 2).add
    ((tendsto_critical_packet_reference_mixed_mass hsupp hB hc).const_mul 2)
  simp only [mul_zero, zero_add] at ht
  apply squeeze_zero _ _ ht
  · intro N
    apply sum_nonneg
    intro m hm
    exact div_nonneg (sq_nonneg _) (mul_nonneg (zero_le_one.trans (hc N))
      (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_support
        integral_tiltedUnitSpline_sq_pos (zero_lt_one.trans_le (hc N))
        (mem_Icc.mp (mem_filter.mp hm).1).1))
  · intro N
    let Q := ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊
    let S := (Icc 1 Q).filter (fun m => c N < (m : ℝ))
    let E := fun m => completedConductorEnergy tiltedUnitSpline (c N) m
    let v := fun m => normalizedRamanujanHorizonVector m N
    let x := horizonProfileVector (horizonWeights h N) N
    let p := fun m => ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) (v m), x⟫
    let d := fun m => E m * ⟪v m, x⟫
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    have hpoint : ∀ m ∈ S, p m ^ 2 / (c N * E m) ≤
        2 * ((p m - d m) ^ 2 / (c N * E m)) +
          2 * (E m / c N * ⟪v m, x⟫ ^ 2) := by
      intro m hm
      have hm0 := (mem_Icc.mp (mem_filter.mp hm).1).1
      have hE0 : 0 < E m := tiltedSplineSpectralFloorConstant_pos.trans_le
        (tiltedUnitSpline_completedConductorEnergy_ge_above_overlap hc0 hm0
          (mem_filter.mp hm).2.le)
      have hs : p m ^ 2 ≤ 2 * (p m - d m) ^ 2 + 2 * d m ^ 2 := by
        nlinarith only [sq_nonneg (p m - 2 * d m)]
      have hd : d m ^ 2 / (c N * E m) = E m / c N * ⟪v m, x⟫ ^ 2 := by
        dsimp only [d]
        field_simp [hc0.ne', hE0.ne']
      calc
        _ ≤ 2 * ((p m - d m) ^ 2 / (c N * E m)) + 2 * (d m ^ 2 / (c N * E m)) :=
          (div_le_div_of_nonneg_right hs (mul_pos hc0 hE0).le).trans_eq (by ring)
        _ = _ := by rw [hd]
    have href : (∑ m ∈ S, E m / c N * ⟪v m, x⟫ ^ 2) ≤
        ∑ m ∈ Icc 1 Q, E m / c N * ⟪v m, x⟫ ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro m hm _
      exact mul_nonneg (div_nonneg
        (completedConductorEnergy_nonneg contDiff_tiltedUnitSpline tiltedUnitSpline_support
          integral_tiltedUnitSpline_sq_pos hc0 (mem_Icc.mp hm).1) hc0.le) (sq_nonneg _)
    calc
      _ ≤ ∑ m ∈ S, 2 * ((p m - d m) ^ 2 / (c N * E m)) +
          2 * (E m / c N * ⟪v m, x⟫ ^ 2) := sum_le_sum hpoint
      _ = 2 * (∑ m ∈ S, (p m - d m) ^ 2 / (c N * E m)) +
          2 * (∑ m ∈ S, E m / c N * ⟪v m, x⟫ ^ 2) := by
        rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      _ ≤ 2 * (∑ m ∈ S, (p m - d m) ^ 2 / (c N * E m)) +
          2 * (∑ m ∈ Icc 1 Q, E m / c N * ⟪v m, x⟫ ^ 2) :=
        add_le_add_left (mul_le_mul_of_nonneg_left href (by norm_num)) _
      _ = _ := by simp only [inner_sub_left, real_inner_smul_left]; rfl

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_above_overlap_normalized_residual_sum_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_upper_critical_packet_residual_mass_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_upper_critical_packet_residual_mixed_mass
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_critical_packet_reference_mixed_mass
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_upper_critical_packet_complete_mixed_mass
