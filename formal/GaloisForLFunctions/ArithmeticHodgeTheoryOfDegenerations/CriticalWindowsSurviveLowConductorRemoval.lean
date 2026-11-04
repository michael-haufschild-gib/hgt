import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.WindowConductorCoordinatesVanishUniformly
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCriticalLowPacketHasAUniformResidualBudget
import GaloisForLFunctions.CompletedArithmeticForms.ConductorEnergiesHaveAUniformLogarithmicUpperBound
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingConstantOfTheTiltedSpline
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ATwistedCompleteWeilMatrixIsDecidedByItsRamanujanPackets

/-!
# Removing low conductors preserves a critical window

Terminal windows have small coordinates in the actual conductor frame.
The inverse-energy residual budget controls the complete operator on
their entire low-conductor projection, including its mixed energy.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CompletedArithmeticForms
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis

private theorem norm_sum_smul_sq_le {ι E : Type*} [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Finset ι) (b : ι → ℝ) (v : ι → E) :
    ‖∑ m ∈ S, b m • v m‖ ^ 2 ≤
      (∑ m ∈ S, b m ^ 2) * ∑ m ∈ S, ‖v m‖ ^ 2 := by
  have htri : ‖∑ m ∈ S, b m • v m‖ ≤ ∑ m ∈ S, |b m| * ‖v m‖ := by
    simpa only [norm_smul, Real.norm_eq_abs] using norm_sum_le (s := S) (fun m => b m • v m)
  calc
    _ ≤ (∑ m ∈ S, |b m| * ‖v m‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ _ := by
      simpa only [sq_abs] using
        Finset.sum_mul_sq_le_sq_mul_sq S (fun m => |b m|) (fun m => ‖v m‖)

private theorem low_packet_action_sq_le {Q N : ℕ} (hQ : 2 ≤ Q)
    (hQN : Q * Q ≤ N) (hlog : 18 * (1 + Real.log Q) ≤ Real.log N)
    {c U V : ℝ} (hc : 1 ≤ c) (hU : 0 ≤ U)
    (hE : ∀ m ∈ Icc 1 Q, completedConductorEnergy tiltedUnitSpline c m ≤ U)
    (hbudget : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m •
          normalizedRamanujanHorizonVector m N‖ ^ 2 /
        completedConductorEnergy tiltedUnitSpline c m) ≤ V)
    (b : ℕ → ℝ) :
    ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
        (∑ m ∈ Icc 1 Q, b m • normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
      (3 * U ^ 2 + 2 * U * V) * ∑ m ∈ Icc 1 Q, b m ^ 2 := by
  let v := fun m => normalizedRamanujanHorizonVector m N
  let E := completedConductorEnergy tiltedUnitSpline c
  let B := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
  let r := fun m => B (v m) - E m • v m
  let d := ∑ m ∈ Icc 1 Q, (E m * b m) • v m
  let z := ∑ m ∈ Icc 1 Q, b m • r m
  let S := ∑ m ∈ Icc 1 Q, b m ^ 2
  have hS : 0 ≤ S := sum_nonneg fun _ _ => sq_nonneg _
  have hpos : ∀ m ∈ Icc 1 Q, 0 < E m := by
    intro m hm
    exact (div_pos tiltedSplineSpectralFloorConstant_pos
      (pow_pos (zero_lt_one.trans_le hc) 7)).trans_le
        (tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hc (mem_Icc.mp hm).1)
  have hr : (∑ m ∈ Icc 1 Q, ‖r m‖ ^ 2) ≤ U * V := by
    calc
      _ ≤ ∑ m ∈ Icc 1 Q, U * (‖r m‖ ^ 2 / E m) := by
        apply sum_le_sum
        intro m hm
        calc
          _ = E m * (‖r m‖ ^ 2 / E m) := by field_simp [(hpos m hm).ne']
          _ ≤ _ := mul_le_mul_of_nonneg_right (hE m hm)
            (div_nonneg (sq_nonneg _) (hpos m hm).le)
      _ = U * ∑ m ∈ Icc 1 Q, ‖r m‖ ^ 2 / E m := (mul_sum _ _ _).symm
      _ ≤ U * V := mul_le_mul_of_nonneg_left hbudget hU
  have hz : ‖z‖ ^ 2 ≤ S * (U * V) :=
    (norm_sum_smul_sq_le (Icc 1 Q) b r).trans (mul_le_mul_of_nonneg_left hr hS)
  have hd : ‖d‖ ^ 2 ≤ (3 / 2 : ℝ) * (U ^ 2 * S) := by
    refine (half_and_three_halves_riesz_of_log_le hQ hQN hlog (fun m => E m * b m)).2.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      _ ≤ ∑ m ∈ Icc 1 Q, U ^ 2 * b m ^ 2 := by
        apply sum_le_sum
        intro m hm
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hpos m hm).le (hE m hm) 2)
          (sq_nonneg _)
      _ = _ := (mul_sum _ _ _).symm
  have hexpand : B (∑ m ∈ Icc 1 Q, b m • v m) = d + z := by
    simp only [d, z, r, map_sum, map_smul, ← sum_add_distrib, smul_sub, smul_smul]
    apply sum_congr rfl
    intro m hm
    rw [mul_comm (E m) (b m)]
    abel
  change ‖B (∑ m ∈ Icc 1 Q, b m • v m)‖ ^ 2 ≤ (3 * U ^ 2 + 2 * U * V) * S
  rw [hexpand]
  have htri := pow_le_pow_left₀ (norm_nonneg (d + z)) (norm_add_le d z) 2
  nlinarith only [htri, hd, hz, sq_nonneg (‖d‖ - ‖z‖)]

/-- The complete operator sends a terminal window's entire low-conductor projection to zero,
with an eventual inverse-quarter-logarithm square bound at every critical ratio. -/
theorem eventually_completeWeil_window_projection_action_sq_le {h : ℝ → ℝ} {A M : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hM : ∀ y, |h y| ≤ M)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop,
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        ((conductorSubspace ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊ N).starProjection
          (horizonProfileVector (horizonWeights h N) N))‖ ^ 2 ≤
        1 / Real.log N ^ (1 / 4 : ℝ) := by
  let C : ℝ := |completeWeilSelfFinitePart tiltedUnitSpline 1| + 5
  let D : ℝ := 2 * M * Real.exp A
  have hC : 0 < C := by dsimp only [C]; positivity
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLN := criticalCurve_pow_log_div_natCast hc hR hcrit 0 2
  simp only [pow_zero, one_mul] at hLN
  filter_upwards [eventually_critical_low_packet_residual_budget hc hR hcrit,
    hlog.eventually_ge_atTop 1, eventually_ge_atTop 1,
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 13 / 32)).comp hlog).eventually_ge_atTop 2,
    hLN.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hlog.eventually (eventually_mul_rpow_polylog_le_rpow (by norm_num : (0 : ℝ) < 1) 1 18),
    hlog.eventually (eventually_mul_rpow_polylog_le_rpow
      (by norm_num : (-11 / 32 : ℝ) < -1 / 4) 2 (4 * D ^ 2 * (3 * C ^ 2 + 2 * C)))]
    with N hbudget hL1 hN hQpow2 hLN hlogsmall hsmall
  let L : ℝ := Real.log N
  let Q : ℕ := ⌊L ^ (13 / 32 : ℝ)⌋₊
  let U : ℝ := 1 + Real.log L
  let x := horizonProfileVector (horizonWeights h N) N
  let p := (conductorSubspace Q N).starProjection x
  change 1 ≤ L at hL1
  change 2 ≤ L ^ (13 / 32 : ℝ) at hQpow2
  change 18 * L ^ (0 : ℝ) * U ^ 1 ≤ L ^ (1 : ℝ) at hlogsmall
  change 4 * D ^ 2 * (3 * C ^ 2 + 2 * C) * L ^ (-11 / 32 : ℝ) * U ^ 2 ≤
    L ^ (-1 / 4 : ℝ) at hsmall
  have hL0 : 0 < L := zero_lt_one.trans_le hL1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hU1 : 1 ≤ U := by dsimp only [U]; linarith [Real.log_nonneg hL1]
  have hU0 : 0 ≤ U := zero_le_one.trans hU1
  have hQ2 : 2 ≤ Q := Nat.le_floor hQpow2
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (by omega : 0 < Q)
  have hQpow : (Q : ℝ) ≤ L ^ (13 / 32 : ℝ) := Nat.floor_le (Real.rpow_nonneg hL0.le _)
  have hQL : (Q : ℝ) ≤ L := hQpow.trans
    ((Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (13 / 32 : ℝ) ≤ 1)).trans_eq
      (Real.rpow_one L))
  have hQN : Q * Q ≤ N := by
    have hs : (Q : ℝ) ^ 2 ≤ N :=
      (pow_le_pow_left₀ (Nat.cast_nonneg Q) hQL 2).trans ((div_le_one hN0).mp hLN.le)
    exact_mod_cast (show (Q : ℝ) * Q ≤ N by simpa only [pow_two] using hs)
  have hlogQ : 18 * (1 + Real.log Q) ≤ Real.log N := by
    have hq := Real.log_le_log hQ0 hQL
    have hs : 18 * U ≤ L := by
      simpa only [Real.rpow_zero, mul_one, pow_one, Real.rpow_one] using hlogsmall
    dsimp only [U, L] at hs
    linarith only [hq, hs]
  have hE : ∀ m ∈ Icc 1 Q,
      completedConductorEnergy tiltedUnitSpline (c N) m ≤ C * U := by
    intro m hm
    have hm1 := (mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have hmL : (m : ℝ) ≤ L := (by exact_mod_cast (mem_Icc.mp hm).2 : (m : ℝ) ≤ Q).trans hQL
    have he := completedConductorEnergy_le_logarithmic_uniform contDiff_tiltedUnitSpline
      tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (hc N) hm1
    have hl := Real.log_le_log hm0 hmL
    have hcl : 0 ≤ (C - 2) * Real.log L :=
      mul_nonneg (by dsimp only [C]; linarith [abs_nonneg (completeWeilSelfFinitePart tiltedUnitSpline 1)])
        (Real.log_nonneg hL1)
    dsimp only [C, U] at hcl ⊢
    linarith only [he, hl, hcl]
  have hp : p ∈ conductorSubspace Q N := (conductorSubspace Q N).starProjection_apply_mem x
  obtain ⟨b, -, hb⟩ := (mem_conductorSubspace_iff (x := p)).mp hp
  have hframe := (half_and_three_halves_riesz_of_log_le hQ2 hQN hlogQ b).1
  rw [← hb] at hframe
  have hproj := horizon_window_conductor_projection_sq_le hsupp hM hQ2 hQN hlogQ
  change ‖p‖ ^ 2 ≤ 2 * D ^ 2 * Q / L at hproj
  have hcoef : (∑ m ∈ Icc 1 Q, b m ^ 2) ≤ 4 * D ^ 2 * Q / L := by
    calc
      _ ≤ 2 * ‖p‖ ^ 2 := by linarith only [hframe]
      _ ≤ 2 * (2 * D ^ 2 * Q / L) := mul_le_mul_of_nonneg_left hproj (by norm_num)
      _ = _ := by ring
  have haction := low_packet_action_sq_le hQ2 hQN hlogQ (hc N)
    (mul_nonneg hC.le hU0) hE hbudget b
  rw [← hb] at haction
  have hLquarter : 1 ≤ L ^ (1 / 4 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hfactor : 3 * (C * U) ^ 2 + 2 * (C * U) * L ^ (1 / 4 : ℝ) ≤
      (3 * C ^ 2 + 2 * C) * U ^ 2 * L ^ (1 / 4 : ℝ) := by
    have hu : U ≤ U ^ 2 := by
      simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hU1 hU0
    have h₁ := mul_le_mul_of_nonneg_left hLquarter (by positivity : 0 ≤ 3 * C ^ 2 * U ^ 2)
    have h₂ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hu (by positivity : 0 ≤ 2 * C))
      (Real.rpow_nonneg hL0.le (1 / 4 : ℝ))
    nlinarith only [h₁, h₂]
  change ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N) p‖ ^ 2 ≤
    1 / L ^ (1 / 4 : ℝ)
  calc
    _ ≤ (3 * (C * U) ^ 2 + 2 * (C * U) * L ^ (1 / 4 : ℝ)) *
        ∑ m ∈ Icc 1 Q, b m ^ 2 := haction
    _ ≤ ((3 * C ^ 2 + 2 * C) * U ^ 2 * L ^ (1 / 4 : ℝ)) *
        (4 * D ^ 2 * Q / L) := mul_le_mul hfactor hcoef
          (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
    _ ≤ ((3 * C ^ 2 + 2 * C) * U ^ 2 * L ^ (1 / 4 : ℝ)) *
        (4 * D ^ 2 * L ^ (13 / 32 : ℝ) / L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQpow (by positivity)) hL0.le
    _ = 4 * D ^ 2 * (3 * C ^ 2 + 2 * C) * L ^ (-11 / 32 : ℝ) * U ^ 2 := by
      rw [show (-11 / 32 : ℝ) = 1 / 4 + 13 / 32 + -1 by norm_num,
        Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_neg_one]
      ring
    _ ≤ L ^ (-1 / 4 : ℝ) := hsmall
    _ = _ := by
      rw [show (-1 / 4 : ℝ) = -(1 / 4) by ring, Real.rpow_neg hL0.le]
      simp only [one_div]

/-- At every critical ratio the complete image of the removed low packet tends to zero. -/
theorem tendsto_completeWeil_window_projection_action_norm {h : ℝ → ℝ} {A M : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hM : ∀ y, |h y| ≤ M)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
        ((conductorSubspace ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊ N).starProjection
          (horizonProfileVector (horizonWeights h N) N))‖) atTop (𝓝 0) := by
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun N : ℕ => 1 / Real.log N ^ (1 / 4 : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hlog)
  have hs := squeeze_zero' (Eventually.of_forall fun N => sq_nonneg
    ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      ((conductorSubspace ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊ N).starProjection
        (horizonProfileVector (horizonWeights h N) N))‖)
      (eventually_completeWeil_window_projection_action_sq_le hsupp hM hc hR hcrit) hinv
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
    (Real.continuous_sqrt.tendsto 0).comp hs

/-- Removing the full polylogarithmic conductor projection changes a terminal window's
unnormalized complete energy by a quantity tending to zero. -/
theorem tendsto_completeWeil_window_projection_energy_difference {h : ℝ → ℝ} {A M : ℝ}
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (hM : ∀ y, |h y| ≤ M)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      let x := horizonProfileVector (horizonWeights h N) N
      let p := (conductorSubspace ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊ N).starProjection x
      let B := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      ⟪B (x - p), x - p⟫ - ⟪B x, x⟫) atTop (𝓝 0) := by
  let C : ℝ := Real.sqrt (M ^ 2 * Real.exp A)
  let f := fun N : ℕ =>
    ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      ((conductorSubspace ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊ N).starProjection
        (horizonProfileVector (horizonWeights h N) N))‖
  have hf : Tendsto f atTop (𝓝 0) :=
    tendsto_completeWeil_window_projection_action_norm hsupp hM hc hR hcrit
  have hlim : Tendsto (fun N => 3 * C * f N) atTop (𝓝 0) := by
    simpa only [mul_zero] using hf.const_mul (3 * C)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  let x := horizonProfileVector (horizonWeights h N) N
  let P := (conductorSubspace ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊ N).starProjection
  let p := P x
  let B := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
  have hx : ‖x‖ ≤ C := by
    have hsq := horizon_window_norm_sq_le hsupp hM hN
    have hC := Real.sq_sqrt (by positivity : 0 ≤ M ^ 2 * Real.exp A)
    have hC0 := Real.sqrt_nonneg (M ^ 2 * Real.exp A)
    change ‖x‖ ^ 2 ≤ M ^ 2 * Real.exp A at hsq
    dsimp only [C]
    nlinarith only [hsq, hC, hC0, norm_nonneg x]
  have hp : ‖p‖ ≤ C :=
    ((conductorSubspace ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊ N).norm_starProjection_apply_le x).trans hx
  have hsym : ⟪B x, p⟫ = ⟪B p, x⟫ := by
    rw [(Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (completeWeilMatrix_isHermitian tiltedUnitSpline (c N) N)) x p, real_inner_comm]
  have hid : ⟪B (x - p), x - p⟫ - ⟪B x, x⟫ =
      -2 * ⟪B p, x⟫ + ⟪B p, p⟫ := by
    rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hsym]
    ring
  have h₁ : |⟪B p, x⟫| ≤ ‖B p‖ * C :=
    (abs_real_inner_le_norm (B p) x).trans (mul_le_mul_of_nonneg_left hx (norm_nonneg _))
  have h₂ : |⟪B p, p⟫| ≤ ‖B p‖ * C :=
    (abs_real_inner_le_norm (B p) p).trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
  change ‖⟪B (x - p), x - p⟫ - ⟪B x, x⟫‖ ≤ 3 * C * f N
  rw [Real.norm_eq_abs, hid]
  calc
    _ ≤ |-2 * ⟪B p, x⟫| + |⟪B p, p⟫| := abs_add_le _ _
    _ = 2 * |⟪B p, x⟫| + |⟪B p, p⟫| := by rw [abs_mul]; norm_num
    _ ≤ 2 * (‖B p‖ * C) + ‖B p‖ * C :=
      add_le_add (mul_le_mul_of_nonneg_left h₁ (by norm_num)) h₂
    _ = _ := by dsimp only [f, B, p, P, x]; ring

/-- The same compensated critical Weil limit is carried by the complement of the entire
polylogarithmic conductor packet. -/
theorem horizon_layer_criticalCurve_exact_after_low_projection {h : ℝ → ℝ} {A : ℝ}
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ =>
      let x := horizonProfileVector (horizonWeights h N) N
      let p := (conductorSubspace ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊ N).starProjection x
      let B := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      (c N)⁻¹ * ⟪B (x - p), x - p⟫) atTop
      (𝓝 ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight h) +
        7 * tiltedJordanOne / R * ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) := by
  obtain ⟨M, _, hM, _⟩ := exists_bound_lipschitz hh hsupp
  let x := fun N : ℕ => horizonProfileVector (horizonWeights h N) N
  let p := fun N : ℕ => (conductorSubspace ⌊Real.log N ^ (13 / 32 : ℝ)⌋₊ N).starProjection (x N)
  let B := fun N : ℕ => Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
  have hbase : Tendsto (fun N : ℕ => (c N)⁻¹ * ⟪B N (x N), x N⟫) atTop
      (𝓝 ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) * weilQuad (halfWeight h) +
        7 * tiltedJordanOne / R * ∫ y, Real.exp (-(8 * y)) * halfWeight h y ^ 2)) := by
    refine (horizon_layer_criticalCurve_exact hh hA hsupp hc hR hcrit).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    dsimp only [B, x]
    rw [completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline tiltedUnitSpline_support
      (zero_lt_one.trans_le (hc N)) hN]
    have htest := atomicTest_congr (N := N)
      (x := primeHorizonExtension (horizonProfileVector (horizonWeights h N) N))
      (x' := horizonWeights h N)
      (fun n hn => primeHorizonExtension_coe (horizonProfileVector (horizonWeights h N) N) ⟨n, hn⟩)
      (atomDilate tiltedUnitSpline (c N / N))
    rw [htest]
  have hdiff : Tendsto (fun N : ℕ =>
      ⟪B N (x N - p N), x N - p N⟫ - ⟪B N (x N), x N⟫) atTop (𝓝 0) :=
    tendsto_completeWeil_window_projection_energy_difference hsupp hM hc hR hcrit
  have hinv := tendsto_inv_atTop_zero.comp (criticalCurve_facts hc hR hcrit).1
  have hzero := hinv.mul hdiff
  simp only [mul_zero] at hzero
  have hsum := hbase.add hzero
  simp only [add_zero] at hsum
  refine hsum.congr fun N => ?_
  dsimp only [B, x, p, Function.comp_apply]
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.eventually_completeWeil_window_projection_action_sq_le
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_completeWeil_window_projection_action_norm
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tendsto_completeWeil_window_projection_energy_difference
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.horizon_layer_criticalCurve_exact_after_low_projection
