import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorQuasimodesHavePolynomialError
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorEnergiesHavePolynomialBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheTiltedSplineHasAPolynomialConductorFloor
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.PrimeResidueSourcesHaveQuantitativeLogDecay
import GaloisForLFunctions.HTGeometry.FiniteGramApproximationCertificate
import GaloisForLFunctions.SignedArithmeticHodgeTheory.GrowingRamanujanFamiliesHaveAUniformGramBudget
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeEnergyHasFiniteRamanujanCoordinates

/-!
# Positive conductor packets at prescribed growing overlap

The actual completed-conductor residual has polynomial overlap cost. Quantitative
Gram bounds and a positive Fourier-tail floor therefore preserve positivity on
any fixed finite conductor span throughout `1 ≤ c ≤ (log N)^A`, `0 ≤ A < 1/48`.
All poles, prime powers, and horizon cutoffs remain in the complete Weil matrix.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem log_rpow_div_rpow_tendsto_zero (p : ℝ) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun x : ℝ => Real.log x ^ p / x ^ q) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p q hq).comp Real.tendsto_log_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def, Real.rpow_def_of_pos hx, div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  ring

private theorem iterated_log_rpow_div_log_rpow_tendsto_zero (p : ℝ) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) ^ p / Real.log (N : ℝ) ^ q) atTop (𝓝 0) := by
  exact (log_rpow_div_rpow_tendsto_zero p hq).comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

private theorem iterated_log_power_limit (A : ℝ) (k : ℕ) {q : ℝ} (hq : 0 < q) :
    Tendsto (fun N : ℕ => (Real.log (Real.log (N : ℝ)) ^ A) ^ k /
      Real.log (N : ℝ) ^ q) atTop (𝓝 0) := by
  apply (iterated_log_rpow_div_log_rpow_tendsto_zero (A * (k : ℝ)) hq).congr'
  have hlim := Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hlim.eventually_ge_atTop 0] with N hN
  simp only [Function.comp_def] at hN
  rw [Real.rpow_mul hN, Real.rpow_natCast]

private theorem log_power_ratio_limit (A : ℝ) (k : ℕ) {q : ℝ}
    (hq : A * (k : ℝ) < q) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) ^ A) ^ k /
      Real.log (N : ℝ) ^ q) atTop (𝓝 0) := by
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply ((tendsto_rpow_neg_atTop (sub_pos.mpr hq)).comp hloglim).congr'
  filter_upwards [hloglim.eventually_gt_atTop 0] with N hN
  simp only [Function.comp_def]
  calc
    Real.log (N : ℝ) ^ (-(q - A * (k : ℝ))) =
        Real.log (N : ℝ) ^ (A * (k : ℝ) - q) := by congr 1; ring
    _ = _ := by rw [Real.rpow_sub hN, Real.rpow_mul hN.le, Real.rpow_natCast]

private theorem log_power_div_nat_limit (A : ℝ) (k : ℕ) :
    Tendsto (fun N : ℕ => (Real.log (N : ℝ) ^ A) ^ k / N) atTop (𝓝 0) := by
  have h := (log_rpow_div_rpow_tendsto_zero (A * (k : ℝ))
    (by norm_num : (0 : ℝ) < 1)).comp tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  simp only [Function.comp_def, Real.rpow_one]
  rw [Real.rpow_mul (Real.log_natCast_nonneg N), Real.rpow_natCast]

private theorem eventually_log_power_error_le (A C : ℝ) (hC : 0 ≤ C) (k : ℕ)
    {q ε : ℝ} (hq : A * (k : ℝ) < q) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ A →
      C * c ^ k / Real.log (N : ℝ) ^ q ≤ ε := by
  have hlim : Tendsto (fun N : ℕ => C * (Real.log (N : ℝ) ^ A) ^ k /
      Real.log (N : ℝ) ^ q) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using (log_power_ratio_limit A k hq).const_mul C
  filter_upwards [hlim.eventually (ge_mem_nhds hε)] with N hN
  intro c hc hupper
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hc) hupper k) hC)
    (Real.rpow_nonneg (Real.log_natCast_nonneg N) q)).trans hN

private theorem eventually_log_horizon {A P : ℝ} (hP : 0 ≤ P) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ A →
      P * c ^ 2 ≤ (N : ℝ) := by
  have hlim : Tendsto (fun N : ℕ => P * (Real.log (N : ℝ) ^ A) ^ 2 / N)
      atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using (log_power_div_nat_limit A 2).const_mul P
  filter_upwards [hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1)), eventually_ge_atTop 1]
    with N hsmall hN
  intro c hc hupper
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlarge := (div_le_one hN0).mp hsmall
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hc) hupper 2) hP).trans hlarge

private theorem finite_energy_error_of_entry_bound {I E : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →ₗ[ℝ] E) (v : I → E) (energy a : I → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hentry : ∀ i j, |⟪A (v i), v j⟫ - if i = j then energy i else 0| ≤ ε) :
    |⟪A (∑ i, a i • v i), ∑ i, a i • v i⟫ - ∑ i, energy i * a i ^ 2| ≤
      (Fintype.card I : ℝ) * ε * ∑ i, a i ^ 2 := by
  have henergy : ⟪A (∑ i, a i • v i), ∑ i, a i • v i⟫ =
      ∑ i, ∑ j, a i * a j * ⟪A (v i), v j⟫ := by
    simp only [map_sum, map_smul, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring
  have hdiag : (∑ i, ∑ j, a i * a j * (if i = j then energy i else 0)) =
      ∑ i, energy i * a i ^ 2 := by
    simp only [mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true]
    exact sum_congr rfl fun i _ => by ring
  have hdiff : ⟪A (∑ i, a i • v i), ∑ i, a i • v i⟫ - ∑ i, energy i * a i ^ 2 =
      ∑ i, ∑ j, a i * a j * (⟪A (v i), v j⟫ - if i = j then energy i else 0) := by
    rw [henergy, ← hdiag, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ => by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun j _ => by ring
  rw [hdiff]
  calc
    _ ≤ ∑ i, ∑ j, |a i| * |a j| * ε := by
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
      refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun j _ => ?_)
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hentry i j) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = (∑ i, |a i|) ^ 2 * ε := by
      rw [sq, sum_mul_sum, sum_mul]
      exact sum_congr rfl fun i _ => by rw [sum_mul]
    _ ≤ ((Fintype.card I : ℝ) * ∑ i, a i ^ 2) * ε := by
      apply mul_le_mul_of_nonneg_right _ hε
      simpa only [one_mul, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, sq_abs] using
        (sum_mul_sq_le_sq_mul_sq (univ : Finset I) (fun _ => (1 : ℝ)) (fun i => |a i|))
    _ = _ := by ring

private theorem harmonic_log_error_le (N : ℕ) :
    |(∑ n ∈ Icc 1 N, 1 / (n : ℝ)) - Real.log N| ≤ 1 := by
  have hlo : Real.log N ≤ (harmonic N : ℝ) := by
    simpa only [Nat.floor_natCast] using log_le_harmonic_floor (N : ℝ) (Nat.cast_nonneg N)
  have hup := harmonic_le_one_add_log N
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hlo hup
  simp only [← one_div] at hlo hup
  rw [abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith only [hup]

private theorem normalized_ramanujan_gram_error (m l : ℕ+) {N : ℕ}
    (hN : 0 < Real.log (N : ℝ)) :
    |⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
      if m = l then 1 else 0| ≤ (1 + 2 * (m : ℝ) * (l : ℝ)) / Real.log N := by
  let δ : ℝ := if m = l then 1 else 0
  have hδ : |δ| ≤ 1 := by dsimp only [δ]; split_ifs <;> norm_num
  have hgram := SignedArithmeticHodgeTheory.ramanujanPoleProfile_gram_error_le m l N
  have hlog : |δ * ((∑ n ∈ Icc 1 N, 1 / (n : ℝ)) - Real.log N)| ≤ 1 := by
    rw [abs_mul]
    exact (mul_le_mul hδ (harmonic_log_error_le N) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hraw : |(∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) -
      δ * Real.log N| ≤ 1 + 2 * (m : ℝ) * (l : ℝ) := by
    calc
      _ = |((∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) -
          δ * (∑ n ∈ Icc 1 N, 1 / (n : ℝ))) +
          δ * ((∑ n ∈ Icc 1 N, 1 / (n : ℝ)) - Real.log N)| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans ((add_le_add hgram hlog).trans_eq (add_comm _ _))
  rw [normalizedRamanujanHorizonVector_inner]
  change |(∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) / Real.log N - δ| ≤ _
  have heq : (∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) / Real.log N - δ =
      ((∑ n ∈ Icc 1 N, ramanujanPoleProfile m n * ramanujanPoleProfile l n) - δ * Real.log N) / Real.log N := by
    field_simp [hN.ne']
  rw [heq, abs_div, abs_of_pos hN]
  exact div_le_div_of_nonneg_right hraw hN.le

/-- The actual norm error is negligible relative to the polynomial conductor floor. -/
theorem eventually_tiltedUnitSpline_completed_residual_weighted_small
    {m : ℕ} (hm : 0 < m) {A ε : ℝ} (_hA : 0 ≤ A) (hAupper : A < 1 / 48) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ A →
      c ^ 7 * ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
        (normalizedRamanujanHorizonVector m N) - completedConductorEnergy tiltedUnitSpline c m •
        normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  obtain ⟨K, hK, hres⟩ :=
    exists_tiltedUnitSpline_completedConductor_residual_sq_polynomial_bound hm
  have hsmall := eventually_log_power_error_le A K hK.le 24
    (by norm_num; linarith only [hAupper] : A * (24 : ℝ) < 1 / 2) (sq_pos_of_pos hε)
  have hhorizon := eventually_log_horizon (A := A)
    (show 0 ≤ 4 * (Real.exp 1 + 3) ^ 2 by positivity)
  filter_upwards [hres, hsmall, hhorizon] with N hresN hsmallN hhorizonN
  intro c hc hupper
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hr := hresN c hc (hhorizonN c hc hupper)
  have hs := hsmallN c hc hupper
  rw [← Real.sqrt_eq_rpow] at hs
  have hsq : (c ^ 7 * ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
        (normalizedRamanujanHorizonVector m N) - completedConductorEnergy tiltedUnitSpline c m •
        normalizedRamanujanHorizonVector m N‖) ^ 2 ≤ ε ^ 2 := by
    calc
      _ = c ^ 14 * ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) - completedConductorEnergy tiltedUnitSpline c m •
          normalizedRamanujanHorizonVector m N‖ ^ 2 := by ring
      _ ≤ c ^ 14 * (K * c ^ 10 / Real.sqrt (Real.log N)) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = K * c ^ 24 / Real.sqrt (Real.log N) := by ring
      _ ≤ ε ^ 2 := hs
  exact (sq_le_sq₀ (by positivity) hε.le).mp hsq

/-- Each literal mixed entry approaches its completed diagonal uniformly at growing overlap,
with an error negligible relative to the common positive conductor floor. -/
theorem eventually_tiltedUnitSpline_completed_entry_weighted_small
    (m l : ℕ+) {A ε : ℝ} (hA : 0 ≤ A) (hAupper : A < 1 / 48) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ A →
      c ^ 7 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
        (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector l N⟫ -
        if m = l then completedConductorEnergy tiltedUnitSpline c m else 0| ≤ ε := by
  obtain ⟨C, hC, henergy⟩ := exists_completedConductorEnergy_polynomial_bound
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos m.property
  let G : ℝ := 1 + 2 * (m : ℝ) * (l : ℝ)
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hgram := eventually_log_power_error_le A (C * G)
    (mul_nonneg hC.le hG) 9 (by linarith only [hA, hAupper] : A * (9 : ℝ) < 1)
    (show 0 < ε / 2 by positivity)
  have hres := eventually_tiltedUnitSpline_completed_residual_weighted_small m.property hA hAupper
    (show 0 < ε / 4 by positivity)
  have hnorm : ∀ᶠ N : ℕ in atTop, ‖normalizedRamanujanHorizonVector l N‖ ≤ 2 := by
    have h := (tendsto_normalizedRamanujanHorizonVector_norm_sq l.property).eventually
      (ge_mem_nhds (by norm_num : (1 : ℝ) < 2))
    filter_upwards [h] with N hN
    exact (sq_le_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).mp
      (hN.trans (by norm_num : (2 : ℝ) ≤ 2 ^ 2))
  have hloglim := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hgram, hres, hnorm, hloglim.eventually_gt_atTop 0] with N hg hr hn hlog
  intro c hc hupper
  let v := normalizedRamanujanHorizonVector (m : ℕ) N
  let w := normalizedRamanujanHorizonVector (l : ℕ) N
  let T := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
  let energy := completedConductorEnergy tiltedUnitSpline c (m : ℕ)
  let δ : ℝ := if m = l then 1 else 0
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have he : ⟪T v, w⟫ - (if m = l then energy else 0) =
      energy * (⟪v, w⟫ - δ) + ⟪T v - energy • v, w⟫ := by
    rw [inner_sub_left, real_inner_smul_left]
    dsimp only [δ]
    split_ifs <;> ring
  have hmain : c ^ 7 * (|energy| * |⟪v, w⟫ - δ|) ≤ ε / 2 := by
    calc
      _ ≤ c ^ 7 * ((C * c ^ 2) * (G / Real.log N)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul (henergy c hc) (normalized_ramanujan_gram_error m l hlog)
            (abs_nonneg _) (by positivity)) (by positivity)
      _ = C * G * c ^ 9 / Real.log N := by ring
      _ ≤ ε / 2 := by simpa only [Real.rpow_one] using hg c hc hupper
  have hrem : c ^ 7 * |⟪T v - energy • v, w⟫| ≤ ε / 2 := by
    calc
      _ ≤ c ^ 7 * (‖T v - energy • v‖ * ‖w‖) :=
        mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (T v - energy • v) w) (by positivity)
      _ = (c ^ 7 * ‖T v - energy • v‖) * ‖w‖ := by ring
      _ ≤ (ε / 4) * 2 := mul_le_mul (hr c hc hupper) hn (norm_nonneg _) (by positivity)
      _ = ε / 2 := by ring
  change c ^ 7 * |⟪T v, w⟫ - (if m = l then energy else 0)| ≤ ε
  rw [he]
  calc
    _ ≤ c ^ 7 * (|energy| * |⟪v, w⟫ - δ| + |⟪T v - energy • v, w⟫|) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [abs_mul] using abs_add_le (energy * (⟪v, w⟫ - δ)) ⟪T v - energy • v, w⟫
    _ = c ^ 7 * (|energy| * |⟪v, w⟫ - δ|) + c ^ 7 * |⟪T v - energy • v, w⟫| := by ring
    _ ≤ ε / 2 + ε / 2 := add_le_add hmain hrem
    _ = ε := by ring

/-- One horizon gives a positive actual complete-Weil form on every vector in a fixed finite
conductor span, simultaneously throughout any prescribed logarithmic overlap range. -/
theorem eventually_tiltedUnitSpline_finite_packet_energy_ge_growing_overlap
    (S : Finset ℕ+) {A : ℝ} (hA : 0 ≤ A) (hAupper : A < 1 / 48) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ A →
      ∀ a : S → ℝ,
        (tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)) / c ^ 7 * (∑ m, a m ^ 2) ≤
          completeWeilEnergy tiltedUnitSpline c N
            (∑ m : S, a m • normalizedRamanujanHorizonVector (m.val : ℕ) N) := by
  classical
  let δ : ℝ := 2 * tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)
  let d : ℝ := Fintype.card S
  have hδ : 0 < δ := div_pos (mul_pos (by norm_num) tiltedSplineTailConstant_pos)
    integral_tiltedUnitSpline_sq_pos
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hd1 : 0 < d + 1 := by positivity
  let ε : ℝ := δ / (2 * (d + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hentries : ∀ᶠ N : ℕ in atTop, ∀ m l : S, ∀ c : ℝ,
      1 ≤ c → c ≤ Real.log (N : ℝ) ^ A →
      c ^ 7 * |⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
        (normalizedRamanujanHorizonVector (m.val : ℕ) N),
        normalizedRamanujanHorizonVector (l.val : ℕ) N⟫ -
        if m = l then completedConductorEnergy tiltedUnitSpline c (m.val : ℕ) else 0| ≤ ε := by
    apply Filter.eventually_all.mpr
    intro m
    apply Filter.eventually_all.mpr
    intro l
    simpa only [Subtype.ext_iff] using
      eventually_tiltedUnitSpline_completed_entry_weighted_small m.val l.val hA hAupper hε
  filter_upwards [hentries] with N hN
  intro c hc hupper a
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hc7 : 0 < c ^ 7 := pow_pos hc0 _
  let v : S → EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    fun m => normalizedRamanujanHorizonVector (m.val : ℕ) N
  let T := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
  let energy : S → ℝ := fun m => completedConductorEnergy tiltedUnitSpline c (m.val : ℕ)
  have herr := finite_energy_error_of_entry_bound T v energy a (div_nonneg hε.le hc7.le)
    (fun m l => (le_div_iff₀ hc7).mpr (by simpa only [mul_comm] using hN m l c hc hupper))
  have hfloor : δ / c ^ 7 * (∑ m, a m ^ 2) ≤ ∑ m, energy m * a m ^ 2 := by
    rw [mul_sum]
    exact sum_le_sum fun m _ => mul_le_mul_of_nonneg_right
      (tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hc m.val.property) (sq_nonneg _)
  have hcost : d * (ε / c ^ 7) ≤ δ / (2 * c ^ 7) := by
    apply (le_div_iff₀ (mul_pos (by norm_num) hc7)).mpr
    have hid : (d * (ε / c ^ 7)) * (2 * c ^ 7) = δ * (d / (d + 1)) := by
      dsimp only [ε]
      field_simp [hc7.ne', hd1.ne']
    rw [hid]
    exact (mul_le_mul_of_nonneg_left ((div_le_one hd1).mpr (by linarith only)) hδ.le).trans_eq (mul_one δ)
  have hsum : 0 ≤ ∑ m, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have herror := (abs_le.mp herr).1
  have hcostsum := mul_le_mul_of_nonneg_right hcost hsum
  have hsplit : δ / c ^ 7 * (∑ m, a m ^ 2) =
      δ / (2 * c ^ 7) * (∑ m, a m ^ 2) + δ / (2 * c ^ 7) * (∑ m, a m ^ 2) := by ring
  have hresult : δ / (2 * c ^ 7) * (∑ m, a m ^ 2) ≤ ⟪T (∑ m, a m • v m), ∑ m, a m • v m⟫ := by
    change -(d * (ε / c ^ 7) * ∑ m, a m ^ 2) ≤ _ at herror
    linarith only [herror, hfloor, hcostsum, hsplit]
  have hfactor : δ / (2 * c ^ 7) =
      (tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)) / c ^ 7 := by
    dsimp only [δ]
    ring
  rw [hfactor] at hresult
  exact hresult

/-- Every nonzero coefficient packet has strictly positive actual energy at the same common
horizon throughout the prescribed growing-overlap range. -/
theorem eventually_tiltedUnitSpline_finite_packet_energy_pos_growing_overlap
    (S : Finset ℕ+) {A : ℝ} (hA : 0 ≤ A) (hAupper : A < 1 / 48) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (N : ℝ) ^ A →
      ∀ a : S → ℝ, a ≠ 0 →
        0 < completeWeilEnergy tiltedUnitSpline c N
          (∑ m : S, a m • normalizedRamanujanHorizonVector (m.val : ℕ) N) := by
  classical
  filter_upwards [eventually_tiltedUnitSpline_finite_packet_energy_ge_growing_overlap S hA hAupper]
    with N hN
  intro c hc hupper a ha
  have hex : ∃ m, a m ≠ 0 := by
    by_contra h
    apply ha
    funext m
    exact not_not.mp (fun hm => h ⟨m, hm⟩)
  obtain ⟨m, hm⟩ := hex
  have hsum : 0 < ∑ i, a i ^ 2 :=
    (sq_pos_of_ne_zero hm).trans_le (single_le_sum (fun i _ => sq_nonneg (a i)) (mem_univ m))
  have hcoef : 0 < (tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)) / c ^ 7 :=
    div_pos (div_pos tiltedSplineTailConstant_pos integral_tiltedUnitSpline_sq_pos)
      (pow_pos (zero_lt_one.trans_le hc) _)
  exact (mul_pos hcoef hsum).trans_le (hN c hc hupper a)

/-- Every fixed power of the iterated logarithm is contained in the positive overlap range. -/
theorem eventually_tiltedUnitSpline_finite_packet_energy_ge_iterated_log_overlap
    (S : Finset ℕ+) (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (Real.log (N : ℝ)) ^ A →
      ∀ a : S → ℝ,
        (tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)) / c ^ 7 * (∑ m, a m ^ 2) ≤
          completeWeilEnergy tiltedUnitSpline c N
            (∑ m : S, a m • normalizedRamanujanHorizonVector (m.val : ℕ) N) := by
  have hpacket := eventually_tiltedUnitSpline_finite_packet_energy_ge_growing_overlap S
    (by norm_num : (0 : ℝ) ≤ 1 / 100) (by norm_num : (1 : ℝ) / 100 < 1 / 48)
  have hsmall := (iterated_log_power_limit A 1 (by norm_num : (0 : ℝ) < 1 / 100)).eventually
    (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hpacket, hsmall, hloglim.eventually_gt_atTop 0] with N hN hs hlog
  intro c hc hupper a
  simp only [pow_one] at hs
  have hbound := (div_le_one (Real.rpow_pos_of_pos hlog ((1 : ℝ) / 100))).mp hs
  exact hN c hc (hupper.trans hbound) a

/-- Iterated-logarithmic growing overlap preserves strict positivity for every nonzero packet. -/
theorem eventually_tiltedUnitSpline_finite_packet_energy_pos_iterated_log_overlap
    (S : Finset ℕ+) (A : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (Real.log (N : ℝ)) ^ A →
      ∀ a : S → ℝ, a ≠ 0 →
        0 < completeWeilEnergy tiltedUnitSpline c N
          (∑ m : S, a m • normalizedRamanujanHorizonVector (m.val : ℕ) N) := by
  classical
  filter_upwards [eventually_tiltedUnitSpline_finite_packet_energy_ge_iterated_log_overlap S A]
    with N hN
  intro c hc hupper a ha
  have hex : ∃ m, a m ≠ 0 := by
    by_contra h
    apply ha
    funext m
    exact not_not.mp (fun hm => h ⟨m, hm⟩)
  obtain ⟨m, hm⟩ := hex
  have hsum : 0 < ∑ i, a i ^ 2 :=
    (sq_pos_of_ne_zero hm).trans_le (single_le_sum (fun i _ => sq_nonneg (a i)) (mem_univ m))
  have hcoef : 0 < (tiltedSplineTailConstant / (∫ u, tiltedUnitSpline u ^ 2)) / c ^ 7 :=
    div_pos (div_pos tiltedSplineTailConstant_pos integral_tiltedUnitSpline_sq_pos)
      (pow_pos (zero_lt_one.trans_le hc) _)
  exact (mul_pos hcoef hsum).trans_le (hN c hc hupper a)

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completed_residual_weighted_small
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completed_entry_weighted_small
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_finite_packet_energy_ge_growing_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_finite_packet_energy_pos_growing_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_finite_packet_energy_ge_iterated_log_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_finite_packet_energy_pos_iterated_log_overlap
