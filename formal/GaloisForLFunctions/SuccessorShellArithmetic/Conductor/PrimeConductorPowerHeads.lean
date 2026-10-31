import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorGrowingCorrection
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.PrimeConductorLogMoment
import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.HarmonicGramUniformRemainder
import GaloisForLFunctions.RHTower.VonMangoldtLogSummatory

/-!
# Prime heads at power cutoffs

The exact harmonic Gram remainder controls the undilated part of the
hyperbolic prime head. Mertens' constant and its logarithmic moment give
the cutoff polynomial. The centered correction retains the positive
torsion edge, which cancels its negative Gram contribution at the
square-root cutoff.
-/

open Filter Topology Finset ArithmeticFunction
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory RenormalizedBiarithmeticGeometry
  ArithmeticEffectivityTheory ArithmeticIntersectionTheory
noncomputable section

private def conductorGram (m l Y : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 Y, normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)

private def conductorGramConstant (m l : ℕ) : ℝ :=
  (if m = l then Real.eulerMascheroniConstant else 0) -
    orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))

private theorem gram_ratio_remainder {m l k N : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hk : 0 < k) (hkN : k ≤ N) :
    |conductorGram m l (N / k) -
        (if m = l then Real.log N - Real.log k else 0) - conductorGramConstant m l| ≤
      (4 * (m : ℝ) * l + 2) / (N / k : ℕ) := by
  have hq : 1 ≤ N / k := (Nat.le_div_iff_mul_le hk).mpr (by simpa using hkN)
  have hqR : (0 : ℝ) < (N / k : ℕ) := by exact_mod_cast hq
  have hr := abs_normalizedRamanujan_harmonicGram_log_remainder hm hl hq
  have hround := roundoff_le hk hkN
  have hbase : 4 * (m : ℝ) * l / (((N / k : ℕ) : ℝ) + 1) ≤
      4 * (m : ℝ) * l / (N / k : ℕ) :=
    div_le_div_of_nonneg_left (by positivity) hqR (by linarith)
  change |conductorGram m l (N / k) - (if m = l then Real.log (N / k : ℕ) else 0) -
    conductorGramConstant m l| ≤ _ at hr
  by_cases hml : m = l
  · simp only [if_pos hml] at hr ⊢
    calc
      _ = |(conductorGram m l (N / k) - Real.log (N / k : ℕ) - conductorGramConstant m l) -
          (Real.log N - Real.log (N / k : ℕ) - Real.log k)| := by congr 1; ring
      _ ≤ |conductorGram m l (N / k) - Real.log (N / k : ℕ) - conductorGramConstant m l| +
          |Real.log N - Real.log (N / k : ℕ) - Real.log k| := abs_sub _ _
      _ ≤ (4 * (m : ℝ) * l / (((N / k : ℕ) : ℝ) + 1) + 1 / (N / k : ℕ)) + 1 / (N / k : ℕ) := by
        rw [abs_of_nonneg hround.1]
        exact add_le_add hr hround.2
      _ ≤ (4 * (m : ℝ) * l / (N / k : ℕ) + 1 / (N / k : ℕ)) + 1 / (N / k : ℕ) :=
        add_le_add (add_le_add hbase le_rfl) le_rfl
      _ = _ := by ring
  · simp only [if_neg hml, sub_zero, zero_div, add_zero] at hr ⊢
    have hpos : 0 ≤ 2 / ((N / k : ℕ) : ℝ) := by positivity
    rw [add_div]
    linarith only [hr, hbase, hpos]

private theorem inv_nat_quotient_le {k N : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    (1 : ℝ) / (N / k : ℕ) ≤ 2 * k / N := by
  have hq : 1 ≤ N / k := (Nat.le_div_iff_mul_le hk).mpr (by simpa using hkN)
  have hN : 0 < N := hk.trans_le hkN
  have hqR : (1 : ℝ) ≤ (N / k : ℕ) := by exact_mod_cast hq
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hltR := _root_.RHTower.Mertens.cast_div_lt N k hk
  rw [div_lt_iff₀ hkR] at hltR
  rw [div_le_div_iff₀ (by linarith : (0 : ℝ) < (N / k : ℕ)) hNR]
  nlinarith only [hltR, mul_le_mul_of_nonneg_left hqR hkR.le]

private def undilatedPrimeHead (m l K N : ℕ) : ℝ :=
  2 * ∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) * conductorGram m l (N / k) / Real.log N

private def primeLogMoment (K : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) * Real.log k

private def undilatedPrimeHeadMain (m l K N : ℕ) : ℝ :=
  (if m = l then 2 * (mertensSum K - primeLogMoment K / Real.log N) else 0) +
    2 * conductorGramConstant m l * (mertensSum K / Real.log N)

private theorem undilatedPrimeHeadMain_eq (m l K N : ℕ) (hN : Real.log (N : ℝ) ≠ 0) :
    undilatedPrimeHeadMain m l K N =
      2 * ∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) *
        ((if m = l then Real.log N - Real.log k else 0) + conductorGramConstant m l) / Real.log N := by
  unfold undilatedPrimeHeadMain mertensSum primeLogMoment
  by_cases hml : m = l
  · simp only [if_pos hml, mul_add, mul_sub, add_div, sub_div, sum_add_distrib,
      sum_sub_distrib, ← sum_mul, ← sum_div]
    field_simp [hN]
  · simp only [if_neg hml, zero_add, ← sum_div, ← sum_mul]
    ring

private theorem undilatedPrimeHead_remainder {m l K N : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hK : K ≤ N) (hN : 2 ≤ N) :
    ‖undilatedPrimeHead m l K N - undilatedPrimeHeadMain m l K N‖ ≤
      28 * (4 * (m : ℝ) * l + 2) / Real.log N := by
  let C : ℝ := 4 * (m : ℝ) * l + 2
  let e : ℕ → ℝ := fun k => conductorGram m l (N / k) -
    ((if m = l then Real.log N - Real.log k else 0) + conductorGramConstant m l)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hterm (k : ℕ) (hk : k ∈ Icc 1 K) :
      |vonMangoldt k / (k : ℝ) * e k| ≤ 2 * C / N * vonMangoldt k := by
    have hk0 := (mem_Icc.mp hk).1
    have hkN := (mem_Icc.mp hk).2.trans hK
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hweight : 0 ≤ vonMangoldt k / (k : ℝ) :=
      div_nonneg vonMangoldt_nonneg hkR.le
    have he : |e k| ≤ C * (1 / ((N / k : ℕ) : ℝ)) := by
      simpa only [e, C, sub_add_eq_sub_sub, mul_one_div] using gram_ratio_remainder hm hl hk0 hkN
    calc
      _ = vonMangoldt k / (k : ℝ) * |e k| := by rw [abs_mul, abs_of_nonneg hweight]
      _ ≤ vonMangoldt k / (k : ℝ) * (C * (1 / ((N / k : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left he hweight
      _ ≤ vonMangoldt k / (k : ℝ) * (C * (2 * k / N)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (inv_nat_quotient_le hk0 hkN) hC) hweight
      _ = _ := by field_simp [hkR.ne']
  have hsum : |∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) * e k| ≤ 14 * C := by
    calc
      _ ≤ ∑ k ∈ Icc 1 K, |vonMangoldt k / (k : ℝ) * e k| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Icc 1 K, 2 * C / N * vonMangoldt k := sum_le_sum hterm
      _ = 2 * C / N * _root_.RHTower.chebyshevPsi K := by rw [← mul_sum]; rfl
      _ ≤ 2 * C / N * (7 * K) :=
        mul_le_mul_of_nonneg_left (_root_.RHTower.chebyshevPsi_le_seven K) (by positivity)
      _ ≤ 2 * C / N * (7 * N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hK) (by norm_num)
      _ = _ := by field_simp [hNR.ne']; ring
  have heq : undilatedPrimeHead m l K N - undilatedPrimeHeadMain m l K N =
      2 * (∑ k ∈ Icc 1 K, vonMangoldt k / (k : ℝ) * e k) / Real.log N := by
    rw [undilatedPrimeHead, undilatedPrimeHeadMain_eq m l K N hlog.ne']
    simp only [← sum_div]
    rw [← mul_sub, ← sub_div, ← sum_sub_distrib, mul_div_assoc]
    apply congrArg (fun x : ℝ => 2 * (x / Real.log N))
    exact sum_congr rfl fun k _ => by dsimp only [e]; ring
  rw [heq, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hlog]
  norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    _ ≤ 2 * (14 * C) / Real.log N :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) hlog.le
    _ = _ := by dsimp only [C]; ring

private theorem tendsto_undilatedPrimeHead_remainder {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) {K : ℕ → ℕ} (hK : ∀ᶠ N in atTop, K N ≤ N) :
    Tendsto (fun N : ℕ => undilatedPrimeHead m l (K N) N - undilatedPrimeHeadMain m l (K N) N)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ => 28 * (4 * (m : ℝ) * l + 2) / Real.log N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [hK, eventually_ge_atTop 2] with N hKN hN
  exact undilatedPrimeHead_remainder hm hl hKN hN

/-- The inclusive dilation cutoff at a positive power of the horizon. -/
def primePowerHeadCutoff (θ : ℝ) (N : ℕ) : ℕ := ⌊(N : ℝ) ^ θ⌋₊

private theorem primePowerHeadCutoff_tendsto {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (primePowerHeadCutoff θ) atTop atTop := by
  change Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ θ⌋₊) atTop atTop
  simpa only [Function.comp_def] using
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop)

private theorem primePowerHeadCutoff_le {θ : ℝ} (hθ : θ ≤ 1) {N : ℕ} (hN : 1 ≤ N) :
    primePowerHeadCutoff θ N ≤ N := by
  have h := (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) θ)).trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hθ)
  rw [Real.rpow_one] at h
  exact_mod_cast h

private theorem tendsto_log_primePowerHeadCutoff_sub {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun N => Real.log (primePowerHeadCutoff θ N) - θ * Real.log N) atTop (𝓝 0) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ θ) atTop atTop :=
    (tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop
  have hfloor := primePowerHeadCutoff_tendsto hθ
  have hratio := tendsto_nat_floor_div_atTop.comp hp
  have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
  simp only [Real.log_one] at h
  apply h.congr'
  filter_upwards [hfloor.eventually_ge_atTop 1, eventually_ge_atTop 1] with N hK hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hKR : (primePowerHeadCutoff θ N : ℝ) ≠ 0 := by exact_mod_cast (show primePowerHeadCutoff θ N ≠ 0 by omega)
  change Real.log ((primePowerHeadCutoff θ N : ℝ) / (N : ℝ) ^ θ) = _
  rw [Real.log_div hKR (Real.rpow_pos_of_pos hNR θ).ne', Real.log_rpow hNR]

private theorem tendsto_undilatedPrimeHeadMain_finitePart {m l : ℕ}
    {K : ℕ → ℕ} {θ : ℝ} (hK : Tendsto K atTop atTop)
    (hscale : Tendsto (fun N => Real.log (K N) - θ * Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => undilatedPrimeHeadMain m l (K N) N -
      (if m = l then θ * (2 - θ) * Real.log N else 0)) atTop
      (𝓝 ((if m = l then -2 * Real.eulerMascheroniConstant else 0) +
        2 * conductorGramConstant m l * θ)) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hratio : Tendsto (fun N => Real.log (K N) / Real.log N) atTop (𝓝 θ) := by
    have h := (hscale.div_atTop hlog).add_const θ
    simp only [zero_add] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hL : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    field_simp [hL]
    ring
  have hM : Tendsto (fun N => mertensSum (K N) - Real.log (K N))
      atTop (𝓝 (-Real.eulerMascheroniConstant)) := by
    simpa only [Function.comp_def] using tendsto_mertensSum_sub_log.comp hK
  have hA : Tendsto (fun N => mertensSum (K N) / Real.log N) atTop (𝓝 θ) := by
    have h := (hM.div_atTop hlog).add hratio
    simp only [zero_add] at h
    exact h.congr fun N => by rw [sub_div]; ring
  have hmoment : Tendsto (fun N =>
      (primeLogMoment (K N) - Real.log (K N) ^ 2 / 2) / Real.log N) atTop (𝓝 0) := by
    have h := (tendsto_primeHeadLogMoment_remainder.comp hK).mul hratio
    simp only [zero_mul] at h
    apply h.congr'
    filter_upwards [hK.eventually_ge_atTop 2] with N hN
    have hL : Real.log (K N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < K N by omega))).ne'
    dsimp only [Function.comp_def, primeLogMoment]
    field_simp [hL]
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2) := tendsto_const_nhds
  have hscalar := ((hM.sub hmoment).const_mul 2).add
    (hscale.mul ((htwo.sub hratio).sub_const θ))
  have hscalar' : Tendsto (fun N => 2 * (mertensSum (K N) - primeLogMoment (K N) / Real.log N) -
      θ * (2 - θ) * Real.log N) atTop (𝓝 (-2 * Real.eulerMascheroniConstant)) := by
    have hval : 2 * (-Real.eulerMascheroniConstant - 0) + 0 * (2 - θ - θ) =
        -2 * Real.eulerMascheroniConstant := by ring
    rw [hval] at hscalar
    apply hscalar.congr'
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hL : Real.log (N : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
    field_simp [hL]
    ring
  by_cases hml : m = l
  · have h := hscalar'.add (hA.const_mul (2 * conductorGramConstant m l))
    simp only [if_pos hml]
    apply h.congr
    intro N
    rw [undilatedPrimeHeadMain, if_pos hml]
    ring
  · simpa only [undilatedPrimeHeadMain, if_neg hml, zero_add, sub_zero] using
      hA.const_mul (2 * conductorGramConstant m l)

private theorem growing_head_sub_correction_eq (m l K N : ℕ) :
    primeConductorHeadPairing m l (K + 1) N -
      2 * ∑ k ∈ range (K + 1), vonMangoldt k / (k : ℝ) *
        ((∑ n ∈ Icc 1 (N / k), normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ)) /
          Real.log N) =
      primeConductorHeadPairing m l (K + 1) N - undilatedPrimeHead m l K N := by
  have hset : range (K + 1) = insert 0 (Icc 1 K) := by
    ext k
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, sum_insert (by simp)]
  simp only [Nat.cast_zero, div_zero, zero_mul, zero_add, undilatedPrimeHead,
    conductorGram, mul_div_assoc]

/-- At every power cutoff, the full mixed finite part is an affine torsion coefficient. -/
theorem tendsto_primeConductorPowerHead_finitePart {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    Tendsto (fun N : ℕ => primeConductorHeadPairing m l (primePowerHeadCutoff θ N + 1) N -
      (if m = l then θ * (2 - θ) * Real.log N else 0)) atTop
      (𝓝 ((1 - 2 * θ) * orbitIntersection m l /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m +
          2 * (1 - θ) * Real.eulerMascheroniConstant else 0))) := by
  have hK := primePowerHeadCutoff_tendsto hθ
  have hK' : Tendsto (fun N => primePowerHeadCutoff θ N + 1) atTop atTop := by
    simpa only [Function.comp_def] using (tendsto_add_atTop_nat 1).comp hK
  have hc := tendsto_primeConductorGrowingHead_correction hm hl hK'
  simp only [growing_head_sub_correction_eq] at hc
  have hrem := tendsto_undilatedPrimeHead_remainder hm hl
    (show ∀ᶠ N : ℕ in atTop, primePowerHeadCutoff θ N ≤ N from
      (eventually_ge_atTop 1).mono fun N hN => primePowerHeadCutoff_le hθ1 hN)
  have hmain := tendsto_undilatedPrimeHeadMain_finitePart (m := m) (l := l)
    hK (tendsto_log_primePowerHeadCutoff_sub hθ)
  have h := (hc.add hrem).add hmain
  have hval : (orbitIntersection m l /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m else 0) + 0) +
      ((if m = l then -2 * Real.eulerMascheroniConstant else 0) +
        2 * conductorGramConstant m l * θ) =
      (1 - 2 * θ) * orbitIntersection m l /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m +
          2 * (1 - θ) * Real.eulerMascheroniConstant else 0) := by
    unfold conductorGramConstant
    split_ifs <;> ring
  rw [hval] at h
  exact h.congr fun N => by ring

/-- The square-root prime head has an exactly diagonal conductor finite part. -/
theorem tendsto_primeConductorSqrtHead_finitePart {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => primeConductorHeadPairing m l (⌊Real.sqrt (N : ℝ)⌋₊ + 1) N -
      (if m = l then (3 / 4 : ℝ) * Real.log N else 0)) atTop
      (𝓝 (if m = l then -(Real.eulerMascheroniConstant + Real.log m + tameDifferent m) else 0)) := by
  have h := tendsto_primeConductorPowerHead_finitePart hm hl
    (θ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hv : (1 - 2 * (1 / 2 : ℝ)) * orbitIntersection m l /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
      (if m = l then Real.log m + tameDifferent m +
        2 * (1 - (1 / 2 : ℝ)) * Real.eulerMascheroniConstant else 0) =
      if m = l then -(Real.eulerMascheroniConstant + Real.log m + tameDifferent m) else 0 := by
    split_ifs <;> ring
  rw [hv] at h
  norm_num only [primePowerHeadCutoff, ← Real.sqrt_eq_rpow, show (1 / 2 : ℝ) * (2 - 1 / 2) = 3 / 4 by norm_num] at h
  exact h

#print axioms tendsto_primeConductorPowerHead_finitePart
#print axioms tendsto_primeConductorSqrtHead_finitePart

private theorem tendsto_log_normalizedGram_finitePart {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => Real.log N *
      ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        (if m = l then Real.log N else 0)) atTop (𝓝 (conductorGramConstant m l)) := by
  have hprofile (n : ℕ) : ramanujanPoleProfile m n * ramanujanPoleProfile l n =
      normalizedRamanujanMode m n * normalizedRamanujanMode l n / (n : ℝ) := by
    unfold ramanujanPoleProfile
    rw [div_mul_div_comm, ← sq, Real.sq_sqrt (Nat.cast_nonneg n)]
  apply (tendsto_normalizedRamanujan_harmonicGram_torsion hm hl).congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  rw [normalizedRamanujanHorizonVector_inner]
  simp_rw [hprofile]
  field_simp [hlog]

/-- Scalar-identity centering retains exactly `1-θ²` times the harmonic Gram finite part. -/
theorem tendsto_primeConductorPowerHead_renormalized {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    Tendsto (fun N : ℕ => θ * (2 - θ) * Real.log N *
      ⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        primeConductorHeadPairing m l (primePowerHeadCutoff θ N + 1) N) atTop
      (𝓝 ((if m = l then ramanujanAdjunctionEnergy m else 0) +
        (1 - θ ^ 2) * ((if m = l then Real.eulerMascheroniConstant else 0) -
          orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))))) := by
  have h := ((tendsto_log_normalizedGram_finitePart hm hl).const_mul (θ * (2 - θ))).sub
    (tendsto_primeConductorPowerHead_finitePart hm hl hθ hθ1)
  have hval : θ * (2 - θ) * conductorGramConstant m l -
      ((1 - 2 * θ) * orbitIntersection m l /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m +
          2 * (1 - θ) * Real.eulerMascheroniConstant else 0)) =
      (if m = l then ramanujanAdjunctionEnergy m else 0) +
        (1 - θ ^ 2) * ((if m = l then Real.eulerMascheroniConstant else 0) -
          orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))) := by
    unfold conductorGramConstant ramanujanAdjunctionEnergy
    split_ifs <;> ring
  rw [hval] at h
  apply h.congr
  intro N
  split_ifs <;> ring

#print axioms tendsto_primeConductorPowerHead_renormalized

/-- Every band between power cutoffs carries twice its logarithmic width times the Gram finite part. -/
theorem tendsto_primeConductorPowerBand_finitePart {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) {α β : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    Tendsto (fun N : ℕ =>
      primeConductorHeadPairing m l (primePowerHeadCutoff β N + 1) N -
      primeConductorHeadPairing m l (primePowerHeadCutoff α N + 1) N -
      (if m = l then (β * (2 - β) - α * (2 - α)) * Real.log N else 0)) atTop
      (𝓝 (2 * (β - α) * ((if m = l then Real.eulerMascheroniConstant else 0) -
        orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))))) := by
  have h := (tendsto_primeConductorPowerHead_finitePart hm hl hβ hβ1).sub
    (tendsto_primeConductorPowerHead_finitePart hm hl hα hα1)
  have hval :
      ((1 - 2 * β) * orbitIntersection m l /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m +
          2 * (1 - β) * Real.eulerMascheroniConstant else 0)) -
      ((1 - 2 * α) * orbitIntersection m l /
        (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ)) -
        (if m = l then Real.log m + tameDifferent m +
          2 * (1 - α) * Real.eulerMascheroniConstant else 0)) =
      2 * (β - α) * ((if m = l then Real.eulerMascheroniConstant else 0) -
        orbitIntersection m l / (Real.sqrt (m.totient : ℝ) * Real.sqrt (l.totient : ℝ))) := by
    split_ifs <;> ring
  rw [hval] at h
  apply h.congr
  intro N
  split_ifs <;> ring

#print axioms tendsto_primeConductorPowerBand_finitePart

end
end GaloisForLFunctions.SuccessorShellArithmetic
