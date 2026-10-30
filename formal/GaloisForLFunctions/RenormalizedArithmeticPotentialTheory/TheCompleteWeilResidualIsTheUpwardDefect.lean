import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheReplacementErrorsVanishAtEveryOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheFullDownwardPrimeRowCancelsTheNearGammaRow

/-!
# At every overlap the complete Weil residual is the upward prime defect

Let `v` be the normalized Ramanujan vector of conductor `m` and `E_m(c)` the completed conductor
energy. At every fixed overlap ratio `c > 0` the residual `W v − E_m(c) v` of the complete Weil
matrix is, up to a term vanishing in norm, minus the *upward defect*

`Up v / ‖g‖² − S_m(c) v`, `S_m(c) = 2/(M φ(m)) Σ_{1≤h<c} c_m(h) ∫_{h/c}^1 G(u)/u du`,

where `Up` collects the non-ratio prime windows pairing `n` with indices near `kn`
(`tendsto_completeWeilMatrix_ramanujan_residual_add_upward_norm`). Every other block of the exact
decomposition vanishes: the ratio prime residual, the self and pole errors, the center residual and
the far cross error, and the near block. There the archimedean pairing `log(N/c) G` of nearby atoms
is cancelled by the downward prime products through `Σ_{d∣ℓ} Λ(d) = log ℓ`, and the near center
kernel, of size `O(N)`, carries the coefficient `α/N`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  BezoutValuationIncidence HTGeometry CompletedShell
open _root_.RHTower (archLevyDensity)

variable {φ : ℝ → ℝ}

/-- The upward non-ratio prime windows at the atom mass. -/
def upwardPrimeVector (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => upwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension x) n /
    (∫ u, atomDilate φ (c / N) u ^ 2))

/-- The downward non-ratio prime windows at the atom mass. -/
def downwardPrimeVector (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => downwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension x) n /
    (∫ u, atomDilate φ (c / N) u ^ 2))

/-- The center kernel restricted to near pairs, on the normalized Ramanujan vector. -/
def nearCenterVector (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  WithLp.toLp 2 (fun n => (∑ j ∈ nearRowIndices c N n,
    completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j /
      Real.sqrt j) / Real.sqrt (Real.log N))

/-- The downward row only reads its vector on the horizon, linearly. -/
theorem downwardPrimeRow_congr_smul {g : ℝ → ℝ} {N n : ℕ} {x y : ℕ → ℝ} {r : ℝ}
    (h : ∀ j ∈ Icc 1 N, x j = r * y j) :
    downwardPrimeRow g N x n = r * downwardPrimeRow g N y n := by
  unfold downwardPrimeRow
  have hk : ∀ k : ℕ, _root_.RHTower.vonMangoldtAtom k * ∑ j ∈ Icc 1 N, x j *
      (if n = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j))) =
      r * (_root_.RHTower.vonMangoldtAtom k * ∑ j ∈ Icc 1 N, y j *
        (if n = k * j then 0 else bumpCorr g (Real.log k - (Real.log n - Real.log j)))) := by
    intro k
    rw [mul_left_comm r]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [h j hj]
    ring
  simp_rw [hk]
  exact tsum_mul_left

/-- A near pair has log-gap in `[1/N, 2c/N]`, so its center entry is at most `N/2 + e^{1/2}/4`. -/
theorem abs_nearCenter_entry_le {c : ℝ} {N n j : ℕ} {m : ℕ} (hm : 0 < m) (hN : 1 ≤ N)
    (hcN : 2 * c ≤ N) (hn : n ∈ Icc 1 N) (hj : j ∈ nearRowIndices c N n) :
    |completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j| ≤
      |completeWeilPoleShift φ c| * (1 + Real.exp (1 / 2)) *
        ∑ i ∈ range m, |normalizedRamanujanMode m i| := by
  obtain ⟨hjN, hjn, hlog⟩ := mem_filter.mp hj
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hn1 := (mem_Icc.mp hn).1
  have hj1 := (mem_Icc.mp hjN).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
  set y := |Real.log j - Real.log n| with hy
  have hkernel : archimedeanCenterKernel n j = archLevyDensity y := by
    unfold archimedeanCenterKernel
    rw [if_neg (by push Not; exact ⟨Ne.symm hjn, by omega, by omega⟩)]
  -- the integer gap bounds the log-gap from below by `1/N`
  have hgap : 1 / (N : ℝ) ≤ y := by
    have h := gap_div_le_abs_log_div hj1 hn1 hjn
    rw [Real.log_div hj0.ne' hn0.ne'] at h
    have hd : (1 : ℝ) ≤ |(j : ℝ) - n| := by
      rcases lt_or_gt_of_ne hjn with h' | h'
      · have hR : (j : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr h')
        rw [abs_of_neg (by linarith only [hR])]
        linarith only [hR]
      · have hR : (n : ℝ) + 1 ≤ j := by exact_mod_cast (Nat.succ_le_iff.mpr h')
        rw [abs_of_pos (by linarith only [hR])]
        linarith only [hR]
    have hmax0 : 0 < max (j : ℝ) n := hj0.trans_le (le_max_left _ _)
    have hmaxN : max (j : ℝ) n ≤ N :=
      max_le (by exact_mod_cast (mem_Icc.mp hjN).2) (by exact_mod_cast (mem_Icc.mp hn).2)
    calc 1 / (N : ℝ) ≤ 1 / max (j : ℝ) n := one_div_le_one_div_of_le hmax0 hmaxN
      _ ≤ |(j : ℝ) - n| / max (j : ℝ) n := div_le_div_of_nonneg_right hd hmax0.le
      _ ≤ y := h
  have hy0 : 0 < y := lt_of_lt_of_le (by positivity) hgap
  have hy1 : y ≤ 1 := hlog.trans ((div_le_one hN0).mpr hcN)
  have hD0 : 0 < archLevyDensity y := RHTower.archLevyDensity_pos hy0
  have hD : archLevyDensity y ≤ N / 2 + Real.exp (1 / 2) / 4 := by
    refine (archLevyDensity_le_inv_two_mul_add hy0 hy1).trans ?_
    have : 1 / (2 * y) ≤ N / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have := (div_le_iff₀ hN0).mp hgap
      linarith
    linarith
  have ha := abs_normalizedRamanujanMode_le hm j
  have he : 0 < Real.exp (1 / 2) := Real.exp_pos _
  rw [hkernel, abs_mul, abs_mul, abs_div, abs_of_pos hN0, abs_of_pos hD0]
  have hcoef : |completeWeilPoleShift φ c| / N * archLevyDensity y ≤
      |completeWeilPoleShift φ c| * (1 + Real.exp (1 / 2)) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hN0, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  calc |completeWeilPoleShift φ c| / N * archLevyDensity y * |normalizedRamanujanMode m j|
      ≤ |completeWeilPoleShift φ c| * (1 + Real.exp (1 / 2)) * |normalizedRamanujanMode m j| :=
        mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left ha (by positivity)

theorem nearCenterVector_norm_sq (φ : ℝ → ℝ) (c : ℝ) (N m : ℕ) :
    ‖nearCenterVector φ c N m‖ ^ 2 =
      (∑ n ∈ Icc 1 N, (∑ j ∈ nearRowIndices c N n,
        completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j /
          Real.sqrt j) ^ 2) / Real.log N := by
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ n : PrimeHorizonIndex N, ((∑ j ∈ nearRowIndices c N n,
    completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j /
      Real.sqrt j) / Real.sqrt (Real.log N)) ^ 2) = _
  simp only [div_pow (∑ j ∈ _, _), Real.sq_sqrt (Real.log_natCast_nonneg N)]
  rw [← sum_div]
  congr 1
  exact sum_coe_sort (Icc 1 N) (fun n => (∑ j ∈ nearRowIndices c N n,
    completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j /
      Real.sqrt j) ^ 2)

/-- The near center block vanishes in norm on every normalized Ramanujan mode. -/
theorem tendsto_nearCenterVector_norm (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => ‖nearCenterVector φ c N m‖) atTop (𝓝 0) := by
  set K := |completeWeilPoleShift φ c| * (1 + Real.exp (1 / 2)) *
    ∑ i ∈ range m, |normalizedRamanujanMode m i| with hK
  have hsq : Tendsto (fun N : ℕ => ‖nearCenterVector φ c N m‖ ^ 2) atTop (𝓝 0) := by
    have hlim : Tendsto (fun N : ℕ => 4 * nearRowRadius c ^ 3 * K ^ 2 / Real.log N) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    refine squeeze_zero' (Eventually.of_forall fun N => sq_nonneg _) ?_ hlim
    filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈2 * c⌉₊] with N hN hNc
    have hcN : 2 * c ≤ (N : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hNc)
    rw [nearCenterVector_norm_sq]
    exact div_le_div_of_nonneg_right (sum_near_div_sqrt_sq_le hc hN
      (fun n j => completeWeilPoleShift φ c / N * archimedeanCenterKernel n j *
        normalizedRamanujanMode m j)
      (fun n hn j hj => abs_nearCenter_entry_le hm hN hcN hn hj)) (Real.log_natCast_nonneg N)
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

/-- The overlap block is the downward prime row plus the signed near-Gamma residual and the near
center block. -/
theorem overlapMatrix_ramanujan_row_eq (φ : ℝ → ℝ) (c : ℝ) {N m : ℕ} (hm : 0 < m)
    (n : PrimeHorizonIndex N) :
    (Matrix.toEuclideanLin (overlapMatrix φ c N) (normalizedRamanujanHorizonVector m N)) n =
      downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) n +
        ((Real.sqrt (m.totient : ℝ))⁻¹ * normalizedFullNearGammaDownwardVector φ c N m n +
          nearCenterVector φ c N m n) := by
  set s := (Real.sqrt (Real.log N))⁻¹ with hs
  set r := (Real.sqrt (m.totient : ℝ))⁻¹ with hr
  have hext : ∀ j ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) j =
      (s * r) * (ramanujanLagCoefficient m j / Real.sqrt j) := by
    intro j hj
    rw [primeHorizonExtension, dif_pos hj]
    change s * ramanujanPoleProfile m j = _
    rw [ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient hm, hr]
    ring
  have hdown := downwardPrimeRow_congr_smul (g := atomDilate φ (c / N)) (n := n) hext
  have hov : (Matrix.toEuclideanLin (overlapMatrix φ c N) (normalizedRamanujanHorizonVector m N)) n =
      ∑ j ∈ nearRowIndices c N n,
        (atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) +
          (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j) *
        (s * (normalizedRamanujanMode m j / Real.sqrt j)) := by
    calc (Matrix.toEuclideanLin (overlapMatrix φ c N) (normalizedRamanujanHorizonVector m N)) n
        = ∑ j ∈ Icc 1 N, (if (n : ℕ) ≠ j ∧ |Real.log j - Real.log (n : ℕ)| ≤ 2 * (c / N) then
            atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) +
              (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j else 0) *
            (s * (normalizedRamanujanMode m j / Real.sqrt j)) := by
          change (∑ j : PrimeHorizonIndex N, overlapMatrix φ c N n j *
            normalizedRamanujanHorizonVector m N j) = _
          rw [← Finset.sum_coe_sort (Icc 1 N)]
          exact Finset.sum_congr rfl fun j _ => rfl
      _ = _ := by
          rw [nearRowIndices, sum_filter]
          refine Finset.sum_congr rfl fun j _ => ?_
          by_cases h : j ≠ (n : ℕ) ∧ |Real.log j - Real.log (n : ℕ)| ≤ 2 * c / N
          · rw [if_pos h, if_pos ⟨Ne.symm h.1, by rw [← mul_div_assoc]; exact h.2⟩]
          · rw [if_neg h, if_neg fun h' => h ⟨Ne.symm h'.1, by rw [mul_div_assoc]; exact h'.2⟩,
              zero_mul]
  rw [hov]
  change _ = downwardPrimeRow (atomDilate φ (c / N)) N
      (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n /
        (∫ u, atomDilate φ (c / N) u ^ 2) +
    (r * (((∑ j ∈ nearRowIndices c N n,
      atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) *
        ramanujanLagCoefficient m j / Real.sqrt j) -
      downwardPrimeRow (atomDilate φ (c / N)) N
        (fun j => ramanujanLagCoefficient m j / Real.sqrt j) n /
          (∫ u, atomDilate φ (c / N) u ^ 2)) / Real.sqrt (Real.log N)) +
      (∑ j ∈ nearRowIndices c N n,
        completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j /
          Real.sqrt j) / Real.sqrt (Real.log N))
  rw [hdown, Finset.sum_congr rfl fun j _ => (show
      (atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) +
          (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j) *
        (s * (normalizedRamanujanMode m j / Real.sqrt j)) =
      (atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) *
          ramanujanLagCoefficient m j / Real.sqrt j) * (s * r) +
        (completeWeilPoleShift φ c / N * archimedeanCenterKernel n j * normalizedRamanujanMode m j /
          Real.sqrt j) * s by
      rw [normalizedRamanujanMode_eq_coefficient hm, hr]; ring),
    sum_add_distrib, ← sum_mul, ← sum_mul, hs]
  ring

private theorem norm_seven_residuals_le {E : Type*} [SeminormedAddCommGroup E]
    (p s c x q y z : E) :
    ‖-p + s + c - x + q + (y + z)‖ ≤ ‖p‖ + ‖s‖ + ‖c‖ + ‖x‖ + ‖q‖ + ‖y‖ + ‖z‖ := by
  have h₁ := norm_add_le (-p) s
  have h₂ := norm_add_le (-p + s) c
  have h₃ := norm_sub_le (-p + s + c) x
  have h₄ := norm_add_le (-p + s + c - x) q
  have h₅ := norm_add_le (-p + s + c - x + q) (y + z)
  have h₆ := norm_add_le y z
  rw [norm_neg] at h₁
  linarith only [h₁, h₂, h₃, h₄, h₅, h₆]

/-- **Exact residual at every overlap.** On a Ramanujan vector the residual of the complete Weil
matrix against the completed conductor energy is the sum of the vanishing blocks minus the upward
defect. -/
theorem completeWeilMatrix_ramanujan_residual_eq_at_every_overlap
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) {N : ℕ} (hN : 1 ≤ N) {m : ℕ} (hm : 0 < m) :
    Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N =
      -(Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
          (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) +
        completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N +
        (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
            (normalizedRamanujanHorizonVector m N) -
          (if m = 1 then completeWeilPoleShift φ c else 0) •
            normalizedRamanujanHorizonVector m N) -
        Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N) +
        Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N)
          (normalizedRamanujanHorizonVector m N) +
        ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
          nearCenterVector φ c N m) -
        (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
          shellCorrection φ c m • normalizedRamanujanHorizonVector m N) := by
  have hone : Matrix.toEuclideanLin
      (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
      (normalizedRamanujanHorizonVector m N) = normalizedRamanujanHorizonVector m N := by
    ext i
    change (Matrix.mulVec (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
      (fun j => normalizedRamanujanHorizonVector m N j)) i = normalizedRamanujanHorizonVector m N i
    rw [Matrix.one_mulVec]
  have h := congrArg
    (fun A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ =>
      Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N))
    (completeWeilMatrix_eq_decomposition_at_every_overlap hφ hsupp hM hc0 hN)
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hone] at h
  have hNR : Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N)
      (normalizedRamanujanHorizonVector m N) =
      downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) +
        upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) := by
    ext n
    rw [fullWeilNonRatioMatrix_row_eq hφ hsupp hM hc0 hN, add_div]
    rfl
  have hOv : Matrix.toEuclideanLin (overlapMatrix φ c N) (normalizedRamanujanHorizonVector m N) =
      downwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) +
        ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m +
          nearCenterVector φ c N m) := by
    ext n
    rw [overlapMatrix_ramanujan_row_eq φ c hm n]
    rfl
  rw [h, hNR, hOv, completedConductorEnergy_eq_sub_shellCorrection hc0 hm]
  simp only [completeWeilAdjunctionEnergy]
  module

/-- **The residual is the upward defect.** At every overlap ratio `c > 0`, adding the upward defect
to the complete Weil residual on a normalized Ramanujan vector leaves a term vanishing in norm. -/
theorem tendsto_completeWeilMatrix_ramanujan_residual_add_upward_norm
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc0 : 0 < c) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N +
        (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
          shellCorrection φ c m • normalizedRamanujanHorizonVector m N)‖) atTop (𝓝 0) := by
  have hp := tendsto_normalizedRamanujanHorizonVector_residual_norm hm
  have hv : Tendsto (fun N : ℕ => ‖normalizedRamanujanHorizonVector m N‖) atTop (𝓝 1) := by
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_one] using
      (tendsto_normalizedRamanujanHorizonVector_norm_sq hm).sqrt
  have hs := ((tendsto_completeWeilSelfError_of_pos hφ hsupp hM hc0).abs).mul hv
  have hc := tendsto_fullWeilCenterMatrix_ramanujan_residual_norm hm (completeWeilPoleShift φ c)
  have hx := tendsto_separatedCrossErrorMatrix_ramanujan_norm hφ hsupp hM hc0 hm
  have hq := tendsto_fullWeilPoleErrorMatrix_ramanujan_norm_of_pos hφ hsupp hM hc0 hm
  have hF := (tendsto_normalizedFullNearGammaDownwardVector_norm hφ hsupp hM hc0 m).const_mul
    |(Real.sqrt (m.totient : ℝ))⁻¹|
  have hC := tendsto_nearCenterVector_norm φ hc0 hm
  have hlim := ((((((hp.add hs).add hc).add hx).add hq).add hF).add hC)
  simp only [abs_zero, zero_mul, mul_zero, zero_add] at hlim
  apply squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) _ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN hm,
    sub_add_cancel]
  simpa only [norm_smul, Real.norm_eq_abs] using norm_seven_residuals_le
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
    (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m)
    (nearCenterVector φ c N m)

/-- The upward defect in the coordinates of the horizon. -/
theorem norm_sq_upwardPrimeVector_sub (φ : ℝ → ℝ) (c a : ℝ) (N : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ‖upwardPrimeVector φ c N x - a • x‖ ^ 2 =
      ∑ n ∈ Icc 1 N, (upwardPrimeRow (atomDilate φ (c / N)) N (primeHorizonExtension x) n /
        (∫ u, atomDilate φ (c / N) u ^ 2) - a * primeHorizonExtension x n) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_coe_sort (Icc 1 N)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [primeHorizonExtension_coe]
  rfl

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
