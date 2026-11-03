import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCrossErrorOfTheBulkEntries
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilMatrixHasRamanujanQuasimodes
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.OverlapForcesNewRamanujanTerms
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTwoPoleReplacementHasUniformErrors

/-!
# The bulk entries of the complete Weil matrix at every overlap

At overlap `0 < c < 1` the complete Weil matrix splits exactly (RAPT):
`W = (log N + F(c) − γ + s_N) I − P + Cen − Cr + Pe`, and the Ramanujan packets `R_e` are its
quasimodes with energies `E_e(c) = F(c) + ρ_e − γ + [e = 1]α`, `α = c(∫φ)²/∫φ²`. Every bulk entry
has a second order (`tendsto_completeWeilBulkEntry`):

  `⟨W R_e, R_{e'}⟩ − E_e(c) ⟨R_e, R_{e'}⟩ → −D(e, e') + C_α(e, e') − Cr_{φ,c}(e, e')`,

the prime part `D` (Stieltjes constants `γ, γ₁`), the center part `C_α` (`α(1 − log 2)` at the pole,
`αΛ(e)/φ(e)` on the diagonal) and the cross error `Cr` (the smoothing of the archimedean density
`1/(2y)` by the profile). The self error `s_N = O(1/N)` and the pole-moment error `O(N⁻²)` leave
nothing. Normalized: `log N (⟨W r_e, r_{e'}⟩ − E_e(c)⟨r_e, r_{e'}⟩) → −D + C_α − Cr`
(`tendsto_log_mul_completeWeilBulkEntry`).
-/

noncomputable section

open Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open RenormalizedArithmeticPotentialTheory BezoutValuationIncidence

/-- The second order of the complete bulk entry: `−D(e, e') + C_α(e, e') − Cr_{φ,c}(e, e')`. -/
def completeBulkSecondOrder (φ : ℝ → ℝ) (c : ℝ) (e e' : ℕ) : ℝ :=
  -bulkSecondOrder e e' + centerSecondOrder (completeWeilPoleShift φ c) e e' -
    crossSecondOrder φ c e e'

theorem arithmeticPoleKernel_div_sqrt_mul {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) :
    arithmeticPoleKernel n j / (Real.sqrt n * Real.sqrt j) = 1 / n + 1 / j := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  unfold arithmeticPoleKernel
  obtain ⟨r, hr0, hr⟩ : ∃ r, 0 < r ∧ Real.sqrt n = r := ⟨_, Real.sqrt_pos.mpr hn0, rfl⟩
  obtain ⟨t, ht0, ht⟩ : ∃ t, 0 < t ∧ Real.sqrt j = t := ⟨_, Real.sqrt_pos.mpr hj0, rfl⟩
  have hnr : (n : ℝ) = r ^ 2 := by rw [← hr, Real.sq_sqrt hn0.le]
  have hjt : (j : ℝ) = t ^ 2 := by rw [← ht, Real.sq_sqrt hj0.le]
  have hr0' := hr0.ne'
  have ht0' := ht0.ne'
  rw [hr, ht, hnr, hjt]
  field_simp
  ring

/-- The pole-moment error pairing is `O(log N/N)`. -/
theorem abs_poleErrorPairing_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {N : ℕ} (hN : 1 ≤ N) :
    |⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector e N),
        ramanujanHorizonVector e' N⟫| ≤
      atomPoleMomentErrorConstant φ * c ^ 2 * (2 * (∑ t ∈ e'.divisors, (t : ℝ)) *
        (∑ t ∈ e.divisors, (t : ℝ))) / (Real.sqrt e.totient * Real.sqrt e'.totient) *
        ((harmonic N : ℝ) / N) := by
  set σ : ℝ := ∑ t ∈ e.divisors, (t : ℝ)
  set σ' : ℝ := ∑ t ∈ e'.divisors, (t : ℝ)
  have hσ : 0 ≤ σ := by positivity
  have hσ' : 0 ≤ σ' := by positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt e.totient * Real.sqrt e'.totient := by
    have h1 : (0 : ℝ) < e.totient := by exact_mod_cast Nat.totient_pos.mpr he
    have h2 : (0 : ℝ) < e'.totient := by exact_mod_cast Nat.totient_pos.mpr he'
    positivity
  set κ := atomPoleErrorCoefficient φ c N
  have hκ : |κ| ≤ atomPoleMomentErrorConstant φ * (c / N) ^ 2 :=
    abs_atomPoleErrorCoefficient_le hφ hφsupp hφ0 hc0 hc1 hN
  have hpair : ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector e N),
      ramanujanHorizonVector e' N⟫ = κ / (Real.sqrt e.totient * Real.sqrt e'.totient) *
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j *
          (1 / (n : ℝ) + 1 / j) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change ∑ n : PrimeHorizonIndex N, ramanujanPoleProfile e' n *
      ∑ j : PrimeHorizonIndex N, (κ * arithmeticPoleKernel n j) * ramanujanPoleProfile e j = _
    rw [Finset.sum_coe_sort (Icc 1 N) (fun n => ramanujanPoleProfile e' n *
      ∑ j : PrimeHorizonIndex N, (κ * arithmeticPoleKernel n j) * ramanujanPoleProfile e j),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.sum_coe_sort (Icc 1 N) (fun j => (κ * arithmeticPoleKernel n j) *
      ramanujanPoleProfile e j), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [ramanujanPoleProfile_eq he, ramanujanPoleProfile_eq he',
      ← arithmeticPoleKernel_div_sqrt_mul (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hj).1]
    ring
  have hsum : |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, ramanujanLagCoefficient e' n *
      ramanujanLagCoefficient e j * (1 / (n : ℝ) + 1 / j)| ≤ σ' * σ * (2 * N * harmonic N) := by
    have e1 : ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, ramanujanLagCoefficient e' n *
        ramanujanLagCoefficient e j * (1 / (n : ℝ) + 1 / j) =
        lagHarmonic e' N * lagSum e N + lagSum e' N * lagHarmonic e N := by
      unfold lagHarmonic lagSum
      rw [Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hL : ∀ f : ℕ, |lagHarmonic f N| ≤ (∑ t ∈ f.divisors, (t : ℝ)) * harmonic N := fun f => by
      unfold lagHarmonic
      rw [harmonic_eq_sum_Icc_real, Finset.mul_sum]
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      rw [abs_div, abs_of_pos hn0, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (abs_ramanujanLagCoefficient_le f n) (by positivity)
    have hC : ∀ f : ℕ, |lagSum f N| ≤ (∑ t ∈ f.divisors, (t : ℝ)) * N := fun f => by
      unfold lagSum
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ n ∈ Icc 1 N, |ramanujanLagCoefficient f n| ≤
            ∑ _n ∈ Icc 1 N, ∑ t ∈ f.divisors, (t : ℝ) :=
            Finset.sum_le_sum fun n _ => abs_ramanujanLagCoefficient_le f n
        _ = (∑ t ∈ f.divisors, (t : ℝ)) * N := by
            rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
    have hH : (0 : ℝ) ≤ harmonic N := by
      rw [harmonic_eq_sum_Icc_real]; exact Finset.sum_nonneg fun i _ => by positivity
    rw [e1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have b1 := mul_le_mul (hL e') (hC e) (abs_nonneg _) (by positivity)
    have b2 := mul_le_mul (hC e') (hL e) (abs_nonneg _) (by positivity)
    nlinarith [b1, b2]
  rw [hpair, abs_mul, abs_div, abs_of_pos hs]
  calc |κ| / (Real.sqrt e.totient * Real.sqrt e'.totient) *
        |∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, ramanujanLagCoefficient e' n *
          ramanujanLagCoefficient e j * (1 / (n : ℝ) + 1 / j)|
      ≤ atomPoleMomentErrorConstant φ * (c / N) ^ 2 / (Real.sqrt e.totient * Real.sqrt e'.totient) *
          (σ' * σ * (2 * N * harmonic N)) :=
        mul_le_mul (div_le_div_of_nonneg_right hκ hs.le) hsum (abs_nonneg _) (by
          have := atomPoleMomentErrorConstant_nonneg φ; positivity)
    _ = _ := by field_simp

theorem tendsto_poleErrorPairing {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector e N),
        ramanujanHorizonVector e' N⟫) atTop (𝓝 0) := by
  have hmaj := tendsto_harmonic_div_self.const_mul (atomPoleMomentErrorConstant φ * c ^ 2 *
    (2 * (∑ t ∈ e'.divisors, (t : ℝ)) * (∑ t ∈ e.divisors, (t : ℝ))) /
      (Real.sqrt e.totient * Real.sqrt e'.totient))
  rw [mul_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs]
  exact abs_poleErrorPairing_le hφ hφsupp hφ0 hc0 hc1 he he' hN

/-- The self error against a Gram entry vanishes: `s_N ⟨R_e, R_{e'}⟩ → 0`. -/
theorem tendsto_selfError_mul_gram {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N : ℕ => completeWeilSelfError φ c N *
      ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫) atTop (𝓝 0) := by
  set σ : ℝ := ∑ t ∈ e.divisors, (t : ℝ)
  set σ' : ℝ := ∑ t ∈ e'.divisors, (t : ℝ)
  have hs : 0 < Real.sqrt e.totient * Real.sqrt e'.totient := by
    have h1 : (0 : ℝ) < e.totient := by exact_mod_cast Nat.totient_pos.mpr he
    have h2 : (0 : ℝ) < e'.totient := by exact_mod_cast Nat.totient_pos.mpr he'
    positivity
  set C : ℝ := Real.exp (1 / 2) / 2 * c * (σ * σ' / (Real.sqrt e.totient * Real.sqrt e'.totient))
  have hmaj := tendsto_harmonic_div_self.const_mul C
  rw [mul_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge c
  filter_upwards [eventually_ge_atTop (max N₁ 1)] with N hN
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hcN : c ≤ N := hN₁.trans (by exact_mod_cast le_of_max_le_left hN)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hself := abs_completeWeilSelfError_le_of_width_le_one hφ hφsupp hφ0 hc0 hN1 hcN
  have hgram : |⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫| ≤
      σ * σ' * harmonic N / (Real.sqrt e.totient * Real.sqrt e'.totient) := by
    rw [inner_ramanujanHorizonVector_eq he he', abs_div, abs_of_pos hs]
    refine div_le_div_of_nonneg_right ?_ hs.le
    rw [harmonic_eq_sum_Icc_real, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [abs_div, abs_mul, abs_of_pos hn0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (abs_ramanujanLagCoefficient_le e n)
      (abs_ramanujanLagCoefficient_le e' n) (abs_nonneg _) (by positivity)) (by positivity)
  rw [Real.norm_eq_abs, abs_mul]
  calc |completeWeilSelfError φ c N| * |⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫|
      ≤ Real.exp (1 / 2) / 2 * (c / N) *
          (σ * σ' * harmonic N / (Real.sqrt e.totient * Real.sqrt e'.totient)) :=
        mul_le_mul hself hgram (abs_nonneg _) (by positivity)
    _ = C * ((harmonic N : ℝ) / N) := by ring

/-- **The bulk entries at every overlap**: for `0 < c < 1` and conductors `e, e'`,
`⟨W R_e, R_{e'}⟩ − E_e(c)⟨R_e, R_{e'}⟩ → −D(e, e') + C_α(e, e') − Cr_{φ,c}(e, e')`. -/
theorem tendsto_completeWeilBulkEntry {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N : ℕ =>
      ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ -
        completeWeilAdjunctionEnergy φ c e *
          ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫)
      atTop (𝓝 (completeBulkSecondOrder φ c e e')) := by
  have hP := tendsto_bulkPrimeResidual he he'
  have hS := tendsto_selfError_mul_gram hφ hφsupp hφ0 hc0 he he'
  have hC := tendsto_centerPairing_sub (completeWeilPoleShift φ c) he he'
  have hX := tendsto_crossPairing hφ hφsupp hφ0 hc0 hc1 he he'
  have hQ := tendsto_poleErrorPairing hφ hφsupp hφ0 hc0 hc1 he he'
  have htot := (((hP.neg.add hS).add hC).sub hX).add hQ
  rw [show -bulkSecondOrder e e' + 0 + centerSecondOrder (completeWeilPoleShift φ c) e e' -
    crossSecondOrder φ c e e' + 0 = completeBulkSecondOrder φ c e e' by
      unfold completeBulkSecondOrder; ring] at htot
  refine htot.congr' ?_
  filter_upwards [eventually_div_horizon_lt_atomSpacing hc0 hc1, eventually_ge_atTop 1]
    with N hsep hN
  have hdec := completeWeilMatrix_eq_decomposition hφ hφsupp hφ0 hc0 hN hsep.2.2
  have hone : Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
      (ramanujanHorizonVector e N) = ramanujanHorizonVector e N := by
    ext i
    change (Matrix.mulVec (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
      (fun j => ramanujanHorizonVector e N j)) i = ramanujanHorizonVector e N i
    rw [Matrix.one_mulVec]
  rw [hdec]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hone, inner_add_left, inner_sub_left, real_inner_smul_left]
  unfold completeWeilAdjunctionEnergy ramanujanAdjunctionEnergy
  split_ifs with he1 <;> ring

/-- **Normalized**: `log N (⟨W r_e, r_{e'}⟩ − E_e(c)⟨r_e, r_{e'}⟩) → −D + C_α − Cr`. -/
theorem tendsto_log_mul_completeWeilBulkEntry {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Tendsto (fun N : ℕ => Real.log N *
      (⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector e N),
          normalizedRamanujanHorizonVector e' N⟫ -
        completeWeilAdjunctionEnergy φ c e *
          ⟪normalizedRamanujanHorizonVector e N, normalizedRamanujanHorizonVector e' N⟫))
      atTop (𝓝 (completeBulkSecondOrder φ c e e')) := by
  refine (tendsto_completeWeilBulkEntry hφ hφsupp hφ0 hc0 hc1 he he').congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  obtain ⟨r, hr0, hr⟩ : ∃ r, 0 < r ∧ Real.sqrt (Real.log N) = r :=
    ⟨_, Real.sqrt_pos.mpr hlog, rfl⟩
  have hlr : Real.log N = r ^ 2 := by rw [← hr, Real.sq_sqrt hlog.le]
  have hr0' := hr0.ne'
  unfold normalizedRamanujanHorizonVector
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  rw [hr, hlr]
  field_simp

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
