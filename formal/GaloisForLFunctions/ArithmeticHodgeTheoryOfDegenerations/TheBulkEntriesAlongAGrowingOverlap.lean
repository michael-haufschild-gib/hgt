import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheNearBlockAlongAGrowingOverlap
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheBulkEntriesAtEveryOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleMomentsHaveQuadraticDilationError
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheTiltedSplineHasARegularTail

/-!
# The bulk entries along a growing overlap

Along a growing overlap `c = c_N → ∞`, `c² log² N/N → 0`, every bulk entry of the complete Weil
matrix on Ramanujan packets has second order linear in `c`, supported at the pole
(`tendsto_completeWeilBulkEntry_div_overlap`):

`(⟨W R_e, R_{e'}⟩ − E_e(c) ⟨R_e, R_{e'}⟩)/c → [e = e' = 1] κ (2 + γ − log 4π)`,

`κ = (∫φ)²/∫φ²`, `E_e(c)` the completed conductor energy. The exact decomposition at every overlap
splits the entry into the self error, the ratio-prime residual, the center, the far cross error,
the pole-moment error, the near block (`tendsto_nearBlock_div_overlap`) and the shell correction
`S_e(c) = [e = 1] κ c − log c + O(1)` against the Gram entry. The logarithms `κ c log c` of the
shell correction, the near center and the weighted near pairs cancel; the arithmetic constants
(Stieltjes, divisor jets, `Λ(e)/φ(e)`) cancel between the center, the near center and the
shells. At the pole the archimedean genus `2 + γ − log 4π = Σ_ρ 1/(ρ(1 − ρ))` remains.

**The critical curve** (`tendsto_tiltedUnitSpline_bulkEntry_critical`). For the tilted spline,
`c⁷ E_e(c) → J(e)`; along `c⁸/log N → K > 0` the rescaled normalized entries converge:
`c⁷ ⟨W r_e, r_{e'}⟩ → J(e) δ_{ee'} + [e = e' = 1] K κ (2 + γ − log 4π)`.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis BezoutValuationIncidence
  CompletedArithmeticForms ArithmeticEffectivityTheory

/-! ### The blocks at a growing width -/

theorem fullWeilCenterMatrix_eq_smul (α : ℝ) (N : ℕ) :
    fullWeilCenterMatrix α N = α • fullWeilCenterMatrix 1 N := by
  ext n j
  simp only [fullWeilCenterMatrix, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The pole-moment error pairing is the error coefficient times a horizon sum. -/
theorem abs_poleErrorPairing_le_coeff (φ : ℝ → ℝ) (c : ℝ) {e e' : ℕ} (he : 0 < e)
    (he' : 0 < e') (N : ℕ) :
    |⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector e N),
        ramanujanHorizonVector e' N⟫| ≤
      |atomPoleErrorCoefficient φ c N| * (2 * (∑ t ∈ e'.divisors, (t : ℝ)) *
        (∑ t ∈ e.divisors, (t : ℝ))) * (N * harmonic N) := by
  set σ : ℝ := ∑ t ∈ e.divisors, (t : ℝ)
  set σ' : ℝ := ∑ t ∈ e'.divisors, (t : ℝ)
  have hσ : 0 ≤ σ := by positivity
  have hσ' : 0 ≤ σ' := by positivity
  have h1 : (1 : ℝ) ≤ e.totient := by exact_mod_cast Nat.totient_pos.mpr he
  have h1' : (1 : ℝ) ≤ e'.totient := by exact_mod_cast Nat.totient_pos.mpr he'
  have hZ1 : 1 ≤ Real.sqrt e.totient * Real.sqrt e'.totient :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr h1) (Real.one_le_sqrt.mpr h1')
  have hs : 0 < Real.sqrt e.totient * Real.sqrt e'.totient := by linarith
  set κ := atomPoleErrorCoefficient φ c N
  have hpair : ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector e N),
      ramanujanHorizonVector e' N⟫ = κ / (Real.sqrt e.totient * Real.sqrt e'.totient) *
        ∑ n ∈ Icc 1 N, ∑ j ∈ Icc 1 N, ramanujanLagCoefficient e' n * ramanujanLagCoefficient e j *
          (1 / (n : ℝ) + 1 / j) := by
    rw [inner_matrix_ramanujanHorizonVector_eq (fullWeilPoleErrorMatrix φ c N)
      (fun n j : ℕ => κ * arithmeticPoleKernel n j) (fun n j => rfl) he he', div_mul_eq_mul_div,
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hk := arithmeticPoleKernel_div_sqrt_mul (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hj).1
    rw [← hk]; ring
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
      ≤ |κ| * (σ' * σ * (2 * N * harmonic N)) :=
        mul_le_mul (div_le_self (abs_nonneg _) hZ1) hsum (abs_nonneg _) (abs_nonneg _)
    _ = _ := by ring

section Growing

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
  (hM : 0 < ∫ u, φ u ^ 2)
include hφ hsupp hM

/-- `|Pe| = O((c/N)²)` at every width `c ≤ N`. -/
theorem abs_atomPoleErrorCoefficient_le_of_le {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hcN : c ≤ N) :
    |atomPoleErrorCoefficient φ c N| ≤ atomPoleMomentErrorConstant φ * (c / N) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h := abs_dilated_pole_product_sub_le hφ hsupp hM (div_pos hc hN0)
    ((div_le_one hN0).mpr hcN)
  have e : atomPoleErrorCoefficient φ c N =
      atomExponentialMoment (atomDilate φ (c / N)) (-(1 / 2)) *
        atomExponentialMoment (atomDilate φ (c / N)) (1 / 2) /
          (∫ u, atomDilate φ (c / N) u ^ 2) - c / N * (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) := by
    rw [atomPoleErrorCoefficient, completeWeilPoleShift]; ring
  rw [e]; exact h

/-- The pole-moment error is negligible against `c`. -/
theorem tendsto_poleErrorPairing_div_overlap {e e' : ℕ} (he : 0 < e) (he' : 0 < e')
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ (c N) N)
        (ramanujanHorizonVector e N), ramanujanHorizonVector e' N⟫ / c N) atTop (𝓝 0) := by
  obtain ⟨hr1, hr2, -⟩ := growingOverlap_rates hc1 hcinf hcN
  set K := atomPoleMomentErrorConstant φ * (2 * (∑ t ∈ e'.divisors, (t : ℝ)) *
    (∑ t ∈ e.divisors, (t : ℝ)))
  have hK : 0 ≤ K := by
    have := atomPoleMomentErrorConstant_nonneg φ; positivity
  have hlim : Tendsto (fun N : ℕ => K * (c N * (1 + Real.log (c N) + Real.log N) / N)) atTop
      (𝓝 0) := by simpa using hr2.const_mul K
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hr1.eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop 1] with N h1 hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := hc1 N
  have hc0 : 0 < c N := by linarith
  have hcN' : c N ≤ N := by rw [div_lt_one hN0] at h1; linarith
  have hHnn : (0 : ℝ) ≤ harmonic N := by
    rw [harmonic_eq_sum_Icc_real]; exact Finset.sum_nonneg fun i _ => by positivity
  have hb := (abs_poleErrorPairing_le_coeff φ (c N) he he' N).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (abs_atomPoleErrorCoefficient_le_of_le hφ hsupp hM hc0 hN hcN') (by positivity))
      (mul_nonneg (Nat.cast_nonneg N) hHnn))
  have hH : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  have hlc : 0 ≤ Real.log (c N) := Real.log_nonneg hc
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hc0, div_le_iff₀ hc0]
  calc _ ≤ _ := hb
    _ = K * (c N ^ 2 * harmonic N / N) := by simp only [K]; field_simp
    _ ≤ K * (c N ^ 2 * (1 + Real.log (c N) + Real.log N) / N) := by
        gcongr; linarith
    _ = _ := by ring

/-- The self error is negligible against `c`. -/
theorem tendsto_selfError_mul_gram_div_overlap {e e' : ℕ} (he : 0 < e) (he' : 0 < e')
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => completeWeilSelfError φ (c N) N *
      ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫ / c N) atTop (𝓝 0) := by
  obtain ⟨hr1, -, -⟩ := growingOverlap_rates hc1 hcinf hcN
  set σ : ℝ := ∑ t ∈ e.divisors, (t : ℝ)
  set σ' : ℝ := ∑ t ∈ e'.divisors, (t : ℝ)
  have h1 : (1 : ℝ) ≤ e.totient := by exact_mod_cast Nat.totient_pos.mpr he
  have h1' : (1 : ℝ) ≤ e'.totient := by exact_mod_cast Nat.totient_pos.mpr he'
  have hZ1 : 1 ≤ Real.sqrt e.totient * Real.sqrt e'.totient :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.mpr h1) (Real.one_le_sqrt.mpr h1')
  have hs : 0 < Real.sqrt e.totient * Real.sqrt e'.totient := by linarith
  set K : ℝ := Real.exp (1 / 2) / 2 * (σ * σ')
  have hmaj := tendsto_harmonic_div_self.const_mul K
  rw [mul_zero] at hmaj
  refine squeeze_zero_norm' ?_ hmaj
  filter_upwards [hr1.eventually (gt_mem_nhds zero_lt_one), eventually_ge_atTop 1] with N h1N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := hc1 N
  have hc0 : 0 < c N := by linarith
  have hcN' : c N ≤ N := by rw [div_lt_one hN0] at h1N; linarith
  have hself := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc0 hN hcN'
  have hgram : |⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫| ≤
      σ * σ' * harmonic N := by
    rw [inner_ramanujanHorizonVector_eq he he', abs_div, abs_of_pos hs]
    refine (div_le_self (abs_nonneg _) hZ1).trans ?_
    rw [harmonic_eq_sum_Icc_real, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    rw [abs_div, abs_mul, abs_of_pos hn0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (abs_ramanujanLagCoefficient_le e n)
      (abs_ramanujanLagCoefficient_le e' n) (abs_nonneg _) (by positivity)) (by positivity)
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hc0, div_le_iff₀ hc0]
  calc |completeWeilSelfError φ (c N) N| * |⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫|
      ≤ Real.exp (1 / 2) / 2 * (c N / N) * (σ * σ' * harmonic N) :=
        mul_le_mul hself hgram (abs_nonneg _) (by positivity)
    _ = K * ((harmonic N : ℝ) / N) * c N := by simp only [K]; ring

/-! ### The shell correction against the Gram entry -/

omit hφ hsupp hM in
/-- The shell correction is `[m = 1] κ c − log c` up to a constant and the completed energy. -/
theorem shellCorrection_eq_of_pos {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    shellCorrection φ c m = (if m = 1 then c * ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) else 0) -
      Real.log c + (bumpRobin φ 1 / (∫ u, φ u ^ 2) - Real.log (2 * Real.pi) +
        ramanujanAdjunctionEnergy m - Real.eulerMascheroniConstant) -
      completedConductorEnergy φ c m := by
  have h := completedConductorEnergy_eq_sub_shellCorrection (φ := φ) hc hm
  have hlog : Real.log (1 / (2 * Real.pi * c)) = -Real.log (2 * Real.pi) - Real.log c := by
    rw [one_div, Real.log_inv, Real.log_mul (by positivity) hc.ne']; ring
  rw [h]
  unfold completeWeilAdjunctionEnergy completeWeilSelfFinitePart completeWeilPoleShift
  rw [hlog]
  split_ifs <;> ring

/-- The rates `log c/c → 0`, `(log c)²/c → 0` and `E_m(c) log c/c → 0` along `c → ∞`. -/
theorem growingOverlap_log_rates {c : ℕ → ℝ} (hcinf : Tendsto c atTop atTop) (m : ℕ) :
    Tendsto (fun N : ℕ => Real.log (c N) / c N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => Real.log (c N) ^ 2 / c N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => 1 / c N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => completedConductorEnergy φ (c N) m) atTop (𝓝 0) := by
  have h1 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hcinf
  have h2 := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp hcinf
  refine ⟨?_, ?_, ?_, (tendsto_completedConductorEnergy_atTop hφ hsupp hM m).comp hcinf⟩
  · exact h1.congr fun N => by simp
  · exact h2.congr fun N => by simp
  · simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hcinf

/-- `S_m(c)/c → [m = 1] κ`. -/
theorem tendsto_shellCorrection_div {m : ℕ} (hm : 0 < m) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hcinf : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ => shellCorrection φ (c N) m / c N) atTop
      (𝓝 (if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0)) := by
  obtain ⟨hl, -, hinv, hE⟩ := growingOverlap_log_rates hφ hsupp hM hcinf m
  obtain ⟨k, hk⟩ : ∃ k, k = bumpRobin φ 1 / (∫ u, φ u ^ 2) - Real.log (2 * Real.pi) +
      ramanujanAdjunctionEnergy m - Real.eulerMascheroniConstant := ⟨_, rfl⟩
  have h := ((tendsto_const_nhds (x := if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0)).sub
    hl).add ((hinv.const_mul k).sub (hinv.mul hE))
  simp only [mul_zero, sub_zero, add_zero] at h
  refine h.congr fun N => ?_
  have hc0 : 0 < c N := by linarith [hc1 N]
  rw [shellCorrection_eq_of_pos hc0 hm, ← hk]
  split_ifs <;> field_simp <;> ring

/-- `[e = e'] φ(e) S_e(c) log c/c − [e = e' = 1] κ (log c − 2) → [e = e' = 1] 2κ`. -/
theorem tendsto_shellCorrection_log {e e' : ℕ} (he : 0 < e) {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hcinf : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ => (if e = e' then (e.totient : ℝ) *
        (shellCorrection φ (c N) e * Real.log (c N) / c N) else 0) -
      (if e = 1 ∧ e' = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * (Real.log (c N) - 2) else 0))
      atTop (𝓝 (if e = 1 ∧ e' = 1 then 2 * ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) else 0)) := by
  obtain ⟨hl, hl2, -, hE⟩ := growingOverlap_log_rates hφ hsupp hM hcinf e
  obtain ⟨k, hk⟩ : ∃ k, k = bumpRobin φ 1 / (∫ u, φ u ^ 2) - Real.log (2 * Real.pi) +
      ramanujanAdjunctionEnergy e - Real.eulerMascheroniConstant := ⟨_, rfl⟩
  -- the logarithmic part `(−log c + k − E) log c / c → 0`
  have hz : Tendsto (fun N : ℕ => (-Real.log (c N) + k - completedConductorEnergy φ (c N) e) *
      (Real.log (c N) / c N)) atTop (𝓝 0) := by
    have := ((hl2.neg.add (hl.const_mul k)).sub (hE.mul hl))
    simp only [neg_zero, mul_zero, add_zero, sub_zero] at this
    refine this.congr fun N => ?_
    ring
  by_cases hee : e = e'
  · subst hee
    by_cases h1 : e = 1
    · subst h1
      simp only [and_self, if_true, Nat.totient_one, Nat.cast_one, one_mul]
      have := hz.add_const (2 * ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)))
      rw [zero_add] at this
      refine this.congr fun N => ?_
      have hc0 : 0 < c N := by linarith [hc1 N]
      rw [shellCorrection_eq_of_pos hc0 one_pos, ← hk]
      simp only [if_true]
      field_simp
      ring
    · simp only [if_true, h1, false_and, if_false, sub_zero]
      have := hz.const_mul (e.totient : ℝ)
      rw [mul_zero] at this
      refine this.congr fun N => ?_
      have hc0 : 0 < c N := by linarith [hc1 N]
      rw [shellCorrection_eq_of_pos hc0 he, if_neg h1, ← hk]
      field_simp
      ring
  · have hne : ¬ (e = 1 ∧ e' = 1) := fun h => hee (h.1.trans h.2.symm)
    simp only [if_neg hee, if_neg hne, sub_zero]
    exact tendsto_const_nhds

/-- The shell correction against the Gram entry:
`(S_e/c)(Σ_{n ≤ N} c_e(n)c_{e'}(n)/n − [e = e'] φ(e) log N) → [e = 1] κ (γ or −Λ(e'))`. -/
theorem tendsto_shellCorrection_mul_gram {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {c : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop) :
    Tendsto (fun N : ℕ => shellCorrection φ (c N) e / c N *
      (∑ n ∈ Finset.Icc 1 N, ramanujanLagCoefficient e n * ramanujanLagCoefficient e' n / (n : ℝ) -
        (if e = e' then (e.totient : ℝ) * Real.log N else 0))) atTop
      (𝓝 (if e = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) *
        (if e' = 1 then Real.eulerMascheroniConstant else -ArithmeticFunction.vonMangoldt e')
        else 0)) := by
  have hS := tendsto_shellCorrection_div hφ hsupp hM he hc1 hcinf
  by_cases h1 : e = 1
  · subst h1
    simp only [if_true] at hS ⊢
    have hG : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ramanujanLagCoefficient 1 n *
        ramanujanLagCoefficient e' n / (n : ℝ) - (if 1 = e' then ((1 : ℕ).totient : ℝ) *
          Real.log N else 0)) atTop
        (𝓝 (if e' = 1 then Real.eulerMascheroniConstant else -ArithmeticFunction.vonMangoldt e')) := by
      have hsum : ∀ N : ℕ, ∑ n ∈ Finset.Icc 1 N, ramanujanLagCoefficient 1 n *
          ramanujanLagCoefficient e' n / (n : ℝ) = lagHarmonic e' N := fun N => by
        unfold lagHarmonic
        exact Finset.sum_congr rfl fun n _ => by rw [ramanujanLagCoefficient_one, one_mul]
      simp only [hsum]
      by_cases h2 : e' = 1
      · subst h2
        simp only [if_true, Nat.totient_one, Nat.cast_one, one_mul, lagHarmonic_one]
        exact Real.tendsto_harmonic_sub_log
      · simp only [if_neg h2, if_neg (Ne.symm h2), sub_zero]
        exact tendsto_lagHarmonic (by omega)
    exact hS.mul hG
  · simp only [if_neg h1] at hS ⊢
    -- the Gram entry minus its logarithm converges
    have hG : Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, ramanujanLagCoefficient e n *
        ramanujanLagCoefficient e' n / (n : ℝ) - (if e = e' then (e.totient : ℝ) * Real.log N
          else 0)) atTop
        (𝓝 ((if e = e' then (e.totient : ℝ) * Real.eulerMascheroniConstant else 0) -
          orbitIntersection e e')) := by
      have hD : Tendsto (fun N : ℕ => doubleMoebius e e' (fun d t =>
          (Nat.gcd d t : ℝ) * harmonicFloorError N (Nat.lcm d t))) atTop (𝓝 0) :=
        tendsto_doubleMoebius_zero fun d hd t ht => by
          have hL : 0 < Nat.lcm d t :=
            Nat.lcm_pos (Nat.pos_of_mem_divisors hd) (Nat.pos_of_mem_divisors ht)
          simpa using (tendsto_harmonicFloorError hL).const_mul (Nat.gcd d t : ℝ)
      have := hD.const_add ((if e = e' then (e.totient : ℝ) * Real.eulerMascheroniConstant
        else 0) - orbitIntersection e e')
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop (e * e')] with N hN
      rw [sum_ramanujanLagCoefficient_mul_div_eq he he' hN]
      split_ifs <;> ring
    have := hS.mul hG
    rwa [zero_mul] at this

/-- The shell-mass error is negligible: `log(1/w) (S − [e = e'] ∫φ² φ(e) S_e)/(∫φ² c) → 0`. -/
theorem tendsto_shellMass_error_div {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {c : ℕ → ℝ}
    (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => Real.log (1 / (c N / N)) * ((shellMass φ (c N) N e e' -
        (if e = e' then (∫ u, φ u ^ 2) * e.totient * shellCorrection φ (c N) e else 0)) /
          ∫ u, φ u ^ 2) / c N) atTop (𝓝 0) := by
  obtain ⟨hr1, hr2, -⟩ := growingOverlap_rates hc1 hcinf hcN
  obtain ⟨C, hC0, hC⟩ := abs_shellMass_sub_le hφ hsupp hM (a := e) (b := e') he he'
  have hlim : Tendsto (fun N : ℕ => C / (∫ u, φ u ^ 2) *
      (c N * (1 + Real.log (c N) + Real.log N) / N)) atTop (𝓝 0) := by
    simpa using hr2.const_mul (C / ∫ u, φ u ^ 2)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hr1.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    eventually_ge_atTop 1] with N h8 hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc := hc1 N
  have hc0 : 0 < c N := by linarith
  have hcN8 : 8 * c N ≤ N := by rw [div_lt_iff₀ hN0] at h8; linarith
  have hb := hC (c N) N hc hcN8
  have hlog0 : 0 ≤ Real.log (1 / (c N / N)) := by
    apply Real.log_nonneg
    rw [one_div, one_le_inv₀ (div_pos hc0 hN0), div_le_one hN0]; linarith
  have hlog : Real.log (1 / (c N / N)) ≤ Real.log N := by
    rw [one_div, inv_div]
    exact Real.log_le_log (div_pos hN0 hc0) (div_le_self hN0.le hc)
  have hlc : 0 ≤ Real.log (c N) := Real.log_nonneg hc
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_div, abs_of_pos hc0, abs_of_pos hM,
    abs_of_nonneg hlog0]
  calc Real.log (1 / (c N / N)) * (|shellMass φ (c N) N e e' -
        (if e = e' then (∫ u, φ u ^ 2) * e.totient * shellCorrection φ (c N) e else 0)| /
          ∫ u, φ u ^ 2) / c N
      ≤ Real.log N * (C * c N ^ 2 / N / ∫ u, φ u ^ 2) / c N := by
        gcongr
    _ = C / (∫ u, φ u ^ 2) * (c N * Real.log N / N) := by field_simp
    _ ≤ C / (∫ u, φ u ^ 2) * (c N * (1 + Real.log (c N) + Real.log N) / N) := by
        gcongr
        linarith


/-! ### The assembly -/

/-- **The exact decomposition of a bulk entry at every overlap.** -/
theorem bulkEntry_decomposition {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) {e e' : ℕ}
    (he : 0 < e) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) (ramanujanHorizonVector e N),
        ramanujanHorizonVector e' N⟫ -
      completedConductorEnergy φ c e * ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫ =
    completeWeilSelfError φ c N * ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫ -
      (⟪Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ -
        (Real.log N - ramanujanAdjunctionEnergy e) *
          ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫) +
      completeWeilPoleShift φ c *
        (⟪Matrix.toEuclideanLin (fullWeilCenterMatrix 1 N) (ramanujanHorizonVector e N),
            ramanujanHorizonVector e' N⟫ -
          (if e = 1 then 1 else 0) * ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫) -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (ramanujanHorizonVector e N),
        ramanujanHorizonVector e' N⟫ +
      ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (ramanujanHorizonVector e N),
        ramanujanHorizonVector e' N⟫ +
      (⟪Matrix.toEuclideanLin (overlapMatrix φ c N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ -
        ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫) +
      shellCorrection φ c e * ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫ := by
  rw [completeWeilMatrix_eq_decomposition_at_every_overlap hφ hsupp hM hc hN,
    completedConductorEnergy_eq_sub_shellCorrection hc he,
    fullWeilCenterMatrix_eq_smul (completeWeilPoleShift φ c) N]
  have hone : Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
      (ramanujanHorizonVector e N) = ramanujanHorizonVector e N := by
    ext i
    change (Matrix.mulVec (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
      (fun j => ramanujanHorizonVector e N j)) i = ramanujanHorizonVector e N i
    rw [Matrix.one_mulVec]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hone, inner_add_left, inner_sub_left, real_inner_smul_left]
  unfold completeWeilAdjunctionEnergy
  split_ifs <;> ring

/-- The value of the bulk limit: the arithmetic constants cancel, the archimedean genus remains. -/
theorem bulkGrowingLimit_eq {e e' : ℕ} (he : 0 < e) (he' : 0 < e') :
    Real.sqrt e.totient * Real.sqrt e'.totient *
        ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * centerSecondOrder 1 e e') -
      Real.sqrt e.totient * Real.sqrt e'.totient *
        (if e = 1 ∧ e' = 1 then 2 * farCrossFinitePart φ else 0) +
      ((if e' = 1 ∧ e = 1 then 2 / (∫ u, φ u ^ 2) * ∫ s in (0 : ℝ)..2, nearKernel φ s else 0) +
        (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * (if e = e' then (if e = 1 then
          Real.log 2 + Real.eulerMascheroniConstant - 1 else -ArithmeticFunction.vonMangoldt e)
          else 0) +
        ((if e' = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * ArithmeticFunction.vonMangoldt e
            else 0) +
          (if e = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * ArithmeticFunction.vonMangoldt e'
            else 0))) +
      (if e = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) *
        (if e' = 1 then Real.eulerMascheroniConstant else -ArithmeticFunction.vonMangoldt e')
        else 0) +
      (if e = 1 ∧ e' = 1 then 2 * ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) else 0) =
    Real.sqrt e.totient * Real.sqrt e'.totient *
      (if e = 1 ∧ e' = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) *
        (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) else 0) := by
  have hM' := hM.ne'
  have hΛ1 : ArithmeticFunction.vonMangoldt 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
  by_cases h1 : e = 1
  · subst h1
    by_cases h2 : e' = 1
    · subst h2
      simp only [and_self, if_true, Nat.totient_one, Nat.cast_one, Real.sqrt_one, one_mul,
        centerSecondOrder_one_one, hΛ1, mul_zero, add_zero]
      rw [integral_nearKernel hφ hsupp, nearConstant_eq, farCrossFinitePart]
      have h4 : Real.log (4 * Real.pi) = Real.log 2 + Real.log (2 * Real.pi) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
      rw [h4]
      field_simp
      ring
    · have hc : centerSecondOrder 1 1 e' = 0 := by
        unfold centerSecondOrder centerLimitCoeff
        rw [if_neg (fun h => h2 h.2), if_neg (Ne.symm h2), if_neg h2]; simp
      simp only [hc, h2, and_false, and_true, if_false, if_true, mul_zero, sub_zero,
        zero_add, add_zero, (Ne.symm h2 : (1 : ℕ) ≠ e')]
      ring
  · have h1' : 2 ≤ e := by omega
    by_cases h2 : e' = 1
    · subst h2
      rw [centerSecondOrder_conductor_one h1' 1]
      have hs : 0 < Real.sqrt e.totient := Real.sqrt_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr he)
      simp only [h1, and_true, and_false, if_false, if_true, Nat.totient_one,
        Nat.cast_one, Real.sqrt_one, mul_one, mul_zero, sub_zero, add_zero]
      field_simp
      ring
    · by_cases h3 : e = e'
      · subst h3
        rw [centerSecondOrder_self h1' 1]
        have hφe : (0 : ℝ) < e.totient := by exact_mod_cast Nat.totient_pos.mpr he
        simp only [h1, and_false, if_false, if_true, mul_zero, sub_zero, add_zero, zero_add]
        rw [Real.mul_self_sqrt hφe.le]
        field_simp
        ring
      · have hc : centerSecondOrder 1 e e' = 0 := by
          unfold centerSecondOrder centerLimitCoeff
          rw [if_neg (fun h => h1 h.1), if_neg h3, if_neg h2]; simp
        simp only [hc, h1, h2, h3, and_false, if_false, mul_zero, sub_zero, add_zero]

/-- **The bulk entries along a growing overlap**, for overlaps `c_N ≥ 1`. -/
theorem tendsto_completeWeilBulkEntry_div_overlap_of_one_le {e e' : ℕ} (he : 0 < e) (he' : 0 < e')
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ -
        completedConductorEnergy φ (c N) e *
          ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫) / c N) atTop
      (𝓝 (if e = 1 ∧ e' = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) *
        (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) else 0)) := by
  have hc0 : ∀ N, 0 < c N := fun N => by linarith [hc1 N]
  have hZ : 0 < Real.sqrt e.totient * Real.sqrt e'.totient := by
    have h1 : (0 : ℝ) < e.totient := by exact_mod_cast Nat.totient_pos.mpr he
    have h2 : (0 : ℝ) < e'.totient := by exact_mod_cast Nat.totient_pos.mpr he'
    positivity
  have hc2N : Tendsto (fun N : ℕ => c N ^ 2 / N) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hcN
    filter_upwards [eventually_ge_atTop 3] with N hN
    have hl : 1 ≤ Real.log N := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have : Real.exp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
      linarith [(show (3 : ℝ) ≤ N by exact_mod_cast hN)]
    exact div_le_div_of_nonneg_right (le_mul_of_one_le_right (sq_nonneg _) (one_le_pow₀ hl))
      (Nat.cast_nonneg N)
  have hinv : Tendsto (fun N : ℕ => 1 / c N) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp hcinf
  have hA1 := (tendsto_selfError_mul_gram_div_overlap hφ hsupp hM he he' hc1 hcinf hcN).const_mul
    (Real.sqrt e.totient * Real.sqrt e'.totient)
  have hA2 := ((tendsto_bulkPrimeResidual he he').mul hinv).const_mul
    (Real.sqrt e.totient * Real.sqrt e'.totient)
  have hA3 := ((tendsto_centerPairing_sub 1 he he').const_mul
    ((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2))).const_mul (Real.sqrt e.totient * Real.sqrt e'.totient)
  have hA4 := (tendsto_farCrossPairing_div_overlap hφ hsupp hM he he' hcinf hc2N).const_mul
    (Real.sqrt e.totient * Real.sqrt e'.totient)
  have hA5 := (tendsto_poleErrorPairing_div_overlap hφ hsupp hM he he' hc1 hcinf hcN).const_mul
    (Real.sqrt e.totient * Real.sqrt e'.totient)
  have hA6 := tendsto_nearBlock_div_overlap hφ hsupp hM he he' hc1 hcinf hcN
  have hA7 := tendsto_shellCorrection_mul_gram hφ hsupp hM he he' hc1 hcinf
  have hA8 := tendsto_shellCorrection_log hφ hsupp hM (e' := e') he hc1 hcinf
  have hA9 := tendsto_shellMass_error_div hφ hsupp hM he he' hc1 hcinf hcN
  have hsum := ((((((((hA1.sub hA2).add hA3).sub hA4).add hA5).add hA6).add hA7).add hA8).sub hA9)
  suffices hZX : Tendsto (fun N : ℕ => Real.sqrt e.totient * Real.sqrt e'.totient *
      ((⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ -
        completedConductorEnergy φ (c N) e *
          ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫) / c N)) atTop
      (𝓝 (Real.sqrt e.totient * Real.sqrt e'.totient *
        (if e = 1 ∧ e' = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) *
          (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) else 0))) by
    have h := hZX.div_const (Real.sqrt e.totient * Real.sqrt e'.totient)
    convert h using 2
    · field_simp
    · field_simp
  refine (hsum.congr' ?_).mono_right (le_of_eq (congrArg 𝓝 ?_))
  · filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [bulkEntry_decomposition hφ hsupp hM (hc0 N) hN he, inner_ramanujanHorizonVector_eq he he']
    have hlog : Real.log (1 / (c N / N)) = Real.log N - Real.log (c N) := by
      rw [one_div, inv_div, Real.log_div hN0.ne' (hc0 N).ne']
    rw [hlog]
    simp only [completeWeilPoleShift]
    have hcN0 := (hc0 N).ne'
    have hM0 := hM.ne'
    have hZ0 := hZ.ne'
    split_ifs <;> field_simp <;> ring
  · have hv := bulkGrowingLimit_eq hφ hsupp hM he he'
    linarith [hv]

end Growing

/-- **The bulk entries along a growing overlap.** Along `c_N → ∞`, `c_N² log² N/N → 0`:
`(⟨W R_e, R_{e'}⟩ − E_e(c)⟨R_e, R_{e'}⟩)/c → [e = e' = 1] κ (2 + γ − log 4π)`. -/
theorem tendsto_completeWeilBulkEntry_div_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) {e e' : ℕ} (he : 0 < e)
    (he' : 0 < e') {c : ℕ → ℝ} (hcinf : Tendsto c atTop atTop)
    (hcN : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N ^ 2 / N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ =>
      (⟪Matrix.toEuclideanLin (completeWeilMatrix φ (c N) N) (ramanujanHorizonVector e N),
          ramanujanHorizonVector e' N⟫ -
        completedConductorEnergy φ (c N) e *
          ⟪ramanujanHorizonVector e N, ramanujanHorizonVector e' N⟫) / c N) atTop
      (𝓝 (if e = 1 ∧ e' = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) *
        (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) else 0)) := by
  have hev : ∀ᶠ N : ℕ in atTop, max (c N) 1 = c N := by
    filter_upwards [hcinf.eventually_ge_atTop 1] with N hN
    exact max_eq_left hN
  have hcinf' : Tendsto (fun N => max (c N) 1) atTop atTop :=
    hcinf.congr' (hev.mono fun N h => h.symm)
  have hcN' : Tendsto (fun N : ℕ => max (c N) 1 ^ 2 * Real.log N ^ 2 / N) atTop (𝓝 0) :=
    hcN.congr' (hev.mono fun N h => by simp only [h])
  have h := tendsto_completeWeilBulkEntry_div_overlap_of_one_le hφ hsupp hM he he'
    (c := fun N => max (c N) 1) (fun N => le_max_right _ _) hcinf' hcN'
  exact h.congr' (hev.mono fun N h => by simp only [h])

/-! ### The critical curve -/

/-- **The critical curve of the tilted spline.** For the tilted unit spline, along overlaps
`c_N > 0` with `c_N⁸/log N → K > 0`, the rescaled normalized bulk entries converge:
`c⁷ ⟨W r_e, r_{e'}⟩ → J(e) δ_{ee'} + [e = e' = 1] K κ (2 + γ − log 4π)`, where
`J(e) = (2A/∫φ²) ζ(8) J₈(e)/φ(e)` is the Jordan-totient limit of `c⁷ E_e(c)`. -/
theorem tendsto_tiltedUnitSpline_bulkEntry_critical {e e' : ℕ} (he : 0 < e) (he' : 0 < e')
    {c : ℕ → ℝ} (hc0 : ∀ N, 0 < c N) {K : ℝ} (hK : 0 < K)
    (hcK : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => c N ^ 7 *
      ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector e N), normalizedRamanujanHorizonVector e' N⟫) atTop
      (𝓝 (2 / (∫ u, tiltedUnitSpline u ^ 2) * ArithmeticDegenerationTheory.tiltedTailConstant *
          ArithmeticDegenerationTheory.zetaSum 8 * ArithmeticDegenerationTheory.jordanTotient 8 e /
            e.totient * (if e = e' then 1 else 0) +
        K * (if e = 1 ∧ e' = 1 then (∫ u, tiltedUnitSpline u) ^ 2 /
          (∫ u, tiltedUnitSpline u ^ 2) * (2 + Real.eulerMascheroniConstant -
            Real.log (4 * Real.pi)) else 0))) := by
  have hφ := contDiff_tiltedUnitSpline
  have hsupp : ∀ u, u ∉ Set.Icc 0 1 → tiltedUnitSpline u = 0 :=
    fun u hu => tiltedUnitSpline_eq_zero u hu
  have hM := integral_tiltedUnitSpline_sq_pos
  have hlogN : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- the overlap grows
  have hc8 : Tendsto (fun N : ℕ => c N ^ 8) atTop atTop := by
    refine (hcK.pos_mul_atTop hK hlogN).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    field_simp
  have hcinf : Tendsto c atTop atTop := by
    have h := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < ((8 : ℕ) : ℝ)⁻¹)).comp hc8
    refine h.congr fun N => ?_
    simp only [Function.comp_apply]
    exact Real.pow_rpow_inv_natCast (hc0 N).le (by norm_num)
  -- the growth condition `c² log² N/N → 0`
  have hcN : Tendsto (fun N : ℕ => c N ^ 2 * Real.log N ^ 2 / N) atTop (𝓝 0) := by
    have hl3 : Tendsto (fun N : ℕ => 2 * K * (Real.log N ^ 3 / N)) atTop (𝓝 0) := by
      have := ((Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero).comp
        tendsto_natCast_atTop_atTop).const_mul (2 * K)
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hl3
    filter_upwards [hcK.eventually (gt_mem_nhds (by linarith : K < 2 * K)),
      hcinf.eventually_ge_atTop 1, eventually_ge_atTop 2] with N hK2 hc1 hN
    have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hN0 : (0 : ℝ) < N := by positivity
    have h8 : c N ^ 8 ≤ 2 * K * Real.log N := by
      rw [div_lt_iff₀ hl] at hK2; linarith
    have h28 : c N ^ 2 ≤ c N ^ 8 := pow_le_pow_right₀ hc1 (by norm_num)
    rw [div_le_iff₀ hN0]
    have e : 2 * K * (Real.log N ^ 3 / N) * N = 2 * K * Real.log N * Real.log N ^ 2 := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right (h28.trans h8) (by positivity)
  have hX := tendsto_completeWeilBulkEntry_div_overlap hφ hsupp hM he he' hcinf hcN
  have hJ := (ArithmeticDegenerationTheory.tendsto_rpow_seven_mul_completedConductorEnergy_tiltedUnitSpline
    e).comp hcinf
  have hG := tendsto_normalizedRamanujanHorizonVector_gram he he'
  have htot := (hJ.mul hG).add (hcK.mul hX)
  refine htot.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hcN0 := (hc0 N).ne'
  obtain ⟨r, hr0, hr⟩ : ∃ r, 0 < r ∧ Real.sqrt (Real.log N) = r :=
    ⟨_, Real.sqrt_pos.mpr hlog, rfl⟩
  have hlr : Real.log N = r ^ 2 := by rw [← hr, Real.sq_sqrt hlog.le]
  have hr0' := hr0.ne'
  have h7 : c N ^ (7 : ℝ) = c N ^ 7 := by exact_mod_cast Real.rpow_natCast (c N) 7
  simp only [Function.comp_apply, h7]
  unfold normalizedRamanujanHorizonVector
  simp only [map_smul, real_inner_smul_left, real_inner_smul_right]
  rw [hr, hlr]
  field_simp
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
