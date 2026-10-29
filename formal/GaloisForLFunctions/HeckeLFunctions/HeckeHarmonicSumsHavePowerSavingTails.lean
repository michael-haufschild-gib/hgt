import GaloisForLFunctions.HeckeLFunctions.HeckeLFunctionsContinuePastTheLineReOne
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.MertensTheoremForCharacters

/-!
# Power-saving harmonic tails for Hecke characters

Twisting the ray-class coefficient bound at an intermediate real exponent gives
bounded partial sums. Abel summation then gives a power-saving tail at one and
bounds logarithmically weighted harmonic sums. Both estimates apply to the
actual Hecke coefficients and their existing analytic continuation.
-/

noncomputable section
open Filter Topology Finset NumberField Module
open scoped Classical

namespace GaloisForLFunctions.HTGeometry.BoundedPartialSums

/-- Translating a sequence doubles a uniform partial-sum bound. -/
theorem norm_partialSum_shift_le {a : ℕ → ℂ} {M : ℝ}
    (hM : ∀ N, ‖partialSum a N‖ ≤ M) (N k : ℕ) :
    ‖∑ j ∈ range k, a (N + j)‖ ≤ 2 * M := by
  have h : ∑ j ∈ range k, a (N + j) = partialSum a (N + k) - partialSum a N := by
    rw [partialSum, sum_range_add, partialSum, add_sub_cancel_left]
  rw [h]
  exact (norm_sub_le _ _).trans (by linarith [hM (N + k), hM N])

theorem powNeg_ofReal (δ : ℝ) (n : ℕ) :
    powNeg (δ : ℂ) n = (RHTower.realPowerKernel δ n : ℂ) := by
  rw [powNeg, RHTower.realPowerKernel, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  rfl

/-- A bounded Dirichlet sum at a smaller real exponent gives a power-saving tail. -/
theorem norm_contLSeries_real_sub_partial_le {c : ℕ → ℂ} {σ₀ σ M : ℝ}
    (hM : ∀ N, ‖∑ n ∈ range N, LSeries.term c (σ₀ : ℂ) n‖ ≤ M)
    (hσ : σ₀ < σ) {N : ℕ} (hN : 1 ≤ N) :
    ‖contLSeries c (σ₀ : ℂ) (σ : ℂ) - ∑ n ∈ range N, LSeries.term c (σ : ℂ) n‖ ≤
      2 * M * (N : ℝ) ^ (σ₀ - σ) := by
  have hlim := tendsto_sum_term_contLSeries hM (s := (σ : ℂ)) (by simpa using hσ)
  have hshift := (tendsto_add_atTop_iff_nat N).mpr hlim
  refine le_of_tendsto' ((hshift.sub_const _).norm) fun k => ?_
  rw [add_comm k N, sum_range_add, add_sub_cancel_left]
  have hanti : Antitone fun j => RHTower.realPowerKernel (σ - σ₀) (N + j) :=
    antitone_nat_of_succ_le fun j => by
      rw [show N + (j + 1) = N + j + 1 by omega]
      exact RHTower.realPowerKernel_succ_le (by linarith) (by omega)
  have hb := RenormalizedArithmeticPotentialTheory.norm_sum_antitone_mul_le
    (norm_partialSum_shift_le hM N)
    (fun j => RHTower.realPowerKernel_nonneg (σ - σ₀) (N + j)) hanti k
  have heq (n : ℕ) : LSeries.term c (σ : ℂ) n =
      (RHTower.realPowerKernel (σ - σ₀) n : ℂ) * LSeries.term c (σ₀ : ℂ) n := by
    rw [term_eq_mul_powNeg c (σ₀ : ℂ) (σ : ℂ), ← Complex.ofReal_sub, powNeg_ofReal, mul_comm]
  simp_rw [heq]
  simpa only [add_zero, RHTower.realPowerKernel, neg_sub, mul_comm] using hb

/-- Positive logarithmic power weights eventually decrease, so bounded partial sums still cancel. -/
theorem exists_norm_sum_log_mul_powNeg_le {a : ℕ → ℂ} {M δ : ℝ}
    (hM : ∀ N, ‖partialSum a N‖ ≤ M) (hδ : 0 < δ) :
    ∃ B : ℝ, ∀ N : ℕ,
      ‖∑ n ∈ range N, a n * (Real.log n : ℂ) * powNeg (δ : ℂ) n‖ ≤ B := by
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (Real.exp δ⁻¹ + 1)
  have hM0 : 0 ≤ M := by simpa [partialSum] using hM 0
  let F : ℕ → ℂ := fun n => a n * (Real.log n : ℂ) * powNeg (δ : ℂ) n
  let f : ℕ → ℝ := fun j => Real.log (N₀ + j : ℕ) / (N₀ + j : ℕ) ^ δ
  have hf : ∀ j, 0 ≤ f j := fun j =>
    div_nonneg (Real.log_natCast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hanti : Antitone f := by
    intro i j hij
    apply Real.log_div_self_rpow_antitoneOn hδ
    · change Real.exp δ⁻¹ ≤ ((N₀ + i : ℕ) : ℝ)
      push_cast
      linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    · change Real.exp δ⁻¹ ≤ ((N₀ + j : ℕ) : ℝ)
      push_cast
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
    · exact_mod_cast Nat.add_le_add_left hij N₀
  have heq (j : ℕ) : F (N₀ + j) = (f j : ℂ) * a (N₀ + j) := by
    dsimp only [F, f]
    rw [powNeg_ofReal, RHTower.realPowerKernel, Real.rpow_neg (Nat.cast_nonneg _)]
    push_cast
    ring
  have htail (k : ℕ) : ‖∑ j ∈ range k, F (N₀ + j)‖ ≤ f 0 * (2 * M) := by
    simp_rw [heq]
    exact RenormalizedArithmeticPotentialTheory.norm_sum_antitone_mul_le
      (norm_partialSum_shift_le hM N₀) hf hanti k
  refine ⟨(∑ n ∈ range N₀, ‖F n‖) + f 0 * (2 * M), fun N => ?_⟩
  change ‖∑ n ∈ range N, F n‖ ≤ _
  rcases le_total N N₀ with hN | hN
  · calc
      _ ≤ ∑ n ∈ range N, ‖F n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range N₀, ‖F n‖ :=
        sum_le_sum_of_subset_of_nonneg (range_mono hN) (fun n _ _ => norm_nonneg _)
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (hf 0) (by linarith))
  · rw [show N = N₀ + (N - N₀) by omega, sum_range_add]
    exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (htail _))

end GaloisForLFunctions.HTGeometry.BoundedPartialSums

namespace GaloisForLFunctions.HeckeLFunctions
open HTGeometry.BoundedPartialSums
variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

/-- A positive exponent strictly smaller than the ray-class counting saving. -/
def heckeHarmonicTailExponent : ℝ := (finrank ℚ K : ℝ)⁻¹ / 2

theorem heckeHarmonicTailExponent_pos : 0 < heckeHarmonicTailExponent (K := K) := by
  unfold heckeHarmonicTailExponent
  exact div_pos (inv_pos.mpr (by exact_mod_cast finrank_pos)) (by norm_num)

/-- The harmonic ideal sum, grouped by its positive integral norm. -/
def heckeHarmonicSum (ψ : HeckeCharacter 𝔪) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, heckeCoeff 𝔪 ψ n / (n : ℂ)

theorem heckeHarmonicSum_eq_sum_term (ψ : HeckeCharacter 𝔪) (N : ℕ) :
    heckeHarmonicSum 𝔪 ψ N = ∑ n ∈ range (N + 1), LSeries.term (heckeCoeff 𝔪 ψ) 1 n := by
  rw [sum_range_succ_eq_sum_Icc (by simp), heckeHarmonicSum]
  refine sum_congr rfl fun n hn => ?_
  rw [LSeries.term_of_ne_zero (by have := (mem_Icc.mp hn).1; omega), Complex.cpow_one]

/-- The actual harmonic sums approach the nontrivial Hecke L-value with a power saving. -/
theorem exists_norm_heckeLCont_one_sub_harmonic_le {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖heckeLCont 𝔪 ψ 1 - heckeHarmonicSum 𝔪 ψ N‖ ≤
        C * ((N : ℝ) + 1) ^ (-heckeHarmonicTailExponent (K := K)) := by
  let δ := heckeHarmonicTailExponent (K := K)
  have hδ : 0 < δ := heckeHarmonicTailExponent_pos (K := K)
  have hbase : 1 - (finrank ℚ K : ℝ)⁻¹ < 1 - δ := by
    dsimp only [δ, heckeHarmonicTailExponent]
    linarith [inv_pos.mpr (show (0 : ℝ) < finrank ℚ K by exact_mod_cast finrank_pos)]
  obtain ⟨C, hC⟩ := exists_norm_sum_heckeCoeff_le hψ
  obtain ⟨M, hM⟩ := exists_norm_sum_term_le (heckeCoeff_zero ψ) errExp_nonneg hC hbase
  have hM0 : 0 ≤ M := by simpa using hM 0
  refine ⟨2 * M, mul_nonneg (by norm_num) hM0, fun N => ?_⟩
  have heq : heckeLCont 𝔪 ψ 1 = contLSeries (heckeCoeff 𝔪 ψ) ((1 - δ : ℝ) : ℂ) 1 :=
    growthCont_eq_contLSeries (heckeCoeff_zero ψ) errExp_nonneg hC hbase hM
      (by simp only [Complex.one_re]; linarith)
  rw [heq, heckeHarmonicSum_eq_sum_term]
  have h := norm_contLSeries_real_sub_partial_le hM (σ := 1) (by linarith)
    (N := N + 1) (by omega)
  simpa only [Complex.ofReal_one, Nat.cast_add, Nat.cast_one, sub_sub_cancel_left] using h

/-- The logarithmically weighted harmonic ideal sum, grouped by norm. -/
def heckeLogarithmicHarmonicSum (ψ : HeckeCharacter 𝔪) (N : ℕ) : ℂ :=
  ∑ n ∈ Icc 1 N, heckeCoeff 𝔪 ψ n / (n : ℂ) * (Real.log n : ℂ)

/-- Cancellation of actual ray class coefficients bounds the logarithmic harmonic sums. -/
theorem exists_norm_heckeLogarithmicHarmonicSum_le {ψ : HeckeCharacter 𝔪} (hψ : ψ ≠ 1) :
    ∃ B : ℝ, ∀ N : ℕ, ‖heckeLogarithmicHarmonicSum 𝔪 ψ N‖ ≤ B := by
  let δ := heckeHarmonicTailExponent (K := K)
  have hδ : 0 < δ := heckeHarmonicTailExponent_pos (K := K)
  have hbase : 1 - (finrank ℚ K : ℝ)⁻¹ < 1 - δ := by
    dsimp only [δ, heckeHarmonicTailExponent]
    linarith [inv_pos.mpr (show (0 : ℝ) < finrank ℚ K by exact_mod_cast finrank_pos)]
  obtain ⟨C, hC⟩ := exists_norm_sum_heckeCoeff_le hψ
  obtain ⟨M, hM⟩ := exists_norm_sum_term_le (heckeCoeff_zero ψ) errExp_nonneg hC hbase
  obtain ⟨B, hB⟩ := exists_norm_sum_log_mul_powNeg_le hM hδ
  refine ⟨B, fun N => ?_⟩
  have heq (n : ℕ) :
      LSeries.term (heckeCoeff 𝔪 ψ) ((1 - δ : ℝ) : ℂ) n * (Real.log n : ℂ) *
          powNeg (δ : ℂ) n =
        LSeries.term (heckeCoeff 𝔪 ψ) 1 n * (Real.log n : ℂ) := by
    rw [term_eq_mul_powNeg (heckeCoeff 𝔪 ψ) ((1 - δ : ℝ) : ℂ) 1 n]
    have hd : (1 : ℂ) - ((1 - δ : ℝ) : ℂ) = (δ : ℂ) := by push_cast; ring
    rw [hd]
    ring
  have h := hB (N + 1)
  simp_rw [heq] at h
  rw [sum_range_succ_eq_sum_Icc (by simp)] at h
  convert h using 2
  unfold heckeLogarithmicHarmonicSum
  refine sum_congr rfl fun n hn => ?_
  rw [LSeries.term_of_ne_zero (by have := (mem_Icc.mp hn).1; omega), Complex.cpow_one]

end GaloisForLFunctions.HeckeLFunctions

