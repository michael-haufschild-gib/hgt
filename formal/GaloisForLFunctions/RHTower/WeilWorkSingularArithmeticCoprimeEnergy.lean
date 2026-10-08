import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMaskedEnergy
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticParityVariance
import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCoprimeRatio

/-!
# One energy constant controls every actual coprime residue

The actual forward log-energy constant bounds all finite prime deletions
simultaneously. The canonical density is retained by masked Cauchy--Schwarz.
No coefficient sign, multiplicativity, or uniform radial remainder is assumed.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic
open WeilWorkSettledPhase

/-- Density of the integers coprime to a positive modulus. -/
def coprimeDensity (Q : ℕ) : ℝ := ∏ p ∈ Q.primeFactors, (1 - (p : ℝ)⁻¹)

theorem coprimeDensity_pos (Q : ℕ) : 0 < coprimeDensity Q := by
  apply Finset.prod_pos
  intro p hp
  have hp1 : 1 < (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  exact sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)

theorem coprimeDensity_eq_totient_div (Q : ℕ) [NeZero Q] :
    coprimeDensity Q = (Q.totient : ℝ) / Q := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (Nat.totient_eq_mul_prod_factors Q)
  push_cast at h
  exact (eq_div_iff (by exact_mod_cast (NeZero.ne Q) : (Q : ℝ) ≠ 0)).mpr
    (by simpa only [coprimeDensity, mul_comm] using h.symm)

private theorem mask_sq (Q n : ℕ) :
    ‖(coprimeMask Q n : ℂ)‖ ^ 2 = coprimeMask Q n := by
  unfold coprimeMask
  split_ifs <;> norm_num

private theorem mask_square_summable (Q : ℕ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => ‖(coprimeMask Q n : ℂ)‖ ^ 2 / (n : ℝ) ^ s) := by
  refine (Real.summable_one_div_nat_rpow.mpr hs).of_nonneg_of_le
    (fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) fun n => ?_
  rw [mask_sq]
  unfold coprimeMask
  split_ifs
  · rfl
  · simp only [zero_div]
    positivity

private theorem mask_square_series (Q : ℕ) {s : ℝ} (hs : 1 < s) :
    (LSeries (coprimePart Q 1) (s : ℂ)).re =
      ∑' n : ℕ, ‖(coprimeMask Q n : ℂ)‖ ^ 2 / (n : ℝ) ^ s := by
  have hm := summable_coprimePart Q
    (LSeriesSummable_one_iff.mpr (show 1 < (s : ℂ).re from hs))
  rw [LSeries, Complex.re_tsum hm]
  apply tsum_congr
  intro n
  rw [mask_sq]
  by_cases hn : n = 0
  · simp [hn, LSeries.term, Real.zero_rpow (by linarith : s ≠ 0)]
  · have he : (n : ℂ) ^ (s : ℂ) = (((n : ℝ) ^ s : ℝ) : ℂ) :=
      (Complex.ofReal_cpow (Nat.cast_nonneg n) s).symm
    simp only [LSeries.term, if_neg hn, coprimePart, Pi.one_apply, mul_one,
      he, ← Complex.ofReal_div,
      Complex.ofReal_re]

/-- The actual radial square density of the coprimality mask. -/
theorem coprime_mask_square_residue (Q : ℕ) [NeZero Q] :
    Tendsto (fun s : ℝ =>
      (s - 1) * ∑' n : ℕ, ‖(coprimeMask Q n : ℂ)‖ ^ 2 / (n : ℝ) ^ s)
      (𝓝[>] 1) (𝓝 (coprimeDensity Q)) := by
  have hc : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      DirichletCharacter.LFunctionTrivChar Q (s : ℂ)) (𝓝[>] 1)
      (𝓝 (coprimeDensity Q : ℂ)) := by
    simpa only [Function.comp_def, coprimeDensity, Complex.ofReal_prod,
      Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_inv, Complex.ofReal_natCast] using
      (DirichletCharacter.LFunctionTrivChar_residue_one (N := Q)).comp
        tendsto_ofReal_nhdsWithin_ne_one
  have ht := Complex.continuous_re.continuousAt.tendsto.comp hc
  simp only [Complex.ofReal_re] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply]
  rw [← LSeries_coprimePart_one Q (show 1 < (s : ℂ).re from hs)]
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
    Complex.sub_im, Complex.ofReal_im, Complex.one_im, sub_self, zero_mul, sub_zero]
  rw [mask_square_series Q hs]

/-- The same actual source energy constant controls every finite coprime
radial residue. Full positivity is the only arithmetic premise. -/
theorem exists_forward_coprime_energy {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Finset.Icc 1 N, ‖forwardCoeff lam n‖ ^ 2 / n) / Real.log N)
        atTop (𝓝 K) ∧
      ∀ Q : ℕ, Q ≠ 0 → ∃ r : ℝ, 0 < r ∧
        Tendsto (fun s : ℝ => LSeries (coprimePart Q (sourceCoeff lam)) (s : ℂ) /
          LSeries (sourceCoeff lam) (s : ℂ)) (𝓝[>] 1) (𝓝 (r : ℂ)) ∧
        ‖sourceCompletion hW 1‖ ^ 2 * r ^ 2 ≤ K * coprimeDensity Q := by
  obtain ⟨K, _, hK, _, _, hE, _⟩ := exists_forwardCoeff_energy_variance hW
  refine ⟨K, hK, hE, fun Q hQ => ?_⟩
  haveI : NeZero Q := ⟨hQ⟩
  obtain ⟨r, _, _, hr, _, _, hRatio, _⟩ := exists_coprime_source_ratio_limit hW Q
  refine ⟨r, hr, hRatio, ?_⟩
  have he : Tendsto (fun N : ℕ =>
      weightPartialSum (fun n => ‖sourceCoeff lam n‖ ^ 2 / n) N / Real.log N)
      atTop (𝓝 K) := by
    apply hE.congr
    intro N
    congr 1
    unfold weightPartialSum
    simp only [forwardCoeff_eq_sourceCoeff]
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hn'
      have hn0 : n = 0 := by
        simp only [Finset.mem_Icc] at hn hn'
        omega
      simp [hn0]
  have hfg : (fun n => sourceCoeff lam n * (coprimeMask Q n : ℂ)) =
      coprimePart Q (sourceCoeff lam) := by funext n; exact mul_comm _ _
  have hR : Tendsto (fun s : ℝ => ((s : ℂ) - 1) *
      LSeries (fun n => sourceCoeff lam n * (coprimeMask Q n : ℂ)) (s : ℂ))
      (𝓝[>] 1) (𝓝 ((r : ℂ) * sourceCompletion hW 1)) := by
    apply (hRatio.mul (forward_source_residue hW)).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hn : LSeries (sourceCoeff lam) (s : ℂ) ≠ 0 := by
      rw [(sourceCoeff_LSeries hW (s := (s : ℂ)) hs).2, IntegerMassRigidity.zetaOf]
      exact Complex.exp_ne_zero _
    rw [hfg]
    field_simp [hn]
  have hb := norm_masked_residue_sq_le_log_energy hK.le he
    (fun s hs => by rw [hfg]; exact summable_coprimePart Q (sourceCoeff_LSeries hW hs).1)
    (fun _ hs => mask_square_summable Q hs) (coprime_mask_square_residue Q) hR
  simpa only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    mul_comm] using hb

end RHTower.WeilSingularArithmetic
