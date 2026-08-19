import GaloisForLFunctions.RHTower.Sieve.JointLadderProduct
import GaloisForLFunctions.RHTower.Sieve.LogPolyRestrict
import GaloisForLFunctions.RHTower.Sieve.LadderErrorBudget
import GaloisForLFunctions.RHTower.Sieve.CofactorLowFreqBound

/-!
# The short ladder's defect, at the divisor bound

`Sieve/JointLadderProduct.integral_normSq_jointLadderProductDefect_le_closed` pays the crude
coefficient bound `#Q` for the long-weighted cofactor.  That is fatal in the assembly: `#Q` is of
the size of the long primes themselves, `≍ exp((log x)^b)`, whereas the defect has to be `o(B₀²)`.

The repair is the divisor bound.  Every index of every gap set lies in `[1, B₀]`, and a designated
long prime exceeds `R_Q`, so

```text
   ‖μ(n)·ω_Q(n)‖  ≤  ω_Q(n)  ≤  log B₀ / log R_Q       for  1 ≤ n ≤ B₀ ,
```

which at `log R_Q ≍ (log x)^a` is a *small power of the logarithm* rather than a power of `x`.
This is the same device that keeps `Sieve/LadderProductDefect` honest for the single weight.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The long-weighted coefficient, restricted to an initial segment, obeys the divisor bound.** -/
theorem norm_restrict_omegaQCoeff_le {Q : Finset ℕ} {RQ : ℝ} (hRQ : 1 < RQ)
    (hQprime : ∀ q ∈ Q, q.Prime) (hQge : ∀ q ∈ Q, RQ ≤ (q : ℝ)) (N : ℕ) (n : ℕ) :
    ‖restrictCoeff (Finset.Icc 1 N) (omegaQCoeff Q) n‖ ≤ Real.log N / Real.log RQ + 1 := by
  classical
  have hlogQ : 0 < Real.log RQ := Real.log_pos hRQ
  rw [restrictCoeff]
  by_cases hmem : n ∈ Finset.Icc 1 N
  · rw [if_pos hmem]
    rw [Finset.mem_Icc] at hmem
    have hdiv := card_designatedPrimes_dvd_le hRQ hQprime hQge hmem.1 hmem.2
    have hcast : ‖omegaQCoeff Q n‖ ≤ ((primeFactorsIn Q n).card : ℝ) := by
      rw [omegaQCoeff, norm_mul, Complex.norm_natCast]
      have h1 := norm_moebiusCoeff_le_one n
      have h2 : (0 : ℝ) ≤ ((primeFactorsIn Q n).card : ℝ) := Nat.cast_nonneg _
      nlinarith [h1, h2, norm_nonneg (moebiusCoeff n)]
    have hpf : primeFactorsIn Q n = Q.filter (fun p => p ∣ n) := rfl
    rw [hpf] at hcast
    linarith [hcast, hdiv]
  · rw [if_neg hmem, norm_zero]
    have h0 : (0 : ℝ) ≤ Real.log N / Real.log RQ :=
      div_nonneg (Real.log_natCast_nonneg N) hlogQ.le
    linarith

/-- Restricting a coefficient to a superset of the index set changes nothing. -/
theorem logPoly_restrictCoeff_of_subset (a : ℕ → ℂ) {S T : Finset ℕ} (hST : S ⊆ T) (w : ℝ) :
    logPoly (restrictCoeff T a) S w = logPoly a S w := by
  rw [logPoly, logPoly]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [restrictCoeff, if_pos (hST hn)]

/-- Every gap set of the short ladder over an initial index range lies in that range. -/
theorem ladderGapSetAt_one_subset {B₀ : ℕ} {RP ηP : ℝ} (hRP : 1 ≤ RP)
    (hηP : 0 ≤ ηP) (x : (_ : ℕ) × ℕ) :
    ladderGapSetAt 1 B₀ RP ηP x ⊆ Finset.Icc 1 B₀ := by
  classical
  have hsub : ladderGapSetAt 1 B₀ RP ηP x ⊆ geomCofactorBlockAt 1 B₀ RP ηP x.1 :=
    fun m hm => (Finset.mem_sdiff.1 hm).1
  refine hsub.trans ?_
  rw [geomCofactorBlockAt_one_eq hRP hηP]
  have hr1 : (1 : ℝ) ≤ 1 + ηP := by linarith
  have hpow : (1 : ℝ) ≤ (1 + ηP) ^ x.1 := one_le_pow₀ hr1
  have hden : (1 : ℝ) ≤ RP * (1 + ηP) ^ x.1 := by nlinarith [hRP, hpow]
  have hB0 : (0 : ℝ) ≤ (B₀ : ℝ) := Nat.cast_nonneg _
  have hle : (B₀ : ℝ) / (RP * (1 + ηP) ^ x.1) ≤ (B₀ : ℝ) := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hB0, hden]
  have hfl : ⌊(B₀ : ℝ) / (RP * (1 + ηP) ^ x.1)⌋₊ ≤ B₀ := by
    have hstep := Nat.floor_le_floor hle
    rwa [Nat.floor_natCast] at hstep
  exact Finset.Icc_subset_Icc le_rfl hfl

/-- The short ladder's defect, written with the restricted coefficient. -/
theorem jointLadderProductDefect_eq_restrict {P Q : Finset ℕ} {B₀ : ℕ} {RP ηP : ℝ}
    (hRP : 1 ≤ RP) (hηP : 0 ≤ ηP) (LP : ℕ) (w : ℝ) :
    jointLadderProductDefect P Q 1 B₀ RP ηP LP w
      = ∑ x ∈ ladderIndex P RP ηP LP, moebiusPhase w x.2
          * logPoly (restrictCoeff (Finset.Icc 1 B₀) (omegaQCoeff Q))
              (ladderGapSetAt 1 B₀ RP ηP x) w := by
  rw [jointLadderProductDefect]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [logPoly_restrictCoeff_of_subset (omegaQCoeff Q)
    (ladderGapSetAt_one_subset (B₀ := B₀) hRP hηP x) w]

/-- **The short ladder's defect at the divisor bound.** -/
theorem integral_normSq_jointLadderProductDefect_le_divisor {P Q : Finset ℕ} {B₀ : ℕ}
    {RP ηP W : ℝ} (hRP : 1 < RP) (hηP : 0 ≤ ηP) (hW : 1 ≤ W) {LP : ℕ}
    (hPprime : ∀ p ∈ P, p.Prime) (hPge : ∀ p ∈ P, RP ≤ (p : ℝ))
    {RQ : ℝ} (hRQ : 1 < RQ) (hQprime : ∀ q ∈ Q, q.Prime) (hQge : ∀ q ∈ Q, RQ ≤ (q : ℝ)) :
    (∫ w in Set.Icc (-W) W, ‖jointLadderProductDefect P Q 1 B₀ RP ηP LP w‖ ^ 2)
      ≤ (Real.log B₀ / Real.log RQ + 1) ^ 2
        * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + ηP)⌋₊ : ℕ) : ℝ))
          * (Real.log ((⌊(B₀ : ℝ) * (1 + ηP)⌋₊ : ℕ) : ℝ) / Real.log RP
            * ∑ j ∈ Finset.range LP, (RP * (1 + ηP) ^ j * ηP + 1)
                * ((((1 : ℕ) : ℝ) + (B₀ : ℝ)) * ηP / (RP * (1 + ηP) ^ j) + 5
                  + (B₀ : ℝ) / (RP * (1 + ηP) ^ j) ^ 2))) := by
  classical
  have hRP0 : (0 : ℝ) < RP := lt_trans zero_lt_one hRP
  have hlogRP : 0 < Real.log RP := Real.log_pos hRP
  set N : ℕ := ⌊(B₀ : ℝ) * (1 + ηP)⌋₊ with hN
  have hK0 : (0 : ℝ) ≤ Real.log ((N : ℕ) : ℝ) / Real.log RP :=
    div_nonneg (Real.log_natCast_nonneg N) hlogRP.le
  have hpos : ∀ x ∈ ladderIndex P RP ηP LP, 0 < x.2 := by
    intro x hx
    rw [ladderIndex, Finset.mem_sigma] at hx
    exact (hPprime x.2 (geomBlock_subset P RP (1 + ηP) x.1 hx.2)).pos
  have hDpos : ∀ x ∈ ladderIndex P RP ηP LP, ∀ m ∈ ladderGapSetAt 1 B₀ RP ηP x, 0 < m := by
    intro x _ m hm
    exact ladderGapSetAt_pos (by omega) hRP0 hηP x.1 ((Finset.mem_sdiff.1 hm).1)
  have hDN : ∀ x ∈ ladderIndex P RP ηP LP,
      (ladderGapSetAt 1 B₀ RP ηP x).image (fun m => x.2 * m) ⊆ Finset.Icc 1 N := by
    intro x hx n hn
    have hbase := ladderGapSetAt_image_subset 1 B₀ hRP.le hηP LP x hx hn
    rw [Finset.mem_Icc] at hbase ⊢
    refine ⟨?_, hbase.2⟩
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    have hp := hPprime x.2 (by
      rw [ladderIndex, Finset.mem_sigma] at hx
      exact geomBlock_subset P RP (1 + ηP) x.1 hx.2)
    have hm0 : 0 < m := ladderGapSetAt_pos (by omega) hRP0 hηP x.1 ((Finset.mem_sdiff.1 hm).1)
    have : 0 < x.2 * m := Nat.mul_pos hp.pos hm0
    omega
  have hKmem : ∀ n ∈ Finset.Icc 1 N, (((ladderIndex P RP ηP LP).filter
      (fun x => n ∈ (ladderGapSetAt 1 B₀ RP ηP x).image (fun m => x.2 * m))).card : ℝ)
      ≤ Real.log ((N : ℕ) : ℝ) / Real.log RP := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    refine (ladderIndex_filter_card_le_gen hRP0 hηP LP (ladderGapSetAt 1 B₀ RP ηP) n).trans ?_
    exact card_designatedPrimes_dvd_le hRP hPprime hPge hn.1 hn.2
  have hΩ : (0 : ℝ) < Real.log B₀ / Real.log RQ + 1 := by
    have hlogQ : 0 < Real.log RQ := Real.log_pos hRQ
    have : (0 : ℝ) ≤ Real.log B₀ / Real.log RQ :=
      div_nonneg (Real.log_natCast_nonneg B₀) hlogQ.le
    linarith
  have hcbd := norm_restrict_omegaQCoeff_le (Q := Q) hRQ hQprime hQge B₀
  have hmain := integral_Icc_normSq_primeShift_family_le_bound (ladderIndex P RP ηP LP)
    (fun x => x.2) (ladderGapSetAt 1 B₀ RP ηP)
    (restrictCoeff (Finset.Icc 1 B₀) (omegaQCoeff Q)) hpos hDpos hΩ hcbd hK0 hDN hKmem hW
  have hcongr : (∫ w in Set.Icc (-W) W, ‖jointLadderProductDefect P Q 1 B₀ RP ηP LP w‖ ^ 2)
      = ∫ w in Set.Icc (-W) W,
        ‖∑ x ∈ ladderIndex P RP ηP LP, moebiusPhase w x.2
          * logPoly (restrictCoeff (Finset.Icc 1 B₀) (omegaQCoeff Q))
              (ladderGapSetAt 1 B₀ RP ηP x) w‖ ^ 2 := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => ?_
    rw [jointLadderProductDefect_eq_restrict hRP.le hηP LP w]
  rw [hcongr]
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcoef : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((N : ℕ) : ℝ) := by
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W := mul_nonneg (by positivity) hW0.le
    have h2 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * ((N : ℕ) : ℝ) :=
      mul_nonneg (by positivity) (Nat.cast_nonneg N)
    linarith
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK0) hcoef
  exact sum_card_ladderGapSetAt_le 1 B₀ hRP0 hηP LP hPprime

end

end RHTower.Sieve
