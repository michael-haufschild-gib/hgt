import GaloisForLFunctions.RHTower.Sieve.JointOmegaFactorisation
import GaloisForLFunctions.RHTower.Sieve.LadderProductDefect

/-!
# The jointly weighted polynomial against a genuine product over the short ladder

The `ω_P·ω_Q`-weighted Möbius polynomial factorises exactly over the short designated primes
(`Sieve/JointOmegaFactorisation`), but the cofactor range of each summand depends on the prime.
Replacing it by the common range of the prime's ladder step turns the polynomial into a sum of
*products* — a prime polynomial times one `ω_Q`-weighted cofactor polynomial per step.  This is the
form the harmonic Cauchy–Schwarz and the exceptional-set split of exposé §4 consume.

Everything here mirrors `Sieve/LadderProductDefect`, whose cofactor carries the plain Möbius
coefficient; the only change is that the cofactor coefficient is now `μ(m)·ω_Q(m)`, bounded by
`#Q` rather than by `1`, and the defect bound is rescaled accordingly.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The long-weighted Möbius coefficient carried by the cofactor polynomial. -/
def omegaQCoeff (Q : Finset ℕ) (m : ℕ) : ℂ :=
  ((primeFactorsIn Q m).card : ℂ) * moebiusCoeff m

/-- The single-weight polynomial is the Gallagher polynomial of the long-weighted coefficient. -/
theorem omegaWeightedMoebiusPoly_eq_logPoly (Q S : Finset ℕ) (w : ℝ) :
    omegaWeightedMoebiusPoly Q S w = logPoly (omegaQCoeff Q) S w := by
  rw [omegaWeightedMoebiusPoly, logPoly]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [omegaQCoeff, moebiusCoeff, moebiusPhase, unitLogPhase]
  ring

/-- The long-weighted coefficient is bounded by the size of the long range. -/
theorem norm_omegaQCoeff_le (Q : Finset ℕ) (m : ℕ) : ‖omegaQCoeff Q m‖ ≤ (Q.card : ℝ) := by
  have h1 : ‖((primeFactorsIn Q m).card : ℂ)‖ = ((primeFactorsIn Q m).card : ℝ) := by
    rw [Complex.norm_natCast]
  have h2 := norm_moebiusCoeff_le_one m
  have h3 : ((primeFactorsIn Q m).card : ℝ) ≤ (Q.card : ℝ) := by
    have := Finset.card_le_card (Finset.filter_subset (fun p => p ∣ m) Q)
    exact_mod_cast this
  have h4 : (0 : ℝ) ≤ ((primeFactorsIn Q m).card : ℝ) := Nat.cast_nonneg _
  rw [omegaQCoeff, norm_mul, h1]
  nlinarith [h2, h3, h4, norm_nonneg (moebiusCoeff m)]

/-- Dividing the coefficient divides the polynomial. -/
theorem logPoly_div_const (c : ℕ → ℂ) (D : Finset ℕ) (C : ℂ) (w : ℝ) :
    logPoly (fun n => c n / C) D w = logPoly c D w / C := by
  rw [logPoly, logPoly, Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-! ## The ladder of genuine products -/

/-- The ladder of genuine products, with the long weight retained in the cofactor. -/
def jointLadderProductPoly (P Q : Finset ℕ) (A₀ B₀ : ℕ) (R η : ℝ) (L : ℕ) (w : ℝ) : ℂ :=
  ∑ j ∈ Finset.range L,
    primeBlockPoly (geomBlock P R (1 + η) j) w
      * logPoly (omegaQCoeff Q) (geomCofactorBlockAt A₀ B₀ R η j) w

/-- The defect of the ladder of products against the jointly weighted polynomial. -/
def jointLadderProductDefect (P Q : Finset ℕ) (A₀ B₀ : ℕ) (R η : ℝ) (L : ℕ) (w : ℝ) : ℂ :=
  ∑ x ∈ ladderIndex P R η L,
    moebiusPhase w x.2 * logPoly (omegaQCoeff Q) (ladderGapSetAt A₀ B₀ R η x) w

/-- **The ladder of products differs from the jointly weighted polynomial by one prime-shifted
family.** -/
theorem jointLadderProductPoly_sub_jointOmega_eq {P Q : Finset ℕ} (A₀ B₀ : ℕ) {R η : ℝ}
    (hR : 0 < R) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L)
    (hPprime : ∀ p ∈ P, p.Prime) (hQprime : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
    (hP : ∀ p ∈ P, R < (p : ℝ) ∧ (p : ℝ) ≤ R * (1 + η) ^ L) (w : ℝ) :
    jointLadderProductPoly P Q A₀ B₀ R η L w
        - jointOmegaPoly P Q (Finset.Icc A₀ B₀) w
      = jointLadderProductDefect P Q A₀ B₀ R η L w := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hjoint : jointOmegaPoly P Q (Finset.Icc A₀ B₀) w
      = ∑ j ∈ Finset.range L, ∑ p ∈ geomBlock P R (1 + η) j,
          moebiusPhase w p
            * logPoly (omegaQCoeff Q) {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m} w := by
    rw [jointOmegaPoly_eq_blocks hPprime hQprime hPQ (Finset.Icc A₀ B₀) w (Finset.range L)
      (geomBlock P R (1 + η)) (geomBlock_pairwiseDisjoint P hR hr1 L)
      (geomBlock_biUnion_eq P R (1 + η) hL hP)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => ?_
    rw [omegaWeightedMoebiusPoly_eq_logPoly]
  have hprod : jointLadderProductPoly P Q A₀ B₀ R η L w
      = ∑ j ∈ Finset.range L, ∑ p ∈ geomBlock P R (1 + η) j,
          moebiusPhase w p * logPoly (omegaQCoeff Q) (geomCofactorBlockAt A₀ B₀ R η j) w := by
    rw [jointLadderProductPoly]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [primeBlockPoly, Finset.sum_mul]
  rw [hprod, hjoint, ← Finset.sum_sub_distrib, jointLadderProductDefect, ladderIndex,
    Finset.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  set Rj : ℝ := R * (1 + η) ^ j with hRj
  have hRj0 : (0 : ℝ) < Rj := by
    rw [hRj]
    have : (0 : ℝ) < (1 + η) ^ j := by positivity
    positivity
  have hq := hPprime p (geomBlock_subset P R (1 + η) j hp)
  have hrange : Rj < (p : ℝ) ∧ (p : ℝ) ≤ Rj * (1 + η) := by
    rw [geomBlock, Finset.mem_filter] at hp
    obtain ⟨-, hlo, hhi⟩ := hp
    refine ⟨hlo, ?_⟩
    have hpow : R * (1 + η) ^ (j + 1) = Rj * (1 + η) := by
      rw [hRj, pow_succ]
      ring
    rwa [hpow] at hhi
  have hsub := cofactorFilter_subset_common_at (Q := Rj) (η := η) A₀ B₀ hRj0 hη hq.pos
    hrange.1 hrange.2
  have hUC : {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m}
      \ geomCofactorBlockAt A₀ B₀ R η j = ∅ := by
    rw [geomCofactorBlockAt, ← hRj]
    exact Finset.sdiff_eq_empty_iff_subset.2 hsub
  have hdiff : logPoly (omegaQCoeff Q) (geomCofactorBlockAt A₀ B₀ R η j) w
      - logPoly (omegaQCoeff Q) {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m} w
      = logPoly (omegaQCoeff Q) (ladderGapSetAt A₀ B₀ R η ⟨j, p⟩) w := by
    rw [logPoly_sub_eq_sdiff, hUC, ladderGapSetAt]
    simp [logPoly]
  rw [← mul_sub, hdiff]

/-! ## The mean square of the defect -/

/-- **The prime-shifted family bound at a general coefficient bound.**  The corpus's version assumes
unit coefficients; the long-weighted cofactor is bounded by `#Q`, and the estimate rescales. -/
theorem integral_Icc_normSq_primeShift_family_le_bound {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (p : ι → ℕ) (D : ι → Finset ℕ) (c : ℕ → ℂ) {N : ℕ} {K W Ω : ℝ}
    (hp : ∀ i ∈ I, 0 < p i) (hD : ∀ i ∈ I, ∀ m ∈ D i, 0 < m)
    (hΩ : 0 < Ω) (hc : ∀ n, ‖c n‖ ≤ Ω) (hK0 : 0 ≤ K)
    (hDN : ∀ i ∈ I, (D i).image (fun m => p i * m) ⊆ Finset.Icc 1 N)
    (hK : ∀ n ∈ Finset.Icc 1 N,
      ((I.filter (fun i => n ∈ (D i).image (fun m => p i * m))).card : ℝ) ≤ K)
    (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖∑ i ∈ I, moebiusPhase w (p i) * logPoly c (D i) w‖ ^ (2 : ℕ))
      ≤ Ω ^ (2 : ℕ) * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ))
          * (K * ∑ i ∈ I, ((D i).card : ℝ))) := by
  classical
  have hΩC : (Ω : ℂ) ≠ 0 := by
    simpa using (ne_of_gt hΩ)
  have hc1 : ∀ n, ‖c n / (Ω : ℂ)‖ ≤ 1 := by
    intro n
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΩ, div_le_one hΩ]
    exact hc n
  have hbase := integral_Icc_normSq_primeShift_family_le I p D (fun n => c n / (Ω : ℂ))
    hp hD hc1 hK0 hDN hK hW
  have hrep : ∀ w : ℝ, ‖∑ i ∈ I, moebiusPhase w (p i) * logPoly (fun n => c n / (Ω : ℂ)) (D i) w‖ ^ (2 : ℕ)
      = ‖∑ i ∈ I, moebiusPhase w (p i) * logPoly c (D i) w‖ ^ (2 : ℕ) / Ω ^ (2 : ℕ) := by
    intro w
    have hsum : (∑ i ∈ I, moebiusPhase w (p i) * logPoly (fun n => c n / (Ω : ℂ)) (D i) w)
        = (∑ i ∈ I, moebiusPhase w (p i) * logPoly c (D i) w) / (Ω : ℂ) := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [logPoly_div_const]
      ring
    rw [hsum, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hΩ, div_pow]
  have hint : (∫ w in Set.Icc (-W) W,
        ‖∑ i ∈ I, moebiusPhase w (p i) * logPoly (fun n => c n / (Ω : ℂ)) (D i) w‖ ^ (2 : ℕ))
      = (∫ w in Set.Icc (-W) W, ‖∑ i ∈ I, moebiusPhase w (p i) * logPoly c (D i) w‖ ^ (2 : ℕ))
          / Ω ^ (2 : ℕ) := by
    rw [← MeasureTheory.integral_div]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun w _ => hrep w
  rw [hint, div_le_iff₀ (by positivity)] at hbase
  linarith [hbase]

/-- **The mean square of the joint ladder defect, in closed form.** -/
theorem integral_normSq_jointLadderProductDefect_le_closed {P Q : Finset ℕ} {A₀ B₀ : ℕ}
    (hA : 0 < A₀) {R η W : ℝ} (hR : 1 < R) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ}
    (hPprime : ∀ p ∈ P, p.Prime) (hPge : ∀ p ∈ P, R ≤ (p : ℝ)) :
    (∫ w in Set.Icc (-W) W, ‖jointLadderProductDefect P Q A₀ B₀ R η L w‖ ^ (2 : ℕ))
      ≤ ((Q.card : ℝ) + 1) ^ (2 : ℕ)
        * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
          * (Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log R
            * ∑ j ∈ Finset.range L, (R * (1 + η) ^ j * η + 1)
                * (((A₀ : ℝ) + (B₀ : ℝ)) * η / (R * (1 + η) ^ j) + 5
                  + (B₀ : ℝ) / (R * (1 + η) ^ j) ^ (2 : ℕ)))) := by
  classical
  have hR0 : (0 : ℝ) < R := lt_trans zero_lt_one hR
  have hlogR : 0 < Real.log R := Real.log_pos hR
  set N : ℕ := ⌊(B₀ : ℝ) * (1 + η)⌋₊ with hN
  have hK0 : (0 : ℝ) ≤ Real.log ((N : ℕ) : ℝ) / Real.log R :=
    div_nonneg (Real.log_natCast_nonneg N) hlogR.le
  have hpos : ∀ x ∈ ladderIndex P R η L, 0 < x.2 := by
    intro x hx
    rw [ladderIndex, Finset.mem_sigma] at hx
    exact (hPprime x.2 (geomBlock_subset P R (1 + η) x.1 hx.2)).pos
  have hDpos : ∀ x ∈ ladderIndex P R η L, ∀ m ∈ ladderGapSetAt A₀ B₀ R η x, 0 < m := by
    intro x _ m hm
    exact ladderGapSetAt_pos hA hR0 hη x.1 ((Finset.mem_sdiff.1 hm).1)
  have hDN : ∀ x ∈ ladderIndex P R η L,
      (ladderGapSetAt A₀ B₀ R η x).image (fun m => x.2 * m) ⊆ Finset.Icc 1 N := by
    intro x hx n hn
    have hbase := ladderGapSetAt_image_subset A₀ B₀ hR.le hη L x hx hn
    rw [Finset.mem_Icc] at hbase ⊢
    refine ⟨?_, hbase.2⟩
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    have hp := hPprime x.2 (by
      rw [ladderIndex, Finset.mem_sigma] at hx
      exact geomBlock_subset P R (1 + η) x.1 hx.2)
    have hm0 : 0 < m := ladderGapSetAt_pos hA hR0 hη x.1 ((Finset.mem_sdiff.1 hm).1)
    have : 0 < x.2 * m := Nat.mul_pos hp.pos hm0
    omega
  have hKmem : ∀ n ∈ Finset.Icc 1 N, (((ladderIndex P R η L).filter
      (fun x => n ∈ (ladderGapSetAt A₀ B₀ R η x).image (fun m => x.2 * m))).card : ℝ)
      ≤ Real.log ((N : ℕ) : ℝ) / Real.log R := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    refine (ladderIndex_filter_card_le_gen hR0 hη L (ladderGapSetAt A₀ B₀ R η) n).trans ?_
    exact card_designatedPrimes_dvd_le hR hPprime hPge hn.1 hn.2
  have hΩ : (0 : ℝ) < (Q.card : ℝ) + 1 := by positivity
  have hcbd : ∀ n, ‖omegaQCoeff Q n‖ ≤ (Q.card : ℝ) + 1 := by
    intro n
    have := norm_omegaQCoeff_le Q n
    linarith
  have hmain := integral_Icc_normSq_primeShift_family_le_bound (ladderIndex P R η L)
    (fun x => x.2) (ladderGapSetAt A₀ B₀ R η) (omegaQCoeff Q) hpos hDpos hΩ hcbd hK0 hDN hKmem hW
  simp only [jointLadderProductDefect]
  refine hmain.trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcoef : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((N : ℕ) : ℝ) := by
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W := mul_nonneg (by positivity) hW0.le
    have h2 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * ((N : ℕ) : ℝ) :=
      mul_nonneg (by positivity) (Nat.cast_nonneg N)
    linarith
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK0) hcoef
  exact sum_card_ladderGapSetAt_le A₀ B₀ hR0 hη L hPprime

end

end RHTower.Sieve
