import GaloisForLFunctions.RHTower.Sieve.TwoSidedCofactorBlock
import GaloisForLFunctions.RHTower.Sieve.OmegaWeightedFactorisation

/-!
# The weighted polynomial against a genuine product over the ladder

The `ω_P`-weighted Möbius polynomial factors exactly, but the cofactor range of each summand depends
on the prime.  Replacing it by the common range of the prime's ladder step turns the whole
polynomial into a sum of *products* — a prime polynomial times a single cofactor polynomial — which
is the form the harmonic Cauchy--Schwarz and the twisted prime-sum bound consume.

The defect of that replacement is one prime-shifted family over the gap sets, so its mean square
carries a single power of the overlap count and of the total gap size.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The filtered cofactor set of a thin range sits inside the common two-sided block.** -/
theorem cofactorFilter_subset_common_at (A₀ B₀ : ℕ) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    {p : ℕ} (hp0 : 0 < p) (hplo : Q < (p : ℝ)) (hphi : (p : ℝ) ≤ Q * (1 + η)) :
    {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m}
      ⊆ Finset.Icc ⌈(A₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊ := by
  classical
  have hQη : (0 : ℝ) < Q * (1 + η) := by positivity
  intro m hm
  rw [Finset.mem_filter] at hm
  have hmem := (mem_ramareCofactorSet_iff hp0).1 hm.1
  rw [Finset.mem_Icc] at hmem
  obtain ⟨hlo, hhi⟩ := hmem
  have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hloR : ((A₀ : ℕ) : ℝ) ≤ (p : ℝ) * (m : ℝ) := by exact_mod_cast hlo
  have hhiR : (p : ℝ) * (m : ℝ) ≤ ((B₀ : ℕ) : ℝ) := by exact_mod_cast hhi
  rw [Finset.mem_Icc]
  constructor
  · refine Nat.ceil_le.2 ?_
    rw [div_le_iff₀ hQη]
    nlinarith [hloR, hphi, hmR]
  · refine Nat.le_floor ?_
    rw [le_div_iff₀ hQ]
    nlinarith [hhiR, hplo, hmR]

/-- The Möbius coefficient sequence carried by the Gallagher polynomial. -/
def moebiusCoeff (n : ℕ) : ℂ := ((ArithmeticFunction.moebius n : ℤ) : ℂ)

theorem norm_moebiusCoeff_le_one (n : ℕ) : ‖moebiusCoeff n‖ ≤ 1 := by
  have h : moebiusCoeff n = moebiusPhase 0 n := by
    rw [moebiusCoeff, moebiusPhase, unitLogPhase]
    simp
  rw [h]
  exact norm_moebiusPhase_le_one 0 n

/-- The ladder of genuine products: a prime polynomial times one cofactor polynomial per step. -/
def ladderProductPoly (P : Finset ℕ) (A₀ B₀ : ℕ) (Q η : ℝ) (L : ℕ) (w : ℝ) : ℂ :=
  ∑ j ∈ Finset.range L,
    primeBlockPoly (geomBlock P Q (1 + η) j) w
      * logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w

/-- The defect of the ladder of products against the weighted polynomial. -/
def ladderProductDefect (P : Finset ℕ) (A₀ B₀ : ℕ) (Q η : ℝ) (L : ℕ) (w : ℝ) : ℂ :=
  ∑ x ∈ ladderIndex P Q η L,
    moebiusPhase w x.2 * logPoly moebiusCoeff (ladderGapSetAt A₀ B₀ Q η x) w

/-- **The ladder of products differs from the weighted polynomial by one prime-shifted family.** -/
theorem ladderProductPoly_sub_omegaWeighted_eq {P : Finset ℕ} (A₀ B₀ : ℕ) {Q η : ℝ}
    (hQ : 0 < Q) (hη : 0 ≤ η) {L : ℕ} (hL : 1 ≤ L) (hPprime : ∀ q ∈ P, q.Prime)
    (hP : ∀ p ∈ P, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L) (w : ℝ) :
    ladderProductPoly P A₀ B₀ Q η L w
        - omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w
      = ladderProductDefect P A₀ B₀ Q η L w := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  -- the weighted polynomial, split over the ladder
  have homega : omegaWeightedMoebiusPoly P (Finset.Icc A₀ B₀) w
      = ∑ j ∈ Finset.range L, ∑ p ∈ geomBlock P Q (1 + η) j,
          moebiusPhase w p
            * logPoly moebiusCoeff {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m} w := by
    rw [omegaWeightedMoebiusPoly_eq_blocks hPprime (Finset.Icc A₀ B₀) w (Finset.range L)
      (geomBlock P Q (1 + η)) (geomBlock_pairwiseDisjoint P hQ hr1 L)
      (geomBlock_biUnion_eq P Q (1 + η) hL hP)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ => ?_
    congr 1
  -- the product ladder, expanded
  have hprod : ladderProductPoly P A₀ B₀ Q η L w
      = ∑ j ∈ Finset.range L, ∑ p ∈ geomBlock P Q (1 + η) j,
          moebiusPhase w p * logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w := by
    rw [ladderProductPoly]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [primeBlockPoly, Finset.sum_mul]
  rw [hprod, homega, ← Finset.sum_sub_distrib, ladderProductDefect, ladderIndex,
    Finset.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  set Qj : ℝ := Q * (1 + η) ^ j with hQj
  have hQj0 : (0 : ℝ) < Qj := by
    rw [hQj]
    have : (0 : ℝ) < (1 + η) ^ j := by positivity
    positivity
  have hq := hPprime p (geomBlock_subset P Q (1 + η) j hp)
  have hrange : Qj < (p : ℝ) ∧ (p : ℝ) ≤ Qj * (1 + η) := by
    rw [geomBlock, Finset.mem_filter] at hp
    obtain ⟨-, hlo, hhi⟩ := hp
    refine ⟨hlo, ?_⟩
    have hpow : Q * (1 + η) ^ (j + 1) = Qj * (1 + η) := by
      rw [hQj, pow_succ]
      ring
    rwa [hpow] at hhi
  have hsub := cofactorFilter_subset_common_at (Q := Qj) (η := η) A₀ B₀ hQj0 hη hq.pos
    hrange.1 hrange.2
  have hUC : {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m}
      \ geomCofactorBlockAt A₀ B₀ Q η j = ∅ := by
    rw [geomCofactorBlockAt, ← hQj]
    exact Finset.sdiff_eq_empty_iff_subset.2 hsub
  have hdiff : logPoly moebiusCoeff (geomCofactorBlockAt A₀ B₀ Q η j) w
      - logPoly moebiusCoeff {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m} w
      = logPoly moebiusCoeff (ladderGapSetAt A₀ B₀ Q η ⟨j, p⟩) w := by
    rw [logPoly_sub_eq_sdiff, hUC, ladderGapSetAt]
    simp [logPoly]
  rw [← mul_sub, hdiff]

/-! ## The mean square of the defect -/

/-- **The overlap count of any gap family is at most the designated divisor count.**  Distinct
ladder steps are disjoint, so a prime determines its step; nothing about the gap sets is used. -/
theorem ladderIndex_filter_card_le_gen {P : Finset ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    (L : ℕ) (D : (_ : ℕ) × ℕ → Finset ℕ) (n : ℕ) :
    (((ladderIndex P Q η L).filter
        (fun x => n ∈ (D x).image (fun m => x.2 * m))).card : ℝ)
      ≤ ((P.filter (fun p => p ∣ n)).card : ℝ) := by
  classical
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hmaps : ∀ x ∈ (ladderIndex P Q η L).filter
      (fun x => n ∈ (D x).image (fun m => x.2 * m)),
      x.2 ∈ P.filter (fun p => p ∣ n) := by
    intro x hx
    rw [Finset.mem_filter, ladderIndex, Finset.mem_sigma] at hx
    obtain ⟨⟨-, hxblock⟩, hximg⟩ := hx
    rw [Finset.mem_image] at hximg
    obtain ⟨m, -, hnm⟩ := hximg
    exact Finset.mem_filter.2 ⟨geomBlock_subset P Q (1 + η) x.1 hxblock, ⟨m, hnm.symm⟩⟩
  have hinj : Set.InjOn (fun x : (_ : ℕ) × ℕ => x.2)
      (((ladderIndex P Q η L).filter
        (fun x => n ∈ (D x).image (fun m => x.2 * m)) : Finset _) : Set _) := by
    intro x hx y hy hEq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, ladderIndex, Finset.mem_sigma] at hx hy
    have hxb := hx.1.2
    have hyb := hy.1.2
    have hEq' : x.2 = y.2 := hEq
    have hsame : x.1 = y.1 := by
      by_contra hne
      have hdisj := geomBlock_pairwiseDisjoint P hQ hr1 L (Finset.mem_coe.2 hx.1.1)
        (Finset.mem_coe.2 hy.1.1) hne
      exact (Finset.disjoint_left.1 hdisj) hxb (hEq' ▸ hyb)
    exact Sigma.ext hsame (by rw [hEq'])
  have hcard := Finset.card_le_card_of_injOn (fun x : (_ : ℕ) × ℕ => x.2) hmaps hinj
  exact_mod_cast hcard

/-- **Every shifted gap index stays below `B₀(1+η)`.** -/
theorem ladderGapSetAt_image_subset {P : Finset ℕ} (A₀ B₀ : ℕ) {Q η : ℝ} (hQ : 1 ≤ Q)
    (hη : 0 ≤ η) (L : ℕ) :
    ∀ x ∈ ladderIndex P Q η L,
      (ladderGapSetAt A₀ B₀ Q η x).image (fun m => x.2 * m)
        ⊆ Finset.Icc 0 ⌊(B₀ : ℝ) * (1 + η)⌋₊ := by
  classical
  intro x hx n hn
  rw [Finset.mem_image] at hn
  obtain ⟨m, hm, rfl⟩ := hn
  rw [ladderIndex, Finset.mem_sigma] at hx
  set Qj : ℝ := Q * (1 + η) ^ x.1 with hQj
  have hr1 : (1 : ℝ) ≤ 1 + η := by linarith
  have hQj1 : (1 : ℝ) ≤ Qj := by
    rw [hQj]
    have : (1 : ℝ) ≤ (1 + η) ^ x.1 := one_le_pow₀ hr1
    nlinarith [hQ, this]
  have hQj0 : (0 : ℝ) < Qj := lt_of_lt_of_le zero_lt_one hQj1
  have hphi : (x.2 : ℝ) ≤ Qj * (1 + η) := by
    rw [geomBlock, Finset.mem_filter] at hx
    have hhi := hx.2.2.2
    have hpow : Q * (1 + η) ^ (x.1 + 1) = Qj * (1 + η) := by
      rw [hQj, pow_succ]
      ring
    rwa [hpow] at hhi
  have hmC : m ∈ geomCofactorBlockAt A₀ B₀ Q η x.1 := (Finset.mem_sdiff.1 hm).1
  rw [geomCofactorBlockAt, ← hQj, Finset.mem_Icc] at hmC
  have hmhi : (m : ℝ) ≤ (B₀ : ℝ) / Qj := by
    have hfl : ((⌊((B₀ : ℕ) : ℝ) / Qj⌋₊ : ℕ) : ℝ) ≤ ((B₀ : ℕ) : ℝ) / Qj :=
      Nat.floor_le (by positivity)
    have : ((m : ℕ) : ℝ) ≤ ((⌊((B₀ : ℕ) : ℝ) / Qj⌋₊ : ℕ) : ℝ) := by exact_mod_cast hmC.2
    linarith
  refine Finset.mem_Icc.2 ⟨Nat.zero_le _, ?_⟩
  refine Nat.le_floor ?_
  have hprod : ((x.2 * m : ℕ) : ℝ) = (x.2 : ℝ) * (m : ℝ) := by push_cast; ring
  rw [hprod]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hstep : (x.2 : ℝ) * (m : ℝ) ≤ (Qj * (1 + η)) * ((B₀ : ℝ) / Qj) :=
    mul_le_mul hphi hmhi hm0 (by positivity)
  have hval : (Qj * (1 + η)) * ((B₀ : ℝ) / Qj) = (B₀ : ℝ) * (1 + η) := by
    field_simp
  rwa [hval] at hstep

/-- Every gap index of a step is positive once the block of indices starts above zero. -/
theorem ladderGapSetAt_pos {A₀ B₀ : ℕ} (hA : 0 < A₀) {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η)
    (j : ℕ) {m : ℕ} (hm : m ∈ geomCofactorBlockAt A₀ B₀ Q η j) : 0 < m := by
  rw [geomCofactorBlockAt, Finset.mem_Icc] at hm
  have h1 : 1 ≤ ⌈(A₀ : ℝ) / ((Q * (1 + η) ^ j) * (1 + η))⌉₊ := by
    refine Nat.one_le_ceil_iff.2 ?_
    have hpow : (0 : ℝ) < (1 + η) ^ j := by positivity
    have hA0 : (0 : ℝ) < (A₀ : ℝ) := by exact_mod_cast hA
    positivity
  omega

/-- **The mean square of the defect.**  One power of the overlap count and of the total gap size. -/
theorem integral_normSq_ladderProductDefect_le {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q η W : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L N : ℕ} {K : ℝ} (hK0 : 0 ≤ K)
    (hPprime : ∀ q ∈ P, q.Prime)
    (hDN : ∀ x ∈ ladderIndex P Q η L,
      (ladderGapSetAt A₀ B₀ Q η x).image (fun m => x.2 * m) ⊆ Finset.Icc 1 N)
    (hK : ∀ n ∈ Finset.Icc 1 N, (((ladderIndex P Q η L).filter
      (fun x => n ∈ (ladderGapSetAt A₀ B₀ Q η x).image (fun m => x.2 * m))).card : ℝ) ≤ K) :
    (∫ w in Set.Icc (-W) W, ‖ladderProductDefect P A₀ B₀ Q η L w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ))
          * (K * ∑ x ∈ ladderIndex P Q η L, ((ladderGapSetAt A₀ B₀ Q η x).card : ℝ)) := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hpos : ∀ x ∈ ladderIndex P Q η L, 0 < x.2 := by
    intro x hx
    rw [ladderIndex, Finset.mem_sigma] at hx
    exact (hPprime x.2 (geomBlock_subset P Q (1 + η) x.1 hx.2)).pos
  have hDpos : ∀ x ∈ ladderIndex P Q η L, ∀ m ∈ ladderGapSetAt A₀ B₀ Q η x, 0 < m := by
    intro x _ m hm
    exact ladderGapSetAt_pos hA hQ0 hη x.1 ((Finset.mem_sdiff.1 hm).1)
  exact integral_Icc_normSq_primeShift_family_le (ladderIndex P Q η L) (fun x => x.2)
    (ladderGapSetAt A₀ B₀ Q η) moebiusCoeff hpos hDpos norm_moebiusCoeff_le_one hK0 hDN hK hW

/-- **The mean square of the defect, in closed form.**  The overlap count is the designated divisor
count, and the gap budget is the ladder budget of `Sieve/TwoSidedCofactorBlock`. -/
theorem integral_normSq_ladderProductDefect_le_closed {P : Finset ℕ} {A₀ B₀ : ℕ} (hA : 0 < A₀)
    {Q η W : ℝ} (hQ : 1 < Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {L : ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) (hPge : ∀ p ∈ P, Q ≤ (p : ℝ)) :
    (∫ w in Set.Icc (-W) W, ‖ladderProductDefect P A₀ B₀ Q η L w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ))
          * (Real.log ((⌊(B₀ : ℝ) * (1 + η)⌋₊ : ℕ) : ℝ) / Real.log Q
            * ∑ j ∈ Finset.range L, (Q * (1 + η) ^ j * η + 1)
                * (((A₀ : ℝ) + (B₀ : ℝ)) * η / (Q * (1 + η) ^ j) + 5
                  + (B₀ : ℝ) / (Q * (1 + η) ^ j) ^ 2)) := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_trans zero_lt_one hQ
  have hlogQ : 0 < Real.log Q := Real.log_pos hQ
  set N : ℕ := ⌊(B₀ : ℝ) * (1 + η)⌋₊ with hN
  have hK0 : (0 : ℝ) ≤ Real.log ((N : ℕ) : ℝ) / Real.log Q :=
    div_nonneg (Real.log_natCast_nonneg N) hlogQ.le
  have hDN : ∀ x ∈ ladderIndex P Q η L,
      (ladderGapSetAt A₀ B₀ Q η x).image (fun m => x.2 * m) ⊆ Finset.Icc 1 N := by
    intro x hx n hn
    have hbase := ladderGapSetAt_image_subset A₀ B₀ hQ.le hη L x hx hn
    rw [Finset.mem_Icc] at hbase ⊢
    refine ⟨?_, hbase.2⟩
    rw [Finset.mem_image] at hn
    obtain ⟨m, hm, rfl⟩ := hn
    have hp := hPprime x.2 (by
      rw [ladderIndex, Finset.mem_sigma] at hx
      exact geomBlock_subset P Q (1 + η) x.1 hx.2)
    have hm0 : 0 < m := ladderGapSetAt_pos hA hQ0 hη x.1 ((Finset.mem_sdiff.1 hm).1)
    have : 0 < x.2 * m := Nat.mul_pos hp.pos hm0
    omega
  have hKmem : ∀ n ∈ Finset.Icc 1 N, (((ladderIndex P Q η L).filter
      (fun x => n ∈ (ladderGapSetAt A₀ B₀ Q η x).image (fun m => x.2 * m))).card : ℝ)
      ≤ Real.log ((N : ℕ) : ℝ) / Real.log Q := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    refine (ladderIndex_filter_card_le_gen hQ0 hη L (ladderGapSetAt A₀ B₀ Q η) n).trans ?_
    exact card_designatedPrimes_dvd_le hQ hPprime hPge hn.1 hn.2
  have hmain := integral_normSq_ladderProductDefect_le hA hQ.le hη hW hK0 hPprime hDN hKmem
  refine hmain.trans ?_
  have hcoef : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((N : ℕ) : ℝ) := by
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W := mul_nonneg (by positivity) hW0.le
    have h2 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * ((N : ℕ) : ℝ) :=
      mul_nonneg (by positivity) (Nat.cast_nonneg N)
    linarith
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hK0) hcoef
  exact sum_card_ladderGapSetAt_le A₀ B₀ hQ0 hη L hPprime

end

end RHTower.Sieve
