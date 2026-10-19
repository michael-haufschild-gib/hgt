import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusQuadraticQuotientProfile
import GaloisForLFunctions.RHTower.Sieve.SmoothRough
import GaloisForLFunctions.RHTower.Sieve.AveragedSquarefreeTailSharp
import Mathlib.NumberTheory.Primorial

/-!
# Finite-prime models for complementary Möbius magnitudes

On each integer horizon band, the literal source magnitude is a fixed finite
complementary-quotient sum. Truncating its Möbius factors to gcds with the
squared primorial produces a periodic sequence. The discarded rough factor
is common to every quotient, so the magnitude changes only at integers
containing a large prime square. Anchored multiple counts give a uniform
bound for disagreements across any finite list of shifts.
-/

open Finset ArithmeticFunction
open RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius Classical

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- The fixed complementary-quotient magnitude on one horizon band. -/
def moebiusBandMagnitude (j n : ℕ) : ℝ :=
  |∑ q ∈ Icc 1 j, if q ∣ n then moebiusReal (n / q) else 0|

/-- The finite prime-square approximation of a complementary-quotient magnitude. -/
def moebiusLocalBandMagnitude (j R n : ℕ) : ℝ :=
  |∑ q ∈ Icc 1 j, if q ∣ n then
    moebiusReal (Nat.gcd (n / q) (primorial R ^ 2)) else 0|

/-- A common period of every local quotient in the band. -/
def moebiusLocalBandPeriod (j R : ℕ) : ℕ := Nat.factorial j * primorial R ^ 2

private theorem smooth_prime_le {R n : ℕ} (hn : n ≠ 0) {p : ℕ}
    (hp : p.Prime) (hd : p ∣ smoothPart R n) : p ≤ R := by
  have hm := Nat.mem_primeFactors.mpr ⟨hp, hd, (smoothPart_pos R n).ne'⟩
  rw [primeFactors_smoothPart hn R] at hm
  exact (mem_filter.mp hm).2

private theorem bounded_support_coprime_rough {R n u : ℕ} (hn : n ≠ 0)
    (hu : ∀ p : ℕ, p.Prime → p ∣ u → p ≤ R) : Nat.Coprime u (roughPart R n) := by
  apply Nat.coprime_of_dvd
  intro p hp hpu
  exact not_dvd_roughPart hn (Nat.mem_primesLE.mpr ⟨hu p hp hpu, hp⟩)

private theorem moebius_gcd_prime_square {R u : ℕ}
    (hu : ∀ p : ℕ, p.Prime → p ∣ u → p ≤ R) :
    μ (Nat.gcd u (primorial R ^ 2)) = μ u := by
  by_cases hs : Squarefree u
  · have huP : u ∣ primorial R := by
      rw [← Nat.prod_primeFactors_of_squarefree hs]
      apply (Nat.prod_primeFactors_dvd_iff (primorial_pos R).ne').mpr
      intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      exact Nat.mem_primeFactors.mpr ⟨hpp,
        hpp.dvd_primorial_iff.mpr (hu p hpp (Nat.dvd_of_mem_primeFactors hp)),
        (primorial_pos R).ne'⟩
    rw [Nat.gcd_eq_left (huP.trans (dvd_pow_self (primorial R) (by decide : 2 ≠ 0)))]
  · have hg : ¬ Squarefree (Nat.gcd u (primorial R ^ 2)) := by
      intro hg
      apply hs
      apply Nat.squarefree_iff_prime_squarefree.mpr
      intro p hp hpp
      have hpP := hp.dvd_primorial_iff.mpr (hu p hp ((dvd_mul_right p p).trans hpp))
      apply (Nat.squarefree_iff_prime_squarefree.mp hg) p hp
      exact Nat.dvd_gcd hpp (by simpa only [pow_two] using mul_dvd_mul hpP hpP)
    rw [moebius_eq_zero_of_not_squarefree hs, moebius_eq_zero_of_not_squarefree hg]

private theorem gcd_mul_rough {R n : ℕ} (hn : n ≠ 0) (u : ℕ) :
    Nat.gcd (u * roughPart R n) (primorial R ^ 2) =
      Nat.gcd u (primorial R ^ 2) := by
  have hc : Nat.Coprime (primorial R ^ 2) (roughPart R n) := by
    apply Nat.coprime_of_dvd
    intro p hp hpd
    exact not_dvd_roughPart hn (Nat.mem_primesLE.mpr
      ⟨hp.dvd_primorial_iff.mp (hp.dvd_of_dvd_pow hpd), hp⟩)
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact (hc.coprime_dvd_left (Nat.gcd_dvd_right _ _)).dvd_of_dvd_mul_right
        (Nat.gcd_dvd_left _ _)
    · exact Nat.gcd_dvd_right _ _
  · exact Nat.dvd_gcd (dvd_mul_of_dvd_left (Nat.gcd_dvd_left _ _) _)
      (Nat.gcd_dvd_right _ _)

private theorem quotient_local_factor {R n q : ℕ} (hn : n ≠ 0)
    (hq : 1 ≤ q) (hqR : q ≤ R) :
    (if q ∣ n then moebiusReal (n / q) else 0) =
      moebiusReal (roughPart R n) *
        (if q ∣ n then moebiusReal (Nat.gcd (n / q) (primorial R ^ 2)) else 0) := by
  by_cases hd : q ∣ n
  · simp only [hd, if_true]
    have hqv := bounded_support_coprime_rough (u := q) hn
      (fun p _ hp => (Nat.le_of_dvd hq hp).trans hqR)
    have hqu : q ∣ smoothPart R n := by
      apply hqv.dvd_of_dvd_mul_right
      rwa [smoothPart_mul_roughPart hn R]
    have hdiv : n / q = (smoothPart R n / q) * roughPart R n := by
      calc
        n / q = (smoothPart R n * roughPart R n) / q :=
          congrArg (fun x => x / q) (smoothPart_mul_roughPart hn R).symm
        _ = _ := by simpa only [mul_comm] using Nat.mul_div_assoc (roughPart R n) hqu
    have hu : ∀ p : ℕ, p.Prime → p ∣ smoothPart R n / q → p ≤ R := by
      intro p hp hpd
      exact smooth_prime_le hn hp (hpd.trans (Nat.div_dvd_of_dvd hqu))
    have hcop := bounded_support_coprime_rough hn hu
    rw [hdiv, gcd_mul_rough hn]
    unfold moebiusReal
    rw [isMultiplicative_moebius.map_mul_of_coprime hcop, moebius_gcd_prime_square hu]
    push_cast
    ring
  · simp [hd]

/-- A common rough Möbius factor contains every nonlocal magnitude obstruction. -/
theorem moebiusBandMagnitude_eq_rough_mul_local (R : ℕ) (j : Fin (R + 1)) (n : ℕ+) :
    moebiusBandMagnitude j n = |moebiusReal (roughPart R n)| *
      moebiusLocalBandMagnitude j R n := by
  unfold moebiusBandMagnitude moebiusLocalBandMagnitude
  have heq : (∑ q ∈ Icc 1 (j : ℕ), if q ∣ (n : ℕ) then moebiusReal (n / q) else 0) =
      ∑ q ∈ Icc 1 (j : ℕ), moebiusReal (roughPart R n) *
        (if q ∣ (n : ℕ) then moebiusReal (Nat.gcd (n / q) (primorial R ^ 2)) else 0) := by
    apply Finset.sum_congr rfl
    intro q hq
    exact quotient_local_factor n.ne_zero (mem_Icc.mp hq).1
      ((mem_Icc.mp hq).2.trans (Nat.le_of_lt_succ j.isLt))
  rw [heq, ← Finset.mul_sum, abs_mul]

private theorem magnitude_agrees {R j n : ℕ} (hj : j ≤ R) (hn : n ≠ 0)
    (hsq : ∀ p : ℕ, p.Prime → R < p → ¬ p ^ 2 ∣ n) :
    moebiusBandMagnitude j n = moebiusLocalBandMagnitude j R n := by
  have hv : Squarefree (roughPart R n) := by
    apply Nat.squarefree_iff_prime_squarefree.mpr
    intro p hp hpd
    have hpv : p ∈ (roughPart R n).primeFactors := Nat.mem_primeFactors.mpr
      ⟨hp, (dvd_mul_right p p).trans hpd, (roughPart_pos R n).ne'⟩
    rw [primeFactors_roughPart hn R] at hpv
    apply hsq p hp (Nat.lt_of_not_ge (mem_filter.mp hpv).2)
    simpa only [pow_two] using hpd.trans (roughPart_dvd R n)
  have ha : |moebiusReal (roughPart R n)| = 1 := by
    unfold moebiusReal
    exact_mod_cast (abs_moebius_eq_one_of_squarefree hv)
  have heq := moebiusBandMagnitude_eq_rough_mul_local R
    ⟨j, Nat.lt_succ_of_le hj⟩ ⟨n, Nat.pos_of_ne_zero hn⟩
  change moebiusBandMagnitude j n =
    |moebiusReal (roughPart R n)| * moebiusLocalBandMagnitude j R n at heq
  simpa only [ha, one_mul] using heq


/-- Every finite prime-square approximation has an explicit positive period. -/
theorem moebiusLocalBandMagnitude_periodic (j R : ℕ) :
    Function.Periodic (moebiusLocalBandMagnitude j R) (moebiusLocalBandPeriod j R) := by
  intro n
  unfold moebiusLocalBandMagnitude moebiusLocalBandPeriod
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hqF : q ∣ Nat.factorial j := Nat.dvd_factorial (mem_Icc.mp hq).1 (mem_Icc.mp hq).2
  have hqT : q ∣ Nat.factorial j * primorial R ^ 2 := dvd_mul_of_dvd_left hqF _
  have hiff : q ∣ n + Nat.factorial j * primorial R ^ 2 ↔ q ∣ n := by
    simpa only [Nat.add_comm] using (Nat.dvd_add_iff_right hqT).symm
  simp only [hiff]
  by_cases hqn : q ∣ n
  · simp only [hqn, if_true]
    have htq : Nat.factorial j * primorial R ^ 2 / q =
        (Nat.factorial j / q) * primorial R ^ 2 := by
      rw [mul_comm (Nat.factorial j), Nat.mul_div_assoc _ hqF, mul_comm]
    have hdiv : (n + Nat.factorial j * primorial R ^ 2) / q =
        n / q + (Nat.factorial j / q) * primorial R ^ 2 := by
      rw [Nat.add_comm n, Nat.add_div_of_dvd_right hqT, htq, add_comm]
    rw [hdiv, Nat.gcd_add_mul_right_left]
  · simp only [hqn, if_false]

/-- Complementary quotients recover every literal source magnitude at its exact band. -/
theorem abs_sieveSeq_moebius_eq_bandMagnitude (N n : ℕ+) :
    |sieveSeq N moebiusReal n| =
      if (n : ℕ) = 1 then 1 else moebiusBandMagnitude (((n : ℕ) - 1) / N) n := by
  by_cases hn : (n : ℕ) = 1
  · rw [if_pos hn, hn]
    have h := sieveSeq_moebiusReal_eq_quotient_band_sum (N := (N : ℕ)) (B := 0)
      (k := 1) (by omega) (by
        have hN := N.pos
        simpa only [zero_add, one_mul] using (show 1 ≤ (N : ℕ) by omega))
    simpa using congrArg abs h
  · rw [if_neg hn]
    let j := ((n : ℕ) - 1) / N
    have hrem := Nat.div_add_mod ((n : ℕ) - 1) N
    have hmod := Nat.mod_lt ((n : ℕ) - 1) N.pos
    have hnsub := Nat.sub_add_cancel n.pos
    have hlo : j * (N : ℕ) < n :=
      (Nat.div_mul_le_self ((n : ℕ) - 1) N).trans_lt (Nat.sub_lt n.pos (by decide))
    have hhi : (n : ℕ) ≤ (j + 1) * N := by dsimp [j]; nlinarith
    rw [sieveSeq_moebiusReal_eq_quotient_band_sum n.pos hhi, if_neg hn, zero_sub, abs_neg]
    unfold moebiusBandMagnitude
    congr 1
    apply Finset.sum_congr rfl
    intro q hq
    have hqlo : q * (N : ℕ) < n :=
      (Nat.mul_le_mul_right (N : ℕ) (mem_Icc.mp hq).2).trans_lt hlo
    simp only [moebiusQuotientBandTerm, hqlo, and_true]

private theorem shifted_large_square_count_le (R : ℕ+) (X h : ℕ) :
    (((Icc 1 X).filter (fun n => ∃ d : ℕ, (R : ℕ) < d ∧ d ^ 2 ∣ n + h)).card : ℝ) ≤
      ((X + h : ℕ) : ℝ) / R := by
  classical
  let S := Icc ((R : ℕ) + 1) (X + h)
  let F := fun d => (Icc 1 X).filter (fun n => d ^ 2 ∣ n + h)
  have hcover : (Icc 1 X).filter (fun n => ∃ d : ℕ, (R : ℕ) < d ∧ d ^ 2 ∣ n + h) ⊆
      S.biUnion F := by
    intro n hn
    obtain ⟨hn, d, hd, hdn⟩ := mem_filter.mp hn
    have hdhi : d ≤ X + h :=
      (Nat.le_of_dvd (by have := (mem_Icc.mp hn).1; omega : 0 < n + h)
        ((dvd_pow_self d (by decide : 2 ≠ 0)).trans hdn)).trans
          (Nat.add_le_add_right (mem_Icc.mp hn).2 h)
    exact mem_biUnion.mpr ⟨d, mem_Icc.mpr ⟨by omega, hdhi⟩, mem_filter.mpr ⟨hn, hdn⟩⟩
  have hc : (((Icc 1 X).filter
      (fun n => ∃ d : ℕ, (R : ℕ) < d ∧ d ^ 2 ∣ n + h)).card : ℝ) ≤
      ∑ d ∈ S, ((F d).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hdcount (d : ℕ) : ((F d).card : ℝ) ≤ ((X + h : ℕ) : ℝ) / (d : ℝ) ^ 2 := by
    have hcNat : (F d).card ≤ ((Ioc 0 (X + h)).filter (fun n => d ^ 2 ∣ n)).card := by
      apply Finset.card_le_card_of_injOn (fun n : ℕ => n + h)
      · intro n hn
        change n + h ∈ (Ioc 0 (X + h)).filter (fun n => d ^ 2 ∣ n)
        obtain ⟨hn, hd⟩ := mem_filter.mp hn
        exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨by have := (mem_Icc.mp hn).1; omega,
          by have := (mem_Icc.mp hn).2; omega⟩, hd⟩
      · intro n _ m _ heq
        change n + h = m + h at heq
        omega
    have hcReal : ((F d).card : ℝ) ≤
        (((Ioc 0 (X + h)).filter (fun n => d ^ 2 ∣ n)).card : ℝ) := by exact_mod_cast hcNat
    have ht := card_filter_dvd_Ioc_zero_le (d ^ 2) (X + h)
    push_cast at ht
    exact hcReal.trans (by simpa only [Nat.cast_add] using ht)
  calc
    _ ≤ ∑ d ∈ S, ((F d).card : ℝ) := hc
    _ ≤ ∑ d ∈ S, ((X + h : ℕ) : ℝ) / (d : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun d _ => hdcount d)
    _ = ((X + h : ℕ) : ℝ) * ∑ d ∈ S, (1 : ℝ) / (d : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ ((X + h : ℕ) : ℝ) * (1 / (R : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Icc_inv_sq_le R.pos (X + h)) (by positivity)
    _ = _ := by ring

/-- Joint magnitude errors are confined to a quantitatively controlled union of shifted squares. -/
theorem moebiusBandMagnitude_disagreement_count_le (R : ℕ+) (j : Fin ((R : ℕ) + 1))
    (m X : ℕ) (h : Fin m → ℕ) :
    (((Icc 1 X).filter (fun n => ∃ i : Fin m,
      moebiusBandMagnitude j (n + h i) ≠ moebiusLocalBandMagnitude j R (n + h i))).card : ℝ) ≤
        ∑ i : Fin m, ((X + h i : ℕ) : ℝ) / R := by
  classical
  let F := fun i : Fin m => (Icc 1 X).filter
    (fun n => ∃ d : ℕ, (R : ℕ) < d ∧ d ^ 2 ∣ n + h i)
  have hcover : (Icc 1 X).filter (fun n => ∃ i : Fin m,
      moebiusBandMagnitude j (n + h i) ≠ moebiusLocalBandMagnitude j R (n + h i)) ⊆
        Finset.univ.biUnion F := by
    intro n hn
    obtain ⟨hn, i, hne⟩ := mem_filter.mp hn
    apply mem_biUnion.mpr
    refine ⟨i, mem_univ _, mem_filter.mpr ⟨hn, ?_⟩⟩
    by_contra hnone
    apply hne
    apply magnitude_agrees (Nat.le_of_lt_succ j.isLt)
      (by have := (mem_Icc.mp hn).1; omega)
    intro p _ hp hd
    exact hnone ⟨p, hp, hd⟩
  have hc : (((Icc 1 X).filter (fun n => ∃ i : Fin m,
      moebiusBandMagnitude j (n + h i) ≠ moebiusLocalBandMagnitude j R (n + h i))).card : ℝ) ≤
        ∑ i : Fin m, ((F i).card : ℝ) := by
    exact_mod_cast (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  exact hc.trans (Finset.sum_le_sum (fun i _ => shifted_large_square_count_le R X (h i)))


end
end GaloisForLFunctions.BezoutValuationIncidence
