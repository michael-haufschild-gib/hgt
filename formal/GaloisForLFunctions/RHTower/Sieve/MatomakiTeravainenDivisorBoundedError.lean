import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma23IPaperScale
import GaloisForLFunctions.RHTower.Sieve.DivisorSubmultiplicative

/-!
# Lemma 2.3(i) errors for divisor-bounded coefficients

The iterated Buchstab coefficient is bounded by one ordinary divisor function.  This file keeps
that extra factor literal.  Squaring the error costs the fixed fifth divisor moment, independent
of iteration depth.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Local first-power divisor envelope used by the repaired iteration. -/
def MTDivisorBounded (α : ℕ → ℂ) (B : ℝ) : Prop :=
  ∀ {m : ℕ}, 0 < m → ‖α m‖ ≤ B * (m.divisors.card : ℝ)

/-- The truncation error under one divisor-function coefficient envelope. -/
theorem norm_mtC1Coefficient_le_divisorBounded
    (α : ℕ → ℂ) {z D n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTDivisorBounded α B) :
    ‖mtC1Coefficient α z D n‖ ≤
      B * (n.divisors.card : ℝ) ^ 2 * siftTailDivisorCount z D n := by
  unfold mtC1Coefficient
  calc
    ‖∑ m ∈ n.divisors,
        α m * ((rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ))‖ ≤
      ∑ m ∈ n.divisors,
        ‖α m * ((rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _m ∈ n.divisors,
        (B * (n.divisors.card : ℝ)) * siftTailDivisorCount z D n := by
      apply Finset.sum_le_sum
      intro m hm
      have hmDvd : m ∣ n := (Nat.mem_divisors.mp hm).1
      have hmPos := Nat.pos_of_mem_divisors hm
      have hk : 0 < n / m := Nat.div_pos (Nat.le_of_dvd hn hmDvd) hmPos
      have hkDiv : n / m ∣ n := ⟨m, (Nat.div_mul_cancel hmDvd).symm⟩
      have hmCard : (m.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast card_divisors_mono_of_dvd hmDvd hn.ne'
      have hnorm :
          ‖(rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ)‖ ≤
            (truncTail (n / m) z D : ℝ) := by
        rw [← Int.cast_natCast, ← Int.cast_sub, Complex.norm_intCast]
        exact_mod_cast abs_rho_sub_truncLegendre_le (k := n / m) (z := z) (D := D) hk
      rw [norm_mul]
      exact mul_le_mul
        ((hα hmPos).trans (mul_le_mul_of_nonneg_left hmCard hB))
        (hnorm.trans (truncTail_le_siftTailDivisorCount hkDiv))
        (norm_nonneg _) (mul_nonneg hB (Nat.cast_nonneg _))
    _ = B * (n.divisors.card : ℝ) ^ 2 * siftTailDivisorCount z D n := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- The endpoint error under one divisor-function coefficient envelope. -/
theorem norm_mtC2Coefficient_le_divisorBounded
    (α : ℕ → ℂ) (lowerSpill upperSpill : Finset ℕ) (level : ℕ → ℕ)
    {n : ℕ} (hn : 0 < n) {B : ℝ} (hB : 0 ≤ B) (hα : MTDivisorBounded α B) :
    ‖mtC2Coefficient α lowerSpill upperSpill level n‖ ≤
      B * (n.divisors.card : ℝ) ^ 2 *
        (primeDivisorCount lowerSpill n + primeDivisorCount upperSpill n) := by
  have boundary : ∀ S : Finset ℕ,
      ‖mtC2BoundaryCoefficient α S level n‖ ≤
        B * (n.divisors.card : ℝ) ^ 2 * primeDivisorCount S n := by
    intro S
    unfold mtC2BoundaryCoefficient primeDivisorCount
    calc
      ‖∑ q ∈ S, if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            α m * (rho ((n / q) / m) (level q) : ℂ) else 0‖ ≤
        ∑ q ∈ S, ‖if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            α m * (rho ((n / q) / m) (level q) : ℂ) else 0‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ S,
          if q ∣ n then B * (n.divisors.card : ℝ) ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro q hq
        split_ifs with hqn
        · have hNdiv : n / q ∣ n := ⟨q, (Nat.div_mul_cancel hqn).symm⟩
          have hNpos : 0 < n / q := Nat.div_pos (Nat.le_of_dvd hn hqn)
            (Nat.pos_of_dvd_of_pos hqn hn)
          have hcardN : ((n / q).divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
            exact_mod_cast card_divisors_mono_of_dvd hNdiv hn.ne'
          calc
            ‖∑ m ∈ (n / q).divisors,
                α m * (rho ((n / q) / m) (level q) : ℂ)‖ ≤
              ∑ m ∈ (n / q).divisors,
                ‖α m * (rho ((n / q) / m) (level q) : ℂ)‖ := norm_sum_le _ _
            _ ≤ ∑ _m ∈ (n / q).divisors, B * (n.divisors.card : ℝ) := by
              apply Finset.sum_le_sum
              intro m hm
              have hmDvdN : m ∣ n / q := (Nat.mem_divisors.mp hm).1
              have hmDvd : m ∣ n := hmDvdN.trans hNdiv
              have hmCard : (m.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
                exact_mod_cast card_divisors_mono_of_dvd hmDvd hn.ne'
              rw [norm_mul]
              have hrho : ‖(rho ((n / q) / m) (level q) : ℂ)‖ ≤ 1 := by
                exact_mod_cast rho_le_one ((n / q) / m) (level q)
              exact (mul_le_mul (hα (Nat.pos_of_mem_divisors hm)) hrho
                (norm_nonneg _) (mul_nonneg hB (Nat.cast_nonneg _))).trans
                  (by simpa using mul_le_mul_of_nonneg_left hmCard hB)
            _ = B * (n.divisors.card : ℝ) * ((n / q).divisors.card : ℝ) := by
              simp [Finset.sum_const, nsmul_eq_mul]
              ring
            _ ≤ B * (n.divisors.card : ℝ) ^ 2 := by
              nlinarith [mul_le_mul_of_nonneg_left hcardN
                (mul_nonneg hB (Nat.cast_nonneg n.divisors.card))]
        · simp
      _ = B * (n.divisors.card : ℝ) ^ 2 *
          (∑ q ∈ S, if q ∣ n then 1 else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        split_ifs <;> ring
  unfold mtC2Coefficient
  calc
    ‖mtC2BoundaryCoefficient α upperSpill level n -
        mtC2BoundaryCoefficient α lowerSpill level n‖ ≤
      ‖mtC2BoundaryCoefficient α upperSpill level n‖ +
        ‖mtC2BoundaryCoefficient α lowerSpill level n‖ := norm_sub_le _ _
    _ ≤ B * (n.divisors.card : ℝ) ^ 2 * primeDivisorCount upperSpill n +
        B * (n.divisors.card : ℝ) ^ 2 * primeDivisorCount lowerSpill n :=
      add_le_add (boundary upperSpill) (boundary lowerSpill)
    _ = B * (n.divisors.card : ℝ) ^ 2 *
        (primeDivisorCount lowerSpill n + primeDivisorCount upperSpill n) := by ring

/-- The Buchstab replacement error under one divisor-function coefficient envelope. -/
theorem norm_mtC3Coefficient_le_divisorBounded
    (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (hS : ∀ q ∈ S, q.Prime) (hlower : ∀ q ∈ S, lower q ≤ q)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTDivisorBounded α B) :
    ‖mtC3Coefficient α S lower n‖ ≤
      B * (n.divisors.card : ℝ) ^ 2 *
        primePairDivisorCount S (fun q => primesIco (lower q) q) n := by
  rw [mtC3Coefficient_eq_expanded α S lower hn hS hlower]
  have hexp : ‖mtC3Expanded α S lower n‖ ≤
      (B * (n.divisors.card : ℝ)) * mtC3ExpansionCount S lower n := by
    unfold mtC3Expanded mtC3ExpansionCount
    calc
      ‖∑ q ∈ S, if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            α m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
              (rho (n / q / m / p) p : ℂ) else 0‖ ≤
        ∑ q ∈ S, ‖if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            α m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
              (rho (n / q / m / p) p : ℂ) else 0‖ := norm_sum_le _ _
      _ ≤ ∑ q ∈ S, if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            (B * (n.divisors.card : ℝ)) *
              ((primeWindow (n / q / m) (lower q) q).card : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro q hq
        split_ifs with hqn
        · have hNdiv : n / q ∣ n := ⟨q, (Nat.div_mul_cancel hqn).symm⟩
          apply (norm_sum_le _ _).trans
          apply Finset.sum_le_sum
          intro m hm
          have hmDvd : m ∣ n := (Nat.mem_divisors.mp hm).1.trans hNdiv
          have hmCard : (m.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
            exact_mod_cast card_divisors_mono_of_dvd hmDvd hn.ne'
          rw [norm_mul]
          have hinner :
              ‖∑ p ∈ primeWindow (n / q / m) (lower q) q,
                  (rho (n / q / m / p) p : ℂ)‖ ≤
                ((primeWindow (n / q / m) (lower q) q).card : ℝ) := by
            calc
              ‖∑ p ∈ primeWindow (n / q / m) (lower q) q,
                  (rho (n / q / m / p) p : ℂ)‖ ≤
                ∑ p ∈ primeWindow (n / q / m) (lower q) q,
                  ‖(rho (n / q / m / p) p : ℂ)‖ := norm_sum_le _ _
              _ ≤ ∑ _p ∈ primeWindow (n / q / m) (lower q) q, (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro p hp
                exact_mod_cast rho_le_one (n / q / m / p) p
              _ = ((primeWindow (n / q / m) (lower q) q).card : ℝ) := by simp
          exact mul_le_mul
            ((hα (Nat.pos_of_mem_divisors hm)).trans
              (mul_le_mul_of_nonneg_left hmCard hB)) hinner
            (norm_nonneg _) (mul_nonneg hB (Nat.cast_nonneg _))
        · simp
      _ = (B * (n.divisors.card : ℝ)) *
          ∑ q ∈ S, if q ∣ n then
            ∑ m ∈ (n / q).divisors,
              ((primeWindow (n / q / m) (lower q) q).card : ℝ) else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        split_ifs
        · rw [Finset.mul_sum]
        · simp
  calc
    ‖mtC3Expanded α S lower n‖ ≤
      (B * (n.divisors.card : ℝ)) * mtC3ExpansionCount S lower n := hexp
    _ ≤ (B * (n.divisors.card : ℝ)) *
        ((n.divisors.card : ℝ) *
          primePairDivisorCount S (fun q => primesIco (lower q) q) n) := by
      apply mul_le_mul_of_nonneg_left (mtC3ExpansionCount_le_pairDivisorCount S lower hn)
      positivity
    _ = B * (n.divisors.card : ℝ) ^ 2 *
        primePairDivisorCount S (fun q => primesIco (lower q) q) n := by ring

/-- Fifth-moment first bound for the truncation error. -/
theorem divisor_mul_ternary_mul_norm_mtC1Coefficient_le
    (α : ℕ → ℂ) {z D n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTDivisorBounded α B) :
    (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        ‖mtC1Coefficient α z D n‖ ≤
      B * weightedSiftTailDivisorCount 5 z D n := by
  have hd3 : (ternaryDivisorCount n : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast ternaryDivisorCount_le_sq hn
  have hc := norm_mtC1Coefficient_le_divisorBounded α (z := z) (D := D) hn hB hα
  unfold weightedSiftTailDivisorCount
  calc
    (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        ‖mtC1Coefficient α z D n‖ ≤
      (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) ^ 2) *
        (B * (n.divisors.card : ℝ) ^ 2 * siftTailDivisorCount z D n) := by
      gcongr
    _ = B * ((n.divisors.card : ℝ) ^ 5 * siftTailDivisorCount z D n) := by ring

/-- Fifth-moment first bound for the endpoint error. -/
theorem divisor_mul_ternary_mul_norm_mtC2Coefficient_le
    (α : ℕ → ℂ) (lowerSpill upperSpill : Finset ℕ) (level : ℕ → ℕ)
    {n : ℕ} (hn : 0 < n) {B : ℝ} (hB : 0 ≤ B) (hα : MTDivisorBounded α B) :
    (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        ‖mtC2Coefficient α lowerSpill upperSpill level n‖ ≤
      B * ((weightedPrimeDivisorCount 5 lowerSpill n) +
        weightedPrimeDivisorCount 5 upperSpill n) := by
  have hd3 : (ternaryDivisorCount n : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast ternaryDivisorCount_le_sq hn
  have hc := norm_mtC2Coefficient_le_divisorBounded
    α lowerSpill upperSpill level hn hB hα
  unfold weightedPrimeDivisorCount
  have hl : 0 ≤ primeDivisorCount lowerSpill n := by
    unfold primeDivisorCount
    positivity
  have hu : 0 ≤ primeDivisorCount upperSpill n := by
    unfold primeDivisorCount
    positivity
  calc
    (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        ‖mtC2Coefficient α lowerSpill upperSpill level n‖ ≤
      (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) ^ 2) *
        (B * (n.divisors.card : ℝ) ^ 2 *
          (primeDivisorCount lowerSpill n + primeDivisorCount upperSpill n)) := by
      gcongr
    _ = B * ((n.divisors.card : ℝ) ^ 5 * primeDivisorCount lowerSpill n +
        (n.divisors.card : ℝ) ^ 5 * primeDivisorCount upperSpill n) := by ring

/-- Fifth-moment first bound for the Buchstab replacement error. -/
theorem divisor_mul_ternary_mul_norm_mtC3Coefficient_le
    (α : ℕ → ℂ) (S : Finset ℕ) (lower : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (hS : ∀ q ∈ S, q.Prime) (hlower : ∀ q ∈ S, lower q ≤ q)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTDivisorBounded α B) :
    (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        ‖mtC3Coefficient α S lower n‖ ≤
      B * weightedPrimePairDivisorCount 5 S (fun q => primesIco (lower q) q) n := by
  have hd3 : (ternaryDivisorCount n : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast ternaryDivisorCount_le_sq hn
  have hc := norm_mtC3Coefficient_le_divisorBounded α S lower hn hS hlower hB hα
  unfold weightedPrimePairDivisorCount
  have hp : 0 ≤ primePairDivisorCount S (fun q => primesIco (lower q) q) n := by
    unfold primePairDivisorCount
    positivity
  calc
    (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        ‖mtC3Coefficient α S lower n‖ ≤
      (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) ^ 2) *
        (B * (n.divisors.card : ℝ) ^ 2 *
          primePairDivisorCount S (fun q => primesIco (lower q) q) n) := by
      gcongr
    _ = B * ((n.divisors.card : ℝ) ^ 5 *
        primePairDivisorCount S (fun q => primesIco (lower q) q) n) := by ring

/-- Divisor-bounded combined error has one extra divisor factor in its pointwise envelope. -/
theorem norm_mtLemma23Error_le_five_mul_divisor_mul_ternary
    (α : ℕ → ℂ) (z D : ℕ) (lowerSpill upperSpill P : Finset ℕ)
    (lower : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTDivisorBounded α B) :
    ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ ≤
      5 * B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) := by
  have hlocal : ∀ {m : ℕ}, m ∣ n → ‖α m‖ ≤ B * (n.divisors.card : ℝ) := by
    intro m hmn
    have hm : 0 < m := Nat.pos_of_dvd_of_pos hmn hn
    have hcard : (m.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast card_divisors_mono_of_dvd hmn hn.ne'
    exact (hα hm).trans (mul_le_mul_of_nonneg_left hcard hB)
  unfold mtLemma23Error
  have hc1 : ‖mtC1Coefficient α z D n‖ ≤
      (B * (n.divisors.card : ℝ)) * (ternaryDivisorCount n : ℝ) := by
    unfold mtC1Coefficient ternaryDivisorCount
    apply (norm_sum_le _ _).trans
    calc
      ∑ m ∈ n.divisors,
          ‖α m * ((rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ))‖ ≤
        ∑ m ∈ n.divisors,
          (B * (n.divisors.card : ℝ)) * ((n / m).divisors.card : ℝ) := by
        apply Finset.sum_le_sum
        intro m hm
        have hmDvd := (Nat.mem_divisors.mp hm).1
        have hk := Nat.div_pos (Nat.le_of_dvd hn hmDvd) (Nat.pos_of_mem_divisors hm)
        rw [norm_mul]
        have hnorm :
            ‖(rho (n / m) z : ℂ) - (truncLegendre (n / m) z D : ℂ)‖ ≤
              ((n / m).divisors.card : ℝ) := by
          rw [← Int.cast_natCast, ← Int.cast_sub, Complex.norm_intCast]
          have htailNat : truncTail (n / m) z D ≤ (n / m).divisors.card := by
            unfold truncTail
            exact (Finset.card_filter_le _ _).trans
              (card_divisors_mono_of_dvd (Nat.gcd_dvd_left _ _) hk.ne')
          have htailInt : (truncTail (n / m) z D : ℤ) ≤
              ((n / m).divisors.card : ℤ) := by exact_mod_cast htailNat
          have htotal := (abs_rho_sub_truncLegendre_le hk).trans htailInt
          exact_mod_cast htotal
        exact mul_le_mul (hlocal hmDvd) hnorm (norm_nonneg _) (by positivity)
      _ = (B * (n.divisors.card : ℝ)) *
          ∑ m ∈ n.divisors, ((n / m).divisors.card : ℝ) := by rw [Finset.mul_sum]
    push_cast
    exact le_rfl
  have boundary : ∀ (level : ℕ → ℕ) (S : Finset ℕ),
      ‖mtC2BoundaryCoefficient α S level n‖ ≤
      (B * (n.divisors.card : ℝ)) * (ternaryDivisorCount n : ℝ) := by
    intro level S
    unfold mtC2BoundaryCoefficient ternaryDivisorCount
    apply (norm_sum_le _ _).trans
    calc
      ∑ q ∈ S, ‖if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            α m * (rho ((n / q) / m) (level q) : ℂ) else 0‖ ≤
        ∑ q ∈ S, if q ∣ n then
          (B * (n.divisors.card : ℝ)) * ((n / q).divisors.card : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro q hq
        split_ifs with hqn
        · have hNdiv : n / q ∣ n := ⟨q, (Nat.div_mul_cancel hqn).symm⟩
          apply (norm_sum_le _ _).trans
          calc
            ∑ m ∈ (n / q).divisors,
                ‖α m * (rho ((n / q) / m) (level q) : ℂ)‖ ≤
              ∑ _m ∈ (n / q).divisors, B * (n.divisors.card : ℝ) := by
              apply Finset.sum_le_sum
              intro m hm
              rw [norm_mul]
              have hrho : ‖(rho ((n / q) / m) (level q) : ℂ)‖ ≤ 1 := by
                exact_mod_cast rho_le_one ((n / q) / m) (level q)
              simpa using mul_le_mul
                (hlocal ((Nat.mem_divisors.mp hm).1.trans hNdiv)) hrho
                (norm_nonneg _) (mul_nonneg hB (Nat.cast_nonneg _))
            _ = (B * (n.divisors.card : ℝ)) * ((n / q).divisors.card : ℝ) := by
              simp [Finset.sum_const, nsmul_eq_mul]
              ring
        · simp
      _ = ∑ q ∈ n.divisors,
          if q ∈ S then (B * (n.divisors.card : ℝ)) *
            ((n / q).divisors.card : ℝ) else 0 := by
        rw [sum_divisors_indicator_eq_sum_finset_dvd hn]
      _ ≤ ∑ q ∈ n.divisors,
          (B * (n.divisors.card : ℝ)) * ((n / q).divisors.card : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        split_ifs
        · exact le_rfl
        · positivity
      _ = (B * (n.divisors.card : ℝ)) *
          ∑ q ∈ n.divisors, ((n / q).divisors.card : ℝ) := by rw [Finset.mul_sum]
    push_cast
    exact le_rfl
  have hc2 : ‖mtC2Coefficient α lowerSpill upperSpill lower n‖ ≤
      2 * (B * (n.divisors.card : ℝ)) * (ternaryDivisorCount n : ℝ) := by
    unfold mtC2Coefficient
    calc
      ‖mtC2BoundaryCoefficient α upperSpill lower n -
          mtC2BoundaryCoefficient α lowerSpill lower n‖ ≤
        ‖mtC2BoundaryCoefficient α upperSpill lower n‖ +
          ‖mtC2BoundaryCoefficient α lowerSpill lower n‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add (boundary lower upperSpill) (boundary lower lowerSpill)
      _ = _ := by ring
  have hc3 : ‖mtC3Coefficient α P lower n‖ ≤
      2 * (B * (n.divisors.card : ℝ)) * (ternaryDivisorCount n : ℝ) := by
    rw [mtC3Coefficient_eq_boundary_sub]
    calc
      ‖mtC2BoundaryCoefficient α P lower n - mtC2BoundaryCoefficient α P id n‖ ≤
        ‖mtC2BoundaryCoefficient α P lower n‖ +
          ‖mtC2BoundaryCoefficient α P id n‖ := norm_sub_le _ _
      _ ≤ (B * (n.divisors.card : ℝ)) * (ternaryDivisorCount n : ℝ) +
          (B * (n.divisors.card : ℝ)) * (ternaryDivisorCount n : ℝ) := by
        exact add_le_add (boundary lower P) (boundary id P)
      _ = _ := by ring
  calc
    ‖mtC1Coefficient α z D n + mtC2Coefficient α lowerSpill upperSpill lower n +
        mtC3Coefficient α P lower n‖ ≤
      ‖mtC1Coefficient α z D n‖ +
          ‖mtC2Coefficient α lowerSpill upperSpill lower n‖ +
        ‖mtC3Coefficient α P lower n‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith

/-- The combined divisor-weighted first moment reduces to the three fixed fifth moments. -/
theorem sum_divisor_mul_ternary_mul_norm_mtLemma23Error_le_weighted
    (α : ℕ → ℂ) (z D : ℕ) (lowerSpill upperSpill P : Finset ℕ)
    (lower : ℕ → ℕ) (Y : ℕ)
    (hP : ∀ q ∈ P, q.Prime) (hlower : ∀ q ∈ P, lower q ≤ q)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTDivisorBounded α B) :
    ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ ≤
      B * ∑ n ∈ Finset.Icc 1 Y,
        (weightedSiftTailDivisorCount 5 z D n +
          weightedPrimeDivisorCount 5 lowerSpill n +
          weightedPrimeDivisorCount 5 upperSpill n +
          weightedPrimePairDivisorCount 5 P (fun q => primesIco (lower q) q) n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnPos : 0 < n := by
    rw [Finset.mem_Icc] at hn
    omega
  have hc1 := divisor_mul_ternary_mul_norm_mtC1Coefficient_le
    α (z := z) (D := D) hnPos hB hα
  have hc2 := divisor_mul_ternary_mul_norm_mtC2Coefficient_le
    α lowerSpill upperSpill lower hnPos hB hα
  have hc3 := divisor_mul_ternary_mul_norm_mtC3Coefficient_le
    α P lower hnPos hP hlower hB hα
  unfold mtLemma23Error
  have hnorm := (norm_add_le
    (mtC1Coefficient α z D n + mtC2Coefficient α lowerSpill upperSpill lower n)
    (mtC3Coefficient α P lower n)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  calc
    (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        ‖mtC1Coefficient α z D n + mtC2Coefficient α lowerSpill upperSpill lower n +
          mtC3Coefficient α P lower n‖ ≤
      (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        (‖mtC1Coefficient α z D n‖ +
          ‖mtC2Coefficient α lowerSpill upperSpill lower n‖ +
          ‖mtC3Coefficient α P lower n‖) := by
      gcongr
    _ ≤ B * weightedSiftTailDivisorCount 5 z D n +
        B * (weightedPrimeDivisorCount 5 lowerSpill n +
          weightedPrimeDivisorCount 5 upperSpill n) +
        B * weightedPrimePairDivisorCount 5 P (fun q => primesIco (lower q) q) n := by
      calc
        _ = (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
              ‖mtC1Coefficient α z D n‖ +
            (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
              ‖mtC2Coefficient α lowerSpill upperSpill lower n‖ +
            (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
              ‖mtC3Coefficient α P lower n‖ := by ring
        _ ≤ _ := add_le_add (add_le_add hc1 hc2) hc3
    _ = B * (weightedSiftTailDivisorCount 5 z D n +
        weightedPrimeDivisorCount 5 lowerSpill n +
        weightedPrimeDivisorCount 5 upperSpill n +
        weightedPrimePairDivisorCount 5 P (fun q => primesIco (lower q) q) n) := by ring

/-- The fixed fifth moment converts divisor-bounded error squares to a weighted first moment. -/
theorem sum_norm_sq_mtLemma23Error_le_five_mul_divisor_weighted
    (α : ℕ → ℂ) (z D : ℕ) (lowerSpill upperSpill P : Finset ℕ)
    (lower : ℕ → ℕ) (Y : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hα : MTDivisorBounded α B) :
    ∑ n ∈ Finset.Icc 1 Y,
        ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ ^ 2 ≤
      5 * B * ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnPos : 0 < n := by
    rw [Finset.mem_Icc] at hn
    omega
  have hpoint := norm_mtLemma23Error_le_five_mul_divisor_mul_ternary
    α z D lowerSpill upperSpill P lower hnPos hB hα
  calc
    ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ ^ 2 =
      ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ *
        ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ := by ring
    _ ≤ (5 * B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ)) *
        ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖ :=
      mul_le_mul_of_nonneg_right hpoint (norm_nonneg _)
    _ = 5 * B * ((n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        ‖mtLemma23Error α z D lowerSpill upperSpill P lower n‖) := by ring

end

end RHTower.Sieve
