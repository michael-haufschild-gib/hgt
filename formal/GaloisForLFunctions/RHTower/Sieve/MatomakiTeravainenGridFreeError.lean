import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTerminalCoefficients
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenDivisorBoundedError

/-!
# Grid-free aggregation of Matomäki--Teräväinen error fibres

Terminal coefficient fibres are summed before analytic estimation.  Their joint `ℓ¹` envelope,
rather than the number of adic cutoffs, controls every common error kernel.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- A finite coefficient family has one joint divisor envelope. -/
def MTFiniteFamilyDivisorBounded {u : ℕ} (α : Fin u → ℕ → ℂ) (B : ℝ) : Prop :=
  ∀ {m : ℕ}, 0 < m → ∑ k : Fin u, ‖α k m‖ ≤ B * (m.divisors.card : ℝ)

/-- Summing a jointly divisor-bounded family preserves the same divisor envelope. -/
theorem MTFiniteFamilyDivisorBounded.sum {u : ℕ} {α : Fin u → ℕ → ℂ} {B : ℝ}
    (hα : MTFiniteFamilyDivisorBounded α B) :
    MTDivisorBounded (fun m => ∑ k : Fin u, α k m) B := by
  intro m hm
  exact (norm_sum_le _ _).trans (hα hm)

/-- The common truncation kernel is linear across terminal coefficient fibres. -/
theorem sum_mtC1Coefficient_eq {u : ℕ} (α : Fin u → ℕ → ℂ)
    (z D n : ℕ) :
    ∑ k : Fin u, mtC1Coefficient (α k) z D n =
      mtC1Coefficient (fun m => ∑ k : Fin u, α k m) z D n := by
  unfold mtC1Coefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_mul]

/-- Joint terminal aggregation removes the adic-grid factor from the truncation error. -/
theorem norm_sum_mtC1Coefficient_le_familyDivisorBounded
    {u : ℕ} (α : Fin u → ℕ → ℂ) {z D n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTFiniteFamilyDivisorBounded α B) :
    ‖∑ k : Fin u, mtC1Coefficient (α k) z D n‖ ≤
      B * (n.divisors.card : ℝ) ^ 2 * siftTailDivisorCount z D n := by
  rw [sum_mtC1Coefficient_eq]
  exact norm_mtC1Coefficient_le_divisorBounded
    (fun m => ∑ k : Fin u, α k m) hn hB hα.sum

/-- Extend a finite sum to a containing finset by an exact membership indicator. -/
theorem sum_subset_eq_sum_indicator {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    {S P : Finset ι} (hSP : S ⊆ P) (f : ι → M) :
    ∑ x ∈ S, f x = ∑ x ∈ P, if x ∈ S then f x else 0 := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter]
    constructor
    · exact fun hx => ⟨hSP hx, hx⟩
    · exact fun hx => hx.2
  · intro x hx
    rfl

/-- A family of varying endpoint kernels is controlled by one containing prime set and the joint
coefficient envelope. -/
theorem norm_sum_mtC2BoundaryCoefficient_le_familyDivisorBounded
    {u : ℕ} (α : Fin u → ℕ → ℂ) (S : Fin u → Finset ℕ)
    (level : Fin u → ℕ → ℕ) (P : Finset ℕ) {n : ℕ} (hn : 0 < n)
    (hSP : ∀ k, S k ⊆ P) {B : ℝ} (hB : 0 ≤ B)
    (hα : MTFiniteFamilyDivisorBounded α B) :
    ‖∑ k : Fin u, mtC2BoundaryCoefficient (α k) (S k) (level k) n‖ ≤
      B * (n.divisors.card : ℝ) ^ 2 * primeDivisorCount P n := by
  have hlocal : ∀ {m : ℕ}, m ∣ n →
      ∑ k : Fin u, ‖α k m‖ ≤ B * (n.divisors.card : ℝ) := by
    intro m hmn
    have hm : 0 < m := Nat.pos_of_dvd_of_pos hmn hn
    have hcard : (m.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast card_divisors_mono_of_dvd hmn hn.ne'
    exact (hα hm).trans (mul_le_mul_of_nonneg_left hcard hB)
  unfold mtC2BoundaryCoefficient
  have hreindex :
      (∑ k : Fin u, ∑ q ∈ S k, if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0) =
        ∑ q ∈ P, ∑ k : Fin u, if q ∈ S k then
          (if q ∣ n then ∑ m ∈ (n / q).divisors,
            α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0) else 0 := by
    calc
      _ = ∑ k : Fin u, ∑ q ∈ P, if q ∈ S k then
          (if q ∣ n then ∑ m ∈ (n / q).divisors,
            α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact sum_subset_eq_sum_indicator (hSP k) _
      _ = _ := by rw [Finset.sum_comm]
  rw [hreindex]
  calc
    ‖∑ q ∈ P, ∑ k : Fin u, if q ∈ S k then
        (if q ∣ n then ∑ m ∈ (n / q).divisors,
          α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0) else 0‖ ≤
      ∑ q ∈ P, ‖∑ k : Fin u, if q ∈ S k then
        (if q ∣ n then ∑ m ∈ (n / q).divisors,
          α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0) else 0‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q ∈ P, if q ∣ n then B * (n.divisors.card : ℝ) ^ 2 else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases hqn : q ∣ n
      · simp only [hqn, if_true]
        calc
          ‖∑ k : Fin u, if q ∈ S k then
              ∑ m ∈ (n / q).divisors,
                α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0‖ ≤
            ∑ k : Fin u, if q ∈ S k then
              ∑ m ∈ (n / q).divisors,
                ‖α k m * (rho ((n / q) / m) (level k q) : ℂ)‖ else 0 := by
            apply (norm_sum_le _ _).trans
            apply Finset.sum_le_sum
            intro k hk
            by_cases hqS : q ∈ S k
            · simp only [hqS, if_true]
              exact norm_sum_le _ _
            · simp [hqS]
          _ = ∑ m ∈ (n / q).divisors,
              ∑ k : Fin u, if q ∈ S k then
                ‖α k m * (rho ((n / q) / m) (level k q) : ℂ)‖ else 0 := by
            have hdist :
                (∑ k : Fin u, if q ∈ S k then
                    ∑ m ∈ (n / q).divisors,
                      ‖α k m * (rho ((n / q) / m) (level k q) : ℂ)‖ else 0) =
                  ∑ k : Fin u, ∑ m ∈ (n / q).divisors,
                    if q ∈ S k then
                      ‖α k m * (rho ((n / q) / m) (level k q) : ℂ)‖ else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hqS : q ∈ S k <;> simp [hqS]
            rw [hdist, Finset.sum_comm]
          _ ≤ ∑ _m ∈ (n / q).divisors, B * (n.divisors.card : ℝ) := by
            apply Finset.sum_le_sum
            intro m hm
            have hNdiv : n / q ∣ n := ⟨q, (Nat.div_mul_cancel hqn).symm⟩
            have hmDvd : m ∣ n := (Nat.mem_divisors.mp hm).1.trans hNdiv
            calc
              (∑ k : Fin u, if q ∈ S k then
                  ‖α k m * (rho ((n / q) / m) (level k q) : ℂ)‖ else 0) ≤
                ∑ k : Fin u, ‖α k m‖ := by
                  apply Finset.sum_le_sum
                  intro k hk
                  by_cases hqS : q ∈ S k
                  · simp only [hqS, if_true, norm_mul]
                    have hrho : ‖(rho ((n / q) / m) (level k q) : ℂ)‖ ≤ 1 := by
                      exact_mod_cast rho_le_one ((n / q) / m) (level k q)
                    simpa using mul_le_of_le_one_right (norm_nonneg (α k m)) hrho
                  · simp [hqS]
              _ ≤ B * (n.divisors.card : ℝ) := hlocal hmDvd
          _ = B * (n.divisors.card : ℝ) * ((n / q).divisors.card : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
          _ ≤ B * (n.divisors.card : ℝ) ^ 2 := by
            have hNdiv : n / q ∣ n := ⟨q, (Nat.div_mul_cancel hqn).symm⟩
            have hcard : ((n / q).divisors.card : ℝ) ≤
                (n.divisors.card : ℝ) := by
              exact_mod_cast card_divisors_mono_of_dvd hNdiv hn.ne'
            nlinarith [mul_le_mul_of_nonneg_left hcard
              (mul_nonneg hB (Nat.cast_nonneg n.divisors.card))]
      · simp [hqn]
    _ = B * (n.divisors.card : ℝ) ^ 2 * primeDivisorCount P n := by
      unfold primeDivisorCount
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> ring

/-- Unrestricted pointwise form: all varying boundary supports together still occupy at most the
ternary divisor fibre. -/
theorem norm_sum_mtC2BoundaryCoefficient_le_family_ternary
    {u : ℕ} (α : Fin u → ℕ → ℂ) (S : Fin u → Finset ℕ)
    (level : Fin u → ℕ → ℕ) (P : Finset ℕ) {n : ℕ} (hn : 0 < n)
    (hSP : ∀ k, S k ⊆ P) {B : ℝ} (hB : 0 ≤ B)
    (hα : MTFiniteFamilyDivisorBounded α B) :
    ‖∑ k : Fin u, mtC2BoundaryCoefficient (α k) (S k) (level k) n‖ ≤
      B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) := by
  have hlocal : ∀ {m : ℕ}, m ∣ n →
      ∑ k : Fin u, ‖α k m‖ ≤ B * (n.divisors.card : ℝ) := by
    intro m hmn
    have hm : 0 < m := Nat.pos_of_dvd_of_pos hmn hn
    have hcard : (m.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast card_divisors_mono_of_dvd hmn hn.ne'
    exact (hα hm).trans (mul_le_mul_of_nonneg_left hcard hB)
  unfold mtC2BoundaryCoefficient
  have hreindex :
      (∑ k : Fin u, ∑ q ∈ S k, if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0) =
        ∑ q ∈ P, ∑ k : Fin u, if q ∈ S k then
          (if q ∣ n then ∑ m ∈ (n / q).divisors,
            α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0) else 0 := by
    calc
      _ = ∑ k : Fin u, ∑ q ∈ P, if q ∈ S k then
          (if q ∣ n then ∑ m ∈ (n / q).divisors,
            α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact sum_subset_eq_sum_indicator (hSP k) _
      _ = _ := by rw [Finset.sum_comm]
  rw [hreindex]
  calc
    ‖∑ q ∈ P, ∑ k : Fin u, if q ∈ S k then
        (if q ∣ n then ∑ m ∈ (n / q).divisors,
          α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0) else 0‖ ≤
      ∑ q ∈ P, ‖∑ k : Fin u, if q ∈ S k then
        (if q ∣ n then ∑ m ∈ (n / q).divisors,
          α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0) else 0‖ :=
        norm_sum_le _ _
    _ ≤ ∑ q ∈ P, if q ∣ n then
        (B * (n.divisors.card : ℝ)) * ((n / q).divisors.card : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases hqn : q ∣ n
      · simp only [hqn, if_true]
        calc
          ‖∑ k : Fin u, if q ∈ S k then
              ∑ m ∈ (n / q).divisors,
                α k m * (rho ((n / q) / m) (level k q) : ℂ) else 0‖ ≤
            ∑ k : Fin u, if q ∈ S k then
              ∑ m ∈ (n / q).divisors,
                ‖α k m * (rho ((n / q) / m) (level k q) : ℂ)‖ else 0 := by
            apply (norm_sum_le _ _).trans
            apply Finset.sum_le_sum
            intro k hk
            by_cases hqS : q ∈ S k
            · simp only [hqS, if_true]
              exact norm_sum_le _ _
            · simp [hqS]
          _ = ∑ m ∈ (n / q).divisors,
              ∑ k : Fin u, if q ∈ S k then
                ‖α k m * (rho ((n / q) / m) (level k q) : ℂ)‖ else 0 := by
            have hdist :
                (∑ k : Fin u, if q ∈ S k then
                    ∑ m ∈ (n / q).divisors,
                      ‖α k m * (rho ((n / q) / m) (level k q) : ℂ)‖ else 0) =
                  ∑ k : Fin u, ∑ m ∈ (n / q).divisors,
                    if q ∈ S k then
                      ‖α k m * (rho ((n / q) / m) (level k q) : ℂ)‖ else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hqS : q ∈ S k <;> simp [hqS]
            rw [hdist, Finset.sum_comm]
          _ ≤ ∑ _m ∈ (n / q).divisors, B * (n.divisors.card : ℝ) := by
            apply Finset.sum_le_sum
            intro m hm
            have hNdiv : n / q ∣ n := ⟨q, (Nat.div_mul_cancel hqn).symm⟩
            have hmDvd : m ∣ n := (Nat.mem_divisors.mp hm).1.trans hNdiv
            calc
              (∑ k : Fin u, if q ∈ S k then
                  ‖α k m * (rho ((n / q) / m) (level k q) : ℂ)‖ else 0) ≤
                ∑ k : Fin u, ‖α k m‖ := by
                  apply Finset.sum_le_sum
                  intro k hk
                  by_cases hqS : q ∈ S k
                  · simp only [hqS, if_true, norm_mul]
                    have hrho : ‖(rho ((n / q) / m) (level k q) : ℂ)‖ ≤ 1 := by
                      exact_mod_cast rho_le_one ((n / q) / m) (level k q)
                    simpa using mul_le_of_le_one_right (norm_nonneg (α k m)) hrho
                  · simp [hqS]
              _ ≤ B * (n.divisors.card : ℝ) := hlocal hmDvd
          _ = (B * (n.divisors.card : ℝ)) * ((n / q).divisors.card : ℝ) := by
            simp [Finset.sum_const, nsmul_eq_mul]
            ring
      · simp [hqn]
    _ = ∑ q ∈ n.divisors, if q ∈ P then
        (B * (n.divisors.card : ℝ)) * ((n / q).divisors.card : ℝ) else 0 := by
      rw [sum_divisors_indicator_eq_sum_finset_dvd hn]
    _ ≤ ∑ q ∈ n.divisors,
        (B * (n.divisors.card : ℝ)) * ((n / q).divisors.card : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      split_ifs
      · exact le_rfl
      · positivity
    _ = B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) := by
      unfold ternaryDivisorCount
      push_cast
      rw [Finset.mul_sum]

/-- Both endpoint-spill families retain one joint coefficient envelope. -/
theorem norm_sum_mtC2Coefficient_le_familyDivisorBounded
    {u : ℕ} (α : Fin u → ℕ → ℂ)
    (lowerSpill upperSpill : Fin u → Finset ℕ)
    (level : Fin u → ℕ → ℕ) (PLower PUpper : Finset ℕ) {n : ℕ} (hn : 0 < n)
    (hLower : ∀ k, lowerSpill k ⊆ PLower)
    (hUpper : ∀ k, upperSpill k ⊆ PUpper)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTFiniteFamilyDivisorBounded α B) :
    ‖∑ k : Fin u,
        mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) (level k) n‖ ≤
      B * (n.divisors.card : ℝ) ^ 2 *
        (primeDivisorCount PLower n + primeDivisorCount PUpper n) := by
  have hlower := norm_sum_mtC2BoundaryCoefficient_le_familyDivisorBounded
    α lowerSpill level PLower hn hLower hB hα
  have hupper := norm_sum_mtC2BoundaryCoefficient_le_familyDivisorBounded
    α upperSpill level PUpper hn hUpper hB hα
  unfold mtC2Coefficient
  rw [Finset.sum_sub_distrib]
  calc
    ‖(∑ k : Fin u, mtC2BoundaryCoefficient (α k) (upperSpill k) (level k) n) -
        ∑ k : Fin u, mtC2BoundaryCoefficient (α k) (lowerSpill k) (level k) n‖ ≤
      ‖∑ k : Fin u, mtC2BoundaryCoefficient (α k) (upperSpill k) (level k) n‖ +
        ‖∑ k : Fin u, mtC2BoundaryCoefficient (α k) (lowerSpill k) (level k) n‖ :=
      norm_sub_le _ _
    _ ≤ B * (n.divisors.card : ℝ) ^ 2 * primeDivisorCount PUpper n +
        B * (n.divisors.card : ℝ) ^ 2 * primeDivisorCount PLower n :=
      add_le_add hupper hlower
    _ = _ := by ring

/-- Varying terminal prefixes can be aggregated before the Buchstab replacement estimate.  One
global same-block pair count remains, with no multiplicity from terminal cutoffs. -/
theorem norm_sum_mtC3Coefficient_le_familyDivisorBounded
    {u : ℕ} (α : Fin u → ℕ → ℂ) (S : Fin u → Finset ℕ)
    (P : Finset ℕ) (lower : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (hSP : ∀ k, S k ⊆ P) (hP : ∀ q ∈ P, q.Prime)
    (hlower : ∀ q ∈ P, lower q ≤ q)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTFiniteFamilyDivisorBounded α B) :
    ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n‖ ≤
      B * (n.divisors.card : ℝ) ^ 2 *
        primePairDivisorCount P (fun q => primesIco (lower q) q) n := by
  have hlocal : ∀ {m : ℕ}, m ∣ n →
      ∑ k : Fin u, ‖α k m‖ ≤ B * (n.divisors.card : ℝ) := by
    intro m hmn
    have hm : 0 < m := Nat.pos_of_dvd_of_pos hmn hn
    have hcard : (m.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
      exact_mod_cast card_divisors_mono_of_dvd hmn hn.ne'
    exact (hα hm).trans (mul_le_mul_of_nonneg_left hcard hB)
  have hexpand : ∀ k : Fin u,
      mtC3Coefficient (α k) (S k) lower n = mtC3Expanded (α k) (S k) lower n := by
    intro k
    exact mtC3Coefficient_eq_expanded (α k) (S k) lower hn
      (fun q hq => hP q (hSP k hq))
      (fun q hq => hlower q (hSP k hq))
  simp_rw [hexpand]
  unfold mtC3Expanded
  have hreindex :
      (∑ k : Fin u, ∑ q ∈ S k, if q ∣ n then
          ∑ m ∈ (n / q).divisors,
            α k m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
              (rho (n / q / m / p) p : ℂ) else 0) =
        ∑ q ∈ P, ∑ k : Fin u, if q ∈ S k then
          (if q ∣ n then ∑ m ∈ (n / q).divisors,
            α k m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
              (rho (n / q / m / p) p : ℂ) else 0) else 0 := by
    calc
      _ = ∑ k : Fin u, ∑ q ∈ P, if q ∈ S k then
          (if q ∣ n then ∑ m ∈ (n / q).divisors,
            α k m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
              (rho (n / q / m / p) p : ℂ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact sum_subset_eq_sum_indicator (hSP k) _
      _ = _ := by rw [Finset.sum_comm]
  rw [hreindex]
  calc
    ‖∑ q ∈ P, ∑ k : Fin u, if q ∈ S k then
        (if q ∣ n then ∑ m ∈ (n / q).divisors,
          α k m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
            (rho (n / q / m / p) p : ℂ) else 0) else 0‖ ≤
      ∑ q ∈ P, ‖∑ k : Fin u, if q ∈ S k then
        (if q ∣ n then ∑ m ∈ (n / q).divisors,
          α k m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
            (rho (n / q / m / p) p : ℂ) else 0) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ P, if q ∣ n then
        ∑ m ∈ (n / q).divisors,
          (B * (n.divisors.card : ℝ)) *
            ((primeWindow (n / q / m) (lower q) q).card : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases hqn : q ∣ n
      · simp only [hqn, if_true]
        calc
          ‖∑ k : Fin u, if q ∈ S k then
              ∑ m ∈ (n / q).divisors,
                α k m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
                  (rho (n / q / m / p) p : ℂ) else 0‖ ≤
            ∑ k : Fin u, if q ∈ S k then
              ∑ m ∈ (n / q).divisors,
                ‖α k m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
                  (rho (n / q / m / p) p : ℂ)‖ else 0 := by
            apply (norm_sum_le _ _).trans
            apply Finset.sum_le_sum
            intro k hk
            by_cases hqS : q ∈ S k
            · simp only [hqS, if_true]
              exact norm_sum_le _ _
            · simp [hqS]
          _ = ∑ m ∈ (n / q).divisors,
              ∑ k : Fin u, if q ∈ S k then
                ‖α k m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
                  (rho (n / q / m / p) p : ℂ)‖ else 0 := by
            have hdist :
                (∑ k : Fin u, if q ∈ S k then
                    ∑ m ∈ (n / q).divisors,
                      ‖α k m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
                        (rho (n / q / m / p) p : ℂ)‖ else 0) =
                  ∑ k : Fin u, ∑ m ∈ (n / q).divisors,
                    if q ∈ S k then
                      ‖α k m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
                        (rho (n / q / m / p) p : ℂ)‖ else 0 := by
              apply Finset.sum_congr rfl
              intro k hk
              by_cases hqS : q ∈ S k <;> simp [hqS]
            rw [hdist, Finset.sum_comm]
          _ ≤ ∑ m ∈ (n / q).divisors,
              (B * (n.divisors.card : ℝ)) *
                ((primeWindow (n / q / m) (lower q) q).card : ℝ) := by
            apply Finset.sum_le_sum
            intro m hm
            have hNdiv : n / q ∣ n := ⟨q, (Nat.div_mul_cancel hqn).symm⟩
            have hmDvd : m ∣ n := (Nat.mem_divisors.mp hm).1.trans hNdiv
            let W : ℝ := ((primeWindow (n / q / m) (lower q) q).card : ℝ)
            have hinner :
                ‖∑ p ∈ primeWindow (n / q / m) (lower q) q,
                    (rho (n / q / m / p) p : ℂ)‖ ≤ W := by
              dsimp [W]
              calc
                ‖∑ p ∈ primeWindow (n / q / m) (lower q) q,
                    (rho (n / q / m / p) p : ℂ)‖ ≤
                  ∑ p ∈ primeWindow (n / q / m) (lower q) q,
                    ‖(rho (n / q / m / p) p : ℂ)‖ := norm_sum_le _ _
                _ ≤ ∑ _p ∈ primeWindow (n / q / m) (lower q) q, (1 : ℝ) := by
                  apply Finset.sum_le_sum
                  intro p hp
                  exact_mod_cast rho_le_one (n / q / m / p) p
                _ = _ := by simp
            calc
              (∑ k : Fin u, if q ∈ S k then
                  ‖α k m * ∑ p ∈ primeWindow (n / q / m) (lower q) q,
                    (rho (n / q / m / p) p : ℂ)‖ else 0) ≤
                (∑ k : Fin u, ‖α k m‖) * W := by
                  rw [Finset.sum_mul]
                  apply Finset.sum_le_sum
                  intro k hk
                  by_cases hqS : q ∈ S k
                  · simp only [hqS, if_true, norm_mul]
                    exact mul_le_mul_of_nonneg_left hinner (norm_nonneg (α k m))
                  · simp only [hqS, if_false]
                    exact mul_nonneg (norm_nonneg _) (Nat.cast_nonneg _)
              _ ≤ (B * (n.divisors.card : ℝ)) * W :=
                mul_le_mul_of_nonneg_right (hlocal hmDvd) (by dsimp [W]; positivity)
              _ = _ := rfl
      · simp [hqn]
    _ = (B * (n.divisors.card : ℝ)) * mtC3ExpansionCount P lower n := by
      unfold mtC3ExpansionCount
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs
      · rw [Finset.mul_sum]
      · simp
    _ ≤ (B * (n.divisors.card : ℝ)) *
        ((n.divisors.card : ℝ) *
          primePairDivisorCount P (fun q => primesIco (lower q) q) n) := by
      apply mul_le_mul_of_nonneg_left
        (mtC3ExpansionCount_le_pairDivisorCount P lower hn)
      positivity
    _ = _ := by ring

/-- Pointwise truncation bound for the whole terminal family. -/
theorem norm_sum_mtC1Coefficient_le_family_ternary
    {u : ℕ} (α : Fin u → ℕ → ℂ) (z D : ℕ) {n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTFiniteFamilyDivisorBounded α B) :
    ‖∑ k : Fin u, mtC1Coefficient (α k) z D n‖ ≤
      B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) := by
  let β : ℕ → ℂ := fun m => if m ∣ n then ∑ k : Fin u, α k m else 0
  have hβ : ∀ m, ‖β m‖ ≤ B * (n.divisors.card : ℝ) := by
    intro m
    by_cases hmn : m ∣ n
    · simp only [β, hmn, if_true]
      have hm : 0 < m := Nat.pos_of_dvd_of_pos hmn hn
      have hcard : (m.divisors.card : ℝ) ≤ (n.divisors.card : ℝ) := by
        exact_mod_cast card_divisors_mono_of_dvd hmn hn.ne'
      exact (norm_sum_le _ _).trans <|
        (hα hm).trans (mul_le_mul_of_nonneg_left hcard hB)
    · simp [β, hmn, mul_nonneg hB (Nat.cast_nonneg _)]
  rw [sum_mtC1Coefficient_eq]
  have hcongr :
      mtC1Coefficient (fun m => ∑ k : Fin u, α k m) z D n =
        mtC1Coefficient β z D n := by
    unfold mtC1Coefficient
    apply Finset.sum_congr rfl
    intro m hm
    have hmn : m ∣ n := Nat.dvd_of_mem_divisors hm
    simp [β, hmn]
  rw [hcongr]
  exact norm_mtC1Coefficient_le_ternaryDivisorCount β hn
    (mul_nonneg hB (Nat.cast_nonneg _)) hβ

/-- Pointwise endpoint bound for the whole terminal family. -/
theorem norm_sum_mtC2Coefficient_le_family_ternary
    {u : ℕ} (α : Fin u → ℕ → ℂ)
    (lowerSpill upperSpill : Fin u → Finset ℕ)
    (level : Fin u → ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTFiniteFamilyDivisorBounded α B) :
    ‖∑ k : Fin u,
        mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) (level k) n‖ ≤
      2 * B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) := by
  let PLower := (Finset.univ : Finset (Fin u)).biUnion lowerSpill
  let PUpper := (Finset.univ : Finset (Fin u)).biUnion upperSpill
  have hLower : ∀ k, lowerSpill k ⊆ PLower := by
    intro k q hq
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hq⟩
  have hUpper : ∀ k, upperSpill k ⊆ PUpper := by
    intro k q hq
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hq⟩
  have hlower := norm_sum_mtC2BoundaryCoefficient_le_family_ternary
    α lowerSpill level PLower hn hLower hB hα
  have hupper := norm_sum_mtC2BoundaryCoefficient_le_family_ternary
    α upperSpill level PUpper hn hUpper hB hα
  unfold mtC2Coefficient
  rw [Finset.sum_sub_distrib]
  calc
    ‖(∑ k : Fin u, mtC2BoundaryCoefficient (α k) (upperSpill k) (level k) n) -
        ∑ k : Fin u, mtC2BoundaryCoefficient (α k) (lowerSpill k) (level k) n‖ ≤
      ‖∑ k : Fin u, mtC2BoundaryCoefficient (α k) (upperSpill k) (level k) n‖ +
        ‖∑ k : Fin u, mtC2BoundaryCoefficient (α k) (lowerSpill k) (level k) n‖ :=
      norm_sub_le _ _
    _ ≤ B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) +
        B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) :=
      add_le_add hupper hlower
    _ = _ := by ring

/-- Pointwise Buchstab-replacement bound for the whole terminal family. -/
theorem norm_sum_mtC3Coefficient_le_family_ternary
    {u : ℕ} (α : Fin u → ℕ → ℂ) (S : Fin u → Finset ℕ)
    (lower : Fin u → ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTFiniteFamilyDivisorBounded α B) :
    ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) (lower k) n‖ ≤
      2 * B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) := by
  let P := (Finset.univ : Finset (Fin u)).biUnion S
  have hS : ∀ k, S k ⊆ P := by
    intro k q hq
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hq⟩
  have hlower := norm_sum_mtC2BoundaryCoefficient_le_family_ternary
    α S lower P hn hS hB hα
  have hid := norm_sum_mtC2BoundaryCoefficient_le_family_ternary
    α S (fun _ => id) P hn hS hB hα
  simp_rw [mtC3Coefficient_eq_boundary_sub]
  rw [Finset.sum_sub_distrib]
  calc
    ‖(∑ k : Fin u, mtC2BoundaryCoefficient (α k) (S k) (lower k) n) -
        ∑ k : Fin u, mtC2BoundaryCoefficient (α k) (S k) id n‖ ≤
      ‖∑ k : Fin u, mtC2BoundaryCoefficient (α k) (S k) (lower k) n‖ +
        ‖∑ k : Fin u, mtC2BoundaryCoefficient (α k) (S k) id n‖ := norm_sub_le _ _
    _ ≤ B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) +
        B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) :=
      add_le_add hlower hid
    _ = _ := by ring

/-- The entire terminal error family has the same fixed fifth-moment pointwise envelope as one
divisor-bounded error. -/
theorem norm_sum_mtLemma23Error_le_five_mul_divisor_mul_ternary
    {u : ℕ} (α : Fin u → ℕ → ℂ) (z D : ℕ)
    (lowerSpill upperSpill S : Fin u → Finset ℕ)
    (lower : Fin u → ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTFiniteFamilyDivisorBounded α B) :
    ‖∑ k : Fin u, mtLemma23Error (α k) z D
        (lowerSpill k) (upperSpill k) (S k) (lower k) n‖ ≤
      5 * B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) := by
  have hc1 := norm_sum_mtC1Coefficient_le_family_ternary α z D hn hB hα
  have hc2 := norm_sum_mtC2Coefficient_le_family_ternary
    α lowerSpill upperSpill lower hn hB hα
  have hc3 := norm_sum_mtC3Coefficient_le_family_ternary α S lower hn hB hα
  unfold mtLemma23Error
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  calc
    ‖(∑ k : Fin u, mtC1Coefficient (α k) z D n) +
          (∑ k : Fin u,
            mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) (lower k) n) +
        ∑ k : Fin u, mtC3Coefficient (α k) (S k) (lower k) n‖ ≤
      ‖∑ k : Fin u, mtC1Coefficient (α k) z D n‖ +
          ‖∑ k : Fin u,
            mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) (lower k) n‖ +
        ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) (lower k) n‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by nlinarith

/-- Fixed-fifth-moment first bound for one grid-free terminal family. -/
theorem divisor_mul_ternary_mul_norm_sum_mtLemma23Error_le_weighted
    {u : ℕ} (α : Fin u → ℕ → ℂ) (z D : ℕ)
    (lowerSpill upperSpill S : Fin u → Finset ℕ)
    (lower : ℕ → ℕ) (PLower PUpper P : Finset ℕ)
    {n : ℕ} (hn : 0 < n)
    (hLower : ∀ k, lowerSpill k ⊆ PLower)
    (hUpper : ∀ k, upperSpill k ⊆ PUpper)
    (hSP : ∀ k, S k ⊆ P) (hP : ∀ q ∈ P, q.Prime)
    (hlower : ∀ q ∈ P, lower q ≤ q)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTFiniteFamilyDivisorBounded α B) :
    (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        ‖∑ k : Fin u, mtLemma23Error (α k) z D
          (lowerSpill k) (upperSpill k) (S k) lower n‖ ≤
      B * (weightedSiftTailDivisorCount 5 z D n +
        weightedPrimeDivisorCount 5 PLower n +
        weightedPrimeDivisorCount 5 PUpper n +
        weightedPrimePairDivisorCount 5 P
          (fun q => primesIco (lower q) q) n) := by
  have hd3 : (ternaryDivisorCount n : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
    exact_mod_cast ternaryDivisorCount_le_sq hn
  have hc1 := norm_sum_mtC1Coefficient_le_familyDivisorBounded
    α (z := z) (D := D) hn hB hα
  have hc2 := norm_sum_mtC2Coefficient_le_familyDivisorBounded
    α lowerSpill upperSpill (fun _ => lower) PLower PUpper hn
    hLower hUpper hB hα
  have hc3 := norm_sum_mtC3Coefficient_le_familyDivisorBounded
    α S P lower hn hSP hP hlower hB hα
  have hw1 :
      (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖∑ k : Fin u, mtC1Coefficient (α k) z D n‖ ≤
        B * weightedSiftTailDivisorCount 5 z D n := by
    unfold weightedSiftTailDivisorCount
    calc
      _ ≤ (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) ^ 2) *
          (B * (n.divisors.card : ℝ) ^ 2 * siftTailDivisorCount z D n) := by
        gcongr
      _ = _ := by ring
  have hw2 :
      (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖∑ k : Fin u,
            mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) lower n‖ ≤
        B * (weightedPrimeDivisorCount 5 PLower n +
          weightedPrimeDivisorCount 5 PUpper n) := by
    unfold weightedPrimeDivisorCount
    have hl : 0 ≤ primeDivisorCount PLower n := by
      unfold primeDivisorCount
      positivity
    have hu : 0 ≤ primeDivisorCount PUpper n := by
      unfold primeDivisorCount
      positivity
    calc
      _ ≤ (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) ^ 2) *
          (B * (n.divisors.card : ℝ) ^ 2 *
            (primeDivisorCount PLower n + primeDivisorCount PUpper n)) := by
        gcongr
      _ = _ := by ring
  have hw3 :
      (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n‖ ≤
        B * weightedPrimePairDivisorCount 5 P
          (fun q => primesIco (lower q) q) n := by
    unfold weightedPrimePairDivisorCount
    have hpairs : 0 ≤ primePairDivisorCount P
        (fun q => primesIco (lower q) q) n := by
      unfold primePairDivisorCount
      positivity
    calc
      _ ≤ (n.divisors.card : ℝ) * ((n.divisors.card : ℝ) ^ 2) *
          (B * (n.divisors.card : ℝ) ^ 2 *
            primePairDivisorCount P (fun q => primesIco (lower q) q) n) := by
        gcongr
      _ = _ := by ring
  unfold mtLemma23Error
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hnorm := (norm_add_le
    ((∑ k : Fin u, mtC1Coefficient (α k) z D n) +
      ∑ k : Fin u,
        mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) lower n)
    (∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n)).trans
      (add_le_add (norm_add_le _ _) le_rfl)
  calc
    (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        ‖(∑ k : Fin u, mtC1Coefficient (α k) z D n) +
            (∑ k : Fin u,
              mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) lower n) +
          ∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n‖ ≤
      (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        (‖∑ k : Fin u, mtC1Coefficient (α k) z D n‖ +
          ‖∑ k : Fin u,
            mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) lower n‖ +
          ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n‖) := by
      gcongr
    _ ≤ B * weightedSiftTailDivisorCount 5 z D n +
        B * (weightedPrimeDivisorCount 5 PLower n +
          weightedPrimeDivisorCount 5 PUpper n) +
        B * weightedPrimePairDivisorCount 5 P
          (fun q => primesIco (lower q) q) n := by
      calc
        _ = (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
              ‖∑ k : Fin u, mtC1Coefficient (α k) z D n‖ +
            (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
              ‖∑ k : Fin u,
                mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) lower n‖ +
            (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
              ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n‖ := by ring
        _ ≤ _ := add_le_add (add_le_add hw1 hw2) hw3
    _ = _ := by ring

/-- Weighted first moment of a grid-free terminal family. -/
theorem sum_divisor_mul_ternary_mul_norm_sum_mtLemma23Error_le_weighted
    {u : ℕ} (α : Fin u → ℕ → ℂ) (z D : ℕ)
    (lowerSpill upperSpill S : Fin u → Finset ℕ)
    (lower : ℕ → ℕ) (PLower PUpper P : Finset ℕ) (Y : ℕ)
    (hLower : ∀ k, lowerSpill k ⊆ PLower)
    (hUpper : ∀ k, upperSpill k ⊆ PUpper)
    (hSP : ∀ k, S k ⊆ P) (hP : ∀ q ∈ P, q.Prime)
    (hlower : ∀ q ∈ P, lower q ≤ q)
    {B : ℝ} (hB : 0 ≤ B) (hα : MTFiniteFamilyDivisorBounded α B) :
    ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖∑ k : Fin u, mtLemma23Error (α k) z D
            (lowerSpill k) (upperSpill k) (S k) lower n‖ ≤
      B * ∑ n ∈ Finset.Icc 1 Y,
        (weightedSiftTailDivisorCount 5 z D n +
          weightedPrimeDivisorCount 5 PLower n +
          weightedPrimeDivisorCount 5 PUpper n +
          weightedPrimePairDivisorCount 5 P
            (fun q => primesIco (lower q) q) n) := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hnIcc
  have hn : 0 < n := by
    rw [Finset.mem_Icc] at hnIcc
    omega
  exact divisor_mul_ternary_mul_norm_sum_mtLemma23Error_le_weighted
    α z D lowerSpill upperSpill S lower PLower PUpper P hn
    hLower hUpper hSP hP hlower hB hα

/-- Squaring a grid-free terminal family costs the same fixed fifth divisor moment as one error. -/
theorem sum_norm_sq_sum_mtLemma23Error_le_five_mul_divisor_weighted
    {u : ℕ} (α : Fin u → ℕ → ℂ) (z D : ℕ)
    (lowerSpill upperSpill S : Fin u → Finset ℕ)
    (lower : ℕ → ℕ) (Y : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hα : MTFiniteFamilyDivisorBounded α B) :
    ∑ n ∈ Finset.Icc 1 Y,
        ‖∑ k : Fin u, mtLemma23Error (α k) z D
          (lowerSpill k) (upperSpill k) (S k) lower n‖ ^ 2 ≤
      5 * B * ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖∑ k : Fin u, mtLemma23Error (α k) z D
            (lowerSpill k) (upperSpill k) (S k) lower n‖ := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hnIcc
  have hn : 0 < n := by
    rw [Finset.mem_Icc] at hnIcc
    omega
  have hpoint := norm_sum_mtLemma23Error_le_five_mul_divisor_mul_ternary
    α z D lowerSpill upperSpill S (fun _ => lower) hn hB hα
  calc
    ‖∑ k : Fin u, mtLemma23Error (α k) z D
        (lowerSpill k) (upperSpill k) (S k) lower n‖ ^ 2 =
      ‖∑ k : Fin u, mtLemma23Error (α k) z D
        (lowerSpill k) (upperSpill k) (S k) lower n‖ *
      ‖∑ k : Fin u, mtLemma23Error (α k) z D
        (lowerSpill k) (upperSpill k) (S k) lower n‖ := by ring
    _ ≤ (5 * B * (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ)) *
        ‖∑ k : Fin u, mtLemma23Error (α k) z D
          (lowerSpill k) (upperSpill k) (S k) lower n‖ :=
      mul_le_mul_of_nonneg_right hpoint (norm_nonneg _)
    _ = 5 * B * ((n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
        ‖∑ k : Fin u, mtLemma23Error (α k) z D
          (lowerSpill k) (upperSpill k) (S k) lower n‖) := by ring

/-- Terminal chain fibres satisfy the joint divisor envelope used above. -/
theorem MTFiniteIterationSourceData.terminalCoefficient_familyDivisorBounded
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a : ArithmeticFunction ℂ) (B : ℝ) (hB : 0 ≤ B)
    (ha : ∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B)
    (depth : ℕ) (j : Fin (t + 1)) :
    MTFiniteFamilyDivisorBounded
      (fun k m => mtTerminalCoefficientAF data a depth j k m) B := by
  intro m hm
  exact data.sum_norm_mtTerminalCoefficientAF_le_card_divisors
    a B hB ha depth j hm

/-- With one common block-lower map, a signed source layer is exactly one grid-free error family,
up to its norm-one alternating sign. -/
theorem norm_mtLiteralSignedSourceErrorLayer_eq_norm_sum_mtLemma23Error
    {t : ℕ} (data : MTFiniteIterationSourceData t)
    (a : ArithmeticFunction ℂ) (depth : ℕ) (j : Fin (t + 1))
    (lower : ℕ → ℕ) (hlower : ∀ k, data.lower k = lower)
    {n : ℕ} (hn : 0 < n) :
    ‖mtLiteralSignedSourceErrorLayer data a depth j n‖ =
      ‖∑ k : Fin (t + 1),
        mtLemma23Error
          (fun m => mtTerminalCoefficientAF data a depth j k m)
          data.z₀ data.D (data.lowerSpill k) (data.upperSpill k)
          (primesIco data.z₀ (data.cutoff k)) lower n‖ := by
  rw [mtLiteralSignedSourceErrorLayer_eq_terminalErrors data a depth j hn,
    norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
  apply congrArg norm
  apply Finset.sum_congr rfl
  intro k hk
  rw [hlower k]

end

end RHTower.Sieve
