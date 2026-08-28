import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenGridFreePaperScale
import GaloisForLFunctions.RHTower.Sieve.PrimeWindowRelaxedDilationPaperScale

/-!
# Grid-free error bounds for rounded geometric blocks

Natural endpoints of a literal geometric block introduce one extra rounding factor.  Their
shifted-natural support therefore has relative width at most `1 + 3 δ_A`, while its reciprocal
prime mass is at most `4 δ_A`.  This file keeps that fixed dilation explicit and proves the same
paper exponent with a larger absolute constant.  No adic-grid or terminal-fibre cardinality is
paid.
-/

namespace RHTower.Sieve

open Filter Topology Finset ArithmeticFunction

noncomputable section

/-- The `c₂` first moment with both endpoint families allowed reciprocal mass `4 δ_A`. -/
theorem eventually_sum_divisor_ternary_norm_sum_mtC2_fixedDilation_le_log_rpow
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (u : ℕ) (α : Fin u → ℕ → ℂ)
        (lowerSpill upperSpill : Fin u → Finset ℕ)
        (level : Fin u → ℕ → ℕ) (PLower PUpper : Finset ℕ)
        (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      (∀ k, lowerSpill k ⊆ PLower) → (∀ k, upperSpill k ⊆ PUpper) →
      (∀ q ∈ PLower, q.Prime) → (∀ q ∈ PUpper, q.Prime) →
      (∑ q ∈ PLower, 1 / (q : ℝ)) ≤ 4 * mtPaperWidth A X →
      (∑ q ∈ PUpper, 1 / (q : ℝ)) ≤ 4 * mtPaperWidth A X →
      0 ≤ B → MTFiniteFamilyDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u,
              mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) (level k) n‖ ≤
        2 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_mt_fifthMoment_width_absorption A hA,
    Filter.eventually_ge_atTop 1] with X habsorbX hX
  intro u α lowerSpill upperSpill level PLower PUpper Y B
    hY hYX hLower hUpper hprimeLower hprimeUpper hmassLower hmassUpper hB hα
  have hpoint :
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u,
              mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) (level k) n‖ ≤
        B * ∑ n ∈ Finset.Icc 1 Y,
          (weightedPrimeDivisorCount 5 PLower n +
            weightedPrimeDivisorCount 5 PUpper n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hnIcc
    have hn : 0 < n := by
      rw [Finset.mem_Icc] at hnIcc
      omega
    have hd3 : (ternaryDivisorCount n : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
      exact_mod_cast ternaryDivisorCount_le_sq hn
    have hc2 := norm_sum_mtC2Coefficient_le_familyDivisorBounded
      α lowerSpill upperSpill level PLower PUpper hn hLower hUpper hB hα
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
  let C : ℝ := (2 : ℝ) ^ 5 * (Y : ℝ) *
    (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1)
  have hmeanLower := sum_weightedPrimeDivisorCount_le
    5 Y hY PLower hprimeLower
  have hmeanUpper := sum_weightedPrimeDivisorCount_le
    5 Y hY PUpper hprimeUpper
  have hweighted :
      ∑ n ∈ Finset.Icc 1 Y,
          (weightedPrimeDivisorCount 5 PLower n +
            weightedPrimeDivisorCount 5 PUpper n) ≤
        C * (8 * mtPaperWidth A X) := by
    rw [Finset.sum_add_distrib]
    calc
      _ ≤ C * (∑ q ∈ PLower, 1 / (q : ℝ)) +
          C * ∑ q ∈ PUpper, 1 / (q : ℝ) :=
        add_le_add hmeanLower hmeanUpper
      _ = C * ((∑ q ∈ PLower, 1 / (q : ℝ)) +
          ∑ q ∈ PUpper, 1 / (q : ℝ)) := by ring
      _ ≤ C * (8 * mtPaperWidth A X) := by
        have hC : 0 ≤ C := by
          dsimp [C]
          have hlog : 0 ≤ Real.log (Y : ℝ) :=
            Real.log_nonneg (by exact_mod_cast hY)
          positivity
        exact mul_le_mul_of_nonneg_left (by linarith) hC
  have hscalar := habsorbX Y 1 hY hYX (by omega : 1 ≤ (1 : ℕ))
    (by exact_mod_cast hX)
  have hlogY : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hY)
  have hwidth : 0 ≤ mtPaperWidth A X := by
    rw [mtPaperWidth]
    exact Real.rpow_nonneg (Real.log_nonneg hX) _
  have hcompare :
      (2 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (8 * mtPaperWidth A X) ≤
        2 * ((4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (1 : ℝ))) := by
    norm_num [Real.log_one]
    have hbase : 0 ≤ 1 + Real.log (Y : ℝ) := by linarith
    have hpoly : 0 ≤ (1 + Real.log (Y : ℝ)) ^ 31 := pow_nonneg hbase _
    nlinarith [mul_nonneg hpoly hwidth]
  calc
    _ ≤ B * ∑ n ∈ Finset.Icc 1 Y,
        (weightedPrimeDivisorCount 5 PLower n +
          weightedPrimeDivisorCount 5 PUpper n) := hpoint
    _ ≤ B * (C * (8 * mtPaperWidth A X)) :=
      mul_le_mul_of_nonneg_left hweighted hB
    _ = B * (Y : ℝ) *
        ((2 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (8 * mtPaperWidth A X)) := by
      dsimp [C]
      ring
    _ ≤ B * (Y : ℝ) *
        (2 * ((4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (1 : ℝ)))) := by
      exact mul_le_mul_of_nonneg_left hcompare
        (mul_nonneg hB (Nat.cast_nonneg _))
    _ = 2 * B * (Y : ℝ) *
        ((4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (1 : ℝ))) := by ring
    _ ≤ 2 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_one] using hscalar)
        (mul_nonneg (mul_nonneg (by norm_num) hB) (Nat.cast_nonneg _))

/-- The `c₃` first moment from an explicit `4 δ_A` reciprocal-mass bound on every lower fibre. -/
theorem eventually_sum_divisor_ternary_norm_sum_mtC3_of_fibreMass_le_log_rpow
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (u : ℕ) (α : Fin u → ℕ → ℂ) (S : Fin u → Finset ℕ)
        (P : Finset ℕ) (lower : ℕ → ℕ) (Y N : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ N → (N : ℝ) ≤ X →
      (∀ k, S k ⊆ P) → (∀ q ∈ P, q.Prime) → (∀ q ∈ P, q ≤ N) →
      (∀ q ∈ P, lower q ≤ q) →
      (∀ q ∈ P,
        (∑ p ∈ primesIco (lower q) q, 1 / (p : ℝ)) ≤ 4 * mtPaperWidth A X) →
      0 ≤ B → MTFiniteFamilyDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n‖ ≤
        2 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_mt_fifthMoment_width_absorption A hA]
    with X habsorbX
  intro u α S P lower Y N B hY hYX hN hNX hSP hprime hupper
    hlower hfibre hB hα
  have hpairPrime : ∀ q ∈ P, ∀ p ∈ primesIco (lower q) q, p.Prime := by
    intro q hq p hp
    exact (mem_primesIco.mp hp).2.2
  have hpoint :
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n‖ ≤
        B * ∑ n ∈ Finset.Icc 1 Y,
          weightedPrimePairDivisorCount 5 P
            (fun q => primesIco (lower q) q) n := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hnIcc
    have hn : 0 < n := by
      rw [Finset.mem_Icc] at hnIcc
      omega
    have hd3 : (ternaryDivisorCount n : ℝ) ≤ (n.divisors.card : ℝ) ^ 2 := by
      exact_mod_cast ternaryDivisorCount_le_sq hn
    have hc3 := norm_sum_mtC3Coefficient_le_familyDivisorBounded
      α S P lower hn hSP hprime hlower hB hα
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
  have hweighted := sum_weightedPrimePairDivisorCount_le_of_fibreMass
    5 Y hY P (fun q => primesIco (lower q) q) hprime hpairPrime hfibre
  have houter : ∑ q ∈ P, 1 / (q : ℝ) ≤ 1 + Real.log N :=
    sum_inv_finset_le_one_add_log P N (fun q hq => (hprime q hq).pos) hupper
  have hfactor0 : 0 ≤ (4 : ℝ) ^ 5 * (Y : ℝ) *
      (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) * (4 * mtPaperWidth A X) := by
    have hlog : 0 ≤ Real.log (Y : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hY)
    have hX1 : (1 : ℝ) ≤ X :=
      (by exact_mod_cast hN : (1 : ℝ) ≤ (N : ℝ)).trans hNX
    have hwidth : 0 ≤ mtPaperWidth A X := by
      rw [mtPaperWidth]
      exact Real.rpow_nonneg (Real.log_nonneg hX1) _
    positivity
  have hscalar := habsorbX Y N hY hYX hN hNX
  calc
    _ ≤ B * ∑ n ∈ Finset.Icc 1 Y,
        weightedPrimePairDivisorCount 5 P
          (fun q => primesIco (lower q) q) n := hpoint
    _ ≤ B * ((4 : ℝ) ^ 5 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (4 * mtPaperWidth A X) * ∑ q ∈ P, 1 / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hweighted hB
    _ ≤ B * ((4 : ℝ) ^ 5 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (4 * mtPaperWidth A X) * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left houter hfactor0) hB
    _ = 2 * B * (Y : ℝ) *
        ((4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log N)) := by ring
    _ ≤ 2 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hscalar
        (mul_nonneg (mul_nonneg (by norm_num) hB) (Nat.cast_nonneg _))

/-- Joint first moment when rounded geometric endpoint and collision masses are explicit. -/
theorem eventually_sum_divisor_ternary_norm_sum_mtLemma23Error_fixedDilation_le_log_rpow
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (u : ℕ) (α : Fin u → ℕ → ℂ)
        (lowerSpill upperSpill S : Fin u → Finset ℕ)
        (lower : ℕ → ℕ) (PLower PUpper P : Finset ℕ)
        (Y N : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ N → (N : ℝ) ≤ X →
      (∀ k, lowerSpill k ⊆ PLower) → (∀ k, upperSpill k ⊆ PUpper) →
      (∀ k, S k ⊆ P) →
      (∀ q ∈ PLower, q.Prime) → (∀ q ∈ PUpper, q.Prime) →
      (∀ q ∈ P, q.Prime) → (∀ q ∈ P, q ≤ N) →
      (∑ q ∈ PLower, 1 / (q : ℝ)) ≤ 4 * mtPaperWidth A X →
      (∑ q ∈ PUpper, 1 / (q : ℝ)) ≤ 4 * mtPaperWidth A X →
      (∀ q ∈ P, lower q ≤ q) →
      (∀ q ∈ P,
        (∑ p ∈ primesIco (lower q) q, 1 / (p : ℝ)) ≤ 4 * mtPaperWidth A X) →
      0 ≤ B → MTFiniteFamilyDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u, mtLemma23Error (α k)
              (mtLowerCutoffNat X) (mtTruncationNat X)
              (lowerSpill k) (upperSpill k) (S k) lower n‖ ≤
        5 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_divisor_ternary_norm_sum_mtC1_le_log_rpow A,
    eventually_sum_divisor_ternary_norm_sum_mtC2_fixedDilation_le_log_rpow A hA,
    eventually_sum_divisor_ternary_norm_sum_mtC3_of_fibreMass_le_log_rpow A hA]
      with X hc1X hc2X hc3X
  intro u α lowerSpill upperSpill S lower PLower PUpper P Y N B
    hY hYX hN hNX hLower hUpper hSP hprimeLower hprimeUpper hprime hPUpper
    hmassLower hmassUpper hlower hfibre hB hα
  have hc1 := hc1X u α Y B hY hYX hB hα
  have hc2 := hc2X u α lowerSpill upperSpill (fun _ => lower)
    PLower PUpper Y B hY hYX hLower hUpper hprimeLower hprimeUpper
    hmassLower hmassUpper hB hα
  have hc3 := hc3X u α S P lower Y N B hY hYX hN hNX hSP hprime hPUpper
    hlower hfibre hB hα
  have hpoint : ∀ n ∈ Finset.Icc 1 Y,
      (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖∑ k : Fin u, mtLemma23Error (α k)
            (mtLowerCutoffNat X) (mtTruncationNat X)
            (lowerSpill k) (upperSpill k) (S k) lower n‖ ≤
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          (‖∑ k : Fin u,
              mtC1Coefficient (α k) (mtLowerCutoffNat X) (mtTruncationNat X) n‖ +
            ‖∑ k : Fin u,
              mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) lower n‖ +
            ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n‖) := by
    intro n hn
    unfold mtLemma23Error
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hnorm := (norm_add_le
      ((∑ k : Fin u,
          mtC1Coefficient (α k) (mtLowerCutoffNat X) (mtTruncationNat X) n) +
        ∑ k : Fin u,
          mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) lower n)
      (∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n)).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    gcongr
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          (‖∑ k : Fin u,
              mtC1Coefficient (α k) (mtLowerCutoffNat X) (mtTruncationNat X) n‖ +
            ‖∑ k : Fin u,
              mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) lower n‖ +
            ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n‖) :=
      Finset.sum_le_sum hpoint
    _ = (∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u,
              mtC1Coefficient (α k) (mtLowerCutoffNat X) (mtTruncationNat X) n‖) +
        (∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u,
              mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) lower n‖) +
        ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n‖ := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ ≤ B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) +
        2 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) +
        2 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) :=
      add_le_add (add_le_add hc1 hc2) hc3
    _ = _ := by ring

/-- Mean square for all rounded geometric terminal errors, with no grid-cardinality factor. -/
theorem eventually_sum_norm_sq_sum_mtLemma23Error_fixedDilation_le_log_rpow
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (u : ℕ) (α : Fin u → ℕ → ℂ)
        (lowerSpill upperSpill S : Fin u → Finset ℕ)
        (lower : ℕ → ℕ) (PLower PUpper P : Finset ℕ)
        (Y N : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ N → (N : ℝ) ≤ X →
      (∀ k, lowerSpill k ⊆ PLower) → (∀ k, upperSpill k ⊆ PUpper) →
      (∀ k, S k ⊆ P) →
      (∀ q ∈ PLower, q.Prime) → (∀ q ∈ PUpper, q.Prime) →
      (∀ q ∈ P, q.Prime) → (∀ q ∈ P, q ≤ N) →
      (∑ q ∈ PLower, 1 / (q : ℝ)) ≤ 4 * mtPaperWidth A X →
      (∑ q ∈ PUpper, 1 / (q : ℝ)) ≤ 4 * mtPaperWidth A X →
      (∀ q ∈ P, lower q ≤ q) →
      (∀ q ∈ P,
        (∑ p ∈ primesIco (lower q) q, 1 / (p : ℝ)) ≤ 4 * mtPaperWidth A X) →
      0 ≤ B → MTFiniteFamilyDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖∑ k : Fin u, mtLemma23Error (α k)
            (mtLowerCutoffNat X) (mtTruncationNat X)
            (lowerSpill k) (upperSpill k) (S k) lower n‖ ^ 2 ≤
        25 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [
    eventually_sum_divisor_ternary_norm_sum_mtLemma23Error_fixedDilation_le_log_rpow
      A hA] with X hfirstX
  intro u α lowerSpill upperSpill S lower PLower PUpper P Y N B
    hY hYX hN hNX hLower hUpper hSP hprimeLower hprimeUpper hprime hPUpper
    hmassLower hmassUpper hlower hfibre hB hα
  have hsq := sum_norm_sq_sum_mtLemma23Error_le_five_mul_divisor_weighted
    α (mtLowerCutoffNat X) (mtTruncationNat X)
    lowerSpill upperSpill S lower Y hB hα
  have hfirst := hfirstX u α lowerSpill upperSpill S lower PLower PUpper P
    Y N B hY hYX hN hNX hLower hUpper hSP hprimeLower hprimeUpper hprime
    hPUpper hmassLower hmassUpper hlower hfibre hB hα
  calc
    _ ≤ 5 * B * ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖∑ k : Fin u, mtLemma23Error (α k)
            (mtLowerCutoffNat X) (mtTruncationNat X)
            (lowerSpill k) (upperSpill k) (S k) lower n‖ := hsq
    _ ≤ 5 * B *
        (5 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hfirst (mul_nonneg (by norm_num) hB)
    _ = _ := by ring

/-- Support and reciprocal-mass data sufficient for the rounded geometric schedule. -/
structure MTGridFreeDilationCertificate {t : ℕ}
    (data : MTFiniteIterationSourceData t) (A : ℕ) (X : ℝ) where
  lower : ℕ → ℕ
  PLower : Finset ℕ
  PUpper : Finset ℕ
  P : Finset ℕ
  N : ℕ
  z₀_eq : data.z₀ = mtLowerCutoffNat X
  D_eq : data.D = mtTruncationNat X
  lower_eq : ∀ k, data.lower k = lower
  lower_subset : ∀ k, data.lowerSpill k ⊆ PLower
  upper_subset : ∀ k, data.upperSpill k ⊆ PUpper
  prefix_subset : ∀ k, primesIco data.z₀ (data.cutoff k) ⊆ P
  lower_prime : ∀ q ∈ PLower, q.Prime
  upper_prime : ∀ q ∈ PUpper, q.Prime
  prime : ∀ q ∈ P, q.Prime
  N_one : 1 ≤ N
  N_le : (N : ℝ) ≤ X
  prime_le : ∀ q ∈ P, q ≤ N
  lower_mass : (∑ q ∈ PLower, 1 / (q : ℝ)) ≤ 4 * mtPaperWidth A X
  upper_mass : (∑ q ∈ PUpper, 1 / (q : ℝ)) ≤ 4 * mtPaperWidth A X
  lower_le : ∀ q ∈ P, lower q ≤ q
  fibre_mass : ∀ q ∈ P,
    (∑ p ∈ primesIco (lower q) q, 1 / (p : ℝ)) ≤ 4 * mtPaperWidth A X

/-- One rounded-geometric source layer has the paper-scale mean square. -/
theorem eventually_sum_norm_sq_mtLiteralSignedSourceErrorLayer_dilation_le
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (t : ℕ) (data : MTFiniteIterationSourceData t)
        (_cert : MTGridFreeDilationCertificate data A X)
        (a : ArithmeticFunction ℂ) (depth : ℕ) (j : Fin (t + 1))
        (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtLiteralSignedSourceErrorLayer data a depth j n‖ ^ 2 ≤
        25 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_norm_sq_sum_mtLemma23Error_fixedDilation_le_log_rpow
    A hA] with X hX
  intro t data _cert a depth j Y B hY hYX hB ha
  let α : Fin (t + 1) → ℕ → ℂ := fun k m =>
    mtTerminalCoefficientAF data a depth j k m
  have hα : MTFiniteFamilyDivisorBounded α B :=
    data.terminalCoefficient_familyDivisorBounded a B hB ha depth j
  have hstep := hX (t + 1) α data.lowerSpill data.upperSpill
    (fun k => primesIco data.z₀ (data.cutoff k)) _cert.lower
    _cert.PLower _cert.PUpper _cert.P Y _cert.N B
    hY hYX _cert.N_one _cert.N_le _cert.lower_subset _cert.upper_subset
    _cert.prefix_subset _cert.lower_prime _cert.upper_prime _cert.prime _cert.prime_le
    _cert.lower_mass _cert.upper_mass _cert.lower_le _cert.fibre_mass hB hα
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        ‖mtLiteralSignedSourceErrorLayer data a depth j n‖ ^ 2 =
      ∑ n ∈ Finset.Icc 1 Y,
        ‖∑ k : Fin (t + 1),
          mtLemma23Error (α k) data.z₀ data.D
            (data.lowerSpill k) (data.upperSpill k)
            (primesIco data.z₀ (data.cutoff k)) _cert.lower n‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hnIcc
      have hn : 0 < n := by
        rw [Finset.mem_Icc] at hnIcc
        omega
      rw [norm_mtLiteralSignedSourceErrorLayer_eq_norm_sum_mtLemma23Error
        data a depth j _cert.lower _cert.lower_eq hn]
    _ ≤ 25 * B ^ 2 * (Y : ℝ) *
        (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
      simpa only [_cert.z₀_eq, _cert.D_eq] using hstep

/-- Accumulating depth layers costs only the square of genuine recursion depth. -/
theorem eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_dilation_le
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (t : ℕ) (data : MTFiniteIterationSourceData t)
        (_cert : MTGridFreeDilationCertificate data A X)
        (a : ArithmeticFunction ℂ) (J : ℕ) (j : Fin (t + 1))
        (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data a J j n‖ ^ 2 ≤
        ((J + 1 : ℕ) : ℝ) ^ 2 *
          (25 * B ^ 2 * (Y : ℝ) *
            (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) := by
  filter_upwards [eventually_sum_norm_sq_mtLiteralSignedSourceErrorLayer_dilation_le
    A hA] with X hlayerX
  intro t data _cert a J j Y B hY hYX hB ha
  let C : ℝ := 25 * B ^ 2 * (Y : ℝ) *
    (Real.log X) ^ (-((3 * A : ℕ) : ℝ))
  have hlayer : ∀ layer ∈ Finset.range (J + 1),
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtLiteralSignedSourceErrorLayer data a layer j n‖ ^ 2 ≤ C := by
    intro layer hlayer
    exact hlayerX t data _cert a layer j Y B hY hYX hB ha
  have hpoint : ∀ n ∈ Finset.Icc 1 Y,
      ‖mtAccumulatedSourceErrorAF data a J j n‖ ^ 2 ≤
        ((J + 1 : ℕ) : ℝ) *
          ∑ layer ∈ Finset.range (J + 1),
            ‖mtLiteralSignedSourceErrorLayer data a layer j n‖ ^ 2 := by
    intro n hnIcc
    have hn : 0 < n := by
      rw [Finset.mem_Icc] at hnIcc
      omega
    rw [mtAccumulatedSourceErrorAF_eq_sum_signedLayers,
      arithmeticFunction_finset_sum_apply]
    have hsum :
        (∑ layer ∈ Finset.range (J + 1),
            mtSignedSourceErrorLayerAF data a layer j n) =
          ∑ layer ∈ Finset.range (J + 1),
            mtLiteralSignedSourceErrorLayer data a layer j n := by
      apply Finset.sum_congr rfl
      intro layer hlayer
      exact mtSignedSourceErrorLayerAF_apply_eq_literal data a layer j hn
    rw [hsum]
    simpa using norm_finset_sum_sq_le_card_mul_sum_sq_gridFree
      (Finset.range (J + 1))
      (fun layer => mtLiteralSignedSourceErrorLayer data a layer j n)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 Y,
        ((J + 1 : ℕ) : ℝ) *
          ∑ layer ∈ Finset.range (J + 1),
            ‖mtLiteralSignedSourceErrorLayer data a layer j n‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = ((J + 1 : ℕ) : ℝ) *
        ∑ layer ∈ Finset.range (J + 1), ∑ n ∈ Finset.Icc 1 Y,
          ‖mtLiteralSignedSourceErrorLayer data a layer j n‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
    _ ≤ ((J + 1 : ℕ) : ℝ) * ∑ _layer ∈ Finset.range (J + 1), C := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      exact Finset.sum_le_sum hlayer
    _ = ((J + 1 : ℕ) : ℝ) ^ 2 *
        (25 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) := by
      simp [C, Finset.sum_const, nsmul_eq_mul]
      ring

/-- Final rounded-geometric accumulated error after absorbing genuine recursion depth. -/
theorem eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_dilation_final
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (t : ℕ) (data : MTFiniteIterationSourceData t)
        (_cert : MTGridFreeDilationCertificate data A X)
        (a : ArithmeticFunction ℂ) (J : ℕ) (j : Fin (t + 1))
        (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → (J : ℝ) ≤ Real.log X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data a J j n‖ ^ 2 ≤
        25 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_dilation_le A hA,
    eventually_depth_sq_mul_log_rpow_neg_three_le_neg_two A hA]
      with X haccX habsorbX
  intro t data _cert a J j Y B hY hYX hJ hB ha
  have hacc := haccX t data _cert a J j Y B hY hYX hB ha
  have habsorb := habsorbX J hJ
  calc
    _ ≤ (((J + 1 : ℕ) : ℝ)) ^ 2 *
        (25 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) := hacc
    _ = 25 * B ^ 2 * (Y : ℝ) *
        ((((J + 1 : ℕ) : ℝ)) ^ 2 *
          (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) := by ring
    _ ≤ 25 * B ^ 2 * (Y : ℝ) *
        (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left habsorb (by positivity)

/-- Exact terminal depth version of the rounded-geometric accumulated error theorem. -/
theorem eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_at_logDepth_dilation
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (t : ℕ) (data : MTFiniteIterationSourceData t)
        (_cert : MTGridFreeDilationCertificate data A X)
        (a : ArithmeticFunction ℂ) (j : Fin (t + 1))
        (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B) →
      let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data a J j n‖ ^ 2 ≤
        25 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_dilation_final A hA,
    eventually_mtLogDepth_le_log] with X hfinalX hdepthX
  intro t data _cert a j Y B hY hYX hB ha
  dsimp only
  have hdepth := hdepthX Y hY hYX
  have hdepthData :
      ((Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ)) : ℕ) : ℝ) ≤
        Real.log X := by
    simpa only [_cert.z₀_eq] using hdepth
  exact hfinalX t data _cert a
    (Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))) j Y B
    hY hYX hdepthData hB ha

end

end RHTower.Sieve
