import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenGridFreeError
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma23IDivisorBoundedPaperScale

/-!
# Paper-scale grid-free Matomäki--Teräväinen error bound

All terminal fibres are estimated jointly.  Endpoint supports contribute only their total
reciprocal masses; Buchstab prefixes contribute one global narrow same-block pair family.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

/-- The common truncation term of a terminal family has the divisor-bounded paper saving. -/
theorem eventually_sum_divisor_ternary_norm_sum_mtC1_le_log_rpow
    (A : ℕ) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (u : ℕ) (α : Fin u → ℕ → ℂ) (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B → MTFiniteFamilyDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u,
              mtC1Coefficient (α k) (mtLowerCutoffNat X) (mtTruncationNat X) n‖ ≤
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_divisor_ternary_norm_mtC1_le_log_rpow A]
    with X hX
  intro u α Y B hY hYX hB hα
  have h := hX (fun m => ∑ k : Fin u, α k m) Y B hY hYX hB hα.sum
  simpa only [sum_mtC1Coefficient_eq] using h

/-- Varying endpoint families have one paper-scale bound when their total lower and upper
reciprocal masses each fit one paper-width budget. -/
theorem eventually_sum_divisor_ternary_norm_sum_mtC2_le_log_rpow
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (u : ℕ) (α : Fin u → ℕ → ℂ)
        (lowerSpill upperSpill : Fin u → Finset ℕ)
        (level : Fin u → ℕ → ℕ) (PLower PUpper : Finset ℕ)
        (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      (∀ k, lowerSpill k ⊆ PLower) → (∀ k, upperSpill k ⊆ PUpper) →
      (∀ q ∈ PLower, q.Prime) → (∀ q ∈ PUpper, q.Prime) →
      (∑ q ∈ PLower, 1 / (q : ℝ)) ≤ 2 * mtPaperWidth A X →
      (∑ q ∈ PUpper, 1 / (q : ℝ)) ≤ 2 * mtPaperWidth A X →
      0 ≤ B → MTFiniteFamilyDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u,
              mtC2Coefficient (α k) (lowerSpill k) (upperSpill k) (level k) n‖ ≤
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
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
        C * (4 * mtPaperWidth A X) := by
    rw [Finset.sum_add_distrib]
    calc
      _ ≤ C * (∑ q ∈ PLower, 1 / (q : ℝ)) +
          C * ∑ q ∈ PUpper, 1 / (q : ℝ) :=
        add_le_add hmeanLower hmeanUpper
      _ = C * ((∑ q ∈ PLower, 1 / (q : ℝ)) +
          ∑ q ∈ PUpper, 1 / (q : ℝ)) := by ring
      _ ≤ C * (4 * mtPaperWidth A X) := by
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
          (4 * mtPaperWidth A X) ≤
        (4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (1 : ℝ)) := by
    norm_num [Real.log_one]
    have hbase : 0 ≤ 1 + Real.log (Y : ℝ) := by linarith
    have hpoly : 0 ≤ (1 + Real.log (Y : ℝ)) ^ 31 := pow_nonneg hbase _
    nlinarith [mul_nonneg hpoly hwidth]
  calc
    _ ≤ B * ∑ n ∈ Finset.Icc 1 Y,
        (weightedPrimeDivisorCount 5 PLower n +
          weightedPrimeDivisorCount 5 PUpper n) := hpoint
    _ ≤ B * (C * (4 * mtPaperWidth A X)) :=
      mul_le_mul_of_nonneg_left hweighted hB
    _ = B * (Y : ℝ) *
        ((2 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (4 * mtPaperWidth A X)) := by
      dsimp [C]
      ring
    _ ≤ B * (Y : ℝ) *
        ((4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log (1 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hcompare
        (mul_nonneg hB (Nat.cast_nonneg _))
    _ ≤ B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hB (Nat.cast_nonneg _))
      simpa only [Nat.cast_one] using hscalar

/-- Varying terminal prefixes contribute only one global narrow same-block pair family. -/
theorem eventually_sum_divisor_ternary_norm_sum_mtC3_le_log_rpow
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (u : ℕ) (α : Fin u → ℕ → ℂ) (S : Fin u → Finset ℕ)
        (P : Finset ℕ) (lower : ℕ → ℕ) (Y N : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ N → (N : ℝ) ≤ X →
      (∀ k, S k ⊆ P) → (∀ q ∈ P, q.Prime) → (∀ q ∈ P, q ≤ N) →
      (∀ q ∈ P,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ P, lower q ≤ q) →
      (∀ q ∈ P, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      0 ≤ B → MTFiniteFamilyDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u, mtC3Coefficient (α k) (S k) lower n‖ ≤
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_lowerC3FibreMass_paperWidth A,
    eventually_mt_fifthMoment_width_absorption A hA] with X hmassX habsorbX
  intro u α S P lower Y N B hY hYX hN hNX hSP hprime hupper
    hlowerCut hlower hband hB hα
  have hpairPrime : ∀ q ∈ P, ∀ p ∈ primesIco (lower q) q, p.Prime := by
    intro q hq p hp
    exact (mem_primesIco.mp hp).2.2
  have hfibre := hmassX P lower hlowerCut hlower hband
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
      (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) * (2 * mtPaperWidth A X) := by
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
          (2 * mtPaperWidth A X) * ∑ q ∈ P, 1 / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hweighted hB
    _ ≤ B * ((4 : ℝ) ^ 5 * (Y : ℝ) *
        (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log N)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left houter hfactor0) hB
    _ = B * (Y : ℝ) *
        ((4 : ℝ) ^ 5 * (1 + Real.log (Y : ℝ)) ^ (2 ^ 5 - 1) *
          (2 * mtPaperWidth A X) * (1 + Real.log N)) := by ring
    _ ≤ B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hscalar (mul_nonneg hB (Nat.cast_nonneg _))

/-- Joint first moment for the complete grid-free terminal error family. -/
theorem eventually_sum_divisor_ternary_norm_sum_mtLemma23Error_le_log_rpow
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
      (∑ q ∈ PLower, 1 / (q : ℝ)) ≤ 2 * mtPaperWidth A X →
      (∑ q ∈ PUpper, 1 / (q : ℝ)) ≤ 2 * mtPaperWidth A X →
      (∀ q ∈ P,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ P, lower q ≤ q) →
      (∀ q ∈ P, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      0 ≤ B → MTFiniteFamilyDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
            ‖∑ k : Fin u, mtLemma23Error (α k)
              (mtLowerCutoffNat X) (mtTruncationNat X)
              (lowerSpill k) (upperSpill k) (S k) lower n‖ ≤
        3 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_divisor_ternary_norm_sum_mtC1_le_log_rpow A,
    eventually_sum_divisor_ternary_norm_sum_mtC2_le_log_rpow A hA,
    eventually_sum_divisor_ternary_norm_sum_mtC3_le_log_rpow A hA]
    with X hc1X hc2X hc3X
  intro u α lowerSpill upperSpill S lower PLower PUpper P Y N B
    hY hYX hN hNX hLower hUpper hSP hprimeLower hprimeUpper hprime hPUpper
    hmassLower hmassUpper hlowerCut hlower hband hB hα
  have hc1 := hc1X u α Y B hY hYX hB hα
  have hc2 := hc2X u α lowerSpill upperSpill (fun _ => lower)
    PLower PUpper Y B hY hYX hLower hUpper hprimeLower hprimeUpper
    hmassLower hmassUpper hB hα
  have hc3 := hc3X u α S P lower Y N B hY hYX hN hNX hSP hprime hPUpper
    hlowerCut hlower hband hB hα
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
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) +
        B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) :=
      add_le_add (add_le_add hc1 hc2) hc3
    _ = _ := by ring

/-- Grid-free terminal error mean square: no factor involving adic-grid cardinality. -/
theorem eventually_sum_norm_sq_sum_mtLemma23Error_le_log_rpow
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
      (∑ q ∈ PLower, 1 / (q : ℝ)) ≤ 2 * mtPaperWidth A X →
      (∑ q ∈ PUpper, 1 / (q : ℝ)) ≤ 2 * mtPaperWidth A X →
      (∀ q ∈ P,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ P, lower q ≤ q) →
      (∀ q ∈ P, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      0 ≤ B → MTFiniteFamilyDivisorBounded α B →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖∑ k : Fin u, mtLemma23Error (α k)
            (mtLowerCutoffNat X) (mtTruncationNat X)
            (lowerSpill k) (upperSpill k) (S k) lower n‖ ^ 2 ≤
        15 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [
    eventually_sum_divisor_ternary_norm_sum_mtLemma23Error_le_log_rpow A hA]
    with X hfirstX
  intro u α lowerSpill upperSpill S lower PLower PUpper P Y N B
    hY hYX hN hNX hLower hUpper hSP hprimeLower hprimeUpper hprime hPUpper
    hmassLower hmassUpper hlowerCut hlower hband hB hα
  have hsq := sum_norm_sq_sum_mtLemma23Error_le_five_mul_divisor_weighted
    α (mtLowerCutoffNat X) (mtTruncationNat X)
    lowerSpill upperSpill S lower Y hB hα
  have hfirst := hfirstX u α lowerSpill upperSpill S lower PLower PUpper P
    Y N B hY hYX hN hNX hLower hUpper hSP hprimeLower hprimeUpper hprime
    hPUpper hmassLower hmassUpper hlowerCut hlower hband hB hα
  calc
    _ ≤ 5 * B * ∑ n ∈ Finset.Icc 1 Y,
        (n.divisors.card : ℝ) * (ternaryDivisorCount n : ℝ) *
          ‖∑ k : Fin u, mtLemma23Error (α k)
            (mtLowerCutoffNat X) (mtTruncationNat X)
            (lowerSpill k) (upperSpill k) (S k) lower n‖ := hsq
    _ ≤ 5 * B *
        (3 * B * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hfirst (mul_nonneg (by norm_num) hB)
    _ = _ := by ring

/-- Global support geometry sufficient to estimate every terminal cutoff jointly. -/
structure MTGridFreePaperScaleCertificate {t : ℕ}
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
  lower_mass : (∑ q ∈ PLower, 1 / (q : ℝ)) ≤ 2 * mtPaperWidth A X
  upper_mass : (∑ q ∈ PUpper, 1 / (q : ℝ)) ≤ 2 * mtPaperWidth A X
  lower_cut : ∀ q ∈ P,
    mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)
  lower_le : ∀ q ∈ P, lower q ≤ q
  band : ∀ q ∈ P, ((q - 1 : ℕ) : ℝ) ≤
    (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)

/-- One literal source layer has paper-scale mean square with no adic-grid cardinality. -/
theorem eventually_sum_norm_sq_mtLiteralSignedSourceErrorLayer_gridFree_le
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (t : ℕ) (data : MTFiniteIterationSourceData t)
        (_cert : MTGridFreePaperScaleCertificate data A X)
        (a : ArithmeticFunction ℂ) (depth : ℕ) (j : Fin (t + 1))
        (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtLiteralSignedSourceErrorLayer data a depth j n‖ ^ 2 ≤
        15 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_norm_sq_sum_mtLemma23Error_le_log_rpow A hA]
    with X hX
  intro t data _cert a depth j Y B hY hYX hB ha
  let α : Fin (t + 1) → ℕ → ℂ := fun k m =>
    mtTerminalCoefficientAF data a depth j k m
  have hα : MTFiniteFamilyDivisorBounded α B :=
    data.terminalCoefficient_familyDivisorBounded a B hB ha depth j
  have hstep := hX (t + 1) α
    data.lowerSpill data.upperSpill
    (fun k => primesIco data.z₀ (data.cutoff k)) _cert.lower
    _cert.PLower _cert.PUpper _cert.P Y _cert.N B
    hY hYX _cert.N_one _cert.N_le _cert.lower_subset _cert.upper_subset
    _cert.prefix_subset _cert.lower_prime _cert.upper_prime _cert.prime _cert.prime_le
    _cert.lower_mass _cert.upper_mass _cert.lower_cut _cert.lower_le _cert.band hB hα
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
    _ ≤ 15 * B ^ 2 * (Y : ℝ) *
        (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
      simpa only [_cert.z₀_eq, _cert.D_eq] using hstep

/-- Finite Cauchy--Schwarz used only across genuine iteration depths. -/
theorem norm_finset_sum_sq_le_card_mul_sum_sq_gridFree
    {ι : Type*} (S : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ S, f i‖ ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, ‖f i‖ ^ 2 := by
  have hnorm : ‖∑ i ∈ S, f i‖ ≤ ∑ i ∈ S, ‖f i‖ := norm_sum_le _ _
  have hsum0 : 0 ≤ ∑ i ∈ S, ‖f i‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hcauchy : (∑ i ∈ S, ‖f i‖) ^ 2 ≤
      (S.card : ℝ) * ∑ i ∈ S, ‖f i‖ ^ 2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := S) (f := fun i => ‖f i‖))
  nlinarith [norm_nonneg (∑ i ∈ S, f i)]

/-- The exact accumulated error pays only the square of genuine Buchstab depth, never the number
of adic blocks. -/
theorem eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_gridFree_le
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (t : ℕ) (data : MTFiniteIterationSourceData t)
        (_cert : MTGridFreePaperScaleCertificate data A X)
        (a : ArithmeticFunction ℂ) (J : ℕ) (j : Fin (t + 1))
        (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data a J j n‖ ^ 2 ≤
        ((J + 1 : ℕ) : ℝ) ^ 2 *
          (15 * B ^ 2 * (Y : ℝ) *
            (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) := by
  filter_upwards [eventually_sum_norm_sq_mtLiteralSignedSourceErrorLayer_gridFree_le A hA]
    with X hlayerX
  intro t data _cert a J j Y B hY hYX hB ha
  let C : ℝ := 15 * B ^ 2 * (Y : ℝ) *
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
        (15 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) := by
      simp [C, Finset.sum_const, nsmul_eq_mul]
      ring

/-- Any depth below `log X` has enough room to absorb its Cauchy square from exponent `-3A` to
`-2A`. -/
theorem eventually_depth_sq_mul_log_rpow_neg_three_le_neg_two
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop, ∀ J : ℕ,
      (J : ℝ) ≤ Real.log X →
      ((J + 1 : ℕ) : ℝ) ^ 2 *
          (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) ≤
        (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  have htwoA : (2 : ℝ) < (A : ℝ) := by exact_mod_cast (by omega : 2 < A)
  have hpoly := eventually_const_mul_rpow_polylog_le_rpow
    (C := (4 : ℝ)) (α := (2 : ℝ)) (β := (A : ℝ)) 0 htwoA
  have hpolyX := Real.tendsto_log_atTop.eventually hpoly
  filter_upwards [hpolyX, Filter.eventually_ge_atTop (Real.exp 1)] with X hpolyX hX
  intro J hJ
  have hL1 : 1 ≤ Real.log X := by
    have hmono := Real.log_le_log (Real.exp_pos 1) hX
    simpa only [Real.log_exp] using hmono
  have hL : 0 < Real.log X := lt_of_lt_of_le zero_lt_one hL1
  have hJ1 : (((J + 1 : ℕ) : ℝ)) ≤ 2 * Real.log X := by
    push_cast
    linarith
  have hsq : (((J + 1 : ℕ) : ℝ)) ^ 2 ≤ 4 * (Real.log X) ^ 2 := by
    nlinarith
  have hpow : 4 * (Real.log X) ^ 2 ≤ (Real.log X) ^ (A : ℝ) := by
    simpa [Real.rpow_two] using hpolyX
  have hmain : (((J + 1 : ℕ) : ℝ)) ^ 2 ≤
      (Real.log X) ^ (A : ℝ) := hsq.trans hpow
  calc
    (((J + 1 : ℕ) : ℝ)) ^ 2 *
        (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) ≤
      (Real.log X) ^ (A : ℝ) *
        (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg hL.le _)
    _ = (Real.log X) ^ ((A : ℝ) + (-((3 * A : ℕ) : ℝ))) := by
      rw [← Real.rpow_add hL]
    _ = (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
      congr 1
      push_cast
      ring

/-- Final accumulated-error saving once genuine Buchstab depth is bounded by `log X`. -/
theorem eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_gridFree_final
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (t : ℕ) (data : MTFiniteIterationSourceData t)
        (_cert : MTGridFreePaperScaleCertificate data A X)
        (a : ArithmeticFunction ℂ) (J : ℕ) (j : Fin (t + 1))
        (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → (J : ℝ) ≤ Real.log X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data a J j n‖ ^ 2 ≤
        15 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_gridFree_le A hA,
    eventually_depth_sq_mul_log_rpow_neg_three_le_neg_two A hA]
    with X haccX habsorbX
  intro t data _cert a J j Y B hY hYX hJ hB ha
  have hacc := haccX t data _cert a J j Y B hY hYX hB ha
  have habsorb := habsorbX J hJ
  calc
    _ ≤ (((J + 1 : ℕ) : ℝ)) ^ 2 *
        (15 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) := hacc
    _ = 15 * B ^ 2 * (Y : ℝ) *
        ((((J + 1 : ℕ) : ℝ)) ^ 2 *
          (Real.log X) ^ (-((3 * A : ℕ) : ℝ))) := by ring
    _ ≤ 15 * B ^ 2 * (Y : ℝ) *
        (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left habsorb (by positivity)

/-- Natural lower cutoff inherits the real lower-cutoff logarithm. -/
theorem mtLowerLogCutoff_le_log_mtLowerCutoffNat (X : ℝ) :
    mtLowerLogCutoff X ≤ Real.log (mtLowerCutoffNat X : ℝ) := by
  have hcut : 0 < mtLowerCutoff X := by
    rw [mtLowerCutoff]
    exact Real.exp_pos _
  have hceil : mtLowerCutoff X ≤ (mtLowerCutoffNat X : ℝ) := by
    exact Nat.le_ceil _
  have hlog := Real.log_le_log hcut hceil
  rw [mtLowerCutoff, Real.log_exp] at hlog
  exact hlog

/-- Terminal depth `⌊log Y / log z₀⌋` is eventually below `log X`, uniformly for `Y ≤ 4X`. -/
theorem eventually_mtLogDepth_le_log :
    ∀ᶠ X : ℝ in atTop, ∀ Y : ℕ,
      1 ≤ Y → (Y : ℝ) ≤ 4 * X →
      ((Nat.floor (Real.log (Y : ℝ) /
        Real.log (mtLowerCutoffNat X : ℝ)) : ℕ) : ℝ) ≤ Real.log X := by
  have hcut := tendsto_mtLowerLogCutoff_atTop.eventually_ge_atTop 2
  filter_upwards [hcut, Filter.eventually_ge_atTop 4] with X hcutX hX
  intro Y hY hYX
  have hlogzTwo : 2 ≤ Real.log (mtLowerCutoffNat X : ℝ) :=
    hcutX.trans (mtLowerLogCutoff_le_log_mtLowerCutoffNat X)
  have hlogz : 0 < Real.log (mtLowerCutoffNat X : ℝ) := by linarith
  have hlogY0 : 0 ≤ Real.log (Y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hY)
  have hratio0 : 0 ≤ Real.log (Y : ℝ) /
      Real.log (mtLowerCutoffNat X : ℝ) := div_nonneg hlogY0 hlogz.le
  have hfloor :
      ((Nat.floor (Real.log (Y : ℝ) /
        Real.log (mtLowerCutoffNat X : ℝ)) : ℕ) : ℝ) ≤
          Real.log (Y : ℝ) / Real.log (mtLowerCutoffNat X : ℝ) :=
    Nat.floor_le hratio0
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hYpos : (0 : ℝ) < Y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hY)
  have hlogY : Real.log (Y : ℝ) ≤ Real.log 4 + Real.log X := by
    have hmono := Real.log_le_log hYpos hYX
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hXpos.ne'] at hmono
    exact hmono
  have hlog4 : Real.log 4 ≤ Real.log X :=
    Real.log_le_log (by norm_num) hX
  have hratio : Real.log (Y : ℝ) /
      Real.log (mtLowerCutoffNat X : ℝ) ≤ Real.log X := by
    apply (div_le_iff₀ hlogz).2
    nlinarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  exact hfloor.trans hratio

/-- Repaired Lemma 2.3(ii) error estimate at exact terminal depth, conditional only on the concrete
global support certificate for the chosen block schedule. -/
theorem eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_at_logDepth_gridFree
    (A : ℕ) (hA : 5 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (t : ℕ) (data : MTFiniteIterationSourceData t)
        (_cert : MTGridFreePaperScaleCertificate data A X)
        (a : ArithmeticFunction ℂ) (j : Fin (t + 1))
        (Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 0 ≤ B →
      (∀ {m : ℕ}, 0 < m → ‖a m‖ ≤ B) →
      let J := Nat.floor (Real.log (Y : ℝ) / Real.log (data.z₀ : ℝ))
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtAccumulatedSourceErrorAF data a J j n‖ ^ 2 ≤
        15 * B ^ 2 * (Y : ℝ) *
          (Real.log X) ^ (-((2 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_norm_sq_mtAccumulatedSourceErrorAF_gridFree_final A hA,
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
