import GaloisForLFunctions.RHTower.CCMGuinandWeilPrimeEntryThirdJetTransverse

/-!
# Finite positive connection of prime-entry third jets

Every prime-entry third jet found in the preceding module is a positive arithmetic scale times one
universal cubic Loewner matrix.  This file aggregates arbitrary finite event packets and arbitrary
atom-dependent scalar dressings.

Nonnegative dressing preserves the universal centered square law.  If one positively dressed event
is a genuine prime power, the arithmetic rate and every nonzero first-clock-moment quadratic are
strictly positive.  The literal visible cutoff therefore defines an unconditional positive
semidefinite third-jet connection on the zero-sum coefficient sector at every aperture.
-/

open scoped BigOperators

namespace RHTower

open Matrix

noncomputable section

/-- Universal cubic Loewner direction shared by every prime-entry third jet. -/
def ccmGuinandWeilPrimeEntryUniversalThirdJet (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  fun i j => 2 * Real.pi ^ 2 *
    (ccmPublishedCenteredClock N i ^ 2 +
      ccmPublishedCenteredClock N i * ccmPublishedCenteredClock N j +
      ccmPublishedCenteredClock N j ^ 2) - 3

/-- Each arithmetic third jet is its positive scalar scale times the universal Loewner direction. -/
theorem ccmGuinandWeilPrimeEntryCenteredMatrixJet3_eq_scale_smul
    {k : ℕ} (hk : 1 < k) (N : ℕ) :
    ccmGuinandWeilPrimeEntryCenteredMatrixJet3 k N =
      ccmGuinandWeilPrimeEntryThirdJetScale k •
        ccmGuinandWeilPrimeEntryUniversalThirdJet N := by
  ext i j
  rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3_apply hk]
  rfl

/-- Total arithmetic third-jet rate after arbitrary atomwise dressing. -/
def ccmGuinandWeilPrimeEntryDressedThirdJetRate
    (dressing : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ k ∈ S, dressing k * ccmGuinandWeilPrimeEntryThirdJetScale k

/-- Finite matrix-valued third-jet connection after arbitrary atomwise dressing. -/
def ccmGuinandWeilPrimeEntryDressedThirdJet
    (dressing : ℕ → ℝ) (S : Finset ℕ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ∑ k ∈ S, dressing k • ccmGuinandWeilPrimeEntryCenteredMatrixJet3 k N

/-- **Finite third-jet connection factorization.** Every dressed packet retains one universal cubic
Loewner direction. -/
theorem ccmGuinandWeilPrimeEntryDressedThirdJet_eq_rate_smul
    (dressing : ℕ → ℝ) {S : Finset ℕ} (hS : ∀ k ∈ S, 1 < k) (N : ℕ) :
    ccmGuinandWeilPrimeEntryDressedThirdJet dressing S N =
      ccmGuinandWeilPrimeEntryDressedThirdJetRate dressing S •
        ccmGuinandWeilPrimeEntryUniversalThirdJet N := by
  rw [ccmGuinandWeilPrimeEntryDressedThirdJet,
    ccmGuinandWeilPrimeEntryDressedThirdJetRate]
  calc
    (∑ k ∈ S, dressing k • ccmGuinandWeilPrimeEntryCenteredMatrixJet3 k N) =
        ∑ k ∈ S, (dressing k * ccmGuinandWeilPrimeEntryThirdJetScale k) •
          ccmGuinandWeilPrimeEntryUniversalThirdJet N := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [ccmGuinandWeilPrimeEntryCenteredMatrixJet3_eq_scale_smul (hS k hk),
        smul_smul]
    _ = _ := by rw [Finset.sum_smul]

/-- Every index above one has nonnegative third-jet scale. -/
theorem ccmGuinandWeilPrimeEntryThirdJetScale_nonneg
    {k : ℕ} (hk : 1 < k) :
    0 ≤ ccmGuinandWeilPrimeEntryThirdJetScale k := by
  rw [ccmGuinandWeilPrimeEntryThirdJetScale]
  have hw : 0 ≤ criticalMellinAtomWeight k := by
    rw [criticalMellinAtomWeight]
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _)
      ArithmeticFunction.vonMangoldt_nonneg
  have hlog : 0 < Real.log k := Real.log_pos (by exact_mod_cast hk)
  exact div_nonneg (mul_nonneg (by norm_num) hw) (pow_nonneg hlog.le 3)

/-- Nonnegative dressing with one active prime power gives strictly positive total rate. -/
theorem ccmGuinandWeilPrimeEntryDressedThirdJetRate_pos
    {dressing : ℕ → ℝ} {S : Finset ℕ}
    (hS : ∀ k ∈ S, 1 < k) (hdressing : ∀ k ∈ S, 0 ≤ dressing k)
    (hactive : ∃ k ∈ S, IsPrimePow k ∧ 0 < dressing k) :
    0 < ccmGuinandWeilPrimeEntryDressedThirdJetRate dressing S := by
  rw [ccmGuinandWeilPrimeEntryDressedThirdJetRate]
  have hlt : (∑ _k ∈ S, (0 : ℝ)) <
      ∑ k ∈ S, dressing k * ccmGuinandWeilPrimeEntryThirdJetScale k := by
    apply Finset.sum_lt_sum
    · intro k hk
      exact mul_nonneg (hdressing k hk)
        (ccmGuinandWeilPrimeEntryThirdJetScale_nonneg (hS k hk))
    · obtain ⟨k, hk, hkpow, hdresspos⟩ := hactive
      exact ⟨k, hk, mul_pos hdresspos
        (ccmGuinandWeilPrimeEntryThirdJetScale_pos hkpow)⟩
  simpa using hlt

/-- Exact outer-product decomposition of the universal cubic Loewner direction. -/
theorem ccmGuinandWeilPrimeEntryUniversalThirdJet_eq_outerProducts
    (N : ℕ) :
    ccmGuinandWeilPrimeEntryUniversalThirdJet N =
      (2 * Real.pi ^ 2) •
          Matrix.vecMulVec
            (fun i : Fin (2 * N + 1) => ccmPublishedCenteredClock N i ^ 2)
            ccmConstantBoundary +
        (2 * Real.pi ^ 2) •
          Matrix.vecMulVec (ccmPublishedCenteredClock N)
            (ccmPublishedCenteredClock N) +
        (2 * Real.pi ^ 2) •
          Matrix.vecMulVec ccmConstantBoundary
            (fun i : Fin (2 * N + 1) => ccmPublishedCenteredClock N i ^ 2) -
        (3 : ℝ) • Matrix.vecMulVec ccmConstantBoundary ccmConstantBoundary := by
  ext i j
  simp [ccmGuinandWeilPrimeEntryUniversalThirdJet,
    Matrix.vecMulVec_apply, ccmConstantBoundary]
  ring

/-- Universal centered square law: only the first clock moment survives. -/
theorem ccmGuinandWeilPrimeEntryUniversalThirdJet_quadratic_of_sum_eq_zero
    (N : ℕ) (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0) :
    dotProduct v (ccmGuinandWeilPrimeEntryUniversalThirdJet N *ᵥ v) =
      2 * Real.pi ^ 2 *
        (∑ i, ccmPublishedCenteredClock N i * v i) ^ 2 := by
  rw [ccmGuinandWeilPrimeEntryUniversalThirdJet_eq_outerProducts]
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, dotProduct, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [ccmConstantBoundary, one_mul]
  rw [hv]
  simp
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have hfirst :
      (∑ x, v x *
        (2 * Real.pi ^ 2 *
          (ccmPublishedCenteredClock N x *
            ∑ i, ccmPublishedCenteredClock N i * v i))) =
        (2 * Real.pi ^ 2) *
          (∑ i, ccmPublishedCenteredClock N i * v i) *
            (∑ x, v x * ccmPublishedCenteredClock N x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hsecond :
      (∑ x, v x *
        (2 * Real.pi ^ 2 *
          ∑ x, ccmPublishedCenteredClock N x ^ 2 * v x)) =
        (2 * Real.pi ^ 2) *
          (∑ x, ccmPublishedCenteredClock N x ^ 2 * v x) *
            (∑ x, v x) := by
    calc
      (∑ x, v x *
          (2 * Real.pi ^ 2 *
            ∑ x, ccmPublishedCenteredClock N x ^ 2 * v x)) =
          (∑ x, v x) *
            (2 * Real.pi ^ 2 *
              ∑ x, ccmPublishedCenteredClock N x ^ 2 * v x) :=
        (Finset.sum_mul Finset.univ (fun x => v x)
          (2 * Real.pi ^ 2 *
            ∑ x, ccmPublishedCenteredClock N x ^ 2 * v x)).symm
      _ = _ := by ring
  rw [hfirst, hsecond, hv]
  simp
  have hcomm : (∑ x, v x * ccmPublishedCenteredClock N x) =
      ∑ x, ccmPublishedCenteredClock N x * v x := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hcomm]
  ring

/-- Exact centered quadratic form of every finite dressed third-jet connection. -/
theorem ccmGuinandWeilPrimeEntryDressedThirdJet_quadratic_of_sum_eq_zero
    (dressing : ℕ → ℝ) {S : Finset ℕ} (hS : ∀ k ∈ S, 1 < k)
    (N : ℕ) (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0) :
    dotProduct v
        (ccmGuinandWeilPrimeEntryDressedThirdJet dressing S N *ᵥ v) =
      2 * Real.pi ^ 2 *
        ccmGuinandWeilPrimeEntryDressedThirdJetRate dressing S *
          (∑ i, ccmPublishedCenteredClock N i * v i) ^ 2 := by
  rw [ccmGuinandWeilPrimeEntryDressedThirdJet_eq_rate_smul dressing hS]
  rw [Matrix.smul_mulVec]
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  have hfactor :
      (∑ x, v x *
        (ccmGuinandWeilPrimeEntryDressedThirdJetRate dressing S *
          (ccmGuinandWeilPrimeEntryUniversalThirdJet N *ᵥ v) x)) =
        ccmGuinandWeilPrimeEntryDressedThirdJetRate dressing S *
          dotProduct v
            (ccmGuinandWeilPrimeEntryUniversalThirdJet N *ᵥ v) := by
    simp only [dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hfactor]
  rw [ccmGuinandWeilPrimeEntryUniversalThirdJet_quadratic_of_sum_eq_zero N v hv]
  ring

/-- Nonnegative atomwise dressing gives a positive-semidefinite centered third-jet connection. -/
theorem ccmGuinandWeilPrimeEntryDressedThirdJet_quadratic_nonneg_of_sum_eq_zero
    {dressing : ℕ → ℝ} {S : Finset ℕ}
    (hS : ∀ k ∈ S, 1 < k) (hdressing : ∀ k ∈ S, 0 ≤ dressing k)
    (N : ℕ) (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0) :
    0 ≤ dotProduct v
      (ccmGuinandWeilPrimeEntryDressedThirdJet dressing S N *ᵥ v) := by
  rw [ccmGuinandWeilPrimeEntryDressedThirdJet_quadratic_of_sum_eq_zero
    dressing hS N v hv]
  have hrate : 0 ≤ ccmGuinandWeilPrimeEntryDressedThirdJetRate dressing S := by
    rw [ccmGuinandWeilPrimeEntryDressedThirdJetRate]
    exact Finset.sum_nonneg fun k hk => mul_nonneg (hdressing k hk)
      (ccmGuinandWeilPrimeEntryThirdJetScale_nonneg (hS k hk))
  positivity

/-- With one active prime power, positivity is strict on every visible first-clock moment. -/
theorem ccmGuinandWeilPrimeEntryDressedThirdJet_quadratic_pos_of_sum_eq_zero
    {dressing : ℕ → ℝ} {S : Finset ℕ}
    (hS : ∀ k ∈ S, 1 < k) (hdressing : ∀ k ∈ S, 0 ≤ dressing k)
    (hactive : ∃ k ∈ S, IsPrimePow k ∧ 0 < dressing k)
    (N : ℕ) (v : Fin (2 * N + 1) → ℝ) (hv : ∑ i, v i = 0)
    (hmoment : (∑ i, ccmPublishedCenteredClock N i * v i) ≠ 0) :
    0 < dotProduct v
      (ccmGuinandWeilPrimeEntryDressedThirdJet dressing S N *ᵥ v) := by
  rw [ccmGuinandWeilPrimeEntryDressedThirdJet_quadratic_of_sum_eq_zero
    dressing hS N v hv]
  have hrate := ccmGuinandWeilPrimeEntryDressedThirdJetRate_pos
    hS hdressing hactive
  positivity

/-- Literal third-jet connection over every index visible at aperture `a`. -/
def ccmGuinandWeilVisiblePrimeEntryThirdJet (a : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℝ :=
  ccmGuinandWeilPrimeEntryDressedThirdJet (fun _ => 1)
    (Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊) N

/-- Literal visible third-jet connection is unconditionally positive semidefinite on every
zero-sum coefficient packet. -/
theorem ccmGuinandWeilVisiblePrimeEntryThirdJet_quadratic_nonneg_of_sum_eq_zero
    (a : ℝ) (N : ℕ) (v : Fin (2 * N + 1) → ℝ)
    (hv : ∑ i, v i = 0) :
    0 ≤ dotProduct v (ccmGuinandWeilVisiblePrimeEntryThirdJet a N *ᵥ v) := by
  rw [ccmGuinandWeilVisiblePrimeEntryThirdJet]
  apply ccmGuinandWeilPrimeEntryDressedThirdJet_quadratic_nonneg_of_sum_eq_zero
  · intro k hk
    have hk2 := (Finset.mem_Icc.mp hk).1
    omega
  · intro k hk
    norm_num
  · exact hv

end

end RHTower
