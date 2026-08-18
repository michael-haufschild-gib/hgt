import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIIAmplitudeCells
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIISparseHalaszMontgomery

namespace RHTower.Sieve

/-- Exact finite-set form of the `T₃` estimate, before absorbing cardinality and coefficient size. -/
theorem matomakiTeravainen_typeII_T3_energy
    {α : Type*} {S : Finset α} {F₁ F₂ : α → ℝ} {T B : ℝ}
    (hT : 0 < T)
    (hF₁0 : ∀ q ∈ S, 0 ≤ F₁ q) (hF₂0 : ∀ q ∈ S, 0 ≤ F₂ q)
    (hF₁B : ∀ q ∈ S, F₁ q ≤ B) (hF₂B : ∀ q ∈ S, F₂ q ≤ B)
    (hsmall : ∀ q ∈ S, F₁ q ≤ T ^ (-(1 : ℝ)) ∨ F₂ q ≤ T ^ (-(1 : ℝ))) :
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤
      (S.card : ℝ) * T ^ (-(2 : ℝ)) * B ^ 2 := by
  classical
  have hTinv0 : 0 ≤ T ^ (-(1 : ℝ)) := by positivity
  have hpoint : ∀ q ∈ S,
      F₁ q ^ 2 * F₂ q ^ 2 ≤ T ^ (-(2 : ℝ)) * B ^ 2 := by
    intro q hq
    have hB1 : F₁ q ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (hF₁0 q hq) (hF₁B q hq) 2
    have hB2 : F₂ q ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (hF₂0 q hq) (hF₂B q hq) 2
    have hinv_sq : (T ^ (-(1 : ℝ))) ^ 2 = T ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
      congr 1
      norm_num
    rcases hsmall q hq with hsmall1 | hsmall2
    · have hs1 : F₁ q ^ 2 ≤ (T ^ (-(1 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (hF₁0 q hq) hsmall1 2
      rw [hinv_sq] at hs1
      exact mul_le_mul hs1 hB2 (sq_nonneg _) (by positivity)
    · have hs2 : F₂ q ^ 2 ≤ (T ^ (-(1 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (hF₂0 q hq) hsmall2 2
      rw [hinv_sq] at hs2
      calc
        F₁ q ^ 2 * F₂ q ^ 2 ≤ B ^ 2 * T ^ (-(2 : ℝ)) :=
          mul_le_mul hB1 hs2 (sq_nonneg _) (by positivity)
        _ = T ^ (-(2 : ℝ)) * B ^ 2 := by ring
  calc
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2
        ≤ ∑ _q ∈ S, T ^ (-(2 : ℝ)) * B ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = (S.card : ℝ) * T ^ (-(2 : ℝ)) * B ^ 2 := by simp [mul_assoc]

/-- The published `T^{-1/2}` conclusion with the suppressed cardinality/polylog loss exposed as
the exact budget `(card S) * B² ≤ T^{3/2}`. -/
theorem matomakiTeravainen_typeII_T3_power_saving
    {α : Type*} {S : Finset α} {F₁ F₂ : α → ℝ} {T B : ℝ}
    (hT : 0 < T)
    (hF₁0 : ∀ q ∈ S, 0 ≤ F₁ q) (hF₂0 : ∀ q ∈ S, 0 ≤ F₂ q)
    (hF₁B : ∀ q ∈ S, F₁ q ≤ B) (hF₂B : ∀ q ∈ S, F₂ q ≤ B)
    (hsmall : ∀ q ∈ S, F₁ q ≤ T ^ (-(1 : ℝ)) ∨ F₂ q ≤ T ^ (-(1 : ℝ)))
    (hbudget : (S.card : ℝ) * B ^ 2 ≤ T ^ ((3 : ℝ) / 2)) :
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2 ≤ T ^ (-(1 : ℝ) / 2) := by
  have hbase := matomakiTeravainen_typeII_T3_energy hT hF₁0 hF₂0 hF₁B hF₂B hsmall
  calc
    ∑ q ∈ S, F₁ q ^ 2 * F₂ q ^ 2
        ≤ (S.card : ℝ) * T ^ (-(2 : ℝ)) * B ^ 2 := hbase
    _ = ((S.card : ℝ) * B ^ 2) * T ^ (-(2 : ℝ)) := by ring
    _ ≤ T ^ ((3 : ℝ) / 2) * T ^ (-(2 : ℝ)) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = T ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_add hT]
      congr 1
      ring

/-- An overlap-safe three-way energy partition. This is the finite one-spaced assembly used after
the `T₁/T₂/T₃` decomposition in Proposition 4.2. -/
theorem matomakiTeravainen_typeII_partition_energy
    {α : Type*} [DecidableEq α]
    {S S₁ S₂ S₃ : Finset α} {w : α → ℝ} {B₁ B₂ B₃ : ℝ}
    (hcover : S ⊆ S₁ ∪ S₂ ∪ S₃) (hw : ∀ q, 0 ≤ w q)
    (h₁ : ∑ q ∈ S₁, w q ≤ B₁)
    (h₂ : ∑ q ∈ S₂, w q ≤ B₂)
    (h₃ : ∑ q ∈ S₃, w q ≤ B₃) :
    ∑ q ∈ S, w q ≤ B₁ + B₂ + B₃ := by
  calc
    ∑ q ∈ S, w q ≤ ∑ q ∈ S₁ ∪ S₂ ∪ S₃, w q :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun q _hq _hnq => hw q)
    _ ≤ (∑ q ∈ S₁, w q) + ∑ q ∈ S₂ ∪ S₃, w q :=
      by
        rw [Finset.union_assoc]
        exact sum_union_le_of_nonneg hw
    _ ≤ (∑ q ∈ S₁, w q) + ((∑ q ∈ S₂, w q) + ∑ q ∈ S₃, w q) := by
      gcongr
      exact sum_union_le_of_nonneg hw
    _ ≤ B₁ + B₂ + B₃ := by linarith

end RHTower.Sieve
