import GaloisForLFunctions.RHTower.XiZeroHurwitzJetCofiniteHilbertReconstruction

/-!
# Finite/cofinite Xi-zero Hurwitz jet Hilbert phase

The upper-end HTGeometry bridge makes ordinary linear independence unusually rigid for Xi-zero
Hurwitz jets: it already implies coefficient independence after every finite deletion of the
complex evaluation domain.  Hence one finite positive evaluation Gram is equivalent to positive
evaluation Grams after every finite deletion, and one exact Hilbert reconstruction packet is
equivalent to deletion-robust exact reconstruction.

For a full rectangular jet packet, the intrinsic support/order index is injective exactly when the
support packet itself is injective.  This supplies the missing converses to finite rectangular
reconstruction and gives its exact cofinite classification.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open Complex Filter
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HurwitzJointLadder

noncomputable section

/-- **Finite-to-cofinite rigidity for Xi-zero Hurwitz jets.**  Ordinary linear independence of a
finite literal Xi-zero Hurwitz jet dictionary already survives deletion of every finite subset of
the complex evaluation domain. -/
theorem linearIndependent_xiZeroHurwitzJetFamily_iff_tailCoefficientIndependent
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    LinearIndependent ℂ (xiZeroHurwitzJetFamily ρ order) ↔
      TailCoefficientIndependent (xiZeroHurwitzJetFamily ρ order) := by
  rw [linearIndependent_xiZeroHurwitzJetFamily_iff_injective,
    tailCoefficientIndependent_xiZeroHurwitzJetFamily_iff_injective]

/-- One finite strict Xi-zero Hurwitz jet evaluation Gram exists exactly when strict evaluation
Grams can be chosen after every finite deletion of the complex domain. -/
theorem exists_injective_xiZeroHurwitzJetEvaluationGram_posDef_iff_cofinite
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∃ points : Fin d → ℂ, Function.Injective points ∧
      (xiZeroHurwitzJetEvaluationGram ρ order points).PosDef) ↔
    (∀ F : Set ℂ, F.Finite →
      ∃ points : Fin d → {z : ℂ // z ∉ F},
        (cofiniteEvaluationGram
          (xiZeroHurwitzJetFamily ρ order) F points).PosDef) := by
  calc
    _ ↔ Function.Injective (xiZeroHurwitzJetIndex ρ order) :=
      exists_injective_xiZeroHurwitzJetEvaluationGram_posDef_iff ρ order
    _ ↔ _ :=
      (xiZeroHurwitzJetCofiniteEvaluationGram_posDef_iff_injective
        ρ order).symm

/-- **Finite/cofinite Xi-zero Hurwitz jet Hilbert connector.**  Existence of one pairwise-distinct
sampling packet with exact coefficient reconstruction, strict Gram positivity, and positive volume
is equivalent to existence of such a packet after every finite complex deletion. -/
theorem exists_injective_xiZeroHurwitzJetEvaluationHilbertReconstruction_iff_cofinite
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∃ (points : Fin d → ℂ) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiZeroHurwitzJetFamily ρ order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiZeroHurwitzJetFamily ρ order r (points i)) = a q) ∧
      (xiZeroHurwitzJetEvaluationGram ρ order points).PosDef ∧
      0 < (xiZeroHurwitzJetEvaluationGram ρ order points).det) ↔
    (∀ F : Set ℂ, F.Finite →
      ∃ (points : Fin d → {z : ℂ // z ∉ F}) (dual : Fin d → Fin d → ℂ),
        Function.Injective points ∧
        (∀ q r, ∑ i, dual q i * xiZeroHurwitzJetFamily ρ order r (points i) =
          if q = r then 1 else 0) ∧
        (∀ (a : Fin d → ℂ) q,
          ∑ i, dual q i *
            (∑ r, a r * xiZeroHurwitzJetFamily ρ order r (points i)) = a q) ∧
        (cofiniteEvaluationGram
          (xiZeroHurwitzJetFamily ρ order) F points).PosDef ∧
        0 < (cofiniteEvaluationGram
          (xiZeroHurwitzJetFamily ρ order) F points).det) := by
  calc
    _ ↔ Function.Injective (xiZeroHurwitzJetIndex ρ order) :=
      exists_injective_xiZeroHurwitzJetEvaluationHilbertReconstruction_iff ρ order
    _ ↔ _ :=
      (xiZeroHurwitzJetCofiniteHilbertReconstruction_iff_injective
        ρ order).symm

/-- The flattened support/order index of a full jet rectangle is injective exactly when its
Xi-divisor support packet is injective.  The reverse implication was the previously available
direction; derivative order zero supplies the converse. -/
theorem xiZeroHurwitzJetRectangle_index_injective_iff
    {N : ℕ} (ρ : Fin N → XiDivisorSupport) (m : ℕ) :
    Function.Injective (fun q : Fin (N * (m + 1)) =>
      (ρ (finProdFinEquiv.symm q).1,
        ((finProdFinEquiv.symm q).2 : ℕ))) ↔
      Function.Injective ρ := by
  constructor
  · intro hindex i j hij
    let z : Fin (m + 1) := ⟨0, Nat.zero_lt_succ m⟩
    have hq : finProdFinEquiv (i, z) = finProdFinEquiv (j, z) := by
      apply hindex
      simp [hij]
    exact congrArg Prod.fst (finProdFinEquiv.injective hq)
  · exact xiZeroHurwitzJetRectangle_index_injective ρ m

/-- **Exact finite rectangular reconstruction classification.**  The full Xi-zero Hurwitz jet
rectangle admits exact finite Hilbert reconstruction exactly when the support packet is injective.
This closes the converse absent from the original rectangular existence theorem. -/
theorem exists_injective_xiZeroHurwitzJetRectangleHilbertReconstruction_iff_injective
    {N : ℕ} (ρ : Fin N → XiDivisorSupport) (m : ℕ) :
    (∃ (points : Fin (N * (m + 1)) → ℂ)
        (dual : Fin (N * (m + 1)) → Fin (N * (m + 1)) → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiZeroHurwitzJetRectangle ρ m r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin (N * (m + 1)) → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiZeroHurwitzJetRectangle ρ m r (points i)) = a q) ∧
      (finiteEvaluationGram (xiZeroHurwitzJetRectangle ρ m) points).PosDef ∧
      0 < (finiteEvaluationGram
        (xiZeroHurwitzJetRectangle ρ m) points).det) ↔
      Function.Injective ρ := by
  let support : Fin (N * (m + 1)) → XiDivisorSupport :=
    fun q => ρ (finProdFinEquiv.symm q).1
  let order : Fin (N * (m + 1)) → ℕ :=
    fun q => ((finProdFinEquiv.symm q).2 : ℕ)
  have hfamily :
      xiZeroHurwitzJetFamily support order = xiZeroHurwitzJetRectangle ρ m := by
    rfl
  calc
    _ ↔ Function.Injective (xiZeroHurwitzJetIndex support order) := by
      simpa only [xiZeroHurwitzJetEvaluationGram, hfamily] using
        exists_injective_xiZeroHurwitzJetEvaluationHilbertReconstruction_iff
          support order
    _ ↔ Function.Injective ρ := by
      change Function.Injective (fun q => (support q, order q)) ↔
        Function.Injective ρ
      simpa only [support, order] using
        xiZeroHurwitzJetRectangle_index_injective_iff ρ m

/-- **Exact cofinite rectangular reconstruction classification.**  Exact dual reconstruction,
strict Gram positivity, and positive volume survive every finite complex deletion exactly when the
Xi-divisor support packet is injective. -/
theorem xiZeroHurwitzJetRectangleCofiniteHilbertReconstruction_iff_injective
    {N : ℕ} (ρ : Fin N → XiDivisorSupport) (m : ℕ) :
    (∀ F : Set ℂ, F.Finite →
      ∃ (points : Fin (N * (m + 1)) → {z : ℂ // z ∉ F})
          (dual : Fin (N * (m + 1)) → Fin (N * (m + 1)) → ℂ),
        Function.Injective points ∧
        (∀ q r,
          ∑ i, dual q i * xiZeroHurwitzJetRectangle ρ m r (points i) =
            if q = r then 1 else 0) ∧
        (∀ (a : Fin (N * (m + 1)) → ℂ) q,
          ∑ i, dual q i *
            (∑ r, a r * xiZeroHurwitzJetRectangle ρ m r (points i)) = a q) ∧
        (cofiniteEvaluationGram
          (xiZeroHurwitzJetRectangle ρ m) F points).PosDef ∧
        0 < (cofiniteEvaluationGram
          (xiZeroHurwitzJetRectangle ρ m) F points).det) ↔
      Function.Injective ρ := by
  let support : Fin (N * (m + 1)) → XiDivisorSupport :=
    fun q => ρ (finProdFinEquiv.symm q).1
  let order : Fin (N * (m + 1)) → ℕ :=
    fun q => ((finProdFinEquiv.symm q).2 : ℕ)
  have hfamily :
      xiZeroHurwitzJetFamily support order = xiZeroHurwitzJetRectangle ρ m := by
    rfl
  calc
    _ ↔ Function.Injective (xiZeroHurwitzJetIndex support order) := by
      simpa only [hfamily] using
        xiZeroHurwitzJetCofiniteHilbertReconstruction_iff_injective
          support order
    _ ↔ Function.Injective ρ := by
      change Function.Injective (fun q => (support q, order q)) ↔
        Function.Injective ρ
      simpa only [support, order] using
        xiZeroHurwitzJetRectangle_index_injective_iff ρ m

/-- For full Xi-zero Hurwitz jet rectangles, one finite exact Hilbert reconstruction packet exists
exactly when such packets exist after every finite deletion of the complex domain. -/
theorem exists_injective_xiZeroHurwitzJetRectangleHilbertReconstruction_iff_cofinite
    {N : ℕ} (ρ : Fin N → XiDivisorSupport) (m : ℕ) :
    (∃ (points : Fin (N * (m + 1)) → ℂ)
        (dual : Fin (N * (m + 1)) → Fin (N * (m + 1)) → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiZeroHurwitzJetRectangle ρ m r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin (N * (m + 1)) → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiZeroHurwitzJetRectangle ρ m r (points i)) = a q) ∧
      (finiteEvaluationGram (xiZeroHurwitzJetRectangle ρ m) points).PosDef ∧
      0 < (finiteEvaluationGram
        (xiZeroHurwitzJetRectangle ρ m) points).det) ↔
    (∀ F : Set ℂ, F.Finite →
      ∃ (points : Fin (N * (m + 1)) → {z : ℂ // z ∉ F})
          (dual : Fin (N * (m + 1)) → Fin (N * (m + 1)) → ℂ),
        Function.Injective points ∧
        (∀ q r,
          ∑ i, dual q i * xiZeroHurwitzJetRectangle ρ m r (points i) =
            if q = r then 1 else 0) ∧
        (∀ (a : Fin (N * (m + 1)) → ℂ) q,
          ∑ i, dual q i *
            (∑ r, a r * xiZeroHurwitzJetRectangle ρ m r (points i)) = a q) ∧
        (cofiniteEvaluationGram
          (xiZeroHurwitzJetRectangle ρ m) F points).PosDef ∧
        0 < (cofiniteEvaluationGram
          (xiZeroHurwitzJetRectangle ρ m) F points).det) := by
  calc
    _ ↔ Function.Injective ρ :=
      exists_injective_xiZeroHurwitzJetRectangleHilbertReconstruction_iff_injective ρ m
    _ ↔ _ :=
      (xiZeroHurwitzJetRectangleCofiniteHilbertReconstruction_iff_injective
        ρ m).symm

end

end RHTower
