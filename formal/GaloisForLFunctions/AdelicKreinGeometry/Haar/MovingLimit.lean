import GaloisForLFunctions.AdelicKreinGeometry.Haar.TranslationForms
import GaloisForLFunctions.BiarithmeticGeometry.Affine.FactorialTranslations
import GaloisForLFunctions.HeckeKreinToeplitz.Index.MonotoneHermitianForms

/-!
# The affine-invariant limit of cyclic moving forms

Factorial cyclic subgroups exhaust all rational translations. Their bounded monotone forms converge to an invariant nonnegative form whose remainder kills translation differences.
-/

open Complex Module Filter Topology
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The positive moving form obtained by exhausting rational cyclic translation subgroups. -/
def haarMovingLimit (k : AffineGroupQ → ℂ) (hp : ∀ g, k (g * translation 1) = k g) :
    kernelColumnSpan k → kernelColumnSpan k → ℂ :=
  monotoneHermitianLimit (fun n => translationMovingForm k hp (factorialTranslationStep n))

private theorem factorialMovingForm_monotone {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hp : ∀ g, k (g * translation 1) = k g) (x : kernelColumnSpan k) :
    Monotone (fun n => (translationMovingForm k hp (factorialTranslationStep n) x x).re) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [factorialTranslationStep_eq_succ_mul n]
  exact translationMovingForm_re_le_nat_multiple hk hi hp (factorialTranslationStep (n + 1)) (n + 1) x

private theorem factorialMovingForm_bddAbove {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (x : kernelColumnSpan k) :
    BddAbove (Set.range (fun n => (translationMovingForm k hp (factorialTranslationStep n) x x).re)) := by
  obtain ⟨C, hC⟩ := translationMovingForm_bddAbove hk hi hs hp x
  refine ⟨C, ?_⟩
  rintro a ⟨n, rfl⟩
  exact hC ⟨factorialTranslationStep n, rfl⟩

/-- Factorial cyclic moving forms converge on every pair of algebraic column vectors. -/
theorem tendsto_haarMovingLimit {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (x y : kernelColumnSpan k) :
    Tendsto (fun n => translationMovingForm k hp (factorialTranslationStep n) x y) atTop
      (𝓝 (haarMovingLimit k hp x y)) :=
  tendsto_monotoneHermitianLimit _ (fun n => translationMovingForm_hermitian hk hp (factorialTranslationStep n))
    (factorialMovingForm_monotone hk hi hp) (factorialMovingForm_bddAbove hk hi hs hp) x y

/-- The limiting form is Hermitian and nonnegative. -/
theorem haarMovingLimit_hermitian_nonnegative {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) :
    IsHermitianForm (haarMovingLimit k hp) ∧ ∀ x, 0 ≤ (haarMovingLimit k hp x x).re :=
  monotoneHermitianLimit_isHermitian_nonnegative _
    (fun n => translationMovingForm_hermitian hk hp (factorialTranslationStep n))
    (fun n => translationMovingForm_nonneg hk hi hp (factorialTranslationStep n))
    (factorialMovingForm_monotone hk hi hp) (factorialMovingForm_bddAbove hk hi hs hp)

/-- Cofinality bounds every cyclic moving form by the same limiting form. -/
theorem translationMovingForm_re_le_limit {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (x : kernelColumnSpan k) :
    (translationMovingForm k hp b x x).re ≤ (haarMovingLimit k hp x x).re := by
  have hnonneg (c : ℚ) (hc : 0 ≤ c) :
      (translationMovingForm k hp c x x).re ≤ (haarMovingLimit k hp x x).re := by
    apply ge_of_tendsto
      (Complex.continuous_re.continuousAt.tendsto.comp (tendsto_haarMovingLimit hk hi hs hp x x))
    filter_upwards [eventually_ge_atTop c.den] with n hn
    obtain ⟨m, hm⟩ := eq_nat_mul_factorialTranslationStep c hc hn
    rw [hm]
    exact translationMovingForm_re_le_nat_multiple hk hi hp (factorialTranslationStep n) m x
  by_cases hb : 0 ≤ b
  · exact hnonneg b hb
  · have h := hnonneg (-b) (by linarith only [lt_of_not_ge hb])
    rwa [translationMovingForm_neg] at h

/-- Cofinal cyclic exhaustion makes the limiting form invariant under the full affine group. -/
theorem haarMovingLimit_invariant {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (g : AffineGroupQ) (x y : kernelColumnSpan k) :
    haarMovingLimit k hp (kernelColumnRepresentation k g x) (kernelColumnRepresentation k g y) =
      haarMovingLimit k hp x y := by
  have hle (a : AffineGroupQ) (v : kernelColumnSpan k) :
      (haarMovingLimit k hp (kernelColumnRepresentation k a v) (kernelColumnRepresentation k a v)).re ≤
        (haarMovingLimit k hp v v).re := by
    apply le_of_tendsto'
      (Complex.continuous_re.continuousAt.tendsto.comp (tendsto_haarMovingLimit hk hi hs hp _ _))
    intro n
    dsimp only [Function.comp_def]
    rw [translationMovingForm_affine hk]
    exact translationMovingForm_re_le_limit hk hi hs hp _ v
  have hdiag (v : kernelColumnSpan k) :
      (haarMovingLimit k hp (kernelColumnRepresentation k g v) (kernelColumnRepresentation k g v)).re =
        (haarMovingLimit k hp v v).re := by
    apply le_antisymm (hle g v)
    have h := hle g⁻¹ (kernelColumnRepresentation k g v)
    have he : kernelColumnRepresentation k g⁻¹ (kernelColumnRepresentation k g v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rwa [he] at h
  have hH := (haarMovingLimit_hermitian_nonnegative hk hi hs hp).1
  rw [← hermitianPolarization_diag hH (kernelColumnRepresentation k g x)
    (kernelColumnRepresentation k g y), ← hermitianPolarization_diag hH x y]
  simp only [hermitianPolarization, ← (kernelColumnRepresentation k g).map_smul,
    ← (kernelColumnRepresentation k g).map_add, hdiag]

/-- The discarded limiting form is unchanged by any rational translation in its linear argument. -/
theorem columnPairing_sub_haarMovingLimit_translation {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r) (hs : HasIntegerSuccessor k)
    (hp : ∀ g, k (g * translation 1) = k g) (b : ℚ) (x y : kernelColumnSpan k) :
    kernelColumnPairing k y (kernelColumnRepresentation k (translation b) x) -
        haarMovingLimit k hp (kernelColumnRepresentation k (translation b) x) y =
      kernelColumnPairing k y x - haarMovingLimit k hp x y := by
  have hevent : (fun n => kernelColumnPairing k y (kernelColumnRepresentation k (translation b) x) -
      translationMovingForm k hp (factorialTranslationStep n)
        (kernelColumnRepresentation k (translation b) x) y) =ᶠ[atTop]
      (fun n => kernelColumnPairing k y x - translationMovingForm k hp (factorialTranslationStep n) x y) := by
    filter_upwards [eventually_ge_atTop b.den] with n hn
    obtain ⟨m, hm⟩ := eq_int_mul_factorialTranslationStep b hn
    rw [columnPairing_sub_translationMovingForm hk, columnPairing_sub_translationMovingForm hk,
      hm, translationFixedProjection_int_multiple]
  have hleft := (tendsto_const_nhds (x :=
    kernelColumnPairing k y (kernelColumnRepresentation k (translation b) x))).sub
      (tendsto_haarMovingLimit hk hi hs hp (kernelColumnRepresentation k (translation b) x) y)
  have hright := (tendsto_const_nhds (x := kernelColumnPairing k y x)).sub
    (tendsto_haarMovingLimit hk hi hs hp x y)
  exact tendsto_nhds_unique (hleft.congr' hevent) hright

#print axioms tendsto_haarMovingLimit
#print axioms haarMovingLimit_invariant
#print axioms columnPairing_sub_haarMovingLimit_translation
end GaloisForLFunctions.AdelicKreinGeometry
