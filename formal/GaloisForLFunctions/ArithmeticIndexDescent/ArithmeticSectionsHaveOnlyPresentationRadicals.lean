import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ArithmeticSectionsPayThePole
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceDeterminantalSectionsAndArithmeticRiemannRoch
import GaloisForLFunctions.HTGeometry.FactorThroughRange
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Arithmetic section radicals are presentation relations

The complete Weil form dominates square mass on narrow arithmetic sections.
Consequently the kernel of any finite section Gram is exactly the kernel of
test synthesis, including redundant presentations. Every such null vector
annihilates the mixed pairing with every ambient real test.

This is a source statement: the section space carries only smoothness and
support data. No positivity or mixed-block compatibility is assumed.
-/

open Matrix MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri HTGeometry

/-- The complete real Weil pairing, bundled as a bilinear form. -/
def realWeilForm : LinearMap.BilinForm ℝ realTests where
  toFun f :=
    { toFun := fun g => weilPair f.1 g.1
      map_add' := fun g h => by
        change weilPair f.1 (g.1 + h.1) = _
        rw [weilPair_comm, weilPair_add_left g.2 h.2 f.2]
        rw [weilPair_comm g.1 f.1, weilPair_comm h.1 f.1]
      map_smul' := fun c g => by
        change weilPair f.1 (c • g.1) = c * weilPair f.1 g.1
        rw [weilPair_comm, weilPair_smul_left, weilPair_comm g.1 f.1] }
  map_add' f g := by
    ext h
    exact weilPair_add_left f.2 g.2 h.2
  map_smul' c f := by
    ext g
    exact weilPair_smul_left c f.1 g.1

theorem realWeilForm_symm (f g : realTests) : realWeilForm f g = realWeilForm g f :=
  weilPair_comm f.1 g.1

/-- A finite coefficient presentation of an actual real test. -/
def realTestSynthesis {ι : Type*} [Fintype ι] (f : ι → realTests) (x : ι → ℝ) : realTests :=
  ∑ i, x i • f i

/-- Mixed entries of the complete Weil form. -/
def realWeilMixed {ι κ : Type*} (f : ι → realTests) (g : κ → realTests) : Matrix ι κ ℝ :=
  fun i j => realWeilForm (f i) (g j)

theorem realWeilForm_synthesis_left {ι : Type*} [Fintype ι]
    (f : ι → realTests) (x : ι → ℝ) (g : realTests) :
    realWeilForm (realTestSynthesis f x) g = ∑ i, x i * realWeilForm (f i) g := by
  simp only [realTestSynthesis, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul]

theorem realWeilMixed_mulVec {ι κ : Type*} [Fintype κ]
    (f : ι → realTests) (g : κ → realTests) (x : κ → ℝ) (i : ι) :
    (realWeilMixed f g).mulVec x i = realWeilForm (f i) (realTestSynthesis g x) := by
  change (∑ j, realWeilForm (f i) (g j) * x j) =
    realWeilForm (f i) (∑ j, x j • g j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, smul_eq_mul, mul_comm]

theorem realWeilForm_synthesis_self {ι : Type*} [Fintype ι]
    (f : ι → realTests) (x : ι → ℝ) :
    realWeilForm (realTestSynthesis f x) (realTestSynthesis f x) =
      ∑ i, x i * (realWeilMixed f f).mulVec x i := by
  rw [realWeilForm_synthesis_left]
  simp_rw [realWeilMixed_mulVec]

/-- A narrow section Gram has no radical beyond genuine relations between its tests. -/
theorem arithmeticSection_gram_kernel_iff {ι : Type*} [Fintype ι]
    {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N)
    (f : ι → arithmeticSectionTests N w) (x : ι → ℝ) :
    (realWeilMixed (fun i => (f i).1) (fun i => (f i).1)).mulVec x = 0 ↔
      realTestSynthesis (fun i => (f i).1) x = 0 := by
  constructor
  · intro hx
    let q := realTestSynthesis (fun i => (f i).1) x
    have hq : q ∈ arithmeticSectionTests N w :=
      (arithmeticSectionTests N w).sum_mem fun i _ =>
        (arithmeticSectionTests N w).smul_mem (x i) (f i).2
    have hW : weilPair q.1 q.1 = 0 := by
      change realWeilForm q q = 0
      rw [realWeilForm_synthesis_self, hx]
      simp
    have hupper := integral_sq_le_weilPair_arithmeticSection hN hw0 hw ⟨q, hq⟩
    rw [hW] at hupper
    have hint : (∫ u, q.1 u ^ 2) = 0 :=
      le_antisymm hupper (integral_nonneg fun u => sq_nonneg (q.1 u))
    exact Subtype.ext (eq_zero_of_integral_sq_eq_zero_of_mem_realTests q.2 hint)
  · intro hx
    funext i
    rw [realWeilMixed_mulVec, hx, map_zero]
    rfl

/-- Every null section combination annihilates all ambient mixed Weil entries. -/
theorem arithmeticSection_radical_annihilates_mixed {ι κ : Type*} [Fintype ι]
    {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N)
    (f : ι → arithmeticSectionTests N w) (g : κ → realTests) (x : ι → ℝ)
    (hx : (realWeilMixed (fun i => (f i).1) (fun i => (f i).1)).mulVec x = 0) :
    (realWeilMixed (fun i => (f i).1) g).transpose.mulVec x = 0 := by
  have hzero := (arithmeticSection_gram_kernel_iff hN hw0 hw f x).mp hx
  have htranspose : (realWeilMixed (fun i => (f i).1) g).transpose =
      realWeilMixed g (fun i => (f i).1) := by
    ext i j
    exact realWeilForm_symm _ _
  rw [htranspose]
  funext i
  rw [realWeilMixed_mulVec, hzero, map_zero]
  rfl

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.arithmeticSection_gram_kernel_iff
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.arithmeticSection_radical_annihilates_mixed
