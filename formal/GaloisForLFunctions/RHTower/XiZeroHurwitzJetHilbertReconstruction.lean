import GaloisForLFunctions.RHTower.XiZeroHurwitzHilbertReconstruction
import GaloisForLFunctions.HTGeometry.UpperEndLiteralLinearIndependence

/-!
# Arbitrary Xi-zero Hurwitz jet Hilbert reconstruction

The Xi-zero Hurwitz differential-independence theorem controls every pair consisting of a divisor
support point and a derivative order.  Restricting that theorem to any finite dictionary and then
using the upper-end literal bridge gives an exact collision law: literal derivative functions are
linearly independent precisely when no `(support point, order)` pair is repeated.

Consequently every collision-free dictionary has one pairwise-distinct complex sampling packet
with exact dual coefficient recovery, a positive-definite evaluation Gram, and positive volume.
This includes simultaneous rectangular sampling of every derivative through a fixed depth for
every injective finite Xi-divisor packet.
-/

open scoped BigOperators ComplexOrder Differential

namespace RHTower

open Complex Filter
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HurwitzJointLadder HurwitzZetaContinuation

noncomputable section

local instance xiZeroHurwitzJetHilbertUpperEndDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance xiZeroHurwitzJetHilbertUpperEndComplexAlgebra :
    Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance xiZeroHurwitzJetHilbertUpperEndRatfuncAlgebra :
    Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

local instance xiZeroHurwitzJetHilbertUpperEndDifferential :
    Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

/-- Literal continued-Hurwitz derivatives selected by arbitrary Xi support points and orders. -/
def xiZeroHurwitzJetFamily {d : ℕ} (ρ : Fin d → XiDivisorSupport)
    (order : Fin d → ℕ) : Fin d → ℂ → ℂ :=
  fun i => iteratedDeriv (order i)
    (continuedHzeta ((ρ i : XiDivisorSupport) : ℂ))

/-- The intrinsic label of a selected continued-Hurwitz derivative. -/
def xiZeroHurwitzJetIndex {d : ℕ} (ρ : Fin d → XiDivisorSupport)
    (order : Fin d → ℕ) : Fin d → XiDivisorSupport × ℕ :=
  fun i => (ρ i, order i)

/-- Evaluation Gram of an arbitrary finite Xi-zero Hurwitz jet dictionary. -/
def xiZeroHurwitzJetEvaluationGram {d : ℕ} (ρ : Fin d → XiDivisorSupport)
    (order : Fin d → ℕ) (points : Fin d → ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  finiteEvaluationGram (xiZeroHurwitzJetFamily ρ order) points

/-- Upper-end meromorphic images of arbitrary continued-Hurwitz jets have exactly the intrinsic
support/order collisions. -/
theorem linearIndependent_xiZeroHurwitzJetUpperEndAnalytic_iff_injective
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    LinearIndependent ℂ
        (fun i => algebraMap upperEndAnalyticSubring upperEndMeroField
          (continuedHzetaUpperEndAnalyticJet
            ((ρ i : XiDivisorSupport) : ℂ) (order i))) ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  constructor
  · intro h i j hij
    have hρ : ρ i = ρ j := congrArg Prod.fst hij
    have horder : order i = order j := congrArg Prod.snd hij
    apply h.injective
    simp [hρ, horder]
  · intro hindex
    classical
    let I := {s : XiDivisorSupport // s ∈ Set.range ρ}
    letI : Fintype I := Fintype.ofFinite I
    have hmeroDI : DifferentialIndependent ℂ
        (fun s : I => continuedHzetaUpperEndMero ((s.1 : XiDivisorSupport) : ℂ)) :=
      differentialIndependent_upperEnd_restrictComplex _
        (xi_zero_hurwitz_differentialIndependent
          (fun s : I => s.1) Subtype.coe_injective)
    unfold DifferentialIndependent at hmeroDI
    let e : Fin d → I × ℕ := fun i =>
      (⟨ρ i, Set.mem_range_self i⟩, order i)
    have he : Function.Injective e := by
      intro i j hij
      apply hindex
      apply Prod.ext
      · exact congrArg (fun p : I × ℕ => (p.1 : XiDivisorSupport)) hij
      · exact congrArg (fun p : I × ℕ => p.2) hij
    have hmeroLI := (hmeroDI.comp e he).linearIndependent
    simpa [e, differentialJet_continuedHzetaUpperEndMero] using hmeroLI

/-- **Exact Xi-zero Hurwitz jet collision law.** Arbitrary literal continued-Hurwitz derivatives
are linearly independent exactly when their `(Xi support point, derivative order)` labels are
distinct. Repeated support points are allowed when their derivative orders differ. -/
theorem linearIndependent_xiZeroHurwitzJetFamily_iff_injective
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    LinearIndependent ℂ (xiZeroHurwitzJetFamily ρ order) ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  constructor
  · intro h i j hij
    have hρ : ρ i = ρ j := congrArg Prod.fst hij
    have horder : order i = order j := congrArg Prod.snd hij
    apply h.injective
    simp [xiZeroHurwitzJetFamily, hρ, horder]
  · intro hindex
    apply linearIndependent_literal_of_upperEndMero
      (xiZeroHurwitzJetFamily ρ order)
      (fun i => continuedHzetaUpperEndAnalyticJet
        ((ρ i : XiDivisorSupport) : ℂ) (order i))
    · intro i
      rfl
    · exact
        (linearIndependent_xiZeroHurwitzJetUpperEndAnalytic_iff_injective
          ρ order).2 hindex

/-- **Arbitrary Xi-zero Hurwitz jet Hilbert reconstruction.** Every collision-free finite
dictionary admits pairwise distinct samples and dual weights that isolate every selected jet,
recover every coefficient vector, and carry a strict evaluation Gram with positive volume. -/
theorem exists_injective_xiZeroHurwitzJetEvaluationHilbertReconstruction
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ)
    (hindex : Function.Injective (xiZeroHurwitzJetIndex ρ order)) :
    ∃ (points : Fin d → ℂ) (dual : Fin d → Fin d → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiZeroHurwitzJetFamily ρ order r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin d → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiZeroHurwitzJetFamily ρ order r (points i)) = a q) ∧
      (xiZeroHurwitzJetEvaluationGram ρ order points).PosDef ∧
      0 < (xiZeroHurwitzJetEvaluationGram ρ order points).det := by
  simpa [xiZeroHurwitzJetEvaluationGram] using
    exists_injective_finiteEvaluationHilbertReconstruction_of_linearIndependent
      (xiZeroHurwitzJetFamily ρ order)
      ((linearIndependent_xiZeroHurwitzJetFamily_iff_injective ρ order).2 hindex)

/-- Positive-definite literal sampling exists exactly when the selected support/order pairs do not
collide. -/
theorem exists_injective_xiZeroHurwitzJetEvaluationGram_posDef_iff
    {d : ℕ} (ρ : Fin d → XiDivisorSupport) (order : Fin d → ℕ) :
    (∃ points : Fin d → ℂ, Function.Injective points ∧
      (xiZeroHurwitzJetEvaluationGram ρ order points).PosDef) ↔
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  constructor
  · rintro ⟨points, _hpoints, hgram⟩
    have hcols : LinearIndependent ℂ
        (finiteEvaluationColumn (xiZeroHurwitzJetFamily ρ order) points) :=
      Matrix.posDef_gram_iff_linearIndependent.mp hgram
    intro i j hij
    have hρ : ρ i = ρ j := congrArg Prod.fst hij
    have horder : order i = order j := congrArg Prod.snd hij
    apply hcols.injective
    ext row
    simp [finiteEvaluationColumn, xiZeroHurwitzJetFamily, hρ, horder]
  · intro hindex
    obtain ⟨points, _dual, hpoints, _hdelta, _hrecovery, hgram, _hdet⟩ :=
      exists_injective_xiZeroHurwitzJetEvaluationHilbertReconstruction
        ρ order hindex
    exact ⟨points, hpoints, hgram⟩

/-- Full dual reconstruction, strict Gram positivity, and positive volume exist exactly when the
finite support/order dictionary is collision-free. -/
theorem exists_injective_xiZeroHurwitzJetEvaluationHilbertReconstruction_iff
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
      Function.Injective (xiZeroHurwitzJetIndex ρ order) := by
  change
    FiniteEvaluationHilbertReconstruction
      (xiZeroHurwitzJetFamily ρ order) ↔
        Function.Injective (xiZeroHurwitzJetIndex ρ order)
  calc
    _ ↔ LinearIndependent ℂ (xiZeroHurwitzJetFamily ρ order) :=
      finiteEvaluationHilbertReconstruction_iff_linearIndependent
        (xiZeroHurwitzJetFamily ρ order)
    _ ↔ _ := linearIndependent_xiZeroHurwitzJetFamily_iff_injective ρ order

/-- Every derivative through depth `m` of every member of an injective Xi-divisor packet, flattened
through `Fin N × Fin (m+1) ≃ Fin (N*(m+1))`. -/
def xiZeroHurwitzJetRectangle {N : ℕ} (ρ : Fin N → XiDivisorSupport) (m : ℕ) :
    Fin (N * (m + 1)) → ℂ → ℂ :=
  fun q => iteratedDeriv ((finProdFinEquiv.symm q).2 : ℕ)
    (continuedHzeta
      ((ρ (finProdFinEquiv.symm q).1 : XiDivisorSupport) : ℂ))

/-- An injective Xi-divisor packet gives a collision-free flattened initial-jet rectangle. -/
theorem xiZeroHurwitzJetRectangle_index_injective
    {N : ℕ} (ρ : Fin N → XiDivisorSupport) (m : ℕ)
    (hρ : Function.Injective ρ) :
    Function.Injective (fun q : Fin (N * (m + 1)) =>
      (ρ (finProdFinEquiv.symm q).1,
        ((finProdFinEquiv.symm q).2 : ℕ))) := by
  intro q r hij
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  · apply hρ
    exact congrArg Prod.fst hij
  · apply Fin.ext
    exact congrArg Prod.snd hij

/-- **Simultaneous Xi-zero Hurwitz jet-rectangle reconstruction.** For every finite injective
Xi-divisor packet and every depth, one sampling packet jointly recovers every derivative of every
selected continued-Hurwitz function and carries a strict Hilbert metric with positive volume. -/
theorem exists_injective_xiZeroHurwitzJetRectangleHilbertReconstruction
    {N : ℕ} (ρ : Fin N → XiDivisorSupport) (m : ℕ)
    (hρ : Function.Injective ρ) :
    ∃ (points : Fin (N * (m + 1)) → ℂ)
        (dual : Fin (N * (m + 1)) → Fin (N * (m + 1)) → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * xiZeroHurwitzJetRectangle ρ m r (points i) =
        if q = r then 1 else 0) ∧
      (∀ (a : Fin (N * (m + 1)) → ℂ) q,
        ∑ i, dual q i *
          (∑ r, a r * xiZeroHurwitzJetRectangle ρ m r (points i)) = a q) ∧
      (finiteEvaluationGram (xiZeroHurwitzJetRectangle ρ m) points).PosDef ∧
      0 < (finiteEvaluationGram (xiZeroHurwitzJetRectangle ρ m) points).det := by
  let support : Fin (N * (m + 1)) → XiDivisorSupport :=
    fun q => ρ (finProdFinEquiv.symm q).1
  let order : Fin (N * (m + 1)) → ℕ :=
    fun q => ((finProdFinEquiv.symm q).2 : ℕ)
  have hindex : Function.Injective (xiZeroHurwitzJetIndex support order) := by
    simpa [support, order, xiZeroHurwitzJetIndex] using
      xiZeroHurwitzJetRectangle_index_injective ρ m hρ
  simpa [support, order, xiZeroHurwitzJetRectangle, xiZeroHurwitzJetFamily,
    xiZeroHurwitzJetEvaluationGram] using
      exists_injective_xiZeroHurwitzJetEvaluationHilbertReconstruction
        support order hindex

end

end RHTower
