import GaloisForLFunctions.HTGeometry.CofiniteTailHilbertReconstruction
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Continuous finite-support tail independence

On a perfect T₁ space, a nonzero continuous function cannot have finite support: its nonzero locus
is a nonempty open neighborhood and hence infinite.  Therefore ordinary linear independence and
coefficient independence modulo finite support coincide for every finite continuous family.

Combining this topological rigidity with cofinite Gram polarization identifies ordinary linear
independence with strict square evaluation-Gram realizability after every finite deletion.  This
supplies a reusable finite-to-cofinite bridge without an upper-end or asymptotic hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set
open scoped ComplexOrder

noncomputable section

/-- A finitely supported monomial in continuous complex observables is continuous, even when the
ambient observable dictionary is infinite. -/
theorem continuous_finsuppMonomial
    {ι X : Type*} [TopologicalSpace X]
    (u : ι → X → ℂ) (hu : ∀ i, Continuous (u i)) (e : ι →₀ ℕ) :
    Continuous (e.prod fun i k => u i ^ k) := by
  classical
  induction e using Finsupp.induction with
  | zero => exact continuous_const
  | single_add i k e _hi hk ih =>
      rw [Finsupp.prod_add_index]
      · have hsingle :
            (Finsupp.single i k).prod (fun j m => u j ^ m) = u i ^ k :=
          Finsupp.prod_single_index (pow_zero _)
        rw [hsingle]
        exact (hu i).pow k |>.mul ih
      · simp
      · simp [pow_add]

/-- If the left factor is perfect, its product with any topological space is perfect.  The second
coordinate can be held fixed while the first coordinate moves inside every product neighborhood.
This is exposed as a reducible constructor rather than a global instance so callers control which
factor supplies the absence of isolated points. -/
@[reducible] def perfectSpace_prod_left
    (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] [PerfectSpace X] :
    PerfectSpace (X × Y) where
  univ_preperfect := by
    intro x _hx
    rw [accPt_iff_nhds]
    intro U hU
    obtain ⟨s, hs, t, ht, hst⟩ := mem_nhds_prod_iff.mp hU
    have hxt : x.2 ∈ t := mem_of_mem_nhds ht
    obtain ⟨y, ⟨hys, _hyuniv⟩, hyne⟩ :=
      (accPt_iff_nhds.mp
        (PerfectSpace.univ_preperfect x.1 (Set.mem_univ x.1))) s hs
    refine ⟨(y, x.2), ⟨hst ⟨hys, hxt⟩, Set.mem_univ _⟩, ?_⟩
    intro hpair
    exact hyne (congrArg Prod.fst hpair)

/-- A finite linearly independent family of continuous functions over any nontrivially normed
field remains linearly independent after restricting its domain away from an arbitrary finite
set. -/
theorem linearIndependent_restrict_compl_of_continuous
    {𝕜 J X : Type*} [NontriviallyNormedField 𝕜] [Fintype J]
    [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (u : J → X → 𝕜) (hu : ∀ j, Continuous (u j))
    (hlin : LinearIndependent 𝕜 u) (F : Set X) (hF : F.Finite) :
    LinearIndependent 𝕜
      (fun j => fun x : {x : X // x ∉ F} => u j x) := by
  classical
  rw [Fintype.linearIndependent_iff] at hlin ⊢
  intro c hc
  apply hlin c
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
  let f : X → 𝕜 := fun y => ∑ j, c j * u j y
  have hf : Continuous f := by
    fun_prop
  have hsupp : {y : X | f y ≠ 0}.Finite := hF.subset (by
    intro y hy
    by_contra hyF
    apply hy
    have hpoint := congrFun hc ⟨y, hyF⟩
    simpa [f, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hpoint)
  by_contra hx
  have hopen : IsOpen {y : X | f y ≠ 0} := by
    change IsOpen (f ⁻¹' {0}ᶜ)
    exact isOpen_ne.preimage hf
  have hinfinite : {y : X | f y ≠ 0}.Infinite :=
    infinite_of_mem_nhds x (hopen.mem_nhds hx)
  exact hinfinite hsupp

/-- **Continuous finite-support rigidity.**  For a finite family of continuous complex observables
on a perfect T₁ space, ordinary linear independence already implies independence modulo every
finite subset of the domain.  The reverse implication holds for arbitrary families. -/
theorem tailCoefficientIndependent_iff_linearIndependent_of_continuous
    {J X : Type*} [Fintype J] [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (u : J → X → ℂ) (hu : ∀ j, Continuous (u j)) :
    TailCoefficientIndependent u ↔ LinearIndependent ℂ u := by
  constructor
  · intro htail
    exact htail.linearIndependent u
  · intro hlinear c hsupp
    let F : Set X := {x | ∑ j, c j * u j x ≠ 0}
    have hlinCompl :=
      linearIndependent_restrict_compl_of_continuous u hu hlinear F hsupp
    rw [Fintype.linearIndependent_iff] at hlinCompl
    apply funext
    apply hlinCompl c
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact not_ne_iff.mp x.property

/-- **Continuous cofinite Gram classification.**  A finite continuous family on a perfect T₁
space is linearly independent exactly when every finite deletion leaves a square evaluation packet
with positive-definite Gram matrix. -/
theorem linearIndependent_iff_cofinite_posDef_evaluationGram_of_continuous
    {J X : Type*} [Fintype J] [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (u : J → X → ℂ) (hu : ∀ j, Continuous (u j)) :
    LinearIndependent ℂ u ↔
      ∀ F : Set X, F.Finite →
        ∃ points : J → {x : X // x ∉ F},
          (cofiniteEvaluationGram u F points).PosDef := by
  classical
  calc
    _ ↔ TailCoefficientIndependent u :=
      (tailCoefficientIndependent_iff_linearIndependent_of_continuous u hu).symm
    _ ↔ _ := tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram u

/-- **Continuous cofinite Hilbert reconstruction.**  Every finite linearly independent family of
continuous complex observables on a perfect T₁ space admits pairwise distinct surviving sample
points, exact dual coefficient recovery, a positive-definite evaluation Gram, and positive Hilbert
volume after deleting an arbitrary finite subset of the domain. -/
theorem exists_injective_cofiniteEvaluationHilbertReconstruction_of_linearIndependent_of_continuous
    {J X : Type*} [Fintype J] [DecidableEq J]
    [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (u : J → X → ℂ) (hu : ∀ j, Continuous (u j))
    (hlin : LinearIndependent ℂ u) (F : Set X) (hF : F.Finite) :
    ∃ (points : J → {x : X // x ∉ F}) (dual : J → J → ℂ),
      Function.Injective points ∧
      (∀ q r, ∑ i, dual q i * u r (points i) = if q = r then 1 else 0) ∧
      (∀ (a : J → ℂ) q,
        ∑ i, dual q i * (∑ r, a r * u r (points i)) = a q) ∧
      (cofiniteEvaluationGram u F points).PosDef ∧
      0 < (cofiniteEvaluationGram u F points).det := by
  exact
    exists_injective_cofiniteEvaluationHilbertReconstruction_of_tailCoefficientIndependent
      u ((tailCoefficientIndependent_iff_linearIndependent_of_continuous
        u hu).2 hlin) F hF

/-- **Continuous finite/cofinite Hilbert phase law.** For finite continuous complex function
families on a perfect T₁ domain, one complete finite reconstruction packet exists exactly when
complete reconstruction survives every finite deletion. -/
theorem finiteEvaluationHilbertReconstruction_iff_cofinite_of_continuous
    {J X : Type*} [Fintype J] [DecidableEq J]
    [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    (u : J → X → ℂ) (hu : ∀ j, Continuous (u j)) :
    FiniteEvaluationHilbertReconstruction u ↔
      CofiniteEvaluationHilbertReconstruction u := by
  calc
    _ ↔ LinearIndependent ℂ u :=
      finiteEvaluationHilbertReconstruction_iff_linearIndependent u
    _ ↔ TailCoefficientIndependent u :=
      (tailCoefficientIndependent_iff_linearIndependent_of_continuous u hu).symm
    _ ↔ _ :=
      (cofiniteEvaluationHilbertReconstruction_iff_tailCoefficientIndependent
        u).symm

end

end GaloisForLFunctions.HTGeometry
