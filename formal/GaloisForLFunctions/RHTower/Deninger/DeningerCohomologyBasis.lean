import GaloisForLFunctions.RHTower.Deninger.DeningerStageCohomologyModule
import GaloisForLFunctions.RHTower.Deninger.DeningerDlogWedgeBasis
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# A basis of the cohomology of a character stage

The determinant forms of the `k`-element sets of coordinates are linearly independent — evaluating a
combination on the coordinate vectors of one of the sets isolates its coefficient — and they span the
constant alternating forms, so they are a basis.  Transporting it through the comparison of the
cohomology with the constant forms gives a basis of the cohomology of a character stage made of the
classes of the exterior products of the logarithmic differentials.

* `deningerDetFormBasis` : the determinant forms of the `k`-element sets are a basis.
* `deningerCohomologyBasis` : the classes of the logarithmic wedges are a basis of the cohomology.
* `deningerCohomologyExteriorEquiv` : the cohomology of a stage is the exterior power of the
  covering space.
-/

namespace RHTower

open Complex Finset

section DetFormBasis

variable {r k : ℕ}

/-- The increasing selection of a `k`-element set of coordinates. -/
noncomputable def deningerSubsetTuple (S : {S : Finset (Fin r) // S.card = k}) : Fin k → Fin r :=
  fun a => S.1.orderEmbOfFin S.2 a

theorem deningerSubsetTuple_injective (S : {S : Finset (Fin r) // S.card = k}) :
    Function.Injective (deningerSubsetTuple S) :=
  (S.1.orderEmbOfFin S.2).injective

theorem deningerSubsetTuple_range (S : {S : Finset (Fin r) // S.card = k}) :
    Set.range (deningerSubsetTuple S) = ↑S.1 :=
  S.1.range_orderEmbOfFin S.2

/-- **The determinant forms of the `k`-element sets of coordinates are linearly independent.** -/
theorem deningerDetForm_linearIndependent :
    LinearIndependent ℂ fun S : {S : Finset (Fin r) // S.card = k} =>
      deningerDetForm (deningerSubsetTuple S) := by
  classical
  refine Fintype.linearIndependent_iff.2 fun g hg T => ?_
  have hval := congrArg
    (fun A : (Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ =>
      A fun a => (Pi.single (deningerSubsetTuple T a) (1 : ℂ) : Fin r → ℂ)) hg
  simp only [ContinuousAlternatingMap.sum_apply] at hval
  have hterm : ∀ S : {S : Finset (Fin r) // S.card = k}, S ≠ T →
      (g S • deningerDetForm (deningerSubsetTuple S))
        (fun a => (Pi.single (deningerSubsetTuple T a) (1 : ℂ) : Fin r → ℂ)) = 0 := by
    intro S hST
    have hne : ∃ b : Fin k, ∀ a : Fin k,
        deningerSubsetTuple S b ≠ deningerSubsetTuple T a := by
      by_contra hcon
      push Not at hcon
      have hsub : (S.1 : Set (Fin r)) ⊆ (T.1 : Set (Fin r)) := by
        intro x hx
        rw [← deningerSubsetTuple_range S] at hx
        obtain ⟨b, rfl⟩ := hx
        obtain ⟨a, ha⟩ := hcon b
        rw [ha, ← deningerSubsetTuple_range T]
        exact ⟨a, rfl⟩
      have hSTeq : S.1 = T.1 := by
        refine Finset.eq_of_subset_of_card_le ?_ (le_of_eq (by rw [S.2, T.2]))
        exact fun x hx => (Finset.mem_coe).1 (hsub (Finset.mem_coe.2 hx))
      exact hST (Subtype.ext hSTeq)
    obtain ⟨b, hb⟩ := hne
    show g S • deningerDetForm (deningerSubsetTuple S)
      (fun a => (Pi.single (deningerSubsetTuple T a) (1 : ℂ) : Fin r → ℂ)) = 0
    rw [deningerDetForm_single_eq_zero hb, smul_eq_mul, mul_zero]
  rw [Finset.sum_eq_single T (fun S _ hST => hterm S hST)
    (fun h => absurd (Finset.mem_univ T) h)] at hval
  have hone : deningerDetForm (deningerSubsetTuple T)
      (fun a => (Pi.single (deningerSubsetTuple T a) (1 : ℂ) : Fin r → ℂ)) = 1 :=
    deningerDetForm_stdBasis (deningerSubsetTuple_injective T)
  have hzero : (0 : (Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ)
      (fun a => (Pi.single (deningerSubsetTuple T a) (1 : ℂ) : Fin r → ℂ)) = 0 := rfl
  have hexpand : (g T • deningerDetForm (deningerSubsetTuple T))
      (fun a => (Pi.single (deningerSubsetTuple T a) (1 : ℂ) : Fin r → ℂ)) = g T := by
    show g T • (deningerDetForm (deningerSubsetTuple T)
      (fun a => (Pi.single (deningerSubsetTuple T a) (1 : ℂ) : Fin r → ℂ))) = g T
    rw [hone, smul_eq_mul, mul_one]
  rw [hzero, hexpand] at hval
  exact hval

/-- **The determinant forms of the `k`-element sets of coordinates span the constant forms.** -/
theorem deningerDetForm_span_top :
    ⊤ ≤ Submodule.span ℂ (Set.range fun S : {S : Finset (Fin r) // S.card = k} =>
      deningerDetForm (deningerSubsetTuple S)) := by
  classical
  rintro α -
  rw [deningerDetForm_span α]
  refine Submodule.sum_mem _ fun s _ => ?_
  by_cases hs : s.card = k
  · rw [deningerSubsetForm, dif_pos hs]
    refine Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩
  · rw [deningerSubsetForm, dif_neg hs]
    exact Submodule.zero_mem _

/-- **The determinant forms of the `k`-element sets of coordinates are a basis of the constant
alternating forms.** -/
noncomputable def deningerDetFormBasis (r k : ℕ) :
    Module.Basis {S : Finset (Fin r) // S.card = k} ℂ ((Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ) :=
  Module.Basis.mk deningerDetForm_linearIndependent deningerDetForm_span_top

@[simp]
theorem deningerDetFormBasis_apply (S : {S : Finset (Fin r) // S.card = k}) :
    deningerDetFormBasis r k S = deningerDetForm (deningerSubsetTuple S) :=
  Module.Basis.mk_apply _ _ _

end DetFormBasis

end RHTower

namespace RHTower

open Complex

section CohomologyBasis

variable {r n : ℕ}

/-- **The classes of the exterior products of the logarithmic differentials of the `(n+1)`-element
sets of coordinates are a basis of the cohomology of a character stage.**  This is the comparison
`Λ^k(L ⊗ ℂ) ≅ H^k` with its standard basis on both sides. -/
noncomputable def deningerCohomologyBasis (r n : ℕ) :
    Module.Basis {S : Finset (Fin r) // S.card = n + 1} ℂ (deningerCohomology r n) :=
  (deningerDetFormBasis r (n + 1)).map (deningerCohomologyEquiv r n)

theorem deningerCohomologyBasis_apply (S : {S : Finset (Fin r) // S.card = n + 1}) :
    deningerCohomologyBasis r n S =
      Submodule.Quotient.mk ⟨deningerConstantStageForm (deningerDetForm (deningerSubsetTuple S)),
        deningerConstantStageForm_mem _⟩ := by
  show deningerCohomologyEquiv r n (deningerDetFormBasis r (n + 1) S) = _
  rw [deningerDetFormBasis_apply]
  rfl

/-- **The cohomology of a character stage is the exterior power of the lattice**: both are free on
the `k`-element sets of coordinates, the classes of the exterior products of the logarithmic
differentials on one side and the exterior products of the basis vectors on the other. -/
noncomputable def deningerCohomologyExteriorEquiv (r n : ℕ) :
    deningerCohomology r n ≃ₗ[ℂ] ⋀[ℂ]^(n + 1) (Fin r → ℂ) :=
  (deningerCohomologyBasis r n).equiv
    ((Pi.basisFun ℂ (Fin r)).exteriorPower (n + 1)) (Equiv.refl _)

/-- The basis vectors are the classes of the exterior products of logarithmic differentials. -/
theorem deningerCohomologyBasis_eq_dlogWedge (S : {S : Finset (Fin r) // S.card = n + 1})
    (z : Fin r → ℂ) :
    (deningerConstantStageForm (deningerDetForm (deningerSubsetTuple S)) : DeningerStageForm r _) z =
      deningerDlogWedge (deningerSubsetTuple S) z :=
  deningerConstantStageForm_detForm _ z

end CohomologyBasis

end RHTower
