import GaloisForLFunctions.RHTower.Deninger.DeningerStageConstantForm
import GaloisForLFunctions.RHTower.Deninger.DeningerWedgePullback
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# The determinant forms span the constant forms

The determinant form of a selection of `k` coordinates evaluates on a tuple of coordinate vectors to
the determinant of the incidence matrix of the two selections: zero when the selections differ, and
the sign of the permutation relating them when they agree.  So the determinant forms of the
`k`-element sets of coordinates span the constant alternating forms, and the stage form defined by a
determinant form is the exterior product of the corresponding logarithmic differentials.

* `deningerConstantStageForm_detForm` : the constant stage form of a determinant form is the
  exterior product of logarithmic differentials.
* `deningerDetForm_span` : every constant alternating form is a combination of determinant forms.
-/

namespace RHTower

open Complex Finset ContinuousAlternatingMap

section WedgeIsConstant

variable {r k : ℕ}

/-- **The constant stage form of a determinant form is the exterior product of the logarithmic
differentials** of the selected coordinates. -/
theorem deningerConstantStageForm_detForm (σ : Fin k → Fin r) (z : Fin r → ℂ) :
    deningerConstantStageForm (deningerDetForm σ) z = deningerDlogWedge σ z := by
  ext v
  show deningerDetForm σ (fun i => deningerLogBranchDeriv z (v i)) = deningerDlogWedge σ z v
  rw [deningerDetForm_apply, deningerDlogWedge_apply, deningerDetForm_apply]
  have hmat : (Matrix.of fun a b => (deningerLogBranchDeriv z (v a)) (σ b)) =
      Matrix.of fun a b => (z (σ b))⁻¹ * (Matrix.of fun a b => v a (σ b)) a b := by
    ext a b
    show (z (σ b))⁻¹ * v a (σ b) = (z (σ b))⁻¹ * v a (σ b)
    rfl
  rw [hmat, Matrix.det_mul_row]

end WedgeIsConstant

end RHTower

namespace RHTower

open Complex Finset ContinuousAlternatingMap

section DetFormValues

variable {r k : ℕ}

/-- The value of a determinant form on a tuple of coordinate vectors is the determinant of the
incidence matrix of the two selections. -/
theorem deningerDetForm_apply_single (σ v : Fin k → Fin r) :
    deningerDetForm σ (fun a => (Pi.single (v a) (1 : ℂ) : Fin r → ℂ)) =
      Matrix.det (Matrix.of fun a b => if σ b = v a then (1 : ℂ) else 0) := by
  rw [deningerDetForm_apply]
  congr 1
  ext a b
  show (Pi.single (v a) (1 : ℂ) : Fin r → ℂ) (σ b) = if σ b = v a then (1 : ℂ) else 0
  rw [Pi.single_apply]

/-- A determinant form vanishes on a tuple of coordinate vectors missing one of its coordinates. -/
theorem deningerDetForm_single_eq_zero {σ v : Fin k → Fin r} {b : Fin k}
    (hb : ∀ a : Fin k, σ b ≠ v a) :
    deningerDetForm σ (fun a => (Pi.single (v a) (1 : ℂ) : Fin r → ℂ)) = 0 := by
  rw [deningerDetForm_apply_single]
  refine Matrix.det_eq_zero_of_column_eq_zero b fun a => ?_
  show (if σ b = v a then (1 : ℂ) else 0) = 0
  rw [if_neg (hb a)]

/-- A determinant form evaluates to the sign of the permutation relating the two selections. -/
theorem deningerDetForm_single_perm {σ : Fin k → Fin r} (hσ : Function.Injective σ)
    (τ : Equiv.Perm (Fin k)) :
    deningerDetForm σ ((fun a => (Pi.single (σ a) (1 : ℂ) : Fin r → ℂ)) ∘ τ) =
      ((Equiv.Perm.sign τ : ℤ) : ℂ) := by
  classical
  have hfun : ((fun a => (Pi.single (σ a) (1 : ℂ) : Fin r → ℂ)) ∘ τ) =
      fun a => (Pi.single (σ (τ a)) (1 : ℂ) : Fin r → ℂ) := rfl
  rw [hfun, deningerDetForm_apply_single]
  have hmat : (Matrix.of fun a b => if σ b = σ (τ a) then (1 : ℂ) else 0) =
      Equiv.Perm.permMatrix ℂ τ := by
    ext a b
    show (if σ b = σ (τ a) then (1 : ℂ) else 0) = _
    rw [show ((Equiv.Perm.permMatrix ℂ τ) a b) = if τ a = b then (1 : ℂ) else 0 by
      simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]]
    by_cases h : τ a = b
    · rw [if_pos h, if_pos (congrArg σ h.symm)]
    · rw [if_neg h, if_neg fun hc => h (hσ hc).symm]
  rw [hmat, Matrix.det_permutation]

/-- The determinant form of an injective selection reproduces the value of a constant form on the
corresponding tuple of coordinate vectors. -/
theorem deningerSmul_detForm_perm {α : (Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ} {σ v : Fin k → Fin r}
    (hσ : Function.Injective σ) (τ : Equiv.Perm (Fin k)) (hvτ : ∀ a, v a = σ (τ a)) :
    (α fun a => (Pi.single (σ a) (1 : ℂ) : Fin r → ℂ)) •
        deningerDetForm σ (fun a => (Pi.single (v a) (1 : ℂ) : Fin r → ℂ)) =
      α fun a => (Pi.single (v a) (1 : ℂ) : Fin r → ℂ) := by
  have hvfun : (fun a => (Pi.single (v a) (1 : ℂ) : Fin r → ℂ)) =
      (fun a => (Pi.single (σ a) (1 : ℂ) : Fin r → ℂ)) ∘ τ := by
    funext a
    show (Pi.single (v a) (1 : ℂ) : Fin r → ℂ) = (Pi.single (σ (τ a)) (1 : ℂ) : Fin r → ℂ)
    rw [hvτ a]
  have hperm : α ((fun a => (Pi.single (σ a) (1 : ℂ) : Fin r → ℂ)) ∘ τ) =
      Equiv.Perm.sign τ • α fun a => (Pi.single (σ a) (1 : ℂ) : Fin r → ℂ) :=
    α.map_perm _ τ
  rw [hvfun, hperm, deningerDetForm_single_perm hσ τ]
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h1 | h1 <;> rw [h1] <;> simp

end DetFormValues

end RHTower

namespace RHTower

open Complex Finset ContinuousAlternatingMap

section DetFormSpan

variable {r k : ℕ}

/-- The component of a constant form along a `k`-element set of coordinates. -/
noncomputable def deningerSubsetForm (α : (Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ) (s : Finset (Fin r)) :
    (Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ :=
  if h : s.card = k then
    (α fun a => (Pi.single (s.orderEmbOfFin h a) (1 : ℂ) : Fin r → ℂ)) •
      deningerDetForm (fun a => s.orderEmbOfFin h a)
  else 0

/-- **Every constant alternating form is a combination of the determinant forms** of the
`k`-element sets of coordinates.  Both sides agree on every tuple of distinct coordinate vectors:
only the set of those coordinates contributes, and there the determinant form produces the sign of
the permutation that sorts the tuple. -/
theorem deningerDetForm_span (α : (Fin r → ℂ) [⋀^Fin k]→L[ℂ] ℂ) :
    α = ∑ s : Finset (Fin r), deningerSubsetForm α s := by
  classical
  refine ContinuousAlternatingMap.toAlternatingMap_injective ?_
  refine (Pi.basisFun ℂ (Fin r)).ext_alternating fun v hv => ?_
  have hbasis : ∀ i : Fin k, (Pi.basisFun ℂ (Fin r)) (v i) =
      (Pi.single (v i) (1 : ℂ) : Fin r → ℂ) := fun i => by
    simp [Pi.basisFun_apply]
  show α (fun i => (Pi.basisFun ℂ (Fin r)) (v i)) =
    (∑ s : Finset (Fin r), deningerSubsetForm α s) fun i => (Pi.basisFun ℂ (Fin r)) (v i)
  simp only [hbasis]
  have hcard : (Finset.image v Finset.univ).card = k := by
    rw [Finset.card_image_of_injective _ hv, Finset.card_univ, Fintype.card_fin]
  have hσinj : Function.Injective
      (fun a => (Finset.image v Finset.univ).orderEmbOfFin hcard a) :=
    ((Finset.image v Finset.univ).orderEmbOfFin hcard).injective
  have hvrange : Set.range v = ↑(Finset.image v Finset.univ) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨a, Finset.mem_univ a, rfl⟩)
    · intro hx
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
      exact ⟨a, ha⟩
  have hmem : ∀ a : Fin k, ∃ b : Fin k,
      (Finset.image v Finset.univ).orderEmbOfFin hcard b = v a := by
    intro a
    have hx : v a ∈ Set.range (fun b => (Finset.image v Finset.univ).orderEmbOfFin hcard b) := by
      rw [show Set.range (fun b => (Finset.image v Finset.univ).orderEmbOfFin hcard b) =
        ↑(Finset.image v Finset.univ) from
          (Finset.image v Finset.univ).range_orderEmbOfFin hcard, ← hvrange]
      exact ⟨a, rfl⟩
    exact hx
  choose g hg using hmem
  have hginj : Function.Injective g := by
    intro a b hab
    have hval : v a = v b := by rw [← hg a, ← hg b, hab]
    exact hv hval
  have hbij : Function.Bijective g := ⟨hginj, Finite.injective_iff_surjective.1 hginj⟩
  rw [ContinuousAlternatingMap.sum_apply, Finset.sum_eq_single (Finset.image v Finset.univ)]
  · rw [deningerSubsetForm, dif_pos hcard]
    exact (deningerSmul_detForm_perm (α := α) hσinj (Equiv.ofBijective g hbij)
      fun a => (hg a).symm).symm
  · intro s _ hs
    rw [deningerSubsetForm]
    by_cases hc : s.card = k
    · rw [dif_pos hc]
      show (α fun a => (Pi.single (s.orderEmbOfFin hc a) (1 : ℂ) : Fin r → ℂ)) •
        deningerDetForm (fun a => s.orderEmbOfFin hc a)
          (fun a => (Pi.single (v a) (1 : ℂ) : Fin r → ℂ)) = 0
      have hne : ∃ b : Fin k, ∀ a : Fin k, s.orderEmbOfFin hc b ≠ v a := by
        by_contra hcon
        push Not at hcon
        have hsub : ↑s ⊆ Set.range v := by
          intro x hx
          obtain ⟨b, hb⟩ : ∃ b : Fin k, s.orderEmbOfFin hc b = x := by
            have hr := s.range_orderEmbOfFin hc
            rw [← hr] at hx
            exact hx
          obtain ⟨a, ha⟩ := hcon b
          exact ⟨a, by rw [← ha, hb]⟩
        have hseq : s = Finset.image v Finset.univ := by
          refine Finset.eq_of_subset_of_card_le ?_ (le_of_eq (by rw [hcard, hc]))
          intro x hx
          have hxr : x ∈ Set.range v := hsub hx
          rw [hvrange] at hxr
          exact hxr
        exact hs hseq
      obtain ⟨b, hb⟩ := hne
      rw [deningerDetForm_single_eq_zero hb]
      show (α fun a => (Pi.single (s.orderEmbOfFin hc a) (1 : ℂ) : Fin r → ℂ)) • (0 : ℂ) = 0
      rw [smul_eq_mul, mul_zero]
    · rw [dif_neg hc]
      rfl
  · intro hcon
    exact absurd (Finset.mem_univ (Finset.image v Finset.univ)) hcon

end DetFormSpan

end RHTower
