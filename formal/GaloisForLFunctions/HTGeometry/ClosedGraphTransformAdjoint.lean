import GaloisForLFunctions.HTGeometry.ClosedHyperplaneInverse

/-!
# Adjoint of a closed graph transform

For an injective bounded map `B : K → H` with dense range and a bounded output map
`J : K → H`, the closed graph transform is the literal unbounded operator

`A = J B⁻¹`,  `D(A) = ran(B)`.

This module identifies the maximal Hilbert-space adjoint without assuming any regularity beyond
the stated bounded maps:

`y ∈ D(A†) ↔ J† y ∈ ran(B†)`.

It also proves the exact graph action: if `B† z = J† y`, then `A† y = z`.
-/

open Module Topology Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Exact maximal-adjoint domain of `J B⁻¹`.  The range condition is mathematical content: it is
the weak regularity equation that must be proved for a vector before applying the unbounded
adjoint. -/
theorem closedGraphTransform_mem_adjoint_domain_iff
    (K : Submodule ℂ H) [CompleteSpace K] (B J : K →L[ℂ] H)
    (hB : Function.Injective B) (hDense : Dense (B.range : Set H)) (y : H) :
    y ∈ (closedGraphTransform K B J).adjoint.domain ↔
      J.adjoint y ∈ B.adjoint.range := by
  let A := closedGraphTransform K B J
  have hAdense : Dense (A.domain : Set H) := by
    rw [closedGraphTransform_domain]
    exact hDense
  constructor
  · intro hydom
    let yAdj : A.adjoint.domain := ⟨y, hydom⟩
    let z : H := A.adjoint yAdj
    refine ⟨z, ?_⟩
    apply ext_inner_right ℂ
    intro k
    have hBkDom : B k ∈ A.domain :=
      (closedGraphTransform_apply_B K B J hB k).1
    let x : A.domain := ⟨B k, hBkDom⟩
    have hAx : A x = J k := by
      simpa only [A, x] using (closedGraphTransform_apply_B K B J hB k).2
    have hformal := LinearPMap.adjoint_isFormalAdjoint hAdense yAdj x
    calc
      inner ℂ (B.adjoint z) k = inner ℂ z (B k) := B.adjoint_inner_left k z
      _ = inner ℂ y (A x) := hformal
      _ = inner ℂ y (J k) := by rw [hAx]
      _ = inner ℂ (J.adjoint y) k := (J.adjoint_inner_left k y).symm
  · rintro ⟨z, hz⟩
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨z, ?_⟩
    intro x
    have hxRange : (x : H) ∈ B.range := by
      rw [← closedGraphTransform_domain K B J]
      exact x.property
    rcases hxRange with ⟨k, hk⟩
    have hAx : A x = J k := by
      have h := (closedGraphTransform_apply_B K B J hB k).2
      have heq : x = ⟨B k, (closedGraphTransform_apply_B K B J hB k).1⟩ :=
        Subtype.ext hk.symm
      exact (congrArg A heq).trans h
    calc
      inner ℂ z (x : H) = inner ℂ z (B k) := congrArg (inner ℂ z) hk.symm
      _ = inner ℂ (B.adjoint z) k := (B.adjoint_inner_left k z).symm
      _ = inner ℂ (J.adjoint y) k := congrArg (fun q : K => inner ℂ q k) hz
      _ = inner ℂ y (J k) := J.adjoint_inner_left k y
      _ = inner ℂ y (A x) := congrArg (inner ℂ y) hAx.symm

/-- Exact action of the maximal adjoint of `J B⁻¹`: a solution of the bounded adjoint equation
`B† z = J† y` is necessarily the value of the unbounded adjoint at `y`. -/
theorem closedGraphTransform_adjoint_apply_of_eq_adjoint
    (K : Submodule ℂ H) [CompleteSpace K] (B J : K →L[ℂ] H)
    (hB : Function.Injective B) (hDense : Dense (B.range : Set H))
    (y z : H) (hz : B.adjoint z = J.adjoint y)
    (hydom : y ∈ (closedGraphTransform K B J).adjoint.domain) :
    (closedGraphTransform K B J).adjoint ⟨y, hydom⟩ = z := by
  let A := closedGraphTransform K B J
  have hAdense : Dense (A.domain : Set H) := by
    rw [closedGraphTransform_domain]
    exact hDense
  apply LinearPMap.adjoint_apply_eq hAdense
  intro x
  have hxRange : (x : H) ∈ B.range := by
    rw [← closedGraphTransform_domain K B J]
    exact x.property
  rcases hxRange with ⟨k, hk⟩
  have hAx : A x = J k := by
    have h := (closedGraphTransform_apply_B K B J hB k).2
    have heq : x = ⟨B k, (closedGraphTransform_apply_B K B J hB k).1⟩ :=
      Subtype.ext hk.symm
    exact (congrArg A heq).trans h
  calc
    inner ℂ z (x : H) = inner ℂ z (B k) := congrArg (inner ℂ z) hk.symm
    _ = inner ℂ (B.adjoint z) k := (B.adjoint_inner_left k z).symm
    _ = inner ℂ (J.adjoint y) k := congrArg (fun q : K => inner ℂ q k) hz
    _ = inner ℂ y (J k) := J.adjoint_inner_left k y
    _ = inner ℂ y (A x) := congrArg (inner ℂ y) hAx.symm

end

end GaloisForLFunctions.HTGeometry
