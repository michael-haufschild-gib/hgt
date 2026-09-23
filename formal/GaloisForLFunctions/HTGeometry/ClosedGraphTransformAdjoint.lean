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

/-! ### Transforms between distinct Hilbert carriers -/

/-- The closed graph transform `J B⁻¹` when the input and output Hilbert carriers differ.
The graph coordinate remains a closed subspace of `H₀`, while `B` and `J` are allowed to land in
distinct complete Hilbert spaces.  This is the form needed when a Green symmetry exchanges two
boundary polarizations. -/
def closedGraphTransformBetween
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (K : Submodule ℂ H₀) (B : K →L[ℂ] H₁) (J : K →L[ℂ] H₂) : H₁ →ₗ.[ℂ] H₂ :=
  J.toLinearMap.compPMap (B.toLinearMap.toPMap ⊤).inverse

/-- The bounded injection regarded as a partial map on its full source. -/
def closedGraphTransformBetweenInjectionPMap
    {H₀ H₁ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    (K : Submodule ℂ H₀) (B : K →L[ℂ] H₁) : K →ₗ.[ℂ] H₁ :=
  B.toLinearMap.toPMap ⊤

omit [CompleteSpace H] in
theorem closedGraphTransformBetweenInjectionPMap_toFun_ker_eq_bot
    {H₀ H₁ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    (K : Submodule ℂ H₀) (B : K →L[ℂ] H₁) (hB : Function.Injective B) :
    LinearMap.ker (closedGraphTransformBetweenInjectionPMap K B).toFun = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro x hx
  apply Subtype.ext
  apply hB
  change B (x : K) = B 0
  rw [map_zero]
  exact hx

omit [CompleteSpace H] in
theorem closedGraphTransformBetween_domain
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (K : Submodule ℂ H₀) (B : K →L[ℂ] H₁) (J : K →L[ℂ] H₂) :
    (closedGraphTransformBetween K B J).domain = B.range := by
  change ((closedGraphTransformBetweenInjectionPMap K B).inverse).domain = B.range
  rw [LinearPMap.inverse_domain]
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨(x : K), hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨⟨x, by simp [closedGraphTransformBetweenInjectionPMap]⟩, hx⟩

theorem closedGraphTransformBetween_apply_B
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (K : Submodule ℂ H₀) (B : K →L[ℂ] H₁) (J : K →L[ℂ] H₂)
    (hB : Function.Injective B) (x : K) :
    B x ∈ (closedGraphTransformBetween K B J).domain ∧
      closedGraphTransformBetween K B J
        ⟨B x, by simpa [closedGraphTransformBetween_domain]⟩ = J x := by
  have hmem : B x ∈ (closedGraphTransformBetween K B J).domain := by
    rw [closedGraphTransformBetween_domain]
    exact ⟨x, rfl⟩
  refine ⟨hmem, ?_⟩
  change J
      ((closedGraphTransformBetweenInjectionPMap K B).inverse
        ⟨B x, by
          rw [LinearPMap.inverse_domain]
          exact ⟨⟨x, by simp [closedGraphTransformBetweenInjectionPMap]⟩, rfl⟩⟩) = J x
  exact congrArg J (LinearPMap.inverse_apply_eq
    (closedGraphTransformBetweenInjectionPMap_toFun_ker_eq_bot K B hB)
    (x := ⟨x, by simp [closedGraphTransformBetweenInjectionPMap]⟩)
    (y := ⟨B x, by
      rw [LinearPMap.inverse_domain]
      exact ⟨⟨x, by simp [closedGraphTransformBetweenInjectionPMap]⟩, rfl⟩⟩)
    rfl)

/-- Exact maximal-adjoint domain of a transform between different Hilbert carriers. -/
theorem closedGraphTransformBetween_mem_adjoint_domain_iff
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (K : Submodule ℂ H₀) [CompleteSpace K] (B : K →L[ℂ] H₁) (J : K →L[ℂ] H₂)
    (hB : Function.Injective B) (hDense : Dense (B.range : Set H₁)) (y : H₂) :
    y ∈ (closedGraphTransformBetween K B J).adjoint.domain ↔
      J.adjoint y ∈ B.adjoint.range := by
  let A := closedGraphTransformBetween K B J
  have hAdense : Dense (A.domain : Set H₁) := by
    rw [closedGraphTransformBetween_domain]
    exact hDense
  constructor
  · intro hydom
    let yAdj : A.adjoint.domain := ⟨y, hydom⟩
    let z : H₁ := A.adjoint yAdj
    refine ⟨z, ?_⟩
    apply ext_inner_right ℂ
    intro k
    have hBkDom : B k ∈ A.domain :=
      (closedGraphTransformBetween_apply_B K B J hB k).1
    let x : A.domain := ⟨B k, hBkDom⟩
    have hAx : A x = J k := by
      simpa only [A, x] using (closedGraphTransformBetween_apply_B K B J hB k).2
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
    have hxRange : (x : H₁) ∈ B.range := by
      rw [← closedGraphTransformBetween_domain K B J]
      exact x.property
    rcases hxRange with ⟨k, hk⟩
    have hAx : A x = J k := by
      have h := (closedGraphTransformBetween_apply_B K B J hB k).2
      have heq : x = ⟨B k, (closedGraphTransformBetween_apply_B K B J hB k).1⟩ :=
        Subtype.ext hk.symm
      exact (congrArg A heq).trans h
    calc
      inner ℂ z (x : H₁) = inner ℂ z (B k) := congrArg (inner ℂ z) hk.symm
      _ = inner ℂ (B.adjoint z) k := (B.adjoint_inner_left k z).symm
      _ = inner ℂ (J.adjoint y) k := congrArg (fun q : K => inner ℂ q k) hz
      _ = inner ℂ y (J k) := J.adjoint_inner_left k y
      _ = inner ℂ y (A x) := congrArg (inner ℂ y) hAx.symm

/-- Exact action of the heterogeneous maximal adjoint. -/
theorem closedGraphTransformBetween_adjoint_apply_of_eq_adjoint
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (K : Submodule ℂ H₀) [CompleteSpace K] (B : K →L[ℂ] H₁) (J : K →L[ℂ] H₂)
    (hB : Function.Injective B) (hDense : DenseRange B)
    (y : H₂) (z : H₁) (hz : B.adjoint z = J.adjoint y)
    (hydom : y ∈ (closedGraphTransformBetween K B J).adjoint.domain) :
    (closedGraphTransformBetween K B J).adjoint ⟨y, hydom⟩ = z := by
  let A := closedGraphTransformBetween K B J
  have hAdense : Dense (A.domain : Set H₁) := by
    rw [closedGraphTransformBetween_domain]
    exact hDense
  apply LinearPMap.adjoint_apply_eq hAdense
  intro x
  have hxRange : (x : H₁) ∈ B.range := by
    rw [← closedGraphTransformBetween_domain K B J]
    exact x.property
  rcases hxRange with ⟨k, hk⟩
  have hAx : A x = J k := by
    have h := (closedGraphTransformBetween_apply_B K B J hB k).2
    have heq : x = ⟨B k, (closedGraphTransformBetween_apply_B K B J hB k).1⟩ :=
      Subtype.ext hk.symm
    exact (congrArg A heq).trans h
  calc
    inner ℂ z (x : H₁) = inner ℂ z (B k) := congrArg (inner ℂ z) hk.symm
    _ = inner ℂ (B.adjoint z) k := (B.adjoint_inner_left k z).symm
    _ = inner ℂ (J.adjoint y) k := congrArg (fun q : K => inner ℂ q k) hz
    _ = inner ℂ y (J k) := J.adjoint_inner_left k y
    _ = inner ℂ y (A x) := congrArg (inner ℂ y) hAx.symm

/-- Named maximal adjoint of a transform between distinct Hilbert carriers. -/
noncomputable def closedGraphTransformBetweenAdjoint
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
    (K : Submodule ℂ H₀) (B : K →L[ℂ] H₁) (J : K →L[ℂ] H₂) : H₂ →ₗ.[ℂ] H₁ :=
  (closedGraphTransformBetween K B J).adjoint

/-- Bounded source data for a closed transform between two Hilbert carriers.  Packaging density
with its maps prevents clients from repeatedly elaborating a large range expression. -/
structure ClosedGraphTransformBetweenDatum
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (K : Submodule ℂ H₀) [CompleteSpace K] where
  B : K →L[ℂ] H₁
  J : K →L[ℂ] H₂
  hB : Function.Injective B
  hDense : DenseRange B

/-- Closed transform attached to packaged bounded source data. -/
noncomputable def closedGraphTransformBetweenOfDatum
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (K : Submodule ℂ H₀) [CompleteSpace K]
    (D : ClosedGraphTransformBetweenDatum
      (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) K) : H₁ →ₗ.[ℂ] H₂ :=
  closedGraphTransformBetween K D.B D.J

/-- Maximal adjoint of the closed transform attached to packaged bounded source data. -/
noncomputable def closedGraphTransformBetweenAdjointOfDatum
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (K : Submodule ℂ H₀) [CompleteSpace K]
    (D : ClosedGraphTransformBetweenDatum
      (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) K) : H₂ →ₗ.[ℂ] H₁ :=
  closedGraphTransformBetweenAdjoint K D.B D.J

/-- A pairing identity on the bounded source maps directly constructs the maximal-adjoint witness.
This avoids requiring a concrete client module to elaborate bounded adjoints merely to express the
same Riesz identity. -/
theorem closedGraphTransformBetween_adjoint_exists_of_pairing
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (K : Submodule ℂ H₀) [CompleteSpace K] (B : K →L[ℂ] H₁) (J : K →L[ℂ] H₂)
    (hB : Function.Injective B) (hDense : DenseRange B)
    (z : H₁) (y : H₂) (hpair : ∀ k : K, inner ℂ z (B k) = inner ℂ y (J k)) :
    ∃ hy : y ∈ (closedGraphTransformBetweenAdjoint K B J).domain,
      closedGraphTransformBetweenAdjoint K B J ⟨y, hy⟩ = z := by
  let A := closedGraphTransformBetween K B J
  have hAdense : Dense (A.domain : Set H₁) := by
    rw [closedGraphTransformBetween_domain]
    exact hDense
  have hyDom : y ∈ A.adjoint.domain := by
    apply LinearPMap.mem_adjoint_domain_of_exists
    refine ⟨z, ?_⟩
    intro x
    have hxRange : (x : H₁) ∈ B.range := by
      rw [← closedGraphTransformBetween_domain K B J]
      exact x.property
    rcases hxRange with ⟨k, hk⟩
    have hAx : A x = J k := by
      have h := (closedGraphTransformBetween_apply_B K B J hB k).2
      have heq : x = ⟨B k, (closedGraphTransformBetween_apply_B K B J hB k).1⟩ :=
        Subtype.ext hk.symm
      exact (congrArg A heq).trans h
    calc
      inner ℂ z (x : H₁) = inner ℂ z (B k) := congrArg (inner ℂ z) hk.symm
      _ = inner ℂ y (J k) := hpair k
      _ = inner ℂ y (A x) := congrArg (inner ℂ y) hAx.symm
  have hyDom' : y ∈ (closedGraphTransformBetweenAdjoint K B J).domain := by
    change y ∈ A.adjoint.domain
    exact hyDom
  refine ⟨hyDom', ?_⟩
  change A.adjoint ⟨y, hyDom'⟩ = z
  apply LinearPMap.adjoint_apply_eq hAdense
  intro x
  have hxRange : (x : H₁) ∈ B.range := by
    rw [← closedGraphTransformBetween_domain K B J]
    exact x.property
  rcases hxRange with ⟨k, hk⟩
  have hAx : A x = J k := by
    have h := (closedGraphTransformBetween_apply_B K B J hB k).2
    have heq : x = ⟨B k, (closedGraphTransformBetween_apply_B K B J hB k).1⟩ :=
      Subtype.ext hk.symm
    exact (congrArg A heq).trans h
  calc
    inner ℂ z (x : H₁) = inner ℂ z (B k) := congrArg (inner ℂ z) hk.symm
    _ = inner ℂ y (J k) := hpair k
    _ = inner ℂ y (A x) := congrArg (inner ℂ y) hAx.symm

/-- The graph form of the pairing construction. It keeps the domain witness out of client
theorem statements, which is useful when a maximal adjoint has a large definitional domain. -/
theorem closedGraphTransformBetween_mem_adjoint_graph_of_pairing
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (K : Submodule ℂ H₀) [CompleteSpace K] (B : K →L[ℂ] H₁) (J : K →L[ℂ] H₂)
    (hB : Function.Injective B) (hDense : DenseRange B)
    (z : H₁) (y : H₂) (hpair : ∀ k : K, inner ℂ z (B k) = inner ℂ y (J k)) :
    (y, z) ∈ (closedGraphTransformBetweenAdjoint K B J).graph := by
  obtain ⟨hy, hvalue⟩ := closedGraphTransformBetween_adjoint_exists_of_pairing
    K B J hB hDense z y hpair
  rw [LinearPMap.mem_graph_iff]
  exact ⟨⟨y, hy⟩, rfl, hvalue⟩

/-- Packaged-data graph form of the pairing construction. -/
theorem ClosedGraphTransformBetweenDatum.mem_adjoint_graph_of_pairing
    {H₀ H₁ H₂ : Type*}
    [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (K : Submodule ℂ H₀) [CompleteSpace K]
    (D : ClosedGraphTransformBetweenDatum
      (H₀ := H₀) (H₁ := H₁) (H₂ := H₂) K)
    (z : H₁) (y : H₂) (hpair : ∀ k : K, inner ℂ z (D.B k) = inner ℂ y (D.J k)) :
    (y, z) ∈ (closedGraphTransformBetweenAdjointOfDatum K D).graph := by
  exact closedGraphTransformBetween_mem_adjoint_graph_of_pairing
    K D.B D.J D.hB D.hDense z y hpair

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
