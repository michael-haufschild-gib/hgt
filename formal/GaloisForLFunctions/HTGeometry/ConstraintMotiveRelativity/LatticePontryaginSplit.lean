import Mathlib

/-!
# The integral part of a real subspace and its character sequence

For a lattice `Λ` in a real vector space and a real subspace `V`, the integral part
`Λ_V = Λ ∩ V` is a *primitive* sublattice: the quotient `Λ / Λ_V` is torsion free, hence free,
hence the quotient map splits.  Consequently, for every abelian target `T` the restriction of
characters

`0 → Hom(Λ/Λ_V, T) → Hom(Λ, T) → Hom(Λ_V, T) → 0`

is exact.  With `T` the circle group and `Λ` discrete this is the Pontryagin sequence attached to
a capacity horizon.  If `V` is spanned by lattice vectors then `Λ_V` spans `V`, so its rank is
`dim V`.
-/

namespace HTGeometry.ConstraintMotiveRelativity

section IntegralPart

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
variable (Λ : Submodule ℤ Y) (V : Submodule ℝ Y)

/-- The integral part `Λ ∩ V`, as a sublattice of `Λ`. -/
def latticePart : Submodule ℤ ↥Λ := (V.restrictScalars ℤ).comap Λ.subtype

@[simp] theorem mem_latticePart {z : ↥Λ} : z ∈ latticePart Λ V ↔ (z : Y) ∈ V := Iff.rfl

/-- **Primitivity.**  A lattice vector with a nonzero multiple inside `V` already lies in `V`. -/
theorem latticePart_primitive {m : ℤ} (hm : m ≠ 0) {z : ↥Λ}
    (h : m • z ∈ latticePart Λ V) : z ∈ latticePart Λ V := by
  rw [mem_latticePart] at h ⊢
  have hcoe : ((m • z : ↥Λ) : Y) = (m : ℝ) • (z : Y) := by
    rw [SetLike.val_smul]
    exact (Int.cast_smul_eq_zsmul ℝ m (z : Y)).symm
  rw [hcoe] at h
  have hmR : (m : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hy := V.smul_mem ((m : ℝ)⁻¹) h
  rwa [smul_smul, inv_mul_cancel₀ hmR, one_smul] at hy

/-- The quotient by the integral part is torsion free. -/
theorem isTorsionFree_quotient : Module.IsTorsionFree ℤ (↥Λ ⧸ latticePart Λ V) := by
  refine ⟨fun {m} hm => ?_⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact (not_isRegular_zero (R := ℤ)) hm
  intro z w hzw
  obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective (latticePart Λ V) z
  obtain ⟨w', rfl⟩ := Submodule.Quotient.mk_surjective (latticePart Λ V) w
  have hzw' : Submodule.Quotient.mk (p := latticePart Λ V) (m • z')
      = Submodule.Quotient.mk (p := latticePart Λ V) (m • w') := by
    rw [Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul]
    exact hzw
  have hsub : m • z' - m • w' ∈ latticePart Λ V := (Submodule.Quotient.eq _).1 hzw'
  have hmem : m • (z' - w') ∈ latticePart Λ V := by rwa [smul_sub]
  exact (Submodule.Quotient.eq _).2 (latticePart_primitive Λ V hm0 hmem)

/-- The quotient by the integral part is free. -/
theorem free_quotient [Module.Finite ℤ ↥Λ] : Module.Free ℤ (↥Λ ⧸ latticePart Λ V) := by
  haveI := isTorsionFree_quotient Λ V
  haveI : Module.Finite ℤ (↥Λ ⧸ latticePart Λ V) := Module.Finite.quotient ℤ (latticePart Λ V)
  exact Module.free_of_finite_type_torsion_free'

/-- **The quotient map splits.** -/
theorem exists_splitting [Module.Finite ℤ ↥Λ] :
    ∃ g : (↥Λ ⧸ latticePart Λ V) →ₗ[ℤ] ↥Λ,
      (latticePart Λ V).mkQ ∘ₗ g = LinearMap.id := by
  classical
  haveI hfree : Module.Free ℤ (↥Λ ⧸ latticePart Λ V) := free_quotient Λ V
  set b := Module.Free.chooseBasis ℤ (↥Λ ⧸ latticePart Λ V) with hb
  choose lift hlift using fun i => Submodule.mkQ_surjective (latticePart Λ V) (b i)
  refine ⟨(Finsupp.linearCombination ℤ lift) ∘ₗ b.repr.toLinearMap, b.ext fun i => ?_⟩
  show (latticePart Λ V).mkQ
      ((Finsupp.linearCombination ℤ lift) (b.repr (b i))) = b i
  rw [b.repr_self, Finsupp.linearCombination_single, one_smul, hlift i]

variable (T : Type*) [AddCommGroup T] [Module ℤ T]

/-- Restriction of characters to the integral part. -/
def restrictChar : (↥Λ →ₗ[ℤ] T) →ₗ[ℤ] (↥(latticePart Λ V) →ₗ[ℤ] T) where
  toFun φ := φ ∘ₗ (latticePart Λ V).subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Inflation of characters from the quotient. -/
def inflateChar : ((↥Λ ⧸ latticePart Λ V) →ₗ[ℤ] T) →ₗ[ℤ] (↥Λ →ₗ[ℤ] T) where
  toFun ψ := ψ ∘ₗ (latticePart Λ V).mkQ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **Left exactness.**  Inflation is injective. -/
theorem inflateChar_injective : Function.Injective (inflateChar Λ V T) := by
  intro ψ₁ ψ₂ h
  ext z
  exact congrArg (fun f : ↥Λ →ₗ[ℤ] T => f z) h

/-- **Exactness in the middle.**  A character vanishes on the integral part exactly when it is
inflated from the quotient. -/
theorem range_inflateChar :
    LinearMap.range (inflateChar Λ V T) = LinearMap.ker (restrictChar Λ V T) := by
  ext φ
  constructor
  · rintro ⟨ψ, rfl⟩
    ext z
    have hz : ((z : ↥Λ)) ∈ latticePart Λ V := z.2
    have hzero : (latticePart Λ V).mkQ (z : ↥Λ) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hz
    show ψ ((latticePart Λ V).mkQ (z : ↥Λ)) = 0
    rw [hzero, map_zero]
  · intro hφ
    have hker : ∀ z ∈ latticePart Λ V, φ z = 0 := by
      intro z hz
      have h := congrArg (fun f : ↥(latticePart Λ V) →ₗ[ℤ] T => f ⟨z, hz⟩) hφ
      simpa [restrictChar] using h
    exact ⟨(latticePart Λ V).liftQ φ hker, by ext z; rfl⟩

/-- **Right exactness.**  Every character of the integral part extends to the whole lattice. -/
theorem restrictChar_surjective [Module.Finite ℤ ↥Λ] :
    Function.Surjective (restrictChar Λ V T) := by
  obtain ⟨g, hg⟩ := exists_splitting Λ V
  intro ψ
  have hmk : ∀ z : ↥Λ, (latticePart Λ V).mkQ (g ((latticePart Λ V).mkQ z))
      = (latticePart Λ V).mkQ z := fun z =>
    congrArg (fun f : (↥Λ ⧸ latticePart Λ V) →ₗ[ℤ] (↥Λ ⧸ latticePart Λ V) =>
      f ((latticePart Λ V).mkQ z)) hg
  have hmem : ∀ z : ↥Λ, z - g ((latticePart Λ V).mkQ z) ∈ latticePart Λ V := by
    intro z
    rw [← Submodule.Quotient.mk_eq_zero]
    show (latticePart Λ V).mkQ (z - g ((latticePart Λ V).mkQ z)) = 0
    rw [map_sub, hmk z, sub_self]
  refine ⟨{ toFun := fun z => ψ ⟨z - g ((latticePart Λ V).mkQ z), hmem z⟩
            map_add' := ?_
            map_smul' := ?_ }, ?_⟩
  · intro z w
    have hval : (⟨z + w - g ((latticePart Λ V).mkQ (z + w)), hmem (z + w)⟩ :
        ↥(latticePart Λ V))
        = ⟨z - g ((latticePart Λ V).mkQ z), hmem z⟩
          + ⟨w - g ((latticePart Λ V).mkQ w), hmem w⟩ := by
      apply Subtype.ext
      show z + w - g ((latticePart Λ V).mkQ (z + w))
        = (z - g ((latticePart Λ V).mkQ z)) + (w - g ((latticePart Λ V).mkQ w))
      rw [map_add, map_add]
      abel
    rw [hval, map_add]
  · intro t z
    have hval : (⟨t • z - g ((latticePart Λ V).mkQ (t • z)), hmem (t • z)⟩ :
        ↥(latticePart Λ V))
        = t • ⟨z - g ((latticePart Λ V).mkQ z), hmem z⟩ := by
      apply Subtype.ext
      show t • z - g ((latticePart Λ V).mkQ (t • z))
        = t • (z - g ((latticePart Λ V).mkQ z))
      rw [map_smul, map_smul, smul_sub]
    rw [hval, ψ.map_smul, RingHom.id_apply]
  · ext z
    have hz : ((z : ↥Λ)) ∈ latticePart Λ V := z.2
    have hzero : (latticePart Λ V).mkQ (z : ↥Λ) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hz
    show ψ ⟨(z : ↥Λ) - g ((latticePart Λ V).mkQ (z : ↥Λ)), hmem _⟩ = ψ z
    congr 1
    apply Subtype.ext
    show (z : ↥Λ) - g ((latticePart Λ V).mkQ (z : ↥Λ)) = (z : ↥Λ)
    rw [hzero, map_zero, sub_zero]

/-- **The integral part spans the subspace** when the subspace is spanned by lattice vectors. -/
theorem span_latticePart (s : Set Y) (hs : s ⊆ (Λ : Set Y)) (hV : Submodule.span ℝ s = V) :
    Submodule.span ℝ ((fun z : ↥Λ => (z : Y)) '' (latticePart Λ V : Set ↥Λ)) = V := by
  refine le_antisymm (Submodule.span_le.2 ?_) ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact hz
  · rw [← hV]
    refine Submodule.span_le.2 fun y hy => ?_
    have hyΛ : y ∈ Λ := hs hy
    exact Submodule.subset_span ⟨⟨y, hyΛ⟩, Submodule.subset_span hy, rfl⟩

end IntegralPart

end HTGeometry.ConstraintMotiveRelativity
