import GaloisForLFunctions.RHTower.DeningerRelativeSullivanMilnorResolution
import GaloisForLFunctions.RHTower.DeningerExteriorPairSum

/-!
# The canonical primitive of the first Sullivan layer

The differential of the first relative Sullivan layer sends the new generator attached to a
degree-two class to that class.  Multiplying such a generator by an element of the old algebra and
applying the Leibniz rule therefore produces the class times that element, because the old algebra
consists of cocycles.

Averaging this over all ordered pairs of letters of a wedge monomial and dividing by the number of
pairs gives a *canonical* primitive of the monomial: no choice of a pair, no shuffle sign, no
basis.  Combined with the fact that the Milnor ideal is spanned by the degree-two part, every
Milnor class is a coboundary, and over a field the primitive can be chosen linearly.

* `deningerSullivanPairGenerator` : the new generator attached to a wedge of two vectors.
* `deningerSullivanPairPrimitive` : the averaged primitive of a wedge monomial.
* `deningerSullivanPairPrimitive_normalized` : **its differential is the monomial.**
* `deningerSullivanFirstLayer_milnorIdeal_isCoboundary` : every Milnor class is a coboundary.
* `deningerSullivanPrimitive_exists` : **a linear primitive on the whole Milnor ideal.**
-/

namespace RHTower

open ExteriorAlgebra HTGeometry

noncomputable section

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

/-! ## Sign bookkeeping -/

private theorem deningerUnitsSmul {F M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [FunLike F M N] [AddMonoidHomClass F M N] (f : F) (u : ℤˣ) (x : M) :
    f (u • x) = u • f x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp
  · simp [Units.smul_def]

/-! ## The primitive of a decomposable -/

/-- The new generator of the first Sullivan layer attached to the wedge of two vectors. -/
def deningerSullivanPairGenerator (a b : V) : ExteriorAlgebra k (V × (⋀[k]^2 V)) :=
  ι k ((0, ⟨ι k a * ι k b, deningerExteriorTwo_mem a b⟩) : V × (⋀[k]^2 V))

@[simp]
theorem deningerSullivanFirstLayerDifferential_pairGenerator (a b : V) :
    deningerSullivanFirstLayerDifferential k V (deningerSullivanPairGenerator a b) =
      deningerSullivanInclusion k V (⋀[k]^2 V) (ι k a * ι k b) :=
  deningerSullivanFirstLayerDifferential_new _

/-- Multiplying the new generator of a wedge of two vectors by an old element and differentiating
returns that wedge times the old element: the old algebra consists of cocycles, so the Leibniz
rule has only one surviving term. -/
theorem deningerSullivanFirstLayerDifferential_pairGenerator_mul (a b : V)
    (Y : ExteriorAlgebra k V) :
    deningerSullivanFirstLayerDifferential k V
        (deningerSullivanPairGenerator a b * deningerSullivanInclusion k V (⋀[k]^2 V) Y) =
      deningerSullivanInclusion k V (⋀[k]^2 V) (ι k a * ι k b * Y) := by
  rw [deningerSullivanFirstLayerDifferential_leibniz,
    deningerSullivanFirstLayerDifferential_inl,
    deningerSullivanFirstLayerDifferential_pairGenerator, mul_zero, zero_add, ← map_mul]

/-- **The canonical primitive of a wedge monomial**: the signed average, over all ordered pairs of
letters, of the new generator of that pair times the remaining letters. -/
def deningerSullivanPairPrimitive {r : ℕ} (v : Fin (r + 2) → V) :
    ExteriorAlgebra k (V × (⋀[k]^2 V)) :=
  ∑ p ∈ deningerPairIndex (r + 2),
    Equiv.Perm.sign (deningerPairPerm p.1 p.2) •
      (deningerSullivanPairGenerator (k := k) (v p.1) (v p.2) *
        deningerSullivanInclusion k V (⋀[k]^2 V)
          (List.ofFn fun t : Fin r =>
            ι k (v (deningerPairPerm p.1 p.2 t.succ.succ))).prod)

/-- **The differential of the canonical primitive is the monomial, times the number of pairs.** -/
theorem deningerSullivanPairPrimitive_differential {r : ℕ} (v : Fin (r + 2) → V) :
    deningerSullivanFirstLayerDifferential k V (deningerSullivanPairPrimitive v) =
      ((r + 2).choose 2) • deningerSullivanInclusion k V (⋀[k]^2 V)
        (ExteriorAlgebra.ιMulti k (r + 2) v) := by
  have hstep : deningerSullivanFirstLayerDifferential k V (deningerSullivanPairPrimitive v) =
      deningerSullivanInclusion k V (⋀[k]^2 V)
        (∑ p ∈ deningerPairIndex (r + 2),
          Equiv.Perm.sign (deningerPairPerm p.1 p.2) •
            (ι k (v p.1) * (ι k (v p.2) *
              (List.ofFn fun t : Fin r =>
                ι k (v (deningerPairPerm p.1 p.2 t.succ.succ))).prod))) := by
    rw [deningerSullivanPairPrimitive, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [deningerUnitsSmul, deningerUnitsSmul,
      deningerSullivanFirstLayerDifferential_pairGenerator_mul, mul_assoc]
  rw [hstep, deningerExteriorPairSum, map_nsmul, deningerPairIndex_card]

/-- **The normalized canonical primitive.**  Dividing by the number of pairs turns the averaged
primitive into an honest primitive of the wedge monomial. -/
theorem deningerSullivanPairPrimitive_normalized [CharZero k] {r : ℕ} (v : Fin (r + 2) → V) :
    deningerSullivanFirstLayerDifferential k V
        ((((r + 2).choose 2 : ℕ) : k)⁻¹ • deningerSullivanPairPrimitive v) =
      deningerSullivanInclusion k V (⋀[k]^2 V) (ExteriorAlgebra.ιMulti k (r + 2) v) := by
  have hpos : 0 < (r + 2).choose 2 := Nat.choose_pos (by omega)
  have hne : (((r + 2).choose 2 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
  rw [map_smul, deningerSullivanPairPrimitive_differential,
    ← Nat.cast_smul_eq_nsmul k, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-! ## Every Milnor class is a coboundary -/

/-- **Every element of the Milnor ideal is a coboundary of the first layer.**  The degree-two
generators are differentials of new generators, and the Leibniz rule propagates this through
products with the old algebra, which consists of cocycles. -/
theorem deningerSullivanFirstLayer_milnorIdeal_isCoboundary {z : ExteriorAlgebra k V}
    (hz : z ∈ deningerMilnorIdeal k V) :
    ∃ y, deningerSullivanFirstLayerDifferential k V y =
      deningerSullivanInclusion k V (⋀[k]^2 V) z := by
  rw [deningerMilnorIdeal] at hz
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · intro x hx
    exact deningerSullivanFirstLayer_exteriorTwo_isCoboundary hx
  · exact ⟨0, by rw [map_zero, map_zero]⟩
  · rintro p q _ _ ⟨yp, hyp⟩ ⟨yq, hyq⟩
    exact ⟨yp + yq, by rw [map_add, hyp, hyq, map_add]⟩
  · rintro c p _ ⟨y, hy⟩
    refine ⟨deningerSullivanInclusion k V (⋀[k]^2 V)
      (deningerExteriorInvolute k V c) * y, ?_⟩
    rw [deningerSullivanFirstLayerDifferential_leibniz, hy,
      deningerSullivanFirstLayerDifferential_inl,
      deningerExteriorInvolute_sullivanInclusion, deningerExteriorInvolute_involute,
      zero_mul, add_zero, smul_eq_mul, map_mul]

/-! ## A linear primitive -/

variable (k V)

/-- The Milnor ideal, viewed as a subspace over the ground field. -/
def deningerMilnorSubspace : Submodule k (ExteriorAlgebra k V) :=
  Submodule.restrictScalars k (deningerMilnorIdeal k V)

/-- The image of the Milnor ideal in the first Sullivan layer. -/
def deningerSullivanPrimitiveTarget : Submodule k (ExteriorAlgebra k (V × (⋀[k]^2 V))) :=
  Submodule.map (deningerSullivanInclusion k V (⋀[k]^2 V)).toLinearMap
    (deningerMilnorSubspace k V)

/-- The elements of the first layer whose differential is the inclusion of a Milnor class. -/
def deningerSullivanPrimitiveDomain : Submodule k (ExteriorAlgebra k (V × (⋀[k]^2 V))) :=
  Submodule.comap (deningerSullivanFirstLayerDifferential k V)
    (deningerSullivanPrimitiveTarget k V)

/-- The differential, restricted to the elements that differentiate into a Milnor class. -/
def deningerSullivanPrimitiveRestrict :
    deningerSullivanPrimitiveDomain k V →ₗ[k] deningerSullivanPrimitiveTarget k V :=
  LinearMap.restrict (deningerSullivanFirstLayerDifferential k V) (fun _ hx => hx)

theorem deningerSullivanPrimitiveRestrict_range :
    LinearMap.range (deningerSullivanPrimitiveRestrict k V) = ⊤ := by
  rw [LinearMap.range_eq_top]
  rintro ⟨y, hy⟩
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨w, hw⟩ := deningerSullivanFirstLayer_milnorIdeal_isCoboundary (k := k) (V := V) hz
  have hmem : w ∈ deningerSullivanPrimitiveDomain k V := by
    show deningerSullivanFirstLayerDifferential k V w ∈ deningerSullivanPrimitiveTarget k V
    rw [hw]
    exact ⟨z, hz, rfl⟩
  exact ⟨⟨w, hmem⟩, Subtype.ext hw⟩

/-- **A canonical linear primitive on the whole Milnor ideal.**  The differential is surjective
onto the image of the Milnor ideal, and over a field every surjection of vector spaces splits, so
the primitive can be chosen linearly in the class. -/
theorem deningerSullivanPrimitive_exists :
    ∃ h : deningerMilnorSubspace k V →ₗ[k] ExteriorAlgebra k (V × (⋀[k]^2 V)),
      ∀ x : deningerMilnorSubspace k V,
        deningerSullivanFirstLayerDifferential k V (h x) =
          deningerSullivanInclusion k V (⋀[k]^2 V) (x : ExteriorAlgebra k V) := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective
    (deningerSullivanPrimitiveRestrict k V) (deningerSullivanPrimitiveRestrict_range k V)
  have hinj : Function.Injective
      ((deningerSullivanInclusion k V (⋀[k]^2 V)).toLinearMap) :=
    deningerSullivanInclusion_injective
  refine ⟨(deningerSullivanPrimitiveDomain k V).subtype.comp
    (s.comp (Submodule.equivMapOfInjective _ hinj (deningerMilnorSubspace k V)).toLinearMap),
    fun x => ?_⟩
  have hx := LinearMap.congr_fun hs
    ((Submodule.equivMapOfInjective _ hinj (deningerMilnorSubspace k V)) x)
  have hval := congrArg (Subtype.val) hx
  exact hval

end

end RHTower
