import GaloisForLFunctions.HTGeometry.KaehlerRelativeSpan
import GaloisForLFunctions.HTGeometry.KaehlerRamificationCriterion

/-!
# A degenerate coordinate Jacobian forces ramification

Let `k → A → B` be a tower with `Ω[B⁄k]` free of rank `N` and let `y_1, …, y_N` be elements of `A`
whose differentials generate the differentials of the whole of `A`.  The coordinate matrix of the
`D y_j` in a basis of `Ω[B⁄k]` is the Jacobian of the map.  If its determinant is not a unit the
family cannot span, so the relative differentials do not vanish:

```text
not_subsingleton_kaehler_of_not_isUnit_det :  ¬ IsUnit (det Jacobian)  →  Ω[B⁄A] ≠ 0
```

For a discrete valuation ring upstairs with separable residue extension this is ramification:

```text
map_maximalIdeal_le_sq_of_not_isUnit_det :
    ¬ IsUnit (det Jacobian)  →  (maximalIdeal A).map (algebraMap A B) ≤ (maximalIdeal B) ^ 2
```

which is the statement that the ramification index at the upper place is at least two.
-/

namespace GaloisForLFunctions.HTGeometry

open KaehlerDifferential IsLocalRing

/-- **A non-unit coordinate Jacobian gives nonvanishing relative differentials.** -/
theorem not_subsingleton_kaehler_of_not_isUnit_det
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι B Ω[B⁄k]) (y : ι → A)
    (hgen : ∀ a : A, KaehlerDifferential.D k B (algebraMap A B a)
      ∈ Submodule.span B (Set.range fun j => KaehlerDifferential.D k B (algebraMap A B (y j))))
    (hdet : ¬ IsUnit (Matrix.of (fun i j =>
      b.repr (KaehlerDifferential.D k B (algebraMap A B (y j))) i)).det) :
    ¬ Subsingleton Ω[B⁄A] := by
  intro hsub
  haveI := hsub
  set S : Submodule B Ω[B⁄k] :=
    Submodule.span B (Set.range fun a : A => KaehlerDifferential.D k B (algebraMap A B a)) with hS
  have hquot : Subsingleton (Ω[B⁄k] ⧸ S) :=
    (kaehlerQuotientEquiv k A B).toEquiv.subsingleton
  have htop : S = ⊤ :=
    Submodule.unique_quotient_iff_eq_top.mp ⟨@Unique.mk' _ ⟨0⟩ hquot⟩
  have hle : S ≤ Submodule.span B
      (Set.range fun j => KaehlerDifferential.D k B (algebraMap A B (y j))) := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact hgen a
  rw [htop, top_le_iff] at hle
  exact hdet (isUnit_det_of_span_eq_top b _ hle)

/-- **A non-unit coordinate Jacobian forces ramification index at least two.** -/
theorem map_maximalIdeal_le_sq_of_not_isUnit_det
    {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [IsLocalRing A] [IsDomain B] [IsDiscreteValuationRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι B Ω[B⁄k]) (y : ι → A)
    (hgen : ∀ a : A, KaehlerDifferential.D k B (algebraMap A B a)
      ∈ Submodule.span B (Set.range fun j => KaehlerDifferential.D k B (algebraMap A B (y j))))
    (hdet : ¬ IsUnit (Matrix.of (fun i j =>
      b.repr (KaehlerDifferential.D k B (algebraMap A B (y j))) i)).det)
    (hbot : (maximalIdeal A).map (algebraMap A B) ≠ ⊥) :
    (maximalIdeal A).map (algebraMap A B) ≤ (maximalIdeal B) ^ 2 :=
  map_maximalIdeal_le_sq_of_not_subsingleton
    (not_subsingleton_kaehler_of_not_isUnit_det b y hgen hdet) hbot

end GaloisForLFunctions.HTGeometry
