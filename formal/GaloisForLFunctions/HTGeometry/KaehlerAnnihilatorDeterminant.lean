import GaloisForLFunctions.HTGeometry.KaehlerJacobianRamification

/-!
# The Kähler different of a coordinate presentation

Cramer's rule turns the coordinate matrix of the differentials of a generating family of the base
into an annihilator of the relative differentials:

```text
det_mem_annihilator_kaehler        det P  annihilates  Ω[B⁄A]
annihilator_kaehler_eq_maximalIdeal
    ** with det P irreducible in the discrete valuation ring B,
       Ann (Ω[B⁄A]) is exactly the maximal ideal **
```

The reverse containment is the observation that the annihilator is a proper ideal, which is the
nonvanishing of the relative differentials already recorded in `KaehlerJacobianRamification`.

A spanning family indexed by the index type of a basis is itself a basis
(`basisOfSpanningOfBasis`), because a surjective endomorphism of a finite module over a commutative
ring is injective; this supplies the basis in which the coordinate matrix is the Jacobian itself.
-/

namespace GaloisForLFunctions.HTGeometry

open KaehlerDifferential IsLocalRing

section SpanningBasis

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The linear combination map of a spanning family indexed by the index type of a basis is
bijective: it is surjective by spanning, and a surjective endomorphism of a finite module over a
commutative ring is injective. -/
theorem bijective_linearCombination_of_spanning (b : Module.Basis ι R M) (w : ι → M)
    (hspan : ⊤ ≤ Submodule.span R (Set.range w)) :
    Function.Bijective (Fintype.linearCombination R w) := by
  classical
  haveI : Module.Finite R M := Module.Finite.of_basis b
  have hsurj : Function.Surjective (Fintype.linearCombination R w) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact top_le_iff.mp hspan
  have hgsurj : Function.Surjective
      (b.equivFun.toLinearMap ∘ₗ Fintype.linearCombination R w) :=
    b.equivFun.surjective.comp hsurj
  have hginj : Function.Injective
      (b.equivFun.toLinearMap ∘ₗ Fintype.linearCombination R w) :=
    OrzechProperty.injective_of_surjective_endomorphism _ hgsurj
  refine ⟨fun x y hxy => hginj ?_, hsurj⟩
  simp only [LinearMap.comp_apply]
  rw [hxy]

/-- **A spanning family indexed by the index type of a basis is itself a basis.** -/
noncomputable def basisOfSpanningOfBasis (b : Module.Basis ι R M) (w : ι → M)
    (hspan : ⊤ ≤ Submodule.span R (Set.range w)) : Module.Basis ι R M :=
  Module.Basis.ofEquivFun
    (LinearEquiv.ofBijective (Fintype.linearCombination R w)
      (bijective_linearCombination_of_spanning b w hspan)).symm

@[simp] theorem coe_basisOfSpanningOfBasis (b : Module.Basis ι R M) (w : ι → M)
    (hspan : ⊤ ≤ Submodule.span R (Set.range w)) :
    ⇑(basisOfSpanningOfBasis b w hspan) = w := by
  funext i
  show (Module.Basis.ofEquivFun
      (LinearEquiv.ofBijective (Fintype.linearCombination R w)
        (bijective_linearCombination_of_spanning b w hspan)).symm) i = w i
  rw [Module.Basis.coe_ofEquivFun]
  show (LinearEquiv.ofBijective (Fintype.linearCombination R w)
      (bijective_linearCombination_of_spanning b w hspan)).symm.symm (Pi.single i 1) = w i
  rw [LinearEquiv.symm_symm]
  show Fintype.linearCombination R w (Pi.single i 1) = w i
  rw [Fintype.linearCombination_apply_single, one_smul]

end SpanningBasis

section Annihilator

variable {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
variable [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Cramer's rule for the relative cotangent module.**  If the differentials of a family of base
elements generate the base differentials and have coordinate matrix `P` in a basis, then `det P`
annihilates the relative differentials. -/
theorem det_mem_annihilator_kaehler (b : Module.Basis ι B Ω[B⁄k]) (y : ι → A) (P : Matrix ι ι B)
    (hgen : ∀ a : A, KaehlerDifferential.D k B (algebraMap A B a)
      ∈ Submodule.span B (Set.range fun j => KaehlerDifferential.D k B (algebraMap A B (y j))))
    (hvw : ∀ j, KaehlerDifferential.D k B (algebraMap A B (y j)) = ∑ i, P i j • b i) :
    P.det ∈ Module.annihilator B Ω[B⁄A] := by
  classical
  set S : Submodule B Ω[B⁄k] :=
    Submodule.span B (Set.range fun a : A => KaehlerDifferential.D k B (algebraMap A B a)) with hS
  have hSy : S ≤ Submodule.span B
      (Set.range fun j => KaehlerDifferential.D k B (algebraMap A B (y j))) := by
    rw [hS, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    exact hgen a
  have hdet : ∀ z : Ω[B⁄k], P.det • z ∈ S := by
    intro z
    set c : ι → B := b.equivFun z with hc
    set d : ι → B := P.adjugate.mulVec c with hd
    have hkey : ∑ j, d j • KaehlerDifferential.D k B (algebraMap A B (y j)) = P.det • z := by
      have h1 : ∑ j, d j • KaehlerDifferential.D k B (algebraMap A B (y j))
          = ∑ i, (P.mulVec d i) • b i := by
        simp only [hvw, Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_smul]
        congr 1
        simp [Matrix.mulVec, dotProduct, mul_comm]
      have h2 : P.mulVec d = P.det • c := by
        rw [hd, Matrix.mulVec_mulVec, Matrix.mul_adjugate]
        funext i
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
      rw [h1, h2]
      have h3 : ∑ i, (P.det • c) i • b i = P.det • ∑ i, c i • b i := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by simp [smul_smul]
      rw [h3, hc, b.sum_equivFun]
    rw [← hkey]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨y j, rfl⟩
  rw [Module.mem_annihilator]
  intro ω
  obtain ⟨z, rfl⟩ := KaehlerDifferential.map_surjective k A B ω
  rw [← LinearMap.map_smul]
  have hker : P.det • z ∈ LinearMap.ker (KaehlerDifferential.map k A B B) := by
    rw [← KaehlerDifferential.range_mapBaseChange, range_mapBaseChange_eq_span]
    exact hdet z
  exact hker

/-- **The Kähler different of a coordinate presentation is the maximal ideal**, when the Jacobian
determinant is irreducible in the discrete valuation ring upstairs. -/
theorem annihilator_kaehler_eq_maximalIdeal [IsDomain B] [IsDiscreteValuationRing B]
    (b : Module.Basis ι B Ω[B⁄k]) (y : ι → A) (P : Matrix ι ι B)
    (hgen : ∀ a : A, KaehlerDifferential.D k B (algebraMap A B a)
      ∈ Submodule.span B (Set.range fun j => KaehlerDifferential.D k B (algebraMap A B (y j))))
    (hvw : ∀ j, KaehlerDifferential.D k B (algebraMap A B (y j)) = ∑ i, P i j • b i)
    (hirr : Irreducible P.det) :
    Module.annihilator B Ω[B⁄A] = maximalIdeal B := by
  classical
  have hrepr : (Matrix.of fun i j =>
      b.repr (KaehlerDifferential.D k B (algebraMap A B (y j))) i) = P := by
    refine Matrix.ext fun i j => ?_
    rw [Matrix.of_apply, hvw j, map_sum]
    simp [Module.Basis.repr_self, Finsupp.single_apply]
  have hle : maximalIdeal B ≤ Module.annihilator B Ω[B⁄A] := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer P.det).mp hirr, Ideal.span_le,
      Set.singleton_subset_iff]
    exact det_mem_annihilator_kaehler b y P hgen hvw
  refine le_antisymm (IsLocalRing.le_maximalIdeal fun htop => ?_) hle
  exact not_subsingleton_kaehler_of_not_isUnit_det b y hgen
    (by rw [hrepr]; exact hirr.not_isUnit) (Module.annihilator_eq_top_iff.mp htop)

end Annihilator

end GaloisForLFunctions.HTGeometry
