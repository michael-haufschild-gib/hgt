import GaloisForLFunctions.HTGeometry.GroupAlgebraPointDerivation

/-!
# Co-Lie directions of a quotient character lattice

For an integral character lattice `M = ℤⁿ` and a relation subgroup `L`, the logarithmic
differentials of the standard characters define a linear map

`kⁿ → ω_{k[M/L]}`.

This file proves that its kernel is exactly the `k`-linear span of the integral relations in `L`.
No saturation or connectedness assumption is needed: torsion in `M/L` is handled directly by
point derivations of the quotient group algebra.
-/

open Coalgebra Bialgebra

namespace GaloisForLFunctions.HTGeometry
namespace TorusCharacterCoLie

noncomputable section

open AffineGroupScheme GroupAlgebraPointDerivation

variable (k : Type*) [Field k]

/-- Componentwise scalar extension of an integral exponent vector. -/
noncomputable def integralCast {n : ℕ} :
    (Fin n →₀ ℤ) →+ (Fin n → k) where
  toFun m i := (m i : k)
  map_zero' := by ext; simp
  map_add' m p := by ext; simp

@[simp] theorem integralCast_apply {n : ℕ} (m : Fin n →₀ ℤ) (i : Fin n) :
    integralCast k m i = (m i : k) := rfl

@[simp] theorem integralCast_single_one {n : ℕ} (i : Fin n) :
    integralCast k (Finsupp.single i 1) = Pi.single i 1 := by
  ext j
  by_cases h : i = j <;> simp [h]

/-- Field-linear span of an integral character-relation subgroup. -/
noncomputable def latticeSpan {n : ℕ} (L : AddSubgroup (Fin n →₀ ℤ)) :
    Submodule k (Fin n → k) :=
  Submodule.span k (integralCast k '' (L : Set (Fin n →₀ ℤ)))

/-- Standard logarithmic character differentials in the quotient group algebra `k[ℤⁿ/L]`. -/
noncomputable def quotientGroupCoLieMap {n : ℕ} (L : AddSubgroup (Fin n →₀ ℤ)) :
    (Fin n → k) →ₗ[k]
      coLie k (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ L)) where
  toFun c := ∑ i, c i • d k (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ L))
    (AddMonoidAlgebra.single
      (QuotientAddGroup.mk' L (Finsupp.single i 1)) 1)
  map_add' c e := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by
    simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul]

@[simp] theorem quotientGroupCoLieMap_apply {n : ℕ}
    (L : AddSubgroup (Fin n →₀ ℤ)) (c : Fin n → k) :
    quotientGroupCoLieMap k L c =
      ∑ i, c i • d k (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ L))
        (AddMonoidAlgebra.single
          (QuotientAddGroup.mk' L (Finsupp.single i 1)) 1) := rfl

/-- Additive differential of a quotient character. -/
noncomputable def quotientGroupDifferential {n : ℕ}
    (L : AddSubgroup (Fin n →₀ ℤ)) :
    (Fin n →₀ ℤ) →+
      coLie k (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ L)) where
  toFun m := d k (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ L))
    (AddMonoidAlgebra.single (QuotientAddGroup.mk' L m) 1)
  map_zero' := by
    rw [map_zero, ← AddMonoidAlgebra.one_def]
    exact d_one
  map_add' m p := by
    change d k (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ L))
        (AddMonoidAlgebra.single (QuotientAddGroup.mk' L (m + p)) 1) = _
    rw [map_add]
    have hsingle :
        AddMonoidAlgebra.single
            (QuotientAddGroup.mk' L m + QuotientAddGroup.mk' L p) (1 : k) =
          AddMonoidAlgebra.single (QuotientAddGroup.mk' L m) (1 : k) *
            AddMonoidAlgebra.single (QuotientAddGroup.mk' L p) (1 : k) := by
      simp [AddMonoidAlgebra.single_mul_single]
    calc
      _ = d k (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ L))
          (AddMonoidAlgebra.single (QuotientAddGroup.mk' L m) 1 *
            AddMonoidAlgebra.single (QuotientAddGroup.mk' L p) 1) :=
        congrArg (d k (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ L))) hsingle
      _ = _ := by rw [d_mul]; simp [add_comm]

/-- An arbitrary integral character has the expected logarithmic differential. -/
theorem quotientGroupCoLieMap_integralCast {n : ℕ}
    (L : AddSubgroup (Fin n →₀ ℤ)) (m : Fin n →₀ ℤ) :
    quotientGroupCoLieMap k L (integralCast k m) =
      d k (AddMonoidAlgebra k ((Fin n →₀ ℤ) ⧸ L))
        (AddMonoidAlgebra.single (QuotientAddGroup.mk' L m) 1) := by
  rw [quotientGroupCoLieMap_apply]
  change (∑ i, (m i : k) • quotientGroupDifferential k L (Finsupp.single i 1)) =
    quotientGroupDifferential k L m
  have hcast :
      (∑ i, (m i : k) • quotientGroupDifferential k L (Finsupp.single i 1)) =
        ∑ i, (m i) • quotientGroupDifferential k L (Finsupp.single i 1) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact Int.cast_smul_eq_zsmul k (m i)
      (quotientGroupDifferential k L (Finsupp.single i 1))
  rw [hcast]
  have hm : m = ∑ i, (m i) • Finsupp.single i 1 := by
    classical
    ext i
    simp
  calc
    (∑ i, (m i) • quotientGroupDifferential k L (Finsupp.single i 1)) =
        ∑ i, quotientGroupDifferential k L ((m i) • Finsupp.single i 1) := by
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact (map_zsmul (quotientGroupDifferential k L)
        (m i) (Finsupp.single i 1)).symm
    _ = quotientGroupDifferential k L
          (∑ i, (m i) • Finsupp.single i 1) :=
      (map_sum (quotientGroupDifferential k L) _ _).symm
    _ = quotientGroupDifferential k L m :=
      congrArg (quotientGroupDifferential k L) hm.symm

/-- Every field-linear combination of integral relations has zero quotient logarithmic
differential. -/
theorem latticeSpan_le_ker {n : ℕ} (L : AddSubgroup (Fin n →₀ ℤ)) :
    latticeSpan k L ≤ LinearMap.ker (quotientGroupCoLieMap k L) := by
  rw [latticeSpan, Submodule.span_le]
  rintro c ⟨m, hm, rfl⟩
  change quotientGroupCoLieMap k L (integralCast k m) = 0
  rw [quotientGroupCoLieMap_integralCast]
  have hq : QuotientAddGroup.mk' L m = 0 := (QuotientAddGroup.eq_zero_iff m).2 hm
  rw [hq, ← AddMonoidAlgebra.one_def]
  exact d_one

/-- **Exact co-Lie kernel of a quotient character lattice.** -/
theorem quotientGroupCoLieMap_eq_zero_iff {n : ℕ}
    (L : AddSubgroup (Fin n →₀ ℤ)) (c : Fin n → k) :
    quotientGroupCoLieMap k L c = 0 ↔ c ∈ latticeSpan k L := by
  constructor
  · intro hc
    by_contra hmem
    let B := Module.Free.chooseBasis k ((Fin n → k) ⧸ latticeSpan k L)
    have hq : Submodule.Quotient.mk (p := latticeSpan k L) c ≠ 0 := by
      rw [ne_eq, Submodule.Quotient.mk_eq_zero]
      exact hmem
    have hre : B.repr (Submodule.Quotient.mk (p := latticeSpan k L) c) ≠ 0 := by
      exact fun h => hq (B.repr.injective (by simpa using h))
    obtain ⟨j, hj⟩ := Finsupp.ne_iff.mp hre
    let phi : (Fin n → k) →ₗ[k] k :=
      (B.coord j).comp (Submodule.mkQ (latticeSpan k L))
    have hphi_span : ∀ x ∈ latticeSpan k L, phi x = 0 := by
      intro x hx
      have hx0 : Submodule.Quotient.mk (p := latticeSpan k L) x = 0 :=
        (Submodule.Quotient.mk_eq_zero _).2 hx
      simp [phi, hx0]
    have hphi_c : phi c ≠ 0 := by
      change B.repr (Submodule.Quotient.mk (p := latticeSpan k L) c) j ≠ 0
      exact hj
    let ell0 : (Fin n →₀ ℤ) →+ k :=
      { toFun := fun m => phi (integralCast k m)
        map_zero' := by simp
        map_add' := fun m p => by simp }
    have hL : L ≤ AddMonoidHom.ker ell0 := by
      intro m hm
      change phi (integralCast k m) = 0
      apply hphi_span
      exact Submodule.subset_span ⟨m, hm, rfl⟩
    let ell : ((Fin n →₀ ℤ) ⧸ L) →+ k := QuotientAddGroup.lift L ell0 hL
    have happly := congrArg (fun z => coLieFunctional ell z) hc
    have hcalc : coLieFunctional ell (quotientGroupCoLieMap k L c) = phi c := by
      rw [quotientGroupCoLieMap_apply, map_sum]
      simp only [map_smul, coLieFunctional_d_single, one_mul]
      change (∑ i, c i • phi (integralCast k (Finsupp.single i 1))) = phi c
      have hcoords : c = ∑ i, c i • Pi.single i 1 := by
        classical
        funext j
        rw [Finset.sum_apply]
        rw [Finset.sum_eq_single j (fun i _ hij => by
          change c i * (Pi.single i 1 : Fin n → k) j = 0
          rw [Pi.single_eq_of_ne (Ne.symm hij), mul_zero])
          (fun hmem => absurd (Finset.mem_univ j) hmem)]
        change c j = c j * (Pi.single j 1 : Fin n → k) j
        rw [Pi.single_eq_same, mul_one]
      simp_rw [integralCast_single_one, ← map_smul]
      rw [← map_sum]
      exact congrArg phi hcoords.symm
    rw [hcalc] at happly
    exact hphi_c (by simpa using happly)
  · intro hc
    exact LinearMap.mem_ker.mp (latticeSpan_le_ker k L hc)

end
end TorusCharacterCoLie
end GaloisForLFunctions.HTGeometry
