/-
# Complex descent of a Kähler coordinate representation

A finite family in a field extension `L` of `ℂ` is algebraically independent over `ℂ` exactly when
its universal Kähler differentials are linearly independent over `L`.  Choosing a basis of the span
of those differentials turns that criterion into a finite coordinate matrix over `L`.

The entries of the matrix satisfy a prime ideal of polynomial relations over `ℂ`; by the
Nullstellensatz its zero locus carries a point at which no maximal minor that was nonzero becomes
zero.  Evaluating the coordinates there produces a complex matrix with exactly the same linear
(in)dependence pattern on every subfamily.  The two steps together model the algebraic matroid of
the family by a finite complex vector configuration.
-/
import GaloisForLFunctions.HTGeometry.LinearIndependenceMinorTransfer
import GaloisForLFunctions.HTGeometry.KaehlerAlgebraicIndependence
import Mathlib

open Matrix MvPolynomial Module

namespace GaloisForLFunctions.HTGeometry

variable {L ι κ : Type*} [Field L] [Algebra ℂ L]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The determinant of a square column selection of the universal coordinate matrix. -/
noncomputable def minorPoly (t : Σ J : Finset ι, ({x // x ∈ J} → κ)) :
    MvPolynomial (ι × κ) ℂ :=
  Matrix.det (Matrix.of fun a b : {x // x ∈ t.1} => MvPolynomial.X ((a : ι), t.2 b))

omit [Fintype ι] [Fintype κ] [DecidableEq κ] in
theorem aeval_coordinateMinorPoly {M : Type*} [CommRing M] [Algebra ℂ M] (u : ι → κ → M)
    (t : Σ J : Finset ι, ({x // x ∈ J} → κ)) :
    MvPolynomial.aeval (fun p : ι × κ => u p.1 p.2) (minorPoly t)
      = Matrix.det (Matrix.of fun a b : {x // x ∈ t.1} => u (a : ι) (t.2 b)) := by
  rw [minorPoly, AlgHom.map_det]
  congr 1
  ext a b
  simp [AlgHom.mapMatrix]

/-- **Complex descent of a coordinate representation.**  A finite family of finite coordinate
vectors over a field extension of `ℂ` has a complex model with exactly the same linear
(in)dependence pattern on every subfamily.  The model is a point of the zero locus of the ideal of
relations at which no surviving maximal minor vanishes; it exists by the Nullstellensatz. -/
theorem exists_complexCoords (v : ι → κ → L) :
    ∃ w : ι → κ → ℂ, ∀ J : Finset ι,
      (LinearIndependent ℂ (fun i : {x // x ∈ J} => w (i : ι)) ↔
        LinearIndependent L (fun i : {x // x ∈ J} => v (i : ι))) := by
  classical
  set e : MvPolynomial (ι × κ) ℂ →ₐ[ℂ] L :=
    MvPolynomial.aeval (fun p : ι × κ => v p.1 p.2) with he
  set P : Ideal (MvPolynomial (ι × κ) ℂ) := RingHom.ker (e : MvPolynomial (ι × κ) ℂ →+* L) with hP
  haveI hPprime : P.IsPrime := RingHom.ker_isPrime _
  set S : Finset (Σ J : Finset ι, ({x // x ∈ J} → κ)) :=
    Finset.univ.filter (fun t => e (minorPoly t) ≠ 0) with hS
  set Pd : MvPolynomial (ι × κ) ℂ := ∏ t ∈ S, minorPoly t with hPdef
  have hePd : e Pd ≠ 0 := by
    rw [hPdef, map_prod]
    refine Finset.prod_ne_zero_iff.mpr ?_
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  have hnot : Pd ∉ P := hePd
  rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) P,
    MvPolynomial.mem_vanishingIdeal_iff] at hnot
  push Not at hnot
  obtain ⟨x, hxmem, hxne⟩ := hnot
  have hxfun : (fun p : ι × κ => x (p.1, p.2)) = x := by
    funext p
    rfl
  refine ⟨fun i j => x (i, j), ?_⟩
  intro J
  constructor
  · intro hC
    obtain ⟨s, _, hdet⟩ := exists_injective_det_submatrix_ne_zero
      (M := Matrix.of fun (i : {x // x ∈ J}) (j : κ) => x ((i : ι), j)) hC
    have hxt : MvPolynomial.aeval x (minorPoly ⟨J, s⟩) ≠ 0 := by
      rw [← hxfun, aeval_coordinateMinorPoly (u := fun i j => x (i, j))]
      exact hdet
    have hmemP : minorPoly ⟨J, s⟩ ∉ P := by
      intro hmem
      exact hxt ((MvPolynomial.mem_zeroLocus_iff.mp hxmem) _ hmem)
    have heval : e (minorPoly ⟨J, s⟩) ≠ 0 := hmemP
    refine linearIndependent_rows_of_det_submatrix_ne_zero
      (M := Matrix.of fun (i : {x // x ∈ J}) (j : κ) => v (i : ι) j) (s := s) ?_
    rw [he, aeval_coordinateMinorPoly (u := v)] at heval
    exact heval
  · intro hL
    obtain ⟨s, _, hdet⟩ := exists_injective_det_submatrix_ne_zero
      (M := Matrix.of fun (i : {x // x ∈ J}) (j : κ) => v (i : ι) j) hL
    have hmemS : (⟨J, s⟩ : Σ J : Finset ι, ({x // x ∈ J} → κ)) ∈ S := by
      rw [hS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [he, aeval_coordinateMinorPoly (u := v)]
      exact hdet
    have hprod : MvPolynomial.aeval x Pd = ∏ t ∈ S, MvPolynomial.aeval x (minorPoly t) := by
      rw [hPdef, map_prod]
    have hne : MvPolynomial.aeval x (minorPoly ⟨J, s⟩) ≠ 0 := by
      intro hzero
      apply hxne
      rw [hprod]
      exact Finset.prod_eq_zero hmemS hzero
    refine linearIndependent_rows_of_det_submatrix_ne_zero
      (M := Matrix.of fun (i : {x // x ∈ J}) (j : κ) => x ((i : ι), j)) (s := s) ?_
    rw [← hxfun, aeval_coordinateMinorPoly (u := fun i j => x (i, j))] at hne
    exact hne





/-- **Coordinates for the Kähler representation.**  A finite family in a field extension of `ℂ`
has a finite coordinate model over the same field whose linear (in)dependence on every subfamily
is exactly algebraic (in)dependence over `ℂ`. -/
theorem exists_kaehlerCoords {L ι : Type*} [Field L] [Algebra ℂ L] [Fintype ι] [DecidableEq ι]
    (x : ι → L) :
    ∃ (r : ℕ) (v : ι → Fin r → L), ∀ J : Finset ι,
      (LinearIndependent L (fun i : {a // a ∈ J} => v (i : ι)) ↔
        AlgebraicIndependent ℂ (fun i : {a // a ∈ J} => x (i : ι))) := by
  classical
  set d : ι → KaehlerDifferential ℂ L := fun i => KaehlerDifferential.D ℂ L (x i) with hd
  set W : Submodule L (KaehlerDifferential ℂ L) := Submodule.span L (Set.range d) with hW
  haveI : FiniteDimensional L W :=
    FiniteDimensional.span_of_finite L (Set.finite_range d)
  set b : Basis (Fin (finrank L W)) L W := Module.finBasis L W with hb
  set g : ι → W := fun i => ⟨d i, Submodule.subset_span (Set.mem_range_self i)⟩ with hg
  refine ⟨finrank L W, fun i => fun k => b.repr (g i) k, ?_⟩
  intro J
  rw [algebraicIndependent_iff_kaehlerD_linearIndependent]
  set Φ : W →ₗ[L] (Fin (finrank L W) → L) :=
    (Finsupp.linearEquivFunOnFinite L L (Fin (finrank L W))).toLinearMap ∘ₗ
      b.repr.toLinearMap with hΦ
  have hΦinj : Function.Injective Φ := by
    rw [hΦ]
    exact (Finsupp.linearEquivFunOnFinite L L (Fin (finrank L W))).injective.comp
      b.repr.injective
  have h1 : (LinearIndependent L (fun i : {a // a ∈ J} => Φ (g (i : ι)))) ↔
      LinearIndependent L (fun i : {a // a ∈ J} => g (i : ι)) := by
    constructor
    · intro h
      exact LinearIndependent.of_comp Φ h
    · intro h
      exact h.map' Φ (LinearMap.ker_eq_bot.mpr hΦinj)
  have h2 : (LinearIndependent L (fun i : {a // a ∈ J} => W.subtype (g (i : ι)))) ↔
      LinearIndependent L (fun i : {a // a ∈ J} => g (i : ι)) := by
    constructor
    · intro h
      exact LinearIndependent.of_comp W.subtype h
    · intro h
      exact h.map' W.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  exact h1.trans h2.symm


end GaloisForLFunctions.HTGeometry
