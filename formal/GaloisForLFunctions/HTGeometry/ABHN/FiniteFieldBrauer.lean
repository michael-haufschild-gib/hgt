/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.ABHN.BrauerFoundations
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-!
# Brauer groups of finite fields for ABHN

Every finite-dimensional central simple algebra over a finite field is split.  The proof uses
Artin--Wedderburn, Wedderburn's little theorem, and centrality to show that the division-algebra
factor is the base field.  This supplies the vanishing of finite residue-field Brauer groups used
in unramified local theory, independently of the Galois-cohomology description.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

universe u

/-- Every central simple algebra over a finite field has split Brauer class. -/
theorem finiteField_brauerClass_eq_split (K : Type u) [Field K] [Finite K] (A : CSA.{u, u} K) :
    brauerClass A = brauerSplitClass K := by
  haveI : IsArtinianRing A.carrier := IsArtinianRing.of_finite K A.carrier
  obtain ⟨n, hn, D, hD, hKD, hfinite, ⟨e⟩⟩ :=
    IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite K A.carrier
  letI : DivisionRing D := hD
  letI : Algebra K D := hKD
  letI : Module.Finite K D := hfinite
  letI : Finite D := Module.finite_of_finite K
  letI : Algebra K (Matrix (Fin n) (Fin n) D) := Matrix.instAlgebra
  letI : Algebra.IsCentral K (Matrix (Fin n) (Fin n) D) :=
    Algebra.IsCentral.of_algEquiv K A.carrier (Matrix (Fin n) (Fin n) D) e
  have hbij : Function.Bijective (algebraMap K D) :=
    Algebra.IsCentral.baseField_essentially_unique K D (Matrix (Fin n) (Fin n) D)
  let d : K ≃ₐ[K] D := AlgEquiv.ofBijective (Algebra.ofId K D) hbij
  calc
    brauerClass A = brauerClass (matrixFinCSA (scalarCSA K) n) :=
      brauerClass_eq_of_algEquiv A (matrixFinCSA (scalarCSA K) n) (e.trans d.symm.mapMatrix)
    _ = brauerSplitClass K := brauerClass_matrixFinCSA_scalar_eq n

/-- Every Brauer class over a finite field is split. -/
theorem finiteField_brauerGroup_eq_split (K : Type u) [Field K] [Finite K]
    (x : BrauerGroup.{u, u} K) : x = brauerSplitClass K := by
  refine Quotient.inductionOn x ?_
  exact finiteField_brauerClass_eq_split K

/-- The Brauer group of a finite field is trivial. -/
theorem finiteField_brauerGroup_subsingleton (K : Type u) [Field K] [Finite K] :
    Subsingleton (BrauerGroup.{u, u} K) where
  allEq x y := (finiteField_brauerGroup_eq_split K x).trans
    (finiteField_brauerGroup_eq_split K y).symm

end GaloisForLFunctions.HTGeometry.ABHN
