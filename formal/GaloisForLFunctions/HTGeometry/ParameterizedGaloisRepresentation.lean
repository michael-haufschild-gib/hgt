import GaloisForLFunctions.HTGeometry.LocalizationDerivationExt

/-!
# The parameterized difference Galois representation

The parameterized Galois group is the subgroup of difference automorphisms which also commute with
the derivation.  Its Galois matrix is the same matrix as before, so the representation is the
restriction of the difference Galois representation; what is new is that its entries lie in the
constants of the difference operator, and those constants are closed under the derivation.

So the parameterized Galois group embeds in the invertible matrices over a *differential* field --
the structure a classification of differential algebraic subgroups acts on.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Differential R] [Algebra K R] {n : ℕ}

/-- **The parameterized Galois representation.** -/
def parameterizedGaloisRepresentation (σR : R ≃+* R) (B : Matrix (Fin n) (Fin n) K)
    (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y)
    (hnc : ∀ x : R, σR x = x → ∃ a : K, x = algebraMap K R a) :
    parameterizedAut (K := K) σR →* (Matrix (Fin n) (Fin n) R)ˣ :=
  (galoisRepresentation σR B Y hY hnc).comp
    (Subgroup.inclusion (parameterizedAut_le_differenceAut (K := K) σR))

@[simp] theorem parameterizedGaloisRepresentation_val (σR : R ≃+* R)
    (B : Matrix (Fin n) (Fin n) K) (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y)
    (hnc : ∀ x : R, σR x = x → ∃ a : K, x = algebraMap K R a)
    (φ : parameterizedAut (K := K) σR) :
    ((parameterizedGaloisRepresentation σR B Y hY hnc φ : (Matrix (Fin n) (Fin n) R)ˣ) :
      Matrix (Fin n) (Fin n) R) = galoisMatrix Y φ.1 := rfl

/-- **The representation lands over the differential field of constants.**  Each entry is a constant
of the difference operator, and its derivative is again one. -/
theorem parameterizedGaloisRepresentation_entries (σR : R ≃+* R) (hσ : CommutesDeriv σR)
    (B : Matrix (Fin n) (Fin n) K) (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y)
    (hnc : ∀ x : R, σR x = x → ∃ a : K, x = algebraMap K R a)
    (φ : parameterizedAut (K := K) σR) (i j : Fin n) :
    ((parameterizedGaloisRepresentation σR B Y hY hnc φ : (Matrix (Fin n) (Fin n) R)ˣ) :
        Matrix (Fin n) (Fin n) R) i j ∈ sigmaConstantsSubring σR ∧
      Differential.deriv
        (((parameterizedGaloisRepresentation σR B Y hY hnc φ : (Matrix (Fin n) (Fin n) R)ˣ) :
          Matrix (Fin n) (Fin n) R) i j) ∈ sigmaConstantsSubring σR := by
  rw [parameterizedGaloisRepresentation_val]
  exact galoisMatrix_deriv_mem_sigmaConstants σR hσ B Y hY φ.1 φ.2 i j

/-- **The parameterized representation is faithful** on a Picard--Vessiot ring. -/
theorem parameterizedGaloisRepresentation_injective (σR : R ≃+* R)
    (B : Matrix (Fin n) (Fin n) K) (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y)
    (hnc : ∀ x : R, σR x = x → ∃ a : K, x = algebraMap K R a)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin n × Fin n => Y p.1 p.2) ∪ {u}) = ⊤) :
    Function.Injective (parameterizedGaloisRepresentation σR B Y hY hnc) := by
  intro φ ψ hφψ
  have hinc : (Subgroup.inclusion (parameterizedAut_le_differenceAut (K := K) σR)) φ
      = (Subgroup.inclusion (parameterizedAut_le_differenceAut (K := K) σR)) ψ :=
    galoisRepresentation_injective σR B Y hY hnc u hu htop hφψ
  apply Subtype.ext
  exact congrArg (fun g : differenceAut (K := K) σR => (g : R ≃ₐ[K] R)) hinc

end

end GaloisForLFunctions.HTGeometry
