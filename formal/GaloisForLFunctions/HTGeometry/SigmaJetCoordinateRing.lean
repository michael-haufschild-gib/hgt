import GaloisForLFunctions.HTGeometry.DifferentialPolynomialOver
import GaloisForLFunctions.HTGeometry.ParameterizedPicardVessiotExistence

/-!
# The difference action on the differential coordinate ring of a fundamental matrix

The parameterized theory needs the coordinate ring of a fundamental matrix in the *differential*
sense: polynomials in the jets of the matrix entries, with coefficients in the differential base
field.  That ring and its total derivation are `DifferentialPolynomialOver`.  This file adds the
difference operator.

Its value on a jet variable is forced: `σ` must commute with the derivation, so
`σ (δ^k X_{i j}) = δ^k (σ X_{i j}) = δ^k ((A X)_{i j})`.  Taking that as the definition makes the
commutation a generator check plus an induction, with no Leibniz combinatorics: the two composites
`σ ∘ δ` and `δ ∘ σ` are both twisted derivations, and they agree on constants and on jets.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {K : Type*} [CommRing K] [Differential K] {n : ℕ}

/-- The total derivation of the differential coordinate ring. -/
abbrev jetCoordDeriv (K : Type*) [CommRing K] [Differential K] (n : ℕ) :
    Derivation ℤ (DifferentialPolynomial (Fin n × Fin n) K)
      (DifferentialPolynomial (Fin n × Fin n) K) :=
  differentialPolynomialOverDerivation (Fin n × Fin n) K

/-- The image of the `(i, j)` entry of the fundamental matrix under the system. -/
def systemRow (A : Matrix (Fin n) (Fin n) K) (p : Fin n × Fin n) :
    DifferentialPolynomial (Fin n × Fin n) K :=
  ∑ l, MvPolynomial.C (A p.1 l) * MvPolynomial.X ((l, p.2), 0)

/-- **The difference action on the differential coordinate ring.**  On a jet variable it is the
corresponding jet of the system row, which is what commutation with the derivation forces. -/
def sigmaJetCoordHom (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K) :
    DifferentialPolynomial (Fin n × Fin n) K →+* DifferentialPolynomial (Fin n × Fin n) K :=
  MvPolynomial.eval₂Hom
    ((MvPolynomial.C : K →+* DifferentialPolynomial (Fin n × Fin n) K).comp (σ : K →+* K))
    (fun q : (Fin n × Fin n) × ℕ => (⇑(jetCoordDeriv K n))^[q.2] (systemRow A q.1))

@[simp] theorem sigmaJetCoordHom_C (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K) (a : K) :
    sigmaJetCoordHom σ A (MvPolynomial.C a) = MvPolynomial.C (σ a) := by
  simp [sigmaJetCoordHom]

@[simp] theorem sigmaJetCoordHom_X (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K)
    (p : Fin n × Fin n) (k : ℕ) :
    sigmaJetCoordHom σ A (MvPolynomial.X (p, k))
      = (⇑(jetCoordDeriv K n))^[k] (systemRow A p) := by
  simp [sigmaJetCoordHom]

/-- **The difference action commutes with the derivation.** -/
theorem sigmaJetCoordHom_commutes (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A : Matrix (Fin n) (Fin n) K) (f : DifferentialPolynomial (Fin n × Fin n) K) :
    sigmaJetCoordHom σ A (jetCoordDeriv K n f) = jetCoordDeriv K n (sigmaJetCoordHom σ A f) := by
  classical
  induction f using MvPolynomial.induction_on with
  | C a =>
      rw [differentialPolynomialOverDerivation_C, sigmaJetCoordHom_C, sigmaJetCoordHom_C,
        differentialPolynomialOverDerivation_C, hσ a]
  | add f g hf hg =>
      rw [map_add, map_add, map_add, map_add, hf, hg]
  | mul_X f q hf =>
      obtain ⟨p, k⟩ := q
      have hXcase : sigmaJetCoordHom σ A (jetCoordDeriv K n (MvPolynomial.X (p, k)))
          = jetCoordDeriv K n (sigmaJetCoordHom σ A (MvPolynomial.X (p, k))) := by
        rw [differentialPolynomialOverDerivation_X, sigmaJetCoordHom_X, sigmaJetCoordHom_X,
          Function.iterate_succ_apply']
      have hleib1 : jetCoordDeriv K n (f * MvPolynomial.X (p, k))
          = f * jetCoordDeriv K n (MvPolynomial.X (p, k))
            + MvPolynomial.X (p, k) * jetCoordDeriv K n f := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul]
      have hleib2 : jetCoordDeriv K n
          (sigmaJetCoordHom σ A f * sigmaJetCoordHom σ A (MvPolynomial.X (p, k)))
          = sigmaJetCoordHom σ A f
              * jetCoordDeriv K n (sigmaJetCoordHom σ A (MvPolynomial.X (p, k)))
            + sigmaJetCoordHom σ A (MvPolynomial.X (p, k))
              * jetCoordDeriv K n (sigmaJetCoordHom σ A f) := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul]
      rw [hleib1, map_add, map_mul, map_mul, hf, hXcase, map_mul, hleib2]

end

end GaloisForLFunctions.HTGeometry
