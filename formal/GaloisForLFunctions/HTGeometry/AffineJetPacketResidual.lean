import GaloisForLFunctions.HTGeometry.AffineJetPacketWitness

/-!
# The unconditional residual source set of a noncolliding affine family

Every finite decorated pattern carries an escaping witness, so the countable Baire assembly runs
with the genuine determinant defects: for a countable family of pairwise distinct affine
automorphisms of `ℂᵈ`, `d ≥ 1`, the sources whose decorated jet determinants are all nonzero form a
dense residual subset of the compact-open space of multivariate entire functions.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Topology

noncomputable section

/-- A choice of escaping witness for every finite decorated pattern. -/
def affineJetPacketWitness {d : ℕ} (hd : 0 < d) {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (p : FiniteMultivariateAffineJetPattern Λ d) :
    MultivariateAffinePatternWitness frame p :=
  (nonempty_multivariateAffinePatternWitness hd frame hframe p).some

/-- The sources avoiding every finite decorated jet determinant of the family. -/
def affineJetPacketGenericSet {d : ℕ} (hd : 0 < d) {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame) :
    Set (MultivariateEntire d) :=
  multivariateAffinePatternResidualSet frame (affineJetPacketWitness hd frame hframe)

/-- **Unconditional affine jet-packet Baire law.**  For a countable family of pairwise distinct
affine automorphisms of `ℂᵈ` with `d ≥ 1`, the sources on which every finite decorated
jet-determinant is nonzero form a dense residual set. -/
theorem affineJetPacketGenericSet_dense_residual {d : ℕ} (hd : 0 < d) {Λ : Type*} [Countable Λ]
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame) :
    Dense (affineJetPacketGenericSet hd frame hframe) ∧
      affineJetPacketGenericSet hd frame hframe ∈ residual (MultivariateEntire d) :=
  multivariateAffinePatternResidualSet_dense_residual frame _

/-- Membership in the residual set is exactly nonvanishing of every chosen pattern determinant. -/
theorem mem_affineJetPacketGenericSet_iff {d : ℕ} (hd : 0 < d) {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (f : MultivariateEntire d) :
    f ∈ affineJetPacketGenericSet hd frame hframe ↔
      ∀ p : FiniteMultivariateAffineJetPattern Λ d,
        MvPolynomial.eval
            (multivariateAffinePatternObservationCLM frame p
              (affineJetPacketWitness hd frame hframe p).base f)
            (multivariateCoefficientPatternDeterminant
              (affineJetPacketWitness hd frame hframe p).base
              p.coordinateExponent p.jetExponent) ≠ 0 :=
  Iff.rfl

end

end GaloisForLFunctions.HTGeometry
