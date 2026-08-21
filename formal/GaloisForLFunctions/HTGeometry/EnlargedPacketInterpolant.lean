import GaloisForLFunctions.HTGeometry.QuasiAbelianEnlargedPacket
import GaloisForLFunctions.HTGeometry.MultivariateMultiIndexJet

/-!
# Finite interpolation with vanishing at the translates

Prescribing jets at a packet *and* zero jets at finitely many translates of it is a single
interpolation problem on the enlarged packet, so the corpus's packet surjectivity solves it
outright: one multivariable polynomial realises every mixed partial below the prescribed order at
finitely many distinct points.

The points of the enlarged packet are distinct because the base points are distinct modulo the full
lattice and the complement meets the lower lattice only at zero — which is
`pairwiseDistinctModulo_enlargedPacketPoints`, stated there for the quotient and used here through
plain injectivity.

* `exists_mvPolynomial_packet_and_vanishing`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions

/-- **One polynomial with prescribed jets at the packet and vanishing jets at the translates.** -/
theorem exists_mvPolynomial_packet_and_vanishing {d c : ℕ} {I T : Type*} [Finite I] [Finite T]
    (w : I → Fin d → ℂ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (t : T → (Fin c → ℤ))
    (hinj : Function.Injective (enlargedPacketPoints w comp t))
    (m : I → ℕ) (jet : I → (Fin d →₀ ℕ) → ℂ) (s₀ : T) (hs₀ : t s₀ = 0) :
    ∃ P : MvPolynomial (Fin d) ℂ,
      (∀ i (a : Fin d →₀ ℕ), Finsupp.degree a < m i →
        multiIndexJetEvalCLM (w i) a (mvPolynomialMultivariateEntire P) = jet i a) ∧
      (∀ i (s : T), s ≠ s₀ → ∀ a : Fin d →₀ ℕ, Finsupp.degree a < m i →
        multiIndexJetEvalCLM (w i + comp (t s)) a (mvPolynomialMultivariateEntire P) = 0) := by
  classical
  obtain ⟨P, hP⟩ := exists_mvPolynomial_multiIndexJetEvalCLM_eq_arbitrary
    (enlargedPacketPoints w comp t) hinj (fun p => m p.1)
    (fun p a => if p.2 = s₀ then jet p.1 a else 0)
  refine ⟨P, fun i a ha => ?_, fun i s hs a ha => ?_⟩
  · have h := hP (i, s₀) a ha
    have hif : (if ((i, s₀) : I × T).2 = s₀ then jet ((i, s₀) : I × T).1 a else 0) = jet i a :=
      if_pos rfl
    rw [hif] at h
    have hpt : enlargedPacketPoints w comp t (i, s₀) = w i := by
      rw [enlargedPacketPoints_apply, hs₀, map_zero, add_zero]
    rwa [hpt] at h
  · have h := hP (i, s) a ha
    simp only [if_neg hs] at h
    have hpt : enlargedPacketPoints w comp t (i, s) = w i + comp (t s) := rfl
    rwa [hpt] at h

end

end GaloisForLFunctions.HTGeometry
