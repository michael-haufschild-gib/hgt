import GaloisForLFunctions.HTGeometry.QuasiAbelianDampingMultiplier
import GaloisForLFunctions.HTGeometry.PacketFlatMultiplier

/-!
# The damping packet data from a family of packet profiles

One invariant profile per packet point, each normalized to `1` at its own point, assembles into the
packet multiplier `1 − ∏ᵢ (1 − Θᵢ)^{mᵢ}`, and that multiplier discharges the invariance and
flatness fields of `AbeDampingPacketData` outright.  The packet's own jet orders are exactly the
exponents needed: a packet index carries the proof that its jet degree is below the order at its
point.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

universe u

variable {d c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}

/-- **The damping packet data from a family of normalized invariant profiles.** -/
def abeDampingPacketDataOfPacketProfiles {lower : AutomorphicFactor d ΓH}
    {upper : AutomorphicFactor d Γ} {I : Type u} [Fintype I] [DecidableEq I]
    {w : I → Fin d → ℂ} {m : I → ℕ}
    {lowerColumn : FiniteJetPacketIndex d I m → lower.forms}
    (le : ΓH ≤ Γ)
    (compat : ∀ (η : Fin d → ℂ) (hη : η ∈ ΓH),
      (upper.factor ⟨η, le hη⟩).1 = (lower.factor ⟨η, hη⟩).1)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (comp_mem : ∀ z, comp z ∈ Γ)
    (decomp : ∀ δ ∈ Γ, ∃ η ∈ ΓH, ∃ z : Fin c → ℤ, δ = η + comp z)
    (Θ : ℝ → I → MultivariateEntire d)
    (hΘinv : ∀ (B : ℝ) (i : I), ∀ η ∈ ΓH, ∀ x, (Θ B i).1 (x + η) = (Θ B i).1 x)
    (hΘone : ∀ (B : ℝ) (i : I), (Θ B i).1 (w i) = 1)
    (hnormal : ∀ (B : ℝ) (j : FiniteJetPacketIndex d I m), SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ => poincareTerm upper
        (multivariateEntireMul (packetFlatMultiplier (Θ B) m) (lowerColumn j).1)
        (complementEmbedding comp comp_mem z)) Set.univ)
    (hmaj : ∃ (A : Fin c → ℕ) (sigma : Fin c → ℝ) (r : ℕ) (delta C : ℝ),
      (∀ i, 0 < sigma i) ∧ 0 < delta ∧ 0 ≤ C ∧
      ∀ B : ℝ, 0 ≤ B → ∀ (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m), z ≠ 0 →
        ‖multiIndexJetEvalCLM (w i.1) i.2.1
            (poincareTermEntire upper
              (multivariateEntireMul (packetFlatMultiplier (Θ B) m) (lowerColumn j).1)
              (complementEmbedding comp comp_mem z))‖
          ≤ (C * (B ^ r * Real.exp (-(delta * B)))) *
              polynomialGaussianLatticeWeight (Fin c) A sigma z) :
    AbeDampingPacketData (c := c) lower upper w m lowerColumn :=
  abeDampingPacketDataOfMultiplier le compat comp comp_mem decomp
    (fun B => packetFlatMultiplier (Θ B) m)
    (fun B => packetFlatMultiplier_invariant (Θ B) m (fun i => hΘinv B i))
    (fun B i j => multiIndexJetEvalCLM_packetFlatMultiplier_mul (Θ B) m (lowerColumn j).1 i.1
      (hΘone B i.1) i.2.1 i.2.2)
    hnormal hmaj

end

end GaloisForLFunctions.HTGeometry
