import GaloisForLFunctions.HTGeometry.QuasiAbelianDampedLiftConstruction

/-!
# Building the damping packet data from an invariant multiplier

The damping seed must be an automorphic form for the *lower* factor, so it cannot be an arbitrary
entire function: it has to be built from the prescribed lower column.  Multiplying by a `ΓH`-invariant
entire function is the only operation that keeps a lower form a lower form, and it is what Abe's
construction does.

This file isolates that step: given an invariant multiplier family which is flat on the finite jet
packet and whose complement translates carry the damped polynomial-Gaussian majorant, the whole
`AbeDampingPacketData` is assembled.  What remains of Abe's Proposition 8.2 is then exactly the
existence of such a multiplier family.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

universe u

variable {d c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}

/-- **An invariant multiplier keeps a lower form a lower form.** -/
theorem multivariateEntireMul_mem_forms {lower : AutomorphicFactor d ΓH}
    {g f : MultivariateEntire d} (hg : ∀ (η : Fin d → ℂ), η ∈ ΓH → ∀ x, g.1 (x + η) = g.1 x)
    (hf : f ∈ lower.forms) : multivariateEntireMul g f ∈ lower.forms := by
  intro γ x
  show g.1 (x + γ.1) * f.1 (x + γ.1) = (lower.factor γ).1 x * (g.1 x * f.1 x)
  rw [hg γ.1 γ.2 x, hf γ x]
  ring

/-- **The damping packet data from an invariant multiplier.**  Every field except the multiplier's
own two estimates is discharged here. -/
def abeDampingPacketDataOfMultiplier {lower : AutomorphicFactor d ΓH}
    {upper : AutomorphicFactor d Γ} {I : Type u} [Fintype I] [DecidableEq I]
    {w : I → Fin d → ℂ} {m : I → ℕ}
    {lowerColumn : FiniteJetPacketIndex d I m → lower.forms}
    (le : ΓH ≤ Γ)
    (compat : ∀ (η : Fin d → ℂ) (hη : η ∈ ΓH),
      (upper.factor ⟨η, le hη⟩).1 = (lower.factor ⟨η, hη⟩).1)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (comp_mem : ∀ z, comp z ∈ Γ)
    (decomp : ∀ δ ∈ Γ, ∃ η ∈ ΓH, ∃ z : Fin c → ℤ, δ = η + comp z)
    (mult : ℝ → MultivariateEntire d)
    (hinv : ∀ (B : ℝ) (η : Fin d → ℂ), η ∈ ΓH → ∀ x, (mult B).1 (x + η) = (mult B).1 x)
    (hflat : ∀ (B : ℝ) (i j : FiniteJetPacketIndex d I m),
      multiIndexJetEvalCLM (w i.1) i.2.1 (multivariateEntireMul (mult B) (lowerColumn j).1)
        = multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1)
    (hnormal : ∀ (B : ℝ) (j : FiniteJetPacketIndex d I m), SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ => poincareTerm upper
        (multivariateEntireMul (mult B) (lowerColumn j).1)
        (complementEmbedding comp comp_mem z)) Set.univ)
    (hmaj : ∃ (A : Fin c → ℕ) (sigma : Fin c → ℝ) (r : ℕ) (delta C : ℝ),
      (∀ i, 0 < sigma i) ∧ 0 < delta ∧ 0 ≤ C ∧
      ∀ B : ℝ, 0 ≤ B → ∀ (z : Fin c → ℤ) (i j : FiniteJetPacketIndex d I m), z ≠ 0 →
        ‖multiIndexJetEvalCLM (w i.1) i.2.1
            (poincareTermEntire upper (multivariateEntireMul (mult B) (lowerColumn j).1)
              (complementEmbedding comp comp_mem z))‖
          ≤ (C * (B ^ r * Real.exp (-(delta * B)))) *
              polynomialGaussianLatticeWeight (Fin c) A sigma z) :
    AbeDampingPacketData (c := c) lower upper w m lowerColumn where
  le := le
  compat := compat
  comp := comp
  comp_mem := comp_mem
  decomp := decomp
  seed := fun B j => multivariateEntireMul (mult B) (lowerColumn j).1
  seed_mem := fun B j =>
    multivariateEntireMul_mem_forms (hinv B) (lowerColumn j).2
  seed_jet := hflat
  normal := hnormal
  majorant := hmaj

end

end GaloisForLFunctions.HTGeometry
