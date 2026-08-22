import GaloisForLFunctions.HTGeometry.QuasiAbelianCosetPoincareJet

/-!
# ℓ¹ coefficient majorants extracted from Poincaré normal convergence

In Lean, locally uniform summability is an unconditional finite-subset sum.  Applying a continuous
mixed-jet observation preserves that summability; because its values are complex scalars, the norms
of the resulting jet coefficients are summable.  This gives the exact fixed-jet ℓ¹ majorant needed
for a normal-convergent coefficient source, with no separate majorant interface.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A locally normally convergent complete Poincaré family has an ℓ¹ majorant for every fixed
mixed jet of its actual summands. -/
theorem summable_norm_multiIndexJetEvalCLM_poincareTermEntire {d : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (ψ : AutomorphicFactor d Γ)
    (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun γ => poincareTerm ψ seed γ) Set.univ)
    (x : Fin d → ℂ) (a : Fin d →₀ ℕ) :
    Summable (fun γ => ‖multiIndexJetEvalCLM x a (poincareTermEntire ψ seed γ)‖) := by
  exact (hasSum_multiIndexJetEvalCLM_poincareTermEntire ψ seed hnormal x a).summable.norm

/-- The same ℓ¹ extraction for Abe's complement-indexed partial Poincaré family. -/
theorem summable_norm_multiIndexJetEvalCLM_cosetPoincareTermEntire {d c : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)} (upper : AutomorphicFactor d Γ)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (hcomp : ∀ z, comp z ∈ Γ)
    (seed : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ => poincareTerm upper seed
        (complementEmbedding comp hcomp z)) Set.univ)
    (x : Fin d → ℂ) (a : Fin d →₀ ℕ) :
    Summable (fun z : Fin c → ℤ =>
      ‖multiIndexJetEvalCLM x a
        (poincareTermEntire upper seed (complementEmbedding comp hcomp z))‖) := by
  exact ((hasSum_cosetPoincareTermEntire_of_summableLocallyUniformly
    upper comp hcomp seed hnormal).map (multiIndexJetEvalCLM x a)
      (multiIndexJetEvalCLM x a).continuous).summable.norm

end

end GaloisForLFunctions.HTGeometry
