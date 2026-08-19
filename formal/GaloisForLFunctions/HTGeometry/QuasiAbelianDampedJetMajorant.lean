import GaloisForLFunctions.HTGeometry.QuasiAbelianComplementGrowthData
import GaloisForLFunctions.HTGeometry.MultivariateEntireCauchyEstimate

/-!
# The jet majorant of the damped Poincaré term

The damping data bounds the Poincaré term of the damped seed pointwise on a compact set.  Cauchy's
estimate turns that into a bound on every mixed jet at every point whose reachable ball stays inside
the set — no Leibniz expansion of the product `(factor)⁻¹ · seed` is needed, because the value bound
already holds uniformly on the set the jet's Cauchy circles sweep.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The jet majorant.**  Every mixed jet of the damped Poincaré term is exponentially small in the
scale, against the same polynomial-Gaussian lattice weight. -/
theorem norm_multiIndexJet_poincareTerm_dampedFlatSeed_le {d c : ℕ}
    {Γ : AddSubgroup (Fin d → ℂ)}
    (ψ : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ)) (hcomp : ∀ z, comp z ∈ Γ)
    {K : Set (Fin d → ℂ)} (hK : IsCompact K)
    (G : ComplementGaussianGrowth ψ comp hcomp)
    {I : Type*} [Fintype I] [DecidableEq I] (w : I → Fin d → ℂ)
    (hdistinct : PairwiseDistinctModulo (standardIntegerLattice d) w) (target : I)
    {m : ℕ} (hm : 0 < m) (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    {ρ σ₀ eps : ℝ} (hσ₀le : ∀ i, σ₀ ≤ σ i) (heps : 0 ≤ eps)
    (hgap : ∀ i, G.tau i + eps ≤ σ i / 4)
    (hpos : 0 ≤ σ₀ * G.kappa / 4 - (∑ i, σ i) * (2 * ρ ^ 2))
    (P : MvPolynomial (Fin d) ℂ)
    (hKb : ∀ x ∈ K, ∀ i, |(x i).re - (w target i).re| ≤ ρ ∧ |(x i).im - (w target i).im| ≤ ρ)
    {r : ℝ} (hr : 0 < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℝ, 1 ≤ B → ∀ z : Fin c → ℤ, z ≠ 0 →
      ∀ (p : Fin d → ℂ) (a : Fin d →₀ ℕ),
        (∀ y : Fin d → ℂ,
          ‖y - p‖ ≤ ((Fintype.card (MultiIndexSlot a) : ℕ) : ℝ) * r → y ∈ K) →
        ‖multiIndexJetEvalCLM p a
            (poincareTermEntire ψ (dampedFlatSeed w hdistinct target hm σ P B)
              ⟨comp z, hcomp z⟩)‖
          ≤ (C * Real.exp (-((σ₀ * G.kappa / 4 - (∑ i, σ i) * (2 * ρ ^ 2)) * B))
              * polynomialGaussianLatticeWeight (Fin c) (fun _ => ∑ i, P.degreeOf i)
                  (fun _ => eps * G.kappa) z)
            / r ^ (Fintype.card (MultiIndexSlot a)) := by
  obtain ⟨C, hC0, hC⟩ := norm_poincareTerm_dampedFlatSeed_le ψ comp hcomp hK G w hdistinct
    target hm σ hσ hσ₀le heps hgap hpos P hKb
  refine ⟨C, hC0, fun B hB z hz p a hball => ?_⟩
  refine norm_multiIndexJetEvalCLM_le p a _ hr ?_
  intro y hy
  exact hC B hB z hz y (hball y hy)

end

end GaloisForLFunctions.HTGeometry
