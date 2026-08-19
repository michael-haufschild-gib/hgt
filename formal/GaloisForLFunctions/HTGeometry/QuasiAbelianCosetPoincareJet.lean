import GaloisForLFunctions.HTGeometry.QuasiAbelianCosetPoincareSeries

/-!
# Mixed jets of a partial Poincaré series

Every mixed-jet observation is a continuous linear functional on the compact-open entire-source
space, so it passes through the locally normally convergent partial Poincaré sum term by term.
Splitting off the complement index `0` gives Abe's decomposition at the level of jets:

`jet(F) = jet(seed) + ∑_{z ≠ 0} jet(term z)`,

which is exactly the shape the damped-extension interface of the torusless quasi-Abelian card
consumes.
-/

open Filter Function Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem hasSum_cosetPoincareTermEntire_of_summableLocallyUniformly
    {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (upper : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ))
    (hcomp : ∀ z, comp z ∈ Γ) (H : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ => poincareTerm upper H (complementEmbedding comp hcomp z)) Set.univ) :
    HasSum (fun z : Fin c → ℤ =>
        poincareTermEntire upper H (complementEmbedding comp hcomp z))
      (cosetPoincareSeriesEntire upper comp hcomp H hnormal) := by
  change Tendsto
    (fun s : Finset (Fin c → ℤ) =>
      ∑ z ∈ s, poincareTermEntire upper H (complementEmbedding comp hcomp z)) atTop
    (nhds (cosetPoincareSeriesEntire upper comp hcomp H hnormal))
  apply tendsto_multivariateEntire_of_locallyUniform
  rw [← tendstoLocallyUniformlyOn_univ]
  have hnormal' : TendstoLocallyUniformlyOn
      (fun s : Finset (Fin c → ℤ) => fun x =>
        ∑ z ∈ s, poincareTerm upper H (complementEmbedding comp hcomp z) x)
      (fun x => ∑' z, poincareTerm upper H (complementEmbedding comp hcomp z) x)
      atTop Set.univ :=
    hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp
      hnormal.hasSumLocallyUniformlyOn
  convert hnormal' using 1
  · ext s x
    simp [poincareTermEntire]
  · ext x
    simp [cosetPoincareSeriesEntire, cosetPoincareSeries]

/-- The complement index `0` contributes the seed itself. -/
theorem poincareTermEntire_complementEmbedding_zero
    {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (upper : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ))
    (hcomp : ∀ z, comp z ∈ Γ) (H : MultivariateEntire d) :
    poincareTermEntire upper H (complementEmbedding comp hcomp (0 : Fin c → ℤ)) = H := by
  have he0 : complementEmbedding comp hcomp (0 : Fin c → ℤ) = 0 := by
    ext i
    simp [complementEmbedding, map_zero]
  ext x
  change poincareTerm upper H (complementEmbedding comp hcomp (0 : Fin c → ℤ)) x = H.1 x
  rw [poincareTerm, he0]
  rw [upper.normalized x]
  simp

/-- **The jet of a partial Poincaré series splits as seed plus complement remainder.** -/
theorem jet_cosetPoincareSeriesEntire_eq_seed_add_tail
    {d c : ℕ} {Γ : AddSubgroup (Fin d → ℂ)}
    (upper : AutomorphicFactor d Γ) (comp : (Fin c → ℤ) →+ (Fin d → ℂ))
    (hcomp : ∀ z, comp z ∈ Γ) (H : MultivariateEntire d)
    (hnormal : SummableLocallyUniformlyOn
      (fun z : Fin c → ℤ => poincareTerm upper H (complementEmbedding comp hcomp z)) Set.univ)
    (x : Fin d → ℂ) (a : Fin d →₀ ℕ) :
    multiIndexJetEvalCLM x a (cosetPoincareSeriesEntire upper comp hcomp H hnormal)
      = multiIndexJetEvalCLM x a H
        + ∑' z : Fin c → ℤ,
            (if z = 0 then 0
              else multiIndexJetEvalCLM x a
                (poincareTermEntire upper H (complementEmbedding comp hcomp z))) := by
  have hsum := hasSum_cosetPoincareTermEntire_of_summableLocallyUniformly
    upper comp hcomp H hnormal
  have hmap := hsum.map (multiIndexJetEvalCLM x a) (multiIndexJetEvalCLM x a).continuous
  have hsummable : Summable (fun z : Fin c → ℤ =>
      multiIndexJetEvalCLM x a
        (poincareTermEntire upper H (complementEmbedding comp hcomp z))) := hmap.summable
  have hz := hsummable.tsum_eq_add_tsum_ite (0 : Fin c → ℤ)
  rw [← hmap.tsum_eq]
  simp only [Function.comp_def]
  rw [hz, poincareTermEntire_complementEmbedding_zero]

end

end GaloisForLFunctions.HTGeometry
