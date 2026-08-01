import GaloisForLFunctions.HTGeometry.NondegenerateSolutionPhaseRank
import GaloisForLFunctions.HTGeometry.CarrierTranslationEquivariance

/-!
# One nondegenerate point suffices

Degeneracy of the relation is a closed condition on the carrier, and the jets of the representatives
are translation equivariant, so a carrier point whose representative is degenerate at *every* time
forces degeneracy along a dense set of the carrier, hence everywhere — in particular at the function
itself.

So a single point of the line at which the top partial derivative of the relation is nonzero makes
every carrier representative nondegenerate somewhere, and the frequency rank is finite.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {F : ℂ → ℂ} {σ R r ρ : ℝ} {n : ℕ}

/-- **Finite phase rank from one nondegenerate point.**  If the top partial derivative of the
relation is nonzero at a single jet of the function itself, the rational Bohr frequency rank of the
line restriction is finite. -/
theorem rank_finite_of_nondegenerate_at_point (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n) {P : (Fin (n + 1) → ℂ) → ℂ} (hPcont : Continuous P)
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} (hP'cont : Continuous P')
    (hPd : ∀ y, HasFDerivAt P ((P' y).restrictScalars ℝ) y)
    (hrel : ∀ z ∈ verticalStrip σ R, P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F z) = 0)
    (hnd0 : ∃ t₀ : ℝ, partialCoeff (P' (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) F ((σ : ℂ) + (t₀ : ℂ) * Complex.I))) (Fin.last n) ≠ 0) :
    ∃ N : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (N : Cardinal) := by
  classical
  obtain ⟨Gb, ν, rep, hνcont, hrepdiff, hrepval, hrepline, hrelrep⟩ :=
    exists_carrier_representatives hr hρ hrρ hF hap hf hfu hPcont hrel
  have hrρ0 : 0 < r + ρ := by linarith
  have hsub : verticalStrip σ (r + ρ) ⊆ verticalStrip σ R := fun z hz =>
    lt_trans hz hrρ
  refine rank_finite_of_pointwise_nondegenerate hr hρ hfu hftb hνcont hrepdiff hrepval hrepline hn
    hP'cont hPd (fun x s => hrelrep x _ (mem_verticalStrip_line hrρ0 σ s)) (fun x => ?_)
  by_contra hcon
  push Not at hcon
  set ψ : BohrHull f → ℂ := fun y => partialCoeff (P' (fun k : Fin (n + 1) =>
    iteratedDeriv (k : ℕ) (rep y) ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I))) (Fin.last n) with hψdef
  have hjetc : Continuous fun y : BohrHull f => (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep y) ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)) :=
    continuous_pi fun k =>
      continuous_jet_of_representatives hρ hr (by linarith) hνcont hrepdiff hrepval (k : ℕ) 0
  have hψcont : Continuous ψ := by
    have happ : Continuous fun L : ((Fin (n + 1) → ℂ) →L[ℂ] ℂ) =>
        L (Pi.single (Fin.last n) (1 : ℂ)) := continuous_id.clm_apply continuous_const
    exact happ.comp (hP'cont.comp hjetc)
  have hzero : ∀ t : ℝ, ψ (x + bohrIota f t) = 0 := by
    intro t
    have hjet : ∀ k : Fin (n + 1),
        iteratedDeriv (k : ℕ) (rep (x + bohrIota f t)) ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)
          = iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I) := by
      intro k
      have h := iteratedDeriv_rep_translate hrρ0 hrepdiff hrepline x t (k : ℕ) 0
      rw [h]
      norm_num
    have hfun : (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (rep (x + bohrIota f t))
        ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I))
        = fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I) :=
      funext hjet
    have hrw : ψ (x + bohrIota f t) = partialCoeff (P' (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I))) (Fin.last n) := by
      simp only [hψdef, hfun]
    rw [hrw, hcon t]
  obtain ⟨t₀, ht₀⟩ := hnd0
  have hval : ψ ((0 : BohrHull f) + bohrIota f t₀)
      = partialCoeff (P' (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) F ((σ : ℂ) + (t₀ : ℂ) * Complex.I))) (Fin.last n) := by
    have hjet : ∀ k : Fin (n + 1),
        iteratedDeriv (k : ℕ) (rep ((0 : BohrHull f) + bohrIota f t₀))
            ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I)
          = iteratedDeriv (k : ℕ) F ((σ : ℂ) + (t₀ : ℂ) * Complex.I) := by
      intro k
      rw [iteratedDeriv_rep_translate hrρ0 hrepdiff hrepline 0 t₀ (k : ℕ) 0,
        iteratedDeriv_rep_zero hrρ0 (hF.mono hsub) hf hrepdiff hrepline (k : ℕ) (t₀ + 0)]
      norm_num
    have hfun : (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ)
        (rep ((0 : BohrHull f) + bohrIota f t₀)) ((σ : ℂ) + ((0 : ℝ) : ℂ) * Complex.I))
        = fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
      funext hjet
    simp only [hψdef, hfun]
  rw [eq_of_eqOn_translates hψcont hzero ((0 : BohrHull f) + bohrIota f t₀)] at hval
  exact ht₀ hval.symm

end GaloisForLFunctions
