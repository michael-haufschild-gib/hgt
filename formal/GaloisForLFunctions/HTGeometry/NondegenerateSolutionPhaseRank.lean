import GaloisForLFunctions.HTGeometry.StripSolutionPhaseRank

/-!
# Nondegeneracy replaces the regularity atlas

A regularity region is a convex neighbourhood of a jet on which the top partial derivative of the
relation dominates the deviation of the derivative.  Around any jet where that partial derivative is
nonzero, continuity of the derivative produces such a ball.

The carrier is compact and the jet of the representative at each point of the line is continuous on
it, so if every solution is nondegenerate at some point of the line, finitely many of those balls —
each attached to its own time — already cover the carrier.  The atlas is then not an assumption but a
consequence, and the frequency rank is finite.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {F : ℂ → ℂ} {σ R r ρ : ℝ} {n : ℕ}

/-- **Finite phase rank from pointwise nondegeneracy on the carrier.**  If every carrier
representative has a jet along the line at which the top partial derivative of the relation is
nonzero, the balls where that partial derivative dominates cover the compact carrier, and the
frequency rank is finite. -/
theorem rank_finite_of_pointwise_nondegenerate (hr : 0 < r) (hρ : 0 < ρ)
    {f : ℝ →ᵇ ℂ} (hfu : UniformContinuous (fun x => f x))
    (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {Gb : ℝ →ᵇ ((closedStrip σ (r + ρ)) →ᵇ ℂ)}
    {ν : BohrHull f → BohrHull Gb} (hνcont : Continuous ν)
    {rep : BohrHull f → (ℂ → ℂ)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepval : ∀ (x : BohrHull f) (z : closedStrip σ (r + ρ)),
      rep x (z : ℂ) = bohrEval Gb (ν x) z)
    (hrepline : ∀ (x : BohrHull f) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t))
    (hn : 0 < n) {P : (Fin (n + 1) → ℂ) → ℂ}
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} (hP'cont : Continuous P')
    (hPd : ∀ y, HasFDerivAt P ((P' y).restrictScalars ℝ) y)
    (hrelrep : ∀ (x : BohrHull f) (s : ℝ), P (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (s : ℂ) * Complex.I)) = 0)
    (hnd : ∀ x : BohrHull f, ∃ t : ℝ, partialCoeff (P' (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I))) (Fin.last n) ≠ 0) :
    ∃ N : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (N : Cardinal) := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull hftb
  -- the jet of each representative at a point of the line
  set jet : ℝ → BohrHull f → (Fin (n + 1) → ℂ) := fun t x => fun k : Fin (n + 1) =>
    iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I) with hjet
  have hjetcont : ∀ t : ℝ, Continuous (jet t) := fun t => continuous_pi fun k =>
    continuous_jet_of_representatives hρ hr (by linarith) hνcont hrepdiff hrepval (k : ℕ) t
  -- a regularity region is a time together with a jet at which the top partial is nonzero
  set ι : Type :=
    {i : ℝ × (Fin (n + 1) → ℂ) // partialCoeff (P' i.2) (Fin.last n) ≠ 0} with hιdef
  have hδ : ∀ i : ι, ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Metric.ball ((i : ℝ × (Fin (n + 1) → ℂ)).2) δ,
      ‖P' z - P' ((i : ℝ × (Fin (n + 1) → ℂ)).2)‖
        ≤ ‖partialCoeff (P' ((i : ℝ × (Fin (n + 1) → ℂ)).2)) (Fin.last n)‖ / 2 := by
    intro i
    have hne : partialCoeff (P' ((i : ℝ × (Fin (n + 1) → ℂ)).2)) (Fin.last n) ≠ 0 := i.2
    have hpos : 0 < ‖partialCoeff (P' ((i : ℝ × (Fin (n + 1) → ℂ)).2)) (Fin.last n)‖ / 2 := by
      have := norm_pos_iff.mpr hne
      linarith
    obtain ⟨δ, hδ0, hδlt⟩ :=
      Metric.continuous_iff.mp hP'cont ((i : ℝ × (Fin (n + 1) → ℂ)).2) _ hpos
    refine ⟨δ, hδ0, fun z hz => le_of_lt ?_⟩
    have := hδlt z hz
    rwa [dist_eq_norm] at this
  choose δ hδpos hδbound using hδ
  set S : ι → Set (Fin (n + 1) → ℂ) := fun i =>
    Metric.ball ((i : ℝ × (Fin (n + 1) → ℂ)).2) (δ i) with hS
  set L : ι → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ) := fun i => P' ((i : ℝ × (Fin (n + 1) → ℂ)).2) with hL
  set C : ι → ℝ := fun i =>
    ‖partialCoeff (P' ((i : ℝ × (Fin (n + 1) → ℂ)).2)) (Fin.last n)‖ / 2 with hC
  -- every carrier point is regular in the region around its own jet at its own regular time
  have hcov : ∀ x : BohrHull f,
      ∃ i : ι, x ∈ {x : BohrHull f | jet ((i : ℝ × (Fin (n + 1) → ℂ)).1) x ∈ S i} := by
    intro x
    obtain ⟨t, ht⟩ := hnd x
    exact ⟨⟨(t, jet t x), ht⟩, Metric.mem_ball_self (hδpos _)⟩
  obtain ⟨T, hT⟩ := exists_finite_sample_cover
    (U := fun i : ι => {x : BohrHull f | jet ((i : ℝ × (Fin (n + 1) → ℂ)).1) x ∈ S i})
    (fun i => (hjetcont _).isOpen_preimage _ Metric.isOpen_ball) hcov
  refine ⟨2 * (T.card * (n + 1)), ?_⟩
  refine rank_le_of_regular_jets (τ := fun i : ι => (i : ℝ × (Fin (n + 1) → ℂ)).1)
    (S := S) (L := L) (C := C) (T := T)
    hρ hr hfu hftb hνcont hrepdiff hrepval hrepline hn
    (fun i => Metric.isOpen_ball) (fun i => convex_ball _ _)
    (fun i y _ => (hPd y).hasFDerivWithinAt)
    (fun i => by positivity) (fun i y hy => hδbound i y hy) (fun i => ?_)
    hrelrep (fun x => ?_)
  · have hne : partialCoeff (P' ((i : ℝ × (Fin (n + 1) → ℂ)).2)) (Fin.last n) ≠ 0 := i.2
    have := norm_pos_iff.mpr hne
    show ‖partialCoeff (P' ((i : ℝ × (Fin (n + 1) → ℂ)).2)) (Fin.last n)‖ / 2
      < ‖partialCoeff (L i) (Fin.last n)‖
    rw [hL]
    linarith
  · obtain ⟨i, hiT, hiS⟩ := hT x
    exact ⟨i, hiT, hiS⟩

/-- **Finite phase rank from nondegeneracy alone.**  If the top partial derivative of the relation is
nonzero at *some* jet along the line of every holomorphic solution on the substrip, the rational Bohr
frequency rank of the line restriction is finite. -/
theorem rank_finite_of_nondegenerate_solution (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n) {P : (Fin (n + 1) → ℂ) → ℂ} (hPcont : Continuous P)
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} (hP'cont : Continuous P')
    (hPd : ∀ y, HasFDerivAt P ((P' y).restrictScalars ℝ) y)
    (hrel : ∀ z ∈ verticalStrip σ R, P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F z) = 0)
    (hnd : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (verticalStrip σ (r + ρ)) →
      (∀ z ∈ verticalStrip σ (r + ρ),
        P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) g z) = 0) →
      ∃ t : ℝ, partialCoeff (P' (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I))) (Fin.last n) ≠ 0) :
    ∃ N : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (N : Cardinal) := by
  obtain ⟨Gb, ν, rep, hνcont, hrepdiff, hrepval, hrepline, hrelrep⟩ :=
    exists_carrier_representatives hr hρ hrρ hF hap hf hfu hPcont hrel
  exact rank_finite_of_pointwise_nondegenerate hr hρ hfu hftb hνcont hrepdiff hrepval hrepline hn
    hP'cont hPd
    (fun x s => hrelrep x _ (mem_verticalStrip_line (by linarith) σ s))
    (fun x => hnd (rep x) (hrepdiff x) (hrelrep x))

end GaloisForLFunctions
