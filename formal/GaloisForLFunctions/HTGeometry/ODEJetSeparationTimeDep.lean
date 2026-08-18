import GaloisForLFunctions.HTGeometry.ODEJetSeparation

/-!
# A finite jet determines a solution of a nonautonomous explicit equation

An explicit scalar equation `y⁽ⁿ⁾(t) = Φ t (y(t), …, y⁽ⁿ⁻¹⁾(t))` whose right-hand side is Lipschitz
in the jet, uniformly in the time, becomes a nonautonomous first-order system for the jet vector.
Uniqueness for Lipschitz ordinary differential equations is insensitive to the time dependence: it
asks only for a Lipschitz bound at each time, with no regularity in the time at all.

This is what a differential equation with almost-periodic coefficients needs: solutions on one fibre
of the coefficient projection satisfy one and the same nonautonomous relation, and a finite jet at a
single time separates them.
-/

open Filter Topology Metric

namespace GaloisForLFunctions

/-- The jet vector of a solution of a nonautonomous explicit equation solves the companion
system. -/
theorem hasDerivAt_jetVec_timeDep {n : ℕ} {Φ : ℝ → (Fin n → ℂ) → ℂ} {g : ℝ → ℂ} {t : ℝ}
    (hg : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i g) (iteratedDeriv (i + 1) g t) t)
    (hgODE : iteratedDeriv n g t = Φ t (jetVec g t)) :
    HasDerivAt (jetVec (n := n) g) (companionField (Φ t) (jetVec g t)) t :=
  hasDerivAt_jetVec hg hgODE

/-- **A finite jet determines a solution of a nonautonomous explicit equation, on a region where the
right-hand side is Lipschitz uniformly in the time.** -/
theorem jetVec_eq_of_eq_at_timeDep {n : ℕ} {Φ : ℝ → (Fin n → ℂ) → ℂ} {K : NNReal}
    {S : Set (Fin n → ℂ)} (hΦ : ∀ t, LipschitzOnWith K (Φ t) S) {g h : ℝ → ℂ} {t₀ : ℝ}
    (hg : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i g) (iteratedDeriv (i + 1) g t) t)
    (hgODE : ∀ t, iteratedDeriv n g t = Φ t (jetVec g t)) (hgS : ∀ t, jetVec (n := n) g t ∈ S)
    (hh : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i h) (iteratedDeriv (i + 1) h t) t)
    (hhODE : ∀ t, iteratedDeriv n h t = Φ t (jetVec h t)) (hhS : ∀ t, jetVec (n := n) h t ∈ S)
    (hjet : jetVec (n := n) g t₀ = jetVec (n := n) h t₀) :
    jetVec (n := n) g = jetVec (n := n) h := by
  refine ODE_solution_unique_univ (K := max 1 K) (v := fun t => companionField (Φ t))
    (s := fun _ => S) (t₀ := t₀) ?_ ?_ ?_ hjet
  · intro t
    exact lipschitzOnWith_companionField (hΦ t)
  · intro t
    exact ⟨hasDerivAt_jetVec_timeDep hg (hgODE t), hgS t⟩
  · intro t
    exact ⟨hasDerivAt_jetVec_timeDep hh (hhODE t), hhS t⟩

/-- The scalar consequence. -/
theorem eq_of_jetVec_eq_at_timeDep {n : ℕ} (hn : 0 < n) {Φ : ℝ → (Fin n → ℂ) → ℂ} {K : NNReal}
    {S : Set (Fin n → ℂ)} (hΦ : ∀ t, LipschitzOnWith K (Φ t) S) {g h : ℝ → ℂ} {t₀ : ℝ}
    (hg : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i g) (iteratedDeriv (i + 1) g t) t)
    (hgODE : ∀ t, iteratedDeriv n g t = Φ t (jetVec g t)) (hgS : ∀ t, jetVec (n := n) g t ∈ S)
    (hh : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i h) (iteratedDeriv (i + 1) h t) t)
    (hhODE : ∀ t, iteratedDeriv n h t = Φ t (jetVec h t)) (hhS : ∀ t, jetVec (n := n) h t ∈ S)
    (hjet : jetVec (n := n) g t₀ = jetVec (n := n) h t₀) : g = h := by
  have hall := jetVec_eq_of_eq_at_timeDep hΦ hg hgODE hgS hh hhODE hhS hjet
  funext t
  have := congrFun (congrFun hall t) ⟨0, hn⟩
  simpa [jetVec] using this

/-- **Local jet separation for a nonautonomous equation.** -/
theorem eventuallyEq_of_jetVec_eq_at_timeDep {n : ℕ} (hn : 0 < n) {Φ : ℝ → (Fin n → ℂ) → ℂ}
    {K : NNReal} {S : Set (Fin n → ℂ)} {g h : ℝ → ℂ} {t₀ : ℝ}
    (hΦ : ∀ᶠ t in nhds t₀, LipschitzOnWith K (Φ t) S)
    (hg : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i g) (iteratedDeriv (i + 1) g t) t)
    (hgODE : ∀ᶠ t in nhds t₀, iteratedDeriv n g t = Φ t (jetVec g t))
    (hgS : ∀ᶠ t in nhds t₀, jetVec (n := n) g t ∈ S)
    (hh : ∀ i : ℕ, i < n → ∀ t, HasDerivAt (iteratedDeriv i h) (iteratedDeriv (i + 1) h t) t)
    (hhODE : ∀ᶠ t in nhds t₀, iteratedDeriv n h t = Φ t (jetVec h t))
    (hhS : ∀ᶠ t in nhds t₀, jetVec (n := n) h t ∈ S)
    (hjet : jetVec (n := n) g t₀ = jetVec (n := n) h t₀) :
    g =ᶠ[nhds t₀] h := by
  have hjets : jetVec (n := n) g =ᶠ[nhds t₀] jetVec (n := n) h := by
    refine ODE_solution_unique_of_eventually (K := max 1 K) (v := fun t => companionField (Φ t))
      (s := fun _ => S) ?_ ?_ ?_ hjet
    · filter_upwards [hΦ] with t ht
      exact lipschitzOnWith_companionField ht
    · filter_upwards [hgS, hgODE] with t ht hode
      exact ⟨hasDerivAt_jetVec_timeDep hg hode, ht⟩
    · filter_upwards [hhS, hhODE] with t ht hode
      exact ⟨hasDerivAt_jetVec_timeDep hh hode, ht⟩
  filter_upwards [hjets] with t ht
  have := congrFun ht ⟨0, hn⟩
  simpa [jetVec] using this

end GaloisForLFunctions
