import GaloisForLFunctions.HTGeometry.StripJetSeparation
import GaloisForLFunctions.HTGeometry.ODEJetSeparationTimeDep
import GaloisForLFunctions.HTGeometry.ImplicitLipschitzConst

/-!
# Jet separation on a strip for a relation with varying coefficients

A relation whose coefficients depend on the point of the strip defines, at each time of the central
line, its own explicit branch.  When the dominance datum — the reference functional, the deviation
bound and the convex region — does not depend on the time, all those branches share one Lipschitz
constant, and the nonautonomous uniqueness theorem separates two solutions from their jets at a
single time.

This is the form the relative frequency law needs: two members of one fibre of the coefficient
projection satisfy the *same* relation with varying coefficients, so a finite jet at one time
determines them.
-/

open Filter Topology Metric Set

namespace GaloisForLFunctions

variable {σ R : ℝ} {n : ℕ}

/-- **Finite jets on the central line separate solutions of a nonautonomous explicit equation.** -/
theorem eqOn_of_line_jet_eq_timeDep {g h : ℂ → ℂ} (hR : 0 < R) (hn : 0 < n)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    {Φ : ℝ → (Fin n → ℂ) → ℂ} {K : NNReal} (hΦ : ∀ t, LipschitzWith K (Φ t))
    (hgODE : ∀ t : ℝ, iteratedDeriv n g ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ t fun k : Fin n => iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hhODE : ∀ t : ℝ, iteratedDeriv n h ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ t fun k : Fin n => iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I))
    {t₀ : ℝ}
    (hjet : ∀ k : Fin n, iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
      = iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) :
    Set.EqOn g h (verticalStrip σ R) := by
  have hline : (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I))
      = fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I) := by
    refine eq_of_jetVec_eq_at_timeDep hn
      (Φ := fun t => twistField (Φ t)) (S := Set.univ)
      (fun t => (lipschitzWith_twistField (hΦ t)).lipschitzOnWith) (t₀ := t₀)
      (fun i _ t => hasDerivAt_iteratedDeriv_line hR hg i t)
      (fun t => iteratedDeriv_line_eq_twist hR hg (hgODE t)) (fun _ => trivial)
      (fun i _ t => hasDerivAt_iteratedDeriv_line hR hh i t)
      (fun t => iteratedDeriv_line_eq_twist hR hh (hhODE t)) (fun _ => trivial) ?_
    funext k
    have hk1 : jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀ k
        = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
      iteratedDeriv_line_restriction hR hg (k : ℕ) t₀
    have hk2 : jetVec (fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀ k
        = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
      iteratedDeriv_line_restriction hR hh (k : ℕ) t₀
    rw [hk1, hk2, hjet k]
  exact eqOn_of_eqOn_line hR hg hh (fun t => congrFun hline t)

/-- **Jet separation from a relation with varying coefficients.**  Two holomorphic functions on a
strip whose `(n+1)`-jets along the central line solve the same time-dependent relation inside a
fixed convex region on which one fixed functional dominates, and whose `n`-jets agree at one point,
agree on the strip. -/
theorem eqOn_of_line_jet_eq_implicit_timeDep {g h : ℂ → ℂ} (hR : 0 < R) (hn : 0 < n)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    {P : ℝ → (Fin (n + 1) → ℂ) → ℂ}
    {P' : ℝ → (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : Set (Fin (n + 1) → ℂ)}
    (hS : Convex ℝ S)
    (hP : ∀ t, ∀ y ∈ S, HasFDerivWithinAt (P t) ((P' t y).restrictScalars ℝ) S y)
    {L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ t, ∀ y ∈ S, ‖P' t y - L‖ ≤ C)
    (hdom : C < ‖partialCoeff L (Fin.last n)‖)
    (hgS : ∀ t : ℝ, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hgP : ∀ t : ℝ, P t (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    (hhS : ∀ t : ℝ, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hhP : ∀ t : ℝ, P t (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    {t₀ : ℝ}
    (hjet : ∀ k : Fin n, iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
      = iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) :
    Set.EqOn g h (verticalStrip σ R) := by
  classical
  have hbranch : ∀ t : ℝ, ∃ Φt : (Fin n → ℂ) → ℂ,
      LipschitzWith (implicitLipschitzConst n L C) Φt ∧
        ∀ y ∈ S, P t y = 0 → y (Fin.last n) = Φt (fun k : Fin n => y k.castSucc) := fun t =>
    exists_lipschitz_implicit_const hS (hP t) hC (hbound t) hdom
  choose Φ hΦlip hΦval using hbranch
  have hgODE : ∀ t : ℝ, iteratedDeriv n g ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ t fun k : Fin n => iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    have hval := hΦval t _ (hgS t) (hgP t)
    simpa using hval
  have hhODE : ∀ t : ℝ, iteratedDeriv n h ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ t fun k : Fin n => iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro t
    have hval := hΦval t _ (hhS t) (hhP t)
    simpa using hval
  exact eqOn_of_line_jet_eq_timeDep hR hn hg hh hΦlip hgODE hhODE hjet

/-- **Local jet separation for a nonautonomous explicit equation.** -/
theorem eqOn_of_line_jet_eq_local_timeDep {g h : ℂ → ℂ} (hR : 0 < R) (hn : 0 < n)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    {Φ : ℝ → (Fin n → ℂ) → ℂ} {K : NNReal} {S : Set (Fin n → ℂ)} {t₀ : ℝ}
    (hΦ : ∀ᶠ t in nhds t₀, LipschitzOnWith K (Φ t) S)
    (hgODE : ∀ᶠ t : ℝ in nhds t₀, iteratedDeriv n g ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ t fun k : Fin n => iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hhODE : ∀ᶠ t : ℝ in nhds t₀, iteratedDeriv n h ((σ : ℂ) + (t : ℂ) * Complex.I)
      = Φ t fun k : Fin n => iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hgS : ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin n =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hhS : ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin n =>
      iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hjet : ∀ k : Fin n, iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
      = iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) :
    Set.EqOn g h (verticalStrip σ R) := by
  have htwist : ∀ (u : ℂ → ℂ), DifferentiableOn ℂ u (verticalStrip σ R) → ∀ t : ℝ,
      twistMap (jetVec (fun s : ℝ => u ((σ : ℂ) + (s : ℂ) * Complex.I)) t)
        = fun k : Fin n => iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro u hu t
    funext k
    have hk : jetVec (fun s : ℝ => u ((σ : ℂ) + (s : ℂ) * Complex.I)) t k
        = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I) :=
      iteratedDeriv_line_restriction hR hu (k : ℕ) t
    show (Complex.I ^ (k : ℕ))⁻¹ * jetVec (fun s : ℝ => u ((σ : ℂ) + (s : ℂ) * Complex.I)) t k
      = iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I)
    rw [hk, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ Complex.I_ne_zero), one_mul]
  have hline : (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I))
      =ᶠ[nhds t₀] fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I) := by
    refine eventuallyEq_of_jetVec_eq_at_timeDep hn
      (Φ := fun t => twistField (Φ t)) (S := twistMap ⁻¹' S)
      (by filter_upwards [hΦ] with t ht; exact lipschitzOnWith_twistField ht)
      (fun i _ t => hasDerivAt_iteratedDeriv_line hR hg i t) ?_ ?_
      (fun i _ t => hasDerivAt_iteratedDeriv_line hR hh i t) ?_ ?_ ?_
    · filter_upwards [hgODE] with t ht
      exact iteratedDeriv_line_eq_twist hR hg ht
    · filter_upwards [hgS] with t ht
      show twistMap (jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t) ∈ S
      rw [htwist g hg t]
      exact ht
    · filter_upwards [hhODE] with t ht
      exact iteratedDeriv_line_eq_twist hR hh ht
    · filter_upwards [hhS] with t ht
      show twistMap (jetVec (fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I)) t) ∈ S
      rw [htwist h hh t]
      exact ht
    · funext k
      have hk1 : jetVec (fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀ k
          = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
        iteratedDeriv_line_restriction hR hg (k : ℕ) t₀
      have hk2 : jetVec (fun s : ℝ => h ((σ : ℂ) + (s : ℂ) * Complex.I)) t₀ k
          = Complex.I ^ (k : ℕ) * iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I) :=
        iteratedDeriv_line_restriction hR hh (k : ℕ) t₀
      rw [hk1, hk2, hjet k]
  exact eqOn_of_eventuallyEq_line hR hg hh hline

/-- **Local jet separation from a relation with varying coefficients.** -/
theorem eqOn_of_line_jet_eq_implicit_local_timeDep {g h : ℂ → ℂ} (hR : 0 < R) (hn : 0 < n)
    (hg : DifferentiableOn ℂ g (verticalStrip σ R)) (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    {P : ℝ → (Fin (n + 1) → ℂ) → ℂ}
    {P' : ℝ → (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : Set (Fin (n + 1) → ℂ)}
    (hS : Convex ℝ S) {L : (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hdom : C < ‖partialCoeff L (Fin.last n)‖) {t₀ : ℝ}
    (hPd : ∀ᶠ t : ℝ in nhds t₀, ∀ y ∈ S, HasFDerivWithinAt (P t) ((P' t y).restrictScalars ℝ) S y)
    (hbound : ∀ᶠ t : ℝ in nhds t₀, ∀ y ∈ S, ‖P' t y - L‖ ≤ C)
    (hgS : ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hgP : ∀ᶠ t : ℝ in nhds t₀, P t (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    (hhS : ∀ᶠ t : ℝ in nhds t₀, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S)
    (hhP : ∀ᶠ t : ℝ in nhds t₀, P t (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0)
    (hjet : ∀ k : Fin n, iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t₀ : ℂ) * Complex.I)
      = iteratedDeriv (k : ℕ) h ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) :
    Set.EqOn g h (verticalStrip σ R) := by
  classical
  set Good : ℝ → Prop := fun t => ∃ Φt : (Fin n → ℂ) → ℂ,
      LipschitzWith (implicitLipschitzConst n L C) Φt ∧
        ∀ y ∈ S, P t y = 0 → y (Fin.last n) = Φt (fun k : Fin n => y k.castSucc) with hGood
  have hgood : ∀ᶠ t : ℝ in nhds t₀, Good t := by
    filter_upwards [hPd, hbound] with t h1 h2
    exact exists_lipschitz_implicit_const hS h1 hC h2 hdom
  set Φ : ℝ → (Fin n → ℂ) → ℂ := fun t => if h : Good t then h.choose else 0 with hΦdef
  have hΦlip : ∀ᶠ t : ℝ in nhds t₀,
      LipschitzWith (implicitLipschitzConst n L C) (Φ t) := by
    filter_upwards [hgood] with t ht
    rw [hΦdef]
    simp only [dif_pos ht]
    exact ht.choose_spec.1
  have hΦval : ∀ᶠ t : ℝ in nhds t₀, ∀ y ∈ S, P t y = 0 →
      y (Fin.last n) = Φ t (fun k : Fin n => y k.castSucc) := by
    filter_upwards [hgood] with t ht
    rw [hΦdef]
    simp only [dif_pos ht]
    exact ht.choose_spec.2
  have hODE : ∀ (u : ℂ → ℂ),
      (∀ᶠ t : ℝ in nhds t₀, (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S) →
      (∀ᶠ t : ℝ in nhds t₀, P t (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I)) = 0) →
      ∀ᶠ t : ℝ in nhds t₀, iteratedDeriv n u ((σ : ℂ) + (t : ℂ) * Complex.I)
        = Φ t fun k : Fin n => iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    intro u huS huP
    filter_upwards [huS, huP, hΦval] with t hS' hP' hval'
    have hval := hval' _ hS' hP'
    simpa using hval
  exact eqOn_of_line_jet_eq_local_timeDep hR hn hg hh (S := Set.univ)
    (by filter_upwards [hΦlip] with t ht; exact ht.lipschitzOnWith)
    (hODE g hgS hgP) (hODE h hhS hhP)
    (Filter.Eventually.of_forall fun t => Set.mem_univ _)
    (Filter.Eventually.of_forall fun t => Set.mem_univ _) hjet


end GaloisForLFunctions
