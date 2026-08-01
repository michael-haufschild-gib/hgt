import GaloisForLFunctions.HTGeometry.LineJetPolynomialTwist
import GaloisForLFunctions.HTGeometry.ODEJetSeparation
import GaloisForLFunctions.HTGeometry.StripJetSeparation
import GaloisForLFunctions.HTGeometry.StripRelationPropagation
import GaloisForLFunctions.HTGeometry.StripHullSeparation

/-!
# The jet sample separates solutions of one implicit relation

At a jet where the separant does not vanish, an implicit polynomial relation is locally the graph of
a Lipschitz field, so two solutions of the relation whose jets up to the order of the relation agree
at one point of the line satisfy the same explicit equation near that point.  ODE uniqueness then
makes them agree near the point, and the identity theorem propagates the agreement to the strip.
-/

open Filter Topology MvPolynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- The restriction of a function on the strip to the central line. -/
noncomputable def lineFun (σ : ℝ) (g : ℂ → ℂ) : ℝ → ℂ :=
  fun s : ℝ => g ((σ : ℂ) + (s : ℂ) * Complex.I)

theorem snoc_jetVec {n : ℕ} (G : ℝ → ℂ) (t : ℝ) :
    Fin.snoc (jetVec (n := n) G t) (iteratedDeriv n G t)
      = fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) G t := by
  funext k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp
  · simp [jetVec]

/-- **Solutions with equal jets at a regular point of the line coincide on the strip.** -/
theorem eqOn_of_jet_eq_of_separant {σ R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 0 < n)
    {g h : ℂ → ℂ} (hg : DifferentiableOn ℂ g (verticalStrip σ R))
    (hh : DifferentiableOn ℂ h (verticalStrip σ R))
    (Q : MvPolynomial (Fin (n + 1)) ℂ) (t₀ : ℝ)
    (hgQ : ∀ t : ℝ, MvPolynomial.eval
      (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (lineFun σ g) t) Q = 0)
    (hhQ : ∀ t : ℝ, MvPolynomial.eval
      (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (lineFun σ h) t) Q = 0)
    (hjet : ∀ k : Fin (n + 1),
      iteratedDeriv (k : ℕ) (lineFun σ g) t₀ = iteratedDeriv (k : ℕ) (lineFun σ h) t₀)
    (hsep : deriv (fun u : ℂ => MvPolynomial.eval
        (Fin.snoc (jetVec (n := n) (lineFun σ g) t₀) u) Q)
      (iteratedDeriv n (lineFun σ g) t₀) ≠ 0) :
    Set.EqOn g h (verticalStrip σ R) := by
  classical
  set G : ℝ → ℂ := lineFun σ g with hG
  set H : ℝ → ℂ := lineFun σ h with hH
  set w₀ : Fin n → ℂ := jetVec (n := n) G t₀ with hw₀
  set u₀ : ℂ := iteratedDeriv n G t₀ with hu₀
  -- the derivatives of the line restrictions
  have hGderiv : ∀ i : ℕ, ∀ t : ℝ, HasDerivAt (iteratedDeriv i G) (iteratedDeriv (i + 1) G t) t :=
    fun i t => hasDerivAt_iteratedDeriv_line hR hg i t
  have hHderiv : ∀ i : ℕ, ∀ t : ℝ, HasDerivAt (iteratedDeriv i H) (iteratedDeriv (i + 1) H t) t :=
    fun i t => hasDerivAt_iteratedDeriv_line hR hh i t
  -- the relation at the base jet
  have hP : MvPolynomial.eval (Fin.snoc w₀ u₀) Q = 0 := by
    rw [hw₀, hu₀, snoc_jetVec]
    exact hgQ t₀
  obtain ⟨Φ, K, S, hS, hlip, hΦbase, hgraph, huniq⟩ := exists_lipschitz_implicit_of_polynomial Q w₀ u₀ hP hsep
  -- the jet curves are continuous
  have hjetcontG : ContinuousAt
      (fun t : ℝ => ((jetVec (n := n) G t, iteratedDeriv n G t) : (Fin n → ℂ) × ℂ)) t₀ := by
    refine ContinuousAt.prodMk ?_ ((hGderiv n t₀).continuousAt)
    refine continuousAt_pi.mpr fun i => ?_
    exact (hGderiv (i : ℕ) t₀).continuousAt
  have hjetcontH : ContinuousAt
      (fun t : ℝ => ((jetVec (n := n) H t, iteratedDeriv n H t) : (Fin n → ℂ) × ℂ)) t₀ := by
    refine ContinuousAt.prodMk ?_ ((hHderiv n t₀).continuousAt)
    refine continuousAt_pi.mpr fun i => ?_
    exact (hHderiv (i : ℕ) t₀).continuousAt
  have hbaseH : ((jetVec (n := n) H t₀, iteratedDeriv n H t₀) : (Fin n → ℂ) × ℂ)
      = (w₀, u₀) := by
    refine Prod.ext ?_ ?_
    · funext i
      exact (hjet i.castSucc).symm
    · exact (hjet (Fin.last n)).symm
  -- the explicit form of the equation near `t₀`
  have hgODE : ∀ᶠ t in nhds t₀, iteratedDeriv n G t = Φ (jetVec (n := n) G t) := by
    have htend := hjetcontG.tendsto
    filter_upwards [htend.eventually huniq] with t ht
    refine ht ?_
    rw [snoc_jetVec]
    exact hgQ t
  have hhODE : ∀ᶠ t in nhds t₀, iteratedDeriv n H t = Φ (jetVec (n := n) H t) := by
    have htend := hjetcontH.tendsto
    rw [hbaseH] at htend
    filter_upwards [htend.eventually huniq] with t ht
    refine ht ?_
    rw [snoc_jetVec]
    exact hhQ t
  have hgS : ∀ᶠ t in nhds t₀, jetVec (n := n) G t ∈ S := by
    have htend := hjetcontG.tendsto
    have hfst : Filter.Tendsto (fun t : ℝ => jetVec (n := n) G t) (nhds t₀) (nhds w₀) :=
      (continuous_fst.continuousAt.tendsto).comp htend
    exact hfst.eventually_mem hS
  have hhS : ∀ᶠ t in nhds t₀, jetVec (n := n) H t ∈ S := by
    have htend := hjetcontH.tendsto
    rw [hbaseH] at htend
    have hfst : Filter.Tendsto (fun t : ℝ => jetVec (n := n) H t) (nhds t₀) (nhds w₀) :=
      (continuous_fst.continuousAt.tendsto).comp htend
    exact hfst.eventually_mem hS
  have hjetEq : jetVec (n := n) G t₀ = jetVec (n := n) H t₀ := by
    funext i
    exact hjet i.castSucc
  have hlineEq : G =ᶠ[nhds t₀] H :=
    eventuallyEq_of_jetVec_eq_at hn hlip (fun i _ t => hGderiv i t) hgODE hgS
      (fun i _ t => hHderiv i t) hhODE hhS hjetEq
  exact eqOn_of_eventuallyEq_line hR hg hh hlineEq

/-- A relation transported to another representative of the same germ on the substrip. -/
theorem relation_congr_of_eqOn {σ r : ℝ} {n : ℕ} {g g' : ℂ → ℂ} (Q : MvPolynomial (Fin n) ℂ)
    (hEq : ∀ z ∈ verticalStrip σ r, g z = g' z)
    (hrel : ∀ z ∈ verticalStrip σ r,
      MvPolynomial.eval (fun k : Fin n => iteratedDeriv (k : ℕ) g z) Q = 0)
    {z : ℂ} (hz : z ∈ verticalStrip σ r) :
    MvPolynomial.eval (fun k : Fin n => iteratedDeriv (k : ℕ) g' z) Q = 0 := by
  have hnhds : g =ᶠ[nhds z] g' :=
    Filter.eventually_of_mem ((isOpen_verticalStrip σ r).mem_nhds hz) hEq
  have hjets : (fun k : Fin n => iteratedDeriv (k : ℕ) g' z)
      = fun k : Fin n => iteratedDeriv (k : ℕ) g z := by
    funext k
    exact (hnhds.iteratedDeriv_eq (k : ℕ)).symm
  rw [hjets]
  exact hrel z hz

/-- **The jet sample separates carrier points.**  Two points of the strip carrier whose
representatives have equal jets up to the order of the relation at one point of the line, at a jet
where the separant does not vanish, are equal. -/
theorem hull_eq_of_jet_sample_eq {σ R r : ℝ} (hr0 : 0 < r) (hr : r < R) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    {n : ℕ} (hn : 0 < n) (P : MvPolynomial (Fin (n + 1)) ℂ)
    (hrel : ∀ z ∈ verticalStrip σ R,
      MvPolynomial.eval (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F z) P = 0)
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I))
    {x y : BohrHull Gb} {gx gy : ℂ → ℂ} (t₀ : ℝ)
    (hgx : DifferentiableOn ℂ gx (verticalStrip σ r))
    (hgxv : ∀ z : closedStrip σ r, gx (z : ℂ) = bohrEval Gb x z)
    (hgy : DifferentiableOn ℂ gy (verticalStrip σ r))
    (hgyv : ∀ z : closedStrip σ r, gy (z : ℂ) = bohrEval Gb y z)
    (hjet : ∀ k : Fin (n + 1),
      iteratedDeriv (k : ℕ) (lineFun σ gx) t₀ = iteratedDeriv (k : ℕ) (lineFun σ gy) t₀)
    (hsep : deriv (fun u : ℂ => MvPolynomial.eval
        (Fin.snoc (jetVec (n := n) (lineFun σ gx) t₀) u)
        (scaleVars (fun k : Fin (n + 1) => (Complex.I ^ (k : ℕ))⁻¹) P))
      (iteratedDeriv n (lineFun σ gx) t₀) ≠ 0) :
    x = y := by
  classical
  have hPcont : Continuous
      (fun v : Fin (n + 1) → ℂ => MvPolynomial.eval v P) := by
    have hana : AnalyticOnNhd ℂ (fun v : Fin (n + 1) → ℂ => MvPolynomial.eval v P) Set.univ :=
      AnalyticOnNhd.eval_mvPolynomial P
    rw [← continuousOn_univ]
    exact hana.continuousOn
  have hsub : ∀ z : closedStrip σ r, (z : ℂ) ∈ closedStrip σ r := fun z => z.2
  -- the relations for the two representatives
  have hrelx : ∀ z ∈ verticalStrip σ r,
      MvPolynomial.eval (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) gx z) P = 0 := by
    obtain ⟨g, hgd, hgv, hgrel⟩ := exists_solution_of_hull hr hF hPcont hrel hGb x
    have hEq : ∀ w ∈ verticalStrip σ r, g w = gx w := by
      intro w hw
      have hw' : w ∈ closedStrip σ r := by
        show |w.re - σ| ≤ r
        exact le_of_lt hw
      rw [hgv ⟨w, hw'⟩, ← hgxv ⟨w, hw'⟩]
    intro z hz
    exact relation_congr_of_eqOn P hEq hgrel hz
  have hrely : ∀ z ∈ verticalStrip σ r,
      MvPolynomial.eval (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) gy z) P = 0 := by
    obtain ⟨g, hgd, hgv, hgrel⟩ := exists_solution_of_hull hr hF hPcont hrel hGb y
    have hEq : ∀ w ∈ verticalStrip σ r, g w = gy w := by
      intro w hw
      have hw' : w ∈ closedStrip σ r := by
        show |w.re - σ| ≤ r
        exact le_of_lt hw
      rw [hgv ⟨w, hw'⟩, ← hgyv ⟨w, hw'⟩]
    intro z hz
    exact relation_congr_of_eqOn P hEq hgrel hz
  -- the line form of the relations
  have hlinex : ∀ t : ℝ, MvPolynomial.eval
      (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (lineFun σ gx) t)
      (scaleVars (fun k : Fin (n + 1) => (Complex.I ^ (k : ℕ))⁻¹) P) = 0 :=
    fun t => eval_scaleVars_line hr0 hgx P hrelx t
  have hliney : ∀ t : ℝ, MvPolynomial.eval
      (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (lineFun σ gy) t)
      (scaleVars (fun k : Fin (n + 1) => (Complex.I ^ (k : ℕ))⁻¹) P) = 0 :=
    fun t => eval_scaleVars_line hr0 hgy P hrely t
  -- the two representatives agree on the substrip
  have hEqOn := eqOn_of_jet_eq_of_separant hr0 hn hgx hgy
    (scaleVars (fun k : Fin (n + 1) => (Complex.I ^ (k : ℕ))⁻¹) P) t₀ hlinex hliney hjet hsep
  -- hence the carrier points agree on the line, hence are equal
  refine hull_eq_of_line_eq hr0 hr hF hGb ?_
  intro t hz
  have hmem : ((σ : ℂ) + (t : ℂ) * Complex.I) ∈ verticalStrip σ r :=
    mem_verticalStrip_line hr0 σ t
  rw [← hgxv ⟨_, hz⟩, ← hgyv ⟨_, hz⟩]
  exact hEqOn hmem

end GaloisForLFunctions
