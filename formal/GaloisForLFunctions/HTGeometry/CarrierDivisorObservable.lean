import GaloisForLFunctions.HTGeometry.AutonomousCarrierRegularity
import GaloisForLFunctions.HTGeometry.DivisorPairing

/-!
# The zero divisor is a continuous observable of the carrier

No point of the carrier of a nonzero almost-periodic function has a representative vanishing
identically: such a representative would vanish on the central line, hence the carrier evaluation
would vanish on a dense set of the carrier, hence everywhere, hence the function itself would be
zero.  The representatives depend uniformly continuously on the carrier point, so the zero divisor
paired with a test function is a continuous observable of the carrier.

Along the line that observable is the divisor of the vertical translates of the function, so the
frequency law for continuous observables applies to it: the zero divisor of a strip almost-periodic
solution of an autonomous algebraic differential equation has the same finite frequency rank as the
solution.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ r ρ : ℝ} {n : ℕ}

/-- **No carrier representative vanishes identically.** -/
theorem not_eventually_rep_eq_zero (hr : 0 < r) (hρ : 0 < ρ)
    {f : ℝ →ᵇ ℂ} (hfne : ∃ s : ℝ, f s ≠ 0)
    {rep : BohrHull f → (ℂ → ℂ)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepline : ∀ (x : BohrHull f) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t))
    (x : BohrHull f) (z : ℂ) (hz : z ∈ verticalStrip σ (r + ρ)) :
    ¬ (∀ᶠ w in nhds z, rep x w = 0) := by
  intro hcon
  have hrρ : 0 < r + ρ := by linarith
  have han : AnalyticOnNhd ℂ (rep x) (verticalStrip σ (r + ρ)) :=
    (hrepdiff x).analyticOnNhd (isOpen_verticalStrip σ (r + ρ))
  have hpre : IsPreconnected (verticalStrip σ (r + ρ)) :=
    (convex_verticalStrip σ (r + ρ)).isPreconnected
  have hzero : Set.EqOn (rep x) 0 (verticalStrip σ (r + ρ)) :=
    han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hz hcon
  -- the carrier evaluation vanishes along a dense orbit, hence everywhere
  have hline : ∀ t : ℝ, bohrEval f (x + bohrIota f t) = 0 := by
    intro t
    rw [← hrepline x t]
    exact hzero (mem_verticalStrip_line hrρ σ t)
  have hall : ∀ y : BohrHull f, bohrEval f y = 0 := by
    intro y
    refine congrFun (Continuous.ext_on (denseRange_bohrIota_add f x)
      (continuous_bohrEval f) continuous_const ?_) y
    rintro w ⟨t, rfl⟩
    exact hline t
  obtain ⟨s, hs⟩ := hfne
  exact hs (by rw [← bohrEval_bohrIota f s]; exact hall _)

/-- **The divisor pairing is a continuous observable of the carrier.** -/
theorem continuous_divisorPairing_rep (hr : 0 < r) (hρ : 0 < ρ)
    {f : ℝ →ᵇ ℂ} (hfne : ∃ s : ℝ, f s ≠ 0)
    {Gb : ℝ →ᵇ ((closedStrip σ (r + ρ)) →ᵇ ℂ)} {ν : BohrHull f → BohrHull Gb}
    (hν : Continuous ν) {rep : BohrHull f → (ℂ → ℂ)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepval : ∀ (x : BohrHull f) (z : closedStrip σ (r + ρ)),
      rep x (z : ℂ) = bohrEval Gb (ν x) z)
    (hrepline : ∀ (x : BohrHull f) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t))
    {φ : ℂ → ℂ} (hφ : Continuous φ) (hKc : IsCompact (tsupport φ))
    (hKU : tsupport φ ⊆ verticalStrip σ (r + ρ)) :
    Continuous (fun x : BohrHull f => HTGeometry.divisorPairing (rep x) φ) := by
  have hrρ : 0 < r + ρ := by linarith
  have hEcont : Continuous fun x : BohrHull f => bohrEval Gb (ν x) :=
    (continuous_bohrEval Gb).comp hν
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  refine HTGeometry.continuousAt_divisorPairing (isOpen_verticalStrip σ (r + ρ)) hrepdiff
    (fun z hz => not_eventually_rep_eq_zero hr hρ hfne hrepdiff hrepline x₀ z hz) ?_ hφ hKc hKU
  intro ε hε
  have hev : ∀ᶠ x in nhds x₀, dist (bohrEval Gb (ν x)) (bohrEval Gb (ν x₀)) ≤ ε := by
    have := (hEcont.continuousAt (x := x₀)) (Metric.ball_mem_nhds _ hε)
    filter_upwards [this] with x hx
    exact le_of_lt (Metric.mem_ball.mp hx)
  filter_upwards [hev] with x hx
  intro z hz
  have hzc : z ∈ closedStrip σ (r + ρ) := by
    show |z.re - σ| ≤ r + ρ
    exact le_of_lt hz
  have h1 : rep x z = bohrEval Gb (ν x) ⟨z, hzc⟩ := hrepval x ⟨z, hzc⟩
  have h2 : rep x₀ z = bohrEval Gb (ν x₀) ⟨z, hzc⟩ := hrepval x₀ ⟨z, hzc⟩
  rw [h1, h2, ← dist_eq_norm]
  exact le_trans (BoundedContinuousFunction.dist_coe_le_dist _) hx

/-- The representative of a translated carrier origin is the translate of the function. -/
theorem eqOn_rep_bohrIota (hr : 0 < r) (hρ : 0 < ρ)
    {F : ℂ → ℂ} {f : ℝ →ᵇ ℂ}
    (hF : DifferentiableOn ℂ F (verticalStrip σ (r + ρ)))
    (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    {rep : BohrHull f → (ℂ → ℂ)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepline : ∀ (x : BohrHull f) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t))
    (t : ℝ) :
    Set.EqOn (rep (bohrIota f t)) (fun z => F (z + (t : ℂ) * Complex.I))
      (verticalStrip σ (r + ρ)) := by
  have hrρ : 0 < r + ρ := by linarith
  have hzero : Set.EqOn (rep 0) F (verticalStrip σ (r + ρ)) := by
    refine eqOn_of_eqOn_line hrρ (hrepdiff 0) hF fun s => ?_
    rw [hrepline 0 s, zero_add, bohrEval_bohrIota, hf s]
  have htrans : Set.EqOn (rep (0 + bohrIota f t))
      (fun z => rep 0 (z + (t : ℂ) * Complex.I)) (verticalStrip σ (r + ρ)) :=
    rep_translate_eqOn hrρ hrepdiff hrepline 0 t
  intro z hz
  have h1 : rep (bohrIota f t) z = rep 0 (z + (t : ℂ) * Complex.I) := by
    rw [← zero_add (bohrIota f t)]
    exact htrans hz
  rw [h1]
  exact hzero (mem_verticalStrip_add_I hz t)

/-- **The divisor frequency law.**  The zero divisor of a holomorphic uniformly almost-periodic
solution of a nonzero autonomous algebraic differential equation of exact order `n` on a strip has,
against every continuous test function of compact support inside the strip, frequency group of
rational rank at most `2n`.

The divisor pairing is a continuous observable of the carrier, and along the line it is the divisor
of the vertical translates of the solution, so the observable form of the finite-frequency law
applies verbatim. -/
theorem rank_bohrSpectrum_divisor_le_of_stripAnnihilator {F : ℂ → ℂ} {R : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfne : ∃ s : ℝ, f s ≠ 0)
    (hn : 0 < n)
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ StripAnnihilator σ R F n P)
    (horder : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 → StripAnnihilator σ R F n Q →
      Q.natDegree ≠ 0)
    {φ : ℂ → ℂ} (hφ : Continuous φ) (hKc : IsCompact (tsupport φ))
    (hKU : tsupport φ ⊆ verticalStrip σ (r + ρ)) :
    Module.rank ℤ (AddSubgroup.closure (bohrSpectrum
      (fun t : ℝ => HTGeometry.divisorPairing (fun z => F (z + (t : ℂ) * Complex.I)) φ)))
      ≤ ((n * 2 : ℕ) : Cardinal) := by
  classical
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  have hR : 0 < R := by linarith
  have hstripsub : verticalStrip σ (r + ρ) ⊆ verticalStrip σ R := by
    intro z hz
    show |z.re - σ| < R
    have : |z.re - σ| < r + ρ := hz
    linarith
  have hfline : (fun x : ℝ => f x) = fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    funext x
    exact hf x
  have hfap : HTGeometry.IsBohrAlmostPeriodic (fun x : ℝ => f x) := by
    rw [hfline]
    exact isBohrAlmostPeriodic_line hR hap
  have hfu : UniformContinuous (fun x : ℝ => f x) :=
    uniformContinuous_of_isBohrAlmostPeriodic f.continuous hfap
  have hftb : HasTotallyBoundedOrbit (fun x : ℝ => f x) :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic f.continuous hfap
  -- a minimal equation, and the carrier representatives it produces
  obtain ⟨Pp, hPp0, hPpdeg, hPpann, hPpsep⟩ :=
    exists_minimal_strip_separant_line hR hF hex horder
  obtain ⟨Gb, ν, rep, hνcont, hrepdiff, hrepval, hrepline, hrelrep⟩ :=
    exists_carrier_representatives hr hρ hrρ hF hap hf hfu
      (contDiff_jetRelation n Pp).continuous hPpann
  -- the divisor pairing as a continuous observable
  set Ψ : BohrHull f → ℂ := fun x => HTGeometry.divisorPairing (rep x) φ with hΨdef
  have hΨcont : Continuous Ψ :=
    continuous_divisorPairing_rep hr hρ hfne hνcont hrepdiff hrepval hrepline hφ hKc hKU
  have hΨline : (fun t : ℝ =>
      HTGeometry.divisorPairing (fun z => F (z + (t : ℂ) * Complex.I)) φ)
      = fun t : ℝ => Ψ (bohrIota f t) := by
    funext t
    refine (HTGeometry.divisorPairing_congr (isOpen_verticalStrip σ (r + ρ))
      (eqOn_rep_bohrIota hr hρ (hF.mono hstripsub) hf hrepdiff hrepline t) hKU).symm
  rw [hΨline]
  have hsub : AddSubgroup.closure (bohrSpectrum (fun t : ℝ => Ψ (bohrIota f t)))
      ≤ bohrHullFrequencies f :=
    AddSubgroup.closure_le _ |>.mpr
      (bohrSpectrum_observable_subset_bohrHullFrequencies hfu hftb Ψ hΨcont)
  refine le_trans (rank_le_of_addSubgroup_le hsub) ?_
  exact rank_bohrHullFrequencies_le_of_stripAnnihilator hr hρ hrρ hF hap hf hn hex horder

end GaloisForLFunctions
