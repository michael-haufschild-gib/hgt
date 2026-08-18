import GaloisForLFunctions.HTGeometry.ImplicitCarrierRegularity
import GaloisForLFunctions.HTGeometry.DivisorPairing

/-!
# The divisor half of the relative frequency law

No point of the joint carrier has a representative whose solution component vanishes identically:
such a point would force the solution itself to vanish.  The zero divisor of that component, paired
with a test function, is therefore a continuous observable of the carrier, and every frequency of a
continuous observable is a frequency of the carrier.

Relative rank is monotone along an inclusion of subgroups, so the divisor observable inherits the
bound of the solution: it adds at most `2n` rationally independent frequencies to the coefficients.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ r ρ : ℝ} {N n : ℕ}

/-- **Relative rank is monotone.**  A subgroup between the base and the ambient group has relative
rank at most that of the ambient group. -/
theorem rank_quotient_le_of_le {Γa H G : AddSubgroup ℝ} (hHG : H ≤ G) :
    Module.rank ℤ (H ⧸ (Γa.addSubgroupOf H)) ≤ Module.rank ℤ (G ⧸ (Γa.addSubgroupOf G)) := by
  classical
  set π : H →+ (G ⧸ (Γa.addSubgroupOf G)) :=
    (QuotientAddGroup.mk' (Γa.addSubgroupOf G)).comp (AddSubgroup.inclusion hHG) with hπ
  have hker : ∀ x : H, π x = 0 → x ∈ Γa.addSubgroupOf H := by
    intro x hx
    have h1 : (AddSubgroup.inclusion hHG x) ∈ Γa.addSubgroupOf G :=
      (QuotientAddGroup.eq_zero_iff _).mp hx
    rw [AddSubgroup.mem_addSubgroupOf] at h1 ⊢
    exact h1
  set φ : (H ⧸ (Γa.addSubgroupOf H)) →+ (G ⧸ (Γa.addSubgroupOf G)) :=
    QuotientAddGroup.lift (Γa.addSubgroupOf H) π (by
      intro x hx
      have hxG : (AddSubgroup.inclusion hHG x) ∈ Γa.addSubgroupOf G := by
        rw [AddSubgroup.mem_addSubgroupOf] at hx ⊢
        exact hx
      exact (QuotientAddGroup.eq_zero_iff _).mpr hxG) with hφ
  refine LinearMap.rank_le_of_injective φ.toIntLinearMap ?_
  rw [injective_iff_map_eq_zero]
  intro a
  refine QuotientAddGroup.induction_on a fun x hx => ?_
  have hπ0 : π x = 0 := hx
  exact (QuotientAddGroup.eq_zero_iff _).mpr (hker x hπ0)

/-- **No representative has a vanishing solution component.** -/
theorem not_eventually_rep_snd_eq_zero (hr : 0 < r) (hρ : 0 < ρ)
    {p : ℝ →ᵇ ((Fin N → ℂ) × ℂ)} (hpne : ∃ s : ℝ, (p s).2 ≠ 0)
    {rep : BohrHull p → (ℂ → ((Fin N → ℂ) × ℂ))}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepline : ∀ (x : BohrHull p) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval p (x + bohrIota p t))
    (x : BohrHull p) (z : ℂ) (hz : z ∈ verticalStrip σ (r + ρ)) :
    ¬ (∀ᶠ w in nhds z, (rep x w).2 = 0) := by
  intro hcon
  have hrρ0 : 0 < r + ρ := by linarith
  have hd2 : DifferentiableOn ℂ (fun w => (rep x w).2) (verticalStrip σ (r + ρ)) :=
    (ContinuousLinearMap.snd ℂ (Fin N → ℂ) ℂ).differentiable.comp_differentiableOn (hrepdiff x)
  have han : AnalyticOnNhd ℂ (fun w => (rep x w).2) (verticalStrip σ (r + ρ)) :=
    hd2.analyticOnNhd (isOpen_verticalStrip σ (r + ρ))
  have hpre : IsPreconnected (verticalStrip σ (r + ρ)) :=
    (convex_verticalStrip σ (r + ρ)).isPreconnected
  have hzero : Set.EqOn (fun w => (rep x w).2) 0 (verticalStrip σ (r + ρ)) :=
    han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hz hcon
  have hline : ∀ t : ℝ, (bohrEval p (x + bohrIota p t)).2 = 0 := by
    intro t
    rw [← hrepline x t]
    exact hzero (mem_verticalStrip_line hrρ0 σ t)
  have hall : ∀ y : BohrHull p, (bohrEval p y).2 = 0 := by
    intro y
    refine congrFun (Continuous.ext_on (denseRange_bohrIota_add p x)
      (continuous_snd.comp (continuous_bohrEval p)) continuous_const ?_) y
    rintro w ⟨t, rfl⟩
    exact hline t
  obtain ⟨s, hs⟩ := hpne
  refine hs ?_
  have := hall (bohrIota p s)
  rwa [bohrEval_bohrIota] at this

/-- **The divisor of the solution component is a continuous observable of the joint carrier.** -/
theorem continuous_divisorPairing_rep_snd (hr : 0 < r) (hρ : 0 < ρ)
    {p : ℝ →ᵇ ((Fin N → ℂ) × ℂ)} (hpne : ∃ s : ℝ, (p s).2 ≠ 0)
    {Gb : ℝ →ᵇ ((closedStrip σ (r + ρ)) →ᵇ ((Fin N → ℂ) × ℂ))}
    {ν : BohrHull p → BohrHull Gb} (hν : Continuous ν)
    {rep : BohrHull p → (ℂ → ((Fin N → ℂ) × ℂ))}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepval : ∀ (x : BohrHull p) (z : closedStrip σ (r + ρ)),
      rep x (z : ℂ) = bohrEval Gb (ν x) z)
    (hrepline : ∀ (x : BohrHull p) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval p (x + bohrIota p t))
    {φ : ℂ → ℂ} (hφ : Continuous φ) (hKc : IsCompact (tsupport φ))
    (hKU : tsupport φ ⊆ verticalStrip σ (r + ρ)) :
    Continuous (fun x : BohrHull p =>
      HTGeometry.divisorPairing (fun z => (rep x z).2) φ) := by
  have hrρ0 : 0 < r + ρ := by linarith
  have hd2 : ∀ x : BohrHull p,
      DifferentiableOn ℂ (fun z => (rep x z).2) (verticalStrip σ (r + ρ)) := fun x =>
    (ContinuousLinearMap.snd ℂ (Fin N → ℂ) ℂ).differentiable.comp_differentiableOn (hrepdiff x)
  have hEcont : Continuous fun x : BohrHull p => bohrEval Gb (ν x) :=
    (continuous_bohrEval Gb).comp hν
  refine continuous_iff_continuousAt.mpr fun x₀ => ?_
  refine HTGeometry.continuousAt_divisorPairing (isOpen_verticalStrip σ (r + ρ)) hd2
    (fun z hz => not_eventually_rep_snd_eq_zero hr hρ hpne hrepdiff hrepline x₀ z hz) ?_
    hφ hKc hKU
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
  have hpt : ‖(rep x z).2 - (rep x₀ z).2‖ ≤ ‖rep x z - rep x₀ z‖ := by
    have := norm_snd_le (rep x z - rep x₀ z)
    simpa using this
  refine le_trans hpt ?_
  rw [h1, h2, ← dist_eq_norm]
  exact le_trans (BoundedContinuousFunction.dist_coe_le_dist _) hx


/-- **The divisor half of the relative frequency law.**  The zero divisor of the solution, tested
against a continuous test function of compact support inside the substrip, adds at most `2n`
rationally independent frequencies to the frequency group of the coefficients. -/
theorem rank_quotient_divisor_le_of_implicit_strip_separant {R : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    {A : Fin N → ℂ → ℂ} {e : Fin N → Fin (n + 1) → ℕ}
    {Fv : ℂ → ((Fin N → ℂ) × ℂ)}
    (hFdiff : DifferentiableOn ℂ Fv (verticalStrip σ R))
    (hFap : IsStripAlmostPeriodic Fv σ R)
    (hFcoef : ∀ z ∈ verticalStrip σ (r + ρ), (Fv z).1 = fun i => A i z)
    (hAcont : ∀ i : Fin N, ContinuousOn (fun s : ℝ => A i ((σ : ℂ) + (s : ℂ) * Complex.I))
      Set.univ)
    {p : ℝ →ᵇ ((Fin N → ℂ) × ℂ)}
    (hp : ∀ t : ℝ, p t = Fv ((σ : ℂ) + (t : ℂ) * Complex.I))
    (hpne : ∃ s : ℝ, (p s).2 ≠ 0)
    {q : ℝ →ᵇ (Fin N → ℂ)} (hq : ∀ t : ℝ, q t = (p t).1)
    (hn : 0 < n)
    (hrel : ∀ z ∈ verticalStrip σ R,
      HTGeometry.coeffJetRelation e (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) Fv z) = 0)
    (hsep : ∃ t : ℝ, HTGeometry.jointSeparant e (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) Fv ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0)
    {φ : ℂ → ℂ} (hφ : Continuous φ) (hKc : IsCompact (tsupport φ))
    (hKU : tsupport φ ⊆ verticalStrip σ (r + ρ))
    {H : AddSubgroup ℝ}
    (hH : H = bohrHullFrequencies q ⊔ AddSubgroup.closure (bohrSpectrum
      (fun t : ℝ => HTGeometry.divisorPairing
        (fun z => (Fv (z + (t : ℂ) * Complex.I)).2) φ))) :
    Module.rank ℤ (H ⧸ ((bohrHullFrequencies q).addSubgroupOf H))
      ≤ ((n * 2 : ℕ) : Cardinal) := by
  classical
  subst hH
  letI : MeasurableSpace (BohrHull p) := borel _
  haveI : BorelSpace (BohrHull p) := ⟨rfl⟩
  letI : MeasurableSpace (BohrHull q) := borel _
  haveI : BorelSpace (BohrHull q) := ⟨rfl⟩
  have hR : 0 < R := by linarith
  have hrρ0 : 0 < r + ρ := by linarith
  have hstripsub : verticalStrip σ (r + ρ) ⊆ verticalStrip σ R := by
    intro z hz
    show |z.re - σ| < R
    have : |z.re - σ| < r + ρ := hz
    linarith
  have hpline : (fun x : ℝ => p x)
      = fun t : ℝ => Fv ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    funext x
    exact hp x
  have hpap : HTGeometry.IsBohrAlmostPeriodic (fun x : ℝ => p x) := by
    rw [hpline]
    exact isBohrAlmostPeriodic_line hR hFap
  have hqline : (fun x : ℝ => q x) = fun t : ℝ => ((p t).1) := by
    funext x
    exact hq x
  have hqap : HTGeometry.IsBohrAlmostPeriodic (fun x : ℝ => q x) := by
    rw [hqline]
    exact isBohrAlmostPeriodic_fst hpap
  have hpu : UniformContinuous (fun x : ℝ => p x) :=
    uniformContinuous_of_isBohrAlmostPeriodic p.continuous hpap
  have hptb : HasTotallyBoundedOrbit (fun x : ℝ => p x) :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic p.continuous hpap
  obtain ⟨Gb, ν, rep, hνcont, hrepdiff, hrepval, hrepline, hrelrep⟩ :=
    exists_carrier_representatives hr hρ hrρ hFdiff hFap hp hpu
      (HTGeometry.continuous_coeffJetRelation e) hrel
  -- the observable
  set Ψ : BohrHull p → ℂ := fun x =>
    HTGeometry.divisorPairing (fun z => (rep x z).2) φ with hΨdef
  have hΨcont : Continuous Ψ :=
    continuous_divisorPairing_rep_snd hr hρ hpne hνcont hrepdiff hrepval hrepline hφ hKc hKU
  -- along the line it is the divisor of the vertical translates of the solution
  have hrep0 : Set.EqOn (rep 0) Fv (verticalStrip σ (r + ρ)) := by
    refine eqOn_of_eqOn_line hrρ0 (hrepdiff 0) (hFdiff.mono hstripsub) fun s => ?_
    rw [hrepline 0 s, zero_add, bohrEval_bohrIota, hp s]
  have hΨline : (fun t : ℝ => HTGeometry.divisorPairing
      (fun z => (Fv (z + (t : ℂ) * Complex.I)).2) φ) = fun t : ℝ => Ψ (bohrIota p t) := by
    funext t
    refine (HTGeometry.divisorPairing_congr (isOpen_verticalStrip σ (r + ρ)) ?_ hKU).symm
    intro z hz
    have htrans : Set.EqOn (rep (0 + bohrIota p t))
        (fun w => rep 0 (w + (t : ℂ) * Complex.I)) (verticalStrip σ (r + ρ)) :=
      rep_translate_eqOn hrρ0 hrepdiff hrepline 0 t
    have h1 : rep (bohrIota p t) z = rep 0 (z + (t : ℂ) * Complex.I) := by
      rw [← zero_add (bohrIota p t)]
      exact htrans hz
    show (rep (bohrIota p t) z).2 = (Fv (z + (t : ℂ) * Complex.I)).2
    rw [h1, hrep0 (mem_verticalStrip_add_I hz t)]
  rw [hΨline]
  -- the observable's frequencies live in the carrier's
  have hobs : AddSubgroup.closure (bohrSpectrum (fun t : ℝ => Ψ (bohrIota p t)))
      ≤ bohrHullFrequencies p :=
    AddSubgroup.closure_le _ |>.mpr
      (bohrSpectrum_observable_subset_bohrHullFrequencies hpu hptb Ψ hΨcont)
  have hqp : bohrHullFrequencies q ≤ bohrHullFrequencies p := by
    intro μ hμ
    exact isBohrHullFrequency_of_uniformContinuous_compare
      (uniformContinuous_bohrLine_fst p q hq) hμ
  refine le_trans (rank_quotient_le_of_le (sup_le hqp hobs)) ?_
  exact rank_quotient_le_of_implicit_strip_separant_closed hr hρ hrρ hFdiff hFap hFcoef hAcont
    hp hq hn hrel hsep


end GaloisForLFunctions
