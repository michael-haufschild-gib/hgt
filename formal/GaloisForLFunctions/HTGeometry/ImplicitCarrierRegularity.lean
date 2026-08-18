import GaloisForLFunctions.HTGeometry.ImplicitStripFrequencyLaw
import GaloisForLFunctions.HTGeometry.JointSeparant
import GaloisForLFunctions.HTGeometry.MinimalFlowJetVanishing
import GaloisForLFunctions.HTGeometry.CarrierTranslationEquivariance

/-!
# Regularity propagates to every point of the joint carrier

The separant of the equation, read along the jet of a carrier representative at a real time, is a
continuous family of functionals on the carrier, equivariant for the flow of the line.  Its common
vanishing set is therefore closed and invariant, and since every orbit of the line is dense in the
carrier it is either empty or everything.  It is not everything, because at the origin the
representative has the jets of the solution itself, where the separant is not identically zero.

So no carrier point is everywhere singular — the card's minimality step — and the dominant convex
regions the chart argument needs can be built one per regular jet, valid at every nearby time.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ r ρ : ℝ} {N n : ℕ}

/-- **Regularity at one time for every point of the joint carrier.** -/
theorem exists_joint_regular_time (hr : 0 < r) (hρ : 0 < ρ)
    {p : ℝ →ᵇ ((Fin N → ℂ) × ℂ)}
    {Gb : ℝ →ᵇ ((closedStrip σ (r + ρ)) →ᵇ ((Fin N → ℂ) × ℂ))}
    {ν : BohrHull p → BohrHull Gb} (hν : Continuous ν)
    {rep : BohrHull p → (ℂ → ((Fin N → ℂ) × ℂ))}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepval : ∀ (x : BohrHull p) (z : closedStrip σ (r + ρ)),
      rep x (z : ℂ) = bohrEval Gb (ν x) z)
    (hrepline : ∀ (x : BohrHull p) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval p (x + bohrIota p t))
    (e : Fin N → Fin (n + 1) → ℕ)
    (hbase : ∃ t : ℝ, HTGeometry.jointSeparant e (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep 0) ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0)
    (x : BohrHull p) :
    ∃ t : ℝ, HTGeometry.jointSeparant e (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
  have hrρ : r < r + ρ := by linarith
  have hrρ0 : 0 < r + ρ := by linarith
  set Φ : ℝ → BohrHull p → ℂ := fun t y => HTGeometry.jointSeparant e
    (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (rep y) ((σ : ℂ) + (t : ℂ) * Complex.I)) with hΦ
  have hcont : ∀ t : ℝ, Continuous (Φ t) := by
    intro t
    refine (HTGeometry.continuous_jointSeparant e).comp (continuous_pi fun k => ?_)
    exact continuous_jet_of_representatives hρ hr hrρ hν hrepdiff hrepval (k : ℕ) t
  have hequiv : ∀ (s : ℝ) (t : ℝ), ∃ t' : ℝ,
      ∀ y : BohrHull p, Φ t (y + bohrIota p s) = Φ t' y := by
    intro s t
    refine ⟨s + t, fun y => ?_⟩
    have hjet : ∀ k : ℕ,
        iteratedDeriv k (rep (y + bohrIota p s)) ((σ : ℂ) + (t : ℂ) * Complex.I)
          = iteratedDeriv k (rep y) ((σ : ℂ) + ((s + t : ℝ) : ℂ) * Complex.I) := fun k =>
      iteratedDeriv_rep_translate hrρ0 hrepdiff hrepline y s k t
    show HTGeometry.jointSeparant e _ = HTGeometry.jointSeparant e _
    congr 1
    funext k
    exact hjet (k : ℕ)
  have hdense : ∀ y : BohrHull p, Dense (Set.range fun s : ℝ => y + bohrIota p s) :=
    fun y => denseRange_bohrIota_add p y
  exact HTGeometry.exists_ne_zero_of_dense_translates Φ (fun s y => y + bohrIota p s)
    hcont hequiv hdense hbase x

/-- **The relative frequency law from the card's own hypotheses.**  A holomorphic uniformly
almost-periodic solution of an algebraic differential equation of order `n` with holomorphic
uniformly almost-periodic coefficients, whose separant does not vanish identically along it, adds at
most `2n` rationally independent frequencies to the frequency group of its coefficients.

The regularity of every carrier point is derived, not assumed: the separant is a continuous
equivariant family on the carrier, nonzero at the origin, and every orbit of the line is dense. -/
theorem rank_quotient_le_of_implicit_strip_separant {R : ℝ}
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
    (hpu : UniformContinuous (fun x => p x)) (hptb : HasTotallyBoundedOrbit (fun x => p x))
    [MeasurableSpace (BohrHull p)] [BorelSpace (BohrHull p)]
    {q : ℝ →ᵇ (Fin N → ℂ)} (hq : ∀ t : ℝ, q t = (p t).1)
    (hqu : UniformContinuous (fun x => q x)) (hqtb : HasTotallyBoundedOrbit (fun x => q x))
    [MeasurableSpace (BohrHull q)] [BorelSpace (BohrHull q)]
    (hn : 0 < n)
    (hrel : ∀ z ∈ verticalStrip σ R,
      HTGeometry.coeffJetRelation e (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) Fv z) = 0)
    (hsep : ∃ t : ℝ, HTGeometry.jointSeparant e (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) Fv ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0) :
    Module.rank ℤ ((bohrHullFrequencies p) ⧸
        ((bohrHullFrequencies q).addSubgroupOf (bohrHullFrequencies p)))
      ≤ ((n * 2 : ℕ) : Cardinal) := by
  classical
  have hrρ0 : 0 < r + ρ := by linarith
  have hstripsub : verticalStrip σ (r + ρ) ⊆ verticalStrip σ R := by
    intro z hz
    show |z.re - σ| < R
    have : |z.re - σ| < r + ρ := hz
    linarith
  obtain ⟨Gb, ν, rep, hνcont, hrepdiff, hrepval, hrepline, hrelrep⟩ :=
    exists_carrier_representatives hr hρ hrρ hFdiff hFap hp hpu
      (HTGeometry.continuous_coeffJetRelation e) hrel
  -- the representative of the origin is the function itself
  have hrep0 : Set.EqOn (rep 0) Fv (verticalStrip σ (r + ρ)) := by
    refine eqOn_of_eqOn_line hrρ0 (hrepdiff 0) (hFdiff.mono hstripsub) fun s => ?_
    rw [hrepline 0 s, zero_add, bohrEval_bohrIota, hp s]
  have hjet0 : ∀ (k : ℕ) (t : ℝ),
      iteratedDeriv k (rep 0) ((σ : ℂ) + (t : ℂ) * Complex.I)
        = iteratedDeriv k Fv ((σ : ℂ) + (t : ℂ) * Complex.I) := fun k t =>
    eqOn_iteratedDeriv_of_eqOn (isOpen_verticalStrip σ (r + ρ)) hrep0 k
      (mem_verticalStrip_line hrρ0 σ t)
  have hbase : ∃ t : ℝ, HTGeometry.jointSeparant e (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep 0) ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
    obtain ⟨t, ht⟩ := hsep
    refine ⟨t, ?_⟩
    have hrw : (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (rep 0) ((σ : ℂ) + (t : ℂ) * Complex.I))
        = fun k : Fin (n + 1) =>
          iteratedDeriv (k : ℕ) Fv ((σ : ℂ) + (t : ℂ) * Complex.I) := by
      funext k
      exact hjet0 (k : ℕ) t
    rw [hrw]
    exact ht
  have hreg := exists_joint_regular_time hr hρ hνcont hrepdiff hrepval hrepline e hbase
  -- the second component and its jets
  have hd2 : ∀ x : BohrHull p,
      DifferentiableOn ℂ (fun z => (rep x z).2) (verticalStrip σ (r + ρ)) := fun x =>
    (ContinuousLinearMap.snd ℂ (Fin N → ℂ) ℂ).differentiable.comp_differentiableOn (hrepdiff x)
  have hjetsnd : ∀ (x : BohrHull p) (k : ℕ) (t : ℝ),
      iteratedDeriv k (fun z => (rep x z).2) ((σ : ℂ) + (t : ℂ) * Complex.I)
        = (iteratedDeriv k (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I)).2 := fun x k t =>
    HTGeometry.iteratedDeriv_clm_comp_eqOn (isOpen_verticalStrip σ (r + ρ))
      (ContinuousLinearMap.snd ℂ (Fin N → ℂ) ℂ) (hrepdiff x) k
      (mem_verticalStrip_line hrρ0 σ t)
  -- on the fibre the coefficients return
  have hfibre : ∀ x ∈ bohrHullKernel p
      (Submodule.span ℚ ((bohrHullFrequencies q : AddSubgroup ℝ) : Set ℝ)),
      ∀ z ∈ verticalStrip σ (r + ρ), (rep x z).1 = fun i => A i z := by
    intro x hx z hz
    have h1 : (rep x z).1 = (rep 0 z).1 :=
      eqOn_rep_fst_of_mem_bohrHullKernel hrρ0 hq hqu hqtb hrepdiff hrepline hx hz
    have h2 : (rep 0 z).1 = (Fv z).1 := by rw [hrep0 hz]
    rw [h1, h2, hFcoef z hz]
  have hrelfib : ∀ x ∈ bohrHullKernel p
      (Submodule.span ℚ ((bohrHullFrequencies q : AddSubgroup ℝ) : Set ℝ)),
      ∀ s : ℝ, HTGeometry.frozenRelation e
        (fun j => A j ((σ : ℂ) + (s : ℂ) * Complex.I))
        (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (fun z => (rep x z).2)
          ((σ : ℂ) + (s : ℂ) * Complex.I)) = 0 := by
    intro x hx s
    have hz : ((σ : ℂ) + (s : ℂ) * Complex.I) ∈ verticalStrip σ (r + ρ) :=
      mem_verticalStrip_line hrρ0 σ s
    have hjoint := hrelrep x _ hz
    rw [HTGeometry.coeffJetRelation_jet_eq (hrepdiff x) e hz] at hjoint
    rwa [hfibre x hx _ hz] at hjoint
  -- the dominant regions, one per regular pair of a time and a jet
  set Reg : Type _ := {w : ℝ × (Fin (n + 1) → ℂ) //
    partialCoeff (fderiv ℂ (HTGeometry.frozenRelation e
      (fun j => A j ((σ : ℂ) + ((w.1 : ℝ) : ℂ) * Complex.I))) w.2) (Fin.last n) ≠ 0} with hReg
  have hnbhd : ∀ i : Reg, ∃ (S : Set ((Fin (n + 1)) → ℂ))
      (L : ((Fin (n + 1)) → ℂ) →L[ℂ] ℂ) (C : ℝ),
      IsOpen S ∧ Convex ℝ S ∧ (i : ℝ × (Fin (n + 1) → ℂ)).2 ∈ S ∧ 0 ≤ C ∧
      (∀ᶠ s : ℝ in nhds (i : ℝ × (Fin (n + 1) → ℂ)).1, ∀ y ∈ S,
        ‖fderiv ℂ (HTGeometry.frozenRelation e
          (fun j => A j ((σ : ℂ) + (s : ℂ) * Complex.I))) y - L‖ ≤ C) ∧
      C < ‖partialCoeff L (Fin.last n)‖ := by
    intro i
    refine HTGeometry.exists_time_dominant_nbhd e
      (c := fun s : ℝ => fun j => A j ((σ : ℂ) + (s : ℂ) * Complex.I))
      (fun j => ((hAcont j).continuousAt Filter.univ_mem)) i.2
  choose Sset Lref Cval hSopen' hSconv' hmem' hC0' hbnd' hdom' using hnbhd
  refine rank_quotient_le_of_regular_jets_rel hρ hr hpu hptb hq hqu hqtb hνcont
    hrepdiff hrepval hrepline hn
    (P := fun s => HTGeometry.frozenRelation e (fun j => A j ((σ : ℂ) + (s : ℂ) * Complex.I)))
    (P' := fun s y => fderiv ℂ (HTGeometry.frozenRelation e
      (fun j => A j ((σ : ℂ) + (s : ℂ) * Complex.I))) y)
    (τ := fun i : Reg => (i : ℝ × (Fin (n + 1) → ℂ)).1) (S := fun i : Reg => Sset i)
    (L := fun i : Reg => Lref i) (C := fun i : Reg => Cval i)
    (fun i => hSopen' i) (fun i => hSconv' i)
    (fun i => Filter.Eventually.of_forall fun s => fun y _ =>
      (((HTGeometry.differentiable_frozenRelation e
        (fun j => A j ((σ : ℂ) + (s : ℂ) * Complex.I)) y).hasFDerivAt).restrictScalars
        ℝ).hasFDerivWithinAt)
    (fun i => hC0' i) (fun i => hbnd' i) (fun i => hdom' i)
    hrelfib (fun x hx => ?_)
  obtain ⟨t, ht⟩ := hreg x
  have hcoefval : ((fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I)) 0).1
      = fun j => A j ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    have h0 : ((0 : Fin (n + 1)) : ℕ) = 0 := rfl
    simp only [h0, iteratedDeriv_zero]
    exact hfibre x hx _ (mem_verticalStrip_line hrρ0 σ t)
  have hjetval : (fun k : Fin (n + 1) =>
      ((fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (rep x)
        ((σ : ℂ) + (t : ℂ) * Complex.I)) k).2)
      = fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (fun z => (rep x z).2)
        ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    funext k
    exact (hjetsnd x (k : ℕ) t).symm
  have hne : partialCoeff (fderiv ℂ (HTGeometry.frozenRelation e
      (fun j => A j ((σ : ℂ) + (t : ℂ) * Complex.I)))
      (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (fun z => (rep x z).2)
        ((σ : ℂ) + (t : ℂ) * Complex.I))) (Fin.last n) ≠ 0 := by
    rw [HTGeometry.jointSeparant, hcoefval, hjetval] at ht
    exact ht
  exact ⟨⟨(t, fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (fun z => (rep x z).2)
      ((σ : ℂ) + (t : ℂ) * Complex.I)), hne⟩, hmem' _⟩


/-- Almost periodicity passes to the first component of a pair. -/
theorem isBohrAlmostPeriodic_fst {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    {u : ℝ → E₁ × E₂} (hu : HTGeometry.IsBohrAlmostPeriodic u) :
    HTGeometry.IsBohrAlmostPeriodic fun t => (u t).1 := by
  intro ε hε
  obtain ⟨L, hL, hdense⟩ := hu ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτ, hb⟩ := hdense a
  refine ⟨τ, hτ, fun x => ?_⟩
  have h := hb x
  have hsplit : ‖(u (x + τ)).1 - (u x).1‖ ≤ ‖u (x + τ) - u x‖ := by
    have := norm_fst_le (u (x + τ) - u x)
    simpa using this
  exact le_trans hsplit h

/-- **The relative frequency law, in closed form.**  Uniform continuity and total boundedness of the
translation orbits are not assumed: both follow from almost periodicity on the strip. -/
theorem rank_quotient_le_of_implicit_strip_separant_closed {R : ℝ}
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
    {q : ℝ →ᵇ (Fin N → ℂ)} (hq : ∀ t : ℝ, q t = (p t).1)
    (hn : 0 < n)
    (hrel : ∀ z ∈ verticalStrip σ R,
      HTGeometry.coeffJetRelation e (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) Fv z) = 0)
    (hsep : ∃ t : ℝ, HTGeometry.jointSeparant e (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) Fv ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0) :
    Module.rank ℤ ((bohrHullFrequencies p) ⧸
        ((bohrHullFrequencies q).addSubgroupOf (bohrHullFrequencies p)))
      ≤ ((n * 2 : ℕ) : Cardinal) := by
  classical
  letI : MeasurableSpace (BohrHull p) := borel _
  haveI : BorelSpace (BohrHull p) := ⟨rfl⟩
  letI : MeasurableSpace (BohrHull q) := borel _
  haveI : BorelSpace (BohrHull q) := ⟨rfl⟩
  have hR : 0 < R := by linarith
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
  exact rank_quotient_le_of_implicit_strip_separant hr hρ hrρ hFdiff hFap hFcoef hAcont hp
    (uniformContinuous_of_isBohrAlmostPeriodic p.continuous hpap)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic p.continuous hpap) hq
    (uniformContinuous_of_isBohrAlmostPeriodic q.continuous hqap)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic q.continuous hqap) hn hrel hsep


end GaloisForLFunctions
