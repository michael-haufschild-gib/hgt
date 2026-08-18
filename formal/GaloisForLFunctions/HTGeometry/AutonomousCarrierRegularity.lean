import GaloisForLFunctions.HTGeometry.StripSolutionPhaseRankSharp
import GaloisForLFunctions.HTGeometry.AutonomousStripSeparant
import GaloisForLFunctions.HTGeometry.CarrierTranslationEquivariance

/-!
# Regularity propagates from the function to every carrier point

The separant of a minimal autonomous equation, evaluated along the jet of a carrier representative
at a real time, is a continuous function of the carrier point, and translating the carrier point
translates the time: the family is equivariant for the flow of the line on the carrier.  The set
where the whole family vanishes is therefore closed and invariant, and the translates of any single
carrier point are dense, so that set is either empty or everything.  It is not everything, because
at the origin of the carrier the representative has the jets of the function itself, where the
separant of a minimal equation is not identically zero.

Consequently no carrier point is everywhere singular, which is the regularity input of the
order-sharp frequency-rank bound.  Combining, a holomorphic uniformly almost-periodic function on a
strip satisfying a nonzero autonomous algebraic differential equation of exact order `n` there has
frequency group of rational rank at most `2n`, with no further hypothesis.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ r ρ : ℝ} {n : ℕ}

/-- **Regularity at one time for every carrier point.**  If a jet functional of the function itself
is nonzero at some real time, then for every carrier point the same functional of its representative
is nonzero at some real time. -/
theorem exists_carrier_separant_ne_zero (hr : 0 < r) (hρ : 0 < ρ)
    {F : ℂ → ℂ} {f : ℝ →ᵇ ℂ}
    (hF : DifferentiableOn ℂ F (verticalStrip σ (r + ρ)))
    (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    {Gb : ℝ →ᵇ ((closedStrip σ (r + ρ)) →ᵇ ℂ)} {ν : BohrHull f → BohrHull Gb}
    (hν : Continuous ν) {rep : BohrHull f → (ℂ → ℂ)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepval : ∀ (x : BohrHull f) (z : closedStrip σ (r + ρ)),
      rep x (z : ℂ) = bohrEval Gb (ν x) z)
    (hrepline : ∀ (x : BohrHull f) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t))
    (D : Polynomial (MvPolynomial (Fin n) ℂ))
    (hsep : ∃ t : ℝ, jetRelation n D
      (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0)
    (x : BohrHull f) :
    ∃ t : ℝ, jetRelation n D
      (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
  have hrρ : r < r + ρ := by linarith
  have hrρ0 : 0 < r + ρ := by linarith
  -- the equivariant family: the separant along the jet of the representative at time `t`
  set Φ : ℝ → BohrHull f → ℂ := fun t y => jetRelation n D
    (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) (rep y) ((σ : ℂ) + (t : ℂ) * Complex.I)) with hΦ
  have hcont : ∀ t : ℝ, Continuous (Φ t) := by
    intro t
    refine (contDiff_jetRelation n D).continuous.comp (continuous_pi fun k => ?_)
    exact continuous_jet_of_representatives hρ hr hrρ hν hrepdiff hrepval (k : ℕ) t
  have hequiv : ∀ (s : ℝ) (t : ℝ), ∃ t' : ℝ,
      ∀ y : BohrHull f, Φ t (y + bohrIota f s) = Φ t' y := by
    intro s t
    refine ⟨s + t, fun y => ?_⟩
    have hjet : ∀ k : ℕ,
        iteratedDeriv k (rep (y + bohrIota f s)) ((σ : ℂ) + (t : ℂ) * Complex.I)
          = iteratedDeriv k (rep y) ((σ : ℂ) + ((s + t : ℝ) : ℂ) * Complex.I) := fun k =>
      iteratedDeriv_rep_translate hrρ0 hrepdiff hrepline y s k t
    show jetRelation n D _ = jetRelation n D _
    congr 1
    funext k
    exact hjet (k : ℕ)
  have hdense : ∀ y : BohrHull f, Dense (Set.range fun s : ℝ => y + bohrIota f s) :=
    fun y => denseRange_bohrIota_add f y
  have hbase : ∃ t : ℝ, Φ t 0 ≠ 0 := by
    obtain ⟨t, ht⟩ := hsep
    refine ⟨t, ?_⟩
    have hjet : ∀ k : ℕ, iteratedDeriv k (rep 0) ((σ : ℂ) + (t : ℂ) * Complex.I)
        = iteratedDeriv k F ((σ : ℂ) + (t : ℂ) * Complex.I) := fun k =>
      iteratedDeriv_rep_zero hrρ0 hF hf hrepdiff hrepline k t
    have hrw : (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (rep 0) ((σ : ℂ) + (t : ℂ) * Complex.I))
        = fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F ((σ : ℂ) + (t : ℂ) * Complex.I) := by
      funext k
      exact hjet (k : ℕ)
    show jetRelation n D _ ≠ 0
    rw [hrw]
    exact ht
  exact HTGeometry.exists_ne_zero_of_dense_translates Φ (fun s y => y + bohrIota f s)
    hcont hequiv hdense hbase x


/-- **The finite-frequency law for an autonomous strip equation.**  A function holomorphic and
uniformly almost periodic on a vertical strip which satisfies there a nonzero autonomous algebraic
differential equation of exact order `n` — no nonzero annihilator is free of the top jet — has
frequency group of rational rank at most `2n`.

Ritt's separant step supplies a degree-minimal equation whose separant is nonzero at some real time;
the carrier flow propagates that regularity to every carrier point; and the order-sharp chart bound
converts it into the rank estimate.  Uniform continuity of the line restriction and total
boundedness of its translation orbit are not assumed: both follow from almost periodicity on the
strip. -/
theorem rank_bohrHullFrequencies_le_of_stripAnnihilator {F : ℂ → ℂ} {R : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n)
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ StripAnnihilator σ R F n P)
    (horder : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 → StripAnnihilator σ R F n Q →
      Q.natDegree ≠ 0) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((n * 2 : ℕ) : Cardinal) := by
  classical
  have hR : 0 < R := by linarith
  -- almost periodicity of the line restriction, and the two regularity facts it implies
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
  have hstripsub : verticalStrip σ (r + ρ) ⊆ verticalStrip σ R := by
    intro z hz
    show |z.re - σ| < R
    have : |z.re - σ| < r + ρ := hz
    linarith
  -- a degree-minimal equation whose separant is nonzero at a real time
  obtain ⟨Pp, hPp0, hPpdeg, hPpann, hPpsep⟩ :=
    exists_minimal_strip_separant_line hR hF hex horder
  -- carrier representatives for that equation
  obtain ⟨Gb, ν, rep, hνcont, hrepdiff, hrepval, hrepline, hrelrep⟩ :=
    exists_carrier_representatives hr hρ hrρ hF hap hf hfu
      (contDiff_jetRelation n Pp).continuous hPpann
  -- regularity at one time for every carrier point
  have hcarrier : ∀ x : BohrHull f, ∃ t : ℝ,
      jetRelation n (Polynomial.derivative Pp)
        (fun k : Fin (n + 1) =>
          iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := fun x =>
    exists_carrier_separant_ne_zero hr hρ (hF.mono hstripsub) hf hνcont hrepdiff hrepval hrepline
      (Polynomial.derivative Pp) hPpsep x
  -- the dominant convex regions built from the regular jets
  set Q' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ) :=
    fun y => fderiv ℂ (jetRelation n Pp) y with hQ'
  set Reg : Type _ := {y : Fin (n + 1) → ℂ // partialCoeff (Q' y) (Fin.last n) ≠ 0} with hReg
  have hnbhd : ∀ y : Reg, ∃ (S : Set (Fin (n + 1) → ℂ)) (C : ℝ),
      IsOpen S ∧ Convex ℝ S ∧ (y : Fin (n + 1) → ℂ) ∈ S ∧ 0 ≤ C ∧
      (∀ z ∈ S, ‖Q' z - Q' (y : Fin (n + 1) → ℂ)‖ ≤ C) ∧
      C < ‖partialCoeff (Q' (y : Fin (n + 1) → ℂ)) (Fin.last n)‖ := fun y =>
    HTGeometry.exists_convex_dominant_nbhd ((continuous_fderiv_jetRelation n Pp).continuousAt) y.2
  choose Sset Cval hSopen' hSconv' hmem' hC0' hbnd' hdom' using hnbhd
  refine rank_le_of_regular_jets_sharp (τ := fun i : Reg × ℝ => i.2)
    (S := fun i : Reg × ℝ => Sset i.1) (L := fun i : Reg × ℝ => Q' (i.1 : Fin (n + 1) → ℂ))
    (C := fun i : Reg × ℝ => Cval i.1) (P := jetRelation n Pp) (P' := Q')
    hρ hr hfu hftb hνcont hrepdiff hrepval hrepline hn
    (fun i => hSopen' i.1) (fun i => hSconv' i.1) (fun i y hy => ?_) (fun i => hC0' i.1)
    (fun i y hy => hbnd' i.1 y hy) (fun i => hdom' i.1) (fun x s => ?_) (fun x => ?_)
  · exact ((differentiable_jetRelation n Pp y).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  · exact hrelrep x _ (mem_verticalStrip_line (by linarith) σ s)
  · obtain ⟨t, ht⟩ := hcarrier x
    have hy : partialCoeff (Q' (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I))) (Fin.last n) ≠ 0 := by
      rw [hQ', partialCoeff_fderiv_jetRelation_last]
      exact ht
    exact ⟨(⟨_, hy⟩, t), hmem' ⟨_, hy⟩⟩

/-- **The card's finite-frequency law, in closed form, at the level of the carrier.**  A function
holomorphic and uniformly almost periodic on a vertical strip of positive half-width, satisfying
there a nonzero autonomous algebraic differential equation of exact order `n`, has carrier character
group of rational rank at most `2n`.

No substrip, no regularity, no orbit hypothesis: the substrip is chosen inside the proof, and the
Borel structure on the carrier is the one generated by its topology. -/
theorem rank_bohrHullFrequencies_le_of_strip_differential_equation {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hn : 0 < n)
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ StripAnnihilator σ R F n P)
    (horder : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 → StripAnnihilator σ R F n Q →
      Q.natDegree ≠ 0) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((n * 2 : ℕ) : Cardinal) := by
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  exact rank_bohrHullFrequencies_le_of_stripAnnihilator (r := R / 3) (ρ := R / 3)
    (by linarith) (by linarith) (by linarith) hF hap hf hn hex horder

/-- **The card's finite-frequency law.**  The additive group generated by the Bohr frequencies of the
line restriction has rational rank at most `2n`. -/
theorem rank_bohrSpectrum_le_of_strip_differential_equation {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hn : 0 < n)
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ StripAnnihilator σ R F n P)
    (horder : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 → StripAnnihilator σ R F n Q →
      Q.natDegree ≠ 0) :
    Module.rank ℤ (AddSubgroup.closure (bohrSpectrum (fun x => f x)))
      ≤ ((n * 2 : ℕ) : Cardinal) := by
  have hfap : HTGeometry.IsBohrAlmostPeriodic (fun x : ℝ => f x) := by
    have hfline : (fun x : ℝ => f x) = fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I) := by
      funext x
      exact hf x
    rw [hfline]
    exact isBohrAlmostPeriodic_line hR hap
  refine le_trans (rank_le_of_addSubgroup_le (closure_bohrSpectrum_le_bohrHullFrequencies hfap)) ?_
  exact rank_bohrHullFrequencies_le_of_strip_differential_equation hR hF hap hf hn hex horder

/-- **The observable form of the law.**  Every continuous observable of the carrier — in particular
every continuous translation-equivariant divisor observable of the solution — has frequency group of
rational rank at most `2n`.

A continuous function of the carrier point, read along the line, is almost periodic with all its
frequencies among the characters of the carrier; the rank bound is therefore inherited. -/
theorem rank_bohrSpectrum_observable_le_of_strip_differential_equation {F : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hn : 0 < n)
    (hex : ∃ P : Polynomial (MvPolynomial (Fin n) ℂ), P ≠ 0 ∧ StripAnnihilator σ R F n P)
    (horder : ∀ Q : Polynomial (MvPolynomial (Fin n) ℂ), Q ≠ 0 → StripAnnihilator σ R F n Q →
      Q.natDegree ≠ 0)
    (Ψ : BohrHull f → ℂ) (hΨ : Continuous Ψ) :
    Module.rank ℤ (AddSubgroup.closure (bohrSpectrum (fun t : ℝ => Ψ (bohrIota f t))))
      ≤ ((n * 2 : ℕ) : Cardinal) := by
  have hfap : HTGeometry.IsBohrAlmostPeriodic (fun x : ℝ => f x) := by
    have hfline : (fun x : ℝ => f x) = fun t : ℝ => F ((σ : ℂ) + (t : ℂ) * Complex.I) := by
      funext x
      exact hf x
    rw [hfline]
    exact isBohrAlmostPeriodic_line hR hap
  have hfu : UniformContinuous (fun x : ℝ => f x) :=
    uniformContinuous_of_isBohrAlmostPeriodic f.continuous hfap
  have hftb : HasTotallyBoundedOrbit (fun x : ℝ => f x) :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic f.continuous hfap
  have hsub : AddSubgroup.closure (bohrSpectrum (fun t : ℝ => Ψ (bohrIota f t)))
      ≤ bohrHullFrequencies f :=
    AddSubgroup.closure_le _ |>.mpr
      (bohrSpectrum_observable_subset_bohrHullFrequencies hfu hftb Ψ hΨ)
  refine le_trans (rank_le_of_addSubgroup_le hsub) ?_
  exact rank_bohrHullFrequencies_le_of_strip_differential_equation hR hF hap hf hn hex horder

end GaloisForLFunctions
