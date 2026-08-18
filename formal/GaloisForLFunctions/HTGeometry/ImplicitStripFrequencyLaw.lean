import GaloisForLFunctions.HTGeometry.ImplicitRelativeFrequency
import GaloisForLFunctions.HTGeometry.CoefficientJetRelation

/-!
# The relative frequency law for a strip equation with almost-periodic coefficients

The equation is autonomous in the joint variable, so the pair of the coefficient tuple and the
solution has carrier representatives solving the joint relation.  On the fibre of the coefficient
projection the first component of every representative is the coefficient tuple itself, so there the
joint relation is the original equation with its own coefficients, and the jets of the second
component separate the fibre.

The conclusion is the relative rank: the frequency group of the pair, modulo the frequency group of
the coefficients, has rational rank at most `2n` — with no bound whatever on the coefficients' own
frequency group.
-/

open Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ r ρ : ℝ} {N n : ℕ}

/-- **The relative frequency law.**  A holomorphic uniformly almost-periodic solution of an
algebraic differential equation of order `n` whose coefficients are themselves holomorphic and
uniformly almost periodic on the strip adds at most `2n` rationally independent frequencies to the
frequency group of its coefficients. -/
theorem rank_quotient_le_of_implicit_strip_solution {R : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    {A : Fin N → ℂ → ℂ} {e : Fin N → Fin (n + 1) → ℕ}
    {Fv : ℂ → ((Fin N → ℂ) × ℂ)}
    (hFdiff : DifferentiableOn ℂ Fv (verticalStrip σ R))
    (hFap : IsStripAlmostPeriodic Fv σ R)
    (hFcoef : ∀ z ∈ verticalStrip σ (r + ρ), (Fv z).1 = fun i => A i z)
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
    {ι : Type*} {τ : ι → ℝ} {S : ι → Set (Fin (n + 1) → ℂ)}
    {L : ι → (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ι → ℝ}
    (hSopen : ∀ i, IsOpen (S i)) (hSconv : ∀ i, Convex ℝ (S i))
    (hC : ∀ i, 0 ≤ C i)
    (hbnd : ∀ i, ∀ᶠ s : ℝ in nhds (τ i), ∀ y ∈ S i,
      ‖fderiv ℂ (HTGeometry.frozenRelation e
          (fun j => A j ((σ : ℂ) + (s : ℂ) * Complex.I))) y - L i‖ ≤ C i)
    (hdom : ∀ i, C i < ‖partialCoeff (L i) (Fin.last n)‖)
    (hatlasSol : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (verticalStrip σ (r + ρ)) →
      (∀ s : ℝ, HTGeometry.frozenRelation e (fun j => A j ((σ : ℂ) + (s : ℂ) * Complex.I))
        (fun k : Fin (n + 1) =>
          iteratedDeriv (k : ℕ) g ((σ : ℂ) + (s : ℂ) * Complex.I)) = 0) →
      ∃ i, (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) g ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I)) ∈ S i) :
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
  -- carrier representatives for the joint relation
  obtain ⟨Gb, ν, rep, hνcont, hrepdiff, hrepval, hrepline, hrelrep⟩ :=
    exists_carrier_representatives hr hρ hrρ hFdiff hFap hp hpu
      (HTGeometry.continuous_coeffJetRelation e) hrel
  -- the representative of the origin is the function itself
  have hrep0 : Set.EqOn (rep 0) Fv (verticalStrip σ (r + ρ)) := by
    refine eqOn_of_eqOn_line hrρ0 (hrepdiff 0) (hFdiff.mono hstripsub) fun s => ?_
    rw [hrepline 0 s, zero_add, bohrEval_bohrIota, hp s]
  -- on the fibre the coefficients return
  have hfibre : ∀ x ∈ bohrHullKernel p
      (Submodule.span ℚ ((bohrHullFrequencies q : AddSubgroup ℝ) : Set ℝ)),
      ∀ z ∈ verticalStrip σ (r + ρ), (rep x z).1 = fun i => A i z := by
    intro x hx z hz
    have h1 : (rep x z).1 = (rep 0 z).1 :=
      eqOn_rep_fst_of_mem_bohrHullKernel hrρ0 hq hqu hqtb hrepdiff hrepline hx hz
    have h2 : (rep 0 z).1 = (Fv z).1 := by rw [hrep0 hz]
    rw [h1, h2, hFcoef z hz]
  -- hence the second component solves the frozen equation
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
  refine rank_quotient_le_of_regular_jets_rel hρ hr hpu hptb hq hqu hqtb hνcont
    hrepdiff hrepval hrepline hn
    (P := fun s => HTGeometry.frozenRelation e (fun j => A j ((σ : ℂ) + (s : ℂ) * Complex.I)))
    (P' := fun s y => fderiv ℂ (HTGeometry.frozenRelation e
      (fun j => A j ((σ : ℂ) + (s : ℂ) * Complex.I))) y)
    (τ := τ) (S := S) (L := L) (C := C)
    hSopen hSconv
    (fun i => Filter.Eventually.of_forall fun s => fun y _ =>
      (((HTGeometry.differentiable_frozenRelation e
        (fun j => A j ((σ : ℂ) + (s : ℂ) * Complex.I)) y).hasFDerivAt).restrictScalars
        ℝ).hasFDerivWithinAt)
    hC
    hbnd hdom
    hrelfib (fun x hx => ?_)
  · refine hatlasSol (fun z => (rep x z).2) ?_ (hrelfib x hx)
    exact (ContinuousLinearMap.snd ℂ (Fin N → ℂ) ℂ).differentiable.comp_differentiableOn
      (hrepdiff x)

end GaloisForLFunctions
