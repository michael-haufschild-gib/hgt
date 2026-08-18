import GaloisForLFunctions.HTGeometry.StripSolutionPhaseRank
import GaloisForLFunctions.HTGeometry.HullChartFrequencyRank
import GaloisForLFunctions.HTGeometry.ComplexJetEuclidean
import GaloisForLFunctions.HTGeometry.MinimalFlowJetVanishing
import GaloisForLFunctions.HTGeometry.AutonomousJetRelation

/-!
# The order-sharp phase rank of a strip solution

Collecting all sample jets into one observation map bounds the frequency rank by twice the number
of samples times the jet length.  Passing instead to a finite closed cover subordinate to the
regular sets, and using on each piece the single jet at its own sample time, removes the dependence
on the number of samples.

The exponent is `2n`, not `2(n+1)`: separation needs only the jets of orders `0 … n−1`, because the
top jet is recovered from the relation wherever it is dominant in the last coordinate.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {σ r ρ : ℝ} {n : ℕ}

/-- **The order-sharp frequency-rank bound for a strip solution.**  A finite atlas of regular sample
times bounds the rational rank of the frequency group by `2n`, independently of the size of the
atlas. -/
theorem rank_le_of_regular_jets_sharp (hρ : 0 < ρ) (hrpos : 0 < r)
    {f : ℝ →ᵇ ℂ} (hfu : UniformContinuous (fun x => f x))
    (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {Gb : ℝ →ᵇ ((closedStrip σ (r + ρ)) →ᵇ ℂ)}
    {ν : BohrHull f → BohrHull Gb} (hν : Continuous ν)
    {rep : BohrHull f → (ℂ → ℂ)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ)))
    (hrepval : ∀ (x : BohrHull f) (z : closedStrip σ (r + ρ)),
      rep x (z : ℂ) = bohrEval Gb (ν x) z)
    (hrepline : ∀ (x : BohrHull f) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t))
    (hn : 0 < n) {P : (Fin (n + 1) → ℂ) → ℂ}
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)}
    {ι : Type*} {τ : ι → ℝ} {S : ι → Set (Fin (n + 1) → ℂ)}
    {L : ι → (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ι → ℝ}
    (hSopen : ∀ i, IsOpen (S i)) (hSconv : ∀ i, Convex ℝ (S i))
    (hPd : ∀ i, ∀ y ∈ S i, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) (S i) y)
    (hC : ∀ i, 0 ≤ C i) (hbnd : ∀ i, ∀ y ∈ S i, ‖P' y - L i‖ ≤ C i)
    (hdom : ∀ i, C i < ‖partialCoeff (L i) (Fin.last n)‖)
    (hrelrep : ∀ (x : BohrHull f) (s : ℝ), P (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (s : ℂ) * Complex.I)) = 0)
    (hatlas : ∀ x : BohrHull f, ∃ i, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I)) ∈ S i) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((n * 2 : ℕ) : Cardinal) := by
  classical
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull hftb
  have hrρ : r < r + ρ := by linarith
  have hstripsub : verticalStrip σ r ⊆ verticalStrip σ (r + ρ) := by
    intro z hz
    show |z.re - σ| < r + ρ
    have : |z.re - σ| < r := hz
    linarith
  -- the full jet at each sample time, and the regular sets it defines
  set J : ι → BohrHull f → (Fin (n + 1) → ℂ) := fun i x => fun k : Fin (n + 1) =>
    iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I) with hJ
  have hJcont : ∀ i, Continuous (J i) := fun i =>
    continuous_pi fun k =>
      continuous_jet_of_representatives hρ hrpos hrρ hν hrepdiff hrepval (k : ℕ) (τ i)
  set U : ι → Set (BohrHull f) := fun i => {x | J i x ∈ S i} with hU
  have hUopen : ∀ i, IsOpen (U i) := fun i => (hSopen i).preimage (hJcont i)
  have hUcov : ∀ x : BohrHull f, ∃ i, x ∈ U i := hatlas
  -- the lower jet, which already separates
  set Jlow : ι → BohrHull f → (Fin n → ℂ) := fun i x => fun k : Fin n =>
    iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I) with hJlow
  have hJlowcont : ∀ i, Continuous (Jlow i) := fun i =>
    continuous_pi fun k =>
      continuous_jet_of_representatives hρ hrpos hrρ hν hrepdiff hrepval (k : ℕ) (τ i)
  have hsep : ∀ (i : ι) (x y : BohrHull f), x ∈ U i → y ∈ U i → Jlow i x = Jlow i y → x = y := by
    intro i x y hx hy hxy
    have hxev : ∀ᶠ s : ℝ in nhds (τ i), (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (s : ℂ) * Complex.I)) ∈ S i :=
      eventually_jet_mem (by linarith) (hrepdiff x) (hSopen i) hx
    have hyev : ∀ᶠ s : ℝ in nhds (τ i), (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (rep y) ((σ : ℂ) + (s : ℂ) * Complex.I)) ∈ S i :=
      eventually_jet_mem (by linarith) (hrepdiff y) (hSopen i) hy
    refine carrier_eq_of_jet_eq_local hrpos hfu hn ((hrepdiff x).mono hstripsub)
      ((hrepdiff y).mono hstripsub) (hSconv i) (hPd i) (hC i) (hbnd i) (hdom i)
      hxev (Filter.Eventually.of_forall (hrelrep x)) hyev
      (Filter.Eventually.of_forall (hrelrep y)) (fun k => ?_) (hrepline x) (hrepline y)
    exact congrFun hxy k
  -- a finite closed cover subordinate to the regular sets
  obtain ⟨M, idx, F, hFclosed, hFsub, hFcov⟩ :=
    HTGeometry.exists_finite_closed_cover_subordinate U hUopen hUcov
  refine rank_bohrHullFrequencies_le_of_charts hfu hftb F hFclosed hFcov
    (fun j x => HTGeometry.complexJetToEuclidean n (Jlow (idx j) x)) (fun j => ?_) (fun j => ?_)
  · exact (HTGeometry.continuous_complexJetToEuclidean n).comp (hJlowcont (idx j)) |>.continuousOn
  · refine HTGeometry.injOn_complexJetToEuclidean_comp ?_
    intro x hx y hy hxy
    exact hsep (idx j) x y (hFsub j hx) (hFsub j hy) hxy


/-- **The order-sharp phase-rank theorem for a strip almost-periodic solution.**  A holomorphic
uniformly almost-periodic solution of an algebraic differential relation of order `n`, regular at
some sample time for every carrier point, has frequency group of rational rank at most `2n`. -/
theorem rank_le_of_strip_solution_sharp {F : ℂ → ℂ} {R : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n) {P : (Fin (n + 1) → ℂ) → ℂ} (hPcont : Continuous P)
    (hrel : ∀ z ∈ verticalStrip σ R, P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F z) = 0)
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)}
    {ι : Type*} {τ : ι → ℝ} {S : ι → Set (Fin (n + 1) → ℂ)}
    {L : ι → (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ι → ℝ}
    (hSopen : ∀ i, IsOpen (S i)) (hSconv : ∀ i, Convex ℝ (S i))
    (hPd : ∀ i, ∀ y ∈ S i, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) (S i) y)
    (hC : ∀ i, 0 ≤ C i) (hbnd : ∀ i, ∀ y ∈ S i, ‖P' y - L i‖ ≤ C i)
    (hdom : ∀ i, C i < ‖partialCoeff (L i) (Fin.last n)‖)
    (hatlas : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (verticalStrip σ (r + ρ)) →
      (∀ z ∈ verticalStrip σ (r + ρ), P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) g z) = 0) →
      ∃ i, (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) g ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I)) ∈ S i) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((n * 2 : ℕ) : Cardinal) := by
  obtain ⟨Gb, ν, rep, hνcont, hrepdiff, hrepval, hrepline, hrelrep⟩ :=
    exists_carrier_representatives hr hρ hrρ hF hap hf hfu hPcont hrel
  refine rank_le_of_regular_jets_sharp (τ := τ) hρ hr hfu hftb hνcont hrepdiff hrepval hrepline hn
    hSopen hSconv hPd hC hbnd hdom (fun x s => ?_) (fun x => ?_)
  · exact hrelrep x _ (mem_verticalStrip_line (by linarith) σ s)
  · exact hatlas (rep x) (hrepdiff x) (hrelrep x)


/-! ### The frequency group of the function itself -/

theorem rank_le_of_addSubgroup_le {H K : AddSubgroup ℝ} (h : H ≤ K) :
    Module.rank ℤ H ≤ Module.rank ℤ K := by
  refine LinearMap.rank_le_of_injective (AddSubgroup.inclusion h).toIntLinearMap ?_
  intro a b hab
  have h2 : (AddSubgroup.inclusion h a : ℝ) = (AddSubgroup.inclusion h b : ℝ) :=
    congrArg Subtype.val hab
  exact Subtype.ext h2

/-- **The card's finite-frequency law.**  The additive group generated by the Bohr spectrum of a
holomorphic uniformly almost-periodic solution of an order-`n` relation, regular somewhere on every
carrier point, has rational rank at most `2n`. -/
theorem rank_bohrSpectrum_le_of_strip_solution_sharp {F : ℂ → ℂ} {R : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n) {P : (Fin (n + 1) → ℂ) → ℂ} (hPcont : Continuous P)
    (hrel : ∀ z ∈ verticalStrip σ R, P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F z) = 0)
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)}
    {ι : Type*} {τ : ι → ℝ} {S : ι → Set (Fin (n + 1) → ℂ)}
    {L : ι → (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ι → ℝ}
    (hSopen : ∀ i, IsOpen (S i)) (hSconv : ∀ i, Convex ℝ (S i))
    (hPd : ∀ i, ∀ y ∈ S i, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) (S i) y)
    (hC : ∀ i, 0 ≤ C i) (hbnd : ∀ i, ∀ y ∈ S i, ‖P' y - L i‖ ≤ C i)
    (hdom : ∀ i, C i < ‖partialCoeff (L i) (Fin.last n)‖)
    (hatlas : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (verticalStrip σ (r + ρ)) →
      (∀ z ∈ verticalStrip σ (r + ρ), P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) g z) = 0) →
      ∃ i, (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) g ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I)) ∈ S i) :
    Module.rank ℤ (AddSubgroup.closure (bohrSpectrum (fun x => f x)))
      ≤ ((n * 2 : ℕ) : Cardinal) := by
  have hfa : HTGeometry.IsBohrAlmostPeriodic (fun x => f x) :=
    isBohrAlmostPeriodic_of_hasTotallyBoundedOrbit hftb
  refine le_trans (rank_le_of_addSubgroup_le (closure_bohrSpectrum_le_bohrHullFrequencies hfa)) ?_
  exact rank_le_of_strip_solution_sharp (τ := τ) hr hρ hrρ hF hap hf hfu hftb hn hPcont hrel
    hSopen hSconv hPd hC hbnd hdom hatlas


/-! ### The autonomous form: the relation given as a differential polynomial -/

/-- **The finite-frequency law from an autonomous differential polynomial.**  If `F` is holomorphic
and uniformly almost periodic on a strip, annihilated there by an autonomous differential polynomial
of order `n`, and if every holomorphic solution on the substrip has its separant nonzero at some
real time, then the frequency group of the line restriction has rational rank at most `2n`.

The regularity hypothesis is `(9)`: no carrier point is everywhere singular.  The dominant convex
regions the chart argument needs are built here from it, one per regular jet, by
`exists_convex_dominant_nbhd` together with the identification of the separant with the top partial
derivative. -/
theorem rank_bohrSpectrum_le_of_autonomous_strip_solution {F : ℂ → ℂ} {R : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n) (Pp : Polynomial (MvPolynomial (Fin n) ℂ))
    (hrel : ∀ z ∈ verticalStrip σ R,
      jetRelation n Pp (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F z) = 0)
    (hreg : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (verticalStrip σ (r + ρ)) →
      (∀ z ∈ verticalStrip σ (r + ρ),
        jetRelation n Pp (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) g z) = 0) →
      ∃ t : ℝ, jetRelation n (Polynomial.derivative Pp)
        (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0) :
    Module.rank ℤ (AddSubgroup.closure (bohrSpectrum (fun x => f x)))
      ≤ ((n * 2 : ℕ) : Cardinal) := by
  classical
  set Q : (Fin (n + 1) → ℂ) → ℂ := jetRelation n Pp with hQ
  set Q' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ) := fun y => fderiv ℂ Q y with hQ'
  -- the regular jets, and a dominant convex region around each
  set Reg : Type _ := {y : Fin (n + 1) → ℂ // partialCoeff (Q' y) (Fin.last n) ≠ 0} with hReg
  have hnbhd : ∀ y : Reg, ∃ (S : Set (Fin (n + 1) → ℂ)) (C : ℝ),
      IsOpen S ∧ Convex ℝ S ∧ (y : Fin (n + 1) → ℂ) ∈ S ∧ 0 ≤ C ∧
      (∀ z ∈ S, ‖Q' z - Q' (y : Fin (n + 1) → ℂ)‖ ≤ C) ∧
      C < ‖partialCoeff (Q' (y : Fin (n + 1) → ℂ)) (Fin.last n)‖ := by
    intro y
    exact HTGeometry.exists_convex_dominant_nbhd
      ((continuous_fderiv_jetRelation n Pp).continuousAt) y.2
  choose Sset Cval hSopen' hSconv' hmem' hC0' hbnd' hdom' using hnbhd
  refine rank_bohrSpectrum_le_of_strip_solution_sharp
    (τ := fun i : Reg × ℝ => i.2) (S := fun i : Reg × ℝ => Sset i.1)
    (L := fun i : Reg × ℝ => Q' (i.1 : Fin (n + 1) → ℂ)) (C := fun i : Reg × ℝ => Cval i.1)
    (P' := Q') hr hρ hrρ hF hap hf hfu hftb hn (contDiff_jetRelation n Pp).continuous hrel
    (fun i => hSopen' i.1) (fun i => hSconv' i.1) (fun i y hy => ?_) (fun i => hC0' i.1)
    (fun i y hy => hbnd' i.1 y hy) (fun i => hdom' i.1) (fun g hg hgrel => ?_)
  · exact ((differentiable_jetRelation n Pp y).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  · obtain ⟨t, ht⟩ := hreg g hg hgrel
    have hy : partialCoeff (Q' (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) g ((σ : ℂ) + (t : ℂ) * Complex.I))) (Fin.last n) ≠ 0 := by
      rw [hQ', partialCoeff_fderiv_jetRelation_last]
      exact ht
    exact ⟨(⟨_, hy⟩, t), hmem' ⟨_, hy⟩⟩

end GaloisForLFunctions
