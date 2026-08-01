import GaloisForLFunctions.HTGeometry.CarrierRepresentative
import GaloisForLFunctions.HTGeometry.JetSampleAtlas

/-!
# The finite-phase rank bound, assembled

Every carrier point of an almost periodic function on a strip has a holomorphic representative that
solves the same differential relation.  Suppose each such representative is *regular* at one of
finitely many sample times: its full order-`n` jet there lies in a region where the top partial
derivative of the relation dominates the deviation of the derivative from a fixed functional.

Then the jets at the sample times separate the carrier — the jets of two carrier points agreeing at a
regular time forces their representatives to agree near that time, hence on the strip by the identity
theorem, hence the carrier points are equal — and each jet coordinate is continuous by Cauchy's
estimate.  The finite jet sample is therefore a continuous injection of the carrier into
`ℂ^{m(n+1)}`, and the dimension bound gives

`rank_ℚ Γ_B(f) ≤ 2 m (n+1)`,

the finite-phase law's quantitative form.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {F : ℂ → ℂ} {σ r ρ : ℝ} {n : ℕ}

/-- Continuity in the parameter of the jet of a holomorphic function along the central line. -/
theorem continuous_jet_line {u : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hu : DifferentiableOn ℂ u (verticalStrip σ R)) (k : ℕ) :
    Continuous fun s : ℝ => iteratedDeriv k u ((σ : ℂ) + (s : ℂ) * Complex.I) := by
  have hline : Continuous fun s : ℝ => ((σ : ℂ) + (s : ℂ) * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hk : DifferentiableOn ℂ (iteratedDeriv k u) (verticalStrip σ R) :=
    differentiableOn_iteratedDeriv_verticalStrip hu k
  refine continuous_iff_continuousAt.mpr fun s => ?_
  have hmem : ((σ : ℂ) + (s : ℂ) * Complex.I) ∈ verticalStrip σ R := mem_verticalStrip_line hR σ s
  have hd : DifferentiableAt ℂ (iteratedDeriv k u) ((σ : ℂ) + (s : ℂ) * Complex.I) :=
    hk.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds hmem)
  exact ContinuousAt.comp (x := s) hd.continuousAt hline.continuousAt

/-- If the full jet at a time lies in an open region, it stays there for nearby times. -/
theorem eventually_jet_mem {u : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hu : DifferentiableOn ℂ u (verticalStrip σ R)) {S : Set (Fin (n + 1) → ℂ)} (hSopen : IsOpen S)
    {t : ℝ} (ht : (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) u ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S) :
    ∀ᶠ s : ℝ in nhds t, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) u ((σ : ℂ) + (s : ℂ) * Complex.I)) ∈ S := by
  have hcont : Continuous fun s : ℝ => (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) u ((σ : ℂ) + (s : ℂ) * Complex.I)) :=
    continuous_pi fun k => continuous_jet_line hR hu (k : ℕ)
  exact hcont.continuousAt (hSopen.mem_nhds ht)

/-- **Finite phase rank from a regular jet atlas on the carrier.**  If every carrier point has a
holomorphic representative solving the relation, and each is regular in one of finitely many
regularity regions, each attached to a sample time, the rational frequency rank is at most
`2 |T| (n+1)`. -/
theorem rank_le_of_regular_jets (hρ : 0 < ρ) (hrpos : 0 < r)
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
    {L : ι → (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ι → ℝ} {T : Finset ι}
    (hSopen : ∀ i, IsOpen (S i)) (hSconv : ∀ i, Convex ℝ (S i))
    (hPd : ∀ i, ∀ y ∈ S i, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) (S i) y)
    (hC : ∀ i, 0 ≤ C i) (hbnd : ∀ i, ∀ y ∈ S i, ‖P' y - L i‖ ≤ C i)
    (hdom : ∀ i, C i < ‖partialCoeff (L i) (Fin.last n)‖)
    (hrelrep : ∀ (x : BohrHull f) (s : ℝ), P (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (s : ℂ) * Complex.I)) = 0)
    (hatlas : ∀ x : BohrHull f, ∃ i ∈ T, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I)) ∈ S i) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((2 * (T.card * (n + 1)) : ℕ) : Cardinal) := by
  classical
  have hrρ : r < r + ρ := by linarith
  have hstripsub : verticalStrip σ r ⊆ verticalStrip σ (r + ρ) := by
    intro z hz
    show |z.re - σ| < r + ρ
    have : |z.re - σ| < r := hz
    linarith
  set J : ι → BohrHull f → (Fin (n + 1) → ℂ) := fun i x => fun k : Fin (n + 1) =>
    iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I) with hJ
  set U : ι → Set (BohrHull f) := fun i => {x | J i x ∈ S i} with hU
  refine rank_le_of_jetAtlas hfu hftb (J := J) (U := U) (fun i => ?_) (fun x => ?_)
    (fun i x y hx hxy => ?_)
  · exact continuous_pi fun k =>
      continuous_jet_of_representatives hρ hrpos hrρ hν hrepdiff hrepval (k : ℕ) (τ i)
  · obtain ⟨i, hiT, hiS⟩ := hatlas x
    exact ⟨i, hiT, hiS⟩
  · -- separation at a regular sample time
    have hxS : J i x ∈ S i := hx
    have hyS : J i y ∈ S i := by
      rw [← hxy]
      exact hxS
    have hxev : ∀ᶠ s : ℝ in nhds (τ i), (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (s : ℂ) * Complex.I)) ∈ S i :=
      eventually_jet_mem (by linarith) (hrepdiff x) (hSopen i) hxS
    have hyev : ∀ᶠ s : ℝ in nhds (τ i), (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (rep y) ((σ : ℂ) + (s : ℂ) * Complex.I)) ∈ S i :=
      eventually_jet_mem (by linarith) (hrepdiff y) (hSopen i) hyS
    refine carrier_eq_of_jet_eq_local hrpos hfu hn ((hrepdiff x).mono hstripsub)
      ((hrepdiff y).mono hstripsub) (hSconv i) (hPd i) (hC i) (hbnd i) (hdom i)
      hxev (Filter.Eventually.of_forall (hrelrep x)) hyev
      (Filter.Eventually.of_forall (hrelrep y)) (fun k => ?_) (hrepline x) (hrepline y)
    have h := congrFun hxy k.castSucc
    exact h

end GaloisForLFunctions
