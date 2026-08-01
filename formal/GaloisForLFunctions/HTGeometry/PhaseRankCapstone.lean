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
holomorphic representative solving the relation, and each is regular at one of finitely many sample
times, the rational frequency rank is at most `2 m (n+1)`. -/
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
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)} {S : ℝ → Set (Fin (n + 1) → ℂ)}
    {L : ℝ → (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ℝ → ℝ} {T : Finset ℝ}
    (hSopen : ∀ t, IsOpen (S t)) (hSconv : ∀ t, Convex ℝ (S t))
    (hPd : ∀ t, ∀ y ∈ S t, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) (S t) y)
    (hC : ∀ t, 0 ≤ C t) (hbnd : ∀ t, ∀ y ∈ S t, ‖P' y - L t‖ ≤ C t)
    (hdom : ∀ t, C t < ‖partialCoeff (L t) (Fin.last n)‖)
    (hrelrep : ∀ (x : BohrHull f) (s : ℝ), P (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (s : ℂ) * Complex.I)) = 0)
    (hatlas : ∀ x : BohrHull f, ∃ t ∈ T, (fun k : Fin (n + 1) =>
      iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I)) ∈ S t) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((2 * (T.card * (n + 1)) : ℕ) : Cardinal) := by
  classical
  have hrρ : r < r + ρ := by linarith
  have hstripsub : verticalStrip σ r ⊆ verticalStrip σ (r + ρ) := by
    intro z hz
    show |z.re - σ| < r + ρ
    have : |z.re - σ| < r := hz
    linarith
  set J : ℝ → BohrHull f → (Fin (n + 1) → ℂ) := fun t x => fun k : Fin (n + 1) =>
    iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (t : ℂ) * Complex.I) with hJ
  set U : ℝ → Set (BohrHull f) := fun t => {x | J t x ∈ S t} with hU
  refine rank_le_of_jetAtlas hfu hftb (J := J) (U := U) (fun t => ?_) (fun x => ?_)
    (fun t x y hx hxy => ?_)
  · exact continuous_pi fun k =>
      continuous_jet_of_representatives hρ hrpos hrρ hν hrepdiff hrepval (k : ℕ) t
  · obtain ⟨t, htT, htS⟩ := hatlas x
    exact ⟨t, htT, htS⟩
  · -- separation at a regular sample time
    have hxS : J t x ∈ S t := hx
    have hyS : J t y ∈ S t := by
      rw [← hxy]
      exact hxS
    have hxev : ∀ᶠ s : ℝ in nhds t, (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (rep x) ((σ : ℂ) + (s : ℂ) * Complex.I)) ∈ S t :=
      eventually_jet_mem (by linarith) (hrepdiff x) (hSopen t) hxS
    have hyev : ∀ᶠ s : ℝ in nhds t, (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) (rep y) ((σ : ℂ) + (s : ℂ) * Complex.I)) ∈ S t :=
      eventually_jet_mem (by linarith) (hrepdiff y) (hSopen t) hyS
    refine carrier_eq_of_jet_eq_local hrpos hfu hn ((hrepdiff x).mono hstripsub)
      ((hrepdiff y).mono hstripsub) (hSconv t) (hPd t) (hC t) (hbnd t) (hdom t)
      hxev (Filter.Eventually.of_forall (hrelrep x)) hyev
      (Filter.Eventually.of_forall (hrelrep y)) (fun k => ?_) (hrepline x) (hrepline y)
    have h := congrFun hxy k.castSucc
    exact h

end GaloisForLFunctions
