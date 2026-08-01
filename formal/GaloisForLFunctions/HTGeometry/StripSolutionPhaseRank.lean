import GaloisForLFunctions.HTGeometry.PhaseRankCapstone
import GaloisForLFunctions.HTGeometry.LineStripCarrier
import GaloisForLFunctions.HTGeometry.StripRelationPropagation

/-!
# The phase rank of a strip almost periodic solution

All the carrier plumbing of the phase-rank bound is determined by the function itself: the vertical
translates of a strip almost periodic holomorphic function form a bounded almost periodic curve in
the sup-norm space of a substrip, the line carrier embeds in the strip carrier, and every carrier
point has a holomorphic representative that solves the same relation.

So the rank bound needs only the function, its relation, and a regularity region valid for *every*
holomorphic solution of the relation on the substrip.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {F : ℂ → ℂ} {σ R r ρ : ℝ} {n : ℕ}

/-- **The carrier of a strip almost periodic solution carries holomorphic representatives.**  The
vertical translates form a bounded almost periodic curve in the sup-norm space of the substrip, the
line carrier embeds in the strip carrier, and each carrier point has a holomorphic representative
that agrees with the carrier evaluation and solves the same relation. -/
theorem exists_carrier_representatives (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x))
    {m : ℕ} {P : (Fin m → ℂ) → ℂ} (hPcont : Continuous P)
    (hrel : ∀ z ∈ verticalStrip σ R, P (fun k : Fin m => iteratedDeriv (k : ℕ) F z) = 0) :
    ∃ (Gb : ℝ →ᵇ ((closedStrip σ (r + ρ)) →ᵇ ℂ)) (ν : BohrHull f → BohrHull Gb)
      (rep : BohrHull f → (ℂ → ℂ)), Continuous ν ∧
        (∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ (r + ρ))) ∧
        (∀ (x : BohrHull f) (z : closedStrip σ (r + ρ)), rep x (z : ℂ) = bohrEval Gb (ν x) z) ∧
        (∀ (x : BohrHull f) (t : ℝ),
          rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t)) ∧
        ∀ x, ∀ z ∈ verticalStrip σ (r + ρ),
          P (fun k : Fin m => iteratedDeriv (k : ℕ) (rep x) z) = 0 := by
  classical
  set r₂ : ℝ := (r + ρ + R) / 2 with hr₂def
  have hr₂ : r + ρ < r₂ := by rw [hr₂def]; linarith
  have hr₂R : r₂ < R := by rw [hr₂def]; linarith
  have hrρ0 : 0 ≤ r + ρ := by linarith
  -- a uniform bound on a slightly larger closed strip
  have hcontOn : ContinuousOn F (closedStrip σ r₂) :=
    (hF.mono (closedStrip_subset_verticalStrip hr₂R)).continuousOn
  obtain ⟨M0, hM0⟩ := exists_bound_of_isStripAlmostPeriodicOn hcontOn (hap r₂ hr₂R)
  set M : ℝ := max M0 1 with hMdef
  have hMpos : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hbound : ∀ z ∈ closedStrip σ r₂, ‖F z‖ ≤ M := fun z hz =>
    le_trans (hM0 z hz) (le_max_left _ _)
  have hsubstrip : closedStrip σ (r + ρ) ⊆ closedStrip σ r₂ := fun z hz =>
    le_trans hz (le_of_lt hr₂)
  -- the translate curve as a bounded continuous map into the strip sup-norm space
  obtain ⟨G, hGval, hGcont, -⟩ := exists_strip_curve (r := r + ρ) hrρ hF hap
  have hGnorm : ∀ t : ℝ, ‖G t‖ ≤ M := by
    intro t
    refine (BoundedContinuousFunction.norm_le hMpos.le).mpr fun z => ?_
    rw [hGval t z]
    exact hbound _ (hsubstrip (mem_closedStrip_add_I σ (r + ρ) (z : ℂ) z.2 t))
  set Gb : ℝ →ᵇ ((closedStrip σ (r + ρ)) →ᵇ ℂ) :=
    BoundedContinuousFunction.mkOfBound ⟨G, hGcont⟩ (2 * M) (by
      intro x y
      have := dist_le_norm_add_norm (G x) (G y)
      have hx := hGnorm x
      have hy := hGnorm y
      simp only [ContinuousMap.coe_mk]
      linarith) with hGbdef
  have hGb : ∀ (t : ℝ) (z : closedStrip σ (r + ρ)), Gb t z = F ((z : ℂ) + (t : ℂ) * Complex.I) :=
    fun t z => hGval t z
  -- the carrier map from the line to the strip
  obtain ⟨ν, hνcont, -, hνι⟩ :=
    exists_injective_line_to_strip hrρ0 hr₂ hr₂R hMpos hF hbound hf hGb
  -- holomorphic representatives of the carrier points
  choose rep hrepdiff hrepval hrepline hrelrep using fun x : BohrHull f =>
    exists_holomorphic_rep hrρ hrρ0 hF hPcont hrel hfu hf hGb hνcont hνι x
  exact ⟨Gb, ν, rep, hνcont, hrepdiff, hrepval, hrepline, hrelrep⟩

/-- **The phase rank of a strip almost periodic solution of a differential relation.**  If every
holomorphic solution of the relation on the substrip has a regular jet at one of finitely many sample
times, the rational Bohr frequency rank of the line restriction is at most `2 |T| (n+1)`. -/
theorem rank_le_of_strip_solution (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hn : 0 < n) {P : (Fin (n + 1) → ℂ) → ℂ} (hPcont : Continuous P)
    (hrel : ∀ z ∈ verticalStrip σ R, P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) F z) = 0)
    {P' : (Fin (n + 1) → ℂ) → ((Fin (n + 1) → ℂ) →L[ℂ] ℂ)}
    {ι : Type*} {τ : ι → ℝ} {S : ι → Set (Fin (n + 1) → ℂ)}
    {L : ι → (Fin (n + 1) → ℂ) →L[ℂ] ℂ} {C : ι → ℝ} {T : Finset ι}
    (hSopen : ∀ i, IsOpen (S i)) (hSconv : ∀ i, Convex ℝ (S i))
    (hPd : ∀ i, ∀ y ∈ S i, HasFDerivWithinAt P ((P' y).restrictScalars ℝ) (S i) y)
    (hC : ∀ i, 0 ≤ C i) (hbnd : ∀ i, ∀ y ∈ S i, ‖P' y - L i‖ ≤ C i)
    (hdom : ∀ i, C i < ‖partialCoeff (L i) (Fin.last n)‖)
    (hatlas : ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (verticalStrip σ (r + ρ)) →
      (∀ z ∈ verticalStrip σ (r + ρ), P (fun k : Fin (n + 1) => iteratedDeriv (k : ℕ) g z) = 0) →
      ∃ i ∈ T, (fun k : Fin (n + 1) =>
        iteratedDeriv (k : ℕ) g ((σ : ℂ) + ((τ i : ℝ) : ℂ) * Complex.I)) ∈ S i) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((2 * (T.card * (n + 1)) : ℕ) : Cardinal) := by
  obtain ⟨Gb, ν, rep, hνcont, hrepdiff, hrepval, hrepline, hrelrep⟩ :=
    exists_carrier_representatives hr hρ hrρ hF hap hf hfu hPcont hrel
  refine rank_le_of_regular_jets (τ := τ) hρ hr hfu hftb hνcont hrepdiff hrepval hrepline hn
    hSopen hSconv hPd hC hbnd hdom (fun x s => ?_) (fun x => ?_)
  · exact hrelrep x _ (mem_verticalStrip_line (by linarith) σ s)
  · exact hatlas (rep x) (hrepdiff x) (hrelrep x)

end GaloisForLFunctions
