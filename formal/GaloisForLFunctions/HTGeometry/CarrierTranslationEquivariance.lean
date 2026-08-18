import GaloisForLFunctions.HTGeometry.CarrierRepresentative
import GaloisForLFunctions.HTGeometry.LineJetTransfer

/-!
# Translation equivariance on the carrier

The carrier is a topological group in which the line is dense, so the translates of any single point
by the line are dense: a continuous function constant along them is constant.

The representative of a translated carrier point agrees on the central line with the translate of the
representative, hence on the whole strip, so the jets of the representatives are translation
equivariant.  The representative of the origin has the jets of the function itself.

Together these turn a statement about one point of the line into a statement about every point of the
carrier.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {E : Type*} [NormedAddCommGroup E] {σ R : ℝ}

/-- The translates of one carrier point by the line are dense in the carrier. -/
theorem denseRange_bohrIota_add (f : ℝ →ᵇ E) (x : BohrHull f) :
    DenseRange (fun t : ℝ => x + bohrIota f t) := by
  have hcont : Continuous (fun y : BohrHull f => x + y) := continuous_const.add continuous_id
  have hdense : DenseRange (fun y : BohrHull f => x + y) := by
    intro z
    have : z = x + (-x + z) := by abel
    rw [this]
    exact subset_closure ⟨-x + z, rfl⟩
  exact hdense.comp (denseRange_bohrIota f) hcont

/-- A continuous function on the carrier that is constant along the translates of one point is
constant. -/
theorem eq_of_eqOn_translates {α : Type*} [TopologicalSpace α] [T2Space α] {f : ℝ →ᵇ E}
    {ψ : BohrHull f → α} (hψ : Continuous ψ) {x : BohrHull f} {c : α}
    (h : ∀ t : ℝ, ψ (x + bohrIota f t) = c) (y : BohrHull f) : ψ y = c := by
  refine congrFun (Continuous.ext_on (denseRange_bohrIota_add f x) hψ continuous_const ?_) y
  rintro z ⟨t, rfl⟩
  exact h t

/-- Iterated derivatives of functions agreeing on an open set agree there. -/
theorem eqOn_iteratedDeriv_of_eqOn {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [CompleteSpace E'] {g h : ℂ → E'} {U : Set ℂ} (hU : IsOpen U)
    (hgh : Set.EqOn g h U) : ∀ k : ℕ, Set.EqOn (iteratedDeriv k g) (iteratedDeriv k h) U := by
  intro k
  induction k with
  | zero =>
      intro z hz
      simpa [iteratedDeriv_zero] using hgh hz
  | succ j ih =>
      intro z hz
      have hev : iteratedDeriv j g =ᶠ[nhds z] iteratedDeriv j h :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hz) ih
      rw [iteratedDeriv_succ, iteratedDeriv_succ, hev.deriv_eq]

variable [NormedSpace ℂ E] [CompleteSpace E] {f : ℝ →ᵇ E} {r : ℝ}

/-- A vertical strip is invariant under vertical translation. -/
theorem mem_verticalStrip_add_I {z : ℂ} (hz : z ∈ verticalStrip σ r) (s : ℝ) :
    z + (s : ℂ) * Complex.I ∈ verticalStrip σ r := by
  have hre : (z + (s : ℂ) * Complex.I).re = z.re := by simp
  show |(z + (s : ℂ) * Complex.I).re - σ| < r
  rw [hre]
  exact hz

/-- **Representatives are translation equivariant.**  The representative of a translated carrier
point is the translate of the representative. -/
theorem rep_translate_eqOn (hr : 0 < r) {rep : BohrHull f → (ℂ → E)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ r))
    (hrepline : ∀ (x : BohrHull f) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t))
    (x : BohrHull f) (s : ℝ) :
    Set.EqOn (rep (x + bohrIota f s)) (fun z => rep x (z + (s : ℂ) * Complex.I))
      (verticalStrip σ r) := by
  refine eqOn_of_eqOn_line hr (hrepdiff _) ?_ ?_
  · exact DifferentiableOn.comp (hrepdiff x)
      ((differentiable_id.add_const _).differentiableOn) fun z hz => mem_verticalStrip_add_I hz s
  · intro t
    rw [hrepline (x + bohrIota f s) t]
    have hz : (σ : ℂ) + (t : ℂ) * Complex.I + (s : ℂ) * Complex.I
        = (σ : ℂ) + ((t + s : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    show bohrEval f (x + bohrIota f s + bohrIota f t)
      = rep x ((σ : ℂ) + (t : ℂ) * Complex.I + (s : ℂ) * Complex.I)
    rw [hz, hrepline x (t + s), bohrIota_add]
    congr 1
    abel

/-- The jets of the representatives are translation equivariant along the line. -/
theorem iteratedDeriv_rep_translate (hr : 0 < r) {rep : BohrHull f → (ℂ → E)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ r))
    (hrepline : ∀ (x : BohrHull f) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t))
    (x : BohrHull f) (s : ℝ) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (rep (x + bohrIota f s)) ((σ : ℂ) + (t : ℂ) * Complex.I)
      = iteratedDeriv k (rep x) ((σ : ℂ) + ((s + t : ℝ) : ℂ) * Complex.I) := by
  have h1 := eqOn_iteratedDeriv_of_eqOn (isOpen_verticalStrip σ r)
    (rep_translate_eqOn hr hrepdiff hrepline x s) k (mem_verticalStrip_line hr σ t)
  rw [h1]
  have h2 := congrFun (iteratedDeriv_comp_add_const k (rep x) ((s : ℂ) * Complex.I))
    ((σ : ℂ) + (t : ℂ) * Complex.I)
  rw [h2]
  congr 1
  push_cast
  ring

/-- The representative of the origin of the carrier has the jets of the function itself. -/
theorem iteratedDeriv_rep_zero {F : ℂ → E} (hr : 0 < r)
    (hF : DifferentiableOn ℂ F (verticalStrip σ r))
    (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    {rep : BohrHull f → (ℂ → E)}
    (hrepdiff : ∀ x, DifferentiableOn ℂ (rep x) (verticalStrip σ r))
    (hrepline : ∀ (x : BohrHull f) (t : ℝ),
      rep x ((σ : ℂ) + (t : ℂ) * Complex.I) = bohrEval f (x + bohrIota f t))
    (k : ℕ) (t : ℝ) :
    iteratedDeriv k (rep 0) ((σ : ℂ) + (t : ℂ) * Complex.I)
      = iteratedDeriv k F ((σ : ℂ) + (t : ℂ) * Complex.I) := by
  refine eqOn_iteratedDeriv_of_eqOn (isOpen_verticalStrip σ r)
    (eqOn_of_eqOn_line hr (hrepdiff 0) hF fun s => ?_) k (mem_verticalStrip_line hr σ t)
  rw [hrepline 0 s, zero_add, bohrEval_bohrIota, hf s]

end GaloisForLFunctions
