import GaloisForLFunctions.HTGeometry.MomentHankelStrict

/-!
# Strict Hankel geometry under an observable pushforward

A positive measure may live on an arbitrary measurable hidden space while the reporter sees only
one real observable `node`.  Pushing the measure through that reporter turns the observed powers
into an ordinary moment sequence.  If the reporter retains positive mass outside every finite set
of reported values, every finite Hankel block is strictly positive definite.

This is the measure-theoretic form of the project's observability principle: strictness is a
property of the reported palette, not of an assumed temporal evolution on the hidden space.
-/

open Set MeasureTheory

namespace HTGeometry

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- The positive measure seen through a real-valued reporter. -/
def observablePushforwardMeasure (mu : Measure X) (node : X → ℝ) : Measure ℝ :=
  mu.map node

/-- Integration of a reported power against the pushforward is integration of the same reported
power on the hidden space. -/
theorem integral_pow_observablePushforwardMeasure
    (mu : Measure X) {node : X → ℝ} (hnode : Measurable node) (n : ℕ) :
    ∫ y, y ^ n ∂observablePushforwardMeasure mu node =
      ∫ x, node x ^ n ∂mu := by
  rw [observablePushforwardMeasure]
  rw [show (fun y : ℝ => y ^ n) = id ^ n by
      funext y
      simp only [Pi.pow_apply, id_eq],
    show (fun x => node x ^ n) = (id ^ n) ∘ node by
      funext x
      simp only [Function.comp_apply, Pi.pow_apply, id_eq]]
  exact integral_map_of_stronglyMeasurable (μ := mu) hnode
    ((continuous_id.pow n).stronglyMeasurable :
      StronglyMeasurable (fun y : ℝ ↦ y ^ n))

/-- Integrability of every reported power transports to the pushforward measure. -/
theorem integrable_pow_observablePushforwardMeasure
    (mu : Measure X) {node : X → ℝ} (hnode : Measurable node) {n : ℕ}
    (hint : Integrable (fun x ↦ node x ^ n) mu) :
    Integrable (fun y : ℝ ↦ y ^ n) (observablePushforwardMeasure mu node) := by
  rw [observablePushforwardMeasure]
  apply (integrable_map_measure (μ := mu) (f := node) (g := fun y : ℝ ↦ y ^ n)
    (continuous_id.pow n).aestronglyMeasurable hnode.aemeasurable).2
  rw [show (fun y : ℝ => y ^ n) ∘ node = (fun x => node x ^ n) by
    funext x
    rfl]
  exact hint

/-- Positive mass outside every finite reported palette becomes ordinary infinite support after
pushforward. -/
theorem observablePushforwardMeasure_infiniteSupport
    (mu : Measure X) {node : X → ℝ} (hnode : Measurable node)
    (hinf : ∀ F : Finset ℝ, 0 < mu {x | node x ∉ F})
    (F : Finset ℝ) :
    0 < observablePushforwardMeasure mu node {y : ℝ | y ∉ F} := by
  rw [observablePushforwardMeasure]
  change 0 < (Measure.map node mu) ((↑F : Set ℝ)ᶜ)
  rw [Measure.map_apply hnode F.measurableSet.compl]
  rw [show node ⁻¹' (↑F : Set ℝ)ᶜ = {x | node x ∉ F} by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe, Set.mem_setOf_eq]]
  exact hinf F

/-- Infinite support of a reported pushforward forces infinite support of the hidden measure.
No injectivity is needed: the image of every finite hidden palette is still finite. -/
theorem infiniteSupport_of_observablePushforwardMeasure
    (mu : Measure X) {node : X → ℝ} (hnode : Measurable node)
    (hinf : ∀ G : Finset ℝ,
      0 < observablePushforwardMeasure mu node {y : ℝ | y ∉ G}) :
    ∀ F : Finset X, 0 < mu {x : X | x ∉ F} := by
  intro F
  classical
  let G : Finset ℝ := F.image node
  have hG := hinf G
  rw [observablePushforwardMeasure] at hG
  change 0 < (Measure.map node mu) ((↑G : Set ℝ)ᶜ) at hG
  rw [Measure.map_apply hnode G.measurableSet.compl] at hG
  refine hG.trans_le (measure_mono ?_)
  intro x hx
  simp only [Set.mem_preimage, Set.mem_compl_iff, Finset.mem_coe,
    Set.mem_setOf_eq] at hx ⊢
  intro hxF
  exact hx (Finset.mem_image.mpr ⟨x, hxF, rfl⟩)

/-- **Observable-pushforward strict Hankel law.**  A continuum of reported values makes every
finite observed moment Hankel determinant positive. -/
theorem det_momentHankelMatrix_pos_of_observable_infiniteSupport
    (mu : Measure X) (node : X → ℝ) (hnode : Measurable node)
    (s : ℕ → ℝ) (hs : ∀ n, s n = ∫ x, node x ^ n ∂mu)
    (hint : ∀ n, Integrable (fun x ↦ node x ^ n) mu)
    (hinf : ∀ F : Finset ℝ, 0 < mu {x | node x ∉ F})
    (n : ℕ) :
    0 < (momentHankelMatrix s n).det := by
  let nu : Measure ℝ := observablePushforwardMeasure mu node
  have hmom : ∀ k, s k = ∫ y, y ^ k ∂nu := by
    intro k
    rw [hs k, show nu = observablePushforwardMeasure mu node by rfl,
      integral_pow_observablePushforwardMeasure mu hnode k]
  have hintnu : ∀ k, Integrable (fun y : ℝ ↦ y ^ k) nu := by
    intro k
    exact integrable_pow_observablePushforwardMeasure mu hnode (hint k)
  have hinfnu : ∀ F : Finset ℝ, 0 < nu {y : ℝ | y ∉ F} := by
    intro F
    exact observablePushforwardMeasure_infiniteSupport mu hnode hinf F
  exact det_momentHankelMatrix_pos_of_infiniteSupport s hmom hintnu hinfnu n

end

end HTGeometry
