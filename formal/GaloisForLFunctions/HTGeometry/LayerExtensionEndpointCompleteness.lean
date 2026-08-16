import GaloisForLFunctions.HTGeometry.EndpointProbeTransitionCriterion
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The attached qubit sees every old transition

Attaching a qubit to a simple old spectrum splits every old level in two.  At zero edge coupling
the eigenvectors are products, so the new endpoint sees only pairs inside one old level: the
reduced transition over the old factor vanishes for every pair of distinct old levels.

Switching on the edge coupling repairs this at first order.  The reduced transition entry at the
*flipped* new index has vanishing value and nonvanishing derivative, with leading coefficient
proportional to the old endpoint matrix element of the coupling.  So an old endpoint probe that
sees an old pair makes the new endpoint see the corresponding split pair for all small nonzero
coupling.

The entry at the *unflipped* index has vanishing first-order term, so the flip is forced.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- The reduced transition over the *old* factor of a split index; the surviving factor is the
attached qubit. -/
def layerReducedTransition (ψ φ : A × Bool → ℂ) : Matrix Bool Bool ℂ :=
  Matrix.of fun s r => ∑ α, φ (α, s) * (starRingEnd ℂ) (ψ (α, r))

omit [DecidableEq A] in
theorem layerReducedTransition_eq_reducedTransition (ψ φ : A × Bool → ℂ) :
    layerReducedTransition ψ φ = reducedTransition (ψ ∘ Prod.swap) (φ ∘ Prod.swap) := rfl

/-! ## Two elementary nonvanishing criteria -/

theorem eventually_ne_zero_of_hasDerivAt_zero {F : ℝ → ℂ} {c : ℂ}
    (hF : HasDerivAt F c 0) (h0 : F 0 = 0) (hc : c ≠ 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), F t ≠ 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hF
  have hne := hF.eventually_ne hc
  filter_upwards [hne, self_mem_nhdsWithin] with t ht _
  intro hFt
  apply ht
  simp [slope, h0, hFt]

theorem eventually_ne_zero_of_continuousAt_zero {F : ℝ → ℂ} (hF : ContinuousAt F 0)
    (h0 : F 0 ≠ 0) : ∀ᶠ t in 𝓝 (0 : ℝ), F t ≠ 0 := hF.eventually_ne h0

theorem continuousAt_finsetSum {ι P : Type*} [Fintype ι] [TopologicalSpace P] (f : ι → P → ℂ)
    (x : P) (h : ∀ i, ContinuousAt (f i) x) : ContinuousAt (fun t => ∑ i, f i t) x := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => exact continuousAt_const
  | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (h a).add ih

/-! ## The split pair inside one old level -/

/-- At zero coupling the attached qubit already sees the two halves of one old level, so it still
does for all small coupling. -/
theorem eventually_layerReducedTransition_ne_zero_sameLevel
    {ψ φ : ℝ → A × Bool → ℂ} {α₀ : A} {r₀ s₀ : Bool} {Pi Pi' : ℂ}
    (hPi : Pi ≠ 0) (hPi' : Pi' ≠ 0)
    (hψ0 : ∀ y, ψ 0 y = if y = (α₀, r₀) then Pi else 0)
    (hφ0 : ∀ y, φ 0 y = if y = (α₀, s₀) then Pi' else 0)
    (hψc : ∀ y, ContinuousAt (fun t => ψ t y) 0)
    (hφc : ∀ y, ContinuousAt (fun t => φ t y) 0) :
    ∀ᶠ t in 𝓝 (0 : ℝ), layerReducedTransition (ψ t) (φ t) ≠ 0 := by
  classical
  set F : ℝ → ℂ := fun t => ∑ α, φ t (α, s₀) * (starRingEnd ℂ) (ψ t (α, r₀)) with hFdef
  have hcont : ContinuousAt F 0 := by
    refine continuousAt_finsetSum _ _ fun α => ?_
    exact (hφc (α, s₀)).mul (Complex.continuous_conj.continuousAt.comp (hψc (α, r₀)))
  have hval : F 0 = Pi' * (starRingEnd ℂ) Pi := by
    rw [hFdef]
    simp only
    rw [Finset.sum_eq_single α₀]
    · rw [hψ0 (α₀, r₀), hφ0 (α₀, s₀)]
      simp
    · intro α _ hα
      rw [hφ0 (α, s₀)]
      have : ¬ ((α, s₀) = (α₀, s₀)) := by simp [hα]
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ α₀) h
  have hne : F 0 ≠ 0 := by
    rw [hval]
    exact mul_ne_zero hPi' (by simpa using hPi)
  filter_upwards [eventually_ne_zero_of_continuousAt_zero hcont hne] with t ht
  intro hzero
  apply ht
  have := congrFun (congrFun hzero s₀) r₀
  simpa [hFdef, layerReducedTransition] using this

/-! ## The split pair across two old levels -/

/-- **First-order creation of the new endpoint transition.**  For two distinct old levels the
reduced transition vanishes at zero coupling but its flipped entry has nonzero derivative, with
leading coefficient the old endpoint matrix element.  Hence the attached qubit sees the pair for
all small nonzero coupling. -/
theorem eventually_layerReducedTransition_ne_zero
    {ψ φ : ℝ → A × Bool → ℂ} {Dψ Dφ : A × Bool → ℂ}
    {α₀ β₀ : A} {r₀ s₀ : Bool} {Pi Pi' : ℂ} (hPi' : Pi' ≠ 0)
    (hψ0 : ∀ y, ψ 0 y = if y = (α₀, r₀) then Pi else 0)
    (hφ0 : ∀ y, φ 0 y = if y = (β₀, s₀) then Pi' else 0)
    (hψd : ∀ y, HasDerivAt (fun t => ψ t y) (Dψ y) 0)
    (hφd : ∀ y, HasDerivAt (fun t => φ t y) (Dφ y) 0)
    (hkey : Dψ (β₀, !r₀) ≠ 0) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), layerReducedTransition (ψ t) (φ t) ≠ 0 := by
  classical
  -- the entry of interest
  set G : ℝ → ℂ := fun t => ∑ α, φ t (α, s₀) * (starRingEnd ℂ) (ψ t (α, !r₀)) with hGdef
  -- the old half of every product vanishes at zero coupling
  have hψzero : ∀ α : A, ψ 0 (α, !r₀) = 0 := by
    intro α
    rw [hψ0 (α, !r₀)]
    have : ¬ ((α, !r₀) = (α₀, r₀)) := by
      intro hc
      exact (Bool.not_ne_self r₀) (congrArg Prod.snd hc)
    simp [this]
  have hG0 : G 0 = 0 := by
    rw [hGdef]
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [hψzero α]
    simp
  -- the derivative of the entry
  have hterm : ∀ α : A, HasDerivAt (fun t => φ t (α, s₀) * (starRingEnd ℂ) (ψ t (α, !r₀)))
      (Dφ (α, s₀) * (starRingEnd ℂ) (ψ 0 (α, !r₀))
        + φ 0 (α, s₀) * (starRingEnd ℂ) (Dψ (α, !r₀))) 0 := by
    intro α
    have hstar : HasDerivAt (fun t => (starRingEnd ℂ) (ψ t (α, !r₀)))
        ((starRingEnd ℂ) (Dψ (α, !r₀))) 0 := by
      simpa using (hψd (α, !r₀)).star
    exact (hφd (α, s₀)).mul hstar
  have hfun : (∑ α : A, fun t => φ t (α, s₀) * (starRingEnd ℂ) (ψ t (α, !r₀)))
      = fun t => ∑ α, φ t (α, s₀) * (starRingEnd ℂ) (ψ t (α, !r₀)) := by
    funext t
    rw [Finset.sum_apply]
  have hGd : HasDerivAt G (∑ α : A, (Dφ (α, s₀) * (starRingEnd ℂ) (ψ 0 (α, !r₀))
      + φ 0 (α, s₀) * (starRingEnd ℂ) (Dψ (α, !r₀)))) 0 := by
    have hsum : HasDerivAt (∑ α : A, fun t => φ t (α, s₀) * (starRingEnd ℂ) (ψ t (α, !r₀)))
        (∑ α : A, (Dφ (α, s₀) * (starRingEnd ℂ) (ψ 0 (α, !r₀))
          + φ 0 (α, s₀) * (starRingEnd ℂ) (Dψ (α, !r₀)))) 0 :=
      HasDerivAt.sum fun α _ => hterm α
    rw [hfun] at hsum
    exact hsum
  -- and its value
  have hc : (∑ α : A, (Dφ (α, s₀) * (starRingEnd ℂ) (ψ 0 (α, !r₀))
      + φ 0 (α, s₀) * (starRingEnd ℂ) (Dψ (α, !r₀))))
      = Pi' * (starRingEnd ℂ) (Dψ (β₀, !r₀)) := by
    have hsimp : ∀ α : A, (Dφ (α, s₀) * (starRingEnd ℂ) (ψ 0 (α, !r₀))
        + φ 0 (α, s₀) * (starRingEnd ℂ) (Dψ (α, !r₀)))
        = φ 0 (α, s₀) * (starRingEnd ℂ) (Dψ (α, !r₀)) := by
      intro α
      rw [hψzero α]
      simp
    rw [Finset.sum_congr rfl fun α _ => hsimp α, Finset.sum_eq_single β₀]
    · rw [hφ0 (β₀, s₀)]
      simp
    · intro α _ hα
      rw [hφ0 (α, s₀)]
      have : ¬ ((α, s₀) = (β₀, s₀)) := by simp [hα]
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ β₀) h
  rw [hc] at hGd
  have hcne : Pi' * (starRingEnd ℂ) (Dψ (β₀, !r₀)) ≠ 0 :=
    mul_ne_zero hPi' (by simpa using hkey)
  filter_upwards [eventually_ne_zero_of_hasDerivAt_zero hGd hG0 hcne] with t ht
  intro hzero
  apply ht
  have := congrFun (congrFun hzero s₀) (!r₀)
  simpa [hGdef, layerReducedTransition] using this

/-! ## Endpoint completeness is an open condition -/

/-- **Endpoint completeness is open.**  If the eigenvector family depends continuously on a
parameter and every ordered pair is seen at one point, every ordered pair is seen on a whole
neighbourhood. -/
theorem eventually_forall_layerReducedTransition_ne_zero
    {P : Type*} [TopologicalSpace P] {p₀ : P}
    (ψ : (A × Bool) → P → (A × Bool → ℂ))
    (hcont : ∀ i y, ContinuousAt (fun p => ψ i p y) p₀)
    (hne : ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition (ψ q.1 p₀) (ψ q.2 p₀) ≠ 0) :
    ∀ᶠ p in 𝓝 p₀, ∀ q : (A × Bool) × (A × Bool), q.1 ≠ q.2 →
      layerReducedTransition (ψ q.1 p) (ψ q.2 p) ≠ 0 := by
  classical
  refine Filter.eventually_all.mpr fun q => ?_
  by_cases hq : q.1 = q.2
  · filter_upwards with p hcon
    exact absurd hq hcon
  obtain ⟨s, r, hsr⟩ : ∃ s r, layerReducedTransition (ψ q.1 p₀) (ψ q.2 p₀) s r ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hne q hq (by ext s r; simpa using hcon s r)
  have hc : ContinuousAt (fun p => layerReducedTransition (ψ q.1 p) (ψ q.2 p) s r) p₀ := by
    simp only [layerReducedTransition, Matrix.of_apply]
    refine continuousAt_finsetSum _ _ fun α => ?_
    exact (hcont q.2 (α, s)).mul (Complex.continuous_conj.continuousAt.comp (hcont q.1 (α, r)))
  filter_upwards [hc.eventually_ne hsr] with p hp _
  intro hzero
  apply hp
  have hval := congrFun (congrFun hzero s) r
  simpa [layerReducedTransition] using hval

end

end GaloisForLFunctions.HTGeometry
