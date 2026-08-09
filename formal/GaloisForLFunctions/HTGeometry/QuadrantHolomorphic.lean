import GaloisForLFunctions.HTGeometry.PrimeTangentSpace
import GaloisForLFunctions.HTGeometry.ContinuousMapLocallyConvex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Convex

/-!
# The critical quadrant and its holomorphic functions

The upper half of the critical strip

`Q₊ = {s : 1/2 < Re s < 1, Im s > 0}`

is open and convex.  Its holomorphic functions are carried as a real subspace of the continuous
functions on the subtype, a function being holomorphic when it is the restriction of a function
differentiable on `Q₊`; the witness avoids differentiability on a subtype and the subspace
properties are inherited from the witnesses.

The Euler unit tangents `u_p` live there.  On `Q₊` one has `|p^{-s}| = p^{-Re s} < 1`, and on the
reflected point `1 - s` one has `|p^{-(1-s)}| = p^{-(1-Re s)} < 1`, so both denominators
`(1 - p^{-s})²` are nonvanishing and the functional-equation-symmetrised tangent is holomorphic on
the whole quadrant.

* `HTGeometry.criticalQuadrant`, `HTGeometry.convex_criticalQuadrant`;
* `HTGeometry.holoQuadrant`;
* `HTGeometry.feEulerTangent`, `HTGeometry.feEulerTangent_mem_holoQuadrant`.
-/

open Complex

namespace HTGeometry

/-- The upper half of the critical strip. -/
def criticalQuadrant : Set ℂ := {s : ℂ | 1 / 2 < s.re ∧ s.re < 1 ∧ 0 < s.im}

@[simp] theorem mem_criticalQuadrant {s : ℂ} :
    s ∈ criticalQuadrant ↔ 1 / 2 < s.re ∧ s.re < 1 ∧ 0 < s.im := Iff.rfl

theorem isOpen_criticalQuadrant : IsOpen criticalQuadrant := by
  have h₁ : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h₂ : IsOpen {s : ℂ | s.re < 1} := isOpen_lt Complex.continuous_re continuous_const
  have h₃ : IsOpen {s : ℂ | 0 < s.im} := isOpen_lt continuous_const Complex.continuous_im
  have hEq : criticalQuadrant
      = {s : ℂ | 1 / 2 < s.re} ∩ ({s : ℂ | s.re < 1} ∩ {s : ℂ | 0 < s.im}) := by
    ext s
    simp [criticalQuadrant]
  rw [hEq]
  exact h₁.inter (h₂.inter h₃)

/-- **The critical quadrant is convex**, being an intersection of three half-planes. -/
theorem convex_criticalQuadrant : Convex ℝ criticalQuadrant := by
  have hEq : criticalQuadrant
      = {s : ℂ | 1 / 2 < s.re} ∩ ({s : ℂ | s.re < 1} ∩ {s : ℂ | 0 < s.im}) := by
    ext s
    simp [criticalQuadrant]
  rw [hEq]
  exact Convex.inter (convex_halfSpace_re_gt (1 / 2))
    (Convex.inter (convex_halfSpace_re_lt 1) (convex_halfSpace_im_gt 0))

instance : LocallyCompactSpace (criticalQuadrant : Set ℂ) :=
  isOpen_criticalQuadrant.locallyCompactSpace

/-- The real subspace of continuous functions on the quadrant that extend holomorphically. -/
def holoQuadrant : Submodule ℝ C((criticalQuadrant : Set ℂ), ℂ) where
  carrier := {f | ∃ F : ℂ → ℂ, DifferentiableOn ℂ F criticalQuadrant ∧
    ∀ z : (criticalQuadrant : Set ℂ), f z = F (z : ℂ)}
  add_mem' := by
    rintro f g ⟨F, hF, hf⟩ ⟨G, hG, hg⟩
    refine ⟨fun w => F w + G w, hF.add hG, fun z => ?_⟩
    simp [hf z, hg z]
  zero_mem' := ⟨fun _ => 0, differentiableOn_const 0, fun _ => rfl⟩
  smul_mem' := by
    rintro r f ⟨F, hF, hf⟩
    refine ⟨fun w => (r : ℂ) * F w, (differentiableOn_const (r : ℂ)).mul hF, fun z => ?_⟩
    simp [hf z, Complex.real_smul]

instance : ContinuousAdd (holoQuadrant) :=
  (inferInstance : IsTopologicalAddGroup (holoQuadrant)).toContinuousAdd

instance : ContinuousNeg (holoQuadrant) :=
  (inferInstance : IsTopologicalAddGroup (holoQuadrant)).toContinuousNeg

theorem mem_holoQuadrant_iff {f : C((criticalQuadrant : Set ℂ), ℂ)} :
    f ∈ holoQuadrant ↔ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F criticalQuadrant ∧
      ∀ z : (criticalQuadrant : Set ℂ), f z = F (z : ℂ) := Iff.rfl

/-- The prime Euler unit tangent, before symmetrisation. -/
noncomputable def eulerTangent (p : ℕ) (s : ℂ) : ℂ :=
  (Real.log p : ℂ) * (p : ℂ) ^ (-s) / (1 - (p : ℂ) ^ (-s)) ^ 2

/-- The functional-equation-symmetrised prime Euler unit tangent. -/
noncomputable def feEulerTangent (p : ℕ) (s : ℂ) : ℂ :=
  eulerTangent p s - eulerTangent p (1 - s)

theorem norm_prime_cpow_neg {p : ℕ} (hp : p.Prime) (s : ℂ) :
    ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have := Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)
  simpa using this

/-- On the quadrant the Euler denominator does not vanish. -/
theorem one_sub_prime_cpow_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlt : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_prime_cpow_neg hp s]
    have : (p : ℝ) ^ (-s.re) < (p : ℝ) ^ (0 : ℝ) := by
      refine Real.rpow_lt_rpow_of_exponent_lt hp1 ?_
      linarith
    simpa using this
  intro hcon
  have heq : (p : ℂ) ^ (-s) = 1 := by
    have := sub_eq_zero.mp hcon
    exact this.symm
  rw [heq, norm_one] at hlt
  exact lt_irrefl 1 hlt

theorem differentiableOn_eulerTangent {p : ℕ} (hp : p.Prime) :
    DifferentiableOn ℂ (eulerTangent p) {s : ℂ | 0 < s.re} := by
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hpow : DifferentiableOn ℂ (fun s : ℂ => (p : ℂ) ^ (-s)) {s : ℂ | 0 < s.re} :=
    (differentiable_neg.differentiableOn).const_cpow (Or.inl hp0)
  have hnum : DifferentiableOn ℂ
      (fun s : ℂ => (Real.log p : ℂ) * (p : ℂ) ^ (-s)) {s : ℂ | 0 < s.re} :=
    (differentiableOn_const _).mul hpow
  have hden : DifferentiableOn ℂ
      (fun s : ℂ => (1 - (p : ℂ) ^ (-s)) ^ 2) {s : ℂ | 0 < s.re} :=
    (((differentiableOn_const (1 : ℂ)).sub hpow)).pow 2
  intro s hs
  have hne : (1 - (p : ℂ) ^ (-s)) ^ 2 ≠ 0 :=
    pow_ne_zero 2 (one_sub_prime_cpow_ne_zero hp hs)
  exact (hnum s hs).div (hden s hs) hne

/-- **The symmetrised Euler tangent is holomorphic on the quadrant.** -/
theorem differentiableOn_feEulerTangent {p : ℕ} (hp : p.Prime) :
    DifferentiableOn ℂ (feEulerTangent p) criticalQuadrant := by
  have hsub : criticalQuadrant ⊆ {s : ℂ | 0 < s.re} := by
    intro s hs
    have := hs.1
    simp only [Set.mem_setOf_eq]
    linarith
  have hrefl : DifferentiableOn ℂ (fun s : ℂ => eulerTangent p (1 - s)) criticalQuadrant := by
    have hmap : Set.MapsTo (fun s : ℂ => 1 - s) criticalQuadrant {s : ℂ | 0 < s.re} := by
      intro s hs
      have h2 := hs.2.1
      simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.one_re]
      linarith
    exact ((differentiableOn_eulerTangent hp).comp
      ((differentiableOn_const (1 : ℂ)).sub differentiableOn_id) hmap)
  exact ((differentiableOn_eulerTangent hp).mono hsub).sub hrefl

/-- The symmetrised Euler tangent as a continuous function on the quadrant. -/
noncomputable def feEulerTangentMap (p : Nat.Primes) :
    C((criticalQuadrant : Set ℂ), ℂ) where
  toFun := fun z => feEulerTangent (p : ℕ) (z : ℂ)
  continuous_toFun := by
    have hcont : ContinuousOn (feEulerTangent (p : ℕ)) criticalQuadrant :=
      (differentiableOn_feEulerTangent p.2).continuousOn
    exact hcont.restrict

/-- **The symmetrised Euler tangents are holomorphic elements of the quadrant space.** -/
theorem feEulerTangentMap_mem_holoQuadrant (p : Nat.Primes) :
    feEulerTangentMap p ∈ holoQuadrant :=
  ⟨feEulerTangent (p : ℕ), differentiableOn_feEulerTangent p.2, fun _ => rfl⟩

end HTGeometry
