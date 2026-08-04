import GaloisForLFunctions.HTGeometry.ClockBivariateSecondOrder

/-!
# Continuous partial derivatives in three variables

A field that depends on the two null coordinates and on one transverse coordinate is a function of
three real variables, and the chart d'Alembertian reads its second derivatives. This file records
the three-variable form of the classical theorem that continuous partial derivatives imply total
differentiability.

The proof does not repeat the argument: it groups the first two variables, applies the bivariate
statement on the plane for a fixed value of the third, and then applies the bivariate statement once
more, this time with the plane as the first factor and the transverse line as the second. The
differential is the corresponding iterated coproduct.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Filter

/-- The differential of a function of two real variables, as an operator on the plane. -/
noncomputable def pairToCLM (a b : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ := (toCLM a).coprod (toCLM b)

theorem pairToCLM_apply (a b : ℝ) (z : ℝ × ℝ) : pairToCLM a b z = z.1 * a + z.2 * b := rfl

theorem pairToCLM_eq (a b : ℝ) :
    pairToCLM a b
      = a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  refine ContinuousLinearMap.ext fun z => ?_
  rw [pairToCLM_apply]
  simp [mul_comm]

theorem continuous_pairToCLM : Continuous fun q : ℝ × ℝ => pairToCLM q.1 q.2 := by
  simp only [pairToCLM_eq]
  exact (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)

/-- A function of three real variables read as a function on the product of a plane and a line. -/
noncomputable def uncurry3 (u : ℝ → ℝ → ℝ → ℝ) : (ℝ × ℝ) × ℝ → ℝ :=
  fun q => u q.1.1 q.1.2 q.2

/-- The plane section of a set of triples at a fixed value of the third variable. -/
def sliceSet (Ω : Set ((ℝ × ℝ) × ℝ)) (w : ℝ) : Set (ℝ × ℝ) := {p | (p, w) ∈ Ω}

theorem mem_sliceSet {Ω : Set ((ℝ × ℝ) × ℝ)} {w : ℝ} {p : ℝ × ℝ} :
    p ∈ sliceSet Ω w ↔ ((p, w) : (ℝ × ℝ) × ℝ) ∈ Ω := Iff.rfl

theorem isOpen_sliceSet {Ω : Set ((ℝ × ℝ) × ℝ)} (hΩ : IsOpen Ω) (w : ℝ) :
    IsOpen (sliceSet Ω w) :=
  hΩ.preimage (continuous_id.prodMk continuous_const)

/-- `u` has the continuous partial derivatives `A`, `B` and `C` on the open set `Ω` of triples. -/
structure IsC1On3 (u A B C : ℝ → ℝ → ℝ → ℝ) (Ω : Set ((ℝ × ℝ) × ℝ)) : Prop where
  isOpen : IsOpen Ω
  hasDerivFst : ∀ q ∈ Ω, HasDerivAt (fun x => u x q.1.2 q.2) (A q.1.1 q.1.2 q.2) q.1.1
  hasDerivSnd : ∀ q ∈ Ω, HasDerivAt (fun x => u q.1.1 x q.2) (B q.1.1 q.1.2 q.2) q.1.2
  hasDerivThd : ∀ q ∈ Ω, HasDerivAt (fun x => u q.1.1 q.1.2 x) (C q.1.1 q.1.2 q.2) q.2
  contFst : Continuous fun q : (ℝ × ℝ) × ℝ => A q.1.1 q.1.2 q.2
  contSnd : Continuous fun q : (ℝ × ℝ) × ℝ => B q.1.1 q.1.2 q.2
  contThd : Continuous fun q : (ℝ × ℝ) × ℝ => C q.1.1 q.1.2 q.2

namespace IsC1On3

variable {u A B C : ℝ → ℝ → ℝ → ℝ} {Ω : Set ((ℝ × ℝ) × ℝ)}

/-- The plane section of a three-variable datum at a fixed value of the third variable. -/
theorem slice (h : IsC1On3 u A B C Ω) (w : ℝ) :
    IsC1On (fun s t => u s t w) (fun s t => A s t w) (fun s t => B s t w) (sliceSet Ω w) where
  isOpen := isOpen_sliceSet h.isOpen w
  hasDerivFst := fun p hp => h.hasDerivFst (p, w) hp
  hasDerivSnd := fun p hp => h.hasDerivSnd (p, w) hp
  contFst := h.contFst.comp (continuous_id.prodMk continuous_const)
  contSnd := h.contSnd.comp (continuous_id.prodMk continuous_const)

theorem add {u' A' B' C' : ℝ → ℝ → ℝ → ℝ} (h : IsC1On3 u A B C Ω) (h' : IsC1On3 u' A' B' C' Ω) :
    IsC1On3 (fun s t w => u s t w + u' s t w) (fun s t w => A s t w + A' s t w)
      (fun s t w => B s t w + B' s t w) (fun s t w => C s t w + C' s t w) Ω where
  isOpen := h.isOpen
  hasDerivFst := fun q hq => (h.hasDerivFst q hq).add (h'.hasDerivFst q hq)
  hasDerivSnd := fun q hq => (h.hasDerivSnd q hq).add (h'.hasDerivSnd q hq)
  hasDerivThd := fun q hq => (h.hasDerivThd q hq).add (h'.hasDerivThd q hq)
  contFst := h.contFst.add h'.contFst
  contSnd := h.contSnd.add h'.contSnd
  contThd := h.contThd.add h'.contThd

theorem sub {u' A' B' C' : ℝ → ℝ → ℝ → ℝ} (h : IsC1On3 u A B C Ω) (h' : IsC1On3 u' A' B' C' Ω) :
    IsC1On3 (fun s t w => u s t w - u' s t w) (fun s t w => A s t w - A' s t w)
      (fun s t w => B s t w - B' s t w) (fun s t w => C s t w - C' s t w) Ω where
  isOpen := h.isOpen
  hasDerivFst := fun q hq => (h.hasDerivFst q hq).sub (h'.hasDerivFst q hq)
  hasDerivSnd := fun q hq => (h.hasDerivSnd q hq).sub (h'.hasDerivSnd q hq)
  hasDerivThd := fun q hq => (h.hasDerivThd q hq).sub (h'.hasDerivThd q hq)
  contFst := h.contFst.sub h'.contFst
  contSnd := h.contSnd.sub h'.contSnd
  contThd := h.contThd.sub h'.contThd

end IsC1On3

variable {u A B C : ℝ → ℝ → ℝ → ℝ} {Ω : Set ((ℝ × ℝ) × ℝ)}

/-- **A function of three variables with continuous partial derivatives is differentiable.** -/
theorem hasFDerivAt_uncurry3 (h : IsC1On3 u A B C Ω) {q : (ℝ × ℝ) × ℝ} (hq : q ∈ Ω) :
    HasFDerivAt (uncurry3 u)
      ((pairToCLM (A q.1.1 q.1.2 q.2) (B q.1.1 q.1.2 q.2)).coprod
        (toCLM (C q.1.1 q.1.2 q.2))) q := by
  have df₁ : ∀ᶠ v in nhds q,
      HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2 v.2)
        (Function.uncurry (fun p : ℝ × ℝ => fun w : ℝ => pairToCLM (A p.1 p.2 w) (B p.1 p.2 w)) v)
        v.1 := by
    filter_upwards [h.isOpen.mem_nhds hq] with v hv
    have hslice : v.1 ∈ sliceSet Ω v.2 := hv
    exact hasFDerivAt_uncurry_isC1On (h.slice v.2) hslice
  have df₂ : ∀ᶠ v in nhds q,
      HasFDerivAt (fun w : ℝ => u v.1.1 v.1.2 w)
        (Function.uncurry (fun p : ℝ × ℝ => fun w : ℝ => toCLM (C p.1 p.2 w)) v) v.2 := by
    filter_upwards [h.isOpen.mem_nhds hq] with v hv
    exact (h.hasDerivThd v hv).hasFDerivAt
  have cf₁ : ContinuousAt
      (Function.uncurry fun p : ℝ × ℝ => fun w : ℝ => pairToCLM (A p.1 p.2 w) (B p.1 p.2 w)) q := by
    have hpair : Continuous fun v : (ℝ × ℝ) × ℝ =>
        ((A v.1.1 v.1.2 v.2, B v.1.1 v.1.2 v.2) : ℝ × ℝ) := h.contFst.prodMk h.contSnd
    exact (continuous_pairToCLM.comp hpair).continuousAt
  have cf₂ : ContinuousAt
      (Function.uncurry fun p : ℝ × ℝ => fun w : ℝ => toCLM (C p.1 p.2 w)) q :=
    (continuous_toCLM.comp h.contThd).continuousAt
  exact (hasStrictFDerivAt_uncurry_coprod (f := fun p : ℝ × ℝ => fun w : ℝ => u p.1 p.2 w)
    (f₁ := fun p : ℝ × ℝ => fun w : ℝ => pairToCLM (A p.1 p.2 w) (B p.1 p.2 w))
    (f₂ := fun p : ℝ × ℝ => fun w : ℝ => toCLM (C p.1 p.2 w))
    df₁ df₂ cf₁ cf₂).hasFDerivAt

theorem differentiableAt_uncurry3 (h : IsC1On3 u A B C Ω) {q : (ℝ × ℝ) × ℝ} (hq : q ∈ Ω) :
    DifferentiableAt ℝ (uncurry3 u) q :=
  (hasFDerivAt_uncurry3 h hq).differentiableAt

end GaloisForLFunctions.HTGeometry
