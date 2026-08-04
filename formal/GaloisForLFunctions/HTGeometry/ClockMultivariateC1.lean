import GaloisForLFunctions.HTGeometry.ClockPiPartialC1

/-!
# Continuous partial derivatives in the two null coordinates and finitely many transverse ones

A field depending on the two null coordinates and on `k` transverse coordinates is a function on
`(ℝ × ℝ) × (Fin k → ℝ)`. This file records the form of the classical theorem that continuous partial
derivatives imply total differentiability for that domain.

The proof groups the two null coordinates into the plane, uses the bivariate statement there and the
several-variable statement on the transverse factor, and joins them with the two-factor theorem. The
differential is the corresponding coproduct.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {k : ℕ}

/-- A field of the two null coordinates and `k` transverse ones, read on the product domain. -/
noncomputable def uncurryMulti (u : ℝ → ℝ → (Fin k → ℝ) → ℝ) : (ℝ × ℝ) × (Fin k → ℝ) → ℝ :=
  fun q => u q.1.1 q.1.2 q.2

/-- The null-plane section at a fixed transverse point. -/
def sliceSetMulti (Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))) (y : Fin k → ℝ) : Set (ℝ × ℝ) :=
  {p | (p, y) ∈ Ω}

/-- The transverse section at fixed null coordinates. -/
def transSetMulti (Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))) (p : ℝ × ℝ) : Set (Fin k → ℝ) :=
  {y | (p, y) ∈ Ω}

theorem isOpen_sliceSetMulti {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))} (hΩ : IsOpen Ω) (y : Fin k → ℝ) :
    IsOpen (sliceSetMulti Ω y) :=
  hΩ.preimage (continuous_id.prodMk continuous_const)

theorem isOpen_transSetMulti {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))} (hΩ : IsOpen Ω) (p : ℝ × ℝ) :
    IsOpen (transSetMulti Ω p) :=
  hΩ.preimage (continuous_const.prodMk continuous_id)

/-- `u` has the continuous partial derivatives `A`, `B` in the null coordinates and `C i` in the
transverse ones, on the open set `Ω`. -/
structure IsC1OnMulti (u A B : ℝ → ℝ → (Fin k → ℝ) → ℝ)
    (C : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ) (Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))) : Prop where
  isOpen : IsOpen Ω
  hasDerivFst : ∀ q ∈ Ω, HasDerivAt (fun x : ℝ => u x q.1.2 q.2) (A q.1.1 q.1.2 q.2) q.1.1
  hasDerivSnd : ∀ q ∈ Ω, HasDerivAt (fun x : ℝ => u q.1.1 x q.2) (B q.1.1 q.1.2 q.2) q.1.2
  hasDerivTrans : ∀ q ∈ Ω, ∀ i : Fin k,
    HasDerivAt (fun a : ℝ => u q.1.1 q.1.2 (Function.update q.2 i a)) (C i q.1.1 q.1.2 q.2) (q.2 i)
  contFst : Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => A q.1.1 q.1.2 q.2
  contSnd : Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => B q.1.1 q.1.2 q.2
  contTrans : ∀ i : Fin k, Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => C i q.1.1 q.1.2 q.2

namespace IsC1OnMulti

variable {u A B : ℝ → ℝ → (Fin k → ℝ) → ℝ} {C : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}
  {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))}

/-- The null-plane section of the datum at a fixed transverse point. -/
theorem slice (h : IsC1OnMulti u A B C Ω) (y : Fin k → ℝ) :
    IsC1On (fun s t => u s t y) (fun s t => A s t y) (fun s t => B s t y)
      (sliceSetMulti Ω y) where
  isOpen := isOpen_sliceSetMulti h.isOpen y
  hasDerivFst := fun p hp => h.hasDerivFst (p, y) hp
  hasDerivSnd := fun p hp => h.hasDerivSnd (p, y) hp
  contFst := h.contFst.comp (continuous_id.prodMk continuous_const)
  contSnd := h.contSnd.comp (continuous_id.prodMk continuous_const)

/-- The transverse section of the datum at fixed null coordinates. -/
theorem transSlice (h : IsC1OnMulti u A B C Ω) (p : ℝ × ℝ) :
    IsC1OnPi (fun y : Fin k → ℝ => u p.1 p.2 y) (fun i y => C i p.1 p.2 y)
      (transSetMulti Ω p) where
  isOpen := isOpen_transSetMulti h.isOpen p
  hasDeriv := fun y hy i => h.hasDerivTrans (p, y) hy i
  cont := fun i => (h.contTrans i).comp (continuous_const.prodMk continuous_id)

theorem add {u' A' B' : ℝ → ℝ → (Fin k → ℝ) → ℝ} {C' : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}
    (h : IsC1OnMulti u A B C Ω) (h' : IsC1OnMulti u' A' B' C' Ω) :
    IsC1OnMulti (fun s t y => u s t y + u' s t y) (fun s t y => A s t y + A' s t y)
      (fun s t y => B s t y + B' s t y) (fun i s t y => C i s t y + C' i s t y) Ω where
  isOpen := h.isOpen
  hasDerivFst := fun q hq => (h.hasDerivFst q hq).add (h'.hasDerivFst q hq)
  hasDerivSnd := fun q hq => (h.hasDerivSnd q hq).add (h'.hasDerivSnd q hq)
  hasDerivTrans := fun q hq i => (h.hasDerivTrans q hq i).add (h'.hasDerivTrans q hq i)
  contFst := h.contFst.add h'.contFst
  contSnd := h.contSnd.add h'.contSnd
  contTrans := fun i => (h.contTrans i).add (h'.contTrans i)

theorem sub {u' A' B' : ℝ → ℝ → (Fin k → ℝ) → ℝ} {C' : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}
    (h : IsC1OnMulti u A B C Ω) (h' : IsC1OnMulti u' A' B' C' Ω) :
    IsC1OnMulti (fun s t y => u s t y - u' s t y) (fun s t y => A s t y - A' s t y)
      (fun s t y => B s t y - B' s t y) (fun i s t y => C i s t y - C' i s t y) Ω where
  isOpen := h.isOpen
  hasDerivFst := fun q hq => (h.hasDerivFst q hq).sub (h'.hasDerivFst q hq)
  hasDerivSnd := fun q hq => (h.hasDerivSnd q hq).sub (h'.hasDerivSnd q hq)
  hasDerivTrans := fun q hq i => (h.hasDerivTrans q hq i).sub (h'.hasDerivTrans q hq i)
  contFst := h.contFst.sub h'.contFst
  contSnd := h.contSnd.sub h'.contSnd
  contTrans := fun i => (h.contTrans i).sub (h'.contTrans i)

end IsC1OnMulti

variable {u A B : ℝ → ℝ → (Fin k → ℝ) → ℝ} {C : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}
  {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))}

/-- **A field of the two null coordinates and finitely many transverse ones with continuous partial
derivatives is differentiable.** -/
theorem hasFDerivAt_uncurryMulti (h : IsC1OnMulti u A B C Ω) {q : (ℝ × ℝ) × (Fin k → ℝ)}
    (hq : q ∈ Ω) :
    HasFDerivAt (uncurryMulti u)
      ((pairToCLM (A q.1.1 q.1.2 q.2) (B q.1.1 q.1.2 q.2)).coprod
        (piToCLM fun i => C i q.1.1 q.1.2 q.2)) q := by
  have df₁ : ∀ᶠ v in nhds q,
      HasFDerivAt (fun p : ℝ × ℝ => u p.1 p.2 v.2)
        (Function.uncurry
          (fun (p : ℝ × ℝ) (y : Fin k → ℝ) => pairToCLM (A p.1 p.2 y) (B p.1 p.2 y)) v) v.1 := by
    filter_upwards [h.isOpen.mem_nhds hq] with v hv
    have hslice : v.1 ∈ sliceSetMulti Ω v.2 := hv
    exact hasFDerivAt_uncurry_isC1On (h.slice v.2) hslice
  have df₂ : ∀ᶠ v in nhds q,
      HasFDerivAt (fun y : Fin k → ℝ => u v.1.1 v.1.2 y)
        (Function.uncurry
          (fun (p : ℝ × ℝ) (y : Fin k → ℝ) => piToCLM fun i => C i p.1 p.2 y) v) v.2 := by
    filter_upwards [h.isOpen.mem_nhds hq] with v hv
    have hmem : v.2 ∈ transSetMulti Ω v.1 := hv
    exact hasFDerivAt_of_isC1OnPi k (fun y : Fin k → ℝ => u v.1.1 v.1.2 y)
      (fun i y => C i v.1.1 v.1.2 y) (transSetMulti Ω v.1) (h.transSlice v.1) v.2 hmem
  have cf₁ : ContinuousAt (Function.uncurry
      fun (p : ℝ × ℝ) (y : Fin k → ℝ) => pairToCLM (A p.1 p.2 y) (B p.1 p.2 y)) q := by
    have hpair : Continuous fun v : (ℝ × ℝ) × (Fin k → ℝ) =>
        ((A v.1.1 v.1.2 v.2, B v.1.1 v.1.2 v.2) : ℝ × ℝ) := h.contFst.prodMk h.contSnd
    exact (continuous_pairToCLM.comp hpair).continuousAt
  have cf₂ : ContinuousAt (Function.uncurry
      fun (p : ℝ × ℝ) (y : Fin k → ℝ) => piToCLM fun i => C i p.1 p.2 y) q := by
    have hpi : Continuous fun v : (ℝ × ℝ) × (Fin k → ℝ) =>
        (fun i : Fin k => C i v.1.1 v.1.2 v.2) := continuous_pi fun i => h.contTrans i
    exact (continuous_piToCLM.comp hpi).continuousAt
  exact (hasStrictFDerivAt_uncurry_coprod
    (f := fun (p : ℝ × ℝ) (y : Fin k → ℝ) => u p.1 p.2 y)
    (f₁ := fun (p : ℝ × ℝ) (y : Fin k → ℝ) => pairToCLM (A p.1 p.2 y) (B p.1 p.2 y))
    (f₂ := fun (p : ℝ × ℝ) (y : Fin k → ℝ) => piToCLM fun i => C i p.1 p.2 y)
    df₁ df₂ cf₁ cf₂).hasFDerivAt

theorem differentiableAt_uncurryMulti (h : IsC1OnMulti u A B C Ω)
    {q : (ℝ × ℝ) × (Fin k → ℝ)} (hq : q ∈ Ω) : DifferentiableAt ℝ (uncurryMulti u) q :=
  (hasFDerivAt_uncurryMulti h hq).differentiableAt

end GaloisForLFunctions.HTGeometry
