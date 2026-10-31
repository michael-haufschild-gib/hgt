import GaloisForLFunctions.HTGeometry.LoopEisenstein.TriangularHaarProbability

/-!
# Finite triangular sampling of additive Haar measure

A measure-preserving scalar sampler remains measure preserving after each
sample is translated by a measurable function of strictly earlier source
coordinates. Induction splits off the last coordinate and uses a Haar
translation in that fiber.
-/

namespace GaloisForLFunctions.HTGeometry.LoopEisenstein
open MeasureTheory
noncomputable section

private def samplingHeadLast {A : Type*} [MeasurableSpace A] (N : ℕ) :
    (Fin (N+1) → A) ≃ᵐ (Fin N → A) × A :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N+1) => A) (Fin.last N)).trans
    (MeasurableEquiv.prodComm (α := A) (β := Fin N → A))

private theorem samplingHeadLast_head {A : Type*} [MeasurableSpace A]
    (N : ℕ) (x : Fin (N+1) → A) (i : Fin N) :
    (samplingHeadLast N x).1 i = x i.castSucc := by
  change x ((Fin.last N).succAbove i) = x i.castSucc
  rw [Fin.succAbove_last]

private theorem samplingHeadLast_last {A : Type*} [MeasurableSpace A]
    (N : ℕ) (x : Fin (N+1) → A) :
    (samplingHeadLast N x).2 = x (Fin.last N) := rfl

private theorem measurePreserving_samplingHeadLast {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [SigmaFinite μ] (N : ℕ) :
    MeasurePreserving (samplingHeadLast (A := A) N) (Measure.pi (fun _ : Fin (N+1) => μ))
      ((Measure.pi (fun _ : Fin N => μ)).prod μ) :=
  Measure.measurePreserving_swap.comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (N+1) => μ) (Fin.last N))

variable {C G : Type*} [MeasurableSpace C] [MeasurableSpace G]
  [AddCommGroup G] [MeasurableAdd₂ G]

/-- Sample each coordinate and translate it using only the strict source prefix. -/
def finiteTriangularSampling (f : C → G)
    (φ : ∀ n : ℕ, (Fin n → C) → G) (N : ℕ) (x : Fin N → C) : Fin N → G :=
  fun i => f (x i) + φ i.val (fun j => x ⟨j.val,lt_trans j.isLt i.isLt⟩)

/-- Strict-prefix corrections preserve the sampled finite product Haar law. -/
theorem measurePreserving_finiteTriangularSampling (μ : Measure C) (ν : Measure G) [SigmaFinite μ] [SigmaFinite ν]
    [ν.IsAddRightInvariant] (f : C → G) (hf : MeasurePreserving f μ ν)
    (φ : ∀ n : ℕ, (Fin n → C) → G) (hφ : ∀ n, Measurable (φ n)) (N : ℕ) :
    MeasurePreserving (finiteTriangularSampling f φ N)
      (Measure.pi (fun _ : Fin N => μ)) (Measure.pi (fun _ : Fin N => ν)) := by
  induction N with
  | zero =>
    have h := measurePreserving_pi (fun _ : Fin 0 => μ) (fun _ : Fin 0 => ν)
      (f := fun _ : Fin 0 => f) (fun _ => hf)
    convert h using 1
  | succ N ih =>
    let eC := samplingHeadLast (A := C) N
    let eG := samplingHeadLast (A := G) N
    let h : (Fin N → C) × C → (Fin N → G) × G :=
      fun p => (finiteTriangularSampling f φ N p.1, f p.2 + φ N p.1)
    have hh : MeasurePreserving h ((Measure.pi (fun _ : Fin N => μ)).prod μ)
        ((Measure.pi (fun _ : Fin N => ν)).prod ν) := by
      apply ih.skew_product (g := fun x y => f y + φ N x) (μc := μ) (μd := ν)
        ((hf.measurable.comp measurable_snd).add ((hφ N).comp measurable_fst))
      exact Filter.Eventually.of_forall fun x =>
        ((measurePreserving_add_right ν (φ N x)).comp hf).map_eq
    have hc (x : Fin (N+1) → C) : eG (finiteTriangularSampling f φ (N+1) x) = h (eC x) := by
      apply Prod.ext
      · funext i
        change (samplingHeadLast N (finiteTriangularSampling f φ (N+1) x)).1 i =
          finiteTriangularSampling f φ N (samplingHeadLast N x).1 i
        rw [samplingHeadLast_head]
        simp only [finiteTriangularSampling,samplingHeadLast_head]
        apply congrArg (fun z : Fin i.val → C => f (x i.castSucc) + φ i.val z)
        funext j
        rfl
      · change (samplingHeadLast N (finiteTriangularSampling f φ (N+1) x)).2 =
          f ((samplingHeadLast N x).2) + φ N (samplingHeadLast N x).1
        rw [samplingHeadLast_last,samplingHeadLast_last]
        change f (x (Fin.last N)) + φ N (fun i => x ⟨i.val,lt_trans i.isLt (Fin.last N).isLt⟩) = _
        apply congrArg (fun z : Fin N → C => f (x (Fin.last N)) + φ N z)
        funext i
        exact (samplingHeadLast_head N x i).symm
    have he : finiteTriangularSampling f φ (N+1) = eG.symm ∘ h ∘ eC := by
      funext x
      apply eG.injective
      exact (hc x).trans (eG.apply_symm_apply _).symm
    rw [he]
    exact (MeasurePreserving.symm eG (measurePreserving_samplingHeadLast ν N)).comp
      (hh.comp (measurePreserving_samplingHeadLast μ N))

end
end GaloisForLFunctions.HTGeometry.LoopEisenstein


#print axioms GaloisForLFunctions.HTGeometry.LoopEisenstein.measurePreserving_finiteTriangularSampling
