import GaloisForLFunctions.HTGeometry.FiniteClockReferenceFrameCovariance

/-!
# Typed quantum-clock cycle factorization

Pure perspective changes between three possibly different observer spaces cancel through a common
perspective-neutral space.  Inserting physical endomorphisms of the neutral space leaves exactly
their ordered product, represented in the base clock perspective.
-/

namespace GaloisForLFunctions.HTGeometry

section

variable {𝕜 P A B C : Type*} [RCLike 𝕜]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]
  [NormedAddCommGroup A] [NormedSpace 𝕜 A]
  [NormedAddCommGroup B] [NormedSpace 𝕜 B]
  [NormedAddCommGroup C] [NormedSpace 𝕜 C]

/-- A physical perspective change: lift from the source clock, evolve in the
perspective-neutral space, then reduce to the target clock. -/
def physicalClockFrameChange
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (reduceY : P →L[𝕜] Y) (evolution : P →L[𝕜] P) (liftX : X →L[𝕜] P) :
    X →L[𝕜] Y :=
  reduceY.comp (evolution.comp liftX)

/-- **Typed three-clock residue factorization.**  Intermediate clock reductions and lifts cancel,
leaving only the ordered product of physical neutral-space evolutions, represented in the base
clock perspective. -/
theorem physicalClockFrameChange_cycle_factorization
    (reduceA : P →L[𝕜] A) (liftA : A →L[𝕜] P)
    (reduceB : P →L[𝕜] B) (liftB : B →L[𝕜] P)
    (reduceC : P →L[𝕜] C) (liftC : C →L[𝕜] P)
    (V₁ V₂ V₃ : P →L[𝕜] P)
    (hB : liftB.comp reduceB = ContinuousLinearMap.id 𝕜 P)
    (hC : liftC.comp reduceC = ContinuousLinearMap.id 𝕜 P) :
    (physicalClockFrameChange reduceA V₁ liftB).comp
        ((physicalClockFrameChange reduceB V₂ liftC).comp
          (physicalClockFrameChange reduceC V₃ liftA)) =
      physicalClockFrameChange reduceA (V₁.comp (V₂.comp V₃)) liftA := by
  have hB_apply (x : P) : liftB (reduceB x) = x := by
    have h := congrArg (fun f : P →L[𝕜] P => f x) hB
    simpa using h
  have hC_apply (x : P) : liftC (reduceC x) = x := by
    have h := congrArg (fun f : P →L[𝕜] P => f x) hC
    simpa using h
  ext x
  simp only [physicalClockFrameChange, ContinuousLinearMap.comp_apply]
  rw [hC_apply, hB_apply]

/-- A pure change of clock perspective has identity neutral-space evolution. -/
def pureClockFrameChange
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (reduceY : P →L[𝕜] Y) (liftX : X →L[𝕜] P) :
    X →L[𝕜] Y :=
  physicalClockFrameChange reduceY (ContinuousLinearMap.id 𝕜 P) liftX

/-- **Pure QRF triangle flatness.**  A cycle made only of perspective changes is exactly the
identity on the base clock space. -/
theorem pureClockFrameChange_cycle_eq_id
    (reduceA : P →L[𝕜] A) (liftA : A →L[𝕜] P)
    (reduceB : P →L[𝕜] B) (liftB : B →L[𝕜] P)
    (reduceC : P →L[𝕜] C) (liftC : C →L[𝕜] P)
    (hA : reduceA.comp liftA = ContinuousLinearMap.id 𝕜 A)
    (hB : liftB.comp reduceB = ContinuousLinearMap.id 𝕜 P)
    (hC : liftC.comp reduceC = ContinuousLinearMap.id 𝕜 P) :
    (pureClockFrameChange reduceA liftB).comp
        ((pureClockFrameChange reduceB liftC).comp
          (pureClockFrameChange reduceC liftA)) =
      ContinuousLinearMap.id 𝕜 A := by
  rw [show pureClockFrameChange reduceA liftB =
      physicalClockFrameChange reduceA (ContinuousLinearMap.id 𝕜 P) liftB by rfl]
  rw [show pureClockFrameChange reduceB liftC =
      physicalClockFrameChange reduceB (ContinuousLinearMap.id 𝕜 P) liftC by rfl]
  rw [show pureClockFrameChange reduceC liftA =
      physicalClockFrameChange reduceC (ContinuousLinearMap.id 𝕜 P) liftA by rfl]
  rw [physicalClockFrameChange_cycle_factorization
    reduceA liftA reduceB liftB reduceC liftC
    (ContinuousLinearMap.id 𝕜 P) (ContinuousLinearMap.id 𝕜 P)
    (ContinuousLinearMap.id 𝕜 P) hB hC]
  simpa [physicalClockFrameChange] using hA

/-- If the ordered physical evolution around the neutral-space cycle is the identity, the
represented clock cycle is also the identity. -/
theorem physicalClockFrameChange_cycle_eq_id_of_evolution_cycle
    (reduceA : P →L[𝕜] A) (liftA : A →L[𝕜] P)
    (reduceB : P →L[𝕜] B) (liftB : B →L[𝕜] P)
    (reduceC : P →L[𝕜] C) (liftC : C →L[𝕜] P)
    (V₁ V₂ V₃ : P →L[𝕜] P)
    (hA : reduceA.comp liftA = ContinuousLinearMap.id 𝕜 A)
    (hB : liftB.comp reduceB = ContinuousLinearMap.id 𝕜 P)
    (hC : liftC.comp reduceC = ContinuousLinearMap.id 𝕜 P)
    (hV : V₁.comp (V₂.comp V₃) = ContinuousLinearMap.id 𝕜 P) :
    (physicalClockFrameChange reduceA V₁ liftB).comp
        ((physicalClockFrameChange reduceB V₂ liftC).comp
          (physicalClockFrameChange reduceC V₃ liftA)) =
      ContinuousLinearMap.id 𝕜 A := by
  rw [physicalClockFrameChange_cycle_factorization
    reduceA liftA reduceB liftB reduceC liftC V₁ V₂ V₃ hB hC, hV]
  simpa [physicalClockFrameChange] using hA

end

end GaloisForLFunctions.HTGeometry
