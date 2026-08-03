import GaloisForLFunctions.HTGeometry.InvolutiveProjectiveWedgeTransportLaw

/-!
# The involutive descent exact sequence

For an involution `tau`, the universal obstruction to descent through the
orbit quotient is the difference `f - f ∘ tau`.  Its kernel is exactly the
invariant sector and, over `ℂ`, its image is exactly the odd sector.  A
point-dependent scalar transport satisfies a discrete connection formula;
constant faithful consumers preserve the obstruction, while nonfaithful
consumers can only hide it in their kernel.

The projective wedge is the nowhere-zero gauged form of this universal
difference applied to a logarithmic two-component jet.
-/

open Function

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Universal coequalizer differential for an involution candidate. -/
def involutiveDescentDefect {Q : Type*} (tau : Q -> Q)
    (f : Q -> ℂ) (q : Q) : ℂ :=
  f q - f (tau q)

/-- Reflection-even projection. -/
def involutiveEvenPart {Q : Type*} (tau : Q -> Q)
    (f : Q -> ℂ) (q : Q) : ℂ :=
  (f q + f (tau q)) / 2

/-- Reflection-odd projection. -/
def involutiveOddPart {Q : Type*} (tau : Q -> Q)
    (f : Q -> ℂ) (q : Q) : ℂ :=
  (f q - f (tau q)) / 2

/-- Point-dependent scalar transport. -/
def involutivePointwiseTransport {Q : Type*}
    (a f : Q -> ℂ) (q : Q) : ℂ :=
  a q * f q

/-- The descent defect is reflection odd. -/
theorem involutiveDescentDefect_apply_involution
    {Q : Type*} {tau : Q -> Q} (htau : Involutive tau)
    (f : Q -> ℂ) (q : Q) :
    involutiveDescentDefect tau f (tau q) =
      -involutiveDescentDefect tau f q := by
  rw [involutiveDescentDefect, involutiveDescentDefect, htau q]
  ring

/-- Applying the coequalizer differential twice multiplies it by two. -/
theorem involutiveDescentDefect_iterate
    {Q : Type*} {tau : Q -> Q} (htau : Involutive tau)
    (f : Q -> ℂ) (q : Q) :
    involutiveDescentDefect tau
        (involutiveDescentDefect tau f) q =
      2 * involutiveDescentDefect tau f q := by
  rw [involutiveDescentDefect, involutiveDescentDefect_apply_involution
    htau f q]
  ring

/-- The universal defect vanishes exactly on invariant observables. -/
theorem invariantUnder_iff_involutiveDescentDefect_eq_zero
    {Q : Type*} (tau : Q -> Q) (f : Q -> ℂ) :
    InvariantUnder tau f <->
      forall q, involutiveDescentDefect tau f q = 0 := by
  constructor
  · intro hinv q
    rw [involutiveDescentDefect, hinv q, sub_self]
  · intro hzero q
    have h := hzero q
    rw [involutiveDescentDefect, sub_eq_zero] at h
    exact h.symm

/-- Exact even/odd splitting of every complex observable. -/
theorem involutive_even_odd_decomposition
    {Q : Type*} {tau : Q -> Q} (htau : Involutive tau)
    (f : Q -> ℂ) :
    (forall q, involutiveEvenPart tau f (tau q) =
        involutiveEvenPart tau f q) ∧
    (forall q, involutiveOddPart tau f (tau q) =
        -involutiveOddPart tau f q) ∧
    (forall q, f q =
        involutiveEvenPart tau f q + involutiveOddPart tau f q) ∧
    (forall q, involutiveDescentDefect tau f q =
        2 * involutiveOddPart tau f q) := by
  constructor
  · intro q
    rw [involutiveEvenPart, involutiveEvenPart, htau q]
    ring
  constructor
  · intro q
    rw [involutiveOddPart, involutiveOddPart, htau q]
    ring
  constructor
  · intro q
    rw [involutiveEvenPart, involutiveOddPart]
    ring
  · intro q
    rw [involutiveDescentDefect, involutiveOddPart]
    ring

/-- Exactness onto the anti-invariant sector: a complex field is a descent
defect exactly when it is reflection odd. -/
theorem exists_involutiveDescentDefect_preimage_iff_odd
    {Q : Type*} {tau : Q -> Q} (htau : Involutive tau)
    (h : Q -> ℂ) :
    (exists f : Q -> ℂ,
      forall q, involutiveDescentDefect tau f q = h q) <->
      forall q, h (tau q) = -h q := by
  constructor
  · rintro ⟨f, hf⟩ q
    rw [← hf, ← hf]
    exact involutiveDescentDefect_apply_involution htau f q
  · intro hodd
    refine ⟨fun q => h q / 2, fun q => ?_⟩
    rw [involutiveDescentDefect, hodd q]
    ring

/-- Complete coequalizer classification: a scalar observable factors through
the finest involution-orbit observation exactly when its universal defect
vanishes. -/
theorem factorsThrough_involutionOrbit_iff_descentDefect_zero
    {Q : Type*} (tau : Q -> Q) (htau : Involutive tau)
    (f : Q -> ℂ) :
    FactorsThrough (involutionOrbitObservation tau htau) f <->
      forall q, involutiveDescentDefect tau f q = 0 := by
  rw [← invariantUnder_iff_involutiveDescentDefect_eq_zero]
  constructor
  · intro hfactor q
    exact mapKernelPair_mono_of_factorsThrough hfactor
      (invariantUnder_involutionOrbitObservation tau htau q)
  · intro hinv
    let descend : Quotient (involutionOrbitSetoid tau htau) -> ℂ :=
      Quotient.lift f (by
        intro q r hqr
        rcases hqr with rfl | hqr
        · rfl
        · rw [hqr]
          exact (hinv q).symm)
    refine ⟨descend, ?_⟩
    funext q
    rfl

/-- Discrete connection formula.  Relative motion of the multiplier is the
only inhomogeneous term. -/
theorem involutiveDescentDefect_pointwiseTransport
    {Q : Type*} (tau : Q -> Q) (a f : Q -> ℂ) (q : Q) :
    involutiveDescentDefect tau
        (involutivePointwiseTransport a f) q =
      a q * involutiveDescentDefect tau f q +
        involutiveDescentDefect tau a q * f (tau q) := by
  rw [involutiveDescentDefect, involutivePointwiseTransport,
    involutivePointwiseTransport, involutiveDescentDefect,
    involutiveDescentDefect]
  ring

/-- A nonzero pair-invariant scalar transport preserves the exact descent
locus. -/
theorem involutiveDescentDefect_pointwiseTransport_eq_zero_iff
    {Q : Type*} (tau : Q -> Q) {a f : Q -> ℂ} (q : Q)
    (ha : a (tau q) = a q) (ha0 : a q ≠ 0) :
    involutiveDescentDefect tau
        (involutivePointwiseTransport a f) q = 0 <->
      involutiveDescentDefect tau f q = 0 := by
  rw [involutiveDescentDefect_pointwiseTransport]
  have hda : involutiveDescentDefect tau a q = 0 := by
    rw [involutiveDescentDefect, ha, sub_self]
  rw [hda, zero_mul, add_zero]
  exact mul_eq_zero_iff_left ha0

/-- Naturality under additive consumers. -/
theorem involutiveDescentDefect_addMonoidHom
    {Q : Type*} (tau : Q -> Q) (L : ℂ →+ ℂ)
    (f : Q -> ℂ) (q : Q) :
    involutiveDescentDefect tau (fun p => L (f p)) q =
      L (involutiveDescentDefect tau f q) := by
  rw [involutiveDescentDefect, involutiveDescentDefect, map_sub]

/-- A faithful additive consumer preserves the exact descent locus. -/
theorem involutiveDescentDefect_addMonoidHom_eq_zero_iff
    {Q : Type*} (tau : Q -> Q) (L : ℂ →+ ℂ)
    (hL : Injective L) (f : Q -> ℂ) (q : Q) :
    involutiveDescentDefect tau (fun p => L (f p)) q = 0 <->
      involutiveDescentDefect tau f q = 0 := by
  rw [involutiveDescentDefect_addMonoidHom]
  constructor
  · intro h
    apply hL
    simpa using h
  · intro h
    rw [h, map_zero]

/-- A nonfaithful additive consumer can erase a descent defect only by
placing it in its kernel. -/
theorem involutiveDescentDefect_erased_iff_mem_consumer_kernel
    {Q : Type*} (tau : Q -> Q) (L : ℂ →+ ℂ)
    (f : Q -> ℂ) (q : Q) :
    involutiveDescentDefect tau (fun p => L (f p)) q = 0 <->
      involutiveDescentDefect tau f q ∈ L.ker := by
  rw [involutiveDescentDefect_addMonoidHom]
  rfl

/-- The projective wedge is the universal descent defect of the logarithmic
jet multiplied by its nowhere-zero endpoint gauge. -/
theorem involutiveProjectiveWedge_eq_gauge_mul_descentDefect_logJet
    {Q : Type*} (tau : Q -> Q) {j0 j1 : Q -> ℂ} (q : Q)
    (h0 : j0 q ≠ 0) (h0tau : j0 (tau q) ≠ 0) :
    involutiveProjectiveWedge tau j0 j1 q =
      (j0 q * j0 (tau q)) *
        involutiveDescentDefect tau (fun p => j1 p / j0 p) q := by
  rw [involutiveProjectiveWedge, involutiveDescentDefect]
  field_simp [h0, h0tau]

/-- Universal involutive descent law in one package. -/
theorem involutiveDescentExactSequenceLaw
    {Q : Type*} {tau : Q -> Q} (htau : Involutive tau)
    (a f : Q -> ℂ) (q : Q) :
    involutiveDescentDefect tau f (tau q) =
        -involutiveDescentDefect tau f q ∧
    involutiveDescentDefect tau
        (involutiveDescentDefect tau f) q =
        2 * involutiveDescentDefect tau f q ∧
    involutiveDescentDefect tau
        (involutivePointwiseTransport a f) q =
      a q * involutiveDescentDefect tau f q +
        involutiveDescentDefect tau a q * f (tau q) := by
  exact ⟨
    involutiveDescentDefect_apply_involution htau f q,
    involutiveDescentDefect_iterate htau f q,
    involutiveDescentDefect_pointwiseTransport tau a f q⟩

end

end GaloisForLFunctions.HTGeometry
