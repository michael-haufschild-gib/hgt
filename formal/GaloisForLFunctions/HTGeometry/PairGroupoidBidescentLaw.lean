import GaloisForLFunctions.HTGeometry.InvolutiveDescentExactSequenceLaw

/-!
# Pair-groupoid and bidescent conservation

The universal additive descent defect of an observable is its difference on
an ordered pair.  It is a pair-groupoid one-cocycle.  Descent through any
equivalence quotient is exactly its vanishing on the equivalence relation;
point-dependent transport adds exactly one connection term; additive
consumers carry the cocycle naturally and can erase it only in their kernel.

For a two-directional field, horizontal and vertical differences commute.
Consequently exact gluing in one direction conserves an arbitrary defect in
the other direction but cannot force it to vanish.  An independent anchor is
necessary and sufficient to turn conservation into vanishing.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Universal pair-groupoid descent cocycle. -/
def pairDescentDefect {X : Type*} (f : X -> ℂ) (x y : X) : ℂ :=
  f x - f y

/-- Point-dependent scalar transport. -/
def pairPointwiseTransport {X : Type*} (a f : X -> ℂ) (x : X) : ℂ :=
  a x * f x

@[simp]
theorem pairDescentDefect_self {X : Type*} (f : X -> ℂ) (x : X) :
    pairDescentDefect f x x = 0 := by
  rw [pairDescentDefect, sub_self]

/-- Reversing one pair reverses its defect. -/
theorem pairDescentDefect_swap {X : Type*} (f : X -> ℂ) (x y : X) :
    pairDescentDefect f y x = -pairDescentDefect f x y := by
  rw [pairDescentDefect, pairDescentDefect]
  ring

/-- Pair-groupoid cocycle law. -/
theorem pairDescentDefect_cocycle {X : Type*} (f : X -> ℂ) (x y z : X) :
    pairDescentDefect f x z =
      pairDescentDefect f x y + pairDescentDefect f y z := by
  rw [pairDescentDefect, pairDescentDefect, pairDescentDefect]
  ring

/-- Complete quotient criterion.  An observable factors through the
quotient by an equivalence relation exactly when its cocycle vanishes on
every related pair. -/
theorem factorsThrough_quotient_iff_pairDescentDefect_zero
    {X : Type*} (S : Setoid X) (f : X -> ℂ) :
    FactorsThrough (Quotient.mk S) f <->
      forall x y, S.r x y -> pairDescentDefect f x y = 0 := by
  constructor
  · intro hfactor x y hxy
    rw [pairDescentDefect, sub_eq_zero]
    exact mapKernelPair_mono_of_factorsThrough hfactor
      (Quotient.sound hxy)
  · intro hzero
    let descend : Quotient S -> ℂ :=
      Quotient.lift f (by
        intro x y hxy
        exact sub_eq_zero.mp (hzero x y hxy))
    refine ⟨descend, ?_⟩
    funext x
    rfl

/-- Pair-groupoid connection Leibniz law. -/
theorem pairDescentDefect_pointwiseTransport
    {X : Type*} (a f : X -> ℂ) (x y : X) :
    pairDescentDefect (pairPointwiseTransport a f) x y =
      a x * pairDescentDefect f x y +
        pairDescentDefect a x y * f y := by
  rw [pairDescentDefect, pairPointwiseTransport,
    pairPointwiseTransport, pairDescentDefect, pairDescentDefect]
  ring

/-- Pair-invariant nonzero scalar transport preserves the exact cocycle
zero locus. -/
theorem pairDescentDefect_pointwiseTransport_eq_zero_iff
    {X : Type*} {a f : X -> ℂ} (x y : X)
    (ha : a x = a y) (ha0 : a x ≠ 0) :
    pairDescentDefect (pairPointwiseTransport a f) x y = 0 <->
      pairDescentDefect f x y = 0 := by
  rw [pairDescentDefect_pointwiseTransport]
  have hda : pairDescentDefect a x y = 0 := by
    rw [pairDescentDefect, ha, sub_self]
  rw [hda, zero_mul, add_zero]
  exact mul_eq_zero_iff_left ha0

/-- Additive consumers carry the universal cocycle naturally. -/
theorem pairDescentDefect_addMonoidHom
    {X : Type*} (L : ℂ →+ ℂ) (f : X -> ℂ) (x y : X) :
    pairDescentDefect (fun p => L (f p)) x y =
      L (pairDescentDefect f x y) := by
  rw [pairDescentDefect, pairDescentDefect, map_sub]

/-- A faithful additive consumer preserves the cocycle zero locus. -/
theorem pairDescentDefect_addMonoidHom_eq_zero_iff
    {X : Type*} (L : ℂ →+ ℂ) (hL : Function.Injective L)
    (f : X -> ℂ) (x y : X) :
    pairDescentDefect (fun p => L (f p)) x y = 0 <->
      pairDescentDefect f x y = 0 := by
  rw [pairDescentDefect_addMonoidHom]
  constructor
  · intro h
    apply hL
    simpa using h
  · intro h
    rw [h, map_zero]

/-- An arbitrary additive consumer erases a cocycle precisely on its
kernel. -/
theorem pairDescentDefect_erased_iff_mem_consumer_kernel
    {X : Type*} (L : ℂ →+ ℂ) (f : X -> ℂ) (x y : X) :
    pairDescentDefect (fun p => L (f p)) x y = 0 <->
      pairDescentDefect f x y ∈ L.ker := by
  rw [pairDescentDefect_addMonoidHom]
  rfl

/-- The involutive defect is the restriction of the pair-groupoid cocycle
to involution edges. -/
theorem pairDescentDefect_involution_edge
    {X : Type*} (tau : X -> X) (f : X -> ℂ) (x : X) :
    pairDescentDefect f x (tau x) = involutiveDescentDefect tau f x := by
  rfl

/-- Horizontal difference of a two-directional field. -/
def horizontalPairDescentDefect {A B : Type*}
    (F : A -> B -> ℂ) (b0 b1 : B) (a : A) : ℂ :=
  F a b0 - F a b1

/-- Vertical difference of a two-directional field. -/
def verticalPairDescentDefect {A B : Type*}
    (F : A -> B -> ℂ) (a0 a1 : A) (b : B) : ℂ :=
  F a0 b - F a1 b

/-- **Bidescent commutation law.**  Horizontal and vertical differences
commute; both are the same alternating rectangle sum. -/
theorem vertical_horizontal_pairDescentDefect_commute
    {A B : Type*} (F : A -> B -> ℂ)
    (a0 a1 : A) (b0 b1 : B) :
    verticalPairDescentDefect
        (fun a _ => horizontalPairDescentDefect F b0 b1 a)
        a0 a1 () =
      horizontalPairDescentDefect
        (fun _ b => verticalPairDescentDefect F a0 a1 b)
        b0 b1 () := by
  change
    (F a0 b0 - F a0 b1) - (F a1 b0 - F a1 b1) =
      (F a0 b0 - F a1 b0) - (F a0 b1 - F a1 b1)
  ring

/-- Exact vertical gluing conserves the horizontal defect. -/
theorem horizontalPairDescentDefect_eq_of_vertical_gluing
    {A B : Type*} (F : A -> B -> ℂ)
    (a0 a1 : A) (b0 b1 : B)
    (hv0 : F a0 b0 = F a1 b0)
    (hv1 : F a0 b1 = F a1 b1) :
    horizontalPairDescentDefect F b0 b1 a0 =
      horizontalPairDescentDefect F b0 b1 a1 := by
  rw [horizontalPairDescentDefect, horizontalPairDescentDefect,
    hv0, hv1]

/-- Vertical gluing plus one horizontal anchor forces horizontal vanishing
at the other level. -/
theorem horizontalPairDescentDefect_eq_zero_of_vertical_gluing_of_anchor
    {A B : Type*} (F : A -> B -> ℂ)
    (a0 a1 : A) (b0 b1 : B)
    (hv0 : F a0 b0 = F a1 b0)
    (hv1 : F a0 b1 = F a1 b1)
    (hanchor : horizontalPairDescentDefect F b0 b1 a0 = 0) :
    horizontalPairDescentDefect F b0 b1 a1 = 0 := by
  rw [← horizontalPairDescentDefect_eq_of_vertical_gluing
    F a0 a1 b0 b1 hv0 hv1]
  exact hanchor

/-- Vertical exactness alone permits an arbitrary horizontal cocycle. -/
theorem vertical_gluing_preserves_arbitrary_horizontalPairDescentDefect
    {A B : Type*} (h : B -> ℂ) (a0 a1 : A) (b0 b1 : B) :
    verticalPairDescentDefect (fun _ b => h b) a0 a1 b0 = 0 ∧
    verticalPairDescentDefect (fun _ b => h b) a0 a1 b1 = 0 ∧
    horizontalPairDescentDefect (fun _ b => h b) b0 b1 a1 =
      pairDescentDefect h b0 b1 := by
  constructor
  · rw [verticalPairDescentDefect, sub_self]
  constructor
  · rw [verticalPairDescentDefect, sub_self]
  · rfl

/-- Universal pair-groupoid bidescent law in one package. -/
theorem pairGroupoidBidescentLaw
    {X : Type*} (f : X -> ℂ) (x y z : X) :
    pairDescentDefect f y x = -pairDescentDefect f x y ∧
    pairDescentDefect f x z =
      pairDescentDefect f x y + pairDescentDefect f y z := by
  exact ⟨pairDescentDefect_swap f x y,
    pairDescentDefect_cocycle f x y z⟩

end

end GaloisForLFunctions.HTGeometry
