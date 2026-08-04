import GaloisForLFunctions.HTGeometry.TorusGeneralDeck
import GaloisForLFunctions.HTGeometry.NonautonomousErasedDeckBridge

/-!
# The nonautonomous torus protocol

A sequence of nonsingular integer matrices is an isogeny protocol on the split torus `G_m ^ r`: its
prefix maps are the monomial substitutions of the accumulated matrices, and its deck groups are the
kernels of those matrices on the constant torus.

Since every prefix image is the fixed field of its deck group, the phase tail of the protocol is the
fixed field of the closed erased sector — the card's deck-closure identity, unconditional for a
torus over an algebraically closed field of constants.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

section Prefix

variable {r : ℕ}

/-- The matrix accumulated by the first `n` steps of a torus protocol from phase `i`. -/
def prefixMatrix (m : ℕ → Matrix (Fin r) (Fin r) ℤ) :
    ℕ → ℕ → Matrix (Fin r) (Fin r) ℤ
  | _, 0 => 1
  | i, n + 1 => prefixMatrix m (i + 1) n * m i

@[simp] theorem prefixMatrix_zero (m : ℕ → Matrix (Fin r) (Fin r) ℤ) (i : ℕ) :
    prefixMatrix m i 0 = 1 := rfl

@[simp] theorem prefixMatrix_succ (m : ℕ → Matrix (Fin r) (Fin r) ℤ) (i n : ℕ) :
    prefixMatrix m i (n + 1) = prefixMatrix m (i + 1) n * m i := rfl

theorem det_prefixMatrix_ne_zero {m : ℕ → Matrix (Fin r) (Fin r) ℤ}
    (hm : ∀ j, (m j).det ≠ 0) (i n : ℕ) : (prefixMatrix m i n).det ≠ 0 := by
  induction n generalizing i with
  | zero =>
      rw [prefixMatrix_zero, Matrix.det_one]
      exact one_ne_zero
  | succ n ih =>
      rw [prefixMatrix_succ, Matrix.det_mul]
      exact mul_ne_zero (ih (i + 1)) (hm i)

end Prefix

section Protocol

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E]

variable {r : ℕ} {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

include hx hgen in
/-- **The torus protocol.**  At phase `j` the constraint map substitutes the monomial family of the
matrix `m j`. -/
def torusProtocol (m : ℕ → Matrix (Fin r) (Fin r) ℤ) (hm : ∀ j, (m j).det ≠ 0) :
    ℕ → (E →ₐ[C] E) :=
  fun j ↦ torusEndo hx hgen (hm j)

/-- The prefix of a torus protocol substitutes the accumulated matrix. -/
theorem forwardPrefix_torusProtocol (m : ℕ → Matrix (Fin r) (Fin r) ℤ)
    (hm : ∀ j, (m j).det ≠ 0) (i n : ℕ) :
    forwardPrefix (torusProtocol hx hgen m hm) i n
      = torusEndo hx hgen (det_prefixMatrix_ne_zero hm i n) := by
  induction n generalizing i with
  | zero =>
      rw [forwardPrefix]
      exact (torusEndo_one hx hgen (det_prefixMatrix_ne_zero hm i 0)).symm
  | succ n ih =>
      rw [forwardPrefix, ih (i + 1)]
      change (torusEndo hx hgen (hm i)).comp _ = _
      rw [torusEndo_comp]
      exact torusEndo_congr hx hgen _ _ rfl

/-- The prefix image of a torus protocol is the differential field of the accumulated monomial
family. -/
theorem map_forwardPrefix_torusProtocol (m : ℕ → Matrix (Fin r) (Fin r) ℤ)
    (hm : ∀ j, (m j).det ≠ 0) (i n : ℕ) :
    IntermediateField.map (forwardPrefix (torusProtocol hx hgen m hm) i n) ⊤
      = differentialAdjoin C (Set.range (monomialFamily (prefixMatrix m i n) x)) := by
  rw [forwardPrefix_torusProtocol hx hgen m hm i n]
  exact torusEndo_map_top hx hgen (det_prefixMatrix_ne_zero hm i n)

end Protocol

section Group

variable (C : Type*) [Field C] {r : ℕ}

/-- **The torus protocol on the constant torus.** -/
def torusProtocolGroup (m : ℕ → Matrix (Fin r) (Fin r) ℤ) :
    ∀ _ : ℕ, (Fin r → Cˣ) →* (Fin r → Cˣ) :=
  fun j ↦ torusMonomialHom C (m j)

theorem prefixHom_torusProtocolGroup (m : ℕ → Matrix (Fin r) (Fin r) ℤ) (i n : ℕ) :
    prefixHom (torusProtocolGroup C m) i n = torusMonomialHom C (prefixMatrix m i n) := by
  induction n generalizing i with
  | zero =>
      rw [prefixHom, prefixMatrix_zero, torusMonomialHom_one]
  | succ n ih =>
      rw [prefixHom, ih (i + 1), prefixMatrix_succ, torusMonomialHom_mul]
      rfl

theorem prefixKernel_torusProtocolGroup (m : ℕ → Matrix (Fin r) (Fin r) ℤ) (i n : ℕ) :
    prefixKernel (torusProtocolGroup C m) i n = (torusMonomialHom C (prefixMatrix m i n)).ker := by
  rw [prefixKernel, prefixHom_torusProtocolGroup]

end Group

section Tail

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E] [CharZero C] [IsAlgClosed C]

variable {r : ℕ} {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

include hx hgen in
/-- **The phase tail of a torus protocol.**  Every prefix image is the fixed field of its deck
group, so the tail is the fixed field of the closed erased sector of the scaling action. -/
theorem torusProtocol_nonautonomousTail_eq_fixedField
    [TopologicalSpace (Fin r → Cˣ)] [IsTopologicalGroup (Fin r → Cˣ)]
    [DiscreteTopology (Fin r → Cˣ)]
    (m : ℕ → Matrix (Fin r) (Fin r) ℤ) (hm : ∀ j, (m j).det ≠ 0) (i : ℕ) :
    nonautonomousTail (torusProtocol hx hgen m hm) i
      = IntermediateField.fixedField
          ((erasedClosure (torusProtocolGroup C m) i).map (torusScaleRep hx hgen)) := by
  refine nonautonomousTail_eq_fixedField_erasedClosure (torusProtocol hx hgen m hm) i
    (torusProtocolGroup C m) (torusScaleRep hx hgen) (fun n ↦ ?_) (fun z ↦ isClosed_discrete _)
  rw [map_forwardPrefix_torusProtocol hx hgen m hm i n, prefixKernel_torusProtocolGroup]
  exact differentialAdjoin_monomialFamily_eq_fixedField hx hgen
    (det_prefixMatrix_ne_zero hm i n)

end Tail

end

end GaloisForLFunctions.HTGeometry
