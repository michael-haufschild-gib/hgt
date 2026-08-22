import GaloisForLFunctions.HTGeometry.PerfectUnitaryLinkFlatness
import GaloisForLFunctions.HTGeometry.RationalNonabelianContextAnomaly

/-!
# Directional Wilson reciprocity for passive block kernels

Non-Abelian loop order and nonreciprocal loop orientation are different invariants.  Reversing a
plaquette whose backward links are the adjoints of its forward links conjugates its Wilson trace.
Its real part and modulus are therefore orientation-blind, without commutativity or unitarity.

Positive semidefinite block kernels automatically satisfy this reverse-adjoint law.  In particular,
the corpus's explicit rational positive Gram sector has noncommuting Wilson loops while every
clockwise/counterclockwise real-trace contrast still vanishes.  Thus a directional Wilson contrast
cannot be produced by passive Hilbert/Gram positivity alone; it requires an active non-Hermitian
source law that breaks reverse-adjoint reciprocity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Matrix
open scoped ComplexOrder

section DirectionalWilson

variable {I A : Type*} [Fintype A]

/-- Wilson trace around the ordered plaquette `a → b → c → d → a`. -/
def directionalWilsonPlaquetteTrace
    (link : I → I → Matrix A A ℂ) (a b c d : I) : ℂ :=
  Matrix.trace (link a b * link b c * link c d * link d a)

/-- Wilson trace around the oppositely oriented plaquette. -/
def reverseDirectionalWilsonPlaquetteTrace
    (link : I → I → Matrix A A ℂ) (a b c d : I) : ℂ :=
  Matrix.trace (link a d * link d c * link c b * link b a)

/-- Reverse-adjoint reciprocity conjugates the complete plaquette trace. -/
theorem reverseDirectionalWilsonPlaquetteTrace_eq_conj
    (link : I → I → Matrix A A ℂ)
    (hreciprocal : ∀ i j, link j i = (link i j)ᴴ)
    (a b c d : I) :
    reverseDirectionalWilsonPlaquetteTrace link a b c d =
      starRingEnd ℂ (directionalWilsonPlaquetteTrace link a b c d) := by
  rw [reverseDirectionalWilsonPlaquetteTrace, directionalWilsonPlaquetteTrace,
    hreciprocal d a, hreciprocal c d, hreciprocal b c, hreciprocal a b]
  calc
    Matrix.trace
        ((link d a)ᴴ * (link c d)ᴴ * (link b c)ᴴ * (link a b)ᴴ) =
        Matrix.trace ((link a b * link b c * link c d * link d a)ᴴ) := by
      congr 1
      simp only [Matrix.conjTranspose_mul]
      noncomm_ring
    _ = starRingEnd ℂ
        (Matrix.trace (link a b * link b c * link c d * link d a)) :=
      Matrix.trace_conjTranspose _

/-- A passive reciprocal plaquette has no signed real clockwise/counterclockwise contrast. -/
theorem reverseDirectionalWilsonPlaquetteTrace_re_eq
    (link : I → I → Matrix A A ℂ)
    (hreciprocal : ∀ i j, link j i = (link i j)ᴴ)
    (a b c d : I) :
    (reverseDirectionalWilsonPlaquetteTrace link a b c d).re =
      (directionalWilsonPlaquetteTrace link a b c d).re := by
  rw [reverseDirectionalWilsonPlaquetteTrace_eq_conj link hreciprocal]
  simp

/-- A passive reciprocal plaquette also has no absolute clockwise/counterclockwise contrast. -/
theorem reverseDirectionalWilsonPlaquetteTrace_norm_eq
    (link : I → I → Matrix A A ℂ)
    (hreciprocal : ∀ i j, link j i = (link i j)ᴴ)
    (a b c d : I) :
    ‖reverseDirectionalWilsonPlaquetteTrace link a b c d‖ =
      ‖directionalWilsonPlaquetteTrace link a b c d‖ := by
  rw [reverseDirectionalWilsonPlaquetteTrace_eq_conj link hreciprocal,
    RCLike.norm_conj]

end DirectionalWilson

section PassiveBlockKernel

variable {I A : Type*} [Fintype A] [DecidableEq A]

omit [Fintype A] in
/-- Every positive block kernel has reverse links equal to forward-link adjoints. -/
theorem NormalizedBlockKernel.link_reverse_of_posSemidef
    (K : NormalizedBlockKernel I A) (hK : K.matrix.PosSemidef) (i j : I) :
    K.link j i = (K.link i j)ᴴ := by
  ext a b
  change K.matrix (j, a) (i, b) = star (K.matrix (i, b) (j, a))
  exact (hK.isHermitian.apply (j, a) (i, b)).symm

/-- Positive block kernels are signed-real orientation blind. -/
theorem normalizedBlockKernel_reverseDirectionalWilson_re_eq
    (K : NormalizedBlockKernel I A) (hK : K.matrix.PosSemidef) (a b c d : I) :
    (reverseDirectionalWilsonPlaquetteTrace K.link a b c d).re =
      (directionalWilsonPlaquetteTrace K.link a b c d).re :=
  reverseDirectionalWilsonPlaquetteTrace_re_eq K.link
    (K.link_reverse_of_posSemidef hK) a b c d

/-- Positive block kernels are absolute-Wilson orientation blind. -/
theorem normalizedBlockKernel_reverseDirectionalWilson_norm_eq
    (K : NormalizedBlockKernel I A) (hK : K.matrix.PosSemidef) (a b c d : I) :
    ‖reverseDirectionalWilsonPlaquetteTrace K.link a b c d‖ =
      ‖directionalWilsonPlaquetteTrace K.link a b c d‖ :=
  reverseDirectionalWilsonPlaquetteTrace_norm_eq K.link
    (K.link_reverse_of_posSemidef hK) a b c d

end PassiveBlockKernel

section RationalNonabelianSeparation

/-- Reverse links in the explicit rational Wilson Gram sector are adjoints. -/
theorem rationalWilsonLink_reverse (r : ℕ) (i j : Fin (r + 4)) :
    rationalWilsonLink r j i = (rationalWilsonLink r i j)ᴴ := by
  ext a b
  change rationalWilsonGram r (j, a) (i, b) =
    star (rationalWilsonGram r (i, b) (j, a))
  exact ((rationalWilsonGram_posSemidef r).isHermitian.apply (j, a) (i, b)).symm

/-- **Non-Abelian/passive separation.**  One exact positive Gram sector has noncommuting Wilson
loops at every context order, yet every directional real-trace contrast is zero. -/
theorem rationalWilson_nonabelian_and_directionally_reciprocal (r : ℕ) :
    rationalWilsonLoopX r * rationalWilsonLoopY r -
        rationalWilsonLoopY r * rationalWilsonLoopX r ≠ 0 ∧
      ∀ a b c d : Fin (r + 4),
        (reverseDirectionalWilsonPlaquetteTrace (rationalWilsonLink r) a b c d).re -
          (directionalWilsonPlaquetteTrace (rationalWilsonLink r) a b c d).re = 0 := by
  refine ⟨rationalWilsonLoops_commutator_ne_zero r, ?_⟩
  intro a b c d
  rw [reverseDirectionalWilsonPlaquetteTrace_re_eq
    (rationalWilsonLink r) (rationalWilsonLink_reverse r)]
  ring

end RationalNonabelianSeparation

end

end GaloisForLFunctions.HTGeometry
