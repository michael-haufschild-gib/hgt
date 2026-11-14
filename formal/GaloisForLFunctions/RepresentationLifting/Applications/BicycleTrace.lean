import GaloisForLFunctions.QECLean.Stabilizer.Framework.Homological.BBChainComplex
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Modular trace for bicycle-code convolution operators

Translation-invariant matrices are exactly convolution matrices, with unique coefficient
functions. Their trace retains only the coefficient at zero, multiplied by the group order.
For every torus with an even side length, this scalar trace vanishes over `ZMod 2`, although
the full matrix still recovers every coefficient. This applies the regular-module trace
mechanism of Scavia's Lemma 6.3 to the existing bicycle-code convolution.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting

open Quantum.Stabilizer.Homological.BB

variable {G : Type} [Fintype G] [AddCommGroup G]

/-- Matrix of the convolution used by the bicycle-code boundary maps. -/
def bicycleConvolutionMatrix (a : G → ZMod 2) : Matrix G G (ZMod 2) :=
  fun x y => a (x - y)

theorem bicycleConvolutionMatrix_mulVec (a v : G → ZMod 2) :
    (bicycleConvolutionMatrix a).mulVec v = conv a v := by
  rw [conv_comm a v]
  ext x
  simp only [Matrix.mulVec, dotProduct, bicycleConvolutionMatrix, conv_apply]
  apply Finset.sum_congr rfl
  intro y _
  exact mul_comm _ _

theorem trace_bicycleConvolutionMatrix (a : G → ZMod 2) :
    Matrix.trace (bicycleConvolutionMatrix a) = (Fintype.card G : ZMod 2) * a 0 := by
  simp [Matrix.trace, Matrix.diag, bicycleConvolutionMatrix, nsmul_eq_mul]

omit [Fintype G] in
theorem bicycleConvolutionMatrix_translate (a : G → ZMod 2) (g x y : G) :
    bicycleConvolutionMatrix a (g + x) (g + y) = bicycleConvolutionMatrix a x y := by
  simp [bicycleConvolutionMatrix]

omit [Fintype G] in
theorem bicycleConvolutionMatrix_injective :
    Function.Injective (bicycleConvolutionMatrix (G := G)) := by
  intro a b h
  funext x
  simpa only [bicycleConvolutionMatrix, sub_zero] using congrFun (congrFun h x) 0

omit [Fintype G] in
/-- Translation symmetry determines exactly one convolution kernel. -/
theorem bicycleConvolutionMatrix_classification (T : Matrix G G (ZMod 2)) :
    (∀ g x y, T (g + x) (g + y) = T x y) ↔
      ∃! a : G → ZMod 2, bicycleConvolutionMatrix a = T := by
  constructor
  · intro h
    refine ⟨fun x => T x 0, ?_, ?_⟩
    · ext x y
      simpa [bicycleConvolutionMatrix, sub_eq_add_neg, add_comm] using h (-y) x y
    · intro a ha
      funext x
      simpa [bicycleConvolutionMatrix] using congrFun (congrFun ha x) 0
  · rintro ⟨a, rfl, _⟩
    exact bicycleConvolutionMatrix_translate a

/-- Every convolution operator on an even-sided bicycle torus is traceless. -/
theorem bicycle_even_torus_trace (l m : ℕ)
    (a : ZMod (2 * (l + 1)) × ZMod (m + 1) → ZMod 2) :
    Matrix.trace (bicycleConvolutionMatrix a) = 0 := by
  rw [trace_bicycleConvolutionMatrix]
  have h2 : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
  simp [Fintype.card_prod, ZMod.card, Nat.cast_mul, h2]

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.bicycleConvolutionMatrix_mulVec
#print axioms GaloisForLFunctions.RepresentationLifting.bicycleConvolutionMatrix_classification
#print axioms GaloisForLFunctions.RepresentationLifting.bicycle_even_torus_trace
