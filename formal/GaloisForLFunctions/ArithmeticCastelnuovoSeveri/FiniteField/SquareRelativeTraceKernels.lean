import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteField.FrobeniusTraceKernels
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.KummerParameterCardinality
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FiniteField.SquareFieldTraceFibers

/-!
# Relative trace kernels inside the square constant field

The trace kernel in the square field already lies in its middle fixed
field. Descent to that field gives the exact number of trace-zero
translation parameters without an assumed trace-surjectivity statement.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open ArithmeticHarmonicAnalysis
variable (p : ℕ) [Fact p.Prime] (d m : ℕ)

/-- The actual relative-trace kernel in the prescribed square constant field. -/
def SquareRelativeTraceKernel :=
  {x : SquareConstantField p (kummerSquareIndex d m) //
    frobeniusTraceSum p (d + 1) (m + 1) x = 0}

/-- Trace-zero translation parameters lie in the middle fixed field. -/
theorem squareRelativeTraceKernel_fixed (x : SquareRelativeTraceKernel p d m) :
    x.val ∈ squareFrobeniusFixedField p (kummerSquareIndex d m) := by
  change x.val ^ p ^ (kummerSquareIndex d m + 1) = x.val
  exact (congrArg (fun N : ℕ => x.val ^ p ^ N) (kummerSquareIndex_succ d m)).trans
    (frobeniusTraceSum_zero_fixed p d m x.property)

/-- The square-field trace kernel has exactly `q^m` elements for a trace of length `m+1`. -/
theorem squareRelativeTraceKernel_card :
    Nat.card (SquareRelativeTraceKernel p d m) = p ^ ((d + 1) * m) := by
  let E := squareFrobeniusFixedField p (kummerSquareIndex d m)
  letI : CharP E p := inferInstance
  have hmap (x : E) :
      (frobeniusTraceSum p (d + 1) (m + 1) x : E).val =
        frobeniusTraceSum p (d + 1) (m + 1) x.val :=
    frobeniusTraceSum_map p E.subtype (d + 1) (m + 1) x
  let e : SquareRelativeTraceKernel p d m ≃
      {x : E // frobeniusTraceSum p (d + 1) (m + 1) x = 0} :=
    { toFun := fun x => ⟨⟨x.val, squareRelativeTraceKernel_fixed p d m x⟩, by
        apply E.subtype.injective
        exact (hmap ⟨x.val, squareRelativeTraceKernel_fixed p d m x⟩).trans x.property⟩
      invFun := fun x => ⟨x.val.val, by
        exact (hmap x.val).symm.trans (congrArg (fun a : E => a.val) x.property)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  exact frobeniusTraceSum_kernel_card p d m
    ((squareFrobeniusFixedField_card p (kummerSquareIndex d m)).trans
      (congrArg (p ^ ·) (kummerSquareIndex_succ d m)))

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
