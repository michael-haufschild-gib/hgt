import GaloisForLFunctions.HTGeometry.DennisSteinIndexIndependent
import GaloisForLFunctions.HTGeometry.DennisSteinTransportSymbol

/-!
# The transport symbol `{-1, v}` is an involution

Transport of a Dennis–Stein symbol to another second index costs `{-1, v}` and negates both
arguments, but the symbol itself does not depend on the second index.  So transporting twice
returns the original symbol while paying the cost twice:

```text
⟨a, b⟩ · {-1, v}_ik · {-1, v}_ik = ⟨a, b⟩ ,      hence      {-1, v}_ik² = 1 .
```

Combined with `{-1,v}_ik · {-1,v}_ij = 1`, all six transport symbols of a triple coincide, and each
is its own inverse.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **The transport symbol squares to one.** -/
theorem steinbergSymbol_neg_one_sq {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : Rˣ) :
    steinbergSymbol hik (-1) v * steinbergSymbol hik (-1) v = 1 := by
  have hv : (v : R) = 1 + ((v : R) - 1) * 1 := by ring
  have hv' : (v : R) = 1 + (-((v : R) - 1)) * (-1 : R) := by ring
  have h1 := dennisStein_transport_symbol hij hik hjk ((v : R) - 1) 1 v hv
  have h2 := dennisStein_transport_symbol hij hik hjk (-((v : R) - 1)) (-1 : R) v hv'
  rw [neg_neg, neg_neg] at h2
  have hind1 := dennisStein_index_independent hij hik hjk (-((v : R) - 1)) (-1 : R) v hv'
  have hind2 := dennisStein_index_independent hij hik hjk ((v : R) - 1) 1 v hv
  rw [← hind1] at h1
  rw [← hind2] at h2
  refine mul_left_cancel (a := dennisStein hij ((v : R) - 1) 1 v) ?_
  rw [mul_one, ← mul_assoc, h1, h2]

/-- **All transport symbols of a triple coincide.** -/
theorem steinbergSymbol_neg_one_index_eq {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : Rˣ) :
    steinbergSymbol hij (-1) v = steinbergSymbol hik (-1) v := by
  have h1 := steinbergSymbol_neg_one_transport hij hik hjk v
  have h2 := steinbergSymbol_neg_one_sq hij hik hjk v
  refine mul_left_cancel (a := steinbergSymbol hik (-1) v) ?_
  rw [h1, h2]

end GaloisForLFunctions.HTGeometry

end
