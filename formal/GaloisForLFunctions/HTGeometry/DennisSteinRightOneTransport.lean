import GaloisForLFunctions.HTGeometry.DennisSteinTransportSymbol
import GaloisForLFunctions.HTGeometry.SteinbergTorusPairing

/-!
# Transporting the symbol with second argument `1`

Moving `⟨x, 1⟩` from the pair `(i,k)` to the pair `(i,j)` costs one symbol `{-1, v}` and turns the
arguments into `(-x, -1)`; normalising the second argument back to `1` — legitimate because `-1` is a
unit — costs one commutator of tori.  Together:

```text
⟨x, 1⟩_ik · {-1, v}_ij = ⟨x, 1⟩_ij · [ h_ij(v), h_ik(-1) ] ,      v = 1 + x .
```

Both sides of the classical `⟨x,1⟩ = 0` therefore move between index pairs at a cost that is written
entirely in tori and symbols.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **Transport of the symbol with second argument `1`.** -/
theorem dennisStein_right_one_transport {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : R) (v : Rˣ) (hv : (v : R) = 1 + x) :
    dennisStein hik x 1 v * steinbergSymbol hij (-1) v
      = dennisStein hij x 1 v * torusCommutator hij hik v (-1) := by
  have hv1 : (v : R) = 1 + x * 1 := by rw [hv]; ring
  have hunit : ((((-1 : Rˣ)) : R)) = (-1 : R) := by simp
  have hv2 : (v : R) = 1 + (-x) * ((((-1 : Rˣ)) : R)) := by rw [hunit, hv]; ring
  have h1 := dennisStein_transport_symbol hik hij (Ne.symm hjk) x 1 v hv1
  have h2 := dennisStein_normalize_right hij hik hjk (-x) (-1 : Rˣ) v hv2
  rw [hunit, show ((-1 : R) * -x) = x from by ring] at h2
  rw [h1, h2, torusCommutator]

/-- **The relation between the two triangle defects.**  Substituting the torus evaluation of
`⟨x,1⟩` in both index pairs into the transport relation leaves an identity with no Dennis–Stein
symbol in it: the two defects, the three transport symbols and the commutator pairing. -/
theorem torusTriangleDefect_relation {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (v : Rˣ) :
    (steinbergSymbol (Ne.symm hjk) (-1) v * torusTriangleDefect hij hjk hik v)⁻¹
        * steinbergSymbol hij (-1) v
      = (steinbergSymbol hjk (-1) v * torusTriangleDefect hik (Ne.symm hjk) hij v)⁻¹
        * torusCommutator hij hik v (-1) := by
  have hx : (v : R) = 1 + ((v : R) - 1) := by ring
  have hx1 : (v : R) = 1 + ((v : R) - 1) * 1 := by ring
  have ht := dennisStein_right_one_transport hij hik hjk ((v : R) - 1) v hx
  have e1 := dennisStein_right_one_eq_symbol_defect hij hjk hik ((v : R) - 1) 1 v hx1
  have e2 := dennisStein_right_one_eq_symbol_defect hik (Ne.symm hjk) hij ((v : R) - 1) 1 v hx1
  rw [mul_one] at e1 e2
  rw [e1, e2] at ht
  exact ht

/-- **Reversing the pair twice returns the symbol, so the two reversal symbols cancel.** -/
theorem steinbergSymbol_neg_one_reversal {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : Rˣ) :
    steinbergSymbol (Ne.symm hij) (-1) v * steinbergSymbol hij (-1) v = 1 := by
  have hv : (v : R) = 1 + ((v : R) - 1) * 1 := by ring
  have hv' : (v : R) = 1 + (-((v : R) - 1)) * (-1 : R) := by ring
  have h1 := dennisStein_reversal_symbol hij hik hjk ((v : R) - 1) 1 v hv
  have h2 := dennisStein_reversal_symbol (Ne.symm hij) hjk hik
    (-((v : R) - 1)) (-1 : R) v hv'
  rw [neg_neg, neg_neg] at h2
  refine mul_left_cancel (a := dennisStein hij ((v : R) - 1) 1 v) ?_
  rw [mul_one, ← mul_assoc, h1, h2]

/-- **Reversal transport of the symbol with second argument `1`.** -/
theorem dennisStein_right_one_reversal {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (x : R) (v : Rˣ) (hv : (v : R) = 1 + x) :
    dennisStein hij x 1 v * steinbergSymbol (Ne.symm hij) (-1) v
      = dennisStein (Ne.symm hij) x 1 v * torusCommutator (Ne.symm hij) hjk v (-1) := by
  have hv1 : (v : R) = 1 + x * 1 := by rw [hv]; ring
  have hunit : ((((-1 : Rˣ)) : R)) = (-1 : R) := by simp
  have hv2 : (v : R) = 1 + (-x) * ((((-1 : Rˣ)) : R)) := by rw [hunit, hv]; ring
  have h1 := dennisStein_reversal_symbol hij hik hjk x 1 v hv1
  have h2 := dennisStein_normalize_right (Ne.symm hij) hjk hik (-x) (-1 : Rˣ) v hv2
  rw [hunit, show ((-1 : R) * -x) = x from by ring] at h2
  rw [h1, h2, torusCommutator]

/-- **The commutator pairings of a pair and its reverse are inverse.**  Comparing the two ways of
carrying `⟨1-v, -1⟩` to the reversed pair — normalise then reverse, or reverse then normalise —
cancels everything but the two pairings. -/
theorem torusCommutator_reversal {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (v : Rˣ) :
    torusCommutator hij hik v (-1) = (torusCommutator (Ne.symm hij) hjk v (-1))⁻¹ := by
  have hunit : ((((-1 : Rˣ)) : R)) = (-1 : R) := by simp
  have hw : (v : R) = 1 + (1 - (v : R)) * ((((-1 : Rˣ)) : R)) := by rw [hunit]; ring
  have hw' : (v : R) = 1 + (1 - (v : R)) * (-1 : R) := by ring
  have hv : (v : R) = 1 + ((v : R) - 1) := by ring
  have hSc := Subgroup.mem_center_iff.1
    (steinbergSymbol_mem_center (Ne.symm hij) (-1 : Rˣ) v (Ne.symm hjk) (Ne.symm hik))
  have hn := dennisStein_normalize_right hij hik hjk (1 - (v : R)) (-1 : Rˣ) v hw
  rw [hunit, show ((-1 : R) * (1 - (v : R))) = (v : R) - 1 from by ring] at hn
  have hr := dennisStein_reversal_symbol hij hik hjk (1 - (v : R)) (-1 : R) v hw'
  rw [show (-(1 - (v : R))) = (v : R) - 1 from by ring, neg_neg] at hr
  have hro := dennisStein_right_one_reversal hij hik hjk ((v : R) - 1) v hv
  rw [torusCommutator] at hro
  have hro' : dennisStein (Ne.symm hij) ((v : R) - 1) 1 v
      = dennisStein hij ((v : R) - 1) 1 v * steinbergSymbol (Ne.symm hij) (-1) v
        * (steinbergTorus (Ne.symm hij) v * steinbergTorus hjk (-1)
          * (steinbergTorus (Ne.symm hij) v)⁻¹ * (steinbergTorus hjk (-1))⁻¹)⁻¹ := by
    calc dennisStein (Ne.symm hij) ((v : R) - 1) 1 v
        = dennisStein (Ne.symm hij) ((v : R) - 1) 1 v
          * (steinbergTorus (Ne.symm hij) v * steinbergTorus hjk (-1)
            * (steinbergTorus (Ne.symm hij) v)⁻¹ * (steinbergTorus hjk (-1))⁻¹)
          * (steinbergTorus (Ne.symm hij) v * steinbergTorus hjk (-1)
            * (steinbergTorus (Ne.symm hij) v)⁻¹ * (steinbergTorus hjk (-1))⁻¹)⁻¹ := by group
      _ = dennisStein hij ((v : R) - 1) 1 v * steinbergSymbol (Ne.symm hij) (-1) v
          * (steinbergTorus (Ne.symm hij) v * steinbergTorus hjk (-1)
            * (steinbergTorus (Ne.symm hij) v)⁻¹ * (steinbergTorus hjk (-1))⁻¹)⁻¹ := by
          rw [← hro]
  rw [hn, hro'] at hr
  rw [torusCommutator, torusCommutator]
  have h1 : dennisStein hij ((v : R) - 1) 1 v
        * ((steinbergTorus hij v * steinbergTorus hik (-1) * (steinbergTorus hij v)⁻¹
            * (steinbergTorus hik (-1))⁻¹) * steinbergSymbol (Ne.symm hij) (-1) v)
      = dennisStein hij ((v : R) - 1) 1 v
        * (steinbergSymbol (Ne.symm hij) (-1) v
          * (steinbergTorus (Ne.symm hij) v * steinbergTorus hjk (-1)
            * (steinbergTorus (Ne.symm hij) v)⁻¹ * (steinbergTorus hjk (-1))⁻¹)⁻¹) := by
    rw [← mul_assoc, ← mul_assoc]
    exact hr
  have h2 := mul_left_cancel h1
  rw [hSc (steinbergTorus hij v * steinbergTorus hik (-1) * (steinbergTorus hij v)⁻¹
    * (steinbergTorus hik (-1))⁻¹)] at h2
  exact mul_left_cancel h2

end GaloisForLFunctions.HTGeometry

end
