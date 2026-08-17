import GaloisForLFunctions.HTGeometry.TriangleTorusDefect

/-!
# Transport of a Dennis–Stein symbol costs exactly `{-1, v}`

The torus factors of the transport and reversal relations collapse: writing
`h(-v) h(-1)⁻¹ = {-1, v} h(v)` and cancelling `h(v)` leaves

```text
⟨a, b⟩_ij · {-1, v}_ik = ⟨-a, -b⟩_ik ,      ⟨a, b⟩_ij · {-1, v}_ji = ⟨-a, -b⟩_ji .
```

Transporting twice returns the original symbol, so the two symbols paid must cancel:

```text
{-1, v}_ik · {-1, v}_ij = 1 .
```

Changing the second index of the pair therefore inverts the symbol `{-1, v}`, which is the first
genuine relation between the symbols of different index pairs.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [CommRing R] {n : Type*} [DecidableEq n] [Fintype n]

/-- **Transporting the second index costs one symbol `{-1, v}`.** -/
theorem dennisStein_transport_symbol {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : R) (v : Rˣ) (hv : (v : R) = 1 + a * b) :
    dennisStein hij a b v * steinbergSymbol hik (-1) v = dennisStein hik (-a) (-b) v := by
  have h := dennisStein_index_transport hij hik hjk a b v hv
  have hc : steinbergTorus hik (-v) * (steinbergTorus hik (-1))⁻¹
      = steinbergSymbol hik (-1) v * steinbergTorus hik v := by
    have h0 := transportCorrection_eq_steinbergSymbol hik v
    rw [transportCorrection] at h0
    calc steinbergTorus hik (-v) * (steinbergTorus hik (-1))⁻¹
        = steinbergTorus hik (-v) * (steinbergTorus hik (-1))⁻¹
          * (steinbergTorus hik v)⁻¹ * steinbergTorus hik v := by group
      _ = steinbergSymbol hik (-1) v * steinbergTorus hik v := by rw [h0]
  rw [hc] at h
  refine mul_right_cancel (b := steinbergTorus hik v) ?_
  rw [← h]
  group

/-- **Reversing the index pair costs one symbol `{-1, v}`.** -/
theorem dennisStein_reversal_symbol {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (a b : R) (v : Rˣ) (hv : (v : R) = 1 + a * b) :
    dennisStein hij a b v * steinbergSymbol (Ne.symm hij) (-1) v
      = dennisStein (Ne.symm hij) (-a) (-b) v := by
  have h := dennisStein_index_reversal hij hik hjk a b v hv
  have hc : steinbergTorus (Ne.symm hij) (-v) * (steinbergTorus (Ne.symm hij) (-1))⁻¹
      = steinbergSymbol (Ne.symm hij) (-1) v * steinbergTorus (Ne.symm hij) v := by
    have h0 := transportCorrection_eq_steinbergSymbol (Ne.symm hij) v
    rw [transportCorrection] at h0
    calc steinbergTorus (Ne.symm hij) (-v) * (steinbergTorus (Ne.symm hij) (-1))⁻¹
        = steinbergTorus (Ne.symm hij) (-v) * (steinbergTorus (Ne.symm hij) (-1))⁻¹
          * (steinbergTorus (Ne.symm hij) v)⁻¹ * steinbergTorus (Ne.symm hij) v := by group
      _ = steinbergSymbol (Ne.symm hij) (-1) v * steinbergTorus (Ne.symm hij) v := by rw [h0]
  rw [hc] at h
  refine mul_right_cancel (b := steinbergTorus (Ne.symm hij) v) ?_
  rw [← h]
  group

/-- **Changing the second index inverts the symbol `{-1, v}`.**  Transporting twice returns the
original Dennis–Stein symbol, so the two symbols paid cancel. -/
theorem steinbergSymbol_neg_one_transport {i j k : n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : Rˣ) :
    steinbergSymbol hik (-1) v * steinbergSymbol hij (-1) v = 1 := by
  have hv : (v : R) = 1 + ((v : R) - 1) * 1 := by ring
  have hv' : (v : R) = 1 + (-((v : R) - 1)) * (-1 : R) := by ring
  have h1 := dennisStein_transport_symbol hij hik hjk ((v : R) - 1) 1 v hv
  have h2 := dennisStein_transport_symbol hik hij (Ne.symm hjk) (-((v : R) - 1)) (-1 : R) v hv'
  rw [neg_neg, neg_neg] at h2
  refine mul_left_cancel (a := dennisStein hij ((v : R) - 1) 1 v) ?_
  rw [mul_one, ← mul_assoc, h1, h2]

/-- **Two of the three transport symbols cancel.**  The symbols of the pairs `(j,i)` and `(j,k)`
share their first index, so changing the second inverts one into the other. -/
theorem steinbergSymbol_neg_one_pair_cancel {i j k : n} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (v : Rˣ) :
    steinbergSymbol (Ne.symm hij) (-1) v * steinbergSymbol hjk (-1) v = 1 := by
  have h := steinbergSymbol_neg_one_transport (Ne.symm hij) hjk hik v
  have hc := Subgroup.mem_center_iff.1 (steinbergSymbol_mem_center hjk (-1 : Rˣ) v hij hik)
  rw [hc (steinbergSymbol (Ne.symm hij) (-1) v)]
  exact h

/-- **The symbol with second argument `1`, reduced.**  Only one transport symbol and the triangle
defect survive. -/
theorem dennisStein_right_one_eq_symbol_defect {i j k : n} (hij : i ≠ j) (hjk : j ≠ k)
    (hik : i ≠ k) (a b : R) (v : Rˣ) (hv : (v : R) = 1 + a * b) :
    dennisStein hik (a * b) 1 v
      = (steinbergSymbol (Ne.symm hjk) (-1) v * torusTriangleDefect hij hjk hik v)⁻¹ := by
  rw [dennisStein_right_one_eq_symbols hij hjk hik a b v hv,
    steinbergSymbol_neg_one_pair_cancel hij hjk hik v, one_mul]

end GaloisForLFunctions.HTGeometry

end
