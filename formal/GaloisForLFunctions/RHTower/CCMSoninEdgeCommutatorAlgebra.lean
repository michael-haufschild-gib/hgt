import Mathlib

/-!
# The exact resolvent dressing of the Sonin edge commutator

The card's section "Exact resolvent dressing of the edge trace" is a chain of purely algebraic
commutator identities, proved here in an arbitrary ring:

* `(10)`: with `Q₀ = 1 − P − B` and `[X,P] = 0`, the formal complement contributes `[X,Q₀] = −[X,B]`;
* `(6e)`: with `T = B A B` and `[X,A] = 0`, `[X,T] = [X,B] A B + B A [X,B]`;
* `(6d)`: with `V = (1−T)^{-1}`, `[X,V] = V [X,T] V`;
* `(6c)`: with `Q = E − E V B E` and `[X,E] = 0`,

```text
[X,Q] = −E V ( ([X,B] A B + B A [X,B]) V B + [X,B] ) E .
```

Every term factors through the *same* universal edge distribution `[X,B]`: the Hilbert–Schmidt
projection correction dresses the edge bundle by the prolate resolvent, it does not introduce new
position defects.

The distributional edge formula `(3)`–`(4)`, the Sobolev domain failure `(14)`, and the rigged
extension making `(6c)` an operator identity are cited parents and stay outside the Lean statement.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

variable {R : Type*} [Ring R]

/-! ## The formal complement -/

/-- **Equation (10).**  The formal Sonin complement contributes exactly minus the edge
commutator. -/
theorem commutator_formal_complement {X P B Q0 : R} (hQ : Q0 = 1 - P - B)
    (hXP : X * P - P * X = 0) :
    X * Q0 - Q0 * X = -(X * B - B * X) := by
  rw [hQ]
  have hexp : X * (1 - P - B) - (1 - P - B) * X
      = -(X * P - P * X) - (X * B - B * X) := by noncomm_ring
  rw [hexp, hXP]
  noncomm_ring

/-! ## The Leibniz rule for the alternating block -/

/-- **Equation (6e).**  The commutator of the alternating block factors through the edge
commutator. -/
theorem commutator_alternating_block {X A B T : R} (hT : T = B * A * B)
    (hXA : X * A - A * X = 0) :
    X * T - T * X = (X * B - B * X) * A * B + B * A * (X * B - B * X) := by
  rw [hT]
  have hexp : X * (B * A * B) - (B * A * B) * X
      = (X * B - B * X) * A * B + B * (X * A - A * X) * B
        + B * A * (X * B - B * X) := by noncomm_ring
  rw [hexp, hXA]
  noncomm_ring

/-! ## The inverse-commutator identity -/

/-- **Equation (6d).**  The resolvent commutator is the conjugated block commutator. -/
theorem commutator_resolvent {X V T : R} (hV1 : V * (1 - T) = 1) (hV2 : (1 - T) * V = 1) :
    X * V - V * X = V * (X * T - T * X) * V := by
  have hTV : T * V = V - 1 := by
    have h : V - T * V = 1 := by
      rw [← hV2]
      noncomm_ring
    calc T * V = V - (V - T * V) := by noncomm_ring
      _ = V - 1 := by rw [h]
  have hVT : V * T = V - 1 := by
    have h : V - V * T = 1 := by
      rw [← hV1]
      noncomm_ring
    calc V * T = V - (V - V * T) := by noncomm_ring
      _ = V - 1 := by rw [h]
  have hrhs : V * (X * T - T * X) * V = V * X * (T * V) - (V * T) * X * V := by noncomm_ring
  rw [hrhs, hTV, hVT]
  noncomm_ring

/-! ## The exact projection commutator -/

/-- **Equation (6c).**  Every term of the exact position anomaly factors through the universal edge
commutator, dressed by the prolate resolvent. -/
theorem commutator_exactProjection {X A B E V T Q : R} (hT : T = B * A * B)
    (hV1 : V * (1 - T) = 1) (hV2 : (1 - T) * V = 1)
    (hQ : Q = E - E * V * B * E)
    (hXE : X * E - E * X = 0) (hXA : X * A - A * X = 0) :
    X * Q - Q * X
      = -(E * V * (((X * B - B * X) * A * B + B * A * (X * B - B * X)) * V * B
          + (X * B - B * X)) * E) := by
  have hXEcomm : X * E = E * X := by
    calc X * E = (X * E - E * X) + E * X := by noncomm_ring
      _ = E * X := by rw [hXE]; abel
  have hstep : X * Q - Q * X = -(E * (X * (V * B) - (V * B) * X) * E) := by
    rw [hQ]
    have hexp : X * (E - E * V * B * E) - (E - E * V * B * E) * X
        = (X * E - E * X) - (X * E * V * B * E - E * V * B * E * X) := by noncomm_ring
    rw [hexp, hXE]
    have hpull : X * E * V * B * E - E * V * B * E * X
        = E * (X * (V * B) - (V * B) * X) * E := by
      have h1 : X * E * V * B * E = E * X * V * B * E := by rw [hXEcomm]
      have h2 : E * V * B * E * X = E * V * B * X * E := by
        rw [show E * V * B * E * X = E * V * B * (E * X) by noncomm_ring, ← hXEcomm]
        noncomm_ring
      rw [h1, h2]
      noncomm_ring
    rw [hpull]
    noncomm_ring
  have hVB : X * (V * B) - (V * B) * X
      = (X * V - V * X) * B + V * (X * B - B * X) := by noncomm_ring
  have hres := commutator_resolvent hV1 hV2 (X := X)
  have hblock := commutator_alternating_block hT hXA (X := X)
  rw [hstep, hVB, hres, hblock]
  noncomm_ring

end GaloisForLFunctions.RHTower

end
