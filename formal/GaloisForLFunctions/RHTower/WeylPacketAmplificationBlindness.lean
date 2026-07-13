import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Full-packet rank divisibility is blind to scalar multiplicity

An arbitrary-modulus Hurwitz detour naturally enlarges a scalar local divisor space `V` to a
`q`-component residue packet `Fin q → V`.  Its total rank is therefore `q * finrank ℂ V`, so
divisibility of the packet rank by `q` holds for every scalar multiplicity.  It cannot by itself
imply that the scalar multiplicity is divisible by `q`.

This is the positive algebraic content of the packet-amplification no-go.  A viable arbitrary-
modulus route must construct a source-defined virtual or determinant-line anomaly that removes the
regular packet factor while retaining the projective phase.  The results here are standard finite-
dimensional linear algebra and are not claimed as new scientific knowledge.
-/

open Complex Module

noncomputable section

namespace RHTower

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Free ℂ V]
  [Module.Finite ℂ V]

/-- Amplifying a finite-dimensional complex space by a `q`-component packet multiplies its rank by
`q`. -/
theorem finrank_weylPacketAmplification (q : ℕ) :
    finrank ℂ (Fin q → V) = q * finrank ℂ V := by
  rw [Module.finrank_pi_fintype]
  simp

/-- The total rank of the full `q`-packet is divisible by `q`, independently of the scalar rank. -/
theorem modulus_dvd_finrank_weylPacketAmplification (q : ℕ) :
    q ∣ finrank ℂ (Fin q → V) := by
  rw [Module.finrank_pi_fintype]
  simp

/-- Packet divisibility occurs for every prescribed scalar multiplicity `m`; hence it cannot
constrain that multiplicity without an additional descent or normalization theorem. -/
theorem packetDivisibility_holds_for_every_scalarRank (q m : ℕ) :
    finrank ℂ (Fin m → ℂ) = m ∧
      q ∣ finrank ℂ (Fin q → (Fin m → ℂ)) := by
  constructor
  · exact Module.finrank_fin_fun ℂ
  · rw [Module.finrank_pi_fintype]
    simp

end RHTower
