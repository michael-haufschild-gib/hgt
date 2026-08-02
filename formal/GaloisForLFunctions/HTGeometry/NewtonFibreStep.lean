import GaloisForLFunctions.HTGeometry.CoprimeSplit

/-!
# One Newton step for a deformed critical fibre

Lifting a point of a critical fibre along a deformation of the observation is a Newton iteration.
The state is a pair of displacements `(P, Q)` below the two critical orders, the residual is the
inversion error over the horizon, and one step solves the *linearised* equation at the undeformed
pair — which `existsUnique_coprimeSplit` does exactly, over any ring.

The content of this module is the step's algebra: after correcting by the solution of the linearised
equation, the new error is a sum of products in which every factor is a displacement or a
deformation.  So if all of those lie in an ideal `I`, the new error lies in `I` times the previous
data, and the iteration contracts.  Nothing here needs completeness; completeness is only what turns
the contraction into a limit.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {S : Type*} [CommRing S]

/-- The inversion error of a pair over the horizon. -/
noncomputable def inversionError (Z W : S[X]) : S[X] := Z * W - 1

theorem inversionError_add (Z W dZ dW : S[X]) :
    inversionError (Z + dZ) (W + dW)
      = inversionError Z W + dZ * W + Z * dW + dZ * dW := by
  simp only [inversionError]
  ring

/-- **The Newton step.**  If `E` is the error over the horizon and `(dP, dQ)` solves the linearised
equation `dP B + A dQ = -E` at the undeformed pair `(A, B)`, then the corrected pair has error

`dP (W - B) + (Z - A) dQ + dP dQ`

over the horizon: every term carries a displacement or a deformation as a factor. -/
theorem inversionError_newton_step {L : ℕ} (A B Z W dP dQ E : S[X])
    (hE : (X : S[X]) ^ L ∣ inversionError Z W - E)
    (hsplit : dP * B + A * dQ = -E) :
    (X : S[X]) ^ L ∣ inversionError (Z + dP) (W + dQ)
      - (dP * (W - B) + (Z - A) * dQ + dP * dQ) := by
  have hid : inversionError (Z + dP) (W + dQ)
      - (dP * (W - B) + (Z - A) * dQ + dP * dQ)
      = (inversionError Z W - E) + (E + (dP * B + A * dQ)) := by
    simp only [inversionError]
    ring
  rw [hid, hsplit, add_neg_cancel, add_zero]
  exact hE

/-- **The Newton step is always available.**  Over any ring, for a monic coprime pair of the two
critical degrees, the linearised equation has a unique solution with the right degrees, so the step
can be taken and its result is determined. -/
theorem exists_newton_step [Nontrivial S] {m n : ℕ} {A B : S[X]} (hA : A.Monic)
    (hAdeg : A.natDegree = m) (hBdeg : B.natDegree ≤ n) (hm : 0 < m) (hn : 0 < n)
    (hcop : IsCoprime A B) (Z W E : S[X]) (hE : E.natDegree < m + n)
    (herr : (X : S[X]) ^ (m + n) ∣ inversionError Z W - E) :
    ∃ dP dQ : S[X], dP.natDegree < m ∧ dQ.natDegree < n ∧
      (X : S[X]) ^ (m + n) ∣ inversionError (Z + dP) (W + dQ)
        - (dP * (W - B) + (Z - A) * dQ + dP * dQ) := by
  obtain ⟨⟨dP, dQ⟩, ⟨hdP, hdQ, hsplit⟩, -⟩ :=
    existsUnique_coprimeSplit hA hAdeg hBdeg hm hn hcop
      (E := -E) (by rw [Polynomial.natDegree_neg]; exact hE)
  exact ⟨dP, dQ, hdP, hdQ, inversionError_newton_step A B Z W dP dQ E herr hsplit⟩

/-- **The initial error of a deformation.**  Deforming a pure factorisation by adding `Γ` and `Γ'`
to its two factors changes the error over the horizon by terms each carrying a deformation. -/
theorem inversionError_deformation {L : ℕ} (A B Γ Γ' : S[X])
    (hAB : (X : S[X]) ^ L ∣ inversionError A B) :
    (X : S[X]) ^ L ∣ inversionError (A + Γ) (B + Γ')
      - (Γ * B + A * Γ' + Γ * Γ') := by
  have hid : inversionError (A + Γ) (B + Γ') - (Γ * B + A * Γ' + Γ * Γ')
      = inversionError A B := by
    simp only [inversionError]
    ring
  rw [hid]
  exact hAB

end GaloisForLFunctions.HTGeometry
