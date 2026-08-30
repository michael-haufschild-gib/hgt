import GaloisForLFunctions.HTGeometry.RittSecondJetAffineConnection
import GaloisForLFunctions.HTGeometry.RationalAffineConnection

/-!
# The frame relation is the rational affine-connection equation

A Ritt frame whose base is the rational function field, whose base endomorphism is substitution by a
polynomial `R`, whose chain-rule factor is `R′` and whose base derivation is the ordinary one turns
the conclusion of `exists_affineConnection_of_secondJet_mem`,

`ψ(a)·ρ = a − dK ρ / ρ`,

into `a(R)·(R′)² = R′·a − R″` on multiplying by `R′`.  That is `IsAffineConnection`, so the corpus's
non-existence results for concrete maps apply verbatim to a linearizer with a rational second jet.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {C : Type*} [Field C] [CharZero C]

omit [CharZero C] in
/-- The frame's second-jet relation is the rational affine-connection equation. -/
theorem isAffineConnection_of_ritt_relation {R : C[X]}
    {hR : ¬ ∃ c : C, (algebraMap C[X] (RatFunc C) R) = RatFunc.C c}
    (hd : (algebraMap C[X] (RatFunc C) (derivative R)) ≠ 0) {a : RatFunc C}
    (hrel : ratFuncSubstitutionAlgHom (algebraMap C[X] (RatFunc C) R) hR a
        * algebraMap C[X] (RatFunc C) (derivative R)
      = a - algebraMap C[X] (RatFunc C) (derivative (derivative R))
          / algebraMap C[X] (RatFunc C) (derivative R)) :
    IsAffineConnection R hR a := by
  rw [IsAffineConnection, map_pow]
  field_simp at hrel
  linear_combination hrel

end GaloisForLFunctions.HTGeometry
