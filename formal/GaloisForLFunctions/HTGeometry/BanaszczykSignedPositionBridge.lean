import GaloisForLFunctions.HTGeometry.BanaszczykSignRecovery
import GaloisForLFunctions.HTGeometry.ListSignedPositionSum

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem IsSignedSum.neg {vs : List E} {x : E} (hx : IsSignedSum vs x) :
    IsSignedSum vs (-x) := by
  induction hx with
  | nil => simpa using IsSignedSum.nil
  | add hx ih =>
      convert IsSignedSum.sub ih using 1
      module
  | sub hx ih =>
      convert IsSignedSum.add ih using 1
      module

/-- Existing fermionic alternating position sum is a particular Banaszczyk sign assignment. -/
theorem isSignedSum_signedPositionSum_self (vs : List E) :
    IsSignedSum vs (signedPositionSum ℝ vs (fun v _ => v)) := by
  induction vs with
  | nil => simpa using (IsSignedSum.nil : IsSignedSum ([] : List E) 0)
  | cons v vs ih =>
      rw [signedPositionSum_cons]
      have hneg := ih.neg
      convert IsSignedSum.add hneg using 1
      module

/-- The corpus's alternating position sum has an explicit Boolean-sign representation. -/
theorem exists_signs_signedPositionSum_self (vs : List E) :
    ∃ signs : List Bool, signs.length = vs.length ∧
      signedListSum vs signs = signedPositionSum ℝ vs (fun v _ => v) :=
  (isSignedSum_signedPositionSum_self vs).exists_signs

end GaloisForLFunctions.HTGeometry

