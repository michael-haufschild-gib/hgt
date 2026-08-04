import GaloisForLFunctions.HTGeometry.NonautonomousStableCore

/-!
# Autonomous tails as constant nonautonomous tails

The prefix of a constant protocol is the corresponding iterate.  Consequently its
nonautonomous tail is definitionally the stable range core of the single endomorphism.  This
bridge lets concrete nonautonomous tail classifications discharge autonomous isogeny-tail
statements without duplicating either theory.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A length-`n` prefix of a constant protocol is the `n`-th iterate of its endomorphism. -/
theorem forwardPrefix_const
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (phi : F →ₐ[K] F) (i n : ℕ) :
    forwardPrefix (fun _ => phi) i n = phi ^ n := by
  induction n generalizing i with
  | zero =>
      ext x
      rfl
  | succ n ih =>
      ext x
      rw [forwardPrefix_succ_apply, ih, pow_succ']
      rfl

/-- The tail of a constant protocol is exactly the stable range core of its endomorphism. -/
theorem nonautonomousTail_const_eq_stableRangeCore
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (phi : F →ₐ[K] F) (i : ℕ) :
    nonautonomousTail (fun _ => phi) i = stableRangeCore phi := by
  unfold nonautonomousTail stableRangeCore
  congr 1
  funext n
  rw [forwardPrefix_const]

end


end GaloisForLFunctions.HTGeometry
