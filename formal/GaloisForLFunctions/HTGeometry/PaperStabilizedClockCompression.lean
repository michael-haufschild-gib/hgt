import GaloisForLFunctions.HTGeometry.PaperFourVariableClockObstruction
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.StabilizationEmbedding

/-!
# Compressing the stabilized clock destroys termination

Set the fifth variable to zero after applying the actual stabilized derivation.
The resulting operator is a derivation on the original polynomial algebra and
still sends `f` to one. The non-coordinate theorem forces this compressed clock
to have a nonterminating orbit. Consequently the stabilized clock necessarily
sends at least one original coordinate outside the original subalgebra.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

/-- Retraction to the original four variables, obtained by evaluating the added variable at zero. -/
def paperStabilizationRetraction : R 5 →ₐ[ℂ] R 4 :=
  (Polynomial.eval₂AlgHom (AlgHom.id ℂ (R 4)) 0 (fun _ => Commute.all _ _)).comp
    stabilizationEquiv.toAlgHom

@[simp] theorem paperStabilizationRetraction_stabilize (p : R 4) :
    paperStabilizationRetraction (stabilize p) = p := by
  simp [paperStabilizationRetraction, stabilizationEquiv_stabilize,
    Polynomial.eval₂AlgHom_apply]

/-- The actual stabilized clock followed by the explicit retraction is a four-variable derivation. -/
def paperCompressedClock : Derivation ℂ (R 4) (R 4) where
  toLinearMap := paperStabilizationRetraction.toLinearMap.comp
    (paperStabilizedClock.toLinearMap.comp stabilize.toLinearMap)
  map_one_eq_zero' := by
    change paperStabilizationRetraction (paperStabilizedClock (stabilize 1)) = 0
    simp
  leibniz' p q := by
    change paperStabilizationRetraction (paperStabilizedClock (stabilize (p * q))) =
      p • paperStabilizationRetraction (paperStabilizedClock (stabilize q)) +
        q • paperStabilizationRetraction (paperStabilizedClock (stabilize p))
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add,
      paperStabilizationRetraction_stabilize]

@[simp] theorem paperCompressedClock_apply (p : R 4) :
    paperCompressedClock p =
      paperStabilizationRetraction (paperStabilizedClock (stabilize p)) := rfl

/-- Compression retains exact unit speed on the distinguished polynomial. -/
theorem paperCompressedClock_slice : paperCompressedClock f = 1 := by
  simp [paperStabilizedClock_slice]

/-- Local nilpotence fails for the literal compressed operator. -/
theorem paperCompressedClock_not_locallyNilpotent :
    ¬ ∀ p : R 4, ∃ n : ℕ, (paperCompressedClock^[n]) p = 0 := by
  intro h
  exact paperFourVariable_no_terminating_clock ⟨paperCompressedClock, paperCompressedClock_slice, h⟩

/-- A polynomial has nonzero iterates at every order under the compressed clock. -/
theorem paperCompressedClock_nonterminating_element :
    ∃ p : R 4, ∀ n : ℕ, (paperCompressedClock^[n]) p ≠ 0 := by
  classical
  have h := paperCompressedClock_not_locallyNilpotent
  simp only [not_forall, not_exists] at h
  exact h

/-- On one and the same original polynomial, the stabilized orbit terminates and the compressed orbit does not. -/
theorem paperCompressedClock_termination_mismatch :
    ∃ (p : R 4) (n : ℕ), (paperCompressedClock^[n]) p ≠ 0 ∧
      (paperStabilizedClock^[n]) (stabilize p) = 0 := by
  obtain ⟨p, hp⟩ := paperCompressedClock_nonterminating_element
  obtain ⟨n, hn⟩ := paperStabilizedClock_locallyNilpotent (stabilize p)
  exact ⟨p, n, hp n, hn⟩

/-- The actual stabilized clock does not preserve the original polynomial subalgebra. -/
theorem paperStabilizedClock_not_preserves_original :
    ¬ ∀ p : R 4, paperStabilizedClock (stabilize p) ∈ stabilize.range := by
  intro h
  have hinter (p : R 4) :
      stabilize (paperCompressedClock p) = paperStabilizedClock (stabilize p) := by
    obtain ⟨q, hq⟩ := h p
    change stabilize q = paperStabilizedClock (stabilize p) at hq
    rw [paperCompressedClock_apply, ← hq, paperStabilizationRetraction_stabilize]
  have hi (n : ℕ) (p : R 4) :
      stabilize ((paperCompressedClock^[n]) p) =
        (paperStabilizedClock^[n]) (stabilize p) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [Function.iterate_succ_apply', hinter, ih]
  apply paperCompressedClock_not_locallyNilpotent
  intro p
  obtain ⟨n, hn⟩ := paperStabilizedClock_locallyNilpotent (stabilize p)
  refine ⟨n, stabilize_injective ?_⟩
  rw [map_zero, hi, hn]

/-- At least one of the four original coordinate generators leaves the original subalgebra. -/
theorem paperStabilizedClock_original_generator_escape :
    ∃ i : Fin 4, paperStabilizedClock (stabilize (MvPolynomial.X i)) ∉ stabilize.range := by
  classical
  by_contra! h
  apply paperStabilizedClock_not_preserves_original
  intro p
  induction p using MvPolynomial.induction_on with
  | C r =>
    rw [show MvPolynomial.C r = algebraMap ℂ (R 4) r from rfl,
      AlgHom.commutes, Derivation.map_algebraMap]
    exact stabilize.range.zero_mem
  | add p q hp hq =>
    rw [map_add, map_add]
    exact stabilize.range.add_mem hp hq
  | mul_X p i hp =>
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact stabilize.range.add_mem
      (stabilize.range.mul_mem ⟨p, rfl⟩ (h i))
      (stabilize.range.mul_mem ⟨MvPolynomial.X i, rfl⟩ hp)

end

end GaloisForLFunctions.HTGeometry
