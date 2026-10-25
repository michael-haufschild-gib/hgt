import GaloisForLFunctions.ArithmeticDefectRigidity.CompleteWienerPairingsFollowTheCommonCofactorLimit
import GaloisForLFunctions.ArithmeticOrientationTheory.TheCalculusOfTheObstructionHull

/-!
# Actual cofactor hulls respect conjugation

Real receiver rows conjugate the full Wiener source pairing. This identity
passes to the actual limiting module, preserving cyclic norms, annihilators
and conjugation symmetry of the module hull.
-/
section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology Complex
open scoped InnerProductSpace ComplexConjugate
open GaloisForLFunctions.ArithmeticOrientationTheory
open WienerAlgebraAt

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- Real receiver cells turn coefficient conjugation into source-row conjugation. -/
theorem complexWienerRow_conj (ε : SubcriticalDamping)
    (a : WienerAlgebraAt (1 / 2)) (n : ℕ) :
    complexWienerRow ε (conjW a) n = conj (complexWienerRow ε a n) := by
  simp only [complexWienerRow, conjW, toFn_mk, conjFn, map_sum, map_mul,
    Complex.conj_ofReal]
  rfl

/-- Full finite-horizon pairings preserve simultaneous coefficient conjugation. -/
theorem wienerSourcePairing_conj (ε : SubcriticalDamping) (T : ℕ)
    (a b : WienerAlgebraAt (1 / 2)) :
    wienerSourcePairing ε T (conjW a) (conjW b) =
      conj (wienerSourcePairing ε T a b) := by
  simp only [wienerSourcePairing, complexWienerRow_conj, map_sum, map_mul,
    map_add, map_one, map_natCast, map_div₀, Complex.conj_ofReal]

namespace ActualCofactorLimit

/-- Conjugating both Wiener inputs conjugates their actual limiting inner product. -/
theorem inner_wiener_conj {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (a b : WienerAlgebraAt (1 / 2)) :
    ⟪wienerRepresentation L (conjW b) (vector L 1),
      wienerRepresentation L (conjW a) (vector L 1)⟫_ℂ =
      conj ⟪wienerRepresentation L b (vector L 1),
        wienerRepresentation L a (vector L 1)⟫_ℂ := by
  have h := Complex.continuous_conj.continuousAt.tendsto.comp
    (wienerSourcePairing_tendsto L a b)
  apply tendsto_nhds_unique (wienerSourcePairing_tendsto L (conjW a) (conjW b))
  exact h.congr fun m => (wienerSourcePairing_conj ε (L.subsequence m) a b).symm

/-- The norm of each actual Wiener cyclic vector is unchanged by coefficient conjugation. -/
theorem norm_wiener_conj {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (a : WienerAlgebraAt (1 / 2)) :
    ‖wienerRepresentation L (conjW a) (vector L 1)‖ =
      ‖wienerRepresentation L a (vector L 1)‖ := by
  have h := congrArg Complex.re (inner_wiener_conj L a a)
  simp only [Complex.conj_re] at h
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
  exact h

/-- Every actual cofactor annihilator is invariant under coefficient conjugation. -/
theorem conjW_mem_annihilator_iff {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (a : WienerAlgebraAt (1 / 2)) : conjW a ∈ annihilator L ↔ a ∈ annihilator L := by
  rw [mem_annihilator_iff, mem_annihilator_iff]
  constructor
  · intro h
    apply norm_eq_zero.mp
    rw [← norm_wiener_conj L a, h, norm_zero]
  · intro h
    apply norm_eq_zero.mp
    rw [norm_wiener_conj L a, h, norm_zero]

/-- Every actual module hull contains the conjugate of each of its characters. -/
theorem conj_mem_moduleHull {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    {ω : BohrPoint} (hω : ω ∈ moduleHull L) : ω.conj ∈ moduleHull L := by
  intro a ha
  have hzero := hω (conjW a) ((conjW_mem_annihilator_iff L a).mpr ha)
  have h := bohrEval_conj (conjW a) ω
  have hconj : conjW (conjW a) = a := WienerAlgebraAt.ext fun n => by
    simp [conjW, toFn_mk, conjFn]
  rw [hconj, hzero, map_zero] at h
  exact h

end ActualCofactorLimit
end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.inner_wiener_conj
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.conjW_mem_annihilator_iff
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.conj_mem_moduleHull
end
end

