import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeHorizon
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetUnipotentLogEquiv

/-!
# Finite logarithms and exponentials commute with actual horizon restriction

The truncation degrees change with the horizon. Universal formal lifts prove
compatibility without equating those different finite polynomials.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Actual nilpotent exponentiation commutes with the geometric algebra restriction at every horizon. -/
theorem gomesTruncatedJetHorizonRestriction_exponential (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace (n + r) z) :
    gomesTruncatedJetHorizonRestriction n r z (gomesTruncatedJetNilpotentExponential (n + r) z E) =
      gomesTruncatedJetNilpotentExponential n z (gomesTruncatedJetNilpotentHorizon n r z E) := by
  have lifted (F : PowerSeries ℂ) (M : gomesTruncatedJetJointAlgebra (n + r) z)
      (hM : gomesFiniteFockFormalHom (n + r + 1) F = M.val) :
      gomesFiniteFockFormalHom (n + 1) F = (gomesTruncatedJetHorizonRestriction n r z M).val := by
    have h : Subalgebra.inclusion (gomesTruncatedJetJointAlgebra_le_clock (n + r) z) M =
        gomesFiniteFockFormalSymbolHom (n + r + 1) F := by
      apply Subtype.ext
      exact hM.symm
    change gomesFiniteFockFormalHom (n + 1) F =
      (gomesFiniteFockHorizonRestriction n r
        (Subalgebra.inclusion (gomesTruncatedJetJointAlgebra_le_clock (n + r) z) M)).val
    rw [h, gomesFiniteFockHorizonRestriction_formal]
    rfl
  obtain ⟨G, hG⟩ := gomesTruncatedJetNilpotentSpace_formal_lift (n + r) z E
  have hE := lifted G.val E.val hG
  have hExp : gomesFiniteFockFormalHom (n + r + 1) (gomesBasedFormalExponential G) =
      (gomesTruncatedJetNilpotentExponential (n + r) z E).val := by
    rw [gomesFiniteFockBasedFormal_exponential, hG]
    exact (gomesTruncatedJetNilpotentExponential_val (n + r) z E).symm
  apply Subtype.ext
  rw [← lifted (gomesBasedFormalExponential G) (gomesTruncatedJetNilpotentExponential (n + r) z E) hExp,
    gomesTruncatedJetNilpotentExponential_val, gomesFiniteFockBasedFormal_exponential, hE]
  rfl

/-- Exponentiating any actual nilpotent symmetry and then restricting equals exponentiating its restricted coordinate. -/
theorem gomesTruncatedJetUnipotentHorizon_exponential (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetNilpotentSpace (n + r) z) :
    gomesTruncatedJetUnipotentHorizon n r z (gomesTruncatedJetUnipotentExponential (n + r) z E) =
      gomesTruncatedJetUnipotentExponential n z (gomesTruncatedJetNilpotentHorizon n r z E) := by
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  have h : ((gomesTruncatedJetInternalUnitsEquiv (n + r) z).symm
      (gomesTruncatedJetUnipotentExponential (n + r) z E).val).val =
      gomesTruncatedJetNilpotentExponential (n + r) z E := by
    apply Subtype.ext
    exact gomesTruncatedJetNilpotentExponentialGauge_val (n + r) z E
  change (gomesTruncatedJetHorizonRestriction n r z
    (((gomesTruncatedJetInternalUnitsEquiv (n + r) z).symm
      (gomesTruncatedJetUnipotentExponential (n + r) z E).val).val)).val = _
  rw [h, gomesTruncatedJetHorizonRestriction_exponential]
  exact (gomesTruncatedJetNilpotentExponentialGauge_val n z
    (gomesTruncatedJetNilpotentHorizon n r z E)).symm

/-- The actual terminating matrix logarithm is compatible with every geometric horizon restriction. -/
theorem gomesTruncatedJetUnipotentHorizon_logarithm (n r : ℕ) (z : ℂ)
    (u : gomesTruncatedJetUnipotentGroup (n + r) z) :
    gomesTruncatedJetNilpotentHorizon n r z (gomesTruncatedJetUnipotentLogarithm (n + r) z u) =
      gomesTruncatedJetUnipotentLogarithm n z (gomesTruncatedJetUnipotentHorizon n r z u) := by
  have h := congrArg (gomesTruncatedJetUnipotentLogarithm n z)
    (gomesTruncatedJetUnipotentHorizon_exponential n r z (gomesTruncatedJetUnipotentLogarithm (n + r) z u))
  rw [gomesTruncatedJetUnipotentExponential_logarithm,
    gomesTruncatedJetUnipotentLogarithm_exponential] at h
  exact h.symm

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
