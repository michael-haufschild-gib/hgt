import GaloisForLFunctions.HTGeometry.CayleyWienerHopfIndex
import GaloisForLFunctions.RHTower.PrimeHodgeHistorySurvivalFredholmColligation

/-!
# Three presentations of one transgression

The spectral-aperture card identifies one integer in three ways:

* the **cone winding**: the connecting map of the endpoint sequence `0 → J_T → C*(e_1) → ℂ → 0`
  sends the unit to `δ(1) = [exp(2πi e_1)]`, of stable winding index `1` in `K₁(J_T)`;
* the **theta first exit**: the forced survival shift of the prime–Hodge history has Fredholm index
  `-1`, so the first-exit charge `-ind(C)` is `1`;
* the **open-translation Fredholm index**: the Wiener–Hopf lift of the Cayley generator of the
  crossed product by translations has Fredholm index `1`, the winding of its symbol.
-/

set_option autoImplicit false

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **The cone winding, the theta first-exit charge and the open-translation Fredholm index are
the same integer `1`.** -/
theorem aperture_transgression_three_presentations
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {T : H →L[ℂ] H} (hT : T.IsPositive) (hcpt : IsCompactOperator T)
    (hinj : Function.Injective T) (hH : ¬ FiniteDimensional ℂ H) :
    stableK₁Winding hT hcpt hinj hH (stableConnectingMap hT hcpt hinj hH 1) = 1 ∧
      -_root_.RHTower.primeHodgeHistorySurvivalShiftIndex = 1 ∧
      fredholmIndex cayleyWienerHopf = 1 ∧
      _root_.RHTower.windingNumber (fun θ : ℝ => -Complex.exp (θ * Complex.I)) (-Real.pi)
        Real.pi = 1 := by
  refine ⟨stableK₁Winding_connectingMap hT hcpt hinj hH 1, ?_, fredholmIndex_cayleyWienerHopf,
    windingNumber_cayleyLoop⟩
  rw [_root_.RHTower.primeHodgeHistorySurvivalShiftIndex_eq_neg_one]
  norm_num

end GaloisForLFunctions.HTGeometry
