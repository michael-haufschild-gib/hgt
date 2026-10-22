import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedQuadraticClosure

/-!
# Source-leg grading of the literal cyclic Peierls contact

Each causal Peierls source leg is quadratic in its primary amplitude.  The
actual two-leg contact must consequently be fed the two squared source-leg
amplitudes, not the primary amplitudes.  This leaf fixes that normalization
on the genuine metric contact field.

Proof-chain role:
`two quadratic causal source legs -> quartic actual contact carrier ->
lift-defect/contact boundary equality -> HB B2`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsSourceLegContact

open D4BMMixedQuadraticClosure

noncomputable section
set_option autoImplicit false

/-- Actual contact carrier with the two primary amplitudes regraded to the
quadratic amplitudes of the two literal causal source legs. -/
def sourceLegContactFieldBilinear (q : XiZeroCopy) (branch : Bool) (a d : ℂ)
    (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  contactFieldBilinear q branch (a ^ (2 : ℕ)) (d ^ (2 : ℕ)) x

/-- The regraded actual contact has exactly the biquadratic source-leg
homogeneity carried by the literal two-event Peierls density. -/
theorem sourceLegContactFieldBilinear_eq_product (q : XiZeroCopy) (branch : Bool)
    (a d : ℂ) (x : Fin 4 → ℝ) :
    sourceLegContactFieldBilinear q branch a d x =
      (a ^ (2 : ℕ) * d ^ (2 : ℕ)) • contactField q branch 1 x := by
  unfold sourceLegContactFieldBilinear
  rw [contactFieldBilinear_eq_product]

/-- Cyclic exchange remains literal after source-leg regrading. -/
theorem sourceLegContactFieldBilinear_symm (q : XiZeroCopy) (branch : Bool)
    (a d : ℂ) (x : Fin 4 → ℝ) :
    sourceLegContactFieldBilinear q branch a d x =
      sourceLegContactFieldBilinear q branch d a x := by
  unfold sourceLegContactFieldBilinear
  rw [contactFieldBilinear_symm]

/-- On a repeated source leg, the regraded carrier is exactly the existing
actual contact at the squared source amplitude. -/
theorem sourceLegContactFieldBilinear_diag (q : XiZeroCopy) (branch : Bool)
    (a : ℂ) (x : Fin 4 → ℝ) :
    sourceLegContactFieldBilinear q branch a a x =
      contactField q branch (a ^ (2 : ℕ)) x := by
  unfold sourceLegContactFieldBilinear
  exact contactFieldBilinear_diag q branch (a ^ (2 : ℕ)) x

end

end RHTower.D4BMLiteralCyclicPeierlsSourceLegContact
