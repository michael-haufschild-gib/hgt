import GaloisForLFunctions.RHTower.ProlateSectorSpectralGap
import GaloisForLFunctions.RHTower.ProlateSectorDepthSpectrum
import GaloisForLFunctions.RHTower.ProlateNegativeTrueFamilyDistanceRate

/-!
# The constrained-prolate cards, stated for the operator, with no hypotheses

The two Fourier-sector constrained leakage ground values `mu_±(lambda)` are named here as honest
functions of the aperture, and their defining operator property — being the simple constrained
leakage ground value of `B_lambda = I − T_lambda²` on the sector, i.e. a floor for the leakage form
of every vector of the sector with vanishing integral, attained on a single complex line — is a
theorem about them.

Every law of the three constrained-prolate cards is then restated as an unconditional theorem about
these named quantities and about the constrained eigenvalues of the operator itself:

* the two-mode ground-state card's `(4)`, `(5)`, `(6)`, `(7)`;
* the parity card's `(5)`, `(6)`, `(8)`, `(9)`, `(10)`;
* the fixed-mode spectral ladder card's `(7)`, `(8)`, `(9)`, `(10)`--`(11)`.
-/

noncomputable section

open Filter Set Topology
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-! ## The named ground values -/

/-- `mu_+(lambda)`: the constrained leakage ground value of the Fourier-even prolate sector. -/
def positiveSectorGroundValue (a : ℝ) : ℝ :=
  infiniteSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
    (fun j => ‖evenProlateConstraintCoord a (2 * j)‖)

/-- `mu_-(lambda)`: the constrained leakage ground value of the Fourier-odd prolate sector. -/
def negativeSectorGroundValue (a : ℝ) : ℝ :=
  infiniteSecularRoot (fun j => evenProlateSignedLeakage a (2 * j + 1))
    (fun j => ‖evenProlateConstraintCoord a (2 * j + 1)‖)

/-- `mu_k(lambda)`: the depth-`k` constrained eigenvalue of the Fourier-even prolate sector. -/
def positiveSectorDepthValue (a : ℝ) (k : ℕ) : ℝ :=
  depthSecularRoot (fun j => evenProlateSignedLeakage a (2 * j))
    (fun j => ‖evenProlateConstraintCoord a (2 * j)‖) k

/-- **`mu_+` is the simple constrained leakage ground value of the Fourier-even sector.** -/
theorem eventually_isSectorConstrainedGround_positiveSectorGroundValue :
    ∀ᶠ a : ℝ in atTop,
      IsSectorConstrainedGround a positiveSectorIndex (positiveSectorGroundValue a) :=
  eventually_isSectorConstrainedGround_positive

/-- **`mu_-` is the simple constrained leakage ground value of the Fourier-odd sector.** -/
theorem eventually_isSectorConstrainedGround_negativeSectorGroundValue :
    ∀ᶠ a : ℝ in atTop,
      IsSectorConstrainedGround a negativeSectorIndex (negativeSectorGroundValue a) :=
  eventually_isSectorConstrainedGround_negative

/-! ## The two-mode ground-state card -/

/-- **Equation `(5)`.**  `mu_+(lambda)/d_4(lambda) → 8/11`. -/
theorem positiveSectorGroundValue_ratio_tendsto :
    Tendsto (fun a : ℝ => positiveSectorGroundValue a / evenProlateSignedLeakage a 2)
      atTop (𝓝 (8 / 11)) :=
  constrainedProlatePositive_operator_ground_ratio_tendsto
    eventually_isSectorConstrainedGround_positiveSectorGroundValue

/-- **Equation `(6)`.**  The complementary gap ratio tends to `3/11`. -/
theorem positiveSectorGroundValue_gap_ratio_tendsto :
    Tendsto (fun a : ℝ =>
        (evenProlateSignedLeakage a 2 - positiveSectorGroundValue a)
          / evenProlateSignedLeakage a 2)
      atTop (𝓝 (3 / 11)) :=
  constrainedProlatePositive_operator_gap_ratio_tendsto
    eventually_isSectorConstrainedGround_positiveSectorGroundValue

/-- **Equation `(7)`.**  For every constant below `3/11`, every other constrained eigenvalue of the
compressed leakage operator on the Fourier-even sector eventually exceeds `mu_+` by that multiple of
`d_4`. -/
theorem positiveSector_operator_spectralGap_eventually {cst : ℝ} (hc : cst < 3 / 11) :
    ∀ᶠ a : ℝ in atTop, ∀ (μ : ℝ) (g : evenSubspace),
      IsSectorConstrainedEigen a positiveSectorIndex μ g → μ ≠ positiveSectorGroundValue a →
      cst * evenProlateSignedLeakage a 2 ≤ μ - positiveSectorGroundValue a :=
  constrainedProlatePositive_operator_spectralGap_eventually hc
    eventually_isSectorConstrainedGround_positiveSectorGroundValue

/-! ## The parity card -/

/-- **Equation `(6)` of the parity card.**  `mu_-(lambda)/d_6(lambda) → 8/13`. -/
theorem negativeSectorGroundValue_ratio_tendsto :
    Tendsto (fun a : ℝ => negativeSectorGroundValue a / evenProlateSignedLeakage a 3)
      atTop (𝓝 (8 / 13)) :=
  constrainedProlateNegative_operator_ground_ratio_tendsto
    eventually_isSectorConstrainedGround_negativeSectorGroundValue

/-- **Equation `(10)` of the parity card.**  The complementary gap ratio tends to `5/13`. -/
theorem negativeSectorGroundValue_gap_ratio_tendsto :
    Tendsto (fun a : ℝ =>
        (evenProlateSignedLeakage a 3 - negativeSectorGroundValue a)
          / evenProlateSignedLeakage a 3)
      atTop (𝓝 (5 / 13)) :=
  constrainedProlateNegative_operator_gap_ratio_tendsto
    eventually_isSectorConstrainedGround_negativeSectorGroundValue

/-- **The quantified negative-sector gap.**  For every constant below `5/13`. -/
theorem negativeSector_operator_spectralGap_eventually {cst : ℝ} (hc : cst < 5 / 13) :
    ∀ᶠ a : ℝ in atTop, ∀ (μ : ℝ) (g : evenSubspace),
      IsSectorConstrainedEigen a negativeSectorIndex μ g → μ ≠ negativeSectorGroundValue a →
      cst * evenProlateSignedLeakage a 3 ≤ μ - negativeSectorGroundValue a :=
  constrainedProlateNegative_operator_spectralGap_eventually hc
    eventually_isSectorConstrainedGround_negativeSectorGroundValue

/-- **Equation `(8)` of the parity card.**  `mu_+/mu_- → 0`. -/
theorem parityGroundValue_ratio_tendsto_zero :
    Tendsto (fun a : ℝ => positiveSectorGroundValue a / negativeSectorGroundValue a)
      atTop (𝓝 0) :=
  constrainedProlateParity_operator_ratio_tendsto_zero
    eventually_isSectorConstrainedGround_positiveSectorGroundValue
    eventually_isSectorConstrainedGround_negativeSectorGroundValue

/-- **The leakage-normalized parity collapse.**  The two normalized floors separate by `13/11`. -/
theorem parityGroundValue_normalized_ratio_tendsto :
    Tendsto (fun a : ℝ =>
        positiveSectorGroundValue a / evenProlateSignedLeakage a 2
          / (negativeSectorGroundValue a / evenProlateSignedLeakage a 3))
      atTop (𝓝 (13 / 11)) :=
  constrainedProlateParity_operator_normalized_ratio_tendsto
    eventually_isSectorConstrainedGround_positiveSectorGroundValue
    eventually_isSectorConstrainedGround_negativeSectorGroundValue

/-- **Equation `(9)` of the parity card.**  Eventually `mu_+ < mu_-`, and the gap between them is
asymptotically the whole of `mu_-`. -/
theorem parityGroundValue_separation :
    (∀ᶠ a : ℝ in atTop, positiveSectorGroundValue a < negativeSectorGroundValue a) ∧
      Tendsto (fun a : ℝ =>
          (negativeSectorGroundValue a - positiveSectorGroundValue a)
            / negativeSectorGroundValue a)
        atTop (𝓝 1) :=
  constrainedProlateParity_operator_separation
    eventually_isSectorConstrainedGround_positiveSectorGroundValue
    eventually_isSectorConstrainedGround_negativeSectorGroundValue

/-! ## The fixed-mode spectral ladder card -/

/-- **Equation `(8)` of the ladder card.**  Eventually the compressed leakage operator on the
Fourier-even sector has exactly one constrained eigenvalue in the `k`-th spectral gap, namely
`mu_k(lambda)`, and `mu_k(lambda)/d_{k+1}(lambda) → theta_k`. -/
theorem positiveSectorDepthValue_laws (k : ℕ) :
    (∀ᶠ a : ℝ in atTop,
        (∃ f : evenSubspace, IsSectorConstrainedEigen a positiveSectorIndex
            (positiveSectorDepthValue a k) f) ∧
          (∀ (μ : ℝ) (g : evenSubspace),
            μ ∈ Ioo (evenProlateSignedLeakage a (2 * k))
              (evenProlateSignedLeakage a (2 * (k + 1))) →
            IsSectorConstrainedEigen a positiveSectorIndex μ g →
            μ = positiveSectorDepthValue a k)) ∧
      Tendsto (fun a : ℝ =>
          positiveSectorDepthValue a k / evenProlateSignedLeakage a (2 * (k + 1)))
        atTop (𝓝 (constrainedProlateHermiteTheta k)) :=
  constrainedProlateEven_operator_depth_ratio_tendsto k

/-- **Equation `(9)` of the ladder card.**  The adjacent constrained eigenvalues, corrected by
their dominant leakages, separate by `theta_{k+1}/theta_k`. -/
theorem positiveSectorDepthValue_adjacent_ratio_tendsto (k : ℕ) :
    Tendsto (fun a : ℝ =>
        positiveSectorDepthValue a (k + 1) / positiveSectorDepthValue a k
          * (evenProlateSignedLeakage a (2 * (k + 1))
              / evenProlateSignedLeakage a (2 * (k + 2))))
      atTop (𝓝 (constrainedProlateHermiteTheta (k + 1) / constrainedProlateHermiteTheta k)) :=
  constrainedProlateEven_operator_adjacent_ratio_tendsto k


/-- **Equations `(10)`--`(11)` of the ladder card, in the operator's own terms.**  Eventually the
compressed leakage operator on the Fourier-even sector has a constrained eigenvector at
`mu_k(lambda)` whose coefficients against the sector's orthonormal prolate family are exactly the
depth-`k` secular coordinates; their oriented normalization converges in `ell^2` to the canonical
Hermite contrast unit, and those limits form an orthonormal family. -/
theorem positiveSectorDepthValue_eigenvector_laws (k : ℕ) :
    (∀ᶠ a : ℝ in atTop, ∃ f : evenSubspace,
        IsSectorConstrainedEigen a positiveSectorIndex (positiveSectorDepthValue a k) f ∧
        ∀ j : ℕ, inner ℂ (sectorMode a positiveSectorIndex j) f
          = ((sectorDepthCoeff a positiveSectorIndex k j : ℝ) : ℂ)) ∧
      Tendsto (fun a : ℝ =>
        let V := (secularVector (fun j => evenProlateSignedLeakage a (2 * j))
            (fun j => ‖evenProlateConstraintCoord a (2 * j)‖)
            (positiveSectorDepthValue a k) 0)⁻¹ •
          secularLp (fun j => evenProlateSignedLeakage a (2 * j))
            (fun j => ‖evenProlateConstraintCoord a (2 * j)‖)
            (positiveSectorDepthValue a k)
        (‖V‖)⁻¹ • V) atTop (𝓝 (-hermiteContrastUnit k)) ∧
      Orthonormal ℝ hermiteContrastUnit := by
  refine ⟨?_, (constrainedProlateEven_operator_depth_eigenvector_coeff k).2.1,
    (constrainedProlateEven_operator_depth_eigenvector_coeff k).2.2⟩
  filter_upwards [eventually_exists_sectorDepthEigen_positive k,
    (constrainedProlateEven_operator_depth_eigenvector_coeff k).1] with a hex hco
  obtain ⟨f, hf, heig⟩ := hex
  exact ⟨f, heig, hco f hf⟩

end RHTower

end
