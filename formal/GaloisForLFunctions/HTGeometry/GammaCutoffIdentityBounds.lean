import GaloisForLFunctions.HTGeometry.GammaCutoffDifferentiatedIdentity

/-!
# `(14)` with its hypotheses discharged

The identity of `GammaCutoffDifferentiatedIdentity` needs additivity of the transport and its
commutation with differentiation on the cut-off profile.  Both follow from the same package: a
bounded profile with two bounded derivatives, and a cutoff with two bounded derivatives.  Products
of such data are again of that shape, so nothing beyond the product rule is needed.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The transport is additive on profiles with bounded derivatives. -/
theorem gammaTransport_add {f g f' g' : ℝ → ℝ} {Mf Mg : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hMf : ∀ x, |f' x| ≤ Mf)
    (hg : ∀ x, HasDerivAt g (g' x) x) (hMg : ∀ x, |g' x| ≤ Mg) (L : ℝ) :
    gammaTransport (fun y => f y + g y) L = gammaTransport f L + gammaTransport g L := by
  have hfint := integrableOn_secondDifference_mul_kernel hf hMf L
  have hgint := integrableOn_secondDifference_mul_kernel hg hMg L
  rw [gammaTransport, gammaTransport, gammaTransport, ← integral_add hfint hgint]
  refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
  show secondDifference (fun y => f y + g y) L s * gammaTransportKernel s
    = secondDifference f L s * gammaTransportKernel s
      + secondDifference g L s * gammaTransportKernel s
  rw [secondDifference, secondDifference, secondDifference]
  ring

/-- **`(14)` for a bounded `C²` profile and a bounded `C²` cutoff.** -/
theorem gammaCutoff_differentiated_identity_of_bounds
    {F F' F'' χ χ' χ'' G' : ℝ → ℝ} {B₀ B₁ B₂ C₀ C₁ C₂ : ℝ}
    (hF : ∀ x, HasDerivAt F (F' x) x) (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hB₀ : ∀ x, |F x| ≤ B₀) (hB₁ : ∀ x, |F' x| ≤ B₁) (hB₂ : ∀ x, |F'' x| ≤ B₂)
    (hχ : ∀ x, HasDerivAt χ (χ' x) x) (hχ' : ∀ x, HasDerivAt χ' (χ'' x) x)
    (hC₀ : ∀ x, |χ x| ≤ C₀) (hC₁ : ∀ x, |χ' x| ≤ C₁) (hC₂ : ∀ x, |χ'' x| ≤ C₂)
    (heq : ∀ L : ℝ, 2 * L * F' L + F L + gammaTransport F' L = G' L)
    (L : ℝ) :
    2 * L * (χ' L * F L + χ L * F' L)
        + gammaTransport (fun y => χ' y * F y + χ y * F' y) L + χ L * F L
      = χ L * G' L
        + deriv (gammaCommutator χ F) L
        + (2 * L * (χ' L * F L) + gammaTransport (fun y => χ' y * F y) L)
        - gammaCommutator χ' F L := by
  -- the product profiles and their two derivatives
  have hW : ∀ x, HasDerivAt (fun y => χ y * F y) (χ' x * F x + χ x * F' x) x :=
    fun x => (hχ x).mul (hF x)
  have hW' : ∀ x, HasDerivAt (fun y => χ' y * F y + χ y * F' y)
      ((χ'' x * F x + χ' x * F' x) + (χ' x * F' x + χ x * F'' x)) x :=
    fun x => ((hχ' x).mul (hF x)).add ((hχ x).mul (hF' x))
  have hA : ∀ x, HasDerivAt (fun y => χ' y * F y) (χ'' x * F x + χ' x * F' x) x :=
    fun x => (hχ' x).mul (hF x)
  have hBp : ∀ x, HasDerivAt (fun y => χ y * F' y) (χ' x * F' x + χ x * F'' x) x :=
    fun x => (hχ x).mul (hF' x)
  have hMW : ∀ x, |χ' x * F x + χ x * F' x| ≤ C₁ * B₀ + C₀ * B₁ := by
    intro x
    have h1 : |χ' x * F x| ≤ C₁ * B₀ := by
      rw [abs_mul]
      exact mul_le_mul (hC₁ x) (hB₀ x) (abs_nonneg _) (le_trans (abs_nonneg _) (hC₁ x))
    have h2 : |χ x * F' x| ≤ C₀ * B₁ := by
      rw [abs_mul]
      exact mul_le_mul (hC₀ x) (hB₁ x) (abs_nonneg _) (le_trans (abs_nonneg _) (hC₀ x))
    exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
  have hKW : ∀ x, |(χ'' x * F x + χ' x * F' x) + (χ' x * F' x + χ x * F'' x)|
      ≤ (C₂ * B₀ + C₁ * B₁) + (C₁ * B₁ + C₀ * B₂) := by
    intro x
    have h1 : |χ'' x * F x| ≤ C₂ * B₀ := by
      rw [abs_mul]
      exact mul_le_mul (hC₂ x) (hB₀ x) (abs_nonneg _) (le_trans (abs_nonneg _) (hC₂ x))
    have h2 : |χ' x * F' x| ≤ C₁ * B₁ := by
      rw [abs_mul]
      exact mul_le_mul (hC₁ x) (hB₁ x) (abs_nonneg _) (le_trans (abs_nonneg _) (hC₁ x))
    have h3 : |χ x * F'' x| ≤ C₀ * B₂ := by
      rw [abs_mul]
      exact mul_le_mul (hC₀ x) (hB₂ x) (abs_nonneg _) (le_trans (abs_nonneg _) (hC₀ x))
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
    · exact le_trans (abs_add_le _ _) (add_le_add h2 h3)
  have hMA : ∀ x, |χ'' x * F x + χ' x * F' x| ≤ C₂ * B₀ + C₁ * B₁ := by
    intro x
    have h1 : |χ'' x * F x| ≤ C₂ * B₀ := by
      rw [abs_mul]
      exact mul_le_mul (hC₂ x) (hB₀ x) (abs_nonneg _) (le_trans (abs_nonneg _) (hC₂ x))
    have h2 : |χ' x * F' x| ≤ C₁ * B₁ := by
      rw [abs_mul]
      exact mul_le_mul (hC₁ x) (hB₁ x) (abs_nonneg _) (le_trans (abs_nonneg _) (hC₁ x))
    exact le_trans (abs_add_le _ _) (add_le_add h1 h2)
  have hMB : ∀ x, |χ' x * F' x + χ x * F'' x| ≤ C₁ * B₁ + C₀ * B₂ := by
    intro x
    have h2 : |χ' x * F' x| ≤ C₁ * B₁ := by
      rw [abs_mul]
      exact mul_le_mul (hC₁ x) (hB₁ x) (abs_nonneg _) (le_trans (abs_nonneg _) (hC₁ x))
    have h3 : |χ x * F'' x| ≤ C₀ * B₂ := by
      rw [abs_mul]
      exact mul_le_mul (hC₀ x) (hB₂ x) (abs_nonneg _) (le_trans (abs_nonneg _) (hC₀ x))
    exact le_trans (abs_add_le _ _) (add_le_add h2 h3)
  refine gammaCutoff_differentiated_identity
    (fun M => hasDerivAt_gammaTransport hF hF' hB₁ hB₂ M)
    (fun M => hasDerivAt_gammaTransport hW hW' hMW hKW M)
    (fun M => gammaTransport_add hA hMA hBp hMB M) hχ heq L

end GaloisForLFunctions.HTGeometry
