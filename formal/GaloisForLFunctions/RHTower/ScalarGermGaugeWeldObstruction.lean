import GaloisForLFunctions.RHTower.WeldOrderFiltration

/-!
# Scalar germ gauges cannot trivialize the filtered weld

`WeldOrderFiltration` proves that no order-zero affine cochain trivializes a nonzero weld, but the
interface still asks callers to provide `IsOrderZeroAffineCochain`.  For actual scalar germ-basis
gauges that hypothesis is automatic: a scalar gauge lands in the identity line `(0,r)`, the kernel
of the principal symbol.

This file packages that automatic discharge and removes the admissibility Prop.  No family of real
scalar gauges can have boundary equal to a nonzero weld cocycle.  A family of complex germ scalars
also cannot do so after the canonical additive-size readout `log ‖b_g‖`.  Prime specializations are
hypothesis-free.

Combined with `FESchwarzGermGluingTrivialization`, the conclusion is a strict local/global split:
both fixed and free FE/Schwarz orbit diagrams possess local scalar normalization, but scalar gauges
cannot extend to a global primitive of the prime--archimedean weld.  This still does not prove that a
free zero orbit would produce such a primitive; it identifies that implication as the remaining
mathematical content and rules out solving it by scalar gauge choice alone.
-/

open GaloisForLFunctions

noncomputable section
namespace GaloisForLFunctions.RHTower

/-- Include a real scalar germ-gauge family in the affine coefficient module. -/
def weldRealScalarGaugeCochain (θ : ℝ) (r : WeldGroup → ℝ) :
    WeldGroup → WeldAffineCoeff θ :=
  fun g => weldAffineScalar θ (r g)

/-- Scalar germ gauges have order zero automatically; no admissibility hypothesis is needed. -/
theorem weldRealScalarGaugeCochain_isOrderZero (θ : ℝ) (r : WeldGroup → ℝ) :
    IsOrderZeroAffineCochain θ (weldRealScalarGaugeCochain θ r) := by
  intro g
  rfl

/-- Scalar gauge families embed faithfully in affine cochains. -/
theorem weldRealScalarGaugeCochain_injective (θ : ℝ) :
    Function.Injective (weldRealScalarGaugeCochain θ) := by
  intro r s h
  funext g
  have hg := congrArg (fun b : WeldGroup → WeldAffineCoeff θ => (b g).2) h
  exact hg

/-- **The order-zero Prop is exactly scalar-gauge data.**  Every order-zero affine cochain is
uniquely represented pointwise by its scalar identity coefficient; there are no additional
order-zero directions hidden by the interface. -/
theorem isOrderZeroAffineCochain_iff_exists_realScalarGauge
    (θ : ℝ) (b : WeldGroup → WeldAffineCoeff θ) :
    IsOrderZeroAffineCochain θ b ↔
      ∃ r : WeldGroup → ℝ, b = weldRealScalarGaugeCochain θ r := by
  constructor
  · intro hb
    refine ⟨fun g => (b g).2, ?_⟩
    funext g
    apply Prod.ext
    · exact hb g
    · rfl
  · rintro ⟨r, rfl⟩
    exact weldRealScalarGaugeCochain_isOrderZero θ r

/-- **No real scalar germ-gauge primitive.**  At a nonzero rate, no arbitrary scalar gauge family
can trivialize the affine weld cocycle. -/
theorem no_weldRealScalarGaugePrimitive {θ : ℝ} (hθ : θ ≠ 0) :
    ¬ ∃ r : WeldGroup → ℝ,
      twoCoboundary (weldRealScalarGaugeCochain θ r) = weldAffineCocycle θ := by
  rintro ⟨r, hr⟩
  exact no_orderZeroAffinePrimitive hθ
    ⟨weldRealScalarGaugeCochain θ r, weldRealScalarGaugeCochain_isOrderZero θ r, hr⟩

/-- Every prime weld resists all real scalar germ-gauge families. -/
theorem prime_no_weldRealScalarGaugePrimitive {p : ℕ} (hp : p.Prime) :
    ¬ ∃ r : WeldGroup → ℝ,
      twoCoboundary (weldRealScalarGaugeCochain (Real.log p) r) =
        weldAffineCocycle (Real.log p) :=
  no_weldRealScalarGaugePrimitive
    (ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt)))

/-- The canonical real order-zero cochain read from a complex scalar gauge by logarithmic norm. -/
def weldComplexScalarGaugeLogNormCochain (θ : ℝ) (b : WeldGroup → ℂ) :
    WeldGroup → WeldAffineCoeff θ :=
  weldRealScalarGaugeCochain θ (fun g => Real.log ‖b g‖)

/-- Complex scalar gauges remain order zero after logarithmic-norm readout. -/
theorem weldComplexScalarGaugeLogNormCochain_isOrderZero
    (θ : ℝ) (b : WeldGroup → ℂ) :
    IsOrderZeroAffineCochain θ (weldComplexScalarGaugeLogNormCochain θ b) :=
  weldRealScalarGaugeCochain_isOrderZero θ _

/-- **No complex scalar germ-gauge primitive through logarithmic norm.** -/
theorem no_weldComplexScalarGaugeLogNormPrimitive {θ : ℝ} (hθ : θ ≠ 0) :
    ¬ ∃ b : WeldGroup → ℂ,
      twoCoboundary (weldComplexScalarGaugeLogNormCochain θ b) = weldAffineCocycle θ := by
  rintro ⟨b, hb⟩
  exact no_orderZeroAffinePrimitive hθ
    ⟨weldComplexScalarGaugeLogNormCochain θ b,
      weldComplexScalarGaugeLogNormCochain_isOrderZero θ b, hb⟩

/-- Every prime weld resists complex scalar germ gauges after the canonical size readout. -/
theorem prime_no_weldComplexScalarGaugeLogNormPrimitive {p : ℕ} (hp : p.Prime) :
    ¬ ∃ b : WeldGroup → ℂ,
      twoCoboundary (weldComplexScalarGaugeLogNormCochain (Real.log p) b) =
        weldAffineCocycle (Real.log p) :=
  no_weldComplexScalarGaugeLogNormPrimitive
    (ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt)))

end GaloisForLFunctions.RHTower
