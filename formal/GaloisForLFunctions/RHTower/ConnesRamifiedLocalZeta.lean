import GaloisForLFunctions.RHTower.ConnesUnramifiedLocalZeta

/-!
# The local Tate integral at a ramified place

Appendix I Lemma 1 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  *"To prove the second equality one only needs to consider the infinite tensor product for finite
  places `v ∉ P`."*

`P` is the ramification locus of `Χ_0`.  The reason the ramified places drop out is local: on the
valuation shell `v(x) = m` a quasi-character splits as `Χ(π^m)·Χ(u)`, so the shell integral
carries the factor `∫_{R_v^*} Χ_v(u) du`, which vanishes as soon as `Χ_v` is nontrivial on the
units.  Hence every shell contributes zero and the whole local integral vanishes — which is why
`L(Χ_0, s)` is a product over the unramified places only.
-/

open MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- **The valuation/angle split of a quasi-character.**  Every monoid homomorphism of `ℚ_p^*`
factors on each shell into its value at the uniformizer power and its value on the unit. -/
theorem connes_padic_character_split (χ : ℚ_[p]ˣ →* ℂ) (m : ℤ) (u : ℤ_[p]ˣ) :
    χ (fieldOnePadicValuationUnitContinuousMulEquiv p (Multiplicative.ofAdd m, u))
      = χ (fieldOnePadicValuationUnitContinuousMulEquiv p
            (Multiplicative.ofAdd m, (1 : ℤ_[p]ˣ)))
        * χ (fieldOnePadicValuationUnitContinuousMulEquiv p
            (Multiplicative.ofAdd (0 : ℤ), u)) := by
  have hsplit : ((Multiplicative.ofAdd m, u) : Multiplicative ℤ × ℤ_[p]ˣ)
      = (Multiplicative.ofAdd m, (1 : ℤ_[p]ˣ)) *
        (Multiplicative.ofAdd (0 : ℤ), u) := by
    refine Prod.ext ?_ ?_
    · show Multiplicative.ofAdd m
        = Multiplicative.ofAdd m * Multiplicative.ofAdd (0 : ℤ)
      rw [← ofAdd_add, add_zero]
    · show u = 1 * u
      rw [one_mul]
  rw [hsplit, map_mul, map_mul]

/-- **Appendix I Lemma 1, ramified place.**  If the angular profile of a shell-split integrand has
zero mean on the units, the whole local multiplicative integral vanishes. -/
theorem connes_padic_tate_ramified_vanishes (f : ℚ_[p]ˣ → ℂ) (g : ℤ → ℂ) (a : ℤ_[p]ˣ → ℂ)
    (hcoord : ∀ (m : ℤ) (u : ℤ_[p]ˣ),
      f (fieldOnePadicValuationUnitContinuousMulEquiv p (Multiplicative.ofAdd m, u))
        = g m * a u)
    (hmean : (∫ u : ℤ_[p]ˣ, a u ∂fieldOnePadicUnitNormalizedHaar p) = 0)
    (hf : Integrable f (fieldOnePadicMultiplicativeHaar p)) :
    (∫ x, f x ∂fieldOnePadicMultiplicativeHaar p) = 0 := by
  rw [fieldOnePadicMultiplicativeHaar_integral_eq_tsum p f hf]
  have hterm : ∀ k : Multiplicative ℤ,
      (∫ u : ℤ_[p]ˣ, f (fieldOnePadicValuationUnitContinuousMulEquiv p (k, u))
        ∂fieldOnePadicUnitNormalizedHaar p) = 0 := by
    intro k
    have hpoint : ∀ u : ℤ_[p]ˣ,
        f (fieldOnePadicValuationUnitContinuousMulEquiv p (k, u)) = g k.toAdd * a u := by
      intro u
      have hkrep : k = Multiplicative.ofAdd k.toAdd :=
        (Multiplicative.ofAdd.apply_symm_apply k).symm
      rw [hkrep]
      exact hcoord k.toAdd u
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_const_mul, hmean,
      mul_zero]
  rw [tsum_congr hterm, tsum_zero]

/-- **Appendix I Lemma 1, ramified place, character form.**  For a quasi-character whose
restriction to the units has zero mean, every radially weighted local Tate integral vanishes. -/
theorem connes_padic_tate_ramified_character (χ : ℚ_[p]ˣ →* ℂ) (g : ℤ → ℂ)
    (hmean : (∫ u : ℤ_[p]ˣ, χ (fieldOnePadicValuationUnitContinuousMulEquiv p
        (Multiplicative.ofAdd (0 : ℤ), u)) ∂fieldOnePadicUnitNormalizedHaar p) = 0)
    (f : ℚ_[p]ˣ → ℂ)
    (hcoord : ∀ (m : ℤ) (u : ℤ_[p]ˣ),
      f (fieldOnePadicValuationUnitContinuousMulEquiv p (Multiplicative.ofAdd m, u))
        = g m * χ (fieldOnePadicValuationUnitContinuousMulEquiv p (Multiplicative.ofAdd m, u)))
    (hf : Integrable f (fieldOnePadicMultiplicativeHaar p)) :
    (∫ x, f x ∂fieldOnePadicMultiplicativeHaar p) = 0 := by
  refine connes_padic_tate_ramified_vanishes p f
    (fun m => g m * χ (fieldOnePadicValuationUnitContinuousMulEquiv p
      (Multiplicative.ofAdd m, (1 : ℤ_[p]ˣ))))
    (fun u => χ (fieldOnePadicValuationUnitContinuousMulEquiv p
      (Multiplicative.ofAdd (0 : ℤ), u))) ?_ hmean hf
  intro m u
  rw [hcoord m u, connes_padic_character_split p χ m u]
  ring

end

end GaloisForLFunctions.RHTower
