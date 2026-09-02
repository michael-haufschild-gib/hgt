import GaloisForLFunctions.HTGeometry.PoincareSeriesPeterssonIntegrand

/-!
# The Petersson product against a Poincaré series unfolds to the strip

For a cusp form `f` of weight `k ≥ 3` and `m ≥ 1`, with `ψ = petersson k f e_m`,

  `⟨f, P_m⟩ = ∫_𝒟 petersson k f P_m = ∫_𝒟 Σ_{(c,d)} ψ(M_{c,d} z) = Σ_{(c,d)} ∫_𝒟 ψ(M_{c,d} z)
            = 2 ∫_{0 ≤ Re z < 1} ψ`.

The exchange of sum and integral is justified by the absolute unfolding of `‖ψ‖`, itself an
instance of the unfolding identity.
-/

open UpperHalfPlane hiding I
open MeasureTheory Set ModularForm EisensteinSeries Complex ModularGroup
open scoped MatrixGroups ModularForm ComplexConjugate Real Pointwise

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Petersson product `∫_𝒟 conj(f) g y^k dμ` over the modular fundamental domain. -/
def peterssonInner (k : ℤ) (f g : ℍ → ℂ) : ℂ := ∫ z in fd, petersson k f g z

/-- **Unfolding of the Petersson product against `P_m`.** -/
theorem peterssonInner_poincareSeries_eq_two_mul_setIntegral_modularStrip {k : ℤ} (hk : 3 ≤ k)
    {m : ℕ} (hm : 1 ≤ m) (f : CuspForm 𝒮ℒ k) :
    peterssonInner k f (poincareSeries k m)
      = 2 * ∫ z in modularStrip, petersson k f (expSeed m) z := by
  have hper : ∀ (n : ℤ) (z : ℍ),
      petersson k f (expSeed m) (ModularGroup.T ^ n • z) = petersson k f (expSeed m) z :=
    petersson_expSeed_T_zpow_smul m f
  have hint : IntegrableOn (petersson k f (expSeed m)) modularStrip volume :=
    integrableOn_modularStrip_petersson_expSeed hk hm f
  rw [← tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip _ hper hint, peterssonInner]
  simp_rw [petersson_poincareSeries_eq_tsum m f]
  symm
  refine integral_tsum_of_summable_integral_norm (fun v => ?_) ?_
  · exact (integrableOn_smul_set_iff (gammaSetMatrix v) _ fd).mp
      (integrableOn_smul_fd_of_periodic hper hint _)
  · have hnorm := summable_fdUnfoldTerm
      (φ := fun z => ((‖petersson k f (expSeed m) z‖ : ℝ) : ℂ))
      (fun n z => by rw [hper]) hint.norm.ofReal
    have : fdUnfoldTerm (fun z => ((‖petersson k f (expSeed m) z‖ : ℝ) : ℂ))
        = fun v => ((∫ z in fd, ‖petersson k f (expSeed m) (gammaSetMatrix v • z)‖ : ℝ) : ℂ) := by
      funext v
      rw [fdUnfoldTerm]
      exact integral_ofReal
    rw [this] at hnorm
    exact Complex.summable_ofReal.mp hnorm

end

end GaloisForLFunctions.HTGeometry
