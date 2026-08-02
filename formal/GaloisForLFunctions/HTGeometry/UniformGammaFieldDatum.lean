import GaloisForLFunctions.HTGeometry.UniformGammaAlgebraDatum

/-!
# The datum of an element of the Gamma field, uniformly on a tube

An element of the differential field generated over `ℂ(s)` by `Γ` is a quotient of two elements of
the jet algebra.  Each has a nonzero residue against an integer Gamma shape uniformly on a tube, and
the quotient of two such residues is again one — the denominator's residue is nonzero, so the
quotient is bounded away from the singular set at all large heights at once.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance uniformGammaFieldDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance uniformGammaFieldIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance uniformGammaFieldDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance uniformGammaFieldComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance uniformGammaFieldRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- A quotient of tube limits with nonvanishing denominator. -/
theorem TubeLimit.div {M : ℝ} {f g : ℝ → ℝ → ℂ} {a b : ℂ} (hf : TubeLimit M f a)
    (hg : TubeLimit M g b) (hb : b ≠ 0) :
    TubeLimit M (fun σ t => f σ t / g σ t) (a / b) := by
  have h := hf.mul (hg.inv hb)
  rw [div_eq_mul_inv]
  exact h.congr (T₀ := 0) fun σ t _ _ _ => (div_eq_mul_inv _ _).symm

/-- **Every nonzero element of the Gamma field over the rational base has a tube datum.**  Clearing
the field denominator and the coefficient denominators presents it as a quotient of two analytic
germs, each with a nonzero residue against an integer Gamma shape uniformly for `0 < σ ≤ M`; the
quotient of the two residues is nonzero. -/
theorem exists_tubeLimit_gammaField_datum {M : ℝ} (hM : 0 < M) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) :
    ∃ (q₁ q₂ : Polynomial ℂ) (U V : upperEndAnalyticSubring) (G H : ℂ → ℂ)
      (k₁ A₁ e₁ k₂ A₂ e₂ : ℤ) (r : ℂ),
      q₁ ≠ 0 ∧ q₂ ≠ 0 ∧ r ≠ 0
        ∧ x = (upperEndPolyToMero q₂
              * algebraMap upperEndAnalyticSubring upperEndMeroField U)
            / (upperEndPolyToMero q₁
              * algebraMap upperEndAnalyticSubring upperEndMeroField V)
        ∧ upperEndAnalyticSubring.subtype U = Germ.coeRingHom upperEndFilter G
        ∧ upperEndAnalyticSubring.subtype V = Germ.coeRingHom upperEndFilter H
        ∧ TubeLimit M (fun σ t =>
            (G ((σ : ℂ) + (t : ℂ) * Complex.I) / gammaShapeZ σ k₁ A₁ e₁ t)
            / (H ((σ : ℂ) + (t : ℂ) * Complex.I) / gammaShapeZ σ k₂ A₂ e₂ t)) r := by
  classical
  obtain ⟨D, hDmem, hD0, hxD⟩ := exists_jetAlgebra_denominator (F := RatFunc ℂ) hx
  have hxD0 : x * D ≠ 0 := mul_ne_zero hx0 hD0
  obtain ⟨q₁, U, G, k₁, A₁, e₁, r₁, hq₁, hr₁, hU, hGgerm, hGlim⟩ :=
    exists_tubeLimit_gammaAlgebra_datum hM hxD hxD0
  obtain ⟨q₂, V, H, k₂, A₂, e₂, r₂, hq₂, hr₂, hV, hHgerm, hHlim⟩ :=
    exists_tubeLimit_gammaAlgebra_datum hM hDmem hD0
  have hq₁mero : upperEndPolyToMero q₁ ≠ 0 := fun h =>
    hq₁ (upperEndPolyToMero_injective (by rw [h, map_zero]))
  have hq₂mero : upperEndPolyToMero q₂ ≠ 0 := fun h =>
    hq₂ (upperEndPolyToMero_injective (by rw [h, map_zero]))
  have hVne : algebraMap upperEndAnalyticSubring upperEndMeroField V ≠ 0 := by
    rw [← hV]
    exact mul_ne_zero hq₂mero hD0
  have hxeq : x = (upperEndPolyToMero q₂
        * algebraMap upperEndAnalyticSubring upperEndMeroField U)
      / (upperEndPolyToMero q₁
        * algebraMap upperEndAnalyticSubring upperEndMeroField V) := by
    rw [← hU, ← hV]
    field_simp
  exact ⟨q₁, q₂, U, V, G, H, k₁, A₁, e₁, k₂, A₂, e₂, r₁ / r₂,
    hq₁, hq₂, div_ne_zero hr₁ hr₂, hxeq, hGgerm, hHgerm, hGlim.div hHlim hr₂⟩

end

end GaloisForLFunctions.HTGeometry
