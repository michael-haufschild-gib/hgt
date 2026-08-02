import GaloisForLFunctions.HTGeometry.UniformGammaFieldDatum
import GaloisForLFunctions.HTGeometry.GammaFieldIntegerDatum

/-!
# The integer datum of a Gamma-field element, uniformly on a tube

The datum of a field element is the residue of the element itself, not of its cleared germ: the two
clearing polynomials contribute their leading coefficients and a shift of the argument exponent.
Both contributions are uniform on a tube, so the whole datum is.

`RepresentsOnTube` records the representation as a quotient of analytic germs read along every
vertical line at once; restricting it to one abscissa is `RepresentsOnLine`.
-/

open Filter Set Topology Function
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

local instance uniformGammaIntDomain : IsDomain upperEndAnalyticSubring :=
  isDomain_upperEndAnalyticSubring

local instance uniformGammaIntIntAlgebra : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _

local instance uniformGammaIntDifferential : Differential upperEndMeroField :=
  upperEndMeroFieldDifferential

local instance uniformGammaIntComplexAlgebra : Algebra ℂ upperEndMeroField :=
  upperEndComplexToMero.toAlgebra

local instance uniformGammaIntRatAlgebra : Algebra (RatFunc ℂ) upperEndMeroField :=
  upperEndRatfuncToMero.toAlgebra

/-- The vertical argument is nonzero beyond a fixed height. -/
theorem vertical_ne_zero_of_le {σ t : ℝ} (ht : 3 ≤ t) :
    ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  intro h0
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
  rw [h0] at him
  simp only [Complex.zero_im] at him
  linarith

/-- The vertical logarithm is nonzero beyond a fixed height. -/
theorem vertLog_ne_zero_of_le {t : ℝ} (ht : 3 ≤ t) : vertLog t ≠ 0 := by
  intro h0
  have hre : (vertLog t).re = Real.log t := by
    rw [vertLog]
    simp
  rw [h0] at hre
  simp only [Complex.zero_re] at hre
  have hlog1 : (1 : ℝ) ≤ Real.log t := by
    have hexp : Real.exp 1 ≤ t := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  linarith

/-- Shifting the argument exponent of a boundary shape, beyond a fixed height. -/
theorem gammaShapeZ_arg_add_of_le {σ t : ℝ} (ht : 3 ≤ t) (k a b Δ : ℤ) :
    gammaShapeZ σ k (a + Δ) b t
      = gammaShapeZ σ k a b t * ((σ : ℂ) + (t : ℂ) * Complex.I) ^ Δ := by
  have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_le ht
  rw [gammaShapeZ, gammaShapeZ, zpow_add₀ hs]
  ring

/-- **A polynomial against the corresponding power of the argument, uniformly on a tube.** -/
theorem tubeLimit_poly_div_pow {M : ℝ} (q : Polynomial ℂ) :
    TubeLimit M (fun σ t => q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
      / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q.natDegree) q.leadingCoeff := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_bound_polynomial_mul_inv_pow q
  refine tubeLimit_of_bound hB fun σ t hσ hσM ht => ?_
  have hval : q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
      / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ q.natDegree
      = q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        * (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ q.natDegree := by
    rw [div_eq_mul_inv, inv_pow]
  rw [hval]
  exact hbound σ t hσ ht

/-- The representation of a field element as a quotient of analytic germs, read on every vertical
line at once. -/
def RepresentsOnTube (x : upperEndMeroField) (φ : ℝ → ℝ → ℂ) : Prop :=
  ∃ (U V : upperEndAnalyticSubring) (G H : ℂ → ℂ),
    upperEndAnalyticSubring.subtype U = Germ.coeRingHom upperEndFilter G
      ∧ upperEndAnalyticSubring.subtype V = Germ.coeRingHom upperEndFilter H
      ∧ algebraMap upperEndAnalyticSubring upperEndMeroField V ≠ 0
      ∧ x = algebraMap upperEndAnalyticSubring upperEndMeroField U
          / algebraMap upperEndAnalyticSubring upperEndMeroField V
      ∧ ∀ σ t : ℝ, φ σ t
          = G ((σ : ℂ) + (t : ℂ) * Complex.I) / H ((σ : ℂ) + (t : ℂ) * Complex.I)

/-- A tube representation restricts to every vertical line. -/
theorem representsOnLine_of_representsOnTube {x : upperEndMeroField} {φ : ℝ → ℝ → ℂ}
    (h : RepresentsOnTube x φ) (σ : ℝ) : RepresentsOnLine σ x (φ σ) := by
  obtain ⟨U, V, G, H, hU, hV, hVne, hx, hφ⟩ := h
  exact ⟨U, V, G, H, hU, hV, hVne, hx, fun t => hφ σ t⟩

/-- **Every nonzero element of the Gamma field has an integer datum, uniformly on a tube.**  The
clearing polynomials contribute their leading coefficients and shift the argument exponent; both are
uniform for `0 < σ ≤ M`. -/
theorem exists_tubeLimit_gammaField_intDatum {M : ℝ} (hM : 0 < M) {x : upperEndMeroField}
    (hx : x ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (hx0 : x ≠ 0) :
    ∃ (k A B : ℤ) (φ : ℝ → ℝ → ℂ) (c : ℂ),
      c ≠ 0 ∧ RepresentsOnTube x φ
        ∧ TubeLimit M (fun σ t => φ σ t / gammaShapeZ σ k A B t) c := by
  classical
  obtain ⟨q₁, q₂, U, V, G, H, k₁, A₁, e₁, k₂, A₂, e₂, r,
    hq₁, hq₂, hr, hxeq, hUgerm, hVgerm, hlim⟩ := exists_tubeLimit_gammaField_datum hM hx hx0
  have hlead₁ : q₁.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq₁
  have hlead₂ : q₂.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq₂
  set Δ : ℤ := (q₂.natDegree : ℤ) - (q₁.natDegree : ℤ) with hΔ
  set φ : ℝ → ℝ → ℂ := fun σ t =>
    (q₂.eval ((σ : ℂ) + (t : ℂ) * Complex.I) * G ((σ : ℂ) + (t : ℂ) * Complex.I))
      / (q₁.eval ((σ : ℂ) + (t : ℂ) * Complex.I) * H ((σ : ℂ) + (t : ℂ) * Complex.I)) with hφ
  have hpoly := (tubeLimit_poly_div_pow (M := M) q₂).div (tubeLimit_poly_div_pow (M := M) q₁) hlead₁
  refine ⟨k₁ - k₂, (A₁ - A₂) + Δ, e₁ - e₂, φ,
    (q₂.leadingCoeff / q₁.leadingCoeff) * r, mul_ne_zero (div_ne_zero hlead₂ hlead₁) hr, ?_, ?_⟩
  · -- the representation, with the clearing polynomials absorbed into the germs
    refine ⟨upperEndPolyToAnalytic q₂ * U, upperEndPolyToAnalytic q₁ * V,
      fun z => q₂.eval z * G z, fun z => q₁.eval z * H z, ?_, ?_, ?_, ?_, fun σ t => rfl⟩
    · rw [map_mul, hUgerm, polyToAnalytic_subtype, ← map_mul]
      rfl
    · rw [map_mul, hVgerm, polyToAnalytic_subtype, ← map_mul]
      rfl
    · intro h0
      rw [hxeq] at hx0
      refine hx0 ?_
      rw [show upperEndPolyToMero q₁ * algebraMap upperEndAnalyticSubring upperEndMeroField V
          = algebraMap upperEndAnalyticSubring upperEndMeroField (upperEndPolyToAnalytic q₁ * V) by
        rw [map_mul]; rfl, h0, div_zero]
    · rw [hxeq, map_mul, map_mul]
      rfl
  · -- the residue: the polynomial ratio times the germ ratio
    have hmain := hpoly.mul hlim
    refine hmain.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
    have hs : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := vertical_ne_zero_of_le ht
    have hS₁ : gammaShapeZ σ k₁ A₁ e₁ t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
    have hS₂ : gammaShapeZ σ k₂ A₂ e₂ t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
    have hshape : gammaShapeZ σ (k₁ - k₂) ((A₁ - A₂) + Δ) (e₁ - e₂) t
        = (gammaShapeZ σ k₁ A₁ e₁ t / gammaShapeZ σ k₂ A₂ e₂ t)
          * (((σ : ℂ) + (t : ℂ) * Complex.I) ^ (q₂.natDegree : ℤ)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (q₁.natDegree : ℤ)) := by
      rw [gammaShapeZ_arg_add_of_le ht, gammaShapeZ_div_of_le hσ ht, hΔ, zpow_sub₀ hs]
    rw [hshape, hφ, zpow_natCast, zpow_natCast]
    dsimp only
    by_cases hq1t : q₁.eval ((σ : ℂ) + (t : ℂ) * Complex.I) = 0
    · rw [hq1t]
      simp
    · by_cases hHt : H ((σ : ℂ) + (t : ℂ) * Complex.I) = 0
      · rw [hHt]
        simp
      · field_simp

/-- **The projective boundary of a finite tuple, uniformly on a tube.**  One member dominates, and
every ratio to it converges with a single height threshold for all abscissas in `(0, M]`. -/
theorem exists_tubeLimit_dominant_gammaField_ratio {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N)
    (F : Fin N → upperEndMeroField)
    (hmem : ∀ α, F α ∈ differentialAdjoin (RatFunc ℂ) ({gammaUpperMero} : Set upperEndMeroField))
    (h0 : ∀ α, F α ≠ 0) :
    ∃ (β : Fin N) (φ : Fin N → ℝ → ℝ → ℂ) (d : Fin N → ℂ),
      (∀ α, RepresentsOnTube (F α) (φ α)) ∧ d β = 1
        ∧ ∀ α, TubeLimit M (fun σ t => φ α σ t / φ β σ t) (d α) := by
  classical
  choose k A B φ c hc hrep hlim using
    fun α => exists_tubeLimit_gammaField_intDatum hM (hmem α) (h0 α)
  obtain ⟨β, d, hdβ, hratio⟩ := exists_tubeLimit_dominant_ratio hM hN φ k A B c hc hlim
  exact ⟨β, φ, d, hrep, hdβ, hratio⟩

end

end GaloisForLFunctions.HTGeometry
