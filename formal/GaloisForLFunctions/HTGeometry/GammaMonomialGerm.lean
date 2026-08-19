import GaloisForLFunctions.HTGeometry.GermNegligible
import GaloisForLFunctions.HTGeometry.GammaMonomialTubeGrowth

/-!
# The germ of a Gamma monomial at the upper end

The unit shift multiplies a Gamma monomial by a rational function, so at the upper end the monomial
is an eigenvector of the shift with a rational eigenvalue.  This is the structure the shift
elimination runs on.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Polynomial

noncomputable section

variable {r : ℕ}

/-- The germ of a Gamma monomial at the upper end. -/
def gammaMonomialGerm (lam : Fin r → ℝ) (e : Fin r → ℤ) : Germ upperEndFilter ℂ :=
  ((gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) e : ℂ → ℂ) : Germ upperEndFilter ℂ)

/-- The shift eigenvalue of a Gamma monomial, as a rational function. -/
def gammaShiftFactor (lam : Fin r → ℝ) (e : Fin r → ℤ) : RatFunc ℂ :=
  ∏ k, (RatFunc.X + RatFunc.C ((lam k : ℝ) : ℂ)) ^ (e k)

/-- The numerator of the shift eigenvalue. -/
def gammaShiftNumer (lam : Fin r → ℝ) (e : Fin r → ℤ) : Polynomial ℂ :=
  ∏ k, (X + C ((lam k : ℝ) : ℂ)) ^ ((e k).toNat)

/-- The denominator of the shift eigenvalue. -/
def gammaShiftDenom (lam : Fin r → ℝ) (e : Fin r → ℤ) : Polynomial ℂ :=
  ∏ k, (X + C ((lam k : ℝ) : ℂ)) ^ (((-(e k)).toNat))

theorem gammaShiftDenom_ne_zero (lam : Fin r → ℝ) (e : Fin r → ℤ) :
    gammaShiftDenom lam e ≠ 0 := by
  rw [gammaShiftDenom]
  refine Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ ?_
  exact Polynomial.X_add_C_ne_zero _

theorem gammaShiftFactor_eq_div (lam : Fin r → ℝ) (e : Fin r → ℤ) :
    gammaShiftFactor lam e
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (gammaShiftNumer lam e)
        / algebraMap (Polynomial ℂ) (RatFunc ℂ) (gammaShiftDenom lam e) := by
  rw [gammaShiftFactor, gammaShiftNumer, gammaShiftDenom, map_prod, map_prod,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hXC : (RatFunc.X + RatFunc.C ((lam k : ℝ) : ℂ))
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (X + C ((lam k : ℝ) : ℂ)) := by
    rw [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hne : algebraMap (Polynomial ℂ) (RatFunc ℂ) (X + C ((lam k : ℝ) : ℂ)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (Polynomial.X_add_C_ne_zero _)
  rw [hXC, map_pow, map_pow, ← zpow_natCast _ ((e k).toNat),
    ← zpow_natCast _ (((-(e k)).toNat)), ← zpow_sub₀ hne]
  congr 1
  omega

/-- The eigenvalue germ is the germ of the pointwise product. -/
theorem ratFuncGerm_gammaShiftFactor (lam : Fin r → ℝ) (e : Fin r → ℤ) :
    ratFuncGerm (gammaShiftFactor lam e)
      = ((fun z : ℂ => ∏ k, (z + ((lam k : ℝ) : ℂ)) ^ (e k)) : Germ upperEndFilter ℂ) := by
  rw [gammaShiftFactor_eq_div, ratFuncGerm_div (gammaShiftDenom_ne_zero lam e)]
  have hmem : upperTail 0 ∈ upperEndFilter :=
    upperEndFilter_basis.mem_of_mem (i := (0 : ℝ)) trivial
  refine Germ.coe_eq.mpr ?_
  filter_upwards [hmem] with z hz
  have hzim : (0 : ℝ) < z.im := hz
  have hne : ∀ k : Fin r, z + ((lam k : ℝ) : ℂ) ≠ 0 := by
    intro k hcon
    have him : (z + ((lam k : ℝ) : ℂ)).im = z.im := by simp
    rw [hcon] at him
    simp only [Complex.zero_im] at him
    linarith
  rw [gammaShiftNumer, gammaShiftDenom, Polynomial.eval_prod, Polynomial.eval_prod,
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  rw [← zpow_natCast _ ((e k).toNat), ← zpow_natCast _ (((-(e k)).toNat)),
    ← zpow_sub₀ (hne k)]
  congr 1
  omega

/-- **The Gamma monomial germ is a shift eigenvector with rational eigenvalue.** -/
theorem upperEndTranslateGerm_gammaMonomialGerm (lam : Fin r → ℝ) (e : Fin r → ℤ) :
    upperEndTranslateGerm 1 (gammaMonomialGerm lam e)
      = ratFuncGerm (gammaShiftFactor lam e) * gammaMonomialGerm lam e := by
  simp only [gammaMonomialGerm]
  rw [upperEndTranslateGerm_coe, ratFuncGerm_gammaShiftFactor, ← Germ.coe_mul]
  have hmem : upperTail 0 ∈ upperEndFilter :=
    upperEndFilter_basis.mem_of_mem (i := (0 : ℝ)) trivial
  refine Germ.coe_eq.mpr ?_
  filter_upwards [hmem] with z hz
  have hzim : (0 : ℝ) < z.im := hz
  have hne : ∀ k : Fin r, z + ((lam k : ℝ) : ℂ) ≠ 0 := by
    intro k hcon
    have him : (z + ((lam k : ℝ) : ℂ)).im = z.im := by simp
    rw [hcon] at him
    simp only [Complex.zero_im] at him
    linarith
  exact gammaMonomial_shift (fun i => ((lam i : ℝ) : ℂ)) e hne

end

end GaloisForLFunctions.HTGeometry
