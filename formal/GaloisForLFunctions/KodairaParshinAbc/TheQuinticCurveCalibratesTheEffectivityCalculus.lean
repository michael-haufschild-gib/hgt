import GaloisForLFunctions.KodairaParshinAbc.WeilBoundsForTheQuinticAndFreyCurves
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHyperellipticCalibration

/-!
# The quintic curve calibrates the effectivity calculus

The genus-two curve `C : y² + y = x⁵` carries the uniform `abc` inequality through its map
`y : C → P¹` of degree five.  Over a finite field `F` of characteristic different from `2` and `5`
its model `Y² = 4x⁵ + 1` is a squarefree quintic, so the corpus hyperelliptic calibration
(`ArithmeticEffectivityTheory.hyperellipticDatum`) attaches to `C` a curve datum of genus two:

* four normalized Frobenius eigenvalues, all of absolute value one (`quinticDatum_unitary`);
* Lefschetz numbers equal to point counts: over every finite extension `E` of `F`,
  `N_{[E:F]} = #{(x, y) ∈ E² : y² + y = x⁵} + 1` (`quinticDatum_pointCount`);
* every Frobenius window carries an effectivity function and the integral Rosati form has a naive
  height (`quinticDatum_window_exists_effectivity`, `quinticDatum_exists_naiveHeight`).
-/

noncomputable section

open Polynomial Finset

namespace GaloisForLFunctions.KodairaParshinAbc

open ArithmeticEffectivityTheory ArithmeticCastelnuovoSeveri

variable {F : Type*} [Field F] [Fintype F]

omit [Fintype F] in
theorem odd_natDegree_quinticModel (h2 : ringChar F ≠ 2) :
    Odd (quinticModel : F[X]).natDegree := by
  rw [natDegree_quinticModel (Ring.two_ne_zero h2)]
  exact ⟨2, rfl⟩

/-- **The curve datum of `y² + y = x⁵`** over `F`. -/
def quinticDatum (h2 : ringChar F ≠ 2) (h5 : (5 : F) ≠ 0) :
    CurveDatum (Fin (RHTower.Hyperelliptic.lRoots (quinticModel : F[X])).toList.length) :=
  hyperellipticDatum h2 (squarefree_quinticModel h5) (odd_natDegree_quinticModel h2)

variable (h2 : ringChar F ≠ 2) (h5 : (5 : F) ≠ 0)

include h2 in
/-- The datum has `2g = 4` eigenvalues: genus two. -/
theorem card_quinticDatum :
    Fintype.card (Fin (RHTower.Hyperelliptic.lRoots (quinticModel : F[X])).toList.length) = 4 := by
  rw [card_hyperellipticDatum (odd_natDegree_quinticModel h2),
    natDegree_quinticModel (Ring.two_ne_zero h2)]

/-- **Riemann hypothesis for `y² + y = x⁵`**: all normalized eigenvalues have absolute value one. -/
theorem quinticDatum_unitary : ∀ i, ‖(quinticDatum h2 h5).β i‖ = 1 :=
  hyperellipticDatum_unitary h2 (squarefree_quinticModel h5) (odd_natDegree_quinticModel h2)

omit [Fintype F] in
theorem aeval_quinticModel {E : Type*} [Field E] [Algebra F E] (x : E) :
    aeval x (quinticModel : F[X]) = 4 * x ^ 5 + 1 := by
  simp [quinticModel, map_ofNat]

/-- **The Lefschetz numbers of `C` are its point counts**: over a finite extension `E`,
`N_{[E:F]} = #{y² + y = x⁵}(E) + 1`. -/
theorem quinticDatum_pointCount (E : Type*) [Field E] [Fintype E] [Algebra F E] [DecidableEq E] :
    (quinticDatum h2 h5).pointCount (Module.finrank F E) =
      (univ.filter fun q : E × E => q.2 ^ 2 + q.2 = q.1 ^ 5).card + 1 := by
  have h2E : (2 : E) ≠ 0 := by
    have : ringChar E ≠ 2 := by rwa [← Algebra.ringChar_eq F E]
    exact Ring.two_ne_zero this
  rw [quinticDatum, hyperellipticDatum_pointCount, card_quintic_eq h2E]
  congr 1
  rw [Nat.cast_inj]
  congr 1
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, aeval_quinticModel]

/-- **Effectivity on the quintic curve**: every Frobenius window carries an effectivity function. -/
theorem quinticDatum_window_exists_effectivity (a b χ₀ : ℝ) (W : Finset ℕ) :
    ∃ h : SpanCycle → ℝ,
      RiemannInequality ((quinticDatum h2 h5).windowSurface W)
        (a • ((quinticDatum h2 h5).windowSurface W).H +
          b • ((quinticDatum h2 h5).windowSurface W).V) χ₀ h ∧
        DegreeBounded ((quinticDatum h2 h5).windowSurface W) h :=
  hyperellipticDatum_window_exists_effectivity h2 (squarefree_quinticModel h5)
    (odd_natDegree_quinticModel h2) a b χ₀ W

/-- **The integral Rosati form of the quintic curve has a naive height.** -/
theorem quinticDatum_exists_naiveHeight :
    ∃ h : ℤ[X] → ℝ, ∃ K B : ℝ, (∀ P, -K ≤ h P) ∧
      ∀ P, |h P - intRosatiDeg (quinticDatum h2 h5) P| ≤ B :=
  hyperellipticDatum_exists_naiveHeight h2 (squarefree_quinticModel h5)
    (odd_natDegree_quinticModel h2)

end GaloisForLFunctions.KodairaParshinAbc
