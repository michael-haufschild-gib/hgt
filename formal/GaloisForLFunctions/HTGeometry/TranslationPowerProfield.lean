import GaloisForLFunctions.HTGeometry.DifferentialAdjoinBaseScaling
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval
import GaloisForLFunctions.HTGeometry.LocalAnalyticExponentialClock
import GaloisForLFunctions.HTGeometry.MeromorphicGammaOrbit

/-!
# The complete positive-power translation profield

For an entire `E` and `n ≥ 1` the profield

`T_n(E) = C(z) (D^q (E(z+h)^n) : h in C, q >= 0)`

is the differential subfield of the global meromorphic field generated over the rational coordinate
field by all translated `n`-th powers.  Multiplying `E` by a nonzero polynomial does not change it:
each translated power changes by a nonzero element of `C(z)`, which is already in the base.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

/-- The domain of entire germs. -/
local instance profieldEntireDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

/-- The rational coordinate field inside the global meromorphic field. -/
local instance profieldRatFuncAlgebra :
    Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ).toAlgebra

/-- The ordinary derivative as the differential structure on the global meromorphic field. -/
local instance profieldMeroDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
    Set.univ_nonempty

/-- The rational coordinate field with its own derivation. -/
local instance profieldRatFuncDifferential : Differential (RatFunc ℂ) :=
  ratFuncCoordinateDifferential

/-- The rational coordinate embedding is differential. -/
local instance profieldRatFuncDifferentialAlgebra :
    DifferentialAlgebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  meroFieldRatFuncDifferentialAlgebra isOpen_univ isPreconnected_univ
    Set.univ_nonempty Set.infinite_univ

/-- A polynomial germ is the image of the polynomial under the rational coordinate embedding. -/
theorem analyticMeroElement_polyEval (r : Polynomial ℂ) :
    analyticMeroElement (fun z : ℂ => Polynomial.eval z r)
        (analyticOnNhd_polyEval (Set.univ : Set ℂ) r)
      = algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))
          (algebraMap (Polynomial ℂ) (RatFunc ℂ) r) := by
  show _ = ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
    Set.infinite_univ (algebraMap (Polynomial ℂ) (RatFunc ℂ) r)
  rw [ratfuncToMero_algebraMap_polynomial, polyToMero, RingHom.comp_apply, analyticMeroElement]
  congr 1

/-- `E(z+h)^n` as an entire function. -/
def translationPower (E : ℂ → ℂ) (n : ℕ) (h : ℂ) : ℂ → ℂ := fun z => (E (z + h)) ^ n

theorem analyticOnNhd_translationPower {E : ℂ → ℂ} (hE : AnalyticOnNhd ℂ E Set.univ) (n : ℕ)
    (h : ℂ) : AnalyticOnNhd ℂ (translationPower E n h) Set.univ := by
  intro z _
  have hshift : AnalyticAt ℂ (fun w : ℂ => w + h) z := by fun_prop
  have hcomp : AnalyticAt ℂ (fun w : ℂ => E (w + h)) z :=
    AnalyticAt.comp (g := E) (f := fun w : ℂ => w + h) (x := z) (hE (z + h) (Set.mem_univ _))
      hshift
  exact hcomp.pow n

/-- The order-zero generators of the positive-power translation profield. -/
def translationPowerGen (E : ℂ → ℂ) (hE : AnalyticOnNhd ℂ E Set.univ) (n : ℕ) :
    ℂ → meroField (Set.univ : Set ℂ) :=
  fun h => analyticMeroElement (translationPower E n h) (analyticOnNhd_translationPower hE n h)

/-- **The complete positive-power translation profield** `T_n(E)`. -/
def translationPowerProfield (E : ℂ → ℂ) (hE : AnalyticOnNhd ℂ E Set.univ) (n : ℕ) :
    IntermediateField (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
  differentialAdjoin (RatFunc ℂ) (Set.range (translationPowerGen E hE n))

/-- The `h`-translate of a polynomial. -/
def shiftPoly (p : Polynomial ℂ) (h : ℂ) : Polynomial ℂ :=
  p.comp (Polynomial.X + Polynomial.C h)

theorem eval_shiftPoly (p : Polynomial ℂ) (h z : ℂ) :
    Polynomial.eval z (shiftPoly p h) = Polynomial.eval (z + h) p := by
  rw [shiftPoly, Polynomial.eval_comp]
  simp

theorem shiftPoly_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) (h : ℂ) : shiftPoly p h ≠ 0 := by
  intro hcon
  refine hp (Polynomial.funext fun x => ?_)
  have := eval_shiftPoly p h (x - h)
  rw [hcon] at this
  simpa using this.symm

/-- **A nonzero polynomial factor does not change the positive-power translation profield.** -/
theorem translationPowerProfield_mul_polynomial {E F : ℂ → ℂ}
    (hE : AnalyticOnNhd ℂ E Set.univ) (hF : AnalyticOnNhd ℂ F Set.univ)
    {p : Polynomial ℂ} (hp : p ≠ 0) (hEF : ∀ z, F z = Polynomial.eval z p * E z) (n : ℕ) :
    translationPowerProfield F hF n = translationPowerProfield E hE n := by
  set b : ℂ → RatFunc ℂ :=
    fun h => algebraMap (Polynomial ℂ) (RatFunc ℂ) (shiftPoly p h ^ n) with hb
  have hbne : ∀ h, b h ≠ 0 := by
    intro h
    rw [hb]
    exact fun hc => pow_ne_zero n (shiftPoly_ne_zero hp h)
      (IsFractionRing.injective (Polynomial ℂ) (RatFunc ℂ) (by simpa using hc))
  have hgen : translationPowerGen F hF n
      = fun h => algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) (b h)
          * translationPowerGen E hE n h := by
    funext h
    have hpoly : AnalyticOnNhd ℂ (fun z : ℂ => Polynomial.eval z (shiftPoly p h ^ n))
        (Set.univ : Set ℂ) := analyticOnNhd_polyEval (Set.univ : Set ℂ) _
    have hfun : translationPower F n h
        = fun z => Polynomial.eval z (shiftPoly p h ^ n) * translationPower E n h z := by
      funext z
      rw [translationPower, translationPower, hEF (z + h), Polynomial.eval_pow, eval_shiftPoly]
      ring
    rw [translationPowerGen, translationPowerGen,
      analyticMeroElement_congr _ (hpoly.mul (analyticOnNhd_translationPower hE n h)) hfun,
      analyticMeroElement_mul hpoly (analyticOnNhd_translationPower hE n h),
      analyticMeroElement_polyEval (shiftPoly p h ^ n)]
  rw [translationPowerProfield, translationPowerProfield, hgen]
  exact differentialAdjoin_mul_base (translationPowerGen E hE n) b hbne

end

end GaloisForLFunctions.HTGeometry
