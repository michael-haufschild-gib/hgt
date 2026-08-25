import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedPoleResidueDerivative

/-!
# Real-displacement derivative of the Gaussian AFE pole residue

The displacement direction has `d(1-s(d))/dd = 1`.  The resulting elementary
quotient derivative is also `I` times the already formalized height derivative.
-/

noncomputable section

namespace RHTower

open Complex

def smoothAFEZetaDisplacedPoleResidueDisplacementDerivative
    (d x tau : ℝ) : ℂ :=
  let z := smoothAFEZetaDisplacedPoleCoordinate d tau
  let A := (x : ℂ) ^ z
  let E := Complex.exp (z ^ 2)
  let Az := A * Complex.log (x : ℂ)
  let Ez := E * (2 * z)
  ((Az * E + A * Ez) * z - A * E) / z ^ 2

theorem smoothAFEZetaDisplacedPoleResidueDisplacementDerivative_eq_I_mul_height
    (d x tau : ℝ) :
    smoothAFEZetaDisplacedPoleResidueDisplacementDerivative d x tau =
      I * smoothAFEZetaDisplacedPoleResidueHeightDerivative d x tau := by
  unfold smoothAFEZetaDisplacedPoleResidueDisplacementDerivative
    smoothAFEZetaDisplacedPoleResidueHeightDerivative
  ring_nf
  simp
  ring

theorem hasDerivAt_smoothAFEZetaShiftedPoleResidue_displacement
    {d x : ℝ} (hd : 0 < d) (hx : 0 < x) (tau : ℝ) :
    HasDerivAt
      (fun u : ℝ =>
        smoothAFEZetaShiftedPoleResidue (displacedLinePt u tau) x)
      (smoothAFEZetaDisplacedPoleResidueDisplacementDerivative d x tau) d := by
  let z : ℝ → ℂ := fun u => smoothAFEZetaDisplacedPoleCoordinate u tau
  have hs : HasDerivAt (fun u : ℝ => displacedLinePt u tau) (-1 : ℂ) d := by
    have hreal :=
      ((hasDerivAt_const d (1 / 2 : ℝ)).sub (hasDerivAt_id d)).ofReal_comp
    simpa [displacedLinePt] using hreal.add_const ((tau : ℂ) * I)
  have hz : HasDerivAt z (1 : ℂ) d := by
    change HasDerivAt (fun u : ℝ => 1 - displacedLinePt u tau) 1 d
    simpa using hs.const_sub (1 : ℂ)
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpowC :=
    (Complex.hasStrictDerivAt_const_cpow
      (x := (x : ℂ)) (y := z d) (Or.inl hxC)).hasDerivAt
  have hpow := hpowC.comp d hz
  have hexp := (hz.pow 2).cexp
  have hnum := hpow.mul hexp
  have hdiv := hnum.div hz
    (smoothAFEZetaDisplacedPoleCoordinate_ne_zero hd tau)
  have hfun :
      (fun u : ℝ =>
        smoothAFEZetaShiftedPoleResidue (displacedLinePt u tau) x) =
      (((fun y : ℂ => (x : ℂ) ^ y) ∘ z) *
        (fun u : ℝ => Complex.exp ((z ^ 2) u))) / z := by
    funext u
    simp only [smoothAFEZetaShiftedPoleResidue, z,
      smoothAFEZetaDisplacedPoleCoordinate, Function.comp_apply, Pi.mul_apply,
      Pi.div_apply, Pi.pow_apply]
  have hcoeff :
      smoothAFEZetaDisplacedPoleResidueDisplacementDerivative d x tau =
        (((((x : ℂ) ^ z d * Complex.log (x : ℂ)) * 1) *
              Complex.exp ((z ^ 2) d) +
            (((fun y : ℂ => (x : ℂ) ^ y) ∘ z) d) *
              (Complex.exp ((z ^ 2) d) *
                ((2 : ℂ) * (z d) ^ (2 - 1) * 1))) * z d -
          ((((fun y : ℂ => (x : ℂ) ^ y) ∘ z) *
            (fun u : ℝ => Complex.exp ((z ^ 2) u))) d) * 1) /
            (z d) ^ 2 := by
    dsimp only [smoothAFEZetaDisplacedPoleResidueDisplacementDerivative, z,
      Function.comp_apply, Pi.mul_apply, Pi.pow_apply]
    norm_num
  rw [hfun, hcoeff]
  exact hdiv

end RHTower
