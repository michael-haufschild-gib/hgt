import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMJointSourceTimeField

/-!
# A common radial differential producer for both literal BM source branches

The physical branches have one scalar eigenvalue. Their different cubic source
coefficients are evaluations of one radial differential operator on their actual
ingoing seed fields. Holding ingoing time fixed retains the complete onset and
introduces no derivative or division of the clock. The angular Laplacian is the
actual one on the original theta half-square.
-/

namespace RHTower.D4BMCommonRadialSource
open GaloisForLFunctions.HTGeometry
open D4BMJointSource D4BMModularCore D4BMHorizon D4BMGlobalAngularResponse
noncomputable section
set_option autoImplicit false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

/-- Common scalar eigenvalue of the two original physical source branches. -/
def scalarParameter (q : XiZeroCopy) : ℂ := (q.1:ℂ)*((q.1:ℂ)-1)

private theorem scalarParameter_rate (q : XiZeroCopy) (branch : Bool) :
    scalarParameter q=(physicalRate q branch+1)*(physicalRate q branch+2) := by
  cases branch <;> dsimp [scalarParameter,physicalRate] <;> ring

/-- Original ingoing seed, with ingoing time held fixed under radial differentiation. -/
def seed (s a : ℂ) (v x : ℝ) (J : ℂ) : ℂ :=
  sourceAmplitude s 0 a 1 x*timeOnset (2*s) v*J

/-- Radial generator `(1+u)partial_u+3` written in the true tortoise coordinate. -/
def radialGenerator (F : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv F x/((radialUnit x:ℂ)-1)+3*F x

/-- One source operator for both physical branches, with its actual angular Laplacian input. -/
def commonSource (lam : ℂ) (F LF : ℝ → ℂ) (x : ℝ) : ℂ :=
  (5*lam-6)/4*F x+(radialUnit x:ℂ)^(2 : ℕ)/8*
    ((4*lam+1)*(lam+2)*F x-(lam+4)*LF x-
      (7*lam-2)*radialGenerator F x+2*radialGenerator LF x)

private theorem seed_derivative (s a : ℂ) (v x : ℝ) (J : ℂ) :
    HasDerivAt (fun y => seed s a v y J)
      (amplitudeRate s 0 (radialUnit x)*seed s a v x J) x := by
  apply (((sourceAmplitude_hasDerivAt s 0 a 1 x).mul_const (timeOnset (2*s) v)).mul_const J).congr_deriv
  dsimp [seed]
  ring

private theorem radialGenerator_seed (s a : ℂ) (v : ℝ) (x : {x : ℝ // x < 0}) (J : ℂ) :
    radialGenerator (fun y => seed s a v y J) x.val=(2*s+3)*seed s a v x.val J := by
  have hn : (radialUnit x.val:ℂ)-1 ≠ 0 := by
    exact_mod_cast (sub_ne_zero.mpr (ne_of_lt (radialUnit_bounds x.val x.property).2))
  rw [radialGenerator,(seed_derivative s a v x.val J).deriv]
  dsimp [amplitudeRate]
  field_simp [hn]
  ring

/-- The original fixed-clock source on either physical branch is produced by the
same radial operator. Both the complete theta half-square and its actual Laplacian
are retained; no source, clock, eigen-equation or cancellation premise is supplied. -/
theorem timeOriginalForcing_common_source (q : XiZeroCopy) (branch : Bool) (a : ℂ)
    (v : ℝ) (x : {x : ℝ // x < 0}) (z : UpperHalfPlane) :
    timeOriginalForcing q branch a (v-x.val) x.val (coordinates z) =
      -2*(1-(radialUnit x.val:ℂ)^(2 : ℕ))*(radialUnit x.val:ℂ)*
        commonSource (scalarParameter q)
          (fun y => seed (physicalRate q branch) a v y (fullSquarePotential q (coordinates z)))
          (fun y => seed (physicalRate q branch) a v y
            (scalarLaplacian (fullSquarePotential q) (coordinates z))) x.val := by
  rw [commonSource,radialGenerator_seed,radialGenerator_seed,scalarParameter_rate q branch,
    fullSquarePotential_laplacian q branch (coordinates z) z.im_pos]
  simp only [timeOriginalForcing,sub_add_cancel,originalForcing,seed]
  ring

/-- The common producer in ordinary compact-radial derivative form. -/
theorem commonSource_differential_form (lam : ℂ) (F LF : ℝ → ℂ) (x : {x : ℝ // x < 0}) :
    commonSource lam F LF x.val =
      (5*lam-6)/4*F x.val+(radialUnit x.val:ℂ)^(2 : ℕ)/8*
        ((lam-2)*(4*(lam-1)*F x.val-LF x.val)-
          ((7*lam-2)*deriv F x.val-2*deriv LF x.val)/((radialUnit x.val:ℂ)-1)) := by
  dsimp [commonSource,radialGenerator]
  ring

end
end RHTower.D4BMCommonRadialSource
