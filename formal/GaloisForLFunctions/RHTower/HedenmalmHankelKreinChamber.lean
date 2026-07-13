import GaloisForLFunctions.RHTower.HedenmalmLocalFrameObstruction
import GaloisForLFunctions.RHTower.XiHedenmalmDeBrangesSeam

/-!
# The Hedenmalm source orbit lies in a split Hankel--Krein chamber

The center-mixed Hedenmalm kernel has separable rank four and an ambient Hermitian form of
signature `(2, 2)`.  Schwarz reality and the functional equation constrain the actual theta
source to a pointed real slice of this split space.  On that source orbit the Krein value is
exactly the horizontal derivative of the squared Xi modulus.

This is unconditional orientation geometry, not an orientation theorem.  It identifies the
missing sign as global avoidance of the negative chamber by one analytically fixed source orbit.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- The radial Hankel kernel obtained after center mixing. -/
def hedenmalmHankelKernel (a x y : ℝ) : ℝ :=
  (x + y) * Real.sinh (a * (x + y))

def hedenmalmHankelPlus (a x : ℝ) : ℝ := Real.exp (a * x)

def hedenmalmHankelPlusTangent (a x : ℝ) : ℝ := x * Real.exp (a * x)

def hedenmalmHankelMinus (a x : ℝ) : ℝ := Real.exp (-a * x)

def hedenmalmHankelMinusTangent (a x : ℝ) : ℝ := x * Real.exp (-a * x)

/-- Exact separable rank-four decomposition of the center-mixed Hankel kernel. -/
theorem hedenmalmHankelKernel_rankFour_decomposition (a x y : ℝ) :
    hedenmalmHankelKernel a x y =
      (1 / 2 : ℝ) *
        (hedenmalmHankelPlusTangent a x * hedenmalmHankelPlus a y +
          hedenmalmHankelPlus a x * hedenmalmHankelPlusTangent a y -
          hedenmalmHankelMinusTangent a x * hedenmalmHankelMinus a y -
          hedenmalmHankelMinus a x * hedenmalmHankelMinusTangent a y) := by
  simp only [hedenmalmHankelKernel, hedenmalmHankelPlus,
    hedenmalmHankelPlusTangent, hedenmalmHankelMinus,
    hedenmalmHankelMinusTangent, Real.sinh_eq]
  rw [show a * (x + y) = a * x + a * y by ring,
    show -(a * x + a * y) = -a * x + -a * y by ring,
    Real.exp_add, Real.exp_add]
  ring_nf

/-- The split Hermitian coordinate form of the rank-four Hankel kernel. -/
def hedenmalmHankelKreinForm
    (uPlus vPlus uMinus vMinus : ℂ) : ℝ :=
  ((starRingEnd ℂ) uPlus * vPlus).re -
    ((starRingEnd ℂ) uMinus * vMinus).re

/-- Light-cone normal form, displaying two positive and two negative complex directions. -/
theorem hedenmalmHankelKreinForm_lightCone
    (uPlus vPlus uMinus vMinus : ℂ) :
    hedenmalmHankelKreinForm uPlus vPlus uMinus vMinus =
      (1 / 4 : ℝ) *
        (normSq (uPlus + vPlus) - normSq (uPlus - vPlus) -
          normSq (uMinus + vMinus) + normSq (uMinus - vMinus)) := by
  simp only [hedenmalmHankelKreinForm, normSq_apply, add_re, add_im,
    sub_re, sub_im, mul_re, conj_re, conj_im]
  ring_nf

@[simp] theorem hedenmalmHankelKreinForm_posDirection_one :
    hedenmalmHankelKreinForm 1 1 0 0 = 1 := by
  simp [hedenmalmHankelKreinForm]

@[simp] theorem hedenmalmHankelKreinForm_negDirection_one :
    hedenmalmHankelKreinForm 1 (-1) 0 0 = -1 := by
  simp [hedenmalmHankelKreinForm]

@[simp] theorem hedenmalmHankelKreinForm_negDirection_two :
    hedenmalmHankelKreinForm 0 0 1 1 = -1 := by
  simp [hedenmalmHankelKreinForm]

@[simp] theorem hedenmalmHankelKreinForm_posDirection_two :
    hedenmalmHankelKreinForm 0 0 1 (-1) = 1 := by
  simp [hedenmalmHankelKreinForm]

/-- On the even-real source slice, the split form reduces to one Lorentzian orientation
current. -/
theorem hedenmalmHankelKreinForm_evenReal_reduction (u v : ℂ) :
    hedenmalmHankelKreinForm u v
        ((starRingEnd ℂ) u) (-((starRingEnd ℂ) v)) =
      2 * (((starRingEnd ℂ) u) * v).re := by
  simp only [hedenmalmHankelKreinForm, starRingEnd_self_apply]
  simp only [mul_re, conj_re, conj_im, neg_re, neg_im]
  ring_nf

/-- Value coordinate of the right-hand theta/Xi orbit. -/
def thetaXiHankelOrbitValuePlus (a b : ℝ) : ℂ :=
  XiC ((b : ℂ) - (a : ℂ) * I)

/-- Horizontal tangent coordinate of the right-hand theta/Xi orbit. -/
def thetaXiHankelOrbitTangentPlus (a b : ℝ) : ℂ :=
  -I * deriv XiC ((b : ℂ) - (a : ℂ) * I)

/-- Value coordinate on the reflected theta/Xi orbit. -/
def thetaXiHankelOrbitValueMinus (a b : ℝ) : ℂ :=
  XiC ((b : ℂ) + (a : ℂ) * I)

/-- Horizontal tangent coordinate on the reflected theta/Xi orbit. -/
def thetaXiHankelOrbitTangentMinus (a b : ℝ) : ℂ :=
  -I * deriv XiC ((b : ℂ) + (a : ℂ) * I)

/-- The plus value coordinate is the completed Xi value on the line `Re s = 1/2 + a`. -/
theorem thetaXiHankelOrbitValuePlus_eq_xi (a b : ℝ) :
    thetaXiHankelOrbitValuePlus a b =
      xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) := by
  rw [thetaXiHankelOrbitValuePlus, XiC]
  congr 1
  simp [sub_mul, mul_assoc, I_mul_I]
  ring

/-- The plus tangent coordinate is the horizontal Xi derivative. -/
theorem thetaXiHankelOrbitTangentPlus_eq_deriv_xi (a b : ℝ) :
    thetaXiHankelOrbitTangentPlus a b =
      deriv xi ((1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I) := by
  rw [thetaXiHankelOrbitTangentPlus, deriv_XiC_eq_deriv_xi_mul_I]
  have harg : (1 : ℂ) / 2 + ((b : ℂ) - (a : ℂ) * I) * I =
      (1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I := by
    simp [sub_mul, mul_assoc, I_mul_I]
    ring
  rw [harg]
  ring_nf
  rw [I_sq]
  ring

/-- Schwarz reality identifies the reflected value coordinate with the conjugate plus
coordinate. -/
theorem thetaXiHankelOrbitValueMinus_eq_conj (a b : ℝ) :
    thetaXiHankelOrbitValueMinus a b =
      (starRingEnd ℂ) (thetaXiHankelOrbitValuePlus a b) := by
  rw [thetaXiHankelOrbitValueMinus, thetaXiHankelOrbitValuePlus]
  have harg : (b : ℂ) + (a : ℂ) * I =
      (starRingEnd ℂ) ((b : ℂ) - (a : ℂ) * I) := by
    simp
  rw [harg, xiHedenmalm_XiC_conj]

/-- The functional-equation/Schwarz reflection reverses the tangent orientation. -/
theorem thetaXiHankelOrbitTangentMinus_eq_neg_conj (a b : ℝ) :
    thetaXiHankelOrbitTangentMinus a b =
      -((starRingEnd ℂ) (thetaXiHankelOrbitTangentPlus a b)) := by
  rw [thetaXiHankelOrbitTangentMinus, thetaXiHankelOrbitTangentPlus]
  have harg : (b : ℂ) + (a : ℂ) * I =
      (starRingEnd ℂ) ((b : ℂ) - (a : ℂ) * I) := by
    simp
  rw [harg, deriv_XiC_conj]
  simp

/-- The actual source orbit reduces the ambient split form to its scalar orientation current. -/
theorem thetaXiHankelOrbit_kreinForm_eq (a b : ℝ) :
    hedenmalmHankelKreinForm
        (thetaXiHankelOrbitValuePlus a b)
        (thetaXiHankelOrbitTangentPlus a b)
        (thetaXiHankelOrbitValueMinus a b)
        (thetaXiHankelOrbitTangentMinus a b) =
      2 * (((starRingEnd ℂ) (thetaXiHankelOrbitValuePlus a b)) *
        thetaXiHankelOrbitTangentPlus a b).re := by
  rw [thetaXiHankelOrbitValueMinus_eq_conj,
    thetaXiHankelOrbitTangentMinus_eq_neg_conj]
  exact hedenmalmHankelKreinForm_evenReal_reduction _ _

/-- The split Krein value of the actual theta/Xi orbit is exactly the horizontal derivative of
the squared completed-Xi modulus.  The missing Hilbert--Polya sign is therefore a chamber-avoidance
theorem for this one pointed analytic orbit, rather than positivity of the ambient form. -/
theorem hasDerivAt_thetaXiHankelOrbit_normSq (a b : ℝ) :
    HasDerivAt
      (fun t : ℝ => normSq (thetaXiHankelOrbitValuePlus t b))
      (hedenmalmHankelKreinForm
        (thetaXiHankelOrbitValuePlus a b)
        (thetaXiHankelOrbitTangentPlus a b)
        (thetaXiHankelOrbitValueMinus a b)
        (thetaXiHankelOrbitTangentMinus a b)) a := by
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have hz : HasDerivAt (fun t : ℝ => (b : ℂ) - (t : ℂ) * I) (-I) a := by
    have h := (Complex.ofRealCLM.hasDerivAt (x := a)).mul_const I
    simpa using h.const_sub (b : ℂ)
  have hXi : HasDerivAt
      (fun t : ℝ => XiC ((b : ℂ) - (t : ℂ) * I))
      (deriv XiC z * (-I)) a := by
    simpa [z] using
      (XiC_differentiable.differentiableAt.hasDerivAt.comp a hz)
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt a hXi
  have him := Complex.imCLM.hasFDerivAt.comp_hasDerivAt a hXi
  have hsq := (hre.mul hre).add (him.mul him)
  rw [thetaXiHankelOrbit_kreinForm_eq]
  convert hsq using 1
  dsimp [z]
  simp only [thetaXiHankelOrbitValuePlus, thetaXiHankelOrbitTangentPlus,
    mul_re, conj_re, conj_im, neg_re, neg_im, I_re, I_im]
  ring_nf

/-- The Fourier transform of the actual theta autocorrelation tangent is exactly the Krein value
of the pointed source orbit.  This closes the source-to-chamber incidence without any positivity
or nonvanishing premise. -/
theorem fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm
    {a : ℝ} (ha : |a| < 1) (b : ℝ) :
    FourierTransform.fourier
        (thetaCuspHorizontalAutocorrelationTangent a ha)
        (b / (2 * Real.pi)) =
      (hedenmalmHankelKreinForm
        (thetaXiHankelOrbitValuePlus a b)
        (thetaXiHankelOrbitTangentPlus a b)
        (thetaXiHankelOrbitValueMinus a b)
        (thetaXiHankelOrbitTangentMinus a b) : ℝ) := by
  rw [fourier_thetaCuspHorizontalAutocorrelationTangent_scaled ha,
    thetaXiHankelOrbit_kreinForm_eq,
    thetaXiHankelOrbitValuePlus_eq_xi,
    thetaXiHankelOrbitTangentPlus_eq_deriv_xi]
  let s : ℂ := (1 : ℂ) / 2 + (a : ℂ) + (b : ℂ) * I
  have harg : (1 : ℂ) / 2 + (a : ℂ) - (b : ℂ) * I =
      (starRingEnd ℂ) s := by
    apply Complex.ext <;> simp [s]
  rw [harg, xi_conj, xi_deriv_conj]
  dsimp [s]
  apply Complex.ext
  · simp only [add_re, mul_re, conj_re, conj_im, ofReal_re]
    ring
  · simp only [add_im, mul_im, conj_re, conj_im, ofReal_im]
    ring

end RHTower
