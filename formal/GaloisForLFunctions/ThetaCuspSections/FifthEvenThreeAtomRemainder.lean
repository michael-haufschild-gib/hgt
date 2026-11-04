import GaloisForLFunctions.ThetaCuspSections.FifthEvenLeadingPairReserve
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspThreeAtomCauchyTail
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourCentralBound

/-!
# Remaining pairs and the three-atom tail in fifth even coordinates

The common positive factor is `4q² exp(x-2q)`. After dividing the moment of
order `k` by `q^k`, the two remaining unequal pairs have weights `18 exp(-8q)`
and `72 exp(-11q)`. The reflected tail is expressed in the same Gaussian
coordinates, so its entry bounds can be compared with the leading-pair reserve.
-/

noncomputable section
open Matrix RHTower
namespace GaloisForLFunctions.ThetaCuspSections.FifthRemainder
open FifthLeadingPair

/-- Common factor in the radial atom-pair formulas. -/
def sourceUnit (x : ℝ) : ℝ :=
  4*(thetaCuspSingleAtomReflectionScale 1 x)^2*
    Real.exp (x-2*thetaCuspSingleAtomReflectionScale 1 x)

/-- A normalized radial pair in Gaussian polynomial coordinates. -/
def pairGram (a b q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianGram (fun i j =>
    (thetaPairRadialEvenPolynomial (a*q^2) (i.val+j.val)).eval (b*q)/q^(i.val+j.val))

/-- The unequal pairs involving the third atom. -/
def omittedPairGram (q : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  (18*Real.exp (-8*q)) • pairGram 9 10 q+
    (72*Real.exp (-11*q)) • pairGram 36 13 q

/-- The signed reflected tail beyond the first three atoms, in the same coordinates. -/
def tailGram (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  gaussianGram (fun i j => (-1 : ℝ)^(i.val+j.val)*
    (thetaCuspNativeReflectionJet (2*(i.val+j.val)) x-
      thetaCuspThreeAtomReflectionJet (2*(i.val+j.val)) x)/
        (sourceUnit x*(thetaCuspSingleAtomReflectionScale 1 x)^(i.val+j.val)))

/-- All remaining signed terms after retaining the leading pairs and pure atoms. -/
def remainderGram (x : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  omittedPairGram (thetaCuspSingleAtomReflectionScale 1 x)+tailGram x

end GaloisForLFunctions.ThetaCuspSections.FifthRemainder
