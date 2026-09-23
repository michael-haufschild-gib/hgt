import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactSourceJets
import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactRemainder6

/-!
# Normalized odd determinant and its nonnegative compact remainder

Polynomial observables retain the complete normalized modular source. The
remainder is a sum of already checked nonnegative parts; its incidence with
the determinant is proved separately.
-/

open MvPolynomial
namespace HTGeometry
noncomputable section

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Exact reflected source derivative polynomial, at every order. -/
def oddCompactReflectedJetPolynomial (n : ℕ) : ModularThetaLyapunovPolynomial :=
  ∑ i ∈ Finset.range (n+1), C ((n.choose i : ℂ)*(-1 : ℂ)^(n-i)) *
    modularThetaLyapunovNormalizedSourceJet i * modularThetaLyapunovNormalizedSourceJet (n-i)

/-- Leading signed odd minor in the normalized polynomial source. -/
def oddCompactHeadPolynomial : ModularThetaLyapunovPolynomial :=
  (-oddCompactReflectedJetPolynomial 2)*(-oddCompactReflectedJetPolynomial 6) -
    oddCompactReflectedJetPolynomial 4^(2 : ℕ)

/-- Full signed odd rank-three determinant polynomial. -/
def oddCompactDetPolynomial : ModularThetaLyapunovPolynomial :=
  let a := -oddCompactReflectedJetPolynomial 2
  let b := oddCompactReflectedJetPolynomial 4
  let c := -oddCompactReflectedJetPolynomial 6
  let d := oddCompactReflectedJetPolynomial 8
  let e := -oddCompactReflectedJetPolynomial 10
  a*c*e-a*d^(2 : ℕ)-b^(2 : ℕ)*e+C 2*b*c*d-c^(3 : ℕ)

/-- Nonnegative drift coordinate is the negative of the original modular drift. -/
def oddCompactState (u a w : ℝ) : ModularThetaLyapunovState → ℂ
  | .S => (-u : ℝ)
  | .A => a
  | .W => w

/-- Mass-normalized real odd determinant. -/
def oddCompactDet (u a w : ℝ) : ℝ :=
  (MvPolynomial.eval (oddCompactState u a w) oddCompactDetPolynomial).re

/-- Mass-normalized real leading odd minor. -/
def oddCompactHead (u a w : ℝ) : ℝ :=
  (MvPolynomial.eval (oddCompactState u a w) oddCompactHeadPolynomial).re

/-- Mass-normalized zeroth source coordinate. -/
def oddCompactSourceZero (u a : ℝ) : ℝ := u^(2 : ℕ)/24+a/16-3/8

/-- Mass-normalized first source derivative. -/
def oddCompactSourceFirst (u a w : ℝ) : ℝ :=
  5*u^(3 : ℕ)/144+7*u*a/96-5*u/16-a*w/8

/-- Compact lower source correction on centers at most `137/2000`. -/
def oddCompactLowerSource (u a w : ℝ) : ℝ :=
  3*(oddCompactSourceZero u a)^(2 : ℕ) -
    (137/1000 : ℝ)*oddCompactSourceZero u a*(a*w/8+5*u/16)

/-- Complete nonnegative remainder discarded in the cubic reduction. -/
def oddCompactRemainder (u t w : ℝ) : ℝ :=
  (((((oddCompactRemainderPart0 u t w +
    (oddCompactRemainderPart1 u t w +
    oddCompactRemainderPart2 u t w)) +
    (oddCompactRemainderPart3 u t w +
    (oddCompactRemainderPart4 u t w +
    oddCompactRemainderPart5 u t w))) +
    ((oddCompactRemainderPart6 u t w +
    (oddCompactRemainderPart7 u t w +
    oddCompactRemainderPart8 u t w)) +
    (oddCompactRemainderPart9 u t w +
    (oddCompactRemainderPart10 u t w +
    oddCompactRemainderPart11 u t w)))) +
    (((oddCompactRemainderPart12 u t w +
    (oddCompactRemainderPart13 u t w +
    oddCompactRemainderPart14 u t w)) +
    (oddCompactRemainderPart15 u t w +
    (oddCompactRemainderPart16 u t w +
    oddCompactRemainderPart17 u t w))) +
    ((oddCompactRemainderPart18 u t w +
    (oddCompactRemainderPart19 u t w +
    oddCompactRemainderPart20 u t w)) +
    ((oddCompactRemainderPart21 u t w +
    oddCompactRemainderPart22 u t w) +
    (oddCompactRemainderPart23 u t w +
    oddCompactRemainderPart24 u t w))))) +
    ((((oddCompactRemainderPart25 u t w +
    (oddCompactRemainderPart26 u t w +
    oddCompactRemainderPart27 u t w)) +
    (oddCompactRemainderPart28 u t w +
    (oddCompactRemainderPart29 u t w +
    oddCompactRemainderPart30 u t w))) +
    ((oddCompactRemainderPart31 u t w +
    (oddCompactRemainderPart32 u t w +
    oddCompactRemainderPart33 u t w)) +
    ((oddCompactRemainderPart34 u t w +
    oddCompactRemainderPart35 u t w) +
    (oddCompactRemainderPart36 u t w +
    oddCompactRemainderPart37 u t w)))) +
    (((oddCompactRemainderPart38 u t w +
    (oddCompactRemainderPart39 u t w +
    oddCompactRemainderPart40 u t w)) +
    (oddCompactRemainderPart41 u t w +
    (oddCompactRemainderPart42 u t w +
    oddCompactRemainderPart43 u t w))) +
    ((oddCompactRemainderPart44 u t w +
    (oddCompactRemainderPart45 u t w +
    oddCompactRemainderPart46 u t w)) +
    ((oddCompactRemainderPart47 u t w +
    oddCompactRemainderPart48 u t w) +
    (oddCompactRemainderPart49 u t w +
    oddCompactRemainderPart50 u t w))))))

/-- Each discarded term has the required nonnegative orientation. -/
theorem oddCompactRemainder_nonneg {u t w : ℝ}
    (hu : 0 ≤ u) (ht : 0 ≤ t) (hw : 0 ≤ w) :
    0 ≤ oddCompactRemainder u t w := by
  unfold oddCompactRemainder
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (oddCompactRemainderPart0_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart1_nonneg hu ht hw)
    (oddCompactRemainderPart2_nonneg hu ht hw)))
    (add_nonneg (oddCompactRemainderPart3_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart4_nonneg hu ht hw)
    (oddCompactRemainderPart5_nonneg hu ht hw))))
    (add_nonneg (add_nonneg (oddCompactRemainderPart6_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart7_nonneg hu ht hw)
    (oddCompactRemainderPart8_nonneg hu ht hw)))
    (add_nonneg (oddCompactRemainderPart9_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart10_nonneg hu ht hw)
    (oddCompactRemainderPart11_nonneg hu ht hw)))))
    (add_nonneg (add_nonneg (add_nonneg (oddCompactRemainderPart12_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart13_nonneg hu ht hw)
    (oddCompactRemainderPart14_nonneg hu ht hw)))
    (add_nonneg (oddCompactRemainderPart15_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart16_nonneg hu ht hw)
    (oddCompactRemainderPart17_nonneg hu ht hw))))
    (add_nonneg (add_nonneg (oddCompactRemainderPart18_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart19_nonneg hu ht hw)
    (oddCompactRemainderPart20_nonneg hu ht hw)))
    (add_nonneg (add_nonneg (oddCompactRemainderPart21_nonneg hu ht hw)
    (oddCompactRemainderPart22_nonneg hu ht hw))
    (add_nonneg (oddCompactRemainderPart23_nonneg hu ht hw)
    (oddCompactRemainderPart24_nonneg hu ht hw))))))
    (add_nonneg (add_nonneg (add_nonneg (add_nonneg (oddCompactRemainderPart25_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart26_nonneg hu ht hw)
    (oddCompactRemainderPart27_nonneg hu ht hw)))
    (add_nonneg (oddCompactRemainderPart28_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart29_nonneg hu ht hw)
    (oddCompactRemainderPart30_nonneg hu ht hw))))
    (add_nonneg (add_nonneg (oddCompactRemainderPart31_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart32_nonneg hu ht hw)
    (oddCompactRemainderPart33_nonneg hu ht hw)))
    (add_nonneg (add_nonneg (oddCompactRemainderPart34_nonneg hu ht hw)
    (oddCompactRemainderPart35_nonneg hu ht hw))
    (add_nonneg (oddCompactRemainderPart36_nonneg hu ht hw)
    (oddCompactRemainderPart37_nonneg hu ht hw)))))
    (add_nonneg (add_nonneg (add_nonneg (oddCompactRemainderPart38_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart39_nonneg hu ht hw)
    (oddCompactRemainderPart40_nonneg hu ht hw)))
    (add_nonneg (oddCompactRemainderPart41_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart42_nonneg hu ht hw)
    (oddCompactRemainderPart43_nonneg hu ht hw))))
    (add_nonneg (add_nonneg (oddCompactRemainderPart44_nonneg hu ht hw)
    (add_nonneg (oddCompactRemainderPart45_nonneg hu ht hw)
    (oddCompactRemainderPart46_nonneg hu ht hw)))
    (add_nonneg (add_nonneg (oddCompactRemainderPart47_nonneg hu ht hw)
    (oddCompactRemainderPart48_nonneg hu ht hw))
    (add_nonneg (oddCompactRemainderPart49_nonneg hu ht hw)
    (oddCompactRemainderPart50_nonneg hu ht hw)))))))

end
end HTGeometry
