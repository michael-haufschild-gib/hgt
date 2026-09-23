import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolWardHerglotzTangent
import GaloisForLFunctions.RHTower.RoutePCriticalCollisionSchurTrace

/-!
# Cubic Ward/Herglotz external mixed jet (W-H199)

P-G197 leaves one precise conjecture: the cubic conormal should be the mixed external-node Hardy
jet of its resolved Ward--Herglotz columns.  This module proves that identification.

The independent two-chamber Hardy cell `(p+u)⁻¹` has mixed derivative `2/(p+u)³`.  Its right and
left holomorphic doubling maps are `(3z+zSharp)/2` and `(z+3zSharp)/2`.  On the reflection graph
`zSharp=star z` they double only horizontal depth and retain signed ordinate.  The signed
four-cell compression of the mixed jet is exactly P-G173's full collision kernel, including
arbitrary ordinate gaps.  Equivalently, P-G173's doubled Schur cube is literally the mixed Hardy
jet, not an unrelated positive majorant.

This resolves the zero-side jet/dressing geometry and explains the earlier complex-structure
wall: horizontal doubling is holomorphic only before the two chambers are identified.  Remaining
producer is source-side: dominate this full bichamber Ward--Herglotz jet by the coefficient-
faithful primitive pole--Gamma trace without collapsing the two chamber variables.
-/

open Complex

namespace RHTower

noncomputable section

/-- Hardy resolvent with left and right chamber variables kept independent. -/
def xiWardCubicHardyBichamberCell (p u : ℂ) : ℂ := (p + u)⁻¹

/-- Mixed external derivative of the bichamber Hardy cell. -/
def xiWardCubicHardyMixedJet (p u : ℂ) : ℂ := 2 / (p + u) ^ (3 : ℕ)

/-- First external derivative of a resolved P-G197 Hardy column. -/
theorem hasDerivAt_xiWardCubicHardyBichamberCell_left
    {p u : ℂ} (h : p + u ≠ 0) :
    HasDerivAt (fun z : ℂ => xiWardCubicHardyBichamberCell z u)
      (-(p + u)⁻¹ ^ (2 : ℕ)) p := by
  have hi := ((hasDerivAt_id p).add_const u).inv h
  simpa [xiWardCubicHardyBichamberCell, div_eq_mul_inv, inv_pow] using! hi

/-- The second, independent-chamber derivative is the cubic Hardy jet. -/
theorem hasDerivAt_xiWardCubicHardyCell_leftDerivative_right
    {p u : ℂ} (h : p + u ≠ 0) :
    HasDerivAt (fun v : ℂ => -(p + v)⁻¹ ^ (2 : ℕ))
      (xiWardCubicHardyMixedJet p u) u := by
  have hi := ((hasDerivAt_const u p).add (hasDerivAt_id u)).inv h
  have hs := (hi.pow 2).neg
  have hs' : HasDerivAt (fun v : ℂ => -(p + v)⁻¹ ^ (2 : ℕ))
      (-(2 * (p + u)⁻¹ * (-1 / (p + u) ^ (2 : ℕ)))) u := by
    simpa using! hs
  apply hs'.congr_deriv
  rw [xiWardCubicHardyMixedJet]
  field_simp [h]

/-- Holomorphic right-chamber map which becomes horizontal-depth doubling on reflection. -/
def xiWardCubicBichamberRightDouble (z zSharp : ℂ) : ℂ :=
  (3 * z + zSharp) / 2

/-- Holomorphic left-chamber mate of horizontal-depth doubling. -/
def xiWardCubicBichamberLeftDouble (z zSharp : ℂ) : ℂ :=
  (z + 3 * zSharp) / 2

/-- P-G197 resolved column after the source-generated Hellinger first difference. -/
def xiWardCubicResolvedHellingerTransform
    (p z zSharp : ℂ) : ℂ :=
  xiWardCubicHardyBichamberCell p z -
    xiWardCubicHardyBichamberCell p
      (xiWardCubicBichamberRightDouble z zSharp)

/-- External derivative column of the resolved Hellinger transform. -/
def xiWardCubicResolvedHellingerExternalJet
    (p z zSharp : ℂ) : ℂ :=
  (p + z)⁻¹ ^ (2 : ℕ) -
    (p + xiWardCubicBichamberRightDouble z zSharp)⁻¹ ^ (2 : ℕ)

/-- The cubic conormal transform is exactly the external derivative of the resolved P-G197
column difference. -/
theorem hasDerivAt_xiWardCubicResolvedHellingerTransform
    {p z zSharp : ℂ} (hz : p + z ≠ 0)
    (hdouble : p + xiWardCubicBichamberRightDouble z zSharp ≠ 0) :
    HasDerivAt
      (fun w : ℂ => xiWardCubicResolvedHellingerTransform w z zSharp)
      (-xiWardCubicResolvedHellingerExternalJet p z zSharp) p := by
  have hfirst := hasDerivAt_xiWardCubicHardyBichamberCell_left hz
  have hsecond := hasDerivAt_xiWardCubicHardyBichamberCell_left hdouble
  have hsub := hfirst.sub hsecond
  have heq :
      -(p + z)⁻¹ ^ (2 : ℕ) -
          -(p + xiWardCubicBichamberRightDouble z zSharp)⁻¹ ^ (2 : ℕ) =
        -xiWardCubicResolvedHellingerExternalJet p z zSharp := by
    rw [xiWardCubicResolvedHellingerExternalJet]
    ring
  have hsub' := hsub.congr_deriv heq
  simpa [xiWardCubicResolvedHellingerTransform] using! hsub'

/-- Reflection-graph restriction doubles real depth and preserves ordinate. -/
theorem xiWardCubicBichamberRightDouble_reflection (z : ℂ) :
    xiWardCubicBichamberRightDouble z (star z) =
      ((2 * z.re : ℝ) : ℂ) + I * ((z.im : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [xiWardCubicBichamberRightDouble] <;> ring

/-- Left reflection-graph restriction is the Hermitian mate of horizontal doubling. -/
theorem xiWardCubicBichamberLeftDouble_reflection (z : ℂ) :
    xiWardCubicBichamberLeftDouble z (star z) =
      ((2 * z.re : ℝ) : ℂ) - I * ((z.im : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [xiWardCubicBichamberLeftDouble] <;> ring

/-- Four-cell first-difference compression of the bichamber cubic Hardy jet. -/
def xiWardCubicHardyMixedJetCodiagonal
    (z zSharp w wSharp : ℂ) : ℂ :=
  xiWardCubicHardyMixedJet z wSharp -
    xiWardCubicHardyMixedJet z
      (xiWardCubicBichamberLeftDouble w wSharp) -
    xiWardCubicHardyMixedJet
      (xiWardCubicBichamberRightDouble z zSharp) wSharp +
    xiWardCubicHardyMixedJet
      (xiWardCubicBichamberRightDouble z zSharp)
      (xiWardCubicBichamberLeftDouble w wSharp)

/-- **W-H199 jet incidence.** On reflected right-half-plane nodes the mixed external Hardy jet
is exactly the complete cubic collision kernel, with signed ordinate gap retained. -/
theorem xiWardCubicHardyMixedJetCodiagonal_eq_collision
    (a b kappa tau : ℝ) :
    xiWardCubicHardyMixedJetCodiagonal
      ((a : ℂ) - (kappa : ℂ) * I)
      ((a : ℂ) + (kappa : ℂ) * I)
      ((b : ℂ) - (tau : ℂ) * I)
      ((b : ℂ) + (tau : ℂ) * I) =
    routePCollisionCubicKernel 1 a b (tau - kappa) := by
  simp only [xiWardCubicHardyMixedJetCodiagonal,
    xiWardCubicHardyMixedJet, xiWardCubicBichamberRightDouble,
    xiWardCubicBichamberLeftDouble, routePCollisionCubicKernel,
    routePCollisionPairFrequency]
  push_cast
  congr 1 <;> ring

/-- P-G173's doubled cubic Gram is pointwise the mixed external Hardy jet, with its clock
normalization exposed. -/
theorem routePCollisionDoubledCubicGram_eq_xiWardCubicHardyMixedJet
    {N : ℕ} (R : ℝ) (a kappa : Fin N → ℝ)
    (x y : Fin N ⊕ Fin N) :
    routePCollisionDoubledCubicGram R a kappa x y =
      (R : ℂ) ^ (3 : ℕ) * xiWardCubicHardyMixedJet
        (routePCollisionDoubledNode R a kappa x)
        (star (routePCollisionDoubledNode R a kappa y)) := by
  rw [routePCollisionDoubledCubicGram_apply]
  simp [xiWardCubicHardyMixedJet]
  ring

end


end RHTower
