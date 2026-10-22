import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnSquarefreeFisherConormalResidue
import GaloisForLFunctions.RHTower.XiSourceNormalConeDivisorConservation

/-!
# Fisher conormal and exceptional Xi affine residue are one source current

C26 shows that squarefree Fisher quotient has residue 2m at a strict-right Xi zero of
multiplicity m. Source normal-cone law independently shows that centered exceptional
Xi current has residue -(rho - 1/2)m.

This module proves that these are not two divisor records. Multiplying Fisher conormal by forced
centered affine polarization -(rho - 1/2)/2 gives exactly exceptional-current residue.
Its real part is strictly negative at every strict-right zero.

Result isolates producer needed after Route N: a pre-divisor theorem excluding negative
horizontal affine source residue. Divisibility, curvature, bounded escape, and reciprocal
holonomy cannot supply that sign because they act after conserved conormal has formed.
-/

open Complex Filter Set Topology

namespace RHTower

noncomputable section

/-- **Fisher--normal-cone residue conservation.** Scaled squarefree Fisher conormal and
completed exceptional Xi affine current converge to same full position-times-multiplicity
residue at every strict-right Xi zero. -/
theorem squarefreeFisherConormal_scaled_limit_eq_xiAffineResidueLimit
    {sigma epsilon u rho : ℂ}
    (hsigma : 1 < sigma.re) (hepsilon : epsilon ≠ 0)
    (hcoord : sigma + u * epsilon = rho)
    (hρhalf : 1 / 2 < rho.re) (hρone : rho.re < 1)
    (hzero : xi rho = 0) :
    ∃ k : ℕ, analyticOrderAt xi rho = (k + 1 : ℕ) ∧
      Tendsto
        (fun v => (-(rho - 1 / 2) / 2) *
          ((v - u) *
            (GaloisForLFunctions.squarefreeFisherScore sigma epsilon v /
              GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon v)))
        (𝓝[≠] u)
        (𝓝 (-((rho - 1 / 2) * ((k + 1 : ℕ) : ℂ)))) ∧
      Tendsto
        (fun s => (s - rho) * xiExceptionalAffineDivisorCurrent s)
        (𝓝[≠] rho)
        (𝓝 (-((rho - 1 / 2) * ((k + 1 : ℕ) : ℂ)))) := by
  obtain ⟨k, hkXi, hkFisher⟩ :=
    tendsto_squarefreeFisherScore_div_overlap_residue_at_strictRightXiZero
      hsigma hepsilon hcoord hρhalf hρone hzero
  refine ⟨k, hkXi, ?_, ?_⟩
  · have hscaled := hkFisher.const_mul (-(rho - 1 / 2) / 2)
    convert hscaled using 1
    congr 1
    ring
  · have hxi : AnalyticAt ℂ xi rho :=
      xi_analyticOnNhd_univ rho (Set.mem_univ rho)
    have horder :
        meromorphicOrderAt xi rho = ((k + 1 : ℕ) : ℤ) := by
      rw [hxi.meromorphicOrderAt_eq, hkXi, ENat.map_coe]
    exact xiExceptionalAffineDivisorCurrent_residue horder

/-- Every strict-right Xi affine residue has strictly negative horizontal component. -/
theorem re_xiAffineResidueLimit_neg_of_strictRightXiZero
    {rho : ℂ} {k : ℕ} (hρhalf : 1 / 2 < rho.re) :
    (-((rho - 1 / 2) * ((k + 1 : ℕ) : ℂ))).re < 0 := by
  have hre :
      (-((rho - 1 / 2) * ((k + 1 : ℕ) : ℂ))).re =
        -(rho.re - 1 / 2) * ((k + 1 : ℕ) : ℝ) := by
    norm_num [mul_re]
    ring
  rw [hre]
  have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  exact mul_neg_of_neg_of_pos (by linarith) hkpos

/-- Closed certificate for position-sensitive source-incidence survivor. -/
structure RouteNSquarefreeFisherAffineResidueCertificate : Prop where
  residueConservation :
    ∀ {sigma epsilon u rho : ℂ},
      1 < sigma.re → epsilon ≠ 0 → sigma + u * epsilon = rho →
      1 / 2 < rho.re → rho.re < 1 → xi rho = 0 →
      ∃ k : ℕ, analyticOrderAt xi rho = (k + 1 : ℕ) ∧
        Tendsto
          (fun v => (-(rho - 1 / 2) / 2) *
            ((v - u) *
              (GaloisForLFunctions.squarefreeFisherScore sigma epsilon v /
                GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon v)))
          (𝓝[≠] u)
          (𝓝 (-((rho - 1 / 2) * ((k + 1 : ℕ) : ℂ)))) ∧
        Tendsto
          (fun s => (s - rho) * xiExceptionalAffineDivisorCurrent s)
          (𝓝[≠] rho)
          (𝓝 (-((rho - 1 / 2) * ((k + 1 : ℕ) : ℂ))))
  strictRightHorizontalSign :
    ∀ {rho : ℂ} {k : ℕ}, 1 / 2 < rho.re →
      (-((rho - 1 / 2) * ((k + 1 : ℕ) : ℂ))).re < 0

/-- **Unconditional Fisher--affine residue conservation law.** -/
theorem routeNSquarefreeFisherAffineResidue_law :
    RouteNSquarefreeFisherAffineResidueCertificate where
  residueConservation :=
    squarefreeFisherConormal_scaled_limit_eq_xiAffineResidueLimit
  strictRightHorizontalSign :=
    re_xiAffineResidueLimit_neg_of_strictRightXiZero

end

end RHTower
