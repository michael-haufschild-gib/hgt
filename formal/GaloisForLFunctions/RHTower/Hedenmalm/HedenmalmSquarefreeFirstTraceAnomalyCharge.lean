import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnSquarefreeFisherConormalResidue
import GaloisForLFunctions.RHTower.SquarefreeCarlemanLogExpansion
import GaloisForLFunctions.RHTower.XiReflectionSelfIntersectionCharge

/-!
# Squarefree first-trace anomaly charge

The squarefree Euler operator is uniformly invertible and its Hilbert--Carleman determinant is
holomorphic and nowhere zero on the source half-plane.  Hence that determinant cannot carry the
Xi divisor found in the squarefree boundary overlap.  This module removes the Carleman transport
and proves that the remaining first-trace anomaly carries the complete divisor order, its Fisher
conormal still has residue twice that order, and its finite-window squared charge is exactly the
canonical reflection self-intersection charge.

On the Euler-product half-plane the anomaly is literally the exponential of a prime-zeta
difference.  Thus every discrete reflection incidence is localized in the failure of this
first-trace logarithm to continue zero-freely; no higher regularized determinant order contributes.
-/

open Complex Filter Set Topology
open scoped BigOperators

namespace RHTower

noncomputable section

set_option maxHeartbeats 200000

/-- Carleman-determinant transport along one affine squarefree source line. -/
def squarefreeCarlemanTransport (sigma epsilon u : ℂ) : ℂ :=
  squarefreeCarlemanDet (sigma + u * epsilon) / squarefreeCarlemanDet sigma

/-- The divisor-bearing first-trace anomaly left after removing the nonvanishing Carleman
transport from the squarefree boundary overlap. -/
def squarefreeFirstTraceAnomaly (sigma epsilon u : ℂ) : ℂ :=
  GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon u /
    squarefreeCarlemanTransport sigma epsilon u

theorem squarefreeCarlemanTransport_ne_zero (sigma epsilon u : ℂ) :
    squarefreeCarlemanTransport sigma epsilon u ≠ 0 := by
  exact div_ne_zero (squarefreeCarlemanDet_ne_zero _)
    (squarefreeCarlemanDet_ne_zero _)

/-- Carleman transport is analytic at every affine point still in the strict source half-plane. -/
theorem analyticAt_squarefreeCarlemanTransport
    {sigma epsilon u : ℂ} (hshift : 1 / 2 < (sigma + u * epsilon).re) :
    AnalyticAt ℂ (squarefreeCarlemanTransport sigma epsilon) u := by
  have hopen : IsOpen {z : ℂ | 1 / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have houter : AnalyticAt ℂ squarefreeCarlemanDet (sigma + u * epsilon) :=
    differentiableOn_squarefreeCarlemanDet.analyticAt
      (hopen.mem_nhds hshift)
  have hinner : AnalyticAt ℂ (fun v : ℂ => sigma + v * epsilon) u := by
    fun_prop
  have hcomp : AnalyticAt ℂ
      (fun v : ℂ => squarefreeCarlemanDet (sigma + v * epsilon)) u := by
    exact AnalyticAt.comp (x := u) (f := fun v : ℂ => sigma + v * epsilon)
      (g := squarefreeCarlemanDet) houter hinner
  exact hcomp.div_const

/-- Removing Carleman transport changes no local analytic order. -/
theorem analyticOrderAt_squarefreeFirstTraceAnomaly_eq_overlap
    {sigma epsilon u : ℂ}
    (hshift : 1 / 2 < (sigma + u * epsilon).re)
    (hshift1 : sigma + u * epsilon ≠ 1) :
    analyticOrderAt (squarefreeFirstTraceAnomaly sigma epsilon) u =
      analyticOrderAt
        (GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon) u := by
  have hB := analyticAt_squarefreeBoundaryOverlap_of_half_lt_re hshift hshift1
  have hU := analyticAt_squarefreeCarlemanTransport hshift
  have hUne := squarefreeCarlemanTransport_ne_zero sigma epsilon u
  have hUinv : AnalyticAt ℂ (squarefreeCarlemanTransport sigma epsilon)⁻¹ u :=
    hU.inv hUne
  have hUinvOrder :
      analyticOrderAt (squarefreeCarlemanTransport sigma epsilon)⁻¹ u = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (inv_ne_zero hUne))
  have hfun : squarefreeFirstTraceAnomaly sigma epsilon =
      GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon *
        (squarefreeCarlemanTransport sigma epsilon)⁻¹ := by
    funext v
    exact div_eq_mul_inv _ _
  rw [hfun, analyticOrderAt_mul hB hUinv, hUinvOrder, add_zero]

/-- Throughout the strict-right critical strip, the first-trace anomaly carries the complete Xi
divisor order. -/
theorem analyticOrderAt_squarefreeFirstTraceAnomaly_eq_xi_of_strictRightStrip
    {sigma epsilon u rho : ℂ}
    (hsigma : 1 < sigma.re) (hepsilon : epsilon ≠ 0)
    (hcoord : sigma + u * epsilon = rho)
    (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1) :
    analyticOrderAt (squarefreeFirstTraceAnomaly sigma epsilon) u =
      analyticOrderAt xi rho := by
  have hrho1 : rho ≠ 1 := by
    intro h
    rw [h] at hone
    norm_num at hone
  rw [analyticOrderAt_squarefreeFirstTraceAnomaly_eq_overlap
      (by simpa [hcoord] using hhalf) (by simpa [hcoord] using hrho1),
    analyticOrderAt_squarefreeBoundaryOverlap_eq_xi_of_strictRightStrip
      hsigma hepsilon hcoord hhalf hone]

/-- The natural pointed Fisher numerator of the first-trace anomaly.  Its base connection is the
literal first-prime-trace current `-P'(sigma)` rather than the removed Carleman current. -/
def squarefreeFirstTraceAnomalyFisherScore
    (sigma epsilon u : ℂ) : ℂ :=
  pointedFisherNumerator (squarefreeFirstTraceAnomaly sigma epsilon)
    (-epsilon * deriv coronaPrimeZeta sigma) u

/-- The first-trace anomaly Fisher quotient retains residue twice the complete Xi multiplicity.
The removed Carleman determinant contributes no part of this residue. -/
theorem tendsto_squarefreeFirstTraceAnomalyFisherQuotient_residue
    {sigma epsilon u rho : ℂ}
    (hsigma : 1 < sigma.re) (hepsilon : epsilon ≠ 0)
    (hcoord : sigma + u * epsilon = rho)
    (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1)
    (hzero : xi rho = 0) :
    ∃ k : ℕ, analyticOrderAt xi rho = (k + 1 : ℕ) ∧
      Tendsto
        (fun v => (v - u) *
          (squarefreeFirstTraceAnomalyFisherScore sigma epsilon v /
            squarefreeFirstTraceAnomaly sigma epsilon v))
        (𝓝[≠] u) (𝓝 (2 * ((k + 1 : ℕ) : ℂ))) := by
  obtain ⟨k, hk, _⟩ :=
    tendsto_squarefreeFisherScore_div_overlap_residue_at_strictRightXiZero
      hsigma hepsilon hcoord hhalf hone hzero
  have hrho1 : rho ≠ 1 := by
    intro h
    rw [h] at hone
    norm_num at hone
  have hA : AnalyticAt ℂ (squarefreeFirstTraceAnomaly sigma epsilon) u := by
    exact (analyticAt_squarefreeBoundaryOverlap_of_half_lt_re
      (by simpa [hcoord] using hhalf) (by simpa [hcoord] using hrho1)).div
        (analyticAt_squarefreeCarlemanTransport (by simpa [hcoord] using hhalf))
        (squarefreeCarlemanTransport_ne_zero sigma epsilon u)
  have horder :
      analyticOrderAt (squarefreeFirstTraceAnomaly sigma epsilon) u =
        ((k + 1 : ℕ) : ℕ∞) := by
    rw [analyticOrderAt_squarefreeFirstTraceAnomaly_eq_xi_of_strictRightStrip
      hsigma hepsilon hcoord hhalf hone, hk]
  refine ⟨k, hk, ?_⟩
  simpa only [squarefreeFirstTraceAnomalyFisherScore] using
    (tendsto_pointedFisherQuotient_residue
      (f := squarefreeFirstTraceAnomaly sigma epsilon)
      (c := -epsilon * deriv coronaPrimeZeta sigma) hA horder)

/-- The regular Carleman connection has zero punctured residue at every point in its domain. -/
theorem tendsto_squarefreeCarlemanTransport_logDeriv_residue_zero
    {sigma epsilon u : ℂ} (hshift : 1 / 2 < (sigma + u * epsilon).re) :
    Tendsto
      (fun v => (v - u) * logDeriv (squarefreeCarlemanTransport sigma epsilon) v)
      (𝓝[≠] u) (𝓝 0) := by
  have hU := analyticAt_squarefreeCarlemanTransport hshift
  have hUne := squarefreeCarlemanTransport_ne_zero sigma epsilon u
  have hlog : AnalyticAt ℂ (logDeriv (squarefreeCarlemanTransport sigma epsilon)) u := by
    exact hU.deriv.div hU hUne
  have hsubFull : Tendsto (fun v : ℂ => v - u) (𝓝 u) (𝓝 0) := by
    convert (continuousAt_id.sub_const u) using 1 <;> simp
  have hsub : Tendsto (fun v : ℂ => v - u) (𝓝[≠] u) (𝓝 0) :=
    hsubFull.mono_left nhdsWithin_le_nhds
  have hlogT : Tendsto (logDeriv (squarefreeCarlemanTransport sigma epsilon))
      (𝓝[≠] u)
      (𝓝 (logDeriv (squarefreeCarlemanTransport sigma epsilon) u)) :=
    hlog.continuousAt.mono_left nhdsWithin_le_nhds
  simpa using hsub.mul hlogT

/-- In the Euler chamber, first-trace anomaly is exactly the exponential of prime-zeta transport.
This identifies it with the omitted trace-one term coefficient-for-coefficient. -/
theorem squarefreeFirstTraceAnomaly_eq_exp_primeZeta_sub
    {sigma epsilon u : ℂ} (hsigma : 1 < sigma.re)
    (hshift : 1 < (sigma + u * epsilon).re) :
    squarefreeFirstTraceAnomaly sigma epsilon u =
      Complex.exp (coronaPrimeZeta (sigma + u * epsilon) - coronaPrimeZeta sigma) := by
  rw [squarefreeFirstTraceAnomaly, squarefreeCarlemanTransport,
    GaloisForLFunctions.squarefreeBoundaryOverlap,
    squarefreePartition_eq_carleman_mul_exp hsigma,
    squarefreePartition_eq_carleman_mul_exp hshift,
    Complex.exp_sub]
  field_simp [squarefreeCarlemanDet_ne_zero, Complex.exp_ne_zero]

/-- A first-trace anomaly vanishes exactly when the underlying squarefree overlap vanishes. -/
theorem squarefreeFirstTraceAnomaly_eq_zero_iff
    (sigma epsilon u : ℂ) :
    squarefreeFirstTraceAnomaly sigma epsilon u = 0 ↔
      GaloisForLFunctions.squarefreeBoundaryOverlap sigma epsilon u = 0 := by
  rw [squarefreeFirstTraceAnomaly]
  constructor
  · intro h
    exact (div_eq_zero_iff.mp h).resolve_right
      (squarefreeCarlemanTransport_ne_zero sigma epsilon u)
  · intro h
    exact div_eq_zero_iff.mpr (Or.inl h)

/-- Strict-right finite-window support defined by zeros of the first-trace anomaly itself. -/
def hedenmalmSquarefreeFirstTraceRightSourceZeros (T : ℝ) : Set ℂ :=
  {rho | 1 / 2 < rho.re ∧ rho.re < 1 ∧ 0 ≤ rho.im ∧ rho.im < T ∧
    squarefreeFirstTraceAnomaly 2 1 (rho - 2) = 0}

/-- The anomaly-defined support is exactly strict-right Xi support. -/
theorem hedenmalmSquarefreeFirstTraceRightSourceZeros_eq (T : ℝ) :
    hedenmalmSquarefreeFirstTraceRightSourceZeros T =
      {rho | rho ∈ stripZeros T ∧ 1 / 2 < rho.re} := by
  ext rho
  have hcoord : (2 : ℂ) + (rho - 2) * 1 = rho := by ring
  have hbase : GaloisForLFunctions.squarefreePartition (2 : ℂ) ≠ 0 :=
    GaloisForLFunctions.squarefreePartition_ne_zero (by norm_num)
  have hAnomaly : squarefreeFirstTraceAnomaly 2 1 (rho - 2) = 0 ↔
      GaloisForLFunctions.squarefreePartition rho = 0 := by
    rw [squarefreeFirstTraceAnomaly_eq_zero_iff,
      GaloisForLFunctions.squarefreeBoundaryOverlap, hcoord]
    constructor
    · intro h
      exact (div_eq_zero_iff.mp h).resolve_right hbase
    · intro h
      exact div_eq_zero_iff.mpr (Or.inl h)
  constructor
  · intro h
    change 1 / 2 < rho.re ∧ rho.re < 1 ∧ 0 ≤ rho.im ∧ rho.im < T ∧
      squarefreeFirstTraceAnomaly 2 1 (rho - 2) = 0 at h
    rcases h with ⟨hhalf, hone, him0, himT, hA⟩
    have hsq : GaloisForLFunctions.squarefreePartition rho = 0 := hAnomaly.mp hA
    have hxi :=
      (squarefreePartition_eq_zero_iff_xi_eq_zero_of_strictRightStrip hhalf hone).mp hsq
    exact ⟨⟨⟨by linarith, hone, him0, himT⟩, hxi⟩, hhalf⟩
  · intro h
    rcases h with ⟨hstrip, hhalf⟩
    change 1 / 2 < rho.re ∧ rho.re < 1 ∧ 0 ≤ rho.im ∧ rho.im < T ∧
      squarefreeFirstTraceAnomaly 2 1 (rho - 2) = 0
    exact ⟨hhalf, hstrip.1.2.1, hstrip.1.2.2.1, hstrip.1.2.2.2,
      hAnomaly.mpr
        ((squarefreePartition_eq_zero_iff_xi_eq_zero_of_strictRightStrip
          hhalf hstrip.1.2.1).mpr hstrip.2)⟩

theorem hedenmalmSquarefreeFirstTraceRightSourceZeros_finite (T : ℝ) :
    (hedenmalmSquarefreeFirstTraceRightSourceZeros T).Finite := by
  rw [hedenmalmSquarefreeFirstTraceRightSourceZeros_eq]
  exact (stripZeros_finite T).subset (fun _ h => h.1)

/-- Multiplicity read solely from the first-trace anomaly at the fixed affine source chart. -/
def hedenmalmSquarefreeFirstTraceAnomalyMultiplicity (rho : ℂ) : ℕ :=
  (analyticOrderAt (squarefreeFirstTraceAnomaly 2 1) (rho - 2)).toNat

theorem hedenmalmSquarefreeFirstTraceAnomalyMultiplicity_eq_xi
    {rho : ℂ} (hhalf : 1 / 2 < rho.re) (hone : rho.re < 1) :
    hedenmalmSquarefreeFirstTraceAnomalyMultiplicity rho =
      (analyticOrderAt xi rho).toNat := by
  unfold hedenmalmSquarefreeFirstTraceAnomalyMultiplicity
  congr 1
  exact analyticOrderAt_squarefreeFirstTraceAnomaly_eq_xi_of_strictRightStrip
    (sigma := 2) (epsilon := 1) (u := rho - 2) (rho := rho)
    (by norm_num) (by norm_num) (by ring) hhalf hone

/-- Twice squared anomaly multiplicity over the anomaly-defined source support. -/
def hedenmalmSquarefreeFirstTraceAnomalyReflectionCharge (T : ℝ) : ℕ :=
  2 * ∑ rho ∈ (hedenmalmSquarefreeFirstTraceRightSourceZeros_finite T).toFinset,
    (hedenmalmSquarefreeFirstTraceAnomalyMultiplicity rho) ^ (2 : ℕ)

/-- The first-trace anomaly charge is coefficient-exact canonical reflection self-intersection. -/
theorem hedenmalmSquarefreeFirstTraceAnomalyReflectionCharge_eq (T : ℝ) :
    hedenmalmSquarefreeFirstTraceAnomalyReflectionCharge T =
      xiReflectionSelfIntersectionCharge T := by
  have hsupport :
      (hedenmalmSquarefreeFirstTraceRightSourceZeros_finite T).toFinset =
        (stripZeros_finite T).toFinset.filter (fun rho => 1 / 2 < rho.re) := by
    ext rho
    rw [Set.Finite.mem_toFinset, Finset.mem_filter, Set.Finite.mem_toFinset,
      hedenmalmSquarefreeFirstTraceRightSourceZeros_eq]
    rfl
  rw [hedenmalmSquarefreeFirstTraceAnomalyReflectionCharge, hsupport,
    xiReflectionSelfIntersectionCharge, xiStripWindowRightSquareOrder]
  congr 1
  apply Finset.sum_congr rfl
  intro rho hrho
  have hdata := Finset.mem_filter.mp hrho
  have hstrip : rho ∈ stripZeros T := by
    rw [Set.Finite.mem_toFinset] at hdata
    exact hdata.1
  rw [hedenmalmSquarefreeFirstTraceAnomalyMultiplicity_eq_xi
    hdata.2 hstrip.1.2.1]

end

end RHTower
