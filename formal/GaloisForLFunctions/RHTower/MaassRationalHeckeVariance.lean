import GaloisForLFunctions.RHTower.MaassRationalHeckeCorrespondenceL2
import GaloisForLFunctions.RHTower.MaassRationalHeckeAdjoint

/-!
# Exact variance of rational Hecke correspondences

Let A and B be the two common-cover pullbacks, T the adjoint of B, and d_1, d_2
their degrees. Exact pullback scaling and adjointness give

  norm(d_2 * A f - B (T (A f)))^2 + d_2 * norm(T (A f))^2
    = d_2^2 * d_1 * norm(f)^2.

The nonnegative residual recovers the degree bound, not a Ramanujan bound.
The final equivalence isolates the additional quantitative lower bound needed
on actual Maass sources. No such lower bound or classical-prime normalization
identification is proved here.
-/

open MeasureTheory Matrix
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower

/-- Degree of the conjugate-side common cover, as a real scalar. -/
noncomputable def rationalHeckeConjugateCoverDegree (N : ℕ) (g : GL (Fin 2) ℚ) : ℝ :=
  Nat.card ((rationalConjugateSL2Group N g) ⧸
    (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g))

theorem rationalHeckeConjugateCoverDegree_pos (N : ℕ) (g : GL (Fin 2) ℚ) :
    0 < rationalHeckeConjugateCoverDegree N g := by
  unfold rationalHeckeConjugateCoverDegree
  exact_mod_cast (Nat.card_pos (α := (rationalConjugateSL2Group N g) ⧸
    (rationalHeckeCommonCoverReal N g).subgroupOf (rationalConjugateSL2Group N g)))

/-- Unnormalized deviation from the conjugate-fibre average. -/
noncomputable def rationalHeckeFiberResidualLp (N : ℕ) (g : GL (Fin 2) ℚ)
    (u : Lp ℂ 2 (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))) :
    Lp ℂ 2 (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) :=
  (rationalHeckeConjugateCoverDegree N g : ℂ) • u -
    rationalHeckeConjugateCoverPullbackLp N g (rationalHeckeConjugateFiberTraceLp N g u)

/-- Exact trace energy plus residual energy, with no division by the cover degree. -/
theorem rationalHeckeFiberResidualLp_energy (N : ℕ) (g : GL (Fin 2) ℚ)
    (u : Lp ℂ 2 (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g))) :
    ‖rationalHeckeFiberResidualLp N g u‖ ^ 2 +
        rationalHeckeConjugateCoverDegree N g * ‖rationalHeckeConjugateFiberTraceLp N g u‖ ^ 2 =
      rationalHeckeConjugateCoverDegree N g ^ 2 * ‖u‖ ^ 2 := by
  let d := rationalHeckeConjugateCoverDegree N g
  let v := rationalHeckeConjugateFiberTraceLp N g u
  let w := rationalHeckeConjugateCoverPullbackLp N g v
  have hd : 0 ≤ d := (rationalHeckeConjugateCoverDegree_pos N g).le
  have hw : ‖w‖ ^ 2 = d * ‖v‖ ^ 2 := by
    rw [norm_rationalHeckeConjugateCoverPullbackLp, mul_pow, Real.sq_sqrt]
    · rfl
    · exact hd
  have huv : (inner ℂ u w).re = ‖v‖ ^ 2 := by
    rw [← rationalHeckeConjugateFiberTraceLp_inner_eq_pullback]
    exact inner_self_eq_norm_sq (𝕜 := ℂ) v
  have hscaled : (inner ℂ ((d : ℂ) • u) w).re = d * ‖v‖ ^ 2 := by
    simpa only [inner_smul_left, Complex.conj_ofReal, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
      congrArg (fun x : ℝ => d * x) huv
  change ‖(d : ℂ) • u - w‖ ^ 2 + d * ‖v‖ ^ 2 = d ^ 2 * ‖u‖ ^ 2
  rw [norm_sub_sq (𝕜 := ℂ), norm_smul, Complex.norm_of_nonneg hd]
  change (d * ‖u‖) ^ 2 - 2 * (inner ℂ ((d : ℂ) • u) w).re + ‖w‖ ^ 2 +
    d * ‖v‖ ^ 2 = d ^ 2 * ‖u‖ ^ 2
  rw [hscaled, hw]
  ring

/-- The exact finite-fibre energy decomposition on an actual Maass source. -/
theorem rationalHeckeFiberResidualLp_source_energy
    (N : ℕ) (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    ‖rationalHeckeFiberResidualLp N g (rationalHeckeIntegralCoverSourceLp N g f)‖ ^ 2 +
        rationalHeckeConjugateCoverDegree N g * ‖rationalHeckeConjugateFiberTraceSourceLp N g f‖ ^ 2 =
      rationalHeckeConjugateCoverDegree N g ^ 2 *
        (Nat.card ((CongruenceSubgroup.Gamma (N + 1)) ⧸
          (rationalHeckeIntegralIntersection N g).subgroupOf
            (CongruenceSubgroup.Gamma (N + 1))) : ℝ) * ‖MaassQuotientL2.sourceLp N f‖ ^ 2 := by
  letI : (rationalHeckeIntegralIntersection N g).IsFiniteRelIndex
      (CongruenceSubgroup.Gamma (N + 1)) :=
    rationalHeckeIntegralIntersection_isFiniteRelIndex_principal N g
  have hsource : ‖rationalHeckeIntegralCoverSourceLp N g f‖ ^ 2 =
      (Nat.card ((CongruenceSubgroup.Gamma (N + 1)) ⧸
        (rationalHeckeIntegralIntersection N g).subgroupOf
          (CongruenceSubgroup.Gamma (N + 1))) : ℝ) * ‖MaassQuotientL2.sourceLp N f‖ ^ 2 := by
    rw [← rationalHeckeIntegralCoverSourceLp_eq_finiteCoverPullback,
      norm_integralFiniteCoverPullbackLp, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have h := rationalHeckeFiberResidualLp_energy N g (rationalHeckeIntegralCoverSourceLp N g f)
  change _ + rationalHeckeConjugateCoverDegree N g *
      ‖rationalHeckeConjugateFiberTraceSourceLp N g f‖ ^ 2 = _ at h
  rw [hsource, ← mul_assoc] at h
  exact h

/-- A squared correspondence bound is exactly a quantitative residual lower bound.
This does not assert either bound. -/
theorem rationalHeckeFiberResidualLp_source_bound_iff
    (N : ℕ) (g : GL (Fin 2) ℚ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) (C : ℝ) :
    ‖rationalHeckeConjugateFiberTraceSourceLp N g f‖ ^ 2 ≤ C * ‖MaassQuotientL2.sourceLp N f‖ ^ 2 ↔
      (rationalHeckeConjugateCoverDegree N g ^ 2 *
          (Nat.card ((CongruenceSubgroup.Gamma (N + 1)) ⧸
            (rationalHeckeIntegralIntersection N g).subgroupOf
              (CongruenceSubgroup.Gamma (N + 1))) : ℝ) -
        rationalHeckeConjugateCoverDegree N g * C) * ‖MaassQuotientL2.sourceLp N f‖ ^ 2 ≤
      ‖rationalHeckeFiberResidualLp N g (rationalHeckeIntegralCoverSourceLp N g f)‖ ^ 2 := by
  have hdiff :
      ‖rationalHeckeFiberResidualLp N g (rationalHeckeIntegralCoverSourceLp N g f)‖ ^ 2 -
        (rationalHeckeConjugateCoverDegree N g ^ 2 *
            (Nat.card ((CongruenceSubgroup.Gamma (N + 1)) ⧸
              (rationalHeckeIntegralIntersection N g).subgroupOf
                (CongruenceSubgroup.Gamma (N + 1))) : ℝ) -
          rationalHeckeConjugateCoverDegree N g * C) * ‖MaassQuotientL2.sourceLp N f‖ ^ 2 =
        rationalHeckeConjugateCoverDegree N g *
          (C * ‖MaassQuotientL2.sourceLp N f‖ ^ 2 -
            ‖rationalHeckeConjugateFiberTraceSourceLp N g f‖ ^ 2) := by
    linear_combination rationalHeckeFiberResidualLp_source_energy N g f
  constructor
  · intro h
    apply sub_nonneg.mp
    rw [hdiff]
    exact mul_nonneg (rationalHeckeConjugateCoverDegree_pos N g).le (sub_nonneg.mpr h)
  · intro h
    apply sub_nonneg.mp
    apply (mul_nonneg_iff_of_pos_left (rationalHeckeConjugateCoverDegree_pos N g)).mp
    rw [← hdiff]
    exact sub_nonneg.mpr h

end GaloisForLFunctions.RHTower
