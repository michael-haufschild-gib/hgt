import GaloisForLFunctions.RHTower.Mollifier
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling

/-!
# Pole-regularized Ingham detector

Ingham's zero-density method uses the complex Möbius polynomial
`M_X(s) = ∑_{n≤X} μ(n)n⁻ˢ` and the detector
`1 - (ζ(s)M_X(s)-1)²`.  That detector has a double pole at `s = 1`, so it cannot be fed directly
to an analytic rectangle theorem containing the zeta pole.

Writing `G(s) = (s-1)ζ(s)` for the entire zeta residue unit, its pole-cleared form is

`H_X(s) = G(s)M_X(s)(2(s-1)-G(s)M_X(s))`.

This file proves that `H_X` is entire, agrees with the pole-cleared classical detector away from
`1`, and contains the full zero divisor of `G`.  Extra mollifier or detector zeros are harmless:
the analytic order of `G` is bounded by the analytic order of `H_X`.
-/

open Complex Nat ArithmeticFunction Finset Set Topology

namespace RHTower.Sieve

noncomputable section

/-- Complex Möbius mollifier used by Ingham's density detector. -/
noncomputable def inghamMollifier (X : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 X,
    ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-s)

/-- The finite complex Möbius mollifier is entire in its complex argument. -/
theorem analyticAt_inghamMollifier (X : ℕ) (s : ℂ) :
    AnalyticAt ℂ (inghamMollifier X) s := by
  change AnalyticAt ℂ
    (fun z => ∑ n ∈ Finset.Icc 1 X,
      ((ArithmeticFunction.moebius n : ℤ) : ℂ) * (n : ℂ) ^ (-z)) s
  exact Finset.analyticAt_fun_sum (Finset.Icc 1 X) fun n hn => by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hpow : Differentiable ℂ (fun z : ℂ => (n : ℂ) ^ (-z)) :=
      differentiable_id.neg.const_cpow (Or.inl hn0)
    exact analyticAt_const.mul (hpow.analyticAt s)

@[simp] theorem inghamMollifier_one (s : ℂ) :
    inghamMollifier 1 s = 1 := by
  simp [inghamMollifier]

/-- Entire pole-regularized form of Ingham's mollified zero detector. -/
noncomputable def inghamDetector (X : ℕ) (s : ℂ) : ℂ :=
  zetaResidueUnit s * inghamMollifier X s *
    (2 * (s - 1) - zetaResidueUnit s * inghamMollifier X s)

/-- The pole-regularized Ingham detector is analytic at every point. -/
theorem analyticAt_inghamDetector (X : ℕ) (s : ℂ) :
    AnalyticAt ℂ (inghamDetector X) s := by
  exact ((analyticAt_zetaResidueUnit s).mul (analyticAt_inghamMollifier X s)).mul
    ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).sub
      ((analyticAt_zetaResidueUnit s).mul (analyticAt_inghamMollifier X s)))

/-- The pole-regularized Ingham detector is entire. -/
theorem inghamDetector_analyticOnNhd_univ (X : ℕ) :
    AnalyticOnNhd ℂ (inghamDetector X) Set.univ :=
  fun s _ => analyticAt_inghamDetector X s

/-- The length-one detector is visibly nontrivial.  This also provides a closed sanity check on the
pole regularization at `s = 1`. -/
@[simp] theorem inghamDetector_one_one : inghamDetector 1 1 = -1 := by
  simp [inghamDetector, zetaResidueUnit_one]

/-- Away from the zeta pole, `inghamDetector` is exactly `(s-1)²` times Ingham's classical
meromorphic detector `1-(ζM_X-1)²`. -/
theorem inghamDetector_eq_poleCleared (X : ℕ) {s : ℂ} (hs : s ≠ 1) :
    inghamDetector X s =
      (s - 1) ^ 2 * (1 - (riemannZeta s * inghamMollifier X s - 1) ^ 2) := by
  have hG : zetaResidueUnit s = (s - 1) * riemannZeta s := by
    simp [zetaResidueUnit, Function.update_of_ne hs]
  rw [inghamDetector, hG]
  ring

/-- Every residue-unit zero is a zero of the pole-regularized Ingham detector. -/
theorem inghamDetector_eq_zero_of_zetaResidueUnit_eq_zero
    (X : ℕ) {rho : ℂ} (hzero : zetaResidueUnit rho = 0) :
    inghamDetector X rho = 0 := by
  simp [inghamDetector, hzero]

/-- Every Riemann-zeta zero is a zero of the pole-regularized Ingham detector. -/
theorem inghamDetector_eq_zero_of_riemannZeta_eq_zero
    (X : ℕ) {rho : ℂ} (hzero : riemannZeta rho = 0) :
    inghamDetector X rho = 0 := by
  have hrho : rho ≠ 1 := riemannZeta_zero_ne_one hzero
  exact inghamDetector_eq_zero_of_zetaResidueUnit_eq_zero X
    (by simp [zetaResidueUnit, Function.update_of_ne hrho, hzero])

/-- **Divisor inheritance.**  The complete analytic zero divisor of the zeta residue unit is a
subdivisor of the pole-regularized Ingham detector.  This `ℕ∞` statement remains valid even in the
degenerate case where the detector is locally zero. -/
theorem analyticOrderAt_zetaResidueUnit_le_inghamDetector
    (X : ℕ) (rho : ℂ) :
    analyticOrderAt zetaResidueUnit rho ≤ analyticOrderAt (inghamDetector X) rho := by
  have hrest : AnalyticAt ℂ
      (fun s => inghamMollifier X s *
        (2 * (s - 1) - zetaResidueUnit s * inghamMollifier X s)) rho :=
    (analyticAt_inghamMollifier X rho).mul
      ((analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).sub
        ((analyticAt_zetaResidueUnit rho).mul (analyticAt_inghamMollifier X rho)))
  have hfun : inghamDetector X = zetaResidueUnit *
      (fun s => inghamMollifier X s *
        (2 * (s - 1) - zetaResidueUnit s * inghamMollifier X s)) := by
    funext s
    simp [inghamDetector, Pi.mul_apply, mul_assoc]
  rw [hfun, analyticOrderAt_mul (analyticAt_zetaResidueUnit rho) hrest]
  exact le_add_right le_rfl

/-- A single nonzero detector value rules out infinite local order everywhere, by analytic
continuation on the connected complex plane. -/
theorem inghamDetector_order_ne_top_of_exists_ne_zero
    (X : ℕ) (rho : ℂ) (hne : ∃ z : ℂ, inghamDetector X z ≠ 0) :
    analyticOrderAt (inghamDetector X) rho ≠ ⊤ := by
  intro htop
  have hevent : inghamDetector X =ᶠ[nhds rho] 0 := analyticOrderAt_eq_top.mp htop
  have heq : Set.EqOn (inghamDetector X) 0 (Set.univ : Set ℂ) :=
    (inghamDetector_analyticOnNhd_univ X).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ rho) hevent
  obtain ⟨z, hz⟩ := hne
  exact hz (heq (Set.mem_univ z))

/-- The length-one detector has finite analytic order at every point. -/
theorem inghamDetector_one_order_ne_top (rho : ℂ) :
    analyticOrderAt (inghamDetector 1) rho ≠ ⊤ :=
  inghamDetector_order_ne_top_of_exists_ne_zero 1 rho ⟨1, by simp⟩

/-- Finite analytic multiplicity of every zeta-residue-unit zero is bounded by the corresponding
detector multiplicity as soon as one nonzero detector value is known.  A nonvanishing contour edge
will supply this witness in the rectangle-counting application. -/
theorem zetaResidueUnit_multiplicity_le_inghamDetector
    (X : ℕ) (rho : ℂ) (hne : ∃ z : ℂ, inghamDetector X z ≠ 0) :
    (analyticOrderAt zetaResidueUnit rho).toNat ≤
      (analyticOrderAt (inghamDetector X) rho).toNat :=
  ENat.toNat_le_toNat (analyticOrderAt_zetaResidueUnit_le_inghamDetector X rho)
    (inghamDetector_order_ne_top_of_exists_ne_zero X rho hne)

end


end RHTower.Sieve
