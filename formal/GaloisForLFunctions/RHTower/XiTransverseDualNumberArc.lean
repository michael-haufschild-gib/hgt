import GaloisForLFunctions.HTGeometry.SquareZeroDualNumberEmbedding
import GaloisForLFunctions.HTGeometry.PolarizedExactnessHorizonRelativeConnesPhaseLaw
import GaloisForLFunctions.RHTower.XiInternalTransverseCompletionSyndrome

/-!
# Transverse dual-number arcs on the Xi divisor

The square-zero transverse completion defect has a stronger algebraic meaning:
it is the tangent vector of a canonical dual-number arc in the Route-R
summable Hadamard corona.  The arc is faithful exactly off the critical line.

This is deliberately a relative statement.  Every Xi zero retains a separate
internal EWQ nilpotent channel, so formal unramifiedness of the entire divisor
object would be too strong.  Only the canonical transverse image algebra is
required to have no infinitesimal direction.
-/

open Complex

namespace RHTower

noncomputable section

/-- Canonical transverse infinitesimal arc attached to a Xi-divisor point. -/
def xiTransverseDualNumberArc
    (rho : XiDivisorSupport) :
    DualNumber ℂ →ₐ[ℂ] RouteRSummableHadamardCorona :=
  SquareZeroDualNumber.dualNumberMap
    (xiTransverseCompletionDefect rho)
    (routeRPrimeGammaCriticalWallSummableHadamardClass_sq_zero _)

@[simp]
theorem xiTransverseDualNumberArc_apply
    (rho : XiDivisorSupport) (x : DualNumber ℂ) :
    xiTransverseDualNumberArc rho x =
      algebraMap ℂ RouteRSummableHadamardCorona x.fst +
        x.snd • xiTransverseCompletionDefect rho := by
  exact SquareZeroDualNumber.dualNumberMap_apply _ _ _

/-- The transverse completion vector is nonzero exactly off the critical line. -/
theorem xiTransverseCompletionDefect_ne_zero_iff_re_ne_half
    (rho : XiDivisorSupport) :
    xiTransverseCompletionDefect rho ≠ 0 ↔ (rho : ℂ).re ≠ 1 / 2 := by
  rw [xiTransverseCompletionDefect,
    routeRPrimeGammaCriticalWallSummableHadamardClass_ne_zero_iff]
  exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).not

/-- The transverse dual-number arc is faithful exactly off the critical line. -/
theorem xiTransverseDualNumberArc_injective_iff_re_ne_half
    (rho : XiDivisorSupport) :
    Function.Injective (xiTransverseDualNumberArc rho) ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  rw [xiTransverseDualNumberArc,
    SquareZeroDualNumber.dualNumberMap_injective_iff,
    xiTransverseCompletionDefect_ne_zero_iff_re_ne_half]

/-- Image algebra of the canonical transverse arc.  At an off-line divisor point
this is an embedded copy of the dual numbers, not merely a nonzero class. -/
abbrev XiTransverseArcAlgebra (rho : XiDivisorSupport) :=
  (xiTransverseDualNumberArc rho).range

/-- Off-line placement identifies the transverse image algebra with dual numbers. -/
def xiTransverseArcAlgEquiv
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    DualNumber ℂ ≃ₐ[ℂ] XiTransverseArcAlgebra rho :=
  AlgEquiv.ofInjective (xiTransverseDualNumberArc rho)
    ((xiTransverseDualNumberArc_injective_iff_re_ne_half rho).2 hoff)

/-- Off-line transverse image is formally ramified: its cotangent direction
cannot vanish because it is algebraically the dual-number Euler direction. -/
theorem xiTransverseArcAlgebra_not_formallyUnramified_of_offLine
    (rho : XiDivisorSupport) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    ¬ Algebra.FormallyUnramified ℂ (XiTransverseArcAlgebra rho) :=
  SquareZeroDualNumber.not_formallyUnramified_of_equiv
    (xiTransverseArcAlgEquiv rho hoff)

/-- On the critical line the transverse image collapses to the scalar
subalgebra, hence is formally unramified even though the independent internal
Xi-divisor algebra remains nonreduced. -/
theorem xiTransverseArcAlgebra_formallyUnramified_of_re_eq_half
    (rho : XiDivisorSupport) (hline : (rho : ℂ).re = 1 / 2) :
    Algebra.FormallyUnramified ℂ (XiTransverseArcAlgebra rho) := by
  have hzero : xiTransverseCompletionDefect rho = 0 := by
    rw [xiTransverseCompletionDefect,
      routeRPrimeGammaCriticalWallSummableHadamardClass_eq_zero_iff,
      primeDepthBVWoldXiCenteredRate_eq_zero_iff]
    exact hline
  apply Algebra.FormallyUnramified.of_surjective
    (Algebra.ofId ℂ (XiTransverseArcAlgebra rho))
  intro y
  rcases y.2 with ⟨x, hx⟩
  refine ⟨x.fst, ?_⟩
  apply Subtype.ext
  change algebraMap ℂ RouteRSummableHadamardCorona x.fst = y.1
  calc
    algebraMap ℂ RouteRSummableHadamardCorona x.fst =
        xiTransverseDualNumberArc rho x := by
      rw [xiTransverseDualNumberArc_apply, hzero, smul_zero, add_zero]
    _ = y.1 := hx

/-- Direction-selective formal-unramified law.  It applies only to the
canonical transverse source image and therefore does not erase the internal
nilpotent channel present at every Xi zero. -/
theorem xiTransverseArcAlgebra_formallyUnramified_iff_re_eq_half
    (rho : XiDivisorSupport) :
    Algebra.FormallyUnramified ℂ (XiTransverseArcAlgebra rho) ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hunramified
    by_contra hoff
    exact
      (xiTransverseArcAlgebra_not_formallyUnramified_of_offLine rho hoff)
        hunramified
  · exact xiTransverseArcAlgebra_formallyUnramified_of_re_eq_half rho

/-- Reflection of the Xi divisor is the sign involution on the framed
transverse dual-number arc. -/
theorem xiTransverseDualNumberArc_lineConj_comp_sign
    (rho : XiDivisorSupport) :
    xiTransverseDualNumberArc (xiZeroLineConjEquiv rho) =
      (xiTransverseDualNumberArc rho).comp
        GaloisForLFunctions.HTGeometry.dualNumberSignHom := by
  apply AlgHom.ext
  intro x
  rw [xiTransverseDualNumberArc_apply, AlgHom.comp_apply,
    xiTransverseDualNumberArc_apply,
    xiTransverseCompletionDefect_lineConj]
  simp [GaloisForLFunctions.HTGeometry.dualNumberSignHom]

/-- Forgetting the infinitesimal frame erases the reflection anomaly: direct
and reflected arcs have the same image subalgebra at every Xi divisor. -/
theorem xiTransverseDualNumberArc_range_lineConj
    (rho : XiDivisorSupport) :
    (xiTransverseDualNumberArc (xiZeroLineConjEquiv rho)).range =
      (xiTransverseDualNumberArc rho).range := by
  rw [xiTransverseDualNumberArc_lineConj_comp_sign]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨GaloisForLFunctions.HTGeometry.dualNumberSignHom x, rfl⟩
  · rintro ⟨x, rfl⟩
    refine ⟨GaloisForLFunctions.HTGeometry.dualNumberSignHom x, ?_⟩
    simp [AlgHom.comp_apply,
      GaloisForLFunctions.HTGeometry.dualNumberSignHom_involutive]

/-- The oriented transverse frame descends through reflection exactly on the
critical line.  This is stronger than equality of the unframed image, which
holds unconditionally. -/
theorem xiTransverseDualNumberArc_lineConj_eq_iff_re_eq_half
    (rho : XiDivisorSupport) :
    xiTransverseDualNumberArc (xiZeroLineConjEquiv rho) =
        xiTransverseDualNumberArc rho ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hframe
    have heps := DFunLike.congr_fun hframe
      (TrivSqZeroExt.inr (1 : ℂ) : DualNumber ℂ)
    rw [xiTransverseDualNumberArc_apply,
      xiTransverseDualNumberArc_apply,
      xiTransverseCompletionDefect_lineConj] at heps
    simp only [TrivSqZeroExt.fst_inr, map_zero,
      TrivSqZeroExt.snd_inr, one_smul, zero_add] at heps
    have hzero : xiTransverseCompletionDefect rho = 0 := by
      have hadd : xiTransverseCompletionDefect rho +
          xiTransverseCompletionDefect rho = 0 := by
        calc
          xiTransverseCompletionDefect rho +
              xiTransverseCompletionDefect rho =
            xiTransverseCompletionDefect rho +
              (-xiTransverseCompletionDefect rho) := by rw [heps]
          _ = 0 := add_neg_cancel _
      have hsmul : (2 : ℂ) • xiTransverseCompletionDefect rho = 0 := by
        simpa [two_smul] using hadd
      exact (smul_eq_zero.mp hsmul).resolve_left (by norm_num)
    rw [xiTransverseCompletionDefect,
      routeRPrimeGammaCriticalWallSummableHadamardClass_eq_zero_iff,
      primeDepthBVWoldXiCenteredRate_eq_zero_iff] at hzero
    exact hzero
  · intro hline
    apply AlgHom.ext
    intro x
    rw [xiTransverseDualNumberArc_apply,
      xiTransverseDualNumberArc_apply,
      xiTransverseCompletionDefect_lineConj]
    have hzero : xiTransverseCompletionDefect rho = 0 := by
      rw [xiTransverseCompletionDefect,
        routeRPrimeGammaCriticalWallSummableHadamardClass_eq_zero_iff,
        primeDepthBVWoldXiCenteredRate_eq_zero_iff]
      exact hline
    rw [hzero, neg_zero]

/-- Exact pointwise admission law: critical-line placement is equivalent to
the absence of a faithful transverse infinitesimal arc. -/
theorem xi_no_faithful_transverse_arc_iff_re_eq_half
    (rho : XiDivisorSupport) :
    ¬ Function.Injective (xiTransverseDualNumberArc rho) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [xiTransverseDualNumberArc_injective_iff_re_ne_half, not_ne_iff]

/-- **Transverse-arc reformulation of RH.** RH says no Xi-divisor point admits
the canonical faithful infinitesimal arc normal to the reflection wall. -/
theorem noXiDivisorHasFaithfulTransverseArc_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport,
      ¬ Function.Injective (xiTransverseDualNumberArc rho)) ↔
      RiemannHypothesis := by
  constructor
  · intro hall
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro s hs
    let rho : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hs⟩
    exact (xi_no_faithful_transverse_arc_iff_re_eq_half rho).1 (hall rho)
  · intro hRH rho
    apply (xi_no_faithful_transverse_arc_iff_re_eq_half rho).2
    exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH)
      (rho : ℂ) (xi_eq_zero_of_mem_divisor_support rho)

/-- **Framed transverse reformulation of RH.**  Every unframed transverse
image is reflection-invariant, but RH is exactly global descent of its
oriented infinitesimal frame. -/
theorem everyXiTransverseDualNumberFrameDescends_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport,
      xiTransverseDualNumberArc (xiZeroLineConjEquiv rho) =
        xiTransverseDualNumberArc rho) ↔
      RiemannHypothesis := by
  constructor
  · intro hall
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro s hs
    let rho : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hs⟩
    exact (xiTransverseDualNumberArc_lineConj_eq_iff_re_eq_half rho).1
      (hall rho)
  · intro hRH rho
    apply (xiTransverseDualNumberArc_lineConj_eq_iff_re_eq_half rho).2
    exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH)
      (rho : ℂ) (xi_eq_zero_of_mem_divisor_support rho)

/-- **Directional formal-unramified reformulation of RH.**  RH does not demand
that Xi divisor geometry be reduced.  It demands only that every canonical
reflection-normal source image have trivial cotangent direction. -/
theorem everyXiTransverseArcAlgebraFormallyUnramified_iff_riemannHypothesis :
    (∀ rho : XiDivisorSupport,
      Algebra.FormallyUnramified ℂ (XiTransverseArcAlgebra rho)) ↔
      RiemannHypothesis := by
  constructor
  · intro hall
    rw [riemannHypothesis_iff_xi_zero_re_eq_half]
    intro s hs
    let rho : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hs⟩
    exact (xiTransverseArcAlgebra_formallyUnramified_iff_re_eq_half rho).1
      (hall rho)
  · intro hRH rho
    apply (xiTransverseArcAlgebra_formallyUnramified_iff_re_eq_half rho).2
    exact (riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH)
      (rho : ℂ) (xi_eq_zero_of_mem_divisor_support rho)

end

end RHTower
