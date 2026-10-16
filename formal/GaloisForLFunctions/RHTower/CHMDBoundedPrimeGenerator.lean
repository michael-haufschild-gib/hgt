import GaloisForLFunctions.RHTower.CHMDPrimeDomain
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# The full prime generator is a bounded operator on the actual mass space

Automatic arithmetic admission makes the closed prime graph isomorphic to mass
L2. Its inverse gives the literal bounded difference map. The complete positive
arithmetic generator is its adjoint square, with no cutoff or domain premise.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDDoobGraph
open CHMDClosedJump

abbrev PrimeGraph := graph massMeasure allPrimeMeasure left right
  nonsingular_allPrime_left nonsingular_allPrime_right

def primeSourceMap : PrimeGraph →L[ℝ] Lp ℝ 2 massMeasure :=
  (WithLp.fstL 2 ℝ _ _).comp PrimeGraph.subtypeL

theorem primeSourceMap_injective : Function.Injective primeSourceMap :=
  source_injective massMeasure allPrimeMeasure left right
    nonsingular_allPrime_left nonsingular_allPrime_right

theorem primeSourceMap_surjective : Function.Surjective primeSourceMap := by
  intro w
  refine ⟨ofFunction massMeasure allPrimeMeasure left right
    nonsingular_allPrime_left nonsingular_allPrime_right w (Lp.memLp w)
    (memLp_allPrime_difference (Lp.memLp w)), ?_⟩
  exact Lp.toLp_coeFn w (Lp.memLp w)

def primeSourceEquiv : PrimeGraph ≃L[ℝ] Lp ℝ 2 massMeasure :=
  ContinuousLinearEquiv.ofBijective primeSourceMap
    (LinearMap.ker_eq_bot.mpr primeSourceMap_injective)
    (LinearMap.range_eq_top.mpr primeSourceMap_surjective)

theorem primeSourceEquiv_apply (p : PrimeGraph) : primeSourceEquiv p = p.val.fst := rfl

theorem primeSourceEquiv_symm_source (w : Lp ℝ 2 massMeasure) :
    (primeSourceEquiv.symm w).val.fst = w := primeSourceEquiv.apply_symm_apply w

/-- Bounded literal difference on every mass-L2 vector. -/
def primeDifference : Lp ℝ 2 massMeasure →L[ℝ] Lp ℝ 2 allPrimeMeasure :=
  ((WithLp.sndL 2 ℝ _ _).comp PrimeGraph.subtypeL).comp
    primeSourceEquiv.symm.toContinuousLinearMap

theorem primeDifference_ae (w : Lp ℝ 2 massMeasure) :
    primeDifference w =ᵐ[allPrimeMeasure] difference w := by
  have h := (primeSourceEquiv.symm w).property
  change (primeSourceEquiv.symm w).val.snd =ᵐ[allPrimeMeasure]
    difference (primeSourceEquiv.symm w).val.fst at h
  rw [primeSourceEquiv_symm_source] at h
  exact h

theorem primeDifference_eq_toLp (w : Lp ℝ 2 massMeasure) :
    primeDifference w = (memLp_allPrime_difference (Lp.memLp w)).toLp (difference w) := by
  apply Lp.ext
  exact (primeDifference_ae w).trans
    (memLp_allPrime_difference (Lp.memLp w)).coeFn_toLp.symm

def primeGenerator : Lp ℝ 2 massMeasure →L[ℝ] Lp ℝ 2 massMeasure :=
  primeDifference.adjoint.comp primeDifference

theorem primeGenerator_isPositive : primeGenerator.IsPositive :=
  ContinuousLinearMap.isPositive_adjoint_comp_self primeDifference

theorem primeGenerator_isSelfAdjoint : IsSelfAdjoint primeGenerator :=
  primeGenerator_isPositive.isSelfAdjoint

theorem inner_primeGenerator (v w : Lp ℝ 2 massMeasure) :
    ⟪primeGenerator v, w⟫_ℝ = ⟪primeDifference v, primeDifference w⟫_ℝ :=
  primeDifference.adjoint_inner_left w (primeDifference v)

theorem inner_primeGenerator_self (w : Lp ℝ 2 massMeasure) :
    ⟪primeGenerator w, w⟫_ℝ = ‖primeDifference w‖ ^ 2 := by
  rw [inner_primeGenerator, real_inner_self_eq_norm_sq]

theorem inner_primeGenerator_eq_integral (v w : Lp ℝ 2 massMeasure) :
    ⟪primeGenerator v, w⟫_ℝ =
      ∫ e, difference v e * difference w e ∂allPrimeMeasure := by
  rw [inner_primeGenerator, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [primeDifference_ae v, primeDifference_ae w] with e hv hw
  simp only [hv, hw, RCLike.inner_apply, conj_trivial]
  ring

theorem primeGenerator_eq_zero_iff (w : Lp ℝ 2 massMeasure) :
    primeGenerator w = 0 ↔ primeDifference w = 0 := by
  constructor
  · intro h
    have hn := inner_primeGenerator_self w
    rw [h, inner_zero_left] at hn
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (primeDifference w)])
  · intro h
    change primeDifference.adjoint (primeDifference w) = 0
    rw [h, map_zero]

end RHTower.CHMDDoobGraph
