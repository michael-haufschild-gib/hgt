import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeightedHyperbolicGreenKernelDescendsToTheRationalTorus
import Mathlib.Analysis.Normed.Ring.Finite
import Mathlib.Topology.Piecewise

/-!
# The Robin diagonal of the rational-torus Green kernel

Summability of the adelic profiles forces every finite-vertex torus stabilizer
to be exactly the central pair `±1`. Removing those two terms leaves an orbit
tail continuous along each hyperbolic leaf, by a uniform summable majorant.
The local Newtonian finite part therefore passes to the full orbit sum.
Dividing by the central multiplicity gives its normalized quotient Robin mass.
-/

set_option autoImplicit false
noncomputable section
open Filter Matrix
open scoped Classical BigOperators Topology
namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic CoupledProductObstruction SurfaceOfSpecZ

/-- Finite component of the rational-torus homomorphism. -/
def rationalTorusFiniteHom : ℚˣ →* FiniteAdelicGroup where
  toFun := rationalTorusFinite
  map_one' := congrArg Prod.snd rationalTorusEmbedding.map_one
  map_mul' q r := congrArg Prod.snd (rationalTorusEmbedding.map_mul q r)

private def finiteTorusStabilizer (u : FiniteVertices) : Subgroup ℚˣ :=
  (MulAction.stabilizer FiniteAdelicGroup u).comap rationalTorusFiniteHom

private theorem finite_finiteTorusStabilizer (u : FiniteVertices) :
    (finiteTorusStabilizer u : Set ℚˣ).Finite := by
  convert finite_rationalTorus_equal_fibres u u using 1
  ext q
  change (rationalTorusFinite q • u = u) ↔ (u = rationalTorusFinite q • u)
  exact eq_comm

/-- A finite stabilizer makes its rational parameters torsion; their real absolute value is one. -/
theorem rationalTorus_finite_fix_imp_sign (u : FiniteVertices) (q : ℚˣ)
    (hq : rationalTorusFinite q • u = u) : q = 1 ∨ q = -1 := by
  letI : Finite (finiteTorusStabilizer u) := finite_finiteTorusStabilizer u
  have hqmem : q ∈ finiteTorusStabilizer u := hq
  have ho : IsOfFinOrder q := (finiteTorusStabilizer u).subtype.isOfFinOrder
    (isOfFinOrder_of_finite (⟨q, hqmem⟩ : finiteTorusStabilizer u))
  have hv : IsOfFinOrder (((q : ℚ) : ℝ)) :=
    (Rat.castHom ℝ).toMonoidHom.isOfFinOrder ((Units.coeHom ℚ).isOfFinOrder ho)
  have hn : |((q : ℚ) : ℝ)| = 1 := by simpa only [Real.norm_eq_abs] using hv.norm_eq_one
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with h | h
  · left
    apply Units.ext
    change (q : ℚ) = 1
    exact_mod_cast h
  · right
    apply Units.ext
    change (q : ℚ) = -1
    exact_mod_cast h

/-- The central sign is a scalar at every finite place. -/
theorem rationalTorusFinite_neg_one : rationalTorusFinite (-1) = 1 := by
  have hd : OppositeAdelic.weyl⁻¹ * OppositeAdelic.diagonal (-1) (by norm_num) *
      OppositeAdelic.weyl = OppositeAdelic.diagonal (-1) (by norm_num) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [OppositeAdelic.weyl, OppositeAdelic.diagonal, Matrix.mul_apply, Fin.sum_univ_two]
  have hg : SpecialLinearGroup.toGL (OppositeAdelic.diagonal (-1) (by norm_num)) =
      GeneralLinearGroup.scalar (Fin 2) (-1 : ℚˣ) := by
    apply GeneralLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [OppositeAdelic.diagonal, SpecialLinearGroup.toGL,
        GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  apply Subtype.ext
  funext p
  change (conjugateEmbedding (OppositeAdelic.diagonal (-1) _)).2 p = 1
  rw [conjugateEmbedding_finite, hd, localProj_toGL, hg]
  change ProjGenLinGroup.mk (GeneralLinearGroup.map (Rat.castHom ℚ_[p.1])
    (GeneralLinearGroup.scalar (Fin 2) (-1 : ℚˣ))) = 1
  rw [GeneralLinearGroup.map_scalar, ProjGenLinGroup.mk_scalar]

/-- The central sign also acts trivially on hyperbolic space. -/
theorem rationalTorusEmbedding_neg_one_smul (x : GlobalSpace) :
    rationalTorusEmbedding (-1) • x = x := by
  apply Prod.ext
  · change h3Act (conjugateEmbedding (OppositeAdelic.diagonal (-1) _)).1 x.1 = x.1
    rw [conjugateEmbedding_arch]
    apply H3.ext <;>
      simp [h3Act, h3Denom, OppositeAdelic.archMap, OppositeAdelic.diagonal]
  · change rationalTorusFinite (-1) • x.2 = x.2
    rw [rationalTorusFinite_neg_one, one_smul]

/-- Every finite-vertex stabilizer of the rational torus is exactly the central pair. -/
theorem rationalTorus_finite_fix_iff_sign (u : FiniteVertices) (q : ℚˣ) :
    rationalTorusFinite q • u = u ↔ q = 1 ∨ q = -1 := by
  constructor
  · exact rationalTorus_finite_fix_imp_sign u q
  · rintro (rfl | rfl)
    · change rationalTorusFiniteHom 1 • u = u
      rw [map_one, one_smul]
    · rw [rationalTorusFinite_neg_one, one_smul]

private theorem continuousAt_mixedGreen_ne_zero {r : ℝ} (hr : r ≠ 0) :
    ContinuousAt mixedGreen r := by
  have hs : 4 * Real.pi * Real.sinh r ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) (by rwa [ne_eq, Real.sinh_eq_zero])
  have hg : ContinuousAt (hyperbolicGreen 1) r := by
    have he : hyperbolicGreen 1 = (fun t : ℝ => 1 / (4 * Real.pi * Real.sinh t)) := by
      funext t
      simp only [hyperbolicGreen, sub_self, neg_zero, zero_mul, Real.exp_zero]
    rw [he]
    exact continuousAt_const.div (continuousAt_const.mul Real.continuous_sinh.continuousAt) hs
  exact hg.smul (hasDerivAt_hyperbolicEvolution r).continuousAt

/-- Off the finite diagonal, the Robin prescription is the continuous extension across zero distance. -/
theorem continuous_regularizedMixedEntry {u v : FiniteVertices} (huv : u ≠ v) :
    Continuous (fun r : ℝ => regularizedMixedEntry r u v) := by
  apply continuous_iff_continuousAt.mpr
  intro r
  by_cases hr : r = 0
  · subst r
    have he : (fun t => regularizedMixedEntry t u v) =
        Function.update (fun t => mixedGreenEntry t u v) 0 (mixedRobinEntry u v) := by
      funext t
      simp only [regularizedMixedEntry, Function.update_apply]
    rw [he]
    exact continuousAt_update_same.mpr (tendsto_mixedGreenEntry_collision huv)
  · let ev : ChargeOperator →L[ℝ] ℝ :=
      (lp.evalCLM ℝ (fun _ : FiniteVertices => ℝ) 2 v).comp
        (ContinuousLinearMap.apply ℝ ChargeSpace (lp.single 2 u (1 : ℝ)))
    have hc : ContinuousAt (fun t => mixedGreenEntry t u v) r :=
      ev.continuous.continuousAt.comp (continuousAt_mixedGreen_ne_zero hr)
    apply hc.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hr] with t ht
    exact if_neg ht

/-- The orbit term with the two central parameters removed. -/
def torusTailTerm (x y : GlobalSpace) (q : ℚˣ) : ℝ :=
  if q = 1 ∨ q = -1 then 0 else regularizedMixedKernel x (rationalTorusEmbedding q • y)

/-- The nonsingular orbit tail after removing central multiplicity. -/
def torusTailSum (x y : GlobalSpace) : ℝ := ∑' q : ℚˣ, torusTailTerm x y q

/-- The two central parameters contribute identical copies of the original kernel. -/
theorem torusGreenSum_split_center (x y : GlobalSpace) :
    torusGreenSum x y = 2 * regularizedMixedKernel x y + torusTailSum x y := by
  let c : Finset ℚˣ := {1, -1}
  let f : ℚˣ → ℝ := fun q => regularizedMixedKernel x (rationalTorusEmbedding q • y)
  have hc : Summable (fun q => if q ∈ c then f q else 0) :=
    summable_of_ne_finset_zero (s := c) fun q hq => if_neg hq
  have ht : Summable (torusTailTerm x y) :=
    ((summable_torusGreen x y).sub hc).congr fun q => by
      simp only [c, Finset.mem_insert, Finset.mem_singleton] 
      by_cases hq : q = 1 ∨ q = -1 <;> simp [torusTailTerm, hq, f]
  have hsign : (1 : ℚˣ) ≠ -1 := by
    intro h
    have h' := congrArg (fun q : ℚˣ => (q : ℚ)) h
    norm_num at h'
  have he : ∑' q, (if q ∈ c then f q else 0) = 2 * regularizedMixedKernel x y := by
    rw [tsum_eq_sum (s := c) fun q hq => if_neg hq]
    calc
      ∑ q ∈ c, (if q ∈ c then f q else 0) = ∑ q ∈ c, f q :=
        Finset.sum_congr rfl fun q hq => if_pos hq
      _ = _ := by
        simp [c, f, hsign, rationalTorusEmbedding_neg_one_smul, two_mul]
  rw [← he]
  change (∑' q, f q) = (∑' q, if q ∈ c then f q else 0) + ∑' q, torusTailTerm x y q
  rw [← hc.tsum_add ht]
  apply tsum_congr
  intro q
  change f q = (if q ∈ c then f q else 0) + torusTailTerm x y q
  simp only [c, Finset.mem_insert, Finset.mem_singleton]
  by_cases hq : q = 1 ∨ q = -1 <;> simp [torusTailTerm, hq, f]

private theorem torusTailTerm_same_fibre_bound (z w : H3) (u : FiniteVertices) (q : ℚˣ) :
    ‖torusTailTerm (z, u) (w, u) q‖ ≤
      (barrierRemainder / (4 * Real.pi)) * barrierProfile u (rationalTorusFinite q • u) := by
  by_cases hq : q = 1 ∨ q = -1
  · rw [torusTailTerm, if_pos hq, norm_zero]
    exact mul_nonneg (div_nonneg barrierRemainder_pos.le (by positivity))
      (barrierProfile_pos _ _).le
  · have huq : u ≠ rationalTorusFinite q • u :=
      fun h => hq ((rationalTorus_finite_fix_iff_sign u q).mp h.symm)
    have hb := regularizedMixedEntry_bound
      (h3Dist_nonneg z (rationalTorusEmbedding q • (w, u)).1) huq
    change ‖if q = 1 ∨ q = -1 then 0 else
      regularizedMixedEntry (h3Dist z (rationalTorusEmbedding q • (w, u)).1)
        u (rationalTorusFinite q • u)‖ ≤ _
    simpa only [if_neg hq, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

private theorem continuous_torusTailTerm_same_fibre (z : H3) (u : FiniteVertices) (q : ℚˣ) :
    Continuous (fun w : H3 => torusTailTerm (z, u) (w, u) q) := by
  by_cases hq : q = 1 ∨ q = -1
  · simp only [torusTailTerm, if_pos hq]
    exact continuous_const
  · have huq : u ≠ rationalTorusFinite q • u :=
      fun h => hq ((rationalTorus_finite_fix_iff_sign u q).mp h.symm)
    simp only [torusTailTerm, if_neg hq]
    exact (continuous_regularizedMixedEntry huq).comp
      ((continuous_h3Dist_right z).comp (continuous_h3Act (rationalTorusEmbedding q).1))

/-- A summable bound independent of the archimedean points makes the complete tail continuous. -/
theorem continuous_torusTailSum_same_fibre (z : H3) (u : FiniteVertices) :
    Continuous (fun w : H3 => torusTailSum (z, u) (w, u)) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  exact tendsto_tsum_of_dominated_convergence
    ((summable_barrierProfile_rationalTorus u u).mul_left (barrierRemainder / (4 * Real.pi)))
    (fun q => (continuous_torusTailTerm_same_fibre z u q).continuousAt)
    (Eventually.of_forall fun w q => torusTailTerm_same_fibre_bound z w u q)

private theorem tendsto_h3Dist_punctured (z : H3) :
    Tendsto (h3Dist z) (𝓝[≠] z) (𝓝[≠] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [h3Dist_self] using
      ((continuous_h3Dist_right z).tendsto z).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    change w ≠ z at hw
    change h3Dist z w ≠ 0
    exact fun h => hw ((h3Dist_eq_zero_iff z w).mp h).symm

/-- The normalized orbit sum has its prescribed diagonal as its actual Newtonian finite part. -/
theorem tendsto_torusGreenSum_robin (z : H3) (u : FiniteVertices) :
    Tendsto (fun w : H3 => torusGreenSum (z, u) (w, u) / 2 -
      1 / (4 * Real.pi * h3Dist z w))
      (𝓝[≠] z) (𝓝 (torusGreenSum (z, u) (z, u) / 2)) := by
  have hl : Tendsto (fun w : H3 => mixedGreenEntry (h3Dist z w) u u -
      1 / (4 * Real.pi * h3Dist z w)) (𝓝[≠] z) (𝓝 (mixedRobinEntry u u)) := by
    simpa [Function.comp_def, pointMass] using
      (tendsto_mixedGreenEntry_regularized u u).comp (tendsto_h3Dist_punctured z)
  have ht : Tendsto (fun w : H3 => torusTailSum (z, u) (w, u)) (𝓝[≠] z)
      (𝓝 (torusTailSum (z, u) (z, u))) :=
    ((continuous_torusTailSum_same_fibre z u).tendsto z).mono_left nhdsWithin_le_nhds
  have hd : torusGreenSum (z, u) (z, u) / 2 =
      mixedRobinEntry u u + torusTailSum (z, u) (z, u) / 2 := by
    rw [torusGreenSum_split_center]
    simp [regularizedMixedKernel, h3Dist_self, regularizedMixedEntry] <;> ring
  rw [hd]
  apply (hl.add (ht.div_const 2)).congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  change w ≠ z at hw
  have hdist : h3Dist z w ≠ 0 := fun h => hw ((h3Dist_eq_zero_iff z w).mp h).symm
  rw [torusGreenSum_split_center]
  simp only [regularizedMixedKernel, regularizedMixedEntry, if_neg hdist]
  ring

/-- The central multiplicity is removed before taking the quotient Robin mass. -/
def torusQuotientRobin (x : RationalTorusCarrier) : ℝ := torusQuotientGreen x x / 2

/-- The globally defined quotient diagonal is the Robin finite part along each hyperbolic leaf. -/
theorem tendsto_torusQuotientGreen_robin (z : H3) (u : FiniteVertices) :
    Tendsto (fun w : H3 =>
      torusQuotientGreen (Quotient.mk _ (z, u)) (Quotient.mk _ (w, u)) / 2 -
        1 / (4 * Real.pi * h3Dist z w))
      (𝓝[≠] z) (𝓝 (torusQuotientRobin (Quotient.mk _ (z, u)))) :=
  tendsto_torusGreenSum_robin z u

#print axioms rationalTorus_finite_fix_iff_sign
#print axioms continuous_regularizedMixedEntry
#print axioms torusGreenSum_split_center
#print axioms continuous_torusTailSum_same_fibre
#print axioms tendsto_torusQuotientGreen_robin
end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
