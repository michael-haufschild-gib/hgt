import GaloisForLFunctions.RHTower.MaassModelHilbertGenerators
import GaloisForLFunctions.RHTower.MaassModelHilbertAnalyticVectorBounds
import GaloisForLFunctions.HTGeometry.KrylovProjectedCompleteIncidenceLaw
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# All-time quotient-orbit derivatives for the Maass model

A finite Maass-model vector has a quotient `L²` derivative at time zero for the diagonal,
compact, and quarter-diagonal one-parameter subgroups.  This file supplies the missing
functional-analytic transport: a zero-time derivative of any quotient orbit propagates to every
time through the actual unitary representation.  Together with the factorial diagonal-generator
bound, it is the input for a Taylor argument showing that diagonal quotient orbits stay in the
closed completed-model range.
-/

open MeasureTheory Filter Topology
namespace GaloisForLFunctions.RHTower
open MaassModelQuotientL2

noncomputable section

/-- A zero-time derivative of a quotient unitary orbit propagates to every time along a
one-parameter subgroup.  The fixed unitary is restricted to a real continuous linear map because
the orbit parameter is real. -/
theorem integralSubgroupUnitary_hasDerivAt_all_times
    (Γ : Subgroup SL2Z) (p : ℝ → SL2R)
    (hp : ∀ t s, p (t + s) = p t * p s)
    (x x' : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ))
    (h0 : HasDerivAt (fun t => integralSubgroupUnitary Γ (p t) x) x' 0) (t : ℝ) :
    HasDerivAt (fun u => integralSubgroupUnitary Γ (p u) x)
      (integralSubgroupUnitary Γ (p t) x') t := by
  let L : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ) →L[ℝ]
      Lp ℂ 2 (integralSubgroupQuotientMeasure Γ) :=
    (integralSubgroupUnitary Γ (p t)).toLinearIsometry.toContinuousLinearMap.restrictScalars ℝ
  have hL : HasDerivAt (fun _ : ℝ => L) 0 0 := hasDerivAt_const 0 L
  have hlinear := hL.clm_apply h0
  have hzero : HasDerivAt (fun u => L (integralSubgroupUnitary Γ (p u) x))
      (L x') (t - t) := by
    simpa only [sub_self, zero_apply, zero_add] using hlinear
  have hshift := hzero.scomp (h := fun u : ℝ => u - t) t
    ((hasDerivAt_id t).sub_const t)
  have heq : (fun u => L (integralSubgroupUnitary Γ (p (u - t)) x)) =
      fun u => integralSubgroupUnitary Γ (p u) x := by
    funext u
    change integralSubgroupUnitary Γ (p t)
      (integralSubgroupUnitary Γ (p (u - t)) x) = _
    rw [← integralSubgroupUnitary_mul, ← hp]
    have hut : t + (u - t) = u := by linarith
    rw [hut]
  have hL_apply : L x' = integralSubgroupUnitary Γ (p t) x' := rfl
  simpa only [sub_self, zero_apply, zero_add, one_smul, Function.comp_def, heq, hL_apply]
    using hshift

/-- The quotient `L²` orbit of a finite complementary-model vector under the diagonal
one-parameter subgroup. -/
def modelToLpComplementaryDiagonalOrbit
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) :
    ℝ → Lp ℂ 2 (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1))) :=
  fun t => integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
    (realPositiveDiagonalBorel (-t) : SL2R)
    (modelToLp N lam f (ComplementaryKFinite.toModel lam v))

/-- Every unnormalized finite Maass-model image already belongs to the normalized finite model
image defining the completed isometry range. -/
theorem modelToLp_mem_range_modelIsometry
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) :
    modelToLp N lam f (ComplementaryKFinite.toModel lam v) ∈
      Set.range (modelIsometry N lam f) := by
  let c : ℂ := ‖modelToLp N lam f (Finsupp.single 0 1)‖
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (modelToLp_spherical_norm_pos N lam f).ne'
  refine ⟨c • v, ?_⟩
  change c⁻¹ • modelToLp N lam f (ComplementaryKFinite.toModel lam (c • v)) = _
  rw [map_smul, map_smul, ← mul_smul, inv_mul_cancel₀ hc, one_smul]

/-- The finite complementary-model diagonal quotient orbit is continuous. -/
theorem continuous_modelToLpComplementaryDiagonalOrbit
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) :
    Continuous (modelToLpComplementaryDiagonalOrbit N lam f v) := by
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  change Continuous (fun t : ℝ =>
    DomMulAct.mk (realPositiveDiagonalBorel (-t) : SL2R)⁻¹ •
      modelToLp N lam f (ComplementaryKFinite.toModel lam v))
  have hp : Continuous (fun t : ℝ => (realPositiveDiagonalBorel (-t) : SL2R)) := by
    fun_prop
  exact (DomMulAct.continuous_mk.comp hp.inv).smul continuous_const

/-- The actual quotient orbit of a finite complementary-model vector has the source-attached
diagonal derivative at every time. -/
theorem modelToLp_complementaryDiagonal_hasDerivAt_all_times
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (t : ℝ) :
    HasDerivAt (fun u => integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
      (realPositiveDiagonalBorel (-u) : SL2R)
      (modelToLp N lam f (ComplementaryKFinite.toModel lam v)))
      (integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
        (realPositiveDiagonalBorel (-t) : SL2R)
        (modelToLp N lam f (ComplementaryKFinite.toModel lam
          (complementaryDiagonalGenerator lam v)))) t := by
  apply integralSubgroupUnitary_hasDerivAt_all_times
    (CongruenceSubgroup.Gamma (N + 1))
    (fun u => (realPositiveDiagonalBorel (-u) : SL2R))
    (by
      intro a b
      simp only [neg_add, realPositiveDiagonalBorel_add, Subgroup.coe_mul])
  simpa only [complementaryDiagonal_toModel] using
    (modelToLp_diagonal_hasDerivAt N lam f (ComplementaryKFinite.toModel lam v))

/-- Every finite diagonal-generator iterate has the next iterate as its quotient-orbit derivative
at every time. -/
theorem modelToLp_complementaryDiagonalIterate_hasDerivAt_all_times
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (n : ℕ) (t : ℝ) :
    HasDerivAt (fun u => integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
      (realPositiveDiagonalBorel (-u) : SL2R)
      (modelToLp N lam f (ComplementaryKFinite.toModel lam
        (complementaryDiagonalIterate lam n v))))
      (integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
        (realPositiveDiagonalBorel (-t) : SL2R)
        (modelToLp N lam f (ComplementaryKFinite.toModel lam
          (complementaryDiagonalIterate lam (n + 1) v)))) t := by
  simpa only [complementaryDiagonalIterate, LinearMap.comp_apply] using
    (modelToLp_complementaryDiagonal_hasDerivAt_all_times N lam f
      (complementaryDiagonalIterate lam n v) t)

/-- The iterated real derivative of a quotient diagonal orbit is exactly the corresponding
finite complementary-model diagonal iterate. -/
theorem iteratedDeriv_modelToLp_complementaryDiagonal_orbit
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) :
    ∀ n : ℕ, iteratedDeriv n (fun u => integralSubgroupUnitary
      (CongruenceSubgroup.Gamma (N + 1)) (realPositiveDiagonalBorel (-u) : SL2R)
      (modelToLp N lam f (ComplementaryKFinite.toModel lam v))) =
      fun t => integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
        (realPositiveDiagonalBorel (-t) : SL2R)
        (modelToLp N lam f (ComplementaryKFinite.toModel lam
          (complementaryDiagonalIterate lam n v))) := by
  intro n
  induction n with
  | zero =>
      simp only [iteratedDeriv_zero, complementaryDiagonalIterate, LinearMap.id_apply]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact (modelToLp_complementaryDiagonalIterate_hasDerivAt_all_times N lam f v n t).deriv

/-- Every finite complementary-model diagonal quotient orbit is smooth to any prescribed finite
order. -/
theorem contDiff_modelToLpComplementaryDiagonalOrbit
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) :
    ∀ n : ℕ, ContDiff ℝ n (modelToLpComplementaryDiagonalOrbit N lam f v) := by
  intro n
  induction n generalizing v with
  | zero =>
      exact contDiff_zero.mpr (continuous_modelToLpComplementaryDiagonalOrbit N lam f v)
  | succ n ih =>
      suffices ContDiff ℝ ((n : WithTop ℕ∞) + 1)
          (modelToLpComplementaryDiagonalOrbit N lam f v) by
        simpa only [Nat.cast_add, Nat.cast_one] using this
      apply (contDiff_succ_iff_deriv).mpr
      refine ⟨?_, by simp, ?_⟩
      · intro t
        change DifferentiableAt ℝ (fun u => integralSubgroupUnitary
          (CongruenceSubgroup.Gamma (N + 1)) (realPositiveDiagonalBorel (-u) : SL2R)
          (modelToLp N lam f (ComplementaryKFinite.toModel lam v))) t
        exact (modelToLp_complementaryDiagonal_hasDerivAt_all_times N lam f v t).differentiableAt
      · have hderiv : deriv (modelToLpComplementaryDiagonalOrbit N lam f v) =
            modelToLpComplementaryDiagonalOrbit N lam f
              (complementaryDiagonalGenerator lam v) := by
          funext t
          change deriv (fun u => integralSubgroupUnitary
            (CongruenceSubgroup.Gamma (N + 1)) (realPositiveDiagonalBorel (-u) : SL2R)
            (modelToLp N lam f (ComplementaryKFinite.toModel lam v))) t =
              integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
                (realPositiveDiagonalBorel (-t) : SL2R)
                (modelToLp N lam f (ComplementaryKFinite.toModel lam
                  (complementaryDiagonalGenerator lam v)))
          exact (modelToLp_complementaryDiagonal_hasDerivAt_all_times N lam f v t).deriv
        rw [hderiv]
        exact ih (complementaryDiagonalGenerator lam v)

/-- The factorial complementary-model estimate controls every real derivative of the actual
quotient diagonal orbit. -/
theorem norm_iteratedDeriv_modelToLpComplementaryDiagonalOrbit_le_factorial
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (n : ℕ) (t : ℝ) :
    ‖iteratedDeriv n (modelToLpComplementaryDiagonalOrbit N lam f v) t‖ ≤
      (2 * r + 2) ^ n * n.factorial *
        ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ := by
  change ‖iteratedDeriv n (fun u => integralSubgroupUnitary
    (CongruenceSubgroup.Gamma (N + 1)) (realPositiveDiagonalBorel (-u) : SL2R)
    (modelToLp N lam f (ComplementaryKFinite.toModel lam v))) t‖ ≤ _
  rw [iteratedDeriv_modelToLp_complementaryDiagonal_orbit N lam f v n]
  calc
    ‖integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
        (realPositiveDiagonalBorel (-t) : SL2R)
        (modelToLp N lam f (ComplementaryKFinite.toModel lam
          (complementaryDiagonalIterate lam n v)))‖ =
        ‖modelToLp N lam f (ComplementaryKFinite.toModel lam
          (complementaryDiagonalIterate lam n v))‖ :=
      LinearIsometryEquiv.norm_map _ _
    _ = ‖modelToLp N lam f (Finsupp.single 0 1)‖ *
        ‖complementaryDiagonalIterate lam n v‖ :=
      modelToLp_norm N lam f (complementaryDiagonalIterate lam n v)
    _ ≤ ‖modelToLp N lam f (Finsupp.single 0 1)‖ *
        ((2 * r + 2) ^ n * n.factorial * ‖v‖) :=
      mul_le_mul_of_nonneg_left
        (complementaryDiagonalIterate_norm_le_factorial lam v r hr hsupp n) (norm_nonneg _)
    _ = (2 * r + 2) ^ n * n.factorial *
        ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ := by ring

/-- Banach-valued Taylor remainder bound for a source-attached quotient diagonal orbit. -/
theorem norm_sub_taylorWithinEval_modelToLpComplementaryDiagonalOrbit_le_factorial
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖modelToLpComplementaryDiagonalOrbit N lam f v t -
        taylorWithinEval (modelToLpComplementaryDiagonalOrbit N lam f v) K (Set.Icc 0 t) 0 t‖ ≤
      ((2 * r + 2) ^ (K + 1) * (K + 1).factorial *
        ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖) * t ^ (K + 1) /
          (K + 1).factorial := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  apply HTGeometry.norm_sub_taylorWithinEval_le_factorial ht.le
    (contDiff_modelToLpComplementaryDiagonalOrbit N lam f v (K + 1)).contDiffOn
  intro y hy
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
    ((contDiff_modelToLpComplementaryDiagonalOrbit N lam f v (K + 1)).contDiffAt) hy]
  exact norm_iteratedDeriv_modelToLpComplementaryDiagonalOrbit_le_factorial
    N lam f v r hr hsupp (K + 1) y

/-- At the initial endpoint of a nondegenerate Taylor interval, each within-derivative of the
quotient diagonal orbit is its finite complementary-model iterate. -/
theorem iteratedDerivWithin_modelToLpComplementaryDiagonalOrbit_zero
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    iteratedDerivWithin n (modelToLpComplementaryDiagonalOrbit N lam f v) (Set.Icc 0 t) 0 =
      modelToLp N lam f (ComplementaryKFinite.toModel lam
        (complementaryDiagonalIterate lam n v)) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
    ((contDiff_modelToLpComplementaryDiagonalOrbit N lam f v n).contDiffAt) ⟨le_rfl, ht.le⟩]
  change iteratedDeriv n (fun u => integralSubgroupUnitary
    (CongruenceSubgroup.Gamma (N + 1)) (realPositiveDiagonalBorel (-u) : SL2R)
    (modelToLp N lam f (ComplementaryKFinite.toModel lam v))) 0 = _
  rw [iteratedDeriv_modelToLp_complementaryDiagonal_orbit N lam f v n]
  simp only [neg_zero, realPositiveDiagonalBorel_zero, OneMemClass.coe_one,
    integralSubgroupUnitary_one]

/-- Every finite Taylor polynomial of a nondegenerate quotient diagonal orbit is already in the
normalized finite Maass-model image. -/
theorem taylorWithinEval_modelToLpComplementaryDiagonalOrbit_mem_range_modelIsometry
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (K : ℕ) (t : ℝ) (ht : 0 < t) :
    taylorWithinEval (modelToLpComplementaryDiagonalOrbit N lam f v) K (Set.Icc 0 t) 0 t ∈
      Set.range (modelIsometry N lam f) := by
  rw [taylor_within_apply]
  change _ ∈ LinearMap.range (modelIsometry N lam f).toLinearMap
  apply (LinearMap.range (modelIsometry N lam f).toLinearMap).sum_mem
  intro k hk
  rw [iteratedDerivWithin_modelToLpComplementaryDiagonalOrbit_zero N lam f v k t ht]
  let a : ℝ := (k.factorial : ℝ)⁻¹ * (t - 0) ^ k
  change ((a : ℂ) •
    modelToLp N lam f (ComplementaryKFinite.toModel lam
      (complementaryDiagonalIterate lam k v))) ∈
        LinearMap.range (modelIsometry N lam f).toLinearMap
  exact (LinearMap.range (modelIsometry N lam f).toLinearMap).smul_mem _
    (modelToLp_mem_range_modelIsometry N lam f (complementaryDiagonalIterate lam k v))

/-- After cancelling the factorial, the Taylor remainder is controlled by the geometric
majorant associated to the complementary diagonal-generator bound. -/
theorem norm_sub_taylorWithinEval_modelToLpComplementaryDiagonalOrbit_le_geometric
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖modelToLpComplementaryDiagonalOrbit N lam f v t -
        taylorWithinEval (modelToLpComplementaryDiagonalOrbit N lam f v) K (Set.Icc 0 t) 0 t‖ ≤
      ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ * ((2 * r + 2) * t) ^ (K + 1) := by
  calc
    ‖modelToLpComplementaryDiagonalOrbit N lam f v t -
        taylorWithinEval (modelToLpComplementaryDiagonalOrbit N lam f v) K (Set.Icc 0 t) 0 t‖ ≤
        ((2 * r + 2) ^ (K + 1) * (K + 1).factorial *
          ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖) * t ^ (K + 1) /
            (K + 1).factorial :=
      norm_sub_taylorWithinEval_modelToLpComplementaryDiagonalOrbit_le_factorial
        N lam f v r hr hsupp K t ht
    _ = ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ * ((2 * r + 2) * t) ^ (K + 1) := by
      have hfac : (((K + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
      rw [mul_pow]
      field_simp

/-- A finite complementary-model diagonal orbit belongs to the completed-model image for every
positive time inside its certified geometric Taylor radius. -/
theorem modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_pos_of_lt
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (t : ℝ) (ht : 0 < t) (hsmall : (2 * r + 2) * t < 1) :
    modelToLpComplementaryDiagonalOrbit N lam f v t ∈
      Set.range (completedModelIsometry N lam f) := by
  have hbase : 0 ≤ 2 * r + 2 := by nlinarith
  have hq0 : 0 ≤ (2 * r + 2) * t := mul_nonneg hbase ht.le
  have hshift : Filter.Tendsto (fun K : ℕ => K + 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with K hK
    exact hK.trans (Nat.le_add_right K 1)
  have hgeometric : Filter.Tendsto
      (fun K : ℕ => ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ *
        ((2 * r + 2) * t) ^ (K + 1)) Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hsmall).comp hshift).const_mul
        (‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖)
  have hnorm : Filter.Tendsto
      (fun K : ℕ => ‖modelToLpComplementaryDiagonalOrbit N lam f v t -
        taylorWithinEval (modelToLpComplementaryDiagonalOrbit N lam f v) K (Set.Icc 0 t) 0 t‖)
      Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro K
      exact norm_nonneg _
    · intro K
      exact norm_sub_taylorWithinEval_modelToLpComplementaryDiagonalOrbit_le_geometric
        N lam f v r hr hsupp K t ht.le
    · exact hgeometric
  have htaylor : Filter.Tendsto
      (fun K : ℕ => taylorWithinEval (modelToLpComplementaryDiagonalOrbit N lam f v) K
        (Set.Icc 0 t) 0 t) Filter.atTop
      (nhds (modelToLpComplementaryDiagonalOrbit N lam f v t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hnorm
  rw [completedModelIsometry_range]
  apply mem_closure_of_tendsto htaylor
  exact Filter.Eventually.of_forall fun K =>
    taylorWithinEval_modelToLpComplementaryDiagonalOrbit_mem_range_modelIsometry
      N lam f v K t ht

/-- The initial point of every finite complementary-model diagonal orbit is in the completed
model image. -/
theorem modelToLpComplementaryDiagonalOrbit_zero_mem_range_completedModelIsometry
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) :
    modelToLpComplementaryDiagonalOrbit N lam f v 0 ∈
      Set.range (completedModelIsometry N lam f) := by
  rw [completedModelIsometry_range]
  apply subset_closure
  simpa only [modelToLpComplementaryDiagonalOrbit, neg_zero,
    realPositiveDiagonalBorel_zero, OneMemClass.coe_one, integralSubgroupUnitary_one] using
    (modelToLp_mem_range_modelIsometry N lam f v)

/-- The reverse-time parameterization of a quotient diagonal orbit. -/
def modelToLpComplementaryNegativeDiagonalOrbit
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) : ℝ →
    Lp ℂ 2 (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1))) :=
  fun t => modelToLpComplementaryDiagonalOrbit N lam f v (-t)

/-- Reverse time preserves finite-order smoothness of the source-attached diagonal orbit. -/
theorem contDiff_modelToLpComplementaryNegativeDiagonalOrbit
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) :
    ∀ n : ℕ, ContDiff ℝ n (modelToLpComplementaryNegativeDiagonalOrbit N lam f v) := by
  intro n
  change ContDiff ℝ n (fun t : ℝ => modelToLpComplementaryDiagonalOrbit N lam f v (-t))
  change ContDiff ℝ n
    (modelToLpComplementaryDiagonalOrbit N lam f v ∘ fun t : ℝ => -t)
  exact (contDiff_modelToLpComplementaryDiagonalOrbit N lam f v n).comp
    (contDiff_neg : ContDiff ℝ n fun t : ℝ => -t)

/-- The reverse-time quotient orbit has the same factorial derivative majorant. -/
theorem norm_iteratedDeriv_modelToLpComplementaryNegativeDiagonalOrbit_le_factorial
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (n : ℕ) (t : ℝ) :
    ‖iteratedDeriv n (modelToLpComplementaryNegativeDiagonalOrbit N lam f v) t‖ ≤
      (2 * r + 2) ^ n * n.factorial *
        ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ := by
  change ‖iteratedDeriv n (fun u : ℝ =>
    modelToLpComplementaryDiagonalOrbit N lam f v (-u)) t‖ ≤ _
  rw [iteratedDeriv_comp_neg, norm_smul, norm_pow]
  simpa only [norm_neg, norm_one, one_pow, one_mul] using
    (norm_iteratedDeriv_modelToLpComplementaryDiagonalOrbit_le_factorial
      N lam f v r hr hsupp n (-t))

/-- At the initial endpoint of a reverse-time Taylor interval, the quotient derivative is the
corresponding finite model iterate with its exact parity sign. -/
theorem iteratedDerivWithin_modelToLpComplementaryNegativeDiagonalOrbit_zero
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    iteratedDerivWithin n (modelToLpComplementaryNegativeDiagonalOrbit N lam f v)
      (Set.Icc 0 t) 0 =
      (-1 : ℝ) ^ n • modelToLp N lam f (ComplementaryKFinite.toModel lam
        (complementaryDiagonalIterate lam n v)) := by
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
    ((contDiff_modelToLpComplementaryNegativeDiagonalOrbit N lam f v n).contDiffAt)
    ⟨le_rfl, ht.le⟩]
  change iteratedDeriv n (fun u : ℝ => modelToLpComplementaryDiagonalOrbit N lam f v (-u)) 0 = _
  rw [iteratedDeriv_comp_neg]
  simp only [neg_zero]
  have horbit : iteratedDeriv n (modelToLpComplementaryDiagonalOrbit N lam f v) 0 =
      modelToLp N lam f (ComplementaryKFinite.toModel lam
        (complementaryDiagonalIterate lam n v)) := by
    change iteratedDeriv n (fun u => integralSubgroupUnitary
      (CongruenceSubgroup.Gamma (N + 1)) (realPositiveDiagonalBorel (-u) : SL2R)
      (modelToLp N lam f (ComplementaryKFinite.toModel lam v))) 0 = _
    rw [iteratedDeriv_modelToLp_complementaryDiagonal_orbit N lam f v n]
    simp only [neg_zero, realPositiveDiagonalBorel_zero, OneMemClass.coe_one,
      integralSubgroupUnitary_one]
  rw [horbit]

/-- Banach-valued Taylor remainder bound for a reverse-time quotient diagonal orbit. -/
theorem norm_sub_taylorWithinEval_modelToLpComplementaryNegativeDiagonalOrbit_le_factorial
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖modelToLpComplementaryNegativeDiagonalOrbit N lam f v t -
        taylorWithinEval (modelToLpComplementaryNegativeDiagonalOrbit N lam f v)
          K (Set.Icc 0 t) 0 t‖ ≤
      ((2 * r + 2) ^ (K + 1) * (K + 1).factorial *
        ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖) * t ^ (K + 1) /
          (K + 1).factorial := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp [modelToLpComplementaryNegativeDiagonalOrbit]
  apply HTGeometry.norm_sub_taylorWithinEval_le_factorial ht.le
    (contDiff_modelToLpComplementaryNegativeDiagonalOrbit N lam f v (K + 1)).contDiffOn
  intro y hy
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc ht)
    ((contDiff_modelToLpComplementaryNegativeDiagonalOrbit N lam f v (K + 1)).contDiffAt) hy]
  exact norm_iteratedDeriv_modelToLpComplementaryNegativeDiagonalOrbit_le_factorial
    N lam f v r hr hsupp (K + 1) y

/-- Every finite Taylor polynomial of a reverse-time quotient diagonal orbit remains in the
normalized finite Maass-model image. -/
theorem taylorWithinEval_modelToLpComplementaryNegativeDiagonalOrbit_mem_range_modelIsometry
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (K : ℕ) (t : ℝ) (ht : 0 < t) :
    taylorWithinEval (modelToLpComplementaryNegativeDiagonalOrbit N lam f v) K
      (Set.Icc 0 t) 0 t ∈ Set.range (modelIsometry N lam f) := by
  rw [taylor_within_apply]
  change _ ∈ LinearMap.range (modelIsometry N lam f).toLinearMap
  apply (LinearMap.range (modelIsometry N lam f).toLinearMap).sum_mem
  intro k hk
  rw [iteratedDerivWithin_modelToLpComplementaryNegativeDiagonalOrbit_zero N lam f v k t ht]
  rw [smul_smul]
  let a : ℝ := ((k.factorial : ℝ)⁻¹ * (t - 0) ^ k) * (-1 : ℝ) ^ k
  change ((a : ℂ) • modelToLp N lam f (ComplementaryKFinite.toModel lam
    (complementaryDiagonalIterate lam k v))) ∈
      LinearMap.range (modelIsometry N lam f).toLinearMap
  exact (LinearMap.range (modelIsometry N lam f).toLinearMap).smul_mem _
    (modelToLp_mem_range_modelIsometry N lam f (complementaryDiagonalIterate lam k v))

/-- After cancelling the factorial, the reverse-time Taylor remainder has the same geometric
majorant as the forward orbit. -/
theorem norm_sub_taylorWithinEval_modelToLpComplementaryNegativeDiagonalOrbit_le_geometric
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ‖modelToLpComplementaryNegativeDiagonalOrbit N lam f v t -
        taylorWithinEval (modelToLpComplementaryNegativeDiagonalOrbit N lam f v)
          K (Set.Icc 0 t) 0 t‖ ≤
      ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ * ((2 * r + 2) * t) ^ (K + 1) := by
  calc
    ‖modelToLpComplementaryNegativeDiagonalOrbit N lam f v t -
        taylorWithinEval (modelToLpComplementaryNegativeDiagonalOrbit N lam f v)
          K (Set.Icc 0 t) 0 t‖ ≤
        ((2 * r + 2) ^ (K + 1) * (K + 1).factorial *
          ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖) * t ^ (K + 1) /
            (K + 1).factorial :=
      norm_sub_taylorWithinEval_modelToLpComplementaryNegativeDiagonalOrbit_le_factorial
        N lam f v r hr hsupp K t ht
    _ = ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ * ((2 * r + 2) * t) ^ (K + 1) := by
      have hfac : (((K + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
      rw [mul_pow]
      field_simp

/-- A finite complementary-model reverse diagonal orbit belongs to the completed-model image
for every positive time inside its certified geometric Taylor radius. -/
theorem modelToLpComplementaryNegativeDiagonalOrbit_mem_range_completedModelIsometry_of_pos_of_lt
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (t : ℝ) (ht : 0 < t) (hsmall : (2 * r + 2) * t < 1) :
    modelToLpComplementaryNegativeDiagonalOrbit N lam f v t ∈
      Set.range (completedModelIsometry N lam f) := by
  have hbase : 0 ≤ 2 * r + 2 := by nlinarith
  have hq0 : 0 ≤ (2 * r + 2) * t := mul_nonneg hbase ht.le
  have hshift : Filter.Tendsto (fun K : ℕ => K + 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with K hK
    exact hK.trans (Nat.le_add_right K 1)
  have hgeometric : Filter.Tendsto
      (fun K : ℕ => ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ *
        ((2 * r + 2) * t) ^ (K + 1)) Filter.atTop (nhds 0) := by
    simpa using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hsmall).comp hshift).const_mul
        (‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖)
  have hnorm : Filter.Tendsto
      (fun K : ℕ => ‖modelToLpComplementaryNegativeDiagonalOrbit N lam f v t -
        taylorWithinEval (modelToLpComplementaryNegativeDiagonalOrbit N lam f v)
          K (Set.Icc 0 t) 0 t‖) Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro K
      exact norm_nonneg _
    · intro K
      exact norm_sub_taylorWithinEval_modelToLpComplementaryNegativeDiagonalOrbit_le_geometric
        N lam f v r hr hsupp K t ht.le
    · exact hgeometric
  have htaylor : Filter.Tendsto
      (fun K : ℕ => taylorWithinEval (modelToLpComplementaryNegativeDiagonalOrbit N lam f v)
        K (Set.Icc 0 t) 0 t) Filter.atTop
      (nhds (modelToLpComplementaryNegativeDiagonalOrbit N lam f v t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hnorm
  rw [completedModelIsometry_range]
  apply mem_closure_of_tendsto htaylor
  exact Filter.Eventually.of_forall fun K =>
    taylorWithinEval_modelToLpComplementaryNegativeDiagonalOrbit_mem_range_modelIsometry
      N lam f v K t ht

/-- The completed Maass-model image contains every finite-model diagonal translate in the full
two-sided certified Taylor neighborhood of the identity. -/
theorem modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_abs_lt
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (t : ℝ) (hsmall : |(2 * r + 2) * t| < 1) :
    modelToLpComplementaryDiagonalOrbit N lam f v t ∈
      Set.range (completedModelIsometry N lam f) := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hbase : 0 ≤ 2 * r + 2 := by nlinarith
    have hnonpos : (2 * r + 2) * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbase ht.le
    have hsmallNeg : (2 * r + 2) * (-t) < 1 := by
      calc
        (2 * r + 2) * (-t) = -((2 * r + 2) * t) := by ring
        _ = |(2 * r + 2) * t| := (abs_of_nonpos hnonpos).symm
        _ < 1 := hsmall
    simpa only [modelToLpComplementaryNegativeDiagonalOrbit, neg_neg] using
      (modelToLpComplementaryNegativeDiagonalOrbit_mem_range_completedModelIsometry_of_pos_of_lt
        N lam f v r hr hsupp (-t) (neg_pos.mpr ht) hsmallNeg)
  · exact modelToLpComplementaryDiagonalOrbit_zero_mem_range_completedModelIsometry N lam f v
  · exact modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_pos_of_lt
      N lam f v r hr hsupp t ht (lt_of_le_of_lt (le_abs_self _) hsmall)

/-- A derivative at the right endpoint of a closed interval remains in a closed real submodule
when the whole interval lies in that submodule. -/
theorem closedSubmodule_deriv_mem_of_mem_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Submodule ℝ E) (hW : IsClosed (W : Set E))
    {u' : E} {g : ℝ → E} {a b : ℝ}
    (hba : b < a) (hderiv : HasDerivAt g u' a)
    (hmem : ∀ x ∈ Set.Icc b a, g x ∈ W) : u' ∈ W := by
  apply hW.mem_of_tendsto hderiv.tendsto_slope_zero_left
  filter_upwards [
    (show Set.Iio (0 : ℝ) ∈ 𝓝[<] 0 from self_mem_nhdsWithin),
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by linarith : b - a < 0))]
    with s hsneg hsnear
  change s < 0 at hsneg
  change b - a < s at hsnear
  apply W.smul_mem
  apply W.sub_mem
  · exact hmem (a + s) ⟨by linarith, by linarith⟩
  · exact hmem a ⟨hba.le, le_rfl⟩

/-- If a smooth curve takes a whole closed interval into a closed real submodule, every
iterated derivative takes the interval's interior into that submodule. -/
theorem closedSubmodule_iteratedDeriv_mem_of_mem_Icc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (W : Submodule ℝ E) (hW : IsClosed (W : Set E))
    {g : ℝ → E} {a b : ℝ}
    (hderiv : ∀ n x, HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g x) x)
    (hmem : ∀ x ∈ Set.Icc b a, g x ∈ W)
    (n : ℕ) (x : ℝ) (hx : x ∈ Set.Ioc b a) : iteratedDeriv n g x ∈ W := by
  induction n generalizing x with
  | zero =>
      simpa only [iteratedDeriv_zero] using hmem x ⟨hx.1.le, hx.2⟩
  | succ n ih =>
      rw [iteratedDeriv_succ, (hderiv n x).deriv]
      let c : ℝ := (b + x) / 2
      have hcx : c < x := by
        dsimp [c]
        linarith [hx.1]
      apply closedSubmodule_deriv_mem_of_mem_Icc W hW hcx (hderiv n x)
      intro y hy
      exact ih y ⟨by
        dsimp [c] at hy hcx ⊢
        linarith [hx.1, hy.1], hy.2.trans hx.2⟩

/-- The exact derivative of every finite complementary-model diagonal orbit jet is its next
orbit jet. -/
theorem hasDerivAt_iteratedDeriv_modelToLpComplementaryDiagonalOrbit
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (k : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv k (modelToLpComplementaryDiagonalOrbit N lam f v))
      (iteratedDeriv (k + 1) (modelToLpComplementaryDiagonalOrbit N lam f v) x) x := by
  change HasDerivAt
    (iteratedDeriv k (fun u => integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
      (realPositiveDiagonalBorel (-u) : SL2R)
      (modelToLp N lam f (ComplementaryKFinite.toModel lam v))))
    (iteratedDeriv (k + 1) (fun u => integralSubgroupUnitary
      (CongruenceSubgroup.Gamma (N + 1)) (realPositiveDiagonalBorel (-u) : SL2R)
      (modelToLp N lam f (ComplementaryKFinite.toModel lam v))) x) x
  rw [iteratedDeriv_modelToLp_complementaryDiagonal_orbit N lam f v k,
    iteratedDeriv_modelToLp_complementaryDiagonal_orbit N lam f v (k + 1)]
  exact modelToLp_complementaryDiagonalIterate_hasDerivAt_all_times N lam f v k x

/-- Every finite-model diagonal-orbit jet belongs to the completed range throughout its
certified local interval. -/
theorem iteratedDeriv_modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_abs_lt
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (n : ℕ) (t : ℝ) (hsmall : |(2 * r + 2) * t| < 1) :
    iteratedDeriv n (modelToLpComplementaryDiagonalOrbit N lam f v) t ∈
      Set.range (completedModelIsometry N lam f) := by
  let W : Submodule ℝ (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) :=
    (LinearMap.range (completedModelIsometry N lam f).toLinearMap).restrictScalars ℝ
  have hWclosed : IsClosed (W : Set (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1))))) := by
    change IsClosed (Set.range (completedModelIsometry N lam f))
    exact (completedModelIsometry N lam f).isometry.isClosedEmbedding.isClosed_range
  let C : ℝ := 2 * r + 2
  have hCpos : 0 < C := by
    dsimp [C]
    nlinarith
  have hlocal : ∀ x : ℝ, |C * x| < 1 →
      modelToLpComplementaryDiagonalOrbit N lam f v x ∈ W := by
    intro x hx
    change modelToLpComplementaryDiagonalOrbit N lam f v x ∈
      Set.range (completedModelIsometry N lam f)
    exact modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_abs_lt
      N lam f v r hr hsupp x (by simpa [C] using hx)
  have hderiv : ∀ k x, HasDerivAt
      (iteratedDeriv k (modelToLpComplementaryDiagonalOrbit N lam f v))
      (iteratedDeriv (k + 1) (modelToLpComplementaryDiagonalOrbit N lam f v) x) x :=
    hasDerivAt_iteratedDeriv_modelToLpComplementaryDiagonalOrbit N lam f v
  have hall : ∀ k x, |C * x| < 1 →
      iteratedDeriv k (modelToLpComplementaryDiagonalOrbit N lam f v) x ∈ W := by
    intro k
    induction k with
    | zero =>
        intro x hx
        simpa only [iteratedDeriv_zero] using hlocal x hx
    | succ k ih =>
        intro x hx
        rw [iteratedDeriv_succ, (hderiv k x).deriv]
        let δ : ℝ := (1 - |C * x|) / (2 * C)
        have hδ : 0 < δ := by
          apply div_pos <;> linarith
        apply closedSubmodule_deriv_mem_of_mem_Icc W hWclosed (sub_lt_self x hδ)
          (hderiv k x)
        intro y hy
        have hyabs : |y - x| ≤ δ :=
          abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
        have hCδ : C * δ = (1 - |C * x|) / 2 := by
          dsimp [δ]
          field_simp
        have hybound : |C * y| < 1 := by
          calc
            |C * y| = |C * x + C * (y - x)| := by
              congr 1
              ring
            _ ≤ |C * x| + |C * (y - x)| := abs_add_le _ _
            _ = |C * x| + C * |y - x| := by
              simp [abs_mul, abs_of_pos hCpos]
            _ ≤ |C * x| + C * δ := by gcongr
            _ = |C * x| + (1 - |C * x|) / 2 := by rw [hCδ]
            _ < 1 := by linarith
        exact ih y hybound
  exact hall n t (by simpa [C] using hsmall)

/-- A completed-range jet at a center propagates a finite complementary-model diagonal orbit
one Taylor step forward; its radius depends only on the fixed finite vector. -/
theorem modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_center_of_pos_of_lt
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (a h : ℝ) (hjets : ∀ n : ℕ,
      iteratedDeriv n (modelToLpComplementaryDiagonalOrbit N lam f v) a ∈
        Set.range (completedModelIsometry N lam f))
    (hpos : 0 < h) (hsmall : (2 * r + 2) * h < 1) :
    modelToLpComplementaryDiagonalOrbit N lam f v (a + h) ∈
      Set.range (completedModelIsometry N lam f) := by
  let W : Submodule ℝ (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) :=
    (LinearMap.range (completedModelIsometry N lam f).toLinearMap).restrictScalars ℝ
  have hWclosed : IsClosed (W : Set (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1))))) := by
    change IsClosed (Set.range (completedModelIsometry N lam f))
    exact (completedModelIsometry N lam f).isometry.isClosedEmbedding.isClosed_range
  have hjetsW : ∀ n : ℕ,
      iteratedDeriv n (modelToLpComplementaryDiagonalOrbit N lam f v) a ∈ W := by
    intro n
    change iteratedDeriv n (modelToLpComplementaryDiagonalOrbit N lam f v) a ∈
      Set.range (completedModelIsometry N lam f)
    exact hjets n
  have hcont : ∀ n : ℕ, ContDiff ℝ n
      (fun u => modelToLpComplementaryDiagonalOrbit N lam f v (a + u)) := by
    intro n
    exact (contDiff_modelToLpComplementaryDiagonalOrbit N lam f v n).comp
      (contDiff_const.add contDiff_id)
  have hpoly : ∀ K : ℕ,
      taylorWithinEval (fun u => modelToLpComplementaryDiagonalOrbit N lam f v (a + u))
        K (Set.Icc 0 h) 0 h ∈ W := by
    intro K
    rw [taylor_within_apply]
    apply W.sum_mem
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hpos)
      ((hcont k).contDiffAt) ⟨le_rfl, hpos.le⟩,
      iteratedDeriv_comp_const_add]
    simpa only [add_zero, sub_zero] using W.smul_mem _ (hjetsW k)
  have hrem : ∀ K : ℕ,
      ‖modelToLpComplementaryDiagonalOrbit N lam f v (a + h) -
        taylorWithinEval (fun u => modelToLpComplementaryDiagonalOrbit N lam f v (a + u))
          K (Set.Icc 0 h) 0 h‖ ≤
        ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ * ((2 * r + 2) * h) ^ (K + 1) := by
    intro K
    calc
      ‖modelToLpComplementaryDiagonalOrbit N lam f v (a + h) -
        taylorWithinEval (fun u => modelToLpComplementaryDiagonalOrbit N lam f v (a + u))
          K (Set.Icc 0 h) 0 h‖ ≤
        ((2 * r + 2) ^ (K + 1) * (K + 1).factorial *
          ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖) * h ^ (K + 1) /
            (K + 1).factorial := by
        apply HTGeometry.norm_sub_taylorWithinEval_le_factorial hpos.le (hcont (K + 1)).contDiffOn
        intro y hy
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hpos)
          ((hcont (K + 1)).contDiffAt) hy, iteratedDeriv_comp_const_add]
        exact norm_iteratedDeriv_modelToLpComplementaryDiagonalOrbit_le_factorial
          N lam f v r hr hsupp (K + 1) (a + y)
      _ = ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ * ((2 * r + 2) * h) ^ (K + 1) := by
        have hfac : (((K + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
        rw [mul_pow]
        field_simp
  have hbase : 0 ≤ (2 * r + 2) * h := by nlinarith
  have hshift : Filter.Tendsto (fun K : ℕ => K + 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with K hK
    exact hK.trans (Nat.le_add_right K 1)
  have hgeometric : Filter.Tendsto
      (fun K : ℕ => ‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖ *
        ((2 * r + 2) * h) ^ (K + 1)) Filter.atTop (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hbase hsmall).comp hshift).const_mul
      (‖modelToLp N lam f (Finsupp.single 0 1)‖ * ‖v‖)
  have hnorm : Filter.Tendsto
      (fun K : ℕ => ‖modelToLpComplementaryDiagonalOrbit N lam f v (a + h) -
        taylorWithinEval (fun u => modelToLpComplementaryDiagonalOrbit N lam f v (a + u))
          K (Set.Icc 0 h) 0 h‖) Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro K
      exact norm_nonneg _
    · intro K
      exact hrem K
    · exact hgeometric
  have htaylor : Filter.Tendsto
      (fun K : ℕ => taylorWithinEval (fun u => modelToLpComplementaryDiagonalOrbit N lam f v (a + u))
        K (Set.Icc 0 h) 0 h) Filter.atTop
      (nhds (modelToLpComplementaryDiagonalOrbit N lam f v (a + h))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hnorm
  change modelToLpComplementaryDiagonalOrbit N lam f v (a + h) ∈ W
  exact hWclosed.mem_of_tendsto htaylor (Filter.Eventually.of_forall hpoly)

/-- A finite complementary-model diagonal orbit stays in the completed-model range for every
nonnegative time.  Its support radius is fixed before the continuation, so Taylor propagation
uses a uniform positive step along that one orbit. -/
theorem modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_nonneg
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (t : ℝ) (ht : 0 ≤ t) :
    modelToLpComplementaryDiagonalOrbit N lam f v t ∈
      Set.range (completedModelIsometry N lam f) := by
  let W : Submodule ℝ (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) :=
    (LinearMap.range (completedModelIsometry N lam f).toLinearMap).restrictScalars ℝ
  have hWclosed : IsClosed (W : Set (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1))))) := by
    change IsClosed (Set.range (completedModelIsometry N lam f))
    exact (completedModelIsometry N lam f).isometry.isClosedEmbedding.isClosed_range
  let C : ℝ := 2 * r + 2
  let d : ℝ := (2 * C)⁻¹
  have hCpos : 0 < C := by
    dsimp [C]
    nlinarith
  have hdpos : 0 < d := by
    dsimp [d]
    positivity
  have hCd : C * d = 1 / 2 := by
    dsimp [d]
    field_simp
  have hP : ∀ n : ℕ, ∀ s : ℝ, 0 ≤ s → s ≤ (n : ℝ) * d →
      modelToLpComplementaryDiagonalOrbit N lam f v s ∈ W := by
    intro n
    induction n with
    | zero =>
        intro s hs hsn
        have hs_zero : s = 0 := by
          norm_num at hsn ⊢
          linarith
        subst s
        change modelToLpComplementaryDiagonalOrbit N lam f v 0 ∈
          Set.range (completedModelIsometry N lam f)
        exact modelToLpComplementaryDiagonalOrbit_zero_mem_range_completedModelIsometry
          N lam f v
    | succ n ih =>
        intro s hs hsn
        by_cases hle : s ≤ (n : ℝ) * d
        · exact ih s hs hle
        · have hlt : (n : ℝ) * d < s := lt_of_not_ge hle
          let a : ℝ := (n : ℝ) * d
          let h : ℝ := s - a
          have hpos : 0 < h := by
            dsimp [h, a]
            linarith
          have hhd : h ≤ d := by
            dsimp [h, a]
            rw [Nat.cast_succ] at hsn
            nlinarith [hsn]
          have hsmall : C * h < 1 := by
            calc
              C * h ≤ C * d := mul_le_mul_of_nonneg_left hhd hCpos.le
              _ = 1 / 2 := hCd
              _ < 1 := by norm_num
          have hjets : ∀ k : ℕ,
              iteratedDeriv k (modelToLpComplementaryDiagonalOrbit N lam f v) a ∈ W := by
            cases n with
            | zero =>
                intro k
                have ha_zero : a = 0 := by
                  dsimp [a]
                  norm_num
                rw [ha_zero]
                change iteratedDeriv k (modelToLpComplementaryDiagonalOrbit N lam f v) 0 ∈
                  Set.range (completedModelIsometry N lam f)
                exact iteratedDeriv_modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_abs_lt
                  N lam f v r hr hsupp k 0 (by norm_num)
            | succ n =>
                intro k
                refine closedSubmodule_iteratedDeriv_mem_of_mem_Icc W hWclosed (a := a) (b := 0)
                  (hasDerivAt_iteratedDeriv_modelToLpComplementaryDiagonalOrbit N lam f v) ?_ k a ?_
                · intro x hx
                  exact ih x hx.1 hx.2
                · refine ⟨?_, le_rfl⟩
                  dsimp [a]
                  rw [Nat.cast_succ]
                  positivity
          have hnext :=
            modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_center_of_pos_of_lt
              N lam f v r hr hsupp a h (fun k => by exact hjets k) hpos (by
                simpa [C] using hsmall)
          change modelToLpComplementaryDiagonalOrbit N lam f v s ∈ W
          change modelToLpComplementaryDiagonalOrbit N lam f v (a + h) ∈ W at hnext
          have hasum : a + h = s := by
            dsimp [h]
            ring
          rw [hasum] at hnext
          exact hnext
  obtain ⟨n, hn⟩ := exists_nat_gt (t / d)
  have hbound : t ≤ (n : ℝ) * d := by
    apply (div_le_iff₀ hdpos).mp
    exact hn.le
  change modelToLpComplementaryDiagonalOrbit N lam f v t ∈ W
  exact hP n t ht hbound

private theorem spherical_support_zero
    (lam : SelbergExceptionalEigenvalue) :
    ∀ m ∈ (ComplementaryKFinite.toModel lam (Finsupp.single 0 1)).support, |(m : ℝ)| ≤ 0 := by
  intro m hm
  have hm_ne : (Finsupp.single 0 1 : SphericalKFiniteModel) m ≠ 0 := by
    exact Finsupp.mem_support_iff.mp hm
  have hm_zero : m = 0 := by
    by_contra hne
    apply hm_ne
    have hne' : ¬ 0 = m := fun h => hne h.symm
    simp only [Finsupp.single_apply, if_neg hne']
  subst m
  simp

/-- The exact derivative of every zero-`K`-type diagonal orbit jet is its next orbit jet. -/
theorem hasDerivAt_iteratedDeriv_modelToLpComplementarySphericalOrbit
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (k : ℕ) (x : ℝ) :
    HasDerivAt
      (iteratedDeriv k (modelToLpComplementaryDiagonalOrbit N lam f
        (Finsupp.single 0 1 : ComplementaryKFinite lam)))
      (iteratedDeriv (k + 1) (modelToLpComplementaryDiagonalOrbit N lam f
        (Finsupp.single 0 1 : ComplementaryKFinite lam)) x) x := by
  change HasDerivAt
    (iteratedDeriv k (fun u => integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
      (realPositiveDiagonalBorel (-u) : SL2R)
      (modelToLp N lam f (ComplementaryKFinite.toModel lam
        (Finsupp.single 0 1 : ComplementaryKFinite lam)))))
    (iteratedDeriv (k + 1) (fun u => integralSubgroupUnitary
      (CongruenceSubgroup.Gamma (N + 1)) (realPositiveDiagonalBorel (-u) : SL2R)
      (modelToLp N lam f (ComplementaryKFinite.toModel lam
        (Finsupp.single 0 1 : ComplementaryKFinite lam)))) x) x
  rw [iteratedDeriv_modelToLp_complementaryDiagonal_orbit N lam f
    (Finsupp.single 0 1 : ComplementaryKFinite lam) k,
    iteratedDeriv_modelToLp_complementaryDiagonal_orbit N lam f
    (Finsupp.single 0 1 : ComplementaryKFinite lam) (k + 1)]
  exact modelToLp_complementaryDiagonalIterate_hasDerivAt_all_times N lam f
    (Finsupp.single 0 1 : ComplementaryKFinite lam) k x

/-- Every real derivative of the zero-`K`-type quotient orbit stays in the completed
complementary-model range throughout its certified local interval. -/
theorem iteratedDeriv_modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_abs_lt
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (n : ℕ) (t : ℝ) (hsmall : |2 * t| < 1) :
    iteratedDeriv n
      (modelToLpComplementaryDiagonalOrbit N lam f
        (Finsupp.single 0 1 : ComplementaryKFinite lam)) t ∈
      Set.range (completedModelIsometry N lam f) := by
  let W : Submodule ℝ (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) :=
    (LinearMap.range (completedModelIsometry N lam f).toLinearMap).restrictScalars ℝ
  have hWclosed : IsClosed (W : Set (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1))))) := by
    change IsClosed (Set.range (completedModelIsometry N lam f))
    exact (completedModelIsometry N lam f).isometry.isClosedEmbedding.isClosed_range
  have hlocal : ∀ x : ℝ, |2 * x| < 1 →
      modelToLpComplementaryDiagonalOrbit N lam f
        (Finsupp.single 0 1 : ComplementaryKFinite lam) x ∈ W := by
    intro x hx
    change modelToLpComplementaryDiagonalOrbit N lam f
        (Finsupp.single 0 1 : ComplementaryKFinite lam) x ∈
      Set.range (completedModelIsometry N lam f)
    exact modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_abs_lt
      N lam f (Finsupp.single 0 1 : ComplementaryKFinite lam) 0 (by norm_num)
        (spherical_support_zero lam) x (by
          simpa only [mul_zero, zero_add] using hx)
  have hderiv : ∀ k x, HasDerivAt
      (iteratedDeriv k (modelToLpComplementaryDiagonalOrbit N lam f
        (Finsupp.single 0 1 : ComplementaryKFinite lam)))
      (iteratedDeriv (k + 1) (modelToLpComplementaryDiagonalOrbit N lam f
        (Finsupp.single 0 1 : ComplementaryKFinite lam)) x) x :=
    hasDerivAt_iteratedDeriv_modelToLpComplementarySphericalOrbit N lam f
  have hall : ∀ k x, |2 * x| < 1 →
      iteratedDeriv k (modelToLpComplementaryDiagonalOrbit N lam f
        (Finsupp.single 0 1 : ComplementaryKFinite lam)) x ∈ W := by
    intro k
    induction k with
    | zero =>
        intro x hx
        simpa only [iteratedDeriv_zero] using hlocal x hx
    | succ k ih =>
        intro x hx
        rw [iteratedDeriv_succ, (hderiv k x).deriv]
        let δ : ℝ := (1 - |2 * x|) / 4
        have hδ : 0 < δ := by
          dsimp [δ]
          linarith
        apply closedSubmodule_deriv_mem_of_mem_Icc W hWclosed (sub_lt_self x hδ)
          (hderiv k x)
        intro y hy
        have hybound : |2 * y| < 1 := by
          have hyabs : |y - x| ≤ δ :=
            abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
          calc
            |2 * y| = |2 * x + 2 * (y - x)| := by
              congr 1
              ring
            _ ≤ |2 * x| + |2 * (y - x)| := abs_add_le _ _
            _ = |2 * x| + 2 * |y - x| := by norm_num [abs_mul]
            _ ≤ |2 * x| + 2 * δ := by gcongr
            _ < 1 := by
              dsimp [δ]
              linarith
        exact ih y hybound
  exact hall n t hsmall

/-- A completed-range jet at a time center propagates the zero-`K`-type diagonal orbit one
Taylor step forward.  The step bound is independent of the time center. -/
theorem modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_center_of_pos_of_lt
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (a h : ℝ) (hjets : ∀ n : ℕ,
      iteratedDeriv n (modelToLpComplementaryDiagonalOrbit N lam f
        (Finsupp.single 0 1 : ComplementaryKFinite lam)) a ∈
        Set.range (completedModelIsometry N lam f))
    (hpos : 0 < h) (hsmall : 2 * h < 1) :
    modelToLpComplementaryDiagonalOrbit N lam f
      (Finsupp.single 0 1 : ComplementaryKFinite lam) (a + h) ∈
      Set.range (completedModelIsometry N lam f) := by
  let s0 : SphericalKFiniteModel := Finsupp.single 0 1
  let v0 : ComplementaryKFinite lam := s0
  let W : Submodule ℝ (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) :=
    (LinearMap.range (completedModelIsometry N lam f).toLinearMap).restrictScalars ℝ
  have hWclosed : IsClosed (W : Set (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1))))) := by
    change IsClosed (Set.range (completedModelIsometry N lam f))
    exact (completedModelIsometry N lam f).isometry.isClosedEmbedding.isClosed_range
  have hjetsW : ∀ n : ℕ,
      iteratedDeriv n (modelToLpComplementaryDiagonalOrbit N lam f v0) a ∈ W := by
    intro n
    change iteratedDeriv n (modelToLpComplementaryDiagonalOrbit N lam f v0) a ∈
      Set.range (completedModelIsometry N lam f)
    simpa [v0, s0] using hjets n
  have hcont : ∀ n : ℕ, ContDiff ℝ n
      (fun u => modelToLpComplementaryDiagonalOrbit N lam f v0 (a + u)) := by
    intro n
    exact (contDiff_modelToLpComplementaryDiagonalOrbit N lam f v0 n).comp
      (contDiff_const.add contDiff_id)
  have hpoly : ∀ K : ℕ,
      taylorWithinEval (fun u => modelToLpComplementaryDiagonalOrbit N lam f v0 (a + u))
        K (Set.Icc 0 h) 0 h ∈ W := by
    intro K
    rw [taylor_within_apply]
    apply W.sum_mem
    intro k hk
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hpos)
      ((hcont k).contDiffAt) ⟨le_rfl, hpos.le⟩,
      iteratedDeriv_comp_const_add]
    simpa only [add_zero, sub_zero] using W.smul_mem _ (hjetsW k)
  have hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v0).support, |(m : ℝ)| ≤ 0 := by
    change ∀ m ∈ (ComplementaryKFinite.toModel lam
      (Finsupp.single 0 1 : ComplementaryKFinite lam)).support, |(m : ℝ)| ≤ 0
    exact spherical_support_zero lam
  have hrem : ∀ K : ℕ,
      ‖modelToLpComplementaryDiagonalOrbit N lam f v0 (a + h) -
        taylorWithinEval (fun u => modelToLpComplementaryDiagonalOrbit N lam f v0 (a + u))
          K (Set.Icc 0 h) 0 h‖ ≤
        ‖modelToLp N lam f s0‖ * ‖v0‖ * (2 * h) ^ (K + 1) := by
    intro K
    calc
      ‖modelToLpComplementaryDiagonalOrbit N lam f v0 (a + h) -
        taylorWithinEval (fun u => modelToLpComplementaryDiagonalOrbit N lam f v0 (a + u))
          K (Set.Icc 0 h) 0 h‖ ≤
        ((2 * 0 + 2) ^ (K + 1) * (K + 1).factorial *
          ‖modelToLp N lam f s0‖ * ‖v0‖) * h ^ (K + 1) /
            (K + 1).factorial := by
        apply HTGeometry.norm_sub_taylorWithinEval_le_factorial hpos.le (hcont (K + 1)).contDiffOn
        intro y hy
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hpos)
          ((hcont (K + 1)).contDiffAt) hy, iteratedDeriv_comp_const_add]
        have hbound := norm_iteratedDeriv_modelToLpComplementaryDiagonalOrbit_le_factorial
          N lam f v0 0 (by norm_num) hsupp (K + 1) (a + y)
        simpa [v0, s0] using hbound
      _ = ‖modelToLp N lam f s0‖ * ‖v0‖ * (2 * h) ^ (K + 1) := by
        have hfac : (((K + 1).factorial : ℕ) : ℝ) ≠ 0 := by positivity
        rw [mul_pow]
        field_simp
        ring
  have hq : 0 ≤ 2 * h := by linarith
  have hshift : Filter.Tendsto (fun K : ℕ => K + 1) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with K hK
    exact hK.trans (Nat.le_add_right K 1)
  have hgeometric : Filter.Tendsto
      (fun K : ℕ => ‖modelToLp N lam f s0‖ * ‖v0‖ * (2 * h) ^ (K + 1))
      Filter.atTop (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq hsmall).comp hshift).const_mul
      (‖modelToLp N lam f s0‖ * ‖v0‖)
  have hnorm : Filter.Tendsto
      (fun K : ℕ => ‖modelToLpComplementaryDiagonalOrbit N lam f v0 (a + h) -
        taylorWithinEval (fun u => modelToLpComplementaryDiagonalOrbit N lam f v0 (a + u))
          K (Set.Icc 0 h) 0 h‖) Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro K
      exact norm_nonneg _
    · intro K
      exact hrem K
    · exact hgeometric
  have htaylor : Filter.Tendsto
      (fun K : ℕ => taylorWithinEval (fun u => modelToLpComplementaryDiagonalOrbit N lam f v0 (a + u))
        K (Set.Icc 0 h) 0 h) Filter.atTop
      (nhds (modelToLpComplementaryDiagonalOrbit N lam f v0 (a + h))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hnorm
  change modelToLpComplementaryDiagonalOrbit N lam f v0 (a + h) ∈ W
  exact hWclosed.mem_of_tendsto htaylor (Filter.Eventually.of_forall hpoly)

/-- The locally certified zero-`K`-type interval supplies every center jet needed for one
support-free Taylor continuation step. -/
theorem modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_center_abs_lt_of_pos_of_lt
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (a h : ℝ) (ha : |2 * a| < 1) (hpos : 0 < h) (hsmall : 2 * h < 1) :
    modelToLpComplementaryDiagonalOrbit N lam f
      (Finsupp.single 0 1 : ComplementaryKFinite lam) (a + h) ∈
      Set.range (completedModelIsometry N lam f) :=
  modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_center_of_pos_of_lt
    N lam f a h
    (fun n => iteratedDeriv_modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_abs_lt
      N lam f n a ha) hpos hsmall

/-- The zero-`K`-type orbit remains in the completed complementary-model range for the first
full forward unit interval. -/
theorem modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_nonneg_of_lt_one
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (t : ℝ) (ht : 0 ≤ t) (htone : t < 1) :
    modelToLpComplementaryDiagonalOrbit N lam f
      (Finsupp.single 0 1 : ComplementaryKFinite lam) t ∈
      Set.range (completedModelIsometry N lam f) := by
  rcases eq_or_lt_of_le ht with rfl | ht
  · exact modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_abs_lt
      N lam f (Finsupp.single 0 1 : ComplementaryKFinite lam) 0 (by norm_num)
        (spherical_support_zero lam) 0 (by norm_num)
  · have hcenter : |2 * (t / 2)| < 1 := by
      calc
        |2 * (t / 2)| = |t| := by
          congr 1
          ring
        _ = t := abs_of_nonneg ht.le
        _ < 1 := htone
    have hstep : 2 * (t / 2) < 1 := by linarith
    have hsum : t / 2 + t / 2 = t := by ring
    rw [← hsum]
    exact modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_center_abs_lt_of_pos_of_lt
      N lam f (t / 2) (t / 2) hcenter (by linarith) hstep

/-- Every zero-`K`-type diagonal orbit jet lies in the completed range at every positive time
in the first forward unit interval. -/
theorem iteratedDeriv_modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_pos_of_lt_one
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (n : ℕ) (t : ℝ) (ht : 0 < t) (htone : t < 1) :
    iteratedDeriv n (modelToLpComplementaryDiagonalOrbit N lam f
      (Finsupp.single 0 1 : ComplementaryKFinite lam)) t ∈
      Set.range (completedModelIsometry N lam f) := by
  let W : Submodule ℝ (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) :=
    (LinearMap.range (completedModelIsometry N lam f).toLinearMap).restrictScalars ℝ
  have hWclosed : IsClosed (W : Set (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1))))) := by
    change IsClosed (Set.range (completedModelIsometry N lam f))
    exact (completedModelIsometry N lam f).isometry.isClosedEmbedding.isClosed_range
  change iteratedDeriv n (modelToLpComplementaryDiagonalOrbit N lam f
      (Finsupp.single 0 1 : ComplementaryKFinite lam)) t ∈ W
  apply closedSubmodule_iteratedDeriv_mem_of_mem_Icc W hWclosed
    (hasDerivAt_iteratedDeriv_modelToLpComplementarySphericalOrbit N lam f)
  · intro x hx
    change modelToLpComplementaryDiagonalOrbit N lam f
        (Finsupp.single 0 1 : ComplementaryKFinite lam) x ∈
      Set.range (completedModelIsometry N lam f)
    exact modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_nonneg_of_lt_one
      N lam f x hx.1 (lt_of_le_of_lt hx.2 htone)
  · exact ⟨ht, le_rfl⟩

/-- The zero-`K`-type quotient orbit stays in the completed complementary-model range for all
nonnegative diagonal times.  The proof bootstraps range membership on quarter-length intervals:
closed-range difference quotients recover every center jet, and the centered Taylor theorem
advances by at most one quarter. -/
theorem modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_nonneg
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (t : ℝ) (ht : 0 ≤ t) :
    modelToLpComplementaryDiagonalOrbit N lam f
      (Finsupp.single 0 1 : ComplementaryKFinite lam) t ∈
      Set.range (completedModelIsometry N lam f) := by
  let W : Submodule ℝ (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1)))) :=
    (LinearMap.range (completedModelIsometry N lam f).toLinearMap).restrictScalars ℝ
  have hWclosed : IsClosed (W : Set (Lp ℂ 2
      (integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1))))) := by
    change IsClosed (Set.range (completedModelIsometry N lam f))
    exact (completedModelIsometry N lam f).isometry.isClosedEmbedding.isClosed_range
  have hP : ∀ n : ℕ, ∀ s : ℝ, 0 ≤ s → s ≤ (n : ℝ) / 4 →
      modelToLpComplementaryDiagonalOrbit N lam f
        (Finsupp.single 0 1 : ComplementaryKFinite lam) s ∈ W := by
    intro n
    induction n with
    | zero =>
        intro s hs hsn
        have hs_zero : s = 0 := by norm_num at hsn ⊢; linarith
        subst s
        change modelToLpComplementaryDiagonalOrbit N lam f
            (Finsupp.single 0 1 : ComplementaryKFinite lam) 0 ∈
          Set.range (completedModelIsometry N lam f)
        exact modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_abs_lt
          N lam f (Finsupp.single 0 1 : ComplementaryKFinite lam) 0 (by norm_num)
            (spherical_support_zero lam) 0 (by norm_num)
    | succ n ih =>
        intro s hs hsn
        by_cases hle : s ≤ (n : ℝ) / 4
        · exact ih s hs hle
        · have hlt : (n : ℝ) / 4 < s := lt_of_not_ge hle
          let a : ℝ := (n : ℝ) / 4
          let h : ℝ := s - a
          have hpos : 0 < h := by
            dsimp [h, a]
            linarith
          have hsmall : 2 * h < 1 := by
            dsimp [h, a]
            rw [Nat.cast_add, Nat.cast_one] at hsn
            nlinarith [hsn]
          have hjets : ∀ k : ℕ,
              iteratedDeriv k (modelToLpComplementaryDiagonalOrbit N lam f
                (Finsupp.single 0 1 : ComplementaryKFinite lam)) a ∈ W := by
            cases n with
            | zero =>
                intro k
                have ha_zero : a = 0 := by
                  dsimp [a]
                  norm_num
                rw [ha_zero]
                change iteratedDeriv k (modelToLpComplementaryDiagonalOrbit N lam f
                    (Finsupp.single 0 1 : ComplementaryKFinite lam)) 0 ∈
                  Set.range (completedModelIsometry N lam f)
                exact iteratedDeriv_modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_abs_lt
                  N lam f k 0 (by norm_num)
            | succ n =>
                intro k
                refine closedSubmodule_iteratedDeriv_mem_of_mem_Icc W hWclosed (a := a) (b := 0)
                  (hasDerivAt_iteratedDeriv_modelToLpComplementarySphericalOrbit N lam f) ?_ k a ?_
                · intro x hx
                  exact ih x hx.1 hx.2
                · refine ⟨?_, le_rfl⟩
                  dsimp [a]
                  positivity
          have hnext :=
            modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_center_of_pos_of_lt
              N lam f a h (fun k => by
                exact hjets k) hpos hsmall
          change modelToLpComplementaryDiagonalOrbit N lam f
              (Finsupp.single 0 1 : ComplementaryKFinite lam) s ∈ W
          change modelToLpComplementaryDiagonalOrbit N lam f
              (Finsupp.single 0 1 : ComplementaryKFinite lam) (a + h) ∈ W at hnext
          have hasum : a + h = s := by
            dsimp [h]
            ring
          rw [hasum] at hnext
          exact hnext
  obtain ⟨n, hn⟩ := exists_nat_gt (4 * t)
  have hbound : t ≤ (n : ℝ) / 4 := by nlinarith [hn]
  change modelToLpComplementaryDiagonalOrbit N lam f
      (Finsupp.single 0 1 : ComplementaryKFinite lam) t ∈ W
  exact hP n t ht hbound

/-- The actual quotient-`L²` Maass source has a completed complementary-model diagonal orbit
throughout the support-free certified neighborhood of the identity. -/
theorem sourceLp_diagonal_mem_range_completedModelIsometry_of_abs_lt
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (t : ℝ) (hsmall : |2 * t| < 1) :
    integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
      (realPositiveDiagonalBorel (-t) : SL2R) (MaassQuotientL2.sourceLp N f) ∈
      Set.range (completedModelIsometry N lam f) := by
  have h := modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_abs_lt
    N lam f (Finsupp.single 0 1 : ComplementaryKFinite lam) 0 (by norm_num)
      (spherical_support_zero lam) t (by
      simpa only [mul_zero, zero_add] using hsmall)
  have hzero : modelToLp N lam f
      (ComplementaryKFinite.toModel lam (Finsupp.single 0 1)) = MaassQuotientL2.sourceLp N f := by
    change modelToLp N lam f (Finsupp.single 0 1) = MaassQuotientL2.sourceLp N f
    exact modelToLp_spherical N lam f
  simpa only [modelToLpComplementaryDiagonalOrbit, hzero] using h

/-- The genuine quotient-`L²` Maass source stays in the completed complementary-model image
under every nonnegative diagonal time. -/
theorem sourceLp_diagonal_mem_range_completedModelIsometry_of_nonneg
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (t : ℝ) (ht : 0 ≤ t) :
    integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
      (realPositiveDiagonalBorel (-t) : SL2R) (MaassQuotientL2.sourceLp N f) ∈
      Set.range (completedModelIsometry N lam f) := by
  have h := modelToLpComplementarySphericalOrbit_mem_range_completedModelIsometry_of_nonneg
    N lam f t ht
  have hzero : modelToLp N lam f
      (ComplementaryKFinite.toModel lam (Finsupp.single 0 1)) = MaassQuotientL2.sourceLp N f := by
    change modelToLp N lam f (Finsupp.single 0 1) = MaassQuotientL2.sourceLp N f
    exact modelToLp_spherical N lam f
  simpa only [modelToLpComplementaryDiagonalOrbit, hzero] using h

/-- The locally invariant finite raw model image transports to the normalized isometric image. -/
theorem integralSubgroupUnitary_modelIsometry_mem_range_completedModelIsometry_of_abs_lt
    (N : ℕ) (lam : SelbergExceptionalEigenvalue)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam.1)
    (v : ComplementaryKFinite lam) (r : ℝ) (hr : 0 ≤ r)
    (hsupp : ∀ m ∈ (ComplementaryKFinite.toModel lam v).support, |(m : ℝ)| ≤ r)
    (t : ℝ) (hsmall : |(2 * r + 2) * t| < 1) :
    integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
      (realPositiveDiagonalBorel (-t) : SL2R) (modelIsometry N lam f v) ∈
      Set.range (completedModelIsometry N lam f) := by
  rcases modelToLpComplementaryDiagonalOrbit_mem_range_completedModelIsometry_of_abs_lt
      N lam f v r hr hsupp t hsmall with ⟨w, hw⟩
  refine ⟨(‖modelToLp N lam f (Finsupp.single 0 1)‖ : ℂ)⁻¹ • w, ?_⟩
  change completedModelIsometry N lam f
      ((‖modelToLp N lam f (Finsupp.single 0 1)‖ : ℂ)⁻¹ • w) =
      integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1))
        (realPositiveDiagonalBorel (-t) : SL2R)
        ((‖modelToLp N lam f (Finsupp.single 0 1)‖ : ℂ)⁻¹ •
          modelToLp N lam f (ComplementaryKFinite.toModel lam v))
  rw [map_smul, map_smul, hw]
  rfl

end

end GaloisForLFunctions.RHTower
