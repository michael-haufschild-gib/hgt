import GaloisForLFunctions.HyperbolicArakelovTheory.TheFiniteDirichletSectionsRecoverTheHyperbolicGreenKernel
import GaloisForLFunctions.HyperbolicArakelovTheory.TheWeightedAdelicProductAdmitsStrictlyTemperedBarriers

/-!
# Uniform adelic decay across archimedean collisions

Strictly tempered positive product barriers control the square-root remainder
on finite Dirichlet sections and then on the full carrier. Between distinct
finite vertices the exponential's identity coefficient vanishes; the resulting
Green bound stays finite as the archimedean distance tends to zero.
-/

set_option autoImplicit false
noncomputable section
open Filter NormedSpace
open scoped Classical BigOperators Topology
namespace GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
open FullAdelic SurfaceOfSpecZ

/-- Finite restriction of a positive radial barrier, as an actual square-summable charge. -/
def finiteBarrierCharge (F : Finset FiniteVertices) (x : FiniteVertices) : ChargeSpace :=
  ∑ y ∈ F, lp.single 2 y (barrierProfile x y)

theorem finiteBarrierCharge_coord (F : Finset FiniteVertices) (x y : FiniteVertices) :
    finiteBarrierCharge F x y = if y ∈ F then barrierProfile x y else 0 := by
  simp only [finiteBarrierCharge, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single]

private theorem finiteBarrierCharge_nonneg (F : Finset FiniteVertices) (x y : FiniteVertices) :
    0 ≤ finiteBarrierCharge F x y := by
  rw [finiteBarrierCharge_coord]
  split_ifs
  · exact (barrierProfile_pos x y).le
  · exact le_rfl

private theorem finiteBarrierCharge_le (F : Finset FiniteVertices) (x y : FiniteVertices) :
    finiteBarrierCharge F x y ≤ barrierProfile x y := by
  rw [finiteBarrierCharge_coord]
  split_ifs
  · exact le_rfl
  · exact (barrierProfile_pos x y).le

private theorem projection_finiteBarrierCharge (F : Finset FiniteVertices) (x : FiniteVertices) :
    sectionProjection F (finiteBarrierCharge F x) = finiteBarrierCharge F x := by
  apply lp.ext
  funext y
  simp only [sectionProjection_coord, finiteBarrierCharge_coord]
  split_ifs <;> rfl

private theorem sectionProjection_nonneg (F : Finset FiniteVertices) (f : ChargeSpace)
    (hf : ∀ y, 0 ≤ f y) (y : FiniteVertices) : 0 ≤ sectionProjection F f y := by
  rw [sectionProjection_coord]
  split_ifs
  · exact hf y
  · exact le_rfl

private theorem sectionAdjacency_nonneg (F : Finset FiniteVertices) (f : ChargeSpace)
    (hf : ∀ y, 0 ≤ f y) (y : FiniteVertices) : 0 ≤ sectionAdjacency F f y :=
  sectionProjection_nonneg F _
    (adjacencyOperator_nonneg _ (sectionProjection_nonneg F f hf)) y

private theorem section_iterate_nonneg (F : Finset FiniteVertices) (n : ℕ)
    (f : ChargeSpace) (hf : ∀ y, 0 ≤ f y) (y : FiniteVertices) :
    0 ≤ ((sectionRootStep F)^[n] 0) f y := by
  induction n generalizing f y with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      change 0 ≤ (2 * rootScale)⁻¹ * (sectionAdjacency F f y +
        ((sectionRootStep F)^[n] 0) (((sectionRootStep F)^[n] 0) f) y)
      exact mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) rootScale_pos.le))
        (add_nonneg (sectionAdjacency_nonneg F f hf y)
          (ih _ (fun z => ih f hf z) y))

theorem sectionRemainder_nonneg (F : Finset FiniteVertices) (f : ChargeSpace)
    (hf : ∀ y, 0 ≤ f y) (y : FiniteVertices) : 0 ≤ sectionRemainder F f y := by
  have ht := ((ContinuousLinearMap.apply ℝ ChargeSpace f).continuous.tendsto
    (sectionRemainder F)).comp (tendsto_sectionRootStep_iterate F)
  have he := ((lp.lipschitzWith_one_eval 2 y).continuous.tendsto
    (sectionRemainder F f)).comp ht
  exact ge_of_tendsto he (Filter.Eventually.of_forall fun n => section_iterate_nonneg F n f hf y)

private theorem positive_operator_mono (T : ChargeOperator)
    (hT : ∀ f : ChargeSpace, (∀ y, 0 ≤ f y) → ∀ y, 0 ≤ T f y)
    (f g : ChargeSpace) (hfg : ∀ y, f y ≤ g y) (y : FiniteVertices) : T f y ≤ T g y := by
  have h := hT (g - f) (fun z => sub_nonneg.mpr (hfg z)) y
  rw [map_sub] at h
  exact sub_nonneg.mp h

private theorem sectionAdjacency_barrier_le (F : Finset FiniteVertices) (x y : FiniteVertices) :
    sectionAdjacency F (finiteBarrierCharge F x) y ≤ barrierEnergy * finiteBarrierCharge F x y := by
  change sectionProjection F (adjacencyOperator
    (sectionProjection F (finiteBarrierCharge F x))) y ≤ _
  rw [projection_finiteBarrierCharge, sectionProjection_coord, finiteBarrierCharge_coord]
  by_cases hy : y ∈ F
  · simp only [if_pos hy]
    rw [adjacencyOperator_apply]
    calc
      _ ≤ adjacency (barrierProfile x) y :=
        Summable.tsum_le_tsum (fun p => placeTerm_mono p (finiteBarrierCharge_le F x) y)
          (chargeSpace_inDomain (finiteBarrierCharge F x) y) (barrierProfile_inDomain x y)
      _ ≤ _ := adjacency_barrierProfile_le x y
  · simp only [if_neg hy, mul_zero, le_refl]

private theorem section_iterate_barrier_le (F : Finset FiniteVertices) (x : FiniteVertices)
    (n : ℕ) (y : FiniteVertices) :
    ((sectionRootStep F)^[n] 0) (finiteBarrierCharge F x) y ≤
      barrierRemainder * finiteBarrierCharge F x y := by
  induction n generalizing y with
  | zero => exact mul_nonneg barrierRemainder_pos.le (finiteBarrierCharge_nonneg F x y)
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have hm := positive_operator_mono ((sectionRootStep F)^[n] 0)
        (section_iterate_nonneg F n) (((sectionRootStep F)^[n] 0) (finiteBarrierCharge F x))
        (barrierRemainder • finiteBarrierCharge F x) ih y
      rw [map_smul] at hm
      change ((sectionRootStep F)^[n] 0) (((sectionRootStep F)^[n] 0)
        (finiteBarrierCharge F x)) y ≤
          barrierRemainder * (((sectionRootStep F)^[n] 0) (finiteBarrierCharge F x) y) at hm
      have hsq := hm.trans (mul_le_mul_of_nonneg_left (ih y) barrierRemainder_pos.le)
      change (2 * rootScale)⁻¹ * (sectionAdjacency F (finiteBarrierCharge F x) y +
        ((sectionRootStep F)^[n] 0) (((sectionRootStep F)^[n] 0) (finiteBarrierCharge F x)) y) ≤ _
      calc
        _ ≤ (2 * rootScale)⁻¹ * (barrierEnergy * finiteBarrierCharge F x y +
            barrierRemainder * (barrierRemainder * finiteBarrierCharge F x y)) :=
          mul_le_mul_of_nonneg_left (add_le_add (sectionAdjacency_barrier_le F x y) hsq)
            (inv_nonneg.mpr (mul_nonneg (by norm_num) rootScale_pos.le))
        _ = barrierRemainder * finiteBarrierCharge F x y := by
          have hi := congrArg (fun t : ℝ => t * finiteBarrierCharge F x y) barrierRemainder_identity
          field_simp [rootScale_pos.ne']
          nlinarith only [hi]

theorem sectionRemainder_barrier_le (F : Finset FiniteVertices) (x y : FiniteVertices) :
    sectionRemainder F (finiteBarrierCharge F x) y ≤
      barrierRemainder * finiteBarrierCharge F x y := by
  have ht := ((ContinuousLinearMap.apply ℝ ChargeSpace (finiteBarrierCharge F x)).continuous.tendsto
    (sectionRemainder F)).comp (tendsto_sectionRootStep_iterate F)
  have he := ((lp.lipschitzWith_one_eval 2 y).continuous.tendsto
    (sectionRemainder F (finiteBarrierCharge F x))).comp ht
  exact le_of_tendsto he (Filter.Eventually.of_forall fun n => section_iterate_barrier_le F x n y)

/-- The square-root remainder preserves the global positive barrier bound on actual charges. -/
theorem rootRemainder_charge_bound (x : FiniteVertices) (f : ChargeSpace)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ y, f y ≤ C * barrierProfile x y)
    (y : FiniteVertices) : rootRemainder f y ≤ C * barrierRemainder * barrierProfile x y := by
  have hfinite (F : Finset FiniteVertices) :
      sectionRemainder F f y ≤ C * barrierRemainder * barrierProfile x y := by
    have hp : ∀ z, sectionProjection F f z ≤ (C • finiteBarrierCharge F x) z := by
      intro z
      change sectionProjection F f z ≤ C * finiteBarrierCharge F x z
      rw [sectionProjection_coord, finiteBarrierCharge_coord]
      split_ifs
      · exact hb z
      · simp only [mul_zero, le_refl]
    have hm := positive_operator_mono (sectionRemainder F) (sectionRemainder_nonneg F)
      (sectionProjection F f) (C • finiteBarrierCharge F x) hp y
    have hs := congrArg (fun T : ChargeOperator => T f y) (sectionRemainder_supported F).2
    change sectionRemainder F (sectionProjection F f) y = sectionRemainder F f y at hs
    rw [map_smul] at hm
    change sectionRemainder F (sectionProjection F f) y ≤
      C * sectionRemainder F (finiteBarrierCharge F x) y at hm
    rw [hs] at hm
    calc
      _ ≤ C * (barrierRemainder * finiteBarrierCharge F x y) :=
        hm.trans (mul_le_mul_of_nonneg_left (sectionRemainder_barrier_le F x y) hC)
      _ ≤ C * barrierRemainder * barrierProfile x y := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_left (finiteBarrierCharge_le F x y)
          (mul_nonneg hC barrierRemainder_pos.le)
  have he := ((lp.lipschitzWith_one_eval 2 y).continuous.tendsto
    (rootRemainder f)).comp (tendsto_sectionRemainder f)
  exact le_of_tendsto he (Filter.Eventually.of_forall hfinite)

/-- Every power of the full remainder has the same strictly tempered radial envelope. -/
theorem remainder_power_entry_bound (n : ℕ) (x y : FiniteVertices) :
    0 ≤ (rootRemainder ^ n) (lp.single 2 x (1 : ℝ)) y ∧
      (rootRemainder ^ n) (lp.single 2 x (1 : ℝ)) y ≤
        barrierRemainder ^ n * barrierProfile x y := by
  induction n generalizing y with
  | zero =>
      simp only [pow_zero, one_apply_eq_self, one_mul]
      by_cases hy : y = x
      · subst y
        rw [lp.single_apply_self, barrierProfile_self]
        constructor <;> norm_num
      · rw [lp.single_apply_ne (E := fun _ : FiniteVertices => ℝ) 2 x 1 hy]
        exact ⟨le_rfl, (barrierProfile_pos x y).le⟩
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp]
      refine ⟨rootRemainder_nonneg _ (fun z => (ih z).1) y, ?_⟩
      have h := rootRemainder_charge_bound x ((rootRemainder ^ n) (lp.single 2 x (1 : ℝ)))
        (barrierRemainder ^ n) (pow_nonneg barrierRemainder_pos.le n) (fun z => (ih z).2) y
      simpa only [pow_succ, mul_assoc] using h

private def remainderSeries (r : ℝ) (x y : FiniteVertices) (n : ℕ) : ℝ :=
  (n.factorial : ℝ)⁻¹ * r ^ n * (rootRemainder ^ n) (lp.single 2 x (1 : ℝ)) y

private def barrierSeries (r : ℝ) (x y : FiniteVertices) (n : ℕ) : ℝ :=
  (n.factorial : ℝ)⁻¹ * (r * barrierRemainder) ^ n * barrierProfile x y

private theorem remainderSeries_nonneg {r : ℝ} (hr : 0 ≤ r)
    (x y : FiniteVertices) (n : ℕ) : 0 ≤ remainderSeries r x y n :=
  mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hr n))
    (remainder_power_entry_bound n x y).1

private theorem remainderSeries_le {r : ℝ} (hr : 0 ≤ r)
    (x y : FiniteVertices) (n : ℕ) : remainderSeries r x y n ≤ barrierSeries r x y n := by
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ * r ^ n * (barrierRemainder ^ n * barrierProfile x y) :=
      mul_le_mul_of_nonneg_left (remainder_power_entry_bound n x y).2
        (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (pow_nonneg hr n))
    _ = _ := by rw [barrierSeries, mul_pow]; ring

private theorem summable_barrierSeries (r : ℝ) (x y : FiniteVertices) :
    Summable (barrierSeries r x y) := by
  change Summable (fun n : ℕ =>
    (n.factorial : ℝ)⁻¹ * (r * barrierRemainder) ^ n * barrierProfile x y)
  simpa only [smul_eq_mul] using
    (expSeries_summable' (𝕂 := ℝ) (r * barrierRemainder)).mul_right (barrierProfile x y)

private theorem summable_remainderSeries {r : ℝ} (hr : 0 ≤ r) (x y : FiniteVertices) :
    Summable (remainderSeries r x y) :=
  Summable.of_nonneg_of_le (remainderSeries_nonneg hr x y) (remainderSeries_le hr x y)
    (summable_barrierSeries r x y)

private theorem remainder_exponential_entry (r : ℝ) (x y : FiniteVertices) :
    exp (r • rootRemainder) (lp.single 2 x (1 : ℝ)) y = ∑' n, remainderSeries r x y n := by
  let ev : ChargeOperator →L[ℝ] ℝ :=
    (lp.evalCLM ℝ (fun _ : FiniteVertices => ℝ) 2 y).comp
      (ContinuousLinearMap.apply ℝ ChargeSpace (lp.single 2 x (1 : ℝ)))
  rw [exp_eq_tsum ℝ]
  change ev (∑' n : ℕ, (n.factorial : ℝ)⁻¹ • (r • rootRemainder) ^ n) = _
  rw [ev.map_tsum (expSeries_summable' (𝕂 := ℝ) (r • rootRemainder))]
  apply tsum_congr
  intro n
  change ((n.factorial : ℝ)⁻¹ • (r • rootRemainder) ^ n) (lp.single 2 x (1 : ℝ)) y = _
  rw [smul_pow]
  change (n.factorial : ℝ)⁻¹ * (r ^ n * (rootRemainder ^ n) (lp.single 2 x (1 : ℝ)) y) = _
  unfold remainderSeries
  ring

private theorem tsum_barrierSeries (r : ℝ) (x y : FiniteVertices) :
    (∑' n, barrierSeries r x y n) = Real.exp (r * barrierRemainder) * barrierProfile x y := by
  unfold barrierSeries
  rw [tsum_mul_right, Real.exp_eq_exp_ℝ, exp_eq_tsum ℝ]
  rfl

/-- Distinct finite vertices have no identity contribution to the exponential kernel. -/
theorem remainder_exponential_off_diagonal_le {r : ℝ} (hr : 0 ≤ r)
    {x y : FiniteVertices} (hxy : x ≠ y) :
    exp (r • rootRemainder) (lp.single 2 x (1 : ℝ)) y ≤
      (Real.exp (r * barrierRemainder) - 1) * barrierProfile x y := by
  have hα := summable_remainderSeries hr x y
  have hβ := summable_barrierSeries r x y
  have hzero : remainderSeries r x y 0 = 0 := by
    simp only [remainderSeries, pow_zero, one_apply_eq_self,
      lp.single_apply_ne (E := fun _ : FiniteVertices => ℝ) 2 x 1 hxy.symm, mul_zero]
  have hβzero : barrierSeries r x y 0 = barrierProfile x y := by
    simp only [barrierSeries, Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_mul]
  have htail : (∑' n : ℕ, barrierSeries r x y (n + 1)) =
      (Real.exp (r * barrierRemainder) - 1) * barrierProfile x y := by
    have h := hβ.tsum_eq_zero_add
    rw [tsum_barrierSeries, hβzero] at h
    linarith only [h]
  rw [remainder_exponential_entry, hα.tsum_eq_zero_add, hzero, zero_add]
  calc
    _ ≤ ∑' n : ℕ, barrierSeries r x y (n + 1) :=
      Summable.tsum_le_tsum (fun n => remainderSeries_le hr x y (n + 1))
        (hα.comp_injective Nat.succ_injective) (hβ.comp_injective Nat.succ_injective)
    _ = _ := htail

private theorem exp_sub_one_le_mul_exp (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h₁ : 1 - t ≤ Real.exp (-t) := by
    have h := Real.add_one_le_exp (-t)
    linarith only [h]
  have h₂ : Real.exp t * (1 - t) ≤ 1 := by
    calc
      _ ≤ Real.exp t * Real.exp (-t) := mul_le_mul_of_nonneg_left h₁ (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  nlinarith only [h₂]

private theorem hyperbolic_barrier_scalar {r : ℝ} (hr : 0 < r) :
    Real.exp (-r * rootScale) * (Real.exp (r * barrierRemainder) - 1) /
        (4 * Real.pi * Real.sinh r) ≤ barrierRemainder / (4 * Real.pi) := by
  have hs : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hr
  have he : Real.exp (-r * rootScale + r * barrierRemainder) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have h := mul_le_mul_of_nonneg_left barrierRemainder_lt_scale.le hr.le
    linarith only [h]
  have hnum : Real.exp (-r * rootScale) * (Real.exp (r * barrierRemainder) - 1) ≤
      barrierRemainder * Real.sinh r := by
    calc
      _ ≤ Real.exp (-r * rootScale) * (r * barrierRemainder * Real.exp (r * barrierRemainder)) :=
        mul_le_mul_of_nonneg_left (exp_sub_one_le_mul_exp _) (Real.exp_pos _).le
      _ = (r * barrierRemainder) * Real.exp (-r * rootScale + r * barrierRemainder) := by
        rw [Real.exp_add]
        ring
      _ ≤ (r * barrierRemainder) * 1 :=
        mul_le_mul_of_nonneg_left he (mul_nonneg hr.le barrierRemainder_pos.le)
      _ ≤ barrierRemainder * Real.sinh r := by
        rw [mul_one, mul_comm r]
        exact mul_le_mul_of_nonneg_left (Real.self_le_sinh_iff.mpr hr.le) barrierRemainder_pos.le
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) Real.pi_pos) hs)).mpr
  calc
    _ ≤ barrierRemainder * Real.sinh r := hnum
    _ = barrierRemainder / (4 * Real.pi) * (4 * Real.pi * Real.sinh r) := by
      field_simp [Real.pi_ne_zero]

/-- Uniform decay in the finite adelic separation, independent of the positive archimedean distance. -/
theorem mixedGreenEntry_le_barrier {r : ℝ} (hr : 0 < r)
    {x y : FiniteVertices} (hxy : x ≠ y) :
    mixedGreenEntry r x y ≤ (barrierRemainder / (4 * Real.pi)) * barrierProfile x y := by
  have hg : 0 ≤ hyperbolicGreen 1 r := by
    unfold hyperbolicGreen
    exact div_nonneg (Real.exp_pos _).le
      (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) (Real.sinh_pos_iff.mpr hr).le)
  unfold mixedGreenEntry mixedGreen
  rw [hyperbolicEvolution_factor]
  change hyperbolicGreen 1 r * (Real.exp (-r * rootScale) *
    exp (r • rootRemainder) (lp.single 2 x (1 : ℝ)) y) ≤ _
  calc
    _ ≤ hyperbolicGreen 1 r * (Real.exp (-r * rootScale) *
        ((Real.exp (r * barrierRemainder) - 1) * barrierProfile x y)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (remainder_exponential_off_diagonal_le hr.le hxy) (Real.exp_pos _).le) hg
    _ = (Real.exp (-r * rootScale) * (Real.exp (r * barrierRemainder) - 1) /
        (4 * Real.pi * Real.sinh r)) * barrierProfile x y := by
      simp only [hyperbolicGreen, sub_self, neg_zero, zero_mul, Real.exp_zero]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (hyperbolic_barrier_scalar hr) (barrierProfile_pos x y).le

theorem mixedRobinEntry_le_barrier {x y : FiniteVertices} (hxy : x ≠ y) :
    mixedRobinEntry x y ≤ (barrierRemainder / (4 * Real.pi)) * barrierProfile x y := by
  rw [mixedRobinEntry_off_diagonal hxy]
  have hb := (remainder_power_entry_bound 1 x y).2
  simp only [pow_one] at hb
  calc
    _ ≤ (1 / (4 * Real.pi)) * (barrierRemainder * barrierProfile x y) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by ring

/-- The strictly tempered adelic bound persists through archimedean collisions. -/
theorem regularizedMixedEntry_bound {r : ℝ} (hr : 0 ≤ r)
    {x y : FiniteVertices} (hxy : x ≠ y) :
    0 ≤ regularizedMixedEntry r x y ∧
      regularizedMixedEntry r x y ≤ (barrierRemainder / (4 * Real.pi)) * barrierProfile x y := by
  by_cases hzero : r = 0
  · simp only [regularizedMixedEntry, if_pos hzero]
    exact ⟨mixedRobinEntry_off_diagonal_nonneg hxy, mixedRobinEntry_le_barrier hxy⟩
  · have hrpos : 0 < r := lt_of_le_of_ne hr (fun he => hzero he.symm)
    simp only [regularizedMixedEntry, if_neg hzero]
    exact ⟨mixedGreenEntry_nonneg hrpos x y, mixedGreenEntry_le_barrier hrpos hxy⟩

#print axioms sectionRemainder_nonneg
#print axioms sectionRemainder_barrier_le
#print axioms rootRemainder_charge_bound
#print axioms remainder_power_entry_bound
#print axioms remainder_exponential_off_diagonal_le
#print axioms regularizedMixedEntry_bound
end GaloisForLFunctions.HyperbolicArakelovTheory.WeightedAdelicGreen
