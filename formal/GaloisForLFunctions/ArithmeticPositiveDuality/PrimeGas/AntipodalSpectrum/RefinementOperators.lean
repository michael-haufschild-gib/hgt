import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.RefinementTail
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.ProjectionLimit
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier

/-!
# Strong and heat-weighted norm convergence of refined projections

A fixed wave has vanishing mass in the shrinking remainder. The lowest
remaining occupation attains the largest thermal multiplier, including
at zero inverse temperature where the projection error has norm one.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

open SampledClocks CopyExchange DyadicAperture.Binary Filter
open scoped Classical Topology

def projectionRemainder (t : ExceptionalTime) (j : ℕ) :=
  project (saturated t) - project (rejected (refined t j).val)

theorem remainder_apply (t : ExceptionalTime) (j : ℕ) (f : LabelSpace Word) (x : Word) :
    projectionRemainder t j f x = if remainder t j x then f x else 0 := by
  change ({y | saturated t y} : Set Word).indicator (fun y => f y) x -
    ({y | rejected (refined t j).val y} : Set Word).indicator (fun y => f y) x = _
  simp only [Set.indicator_apply,Set.mem_setOf_eq]
  by_cases hj : rejected (refined t j).val x
  · simp [hj,show saturated t x from ⟨j,hj⟩,remainder]
  · simp [hj,remainder]

private theorem eventual_remainder_empty (t : ExceptionalTime) (x : Word) :
    ∀ᶠ j : ℕ in atTop, ¬remainder t j x := by
  by_cases h : saturated t x
  · obtain ⟨i,hi⟩ := h
    have hm : Monotone (fun j : ℕ => {y : Word | rejected (refined t j).val y}) :=
      monotone_nat_of_le_succ (fun j y hy => half_inclusion _ y hy)
    exact (eventually_ge_atTop i).mono fun j hj hr => hr.2 (hm hj hi)
  · exact Eventually.of_forall fun _ hr => h hr.1

theorem refined_projection_strong (t : ExceptionalTime) (f : LabelSpace Word) :
    Tendsto (fun j => project (rejected (refined t j).val) f) atTop (𝓝 (project (saturated t) f)) := by
  let T := projectionRemainder t
  have hs : Tendsto (fun j => ‖T j f‖^2) atTop (𝓝 0) := by
    simp_rw [HilbertSchmidt.lp_norm_sq_eq]
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
      (f := fun j x => ‖T j f x‖^2) (g := fun _ => (0:ℝ)) (HilbertSchmidt.summable_coe_sq f)
      (fun x => ?_) ?_
    · simpa only [tsum_zero] using h
    · apply tendsto_const_nhds.congr'
      filter_upwards [eventual_remainder_empty t x] with j hj
      simp only [T,remainder_apply,if_neg hj,norm_zero,zero_pow (two_ne_zero : (2:ℕ) ≠ 0)]
    · refine Eventually.of_forall fun j x => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      change ‖projectionRemainder t j f x‖^2 ≤ ‖f x‖^2
      rw [remainder_apply]
      split_ifs
      · exact le_rfl
      · simpa only [norm_zero,zero_pow (two_ne_zero : (2:ℕ) ≠ 0)] using sq_nonneg ‖f x‖
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h := (Real.continuous_sqrt.tendsto 0).comp hs
  simp only [Real.sqrt_zero] at h
  exact h.congr fun j => (Real.sqrt_sq (norm_nonneg (T j f))).trans (norm_sub_rev _ _)

abbrev ClosedHeatPlane := {s : ℂ // 0 ≤ s.re}

private theorem heat_antitone (s : ClosedHeatPlane) {a b : ℕ+} (h : a ≤ b) :
    ‖heat s.val b‖ ≤ ‖heat s.val a‖ := by
  rw [norm_heat,norm_heat]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (Real.log_le_log (Nat.cast_pos.mpr a.pos)
    (by exact_mod_cast h : (a.val:ℝ) ≤ b.val)) (neg_nonpos.mpr s.property))

private theorem word_norm_le_one (s : ClosedHeatPlane) (x : Word) : ‖wordHeat s.val x‖ ≤ 1 := by
  rw [wordHeat_total]
  exact (heat_antitone s (a := 1) (b := ∏ i, x i) (∏ i, x i).pos).trans_eq (by simp [heat,energy])

/-- Bounded heat on the full two-copy Hilbert space, including imaginary time. -/
def twoCopyHeat (s : ClosedHeatPlane) : LabelSpace Word →L[ℂ] LabelSpace Word :=
  lpDiagonalCLM (wordHeat s.val) zero_le_one (word_norm_le_one s)

def dampedRemainder (t : ExceptionalTime) (j : ℕ) (s : ClosedHeatPlane) :=
  projectionRemainder t j ∘L twoCopyHeat s

def tailMultiplier (t : ExceptionalTime) (j : ℕ) (s : ℂ) (x : Word) :=
  if remainder t j x then wordHeat s x else 0

theorem tail_bound (t : ExceptionalTime) (j : ℕ) (s : ClosedHeatPlane) (x : Word) :
    ‖tailMultiplier t j s.val x‖ ≤ ‖heat s.val ((block t)^(windingOrder (refined t j)))‖ := by
  unfold tailMultiplier
  split_ifs with hx
  · rw [wordHeat_total,Fintype.prod_bool]
    exact heat_antitone s ((remainder_least_product t j).2 ⟨x,hx,mul_comm _ _⟩)
  · simpa only [norm_zero] using norm_nonneg _

theorem damped_diagonal (t : ExceptionalTime) (j : ℕ) (s : ClosedHeatPlane) :
    dampedRemainder t j s = lpDiagonalCLM (tailMultiplier t j s.val) (norm_nonneg _) (tail_bound t j s) := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  change projectionRemainder t j (twoCopyHeat s f) x = tailMultiplier t j s.val x*f x
  rw [remainder_apply]
  by_cases hx : remainder t j x <;> simp [tailMultiplier,hx,twoCopyHeat]

/-- The least omitted shell attains the operator norm of the heat-weighted projection error. -/
theorem damped_norm (t : ExceptionalTime) (j : ℕ) (s : ClosedHeatPlane) :
    ‖dampedRemainder t j s‖ = ‖heat s.val (block t)‖^(2^j*windingOrder t) := by
  let H := block t
  let M := windingOrder (refined t j)
  have h : ‖dampedRemainder t j s‖ = ‖heat s.val (H^M)‖ := by
    rw [damped_diagonal]
    apply le_antisymm (norm_lpDiagonalCLM_le _ _ _)
    obtain ⟨x,hx,hp⟩ := (remainder_least_product t j).1
    let c := tailMultiplier t j s.val
    let A := lpDiagonalCLM c (norm_nonneg _) (tail_bound t j s)
    have hl := A.le_opNorm (lp.single 2 x (1:ℂ))
    rw [lpDiagonalCLM_single,lp.norm_single (by norm_num),lp.norm_single (by norm_num),norm_one,mul_one] at hl
    have hp' := (mul_comm (x true) (x false)).trans hp
    simpa only [c,tailMultiplier,if_pos hx,wordHeat_total,Fintype.prod_bool,hp'] using hl
  rw [h,norm_heat,norm_heat]
  simp only [energy,PNat.pow_coe,Nat.cast_pow,Real.log_pow]
  rw [← Real.exp_nat_mul,(refined_parameters t j).2.2.symm]
  congr 1
  ring

theorem bare_projection_norm (t : ExceptionalTime) (j : ℕ) : ‖projectionRemainder t j‖ = 1 := by
  let s : ClosedHeatPlane := ⟨0,by simp⟩
  have he : twoCopyHeat s = ContinuousLinearMap.id ℂ (LabelSpace Word) := by
    ext f x
    change wordHeat 0 x*f x = f x
    simp [wordHeat,heat]
  have h := damped_norm t j s
  simpa only [dampedRemainder,he,ContinuousLinearMap.comp_id,s,heat,neg_zero,zero_mul,Complex.exp_zero,norm_one,one_pow] using h

theorem damped_norm_converges_iff (t : ExceptionalTime) (s : ClosedHeatPlane) :
    Tendsto (fun j => ‖dampedRemainder t j s‖) atTop (𝓝 0) ↔ 0 < s.val.re := by
  simp only [damped_norm]
  constructor
  · intro h
    by_contra! hn
    have he := le_antisymm hn s.property
    simp only [norm_heat,he,neg_zero,zero_mul,Real.exp_zero,one_pow] at h
    exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h)
  · intro hs
    apply (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (heat_contraction _ (block_nontrivial t) _ hs)).comp
    apply tendsto_atTop_mono (fun _ => Nat.le_mul_of_pos_right _ (Nat.zero_lt_one.trans (order_nontrivial t)))
    exact tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2:ℕ))

#print axioms refined_projection_strong
#print axioms bare_projection_norm
#print axioms damped_norm
#print axioms damped_norm_converges_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
