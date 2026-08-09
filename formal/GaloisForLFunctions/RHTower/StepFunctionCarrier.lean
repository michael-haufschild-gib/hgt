import GaloisForLFunctions.RHTower.BaezDuartePairingSeries

/-!
# The step-function subspace: the criterion is a discrete ℓ² problem

`BaezDuarteGramDiscrete` showed that `bdGenReal (1/m) v = (⌊v⌋ mod m)/(m·v)`, and `bdTargetFun v = 1/v`.
Both are of the shape

`stepFun s : v ↦ s(⌊v⌋)/v`  for a bounded sequence `s : ℕ → ℝ`,

the generator with `s n = (n mod m)/m` and the target with `s ≡ 1`.  This file develops that shape once.

The inner product of two step vectors is a weighted `ℓ²` inner product with the *rational* weights
`1/(n(n+1))`:

**`hasSum_stepGram` — `⟪stepFun s₁, stepFun s₂⟫ = ∑_{n≥1} s₁(n)·s₂(n)/(n(n+1))`.**

So the whole Nyman--Beurling problem transports to `ℓ²(ℕ≥1, 1/(n(n+1)))`: the target is the constant
sequence `1` (of norm `∑1/(n(n+1)) = 1`, matching `norm_bdTarget`), the generators are the sequences
`n ↦ (n mod m)/m`, and RH follows if the constant sequence lies in their closed span.  No integral, no
measure theory, no zeta function appears in that statement.

`hasSum_bdGram_discrete` and `hasSum_pairing_discrete` are the two instances of `hasSum_stepGram` obtained
by feeding it the modular sequences and the constant sequence; `bdGen_eq_stepVec` and `bdTarget_eq_stepVec`
identify the carrier elements.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace RHTower

/-- The step function attached to a sequence: `s(⌊v⌋)/v`. -/
def stepFun (s : ℕ → ℝ) : ℝ → ℂ := fun v => ((s ⌊v⌋₊ : ℝ) : ℂ) * ((v : ℂ))⁻¹

theorem norm_stepFun_le {s : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |s n| ≤ C) {v : ℝ} (hv : 0 < v) :
    ‖stepFun s v‖ ≤ C * v⁻¹ := by
  rw [stepFun, norm_mul, norm_inv, Complex.norm_real v, Real.norm_eq_abs, abs_of_pos hv,
    Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hb _) (by positivity)

theorem measurable_stepFun (s : ℕ → ℝ) : Measurable (stepFun s) := by
  refine Measurable.mul ?_ (Complex.measurable_ofReal.inv)
  exact Complex.measurable_ofReal.comp ((measurable_of_countable s).comp Nat.measurable_floor)

theorem memLp_stepFun {s : ℕ → ℝ} {C : ℝ} (hb : ∀ n, |s n| ≤ C) :
    MemLp (stepFun s) 2 bdMeasure := by
  have hC : 0 ≤ C := le_trans (abs_nonneg (s 0)) (hb 0)
  refine memLp_two_bdMeasure_of_sq_le (measurable_stepFun s).aestronglyMeasurable
    (C := C ^ 2) (b := -2) (by norm_num) ?_
  intro u hu
  have hu0 : (0 : ℝ) < u := lt_trans zero_lt_one (mem_Ioi.mp hu)
  calc ‖stepFun s u‖ ^ 2 ≤ (C * u⁻¹) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_stepFun_le hb hu0) 2
    _ = C ^ 2 * u ^ (-2 : ℝ) := by rw [mul_pow, inv_sq_eq_rpow hu0]

/-- The step vector in the carrier. -/
def stepVec (s : ℕ → ℝ) {C : ℝ} (hb : ∀ n, |s n| ≤ C) : BDCarrier := (memLp_stepFun hb).toLp _

/-- The weighted `ℓ²` pairing of two sequences, as an integral over the tail ray. -/
def stepGram (s₁ s₂ : ℕ → ℝ) : ℝ :=
  ∫ v in Ioi (1 : ℝ), s₁ ⌊v⌋₊ * s₂ ⌊v⌋₊ * (v⁻¹) ^ 2

theorem integrableOn_stepGramIntegrand {s₁ s₂ : ℕ → ℝ} {C₁ C₂ : ℝ}
    (hb₁ : ∀ n, |s₁ n| ≤ C₁) (hb₂ : ∀ n, |s₂ n| ≤ C₂) :
    IntegrableOn (fun v => s₁ ⌊v⌋₊ * s₂ ⌊v⌋₊ * (v⁻¹) ^ 2) (Ioi 1) := by
  have hmeas : Measurable (fun v : ℝ => s₁ ⌊v⌋₊ * s₂ ⌊v⌋₊ * (v⁻¹) ^ 2) := by
    refine Measurable.mul (Measurable.mul ?_ ?_) ((measurable_id.inv).pow_const 2)
    · exact (measurable_of_countable s₁).comp Nat.measurable_floor
    · exact (measurable_of_countable s₂).comp Nat.measurable_floor
  have hC₁ : 0 ≤ C₁ := le_trans (abs_nonneg (s₁ 0)) (hb₁ 0)
  have hC₂ : 0 ≤ C₂ := le_trans (abs_nonneg (s₂ 0)) (hb₂ 0)
  refine Integrable.mono' (g := fun v => (C₁ * C₂) * v ^ (-2 : ℝ))
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul (C₁ * C₂))
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (0 : ℝ) < v := lt_trans zero_lt_one (mem_Ioi.mp hv)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (v⁻¹) ^ 2),
    ← inv_sq_eq_rpow hv0]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul (hb₁ _) (hb₂ _) (abs_nonneg _) hC₁

theorem integral_tailCell_stepGramIntegrand (s₁ s₂ : ℕ → ℝ) (n : ℕ) :
    (∫ v in tailCell n, s₁ ⌊v⌋₊ * s₂ ⌊v⌋₊ * (v⁻¹) ^ 2)
      = s₁ (n + 1) * s₂ (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  set a : ℕ := n + 1 with ha
  have haR : ((a : ℕ) : ℝ) = (n : ℝ) + 1 := by rw [ha]; push_cast; ring
  have hcell : tailCell n = Ioc ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1) := by
    rw [tailCell, haR, show ((n : ℝ) + 2) = ((n : ℝ) + 1) + 1 from by ring]
  have hcongr : ∀ v ∈ Ioo ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1),
      s₁ ⌊v⌋₊ * s₂ ⌊v⌋₊ * (v⁻¹) ^ 2 = (s₁ a * s₂ a) * (v⁻¹) ^ 2 := by
    intro v hv
    have hfl : ⌊v⌋₊ = a := by
      refine Nat.floor_eq_iff (le_trans (Nat.cast_nonneg a) hv.1.le) |>.mpr ⟨hv.1.le, ?_⟩
      exact hv.2
    rw [hfl]
  have hpos : (0 : ℝ) < ((a : ℕ) : ℝ) := by rw [haR]; positivity
  have hle : ((a : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) + 1 := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1) := by
    rw [Set.uIcc_of_le hle, Set.mem_Icc]
    intro h
    linarith [h.1]
  have hsq : (∫ v in ((a : ℕ) : ℝ)..(((a : ℕ) : ℝ) + 1), (v⁻¹) ^ 2)
      = 1 / ((a : ℕ) : ℝ) - 1 / (((a : ℕ) : ℝ) + 1) := by
    have hcongr2 : ∀ v ∈ Set.uIcc ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1), (v⁻¹) ^ 2 = v ^ (-2 : ℤ) := by
      intro v _
      rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from by norm_num, zpow_neg, zpow_natCast, ← inv_pow]
    rw [intervalIntegral.integral_congr hcongr2, integral_zpow (Or.inr ⟨by norm_num, hzero⟩)]
    have hane : ((a : ℕ) : ℝ) ≠ 0 := ne_of_gt hpos
    have hane1 : ((a : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  rw [hcell, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hcongr,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_const_mul, hsq]
  have hane : ((a : ℕ) : ℝ) ≠ 0 := ne_of_gt hpos
  rw [haR] at hane ⊢
  field_simp
  ring

/-- **The step pairing is a weighted `ℓ²` inner product with rational weights.** -/
theorem hasSum_stepGram {s₁ s₂ : ℕ → ℝ} {C₁ C₂ : ℝ}
    (hb₁ : ∀ n, |s₁ n| ≤ C₁) (hb₂ : ∀ n, |s₂ n| ≤ C₂) :
    HasSum (fun n : ℕ => s₁ (n + 1) * s₂ (n + 1) / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (stepGram s₁ s₂) := by
  have hint : IntegrableOn (fun v => s₁ ⌊v⌋₊ * s₂ ⌊v⌋₊ * (v⁻¹) ^ 2) (⋃ n : ℕ, tailCell n) := by
    rw [iUnion_tailCell]
    exact integrableOn_stepGramIntegrand hb₁ hb₂
  have h := MeasureTheory.hasSum_integral_iUnion measurableSet_tailCell
    pairwise_disjoint_tailCell hint
  rw [iUnion_tailCell] at h
  rw [stepGram]
  exact (funext (fun n => integral_tailCell_stepGramIntegrand s₁ s₂ n)) ▸ h

/-- The carrier inner product of two step vectors is the step pairing. -/
theorem inner_stepVec {s₁ s₂ : ℕ → ℝ} {C₁ C₂ : ℝ}
    (hb₁ : ∀ n, |s₁ n| ≤ C₁) (hb₂ : ∀ n, |s₂ n| ≤ C₂) :
    inner ℂ (stepVec s₁ hb₁) (stepVec s₂ hb₂) = ((stepGram s₁ s₂ : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, stepGram, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_stepFun hb₁).coeFn_toLp, (memLp_stepFun hb₂).coeFn_toLp,
    ae_restrict_mem measurableSet_Ioi] with v hu1 hu2 hv
  have hv0 : (0 : ℝ) < v := lt_trans zero_lt_one (mem_Ioi.mp hv)
  have hvne : (v : ℝ) ≠ 0 := ne_of_gt hv0
  have hs : ∀ s : ℕ → ℝ, stepFun s v = ((s ⌊v⌋₊ * v⁻¹ : ℝ) : ℂ) := by
    intro s
    rw [stepFun, Complex.ofReal_mul, Complex.ofReal_inv]
  rw [stepVec, stepVec, hu1, hu2, hs, hs, RCLike.inner_apply, Complex.conj_ofReal,
    ← Complex.ofReal_mul]
  congr 1
  field_simp

/-! ## The Báez-Duarte data as step vectors -/

theorem abs_modSeq_le (m : ℕ) (n : ℕ) : |((n % m : ℕ) : ℝ) / (m : ℝ)| ≤ 1 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · simp [hm]
  · have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hlt : ((n % m : ℕ) : ℝ) < (m : ℝ) := by
      have := Nat.mod_lt n hm
      exact_mod_cast this
    rw [abs_div, abs_of_pos hm0, abs_of_nonneg (Nat.cast_nonneg _), div_le_one hm0]
    exact hlt.le

theorem abs_one_le (_n : ℕ) : |(1 : ℝ)| ≤ 1 := by norm_num

/-- Almost every point of the tail ray is not an integer. -/
theorem ae_not_mem_range_natCast :
    ∀ᵐ v ∂bdMeasure, v ∉ Set.range (fun n : ℕ => (n : ℝ)) := by
  refine ae_restrict_of_ae ?_
  have h : (volume (Set.range (fun n : ℕ => (n : ℝ)))) = 0 :=
    (Set.countable_range (fun n : ℕ => (n : ℝ))).measure_zero volume
  rw [Filter.eventually_iff, mem_ae_iff]
  convert h using 2
  ext x
  simp

/-- **The generator is a step vector**, with the modular sequence. -/
theorem bdGen_eq_stepVec {m : ℕ} (hm : 1 ≤ m) :
    bdGen (1 / (m : ℝ)) = stepVec (fun n => ((n % m : ℕ) : ℝ) / (m : ℝ)) (abs_modSeq_le m) := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [(memLp_bdGenFun (1 / (m : ℝ))).coeFn_toLp,
    (memLp_stepFun (abs_modSeq_le m)).coeFn_toLp, ae_restrict_mem measurableSet_Ioi,
    ae_not_mem_range_natCast] with v h1 h2 hv hnint
  have hv1 : (1 : ℝ) < v := mem_Ioi.mp hv
  have hv0 : (0 : ℝ) < v := lt_trans zero_lt_one hv1
  set a : ℕ := ⌊v⌋₊ with ha
  have hfl : (a : ℝ) ≤ v := Nat.floor_le hv0.le
  have hfl2 : v < (a : ℝ) + 1 := Nat.lt_floor_add_one v
  have hEq : v ≠ (a : ℝ) := by
    intro h
    exact hnint ⟨a, h.symm⟩
  have hmem : v ∈ Ioo ((a : ℝ)) ((a : ℝ) + 1) := ⟨lt_of_le_of_ne hfl (Ne.symm hEq), hfl2⟩
  have hstep := bdGenReal_inv_nat_eq_of_mem_cell hm hmem
  have hcast : bdGenFun (1 / (m : ℝ)) v = ((bdGenReal (1 / (m : ℝ)) v : ℝ) : ℂ) :=
    bdGenFun_eq_ofReal _ v
  rw [bdGen, stepVec, h1, h2, stepFun, hcast, hstep]
  push_cast
  field_simp
  ring

/-- **The target is the constant step vector.** -/
theorem bdTarget_eq_stepVec :
    bdTarget = stepVec (fun _ => (1 : ℝ)) abs_one_le := by
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [memLp_bdTargetFun.coeFn_toLp, (memLp_stepFun abs_one_le).coeFn_toLp] with v h1 h2
  rw [bdTarget, stepVec, h1, h2, stepFun, bdTargetFun]
  norm_num

/-- The generators of the criterion's own system, as step vectors. -/
theorem bdGen_bdDiscrete_eq_stepVec (i : ℕ) :
    bdGen (bdDiscrete i)
      = stepVec (fun n => ((n % (i + 1) : ℕ) : ℝ) / (((i + 1 : ℕ)) : ℝ))
          (abs_modSeq_le (i + 1)) := by
  have hi : bdDiscrete i = 1 / (((i + 1 : ℕ) : ℝ)) := by
    rw [bdDiscrete]
    push_cast
    ring
  rw [hi]
  exact bdGen_eq_stepVec (by omega)

/-- **The Nyman--Beurling criterion in the discrete carrier.**  If the constant sequence `1` lies in the
closed span of the modular sequences `n ↦ (n mod m)/m` inside `ℓ²(ℕ≥1, 1/(n(n+1)))` — transported here as
step vectors — then the Riemann hypothesis holds.  No integral and no zeta function occurs in the
hypothesis. -/
theorem riemannHypothesis_of_constStep_mem_closedSpan
    (h : stepVec (fun _ => (1 : ℝ)) abs_one_le ∈
      (Submodule.span ℂ (Set.range (fun i : ℕ =>
        stepVec (fun n => ((n % (i + 1) : ℕ) : ℝ) / (((i + 1 : ℕ)) : ℝ))
          (abs_modSeq_le (i + 1))))).topologicalClosure) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_bdTarget_mem_closedSpan_discrete ?_
  rw [bdTarget_eq_stepVec]
  have hrange : (fun i : ℕ => bdGen (bdDiscrete i))
      = fun i : ℕ => stepVec (fun n => ((n % (i + 1) : ℕ) : ℝ) / (((i + 1 : ℕ)) : ℝ))
          (abs_modSeq_le (i + 1)) := funext bdGen_bdDiscrete_eq_stepVec
  rw [hrange]
  exact h

end RHTower

end
