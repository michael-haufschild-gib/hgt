import GaloisForLFunctions.HTGeometry.PoissonOccupancyHistorySplit

/-!
# Superposition saturation and hidden-history action density

Independent superposition of `m` copies of a Poisson formation of rate `x` gives rate `mx`.  This
module proves that under repeated superposition the Boolean occupancy report saturates and its
information vanishes, that the vertical history action grows linearly with asymptotic density
equal to the one-copy Poisson Jeffreys information, that the excess-count history escapes every
finite window, and that bounded orbit action along any geometric depth schedule is equivalent to
equality of the two rates.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal

noncomputable section

/-! ## Formation depth -/

/-- One-copy Poisson Jeffreys information of two formation rates. -/
def rateJeffreys (α β : ℝ≥0) : ℝ := ((α : ℝ) - (β : ℝ)) * Real.log ((α : ℝ) / (β : ℝ))

/-- Boolean occupancy work at superposition depth `m`. -/
def formationBooleanWork (α β : ℝ≥0) (m : ℕ) : ℝ :=
  booleanOccupancyJeffreys ((m : ℝ≥0) * α) ((m : ℝ≥0) * β)

/-- Vertical history action at superposition depth `m`. -/
def formationHistoryWork (α β : ℝ≥0) (m : ℕ) : ℝ :=
  hiddenHistoryWork ((m : ℝ≥0) * α) ((m : ℝ≥0) * β)

theorem depthRate_pos {α : ℝ≥0} (hα : 0 < α) {m : ℕ} (hm : 0 < m) : 0 < (m : ℝ≥0) * α :=
  mul_pos (by exact_mod_cast hm) hα

theorem coe_depthRate (α : ℝ≥0) (m : ℕ) : (((m : ℝ≥0) * α : ℝ≥0) : ℝ) = (m : ℝ) * (α : ℝ) := by
  push_cast
  ring

/-- **Extensive formation conservation** at every superposition depth. -/
theorem formation_conservation {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) {m : ℕ} (hm : 0 < m) :
    (m : ℝ) * rateJeffreys α β = formationBooleanWork α β m + formationHistoryWork α β m := by
  have hma := depthRate_pos hα hm
  have hmb := depthRate_pos hβ hm
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hβ' : (β : ℝ) ≠ 0 := ne_of_gt (show (0:ℝ) < (β : ℝ) from hβ)
  rw [formationBooleanWork, formationHistoryWork,
    ← poissonJeffreys_eq_boolean_add_hidden hma hmb, poissonJeffreys_eq hma hmb, rateJeffreys,
    coe_depthRate, coe_depthRate,
    show (m : ℝ) * (α : ℝ) / ((m : ℝ) * (β : ℝ)) = (α : ℝ) / (β : ℝ) from by field_simp]
  ring

theorem formationBooleanWork_nonneg (α β : ℝ≥0) (m : ℕ) : 0 ≤ formationBooleanWork α β m :=
  booleanOccupancyJeffreys_nonneg _ _

theorem formationHistoryWork_nonneg (α β : ℝ≥0) (m : ℕ) : 0 ≤ formationHistoryWork α β m :=
  hiddenHistoryWork_nonneg _ _

theorem rateJeffreys_nonneg {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) : 0 ≤ rateJeffreys α β := by
  have h := formation_conservation hα hβ (m := 1) one_pos
  have h1 := formationBooleanWork_nonneg α β 1
  have h2 := formationHistoryWork_nonneg α β 1
  simp only [Nat.cast_one, one_mul] at h
  linarith

theorem rateJeffreys_pos_of_ne {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) (hne : α ≠ β) :
    0 < rateJeffreys α β := by
  have hα' : (0 : ℝ) < (α : ℝ) := hα
  have hβ' : (0 : ℝ) < (β : ℝ) := hβ
  have hne' : (α : ℝ) ≠ (β : ℝ) := fun h => hne (NNReal.coe_injective h)
  rcases lt_or_gt_of_ne hne' with h | h
  · have hlog : Real.log ((α : ℝ) / (β : ℝ)) < 0 :=
      Real.log_neg (by positivity) ((div_lt_one hβ').2 h)
    have : (α : ℝ) - (β : ℝ) < 0 := by linarith
    exact mul_pos_of_neg_of_neg this hlog
  · have hlog : 0 < Real.log ((α : ℝ) / (β : ℝ)) :=
      Real.log_pos ((one_lt_div hβ').2 h)
    have : (0 : ℝ) < (α : ℝ) - (β : ℝ) := by linarith
    exact mul_pos this hlog

theorem rateJeffreys_eq_zero_iff {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) :
    rateJeffreys α β = 0 ↔ α = β := by
  constructor
  · intro h
    by_contra hne
    exact absurd h (rateJeffreys_pos_of_ne hα hβ hne).ne'
  · rintro rfl
    simp [rateJeffreys]

/-! ## Boolean saturation -/

theorem tendsto_expNegDepth {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => Real.exp (-((m : ℝ) * c))) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
  exact Filter.Tendsto.atTop_mul_const hc tendsto_natCast_atTop_atTop

theorem tendsto_natMul_expNegDepth {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => (m : ℝ) * Real.exp (-((m : ℝ) * c))) atTop (𝓝 0) := by
  have hscale : Tendsto (fun m : ℕ => (m : ℝ) * c) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hc tendsto_natCast_atTop_atTop
  have hbase : Tendsto (fun m : ℕ => ((m : ℝ) * c) ^ 1 * Real.exp (-((m : ℝ) * c))) atTop (𝓝 0) :=
    (tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hscale
  have hmul := hbase.const_mul c⁻¹
  rw [mul_zero] at hmul
  refine hmul.congr fun m => ?_
  rw [pow_one]
  field_simp

/-- **Observer saturation.**  Boolean occupancy of a superposed Poisson formation tends to one. -/
theorem tendsto_poissonOccupancy_depth {α : ℝ≥0} (hα : 0 < α) :
    Tendsto (fun m : ℕ => (poissonOccupancyUnit ((m : ℝ≥0) * α) : ℝ)) atTop (𝓝 1) := by
  have hα' : (0 : ℝ) < (α : ℝ) := hα
  have h := tendsto_expNegDepth hα'
  have hrw : ∀ m : ℕ, (poissonOccupancyUnit ((m : ℝ≥0) * α) : ℝ)
      = 1 - Real.exp (-((m : ℝ) * (α : ℝ))) := by
    intro m
    rw [coe_poissonOccupancyUnit, coe_depthRate]
  simpa [hrw] using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub h

theorem formationBooleanWork_symm (α β : ℝ≥0) (m : ℕ) :
    formationBooleanWork α β m = formationBooleanWork β α m :=
  booleanOccupancyJeffreys_symm _ _

theorem formationHistoryWork_symm (α β : ℝ≥0) (m : ℕ) :
    formationHistoryWork α β m = formationHistoryWork β α m :=
  hiddenHistoryWork_symm _ _

/-- **Exact Boolean occupancy work at superposition depth `m`.** -/
theorem formationBooleanWork_eq {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) {m : ℕ} (hm : 0 < m) :
    formationBooleanWork α β m
      = (Real.exp (-((m : ℝ) * (β : ℝ))) - Real.exp (-((m : ℝ) * (α : ℝ)))) *
        Real.log ((Real.exp ((m : ℝ) * (α : ℝ)) - 1) /
          (Real.exp ((m : ℝ) * (β : ℝ)) - 1)) := by
  rw [formationBooleanWork,
    booleanOccupancyJeffreys_eq (depthRate_pos hα hm) (depthRate_pos hβ hm),
    coe_depthRate, coe_depthRate]

/-- The Stirling-free split of the reflected occupancy logarithm. -/
theorem log_expSub_ratio_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log ((Real.exp a - 1) / (Real.exp b - 1))
      = (a - b) + Real.log ((1 - Real.exp (-a)) / (1 - Real.exp (-b))) := by
  have hea := exp_sub_one_pos ha
  have heb := exp_sub_one_pos hb
  have hexpa := Real.exp_pos a
  have hexpb := Real.exp_pos b
  have hna : 1 - Real.exp (-a) = (Real.exp a - 1) / Real.exp a := by
    rw [Real.exp_neg]
    field_simp
  have hnb : 1 - Real.exp (-b) = (Real.exp b - 1) / Real.exp b := by
    rw [Real.exp_neg]
    field_simp
  have hsplit : (Real.exp a - 1) / (Real.exp b - 1)
      = Real.exp (a - b) * ((1 - Real.exp (-a)) / (1 - Real.exp (-b))) := by
    rw [hna, hnb, Real.exp_sub]
    field_simp
  rw [hsplit, Real.log_mul (Real.exp_ne_zero _) (by
    rw [hna, hnb]
    positivity), Real.log_exp]

/-- **Sharp Boolean saturation rate.**  For distinct rates the occupancy work is asymptotically
`m(a-b)e^{-mb}` with `a` the larger and `b` the smaller rate. -/
theorem isEquivalent_formationBooleanWork {α β : ℝ≥0} (hβ : 0 < β) (hlt : β < α) :
    Asymptotics.IsEquivalent atTop (fun m : ℕ => formationBooleanWork α β m)
      (fun m : ℕ => (m : ℝ) * ((α : ℝ) - (β : ℝ)) * Real.exp (-((m : ℝ) * (β : ℝ)))) := by
  have hα : 0 < α := lt_trans hβ hlt
  have hα' : (0 : ℝ) < (α : ℝ) := hα
  have hβ' : (0 : ℝ) < (β : ℝ) := hβ
  have hgap : (0 : ℝ) < (α : ℝ) - (β : ℝ) := by
    have : (β : ℝ) < (α : ℝ) := hlt
    linarith
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have hquot : ((fun m : ℕ => formationBooleanWork α β m) /
        fun m : ℕ => (m : ℝ) * ((α : ℝ) - (β : ℝ)) * Real.exp (-((m : ℝ) * (β : ℝ))))
        =ᶠ[atTop] fun m : ℕ => (1 - Real.exp (-((m : ℝ) * ((α : ℝ) - (β : ℝ))))) *
          (1 + Real.log ((1 - Real.exp (-((m : ℝ) * (α : ℝ)))) /
              (1 - Real.exp (-((m : ℝ) * (β : ℝ))))) / ((m : ℝ) * ((α : ℝ) - (β : ℝ)))) := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hma : (0 : ℝ) < (m : ℝ) * (α : ℝ) := by positivity
    have hmb : (0 : ℝ) < (m : ℝ) * (β : ℝ) := by positivity
    simp only [Pi.div_def]
    rw [formationBooleanWork_eq hα hβ hm, log_expSub_ratio_eq hma hmb]
    have hexp : Real.exp (-((m : ℝ) * (β : ℝ))) - Real.exp (-((m : ℝ) * (α : ℝ)))
        = Real.exp (-((m : ℝ) * (β : ℝ))) *
          (1 - Real.exp (-((m : ℝ) * ((α : ℝ) - (β : ℝ))))) := by
      rw [mul_sub, mul_one, ← Real.exp_add]
      congr 2
      ring
    have hgapm : (m : ℝ) * (α : ℝ) - (m : ℝ) * (β : ℝ) = (m : ℝ) * ((α : ℝ) - (β : ℝ)) := by
      ring
    rw [hexp, hgapm]
    have hne : ((m : ℝ) * ((α : ℝ) - (β : ℝ))) ≠ 0 := by positivity
    have hene : Real.exp (-((m : ℝ) * (β : ℝ))) ≠ 0 := Real.exp_ne_zero _
    field_simp
  refine Filter.Tendsto.congr' hquot.symm ?_
  have h1 : Tendsto (fun m : ℕ => 1 - Real.exp (-((m : ℝ) * ((α : ℝ) - (β : ℝ)))))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub
      (tendsto_expNegDepth hgap)
  have hnumα : Tendsto (fun m : ℕ => 1 - Real.exp (-((m : ℝ) * (α : ℝ)))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub
      (tendsto_expNegDepth hα')
  have hnumβ : Tendsto (fun m : ℕ => 1 - Real.exp (-((m : ℝ) * (β : ℝ)))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub
      (tendsto_expNegDepth hβ')
  have hdiv : Tendsto (fun m : ℕ => (1 - Real.exp (-((m : ℝ) * (α : ℝ)))) /
      (1 - Real.exp (-((m : ℝ) * (β : ℝ))))) atTop (𝓝 1) := by
    have h := hnumα.div hnumβ one_ne_zero
    simpa [Pi.div_def] using h
  have hlog : Tendsto (fun m : ℕ => Real.log ((1 - Real.exp (-((m : ℝ) * (α : ℝ)))) /
      (1 - Real.exp (-((m : ℝ) * (β : ℝ)))))) atTop (𝓝 0) := by
    have h := (Real.continuousAt_log one_ne_zero).tendsto.comp hdiv
    simpa [Function.comp_def] using h
  have h2 : Tendsto (fun m : ℕ => 1 + Real.log ((1 - Real.exp (-((m : ℝ) * (α : ℝ)))) /
      (1 - Real.exp (-((m : ℝ) * (β : ℝ))))) / ((m : ℝ) * ((α : ℝ) - (β : ℝ)))) atTop (𝓝 1) := by
    have hmul := hlog.div_atTop
      (Filter.Tendsto.atTop_mul_const hgap tendsto_natCast_atTop_atTop)
    have hsum := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).add hmul
    simpa using hsum
  simpa using h1.mul h2

/-- **Boolean observation saturates.**  Occupancy work vanishes at infinite formation depth. -/
theorem tendsto_formationBooleanWork_zero {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun m : ℕ => formationBooleanWork α β m) atTop (𝓝 0) := by
  rcases lt_trichotomy β α with h | h | h
  · refine (isEquivalent_formationBooleanWork hβ h).symm.tendsto_nhds ?_
    have := (tendsto_natMul_expNegDepth (show (0:ℝ) < (β : ℝ) from hβ)).const_mul
      ((α : ℝ) - (β : ℝ))
    rw [mul_zero] at this
    refine this.congr fun m => ?_
    ring
  · subst h
    simp [formationBooleanWork]
  · have hsym : ∀ m : ℕ, formationBooleanWork α β m = formationBooleanWork β α m :=
      formationBooleanWork_symm α β
    simp only [hsym]
    refine (isEquivalent_formationBooleanWork hα h).symm.tendsto_nhds ?_
    have := (tendsto_natMul_expNegDepth (show (0:ℝ) < (α : ℝ) from hα)).const_mul
      ((β : ℝ) - (α : ℝ))
    rw [mul_zero] at this
    refine this.congr fun m => ?_
    ring

/-! ## Hidden-history action density -/

@[simp] theorem formationHistoryWork_self (α : ℝ≥0) (m : ℕ) : formationHistoryWork α α m = 0 := by
  simp [formationHistoryWork]

@[simp] theorem formationBooleanWork_self (α : ℝ≥0) (m : ℕ) : formationBooleanWork α α m = 0 := by
  simp [formationBooleanWork]

/-- **History-density reconstruction.**  The vertical action density converges to the complete
one-copy Poisson Jeffreys information. -/
theorem tendsto_formationHistoryWork_div {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) :
    Tendsto (fun m : ℕ => formationHistoryWork α β m / (m : ℝ)) atTop
      (𝓝 (rateJeffreys α β)) := by
  have hB : Tendsto (fun m : ℕ => formationBooleanWork α β m / (m : ℝ)) atTop (𝓝 0) :=
    (tendsto_formationBooleanWork_zero hα hβ).div_atTop tendsto_natCast_atTop_atTop
  have heq : (fun m : ℕ => formationHistoryWork α β m / (m : ℝ))
      =ᶠ[atTop] fun m : ℕ => rateJeffreys α β - formationBooleanWork α β m / (m : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with m hm
    have h := formation_conservation hα hβ hm
    have hm' : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
    field_simp
    linarith [h]
  refine Filter.Tendsto.congr' heq.symm ?_
  simpa using (tendsto_const_nhds (x := rateJeffreys α β) (f := atTop (α := ℕ))).sub hB

/-- **Linear vertical escape.**  For distinct rates the vertical action eventually exceeds half the
one-copy information at every depth. -/
theorem eventually_half_rateJeffreys_mul_le {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) (hne : α ≠ β) :
    ∀ᶠ m : ℕ in atTop, 1 / 2 * rateJeffreys α β * (m : ℝ) ≤ formationHistoryWork α β m := by
  have hC := rateJeffreys_pos_of_ne hα hβ hne
  have hhalf : 1 / 2 * rateJeffreys α β < rateJeffreys α β := by linarith
  have hev := (tendsto_formationHistoryWork_div hα hβ).eventually_const_le hhalf
  filter_upwards [hev, eventually_gt_atTop 0] with m hm hm0
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  rw [le_div_iff₀ hm'] at hm
  exact hm

/-- Under linear vertical escape the action itself diverges. -/
theorem tendsto_formationHistoryWork_atTop {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) (hne : α ≠ β) :
    Tendsto (fun m : ℕ => formationHistoryWork α β m) atTop atTop := by
  have hC := rateJeffreys_pos_of_ne hα hβ hne
  refine tendsto_atTop_mono' atTop (eventually_half_rateJeffreys_mul_le hα hβ hne) ?_
  exact Filter.Tendsto.const_mul_atTop (by linarith) tendsto_natCast_atTop_atTop

/-! ## Open history over a closed observer boundary -/

/-- The excess-count mass of a fixed window vanishes at large rate. -/
theorem tendsto_excessCountWeight_atTop_zero (n : ℕ) :
    Tendsto (fun y : ℝ => excessCountWeight y n) atTop (𝓝 0) := by
  have hdecay : Tendsto (fun y : ℝ => y ^ (n + 1) * Real.exp (-y)) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_atTop_nhds_zero (n + 1)
  have hcorr : Tendsto (fun y : ℝ => (1 - Real.exp (-y))⁻¹) atTop (𝓝 1) := by
    have hnum : Tendsto (fun y : ℝ => 1 - Real.exp (-y)) atTop (𝓝 1) := by
      have h : Tendsto (fun y : ℝ => Real.exp (-y)) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).sub h
    simpa using hnum.inv₀ one_ne_zero
  have hprod : Tendsto (fun y : ℝ =>
      (y ^ (n + 1) * Real.exp (-y) * (1 - Real.exp (-y))⁻¹) * ((n + 1).factorial : ℝ)⁻¹)
      atTop (𝓝 ((0 * 1) * ((n + 1).factorial : ℝ)⁻¹)) :=
    (hdecay.mul hcorr).mul_const _
  rw [zero_mul, zero_mul] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  have hey := exp_sub_one_pos hy
  have hexp := Real.exp_pos y
  have hne : (1 : ℝ) - Real.exp (-y) ≠ 0 := by
    have hlt : Real.exp (-y) < 1 := Real.exp_lt_one_iff.2 (by linarith)
    linarith
  rw [excessCountWeight, Real.exp_neg]
  field_simp

/-- **History escape.**  Every fixed excess-count window is asymptotically evacuated under
superposition. -/
theorem tendsto_excessCountMeasure_Iic {x : ℝ} (hx : 0 < x) (R : ℕ) :
    Tendsto (fun m : ℕ => (excessCountMeasure ((m : ℝ) * x) (Set.Iic R)).toReal)
      atTop (𝓝 0) := by
  have hrate : Tendsto (fun m : ℕ => (m : ℝ) * x) atTop atTop :=
    Filter.Tendsto.atTop_mul_const hx tendsto_natCast_atTop_atTop
  have hsum : Tendsto (fun m : ℕ =>
      ∑ n ∈ Finset.Iic R, excessCountWeight ((m : ℝ) * x) n) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.Iic R)
      (f := fun n (m : ℕ) => excessCountWeight ((m : ℝ) * x) n) (a := fun _ => (0 : ℝ))
      (fun n _ => (tendsto_excessCountWeight_atTop_zero n).comp hrate)
    simpa using this
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hy : (0 : ℝ) < (m : ℝ) * x := by positivity
  rw [← Finset.coe_Iic, ← sum_measure_singleton (μ := excessCountMeasure ((m : ℝ) * x)),
    ENNReal.toReal_sum (fun n _ => by
      rw [excessCountMeasure_singleton]
      exact ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun n _ => (excessCountMeasure_singleton_toReal hy n).symm

/-! ## Global formation properness -/

/-- Source-generated orbit action along the geometric depth schedule `d ^ n`. -/
def orbitAction (d : ℕ) (α β : ℝ≥0) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (formationHistoryWork α β (d ^ n))

@[simp] theorem orbitAction_self (d : ℕ) (α : ℝ≥0) : orbitAction d α α = 0 := by
  simp [orbitAction]

theorem orbitAction_eq_top_of_ne {d : ℕ} (hd : 1 < d) {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β)
    (hne : α ≠ β) : orbitAction d α β = ⊤ := by
  have hdepth : Tendsto (fun n : ℕ => formationHistoryWork α β (d ^ n)) atTop atTop :=
    (tendsto_formationHistoryWork_atTop hα hβ hne).comp (tendsto_pow_atTop_atTop_of_one_lt hd)
  refine iSup_eq_top.2 fun b hb => ?_
  obtain ⟨n, hn⟩ := (hdepth.eventually_ge_atTop (b.toReal + 1)).exists
  refine ⟨n, ?_⟩
  calc b = ENNReal.ofReal b.toReal := (ENNReal.ofReal_toReal hb.ne).symm
    _ < ENNReal.ofReal (formationHistoryWork α β (d ^ n)) := by
        refine ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg |>.2 ?_
        linarith

theorem orbitAction_ne_top_iff {d : ℕ} (hd : 1 < d) {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) :
    orbitAction d α β ≠ ⊤ ↔ α = β := by
  constructor
  · intro h
    by_contra hne
    exact h (orbitAction_eq_top_of_ne hd hα hβ hne)
  · rintro rfl
    simp

/-- Vacuum-completed orbit action on the closed rate cone. -/
def completedOrbitAction (d : ℕ) (α β : ℝ≥0) : ℝ≥0∞ :=
  if α = 0 then (if β = 0 then 0 else ⊤) else if β = 0 then ⊤ else orbitAction d α β

/-- **Source-generated global properness.**  Bounded orbit action along any geometric depth
schedule is exactly rate equality. -/
theorem completedOrbitAction_ne_top_iff {d : ℕ} (hd : 1 < d) (α β : ℝ≥0) :
    completedOrbitAction d α β ≠ ⊤ ↔ α = β := by
  rw [completedOrbitAction]
  by_cases hα : α = 0
  · subst hα
    by_cases hβ : β = 0
    · subst hβ; simp
    · simp [hβ, Ne.symm hβ]
  · by_cases hβ : β = 0
    · subst hβ
      simp [hα]
    · rw [if_neg hα, if_neg hβ]
      exact orbitAction_ne_top_iff hd (pos_of_ne_zero hα) (pos_of_ne_zero hβ)

theorem completedOrbitAction_self (d : ℕ) (α : ℝ≥0) : completedOrbitAction d α α = 0 := by
  rw [completedOrbitAction]
  by_cases hα : α = 0 <;> simp [hα]

/-- **Compact source lift.**  Bounded extensive observer formation together with bounded recovered
history action cuts out exactly the diagonal segment. -/
theorem completedOrbitAction_sublevel_eq {d : ℕ} (hd : 1 < d) (M : ℝ≥0) {C : ℝ≥0∞} (hC : C ≠ ⊤) :
    {q : ℝ≥0 × ℝ≥0 | q.1 + q.2 ≤ M ∧ completedOrbitAction d q.1 q.2 ≤ C}
      = (fun x : ℝ≥0 => (x, x)) '' Set.Icc 0 (M / 2) := by
  have hhalf : ∀ x : ℝ≥0, x + x ≤ M ↔ x ≤ M / 2 := by
    intro x
    rw [← two_mul, le_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2), mul_comm]
  ext q
  obtain ⟨u, v⟩ := q
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_Icc]
  constructor
  · rintro ⟨hsum, hle⟩
    have hnetop : completedOrbitAction d u v ≠ ⊤ := fun h => hC (top_le_iff.1 (h ▸ hle))
    have huv : u = v := (completedOrbitAction_ne_top_iff hd u v).1 hnetop
    subst huv
    exact ⟨u, ⟨bot_le, (hhalf u).1 hsum⟩, rfl⟩
  · rintro ⟨x, ⟨-, hx⟩, hxy⟩
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact ⟨(hhalf x).2 hx, by simp [completedOrbitAction_self]⟩

theorem isCompact_completedOrbitAction_sublevel {d : ℕ} (hd : 1 < d) (M : ℝ≥0) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) :
    IsCompact {q : ℝ≥0 × ℝ≥0 | q.1 + q.2 ≤ M ∧ completedOrbitAction d q.1 q.2 ≤ C} := by
  rw [completedOrbitAction_sublevel_eq hd M hC]
  exact (isCompact_Icc (a := (0 : ℝ≥0)) (b := M / 2)).image (by fun_prop)

theorem orbitAction_symm (d : ℕ) (α β : ℝ≥0) : orbitAction d α β = orbitAction d β α := by
  simp only [orbitAction, formationHistoryWork_symm]

theorem completedOrbitAction_symm (d : ℕ) (α β : ℝ≥0) :
    completedOrbitAction d α β = completedOrbitAction d β α := by
  rw [completedOrbitAction, completedOrbitAction]
  by_cases hα : α = 0 <;> by_cases hβ : β = 0 <;>
    simp [hα, hβ, orbitAction_symm d α β]

/-- **Infinite relaxed action at every off-diagonal observer-boundary lift.** -/
theorem liminf_formationHistoryWork {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) :
    Filter.liminf (fun m : ℕ => ENNReal.ofReal (formationHistoryWork α β m)) atTop
      = if α = β then 0 else ⊤ := by
  by_cases h : α = β
  · subst h
    simp
  · rw [if_neg h]
    have hdiv := tendsto_formationHistoryWork_atTop hα hβ h
    have hcomp := ENNReal.tendsto_ofReal_atTop.comp hdiv
    exact (hcomp.congr fun m => rfl).liminf_eq

/-! ## Functional-equation specialization -/

/-- Reflected source rate of a prime at aperture `t`. -/
def reflectedSourceRate (p : Nat.Primes) (t : ℝ) : ℝ≥0 :=
  ⟨Real.log (1 + (p : ℝ) ^ (t - 1)), Real.log_nonneg (by
    have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
    have : (0 : ℝ) < (p : ℝ) ^ (t - 1) := Real.rpow_pos_of_pos hp _
    linarith)⟩

theorem coe_reflectedSourceRate (p : Nat.Primes) (t : ℝ) :
    (reflectedSourceRate p t : ℝ) = Real.log (1 + (p : ℝ) ^ (t - 1)) := rfl

theorem reflectedSourceRate_pos (p : Nat.Primes) (t : ℝ) : 0 < reflectedSourceRate p t := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hrp : (0 : ℝ) < (p : ℝ) ^ (t - 1) := Real.rpow_pos_of_pos hp _
  have : (0 : ℝ) < Real.log (1 + (p : ℝ) ^ (t - 1)) := Real.log_pos (by linarith)
  exact this

/-- Strict monotonicity of the source rate in the reflected aperture: the two reflected rates agree
exactly at the neutral point. -/
theorem reflectedSourceRate_eq_iff (p : Nat.Primes) (t : ℝ) :
    reflectedSourceRate p t = reflectedSourceRate p (-t) ↔ t = 0 := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp
  have hrp : ∀ u : ℝ, (0 : ℝ) < (p : ℝ) ^ (u - 1) := fun u => Real.rpow_pos_of_pos hp0 _
  constructor
  · intro h
    have h' : Real.log (1 + (p : ℝ) ^ (t - 1)) = Real.log (1 + (p : ℝ) ^ (-t - 1)) := by
      simpa [coe_reflectedSourceRate] using congrArg (fun x : ℝ≥0 => (x : ℝ)) h
    have hpow : (p : ℝ) ^ (t - 1) = (p : ℝ) ^ (-t - 1) := by
      have h1 := hrp t
      have h2 := hrp (-t)
      have := Real.exp_log (show (0:ℝ) < 1 + (p : ℝ) ^ (t - 1) by linarith)
      have h3 : (1 : ℝ) + (p : ℝ) ^ (t - 1) = 1 + (p : ℝ) ^ (-t - 1) := by
        rw [← Real.exp_log (show (0:ℝ) < 1 + (p : ℝ) ^ (t - 1) by linarith),
          ← Real.exp_log (show (0:ℝ) < 1 + (p : ℝ) ^ (-t - 1) by linarith), h']
      linarith
    rw [Real.rpow_def_of_pos hp0, Real.rpow_def_of_pos hp0] at hpow
    have hlin : Real.log (p : ℝ) * (t - 1) = Real.log (p : ℝ) * (-t - 1) := Real.exp_injective hpow
    have : Real.log (p : ℝ) * (2 * t) = 0 := by linarith
    rcases mul_eq_zero.1 this with h'' | h''
    · exact absurd h'' hlogp.ne'
    · linarith
  · rintro rfl
    norm_num

/-- **Bounded formation-depth history selects the neutral aperture.** -/
theorem completedOrbitAction_reflectedSourceRate_ne_top_iff {d : ℕ} (hd : 1 < d)
    (p : Nat.Primes) (t : ℝ) :
    completedOrbitAction d (reflectedSourceRate p t) (reflectedSourceRate p (-t)) ≠ ⊤
      ↔ t = 0 := by
  rw [completedOrbitAction_ne_top_iff hd, reflectedSourceRate_eq_iff]

/-- Reflection of the aperture leaves the orbit action invariant. -/
theorem completedOrbitAction_reflectedSourceRate_reflection (d : ℕ) (p : Nat.Primes) (t : ℝ) :
    completedOrbitAction d (reflectedSourceRate p (-t)) (reflectedSourceRate p (-(-t)))
      = completedOrbitAction d (reflectedSourceRate p t) (reflectedSourceRate p (-t)) := by
  rw [neg_neg, completedOrbitAction_symm]

end

end GaloisForLFunctions.HTGeometry
