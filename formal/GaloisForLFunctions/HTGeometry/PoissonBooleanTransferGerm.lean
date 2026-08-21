import GaloisForLFunctions.HTGeometry.ConstitutiveFormationTransferGerm
import GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalGeometry
import GaloisForLFunctions.HTGeometry.PoissonIntensityMarkingIsometry

/-!
# The Poisson--Boolean transfer germ

Boolean occupancy of a depth-`mn` Poisson formation is the logical OR of `n` independent depth-`m`
occupancy reports.  Relative entropy is additive on the block product and contracts under the OR
observer, so each directed scale-transfer cell is nonnegative: it is exactly the block history
information hidden by the OR observation.  The concrete Bernoulli formulas then identify the
cofinal transfer germ with the exact exponential model.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory InformationTheory ProbabilityTheory Real Filter Topology Asymptotics
open scoped ENNReal NNReal

noncomputable section

/-! ## The Boolean OR observer -/

/-- The logical OR of a block of occupancy reports. -/
def orObserver {n : ℕ} (f : Fin n → Bool) : Bool := decide (∃ i, f i = true)

theorem orObserver_eq_false_iff {n : ℕ} (f : Fin n → Bool) :
    orObserver f = false ↔ ∀ i, f i = false := by
  simp [orObserver]

theorem preimage_orObserver_false {n : ℕ} :
    (orObserver (n := n)) ⁻¹' {false} = Set.univ.pi fun _ : Fin n => ({false} : Set Bool) := by
  ext f
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_pi, Set.mem_univ, forall_true_left]
  rw [orObserver_eq_false_iff]

/-- The OR parameter of a block of independent Bernoulli occupancy reports. -/
def orParam (n : ℕ) (p : unitInterval) : unitInterval :=
  ⟨1 - (1 - (p : ℝ)) ^ n, by
    have h0 : (0 : ℝ) ≤ 1 - (p : ℝ) := by
      have := p.2.2
      linarith
    have h1 : (1 : ℝ) - (p : ℝ) ≤ 1 := by
      have := p.2.1
      linarith
    constructor
    · have : (1 - (p : ℝ)) ^ n ≤ 1 := pow_le_one₀ h0 h1
      linarith
    · have : (0 : ℝ) ≤ (1 - (p : ℝ)) ^ n := pow_nonneg h0 n
      linarith⟩

@[simp] theorem coe_orParam (n : ℕ) (p : unitInterval) :
    (orParam n p : ℝ) = 1 - (1 - (p : ℝ)) ^ n := rfl

/-- **Block OR of Bernoulli occupancy reports.** -/
theorem map_orObserver_bernoulli (n : ℕ) (p : unitInterval) :
    Measure.map orObserver (Measure.pi fun _ : Fin n => Ber(true, false, p))
      = Ber(true, false, orParam n p) := by
  have hfalse : (Measure.map orObserver (Measure.pi fun _ : Fin n => Ber(true, false, p)))
      {false} = Ber(true, false, orParam n p) {false} := by
    rw [Measure.map_apply Measurable.of_discrete (MeasurableSet.singleton false),
      preimage_orObserver_false, Measure.pi_pi]
    have hone : ∀ _i : Fin n, Ber(true, false, p) ({false} : Set Bool)
        = ENNReal.ofReal (1 - (p : ℝ)) := by
      intro i
      rw [bernoulliMeasure_apply_of_notMem_of_mem p (MeasurableSet.singleton false)
        (by simp) (by simp)]
      simp [← ENNReal.ofReal_coe_nnreal]
    rw [Finset.prod_congr rfl fun i _ => hone i, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← ENNReal.ofReal_pow (by
        have := p.2.2
        linarith)]
    rw [bernoulliMeasure_apply_of_notMem_of_mem (orParam n p) (MeasurableSet.singleton false)
      (by simp) (by simp)]
    simp [← ENNReal.ofReal_coe_nnreal]
  refine Measure.ext_of_singleton fun b => ?_
  cases b with
  | false => exact hfalse
  | true =>
      haveI : IsProbabilityMeasure
          (Measure.map orObserver (Measure.pi fun _ : Fin n => Ber(true, false, p))) :=
        Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable
      have h1 : (Measure.map orObserver (Measure.pi fun _ : Fin n => Ber(true, false, p)))
          Set.univ = 1 := measure_univ
      have h2 : Ber(true, false, orParam n p) (Set.univ : Set Bool) = 1 := by simp
      have hsplit : ∀ μ : Measure Bool, μ Set.univ = μ {false} + μ {true} := by
        intro μ
        rw [show (Set.univ : Set Bool) = {false} ∪ {true} from by
          ext b; cases b <;> simp]
        exact measure_union (by simp) (MeasurableSet.singleton true)
      rw [hsplit] at h1 h2
      rw [hfalse] at h1
      have hfin : Ber(true, false, orParam n p) {false} ≠ ⊤ := measure_ne_top _ _
      exact (ENNReal.add_right_inj hfin).1 (h1.trans h2.symm)

/-! ## Positivity of the directed transfer cell -/

/-- Directed Boolean occupancy work at formation depth `m`. -/
def booleanForwardWork (α β : ℝ≥0) (m : ℕ) : ℝ :=
  (klDiv (occupancyReport ((m : ℝ≥0) * α)) (occupancyReport ((m : ℝ≥0) * β))).toReal

theorem booleanForwardWork_add (α β : ℝ≥0) (m : ℕ) :
    booleanForwardWork α β m + booleanForwardWork β α m = formationBooleanWork α β m := by
  rw [booleanForwardWork, booleanForwardWork, formationBooleanWork, booleanOccupancyJeffreys]

/-- Boolean occupancy of a depth-`mn` formation is the OR of `n` depth-`m` reports. -/
theorem orParam_poissonOccupancyUnit (α : ℝ≥0) (m n : ℕ) :
    orParam n (poissonOccupancyUnit ((m : ℝ≥0) * α)) = poissonOccupancyUnit ((m * n : ℕ) * α) := by
  apply Subtype.ext
  rw [coe_orParam, coe_poissonOccupancyUnit, coe_poissonOccupancyUnit]
  rw [show (1 : ℝ) - (1 - Real.exp (-(((m : ℝ≥0) * α : ℝ≥0) : ℝ)))
      = Real.exp (-(((m : ℝ≥0) * α : ℝ≥0) : ℝ)) from by ring, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem occupancyReport_or (α : ℝ≥0) (m n : ℕ) :
    Measure.map orObserver
        (Measure.pi fun _ : Fin n => occupancyReport ((m : ℝ≥0) * α))
      = occupancyReport (((m * n : ℕ) : ℝ≥0) * α) := by
  rw [occupancyReport, map_orObserver_bernoulli, orParam_poissonOccupancyUnit, occupancyReport]

/-- **Positivity of the directed transfer cell** (ULF-FTGM-1, (2.3)).  Relative entropy contracts under
the OR observer, so forming `n` depth-`m` blocks never increases the directed occupancy work. -/
theorem booleanForwardWork_subadditive (α : ℝ≥0) {β : ℝ≥0} (hβ : 0 < β) {m : ℕ} (hm : 0 < m)
    (n : ℕ) :
    booleanForwardWork α β (m * n) ≤ n * booleanForwardWork α β m := by
  have hmb := depthRate_pos hβ hm
  have hne : klDiv (occupancyReport ((m : ℝ≥0) * α)) (occupancyReport ((m : ℝ≥0) * β)) ≠ ⊤ :=
    klDiv_bernoulli_ne_top_baseline_interior _ _ (coe_poissonOccupancyUnit_pos hmb)
      (coe_poissonOccupancyUnit_lt_one _)
  have hdpi : klDiv (occupancyReport (((m * n : ℕ) : ℝ≥0) * α))
      (occupancyReport (((m * n : ℕ) : ℝ≥0) * β))
      ≤ (n : ℝ≥0∞) * klDiv (occupancyReport ((m : ℝ≥0) * α))
        (occupancyReport ((m : ℝ≥0) * β)) := by
    rw [← occupancyReport_or α m n, ← occupancyReport_or β m n]
    refine le_trans (klDiv_map_le_arbitrary _ _ orObserver Measurable.of_discrete) ?_
    rw [klDiv_pi]
    simp
  have hle := ENNReal.toReal_mono (by
    refine ENNReal.mul_ne_top (by simp) hne) hdpi
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hle
  simpa [booleanForwardWork] using hle

theorem directedFormationTransfer_nonneg (α : ℝ≥0) {β : ℝ≥0} (hβ : 0 < β) {m : ℕ} (hm : 0 < m)
    (n : ℕ) :
    0 ≤ formationInformationTransfer (booleanForwardWork α β) m n := by
  rw [formationInformationTransfer]
  linarith [booleanForwardWork_subadditive α hβ hm n]

theorem symmetricFormationTransfer_nonneg {α β : ℝ≥0} (hα : 0 < α) (hβ : 0 < β) {m : ℕ}
    (hm : 0 < m) (n : ℕ) :
    0 ≤ formationInformationTransfer (formationBooleanWork α β) m n := by
  have h1 := directedFormationTransfer_nonneg α hβ hm n
  have h2 := directedFormationTransfer_nonneg β hα hm n
  rw [formationInformationTransfer] at h1 h2 ⊢
  rw [← booleanForwardWork_add α β m, ← booleanForwardWork_add α β (m * n)]
  linarith [h1, h2]

/-! ## Abstract boundary-germ tomography -/

section Tomography

variable {Δ b : ℝ} {d : ℕ} {g : ℕ → ℝ}

theorem tendsto_pow_atTop_of_one_lt' (hd : 1 < d) :
    Tendsto (fun j : ℕ => ((d : ℝ)) ^ j) atTop atTop := by
  refine tendsto_pow_atTop_atTop_of_one_lt ?_
  exact_mod_cast hd

theorem tendsto_germRatio (hΔ : 0 < Δ)
    (hg : g ~[atTop] fun j : ℕ => Δ * Real.exp (-(b * (d : ℝ) ^ j))) :
    Tendsto (fun j : ℕ => g j / (Δ * Real.exp (-(b * (d : ℝ) ^ j)))) atTop (𝓝 1) := by
  refine (Asymptotics.isEquivalent_iff_tendsto_one ?_).1 hg
  filter_upwards with j
  positivity

/-- **Decay tomography** (ULF-FTGM-1, (3.6)). -/
theorem tendsto_neg_log_germ_div (hΔ : 0 < Δ) (hd : 1 < d)
    (hg : g ~[atTop] fun j : ℕ => Δ * Real.exp (-(b * (d : ℝ) ^ j))) :
    Tendsto (fun j : ℕ => -Real.log (g j) / (d : ℝ) ^ j) atTop (𝓝 b) := by
  have hR := tendsto_germRatio hΔ hg
  have hRpos : ∀ᶠ j : ℕ in atTop, 0 < g j / (Δ * Real.exp (-(b * (d : ℝ) ^ j))) :=
    hR.eventually (eventually_gt_nhds one_pos)
  have hlogR : Tendsto (fun j : ℕ =>
      Real.log (g j / (Δ * Real.exp (-(b * (d : ℝ) ^ j))))) atTop (𝓝 0) := by
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp hR
    simpa [Function.comp_def] using this
  have hdtop := tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < (d : ℝ) by exact_mod_cast hd)
  have hquot : Tendsto (fun j : ℕ =>
      (Real.log (g j / (Δ * Real.exp (-(b * (d : ℝ) ^ j)))) + Real.log Δ) / (d : ℝ) ^ j)
      atTop (𝓝 0) := by
    have hnum : Tendsto (fun j : ℕ =>
        Real.log (g j / (Δ * Real.exp (-(b * (d : ℝ) ^ j)))) + Real.log Δ) atTop
        (𝓝 (0 + Real.log Δ)) := hlogR.add tendsto_const_nhds
    exact Filter.Tendsto.div_atTop hnum hdtop
  have hEq : (fun j : ℕ => -Real.log (g j) / (d : ℝ) ^ j)
      =ᶠ[atTop] fun j : ℕ =>
        b - (Real.log (g j / (Δ * Real.exp (-(b * (d : ℝ) ^ j)))) + Real.log Δ) / (d : ℝ) ^ j := by
    filter_upwards [hRpos] with j hj
    have hvpos : (0 : ℝ) < Δ * Real.exp (-(b * (d : ℝ) ^ j)) := by positivity
    have hgpos : 0 < g j := by
      have := mul_pos hj hvpos
      rwa [div_mul_cancel₀ _ hvpos.ne'] at this
    have hdpos : (0 : ℝ) < (d : ℝ) ^ j := by
      have : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hd.le
      positivity
    rw [Real.log_div hgpos.ne' hvpos.ne', Real.log_mul hΔ.ne' (Real.exp_ne_zero _), Real.log_exp]
    field_simp
    ring
  refine Filter.Tendsto.congr' hEq.symm ?_
  have := (tendsto_const_nhds (x := b) (f := atTop (α := ℕ))).sub hquot
  simpa using this

/-- **Amplitude tomography** (ULF-FTGM-1, (3.7)). -/
theorem tendsto_germ_scale_ratio (hΔ : 0 < Δ)
    (hg : g ~[atTop] fun j : ℕ => Δ * Real.exp (-(b * (d : ℝ) ^ j))) :
    Tendsto (fun j : ℕ => g (j + 1) / (g j) ^ d) atTop (𝓝 (Δ / Δ ^ d)) := by
  have hR := tendsto_germRatio hΔ hg
  have hRsucc : Tendsto (fun j : ℕ =>
      g (j + 1) / (Δ * Real.exp (-(b * (d : ℝ) ^ (j + 1))))) atTop (𝓝 1) :=
    hR.comp (Filter.tendsto_add_atTop_nat 1)
  have hden : Tendsto (fun j : ℕ =>
      (g j / (Δ * Real.exp (-(b * (d : ℝ) ^ j)))) ^ d) atTop (𝓝 1) := by
    simpa using hR.pow d
  have hquot : Tendsto (fun j : ℕ =>
      (g (j + 1) / (Δ * Real.exp (-(b * (d : ℝ) ^ (j + 1))))) /
        ((g j / (Δ * Real.exp (-(b * (d : ℝ) ^ j)))) ^ d)) atTop (𝓝 (1 / 1)) :=
    hRsucc.div hden one_ne_zero
  rw [div_one] at hquot
  have hmul := hquot.const_mul (Δ / Δ ^ d)
  rw [mul_one] at hmul
  have hRpos : ∀ᶠ j : ℕ in atTop, 0 < g j / (Δ * Real.exp (-(b * (d : ℝ) ^ j))) :=
    hR.eventually (eventually_gt_nhds one_pos)
  have hRsuccpos : ∀ᶠ j : ℕ in atTop,
      0 < g (j + 1) / (Δ * Real.exp (-(b * (d : ℝ) ^ (j + 1)))) :=
    hRsucc.eventually (eventually_gt_nhds one_pos)
  refine Filter.Tendsto.congr' ?_ hmul
  filter_upwards [hRpos, hRsuccpos] with j hj hjs
  have hvpos : (0 : ℝ) < Δ * Real.exp (-(b * (d : ℝ) ^ j)) := by positivity
  have hvspos : (0 : ℝ) < Δ * Real.exp (-(b * (d : ℝ) ^ (j + 1))) := by positivity
  have hgpos : 0 < g j := by
    have := mul_pos hj hvpos
    rwa [div_mul_cancel₀ _ hvpos.ne'] at this
  have hexp : Real.exp (-(b * (d : ℝ) ^ (j + 1)))
      = (Real.exp (-(b * (d : ℝ) ^ j))) ^ d := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [pow_succ]
    ring
  rw [div_pow, hexp]
  field_simp
  ring

end Tomography

/-! ## The Poisson--Boolean boundary germ -/

/-- One-step symmetric transfer density along the geometric depth schedule `d ^ j`. -/
def booleanTransferDensity (α β : ℝ≥0) (d : ℕ) (j : ℕ) : ℝ :=
  formationBooleanWork α β (d ^ j) / (d : ℝ) ^ j
    - formationBooleanWork α β (d ^ (j + 1)) / (d : ℝ) ^ (j + 1)

/-- The transfer density is the normalized one-step transfer cell (ULF-FTGM-1, (3.1)). -/
theorem booleanTransferDensity_eq_transfer (α β : ℝ≥0) {d : ℕ} (hd : 0 < d) (j : ℕ) :
    booleanTransferDensity α β d j
      = formationInformationTransfer (formationBooleanWork α β) (d ^ j) d /
        ((d : ℝ) * (d : ℝ) ^ j) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hpow : (0 : ℝ) < (d : ℝ) ^ j := by positivity
  rw [booleanTransferDensity, formationInformationTransfer,
    show d ^ j * d = d ^ (j + 1) from by ring]
  field_simp
  ring

theorem isLittleO_shifted_germ {b : ℝ} (hb : 0 < b) {Δ : ℝ} {d : ℕ} (hd : 1 < d) :
    (fun j : ℕ => Δ * Real.exp (-(b * (d : ℝ) ^ (j + 1))))
      =o[atTop] fun j : ℕ => Δ * Real.exp (-(b * (d : ℝ) ^ j)) := by
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine Asymptotics.isLittleO_iff_tendsto (fun j hj => ?_) |>.2 ?_
  · have : Real.exp (-(b * (d : ℝ) ^ j)) ≠ 0 := Real.exp_ne_zero _
    have hΔ : Δ = 0 := by
      rcases mul_eq_zero.1 hj with h | h
      · exact h
      · exact absurd h this
    simp [hΔ]
  · have hratio : ∀ j : ℕ,
        (Δ * Real.exp (-(b * (d : ℝ) ^ (j + 1)))) / (Δ * Real.exp (-(b * (d : ℝ) ^ j)))
          = (if Δ = 0 then 0 else 1) * Real.exp (-(b * ((d : ℝ) - 1) * (d : ℝ) ^ j)) := by
      intro j
      by_cases hΔ : Δ = 0
      · simp [hΔ]
      · rw [if_neg hΔ, one_mul, mul_div_mul_left _ _ hΔ, ← Real.exp_sub]
        congr 1
        rw [pow_succ]
        ring
    have hdecay : Tendsto (fun j : ℕ => Real.exp (-(b * ((d : ℝ) - 1) * (d : ℝ) ^ j)))
        atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
      exact Filter.Tendsto.const_mul_atTop (by nlinarith)
        (tendsto_pow_atTop_atTop_of_one_lt hdR)
    have := hdecay.const_mul (if Δ = 0 then (0:ℝ) else 1)
    rw [mul_zero] at this
    exact this.congr fun j => (hratio j).symm

/-- **The Poisson--Boolean boundary germ is the exact exponential model** (ULF-FTGM-1, (3.5)). -/
theorem isEquivalent_booleanTransferDensity {α β : ℝ≥0} (hβ : 0 < β) (hlt : β < α) {d : ℕ}
    (hd : 1 < d) :
    (fun j : ℕ => booleanTransferDensity α β d j)
      ~[atTop] fun j : ℕ => ((α : ℝ) - (β : ℝ)) * Real.exp (-((β : ℝ) * (d : ℝ) ^ j)) := by
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hdtop : Tendsto (fun j : ℕ => d ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hd
  have hB := isEquivalent_formationBooleanWork hβ hlt
  have hcomp := hB.comp_tendsto hdtop
  have hstep : (fun j : ℕ => formationBooleanWork α β (d ^ j) / (d : ℝ) ^ j)
      ~[atTop] fun j : ℕ => ((α : ℝ) - (β : ℝ)) * Real.exp (-((β : ℝ) * (d : ℝ) ^ j)) := by
    have hself : (fun j : ℕ => ((d : ℝ)) ^ j) ~[atTop] fun j : ℕ => ((d : ℝ)) ^ j :=
      Asymptotics.IsEquivalent.refl
    have hdiv := hcomp.div hself
    refine hdiv.congr_right ?_ |>.congr_left ?_
    · refine Filter.Eventually.of_forall fun j => ?_
      simp only [Function.comp_apply, Pi.div_apply]
      have hpow : (0 : ℝ) < (d : ℝ) ^ j := by positivity
      push_cast
      field_simp
    · refine Filter.Eventually.of_forall fun j => ?_
      simp only [Function.comp_apply, Pi.div_apply]
  have hshift : (fun j : ℕ => formationBooleanWork α β (d ^ (j + 1)) / (d : ℝ) ^ (j + 1))
      ~[atTop] fun j : ℕ => ((α : ℝ) - (β : ℝ)) * Real.exp (-((β : ℝ) * (d : ℝ) ^ (j + 1))) :=
    hstep.comp_tendsto (Filter.tendsto_add_atTop_nat 1)
  have hlo : (fun j : ℕ => -(formationBooleanWork α β (d ^ (j + 1)) / (d : ℝ) ^ (j + 1)))
      =o[atTop] fun j : ℕ => ((α : ℝ) - (β : ℝ)) * Real.exp (-((β : ℝ) * (d : ℝ) ^ j)) := by
    refine Asymptotics.IsLittleO.neg_left ?_
    exact hshift.trans_isLittleO (isLittleO_shifted_germ (show (0:ℝ) < (β : ℝ) from hβ) hd)
  have := hstep.add_isLittleO hlo
  refine this.congr_left ?_
  refine Filter.Eventually.of_forall fun j => ?_
  simp only [Pi.add_apply]
  rw [booleanTransferDensity]
  ring

/-! ## Directed asymptotics -/

section Directed

theorem tendsto_log_one_add_div :
    Tendsto (fun u : ℝ => Real.log (1 + u) / u) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (𝓝 1) := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add 1
  have hd : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    have := (Real.hasDerivAt_log (by norm_num : (1 : ℝ) + 0 ≠ 0)).comp 0 h1
    simpa [Function.comp_def] using this
  refine (hasDerivAt_iff_tendsto_slope.1 hd).congr fun u => ?_
  rw [slope_def_field]
  simp [div_eq_inv_mul]

variable {α β : ℝ≥0}

/-- The exact directed occupancy work (ULF-FTGM-1, (4.5)). -/
theorem booleanForwardWork_eq (hα : 0 < α) (hβ : 0 < β) {m : ℕ} (hm : 0 < m) :
    booleanForwardWork α β m
      = (1 - Real.exp (-((m : ℝ) * (α : ℝ)))) *
          Real.log ((1 - Real.exp (-((m : ℝ) * (α : ℝ)))) /
            (1 - Real.exp (-((m : ℝ) * (β : ℝ)))))
        + Real.exp (-((m : ℝ) * (α : ℝ))) * (-((m : ℝ) * ((α : ℝ) - (β : ℝ)))) := by
  have hma := depthRate_pos hα hm
  have hmb := depthRate_pos hβ hm
  rw [booleanForwardWork, occupancyReport, occupancyReport,
    toReal_klDiv_bernoulli_baseline_interior _ _ (coe_poissonOccupancyUnit_pos hmb)
      (coe_poissonOccupancyUnit_lt_one _)]
  simp only [coe_poissonOccupancyUnit, coe_depthRate, sub_sub_cancel]
  congr 2
  rw [← Real.exp_sub, Real.log_exp]
  ring

/-- The shared logarithmic ratio of the two directed works. -/
theorem tendsto_logRatio_div (hβ : 0 < β) (hlt : β < α) :
    Tendsto (fun m : ℕ =>
      Real.log ((1 - Real.exp (-((m : ℝ) * (α : ℝ)))) / (1 - Real.exp (-((m : ℝ) * (β : ℝ)))))
        / Real.exp (-((m : ℝ) * (β : ℝ)))) atTop (𝓝 1) := by
  have hα : (0 : ℝ) < (α : ℝ) := lt_trans hβ hlt
  have hβ' : (0 : ℝ) < (β : ℝ) := hβ
  have hgap : (0 : ℝ) < (α : ℝ) - (β : ℝ) := by
    have : (β : ℝ) < (α : ℝ) := hlt
    linarith
  set A : ℕ → ℝ := fun m => Real.exp (-((m : ℝ) * (α : ℝ))) with hA
  set B : ℕ → ℝ := fun m => Real.exp (-((m : ℝ) * (β : ℝ))) with hB
  have hApos : ∀ m, 0 < A m := fun m => Real.exp_pos _
  have hBpos : ∀ m, 0 < B m := fun m => Real.exp_pos _
  have hAzero : Tendsto A atTop (𝓝 0) := by
    refine (tendsto_expNegDepth hα).congr fun m => ?_
    rw [hA]
  have hBzero : Tendsto B atTop (𝓝 0) := by
    refine (tendsto_expNegDepth hβ').congr fun m => ?_
    rw [hB]
  have hAB : Tendsto (fun m : ℕ => A m / B m) atTop (𝓝 0) := by
    refine (tendsto_expNegDepth hgap).congr fun m => ?_
    rw [hA, hB, ← Real.exp_sub]
    congr 1
    ring
  set u : ℕ → ℝ := fun m => (B m - A m) / (1 - B m) with hu
  have hBlt : ∀ᶠ m : ℕ in atTop, B m < 1 := hBzero.eventually (eventually_lt_nhds one_pos)
  have hAltB : ∀ m : ℕ, 0 < m → A m < B m := by
    intro m hm
    rw [hA, hB, Real.exp_lt_exp]
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    nlinarith
  have huratio : Tendsto (fun m : ℕ => u m / B m) atTop (𝓝 1) := by
    have hnum : Tendsto (fun m : ℕ => (1 - A m / B m) / (1 - B m)) atTop (𝓝 ((1 - 0) / (1 - 0))) :=
      ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hAB).div
        ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hBzero) (by norm_num)
    rw [show ((1 : ℝ) - 0) / (1 - 0) = 1 from by norm_num] at hnum
    refine hnum.congr' ?_
    filter_upwards [hBlt] with m hm
    have hb1 : (1 : ℝ) - B m ≠ 0 := by
      intro hz
      exact absurd hm (by linarith [hz] : ¬ B m < 1)
    have hBne : B m ≠ 0 := ne_of_gt (hBpos m)
    rw [hu]
    field_simp
  have huzero : Tendsto u atTop (𝓝[{(0 : ℝ)}ᶜ] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hlim : Tendsto (fun m : ℕ => (B m - A m) / (1 - B m)) atTop (𝓝 ((0 - 0) / (1 - 0))) :=
        (hBzero.sub hAzero).div
          ((tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hBzero) (by norm_num)
      rw [show ((0 : ℝ) - 0) / (1 - 0) = 0 from by norm_num] at hlim
      exact hlim
    · filter_upwards [hBlt, eventually_gt_atTop 0] with m hm hmpos
      have hb1 : (0 : ℝ) < 1 - B m := by linarith
      have hnum : 0 < B m - A m := by linarith [hAltB m hmpos]
      rw [hu]
      exact ne_of_gt (div_pos hnum hb1)
  have hlogu : Tendsto (fun m : ℕ => Real.log (1 + u m) / u m) atTop (𝓝 1) :=
    tendsto_log_one_add_div.comp huzero
  have hmul := hlogu.mul huratio
  rw [one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [hBlt, eventually_gt_atTop 0] with m hm hmpos
  have hb1 : (0 : ℝ) < 1 - B m := by linarith
  have hb1' : (1 : ℝ) - B m ≠ 0 := ne_of_gt hb1
  have hBne : B m ≠ 0 := ne_of_gt (hBpos m)
  have hnum : 0 < B m - A m := by linarith [hAltB m hmpos]
  have hune : u m ≠ 0 := by
    rw [hu]
    exact ne_of_gt (div_pos hnum hb1)
  have hone : (1 : ℝ) + u m = (1 - A m) / (1 - B m) := by
    rw [hu]
    field_simp
    ring
  rw [hone]
  field_simp
  ring

theorem isLittleO_of_eventuallyEq_mul {u v e : ℕ → ℝ} (he : Tendsto e atTop (𝓝 0))
    (h : u =ᶠ[atTop] fun j => e j * v j) : u =o[atTop] v := by
  have h1 : e =o[atTop] fun _ : ℕ => (1 : ℝ) := (Asymptotics.isLittleO_one_iff ℝ).2 he
  have h2 := h1.mul_isBigO (Asymptotics.isBigO_refl v atTop)
  refine h2.congr' h.symm (Filter.Eventually.of_forall fun j => ?_)
  simp

/-- **Directed occupancy asymptotics, forward leg** (ULF-FTGM-1, (4.7)). -/
theorem isEquivalent_booleanForwardWork (hβ : 0 < β) (hlt : β < α) :
    (fun m : ℕ => booleanForwardWork α β m)
      ~[atTop] fun m : ℕ => Real.exp (-((m : ℝ) * (β : ℝ))) := by
  have hα : (0 : ℝ) < (α : ℝ) := lt_trans hβ hlt
  have hβ' : (0 : ℝ) < (β : ℝ) := hβ
  have hgap : (0 : ℝ) < (α : ℝ) - (β : ℝ) := by
    have : (β : ℝ) < (α : ℝ) := hlt
    linarith
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have hL := tendsto_logRatio_div hβ hlt
  have hone : Tendsto (fun m : ℕ => 1 - Real.exp (-((m : ℝ) * (α : ℝ)))) atTop (𝓝 (1 - 0)) :=
    (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub (tendsto_expNegDepth hα)
  rw [sub_zero] at hone
  have hdrop : Tendsto (fun m : ℕ => ((α : ℝ) - (β : ℝ)) *
      ((m : ℝ) * Real.exp (-((m : ℝ) * ((α : ℝ) - (β : ℝ)))))) atTop (𝓝 0) := by
    have := (tendsto_natMul_expNegDepth hgap).const_mul ((α : ℝ) - (β : ℝ))
    rwa [mul_zero] at this
  have hcomb := (hone.mul hL).sub hdrop
  rw [one_mul, sub_zero] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  simp only [Pi.div_apply]
  have hAne : Real.exp (-((m : ℝ) * (α : ℝ))) ≠ 0 := Real.exp_ne_zero _
  have hBne : Real.exp (-((m : ℝ) * (β : ℝ))) ≠ 0 := Real.exp_ne_zero _
  rw [booleanForwardWork_eq (hβ.trans hlt) hβ hm]
  have hexp : Real.exp (-((m : ℝ) * (α : ℝ)))
      = Real.exp (-((m : ℝ) * ((α : ℝ) - (β : ℝ)))) * Real.exp (-((m : ℝ) * (β : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  field_simp
  rw [hexp]
  ring

/-- **Directed occupancy asymptotics, reverse leg** (ULF-FTGM-1, (4.7)). -/
theorem isEquivalent_booleanBackwardWork (hβ : 0 < β) (hlt : β < α) :
    (fun m : ℕ => booleanForwardWork β α m)
      ~[atTop] fun m : ℕ => (m : ℝ) * ((α : ℝ) - (β : ℝ)) * Real.exp (-((m : ℝ) * (β : ℝ))) := by
  have hα : (0 : ℝ) < (α : ℝ) := lt_trans hβ hlt
  have hβ' : (0 : ℝ) < (β : ℝ) := hβ
  have hgap : (0 : ℝ) < (α : ℝ) - (β : ℝ) := by
    have : (β : ℝ) < (α : ℝ) := hlt
    linarith
  refine Asymptotics.isEquivalent_of_tendsto_one ?_
  have hL := tendsto_logRatio_div hβ hlt
  have hone : Tendsto (fun m : ℕ => 1 - Real.exp (-((m : ℝ) * (β : ℝ)))) atTop (𝓝 (1 - 0)) :=
    (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub (tendsto_expNegDepth hβ')
  rw [sub_zero] at hone
  have hinv : Tendsto (fun m : ℕ => ((m : ℝ) * ((α : ℝ) - (β : ℝ)))⁻¹) atTop (𝓝 0) := by
    refine Filter.Tendsto.inv_tendsto_atTop ?_
    exact Filter.Tendsto.atTop_mul_const hgap tendsto_natCast_atTop_atTop
  have hprod := ((hone.mul hL).neg.mul hinv).add
    (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ)))
  rw [one_mul, neg_one_mul, neg_zero, zero_add] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  simp only [Pi.div_apply]
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hAne : Real.exp (-((m : ℝ) * (α : ℝ))) ≠ 0 := Real.exp_ne_zero _
  have hBne : Real.exp (-((m : ℝ) * (β : ℝ))) ≠ 0 := Real.exp_ne_zero _
  have hmne : ((m : ℝ) * ((α : ℝ) - (β : ℝ))) ≠ 0 := by positivity
  have hA1 : Real.exp (-((m : ℝ) * (α : ℝ))) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hB1 : Real.exp (-((m : ℝ) * (β : ℝ))) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hswap : Real.log ((1 - Real.exp (-((m : ℝ) * (β : ℝ)))) /
        (1 - Real.exp (-((m : ℝ) * (α : ℝ)))))
      = -Real.log ((1 - Real.exp (-((m : ℝ) * (α : ℝ)))) /
        (1 - Real.exp (-((m : ℝ) * (β : ℝ))))) := by
    rw [← Real.log_inv]
    congr 1
    rw [inv_div]
  rw [booleanForwardWork_eq hβ (hβ.trans hlt) hm, hswap]
  field_simp
  ring

theorem isLittleO_shift_of_tendsto_ratio {v : ℕ → ℝ} (hv : ∀ j, v j ≠ 0)
    (h : Tendsto (fun j : ℕ => v (j + 1) / v j) atTop (𝓝 0)) :
    (fun j : ℕ => v (j + 1)) =o[atTop] v :=
  isLittleO_of_eventuallyEq_mul h (Filter.Eventually.of_forall fun j => by
    show v (j + 1) = v (j + 1) / v j * v j
    rw [div_mul_cancel₀ _ (hv j)])

/-- A geometric-schedule difference inherits the asymptotics of its leading cell. -/
theorem isEquivalent_geometricDifference {K w v : ℕ → ℝ} {d : ℕ} (hd : 1 < d)
    (hK : (fun m : ℕ => K m) ~[atTop] w)
    (hv : ∀ j : ℕ, w (d ^ j) / (d : ℝ) ^ j = v j)
    (hshift : (fun j : ℕ => v (j + 1)) =o[atTop] v) :
    (fun j : ℕ => K (d ^ j) / (d : ℝ) ^ j - K (d ^ (j + 1)) / (d : ℝ) ^ (j + 1)) ~[atTop] v := by
  have hdtop : Tendsto (fun j : ℕ => d ^ j) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hd
  have hbase : (fun j : ℕ => K (d ^ j) / (d : ℝ) ^ j) ~[atTop] v := by
    have hdiv := (hK.comp_tendsto hdtop).div
      (Asymptotics.IsEquivalent.refl (u := fun j : ℕ => ((d : ℝ)) ^ j) (l := atTop))
    refine hdiv.congr_right ?_ |>.congr_left ?_
    · exact Filter.Eventually.of_forall fun j => by
        simp only [Function.comp_apply, Pi.div_apply]
        exact hv j
    · exact Filter.Eventually.of_forall fun j => by
        simp only [Function.comp_apply, Pi.div_apply]
  have hstep : (fun j : ℕ => K (d ^ (j + 1)) / (d : ℝ) ^ (j + 1))
      ~[atTop] fun j : ℕ => v (j + 1) :=
    hbase.comp_tendsto (Filter.tendsto_add_atTop_nat 1)
  have hlo : (fun j : ℕ => -(K (d ^ (j + 1)) / (d : ℝ) ^ (j + 1))) =o[atTop] v :=
    (hstep.trans_isLittleO hshift).neg_left
  refine (hbase.add_isLittleO hlo).congr_left ?_
  exact Filter.Eventually.of_forall fun j => by
    simp only [Pi.add_apply]
    ring

/-- Directed one-step transfer density along the geometric depth schedule (ULF-FTGM-1, (4.1)). -/
def directedTransferDensity (α β : ℝ≥0) (d j : ℕ) : ℝ :=
  booleanForwardWork α β (d ^ j) / (d : ℝ) ^ j
    - booleanForwardWork α β (d ^ (j + 1)) / (d : ℝ) ^ (j + 1)

/-- The two directed densities recompose the symmetric one (ULF-FTGM-1, (4.1)). -/
theorem directedTransferDensity_add (α β : ℝ≥0) (d j : ℕ) :
    directedTransferDensity α β d j + directedTransferDensity β α d j
      = booleanTransferDensity α β d j := by
  rw [directedTransferDensity, directedTransferDensity, booleanTransferDensity,
    ← booleanForwardWork_add α β (d ^ j), ← booleanForwardWork_add α β (d ^ (j + 1))]
  ring

theorem tendsto_geometricRatio {b : ℝ} (hb : 0 < b) {d : ℕ} (hd : 1 < d) :
    Tendsto (fun j : ℕ => Real.exp (-(b * ((d : ℝ) - 1) * (d : ℝ) ^ j))) atTop (𝓝 0) := by
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  refine Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp ?_)
  exact Filter.Tendsto.const_mul_atTop (by nlinarith) (tendsto_pow_atTop_atTop_of_one_lt hdR)

/-- **Forward directed germ** (ULF-FTGM-1, (4.2)). -/
theorem isEquivalent_directedTransferDensity_forward (hβ : 0 < β) (hlt : β < α) {d : ℕ}
    (hd : 1 < d) :
    (fun j : ℕ => directedTransferDensity α β d j)
      ~[atTop] fun j : ℕ => Real.exp (-((β : ℝ) * (d : ℝ) ^ j)) / (d : ℝ) ^ j := by
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hβ' : (0 : ℝ) < (β : ℝ) := hβ
  refine isEquivalent_geometricDifference hd (isEquivalent_booleanForwardWork hβ hlt) ?_ ?_
  · intro j
    have hpow : (0 : ℝ) < (d : ℝ) ^ j := by positivity
    push_cast
    ring_nf
  · refine isLittleO_shift_of_tendsto_ratio
      (v := fun j : ℕ => Real.exp (-((β : ℝ) * (d : ℝ) ^ j)) / (d : ℝ) ^ j) (fun j => ?_) ?_
    · have hpow : (0 : ℝ) < (d : ℝ) ^ j := by positivity
      exact ne_of_gt (div_pos (Real.exp_pos _) hpow)
    · have hlim := (tendsto_geometricRatio hβ' hd).const_mul ((d : ℝ)⁻¹)
      rw [mul_zero] at hlim
      refine hlim.congr fun j => ?_
      have hpow : (0 : ℝ) < (d : ℝ) ^ j := by positivity
      have hE : Real.exp (-((β : ℝ) * (d : ℝ) ^ (j + 1)))
          = Real.exp (-((β : ℝ) * ((d : ℝ) - 1) * (d : ℝ) ^ j)) *
            Real.exp (-((β : ℝ) * (d : ℝ) ^ j)) := by
        rw [← Real.exp_add, Real.exp_eq_exp, pow_succ]
        ring
      have hBne : Real.exp (-((β : ℝ) * (d : ℝ) ^ j)) ≠ 0 := Real.exp_ne_zero _
      rw [hE, pow_succ]
      field_simp

/-- **Reverse directed germ** (ULF-FTGM-1, (4.2)). -/
theorem isEquivalent_directedTransferDensity_reverse (hβ : 0 < β) (hlt : β < α) {d : ℕ}
    (hd : 1 < d) :
    (fun j : ℕ => directedTransferDensity β α d j)
      ~[atTop] fun j : ℕ => ((α : ℝ) - (β : ℝ)) * Real.exp (-((β : ℝ) * (d : ℝ) ^ j)) := by
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hβ' : (0 : ℝ) < (β : ℝ) := hβ
  have hgap : (0 : ℝ) < (α : ℝ) - (β : ℝ) := by
    have : (β : ℝ) < (α : ℝ) := hlt
    linarith
  refine isEquivalent_geometricDifference hd (isEquivalent_booleanBackwardWork hβ hlt) ?_ ?_
  · intro j
    have hpow : (0 : ℝ) < (d : ℝ) ^ j := by positivity
    push_cast
    field_simp
  · refine isLittleO_shift_of_tendsto_ratio
      (v := fun j : ℕ => ((α : ℝ) - (β : ℝ)) * Real.exp (-((β : ℝ) * (d : ℝ) ^ j)))
      (fun j => ?_) ?_
    · exact ne_of_gt (mul_pos hgap (Real.exp_pos _))
    · refine (tendsto_geometricRatio hβ' hd).congr fun j => ?_
      rw [mul_div_mul_left _ _ (ne_of_gt hgap), ← Real.exp_sub, Real.exp_eq_exp, pow_succ]
      ring

section Orientation

variable {d : ℕ}

/-- **Rate-gap recovery from the directed germ** (ULF-FTGM-1, (4.3), oriented form). -/
theorem tendsto_directedTransferDensity_ratio (hβ : 0 < β) (hlt : β < α) (hd : 1 < d) :
    Tendsto (fun j : ℕ => directedTransferDensity β α d j /
      ((d : ℝ) ^ j * directedTransferDensity α β d j)) atTop (𝓝 ((α : ℝ) - (β : ℝ))) := by
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hnum := isEquivalent_directedTransferDensity_reverse hβ hlt hd
  have hfwd := isEquivalent_directedTransferDensity_forward hβ hlt hd
  have hden : (fun j : ℕ => (d : ℝ) ^ j * directedTransferDensity α β d j)
      ~[atTop] fun j : ℕ => Real.exp (-((β : ℝ) * (d : ℝ) ^ j)) := by
    have := (Asymptotics.IsEquivalent.refl (u := fun j : ℕ => ((d : ℝ)) ^ j)
      (l := atTop)).mul hfwd
    refine this.congr_left (Filter.Eventually.of_forall fun j => ?_) |>.congr_right
      (Filter.Eventually.of_forall fun j => ?_)
    · simp only [Pi.mul_apply]
    · have hpow : (0 : ℝ) < (d : ℝ) ^ j := by positivity
      simp only [Pi.mul_apply]
      field_simp
  have hq := hnum.div hden
  have hconst : (fun _ : ℕ => (α : ℝ) - (β : ℝ)) ~[atTop]
      fun j : ℕ => directedTransferDensity β α d j /
        ((d : ℝ) ^ j * directedTransferDensity α β d j) := by
    refine (hq.congr_right (Filter.Eventually.of_forall fun j => ?_)).symm
    simp only [Pi.div_apply]
    rw [mul_div_assoc, div_self (Real.exp_ne_zero _), mul_one]
  exact hconst.tendsto_nhds tendsto_const_nhds

/-- **Orientation recovery** (ULF-FTGM-1, (4.4)). -/
theorem eventually_directedTransferDensity_lt (hβ : 0 < β) (hlt : β < α) (hd : 1 < d) :
    ∀ᶠ j : ℕ in atTop,
      directedTransferDensity α β d j < directedTransferDensity β α d j := by
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hgap : (0 : ℝ) < (α : ℝ) - (β : ℝ) := by
    have : (β : ℝ) < (α : ℝ) := hlt
    linarith
  have hnum := isEquivalent_directedTransferDensity_reverse hβ hlt hd
  have hfwd := isEquivalent_directedTransferDensity_forward hβ hlt hd
  have hposneg : ∀ᶠ j : ℕ in atTop, 0 < directedTransferDensity β α d j :=
    hnum.eventually_pos (Filter.Eventually.of_forall fun j => by positivity)
  have hquot : Tendsto (fun j : ℕ =>
      directedTransferDensity α β d j / directedTransferDensity β α d j) atTop (𝓝 0) := by
    have hq := hfwd.div hnum
    have hzero : Tendsto (fun j : ℕ => (((α : ℝ) - (β : ℝ)) * (d : ℝ) ^ j)⁻¹) atTop (𝓝 0) := by
      refine Filter.Tendsto.inv_tendsto_atTop ?_
      exact Filter.Tendsto.const_mul_atTop hgap (tendsto_pow_atTop_atTop_of_one_lt hdR)
    have hcongr : (fun j : ℕ => (((α : ℝ) - (β : ℝ)) * (d : ℝ) ^ j)⁻¹) ~[atTop]
        fun j : ℕ => directedTransferDensity α β d j / directedTransferDensity β α d j := by
      refine (hq.congr_right (Filter.Eventually.of_forall fun j => ?_)).symm
      simp only [Pi.div_apply]
      have hpow : (0 : ℝ) < (d : ℝ) ^ j := by positivity
      have hE : Real.exp (-((β : ℝ) * (d : ℝ) ^ j)) ≠ 0 := Real.exp_ne_zero _
      field_simp
    exact hcongr.tendsto_nhds hzero
  filter_upwards [hposneg, hquot.eventually (eventually_lt_nhds one_pos)] with j hp hr
  exact (div_lt_one hp).1 hr

/-- **Rate-gap recovery in unoriented form** (ULF-FTGM-1, (4.3)). -/
theorem tendsto_directedTransferDensity_maxmin (hβ : 0 < β) (hlt : β < α) (hd : 1 < d) :
    Tendsto (fun j : ℕ =>
        max (directedTransferDensity α β d j) (directedTransferDensity β α d j) /
        ((d : ℝ) ^ j * min (directedTransferDensity α β d j) (directedTransferDensity β α d j)))
      atTop (𝓝 ((α : ℝ) - (β : ℝ))) := by
  refine (tendsto_directedTransferDensity_ratio hβ hlt hd).congr' ?_
  filter_upwards [eventually_directedTransferDensity_lt hβ hlt hd] with j hj
  rw [max_eq_right hj.le, min_eq_left hj.le]

end Orientation

end Directed

/-! ## Reflected prime packets -/

section Reflected

theorem exp_reflectedSourceRate_sub_one (p : Nat.Primes) (t : ℝ) :
    Real.exp ((reflectedSourceRate p t : ℝ)) - 1 = (p : ℝ) ^ (t - 1) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [coe_reflectedSourceRate, Real.exp_log (by positivity)]
  ring

/-- **Reflected-parameter recovery from the ordered rate pair** (ULF-FTGM-1, (5.3)). -/
theorem reflectedSourceRate_recovery (p : Nat.Primes) (t : ℝ) :
    1 / (2 * Real.log (p : ℝ)) *
        Real.log ((Real.exp ((reflectedSourceRate p t : ℝ)) - 1) /
          (Real.exp ((reflectedSourceRate p (-t) : ℝ)) - 1)) = t := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hlog : Real.log (p : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hp1)
  rw [exp_reflectedSourceRate_sub_one, exp_reflectedSourceRate_sub_one,
    ← Real.rpow_sub hp0, Real.log_rpow hp0,
    show (t - 1) - (-t - 1) = 2 * t from by ring]
  field_simp

/-- The reflected rate pair is ordered by the sign of the reflected parameter. -/
theorem reflectedSourceRate_lt_iff (p : Nat.Primes) (t : ℝ) :
    reflectedSourceRate p (-t) < reflectedSourceRate p t ↔ 0 < t := by
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rw [← NNReal.coe_lt_coe, coe_reflectedSourceRate, coe_reflectedSourceRate,
    Real.log_lt_log_iff (by positivity) (by positivity)]
  constructor
  · intro h
    have hr : (p : ℝ) ^ (-t - 1) < (p : ℝ) ^ (t - 1) := by linarith
    have := (Real.rpow_lt_rpow_left_iff hp1).1 hr
    linarith
  · intro h
    have hr : (p : ℝ) ^ (-t - 1) < (p : ℝ) ^ (t - 1) :=
      (Real.rpow_lt_rpow_left_iff hp1).2 (by linarith)
    linarith

/-- **The directed boundary germ of a reflected prime packet recovers the rate gap.**
Together with `reflectedSourceRate_recovery` this reconstructs the reflected parameter. -/
theorem tendsto_reflectedTransferDensity_maxmin {p : Nat.Primes} {t : ℝ} (ht : 0 < t) {d : ℕ}
    (hd : 1 < d) :
    Tendsto (fun j : ℕ =>
        max (directedTransferDensity (reflectedSourceRate p t) (reflectedSourceRate p (-t)) d j)
            (directedTransferDensity (reflectedSourceRate p (-t)) (reflectedSourceRate p t) d j) /
          ((d : ℝ) ^ j *
            min (directedTransferDensity (reflectedSourceRate p t)
                  (reflectedSourceRate p (-t)) d j)
                (directedTransferDensity (reflectedSourceRate p (-t))
                  (reflectedSourceRate p t) d j)))
      atTop (𝓝 ((reflectedSourceRate p t : ℝ) - (reflectedSourceRate p (-t) : ℝ))) :=
  tendsto_directedTransferDensity_maxmin (reflectedSourceRate_pos p (-t))
    ((reflectedSourceRate_lt_iff p t).2 ht) hd

end Reflected

/-! ## Exact formulas and the concrete tomography chain -/

section Concrete

variable {α β : ℝ≥0}

/-- Normalized transfer is the drop in observer work density (ULF-FTGM-1, (2.6)). -/
theorem formationInformationTransfer_div (W : ℕ → ℝ) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    formationInformationTransfer W m n / ((m : ℝ) * (n : ℝ))
      = W m / (m : ℝ) - W (m * n) / ((m : ℝ) * (n : ℝ)) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [formationInformationTransfer]
  field_simp

/-- **Symmetric observer-work density** (ULF-FTGM-1, (3.4)). -/
theorem isEquivalent_formationBooleanWork_div (hβ : 0 < β) (hlt : β < α) :
    (fun m : ℕ => formationBooleanWork α β m / (m : ℝ))
      ~[atTop] fun m : ℕ => ((α : ℝ) - (β : ℝ)) * Real.exp (-((m : ℝ) * (β : ℝ))) := by
  have hdiv := (isEquivalent_formationBooleanWork hβ hlt).div
    (Asymptotics.IsEquivalent.refl (u := fun m : ℕ => ((m : ℝ))) (l := atTop))
  refine hdiv.congr_left (Filter.Eventually.of_forall fun m => rfl) |>.congr_right ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  simp only [Pi.div_apply]
  field_simp

/-- **Directed formation cocycle** (ULF-FTGM-1, (2.4)). -/
theorem booleanForwardWork_cocycle (α β : ℝ≥0) (m n k : ℕ) :
    formationInformationTransfer (booleanForwardWork α β) m (n * k)
      = (k : ℝ) * formationInformationTransfer (booleanForwardWork α β) m n +
        formationInformationTransfer (booleanForwardWork α β) (m * n) k :=
  formationInformationTransfer_cocycle _ m n k

/-- **Symmetric formation cocycle** (ULF-FTGM-1, (2.4)). -/
theorem formationBooleanWork_cocycle (α β : ℝ≥0) (m n k : ℕ) :
    formationInformationTransfer (formationBooleanWork α β) m (n * k)
      = (k : ℝ) * formationInformationTransfer (formationBooleanWork α β) m n +
        formationInformationTransfer (formationBooleanWork α β) (m * n) k :=
  formationInformationTransfer_cocycle _ m n k

/-- **History conservation across a formation step** (ULF-FTGM-1, (2.5)). -/
theorem formationHistoryWork_mul (hα : 0 < α) (hβ : 0 < β) {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    formationHistoryWork α β (m * n)
      = (n : ℝ) * formationHistoryWork α β m +
        formationInformationTransfer (formationBooleanWork α β) m n := by
  have hcm := formation_conservation hα hβ hm
  have hcmn := formation_conservation hα hβ (Nat.mul_pos hm hn)
  rw [formationInformationTransfer, Nat.cast_mul] at *
  nlinarith [hcm, hcmn]

/-- The symmetric transfer germ is eventually positive (ULF-FTGM-1, Theorem 3.1). -/
theorem eventually_booleanTransferDensity_pos (hβ : 0 < β) (hlt : β < α) {d : ℕ} (hd : 1 < d) :
    ∀ᶠ j : ℕ in atTop, 0 < booleanTransferDensity α β d j := by
  have hgap : (0 : ℝ) < (α : ℝ) - (β : ℝ) := by
    have : (β : ℝ) < (α : ℝ) := hlt
    linarith
  exact (isEquivalent_booleanTransferDensity hβ hlt hd).eventually_pos
    (Filter.Eventually.of_forall fun j => by positivity)

/-- **The smaller rate is the germ decay slope** (ULF-FTGM-1, (3.6)). -/
theorem tendsto_neg_log_booleanTransferDensity (hβ : 0 < β) (hlt : β < α) {d : ℕ} (hd : 1 < d) :
    Tendsto (fun j : ℕ => -Real.log (booleanTransferDensity α β d j) / (d : ℝ) ^ j)
      atTop (𝓝 (β : ℝ)) := by
  have hgap : (0 : ℝ) < (α : ℝ) - (β : ℝ) := by
    have : (β : ℝ) < (α : ℝ) := hlt
    linarith
  exact tendsto_neg_log_germ_div hgap hd (isEquivalent_booleanTransferDensity hβ hlt hd)

/-- **The rate gap is the germ scaling defect** (ULF-FTGM-1, (3.7)). -/
theorem tendsto_booleanTransferDensity_scale (hβ : 0 < β) (hlt : β < α) {d : ℕ} (hd : 1 < d) :
    Tendsto (fun j : ℕ =>
        booleanTransferDensity α β d (j + 1) / (booleanTransferDensity α β d j) ^ d)
      atTop (𝓝 (((α : ℝ) - (β : ℝ)) / ((α : ℝ) - (β : ℝ)) ^ d)) := by
  have hgap : (0 : ℝ) < (α : ℝ) - (β : ℝ) := by
    have : (β : ℝ) < (α : ℝ) := hlt
    linarith
  exact tendsto_germ_scale_ratio hgap (isEquivalent_booleanTransferDensity hβ hlt hd)

/-- The scaling defect determines the rate gap (ULF-FTGM-1, (3.7), inverse form). -/
theorem rpow_scaleRatio_recovery {Δ : ℝ} (hΔ : 0 < Δ) {d : ℕ} (hd : 1 < d) :
    (Δ / Δ ^ d) ^ (-(1 : ℝ) / ((d : ℝ) - 1)) = Δ := by
  have hdR : (1 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd1 : ((d : ℝ) - 1) ≠ 0 := by linarith
  have hpow : Δ / Δ ^ d = Δ ^ ((1 : ℝ) - (d : ℝ)) := by
    rw [Real.rpow_sub hΔ, Real.rpow_one, ← Real.rpow_natCast Δ d]
  rw [hpow, ← Real.rpow_mul hΔ.le,
    show ((1 : ℝ) - (d : ℝ)) * (-(1 : ℝ) / ((d : ℝ) - 1)) = 1 from by
      field_simp
      ring,
    Real.rpow_one]

/-- **Rate gap read off any limit of the germ scaling ratio** (ULF-FTGM-1, (3.7)). -/
theorem booleanTransferDensity_gap_of_scale_limit (hβ : 0 < β) (hlt : β < α) {d : ℕ} (hd : 1 < d)
    {L : ℝ} (hL : Tendsto (fun j : ℕ =>
      booleanTransferDensity α β d (j + 1) / (booleanTransferDensity α β d j) ^ d)
      atTop (𝓝 L)) :
    L ^ (-(1 : ℝ) / ((d : ℝ) - 1)) = (α : ℝ) - (β : ℝ) := by
  have hgap : (0 : ℝ) < (α : ℝ) - (β : ℝ) := by
    have : (β : ℝ) < (α : ℝ) := hlt
    linarith
  rw [tendsto_nhds_unique hL (tendsto_booleanTransferDensity_scale hβ hlt hd)]
  exact rpow_scaleRatio_recovery hgap hd

/-- The symmetric transfer germ is invariant under rate exchange, while the directed germs are
exchanged: the functional-equation label swap is an isometry of the symmetric germ and an
orientation reversal of the directed germ (ULF-FTGM-1, (5.1)). -/
theorem booleanTransferDensity_swap (α β : ℝ≥0) (d j : ℕ) :
    booleanTransferDensity β α d j = booleanTransferDensity α β d j := by
  rw [booleanTransferDensity, booleanTransferDensity, formationBooleanWork_symm α β,
    formationBooleanWork_symm α β]

end Concrete

end

end GaloisForLFunctions.HTGeometry
