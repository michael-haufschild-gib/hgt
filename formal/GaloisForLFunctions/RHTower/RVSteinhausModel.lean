import GaloisForLFunctions.RHTower.SteinhausChernoff
import GaloisForLFunctions.RHTower.RVCumulantLimit
import GaloisForLFunctions.HTGeometry.SteinhausSharpAsymptotic
import GaloisForLFunctions.RHTower.SteinhausCriticalRate

/-!
# The regular-variation Steinhaus model

The card's `Y_X = ∑_{p ≤ X} a_{p,X} U_p`.  The index type is the finite set of primes up to `X`,
the weights are `a_{p,X} = (log p)p^{−α}L(p)/W_X`, and `d_X a_{p,X}` is exactly the `rvNormReal` of
`(10)`.  The weights sum to one, so the model is supported in the closed unit disk and every
modulus below one is attained on a nonempty open set — which makes the deviation probability
strictly positive.
-/

open MeasureTheory Filter Topology HTGeometry

namespace RHTower

local instance phaseCirclePositiveModel : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

/-- The primes up to `X`. -/
def rvPrimeFinset (X : ℝ) : Finset ℕ := (Finset.Ioc 0 ⌊X⌋₊).filter (fun p => Nat.Prime p)

/-- The normalized weights of the model. -/
def rvWeightFun (α : ℝ) (L : ℝ → ℝ) (X : ℝ) : ↥(rvPrimeFinset X) → ℝ :=
  fun i => Real.log i.val * rvPrimeWeight α L i.val / rvWeightSum α L X

theorem rvPrimeCount_mul_rvWeightFun {α : ℝ} {L : ℝ → ℝ} {X : ℝ}
    (i : ↥(rvPrimeFinset X)) :
    rvPrimeCount X * rvWeightFun α L X i = rvNormReal α L X i.val := by
  rw [rvWeightFun, rvNormReal]
  ring

theorem sum_rvWeightFun {α : ℝ} {L : ℝ → ℝ} {X : ℝ} (hW : rvWeightSum α L X ≠ 0) :
    ∑ i : ↥(rvPrimeFinset X), rvWeightFun α L X i = 1 := by
  have hsum : ∑ i : ↥(rvPrimeFinset X), rvWeightFun α L X i
      = (∑ p ∈ rvPrimeFinset X, Real.log p * rvPrimeWeight α L p) / rvWeightSum α L X := by
    rw [Finset.sum_div]
    exact Finset.sum_coe_sort (rvPrimeFinset X)
      (fun p : ℕ => Real.log p * rvPrimeWeight α L p / rvWeightSum α L X)
  rw [hsum]
  have hnum : (∑ p ∈ rvPrimeFinset X, Real.log p * rvPrimeWeight α L p) = rvWeightSum α L X := by
    rw [rvWeightSum, primeLogSum, Nat.floor_zero]
    rfl
  rw [hnum, div_self hW]

theorem rvWeightFun_nonneg {α : ℝ} {L : ℝ → ℝ} (hL : IsSlowlyVarying L) {X : ℝ}
    (hW : 0 < rvWeightSum α L X) (i : ↥(rvPrimeFinset X)) : 0 ≤ rvWeightFun α L X i := by
  have hmem := i.2
  simp only [rvPrimeFinset, Finset.mem_filter, Finset.mem_Ioc] at hmem
  have hprime : Nat.Prime i.val := hmem.2
  have hp1 : (1 : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hprime.one_lt.le
  have hp0 : (0 : ℝ) < (i.val : ℝ) := lt_of_lt_of_le one_pos hp1
  have hlog : 0 ≤ Real.log i.val := Real.log_nonneg hp1
  have hw : 0 ≤ rvPrimeWeight α L i.val := rvPrimeWeight_nonneg hL hp0
  rw [rvWeightFun]
  positivity

/-- The tilted cumulant sum of the model is the prime average of `(12)`. -/
theorem sum_steinhausLogLaplace_rvWeightFun {α : ℝ} {L : ℝ → ℝ} {lam X : ℝ} :
    ∑ i : ↥(rvPrimeFinset X),
        steinhausLogLaplace (lam * rvPrimeCount X * rvWeightFun α L X i)
      = primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 X := by
  rw [primeCountSum]
  have hid : ∀ i : ↥(rvPrimeFinset X),
      steinhausLogLaplace (lam * rvPrimeCount X * rvWeightFun α L X i)
        = steinhausLogLaplace (lam * rvNormReal α L X i.val) := by
    intro i
    rw [mul_assoc, rvPrimeCount_mul_rvWeightFun]
  have hsum : ∑ i : ↥(rvPrimeFinset X),
      steinhausLogLaplace (lam * rvNormReal α L X i.val)
      = ∑ p ∈ rvPrimeFinset X, steinhausLogLaplace (lam * rvNormReal α L X p) :=
    Finset.sum_coe_sort (rvPrimeFinset X)
      (fun p : ℕ => steinhausLogLaplace (lam * rvNormReal α L X (p : ℝ)))
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hid i, hsum, Nat.floor_zero]
  rfl


/-- The deviation probability of the model. -/
def rvDeviationProb (α : ℝ) (L : ℝ → ℝ) (X q : ℝ) : ℝ :=
  ((Measure.pi fun _ : ↥(rvPrimeFinset X) => AddCircle.haarAddCircle)
    {x | q ≤ ‖steinhausSum (rvWeightFun α L X) x‖}).toReal

theorem steinhausPhase_zero : steinhausPhase 0 = 1 := by
  rw [steinhausPhase]
  simp

/-- **The deviation probability is strictly positive below the boundary.** -/
theorem rvDeviationProb_pos {α : ℝ} {L : ℝ → ℝ} {X q : ℝ} (hq : q < 1)
    (hW : rvWeightSum α L X ≠ 0) : 0 < rvDeviationProb α L X q := by
  set μ : Measure (↥(rvPrimeFinset X) → PhaseCircle) :=
    Measure.pi fun _ : ↥(rvPrimeFinset X) => AddCircle.haarAddCircle with hμ
  set U : Set (↥(rvPrimeFinset X) → PhaseCircle) :=
    {x | q < ‖steinhausSum (rvWeightFun α L X) x‖} with hU
  have hopen : IsOpen U := by
    rw [hU]
    exact isOpen_lt continuous_const (continuous_steinhausSum_norm _)
  have hmem : (0 : ↥(rvPrimeFinset X) → PhaseCircle) ∈ U := by
    rw [hU, Set.mem_setOf_eq, steinhausSum]
    have hz : ∀ i : ↥(rvPrimeFinset X),
        ((rvWeightFun α L X i : ℂ)) * steinhausPhase (0 : PhaseCircle)
          = ((rvWeightFun α L X i : ℂ)) := by
      intro i
      rw [steinhausPhase_zero, mul_one]
    have hsum : ∑ i : ↥(rvPrimeFinset X),
        ((rvWeightFun α L X i : ℂ)) * steinhausPhase ((0 : ↥(rvPrimeFinset X) → PhaseCircle) i)
        = ((∑ i : ↥(rvPrimeFinset X), rvWeightFun α L X i : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => hz i
    rw [hsum, sum_rvWeightFun hW]
    simpa using hq
  have hne : U.Nonempty := ⟨0, hmem⟩
  have hUpos : 0 < μ U := hopen.measure_pos μ hne
  have hsub : U ⊆ {x | q ≤ ‖steinhausSum (rvWeightFun α L X) x‖} := by
    intro x hx
    rw [hU, Set.mem_setOf_eq] at hx
    exact le_of_lt hx
  have hle : μ U ≤ μ {x | q ≤ ‖steinhausSum (rvWeightFun α L X) x‖} := measure_mono hsub
  have hfin : μ {x | q ≤ ‖steinhausSum (rvWeightFun α L X) x‖} ≠ ⊤ := measure_ne_top μ _
  rw [rvDeviationProb, ← hμ]
  rw [ENNReal.toReal_pos_iff]
  exact ⟨lt_of_lt_of_le hUpos hle, lt_of_le_of_ne le_top hfin⟩

/-- **The Chernoff bound for the model.** -/
theorem log_rvDeviationProb_le {α : ℝ} {L : ℝ → ℝ} {lam X q : ℝ} (hlam : 0 ≤ lam)
    (hq : 0 ≤ q) (hqlt : q < 1) (hW : rvWeightSum α L X ≠ 0) :
    Real.log (rvDeviationProb α L X q)
      ≤ primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 X
        - steinhausLogLaplace (lam * rvPrimeCount X * q) := by
  have hd0 : (0 : ℝ) ≤ rvPrimeCount X := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ lam * rvPrimeCount X := mul_nonneg hlam hd0
  have hchernoff := meas_norm_ge_mul_le (rvWeightFun α L X) ht hq
  have hP : 0 < rvDeviationProb α L X q := rvDeviationProb_pos hqlt hW
  rw [← rvDeviationProb] at hchernoff
  have hIq : 0 < steinhausLaplace (lam * rvPrimeCount X * q) := steinhausLaplace_pos _
  have hprodpos : (0 : ℝ) < ∏ i : ↥(rvPrimeFinset X),
      steinhausLaplace (lam * rvPrimeCount X * rvWeightFun α L X i) :=
    Finset.prod_pos fun i _ => steinhausLaplace_pos _
  have hlogle : Real.log (rvDeviationProb α L X q * steinhausLaplace (lam * rvPrimeCount X * q))
      ≤ Real.log (∏ i : ↥(rvPrimeFinset X),
          steinhausLaplace (lam * rvPrimeCount X * rvWeightFun α L X i)) :=
    Real.log_le_log (by positivity) hchernoff
  rw [Real.log_mul hP.ne' hIq.ne'] at hlogle
  rw [Real.log_prod (s := (Finset.univ : Finset ↥(rvPrimeFinset X)))
    (f := fun i => steinhausLaplace (lam * rvPrimeCount X * rvWeightFun α L X i))
    (fun i _ => (steinhausLaplace_pos _).ne')] at hlogle
  have hsum : ∑ i : ↥(rvPrimeFinset X),
      Real.log (steinhausLaplace (lam * rvPrimeCount X * rvWeightFun α L X i))
      = primeCountSum (fun t => steinhausLogLaplace (lam * rvNormReal α L X t)) 0 X := by
    rw [← sum_steinhausLogLaplace_rvWeightFun (α := α) (L := L) (lam := lam) (X := X)]
    rfl
  rw [hsum] at hlogle
  have hIqlog : Real.log (steinhausLaplace (lam * rvPrimeCount X * q))
      = steinhausLogLaplace (lam * rvPrimeCount X * q) := rfl
  rw [hIqlog] at hlogle
  linarith [hlogle]


theorem rvDeviationProb_le_one {α : ℝ} {L : ℝ → ℝ} {X q : ℝ} :
    rvDeviationProb α L X q ≤ 1 := by
  set μ : Measure (↥(rvPrimeFinset X) → PhaseCircle) :=
    Measure.pi fun _ : ↥(rvPrimeFinset X) => AddCircle.haarAddCircle with hμ
  have hprob : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  have hle : μ {x | q ≤ ‖steinhausSum (rvWeightFun α L X) x‖} ≤ 1 := by
    rw [← measure_univ (μ := μ)]
    exact measure_mono (Set.subset_univ _)
  rw [rvDeviationProb, ← hμ]
  have := ENNReal.toReal_le_toReal (measure_ne_top μ _) ENNReal.one_ne_top |>.2 hle
  simpa using this

/-- The sharp asymptotic in ratio form. -/
theorem tendsto_steinhausLogLaplace_div_id :
    Tendsto (fun y : ℝ => steinhausLogLaplace y / y) atTop (𝓝 1) := by
  have hsharp := tendsto_steinhausLogLaplace_sub_sharp
  have hdiv : Tendsto (fun y : ℝ =>
      (steinhausLogLaplace y - y + (1 / 2) * Real.log (2 * Real.pi * y)) / y) atTop (𝓝 0) := by
    have := hsharp.div_atTop (tendsto_id (α := ℝ))
    exact this
  have hlog : Tendsto (fun y : ℝ => (1 / 2) * Real.log (2 * Real.pi * y) / y) atTop (𝓝 0) := by
    have hbase : Tendsto (fun y : ℝ => Real.log (2 * Real.pi * y) / y) atTop (𝓝 0) := by
      have hcomp : Tendsto (fun y : ℝ => Real.log (2 * Real.pi * y) / (2 * Real.pi * y))
          atTop (𝓝 0) :=
        tendsto_log_div_id_atTop.comp (tendsto_const_mul_atTop_of_pos (by positivity))
      have hmul := hcomp.const_mul (2 * Real.pi)
      rw [mul_zero] at hmul
      refine Tendsto.congr' ?_ hmul
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
      field_simp
    have := hbase.const_mul (1 / 2)
    rw [mul_zero] at this
    refine Tendsto.congr' ?_ this
    filter_upwards with y
    ring
  have hcomb := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℝ))).add
    (hdiv.sub hlog)
  rw [sub_zero, add_zero] at hcomb
  refine Tendsto.congr' ?_ hcomb
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  field_simp
  ring

theorem tendsto_rvPrimeCount_atTop : Tendsto rvPrimeCount atTop atTop := by
  have hratio := tendsto_rvPrimeCount_ratio
  have hev : ∀ᶠ X in atTop, (1 : ℝ) / 2 ≤ rvPrimeCount X / (X / Real.log X) := by
    exact hratio.eventually (eventually_ge_nhds (by norm_num : (1 : ℝ) / 2 < 1))
  have hbase : Tendsto (fun X : ℝ => (1 / 2) * (X / Real.log X)) atTop atTop := by
    have hXlog : Tendsto (fun X : ℝ => X / Real.log X) atTop atTop := by
      have hnw : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝[>] (0 : ℝ)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          tendsto_log_div_id_atTop ?_
        filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
        have hlx : 0 < Real.log x := Real.log_pos hx
        have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
        exact div_pos hlx hx0
      have hinv := tendsto_inv_nhdsGT_zero (𝕜 := ℝ) |>.comp hnw
      refine hinv.congr fun x => ?_
      rw [Function.comp_apply, inv_div]
    exact hXlog.const_mul_atTop (by norm_num)
  refine tendsto_atTop_mono' atTop ?_ hbase
  filter_upwards [hev, eventually_gt_atTop (2 : ℝ)] with X hX hX2
  have hlX : 0 < Real.log X := Real.log_pos (by linarith)
  have hXpos : (0 : ℝ) < X / Real.log X := by positivity
  rw [le_div_iff₀ hXpos] at hX
  linarith [hX]


theorem tendsto_rvPrimeCount_logI0 {lam q : ℝ} (hlam : 0 < lam) (hq : 0 < q) :
    Tendsto (fun X : ℝ => steinhausLogLaplace (lam * rvPrimeCount X * q) / rvPrimeCount X)
      atTop (𝓝 (lam * q)) := by
  have hy : Tendsto (fun X : ℝ => lam * rvPrimeCount X * q) atTop atTop := by
    have h1 := tendsto_rvPrimeCount_atTop.const_mul_atTop hlam
    exact h1.atTop_mul_const hq
  have hratio := tendsto_steinhausLogLaplace_div_id.comp hy
  have hmul := hratio.const_mul (lam * q)
  rw [mul_one] at hmul
  refine Tendsto.congr' ?_ hmul
  filter_upwards [tendsto_rvPrimeCount_atTop.eventually_gt_atTop 0] with X hX
  rw [Function.comp_apply]
  field_simp

/-- **The large-deviation upper bound**, the upper half of the card's `(5)`. -/
theorem eventually_log_rvDeviationProb_le {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X in atTop,
      Real.log (rvDeviationProb α L X q) / rvPrimeCount X ≤ -(rvRate α q) + ε := by
  have hWpos : ∀ᶠ X in atTop, 0 < rvWeightSum α L X := by
    have hα' : (0 : ℝ) < 1 - α := by linarith
    have hlim := (tendsto_rvWeightSum hα0 hα1 hL).eventually_const_lt
      (show (0 : ℝ) < 1 / (1 - α) by positivity)
    filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with X hX hX1
    have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
    have hLX : 0 < L X := hL.pos _ hX0
    have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
    have hden : (0 : ℝ) < X ^ (1 - α) * L X := mul_pos hXpow hLX
    rw [lt_div_iff₀ hden, zero_mul] at hX
    exact hX
  rcases le_or_gt 0 (-(rvRate α q) + ε) with hnn | hneg
  · filter_upwards [tendsto_rvPrimeCount_atTop.eventually_gt_atTop 0] with X hX
    have hPnn : 0 ≤ rvDeviationProb α L X q := ENNReal.toReal_nonneg
    have hlog : Real.log (rvDeviationProb α L X q) ≤ 0 :=
      Real.log_nonpos hPnn rvDeviationProb_le_one
    have : Real.log (rvDeviationProb α L X q) / rvPrimeCount X ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hlog hX.le
    linarith
  · have hrate : ε < rvRate α q := by linarith
    obtain ⟨y, hy, hylt⟩ := exists_lt_of_lt_csSup (rvLegendreSet_nonempty α q)
      (show rvRate α q - ε / 2 < rvRate α q by linarith)
    obtain ⟨lam, hlam0, rfl⟩ := hy
    have hval : rvRate α q - ε / 2 < lam * q - rvCumulant α lam := hylt
    have hlampos : 0 < lam := by
      rcases eq_or_lt_of_le hlam0 with h | h
      · exfalso
        rw [← h, zero_mul, rvCumulant_zero, sub_zero] at hval
        linarith
      · exact h
    have hcum := (tendsto_rvCumulantAverage hα0 hα1 hL hlam0).eventually
      (eventually_lt_nhds (show rvCumulant α lam < rvCumulant α lam + ε / 4 by linarith))
    have hbess := (tendsto_rvPrimeCount_logI0 hlampos hq0).eventually
      (eventually_gt_nhds (show lam * q - ε / 4 < lam * q by linarith))
    filter_upwards [hcum, hbess, hWpos,
      tendsto_rvPrimeCount_atTop.eventually_gt_atTop 0] with X hXcum hXbess hXW hXd
    have hchernoff := log_rvDeviationProb_le (α := α) (L := L) (lam := lam) (X := X) (q := q)
      hlam0 hq0.le hq1 hXW.ne'
    have hdiv : Real.log (rvDeviationProb α L X q) / rvPrimeCount X
        ≤ rvCumulantAverage α L lam X
          - steinhausLogLaplace (lam * rvPrimeCount X * q) / rvPrimeCount X := by
      rw [div_le_iff₀ hXd, rvCumulantAverage, sub_mul, div_mul_cancel₀ _ hXd.ne',
        div_mul_cancel₀ _ hXd.ne']
      exact hchernoff
    linarith [hdiv, hXcum, hXbess, hval]

end

end RHTower
