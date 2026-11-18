import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.IntegerQuadratureAsAFractionalPartConvolution
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheFractionalPartTestOfThePrimeWave
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeWaveAtTheWallIsTheBoundedOrderOfTheWallLaw

/-!
# The state weights after the fractional test

Testing a single integer before Abel summation differentiates the floor
primitive. A moving cutoff on the right removes an explicit integral of the
profile between that cutoff and its wall.
-/

noncomputable section
open MeasureTheory Filter Set Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory

/-- Oriented weight at integer abscissa exp(p) after applying the original test. -/
def testedIntegerWeight (Φ : ℝ → ℝ) (T p : ℝ) : ℝ :=
  ∫ t, (∫ v, Φ v)*continuousIntegerAtom Φ (Real.exp p) t*fractionalPrimeTest (T-t)

private theorem atom_at_log_abscissa (Φ : ℝ → ℝ) (p t : ℝ) :
    continuousIntegerAtom Φ (Real.exp p) t = Real.exp (-p/2)*Φ (t-p) := by
  rw [continuousIntegerAtom,Real.log_exp,← Real.exp_half,neg_div,Real.exp_neg]

private theorem fractional_test_eq_neg_floor (v : ℝ) :
    fractionalPrimeTest v = -weightedFloorDiscrepancy (1/2) v := by
  rw [fractionalPrimeTest,weightedFloorDiscrepancy,neg_mul,neg_neg,
    show -(1/2:ℝ)*v = -v/2 by ring]

/-- Translation of the original kernel identifies the tested weight with
the untilted integer primitive at the reflected logarithmic abscissa. -/
theorem testedIntegerWeight_eq_primitive {Φ : ℝ → ℝ} (hc : Continuous Φ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v))
    (hp : Integrable fun v : ℝ => Real.exp (-v/2)*Φ v)
    (hm : Integrable fun v : ℝ => Real.exp (v/2)*Φ v) (T p : ℝ) :
    testedIntegerWeight Φ T p = -(∫ v, Φ v)*Real.exp (-p/2)*weightedIntegerPrimitive Φ 0 (T-p) := by
  let g := fun v : ℝ => weightedFloorDiscrepancy (1/2) (T-p-v)*Φ v
  have hg : weightedIntegerPrimitive Φ 0 (T-p) = ∫ v, g v := by
    rw [weightedIntegerPrimitive_eq_convolution hc hC hb hp hm]
    simp only [sub_zero,zero_mul,Real.exp_zero,one_mul,g]
  rw [testedIntegerWeight,hg,← integral_sub_right_eq_self g p,← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only [g]
  rw [atom_at_log_abscissa,fractional_test_eq_neg_floor,show T-p-(t-p)=T-t by ring]
  ring

/-- Differentiating the tested weight in log abscissa leaves exactly the
integer wave minus its polar term. The profile is only required to be continuous. -/
theorem hasDerivAt_testedIntegerWeight {Φ : ℝ → ℝ} (hc : Continuous Φ) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v))
    (hp : Integrable fun v : ℝ => Real.exp (-v/2)*Φ v)
    (hm : Integrable fun v : ℝ => Real.exp (v/2)*Φ v) (T p : ℝ) :
    HasDerivAt (testedIntegerWeight Φ T)
      ((∫ v, Φ v)*Real.exp (-p/2)*(integerReferenceWave Φ (T-p)-
        Real.exp ((T-p)/2)*(∫ v, Real.exp (-v/2)*Φ v))) p := by
  have he := (((hasDerivAt_id p).neg.div_const 2).exp).const_mul (-(∫ v, Φ v))
  have ha := (hasDerivAt_weightedIntegerPrimitive hc hC hb 0 (T-p)).comp p
    ((hasDerivAt_id p).const_sub T)
  rw [show testedIntegerWeight Φ T = fun x => -(∫ v, Φ v)*Real.exp (-x/2)*
    weightedIntegerPrimitive Φ 0 (T-x) from funext (testedIntegerWeight_eq_primitive hc hC hb hp hm T)]
  have h := he.mul ha
  change HasDerivAt (fun x => -(∫ v, Φ v)*Real.exp (-x/2)*weightedIntegerPrimitive Φ 0 (T-x))
    ((-(∫ v, Φ v)*(Real.exp (-p/2)*(-1/2)))*weightedIntegerPrimitive Φ 0 (T-p)+
    (-(∫ v, Φ v)*Real.exp (-p/2))*((-(1/2-0)*weightedIntegerPrimitive Φ 0 (T-p)+
      Real.exp (0*(T-p))*(integerReferenceWave Φ (T-p)-Real.exp ((T-p)/2)*
        (∫ v, Real.exp (-v/2)*Φ v)))*(-1))) p at h
  simp only [sub_zero,zero_mul,Real.exp_zero,one_mul] at h
  convert h using 1
  ring

private theorem tested_atom_integrable {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (T p : ℝ) : Integrable (fun t => (∫ v, Φ v)*continuousIntegerAtom Φ (Real.exp p) t*
      fractionalPrimeTest (T-t)) := by
  simp only [atom_at_log_abscissa]
  let a := (∫ v, Φ v)*Real.exp (-p/2)
  have hf := ((hi.comp_sub_right p).const_mul a).norm
  refine hf.mono' (((measurable_const.mul (measurable_const.mul
    (hc.measurable.comp (measurable_id.sub measurable_const)))).mul
    (measurable_fractionalPrimeTest.comp (measurable_const.sub measurable_id))).aestronglyMeasurable) ?_
  apply Eventually.of_forall fun t => ?_
  change |(∫ v, Φ v)*(Real.exp (-p/2)*Φ (t-p))*fractionalPrimeTest (T-t)| ≤ |a*Φ (t-p)|
  rw [← mul_assoc (∫ v, Φ v),abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (fractionalPrimeTest_bounds _).1

/-- For a cutoff r between the test center and the particle wall p, the
excluded part has an exact exponential price, including its moving endpoints. -/
theorem testedIntegerWeight_cut_at_wall {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (hs : ∀ v, 0 ≤ v → Φ v=0) {T r p : ℝ} (hT : T ≤ r) (hr : r ≤ p) :
    (∫ t in Iic r, (∫ v, Φ v)*continuousIntegerAtom Φ (Real.exp p) t*fractionalPrimeTest (T-t)) =
      testedIntegerWeight Φ T p - (∫ v, Φ v)*Real.exp (T/2-p)*
        (∫ v in r-p..0, Real.exp (-v/2)*Φ v) := by
  let f := fun t => (∫ v, Φ v)*continuousIntegerAtom Φ (Real.exp p) t*fractionalPrimeTest (T-t)
  have hf : Integrable f := tested_atom_integrable hc hi T p
  have hwhole : (∫ t in Iic p, f t) = testedIntegerWeight Φ T p := by
    rw [testedIntegerWeight,← integral_add_compl (measurableSet_Iic (a := p)) hf,compl_Iic]
    have hz : ∫ t in Ioi p, f t = 0 := setIntegral_eq_zero_of_forall_eq_zero fun t ht => by
      dsimp only [f]; rw [atom_at_log_abscissa,hs _ (sub_nonneg.mpr ht.le)]; ring
    change _ = (∫ t in Iic p, f t)+(∫ t in Ioi p, f t)
    rw [hz,add_zero]
  have hsplit : (∫ t in Iic r, f t)+(∫ t in r..p, f t) = testedIntegerWeight Φ T p := by
    rw [intervalIntegral.integral_of_le hr,← setIntegral_union (Iic_disjoint_Ioc le_rfl)
      measurableSet_Ioc hf.integrableOn hf.integrableOn,Iic_union_Ioc_eq_Iic hr,hwhole]
  have hcell : (∫ t in r..p, f t) = (∫ v, Φ v)*Real.exp (T/2-p)*
      (∫ v in r-p..0, Real.exp (-v/2)*Φ v) := by
    let g := fun v : ℝ => Real.exp (-v/2)*Φ v
    have hshift := intervalIntegral.integral_comp_sub_right (a := r) (b := p) g p
    rw [sub_self] at hshift
    change _ = _*(∫ v in r-p..0, g v)
    rw [← hshift,← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_of_le hr,intervalIntegral.integral_of_le hr]
    apply setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have hneg : T-t < 0 := sub_neg.mpr (hT.trans_lt ht.1)
    have hk : fractionalPrimeTest (T-t)=Real.exp ((T-t)/2) := by
      rw [fractionalPrimeTest,Int.fract_eq_self.mpr
        ⟨(Real.exp_pos _).le,Real.exp_lt_one_iff.mpr hneg⟩,← Real.exp_add]; congr 1; ring
    have hex : Real.exp (-p/2)*Real.exp ((T-t)/2)=Real.exp (T/2-p)*Real.exp (-(t-p)/2) := by
      rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
    dsimp only [f,g]; rw [atom_at_log_abscissa,hk]
    linear_combination (∫ v, Φ v)*Φ (t-p)*hex
  rw [hcell] at hsplit
  exact eq_sub_of_add_eq hsplit

/-- Log abscissa at the far edge of the critical window based at exp(r). -/
def criticalEdgeLog (r : ℝ) : ℝ :=
  r+Real.log (1+Real.exp (-r/2)*Real.sqrt r)

theorem exp_criticalEdgeLog (r : ℝ) :
    Real.exp (criticalEdgeLog r) = Real.exp r + Real.sqrt (Real.exp r*Real.log (Real.exp r)) := by
  rw [criticalEdgeLog,Real.exp_add,Real.exp_log (by positivity),Real.log_exp,
    Real.sqrt_mul (Real.exp_pos _).le,← Real.exp_half,mul_add,mul_one,← mul_assoc,← Real.exp_add]
  rw [show r + -r/2 = r/2 by ring]

/-- The cutoff t ≤ r as a function of the log center r, with its integer
abscissa following the actual far edge exp(r)+sqrt(exp(r)*r). -/
def testedCriticalComplementWeight (Φ : ℝ → ℝ) (T r : ℝ) : ℝ :=
  ∫ t in Iic r, (∫ v, Φ v)*continuousIntegerAtom Φ (Real.exp (criticalEdgeLog r)) t*
    fractionalPrimeTest (T-t)

private def edgeSpeed (r : ℝ) : ℝ :=
  1 + (Real.exp (-r/2)/(2*Real.sqrt r) - Real.exp (-r/2)*Real.sqrt r/2)/
    (1+Real.exp (-r/2)*Real.sqrt r)

private theorem criticalEdgeLog_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt criticalEdgeLog (edgeSpeed r) r := by
  have hd := (((hasDerivAt_id r).neg.div_const 2).exp).mul ((hasDerivAt_id r).sqrt hr.ne')
  have h := (hasDerivAt_id r).add ((hd.const_add 1).log (by
    change 1+Real.exp (-r/2)*Real.sqrt r ≠ 0
    positivity))
  change HasDerivAt criticalEdgeLog (1+
    (Real.exp (-r/2)*(-1/2)*Real.sqrt r+Real.exp (-r/2)*(1/(2*Real.sqrt r)))/
    (1+Real.exp (-r/2)*Real.sqrt r)) r at h
  convert h using 1
  unfold edgeSpeed
  ring

private theorem criticalEdgeLog_gt {r : ℝ} (hr : 0 < r) : r < criticalEdgeLog r :=
  lt_add_of_pos_right _ (Real.log_pos (lt_add_of_pos_right 1 (mul_pos
    (Real.exp_pos _) (Real.sqrt_pos.mpr hr))))

/-- Differentiating the truncated original test along the moving edge. The
last summand is the value of the state exactly where the first window ends. -/
theorem deriv_testedCriticalComplementWeight {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (hs : ∀ v, 0 ≤ v → Φ v=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v))
    (hp : Integrable fun v : ℝ => Real.exp (-v/2)*Φ v)
    (hm : Integrable fun v : ℝ => Real.exp (v/2)*Φ v) {T r : ℝ} (hr : 0 < r) (hT : T < r) :
    let p := criticalEdgeLog r
    let d := edgeSpeed r
    let q := r-p
    let m := ∫ v, Φ v
    let g := fun v : ℝ => Real.exp (-v/2)*Φ v
    Real.exp (p-T/2)*deriv (testedCriticalComplementWeight Φ T) r =
      d*(m*Real.exp (-(T-p)/2)*integerReferenceWave Φ (T-p)-m*(∫ v, g v)+m*(∫ v in q..0, g v))+
        (1-d)*m*g q := by
  let p := criticalEdgeLog r
  let d := edgeSpeed r
  let q := r-p
  let m := ∫ v, Φ v
  let g := fun v : ℝ => Real.exp (-v/2)*Φ v
  have hgc : Continuous g := by dsimp only [g]; fun_prop
  let J := fun z : ℝ => ∫ v in 0..z, g v
  have hJ : HasDerivAt J (g q) q := (hgc.integral_hasStrictDerivAt 0 q).hasDerivAt
  have hd := criticalEdgeLog_hasDerivAt hr
  have hfirst := (hasDerivAt_testedIntegerWeight hc hC hb hp hm T p).comp r hd
  have hcoef := ((hd.const_sub (T/2)).exp).const_mul m
  have hmar := hcoef.mul (hJ.comp r ((hasDerivAt_id r).sub hd))
  have hdif := hfirst.add hmar
  have heq : testedCriticalComplementWeight Φ T =ᶠ[𝓝 r]
      fun x => testedIntegerWeight Φ T (criticalEdgeLog x)+m*Real.exp (T/2-criticalEdgeLog x)*J (x-criticalEdgeLog x) := by
    filter_upwards [Ioi_mem_nhds hr,Ioi_mem_nhds hT] with x hx hTx
    rw [testedCriticalComplementWeight,testedIntegerWeight_cut_at_wall hc hi hs hTx.le
      (criticalEdgeLog_gt hx).le,intervalIntegral.integral_symm (a := 0) (b := x-criticalEdgeLog x)]
    dsimp only [m,J,g]; ring
  have H := (hdif.congr_of_eventuallyEq heq).deriv
  change Real.exp (p-T/2)*deriv (testedCriticalComplementWeight Φ T) r = _
  rw [H]
  have e1 : Real.exp (p-T/2)*Real.exp (-p/2) = Real.exp (-(T-p)/2) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (p-T/2)*Real.exp (T/2-p) = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have e3 : Real.exp (-(T-p)/2)*Real.exp ((T-p)/2) = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  change Real.exp (p-T/2)*
    (m*Real.exp (-p/2)*(integerReferenceWave Φ (T-p)-Real.exp ((T-p)/2)*(∫ v, g v))*d+
    (m*(Real.exp (T/2-p)* (-d))*J q+m*Real.exp (T/2-p)*(g q*(1-d)))) = _
  rw [show J q = -(∫ v in q..0, g v) from intervalIntegral.integral_symm q 0]
  linear_combination m*d*(integerReferenceWave Φ (T-p)-Real.exp ((T-p)/2)*(∫ v, g v))*e1 -
    m*d*(∫ v, g v)*e3 + (m*d*(∫ v in q..0, g v)+(1-d)*m*g q)*e2

private theorem criticalEdgeLog_limits :
    Tendsto (fun r => r-criticalEdgeLog r) atTop (𝓝 0) ∧ Tendsto edgeSpeed atTop (𝓝 1) := by
  let v := fun r : ℝ => Real.exp (-r/2)*Real.sqrt r
  have hv : Tendsto v atTop (𝓝 0) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1/2) (1/2) (by norm_num)
    simpa only [v,Real.sqrt_eq_rpow,show ∀ r : ℝ, -(1/2)*r = -r/2 by intro r; ring,mul_comm] using h
  have hone : Tendsto (fun r => 1+v r) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1:ℝ))).add hv
  have he : Tendsto (fun r : ℝ => Real.exp (-r/2)) atTop (𝓝 0) := by
    apply (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/2:ℝ)<0))).congr
    intro r
    change Real.exp ((-1/2)*r) = Real.exp (-r/2)
    congr 1; ring
  have hinv := tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.const_mul_atTop (by norm_num : (0:ℝ)<2))
  have hv' : Tendsto (fun r : ℝ => Real.exp (-r/2)/(2*Real.sqrt r)-v r/2) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,div_eq_mul_inv,zero_mul,sub_zero] using (he.mul hinv).sub (hv.div_const 2)
  constructor
  · have h := ((Real.continuousAt_log one_ne_zero).tendsto.comp hone).neg
    simp only [Function.comp_apply,Real.log_one,neg_zero] at h
    exact h.congr fun r => by dsimp only [criticalEdgeLog,v]; ring
  · have h := (tendsto_const_nhds (x := (1:ℝ))).add (hv'.div hone one_ne_zero)
    rw [zero_div,add_zero] at h
    exact h.congr fun _ => rfl

private theorem normalizedIntegerReference_atBot {Φ : ℝ → ℝ} {C : ℝ}
    (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v)) :
    Tendsto (fun s => Real.exp (-s/2)*integerReferenceWave Φ s) atBot (𝓝 0) := by
  let a := fun n : ℕ => 1/(n:ℝ)^2
  have ha : Summable a := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have hN (s : ℝ) : |integerReferenceWave Φ s| ≤ (C*Real.exp (2*s))*(∑' n, a n) := by
    rw [← tsum_continuousIntegerAtom hb,← tsum_mul_left]
    have hs := (summable_continuousIntegerAtom hb s).norm
    apply (show |∑' n : ℕ, continuousIntegerAtom Φ n s| ≤ ∑' n : ℕ, ‖continuousIntegerAtom Φ n s‖
      from norm_tsum_le_tsum_norm hs).trans
    apply hs.tsum_le_tsum _ (ha.mul_left _)
    intro n
    rw [Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [continuousIntegerAtom,a]
    exact continuousIntegerAtom_bound hb (by exact_mod_cast hn : (1:ℝ) ≤ n) s
  have hl : Tendsto (fun s : ℝ => C*(∑' n, a n)*Real.exp ((3/2)*s)) atBot (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply,id_eq] using
      (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (by norm_num : (0:ℝ)<3/2))).const_mul
        (C*(∑' n, a n))
  apply squeeze_zero_norm' (Eventually.of_forall fun s => ?_) hl
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (Real.exp_pos _)]
  apply (mul_le_mul_of_nonneg_left (hN s) (Real.exp_pos _).le).trans_eq
  have h : Real.exp (-s/2)*Real.exp (2*s) = Real.exp ((3/2)*s) := by
    rw [← Real.exp_add]; congr 1; ring
  linear_combination C*(∑' n, a n)*h

/-- Along every far-edge regime with r and r−T tending to infinity, the
scaled derivative of the actual truncated weight converges to the signed
polar charge. T is held fixed when the derivative in r is taken. -/
theorem riemannHypothesis_or_far_edge_tested_weight_slope : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ T : ℝ → ℝ, Tendsto (fun r => r-T r) atTop atTop →
        Tendsto (fun r => Real.exp (criticalEdgeLog r-T r/2)*
          deriv (testedCriticalComplementWeight Φ (T r)) r) atTop
            (𝓝 (-(∫ v, Φ v)*(∫ v, Real.exp (-v/2)*Φ v))) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hc,he,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hw {b : ℝ} (ha : -4 < b) : Integrable fun v => Real.exp (b*v)*Φ v := by
    apply (integrable_mul_exp_of_domain hd ha).congr
    filter_upwards [he] with v hv
    rw [hv,mul_comm]
  have hp : Integrable fun v : ℝ => Real.exp (-v/2)*Φ v := by
    simpa only [show ∀ v : ℝ, (-1/2)*v=-v/2 by intro v; ring] using hw (by norm_num : (-4:ℝ)< -1/2)
  have hm : Integrable fun v : ℝ => Real.exp (v/2)*Φ v := by
    simpa only [show ∀ v : ℝ, (1/2)*v=v/2 by intro v; ring] using hw (by norm_num : (-4:ℝ)< 1/2)
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,fun T hT => ?_⟩
  let m := ∫ v, Φ v
  let g := fun v : ℝ => Real.exp (-v/2)*Φ v
  let A := ∫ v, g v
  let q := fun r => r-criticalEdgeLog r
  let s := fun r => T r-criticalEdgeLog r
  have hgc : Continuous g := by dsimp only [g]; fun_prop
  obtain ⟨hq,hd'⟩ := criticalEdgeLog_limits
  have hs' : Tendsto s atTop atBot := by
    apply tendsto_atBot_mono' _ _ (tendsto_neg_atTop_atBot.comp hT)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    change T r-criticalEdgeLog r ≤ -(r-T r)
    linarith only [criticalEdgeLog_gt hr]
  have hn := (normalizedIntegerReference_atBot hb).comp hs'
  have hg : Tendsto (fun r => g (q r)) atTop (𝓝 (g 0)) := hgc.continuousAt.tendsto.comp hq
  have hj : Tendsto (fun r => ∫ v in q r..0, g v) atTop (𝓝 0) := by
    have hj' := ((hgc.integral_hasStrictDerivAt 0 0).hasDerivAt.continuousAt.tendsto.comp hq).neg
    simp only [intervalIntegral.integral_same,neg_zero,Function.comp_apply] at hj'
    exact hj'.congr fun r => (intervalIntegral.integral_symm 0 (q r)).symm
  have hlim := (hd'.mul (((hn.const_mul m).sub_const (m*A)).add (hj.const_mul m))).add
    ((((tendsto_const_nhds (x := (1:ℝ))).sub hd').mul_const m).mul hg)
  simp only [mul_zero,zero_sub,add_zero,one_mul,sub_self,zero_mul] at hlim
  rw [neg_mul]
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ),hT.eventually_gt_atTop 0] with r hr hTr
  have hdif := deriv_testedCriticalComplementWeight hc (hd.integrable.congr he) hs hC hb hp hm hr
    (sub_pos.mp hTr)
  dsimp only [Function.comp_apply]
  simpa only [m,A,g,q,s,mul_assoc] using hdif.symm

/-- The moving time cut is exactly the set of times when the abscissa lies
beyond the arithmetic window. Its boundary is a single null point. -/
theorem testedCriticalComplementWeight_eq_original_window (Φ : ℝ → ℝ) (T r : ℝ) :
    testedCriticalComplementWeight Φ T r =
      ∫ t in {t : ℝ | Real.exp t+Real.sqrt (Real.exp t*Real.log (Real.exp t)) <
          Real.exp (criticalEdgeLog r)}, (∫ v, Φ v)*
          continuousIntegerAtom Φ (Real.exp (criticalEdgeLog r)) t*fractionalPrimeTest (T-t) := by
  let g := fun t : ℝ => Real.exp t+Real.sqrt (Real.exp t*Real.log (Real.exp t))
  have hmono : StrictMono g := by
    intro x y hxy
    dsimp only [g]
    rw [Real.log_exp,Real.log_exp,Real.sqrt_mul (Real.exp_pos x).le,
      Real.sqrt_mul (Real.exp_pos y).le]
    exact add_lt_add_of_lt_of_le (Real.exp_lt_exp.mpr hxy)
      (mul_le_mul (Real.sqrt_le_sqrt (Real.exp_le_exp.mpr hxy.le)) (Real.sqrt_le_sqrt hxy.le)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have heq : {t : ℝ | g t < Real.exp (criticalEdgeLog r)} = Iio r := by
    ext t
    change g t < Real.exp (criticalEdgeLog r) ↔ t < r
    rw [exp_criticalEdgeLog]
    exact hmono.lt_iff_lt
  rw [testedCriticalComplementWeight,heq,integral_Iic_eq_integral_Iio]

#print axioms testedCriticalComplementWeight_eq_original_window
#print axioms testedIntegerWeight_cut_at_wall
#print axioms riemannHypothesis_or_far_edge_tested_weight_slope
end GaloisForLFunctions.ExclusionOfTheCriticalState
