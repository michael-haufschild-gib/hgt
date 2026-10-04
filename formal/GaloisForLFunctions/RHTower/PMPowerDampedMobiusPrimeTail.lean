import GaloisForLFunctions.RHTower.PrimeRpowAbelSummation
import GaloisForLFunctions.RHTower.PrimePowerSumBound
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusBoundaryMoments

/-!
# Prime and boundary tails for the actual power-damped Möbius source

Abel summation retains the prime-density factor in the cofactor tail. The
boundary mass tail uses the unconditional log-four source envelope. These
estimates require no canonical square-integrability premise.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace RHTower

private theorem pmt_decreasing_prime_abel {a b C : ℝ} {g g' : ℝ → ℝ}
    (ha : 2 ≤ a) (hab : a ≤ b)
    (hC : ∀ t ∈ Icc a b, Chebyshev.theta t ≤ C*t)
    (hd : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hc : ContinuousOn g' (Icc a b))
    (hg : ∀ t ∈ Icc a b, 0 ≤ g t)
    (hg' : ∀ t ∈ Icc a b, g' t ≤ 0) :
    (∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, g q*primeLogWeight_primeRpowAbelSummation q) ≤
      C*(a*g a+∫ t in Ioc a b,g t) := by
  have ha0 : 0 ≤ a := by linarith
  have hgi : IntegrableOn g (Icc a b) :=
    (show ContinuousOn g (Icc a b) from
      fun t ht => (hd t ht).continuousAt.continuousWithinAt).integrableOn_Icc
  have hgdi : IntegrableOn g' (Icc a b) := hc.integrableOn_Icc
  have hder : Set.EqOn (deriv g) g' (Icc a b) := fun t ht => (hd t ht).deriv
  have hderi : IntegrableOn (deriv g) (Icc a b) :=
    hgdi.congr_fun (fun t ht => (hder ht).symm) measurableSet_Icc
  have hs := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ)
    primeLogWeight_primeRpowAbelSummation ha0 hab
    (fun t ht => (hd t ht).differentiableAt) hderi
  simp only [sum_primeLogWeight_eq_theta] at hs
  have hti : IntegrableOn Chebyshev.theta (Icc a b) :=
    MonotoneOn.integrableOn_isCompact isCompact_Icc (Chebyshev.theta_mono.monotoneOn _)
  have hprod : IntegrableOn (fun t => g' t*Chebyshev.theta t) (Icc a b) := by
    exact (hti.mul_continuousOn hc isCompact_Icc).congr_fun
      (fun t _ => by ring) measurableSet_Icc
  have hid : IntegrableOn (fun t : ℝ => g' t*t) (Icc a b) :=
    (hc.mul continuousOn_id).integrableOn_Icc
  have himono : C*(∫ t in Ioc a b,g' t*t) ≤
      ∫ t in Ioc a b,g' t*Chebyshev.theta t := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on ((hid.mono_set Ioc_subset_Icc_self).const_mul C)
      (hprod.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
    intro t ht
    have hh := mul_le_mul_of_nonpos_left (hC t ⟨ht.1.le,ht.2⟩) (hg' t ⟨ht.1.le,ht.2⟩)
    nlinarith
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t : ℝ => t) (u' := fun _ => 1) (v := g) (v' := g')
    (fun t _ => hasDerivAt_id t)
    (fun t ht => hd t (uIcc_of_le hab ▸ ht)) intervalIntegrable_const
    ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hgdi)
  have hibp' : (∫ t in Ioc a b,g' t*t) = b*g b-a*g a-∫ t in Ioc a b,g t := by
    rw [← intervalIntegral.integral_of_le hab,← intervalIntegral.integral_of_le hab]
    simpa only [one_mul,mul_one,mul_comm] using hibp
  have hrewrite : (∫ t in Ioc a b,deriv g t*Chebyshev.theta t) =
      ∫ t in Ioc a b,g' t*Chebyshev.theta t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [hder ⟨ht.1.le,ht.2⟩]
  rw [hs,hrewrite]
  have hupper := mul_le_mul_of_nonneg_left (hC b ⟨hab,le_rfl⟩) (hg b ⟨hab,le_rfl⟩)
  have hlower := mul_nonneg (hg a ⟨le_rfl,hab⟩) (chebyshevTheta_nonneg a)
  rw [hibp'] at himono
  nlinarith

private def pmt_tailWeight (L t : ℝ) : ℝ := 1/(t*(L-Real.log t)^4*Real.log t)
private def pmt_tailWeightDeriv (L t : ℝ) : ℝ :=
  -(((L-Real.log t-4)*Real.log t+(L-Real.log t))/(t^2*(L-Real.log t)^5*Real.log t^2))

private theorem pmt_tailWeight_hasDeriv {L t : ℝ} (ht : 2 ≤ t) (hv : 0 < L-Real.log t) :
    HasDerivAt (pmt_tailWeight L) (pmt_tailWeightDeriv L t) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hd := (((hasDerivAt_id t).mul
    (((hasDerivAt_const t L).sub (Real.hasDerivAt_log ht0.ne')).pow 4)).mul
      (Real.hasDerivAt_log ht0.ne')).inv (by positivity : t*(L-Real.log t)^4*Real.log t ≠ 0)
  refine hd.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · dsimp [pmt_tailWeightDeriv]
    field_simp
    ring
  · filter_upwards with x
    simp only [pmt_tailWeight,one_div,Pi.inv_apply,Pi.mul_apply,Pi.pow_apply,Pi.sub_apply,id_eq]

private theorem pmt_tailWeightDeriv_continuousAt {L t : ℝ}
    (ht : 2 ≤ t) (hv : 0 < L-Real.log t) : ContinuousAt (pmt_tailWeightDeriv L) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos (by linarith)
  have hc := Real.continuousAt_log ht0.ne'
  have hvc : ContinuousAt (fun t : ℝ => L-Real.log t) t := continuousAt_const.sub hc
  exact (((hvc.sub continuousAt_const).mul hc).add hvc |>.div
    (((continuousAt_id.pow 2).mul (hvc.pow 5)).mul (hc.pow 2))
      (by change t^2*(L-Real.log t)^5*Real.log t^2 ≠ 0; positivity)).neg

private theorem pmt_logTail_primitive {L t : ℝ} (ht : 0 < t) (hv : 0 < L-Real.log t) :
    HasDerivAt (fun t : ℝ => 1/(3*(L-Real.log t)^3)) (1/(t*(L-Real.log t)^4)) t := by
  have hd := ((((hasDerivAt_const t L).sub (Real.hasDerivAt_log ht.ne')).pow 3).const_mul 3).inv
    (by positivity : 3*(L-Real.log t)^3 ≠ 0)
  refine hd.congr_deriv ?_ |>.congr_of_eventuallyEq ?_
  · dsimp only [Pi.pow_apply,Pi.sub_apply]
    field_simp
    ring
  · filter_upwards with x
    simp only [one_div,Pi.inv_apply,Pi.pow_apply,Pi.sub_apply]

/-- A prime-density tail estimate with the logarithmic cofactor weight retained. -/
theorem pm_prime_log_cofactor_tail :
    ∃ C > 0, ∀ L a b : ℝ, 2 ≤ a → a ≤ b → 8 ≤ L-Real.log b →
      (∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        if q.Prime then 1/((q : ℝ)*(L-Real.log q)^4) else 0) ≤
        C/(Real.log a*(L-Real.log b)^3) := by
  obtain ⟨C,hC,hCb⟩ := exists_chebyshevTheta_le_linear
  refine ⟨2*C,by positivity,?_⟩
  intro L a b ha hab hL
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hla : 0 < Real.log a := Real.log_pos (by linarith)
  have hvb : 0 < L-Real.log b := by linarith
  have hv (t : ℝ) (ht : t ∈ Icc a b) : 8 ≤ L-Real.log t := by
    have ht0 : 0 < t := ha0.trans_le ht.1
    linarith [Real.log_le_log ht0 ht.2]
  have hθ (t : ℝ) (ht : t ∈ Icc a b) : Chebyshev.theta t ≤ C*t :=
    hCb t (by linarith [ht.1])
  have hd (t : ℝ) (ht : t ∈ Icc a b) := pmt_tailWeight_hasDeriv
    (ha.trans ht.1) (by linarith [hv t ht] : 0 < L-Real.log t)
  have hdc : ContinuousOn (pmt_tailWeightDeriv L) (Icc a b) := fun t ht =>
    (pmt_tailWeightDeriv_continuousAt (ha.trans ht.1)
      (by linarith [hv t ht])).continuousWithinAt
  have hg (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ pmt_tailWeight L t := by
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hlt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    dsimp [pmt_tailWeight]
    positivity
  have hg' (t : ℝ) (ht : t ∈ Icc a b) : pmt_tailWeightDeriv L t ≤ 0 := by
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hlt : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hv4 : 0 ≤ L-Real.log t-4 := by linarith [hv t ht]
    have hv0 : 0 < L-Real.log t := by linarith [hv t ht]
    dsimp [pmt_tailWeightDeriv]
    apply neg_nonpos.mpr
    positivity
  have hs := pmt_decreasing_prime_abel ha hab hθ hd hdc hg hg'
  have hsum : (∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
      pmt_tailWeight L q*primeLogWeight_primeRpowAbelSummation q) =
      ∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        if q.Prime then 1/((q : ℝ)*(L-Real.log q)^4) else 0 := by
    apply Finset.sum_congr rfl
    intro q hq
    rw [primeLogWeight_primeRpowAbelSummation]
    split_ifs with hp
    · have hq1 : (1 : ℝ) < q := by exact_mod_cast hp.one_lt
      have hlq : Real.log (q : ℝ) ≠ 0 := (Real.log_pos hq1).ne'
      dsimp [pmt_tailWeight]
      field_simp
    · simp
  rw [hsum] at hs
  have hbasec : ContinuousOn (fun t : ℝ => 1/(t*(L-Real.log t)^4)) (Icc a b) := by
    intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    have hv0 : 0 < L-Real.log t := by linarith [hv t ht]
    exact continuousAt_const.div (continuousAt_id.mul
      ((continuousAt_const.sub (Real.continuousAt_log ht0.ne')).pow 4))
        (by change t*(L-Real.log t)^4 ≠ 0; positivity) |>.continuousWithinAt
  have hbasei : IntegrableOn (fun t : ℝ => 1/(t*(L-Real.log t)^4)) (Icc a b) :=
    hbasec.integrableOn_Icc
  have hgi : IntegrableOn (pmt_tailWeight L) (Icc a b) :=
    (show ContinuousOn (pmt_tailWeight L) (Icc a b) from
      fun t ht => (hd t ht).continuousAt.continuousWithinAt).integrableOn_Icc
  have hib : (∫ t in Ioc a b,pmt_tailWeight L t) ≤
      (1/Real.log a)*(∫ t in Ioc a b,1/(t*(L-Real.log t)^4)) := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hgi.mono_set Ioc_subset_Icc_self)
      ((hbasei.mono_set Ioc_subset_Icc_self).const_mul _) measurableSet_Ioc
    intro t ht
    have ht0 : 0 < t := ha0.trans_le ht.1.le
    have hv0 : 0 < L-Real.log t := by linarith [hv t ⟨ht.1.le,ht.2⟩]
    have hlog := Real.log_le_log ha0 ht.1.le
    have hlt : 0 < Real.log t := hla.trans_le hlog
    dsimp [pmt_tailWeight]
    have hi := one_div_le_one_div_of_le hla hlog
    calc
      _ = (1/Real.log t)*(1/(t*(L-Real.log t)^4)) := by
        simp only [one_div,mul_inv_rev]
      _ ≤ _ := mul_le_mul_of_nonneg_right hi (by positivity)
  have hprimitive : (∫ t in Ioc a b,1/(t*(L-Real.log t)^4)) =
      1/(3*(L-Real.log b)^3)-1/(3*(L-Real.log a)^3) := by
    rw [← intervalIntegral.integral_of_le hab]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => pmt_logTail_primitive (ha0.trans_le (uIcc_of_le hab ▸ ht).1)
        (by linarith [hv t (uIcc_of_le hab ▸ ht)]))
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hbasei)
  rw [hprimitive] at hib
  have hva : 0 < L-Real.log a := by linarith [hv a ⟨le_rfl,hab⟩]
  have hvab : L-Real.log b ≤ L-Real.log a := by
    linarith [Real.log_le_log ha0 hab]
  have hendpoint : a*pmt_tailWeight L a ≤ 1/(Real.log a*(L-Real.log b)^3) := by
    have hpow : (L-Real.log b)^3 ≤ (L-Real.log a)^4 := by
      have hp := pow_le_pow_left₀ hvb.le hvab 3
      have hva1 : 1 ≤ L-Real.log a := by linarith
      calc
        _ ≤ (L-Real.log a)^3 := hp
        _ ≤ (L-Real.log a)^3*(L-Real.log a) :=
          le_mul_of_one_le_right (by positivity) hva1
        _ = _ := by ring
    have hi := one_div_le_one_div_of_le (by positivity : 0 < Real.log a*(L-Real.log b)^3)
      (mul_le_mul_of_nonneg_left hpow hla.le)
    dsimp [pmt_tailWeight]
    calc
      _ = 1/(Real.log a*(L-Real.log a)^4) := by field_simp
      _ ≤ _ := hi
  have hiupper : (∫ t in Ioc a b,pmt_tailWeight L t) ≤
      1/(Real.log a*(L-Real.log b)^3) := by
    have hpos : 0 ≤ (1/Real.log a)*(1/(3*(L-Real.log a)^3)) := by positivity
    have hposb : 0 ≤ 1/(Real.log a*(L-Real.log b)^3) := by positivity
    have hid : (1/Real.log a)*(1/(3*(L-Real.log b)^3)) =
        (1/(Real.log a*(L-Real.log b)^3))/3 := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    nlinarith
  calc
    _ ≤ C*(a*pmt_tailWeight L a+∫ t in Ioc a b,pmt_tailWeight L t) := hs
    _ ≤ C*(1/(Real.log a*(L-Real.log b)^3)+1/(Real.log a*(L-Real.log b)^3)) :=
      mul_le_mul_of_nonneg_left (add_le_add hendpoint hiupper) hC.le
    _ = _ := by ring

/-- Absolute prime-tail control for the literal PM source, retaining prime density. -/
theorem pmPowerDampedFermiSource_prime_tail_bound {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ C > 0, ∃ R > 0, ∀ X a b : ℝ,
      2 ≤ a → a ≤ b → b ≤ X/R → 8 ≤ Real.log X-Real.log b →
      (∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        if q.Prime then (q : ℝ)^(-ε)*‖pmPowerDampedFermiSource ε ((q : ℝ)/X)‖ else 0) ≤
        C*X^(1-ε)/(Real.log a*(Real.log X-Real.log b)^3) := by
  obtain ⟨D,hD,he⟩ := pmPowerDampedFermiSource_reciprocal_eventually_log_four hε hεhalf
  obtain ⟨R₀,hR₀⟩ := eventually_atTop.mp he
  obtain ⟨C,hC,hCb⟩ := pm_prime_log_cofactor_tail
  let R : ℝ := max R₀ 1
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR0 : 0 < R := by linarith
  refine ⟨(D+1)*C,by positivity,R,hR0,?_⟩
  intro X a b ha hab hb hlog
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hX0 : 0 < X := by nlinarith [(le_div_iff₀ hR0).mp hb]
  have hs : (∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
      if q.Prime then (q : ℝ)^(-ε)*‖pmPowerDampedFermiSource ε ((q : ℝ)/X)‖ else 0) ≤
      (D+1)*X^(1-ε)*(∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        if q.Prime then 1/((q : ℝ)*(Real.log X-Real.log q)^4) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q hq
    split_ifs with hp
    · have hq0 : (0 : ℝ) < q := by exact_mod_cast hp.pos
      have hqb : (q : ℝ) ≤ b := (Nat.le_floor_iff hb0.le).mp (Finset.mem_Ioc.mp hq).2
      have hqR : R ≤ X/q := (le_div_iff₀ hq0).mpr (by
        nlinarith [(le_div_iff₀ hR0).mp hb])
      have hf := hR₀ (X/q) ((le_max_left _ _).trans hqR)
      have harg : 1/(X/(q : ℝ)) = (q : ℝ)/X := by field_simp
      rw [harg,Real.log_div hX0.ne' hq0.ne'] at hf
      have hpow : (q : ℝ)^(-ε)*(X/q)^(1-ε) = X^(1-ε)/(q : ℝ) := by
        rw [Real.div_rpow hX0.le hq0.le]
        have hqpow : (q : ℝ)^(1-ε) = (q : ℝ)*(q : ℝ)^(-ε) := by
          rw [sub_eq_add_neg,Real.rpow_add hq0,Real.rpow_one]
        rw [hqpow]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hq0 (-ε))]
      have hm := mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg hq0.le (-ε))
      have hm' : (q : ℝ)^(-ε)*(D*(X/q)^(1-ε)/(Real.log X-Real.log q)^4) =
          D*X^(1-ε)*(1/((q : ℝ)*(Real.log X-Real.log q)^4)) := by
        calc
          _ = D*((q : ℝ)^(-ε)*(X/q)^(1-ε))/(Real.log X-Real.log q)^4 := by ring
          _ = _ := by rw [hpow]; simp only [div_eq_mul_inv,mul_inv_rev]; ring
      rw [hm'] at hm
      exact hm.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : D ≤ D+1) (by positivity)) (by positivity))
    · simp
  have ht := hCb (Real.log X) a b ha hab hlog
  have hcoef : 0 ≤ (D+1)*X^(1-ε) := by positivity
  calc
    _ ≤ (D+1)*X^(1-ε)*(∑ q ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        if q.Prime then 1/((q : ℝ)*(Real.log X-Real.log q)^4) else 0) := hs
    _ ≤ (D+1)*X^(1-ε)*(C/(Real.log a*(Real.log X-Real.log b)^3)) :=
      mul_le_mul_of_nonneg_left ht hcoef
    _ = _ := by ring

/-- Quantitative mass-tail control needed to center the moving boundary kernel. -/
theorem pmPowerDampedBoundaryWeight_mass_tail_bound {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε < 1/2) :
    ∃ C ≥ 0, ∀ᶠ H : ℝ in atTop,
      ‖∫ x in Ioi H, pmPowerDampedBoundaryWeight ε x‖ ≤ C/Real.log H^3 := by
  obtain ⟨C,hC,he⟩ := pmPowerDampedFermiSource_reciprocal_eventually_log_four hε hεhalf
  obtain ⟨R,hR⟩ := eventually_atTop.mp he
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop (max R (Real.exp 1))] with H hH
  have hH1 : 1 < H := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le
    ((le_max_right _ _).trans hH)
  have hH0 : 0 < H := by linarith
  have hlH : 0 < Real.log H := Real.log_pos hH1
  have hi := (integrableOn_inv_div_log_sq_Ioi hH1).const_mul (C/Real.log H^2)
  have hb := norm_integral_le_of_norm_le hi (f := pmPowerDampedBoundaryWeight ε) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hH0.trans hx
    have hlog : Real.log H ≤ Real.log x := Real.log_le_log hH0 hx.le
    have hlx : 0 < Real.log x := hlH.trans_le hlog
    have hs := hR x (((le_max_left _ _).trans hH).trans hx.le)
    have hp : x^(ε-2)*x^(1-ε) = x⁻¹ := by
      rw [← Real.rpow_add hx0,show ε-2+(1-ε) = (-1 : ℝ) by ring,Real.rpow_neg_one]
    rw [pmPowerDampedBoundaryWeight,norm_mul,Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    calc
      _ ≤ x^(ε-2)*(C*x^(1-ε)/Real.log x^4) :=
        mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hx0.le _)
      _ = C*(x^(ε-2)*x^(1-ε))/Real.log x^4 := by ring
      _ = (C*(x⁻¹/Real.log x^2))/Real.log x^2 := by rw [hp]; ring
      _ ≤ (C*(x⁻¹/Real.log x^2))/Real.log H^2 :=
        div_le_div_of_nonneg_left (by positivity) (by positivity)
          (pow_le_pow_left₀ hlH.le hlog 2)
      _ = (C/Real.log H^2)*(x⁻¹/Real.log x^2) := by ring)
  rw [integral_const_mul,integral_inv_div_log_sq_Ioi hH1] at hb
  exact hb.trans_eq (by field_simp)

end RHTower
