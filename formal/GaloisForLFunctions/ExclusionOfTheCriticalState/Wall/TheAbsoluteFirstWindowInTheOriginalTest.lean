import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PrimeSupportAcrossLateCriticalWidthWindows
import GaloisForLFunctions.RHTower.Sieve.LinearRangeVariable

/-!
# Absolute contribution of the signed first window

The first-window sum is measurable and bounded, including at its moving
endpoints. Its exceptional length in the integer abscissa controls its
absolute integral in logarithmic time under the original fractional test.
-/

noncomputable section
open MeasureTheory Filter Set Topology
open scoped Classical
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open HTGeometry ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory _root_.RHTower

/-- The finite window with its moving integer endpoints is measurable in log time. -/
theorem measurable_criticalWidthSignedReading {Φ : ℝ → ℝ} (hc : Continuous Φ) :
    Measurable (criticalWidthSignedReading Φ) := by
  let J := fun t => wallIntegerWindow t (criticalWallWidth t)
  let a := fun (n : ℕ) (t : ℝ) => (∫ u, Φ u)*
    ((ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t)
  let E := fun (n : ℕ) => {t : ℝ | Real.exp t < n ∧ (n:ℝ) ≤ Real.exp t+criticalWallWidth t}
  have hH : Measurable criticalWallWidth := by unfold criticalWallWidth; fun_prop
  have hE (n : ℕ) : MeasurableSet (E n) :=
    (measurableSet_lt Real.measurable_exp measurable_const).inter
      (measurableSet_le measurable_const (Real.measurable_exp.add hH))
  have ha (n : ℕ) : Measurable (a n) := measurable_const.mul
    (measurable_const.mul (measurable_const.mul (hc.measurable.comp (by fun_prop))))
  have heq (t : ℝ) (n : ℕ) : n ∈ J t ↔ t ∈ E n := by
    have h0 : 0 ≤ Real.exp t+criticalWallWidth t := add_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _))
    exact Finset.mem_Ioc.trans (and_congr (Nat.floor_lt (Real.exp_pos _).le) (Nat.le_floor_iff h0))
  have hfun (t : ℝ) : (∑' n : ℕ, (E n).indicator (a n) t) = criticalWidthSignedReading Φ t := by
    rw [tsum_eq_sum (s := J t) (fun n hn => indicator_of_notMem (fun h => hn ((heq t n).mpr h)) _)]
    exact Finset.sum_congr rfl fun n hn => indicator_of_mem ((heq t n).mp hn) _
  rw [← funext hfun]
  exact Measurable.tsum fun n => (ha n).indicator (hE n)

/-- Uniformity in the center follows from the linear prime sieve at the
actual wall width. Below a fixed center only finitely many atoms can enter. -/
private theorem bounded_signed_first_window {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hf : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |criticalWidthSignedReading Φ t| ≤ M := by
  obtain ⟨_,_,Ψ,hΨ,heΨ,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hf
  have heq : Ψ=Φ := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  obtain ⟨hL,hlaw⟩ := criticalState_oriented_wall_limit hW ht hf hc he
  have hread := tendsto_criticalWidthSignedReading_sub_chebyshev rfl hlaw
  let γ := Real.sqrt 2*(|∫ u, Φ u| *Real.sqrt (8*criticalAliasCoefficient W₀*
    ∫ u : ℝ, F u^2*Real.exp (-(8*u))))
  have hγ : 0 < γ := mul_pos (by positivity : 0 < Real.sqrt 2) hL
  obtain ⟨D,hD,hsieve⟩ := mangoldt_mass_on_power_width
  have hlate : ∀ᶠ t : ℝ in atTop, |criticalWidthSignedReading Φ t| ≤ 1+γ*(D+1) := by
    filter_upwards [hread.eventually (Metric.ball_mem_nhds (0:ℝ) zero_lt_one),
      eventually_ge_atTop (1:ℝ)] with t h ht
    let H := criticalWallWidth t
    let x := Real.exp t
    have ht0 := zero_lt_one.trans_le ht
    have hH : 0 < H := mul_pos (Real.exp_pos _) (Real.sqrt_pos.mpr ht0)
    have hlo : Real.exp (t/4) ≤ H := (Real.exp_le_exp.mpr (by linarith only [ht])).trans
      (le_mul_of_one_le_right (Real.exp_pos _).le (by simpa using Real.sqrt_le_sqrt ht))
    have hhi : H ≤ x := by
      have hs : Real.sqrt t ≤ Real.exp (t/2) := by
        apply (Real.sqrt_le_left (Real.exp_pos _).le).mpr
        rw [sq,← Real.exp_add,show t/2+t/2=t by ring]
        linarith only [Real.add_one_le_exp t]
      calc H ≤ Real.exp (t/2)*Real.exp (t/2) := mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
           _ = x := by rw [← Real.exp_add,show t/2+t/2=t by ring]
    have hxH : x ≤ x+H := le_add_of_nonneg_right hH.le
    let q := (Chebyshev.psi (x+H)-Chebyshev.psi x)/H
    have hq0 : 0 ≤ q := div_nonneg (sub_nonneg.mpr (Chebyshev.psi_mono hxH)) hH.le
    have hqD : q ≤ D := by
      apply (div_le_iff₀ hH).mpr
      rw [_root_.RHTower.Sieve.psi_sub_eq_sum_Ioc hxH]
      exact hsieve t ht H hlo hhi
    change dist (criticalWidthSignedReading Φ t-γ*(q-1)) 0 < 1 at h
    rw [Real.dist_eq,sub_zero,abs_lt] at h
    apply abs_le.mpr
    constructor <;> linarith only [h.1,h.2,mul_nonneg hγ.le hq0,
      mul_le_mul_of_nonneg_left hqD hγ.le,mul_nonneg hγ.le hD,hγ.le]
  obtain ⟨U,hU⟩ := eventually_atTop.mp hlate
  let b := ⌊Real.exp U+criticalWallWidth U⌋₊
  let m := ∫ u, Φ u
  let a := fun n : ℕ => |m| *(|ArithmeticFunction.vonMangoldt n-1| *
    ((Real.sqrt n)⁻¹*(C*Real.exp (2*U))))
  have ha (n : ℕ) : 0 ≤ a n := by dsimp only [a]; positivity
  let B := ∑ n ∈ Finset.range (b+1), a n
  refine ⟨max B (1+γ*(D+1)),(Finset.sum_nonneg fun n _ => ha n).trans (le_max_left ..),fun t => ?_⟩
  rcases le_total U t with hUt | htU
  · exact (hU t hUt).trans (le_max_right ..)
  have hwidth : criticalWallWidth t ≤ criticalWallWidth U :=
    mul_le_mul (Real.exp_le_exp.mpr (by linarith only [htU])) (Real.sqrt_le_sqrt htU)
      (Real.sqrt_nonneg _) (Real.exp_pos _).le
  let J := wallIntegerWindow t (criticalWallWidth t)
  have hJ : J ⊆ Finset.range (b+1) := fun n hn => Finset.mem_range.mpr (Nat.lt_succ_of_le
    ((Finset.mem_Ioc.mp hn).2.trans (Nat.floor_mono (add_le_add (Real.exp_le_exp.mpr htU) hwidth))))
  apply le_trans _ (le_max_left ..)
  calc |criticalWidthSignedReading Φ t| ≤ ∑ n ∈ J,
        |m*((ArithmeticFunction.vonMangoldt n-1)*continuousIntegerAtom Φ n t)| :=
          Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ n ∈ J, a n := by
         apply Finset.sum_le_sum
         intro n _
         have hφ : |Φ (t-Real.log n)| ≤ C*Real.exp (2*U) :=
           (hb (t-Real.log n)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
           (by linarith only [htU,Real.log_natCast_nonneg n])) hC)
         simp only [a,continuousIntegerAtom,abs_mul,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
         exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_left hφ (inv_nonneg.mpr (Real.sqrt_nonneg _))) (abs_nonneg _)) (abs_nonneg _)
       _ ≤ B := Finset.sum_le_sum_of_subset_of_nonneg hJ fun n _ _ => ha n

private theorem integrableOn_Ioc_of_abs_bound {w : ℝ → ℝ} (hm : Measurable w)
    {M : ℝ} (hb : ∀ t, |w t| ≤ M) (a b : ℝ) : IntegrableOn w (Ioc a b) :=
  (integrableOn_const (C := M) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).mono'
    hm.aestronglyMeasurable (Eventually.of_forall fun t => hb t)

/-- In logarithmic time the Jacobian on the original octave is at most
the reciprocal of its left endpoint, including on the exceptional set. -/
private theorem tendsto_log_octave_mass {w : ℝ → ℝ} (hm : Measurable w)
    (hn : ∀ t, 0 ≤ w t) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t, w t ≤ M)
    (hex : ∀ ε : ℝ, 0 < ε → ∃ bad : ℝ → Set ℝ,
      (∀ X, MeasurableSet (bad X) ∧ bad X ⊆ Icc X (2*X)) ∧
      Tendsto (fun X : ℝ => volume.real (bad X)/X) atTop (𝓝 0) ∧
      ∀ᶠ X : ℝ in atTop, ∀ u ∈ Icc X (2*X), u ∉ bad X → w (Real.log u) < ε) :
    Tendsto (fun T => ∫ t in Ioc T (T+Real.log 2), w t) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨bad,hmBad,hvol,hgood⟩ := hex (ε/2) (half_pos hε)
  have hsmall := (hvol.const_mul M).eventually_lt_const
    (by simpa only [mul_zero] using half_pos hε : M*0 < ε/2)
  filter_upwards [Real.tendsto_exp_atTop.eventually hsmall,Real.tendsto_exp_atTop.eventually hgood] with T hcost hwin
  let X := Real.exp T
  let I := Ioc X (2*X)
  let E := bad X
  have hx : 0 < X := Real.exp_pos _
  have hE := (hmBad X).1
  have hEf : volume E ≠ ⊤ := measure_ne_top_of_subset (hmBad X).2 measure_Icc_lt_top.ne
  have hI : MeasurableSet I := measurableSet_Ioc
  let a := fun u : ℝ => (ε/2 + E.indicator (fun _ => M) u)/X
  have hInd : Integrable (E.indicator (fun _ : ℝ => M)) :=
    (integrable_indicator_iff hE).mpr (integrableOn_const hEf)
  have hi : IntegrableOn a I := ((integrableOn_const (C := ε/2)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).add hInd.integrableOn).div_const X
  let f := fun u : ℝ => w (Real.log u)/u
  have hf : Measurable f := (hm.comp Real.measurable_log).div measurable_id
  have hle (u : ℝ) (hu : u ∈ I) : f u ≤ a u := by
    have hu0 := hx.trans hu.1
    apply (div_le_div_of_nonneg_left (hn _) hx hu.1.le).trans
    apply div_le_div_of_nonneg_right _ hx.le
    by_cases h : u ∈ E
    · rw [indicator_of_mem h]; linarith only [hb (Real.log u),hε]
    · rw [indicator_of_notMem h,add_zero]
      exact (hwin u ⟨hu.1.le,hu.2⟩ h).le
  have hfi : IntegrableOn f I := hi.mono' hf.aestronglyMeasurable (by
    filter_upwards [ae_restrict_mem (μ := volume) hI] with u hu
    rw [Real.norm_of_nonneg (div_nonneg (hn _) (hx.trans hu.1).le)]
    exact hle u hu)
  have hchange := RHTower.Sieve.integral_Ioc_eq_integral_log f T (T+Real.log 2)
  rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<2),mul_comm (Real.exp T)] at hchange
  have heq : (∫ t in Ioc T (T+Real.log 2), w t) = ∫ u in I, f u := by
    rw [hchange]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    dsimp only [f]
    rw [Real.log_exp]; field_simp
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg hn),heq]
  apply (setIntegral_mono_on hfi hi hI hle).trans_lt
  have hconst : IntegrableOn (fun _ : ℝ => ε/2) I := integrableOn_const
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  have hInd0 (u : ℝ) : 0 ≤ E.indicator (fun _ : ℝ => M) u :=
    indicator_nonneg (fun _ _ => hM) _
  have hIndbound : (∫ u in I, E.indicator (fun _ : ℝ => M) u) ≤ volume.real E*M := calc
    _ ≤ ∫ u, E.indicator (fun _ : ℝ => M) u := setIntegral_le_integral hInd (Eventually.of_forall hInd0)
    _ = _ := by rw [integral_indicator hE,setIntegral_const,smul_eq_mul]
  dsimp only [a]
  rw [integral_div,integral_add hconst hInd.integrableOn,setIntegral_const,smul_eq_mul,
    Real.volume_real_Ioc_of_le (show X ≤ 2*X by linarith only [hx])]
  apply (div_le_div_of_nonneg_right (add_le_add (le_refl ((2*X-X)*(ε/2))) hIndbound) hx.le).trans_lt
  change M*(volume.real E/X) < ε/2 at hcost
  calc ((2*X-X)*(ε/2)+volume.real E*M)/X = ε/2+M*(volume.real E/X) := by field_simp; ring
       _ < ε := by linarith only [hcost]

-- A fixed number of consecutive log octaves keeps the same vanishing mass.
private theorem tendsto_adjacent_log_blocks {w : ℝ → ℝ} (hm : Measurable w)
    {M ℓ : ℝ} (hb : ∀ t, |w t| ≤ M) (hℓ : 0 < ℓ)
    (ho : Tendsto (fun T : ℝ => ∫ t in Ioc T (T+ℓ), w t) atTop (𝓝 0)) (n : ℕ) :
    Tendsto (fun T : ℝ => ∫ t in Ioc T (T+n*ℓ), w t) atTop (𝓝 0) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := ho.comp (tendsto_atTop_add_const_right atTop ((n:ℝ)*ℓ) tendsto_id)
    have hlim := ih.add h
    rw [zero_add] at hlim
    apply hlim.congr
    intro T
    have h0 : T ≤ T+n*ℓ := le_add_of_nonneg_right (by positivity)
    have h1 : T+n*ℓ ≤ T+n*ℓ+ℓ := le_add_of_nonneg_right hℓ.le
    have hi {a b : ℝ} (hab : a ≤ b) : IntervalIntegrable w volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr (integrableOn_Ioc_of_abs_bound hm hb a b)
    change (∫ t in Ioc T (T+n*ℓ), w t)+(∫ t in Ioc (T+n*ℓ) (T+n*ℓ+ℓ), w t) = _
    rw [← intervalIntegral.integral_of_le h0,← intervalIntegral.integral_of_le h1,
      intervalIntegral.integral_add_adjacent_intervals (hi h0) (hi h1),intervalIntegral.integral_of_le (h0.trans h1)]
    norm_num [Nat.cast_succ,add_mul,add_assoc]

/-- The far portion is controlled uniformly by the integrable kernel.
The central portion is a fixed finite union of original octaves. -/
private theorem fractional_test_of_vanishing_octaves {w : ℝ → ℝ} (hm : Measurable w)
    (hn : ∀ t, 0 ≤ w t) {M : ℝ} (hM : 0 ≤ M) (hb : ∀ t, w t ≤ M)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (ho : Tendsto (fun T : ℝ => ∫ t in Ioc T (T+ℓ), w t) atTop (𝓝 0)) :
    (∀ T : ℝ, Integrable fun t => w t*fractionalPrimeTest (T-t)) ∧
      Tendsto (fun T : ℝ => ∫ t, w t*fractionalPrimeTest (T-t)) atTop (𝓝 0) := by
  let K := fractionalPrimeTest
  have hk (v : ℝ) : 0 ≤ K v := mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _)
  have hiK : Integrable K := by
    apply (integrable_weightedFloorDiscrepancy (by norm_num : (0:ℝ)<1/2) (by norm_num)).neg.congr
    apply Eventually.of_forall fun v => ?_
    dsimp only [K,fractionalPrimeTest,weightedFloorDiscrepancy,Pi.neg_apply]
    rw [neg_mul,neg_neg,show -(1/2:ℝ)*v= -v/2 by ring]
  have hi (T : ℝ) : Integrable fun t => w t*K (T-t) := by
    apply ((hiK.comp_sub_left T).const_mul M).mono' (hm.mul
      (measurable_fractionalPrimeTest.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
    exact Eventually.of_forall fun t => (Real.norm_of_nonneg (mul_nonneg (hn _) (hk _))).le.trans
      (mul_le_mul_of_nonneg_right (hb _) (hk _))
  refine ⟨hi,Metric.tendsto_nhds.mpr fun ε hε => ?_⟩
  let A := fun n : ℕ => Icc (-((n:ℝ)*ℓ)) ((n:ℝ)*ℓ)
  let k := fun n : ℕ => (A n)ᶜ.indicator K
  have hkm (n : ℕ) : Measurable (k n) := measurable_fractionalPrimeTest.indicator measurableSet_Icc.compl
  have hki (n : ℕ) : Integrable (k n) := hiK.indicator measurableSet_Icc.compl
  have hkn (n : ℕ) (v : ℝ) : 0 ≤ k n v := indicator_nonneg (fun v _ => hk v) v
  have hkb (n : ℕ) (v : ℝ) : ‖k n v‖ ≤ K v := by
    rw [Real.norm_of_nonneg (hkn n v)]
    change (A n)ᶜ.indicator K v ≤ K v
    by_cases hv : v ∈ (A n)ᶜ
    · rw [indicator_of_mem hv]
    · rw [indicator_of_notMem hv]; exact hk _
  have hw : Tendsto (fun n : ℕ => (n:ℝ)*ℓ) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hℓ
  have hpt (v : ℝ) : Tendsto (fun n => k n v) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hw.eventually_ge_atTop |v|] with n h
    have hmem : v ∈ A n := ⟨(neg_le_neg h).trans (neg_abs_le _),(le_abs_self _).trans h⟩
    exact (indicator_of_notMem (show v ∉ (A n)ᶜ from fun h => h hmem) K).symm
  have ht := tendsto_integral_filter_of_dominated_convergence (f := fun _ : ℝ => (0:ℝ)) K
    (Eventually.of_forall fun n => (hkm n).aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall (hkb n)) hiK (Eventually.of_forall hpt)
  rw [integral_zero] at ht
  obtain ⟨n,hsmall⟩ := ((ht.const_mul M).eventually_lt_const
    (by simpa only [mul_zero] using half_pos hε : M*0 < ε/2)).exists
  let H : ℝ := n*ℓ
  have hblocks := (tendsto_adjacent_log_blocks hm (fun t => (abs_of_nonneg (hn t)).le.trans (hb t))
    hℓ ho (2*n)).comp (tendsto_atTop_add_const_right atTop (-H) tendsto_id)
  filter_upwards [hblocks.eventually_lt_const (half_pos hε)] with T hblocks
  let J := Icc (T-H) (T+H)
  have hJ : MeasurableSet J := measurableSet_Icc
  have hji : Integrable (J.indicator w) := (integrable_indicator_iff hJ).mpr
    ((integrableOn_const (C := M) measure_Icc_lt_top.ne).mono' hm.aestronglyMeasurable
      (Eventually.of_forall fun t => (Real.norm_of_nonneg (hn t)).le.trans (hb t)))
  have hdom (t : ℝ) : w t*K (T-t) ≤ J.indicator w t + M*k n (T-t) := by
    by_cases htj : t ∈ J
    · rw [indicator_of_mem htj]
      exact (mul_le_of_le_one_right (hn _) ((le_abs_self _).trans (fractionalPrimeTest_bounds _).1)).trans
        (le_add_of_nonneg_right (mul_nonneg hM (hkn _ _)))
    · have hv : T-t ∈ (A n)ᶜ := by
        intro h
        apply htj
        change -H ≤ T-t ∧ T-t ≤ H at h
        exact ⟨by linarith only [h.2],by linarith only [h.1]⟩
      rw [indicator_of_notMem htj,zero_add,show k n (T-t) = K (T-t) from indicator_of_mem hv K]
      exact mul_le_mul_of_nonneg_right (hb _) (hk _)
  have hjnear : (∫ t in J, w t) < ε/2 := by
    rw [integral_Icc_eq_integral_Ioc]
    change (∫ t in Ioc (T+ -H) ((T+ -H)+(↑(2*n):ℝ)*ℓ), w t) < ε/2 at hblocks
    rw [show T+ -H=T-H by ring,
      show T-H+(↑(2*n):ℝ)*ℓ=T+H by push_cast; dsimp only [H]; ring] at hblocks
    exact hblocks
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg fun t => mul_nonneg (hn _) (hk _))]
  apply (integral_mono (hi T) (hji.add (((hki n).comp_sub_left T).const_mul M)) hdom).trans_lt
  change (∫ t, J.indicator w t + M*k n (T-t)) < ε
  rw [integral_add hji (((hki n).comp_sub_left T).const_mul M),integral_indicator hJ,
    integral_const_mul,integral_sub_left_eq_self (k n) volume T]
  linarith only [hjnear,hsmall]

/-- The absolute contribution of the signed first arithmetic window tends
to zero on the full original fractional test, uniformly on every time set. -/
theorem riemannHypothesis_or_first_window_absolute_test_vanishes : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ D : Set ℝ, MeasurableSet D →
        let f := fun t => |criticalWidthSignedReading Φ t| *fractionalPrimeTest (T-t)
        IntegrableOn f D ∧ (∫ t in D, f t) < ε := by
  rcases riemannHypothesis_or_signed_window_vanishes_in_measure with hr | ⟨W₀,F,Φ,hW,ht,hf,hc,he,h⟩
  · exact Or.inl hr
  obtain ⟨M,hM,hb⟩ := bounded_signed_first_window hW ht hf hc he
  let w := fun t => |criticalWidthSignedReading Φ t|
  have hm : Measurable w := (measurable_criticalWidthSignedReading hc).abs
  have hn (t : ℝ) : 0 ≤ w t := abs_nonneg _
  have ho := tendsto_log_octave_mass hm hn hM hb (fun ε hε => by
    obtain ⟨bad,hB,hmass,hgood⟩ := h ε hε
    exact ⟨bad,hB,hmass,hgood.mono (fun X hX u hu hbu => (hX u hu hbu).1)⟩)
  obtain ⟨hi,hlim⟩ := fractional_test_of_vanishing_octaves hm hn hM hb (Real.log_pos (by norm_num)) ho
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hf,hc,he,fun ε hε => ?_⟩
  filter_upwards [hlim.eventually_lt_const hε] with T hT
  intro D _
  exact ⟨(hi T).integrableOn,(setIntegral_le_integral (hi T) (Eventually.of_forall fun t =>
    mul_nonneg (hn _) (mul_nonneg (Real.exp_pos _).le (Int.fract_nonneg _)))).trans_lt hT⟩

#print axioms riemannHypothesis_or_first_window_absolute_test_vanishes
end GaloisForLFunctions.ExclusionOfTheCriticalState
