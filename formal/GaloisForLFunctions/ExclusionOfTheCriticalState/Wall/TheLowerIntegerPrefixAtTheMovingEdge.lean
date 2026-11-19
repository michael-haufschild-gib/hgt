import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheSignedIntegerWeightsBelowTheTestAbscissa
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheLateTimeEndpointOfTheTestedIntegerRows

/-!
# The lower integer prefix at the moving edge

Only the first wall window separates the full tested integer prefix from
the complementary row. Its intersection with any prefix ends at log N.
Counting the integers in that window bounds its original test absolutely.
-/

noncomputable section
open MeasureTheory Filter Set Topology ArithmeticFunction
open scoped Classical
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations

/-- Tested atoms through N lying outside the moving complement. -/
def prefixWallStrip (Φ : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 N, if pastCriticalEdge n t then 0 else
    (vonMangoldt n-1)*continuousIntegerAtom Φ n t

/-- The first-window prefix is supported below log N and bounded by its width. -/
theorem prefixWallStrip_bound {Φ : ℝ → ℝ} (hs : ∀ v, 0 ≤ v → Φ v=0)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v)) (N : ℕ) (t : ℝ) :
    |prefixWallStrip Φ N t| ≤ (Iic (Real.log N)).indicator
      (fun _ => C*(Real.log N+1)*(Real.sqrt (Real.log N)+1)) t := by
  classical
  let x := Real.exp t
  let H := Real.exp (t/2)*Real.sqrt t
  let A := Finset.Ioc 0 N
  let J := A.filter (fun n : ℕ => x < n ∧ (n:ℝ) ≤ x+H)
  let w := fun n : ℕ => (vonMangoldt n-1)*continuousIntegerAtom Φ n t
  have hx : 0 < x := Real.exp_pos _
  have hH : 0 ≤ H := mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)
  have hid : prefixWallStrip Φ N t = ∑ n ∈ J, w n := by
    dsimp only [J]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
    have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn0
    by_cases h : pastCriticalEdge n t
    · have hnot : ¬ (x < (n:ℝ) ∧ (n:ℝ) ≤ x+H) := fun u => (not_le.mpr h) u.2
      simp only [h,hnot,if_false,if_true]
    · have hu : (n:ℝ) ≤ x+H := le_of_not_gt h
      by_cases hv : x < (n:ℝ)
      · simp only [h,hv,hu,true_and,if_true,if_false,w]
      · have hlog : Real.log n ≤ t := by
          have := Real.log_le_log hn' (le_of_not_gt hv)
          simpa only [x,Real.log_exp] using this
        simp only [h,hv,false_and,if_false,continuousIntegerAtom,hs _ (sub_nonneg.mpr hlog),mul_zero]
  rw [hid]
  by_cases hJ : J.Nonempty
  · obtain ⟨k,hk⟩ := hJ
    obtain ⟨hkA,hkx,_⟩ := Finset.mem_filter.mp hk
    have htN : t ≤ Real.log N := by
      have hh : x ≤ (N:ℝ) := hkx.le.trans (Nat.cast_le.mpr (Finset.mem_Ioc.mp hkA).2)
      simpa only [x,Real.log_exp] using Real.log_le_log hx hh
    rw [indicator_of_mem (show t ∈ Iic (Real.log N) from htN)]
    have ht : 0 < t := by
      by_contra! ht
      have hHz : H=0 := by simp only [H,Real.sqrt_eq_zero_of_nonpos ht,mul_zero]
      have hu := (Finset.mem_filter.mp hk).2.2
      rw [hHz,add_zero] at hu
      exact hkx.not_ge hu
    have hcard : (J.card:ℝ) ≤ H+1 := by
      have hsub : J ⊆ Finset.Ioc ⌊x⌋₊ ⌊x+H⌋₊ := by
        intro n hn
        obtain ⟨_,h1,h2⟩ := Finset.mem_filter.mp hn
        exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hx.le).mpr h1,(Nat.le_floor_iff (add_nonneg hx.le hH)).mpr h2⟩
      have h : (J.card:ℝ) ≤ (Finset.Ioc ⌊x⌋₊ ⌊x+H⌋₊).card := Nat.cast_le.mpr (Finset.card_le_card hsub)
      rw [Nat.card_Ioc,Nat.cast_sub (Nat.floor_mono (le_add_of_nonneg_right hH))] at h
      linarith only [h,Nat.floor_le (add_nonneg hx.le hH),Nat.lt_floor_add_one x]
    have hw (n : ℕ) (hn : n ∈ J) : |w n| ≤ (Real.log N+1)*(C*Real.exp (-t/2)) := by
      obtain ⟨hnA,hnx,_⟩ := Finset.mem_filter.mp hn
      have hn' := hx.trans hnx
      have hlog : t ≤ Real.log n := by simpa only [x,Real.log_exp] using Real.log_le_log hx hnx.le
      have hf : |Φ (t-Real.log n)| ≤ C := (hb _).trans
        (mul_le_of_le_one_right hC (Real.exp_le_one_iff.mpr (by linarith only [hlog])))
      have hroot : (Real.sqrt (n:ℝ))⁻¹ ≤ Real.exp (-t/2) := by
        rw [neg_div,Real.exp_neg]
        apply inv_anti₀ (Real.exp_pos _)
        rw [Real.exp_half]
        exact Real.sqrt_le_sqrt hnx.le
      have hcoeff : |vonMangoldt n-1| ≤ Real.log N+1 := by
        apply (abs_sub _ _).trans
        rw [abs_of_nonneg vonMangoldt_nonneg,abs_one]
        exact add_le_add (vonMangoldt_le_log.trans
          (Real.log_le_log hn' (Nat.cast_le.mpr (Finset.mem_Ioc.mp hnA).2))) le_rfl
      change |(vonMangoldt n-1)*((Real.sqrt (n:ℝ))⁻¹*Φ (t-Real.log n))| ≤ _
      rw [abs_mul,abs_mul,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg (n:ℝ)))]
      apply mul_le_mul hcoeff _ (mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (abs_nonneg _))
        (by linarith only [Real.log_natCast_nonneg N])
      rw [mul_comm C]
      exact mul_le_mul hroot hf (abs_nonneg _) (Real.exp_pos _).le
    have hcancel : H*Real.exp (-t/2) = Real.sqrt t := by
      dsimp only [H]; rw [mul_right_comm,← Real.exp_add,show t/2 + -t/2=0 by ring,Real.exp_zero,one_mul]
    have hfactor : (H+1)*Real.exp (-t/2) ≤ Real.sqrt (Real.log N)+1 := by
      rw [add_mul,one_mul,hcancel]
      exact add_le_add (Real.sqrt_le_sqrt htN) (Real.exp_le_one_iff.mpr (by linarith only [ht]))
    have hnon : 0 ≤ C*(Real.log N+1) := mul_nonneg hC (by linarith only [Real.log_natCast_nonneg N])
    calc _ ≤ ∑ n ∈ J, |w n| := Finset.abs_sum_le_sum_abs _ _
         _ ≤ ∑ _n ∈ J, (Real.log N+1)*(C*Real.exp (-t/2)) := Finset.sum_le_sum hw
         _ = J.card*((Real.log N+1)*(C*Real.exp (-t/2))) := by rw [Finset.sum_const,nsmul_eq_mul]
         _ ≤ (H+1)*((Real.log N+1)*(C*Real.exp (-t/2))) :=
           mul_le_mul_of_nonneg_right hcard (mul_nonneg (by linarith only [Real.log_natCast_nonneg N])
             (mul_nonneg hC (Real.exp_pos _).le))
         _ = (C*(Real.log N+1))*((H+1)*Real.exp (-t/2)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hfactor hnon
  · rw [Finset.not_nonempty_iff_eq_empty.mp hJ,Finset.sum_empty,abs_zero]
    exact indicator_nonneg (fun _ _ => mul_nonneg (mul_nonneg hC
      (by linarith only [Real.log_natCast_nonneg N])) (by linarith only [Real.sqrt_nonneg (Real.log N)])) _

/-- The whole signed prefix splits into the two integrable pieces on opposite
sides of the moving far edge. -/
theorem tested_prefix_split_at_moving_edge {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (N : ℕ) (T : ℝ) :
    Integrable (fun t => finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t)) ∧
    Integrable (fun t => prefixWallStrip Φ N t*fractionalPrimeTest (T-t)) ∧
    (∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)) -
      (∫ v, Φ v)*(∫ t, finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t)) =
      (∫ v, Φ v)*(∫ t, prefixWallStrip Φ N t*fractionalPrimeTest (T-t)) := by
  classical
  let m := ∫ v, Φ v
  let A := Finset.Ioc 0 N
  let w := fun (n : ℕ) (t : ℝ) => (vonMangoldt n-1)*continuousIntegerAtom Φ n t
  let K := fun t : ℝ => fractionalPrimeTest (T-t)
  let g := fun (n : ℕ) (t : ℝ) => w n t*K t
  let E := fun n : ℕ => {t : ℝ | pastCriticalEdge n t}
  have hE (n : ℕ) : MeasurableSet (E n) := measurableSet_lt
    (by fun_prop : Measurable fun t : ℝ => Real.exp t+Real.exp (t/2)*Real.sqrt t) measurable_const
  have hKm : Measurable K := measurable_fractionalPrimeTest.comp (measurable_const.sub measurable_id)
  have hgi (n : ℕ) : Integrable (g n) := by
    have hw : Integrable (w n) := ((hi.comp_sub_right (Real.log n)).const_mul
      (Real.sqrt (n:ℝ))⁻¹).const_mul (vonMangoldt n-1)
    have hwm : Measurable (w n) := measurable_const.mul
      (measurable_const.mul (hc.measurable.comp (measurable_id.sub_const _)))
    refine hw.abs.mono' (hwm.mul hKm).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    change |w n t*K t| ≤ |w n t|
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (fractionalPrimeTest_bounds _).1
  have hfull (n : ℕ) (hn : n ∈ A) :
      (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n) = m*∫ t, g n t := by
    rw [testedIntegerWeight,Real.exp_log (Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1),
      ← integral_const_mul,← integral_const_mul m]
    apply integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only [g,w,K,m]; ring
  have hed (t : ℝ) : finiteCriticalComplementRow Φ N t*K t =
      ∑ n ∈ A, (E n).indicator (g n) t := by
    rw [finiteCriticalComplementRow,finiteCriticalComplementBand,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : t ∈ E n
    · rw [if_pos (show pastCriticalEdge n t from h),indicator_of_mem h]
    · rw [if_neg (show ¬pastCriticalEdge n t from h),indicator_of_notMem h,zero_mul]
  have hstrip (t : ℝ) : prefixWallStrip Φ N t*K t =
      ∑ n ∈ A, ((g n t)-(E n).indicator (g n) t) := by
    rw [prefixWallStrip,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : t ∈ E n
    · rw [if_pos (show pastCriticalEdge n t from h),indicator_of_mem h,sub_self,zero_mul]
    · rw [if_neg (show ¬pastCriticalEdge n t from h),indicator_of_notMem h,sub_zero]
  have hid : (∑ n ∈ A, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)) -
      m*(∫ t, finiteCriticalComplementRow Φ N t*K t) = m*∫ t, prefixWallStrip Φ N t*K t := by
    rw [Finset.sum_congr rfl hfull,← Finset.mul_sum,← mul_sub]
    congr 1
    simp_rw [hed,hstrip]
    rw [integral_finsetSum _ (fun n _ => (hgi n).indicator (hE n)),
      integral_finsetSum (f := fun n t => g n t-(E n).indicator (g n) t) A
        (fun n _ => (hgi n).sub ((hgi n).indicator (hE n))),← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => (integral_sub (hgi n) ((hgi n).indicator (hE n))).symm
  refine ⟨?_,?_,hid⟩
  · change Integrable (fun t => finiteCriticalComplementRow Φ N t*K t)
    simp_rw [hed]
    exact integrable_finsetSum _ fun n _ => (hgi n).indicator (hE n)
  · change Integrable (fun t => prefixWallStrip Φ N t*K t)
    simp_rw [hstrip]
    exact integrable_finsetSum _ fun n _ => (hgi n).sub ((hgi n).indicator (hE n))

/-- Counting the first-window atoms through log N bounds the error from
removing that window, for every integer endpoint and every test center. -/
theorem abs_tested_prefix_sub_moving_edge {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (hs : ∀ v, 0 ≤ v → Φ v=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v))
    (N : ℕ) (T : ℝ) :
    |(∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)) -
      (∫ v, Φ v)*(∫ t, finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t))| ≤
      2*|∫ v, Φ v| *(C*(Real.log N+1)*(Real.sqrt (Real.log N)+1))*Real.exp ((Real.log N-T)/2) := by
  let m := ∫ v, Φ v
  let A := Finset.Ioc 0 N
  let K := fun t : ℝ => fractionalPrimeTest (T-t)
  have hid := (tested_prefix_split_at_moving_edge hc hi N T).2.2
  let D := C*(Real.log N+1)*(Real.sqrt (Real.log N)+1)
  have hD : 0 ≤ D := mul_nonneg (mul_nonneg hC (by linarith only [Real.log_natCast_nonneg N]))
    (by linarith only [Real.sqrt_nonneg (Real.log N)])
  let B := fun t : ℝ => (D*Real.exp (-T/2))*Real.exp ((1/2)*t)
  have hB : IntegrableOn B (Iic (Real.log N)) :=
    (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<1/2) _).const_mul _
  have hp (t : ℝ) : ‖prefixWallStrip Φ N t*K t‖ ≤ (Iic (Real.log N)).indicator B t := by
    have h := prefixWallStrip_bound hs hC hb N t
    rw [Real.norm_eq_abs,abs_mul]
    by_cases ht : t ∈ Iic (Real.log N)
    · rw [indicator_of_mem ht] at h ⊢
      have hk : |K t| ≤ Real.exp (-(T-t)/2) := by
        rw [show K t=Real.exp (-(T-t)/2)*Int.fract (Real.exp (T-t)) from rfl,abs_mul,
          abs_of_pos (Real.exp_pos _),abs_of_nonneg (Int.fract_nonneg _)]
        exact mul_le_of_le_one_right (Real.exp_pos _).le (Int.fract_lt_one _).le
      apply (mul_le_mul h hk (abs_nonneg _) hD).trans_eq
      change D*Real.exp (-(T-t)/2) = (D*Real.exp (-T/2))*Real.exp ((1/2)*t)
      rw [show -(T-t)/2 = -T/2+(1/2)*t by ring,Real.exp_add]; ring
    · rw [indicator_of_notMem ht] at h ⊢
      rw [le_antisymm h (abs_nonneg _),zero_mul]
  have hbound := norm_integral_le_of_norm_le (f := fun t => prefixWallStrip Φ N t*K t)
    (hB.integrable_indicator measurableSet_Iic) (Eventually.of_forall hp)
  rw [Real.norm_eq_abs,integral_indicator measurableSet_Iic] at hbound
  have hBI : (∫ t in Iic (Real.log N), B t) = 2*D*Real.exp ((Real.log N-T)/2) := by
    dsimp only [B]
    rw [integral_const_mul,integral_exp_mul_Iic (by norm_num : (0:ℝ)<1/2),
      show (Real.log N-T)/2 = -T/2+(1/2)*Real.log N by ring,Real.exp_add]
    ring
  change |(∑ n ∈ A, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)) -
      m*(∫ t, finiteCriticalComplementRow Φ N t*K t)| ≤ _
  rw [hid,abs_mul]
  exact (mul_le_mul_of_nonneg_left (hbound.trans_eq hBI) (abs_nonneg _)).trans_eq (by dsimp only [m,D]; ring)

#print axioms abs_tested_prefix_sub_moving_edge

/-- Uniformly for log N ≤ 2T/3+B, the actual complementary prefix differs
from the positive half tilt times the normalized Chebyshev discrepancy by o(1). -/
theorem criticalState_lower_moving_prefix {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) (B : ℝ) :
    let m := ∫ v, Φ v
    let a := m*(∫ v, Real.exp (v/2)*Φ v)/2
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, 0 < N → Real.log N ≤ 2*T/3+B →
      |m*(∫ t, finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t)) -
        a*Real.exp (-T/2)*(Chebyshev.psi N-N)| ≤ ε := by
  let m := ∫ v, Φ v
  let a := m*(∫ v, Real.exp (v/2)*Φ v)/2
  dsimp only
  intro ε hε
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  let η := (ε/2)/Real.exp (3*B/2)
  have hη : 0 < η := div_pos (half_pos hε) (Real.exp_pos _)
  obtain ⟨Y,hY,hprice⟩ := criticalState_lower_integer_sum hW ht hF hc he η hη
  let D := 2*|m| *C*144*Real.exp (2*B/3)
  have hdec : Tendsto (fun T : ℝ => D*Real.exp (-T/18)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/18:ℝ)<0))
    simpa only [Function.comp_def,id_eq,show ∀ t : ℝ, (-1/18)*t = -t/18 by intro t; ring,mul_zero]
      using h.const_mul D
  filter_upwards [eventually_ge_atTop (3*(Real.log Y+B)),hdec.eventually_lt_const (half_pos hε)] with T hT hd
  intro N hN hscale
  let q := Real.log N
  have hn : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  change q ≤ 2*T/3+B at hscale
  have hq : 0 ≤ q := Real.log_natCast_nonneg N
  have hratio : Y ≤ Real.exp (T-q) := (Real.log_le_iff_le_exp hY).mp (by linarith only [hscale,hT])
  have hmain := hprice T N hN hratio
  rw [mul_assoc η] at hmain
  have hsize : (N*Real.sqrt N)*Real.exp (-T) ≤ Real.exp (3*B/2) := by
    have heq : Real.exp q = N := Real.exp_log hn
    have hroot : Real.exp (q/2)=Real.sqrt N := by rw [Real.exp_half,heq]
    rw [← hroot,← heq,← Real.exp_add,← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hscale])
  have hsmall := hmain.trans (mul_le_mul_of_nonneg_left hsize hη.le)
  have hηeq : η*Real.exp (3*B/2)=ε/2 := div_mul_cancel₀ _ (Real.exp_pos _).ne'
  rw [hηeq] at hsmall
  have he12 := Real.add_one_le_exp (q/12)
  have hq1 : q+1 ≤ 12*Real.exp (q/12) := by linarith only [he12]
  have hsqrt : Real.sqrt q ≤ q+1 := by nlinarith only [Real.sq_sqrt hq,sq_nonneg (Real.sqrt q-1),hq]
  have hq2 : Real.sqrt q+1 ≤ 12*Real.exp (q/12) := by linarith only [he12,hsqrt]
  have hpoly := mul_le_mul hq1 hq2 (by linarith only [Real.sqrt_nonneg q]) (by positivity)
  have hedge := abs_tested_prefix_sub_moving_edge hc
    ((criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he) hs hC hb N T
  have hcut : 2*|m| *(C*(q+1)*(Real.sqrt q+1))*Real.exp ((q-T)/2) ≤ D*Real.exp (-T/18) := by
    calc _ = (2*|m| *C)*((q+1)*(Real.sqrt q+1))*Real.exp ((q-T)/2) := by ring
         _ ≤ (2*|m| *C)*((12*Real.exp (q/12))*(12*Real.exp (q/12)))*Real.exp ((q-T)/2) :=
           mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (by positivity)) (Real.exp_pos _).le
         _ = (2*|m| *C*144)*Real.exp (q/12+q/12+(q-T)/2) := by rw [Real.exp_add,Real.exp_add]; ring
         _ ≤ (2*|m| *C*144)*Real.exp (2*B/3 + -T/18) :=
           mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith only [hscale])) (by positivity)
         _ = _ := by rw [Real.exp_add]; dsimp only [D]; ring
  let P := ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)
  let M := m*(∫ t, finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t))
  let Q := a*Real.exp (-T/2)*(Chebyshev.psi N-N)
  have hMP : |M-P| ≤ ε/2 := (abs_sub_comm M P).le.trans ((hedge.trans hcut).trans hd.le)
  change |M-Q| ≤ ε
  exact (abs_sub_le M P Q).trans ((add_le_add hMP hsmall).trans_eq (add_halves ε))

/-- The price of cutting every finite complementary prefix at an early time
decays uniformly in its integer endpoint. Above log N that prefix vanishes. -/
theorem finite_complement_prefix_time_cut {Φ : ℝ → ℝ} (hc : Continuous Φ)
    (hs : ∀ v, 0 ≤ v → Φ v=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (N : ℕ) (U M T : ℝ), U ≤ M → Real.log N ≤ M →
      |(∫ t, finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t))-
        (∫ t in Ioc U M, finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t))| ≤
        D*Real.exp ((5*U-T)/2) := by
  classical
  let b := fun n : ℕ => Real.log n/(n:ℝ)^2+1/(n:ℝ)^2
  have hbi : Summable b := GaloisForLFunctions.summable_log_nat_div_sq.add
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  have hb0 (n : ℕ) : 0 ≤ b n := add_nonneg (div_nonneg (Real.log_natCast_nonneg _) (sq_nonneg _)) (by positivity)
  let A := C*(∑' n, b n)
  have hA : 0 ≤ A := mul_nonneg hC (tsum_nonneg hb0)
  refine ⟨A/(5/2),div_nonneg hA (by norm_num),fun N U M T hUM hNM => ?_⟩
  let f := fun t => finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t)
  let B := fun t : ℝ => (A*Real.exp (-T/2))*Real.exp ((5/2)*t)
  have hm : Measurable f := by
    apply Measurable.mul _ (measurable_fractionalPrimeTest.comp (measurable_const.sub measurable_id))
    refine Finset.measurable_sum (Finset.Ioc 0 N) ?_
    intro n _
    exact Measurable.ite (measurableSet_lt (by fun_prop : Measurable fun t : ℝ =>
      Real.exp t+Real.exp (t/2)*Real.sqrt t) measurable_const)
      (measurable_const.mul (measurable_const.mul (hc.measurable.comp (measurable_id.sub_const _)))) measurable_const
  have hf (t : ℝ) : ‖f t‖ ≤ B t := by
    have hrow : |finiteCriticalComplementRow Φ N t| ≤ A*Real.exp (2*t) := by
      unfold finiteCriticalComplementRow finiteCriticalComplementBand
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      calc _ ≤ ∑ n ∈ Finset.Ioc 0 N, (C*Real.exp (2*t))*b n := by
             apply Finset.sum_le_sum
             intro n hn
             split_ifs
             · rw [abs_mul]
               have hcoeff : |vonMangoldt n-1| ≤ Real.log n+1 := by
                 apply (abs_sub _ _).trans
                 rw [abs_of_nonneg vonMangoldt_nonneg,abs_one]
                 exact add_le_add vonMangoldt_le_log le_rfl
               apply (mul_le_mul hcoeff (continuousIntegerAtom_bound hb (by
                 exact_mod_cast (Finset.mem_Ioc.mp hn).1 : (1:ℝ) ≤ n) t) (abs_nonneg _)
                 (by linarith only [Real.log_natCast_nonneg n])).trans_eq
               dsimp only [b]; ring
             · rw [abs_zero]; exact mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) (hb0 n)
           _ ≤ ∑' n, (C*Real.exp (2*t))*b n := (hbi.mul_left _).sum_le_tsum _
             (fun n _ => mul_nonneg (mul_nonneg hC (Real.exp_pos _).le) (hb0 n))
           _ = _ := by rw [tsum_mul_left]; dsimp only [A]; ring
    have hk : |fractionalPrimeTest (T-t)| ≤ Real.exp (-(T-t)/2) := by
      rw [fractionalPrimeTest,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_right (Real.exp_pos _).le (Int.fract_lt_one _).le
    change |finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t)| ≤ B t
    rw [abs_mul]
    apply (mul_le_mul hrow hk (abs_nonneg _) (mul_nonneg hA (Real.exp_pos _).le)).trans_eq
    have hex : Real.exp (2*t)*Real.exp (-(T-t)/2) = Real.exp (-T/2)*Real.exp ((5/2)*t) := by
      rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
    dsimp only [B]; linear_combination A*hex
  have hz (t : ℝ) (ht : M < t) : f t=0 := by
    have hzrow : finiteCriticalComplementRow Φ N t=0 := by
      unfold finiteCriticalComplementRow finiteCriticalComplementBand
      apply Finset.sum_eq_zero
      intro n hn
      have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr (Finset.mem_Ioc.mp hn).1
      have hlog := (Real.log_le_log hn' (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2)).trans hNM
      split_ifs <;> simp only [continuousIntegerAtom,hs _ (sub_nonneg.mpr (hlog.trans ht.le)),mul_zero]
    simp only [f,hzrow,zero_mul]
  have hBi (u : ℝ) : IntegrableOn B (Iic u) :=
    (integrableOn_exp_mul_Iic (by norm_num : (0:ℝ)<5/2) u).const_mul _
  have hfi (u : ℝ) : IntegrableOn f (Iic u) :=
    (hBi u).mono' hm.aestronglyMeasurable (Eventually.of_forall hf)
  have huniv : (∫ t, f t) = ∫ t in Iic M, f t := by
    rw [← integral_indicator measurableSet_Iic]
    exact integral_congr_ae (Eventually.of_forall fun t => by
      change f t = (Iic M).indicator f t
      by_cases ht : t ∈ Iic M
      · rw [indicator_of_mem ht]
      · rw [indicator_of_notMem ht,hz t (lt_of_not_ge ht)])
  have hsplit : (∫ t in Iic U, f t)+(∫ t in Ioc U M, f t) = ∫ t in Iic M, f t := by
    rw [← setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc (hfi U)
      ((hfi M).mono_set Ioc_subset_Iic_self),Iic_union_Ioc_eq_Iic hUM]
  change |(∫ t, f t)-(∫ t in Ioc U M, f t)| ≤ _
  rw [huniv,← hsplit,add_sub_cancel_right,← Real.norm_eq_abs]
  apply (norm_integral_le_of_norm_le (μ := volume.restrict (Iic U)) (f := f) (g := B)
    (hBi U) (Eventually.of_forall hf)).trans_eq
  dsimp only [B]; rw [integral_const_mul,integral_exp_mul_Iic (by norm_num : (0:ℝ)<5/2),
    show (5*U-T)/2= -T/2+(5/2)*U by ring,Real.exp_add]; ring

/-- On the original middle time interval the same state reads the Chebyshev
discrepancy, uniformly through every fixed multiple of the two-thirds scale. -/
theorem criticalState_middle_lower_moving_prefix {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) (B : ℝ) :
    let m := ∫ v, Φ v
    let a := m*(∫ v, Real.exp (v/2)*Φ v)/2
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, 0 < N → Real.log N ≤ 2*T/3+B →
      |m*(∫ t in Ioc (T/6) (6*T), finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t)) -
        a*Real.exp (-T/2)*(Chebyshev.psi N-N)| ≤ ε := by
  let m := ∫ v, Φ v
  let a := m*(∫ v, Real.exp (v/2)*Φ v)/2
  dsimp only
  intro ε hε
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  obtain ⟨D,_,hcut⟩ := finite_complement_prefix_time_cut hc hs hC hb
  have hneg : Tendsto (fun T : ℝ => -T/12) atTop atBot :=
    (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-1/12:ℝ)<0)).congr fun t => by
      change (-1/12)*t = -t/12
      ring
  have hdec : Tendsto (fun T : ℝ => (|m| *D)*Real.exp (-T/12)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using (Real.tendsto_exp_atBot.comp hneg).const_mul (|m| *D)
  filter_upwards [criticalState_lower_moving_prefix hW ht hF hc he B (ε/2) (half_pos hε),
    hdec.eventually_lt_const (half_pos hε),eventually_ge_atTop (0:ℝ),eventually_ge_atTop B] with T hmain hd hT hTB
  intro N hN hscale
  let g := fun t => finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t)
  have h := hcut N (T/6) (6*T) T (by linarith only [hT]) (by linarith only [hscale,hT,hTB])
  rw [show (5*(T/6)-T)/2= -T/12 by ring] at h
  have hpiece : |m*(∫ t in Ioc (T/6) (6*T), g t)-m*(∫ t, g t)| ≤ ε/2 := by
    rw [← mul_sub,abs_mul,abs_sub_comm]
    exact (mul_le_mul_of_nonneg_left h (abs_nonneg m)).trans (by simpa only [mul_assoc] using hd.le)
  apply (abs_sub_le _ (m*(∫ t, g t)) _).trans
  exact (add_le_add hpiece (hmain N hN hscale)).trans_eq (add_halves ε)

/-- On failure of RH the oriented lower integer prefix of the original middle
test has positive leading coefficient on every fixed multiple of X^(2/3). -/
theorem riemannHypothesis_or_lower_moving_prefix : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      let m := ∫ v, Φ v
      let a := m*(∫ v, Real.exp (v/2)*Φ v)/2
      0 < a ∧ ∀ B ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, ∀ N : ℕ, 0 < N → Real.log N ≤ 2*T/3+B →
        |m*(∫ t in Ioc (T/6) (6*T), finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t)) -
          a*Real.exp (-T/2)*(Chebyshev.psi N-N)| ≤ ε := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with h | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl h
  obtain ⟨_,_,Φ,hc,he,_⟩ := criticalState_exists_continuous_representative hW ht hF
  exact Or.inr ⟨W₀,F,Φ,hW,ht,hF,hc,he,(criticalState_signed_weight_below_abscissa hW ht hF hc he).1,
    criticalState_middle_lower_moving_prefix hW ht hF hc he⟩

#print axioms riemannHypothesis_or_lower_moving_prefix
end GaloisForLFunctions.ExclusionOfTheCriticalState
