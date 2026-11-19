import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PositivePrimeExcessInsideTheTestedBand
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ReciprocalPrimeIntervalsAtTheZeroAbscissa
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.SplittingTheTestedIntegerBands

/-!
# The upper integer tail on prime-excess records

The Chebyshev upper exponent controls the reciprocal tail at every large
test scale, including the records selected by the positive lower exponent.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri _root_.RHTower

/-- The decay to the right of the time center pays for both logarithmic
factors in the cost of removing the first wall window. -/
private theorem strip_cost {C T v q : ℝ} (hC : 0 ≤ C) (hv : 0 ≤ v) (hmax : v ≤ 6*T)
    (hq : 8*T/7 ≤ q) :
    C*(v+1)*(Real.sqrt v+1)*Real.exp ((T+1-q)/2) ≤ C*168^2*Real.exp (1/2) := by
  have he := Real.add_one_le_exp (T/28)
  have h1 : v+1 ≤ 168*Real.exp (T/28) := by linarith only [hmax,he]
  have hroot : Real.sqrt v ≤ v+1 := by
    nlinarith only [Real.sq_sqrt hv,sq_nonneg (Real.sqrt v-1)]
  have h2 : Real.sqrt v+1 ≤ 168*Real.exp (T/28) := by linarith only [hmax,hroot,he]
  have hprod := mul_le_mul h1 h2 (by linarith only [Real.sqrt_nonneg v]) (by positivity)
  have hex : Real.exp (T/28)*Real.exp (T/28)*Real.exp ((T+1-q)/2) ≤ Real.exp (1/2) := by
    rw [← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
    linarith only [hq]
  calc _ ≤ C*((168*Real.exp (T/28))*(168*Real.exp (T/28)))*Real.exp ((T+1-q)/2) := by
             rw [mul_assoc C]
             exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hC) (Real.exp_pos _).le
       _ = C*168^2*(Real.exp (T/28)*Real.exp (T/28)*Real.exp ((T+1-q)/2)) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hex (by positivity)

/-- At every real test time the finite comparison up to exp(5T) leaves a
bounded wall and confinement error. The whole signed reciprocal interval
has the Chebyshev upper exponent. -/
theorem criticalState_upper_tail_at_real_times {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) {d : ℝ} (hd : 0 < d) (hθ : zeroReSup < 1-d) :
    ∃ D B : ℝ, 0 ≤ D ∧ 0 ≤ B ∧ ∀ T : ℝ, 1 ≤ T →
      |(∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
        criticalComplementBand Φ ⌈Real.exp (8*T/7)⌉₊ t*fractionalPrimeTest (T-t))|
        ≤ D+B*Real.exp ((1/2-8*d/7)*T) := by
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  let m := ∫ v, Φ v
  let a := m*(∫ v, Real.exp (-v/2)*Φ v)
  let f := fun v => Φ v ^ 2 * Real.exp (-(8*v))
  let H := 2 ^ (7/2:ℝ)*vonMangoldtRpowTailConstant (7/2)+1
  have hH : 0 ≤ H := by
    have := vonMangoldtRpowTailConstant_nonneg (by norm_num : (0:ℝ)<7/2)
    dsimp only [H]; positivity
  have hdom := criticalHalfLineEnergyDomain_of_groundState hF
  have hi := hdom.integrable.congr he
  have hf : Integrable f := hdom.exponential.congr
    (he.mono fun v hv => congrArg (fun x : ℝ => x^2*Real.exp (-(8*v))) hv)
  have htilt : Integrable fun v => Real.exp (-v/2)*Φ v := by
    apply (integrable_mul_exp_of_domain hdom (by norm_num : (-4:ℝ)< -1/2)).congr
    filter_upwards [he] with v hv
    rw [hv,mul_comm]; congr 2; ring
  let Z := Real.sqrt (∫ v, f v)
  have hnorm (x : ℝ) : leftEighthNorm Φ x ≤ Z := Real.sqrt_le_sqrt
    (setIntegral_le_integral hf (Eventually.of_forall fun v => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le))
  obtain ⟨A,hA,hcut⟩ := moving_upper_band_sub_whole hc hi hs hC hb
  obtain ⟨J,hJ,hfar⟩ := criticalState_upper_integer_tail hW ht hF hc he
  obtain ⟨B,hB,hrec⟩ := centered_reciprocal_prime_intervals_of_zeroReSup hd hθ
  let S := C*168^2*Real.exp (1/2)
  let P := |m| *(2*A+4*S)
  let Q := |m| *Z*H
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hZ : 0 ≤ Z := Real.sqrt_nonneg _
  refine ⟨P+Q+J,|a| *B,by dsimp only [P,Q]; positivity,by positivity,fun T hT => ?_⟩
  let k := ⌈Real.exp (8*T/7)⌉₊
  let L := ⌈Real.exp (5*T)⌉₊
  have hkx : Real.exp (8*T/7) ≤ k := Nat.le_ceil _
  have hLx : Real.exp (5*T) ≤ L := Nat.le_ceil _
  have hk : 1 ≤ k := by exact_mod_cast (Real.one_le_exp (by linarith only [hT])).trans hkx
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  have hkL : k ≤ L := Nat.ceil_mono (Real.exp_le_exp.mpr (by linarith only [hT]))
  have hL0 := hk0.trans_le (Nat.cast_le.mpr hkL)
  have hq : 8*T/7 ≤ Real.log k := (Real.le_log_iff_exp_le hk0).mpr hkx
  have hLM : Real.log L ≤ 6*T := by
    apply (Real.log_le_iff_le_exp hL0).mpr
    have hround := Nat.ceil_lt_add_one (Real.exp_pos (5*T)).le
    have hex : 2 ≤ Real.exp T := by linarith only [hT,Real.add_one_le_exp T]
    calc (L:ℝ) ≤ Real.exp (5*T)+1 := hround.le
         _ ≤ Real.exp (5*T)*2 := by linarith only [Real.one_le_exp (by linarith only [hT] : 0 ≤ 5*T)]
         _ ≤ Real.exp (5*T)*Real.exp T := mul_le_mul_of_nonneg_left hex (Real.exp_pos _).le
         _ = Real.exp (6*T) := by rw [← Real.exp_add]; congr 1; ring
  have hkM := (Real.log_le_log hk0 (Nat.cast_le.mpr hkL)).trans hLM
  let U := T/6
  let M := 6*T
  let K := fun t => fractionalPrimeTest (T-t)
  let tail := fun j => m*(∫ t in Ioc U M, criticalComplementBand Φ j t*K t)
  let mid := m*(∫ t in Ioc U M, finiteCriticalComplementBand Φ k L t*K t)
  let whole := ∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)
  have hU : U ≤ T := by dsimp only [U]; linarith only [hT]
  have hM : T ≤ M := by dsimp only [M]; linarith only [hT]
  have hsplit : tail k = mid+tail L := by
    dsimp only [tail,mid,K]
    rw [upper_band_integral_split hc hi hC hb hkL,mul_add]
  have hremote : |tail L| ≤ J := by
    have h := hfar U T M 0 L hU hM hT le_rfl (by
      rw [add_zero]; exact (Real.exp_le_exp.mpr (by linarith only [hT])).trans hLx)
    simpa only [neg_zero,zero_div,Real.exp_zero,mul_one] using h
  have hstrip : |mid-whole| ≤ P := by
    have h := hcut k L U M T hk hkL (hU.trans hM) hLM
    have hearly : Real.exp ((5*U-T)/2) ≤ 1 := Real.exp_le_one_iff.mpr (by dsimp only [U]; linarith only [hT])
    have h1 := strip_cost hC (Real.log_natCast_nonneg L) hLM hq
    have h2 := strip_cost hC (Real.log_natCast_nonneg k) hkM hq
    dsimp only [P,S]
    apply h.trans (mul_le_mul_of_nonneg_left _ (abs_nonneg _))
    linarith only [mul_le_mul_of_nonneg_left hearly (show 0 ≤ 2*A by positivity),h1,h2]
  let R := reciprocalPrimeRemainder k-reciprocalPrimeRemainder L
  -- Keep the reciprocal difference signed until Abel summation has been applied.
  have hco : |R| ≤ B*(k:ℝ)^(-d) := by
    let w := fun n : ℕ => (vonMangoldt n-1)/(n:ℝ)
    change |(-2*Real.eulerMascheroniConstant-∑ n ∈ Finset.Ioc 0 k, w n)-
      (-2*Real.eulerMascheroniConstant-∑ n ∈ Finset.Ioc 0 L, w n)| ≤ _
    rw [← Finset.sum_Ioc_consecutive w (Nat.zero_le k) hkL]
    simpa only [show ∀ u v c : ℝ, (c-u)-(c-(u+v))=v by intros; ring] using hrec k L hk hkL
  have hconf : |whole-a*Real.exp (T/2)*R| ≤ Q := by
    have h := upper_finite_reciprocal_difference hc hf htilt T hk hkL
    have hpow : Real.exp (4*T)*(k:ℝ)^(-(7/2:ℝ)) ≤ 1 := by
      rw [Real.rpow_def_of_pos hk0,← Real.exp_add,Real.exp_le_one_iff]
      linarith only [hq]
    apply h.trans
    change (|m| *leftEighthNorm Φ (T-Real.log k)*Real.exp (4*T))*(H*(k:ℝ)^(-(7/2:ℝ))) ≤ Q
    calc _ = (|m| *leftEighthNorm Φ (T-Real.log k)*H)*(Real.exp (4*T)*(k:ℝ)^(-(7/2:ℝ))) := by ring
         _ ≤ |m| *leftEighthNorm Φ (T-Real.log k)*H := mul_le_of_le_one_right
              (mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hH) hpow
         _ ≤ Q := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hnorm _) (abs_nonneg _)) hH
  have hmain : |a*Real.exp (T/2)*R| ≤ |a| *B*Real.exp ((1/2-8*d/7)*T) := by
    have hpow : Real.exp (T/2)*(k:ℝ)^(-d) ≤ Real.exp ((1/2-8*d/7)*T) := by
      rw [Real.rpow_def_of_pos hk0,← Real.exp_add,Real.exp_le_exp]
      linarith only [mul_le_mul_of_nonneg_right hq hd.le]
    rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    calc _ ≤ |a| *Real.exp (T/2)*(B*(k:ℝ)^(-d)) := mul_le_mul_of_nonneg_left hco (by positivity)
         _ = (|a| *B)*(Real.exp (T/2)*(k:ℝ)^(-d)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  change |tail k| ≤ _
  rw [hsplit]
  have hmid := abs_add_le (mid-whole) (whole-a*Real.exp (T/2)*R)
  have hwhole := abs_add_le (mid-a*Real.exp (T/2)*R) (a*Real.exp (T/2)*R)
  rw [sub_add_sub_cancel] at hmid
  rw [sub_add_cancel] at hwhole
  linarith only [abs_add_le mid (tail L),hmid,hwhole,hremote,hstrip,hconf,hmain]

/-- Every prefix through the two-thirds scale costs at most the same
exponential order as the upper tail. The bound is uniform in its endpoint. -/
private theorem eventual_lower_prefix_cost {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) {d : ℝ} (hθ : zeroReSup < 1-d) :
    ∃ B : ℝ, ∀ᶠ T : ℝ in atTop, ∀ j : ℕ, (j:ℝ) ≤ Real.exp (2*T/3) →
      |(∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
        finiteCriticalComplementRow Φ j t*fractionalPrimeTest (T-t))|
        ≤ 1+B*Real.exp ((1/2-8*d/7)*T) := by
  let a := (∫ v, Φ v)*(∫ v, Real.exp (v/2)*Φ v)/2
  obtain ⟨C,hC,hE⟩ := exists_abs_chebyshevPsi_sub_le_rpow hθ
  have hpos : 0 ≤ 1-d := by linarith only [half_le_zeroReSup,hθ]
  refine ⟨|a| *C,?_⟩
  filter_upwards [criticalState_middle_lower_moving_prefix hW ht hF hc he 0 1 zero_lt_one,
    eventually_ge_atTop (0:ℝ)] with T herr hT
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp only [finiteCriticalComplementRow,finiteCriticalComplementBand,Finset.Ioc_self,
      Finset.sum_empty,zero_mul,integral_zero,mul_zero,abs_zero]
    positivity
  have hj' : 0 < (j:ℝ) := Nat.cast_pos.mpr hj0
  have hlog := (Real.log_le_iff_le_exp hj').mpr hj
  let e := a*Real.exp (-T/2)*(Chebyshev.psi j-j)
  have hpow : Real.exp (-T/2)*(j:ℝ)^(1-d) ≤ Real.exp ((1/2-8*d/7)*T) := by
    rw [Real.rpow_def_of_pos hj',← Real.exp_add,Real.exp_le_exp]
    have h := mul_le_mul_of_nonneg_right hlog hpos
    have h' : -(1/2)+(2/3)*(1-d) ≤ 1/2-8*d/7 := by linarith only [half_le_zeroReSup,hθ]
    linarith only [h,mul_le_mul_of_nonneg_right h' hT]
  have he' : |e| ≤ |a| *C*Real.exp ((1/2-8*d/7)*T) := by
    dsimp only [e]; rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    calc _ ≤ |a| *Real.exp (-T/2)*(C*(j:ℝ)^(1-d)) :=
              mul_le_mul_of_nonneg_left (hE j (by exact_mod_cast hj0)) (by positivity)
         _ = (|a| *C)*(Real.exp (-T/2)*(j:ℝ)^(1-d)) := by ring
         _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have h := herr j hj0 (by simpa only [add_zero] using hlog)
  have htri := abs_sub_le ((∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
    finiteCriticalComplementRow Φ j t*fractionalPrimeTest (T-t))) e 0
  simp only [sub_zero] at htri
  exact htri.trans (add_le_add h he')

/-- On a fixed logarithmic translate, a smaller upper exponent costs a
vanishing fraction of a larger power, even with an additive bounded term. -/
private theorem eventually_upper_cost_le_power (D B s p : ℝ) {c q : ℝ}
    (hc : 0 < c) (hq : 0 < q) (hp : p < q) :
    ∀ᶠ N : ℕ in atTop, D+B*Real.exp (p*(Real.log N+s)) ≤ c*(N:ℝ)^q := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have decay (r A : ℝ) (hr : r < 0) :
      Tendsto (fun N : ℕ => A*Real.exp (r*Real.log N)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using
      (Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg hr)).const_mul A
  have hlim := (decay (-q) D (neg_lt_zero.mpr hq)).add
    (decay (p-q) (B*Real.exp (p*s)) (sub_neg.mpr hp))
  rw [add_zero] at hlim
  filter_upwards [hlim.eventually_le_const hc,eventually_ge_atTop 1] with N h hN
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast hN
  rw [Real.rpow_def_of_pos hN0,mul_comm (Real.log N) q]
  change D*Real.exp (-q * Real.log N)+(B*Real.exp (p*s))*Real.exp ((p-q)*Real.log N) ≤ c at h
  have he (u v : ℝ) : Real.exp u*Real.exp v=Real.exp (u+v) := (Real.exp_add _ _).symm
  apply le_trans _ (mul_le_mul_of_nonneg_right h (Real.exp_pos (q*Real.log N)).le)
  rw [add_mul,mul_assoc D,mul_assoc (B*Real.exp (p*s)),he,he,
    show -q*Real.log N+q*Real.log N=0 by ring,Real.exp_zero,mul_one,
    show (p-q)*Real.log N+q*Real.log N=p*Real.log N by ring,
    mul_assoc B,he,show p*s+p*Real.log N=p*(Real.log N+s) by ring]

/-- The positive block and the estimate for the entire upper tail hold at
the same original test times. The block occupies a vanishing relative width,
and the upper tail together with every lower prefix through the two-thirds
scale costs a fraction of its gain decaying as a power. -/
theorem riemannHypothesis_or_upper_tail_small_on_positive_bands : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (s κ g η c : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      0 ≤ s ∧ 0 < κ ∧ 0 < g ∧ 0 < η ∧ 0 < c ∧ ∃ᶠ N : ℕ in atTop,
        ∃ U V : ℕ, U < V ∧ V ≤ N ∧ (N:ℝ)/2 ≤ U ∧ ((V-U:ℕ):ℝ) ≤ 2*(N:ℝ)^(1-κ) ∧
          let T := Real.log N+s
          let gain := (∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
            finiteCriticalComplementBand Φ U V t*fractionalPrimeTest (T-t))
          c*(N:ℝ)^g ≤ gain ∧
            ∀ j : ℕ, (j:ℝ) ≤ Real.exp (2*T/3) →
              |(∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
                finiteCriticalComplementRow Φ j t*fractionalPrimeTest (T-t))|+
              |(∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
                criticalComplementBand Φ ⌈Real.exp (8*T/7)⌉₊ t*fractionalPrimeTest (T-t))|
              ≤ (N:ℝ)^(-η)*gain := by
  rcases riemannHypothesis_or_positive_central_prime_bands with hr |
    ⟨W₀,F,Φ,s,hW,ht,hF,hc,he,hs,hhalf,hbands⟩
  · exact Or.inl hr
  have hΘ : zeroReSup ≤ 20999/24000 := zeroReSup_le_of_forall_re_le fun z => by
    by_contra! hz
    exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hz
      (riemannZeta_eq_zero_of_xiZeroCopy z)
  let κ := min ((zeroReSup-1/2)/8) ((1-zeroReSup)/64)
  let b := zeroReSup-κ
  let d := 1-zeroReSup-κ
  let g := b-1/2-κ
  let p := 1/2-8*d/7
  have hκ : 0 < κ := lt_min (by linarith only [hhalf]) (by linarith only [hΘ])
  have hκ1 : κ ≤ (zeroReSup-1/2)/8 := min_le_left ..
  have hκ2 : κ ≤ (1-zeroReSup)/64 := min_le_right ..
  have hb : 1/2 < b := by dsimp only [b]; linarith only [hhalf,hκ1]
  have hbΘ : b < zeroReSup := sub_lt_self _ hκ
  have hκb : κ < b-1/2 := by dsimp only [b]; linarith only [hhalf,hκ1]
  have hg : 0 < g := sub_pos.mpr hκb
  have hd : 0 < d := by dsimp only [d]; linarith only [hκ2,hΘ]
  have hdΘ : zeroReSup < 1-d := by dsimp only [d]; linarith only [hκ]
  have hpg : p < g := by dsimp only [p,g,b,d]; linarith only [hκ2,hΘ]
  let η := min (g/2) ((g-p)/2)
  have hη : 0 < η := lt_min (half_pos hg) (half_pos (sub_pos.mpr hpg))
  have hq : 0 < g-η := by linarith only [min_le_left (g/2) ((g-p)/2),hg]
  have hp : p < g-η := by linarith only [min_le_right (g/2) ((g-p)/2),hpg]
  obtain ⟨D,B,_,_,hcost⟩ := criticalState_upper_tail_at_real_times hW ht hF hc he hd hdΘ
  obtain ⟨c,hc0,hgain⟩ := hbands b hb hbΘ κ hκ.le hκb
  refine Or.inr ⟨W₀,F,Φ,s,κ,g,η,c,hW,ht,hF,hc,he,hs,hκ,hg,hη,hc0,?_⟩
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hTend : Tendsto (fun N : ℕ => Real.log N+s) atTop atTop :=
    tendsto_atTop_add_const_right _ s hlog
  obtain ⟨A,hlo⟩ := eventual_lower_prefix_cost hW ht hF hc he hdΘ
  have hev := ((eventually_upper_cost_le_power (1+D) (A+B) s p hc0 hq hp).and
    (hTend.eventually hlo)).and (hlog.eventually_ge_atTop 1)
  apply (hgain.and_eventually (hev.and (eventually_ge_atTop 1))).mono
  rintro N ⟨⟨U,V,_,hUV,hVN,hhalfN,hwidth,_,hG⟩,⟨⟨hsmall,hlower⟩,htime⟩,hN⟩
  change 1 ≤ Real.log N at htime
  have hN0 : 0 < (N:ℝ) := by exact_mod_cast hN
  refine ⟨U,V,hUV,hVN,hhalfN,hwidth,hG,?_⟩
  intro j hj
  have hout := add_le_add (hlower j hj) (hcost (Real.log N+s) (by linarith only [hs,htime]))
  have hle : 1+A*Real.exp (p*(Real.log N+s))+(D+B*Real.exp (p*(Real.log N+s))) ≤ c*(N:ℝ)^(g-η) := by
    linarith only [hsmall]
  apply hout.trans (hle.trans ?_)
  have hscale : c*(N:ℝ)^(g-η)=(N:ℝ)^(-η)*(c*(N:ℝ)^g) := by
    rw [sub_eq_add_neg,Real.rpow_add hN0]; ring
  rw [hscale]
  exact mul_le_mul_of_nonneg_left hG (Real.rpow_nonneg hN0.le _)

#print axioms criticalState_upper_tail_at_real_times
#print axioms riemannHypothesis_or_upper_tail_small_on_positive_bands
end GaloisForLFunctions.ExclusionOfTheCriticalState
