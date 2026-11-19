import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PrimeExcessOnARecordInterval
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheUpperReciprocalTermAtTheMovingEdge

/-!
# Positive prime excess inside the tested band

A short multiplicative interval around a positive tested weight has small
weight variation. Chebyshev records provide intervals where that variation
costs only a fraction of the positive endpoint excess. Removing the first
wall window and restricting time to the original middle interval costs a
logarithmic polynomial.
-/

noncomputable section
open MeasureTheory Filter Set Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri _root_.RHTower

/-- Dilation of all integer abscissae and the test scale preserves the
profile of the tested weights up to the square-root normalization. -/
private theorem scale_tested_weight {Φ : ℝ → ℝ} {n N : ℕ} (hn : 0<n) (hN : 0<N) (s : ℝ) :
    Real.sqrt N*testedIntegerWeight Φ (Real.log N+s) (Real.log n) =
      testedIntegerWeight Φ s (Real.log ((n:ℝ)/N)) := by
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hN' : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  apply mul_left_cancel₀ (Real.exp_pos (s/2)).ne'
  rw [← mul_assoc,Real.log_div hn'.ne' hN'.ne']
  have he : Real.exp (s/2)*Real.sqrt N=Real.exp ((Real.log N+s)/2) := by
    rw [← Real.exp_log hN',← Real.exp_half,Real.log_exp,← Real.exp_add]; congr 1; ring
  rw [he,scaled_testedIntegerWeight_eq_fractional_reading,scaled_testedIntegerWeight_eq_fractional_reading,
    show Real.log N+s-Real.log n=s-(Real.log n-Real.log N) by ring]

/-- The normalized state weight is positive at some fixed dilation and is
Lipschitz throughout an octave of relative abscissae around that endpoint. -/
private theorem criticalState_positive_lipschitz_weight {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) :
    ∃ s B : ℝ, 0 ≤ s ∧ 0 < B ∧ 0 < testedIntegerWeight Φ s 0 ∧
      ∀ x ∈ Icc (1/2:ℝ) 1, ∀ y ∈ Icc (1/2:ℝ) 1,
        |testedIntegerWeight Φ s (Real.log y)-testedIntegerWeight Φ s (Real.log x)| ≤ B*|y-x| := by
  let a := (∫ u, Φ u)*(∫ v, Real.exp (v/2)*Φ v)/2
  obtain ⟨ha,hweight⟩ := criticalState_signed_weight_below_abscissa hW ht hF hc he
  change 0 < a at ha
  obtain ⟨Y,hY,hy⟩ := hweight (a/2) (half_pos ha)
  let s := max 0 (Real.log Y)
  have hs : 0 ≤ s := le_max_left ..
  have hratio : Y ≤ Real.exp (s-0) := by
    rw [sub_zero,← Real.exp_log hY]; exact Real.exp_le_exp.mpr (le_max_right ..)
  have hw := hy s 0 hratio
  have her := Real.exp_le_one_iff.mpr (show (0-s)/2≤0 by linarith)
  have hpos : 0 < testedIntegerWeight Φ s 0 := by
    have h := (abs_le.mp (hw.trans (mul_le_of_le_one_right (half_pos ha).le her))).1
    change -(a/2) ≤ Real.exp (s/2)*testedIntegerWeight Φ s 0-a at h
    have hz : 0 < Real.exp (s/2)*testedIntegerWeight Φ s 0 := by linarith only [h,ha]
    exact pos_of_mul_pos_right hz (Real.exp_pos _).le
  obtain ⟨_,_,Ψ,hΨ,heΨ,_,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have htlt (d : ℝ) (hd' : -4<d) : Integrable fun v => Real.exp (d*v)*Φ v := by
    apply (integrable_mul_exp_of_domain hd hd').congr
    filter_upwards [he] with v hv
    rw [hv,mul_comm]
  have hp : Integrable fun v => Real.exp (-v/2)*Φ v := by
    simpa only [show ∀ v : ℝ, (-1/2)*v= -v/2 by intro v; ring] using htlt (-1/2) (by norm_num)
  have hm : Integrable fun v => Real.exp (v/2)*Φ v := by
    simpa only [show ∀ v : ℝ, (1/2)*v=v/2 by intro v; ring] using htlt (1/2) (by norm_num)
  let m := ∫ v, Φ v
  let A := ∫ v, Real.exp (-v/2)*Φ v
  let f := fun x : ℝ => testedIntegerWeight Φ s (Real.log x)
  let D := fun x : ℝ => (m*Real.exp (-Real.log x/2)*
    (integerReferenceWave Φ (s-Real.log x)-Real.exp ((s-Real.log x)/2)*A))*x⁻¹
  let I := Icc (1/2:ℝ) 1
  have hn (x : ℝ) (hx : x ∈ I) : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1/2) hx.1)
  have hlog : ContinuousOn Real.log I := fun x hx => (Real.continuousAt_log (hn x hx)).continuousWithinAt
  have hN := continuous_integerReferenceWave hc hC hb
  have hcont : ContinuousOn D I := by
    dsimp only [D]
    exact ((continuousOn_const.mul (Real.continuous_exp.comp_continuousOn (hlog.neg.div_const 2))).mul
      ((hN.comp_continuousOn (continuousOn_const.sub hlog)).sub
        ((Real.continuous_exp.comp_continuousOn ((continuousOn_const.sub hlog).div_const 2)).mul
          continuousOn_const))).mul (continuousOn_id.inv₀ hn)
  have hderiv (x : ℝ) (hx : x ∈ I) : HasDerivWithinAt f (D x) I x :=
    ((hasDerivAt_testedIntegerWeight hc hC hb hp hm s (Real.log x)).comp x
      (Real.hasDerivAt_log (hn x hx))).hasDerivWithinAt
  obtain ⟨z,hz,hmax⟩ := (isCompact_Icc (a := (1/2:ℝ)) (b := 1)).exists_isMaxOn
    ⟨1,by constructor <;> norm_num⟩ hcont.norm
  refine ⟨s,‖D z‖+1,hs,by positivity,hpos,fun x hx y hy => ?_⟩
  simpa only [f,Real.norm_eq_abs] using (convex_Icc (1/2:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv (fun v hv => (hmax hv).trans (le_add_of_nonneg_right zero_le_one)) hx hy

private theorem weighted_record_gain {Φ : ℝ → ℝ} {s B q c b : ℝ}
    (hB : 0 < B) (hq : 1/2 ≤ q) (hw : 0 < testedIntegerWeight Φ s 0)
    (hqB : B*(1-q) ≤ testedIntegerWeight Φ s 0/2)
    (hlip : ∀ x ∈ Icc (1/2:ℝ) 1, ∀ y ∈ Icc (1/2:ℝ) 1,
      |testedIntegerWeight Φ s (Real.log y)-testedIntegerWeight Φ s (Real.log x)| ≤ B*|y-x|)
    {L N : ℕ} (hL : 0<L) (hLN : L ≤ N) (hfrac : q*N ≤ L)
    (hbig : c*(N:ℝ)^b ≤ centeredAbelPrefix L N)
    (hp : ∀ j : ℕ, L ≤ j → j ≤ N → 0 ≤ centeredAbelPrefix L j ∧
        centeredAbelPrefix L j ≤ centeredAbelPrefix L N) :
    (testedIntegerWeight Φ s 0/2*c)*(N:ℝ)^(b-1/2) ≤
      ∑ n ∈ Finset.Ioc L N, (vonMangoldt n-1)*testedIntegerWeight Φ (Real.log N+s) (Real.log n) := by
  have hN := hL.trans_le hLN
  have hN' : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  let w := fun j : ℕ => testedIntegerWeight Φ s (Real.log ((j:ℝ)/N))
  have hxy (j : ℕ) (ha : L ≤ j) (hb : j ≤ N) : (j:ℝ)/N ∈ Icc (1/2:ℝ) 1 :=
    ⟨(le_div_iff₀ hN').mpr (((mul_le_mul_of_nonneg_right hq hN'.le).trans hfrac).trans
      (Nat.cast_le.mpr ha)),(div_le_one hN').mpr (Nat.cast_le.mpr hb)⟩
  have hstep (j : ℕ) (ha : L ≤ j) (hb : j<N) : |w (j+1)-w j| ≤ B/N := by
    have h := hlip _ (hxy j ha hb.le) _ (hxy (j+1) (Nat.le_succ_of_le ha) hb)
    rw [Nat.cast_add_one,← sub_div,add_sub_cancel_left,abs_of_pos (one_div_pos.mpr hN')] at h
    simpa only [w,Nat.cast_add_one,mul_one_div] using h
  have hres := record_band_weighted_lower w hLN hp hstep
  have he : w N=testedIntegerWeight Φ s 0 := by simp only [w,div_self hN'.ne',Real.log_one]
  rw [he,Nat.cast_sub hLN] at hres
  have hcost : ((N:ℝ)-L)*(B/N) ≤ B*(1-q) := by
    rw [← mul_div_assoc,div_le_iff₀ hN']
    nlinarith only [mul_le_mul_of_nonneg_right hfrac hB.le]
  have hraw : (testedIntegerWeight Φ s 0/2)*(c*(N:ℝ)^b) ≤
      ∑ n ∈ Finset.Ioc L N, (vonMangoldt n-1)*w n :=
    (mul_le_mul_of_nonneg_left hbig (half_pos hw).le).trans
      ((mul_le_mul_of_nonneg_right (by linarith only [hcost,hqB]) (hp N hLN le_rfl).1).trans hres)
  have hsum : (∑ n ∈ Finset.Ioc L N, (vonMangoldt n-1)*w n) =
      Real.sqrt N*(∑ n ∈ Finset.Ioc L N,
        (vonMangoldt n-1)*testedIntegerWeight Φ (Real.log N+s) (Real.log n)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [mul_left_comm,scale_tested_weight (hL.trans (Finset.mem_Ioc.mp hn).1) hN]
  rw [hsum] at hraw
  apply le_of_mul_le_mul_left (a := Real.sqrt (N:ℝ)) _ (Real.sqrt_pos.mpr hN')
  have heq : Real.sqrt N*(N:ℝ)^(b-1/2)=(N:ℝ)^b := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add hN']; congr 1; ring
  calc _ = (testedIntegerWeight Φ s 0/2*c)*(Real.sqrt N*(N:ℝ)^(b-1/2)) := by ring
       _ ≤ _ := by rw [heq]; simpa only [mul_assoc] using hraw

/-- Split a positive signed sum into consecutive blocks. With at most
twice N^κ blocks one block retains the reciprocal fraction of the gain. -/
private theorem short_positive_block (f : ℕ → ℝ) {L N : ℕ} (hLN : L ≤ N) (hN : 0<N)
    {A d κ : ℝ} (hA : 0<A) (hκ : 0≤κ) (hκ1 : κ≤1)
    (hgain : A*(N:ℝ)^d ≤ ∑ n ∈ Finset.Ioc L N, f n) :
    ∃ U V : ℕ, L ≤ U ∧ U < V ∧ V ≤ N ∧ ((V-U:ℕ):ℝ) ≤ 2*(N:ℝ)^(1-κ) ∧
      A/2*(N:ℝ)^(d-κ) ≤ ∑ n ∈ Finset.Ioc U V, f n := by
  classical
  let M := ⌈(N:ℝ)^κ⌉₊
  let H := ⌈(N:ℝ)^(1-κ)⌉₊
  have hN' : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hm : (N:ℝ)^κ ≤ M := Nat.le_ceil _
  have hh : (N:ℝ)^(1-κ) ≤ H := Nat.le_ceil _
  have hm0 : 0<M := Nat.cast_pos.mp ((Real.rpow_pos_of_pos hN' κ).trans_le hm)
  have hMN : N ≤ M*H := by
    apply (Nat.cast_le (α := ℝ)).mp
    rw [Nat.cast_mul]
    have h := mul_le_mul hm hh (Real.rpow_nonneg hN'.le _) (Nat.cast_nonneg M)
    rwa [← Real.rpow_add hN',show κ+(1-κ)=1 by ring,Real.rpow_one] at h
  have ceil_bound (e : ℝ) (he : 0≤e) : (⌈(N:ℝ)^e⌉₊:ℝ) ≤ 2*(N:ℝ)^e := by
    linarith only [Nat.ceil_lt_add_one (Real.rpow_nonneg hN'.le e),Real.one_le_rpow hN1 he]
  let grid := fun i : ℕ => min N (L+i*H)
  let P := fun n : ℕ => ∑ j ∈ Finset.Ioc 0 n, f j
  have hP {u v : ℕ} (huv : u≤v) : P v-P u = ∑ n ∈ Finset.Ioc u v, f n := by
    have h := Finset.sum_Ioc_consecutive f (Nat.zero_le u) huv
    change P u+_=P v at h
    linarith only [h]
  let w := fun i : ℕ => P (grid (i+1))-P (grid i)
  obtain ⟨i,hi,hmax⟩ := (Finset.range M).exists_max_image w ⟨0,Finset.mem_range.mpr hm0⟩
  have hsum := Finset.sum_le_sum (fun j hj => hmax j hj)
  change (∑ j ∈ Finset.range M, w j) ≤ ∑ _j ∈ Finset.range M, w i at hsum
  have hzero : grid 0=L := by simp [grid,min_eq_right hLN]
  have hend : grid M=N := min_eq_left (by omega : N≤L+M*H)
  have htel : ∑ j ∈ Finset.range M, w j=P (grid M)-P (grid 0) :=
    Finset.sum_range_sub (fun j => P (grid j)) M
  rw [htel,hzero,hend,hP hLN,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have hmul := hgain.trans hsum
  have hwi : 0<w i := pos_of_mul_pos_right ((mul_pos hA (Real.rpow_pos_of_pos hN' _)).trans_le hmul)
    (Nat.cast_nonneg M)
  have hstep : grid i ≤ grid (i+1) := min_le_min_left _ (Nat.add_le_add_left
    (Nat.mul_le_mul_right H (Nat.le_succ i)) L)
  have hstrict : grid i < grid (i+1) := by
    apply lt_of_le_of_ne hstep
    intro heq
    simp only [w,heq,sub_self,lt_self_iff_false] at hwi
  have hwidth : grid (i+1)-grid i ≤ H := by
    dsimp only [grid]; rw [Nat.add_mul,one_mul]; omega
  refine ⟨grid i,grid (i+1),le_min hLN (Nat.le_add_right ..),hstrict,min_le_left ..,
    (Nat.cast_le.mpr hwidth).trans (ceil_bound (1-κ) (sub_nonneg.mpr hκ1)),?_⟩
  rw [← hP hstep]
  change A/2*(N:ℝ)^(d-κ) ≤ w i
  rw [Real.rpow_sub hN',← mul_div_assoc,div_le_iff₀ (Real.rpow_pos_of_pos hN' _)]
  have h2 := hmul.trans (mul_le_mul_of_nonneg_right (ceil_bound κ hκ) hwi.le)
  linarith only [h2]

/-- On integer bands inside one octave the moving-edge cost is logarithmic
in the upper endpoint, uniformly in the starting integer. -/
private theorem octave_moving_cost {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (hs : ∀ v, 0 ≤ v → Φ v=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ v, |Φ v| ≤ C*Real.exp (2*v))
    {s : ℝ} (hs0 : 0 ≤ s) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ L P N : ℕ, 0 < L → L ≤ P → P ≤ N → (N:ℝ)/2 ≤ L →
      let T := Real.log N+s
      |(∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
        finiteCriticalComplementBand Φ L P t*fractionalPrimeTest (T-t))-
        ∑ n ∈ Finset.Ioc L P, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)| ≤
      D*(Real.log N+2)^2 := by
  obtain ⟨J,hJ,hcost⟩ := moving_upper_band_sub_whole hc hi hs hC hb
  let E := Real.exp ((s+1+Real.log 2)/2)
  let m := ∫ v, Φ v
  refine ⟨|m| *(2*J+4*C*E),by dsimp only [E]; positivity,fun L P N hL hLP hPN hhalf => ?_⟩
  let T := Real.log N+s
  have h0 := Real.log_natCast_nonneg N
  have hT : 0 ≤ T := add_nonneg h0 hs0
  have hLN := hLP.trans hPN
  have hN' : 0 < (N:ℝ) := Nat.cast_pos.mpr (hL.trans_le hLN)
  have hL' : 0 < (L:ℝ) := Nat.cast_pos.mpr hL
  have hlog := Real.log_le_log hL' (Nat.cast_le.mpr hLN)
  have hlog2 := Real.log_le_log hN' (show (N:ℝ) ≤ 2*L by linarith only [hhalf])
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hL'.ne'] at hlog2
  have hlogP := Real.log_le_log (Nat.cast_pos.mpr (hL.trans_le hLP)) (Nat.cast_le.mpr hPN : (P:ℝ) ≤ N)
  have hcut := hcost L P (T/6) (6*T) T hL hLP (by linarith only [hT])
    (by dsimp only [T]; linarith only [h0,hs0,hlogP])
  have hfirst : Real.exp ((5*(T/6)-T)/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hT])
  have hlast : Real.exp ((T+1-Real.log L)/2) ≤ E :=
    Real.exp_le_exp.mpr (by dsimp only [T]; linarith only [hlog2])
  let Q := (Real.log N+2)^2
  have hP : 1 ≤ Q := by dsimp only [Q]; nlinarith only [h0,sq_nonneg (Real.log N)]
  have hbound (j : ℕ) (hj : Real.log j ≤ Real.log N) :
      C*(Real.log j+1)*(Real.sqrt (Real.log j)+1) ≤ C*Q := by
    have hg := Real.log_natCast_nonneg j
    have hr := Real.sq_sqrt hg
    have hroot : Real.sqrt (Real.log j)+1 ≤ Real.log N+2 := by
      nlinarith only [hg,hr,hj,sq_nonneg (Real.sqrt (Real.log j)-1)]
    rw [show C*Q=C*((Real.log N+2)*(Real.log N+2)) by dsimp only [Q]; ring,← mul_assoc]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith only [hj]) hC) hroot
      (by linarith only [Real.sqrt_nonneg (Real.log j)]) (mul_nonneg hC (by linarith only [h0]))
  have hsum := add_le_add (hbound P hlogP) (hbound L hlog)
  have henv : 0 ≤ 2*(C*Q+C*Q) := by dsimp only [Q]; positivity
  have he := mul_le_mul (mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ)≤2)) hlast
    (Real.exp_pos _).le henv
  have hea := (mul_le_mul_of_nonneg_left hfirst (show 0≤2*J by positivity)).trans
    (mul_le_mul_of_nonneg_left hP (show 0≤2*J by positivity))
  apply hcut.trans
  apply (mul_le_mul_of_nonneg_left (add_le_add hea he) (abs_nonneg m)).trans_eq
  dsimp only [m,Q]; ring

private theorem eventually_log_cost_le_power {A D d : ℝ} (hA : 0<A) (hD : 0≤D) (hd : 0<d) :
    ∀ᶠ N : ℕ in atTop, D*(Real.log N+2)^2 ≤ (A/2)*(N:ℝ)^d := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hr := (tendsto_exp_mul_div_rpow_atTop 2 d hd).comp hlog
  filter_upwards [hr.eventually_ge_atTop (8*D/A),hlog.eventually_ge_atTop 2,eventually_ge_atTop 1]
    with N hratio hN hN1
  change 2 ≤ Real.log N at hN
  change 8*D/A ≤ Real.exp (d*Real.log N)/(Real.log N)^(2:ℝ) at hratio
  rw [Real.rpow_two,le_div_iff₀ (sq_pos_of_pos (by linarith only [hN]))] at hratio
  have hN' : 0<(N:ℝ) := by exact_mod_cast hN1
  rw [Real.rpow_def_of_pos hN',mul_comm (Real.log N) d]
  have hh : D*(Real.log N+2)^2 ≤ 4*D*(Real.log N)^2 := by
    have h := mul_self_le_mul_self (by linarith only [hN] : 0≤Real.log N+2)
      (by linarith only [hN] : Real.log N+2≤2*Real.log N)
    nlinarith only [mul_le_mul_of_nonneg_left h hD]
  apply hh.trans
  have hscaled := mul_le_mul_of_nonneg_right hratio hA.le
  have hcancel : (8*D/A*(Real.log N)^2)*A=8*D*(Real.log N)^2 := by
    field_simp [hA.ne']
  rw [hcancel] at hscaled
  linarith only [hscaled]

/-- Once the near edge reaches the largest integer, the entire band vanishes. -/
private theorem finite_band_vanishes_after_log {Φ : ℝ → ℝ} {U V : ℕ} (hV : 0<V)
    {t : ℝ} (ht : Real.log V ≤ t) : finiteCriticalComplementBand Φ U V t=0 := by
  apply Finset.sum_eq_zero
  intro n hn
  have h := (Real.log_le_iff_le_exp (Nat.cast_pos.mpr hV : (0:ℝ)<V)).mp ht
  have hle := (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2 : (n:ℝ)≤V).trans h
  have hwidth := mul_nonneg (Real.exp_pos (t/2)).le (Real.sqrt_nonneg t)
  exact if_neg (not_lt.mpr (hle.trans (le_add_of_nonneg_right hwidth)))

/-- Failure of RH forces positive power-sized signed contributions from
consecutive central integer bands in arbitrarily late original middle tests.
Splitting into at most twice N^κ consecutive blocks retains a gain of order
N^(b−1/2−κ) on a band of length at most twice N^(1−κ). -/
theorem riemannHypothesis_or_positive_central_prime_bands : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (s : ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a) = (W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0 ≤ s ∧
      1/2 < zeroReSup ∧ ∀ b : ℝ, 1/2 < b → b < zeroReSup →
      ∀ κ : ℝ, 0 ≤ κ → κ < b-1/2 → ∃ c : ℝ, 0 < c ∧ ∃ᶠ N : ℕ in atTop,
        ∃ U V : ℕ, 0 < U ∧ U < V ∧ V ≤ N ∧ (N:ℝ)/2 ≤ U ∧ ((V-U:ℕ):ℝ) ≤ 2*(N:ℝ)^(1-κ) ∧
        (∀ t : ℝ, Real.log V ≤ t → finiteCriticalComplementBand Φ U V t=0) ∧
        let T := Real.log N+s
        c*(N:ℝ)^(b-1/2-κ) ≤ (∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
          finiteCriticalComplementBand Φ U V t*fractionalPrimeTest (T-t)) := by
  classical
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  obtain ⟨z,hz⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  have hΘ := hz.trans_le (re_le_zeroReSup z)
  obtain ⟨W₀,F,hW,ht,hF⟩ := riemannHypothesis_or_exists_criticalHalfLineGroundState.resolve_left hRH
  obtain ⟨_,_,Φ,hc,he,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨s,B,hs0,hB,hw,hlip⟩ := criticalState_positive_lipschitz_weight hW ht hF hc he
  have hi := (criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he
  obtain ⟨D,hD,hcut⟩ := octave_moving_cost hc hi hs hC hb hs0
  refine Or.inr ⟨W₀,F,Φ,s,hW,ht,hF,hc,he,hs0,hΘ,fun b hhalf hΘb κ hκ hκb => ?_⟩
  let a := testedIntegerWeight Φ s 0
  let d := min (1/2) (a/(2*B))
  let q := 1-d
  have hd : 0 < d := lt_min (by norm_num) (div_pos hw (by positivity))
  have hq : 1/2 ≤ q := by dsimp only [q,d]; linarith only [min_le_left (1/2:ℝ) (a/(2*B))]
  have hq1 : q < 1 := by dsimp only [q]; linarith only [hd]
  have hqB : B*(1-q) ≤ a/2 := by
    have h := (le_div_iff₀ (show 0<2*B by positivity)).mp (min_le_right (1/2:ℝ) (a/(2*B)))
    change d*(2*B) ≤ a at h
    dsimp only [q]; linarith only [h]
  obtain ⟨c,hc0,hfreq⟩ := frequently_centered_prime_record_band (by linarith only [hhalf] : 0<b)
    hΘb (by linarith only [hq] : 0<q) hq1
  let A := a/2*c
  have hA : 0<A := mul_pos (half_pos hw) hc0
  have hAh := half_pos hA
  refine ⟨(A/2)/2,half_pos hAh,?_⟩
  apply (hfreq.and_eventually (eventually_log_cost_le_power hAh hD (sub_pos.mpr hκb))).mono
  rintro N ⟨⟨L,hL,hLN,hfrac,hbig,hpre⟩,hsmall⟩
  have hNh : (N:ℝ)/2 ≤ L := by
    linarith only [hfrac,mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (α := ℝ) N)]
  have hgain := weighted_record_gain hB hq hw hqB hlip hL hLN hfrac hbig hpre
  change A*(N:ℝ)^(b-1/2) ≤ _ at hgain
  have hκ1 : κ ≤ 1 := by linarith only [hκb,hΘb,zeroReSup_le_one]
  obtain ⟨U,V,hLU,hUV,hVN,hwidth,hblock⟩ := short_positive_block _ hLN (hL.trans_le hLN) hA hκ hκ1 hgain
  have hU := hL.trans_le hLU
  have hUhalf := hNh.trans (Nat.cast_le.mpr hLU)
  refine ⟨U,V,hU,hUV,hVN,hUhalf,hwidth,fun _ h => finite_band_vanishes_after_log (hU.trans hUV) h,?_⟩
  have hdiff := (abs_le.mp (hcut U V N hU hUV.le hVN hUhalf)).1
  dsimp only
  linarith only [hblock,hdiff,hsmall]

#print axioms riemannHypothesis_or_positive_central_prime_bands
end GaloisForLFunctions.ExclusionOfTheCriticalState
