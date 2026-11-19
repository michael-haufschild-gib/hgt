import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheSignedFloorRemainderAboveTheTestAbscissa

/-!
# A positive complete prefix in the original prime test

A unit average in test time controls the variation of the normalized weight
by two endpoint readings. This retains the sign of a large Chebyshev excess
after summing every integer through its endpoint.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri _root_.RHTower

private theorem prefix_eq_psi_sub (j : ℕ) : centeredAbelPrefix 0 j=Chebyshev.psi j-j := by
  have h := _root_.RHTower.Sieve.psi_sub_eq_sum_Ioc (Nat.cast_nonneg (α := ℝ) j)
  simp only [Chebyshev.psi_zero,sub_zero,Nat.floor_zero,Nat.floor_natCast] at h
  rw [centeredAbelPrefix,Finset.sum_sub_distrib,← h,Finset.sum_const,Nat.card_Ioc,
    Nat.sub_zero,nsmul_eq_mul,mul_one]

/-- A bound on the values of the translated remainder controls the variation
of its unit average. Summation by parts then costs the largest prefix times
the logarithmic length of the index interval. -/
private theorem exists_time_prefix_error {r : ℝ → ℝ} (hr : Continuous r) {N : ℕ}
    {S Z M : ℝ} (hM : 0 ≤ M) (hprefix : ∀ j ≤ N, |centeredAbelPrefix 0 j| ≤ M)
    (hb : ∀ u : ℝ, S-Real.log N ≤ u → |r u| ≤ Z) :
    ∃ T ∈ Icc S (S+1), -(M*Z*(1+2*Real.log N)) ≤
      ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n-1)*r (T-Real.log n) := by
  let q := Real.log N
  let J := fun x : ℝ => ∫ t in (0:ℝ)..x, r t
  let w := fun p : ℝ => J (S+1-p)-J (S-p)
  have hJ (x : ℝ) : HasDerivAt J (r x) x := intervalIntegral.integral_hasDerivAt_right
    (hr.intervalIntegrable _ _) hr.aestronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt
  have hw (p : ℝ) : w p = ∫ t in S..S+1, r (t-p) := by
    rw [intervalIntegral.integral_comp_sub_right]
    exact intervalIntegral.integral_interval_sub_left (hr.intervalIntegrable _ _) (hr.intervalIntegrable _ _)
  have hder (p : ℝ) : HasDerivAt w (r (S-p)-r (S+1-p)) p := by
    have h := ((hJ (S+1-p)).comp p ((hasDerivAt_id p).const_sub (S+1))).sub
      ((hJ (S-p)).comp p ((hasDerivAt_id p).const_sub S))
    rw [show r (S-p)-r (S+1-p)=r (S+1-p)*(-1)-r (S-p)*(-1) by ring]
    exact h
  have hS : S ≤ S+1 := by linarith
  have hZ : 0 ≤ Z := (abs_nonneg _).trans (hb _ le_rfl)
  have hbound : |w q| ≤ Z := by
    rw [hw,← Real.norm_eq_abs]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := S) (b := S+1)
      (f := fun t => r (t-q)) (C := Z) (fun t ht => by
        rw [uIoc_of_le hS] at ht
        exact (Real.norm_eq_abs _).le.trans (hb _ (sub_le_sub_right ht.1.le q)))
    simpa only [add_sub_cancel_left,abs_one,mul_one] using h
  have hlog : Monotone (fun j : ℕ => Real.log j) := by
    intro i j hij
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simpa only [Nat.cast_zero,Real.log_zero] using Real.log_natCast_nonneg j
    · exact Real.log_le_log (Nat.cast_pos.mpr hi) (Nat.cast_le.mpr hij)
  let P := centeredAbelPrefix 0
  let v := fun j : ℕ => w (Real.log j)
  have step (j : ℕ) (hj : j<N) : |v j-v (j+1)| ≤ 2*Z*(Real.log (j+1:ℕ)-Real.log j) := by
    have hmem (i : ℕ) (hi : i≤N) : Real.log i ∈ Icc 0 q := ⟨Real.log_natCast_nonneg _,hlog hi⟩
    have h := (convex_Icc (0:ℝ) q).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun p _ => (hder p).hasDerivWithinAt) (C := 2*Z) (fun p hp => by
        rw [Real.norm_eq_abs]
        apply (abs_sub _ _).trans
        linarith only [hb (S-p) (by linarith only [hp.2] : S-q ≤ S-p),
          hb (S+1-p) (by linarith only [hp.2] : S-q ≤ S+1-p)])
      (hmem (j+1) hj) (hmem j hj.le)
    simpa only [Real.norm_eq_abs,abs_sub_comm (Real.log j),abs_of_nonneg
      (sub_nonneg.mpr (hlog (Nat.le_succ j)))] using h
  have hsum : |∑ j ∈ Finset.Ico 0 N, P j*(v j-v (j+1))| ≤ M*(2*Z)*q := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc _ ≤ ∑ j ∈ Finset.Ico 0 N, (M*(2*Z))*(Real.log (j+1:ℕ)-Real.log j) := by
              apply Finset.sum_le_sum
              intro j hj
              have hjN := (Finset.mem_Ico.mp hj).2
              rw [abs_mul,mul_assoc M]
              exact mul_le_mul (hprefix j hjN.le) (step j hjN) (abs_nonneg _) hM
         _ = _ := by
              rw [← Finset.mul_sum,Nat.Ico_zero_eq_range,Finset.sum_range_sub (fun i : ℕ => Real.log i) N]
              simp only [Nat.cast_zero,Real.log_zero,sub_zero,q]
  let f := fun t : ℝ => ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n-1)*r (t-Real.log n)
  have hterm (n : ℕ) : Continuous (fun t => (vonMangoldt n-1)*r (t-Real.log n)) :=
    continuous_const.mul (hr.comp (continuous_id.sub continuous_const))
  have hf : Continuous f := continuous_finsetSum _ fun n _ => hterm n
  have hmean : (∫ t in S..S+1, f t) = ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n-1)*v n := by
    dsimp only [f]
    rw [intervalIntegral.integral_finsetSum (s := Finset.Ioc 0 N)
      (f := fun n t => (vonMangoldt n-1)*r (t-Real.log n))
      (fun n _ => (hterm n).intervalIntegrable _ _)]
    simp only [v,hw,intervalIntegral.integral_const_mul]
  have hP0 : P 0=0 := by simp [P,centeredAbelPrefix]
  have hlower : -(M*Z*(1+2*q)) ≤ ∫ t in S..S+1, f t := by
    rw [hmean,centeredAbelPrefix_by_parts v (Nat.zero_le 0) (Nat.zero_le N)]
    change _ ≤ v N*P N-v 0*P 0+_
    rw [hP0,mul_zero,sub_zero]
    have hEnd : |v N*P N| ≤ Z*M := by
      rw [abs_mul]; exact mul_le_mul hbound (hprefix N le_rfl) (abs_nonneg _) hZ
    linarith only [(abs_le.mp hEnd).1,(abs_le.mp hsum).1]
  obtain ⟨T,hT,hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨S,le_rfl,hS⟩ hf.continuousOn
  refine ⟨T,hT,hlower.trans ?_⟩
  have h := intervalIntegral.integral_mono_on (μ := volume) hS (hf.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) (fun t ht => hmax ht)
  simpa only [intervalIntegral.integral_const,add_sub_cancel_left,one_smul] using h

/-- The normalized whole weight depends only on the difference of log
abscissae. Its deviation from the positive half-tilt decays on the right. -/
private theorem normalized_profile {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (u : ℝ) (_ : 0 ≤ u), windowThreshold u)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) :
    ∃ (a u₀ : ℝ) (r : ℝ → ℝ), 0<a ∧ Continuous r ∧
      (∀ u, u₀ ≤ u → |r u| ≤ Real.exp (-u/2)) ∧
      ∀ T p, Real.exp (T/2)*testedIntegerWeight Φ T p=a+r (T-p) := by
  let a := (∫ u, Φ u)*(∫ v, Real.exp (v/2)*Φ v)/2
  let r := fun u => testedIntegerWeight Φ 0 (-u)-a
  have htrans (T p : ℝ) : Real.exp (T/2)*testedIntegerWeight Φ T p=a+r (T-p) := by
    have h := scaled_testedIntegerWeight_eq_fractional_reading Φ 0 (-(T-p))
    simp only [zero_div,Real.exp_zero,one_mul,zero_sub,neg_neg] at h
    rw [scaled_testedIntegerWeight_eq_fractional_reading,← h]
    dsimp only [r]; ring
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have htilt (d : ℝ) (hd' : -4<d) : Integrable fun v => Real.exp (d*v)*Φ v := by
    apply (integrable_mul_exp_of_domain hd hd').congr
    filter_upwards [he] with v hv
    rw [hv,mul_comm]
  have hp : Integrable fun v => Real.exp (-v/2)*Φ v := by
    simpa only [show ∀ v : ℝ, (-1/2)*v= -v/2 by intro v; ring] using htilt (-1/2) (by norm_num)
  have hm : Integrable fun v => Real.exp (v/2)*Φ v := by
    simpa only [show ∀ v : ℝ, (1/2)*v=v/2 by intro v; ring] using htilt (1/2) (by norm_num)
  have hw : Continuous (testedIntegerWeight Φ 0) := continuous_iff_continuousAt.mpr
    fun p => (hasDerivAt_testedIntegerWeight hc hC hb hp hm 0 p).continuousAt
  obtain ⟨ha,hwgt⟩ := criticalState_signed_weight_below_abscissa hW ht hF hc he
  obtain ⟨Y,hY,hy⟩ := hwgt 1 zero_lt_one
  refine ⟨a,Real.log Y,r,ha,(hw.comp continuous_neg).sub continuous_const,fun u hu => ?_,htrans⟩
  have h := hy u 0 (by rw [sub_zero]; exact (Real.log_le_iff_le_exp hY).mp hu)
  rw [htrans,sub_zero,zero_sub,one_mul] at h
  change |a+r u-a| ≤ _ at h
  simpa only [add_sub_cancel_left] using h

private theorem frequently_positive_prefix {b : ℝ} (hb : 0<b) (hbΘ : b<zeroReSup) :
    ∃ᶠ N : ℕ in atTop, (N:ℝ)^b < centeredAbelPrefix 0 N := by
  rw [frequently_atTop]
  intro J
  obtain ⟨x,hx,hJ⟩ := ((frequently_rpow_lt_chebyshevPsi_sub hbΘ).and_eventually
    (eventually_ge_atTop (J:ℝ))).exists
  have hx0 := (Nat.cast_nonneg J).trans hJ
  have hfloor := Nat.floor_le hx0
  have hp := Real.rpow_le_rpow (Nat.cast_nonneg ⌊x⌋₊) hfloor hb.le
  refine ⟨⌊x⌋₊,Nat.le_floor hJ,?_⟩
  rw [prefix_eq_psi_sub]
  rw [Chebyshev.psi_eq_psi_coe_floor x] at hx
  linarith only [hp,hx,hfloor]

/-- The fixed comparison with the full prefix costs a logarithmic
polynomial whenever the test lies to the right of its integer endpoint. -/
private theorem whole_prefix_sub_middle {Φ : ℝ → ℝ} (hc : Continuous Φ) (hi : Integrable Φ)
    (hs : ∀ u, 0 ≤ u → Φ u=0) {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u, |Φ u| ≤ C*Real.exp (2*u)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) (T : ℝ), Real.log N ≤ T →
      |(∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n))-
        (∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T), finiteCriticalComplementRow Φ N t*
          fractionalPrimeTest (T-t))| ≤ B*(1+Real.log N)^2 := by
  let m := ∫ v, Φ v
  obtain ⟨D,hD,hcut⟩ := finite_complement_prefix_time_cut hc hs hC hb
  refine ⟨4*|m| *C+|m| *D,by positivity,fun N T ht => ?_⟩
  let q := Real.log N
  have hq : 0 ≤ q := Real.log_natCast_nonneg N
  have hT := hq.trans ht
  have hp : 1 ≤ (1+q)^2 := by nlinarith only [hq,sq_nonneg q]
  have hr : Real.sqrt q+1 ≤ 2*(1+q) := by
    nlinarith only [Real.sq_sqrt hq,sq_nonneg (Real.sqrt q-1),hq]
  have hpoly : (q+1)*(Real.sqrt q+1) ≤ 2*(1+q)^2 := by
    apply (mul_le_mul_of_nonneg_left hr (by linarith only [hq])).trans_eq; ring
  have he := abs_tested_prefix_sub_moving_edge hc hi hs hC hb N T
  have he1 : Real.exp ((q-T)/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [ht] )
  have hv := hcut N (T/6) (6*T) T (by linarith only [hT]) (by linarith only [ht,hT])
  have hv1 : Real.exp ((5*(T/6)-T)/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hT])
  let whole := ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)
  let row := fun t => finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t)
  change |whole-m*(∫ t in Ioc (T/6) (6*T), row t)| ≤ _
  apply (abs_sub_le _ (m*∫ t, row t) _).trans
  rw [← mul_sub,abs_mul]
  have he' : |whole-m*(∫ t, row t)| ≤ 4*|m| *C*(1+q)^2 := by
    apply he.trans
    apply (mul_le_of_le_one_right (by positivity) he1).trans
    linarith only [mul_le_mul_of_nonneg_left hpoly (show 0≤2*|m| *C by positivity)]
  have hv' := mul_le_mul_of_nonneg_left (hv.trans (mul_le_of_le_one_right hD hv1)) (abs_nonneg m)
  change _ ≤ (4*|m| *C+|m| *D)*(1+q)^2
  linarith only [he',hv',mul_le_mul_of_nonneg_left hp (mul_nonneg (abs_nonneg m) hD)]

private theorem eventually_absorb_polynomial {b r ε C : ℝ} (hr : r < b) (hε : 0 < ε) (hC : 0 ≤ C) :
    ∀ᶠ q : ℝ in atTop, C*(1+q)^2*Real.exp (r*q) ≤ ε*Real.exp (b*q) := by
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (b-r) (sub_pos.mpr hr)).const_mul (4*C)
  simp only [mul_zero,Real.rpow_two] at hlim
  filter_upwards [hlim.eventually_le_const hε,eventually_ge_atTop (1:ℝ)] with q h hq
  change 4*C*(q^2*Real.exp (-(b-r)*q)) ≤ ε at h
  have hpoly : (1+q)^2 ≤ 4*q^2 := by
    nlinarith only [sq_nonneg (q-1),hq,mul_nonneg (sub_nonneg.mpr hq) (show 0≤q by linarith only [hq])]
  have he : Real.exp (-(b-r)*q)*Real.exp (b*q)=Real.exp (r*q) := by
    rw [← Real.exp_add]; congr 1; ring
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC) (Real.exp_pos _).le).trans
  apply le_trans _ (mul_le_mul_of_nonneg_right h (Real.exp_pos (b*q)).le)
  apply le_of_eq
  rw [← he]; ring

/-- If RH fails, every sufficiently small fixed positive upper power gap admits arbitrarily late original tests
whose complete prefix still retains a power gain after the entire upper tail.
Both endpoints of the intervening interval can approach the test exponent one. -/
theorem riemannHypothesis_or_diagonal_positive_prefix : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (c g : ℝ), 0 < W₀ ∧
      (⨅ (u : ℝ) (_ : 0 ≤ u), windowThreshold u) = (W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      0<c ∧ 0<g ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
        ∃ᶠ N : ℕ in atTop, ∃ T ∈ Icc ((1+δ)*Real.log N) ((1+δ)*Real.log N+1),
          let m := ∫ v, Φ v
          let headSum := m*(∫ t in Ioc (T/6) (6*T),
            finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t))
          let tail := m*(∫ t in Ioc (T/6) (6*T),
            criticalComplementBand Φ ⌈Real.exp ((1+η)*T)⌉₊ t*fractionalPrimeTest (T-t))
          let total := m*(∫ t in Ioc (T/6) (6*T),
            criticalComplementBand Φ 0 t*fractionalPrimeTest (T-t))
          let band := m*(∫ t in Ioc (T/6) (6*T),
            finiteCriticalComplementBand Φ N ⌈Real.exp ((1+η)*T)⌉₊ t*fractionalPrimeTest (T-t))
          c*(N:ℝ)^g ≤ headSum-|tail| ∧ c*(N:ℝ)^g ≤ total-band := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  obtain ⟨z,hz⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  have hhalf := hz.trans_le (re_le_zeroReSup z)
  have hΘ : zeroReSup ≤ 20999/24000 := zeroReSup_le_of_forall_re_le fun z => by
    by_contra! hz
    exact MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hz
      (riemannZeta_eq_zero_of_xiZeroCopy z)
  obtain ⟨W₀,F,hW,ht,hF⟩ := riemannHypothesis_or_exists_criticalHalfLineGroundState.resolve_left hRH
  obtain ⟨_,_,Φ,hc,he,hs,⟨C,hC,hbnd⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  obtain ⟨a,u₀,r,ha,hr,hrb,hread⟩ := normalized_profile hW ht hF hc he hC hbnd
  obtain ⟨J,hJ,hwall⟩ := whole_prefix_sub_middle hc
    ((criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he) hs hC hbnd
  let g := (zeroReSup-1/2)/2
  let c := (a/4)*Real.exp (-(1/2))
  have hquarter : 0 < a/4 := by positivity
  refine Or.inr ⟨W₀,F,Φ,c,g,hW,ht,hF,hc,he,mul_pos hquarter (Real.exp_pos _),
    div_pos (sub_pos.mpr hhalf) (by norm_num),fun η hη hη1 => ?_⟩
  let δ₀ := min ((zeroReSup-1/2)/2) (η*(1-zeroReSup)/4)
  have hδ₀ : 0 < δ₀ := lt_min (by linarith only [hhalf])
    (div_pos (mul_pos hη (by linarith only [hΘ])) (by norm_num))
  refine ⟨δ₀,hδ₀,fun δ hδ hδmax => ?_⟩
  obtain ⟨hδw,hδη⟩ := lt_min_iff.mp hδmax
  have hδh : δ < (1-zeroReSup)/4 := hδη.trans_le
    (by linarith only [mul_le_mul_of_nonneg_right hη1 (show 0 ≤ 1-zeroReSup by linarith only [hΘ])])
  let l := 1+δ
  let b := zeroReSup-δ/8
  let θ := zeroReSup+δ/8
  let d := 1-θ
  let p := 1-(1+η)*d
  have hgain : g ≤ b-l/2 := by dsimp only [g,b,l]; linarith only [hδw,hhalf,hδ]
  have hbl : l/2<b := by dsimp only [b,l]; linarith only [hδw,hδ]
  have hb : 0<b := by dsimp only [b]; linarith only [hδw,hδ]
  have hbΘ : b<zeroReSup := by dsimp only [b]; linarith only [hδ]
  have hθ : zeroReSup<θ := by dsimp only [θ]; linarith only [hδ]
  have hd : 0<d := by dsimp only [d,θ]; linarith only [hδh,hδ]
  have hθd : zeroReSup<1-d := by dsimp only [d]; linarith only [hθ]
  have hp : 0<p := by
    have h := mul_le_mul_of_nonneg_right hη1 hd.le
    dsimp only [p,d,θ] at h ⊢
    linarith only [hhalf,hδ,h]
  have hp1 : p≤1 := by dsimp only [p]; linarith only [mul_nonneg (show 0≤1+η by linarith only [hη]) hd.le]
  have hpb : p*l<b := by
    have h := mul_le_mul_of_nonneg_right hp1 hδ.le
    dsimp only [l,b,p,d,θ] at h ⊢
    linarith only [hδη,hδ,h,mul_le_mul_of_nonneg_right hη1 hδ.le]
  have hθb : θ-δ/2<b := by dsimp only [θ,b]; linarith only [hδ]
  obtain ⟨D,B,hD,hB,hupper⟩ := criticalState_upper_tail_at_power_separation hW ht hF hc he hd hθd hη hη1
  obtain ⟨A,hA,hE⟩ := exists_abs_chebyshevPsi_sub_le_rpow hθ
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hev₁ := hlog.eventually (eventually_absorb_polynomial (C := 3*A) hθb hquarter (by positivity))
  have hev₂ := hlog.eventually (eventually_absorb_polynomial (C := (J+D)*Real.exp (1/2)) hbl hquarter
    (by positivity))
  have hev₃ := hlog.eventually (eventually_absorb_polynomial (C := B*Real.exp p) hpb hquarter (by positivity))
  apply ((frequently_positive_prefix hb hbΘ).and_eventually
    (((hev₁.and hev₂).and hev₃).and ((hlog.eventually_ge_atTop 1).and
      ((hlog.const_mul_atTop hδ).eventually_ge_atTop u₀)))).mono
  rintro N ⟨hbig,⟨⟨h₁,h₂⟩,h₃⟩,hq,hfar⟩
  let q := Real.log N
  change 1 ≤ q at hq
  change 3*A*(1+q)^2*Real.exp ((θ-δ/2)*q) ≤ (a/4)*Real.exp (b*q) at h₁
  change (J+D)*Real.exp (1/2)*(1+q)^2*Real.exp ((l/2)*q) ≤ (a/4)*Real.exp (b*q) at h₂
  change B*Real.exp p*(1+q)^2*Real.exp ((p*l)*q) ≤ (a/4)*Real.exp (b*q) at h₃
  change u₀ ≤ δ*q at hfar
  have hN : 0 < N := by
    by_contra! hn
    have hzero : N=0 := Nat.eq_zero_of_le_zero hn
    norm_num [q,hzero] at hq
  have hN0 : 0 < (N:ℝ) := Nat.cast_pos.mpr hN
  have hq0 := zero_le_one.trans hq
  let S := l*q
  let Z := Real.exp (-δ*q/2)
  let M := A*Real.exp (θ*q)
  have hgap : S-q=δ*q := by dsimp only [S,l]; ring
  have hM : 0 ≤ M := mul_nonneg hA (Real.exp_pos _).le
  have hpre (j : ℕ) (hj : j≤N) : |centeredAbelPrefix 0 j| ≤ M := by
    rcases Nat.eq_zero_or_pos j with rfl | hj'
    · simpa only [centeredAbelPrefix,Finset.Ioc_self,Finset.sum_empty,abs_zero] using hM
    rw [prefix_eq_psi_sub]
    apply (hE j (by exact_mod_cast hj')).trans (mul_le_mul_of_nonneg_left _ hA)
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hj'),Real.exp_le_exp,mul_comm θ]
    exact mul_le_mul_of_nonneg_right (Real.log_le_log (Nat.cast_pos.mpr hj') (Nat.cast_le.mpr hj))
      (by linarith only [hhalf,hθ])
  have hrem (u : ℝ) (hu : S-q ≤ u) : |r u| ≤ Z := by
    rw [hgap] at hu
    exact (hrb u (hfar.trans hu)).trans (Real.exp_le_exp.mpr (by linarith only [hu]))
  obtain ⟨T,hT,herr⟩ := exists_time_prefix_error hr hM hpre hrem
  refine ⟨T,hT,?_⟩
  have hTmax : T ≤ l*q+1 := hT.2
  have hqT : q ≤ T := (sub_nonneg.mp ((mul_nonneg hδ.le hq0).trans_eq hgap.symm)).trans hT.1
  have hpoly : 1 ≤ (1+q)^2 := by nlinarith only [hq0,sq_nonneg q]
  have hZerr : M*Z*(1+2*q) ≤ (a/4)*Real.exp (b*q) := by
    have hex : Real.exp (θ*q)*Z=Real.exp ((θ-δ/2)*q) := by dsimp only [Z]; rw [← Real.exp_add]; congr 1; ring
    change A*Real.exp (θ*q)*Z*(1+2*q) ≤ _
    rw [mul_assoc A,hex]
    apply le_trans _ h₁
    have hpoly' : 1+2*q ≤ 3*(1+q)^2 := by nlinarith only [sq_nonneg q,hq0]
    linarith only [mul_le_mul_of_nonneg_left hpoly' (mul_nonneg hA (Real.exp_pos ((θ-δ/2)*q)).le)]
  let whole := ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)
  let m := ∫ v, Φ v
  let headSum := m*(∫ t in Ioc (T/6) (6*T), finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t))
  let tail := m*(∫ t in Ioc (T/6) (6*T), criticalComplementBand Φ ⌈Real.exp ((1+η)*T)⌉₊ t*fractionalPrimeTest (T-t))
  have hsplit : Real.exp (T/2)*whole = a*centeredAbelPrefix 0 N+
      ∑ n ∈ Finset.Ioc 0 N, (vonMangoldt n-1)*r (T-Real.log n) := by
    dsimp only [whole,centeredAbelPrefix]
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    linear_combination (vonMangoldt n-1)*(hread T (Real.log n))
  rw [Real.rpow_def_of_pos hN0,mul_comm (Real.log N) b] at hbig
  have hwhole : 3*(a/4)*Real.exp (b*q) ≤ Real.exp (T/2)*whole := by
    rw [hsplit]
    linarith only [mul_le_mul_of_nonneg_left hbig.le ha.le,herr,hZerr]
  have hex (z : ℝ) (hz : 0 ≤ z) : Real.exp (z*T) ≤ Real.exp z*Real.exp ((z*l)*q) := by
    rw [← Real.exp_add,Real.exp_le_exp]
    linarith only [mul_le_mul_of_nonneg_left hTmax hz]
  have hhalfExp : Real.exp (T/2) ≤ Real.exp (1/2)*Real.exp ((l/2)*q) := by
    simpa only [one_div,inv_mul_eq_div] using hex (1/2) (by norm_num)
  have hcost₁ : Real.exp (T/2)*(|whole-headSum|+D) ≤ (a/4)*Real.exp (b*q) := by
    have h := hwall N T hqT
    change |whole-headSum| ≤ J*(1+q)^2 at h
    apply le_trans _ h₂
    have hle : |whole-headSum|+D ≤ (J+D)*(1+q)^2 := by
      linarith only [h,mul_le_mul_of_nonneg_left hpoly hD]
    apply (mul_le_mul hhalfExp hle (add_nonneg (abs_nonneg _) hD) (by positivity)).trans_eq
    ring
  have hcost₂ : B*Real.exp (p*T) ≤ (a/4)*Real.exp (b*q) := by
    apply le_trans _ h₃
    apply (mul_le_mul_of_nonneg_left (hex p hp.le) hB).trans
    linarith only [mul_le_mul_of_nonneg_left hpoly
      (mul_nonneg (mul_nonneg hB (Real.exp_pos p).le) (Real.exp_pos ((p*l)*q)).le)]
  have hup := mul_le_mul_of_nonneg_left (hupper T (hq.trans hqT)) (Real.exp_pos (T/2)).le
  change Real.exp (T/2)*|tail| ≤ Real.exp (T/2)*(D+B*Real.exp ((1/2-(1+η)*d)*T)) at hup
  have hprod : Real.exp (T/2)*Real.exp ((1/2-(1+η)*d)*T)=Real.exp (p*T) := by
    rw [← Real.exp_add]; dsimp only [p]; congr 1; ring
  rw [mul_add,mul_left_comm (Real.exp (T/2)) B,hprod] at hup
  have hpay : (a/4)*Real.exp (b*q) ≤ Real.exp (T/2)*(headSum-|tail|) := by
    linarith only [hwhole,hcost₁,hcost₂,hup,
      mul_le_mul_of_nonneg_left (le_abs_self (whole-headSum)) (Real.exp_pos (T/2)).le]
  have hnet : c*(N:ℝ)^g ≤ headSum-|tail| := by
    apply le_of_mul_le_mul_left _ (Real.exp_pos (T/2))
    apply le_trans _ hpay
    rw [Real.rpow_def_of_pos hN0,mul_comm (Real.log N) g]
    change Real.exp (T/2)*((a/4)*Real.exp (-(1/2))*Real.exp (g*q)) ≤ _
    have hscale : Real.exp (T/2)*Real.exp (-(1/2))*Real.exp (g*q) ≤ Real.exp (b*q) := by
      rw [← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
      linarith only [hTmax,mul_le_mul_of_nonneg_right hgain hq0]
    linarith only [mul_le_mul_of_nonneg_left hscale hquarter.le]
  refine ⟨hnet,?_⟩
  let k := ⌈Real.exp ((1+η)*T)⌉₊
  have hNk : N ≤ k := by
    apply (Nat.cast_le (α := ℝ)).mp
    apply le_trans _ (Nat.le_ceil _)
    rw [← Real.exp_log hN0]
    exact Real.exp_le_exp.mpr (by change q ≤ (1+η)*T; linarith only [hqT,hq,mul_nonneg hη.le (hq0.trans hqT)])
  have hi := (criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he
  let K := fun t => fractionalPrimeTest (T-t)
  let total := m*(∫ t in Ioc (T/6) (6*T), criticalComplementBand Φ 0 t*K t)
  let band := m*(∫ t in Ioc (T/6) (6*T), finiteCriticalComplementBand Φ N k t*K t)
  have hrest : total-band=headSum+tail := by
    dsimp only [total,band,headSum,tail,K]
    rw [upper_band_integral_split hc hi hC hbnd (Nat.zero_le k),finite_band_integral_sub hc hi hNk]
    simp only [finiteCriticalComplementRow,k]
    ring
  change c*(N:ℝ)^g ≤ total-band
  rw [hrest]
  linarith only [hnet,neg_abs_le tail]

/-- On arbitrarily late original tests, removing one integer interval confined
to any prescribed neighborhood of log(n)/T = 1 leaves an exponential gain.
The exponent and its positive coefficient are uniform in that neighborhood. -/
theorem riemannHypothesis_or_gain_outside_diagonal_interval : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (c g : ℝ), 0 < W₀ ∧
      (⨅ (u : ℝ) (_ : 0 ≤ u), windowThreshold u)=(W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      0<c ∧ 0<g ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ᶠ T : ℝ in atTop,
        ∃ N : ℕ, T/(1+η) ≤ Real.log N ∧ Real.log N ≤ T ∧
          let m := ∫ v, Φ v
          let total := m*(∫ t in Ioc (T/6) (6*T),
            criticalComplementBand Φ 0 t*fractionalPrimeTest (T-t))
          let band := m*(∫ t in Ioc (T/6) (6*T),
            finiteCriticalComplementBand Φ N ⌈Real.exp ((1+η)*T)⌉₊ t*fractionalPrimeTest (T-t))
          c*Real.exp (g*T) ≤ total-band := by
  rcases riemannHypothesis_or_diagonal_positive_prefix with hr | ⟨W,F,Φ,c,g,hW,ht,hF,hc,he,hc₀,hg,h⟩
  · exact Or.inl hr
  refine Or.inr ⟨W,F,Φ,c,g/2,hW,ht,hF,hc,he,hc₀,by positivity,fun η hη hη1 => ?_⟩
  obtain ⟨δ₀,hδ₀,hδ⟩ := h η hη hη1
  let δ := min (δ₀/2) (η/2)
  have hpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hsmall : δ < δ₀ := (min_le_left _ _).trans_lt (by linarith only [hδ₀])
  have hgap : 0 < η-δ := by dsimp only [δ]; linarith only [min_le_right (δ₀/2) (η/2),hη]
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  rw [frequently_atTop]
  intro S
  obtain ⟨N,hN,hS,hgapN,hN0⟩ := ((hδ δ hpos hsmall).and_eventually
    ((hlog.eventually_ge_atTop S).and (((hlog.const_mul_atTop hgap).eventually_ge_atTop 1).and
      (eventually_ge_atTop (1:ℕ))))).exists
  obtain ⟨T,hT,_,hnet⟩ := hN
  have hq := Real.log_natCast_nonneg N
  have hlo : Real.log N ≤ T := by linarith only [hT.1,mul_nonneg hpos.le hq]
  change 1 ≤ (η-δ)*Real.log N at hgapN
  have hhi : T ≤ Real.log N*(1+η) := by linarith only [hT.2,hgapN]
  refine ⟨T,hS.trans hlo,N,(div_le_iff₀ (by linarith only [hη] : 0<1+η)).mpr hhi,hlo,?_⟩
  have h2 : T ≤ 2*Real.log N := by linarith only [hhi,mul_le_mul_of_nonneg_right hη1 hq]
  apply le_trans _ hnet
  apply mul_le_mul_of_nonneg_left _ hc₀.le
  rw [Real.rpow_def_of_pos (by exact_mod_cast hN0 : 0 < (N:ℝ)),Real.exp_le_exp]
  linarith only [mul_le_mul_of_nonneg_left h2 hg.le]

/-- If RH fails, every sufficiently small fixed positive dilation exponent
admits arbitrarily late original tests at which the complete prefix through
N retains a power gain even after paying the entire infinite upper tail.
Only one consecutive interval of integers lies between these two readings. -/
theorem riemannHypothesis_or_positive_complete_prefix : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ) (δ₀ : ℝ), 0 < W₀ ∧
      (⨅ (u : ℝ) (_ : 0 ≤ u), windowThreshold u) = (W₀:EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ c g : ℝ, 0<c ∧ 0<g ∧
        ∃ᶠ N : ℕ in atTop, ∃ T ∈ Icc ((1+δ)*Real.log N) ((1+δ)*Real.log N+1),
          let m := ∫ v, Φ v
          let headSum := m*(∫ t in Ioc (T/6) (6*T),
            finiteCriticalComplementRow Φ N t*fractionalPrimeTest (T-t))
          let tail := m*(∫ t in Ioc (T/6) (6*T),
            criticalComplementBand Φ ⌈Real.exp (8*T/7)⌉₊ t*fractionalPrimeTest (T-t))
          let total := m*(∫ t in Ioc (T/6) (6*T),
            criticalComplementBand Φ 0 t*fractionalPrimeTest (T-t))
          let band := m*(∫ t in Ioc (T/6) (6*T),
            finiteCriticalComplementBand Φ N ⌈Real.exp (8*T/7)⌉₊ t*fractionalPrimeTest (T-t))
          c*(N:ℝ)^g ≤ headSum-|tail| ∧ c*(N:ℝ)^g ≤ total-band := by
  rcases riemannHypothesis_or_diagonal_positive_prefix with h | ⟨W,F,Φ,c,g,hW,ht,hF,hc,he,hc₀,hg,h⟩
  · exact Or.inl h
  obtain ⟨δ₀,hδ₀,hδ⟩ := h (1/7) (by norm_num) (by norm_num)
  refine Or.inr ⟨W,F,Φ,δ₀,hW,ht,hF,hc,he,hδ₀,fun δ hpos hlt => ⟨c,g,hc₀,hg,?_⟩⟩
  simpa only [show ∀ T : ℝ, (1+1/7)*T=8*T/7 by intro T; ring] using hδ δ hpos hlt

#print axioms riemannHypothesis_or_gain_outside_diagonal_interval
#print axioms riemannHypothesis_or_diagonal_positive_prefix
#print axioms riemannHypothesis_or_positive_complete_prefix
end GaloisForLFunctions.ExclusionOfTheCriticalState
