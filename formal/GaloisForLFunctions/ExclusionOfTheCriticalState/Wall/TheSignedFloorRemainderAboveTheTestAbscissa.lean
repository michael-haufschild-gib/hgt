import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheUpperIntegerTailOnPrimeExcessRecords

/-!
# The signed floor remainder above the test abscissa

At each particle the fractional part splits into a reciprocal weight and
a decreasing integer floor. Only prefixes ending below the particle's
abscissa enter the variation of the floor. This controls the entire upper
band even when its lower endpoint is the test scale itself.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri _root_.RHTower

/-- A Chebyshev bound controls the floor sum uniformly in its right endpoint.
The floor vanishes above Y, so all its jumps see prefixes of length at most Y. -/
theorem signed_floor_band_bound {d : ℝ} (hd : 0 < d) (hθ : zeroReSup < 1-d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k L : ℕ) (Y : ℝ), 1 ≤ k → k ≤ L → 0 ≤ Y →
      |∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)*(⌊Y/(n:ℝ)⌋:ℝ)| ≤
        C*(k:ℝ)^(-d)*Y*(Y/k) := by
  obtain ⟨A,hA,hE⟩ := exists_abs_chebyshevPsi_sub_le_rpow hθ
  refine ⟨2*A,by positivity,fun k L Y hk hkL hY => ?_⟩
  let w := fun n : ℕ => (⌊Y/(n:ℝ)⌋:ℝ)
  let M := 2*A*(k:ℝ)^(-d)*Y
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hw (n : ℕ) : 0 ≤ w n := by
    dsimp only [w]; exact_mod_cast Int.floor_nonneg.mpr (div_nonneg hY (Nat.cast_nonneg n))
  have hstep (j : ℕ) (hj : k ≤ j) : w (j+1) ≤ w j := by
    have hj0 := hk0.trans_le (Nat.cast_le.mpr hj)
    dsimp only [w]
    exact_mod_cast Int.floor_mono (div_le_div_of_nonneg_left hY hj0
      (Nat.cast_le.mpr (Nat.le_succ j) : (j:ℝ) ≤ (j+1:ℕ)))
  have hzero (j : ℕ) (hj : Y < (j:ℝ)) : w j=0 := by
    have hj0 := hY.trans_lt hj
    dsimp only [w]
    rw [Int.floor_eq_zero_iff.mpr ⟨div_nonneg hY hj0.le,(div_lt_one hj0).mpr hj⟩,Int.cast_zero]
  have hpoint (j : ℕ) (hj : k ≤ j) (hjy : (j:ℝ) ≤ Y) :
      |centeredAbelPrefix k j| ≤ M := by
    have hE' (i : ℕ) (hi : k ≤ i) (hiy : (i:ℝ) ≤ Y) :
        |Chebyshev.psi i-i| ≤ A*((k:ℝ)^(-d)*Y) := by
      have hi0 := hk0.trans_le (Nat.cast_le.mpr hi)
      apply (hE i (by exact_mod_cast hk.trans hi)).trans
      apply mul_le_mul_of_nonneg_left _ hA
      rw [sub_eq_add_neg,Real.rpow_add hi0,Real.rpow_one,mul_comm]
      exact mul_le_mul (Real.rpow_le_rpow_of_nonpos hk0 (Nat.cast_le.mpr hi) (neg_nonpos.mpr hd.le))
        hiy hi0.le (Real.rpow_nonneg hk0.le _)
    have hpsi := _root_.RHTower.Sieve.psi_sub_eq_sum_Ioc (Nat.cast_le.mpr hj : (k:ℝ) ≤ j)
    simp only [Nat.floor_natCast] at hpsi
    have he : centeredAbelPrefix k j=(Chebyshev.psi j-j)-(Chebyshev.psi k-k) := by
      rw [centeredAbelPrefix,Finset.sum_sub_distrib,← hpsi,Finset.sum_const,Nat.card_Ioc,
        nsmul_eq_mul,mul_one,Nat.cast_sub hj]; ring
    rw [he]
    apply (abs_sub _ _).trans
    dsimp only [M]
    linarith only [hE' j hj hjy,hE' k le_rfl ((Nat.cast_le.mpr hj).trans hjy)]
  have hcost (j : ℕ) (hj : k ≤ j) :
      |centeredAbelPrefix k j*(w j-w (j+1))| ≤ M*(w j-w (j+1)) := by
    have hdec := sub_nonneg.mpr (hstep j hj)
    rw [abs_mul,abs_of_nonneg hdec]
    by_cases hy : (j:ℝ) ≤ Y
    · exact mul_le_mul_of_nonneg_right (hpoint j hj hy) hdec
    · rw [hzero j (lt_of_not_ge hy),hzero (j+1) ((lt_of_not_ge hy).trans_le
          (Nat.cast_le.mpr (Nat.le_succ j))),sub_self,mul_zero,mul_zero]
  have hsum : ∑ j ∈ Finset.Ico k L, |centeredAbelPrefix k j*(w j-w (j+1))| ≤ M*(w k-w L) := by
    induction L, hkL using Nat.le_induction with
    | base => simp
    | succ j hj ih =>
      rw [Finset.sum_Ico_succ_top hj]
      linarith only [add_le_add ih (hcost j hj)]
  have hend : |w L*centeredAbelPrefix k L| ≤ M*w L := by
    rw [abs_mul,abs_of_nonneg (hw L),mul_comm M]
    by_cases hy : (L:ℝ) ≤ Y
    · exact mul_le_mul_of_nonneg_left (hpoint L hkL hy) (hw L)
    · rw [hzero L (lt_of_not_ge hy),zero_mul,zero_mul]
  change |∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)*w n| ≤ M*(Y/k)
  rw [centeredAbelPrefix_by_parts w (le_refl k) hkL]
  have hkz : centeredAbelPrefix k k = 0 := by simp [centeredAbelPrefix]
  rw [hkz,mul_zero,sub_zero]
  apply (abs_add_le _ _).trans
  have hs := Finset.abs_sum_le_sum_abs
    (fun j => centeredAbelPrefix k j*(w j-w (j+1))) (Finset.Ico k L)
  linarith only [hs,hsum,hend,mul_le_mul_of_nonneg_left (Int.floor_le (Y/k)) hM]

/-- After the whole test, the signed discrepancy from the reciprocal term
gains the additional factor exp(T)/k. The bound is uniform in L. -/
theorem criticalState_signed_reciprocal_error {W₀ : ℝ} {F Φ : ℝ → ℝ}
    (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ) (he : F =ᵐ[volume] Φ)
    {d : ℝ} (hd : 0 < d) (hθ : zeroReSup < 1-d) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : ℝ) (k L : ℕ), 1 ≤ k → k ≤ L →
      let a := (∫ v, Φ v)*(∫ v, Real.exp (-v/2)*Φ v)
      let R := ∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)/(n:ℝ)
      |(∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n))-
        a*Real.exp (T/2)*R| ≤ D*Real.exp (T/2)*(k:ℝ)^(-d)*(Real.exp T/k) := by
  obtain ⟨C,hC,hfloor⟩ := signed_floor_band_bound hd hθ
  let m := ∫ v, Φ v
  let g := fun v : ℝ => Real.exp (v/2)*Φ v
  let h := fun v : ℝ => Real.exp (-v/2)*Φ v
  let q := fun v : ℝ => Real.exp (-(3*v)/2)*Φ v
  have htilt (s : ℝ) (hs : -4<s) : Integrable (fun v => Real.exp (s*v)*Φ v) := by
    apply (integrable_mul_exp_of_domain (criticalHalfLineEnergyDomain_of_groundState hF) hs).congr
    filter_upwards [he] with v hv
    rw [hv,mul_comm]
  have hg : Integrable g := by
    simpa only [g,show ∀ v : ℝ, (1/2)*v=v/2 by intro v; ring] using htilt (1/2) (by norm_num)
  have hh : Integrable h := by
    simpa only [h,show ∀ v : ℝ, (-1/2)*v= -v/2 by intro v; ring] using htilt (-1/2) (by norm_num)
  have hq : Integrable q := by
    simpa only [q,show ∀ v : ℝ, (-3/2)*v= -(3*v)/2 by intro v; ring] using htilt (-3/2) (by norm_num)
  let D := |m| *C*(∫ v, |q v|)
  have hQ : 0 ≤ ∫ v, |q v| := integral_nonneg fun _ => abs_nonneg _
  refine ⟨D,by dsimp only [D]; positivity,fun T k L hk hkL => ?_⟩
  let X := Real.exp T
  let Y := fun v : ℝ => X*Real.exp (-v)
  let c := fun n : ℕ => vonMangoldt n-1
  let I := Finset.Ioc k L
  let R := ∑ n ∈ I, c n/(n:ℝ)
  let f := fun (n : ℕ) (v : ℝ) => g v*Int.fract (Y v/n)
  let whole := ∑ n ∈ I, c n*testedIntegerWeight Φ T (Real.log n)
  have hY (v : ℝ) : 0 ≤ Y v := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hmeas (n : ℕ) : Measurable (fun v : ℝ => Y v/n) :=
    ((measurable_const.mul (Real.measurable_exp.comp measurable_neg)).div_const _)
  have hgm : Measurable g := (Real.measurable_exp.comp (measurable_id.div_const 2)).mul hc.measurable
  have hfi (n : ℕ) : Integrable (f n) := by
    apply hg.abs.mono' ((hgm.aestronglyMeasurable.mul
      (measurable_fract.comp (hmeas n)).aestronglyMeasurable)) (Eventually.of_forall fun v => ?_)
    change |g v*Int.fract (Y v/n)| ≤ |g v|
    rw [abs_mul,abs_of_nonneg (Int.fract_nonneg (Y v/n))]
    exact mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le
  have hread : Real.exp (T/2)*whole=m*(∫ v, ∑ n ∈ I, c n*f n v) := by
    dsimp only [whole]
    rw [integral_finsetSum I (fun n _ => (hfi n).const_mul (c n))]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : (0:ℝ)<n := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le k) (Finset.mem_Ioc.mp hn).1)
    have hz (v : ℝ) : Real.exp (T-Real.log n)*Real.exp (-v)=Y v/n := by
      rw [Real.exp_sub,Real.exp_log hn0]; dsimp only [Y,X]; ring
    have hr := scaled_testedIntegerWeight_eq_fractional_reading Φ T (Real.log n)
    simp_rw [hz] at hr
    rw [integral_const_mul]
    linear_combination c n*hr
  let diff := fun v : ℝ => (∑ n ∈ I, c n*f n v)-(X*R)*h v
  have hdiff : Integrable diff := (integrable_finsetSum I (fun n _ => (hfi n).const_mul (c n))).sub
    (hh.const_mul _)
  have hpolar (v : ℝ) : g v*Y v=X*h v := by
    have hx : Real.exp (v/2)*Real.exp (-v)=Real.exp (-v/2) := by rw [← Real.exp_add]; congr 1; ring
    dsimp only [g,h,Y]; linear_combination X*Φ v*hx
  have hid (v : ℝ) : diff v= -g v*(∑ n ∈ I, c n*(⌊Y v/(n:ℝ)⌋:ℝ)) := by
    have hp : ∑ n ∈ I, c n*f n v =
        g v*Y v*R-g v*(∑ n ∈ I, c n*(⌊Y v/(n:ℝ)⌋:ℝ)) := by
      dsimp only [R]; rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro n _; dsimp only [f]; rw [Int.fract]; ring
    dsimp only [diff]; rw [hp,hpolar]; ring
  let V := C*(k:ℝ)^(-d)*X*(X/k)
  have hV : 0 ≤ V := by dsimp only [V,X]; positivity
  have hmajor (v : ℝ) : |diff v| ≤ V*|q v| := by
    rw [hid,abs_mul,abs_neg]
    apply (mul_le_mul_of_nonneg_left (hfloor k L (Y v) hk hkL (hY v)) (abs_nonneg (g v))).trans_eq
    have hex : Real.exp (v/2)*Real.exp (-v)*Real.exp (-v)=Real.exp (-(3*v)/2) := by
      rw [← Real.exp_add,← Real.exp_add]; congr 1; ring
    dsimp only [g,q,V,Y]; rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]
    linear_combination C*(k:ℝ)^(-d)*X*(X/k)*|Φ v| *hex
  have hbound : |∫ v, diff v| ≤ V*(∫ v, |q v|) := by
    apply (show |∫ v, diff v| ≤ ∫ v, |diff v| by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm diff).trans
    rw [← integral_const_mul]
    exact integral_mono hdiff.abs (hq.abs.const_mul _) hmajor
  have hsplit : Real.exp (T/2)*(whole-(m*(∫ v, h v))*Real.exp (T/2)*R)=m*∫ v, diff v := by
    dsimp only [diff]
    rw [integral_sub (integrable_finsetSum I (fun n _ => (hfi n).const_mul (c n))) (hh.const_mul _),
      integral_const_mul,mul_sub,hread]
    have hX : Real.exp (T/2)*Real.exp (T/2)=X := by rw [← Real.exp_add]; congr 1; ring
    linear_combination -(m*(∫ v, h v)*R)*hX
  change |whole-(m*(∫ v, h v))*Real.exp (T/2)*R| ≤ D*Real.exp (T/2)*(k:ℝ)^(-d)*(X/k)
  apply le_of_mul_le_mul_left _ (Real.exp_pos (T/2))
  have hnorm := congrArg abs hsplit
  rw [abs_mul,abs_of_pos (Real.exp_pos (T/2)),abs_mul] at hnorm
  rw [hnorm]
  apply (mul_le_mul_of_nonneg_left hbound (abs_nonneg m)).trans_eq
  have hX : Real.exp (T/2)*Real.exp (T/2)=X := by rw [← Real.exp_add]; congr 1; ring
  dsimp only [V,D]; linear_combination -(|m| *C*(∫ v, |q v|)*(k:ℝ)^(-d)*(X/k))*hX

/-- Every fixed positive logarithmic separation absorbs the wall-strip cost. -/
private theorem separated_strip_cost {C η T v q : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    (hv : 0 ≤ v) (hmax : v ≤ 6*T) (hq : (1+η)*T ≤ q) :
    C*(v+1)*(Real.sqrt v+1)*Real.exp ((T+1-q)/2) ≤
      C*(24/η+2)^2*Real.exp (1/2) := by
  let z := Real.exp (η*T/4)
  have hz : 1+η*T/4 ≤ z := by simpa only [add_comm] using Real.add_one_le_exp (η*T/4)
  have hc : 0 ≤ 24/η+2 := by positivity
  have hlarge : v+2 ≤ (24/η+2)*z := by
    have h := mul_le_mul_of_nonneg_left hz hc
    have hscale : (24/η+2)*(1+η*T/4)=24/η+2+6*T+η*T/2 := by field_simp; ring
    rw [hscale] at h
    linarith only [h,hmax,div_nonneg (show 0 ≤ (24:ℝ) by norm_num) hη.le,
      mul_nonneg hη.le (show 0≤T by linarith only [hv,hmax])]
  have hroot : Real.sqrt v ≤ v+1 := by nlinarith only [Real.sq_sqrt hv,sq_nonneg (Real.sqrt v-1)]
  have hprod := mul_le_mul (show v+1 ≤ (24/η+2)*z by linarith only [hlarge])
    (show Real.sqrt v+1 ≤ (24/η+2)*z by linarith only [hroot,hlarge])
    (show 0 ≤ Real.sqrt v+1 by positivity) (mul_nonneg hc (Real.exp_pos _).le)
  have hex : z*z*Real.exp ((T+1-q)/2) ≤ Real.exp (1/2) := by
    dsimp only [z]; rw [← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
    linarith only [hq]
  calc _ ≤ C*(((24/η+2)*z)*((24/η+2)*z))*Real.exp ((T+1-q)/2) := by
             rw [mul_assoc C (v+1)]
             exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod hC) (Real.exp_pos _).le
       _ = C*(24/η+2)^2*(z*z*Real.exp ((T+1-q)/2)) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left hex (by positivity)

/-- At every real test time, the signed upper tail beyond any fixed positive
power separation has the reciprocal Chebyshev exponent. -/
theorem criticalState_upper_tail_at_power_separation {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (u : ℝ) (_ : 0 ≤ u), windowThreshold u)=(W₀:EReal))
    {F Φ : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (hc : Continuous Φ)
    (he : F =ᵐ[volume] Φ) {d η : ℝ} (hd : 0 < d) (hθ : zeroReSup < 1-d)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ D B : ℝ, 0 ≤ D ∧ 0 ≤ B ∧ ∀ T : ℝ, 1 ≤ T →
      |(∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T),
        criticalComplementBand Φ ⌈Real.exp ((1+η)*T)⌉₊ t*fractionalPrimeTest (T-t))|
        ≤ D+B*Real.exp ((1/2-(1+η)*d)*T) := by
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,⟨C,hC,hb⟩,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  let m := ∫ v, Φ v
  let a := m*(∫ v, Real.exp (-v/2)*Φ v)
  let S := C*(24/η+2)^2*Real.exp (1/2)
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hi := (criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he
  obtain ⟨A,hA,hcut⟩ := moving_upper_band_sub_whole hc hi hs hC hb
  obtain ⟨J,hJ,hfar⟩ := criticalState_upper_integer_tail hW ht hF hc he
  obtain ⟨B,hB,hrec⟩ := centered_reciprocal_prime_intervals_of_zeroReSup hd hθ
  obtain ⟨E,hE,hfloor⟩ := criticalState_signed_reciprocal_error hF hc he hd hθ
  let P := |m| *(2*A+4*S)
  refine ⟨P+J,E+|a| *B,by dsimp only [P]; positivity,by positivity,fun T hT => ?_⟩
  let k := ⌈Real.exp ((1+η)*T)⌉₊
  let L := ⌈Real.exp (5*T)⌉₊
  have hT0 := zero_le_one.trans hT
  have hscale : T ≤ (1+η)*T := by linarith only [mul_nonneg hη.le hT0]
  have hkx : Real.exp ((1+η)*T) ≤ k := Nat.le_ceil _
  have hLx : Real.exp (5*T) ≤ L := Nat.le_ceil _
  have hk : 1 ≤ k := by exact_mod_cast (Real.one_le_exp (hT0.trans hscale)).trans hkx
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk
  have hkL : k ≤ L := Nat.ceil_mono (Real.exp_le_exp.mpr
    (by linarith only [mul_le_mul_of_nonneg_right hη1 hT0,hT0]))
  have hL0 := hk0.trans_le (Nat.cast_le.mpr hkL)
  have hq := (Real.le_log_iff_exp_le hk0).mpr hkx
  have hLM : Real.log L ≤ 6*T := by
    apply (Real.log_le_iff_le_exp hL0).mpr
    have hround := Nat.ceil_lt_add_one (Real.exp_pos (5*T)).le
    have hex : 2 ≤ Real.exp T := by linarith only [hT,Real.add_one_le_exp T]
    calc (L:ℝ) ≤ Real.exp (5*T)+1 := hround.le
         _ ≤ Real.exp (5*T)*2 := by linarith only [Real.one_le_exp (by linarith only [hT] : 0≤5*T)]
         _ ≤ Real.exp (5*T)*Real.exp T := mul_le_mul_of_nonneg_left hex (Real.exp_pos _).le
         _ = Real.exp (6*T) := by rw [← Real.exp_add]; congr 1; ring
  let K := fun t => fractionalPrimeTest (T-t)
  let tail := fun j => m*(∫ t in Ioc (T/6) (6*T), criticalComplementBand Φ j t*K t)
  let mid := m*(∫ t in Ioc (T/6) (6*T), finiteCriticalComplementBand Φ k L t*K t)
  let whole := ∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)*testedIntegerWeight Φ T (Real.log n)
  let R := ∑ n ∈ Finset.Ioc k L, (vonMangoldt n-1)/(n:ℝ)
  have hsplit : tail k = mid+tail L := by
    dsimp only [tail,mid,K]
    rw [upper_band_integral_split hc hi hC hb hkL,mul_add]
  have hremote : |tail L| ≤ J := by
    have h := hfar (T/6) T (6*T) 0 L (by linarith only [hT]) (by linarith only [hT]) hT le_rfl
      (by rw [add_zero]; exact (Real.exp_le_exp.mpr (by linarith only [hT])).trans hLx)
    simpa only [neg_zero,zero_div,Real.exp_zero,mul_one] using h
  have hstrip : |mid-whole| ≤ P := by
    have h := hcut k L (T/6) (6*T) T hk hkL (by linarith only [hT]) hLM
    have hearly : Real.exp ((5*(T/6)-T)/2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith only [hT])
    have h1 := separated_strip_cost hC hη (Real.log_natCast_nonneg L) hLM hq
    have h2 := separated_strip_cost hC hη (Real.log_natCast_nonneg k)
      ((Real.log_le_log hk0 (Nat.cast_le.mpr hkL)).trans hLM) hq
    dsimp only [P,S]
    apply h.trans (mul_le_mul_of_nonneg_left _ (abs_nonneg _))
    linarith only [mul_le_mul_of_nonneg_left hearly (show 0≤2*A by positivity),h1,h2]
  let V := Real.exp (T/2)*(k:ℝ)^(-d)
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hcost : |whole-a*Real.exp (T/2)*R| ≤ E*V := by
    apply (hfloor T k L hk hkL).trans
    have hr : Real.exp T/(k:ℝ) ≤ 1 := (div_le_one hk0).mpr ((Real.exp_le_exp.mpr hscale).trans hkx)
    apply (mul_le_of_le_one_right (show 0≤E*Real.exp (T/2)*(k:ℝ)^(-d) by positivity) hr).trans_eq
    dsimp only [V]; ring
  have hmain : |a*Real.exp (T/2)*R| ≤ (|a| *B)*V := by
    rw [abs_mul,abs_mul,abs_of_pos (Real.exp_pos _)]
    apply (mul_le_mul_of_nonneg_left (hrec k L hk hkL) (by positivity : 0 ≤ |a| *Real.exp (T/2))).trans_eq
    dsimp only [V]; ring
  have hpow : V ≤ Real.exp ((1/2-(1+η)*d)*T) := by
    dsimp only [V]; rw [Real.rpow_def_of_pos hk0,← Real.exp_add,Real.exp_le_exp]
    linarith only [mul_le_mul_of_nonneg_right hq hd.le]
  change |tail k| ≤ _
  rw [hsplit]
  have hmid := abs_add_le (mid-whole) (whole-a*Real.exp (T/2)*R)
  have hwhole := abs_add_le (mid-a*Real.exp (T/2)*R) (a*Real.exp (T/2)*R)
  rw [sub_add_sub_cancel] at hmid
  rw [sub_add_cancel] at hwhole
  linarith only [abs_add_le mid (tail L),hmid,hwhole,hremote,hstrip,hcost,hmain,
    mul_le_mul_of_nonneg_left hpow (show 0 ≤ E+|a| *B by positivity)]

#print axioms signed_floor_band_bound
#print axioms criticalState_signed_reciprocal_error
#print axioms criticalState_upper_tail_at_power_separation
end GaloisForLFunctions.ExclusionOfTheCriticalState
