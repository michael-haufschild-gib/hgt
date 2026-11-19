import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.OddQuotientsInTheFractionalPrimeTest
import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheSquareChargeInsideTheDiagonalInterval

/-!
# An odd-quotient interval inside the ordinary-prime deficit

Translating each atom by its logarithmic abscissa makes the numerator of its
fractional weight common to all integers. The physical edge then cuts one
interval. The prime discrepancy of a single binary digit on this interval
retains the sign of the adverse contribution to the original test.
-/

noncomputable section
open scoped Classical
open Set MeasureTheory Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-- Integer abscissae in the original middle test at fixed state displacement. -/
def ordinaryBandAtDisplacement (k L : ℕ) (T v : ℝ) : Finset ℕ :=
  (Finset.Ioc k L).filter fun n => v+Real.log n ∈ Ioc (T/6) (6*T) ∧ pastCriticalEdge n (v+Real.log n)

private theorem coeff_eq (n : ℕ) :
    ordinaryPrimeExcessCoeff n = (if n.Prime then vonMangoldt n else 0)-1 := by
  unfold ordinaryPrimeExcessCoeff
  by_cases hp : n.Prime
  · rw [if_pos hp,if_pos hp,vonMangoldt_apply_prime hp]
  · rw [if_neg hp,if_neg hp]

private theorem edge_at_displacement {n : ℕ} (hn : 0<n) (v : ℝ) :
    let t := v+Real.log n
    pastCriticalEdge n t ↔ 1+Real.exp (-t/2)*Real.sqrt t < Real.exp (-v) := by
  let t := v+Real.log n
  have hn' : Real.exp t*Real.exp (-v)=(n:ℝ) := by
    rw [← Real.exp_add,show t+ -v=Real.log n by dsimp only [t]; ring,Real.exp_log (Nat.cast_pos.mpr hn)]
  have he : Real.exp t*Real.exp (-t/2)=Real.exp (t/2) := by rw [← Real.exp_add]; congr 1; ring
  change Real.exp t+Real.exp (t/2)*Real.sqrt t < (n:ℝ) ↔ _
  calc _ ↔ Real.exp t*(1+Real.exp (-t/2)*Real.sqrt t)<Real.exp t*Real.exp (-v) := by
             rw [hn',mul_add,mul_one,← mul_assoc,he]
       _ ↔ _ := mul_lt_mul_iff_right₀ (Real.exp_pos t)

private theorem relative_width_antitone {t u : ℝ} (ht : 1≤t) (htu : t≤u) :
    Real.exp (-u/2)*Real.sqrt u ≤ Real.exp (-t/2)*Real.sqrt t := by
  have ht0 : 0≤t := by linarith only [ht]
  have hsq : u ≤ t*Real.exp (u-t) := by
    have h := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (u-t)) ht0
    nlinarith only [h,mul_nonneg (sub_nonneg.mpr ht) (sub_nonneg.mpr htu)]
  have hs := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul ht0,← Real.exp_half] at hs
  have he : Real.exp (-u/2)*Real.exp ((u-t)/2)=Real.exp (-t/2) := by rw [← Real.exp_add]; congr 1; ring
  calc _ ≤ Real.exp (-u/2)*(Real.sqrt t*Real.exp ((u-t)/2)) :=
              mul_le_mul_of_nonneg_left hs (Real.exp_pos _).le
       _ = _ := by rw [← he]; ring

/-- For fixed displacement the relative wall width decreases with the log
center on the middle time interval. All surviving integer abscissae are consecutive. -/
private theorem active_interval {k L H : ℕ} {T v : ℝ} (hT : 6≤T)
    (hS : ((ordinaryBandAtDisplacement k L T v).filter fun n : ℕ => Real.sqrt H < n).Nonempty) :
    ∃ a b : ℕ, k<a ∧ a≤b ∧ b≤L ∧ Real.sqrt H<a ∧
      ((ordinaryBandAtDisplacement k L T v).filter fun n : ℕ => Real.sqrt H < n)=Finset.Icc a b := by
  let S := (ordinaryBandAtDisplacement k L T v).filter fun n : ℕ => Real.sqrt H < n
  let a := S.min' hS
  let b := S.max' hS
  have ha : a∈S := S.min'_mem hS
  have hb : b∈S := S.max'_mem hS
  have hmem (n : ℕ) : n∈S ↔ (k<n ∧ n≤L) ∧
      (v+Real.log n∈Ioc (T/6) (6*T) ∧ pastCriticalEdge n (v+Real.log n)) ∧ Real.sqrt H<n := by
    simp only [S,ordinaryBandAtDisplacement,Finset.mem_filter,Finset.mem_Ioc,and_assoc]
  obtain ⟨hak,hat,hroot⟩ := (hmem _).mp ha
  obtain ⟨hbL,hbt,_⟩ := (hmem _).mp hb
  refine ⟨a,b,hak.1,S.le_max' _ ha,hbL.2,hroot,Finset.ext fun n => ?_⟩
  rw [Finset.mem_Icc]
  constructor
  · intro h; exact ⟨S.min'_le _ h,S.le_max' _ h⟩
  · rintro ⟨han,hnb⟩
    have ha0 : 0<a := Nat.zero_lt_of_lt hak.1
    have hn0 : 0<n := ha0.trans_le han
    have h₁ := Real.log_le_log (Nat.cast_pos.mpr ha0) (Nat.cast_le.mpr han)
    have h₂ := Real.log_le_log (Nat.cast_pos.mpr hn0) (Nat.cast_le.mpr hnb)
    have hwidth := relative_width_antitone (t := v+Real.log a) (u := v+Real.log n)
      (by linarith only [hat.1.1,hT]) (by linarith only [h₁])
    refine (hmem _).mpr ⟨⟨hak.1.trans_le han,hnb.trans hbL.2⟩,
      ⟨⟨by linarith only [hat.1.1,h₁],by linarith only [hbt.1.2,h₂]⟩,
        (edge_at_displacement hn0 v).mpr ?_⟩,hroot.trans_le (Nat.cast_le.mpr han)⟩
    linarith only [hwidth,(edge_at_displacement ha0 v).mp hat.2]

private theorem band_integral_at_displacement {Φ : ℝ → ℝ} (hi : Integrable Φ)
    (k L : ℕ) (T : ℝ) :
    let G := fun v => Φ v*(fractionalPrimeExcess (ordinaryBandAtDisplacement k L T v) (Real.exp (T-v)) /
      Real.sqrt (Real.exp (T-v)))
    Integrable G ∧ (∫ t in Ioc (T/6) (6*T), ordinaryPrimeComplementBand Φ k L t*fractionalPrimeTest (T-t)) =
      ∫ v, G v := by
  let A := Ioc (T/6) (6*T)
  let I := Finset.Ioc k L
  let E := fun n : ℕ => A ∩ {t : ℝ | pastCriticalEdge n t}
  let f := fun (n : ℕ) => (E n).indicator (fun t => ordinaryPrimeExcessCoeff n*continuousIntegerAtom Φ n t*
    fractionalPrimeTest (T-t))
  have hf (n : ℕ) : Integrable (f n) := by
    have hE : MeasurableSet (E n) := measurableSet_Ioc.inter (measurableSet_lt
      (by fun_prop : Measurable fun t : ℝ => Real.exp t+Real.exp (t/2)*Real.sqrt t) measurable_const)
    have h := ((hi.comp_sub_right (Real.log n)).const_mul (Real.sqrt n)⁻¹).const_mul (ordinaryPrimeExcessCoeff n)
    have hK := measurable_fractionalPrimeTest.comp (show Measurable (fun t : ℝ => T-t) from measurable_const.sub measurable_id)
    apply Integrable.indicator _ hE
    apply h.abs.mono' (h.aestronglyMeasurable.mul hK.aestronglyMeasurable)
    apply Eventually.of_forall
    intro t
    change |ordinaryPrimeExcessCoeff n*continuousIntegerAtom Φ n t * fractionalPrimeTest (T-t)| ≤ _
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (fractionalPrimeTest_bounds _).1
  have hrow (t : ℝ) : (∑ n ∈ I, f n t)= A.indicator (fun u => ordinaryPrimeComplementBand Φ k L u*
      fractionalPrimeTest (T-u)) t := by
    by_cases h : t∈A
    · rw [indicator_of_mem h,ordinaryPrimeComplementBand,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n _
      by_cases he : pastCriticalEdge n t
      · rw [if_pos he,show f n t=_ from indicator_of_mem (show t∈E n from ⟨h,he⟩) _,coeff_eq]
      · rw [if_neg he,zero_mul]; exact indicator_of_notMem (fun hm : t∈E n => he hm.2) _
    · rw [indicator_of_notMem h]
      exact Finset.sum_eq_zero fun n _ => indicator_of_notMem (fun hm : t∈E n => h hm.1) _
  let p := fun (n : ℕ) (v : ℝ) => f n (v+Real.log n)
  have hp (n : ℕ) : Integrable (p n) := (hf n).comp_add_right _
  have hread (v : ℝ) : (∑ n ∈ I, p n v)=Φ v*(fractionalPrimeExcess (ordinaryBandAtDisplacement k L T v)
      (Real.exp (T-v))/Real.sqrt (Real.exp (T-v))) := by
    rw [fractionalPrimeExcess,ordinaryBandAtDisplacement,Finset.sum_filter,Finset.sum_div,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have hn0 : 0<(n:ℝ) := Nat.cast_pos.mpr (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1)
    let t := v+Real.log n
    by_cases hm : t ∈ E n
    · rw [if_pos (show v+Real.log n∈A ∧ pastCriticalEdge n (v+Real.log n) from hm)]
      change (E n).indicator _ t=_
      rw [indicator_of_mem hm]
      have hphase : Real.exp (T-t)=Real.exp (T-v)/n := by
        rw [show T-t=(T-v)-Real.log n by dsimp only [t]; ring,Real.exp_sub,Real.exp_log hn0]
      have hroot : (Real.sqrt n)⁻¹=Real.exp (-(Real.log n)/2) := by
        rw [neg_div,Real.exp_neg,Real.exp_half,Real.exp_log hn0]
      have hscale : (Real.sqrt n)⁻¹*Real.exp (-(T-t)/2)=(Real.sqrt (Real.exp (T-v)))⁻¹ := by
        rw [hroot,← Real.exp_add,← Real.exp_half,← Real.exp_neg]
        congr 1; dsimp only [t]; ring
      dsimp only [continuousIntegerAtom,fractionalPrimeTest]
      rw [show t-Real.log n=v by dsimp only [t]; ring,hphase]
      linear_combination ordinaryPrimeExcessCoeff n*Φ v*Int.fract (Real.exp (T-v)/n)*hscale
    · rw [if_neg (show ¬(v+Real.log n∈A ∧ pastCriticalEdge n (v+Real.log n)) from hm),zero_div,mul_zero]
      exact indicator_of_notMem hm _
  have hpint := integrable_finsetSum I (fun n _ => hp n)
  refine ⟨hpint.congr (Eventually.of_forall hread),?_⟩
  rw [← integral_indicator measurableSet_Ioc]
  calc _ = ∫ t, ∑ n ∈ I, f n t := integral_congr_ae (Eventually.of_forall fun t => (hrow t).symm)
       _ = ∑ n ∈ I, ∫ t, f n t := integral_finsetSum _ (fun n _ => hf n)
       _ = ∑ n ∈ I, ∫ v, p n v := Finset.sum_congr rfl fun n _ => (integral_add_right_eq_self (f n) (Real.log n)).symm
       _ = ∫ v, ∑ n ∈ I, p n v := (integral_finsetSum _ (fun n _ => hp n)).symm
       _ = _ := integral_congr_ae (Eventually.of_forall hread)

/-- For even H this factorial ratio is the central binomial coefficient. -/
def halfFactorialQuotient (H : ℕ) : ℕ :=
  H.factorial/((H/2).factorial*(H/2).factorial)

private theorem halves_dvd (H : ℕ) : (H/2).factorial*(H/2).factorial ∣ H.factorial :=
  (Nat.factorial_mul_factorial_dvd_factorial_add _ _).trans (Nat.factorial_dvd_factorial (by omega))

/-- Above the square root, the prime valuation of the factorial ratio
is exactly the parity of the quotient, also for odd numerators. -/
theorem halfFactorialQuotient_valuation {H p : ℕ} (hp : p.Prime) (h : H<p^2) :
    (halfFactorialQuotient H).factorization p = H/p%2 := by
  have hleg (n : ℕ) (hn : n<p^2) : n.factorial.factorization p=n/p := by
    have hlog : Nat.log p n<2 := by
      rcases Nat.eq_zero_or_pos n with rfl|hpos
      · simp
      · exact Nat.log_lt_of_lt_pow hpos.ne' hn
    rw [Nat.factorization_factorial hp hlog]
    simp only [show Finset.Ico 1 2 = {1} by decide,Finset.sum_singleton,pow_one]
  rw [halfFactorialQuotient,Nat.factorization_div (halves_dvd H),Finsupp.coe_tsub,Pi.sub_apply,
    Nat.factorization_mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _),Finsupp.coe_add,Pi.add_apply,
    hleg H h,hleg (H/2) ((Nat.div_le_self _ _).trans_lt h)]
  have he : H/2/p=H/p/2 := by rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,mul_comm 2 p]
  rw [he]; omega

/-- The odd-quotient discrepancy is the logarithmic mass of prime divisors
of one explicit integer minus the count of all selected reference atoms. -/
theorem oddQuotientPrimeExcess_eq_factorial_divisors (S : Finset ℕ) (H : ℕ)
    (hs : ∀ p ∈ S, Real.sqrt H < p) :
    oddQuotientPrimeExcess S H =
      (∑ p ∈ S with p.Prime ∧ p ∣ halfFactorialQuotient H, Real.log p) -
      ((S.filter fun n => H/n%2=1).card:ℝ) := by
  have hpos : halfFactorialQuotient H ≠ 0 := by
    intro hz
    have h := Nat.div_mul_cancel (halves_dvd H)
    change halfFactorialQuotient H * _ = _ at h
    rw [hz,zero_mul] at h
    exact (Nat.factorial_ne_zero H) h.symm
  have hcard : ((S.filter fun n => H/n%2=1).card:ℝ) =
      ∑ n ∈ S, if H/n%2=1 then (1:ℝ) else 0 := by
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [oddQuotientPrimeExcess,hcard,Finset.sum_filter,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hm
  by_cases hp : p.Prime
  · have hlt : (H:ℝ) < (p:ℝ)^2 := (Real.sqrt_lt' (by positivity : (0:ℝ)<p)).mp (hs p hm)
    have hf := halfFactorialQuotient_valuation hp (by exact_mod_cast hlt : H<p^2)
    have hd : p ∣ halfFactorialQuotient H ↔ H/p%2=1 := by
      constructor
      · intro h
        have h1 := hp.factorization_pos_of_dvd hpos h
        rw [hf] at h1
        omega
      · intro h
        by_contra hn
        rw [Nat.factorization_eq_zero_of_not_dvd hn,h] at hf
        omega
    by_cases h : H/p%2=1 <;> simp [ordinaryPrimeExcessCoeff,hp,hd,h]
  · by_cases h : H/p%2=1 <;> simp [ordinaryPrimeExcessCoeff,hp,h]

private def deficitReading (Φ : ℝ → ℝ) (T : ℝ) (k L : ℕ) : ℝ :=
  (∫ v, Φ v)*(∫ t in Ioc (T/6) (6*T), ordinaryPrimeComplementBand Φ k L t*fractionalPrimeTest (T-t))

private theorem extract_quotient {Φ : ℝ → ℝ} (hi : Integrable Φ) (hs : ∀ v, 0≤v → Φ v=0)
    {T B : ℝ} (hT : 6≤T) (hB : 1+Real.log 4 ≤ B) (k L : ℕ)
    (hloss : deficitReading Φ T k L < -8*B*(|∫ v, Φ v| *(∫ v, |Φ v|))) :
    ∃ (v s : ℝ) (j H a b : ℕ), v≤0 ∧ (s=1 ∨ s= -1) ∧ s*(∫ u, Φ u)*Φ v<0 ∧
      H=⌊(2:ℝ)^(j+1)*Real.exp (T-v)⌋₊ ∧ Real.exp T≤H ∧
      k<a ∧ a≤b ∧ b≤L ∧ Real.sqrt H<a ∧
      ((ordinaryBandAtDisplacement k L T v).filter fun n : ℕ => Real.sqrt H < n)=Finset.Icc a b ∧
      B*Real.sqrt H < s*oddQuotientPrimeExcess (Finset.Icc a b) H := by
  let m := ∫ v, Φ v
  let Y := fun v : ℝ => Real.exp (T-v)
  let S := ordinaryBandAtDisplacement k L T
  let G := fun v => Φ v*(fractionalPrimeExcess (S v) (Y v)/Real.sqrt (Y v))
  obtain ⟨hGi,hread⟩ := band_integral_at_displacement hi k L T
  have hex : ∃ v, m*G v < (-8*B*|m|)*|Φ v| := by
    by_contra! h
    have hle := integral_mono (hi.abs.const_mul (-8*B*|m|)) (hGi.const_mul m) h
    rw [integral_const_mul,integral_const_mul] at hle
    change m*_ < _ at hloss
    rw [hread] at hloss
    change -8*B*|m| *(∫ v, |Φ v|) ≤ m*∫ v, G v at hle
    linarith only [hle,hloss]
  obtain ⟨v,hv⟩ := hex
  let d := m*Φ v
  let y := Y v
  let s : ℝ := if d<0 then 1 else -1
  have hd : d≠0 := by
    intro h
    change m*Φ v=0 at h
    change m*(Φ v*_) < _ at hv
    rw [← mul_assoc,show m*Φ v=0 from h,zero_mul] at hv
    have he : |m| *|Φ v|=0 := by rw [← abs_mul,h,abs_zero]
    linarith only [hv,congrArg ((-8*B)*·) he]
  have hv₀ : v≤0 := le_of_not_gt fun h => hd (by dsimp only [d]; rw [hs _ h.le,mul_zero])
  have hsign : s=1 ∨ s= -1 := by by_cases h : d<0 <;> simp [s,h]
  have hds : d = -|d| *s := by
    rcases lt_or_gt_of_ne hd with h | h
    · rw [show s=1 from if_pos h,abs_of_neg h]; ring
    · rw [show s= -1 from if_neg h.not_gt,abs_of_pos h]; ring
  have horient : s*m*Φ v<0 := by
    rw [mul_assoc,show m*Φ v=d from rfl]
    rcases hsign with h | h <;> rw [h] at hds ⊢ <;> linarith only [hds,abs_pos.mpr hd]
  have hy : 0<y := Real.exp_pos _
  have hbpos : 0<B := (by positivity : 0<1+Real.log 4).trans_le hB
  have hbig : 4*(2*B)*Real.sqrt y < s*fractionalPrimeExcess (S v) y := by
    have h : d*(fractionalPrimeExcess (S v) y/Real.sqrt y) < -8*B*|d| := by
      dsimp only [G] at hv
      rw [← mul_assoc] at hv
      simpa only [d,abs_mul,mul_assoc] using hv
    have heq := congrArg (· *(fractionalPrimeExcess (S v) y/Real.sqrt y)) hds
    have hh : 8*B < s*(fractionalPrimeExcess (S v) y/Real.sqrt y) := by
      apply (mul_lt_mul_iff_right₀ (abs_pos.mpr hd)).mp
      linarith only [h,heq]
    rw [← mul_div_assoc,lt_div_iff₀ (Real.sqrt_pos.mpr hy)] at hh
    linarith only [hh]
  obtain ⟨j,hj⟩ := exists_large_oddQuotientPrimeExcess (S v) hy (mul_pos (by norm_num) hbpos) hbig
  let z := (2:ℝ)^(j+1)*y
  let H := ⌊z⌋₊
  let Q := (S v).filter fun n : ℕ => Real.sqrt H < n
  have hzy : 2*y ≤ z := by
    have hp : 1≤(2:ℝ)^j := one_le_pow₀ (by norm_num)
    dsimp only [z]; rw [pow_succ]; nlinarith only [mul_le_mul_of_nonneg_right hp hy.le]
  have hyX : Real.exp T≤y := Real.exp_le_exp.mpr (by linarith only [hv₀])
  have hX : 1≤Real.exp T := Real.one_le_exp (by linarith only [hT])
  have hHX : Real.exp T ≤ (H:ℝ) := by linarith only [Nat.lt_floor_add_one z,hzy,hyX,hX]
  have hH : Real.sqrt H ≤ Real.sqrt z := Real.sqrt_le_sqrt (Nat.floor_le (by positivity : 0≤z))
  have hcost := oddQuotientPrimeExcess_sqrt_cost (S v) (fun n hn =>
    Nat.zero_lt_of_lt (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1) H
  change |oddQuotientPrimeExcess (S v) H-oddQuotientPrimeExcess Q H| ≤ _ at hcost
  have hsg : |s|=1 := hsign.elim (fun h => by rw [h,abs_one]) (fun h => by rw [h,abs_neg,abs_one])
  have hdiff : s*(oddQuotientPrimeExcess (S v) H-oddQuotientPrimeExcess Q H) ≤ B*Real.sqrt H := by
    apply (le_abs_self _).trans; rw [abs_mul,hsg,one_mul]
    exact hcost.trans (mul_le_mul_of_nonneg_right hB (Real.sqrt_nonneg _))
  change 2*B*Real.sqrt z < s*oddQuotientPrimeExcess (S v) H at hj
  have hlarge : B*Real.sqrt H < s*oddQuotientPrimeExcess Q H := by
    linarith only [hj,hdiff,mul_le_mul_of_nonneg_left hH hbpos.le]
  have hne : Q.Nonempty := by
    by_contra! h
    rw [h,oddQuotientPrimeExcess,Finset.sum_empty,mul_zero] at hlarge
    exact (not_lt_of_ge (mul_nonneg hbpos.le (Real.sqrt_nonneg _))) hlarge
  obtain ⟨a,b,ha,hab,hb,hr,hQ⟩ := active_interval hT hne
  exact ⟨v,s,j,H,a,b,hv₀,hsign,horient,rfl,hHX,ha,hab,hb,hr,hQ,hQ ▸ hlarge⟩

private theorem numerator_power_at_test {H a L : ℕ} {T η g : ℝ} (hT : 6≤T) (hη : η≤1)
    (hg : 0<g) (hH : Real.exp T ≤ H) (ha : Real.sqrt H < a) (hL : a ≤ L)
    (he : L=⌈Real.exp ((1+η)*T)⌉₊) : (H:ℝ)^(g/6) ≤ Real.exp (g*T) := by
  have ht : 0≤T := by linarith only [hT]
  have h₂ : 1 ≤ Real.exp (2*T) := Real.one_le_exp (by positivity)
  have h₁ : 2 ≤ Real.exp T := by linarith only [Real.add_one_le_exp T,hT]
  have hceil := Nat.ceil_lt_add_one (Real.exp_pos ((1+η)*T)).le
  have hex : Real.exp ((1+η)*T) ≤ Real.exp (2*T) := Real.exp_le_exp.mpr (by
    linarith only [mul_le_mul_of_nonneg_right hη ht])
  have hh : Real.sqrt H ≤ Real.exp (3*T) := by
    rw [show 3*T=2*T+T by ring,Real.exp_add]
    have hn : (L:ℝ) < Real.exp ((1+η)*T)+1 := he ▸ hceil
    linarith only [ha,(show (a:ℝ)≤L by exact_mod_cast hL),hn,hex,h₂,
      mul_le_mul_of_nonneg_left h₁ (Real.exp_pos (2*T)).le]
  have hl : (H:ℝ) ≤ Real.exp (6*T) := by
    rw [show 6*T=3*T+3*T by ring,Real.exp_add,← sq]
    calc (H:ℝ) = (Real.sqrt H)^2 := (Real.sq_sqrt (Nat.cast_nonneg H)).symm
         _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) hh 2
  have hp := (Real.exp_pos T).trans_le hH
  rw [Real.rpow_def_of_pos hp,Real.exp_le_exp]
  linarith only [mul_le_mul_of_nonneg_right ((Real.log_le_iff_le_exp hp).mpr hl) hg.le]

/-- At the same late tests as the exterior gain, a single ordinary-prime
discrepancy on integers with odd quotient exceeds the square root of its
integer numerator by a power of the test scale. Every integer in the interval
is strictly above that square root. The orientation is opposite the state
at the displacement producing this digit. -/
theorem riemannHypothesis_or_odd_quotient_prime_deficit : RiemannHypothesis ∨
    ∃ (W : ℝ) (F Φ : ℝ → ℝ) (c g : ℝ), 0<W ∧
      (⨅ (a : ℝ) (_ : 0≤a), windowThreshold a)=(W:EReal) ∧ IsCriticalHalfLineGroundState W F ∧
      Continuous Φ ∧ F =ᵐ[volume] Φ ∧ 0<c ∧ 0<g ∧ ∀ η : ℝ, 0<η → η≤1 →
      ∃ (T : ℕ → ℝ) (k : ℕ → ℕ), Tendsto T atTop atTop ∧
        (∀ i, T i/(1+η) ≤ Real.log (k i) ∧ Real.log (k i) ≤ T i) ∧
        let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
        let m := ∫ v, Φ v
        (∀ i, c*Real.exp (g*T i) ≤ m*(∫ t in Ioc (T i/6) (6*T i),
          criticalComplementBand Φ 0 t*fractionalPrimeTest (T i-t)) -
          m*(∫ t in Ioc (T i/6) (6*T i),
          finiteCriticalComplementBand Φ (k i) (L i) t*fractionalPrimeTest (T i-t))) ∧
        ∀ᶠ i in atTop, ∃ (v s : ℝ) (j H a b : ℕ), v≤0 ∧ (s=1 ∨ s= -1) ∧ s*m*Φ v<0 ∧
          H=⌊(2:ℝ)^(j+1)*Real.exp (T i-v)⌋₊ ∧ Real.exp (T i)≤H ∧
          (H:ℝ)^(g/6) ≤ Real.exp (g*T i) ∧ k i<a ∧ a≤b ∧ b≤L i ∧ Real.sqrt H<a ∧
          ((ordinaryBandAtDisplacement (k i) (L i) (T i) v).filter fun n : ℕ => Real.sqrt H < n)=Finset.Icc a b ∧
          c*Real.exp (g*T i)*Real.sqrt H <
            s*((∑ p ∈ Finset.Icc a b with p.Prime ∧ p ∣ halfFactorialQuotient H, Real.log p) -
              (((Finset.Icc a b).filter fun n => H/n%2=1).card:ℝ)) := by
  rcases riemannHypothesis_or_ordinary_prime_diagonal_band with hr | ⟨W,F,Φ,A,g,hW,ht,hF,hc,he,hA,hg,h⟩
  · exact Or.inl hr
  obtain ⟨_,_,Ψ,hΨ,heΨ,hs,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have heq := (Continuous.ae_eq_iff_eq volume hΨ hc).mp (heΨ.symm.trans he)
  subst Ψ
  let m := ∫ v, Φ v
  let M := |m| *(∫ v, |Φ v|)
  let c := A/(16*(M+1))
  have hM : 0≤M := mul_nonneg (abs_nonneg _) (integral_nonneg fun _ => abs_nonneg _)
  have hden : 0 < 16*(M+1) := by positivity
  have hc₀ : 0<c := div_pos hA hden
  have hAc : c*(16*(M+1))=A := div_mul_cancel₀ _ hden.ne'
  have hcA : c≤A := by linarith only [hAc,mul_nonneg hc₀.le hM,hc₀]
  refine Or.inr ⟨W,F,Φ,c,g,hW,ht,hF,hc,he,hc₀,hg,fun η hη hη1 => ?_⟩
  obtain ⟨T,k,hT,hk,hgain,_,_,hdef⟩ := h η hη hη1
  let L := fun i => ⌈Real.exp ((1+η)*T i)⌉₊
  have hdiv := Real.tendsto_exp_atTop.comp (hT.const_mul_atTop hg)
  have hprice := hdiv.const_mul_atTop hc₀
  have hmargin := hdiv.const_mul_atTop (show 0<A/2 by positivity)
  refine ⟨T,k,hT,hk,fun i => (mul_le_mul_of_nonneg_right hcA (Real.exp_pos _).le).trans (hgain i),?_⟩
  filter_upwards [hT.eventually_ge_atTop 6,hprice.eventually_ge_atTop (1+Real.log 4),
    hmargin.eventually_gt_atTop ((riemannZeta (1/2)).re*m^2+1),hdef 1 (by norm_num)] with i hlate hB hpos hd
  have hloss : deficitReading Φ (T i) (k i) (L i) < -8*(c*Real.exp (g*T i))*M := by
    change deficitReading Φ (T i) (k i) (L i) ≤ (riemannZeta (1/2)).re*m^2-A*Real.exp (g*T i)+1 at hd
    change (A/2)*Real.exp (g*T i) > _ at hpos
    change deficitReading Φ (T i) (k i) (L i) < -8*(c*Real.exp (g*T i))*M
    linarith only [hd,hpos,congrArg (· * Real.exp (g*T i)) hAc,
      mul_nonneg hc₀.le (Real.exp_pos (g*T i)).le]
  obtain ⟨v,s,j,H,a,b,hv,hsg,hor,hj,hX,ha,hab,hb,hsq,hcell,hlarge⟩ :=
    extract_quotient ((criticalHalfLineEnergyDomain_of_groundState hF).integrable.congr he) hs hlate hB _ _ hloss
  refine ⟨v,s,j,H,a,b,hv,hsg,hor,hj,hX,
    numerator_power_at_test hlate hη1 hg hX hsq (hab.trans hb) rfl,ha,hab,hb,hsq,hcell,?_⟩
  rw [← oddQuotientPrimeExcess_eq_factorial_divisors _ _ (fun n hn =>
    hsq.trans_le (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).1))]
  exact hlarge

#print axioms halfFactorialQuotient_valuation
#print axioms oddQuotientPrimeExcess_eq_factorial_divisors
#print axioms riemannHypothesis_or_odd_quotient_prime_deficit
end GaloisForLFunctions.ExclusionOfTheCriticalState
