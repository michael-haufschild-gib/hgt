import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.TheDisplacementIntegralOfAnOrdinaryPrimeBand

/-!
# State-oriented quotient intervals in a restricted prime test

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
def ordinaryTestDisplacementSupport (k L : ℕ) (T v : ℝ) : Finset ℕ :=
  (Finset.Ioc k L).filter fun n => v+Real.log n ∈ Ioc (T/6) (6*T) ∧ pastCriticalEdge n (v+Real.log n)

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
    (hS : ((ordinaryTestDisplacementSupport k L T v).filter fun n : ℕ => Real.sqrt H < n).Nonempty) :
    ∃ a b : ℕ, k<a ∧ a≤b ∧ b≤L ∧ Real.sqrt H<a ∧
      ((ordinaryTestDisplacementSupport k L T v).filter fun n : ℕ => Real.sqrt H < n)=Finset.Icc a b := by
  let S := (ordinaryTestDisplacementSupport k L T v).filter fun n : ℕ => Real.sqrt H < n
  let a := S.min' hS
  let b := S.max' hS
  have ha : a∈S := S.min'_mem hS
  have hb : b∈S := S.max'_mem hS
  have hmem (n : ℕ) : n∈S ↔ (k<n ∧ n≤L) ∧
      (v+Real.log n∈Ioc (T/6) (6*T) ∧ pastCriticalEdge n (v+Real.log n)) ∧ Real.sqrt H<n := by
    simp only [S,ordinaryTestDisplacementSupport,Finset.mem_filter,Finset.mem_Ioc,and_assoc]
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
        (pastCriticalEdge_at_displacement hn0 v).mpr ?_⟩,hroot.trans_le (Nat.cast_le.mpr han)⟩
    linarith only [hwidth,(pastCriticalEdge_at_displacement ha0 v).mp hat.2]

private theorem band_integral_at_displacement {Φ : ℝ → ℝ} (hi : Integrable Φ)
    (k L : ℕ) (T : ℝ) :
    let G := fun v => Φ v*(fractionalPrimeExcess (ordinaryTestDisplacementSupport k L T v) (Real.exp (T-v)) /
      Real.sqrt (Real.exp (T-v)))
    Integrable G ∧ (∫ t in Ioc (T/6) (6*T), ordinaryPrimeComplementBand Φ k L t*fractionalPrimeTest (T-t)) =
      ∫ v, G v := by
  have hs (v : ℝ) : ordinaryIndicesAt k L (Ioc (T/6) (6*T)) v=ordinaryTestDisplacementSupport k L T v := by
    ext n
    simp only [ordinaryIndicesAt,ordinaryTestDisplacementSupport,Finset.mem_filter]
  simpa only [hs] using ordinaryBand_displacement_integral hi k L T (Ioc (T/6) (6*T)) measurableSet_Ioc

/-- An adverse displacement selects its own numerator, sign and entire interior interval. -/
def HasOrientedQuotientWitness (Φ : ℝ → ℝ) (m T B : ℝ) (k L : ℕ) (v : ℝ) : Prop :=
    ∃ (s : ℝ) (j H a b : ℕ), v≤0 ∧ (s=1 ∨ s= -1) ∧ s*m*Φ v<0 ∧
      H=⌊(2:ℝ)^(j+1)*Real.exp (T-v)⌋₊ ∧ Real.exp T≤H ∧
      k<a ∧ a≤b ∧ b≤L ∧ Real.sqrt H<a ∧
      ((ordinaryTestDisplacementSupport k L T v).filter fun n : ℕ => Real.sqrt H < n)=Finset.Icc a b ∧
      B*Real.sqrt H < s*oddQuotientPrimeExcess (Finset.Icc a b) H

private def fractionalRow (k L : ℕ) (T v : ℝ) : ℝ :=
  fractionalPrimeExcess (ordinaryTestDisplacementSupport k L T v) (Real.exp (T-v))/Real.sqrt (Real.exp (T-v))

private theorem witness_at_displacement {Φ : ℝ → ℝ} (hs : ∀ v, 0≤v → Φ v=0)
    {T B : ℝ} (hT : 6≤T) (hB : 1+Real.log 4 ≤ B) (k L : ℕ) (m v : ℝ)
    (hv : m*(Φ v*fractionalRow k L T v) < (-8*B*|m|)*|Φ v|) :
    HasOrientedQuotientWitness Φ m T B k L v := by
  let Y := fun v : ℝ => Real.exp (T-v)
  let S := ordinaryTestDisplacementSupport k L T
  let G := fun v => Φ v*(fractionalPrimeExcess (S v) (Y v)/Real.sqrt (Y v))
  change m*G v < _ at hv
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
  exact ⟨s,j,H,a,b,hv₀,hsign,horient,rfl,hHX,ha,hab,hb,hr,hQ,hQ ▸ hlarge⟩

/-- A signed reading with any fixed outer multiplier selects an adverse
odd-quotient interval. The multiplier is retained when the profile is restricted. -/
theorem exists_oriented_quotient_interval {Φ : ℝ → ℝ} (hi : Integrable Φ) (hs : ∀ v, 0≤v → Φ v=0)
    {T B : ℝ} (hT : 6≤T) (hB : 1+Real.log 4 ≤ B) (k L : ℕ) (m : ℝ)
    (hloss : m*(∫ t in Ioc (T/6) (6*T), ordinaryPrimeComplementBand Φ k L t*fractionalPrimeTest (T-t))
      < -8*B*(|m| *(∫ v, |Φ v|))) :
    ∃ (v s : ℝ) (j H a b : ℕ), v≤0 ∧ (s=1 ∨ s= -1) ∧ s*m*Φ v<0 ∧
      H=⌊(2:ℝ)^(j+1)*Real.exp (T-v)⌋₊ ∧ Real.exp T≤H ∧
      k<a ∧ a≤b ∧ b≤L ∧ Real.sqrt H<a ∧
      ((ordinaryTestDisplacementSupport k L T v).filter fun n : ℕ => Real.sqrt H < n)=Finset.Icc a b ∧
      B*Real.sqrt H < s*oddQuotientPrimeExcess (Finset.Icc a b) H := by
  let Y := fun v : ℝ => Real.exp (T-v)
  let S := ordinaryTestDisplacementSupport k L T
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
  exact ⟨v,witness_at_displacement hs hT hB k L m v hv⟩

private theorem measurable_fractionalRow (k L : ℕ) (T : ℝ) : Measurable (fractionalRow k L T) := by
  have hactive (n : ℕ) : MeasurableSet {v : ℝ | v+Real.log n ∈ Ioc (T/6) (6*T) ∧
      pastCriticalEdge n (v+Real.log n)} := by
    apply (measurableSet_Ioc.preimage (measurable_id.add_const (Real.log n))).inter
    change MeasurableSet {v : ℝ | Real.exp (v+Real.log n)+Real.exp ((v+Real.log n)/2)*Real.sqrt (v+Real.log n)<n}
    exact measurableSet_lt (by fun_prop) measurable_const
  unfold fractionalRow fractionalPrimeExcess ordinaryTestDisplacementSupport
  simp_rw [Finset.sum_filter]
  refine Measurable.div ?_ (by fun_prop : Measurable fun v : ℝ => Real.sqrt (Real.exp (T-v)))
  apply Finset.measurable_sum
  intro n _
  exact Measurable.ite (hactive n) (measurable_const.mul
    (measurable_fract.comp (by fun_prop : Measurable fun v : ℝ => Real.exp (T-v)/n))) measurable_const

/-- All displacements in the exceptional set select an oriented numerator.
The signed response on the complement is bounded below by minus the threshold
times the state mass, with the original outer multiplier. -/
theorem exists_oriented_quotient_displacements {Φ : ℝ → ℝ} (hi : Integrable Φ) (hc : Continuous Φ)
    (hs : ∀ v, 0≤v → Φ v=0) {T B : ℝ} (hT : 6≤T) (hB : 1+Real.log 4 ≤ B)
    (k L : ℕ) (m : ℝ) :
    ∃ E : Set ℝ, MeasurableSet E ∧ (∀ v ∈ E, HasOrientedQuotientWitness Φ m T B k L v) ∧
      -8*B*(|m| *(∫ v, |Φ v|)) ≤ m*(∫ t in Ioc (T/6) (6*T),
        ordinaryPrimeComplementBand (Eᶜ.indicator Φ) k L t*fractionalPrimeTest (T-t)) := by
  let E := {v : ℝ | m*(Φ v*fractionalRow k L T v) < (-8*B*|m|)*|Φ v|}
  have hE : MeasurableSet E := measurableSet_lt
    (measurable_const.mul (hc.measurable.mul (measurable_fractionalRow k L T)))
    (measurable_const.mul hc.measurable.abs)
  refine ⟨E,hE,fun v hv => witness_at_displacement hs hT hB k L m v hv,?_⟩
  obtain ⟨hG,heq⟩ := band_integral_at_displacement (hi.indicator hE.compl) k L T
  rw [heq]
  have hpos : 0≤8*B := mul_nonneg (by norm_num) ((by positivity : 0≤1+Real.log 4).trans hB)
  have hle := integral_mono (hi.abs.const_mul (-8*B*|m|)) (hG.const_mul m) (fun v => by
    change (-8*B*|m|)*|Φ v| ≤ m*((Eᶜ.indicator Φ) v*fractionalRow k L T v)
    by_cases hv : v∈E
    · rw [indicator_of_notMem (show v∉Eᶜ from fun h => h hv),zero_mul,mul_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (by linarith only [hpos]) (abs_nonneg _)) (abs_nonneg _)
    · rw [indicator_of_mem (show v∈Eᶜ from hv)]
      exact le_of_not_gt hv)
  simpa only [integral_const_mul,mul_assoc] using hle

/-- The square-root cutoff converts a power of the numerator into a power of the test scale. -/
theorem quotient_numerator_power_at_test {H a L : ℕ} {T η g : ℝ} (hT : 6≤T) (hη : η≤1)
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

#print axioms exists_oriented_quotient_displacements
#print axioms exists_oriented_quotient_interval
end GaloisForLFunctions.ExclusionOfTheCriticalState
