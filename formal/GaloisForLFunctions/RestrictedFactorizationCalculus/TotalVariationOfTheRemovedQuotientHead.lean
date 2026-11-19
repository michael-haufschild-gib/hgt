import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCenteredReadingBelowTheHyperbola
import GaloisForLFunctions.RHTower.Sieve.VariationOfDifference
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheCriticalEulerPriceOfTheLogSquareCutoff

/-!
# Total variation of the eliminated quotient cells

In an increasing observation window with increasing sieve wall, an
inverse coefficient enters the paid head once and can leave only once.
All intermediate changes have the same order of cost as a single head.
The original smooth center increases between successive sieve changes.
-/

noncomputable section
open Filter Finset ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical ArithmeticFunction.Moebius
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem restricted_coefficients (a : ArithmeticFunction ℝ) (y : ℕ) :
    roughFloorCoefficient y (roughRestriction y a)=roughRestriction y (quotientFloorCoefficients a) := by
  simp only [roughFloorCoefficient,roughMobiusWeight,quotientFloorCoefficients,roughRestriction,
    GaloisForLFunctions.SelbergClass.DirichletSeries.primeRestrict_mul]
  exact mul_comm ..

private def ind (P : Prop) : ℝ := if P then 1 else 0
private theorem indicator_mono {P Q : Prop} (h : P → Q) : ind P ≤ ind Q := by
  by_cases p : P
  · simp [ind,p,h p]
  · by_cases q : Q <;> simp [ind,p,q]
private theorem indicator_nonneg (P : Prop) : 0 ≤ ind P := by by_cases h : P <;> simp [ind,h]
private theorem indicator_le_one (P : Prop) : ind P ≤ 1 := by by_cases h : P <;> simp [ind,h]

/-- Recomputing a restricted inverse coefficient head on every member of
an arbitrary increasing family of sieve and height cutoffs costs at most
two visits per divisor, uniformly in the number of observations. -/
theorem variation_of_the_rough_coefficient_head (a : ArithmeticFunction ℝ)
    (Y H : ℕ → ℕ) (walls : Monotone Y) (heights : Monotone H) (N : ℕ) :
    let P := fun i => quotientReading (roughFloorCoefficient (Y i) (roughRestriction (Y i) a)) (H i)
    (∑ i ∈ range N,|P (i+1)-P i|) ≤ 2*∑ d ∈ Icc 1 (H N),|quotientFloorCoefficients a d| := by
  let c := quotientFloorCoefficients a
  let ok := fun d i => IsFree (RoughReading.banned (Y i)) d
  let u := fun d i => ind (ok d i)
  let v := fun d i => ind (ok d i ∧ H i<d)
  let z := fun d i => c d*(u d i-v d i)
  let P := fun i => quotientReading (roughFloorCoefficient (Y i) (roughRestriction (Y i) a)) (H i)
  let S := Icc 1 (H N)
  have falls (d i : ℕ) (h : ok d (i+1)) : ok d i :=
    ⟨h.1,fun p hp bad => h.2 p hp (bad.trans (walls (Nat.le_succ i)))⟩
  have per (d : ℕ) : (∑ i ∈ range N,|z d (i+1)-z d i|) ≤ 2*|c d| := by
    have first (i : ℕ) : u d (i+1) ≤ u d i := indicator_mono (falls ..)
    have second (i : ℕ) : v d (i+1) ≤ v d i := indicator_mono
      (fun h => ⟨falls d i h.1,(heights (Nat.le_succ i)).trans_lt h.2⟩)
    have var := RHTower.Sieve.variation_le_of_sub_antitone first second N
    have cap : (u d 0-u d N)+(v d 0-v d N) ≤ 2 := by
      linarith only [indicator_le_one (ok d 0),indicator_nonneg (ok d N),
        indicator_le_one (ok d 0 ∧ H 0<d),indicator_nonneg (ok d N ∧ H N<d)]
    simp only [z,←mul_sub,abs_mul,←mul_sum]
    simpa only [mul_comm (2:ℝ)] using mul_le_mul_of_nonneg_left (var.trans cap) (abs_nonneg (c d))
  have expr (i : ℕ) (hi : i ≤ N) : P i=∑ d ∈ S,z d i := by
    dsimp only [P,quotientReading]
    rw [restricted_coefficients]
    calc _ = ∑ d ∈ Icc 1 (H i),z d i := by
               apply sum_congr rfl
               intro d hd
               have within := (mem_Icc.mp hd).2
               rw [roughRestriction_apply]
               change (if ok d i then c d else 0)=z d i
               by_cases free : ok d i <;> simp [z,u,v,ind,free,within.not_gt]
         _ = ∑ d ∈ S,z d i := by
               apply sum_subset (Icc_subset_Icc_right (heights hi))
               intro d hd out
               have late : H i<d := lt_of_not_ge (fun h => out (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,h⟩))
               simp [z,u,v,late]
  change (∑ i ∈ range N,|P (i+1)-P i|) ≤ _
  calc _ ≤ ∑ i ∈ range N,∑ d ∈ S,|z d (i+1)-z d i| := by
             apply sum_le_sum
             intro i hi
             have lt := mem_range.mp hi
             rw [expr (i+1) lt,expr i lt.le,←sum_sub_distrib]
             exact abs_sum_le_sum_abs ..
       _ = ∑ d ∈ S,∑ i ∈ range N,|z d (i+1)-z d i| := sum_comm
       _ ≤ ∑ d ∈ S,2*|c d| := sum_le_sum (fun d _ => per d)
       _ = _ := (mul_sum ..).symm

/-- For every Mangoldt-dominated weight the complete price of all changes
to the omitted head at the hyperbola is square-root logarithmic, including
the effect of changing the primorial between every pair of readings. -/
theorem total_cost_of_moving_rough_hyperbola_heads {a : ArithmeticFunction ℝ}
    (dom : ∀ d,|a d| ≤ vonMangoldt d) (Y X : ℕ → ℕ) (walls : Monotone Y)
    (cuts : Monotone X) (N : ℕ) :
    let P := fun i => let f := roughRestriction (Y i) a
      roughCofactorReading (Y i) (X i) (quotientReading f)-roughInteriorReading f (Y i) (X i) (X i).sqrt
    (∑ i ∈ range N,|P (i+1)-P i|) ≤ 2*((X N).sqrt:ℝ)*Real.log (X N).sqrt := by
  let H := fun i => (X i).sqrt
  have mono : Monotone H := fun _ _ h => Nat.sqrt_le_sqrt (cuts h)
  simp only [rough_head_and_interior,add_sub_cancel_left,min_eq_right (Nat.sqrt_le_self _)]
  have var := variation_of_the_rough_coefficient_head a Y H walls mono N
  have per (d : ℕ) (hd : d ∈ Icc 1 (H N)) : |quotientFloorCoefficients a d| ≤ Real.log (H N) :=
    (interpolating_coefficients_le_log dom d).trans (Real.log_le_log (Nat.cast_pos.mpr (mem_Icc.mp hd).1)
      (Nat.cast_le.mpr (mem_Icc.mp hd).2))
  exact var.trans ((mul_le_mul_of_nonneg_left (sum_le_sum per) (by norm_num : (0:ℝ) ≤ 2)).trans_eq
    (by simp [H,mul_assoc]))

private theorem smooth_center_mono (y : ℕ) {l u : ℕ} (order : l ≤ u) :
    smoothQuotientCenter y l ≤ smoothQuotientCenter y u := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact_mod_cast Finset.card_le_card (filter_subset_filter
    (fun n : ℕ => n.primeFactors ⊆ Nat.primesLE y) (Icc_subset_Icc_right (Nat.div_le_div_right order)))

private theorem positive_variation_between_increasing_walls (F : ℕ → ℝ) (Y : ℕ → ℕ)
    (inc : Monotone Y) (same : ∀ i,Y i=Y (i+1) → F i ≤ F (i+1))
    (N : ℕ) {A : ℝ} (pos : 0 ≤ A) (nonneg : ∀ i,0 ≤ F i) (cap : ∀ i,i ≤ N → F i ≤ A) :
    (∑ i ∈ range N,|F (i+1)-F i|) ≤ (1+2*(Y N:ℝ))*A := by
  have step (i : ℕ) (hi : i ∈ range N) :
      |F (i+1)-F i| ≤ F (i+1)-F i+2*A*((Y (i+1):ℝ)-Y i) := by
    by_cases equal : Y i=Y (i+1)
    · rw [abs_of_nonneg (sub_nonneg.mpr (same i equal)),equal,sub_self,mul_zero,add_zero]
    · have jump : Y i+1 ≤ Y (i+1) := (lt_of_le_of_ne (inc (Nat.le_succ i)) equal)
      have room : (Y i:ℝ)+1 ≤ Y (i+1) := by exact_mod_cast jump
      apply abs_le.mpr
      have spend := mul_le_mul_of_nonneg_left room pos
      constructor <;> linarith only [spend,pos,nonneg (i+1),cap i (mem_range.mp hi).le]
  apply (sum_le_sum step).trans
  rw [sum_add_distrib,←mul_sum,Finset.sum_range_sub F,Finset.sum_range_sub (fun i => (Y i:ℝ))]
  linarith only [cap N le_rfl,nonneg 0,mul_nonneg pos (Nat.cast_nonneg (α := ℝ) (Y 0))]

/-- The total variation of the *centered* discrepancy on every increasing
subdivision below X. The smooth population pays only for changes of
prime wall and the final wall. The rough coefficient head pays at most
two visits per divisor below the hyperbola. -/
theorem total_variation_of_the_centered_hyperbola_transfer :
    ∃ C : ℝ,0<C ∧ ∀ᶠ X : ℕ in atTop,∀ cuts : ℕ → ℕ,Monotone cuts →
      0<logSquareCutoff (cuts 0) → ∀ N : ℕ,cuts N ≤ X →
      let D := fun i => centeredPrimePowerRemainder (logSquareCutoff (cuts i)) (cuts i)-
        primePowerReadingBelowTheHyperbola (cuts i)
      (∑ i ∈ range N,|D (i+1)-D i|) ≤ 2*Real.sqrt X*Real.log X+
        (1+2*(logSquareCutoff X:ℝ))*Real.sqrt X*Real.exp (C*Real.log X/Real.log (Real.log X)) := by
  obtain ⟨C,hC,uniform⟩ := critical_upper_price_of_the_smooth_main_term
  refine ⟨C,hC,?_⟩
  filter_upwards [uniform,eventually_ge_atTop (1:ℕ)] with X smooth xp
  intro cuts inc start N last
  let Y := fun i => logSquareCutoff (cuts i)
  have walls : Monotone Y := logSquareCutoff_mono.comp inc
  let P := fun i => let a := roughMangoldtWeight (Y i)
    roughCofactorReading (Y i) (cuts i) (quotientReading a)-
      roughInteriorReading a (Y i) (cuts i) (cuts i).sqrt
  let F := fun i => smoothQuotientCenter (Y i) (cuts i)
  let A := Real.sqrt X*Real.exp (C*Real.log X/Real.log (Real.log X))
  have ap : 0 ≤ A := mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  have decomp (i : ℕ) : centeredPrimePowerRemainder (Y i) (cuts i)-
      primePowerReadingBelowTheHyperbola (cuts i)=P i-F i := by
    rw [centered_eq_rough_reading_sub_smooth (start.trans_le (walls (Nat.zero_le i)))]
    dsimp only [P,F,primePowerReadingBelowTheHyperbola,Y]; ring
  have fbound (i : ℕ) (h : i ≤ N) : F i ≤ A :=
    (smooth_center_mono (Y i) ((inc h).trans last)).trans (smooth (Y i) (logSquareCutoff_mono ((inc h).trans last)))
  have stay (i : ℕ) (e : Y i=Y (i+1)) : F i ≤ F (i+1) := by
    dsimp only [F]; rw [e]; exact smooth_center_mono _ (inc (Nat.le_succ _))
  have fvar := positive_variation_between_increasing_walls F Y walls stay N ap (fun i => mul_nonneg
    (Nat.cast_nonneg _) (Nat.cast_nonneg _)) fbound
  have pvar := total_cost_of_moving_rough_hyperbola_heads (a := vonMangoldt)
    (fun n => (abs_of_nonneg vonMangoldt_nonneg).le) Y cuts walls inc N
  change (∑ i ∈ range N,|P (i+1)-P i|) ≤ _ at pvar
  have root : ((cuts N).sqrt:ℝ) ≤ Real.sqrt X := by
    apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
    exact_mod_cast (Nat.sqrt_le' (cuts N)).trans last
  have log : Real.log ((cuts N).sqrt:ℝ) ≤ Real.log X := by
    rcases Nat.eq_zero_or_pos (cuts N).sqrt with hz | hpos
    · rw [hz,Nat.cast_zero,Real.log_zero]; exact Real.log_natCast_nonneg _
    · exact Real.log_le_log (Nat.cast_pos.mpr hpos) (Nat.cast_le.mpr ((Nat.sqrt_le_self _).trans last))
  have hcap := mul_le_mul root log (Real.log_natCast_nonneg _) (Real.sqrt_nonneg _)
  have wallCap := mul_le_mul_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr (logSquareCutoff_mono last)) ap
  change (∑ i ∈ range N,|(centeredPrimePowerRemainder (Y (i+1)) (cuts (i+1))-
    primePowerReadingBelowTheHyperbola (cuts (i+1)))-(centeredPrimePowerRemainder (Y i) (cuts i)-
    primePowerReadingBelowTheHyperbola (cuts i))|) ≤ _
  simp only [decomp]
  have point (i : ℕ) (_ : i ∈ range N) : |(P (i+1)-F (i+1))-(P i-F i)| ≤
      |P (i+1)-P i|+|F (i+1)-F i| := by
    rw [show (P (i+1)-F (i+1))-(P i-F i)=(P (i+1)-P i)-(F (i+1)-F i) by ring]
    exact abs_sub ..
  apply (sum_le_sum point).trans
  rw [sum_add_distrib]
  change _ ≤ 2*Real.sqrt X*Real.log X+(1+2*(logSquareCutoff X:ℝ))*Real.sqrt X*_
  rw [mul_assoc (1+2*(logSquareCutoff X:ℝ))]
  change _ ≤ 2*Real.sqrt X*Real.log X+(1+2*(logSquareCutoff X:ℝ))*A
  linarith only [pvar,fvar,hcap,wallCap]

#print axioms total_variation_of_the_centered_hyperbola_transfer
#print axioms variation_of_the_rough_coefficient_head
#print axioms total_cost_of_moving_rough_hyperbola_heads
end GaloisForLFunctions.RestrictedFactorizationCalculus
