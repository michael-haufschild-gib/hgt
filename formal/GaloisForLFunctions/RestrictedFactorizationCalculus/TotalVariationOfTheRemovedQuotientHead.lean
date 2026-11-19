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

private abbrev alive (Y H : ℕ → ℕ) (d i : ℕ) : Prop :=
  IsFree (RoughReading.banned (Y i)) d ∧ d ≤ H i

/-- Indicator that a divisor belongs to the head at the given prime
wall and height. -/
def roughHeadIndicator (y h d : ℕ) : ℝ :=
  ind (IsFree (RoughReading.banned y) d ∧ d ≤ h)

private theorem two_changes_per_divisor (Y H : ℕ → ℕ) (walls : Monotone Y) (heights : Monotone H)
    (d N : ℕ) : (∑ i ∈ range N,|ind (alive Y H d (i+1))-ind (alive Y H d i)|) ≤ 2 := by
  let ok := fun i => IsFree (RoughReading.banned (Y i)) d
  let u := fun i => ind (ok i)
  let v := fun i => ind (ok i ∧ H i<d)
  have falls (i : ℕ) (h : ok (i+1)) : ok i :=
    ⟨h.1,fun p hp bad => h.2 p hp (show p ≤ Y (i+1) from
      (show p ≤ Y i from bad).trans (walls (Nat.le_succ i)))⟩
  have first (i : ℕ) : u (i+1) ≤ u i := indicator_mono (falls i)
  have second (i : ℕ) : v (i+1) ≤ v i := indicator_mono
    (fun h => ⟨falls i h.1,(heights (Nat.le_succ i)).trans_lt h.2⟩)
  have eq (i : ℕ) : ind (alive Y H d i)=u i-v i := by
    change ind (ok i ∧ d ≤ H i)=ind (ok i)-ind (ok i ∧ H i<d)
    by_cases h : ok i <;> by_cases t : d ≤ H i <;> simp [ind,h,t,lt_iff_not_ge]
  simp only [eq]
  apply (RHTower.Sieve.variation_le_of_sub_antitone first second N).trans
  linarith only [indicator_le_one (ok 0),indicator_nonneg (ok N),
    indicator_le_one (ok 0 ∧ H 0<d),indicator_nonneg (ok N ∧ H N<d)]

private theorem head_on_the_final_divisor_range (a : ArithmeticFunction ℝ) (Y H : ℕ → ℕ)
    (heights : Monotone H) {i N : ℕ} (hi : i ≤ N) :
    quotientReading (roughFloorCoefficient (Y i) (roughRestriction (Y i) a)) (H i)=
      ∑ d ∈ Icc 1 (H N),quotientFloorCoefficients a d*ind (alive Y H d i) := by
  rw [restricted_coefficients,quotientReading]
  calc _ = ∑ d ∈ Icc 1 (H i),quotientFloorCoefficients a d*ind (alive Y H d i) := by
             apply sum_congr rfl
             intro d hd
             rw [roughRestriction_apply]
             by_cases h : IsFree (RoughReading.banned (Y i)) d <;>
               simp [alive,ind,h,(mem_Icc.mp hd).2]
       _ = _ := by
             apply sum_subset (Icc_subset_Icc_right (heights hi))
             intro d hd out
             have late : ¬d ≤ H i := fun h => out (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,h⟩)
             simp [alive,ind,late]

/-- Each change to the arithmetic reading pays its inverse coefficient
at the arrival wall. Each divisor can independently enter or leave the
moving range at most twice over the full history. -/
theorem variation_with_changes_of_arithmetic_reading (a : ℕ → ArithmeticFunction ℝ)
    (Y H : ℕ → ℕ) (walls : Monotone Y) (heights : Monotone H) (N : ℕ) (cap : ℕ → ℝ)
    (bounded : ∀ i d,i ≤ N → d ∈ Icc 1 (H N) → |quotientFloorCoefficients (a i) d| ≤ cap d) :
    let c := fun i => quotientFloorCoefficients (a i)
    let P := fun i => quotientReading (roughFloorCoefficient (Y i) (roughRestriction (Y i) (a i))) (H i)
    (∑ i ∈ range N,|P (i+1)-P i|) ≤ ∑ d ∈ Icc 1 (H N),
      (2*cap d+∑ i ∈ range N,|c (i+1) d-c i d| * roughHeadIndicator (Y (i+1)) (H (i+1)) d) := by
  let c := fun i => quotientFloorCoefficients (a i)
  let e := fun d i => ind (alive Y H d i)
  let S := Icc 1 (H N)
  let z := fun d i => c i d*e d i
  have per (d : ℕ) (hd : d ∈ S) :
      (∑ i ∈ range N,|z d (i+1)-z d i|) ≤ 2*cap d+∑ i ∈ range N,|c (i+1) d-c i d| * e d (i+1) := by
    have step (i : ℕ) (hi : i ∈ range N) :
        |z d (i+1)-z d i| ≤ cap d*|e d (i+1)-e d i|+|c (i+1) d-c i d| * e d (i+1) := by
      rw [show z d (i+1)-z d i=c i d*(e d (i+1)-e d i)+(c (i+1) d-c i d)*e d (i+1) by
        dsimp only [z]; ring]
      apply (abs_add_le ..).trans
      rw [abs_mul,abs_mul,abs_of_nonneg (indicator_nonneg (alive Y H d (i+1)))]
      exact add_le_add (mul_le_mul_of_nonneg_right (bounded i d (mem_range.mp hi).le hd) (abs_nonneg _)) le_rfl
    apply (sum_le_sum step).trans
    rw [sum_add_distrib,←mul_sum]
    exact add_le_add ((mul_le_mul_of_nonneg_left (two_changes_per_divisor Y H walls heights d N)
      ((abs_nonneg _).trans (bounded 0 d (Nat.zero_le _) hd))).trans_eq (mul_comm ..)) le_rfl
  dsimp only
  calc _ ≤ ∑ i ∈ range N,∑ d ∈ S,|z d (i+1)-z d i| := by
             apply sum_le_sum
             intro i hi
             rw [head_on_the_final_divisor_range _ Y H heights (mem_range.mp hi),
               head_on_the_final_divisor_range _ Y H heights (mem_range.mp hi).le,←sum_sub_distrib]
             exact abs_sum_le_sum_abs ..
       _ = ∑ d ∈ S,∑ i ∈ range N,|z d (i+1)-z d i| := sum_comm
       _ ≤ _ := by
             simpa only [S,c,e,alive,roughHeadIndicator] using sum_le_sum per


private theorem variation_of_a_divisor_coefficient (a : ℕ → ArithmeticFunction ℝ) (N : ℕ)
    {B : ℝ} (change : ∀ q,(∑ i ∈ range N,|a (i+1) q-a i q|) ≤ B*vonMangoldt q) (d : ℕ) :
    (∑ i ∈ range N,|quotientFloorCoefficients (a (i+1)) d-quotientFloorCoefficients (a i) d|) ≤ B*Real.log d := by
  let w := fun q => ((moebius (d/q):ℤ):ℝ)
  have value (f : ArithmeticFunction ℝ) : quotientFloorCoefficients f d=∑ q ∈ d.divisors,f q*w q := by
    rw [quotientFloorCoefficients,mul_apply,Nat.sum_divisorsAntidiagonal
      (fun q k => f q*(moebius : ArithmeticFunction ℝ) k)]
    rfl
  have price (i : ℕ) (_ : i ∈ range N) :
      |quotientFloorCoefficients (a (i+1)) d-quotientFloorCoefficients (a i) d| ≤
        ∑ q ∈ d.divisors,|a (i+1) q-a i q| := by
    rw [value,value,←sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    apply sum_le_sum
    intro q _
    rw [←sub_mul,abs_mul]
    have mw : |w q| ≤ 1 := by
      change |(μ (d/q):ℝ)| ≤ 1
      exact_mod_cast abs_moebius_le_one (n := d/q)
    exact (mul_le_mul_of_nonneg_left mw (abs_nonneg _)).trans_eq (mul_one _)
  apply (sum_le_sum price).trans
  rw [sum_comm,←vonMangoldt_sum (n := d),mul_sum]
  exact sum_le_sum (fun q _ => change q)

/-- The sharp heads for varying weights, sieve walls and quotient cuts.
An atom with total arithmetic variation at most B times its Mangoldt
weight contributes that budget once; the two other charges are its
divisor's entry and exit. -/
theorem total_cost_of_changing_rough_prime_readings (a : ℕ → ArithmeticFunction ℝ)
    (dom : ∀ i q,|a i q| ≤ vonMangoldt q) (Y H : ℕ → ℕ) (walls : Monotone Y)
    (heights : Monotone H) (N : ℕ) {B : ℝ} (bp : 0 ≤ B)
    (change : ∀ q,(∑ i ∈ range N,|a (i+1) q-a i q|) ≤ B*vonMangoldt q) :
    let P := fun i => quotientReading (roughFloorCoefficient (Y i) (roughRestriction (Y i) (a i))) (H i)
    (∑ i ∈ range N,|P (i+1)-P i|) ≤ (2+B)*(H N:ℝ)*Real.log (H N) := by
  have law := variation_with_changes_of_arithmetic_reading a Y H walls heights N (fun d => Real.log d)
    (fun i d _ _ => interpolating_coefficients_le_log (dom i) d)
  apply law.trans
  calc _ ≤ ∑ _d ∈ Icc 1 (H N),(2+B)*Real.log (H N) := by
             apply sum_le_sum
             intro d hd
             have erase (i : ℕ) (_ : i ∈ range N) :
                 |quotientFloorCoefficients (a (i+1)) d-quotientFloorCoefficients (a i) d| * ind (alive Y H d (i+1)) ≤
                    |quotientFloorCoefficients (a (i+1)) d-quotientFloorCoefficients (a i) d| :=
               (mul_le_mul_of_nonneg_left (indicator_le_one _) (abs_nonneg _)).trans_eq (mul_one _)
             have bound := (sum_le_sum erase).trans (variation_of_a_divisor_coefficient a N change d)
             have order := Real.log_le_log (Nat.cast_pos.mpr (mem_Icc.mp hd).1) (Nat.cast_le.mpr (mem_Icc.mp hd).2)
             have cap := mul_le_mul_of_nonneg_left order (by linarith : 0 ≤ 2+B)
             change 2*Real.log d+(∑ i ∈ range N,
               |quotientFloorCoefficients (a (i+1)) d-quotientFloorCoefficients (a i) d| * ind (alive Y H d (i+1))) ≤ _
             linarith only [bound,cap]
       _ = _ := by simp [mul_left_comm,mul_assoc]

/-- Each prime power independently changes from its first weight to
its second one at its prescribed observation. -/
def changingPrimePowerWeight (a b : ArithmeticFunction ℝ) (switchTime : ℕ → ℕ) (i : ℕ) :
    ArithmeticFunction ℝ := ⟨fun q => if switchTime q ≤ i then b q else a q,by simp⟩

/-- Arbitrarily scheduled changes at all prime powers cost at most four
visits per inverse divisor, over an arbitrary increasing path of sieve
walls and head endpoints. -/
theorem independent_changes_of_every_prime_power (a b : ArithmeticFunction ℝ)
    (da : ∀ q,|a q| ≤ vonMangoldt q) (db : ∀ q,|b q| ≤ vonMangoldt q) (switchTime Y H : ℕ → ℕ)
    (walls : Monotone Y) (heights : Monotone H) (N : ℕ) :
    let P := fun i => quotientReading (roughFloorCoefficient (Y i)
      (roughRestriction (Y i) (changingPrimePowerWeight a b switchTime i))) (H i)
    (∑ i ∈ range N,|P (i+1)-P i|) ≤ 4*(H N:ℝ)*Real.log (H N) := by
  let f := changingPrimePowerWeight a b switchTime
  have dom (i q : ℕ) : |f i q| ≤ vonMangoldt q := by
    change |if switchTime q ≤ i then b q else a q| ≤ _
    split <;> first | exact db q | exact da q
  have change (q : ℕ) : (∑ i ∈ range N,|f (i+1) q-f i q|) ≤ 2*vonMangoldt q := by
    have each (i : ℕ) (_ : i ∈ range N) :
        |f (i+1) q-f i q| ≤ if i=switchTime q-1 then 2*vonMangoldt q else 0 := by
      by_cases hit : i=switchTime q-1
      · rw [if_pos hit]
        exact (abs_sub ..).trans ((add_le_add (dom (i+1) q) (dom i q)).trans_eq (two_mul _).symm)
      · rw [if_neg hit]
        have eq : switchTime q ≤ i+1 ↔ switchTime q ≤ i := by omega
        change |(if switchTime q ≤ i+1 then b q else a q)-(if switchTime q ≤ i then b q else a q)| ≤ 0
        simp only [eq,sub_self,abs_zero,le_refl]
    apply (sum_le_sum each).trans
    by_cases inside : switchTime q-1 ∈ range N <;> simp [inside,vonMangoldt_nonneg]
  simpa only [show (2:ℝ)+2=4 by norm_num] using
    total_cost_of_changing_rough_prime_readings f dom Y H walls heights N (by norm_num : (0:ℝ) ≤ 2) change

/-- Recomputing a restricted inverse coefficient head on every member of
an arbitrary increasing family of sieve and height cutoffs costs at most
two visits per divisor, uniformly in the number of observations. -/
theorem variation_of_the_rough_coefficient_head (a : ArithmeticFunction ℝ)
    (Y H : ℕ → ℕ) (walls : Monotone Y) (heights : Monotone H) (N : ℕ) :
    let P := fun i => quotientReading (roughFloorCoefficient (Y i) (roughRestriction (Y i) a)) (H i)
    (∑ i ∈ range N,|P (i+1)-P i|) ≤ 2*∑ d ∈ Icc 1 (H N),|quotientFloorCoefficients a d| := by
  simpa only [sub_self,abs_zero,zero_mul,sum_const_zero,add_zero,←mul_sum] using
    variation_with_changes_of_arithmetic_reading (fun _ => a) Y H walls heights N
      (fun d => |quotientFloorCoefficients a d|) (fun _ _ _ _ => le_rfl)

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
  let f := fun i => roughRestriction (Y i) a
  let raw := fun i => roughCofactorReading (Y i) (X i) (quotientReading (f i))-
    roughInteriorReading (f i) (Y i) (X i) (X i).sqrt
  have paid (i : ℕ) : raw i=quotientReading (roughFloorCoefficient (Y i) (f i)) (H i) := by
    dsimp only [raw,H]
    rw [rough_head_and_interior,add_sub_cancel_left,min_eq_right (Nat.sqrt_le_self _)]
  change (∑ i ∈ range N,|raw (i+1)-raw i|) ≤ _
  simp only [paid]
  have var := variation_of_the_rough_coefficient_head a Y H walls mono N
  have per (d : ℕ) (hd : d ∈ Icc 1 (H N)) : |quotientFloorCoefficients a d| ≤ Real.log (H N) :=
    (interpolating_coefficients_le_log dom d).trans (Real.log_le_log (Nat.cast_pos.mpr (mem_Icc.mp hd).1)
      (Nat.cast_le.mpr (mem_Icc.mp hd).2))
  apply var.trans
  calc _ ≤ 2*∑ _d ∈ Icc 1 (H N),Real.log (H N) :=
             mul_le_mul_of_nonneg_left (sum_le_sum per) (by norm_num)
       _ = 2*((X N).sqrt:ℝ)*Real.log (X N).sqrt := by simp [H,mul_assoc]

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
#print axioms independent_changes_of_every_prime_power
#print axioms total_cost_of_changing_rough_prime_readings
#print axioms variation_of_the_rough_coefficient_head
#print axioms total_cost_of_moving_rough_hyperbola_heads
end GaloisForLFunctions.RestrictedFactorizationCalculus
