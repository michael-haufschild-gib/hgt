import GaloisForLFunctions.RestrictedFactorizationCalculus.RemovingTerminalQuotientCellsByDivisorInversion
import GaloisForLFunctions.SelbergClass.DirichletSeries.PrimeRestriction

/-!
# Rough divisor inversion at the hyperbola

The counting measure on integers coprime to the primorial has Dirichlet
inverse equal to the rough Möbius row. Interpolation with its summatory
function therefore costs only the signed head of the inverse coefficients.
The same transfer removes every cofactor above the hyperbola for all
Mangoldt-dominated quotient weights at square-root logarithmic cost.
-/

noncomputable section
open Finset ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Restriction of an arithmetic function to integers coprime to the primorial. -/
def roughRestriction (y : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  GaloisForLFunctions.SelbergClass.DirichletSeries.primeRestrict {p | y<p} f

theorem roughRestriction_apply (y : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    roughRestriction y f n=if IsFree (RoughReading.banned y) n then f n else 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have eq : ((↑n.primeFactors : Set ℕ) ⊆ {p | y<p}) ↔ IsFree (RoughReading.banned y) n :=
      ⟨fun h => ⟨hn,fun p hp => not_le.mpr (h hp)⟩,fun h p hp => lt_of_not_ge (h.2 p hp)⟩
    simp only [roughRestriction,GaloisForLFunctions.SelbergClass.DirichletSeries.primeRestrict_apply,eq]

/-- Möbius coefficients after deleting primes through y. -/
abbrev roughMobiusWeight (y : ℕ) := roughRestriction y (μ : ArithmeticFunction ℝ)
/-- Unit weights on every positive integer coprime to the primorial. -/
abbrev roughCountingWeight (y : ℕ) := roughRestriction y (ζ : ArithmeticFunction ℝ)

private theorem roughMobiusWeight_apply (y n : ℕ) : roughMobiusWeight y n=RoughReading.row y n := by
  rw [RoughReading.row_value,roughMobiusWeight,roughRestriction_apply] <;> rfl

/-- The inverse identity includes the unit, repeated factors and every
excluded divisor class. -/
theorem inverse_of_the_rough_counting_measure (y : ℕ) :
    roughMobiusWeight y*roughCountingWeight y=1 :=
  GaloisForLFunctions.SelbergClass.DirichletSeries.restricted_moebius_mul_zeta _

private theorem summatory_product (f g : ArithmeticFunction ℝ) (X : ℕ) :
    quotientReading (f*g) X=∑ m ∈ Icc 1 X,f m*quotientReading g (X/m) := by
  unfold quotientReading
  simp only [mul_apply,mul_sum]
  exact RHTower.Sieve.sum_Icc_divisorsAntidiagonal_swap (fun m k => f m*g k) X

theorem rough_action_as_a_coefficient_prefix (y X : ℕ) (f : ArithmeticFunction ℝ) :
    roughCofactorReading y X (quotientReading f)=quotientReading (roughMobiusWeight y*f) X := by
  rw [summatory_product]
  exact sum_congr rfl (fun m _ => congrArg (fun z : ℝ => z*quotientReading f (X/m)) (roughMobiusWeight_apply y m).symm)

/-- The coefficient of the rough counting floor at d. -/
def roughFloorCoefficient (y : ℕ) (a : ArithmeticFunction ℝ) := roughMobiusWeight y*a

private def head (f : ArithmeticFunction ℝ) (T : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d ≤ T then f d else 0,by simp⟩

/-- The replacement center is a sum of counts of rough positive integers
at the actual quotient floors, with coefficients restricted to d ≤ T. -/
def roughCountingCenter (a : ArithmeticFunction ℝ) (y T t : ℕ) :=
  quotientReading (head (roughFloorCoefficient y a) T*roughCountingWeight y) t

theorem rough_counting_center_as_floor_sum (a : ArithmeticFunction ℝ) (y T t : ℕ) :
    roughCountingCenter a y T t=
      ∑ m ∈ (Icc 1 t).filter (· ≤ T),roughFloorCoefficient y a m*quotientReading (roughCountingWeight y) (t/m) := by
  rw [roughCountingCenter,summatory_product,sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : d ≤ T <;> simp [head,hd]

/-- The rough floor is the count of ordinary positive integers avoiding
the forbidden primes, including their allowed repeated prime factors. -/
theorem summatory_rough_counting_weight (y t : ℕ) :
    quotientReading (roughCountingWeight y) t=((RoughReading.freeSet y t).card:ℝ) := by
  rw [RoughReading.freeSet,←sum_boole]
  apply sum_congr rfl
  intro k hk
  have pos := (mem_Icc.mp hk).1
  simp only [roughCountingWeight,roughRestriction_apply,natCoe_apply,
    zeta_apply_ne (Nat.ne_of_gt (show 0<k from pos)),Nat.cast_one]

private theorem reconstruct (y : ℕ) (a : ArithmeticFunction ℝ) :
    roughFloorCoefficient y a*roughCountingWeight y=a := by
  calc _ = (roughMobiusWeight y*roughCountingWeight y)*a := by unfold roughFloorCoefficient; ac_rfl
       _ = a := by rw [inverse_of_the_rough_counting_measure,one_mul]

/-- Every low quotient is reproduced pointwise, for any arithmetic weight. -/
theorem rough_counting_center_exact {t T : ℕ} (ht : t ≤ T) (a : ArithmeticFunction ℝ) (y : ℕ) :
    roughCountingCenter a y T t=quotientReading a t := by
  rw [rough_counting_center_as_floor_sum]
  conv_rhs => rw [←reconstruct y a,summatory_product]
  have all : (Icc 1 t).filter (· ≤ T)=Icc 1 t := filter_eq_self.mpr (fun d hd => (mem_Icc.mp hd).2.trans ht)
  rw [all]

private theorem head_price (a : ArithmeticFunction ℝ) (y X T : ℕ) :
    roughCofactorReading y X (roughCountingCenter a y T)=quotientReading (roughFloorCoefficient y a) (min X T) := by
  unfold roughCountingCenter
  rw [rough_action_as_a_coefficient_prefix,show roughMobiusWeight y*(head (roughFloorCoefficient y a) T*roughCountingWeight y)=head (roughFloorCoefficient y a) T by
    calc _ = (roughMobiusWeight y*roughCountingWeight y)*head (roughFloorCoefficient y a) T := by ac_rfl
         _ = _ := by rw [inverse_of_the_rough_counting_measure,one_mul]]
  unfold quotientReading
  change (∑ d ∈ Icc 1 X,if d ≤ T then _ else 0)=_
  rw [←sum_filter]
  have eq : (Icc 1 X).filter (· ≤ T)=Icc 1 (min X T) := by ext n; simp only [mem_filter,mem_Icc,le_min_iff]; tauto
  rw [eq]

/-- The corrected arithmetic reading on the surviving smaller cofactors. -/
def roughInteriorReading (a : ArithmeticFunction ℝ) (y X T : ℕ) :=
  ∑ m ∈ Icc 1 (X/(T+1)),RoughReading.row y m*
    (quotientReading a (X/m)-roughCountingCenter a y T (X/m))

/-- Exact signed head and interior decomposition at every wall, including
T beyond X. Subtract the identities at two endpoints to take a sharp interval. -/
theorem rough_head_and_interior (a : ArithmeticFunction ℝ) (y X T : ℕ) :
    roughCofactorReading y X (quotientReading a)=
      roughInteriorReading a y X T+quotientReading (roughFloorCoefficient y a) (min X T) := by
  rw [←head_price,←sub_eq_iff_eq_add]
  unfold roughCofactorReading roughInteriorReading
  rw [←sum_sub_distrib]
  simp only [←mul_sub]
  symm
  apply sum_subset (Icc_subset_Icc_right (Nat.div_le_self ..))
  intro m hm outside
  have past : X/(T+1)<m := lt_of_not_ge (fun h => outside (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,h⟩))
  have small : X/m<T+1 := (Nat.div_lt_iff_lt_mul (mem_Icc.mp hm).1).mpr (by
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul (Nat.succ_pos T)).mp past)
  rw [rough_counting_center_exact (Nat.le_of_lt_succ small),sub_self,mul_zero]

private theorem coeff_interval (c : ArithmeticFunction ℝ) {l u : ℕ} (h : l ≤ u) :
    quotientReading c u-quotientReading c l=∑ d ∈ Ioc l u,c d := by
  have sets : Icc 1 u \ Icc 1 l=Ioc l u := by
    ext n
    simp only [Finset.mem_sdiff,mem_Icc,mem_Ioc]
    omega
  rw [←sets,sum_sdiff_eq_sub (Icc_subset_Icc_right h)]
  rfl

/-- On two cuts the common head cancels coefficient by coefficient. A
change of weight or sieve contributes its signed difference on precisely
that common head. This holds for arbitrary finite changes of reading. -/
theorem two_cutoff_change_of_the_rough_reading (a b : ArithmeticFunction ℝ) (y z L U A B : ℕ)
    (order : min L A ≤ min U B) :
    (roughCofactorReading z U (quotientReading b)-roughInteriorReading b z U B)-
      (roughCofactorReading y L (quotientReading a)-roughInteriorReading a y L A)=
      (∑ d ∈ Ioc (min L A) (min U B),roughFloorCoefficient z b d)+
      (∑ d ∈ Icc 1 (min L A),(roughFloorCoefficient z b d-roughFloorCoefficient y a d)) := by
  rw [rough_head_and_interior b,rough_head_and_interior a,add_sub_cancel_left,add_sub_cancel_left,
    ←coeff_interval _ order,sum_sub_distrib]
  unfold quotientReading
  ring

private theorem coefficient_le_log {a : ArithmeticFunction ℝ} (dom : ∀ n,|a n| ≤ vonMangoldt n) (y d : ℕ) :
    |roughFloorCoefficient y a d| ≤ Real.log d := by
  rw [roughFloorCoefficient,mul_comm (roughMobiusWeight y),mul_apply,Nat.sum_divisorsAntidiagonal,←vonMangoldt_sum (n := d)]
  apply (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun q _ => ?_))
  rw [abs_mul]
  have small : |roughMobiusWeight y (d/q)| ≤ 1 := by
    rw [roughMobiusWeight_apply,RoughReading.row_value]
    split
    · exact_mod_cast abs_moebius_le_one (n := d/q)
    · norm_num
  exact (mul_le_mul_of_nonneg_left small (abs_nonneg _)).trans ((mul_one _).le.trans (dom q))

/-- The whole paid piece costs at most T log T, uniformly in the sieve
and the arithmetic weight. No prefix estimate enters the bound. -/
theorem rough_interpolation_price {a : ArithmeticFunction ℝ} (dom : ∀ n,|a n| ≤ vonMangoldt n) (y X T : ℕ) :
    |roughCofactorReading y X (quotientReading a)-roughInteriorReading a y X T| ≤ T*Real.log T := by
  rw [rough_head_and_interior,add_sub_cancel_left]
  apply (abs_sum_le_sum_abs ..).trans
  have cap (d : ℕ) (hd : d ∈ Icc 1 (min X T)) : |roughFloorCoefficient y a d| ≤ Real.log T :=
    (coefficient_le_log dom y d).trans (Real.log_le_log (Nat.cast_pos.mpr (mem_Icc.mp hd).1)
      (Nat.cast_le.mpr ((mem_Icc.mp hd).2.trans (min_le_right ..))))
  apply (sum_le_sum cap).trans
  simpa using mul_le_mul_of_nonneg_right ((Nat.cast_le (α := ℝ)).mpr (min_le_right X T)) (Real.log_natCast_nonneg T)

/-- The same transfer takes every Mangoldt-dominated reading below the
hyperbola with a square-root logarithmic error at each sharp endpoint. -/
theorem transfer_below_the_hyperbola {a : ArithmeticFunction ℝ} (dom : ∀ n,|a n| ≤ vonMangoldt n) (y X : ℕ) :
    X/(X.sqrt+1) ≤ X.sqrt ∧
    |roughCofactorReading y X (quotientReading a)-roughInteriorReading a y X X.sqrt| ≤
      Real.sqrt X*Real.log X := by
  have h : X<(X.sqrt+1)*(X.sqrt+1) := lt_of_not_ge (fun hh => (Nat.not_succ_le_self X.sqrt) (Nat.le_sqrt.mpr hh))
  constructor
  · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul (Nat.succ_pos X.sqrt)).mpr h)
  · have low : (X.sqrt:ℝ) ≤ Real.sqrt X := by
      rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast Nat.sqrt_le' X
    have log : Real.log (X.sqrt:ℝ) ≤ Real.log X := by
      rcases Nat.eq_zero_or_pos X with rfl | xp
      · simp
      · have sqp : 1 ≤ X.sqrt := Nat.le_sqrt.mpr (by simpa using xp)
        exact Real.log_le_log (Nat.cast_pos.mpr sqp) (Nat.cast_le.mpr (Nat.sqrt_le_self X))
    exact (rough_interpolation_price dom y X X.sqrt).trans
      (mul_le_mul low log (Real.log_natCast_nonneg _) (Real.sqrt_nonneg _))

/-- With the weight and sieve frozen, the head at the hyperbola changes
only when a square enters the interval. Its cost depends on the number
of such squares, including zero on all intervals between them. -/
theorem square_crossings_pay_the_interval_error {a : ArithmeticFunction ℝ}
    (dom : ∀ n,|a n| ≤ vonMangoldt n) (y : ℕ) {L U : ℕ} (order : L ≤ U) :
    |(roughCofactorReading y U (quotientReading a)-roughInteriorReading a y U U.sqrt)-
      (roughCofactorReading y L (quotientReading a)-roughInteriorReading a y L L.sqrt)| ≤
      ((U.sqrt-L.sqrt:ℕ):ℝ)*Real.log U.sqrt := by
  have roots : L.sqrt ≤ U.sqrt := Nat.sqrt_le_sqrt order
  have change := two_cutoff_change_of_the_rough_reading a a y y L U L.sqrt U.sqrt
    (by simpa only [min_eq_right (Nat.sqrt_le_self _)] using roots)
  simp only [min_eq_right (Nat.sqrt_le_self _),sub_self,sum_const_zero,add_zero] at change
  rw [change]
  apply (abs_sum_le_sum_abs ..).trans
  have localBound (d : ℕ) (hd : d ∈ Ioc L.sqrt U.sqrt) : |roughFloorCoefficient y a d| ≤ Real.log U.sqrt :=
    (coefficient_le_log dom y d).trans (Real.log_le_log (Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt (mem_Ioc.mp hd).1))
      (Nat.cast_le.mpr (mem_Ioc.mp hd).2))
  exact (sum_le_sum localBound).trans_eq (by simp)

#print axioms two_cutoff_change_of_the_rough_reading
#print axioms square_crossings_pay_the_interval_error
#print axioms inverse_of_the_rough_counting_measure
#print axioms rough_counting_center_exact
#print axioms rough_head_and_interior
#print axioms transfer_below_the_hyperbola

end GaloisForLFunctions.RestrictedFactorizationCalculus
