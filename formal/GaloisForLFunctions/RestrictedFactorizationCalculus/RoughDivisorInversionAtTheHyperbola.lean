import GaloisForLFunctions.RestrictedFactorizationCalculus.RemovingTerminalQuotientCellsByDivisorInversion

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
  ⟨fun n => if IsFree (RoughReading.banned y) n then f n else 0,by simp⟩

private theorem restrict_product (y : ℕ) (f g : ArithmeticFunction ℝ) :
    roughRestriction y (f*g)=roughRestriction y f*roughRestriction y g := by
  ext n
  let E := RoughReading.banned y
  have factor (v : ℕ × ℕ) (hv : v ∈ n.divisorsAntidiagonal) :
      IsFree E n ↔ IsFree E v.1 ∧ IsFree E v.2 := by
    obtain ⟨eq,nz⟩ := Nat.mem_divisorsAntidiagonal.mp hv
    have pn : v.1*v.2 ≠ 0 := eq ▸ nz
    rw [←eq,isFree_mul_iff E (mul_ne_zero_iff.mp pn).1 (mul_ne_zero_iff.mp pn).2]
  change (if IsFree E n then (f*g) n else 0)=_
  rw [mul_apply,mul_apply]
  by_cases good : IsFree E n
  · rw [if_pos good]
    apply sum_congr rfl
    intro v hv
    obtain ⟨a,b⟩ := (factor v hv).mp good
    simp only [roughRestriction,if_pos a,if_pos b, E] at *
    <;> rfl
  · rw [if_neg good]
    symm
    apply sum_eq_zero
    intro v hv
    change (if IsFree E v.1 then _ else 0)*(if IsFree E v.2 then _ else 0)=0
    by_cases first : IsFree E v.1
    · have second : ¬IsFree E v.2 := fun second => good ((factor v hv).mpr ⟨first,second⟩)
      rw [if_neg second,mul_zero]
    · rw [if_neg first,zero_mul]

private abbrev roughMu (y : ℕ) := roughRestriction y (μ : ArithmeticFunction ℝ)
private abbrev roughUnitCount (y : ℕ) := roughRestriction y (ζ : ArithmeticFunction ℝ)

private theorem roughMu_apply (y n : ℕ) : roughMu y n=RoughReading.row y n := by
  rw [RoughReading.row_value]
  rfl

/-- The inverse identity includes the unit, repeated factors and every
excluded divisor class. -/
theorem inverse_of_the_rough_counting_measure (y : ℕ) :
    roughMu y*roughUnitCount y=1 := by
  rw [←restrict_product,coe_moebius_mul_coe_zeta]
  ext n
  by_cases h : n=1
  · subst n; simp [roughRestriction,isFree_one]
  · simp [roughRestriction,one_apply,h]

private theorem summatory_product (f g : ArithmeticFunction ℝ) (X : ℕ) :
    quotientReading (f*g) X=∑ m ∈ Icc 1 X,f m*quotientReading g (X/m) := by
  unfold quotientReading
  simp only [mul_apply,mul_sum]
  exact RHTower.Sieve.sum_Icc_divisorsAntidiagonal_swap (fun m k => f m*g k) X

private theorem signed_action (y X : ℕ) (f : ArithmeticFunction ℝ) :
    roughCofactorReading y X (quotientReading f)=quotientReading (roughMu y*f) X := by
  rw [summatory_product]
  exact sum_congr rfl (fun m _ => congrArg (fun z : ℝ => z*quotientReading f (X/m)) (roughMu_apply y m).symm)

/-- The coefficient of the rough counting floor at d. -/
def roughFloorCoefficient (y : ℕ) (a : ArithmeticFunction ℝ) := roughMu y*a

private def head (f : ArithmeticFunction ℝ) (T : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d ≤ T then f d else 0,by simp⟩

/-- The replacement center is a sum of counts of rough positive integers
at the actual quotient floors, with coefficients restricted to d ≤ T. -/
def roughCountingCenter (a : ArithmeticFunction ℝ) (y T t : ℕ) :=
  quotientReading (head (roughFloorCoefficient y a) T*roughUnitCount y) t

theorem rough_counting_center_as_floor_sum (a : ArithmeticFunction ℝ) (y T t : ℕ) :
    roughCountingCenter a y T t=
      ∑ m ∈ (Icc 1 t).filter (· ≤ T),roughFloorCoefficient y a m*quotientReading (roughUnitCount y) (t/m) := by
  rw [roughCountingCenter,summatory_product,sum_filter]
  apply sum_congr rfl
  intro d _
  by_cases hd : d ≤ T <;> simp [head,hd]

private theorem reconstruct (y : ℕ) (a : ArithmeticFunction ℝ) :
    roughFloorCoefficient y a*roughUnitCount y=a := by
  calc _ = (roughMu y*roughUnitCount y)*a := by unfold roughFloorCoefficient; ac_rfl
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
  rw [signed_action,show roughMu y*(head (roughFloorCoefficient y a) T*roughUnitCount y)=head (roughFloorCoefficient y a) T by
    calc _ = (roughMu y*roughUnitCount y)*head (roughFloorCoefficient y a) T := by ac_rfl
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

private theorem coefficient_le_log {a : ArithmeticFunction ℝ} (dom : ∀ n,|a n| ≤ vonMangoldt n) (y d : ℕ) :
    |roughFloorCoefficient y a d| ≤ Real.log d := by
  rw [roughFloorCoefficient,mul_comm (roughMu y),mul_apply,Nat.sum_divisorsAntidiagonal,←vonMangoldt_sum (n := d)]
  apply (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun q _ => ?_))
  rw [abs_mul]
  have small : |roughMu y (d/q)| ≤ 1 := by
    rw [roughMu_apply,RoughReading.row_value]
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

#print axioms inverse_of_the_rough_counting_measure
#print axioms rough_counting_center_exact
#print axioms rough_head_and_interior
#print axioms transfer_below_the_hyperbola

end GaloisForLFunctions.RestrictedFactorizationCalculus
