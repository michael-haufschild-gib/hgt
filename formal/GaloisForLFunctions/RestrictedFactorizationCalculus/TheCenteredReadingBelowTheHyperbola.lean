import GaloisForLFunctions.RestrictedFactorizationCalculus.RoughDivisorInversionAtTheHyperbola
import GaloisForLFunctions.RestrictedFactorizationCalculus.OneCenteredPrimePowerReadingAtTheLogSquareCutoff

/-!
# The centered prime-power criterion below the hyperbola

Only cofactors through the hyperbola need to carry the corrected prime
reading. Ordinary primes satisfy the same head-price bound. For the
whole Mangoldt weight its signed head is exactly the negative logarithmic
rough Möbius prefix. The original smooth center has its own sign at
both observation endpoints.
-/

noncomputable section

open Filter Finset ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.QuantitativeFactorizationMatching
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The signed head at a smaller endpoint still reads all the original
arithmetic increments, with their quotient taken at that endpoint. -/
theorem coefficient_head_as_quotient_sum (y T : ℕ) (a : ArithmeticFunction ℝ) :
    quotientReading (roughFloorCoefficient y a) T=
      ∑ q ∈ Icc 1 T,a q*coprimeMoebiusSum (primorial y) (T/q) := by
  have zero : coprimeMoebiusSum (primorial y) 0=0 := by simp [coprimeMoebiusSum]
  have h := (rough_action_as_a_coefficient_prefix y T a).symm.trans
    (rough_cofactor_reading_as_a_quotient_boundary a y T)
  simpa only [roughFloorCoefficient,quotientBoundary,Nat.zero_div,zero,sub_zero] using h

/-- The smaller-cofactor sum retains the fixed and crossing charges of
the original weight at both the observation and the removed head. -/
theorem signed_flux_of_the_corrected_interior (F : ℕ → ℕ)
    (law : ∀ n,Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)))
    (a : ArithmeticFunction ℝ) (y X T : ℕ) :
    roughInteriorReading a y X T=
      quotientBoundary (smoothLiftedPrefix (fixedSignedPrefix F) y) (Icc 1 X) a (min X T) X+
      quotientBoundary (smoothLiftedPrefix (crossingSignedPrefix F) y) (Icc 1 X) a (min X T) X := by
  let L := min X T
  let M := coprimeMoebiusSum (primorial y)
  have extend : (∑ q ∈ Icc 1 L,a q*M (L/q))=∑ q ∈ Icc 1 X,a q*M (L/q) := by
    apply sum_subset (Icc_subset_Icc_right (min_le_left X T))
    intro q hq outside
    have high : L<q := lt_of_not_ge (fun h => outside (mem_Icc.mpr ⟨(mem_Icc.mp hq).1,h⟩))
    simp [Nat.div_eq_of_lt high,M,coprimeMoebiusSum]
  have split := rough_head_and_interior a y X T
  rw [rough_action_as_a_coefficient_prefix] at split
  change quotientReading (roughFloorCoefficient y a) X=
    roughInteriorReading a y X T+quotientReading (roughFloorCoefficient y a) L at split
  rw [coefficient_head_as_quotient_sum,coefficient_head_as_quotient_sum,extend] at split
  rw [←two_cutoff_rough_quotient_flux F law]
  simp only [quotientBoundary,mul_sub,sum_sub_distrib]
  exact eq_sub_of_add_eq split.symm

/-- Ordinary primes and all surviving prime powers are read at the same wall. -/
def roughMangoldtWeight (y : ℕ) := roughRestriction y vonMangoldt

def roughOrdinaryPrimeWeight (y : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun q => if q.Prime ∧ y<q then Real.log q else 0,by simp⟩

theorem mangoldt_dominated (y n : ℕ) : |roughMangoldtWeight y n| ≤ vonMangoldt n := by
  rw [roughMangoldtWeight,roughRestriction_apply]
  split
  · exact (abs_of_nonneg vonMangoldt_nonneg).le
  · rw [abs_zero]; exact vonMangoldt_nonneg

theorem ordinary_dominated (y n : ℕ) : |roughOrdinaryPrimeWeight y n| ≤ vonMangoldt n := by
  change |if n.Prime ∧ y<n then Real.log n else 0| ≤ _
  split
  · rename_i h
    rw [vonMangoldt_apply_prime h.1,abs_of_nonneg (Real.log_natCast_nonneg _)]
  · rw [abs_zero]; exact vonMangoldt_nonneg

private theorem reading_eq (y t : ℕ) : quotientReading (roughMangoldtWeight y) t=roughPrimePowerReading y t := by
  simp only [quotientReading,roughMangoldtWeight,roughRestriction_apply,roughPrimePowerReading,
    RoughReading.freeSet,sum_filter]

/-- Logarithmically weighted Möbius prefix at a frozen prime wall. -/
def roughLogarithmicHead (y X : ℕ) := ∑ n ∈ Icc 1 X,RoughReading.row y n*Real.log n
/-- The smooth contribution removed by the exact integer floor center. -/
def smoothQuotientCenter (y X : ℕ) := (y:ℝ)*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) (X/y)).card

/-- Convolving the surviving prime powers with their rough Möbius row
gives the negative logarithmic prefix. -/
theorem full_rough_reading {y : ℕ} (hy : 0<y) (X : ℕ) :
    roughCofactorReading y X (quotientReading (roughMangoldtWeight y))= -roughLogarithmicHead y X := by
  have base := logarithmic_rough_prefix_at_quotient_readings hy X
  have eq : (∑ m ∈ RoughReading.freeSet y (X/y),RoughReading.row y m*roughPrimePowerReading y (X/m))=
      roughCofactorReading y X (quotientReading (roughMangoldtWeight y)) := by
    simp only [roughCofactorReading,reading_eq]
    apply sum_subset ((filter_subset ..).trans (Icc_subset_Icc_right (Nat.div_le_self ..)))
    intro m hm out
    by_cases past : X/y < m
    · have small : X/m<y := (Nat.div_lt_iff_lt_mul (mem_Icc.mp hm).1).mpr (by
        simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hy).mp past)
      rw [roughPrimePowerReading_eq_zero small.le,mul_zero]
    · have bad : ¬IsFree (RoughReading.banned y) m := fun h => out (mem_filter.mpr
        ⟨mem_Icc.mpr ⟨(mem_Icc.mp hm).1,le_of_not_gt past⟩,h⟩)
      rw [RoughReading.row_value,if_neg bad,zero_mul]
  rw [eq] at base
  exact neg_eq_iff_eq_neg.mp base.symm

/-- The original integer floor removes the positive smooth population
from the raw arithmetic reading at exactly the same observation. -/
theorem centered_eq_rough_reading_sub_smooth {y : ℕ} (hy : 0<y) (X : ℕ) :
    centeredPrimePowerRemainder y X=roughCofactorReading y X (quotientReading (roughMangoldtWeight y))-
      smoothQuotientCenter y X := by
  rw [full_rough_reading hy]
  have eq := exact_centered_prime_power_remainder hy X
  rw [neg_mul] at eq
  change roughLogarithmicHead y X+centeredPrimePowerRemainder y X= -smoothQuotientCenter y X at eq
  linarith only [eq]

/-- The signed polynomial or log-square smooth center, the signed head,
and the corrected interior reading at arbitrary sharp endpoints. -/
theorem centered_reading_after_rough_interpolation {y : ℕ} (hy : 0<y) (X T : ℕ) :
    centeredPrimePowerRemainder y X=
      roughInteriorReading (roughMangoldtWeight y) y X T-roughLogarithmicHead y (min X T)-smoothQuotientCenter y X := by
  let a := roughMangoldtWeight y
  have decom := rough_head_and_interior a y X T
  have head : quotientReading (roughFloorCoefficient y a) (min X T)= -roughLogarithmicHead y (min X T) :=
    (rough_action_as_a_coefficient_prefix y (min X T) a).symm.trans (full_rough_reading hy _)
  have total := full_rough_reading hy X
  have center := exact_centered_prime_power_remainder hy X
  rw [neg_mul] at center
  change roughLogarithmicHead y X+centeredPrimePowerRemainder y X= -smoothQuotientCenter y X at center
  rw [head] at decom
  change roughCofactorReading y X (quotientReading a)= -roughLogarithmicHead y X at total
  linarith only [center,decom,total]

/-- At a frozen sieve wall the corrected prime-power sum reads the
weighted Möbius tail on the original interval with its negative sign. -/
theorem interior_reads_the_logarithmic_tail {y : ℕ} (hy : 0<y) (X T : ℕ) :
    roughInteriorReading (roughMangoldtWeight y) y X T=
      roughLogarithmicHead y (min X T)-roughLogarithmicHead y X := by
  have split := centered_reading_after_rough_interpolation hy X T
  rw [centered_eq_rough_reading_sub_smooth hy,full_rough_reading hy] at split
  linarith only [split]

/-- Both ordinary primes and prime powers admit the same unconditional
transfer, including the final sharp prefix. -/
theorem both_prime_readings_below_the_hyperbola (y X : ℕ) :
    ∀ a ∈ ({roughOrdinaryPrimeWeight y,roughMangoldtWeight y} : Finset (ArithmeticFunction ℝ)),
      |roughCofactorReading y X (quotientReading a)-roughInteriorReading a y X X.sqrt| ≤ Real.sqrt X*Real.log X := by
  intro a ha
  simp only [mem_insert,mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact (transfer_below_the_hyperbola (ordinary_dominated y) y X).2
  · exact (transfer_below_the_hyperbola (mangoldt_dominated y) y X).2

private abbrev centered (X : ℕ) := centeredPrimePowerRemainder (logSquareCutoff X) X
/-- The corrected log-square prime-power reading restricted to the smaller cofactors. -/
def primePowerReadingBelowTheHyperbola (X : ℕ) :=
  roughInteriorReading (roughMangoldtWeight (logSquareCutoff X)) (logSquareCutoff X) X X.sqrt

private theorem difference_price {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop,|centered X-primePowerReadingBelowTheHyperbola X| ≤ (1/ε+1)*(X:ℝ)^(1/2+ε) := by
  filter_upwards [logSquareCutoff_tendsto_atTop.eventually_ge_atTop 1,smooth_main_term_paid_at_the_log_square_cutoff hε,
    eventually_ge_atTop (1:ℕ)] with X hy smooth hx
  let y := logSquareCutoff X
  let a := roughMangoldtWeight y
  let B := roughCofactorReading y X (quotientReading a)
  have eq : centered X=B-smoothQuotientCenter y X := centered_eq_rough_reading_sub_smooth hy X
  have head := (transfer_below_the_hyperbola (mangoldt_dominated y) y X).2
  have cost := smooth y le_rfl
  have sp : 0<(X:ℝ) := Nat.cast_pos.mpr hx
  have log := Real.log_le_rpow_div sp.le hε
  have scaled := mul_le_mul_of_nonneg_left log (Real.sqrt_nonneg (X:ℝ))
  have power : Real.sqrt X*((X:ℝ)^ε/ε)=(1/ε)*(X:ℝ)^(1/2+ε) := by
    rw [Real.rpow_add sp,Real.sqrt_eq_rpow]; ring
  rw [power] at scaled
  rw [eq,show B-smoothQuotientCenter y X-primePowerReadingBelowTheHyperbola X=(B-primePowerReadingBelowTheHyperbola X)-smoothQuotientCenter y X by ring]
  apply (abs_sub ..).trans
  rw [abs_of_nonneg (show 0 ≤ smoothQuotientCenter y X from mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  exact (add_le_add (head.trans scaled) cost).trans_eq (by ring)

private theorem transfer_estimate {s D : ℝ} {f g : ℕ → ℝ} (hs : 0<s) (g0 : g 0=0)
    (difference : ∀ᶠ n : ℕ in atTop,|f n-g n| ≤ D*(n:ℝ)^s) (h : PrefixPower s f) : PrefixPower s g := by
  obtain ⟨C,_,cap⟩ := h
  apply prefixPower_of_eventual (C := C+D) g0 hs
  filter_upwards [difference] with n dn
  have tri := abs_sub (f n) (f n-g n)
  rw [sub_sub_cancel] at tri
  exact tri.trans ((add_le_add (cap n) dn).trans_eq (add_mul ..).symm)

/-- At each exponent above one half the centered rough reading has exactly
the power bound of the corrected reading on cofactors through the hyperbola. -/
theorem centered_bound_iff_below_the_hyperbola {ε : ℝ} (hε : 0<ε) :
    PrefixPower (1/2+ε) centered ↔ PrefixPower (1/2+ε) primePowerReadingBelowTheHyperbola := by
  have pos : 0<(1:ℝ)/2+ε := by linarith only [hε]
  have c0 : centered 0=0 := by simp [centered,centeredPrimePowerRemainder,RoughReading.freeSet]
  have i0 : primePowerReadingBelowTheHyperbola 0=0 := by simp [primePowerReadingBelowTheHyperbola,roughInteriorReading]
  refine ⟨transfer_estimate pos i0 (difference_price hε),transfer_estimate (D := 1/ε+1) pos c0 ?_⟩
  filter_upwards [difference_price hε] with n hn
  rwa [abs_sub_comm] at hn

/-- The full Mertens half-plus criterion is equivalent to one arithmetic
reading involving only cofactors m ≤ X/(floor(sqrt X)+1). -/
theorem mertens_criterion_below_the_hyperbola :
    (∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) primePowerReadingBelowTheHyperbola) ↔
      ∀ ε : ℝ,0<ε → PrefixPower (1/2+ε) (coprimeMoebiusSum 1) := by
  rw [←square_root_iff_one_centered_prime_power_reading]
  exact ⟨fun h ε hp => (centered_bound_iff_below_the_hyperbola hp).mpr (h ε hp),
    fun h ε hp => (centered_bound_iff_below_the_hyperbola hp).mp (h ε hp)⟩

#print axioms centered_reading_after_rough_interpolation
#print axioms signed_flux_of_the_corrected_interior
#print axioms interior_reads_the_logarithmic_tail
#print axioms both_prime_readings_below_the_hyperbola
#print axioms mertens_criterion_below_the_hyperbola

end GaloisForLFunctions.RestrictedFactorizationCalculus
