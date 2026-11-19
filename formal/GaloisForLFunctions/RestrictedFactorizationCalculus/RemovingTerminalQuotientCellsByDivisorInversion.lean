import GaloisForLFunctions.RestrictedFactorizationCalculus.SignedFluxOnGrowingQuotientRanges
import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiMobiusDivisorDilationChannels
import GaloisForLFunctions.RHTower.RouteECofactorSquarefreeHarmonic

/-!
# Paying the terminal quotient cells by divisor inversion

The summatory function of an arithmetic weight agrees at all t ≤ T
with a finite combination of quotient floors. Summed against the rough
Möbius function each floor counts smooth integers. Its full signed
price includes the changes at smaller cofactors as well as the band
where this interpolation cancels the reading exactly.
-/

noncomputable section
open Finset ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta
open GaloisForLFunctions.BezoutValuationIncidence
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev smoothCount (y N : ℕ) : ℝ := (RHTower.Sieve.smoothUpTo (Nat.primesLE y) N).card

/-- The summatory function of the quotient increments. -/
def quotientReading (a : ArithmeticFunction ℝ) (t : ℕ) := ∑ q ∈ Icc 1 t,a q

/-- Coefficients of the unique complete expansion in quotient floors. -/
def quotientFloorCoefficients (a : ArithmeticFunction ℝ) := a*(μ : ArithmeticFunction ℝ)

/-- Truncating the divisor coefficients gives the same reading through T. -/
def interpolatedQuotientFloor (a : ArithmeticFunction ℝ) (T t : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 T,quotientFloorCoefficients a d*((t/d:ℕ):ℝ)

/-- The exact response before any cofactor is removed. -/
def roughCofactorReading (y X : ℕ) (w : ℕ → ℝ) :=
  ∑ m ∈ Icc 1 X,RoughReading.row y m*w (X/m)

/-- The complete cofactor reading is a signed response through the
actual quotient walls of the same sharp prefix. -/
theorem rough_cofactor_reading_as_a_quotient_boundary (a : ArithmeticFunction ℝ) (y X : ℕ) :
    roughCofactorReading y X (quotientReading a)=
      quotientBoundary (coprimeMoebiusSum (primorial y)) (Icc 1 X) a 0 X := by
  unfold roughCofactorReading quotientReading
  simp only [mul_sum]
  rw [RHTower.sum_hyperbola_swap_real X (fun m q => RoughReading.row y m*a q)]
  unfold quotientBoundary
  apply sum_congr rfl
  intro q _
  simp only [Nat.zero_div,coprimeMoebiusSum,Icc_eq_empty_of_lt (by decide : (0:ℕ)<1),sum_empty,
    sub_zero,mul_sum]
  exact sum_congr rfl (fun m hm => by
    rw [primorial_indicator_eq_deleted_mobius y m (mem_Icc.mp hm).1,mul_comm])

/-- Dirichlet inversion simultaneously interpolates all integer readings
up to T, including empty and coincident quotient cells. -/
theorem exact_interpolation_on_terminal_quotients (a : ArithmeticFunction ℝ) {t T : ℕ}
    (below : t ≤ T) : quotientReading a t=interpolatedQuotientFloor a T t := by
  let c := quotientFloorCoefficients a
  have recover : c*(ζ : ArithmeticFunction ℝ)=a := by
    simp only [c,quotientFloorCoefficients,mul_assoc,coe_moebius_mul_coe_zeta,mul_one]
  have per (n : ℕ) : a n=∑ v ∈ n.divisorsAntidiagonal,c v.1 := by
    rw [Nat.sum_divisorsAntidiagonal (fun d _ => c d),←coe_mul_zeta_apply,recover]
  calc quotientReading a t = ∑ n ∈ Icc 1 t,∑ v ∈ n.divisorsAntidiagonal,c v.1 :=
           sum_congr rfl (fun n _ => per n)
       _ = ∑ d ∈ Icc 1 t,∑ _k ∈ Icc 1 (t/d),c d :=
           RHTower.Sieve.sum_Icc_divisorsAntidiagonal_swap (fun d _ => c d) t
       _ = ∑ d ∈ Icc 1 t,c d*((t/d:ℕ):ℝ) := by simp [mul_comm]
       _ = interpolatedQuotientFloor a T t := by
           apply sum_subset (Icc_subset_Icc_right below)
           intro d hd outside
           have dt : t<d := by
             by_contra! no
             exact outside (mem_Icc.mpr ⟨(mem_Icc.mp hd).1,no⟩)
           rw [Nat.div_eq_of_lt dt,Nat.cast_zero,mul_zero]

private theorem rough_floor_at_integer (y Z : ℕ) :
    (∑ m ∈ Icc 1 Z,RoughReading.row y m*((Z/m:ℕ):ℝ))=smoothCount y Z := by
  have h := smooth_population_as_a_rough_floor_sum y (Z:ℝ) (Nat.cast_nonneg _)
  rw [Nat.floor_natCast] at h
  have floor (m : ℕ) : (⌊(Z:ℝ)/m⌋:ℝ)=((Z/m:ℕ):ℝ) := by
    rw [←natCast_floor_eq_intCast_floor (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      Nat.floor_div_natCast,Nat.floor_natCast]
  rw [←h]
  simp only [floor,RoughReading.freeSet,sum_filter]
  apply sum_congr rfl
  intro m _
  by_cases h : IsFree (RoughReading.banned y) m
  · rw [if_pos h]
  · rw [if_neg h,RoughReading.row_value,if_neg h,zero_mul]

private theorem one_floor_price (y X d : ℕ) :
    roughCofactorReading y X (fun t => ((t/d:ℕ):ℝ))=smoothCount y (X/d) := by
  rw [←rough_floor_at_integer]
  unfold roughCofactorReading
  have exch (m : ℕ) : X/m/d=X/d/m := by rw [Nat.div_div_eq_div_mul,Nat.mul_comm,Nat.div_div_eq_div_mul]
  simp only [exch]
  symm
  apply sum_subset (Icc_subset_Icc_right (Nat.div_le_self X d))
  intro m hm outside
  have past : X/d<m := by
    by_contra! no
    exact outside (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,no⟩)
  rw [Nat.div_eq_of_lt past,Nat.cast_zero,mul_zero]

/-- Exact total expenditure on all cofactors when the center changes. -/
def smoothInterpolationPrice (a : ArithmeticFunction ℝ) (y X T : ℕ) :=
  ∑ d ∈ Icc 1 T,quotientFloorCoefficients a d*smoothCount y (X/d)

theorem signed_price_of_the_interpolated_center (a : ArithmeticFunction ℝ) (y X T : ℕ) :
    roughCofactorReading y X (interpolatedQuotientFloor a T)=smoothInterpolationPrice a y X T := by
  unfold roughCofactorReading interpolatedQuotientFloor smoothInterpolationPrice
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  rw [←one_floor_price]
  unfold roughCofactorReading
  rw [mul_sum]
  exact sum_congr rfl (fun m _ => by ring)

/-- The surviving cofactor reading after eliminating all quotients through T. -/
def interiorQuotientReading (a : ArithmeticFunction ℝ) (y X T : ℕ) : ℝ :=
  ∑ m ∈ Icc 1 (X/(T+1)),RoughReading.row y m*
    (quotientReading a (X/m)-interpolatedQuotientFloor a T (X/m))

/-- Every terminal quotient cell vanishes. The displayed smooth price
includes all changes to the arithmetic reading on the surviving cells. -/
theorem eliminating_the_terminal_quotient_cells (a : ArithmeticFunction ℝ) (y X T : ℕ) :
    roughCofactorReading y X (quotientReading a)=
      interiorQuotientReading a y X T+smoothInterpolationPrice a y X T := by
  rw [←signed_price_of_the_interpolated_center,←sub_eq_iff_eq_add]
  unfold roughCofactorReading interiorQuotientReading
  rw [←sum_sub_distrib]
  simp only [←mul_sub]
  symm
  apply sum_subset (Icc_subset_Icc_right (Nat.div_le_self ..))
  intro m hm outside
  have past : X/(T+1)<m := by
    by_contra! no
    exact outside (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,no⟩)
  have small : X/m<T+1 := (Nat.div_lt_iff_lt_mul (mem_Icc.mp hm).1).mpr (by
    simpa only [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul (Nat.succ_pos T)).mp past)
  rw [exact_interpolation_on_terminal_quotients a (Nat.le_of_lt_succ small),sub_self,mul_zero]

/-- Every selection or signed modulation of Mangoldt increments has
floor coefficients bounded by log d, independently of its prime wall. -/
theorem interpolating_coefficients_le_log {a : ArithmeticFunction ℝ} (dom : ∀ n,|a n| ≤ vonMangoldt n) (d : ℕ) :
    |quotientFloorCoefficients a d| ≤ Real.log d := by
  rw [quotientFloorCoefficients,mul_apply,Nat.sum_divisorsAntidiagonal,←vonMangoldt_sum (n := d)]
  apply (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun q _ => ?_))
  rw [abs_mul,intCoe_apply]
  have small : |(μ (d/q):ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one (n := d/q)
  exact (mul_le_mul_of_nonneg_left small (abs_nonneg _)).trans ((mul_one _).le.trans (dom q))

/-- Replacing a whole terminal band at either sharp endpoint costs at most
2 E_{1/2}(y) sqrt(XT) log T for every Mangoldt-dominated weight. -/
theorem cost_of_eliminating_a_growing_quotient_band {a : ArithmeticFunction ℝ}
    (dom : ∀ n,|a n| ≤ vonMangoldt n) (y X T : ℕ) :
    |smoothInterpolationPrice a y X T| ≤
      (Real.log T*Real.sqrt X*deletionPrice (1/2) y)*(2*Real.sqrt T) := by
  let H := Real.log T*Real.sqrt X*deletionPrice (1/2) y
  have e0 := zero_le_one.trans (deletionPrice_one_le (by norm_num : 0<(1/2:ℝ)) y)
  have h0 : 0 ≤ H := mul_nonneg (mul_nonneg (Real.log_natCast_nonneg _) (Real.sqrt_nonneg _)) e0
  have per (d : ℕ) (hd : d ∈ Icc 1 T) :
      |quotientFloorCoefficients a d*smoothCount y (X/d)| ≤ H*(Real.sqrt d)⁻¹ := by
    have dp := (mem_Icc.mp hd).1
    have d0 : 0<(d:ℝ) := Nat.cast_pos.mpr dp
    have coef := (interpolating_coefficients_le_log dom d).trans
      (Real.log_le_log d0 (Nat.cast_le.mpr (mem_Icc.mp hd).2))
    have count := smooth_population_le_deletion_price (by norm_num : 0<(1/2:ℝ)) y (X/d)
    rw [←Real.sqrt_eq_rpow] at count
    have frac : ((X/d:ℕ):ℝ) ≤ (X:ℝ)/d := (le_div_iff₀ d0).mpr (by exact_mod_cast Nat.div_mul_le_self X d)
    have sq := Real.sqrt_le_sqrt frac
    rw [Real.sqrt_div (Nat.cast_nonneg _)] at sq
    have room := count.trans (mul_le_mul_of_nonneg_right sq e0)
    rw [abs_mul,abs_of_nonneg (show 0 ≤ smoothCount y (X/d) from Nat.cast_nonneg _)]
    exact (mul_le_mul coef room (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)).trans_eq (by dsimp only [H]; ring)
  apply (abs_sum_le_sum_abs ..).trans ((sum_le_sum per).trans ?_)
  rw [←mul_sum]
  exact mul_le_mul_of_nonneg_left (RHTower.Sieve.sum_sqrtInv_le T) h0

#print axioms rough_cofactor_reading_as_a_quotient_boundary
#print axioms eliminating_the_terminal_quotient_cells
#print axioms cost_of_eliminating_a_growing_quotient_band

end GaloisForLFunctions.RestrictedFactorizationCalculus
