import GaloisForLFunctions.RHTower.PMPowerDampedMobiusFiniteDeletion
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogRecursion
import GaloisForLFunctions.RHTower.Sieve.SmoothSum
import GaloisForLFunctions.RHTower.PrimeWindowLogPowerCount
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheRemainderOfThePrimeNumberTheoremHasLogarithmicMomentsOnATail
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheExplicitLogSquareRoughSet

/-!
# The smooth population in a signed rough prefix

Deleting the small primes in the logarithmic Möbius identity gives a
sum of prime-power readings at the sharp quotient endpoints. Replacing
a reading by its length produces the ordinary count of smooth integers
at X/y. The floor and lower-wall costs are supported on rough cofactors.
-/

noncomputable section

open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Classical ArithmeticFunction.Moebius
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev banned (y : ℕ) : Set ℕ := {p | p ≤ y}
private abbrev row (y n : ℕ) : ℝ := (mobiusAF (banned y) n : ℝ)
private abbrev freeSet (y X : ℕ) := (Icc 1 X).filter (IsFree (banned y))

private theorem row_value (y n : ℕ) :
    row y n=if IsFree (banned y) n then (μ n:ℝ) else 0 := by
  by_cases h : IsFree (banned y) n <;> simp [row,mobiusAF,pmul_apply,freeAF_apply,h]

private theorem prefix_eq_frozen_row (y X : ℕ) :
    coprimeMoebiusSum (primorial y) X=∑ n ∈ Icc 1 X,row y n := by
  apply sum_congr rfl
  intro n hn
  have pos := (mem_Icc.mp hn).1
  have eq : (primorial y).Coprime n ↔ IsFree (banned y) n := by
    constructor
    · intro h
      refine ⟨pos.ne',fun p hp small => ?_⟩
      have prime := Nat.prime_of_mem_primeFactors hp
      exact prime.not_dvd_one (h ▸ Nat.dvd_gcd (prime.dvd_primorial_iff.mpr small) (Nat.dvd_of_mem_primeFactors hp))
    · intro h
      exact RHTower.coprime_primorial_of_primeFactors_gt pos (fun p hp => lt_of_not_ge (h.2 p hp))
  rw [coprimeMoebiusIndicator,row_value,eq]

/-- Logarithmically weighted prime powers avoiding all primes through y. -/
def roughPrimePowerReading (y x : ℕ) : ℝ :=
  ∑ d ∈ freeSet y x,vonMangoldt d

private theorem short_reading {y x : ℕ} (hx : x ≤ y) : roughPrimePowerReading y x=0 := by
  apply sum_eq_zero
  intro d hd
  obtain ⟨hi,free⟩ := mem_filter.mp hd
  have small := (mem_Icc.mp hi).2.trans hx
  by_cases unit : d=1
  · simp [unit]
  have prime := Nat.minFac_prime unit
  have hp : d.minFac ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨prime,Nat.minFac_dvd _,free.1⟩
  exact (free.2 _ hp ((Nat.le_of_dvd (mem_Icc.mp hi).1 (Nat.minFac_dvd d)).trans small)).elim

private theorem log_row (y n : ℕ) :
    row y n*Real.log n= -∑ d ∈ n.divisorsAntidiagonal,
      row y d.1*(if IsFree (banned y) d.2 then vonMangoldt d.2 else 0) := by
  have iden := congrArg (fun f : ArithmeticFunction ℝ => f n) RHTower.Sieve.moebius_pmul_log
  rw [mul_comm (vonMangoldt : ArithmeticFunction ℝ)] at iden
  simp only [pmul_apply,intCoe_apply,log_apply,ArithmeticFunction.neg_apply,mul_apply] at iden
  have split (v : ℕ × ℕ) (hv : v ∈ n.divisorsAntidiagonal) :
      IsFree (banned y) n ↔ IsFree (banned y) v.1 ∧ IsFree (banned y) v.2 := by
    obtain ⟨eq,n0⟩ := Nat.mem_divisorsAntidiagonal.mp hv
    have nz : v.1*v.2 ≠ 0 := eq ▸ n0
    rw [←eq,isFree_mul_iff _ (mul_ne_zero_iff.mp nz).1 (mul_ne_zero_iff.mp nz).2]
  by_cases good : IsFree (banned y) n
  · rw [row_value,if_pos good,iden]
    congr 1
    apply sum_congr rfl
    intro v hv
    obtain ⟨a,b⟩ := (split v hv).mp good
    rw [row_value,if_pos a,if_pos b]
  · rw [row_value,if_neg good,zero_mul]
    symm
    apply neg_eq_zero.mpr
    apply sum_eq_zero
    intro v hv
    rw [row_value]
    by_cases a : IsFree (banned y) v.1
    · have b : ¬ IsFree (banned y) v.2 := fun b => good ((split v hv).mpr ⟨a,b⟩)
      simp only [if_neg b,mul_zero]
    · simp only [if_neg a,zero_mul]

/-- Exact logarithmic summation over the surviving cofactors m≤X/y. -/
theorem logarithmic_rough_prefix_at_quotient_readings {y : ℕ} (hy : 0<y) (X : ℕ) :
    (∑ n ∈ Icc 1 X,row y n*Real.log n)=
      -∑ m ∈ freeSet y (X/y),row y m*roughPrimePowerReading y (X/m) := by
  rw [sum_congr rfl (fun n _ => log_row y n),sum_neg_distrib,
    RHTower.Sieve.sum_Icc_divisorsAntidiagonal_swap]
  congr 1
  let f := fun m : ℕ => row y m*roughPrimePowerReading y (X/m)
  have inner (m : ℕ) : (∑ d ∈ Icc 1 (X/m),row y m*
      (if IsFree (banned y) d then vonMangoldt d else 0))=f m := by
    rw [←mul_sum]; simp only [f,roughPrimePowerReading,freeSet,sum_filter]
  rw [sum_congr rfl (fun m _ => inner m)]
  symm
  apply sum_subset ((filter_subset ..).trans (Icc_subset_Icc_right (Nat.div_le_self ..)))
  intro m hm outside
  have lo := (mem_Icc.mp hm).1
  by_cases late : X/y<m
  · have ym := (Nat.div_lt_iff_lt_mul hy).mp late
    have small : X/m<y := (Nat.div_lt_iff_lt_mul lo).mpr (by rwa [mul_comm])
    simp only [f,short_reading small.le,mul_zero]
  · have early := mem_Icc.mpr ⟨lo,le_of_not_gt late⟩
    have absent : ¬IsFree (banned y) m := fun h => outside (mem_filter.mpr ⟨early,h⟩)
    simp only [f,row_value,if_neg absent,zero_mul]

private theorem round_smooth_count (y : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    |(∑ m ∈ freeSet y ⌊t⌋₊,row y m*(t/m))-
      ((RHTower.Sieve.smoothUpTo (Nat.primesLE y) ⌊t⌋₊).card:ℝ)| ≤ (freeSet y ⌊t⌋₊).card := by
  let S := RHTower.Sieve.smoothUpTo (Nat.primesLE y) ⌊t⌋₊
  have eq := RHTower.pm_deleted_mobius_floor_sum (banned y) ht (le_refl ⌊t⌋₊)
  have count : (∑ n ∈ Icc 1 ⌊t⌋₊,((smoothAF (banned y) n:ℤ):ℝ))=(S.card:ℝ) := by
    rw [show S=(Icc 1 ⌊t⌋₊).filter (fun n => n.primeFactors ⊆ Nat.primesLE y) from rfl,←sum_boole]
    apply sum_congr rfl
    intro n hn
    have test : IsSmooth (banned y) n ↔ n.primeFactors ⊆ Nat.primesLE y :=
      ⟨fun h p hp => Nat.mem_primesLE.mpr ⟨h.2 p hp,Nat.prime_of_mem_primeFactors hp⟩,
       fun h => ⟨(mem_Icc.mp hn).1.ne',fun p hp => (Nat.mem_primesLE.mp (h hp)).1⟩⟩
    by_cases h : IsSmooth (banned y) n <;> simp [smoothAF_apply,h,←test]
  have realEq : (∑ m ∈ Icc 1 ⌊t⌋₊,row y m*(⌊t/m⌋:ℝ))=
      ∑ n ∈ Icc 1 ⌊t⌋₊,((smoothAF (banned y) n:ℤ):ℝ) := by exact_mod_cast eq
  have floorEq : (∑ m ∈ freeSet y ⌊t⌋₊,row y m*(⌊t/m⌋:ℝ))=(S.card:ℝ) := by
    rw [←count,←realEq]
    apply sum_subset (filter_subset ..)
    intro n hn out
    rw [row_value,if_neg (fun h => out (mem_filter.mpr ⟨hn,h⟩)),zero_mul]
  change |_-(S.card:ℝ)| ≤ _
  rw [←floorEq,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  apply (sum_le_sum (g := fun _ => (1:ℝ)) ?_).trans_eq (by simp)
  intro m hm
  rw [←mul_sub,abs_mul,row_value,if_pos (mem_filter.mp hm).2,
    abs_of_nonneg (sub_nonneg.mpr (Int.floor_le _))]
  have bound : |(μ m:ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := m))
  have dist : t/(m:ℝ)-(⌊t/m⌋:ℝ) ≤ 1 := by linarith only [Int.lt_floor_add_one (t/(m:ℝ))]
  exact mul_le_one₀ bound (sub_nonneg.mpr (Int.floor_le _)) dist

/-- The signed rough prefix, with the smooth main term already removed.
The first error is the variation of the logarithmic weight. The second
is the prime-power error at the actual quotient endpoints. The last
counts the only cofactors at which rounding or the lower wall can cost. -/
theorem smooth_main_term_error_at_every_rough_cutoff {y : ℕ} (hy : 0<y) (X : ℕ) :
    |Real.log X*(∑ n ∈ Icc 1 X,row y n)+
      (y:ℝ)*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) (X/y)).card| ≤
      (∑ n ∈ freeSet y X,(Real.log X-Real.log n))+
      (∑ m ∈ freeSet y (X/y),|roughPrimePowerReading y (X/m)-((X:ℝ)/m-y)|)+
      2*(y:ℝ)*(freeSet y (X/y)).card := by
  let A := freeSet y X
  let B := freeSet y (X/y)
  let t := (X:ℝ)/y
  let S := RHTower.Sieve.smoothUpTo (Nat.primesLE y) (X/y)
  let L := ∑ n ∈ Icc 1 X,row y n*Real.log n
  let M := ∑ n ∈ Icc 1 X,row y n
  let D := ∑ m ∈ B,row y m*((X:ℝ)/m)
  have y0 : (0:ℝ)<y := Nat.cast_pos.mpr hy
  have norm (n : ℕ) : |row y n| ≤ 1 := by
    rw [row_value]; split
    · exact_mod_cast abs_moebius_le_one (n := n)
    · norm_num
  have weighted : |Real.log X*M-L| ≤ ∑ n ∈ A,(Real.log X-Real.log n) := by
    dsimp only [M,L]
    rw [mul_sum,←sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    rw [show A=(Icc 1 X).filter (IsFree (banned y)) from rfl,sum_filter]
    apply sum_le_sum
    intro n hn
    by_cases free : IsFree (banned y) n
    · rw [if_pos free,mul_comm (Real.log X),←mul_sub,abs_mul]
      have lo := Nat.cast_pos.mpr (mem_Icc.mp hn).1
      have hi := (Nat.cast_le (α := ℝ)).mpr (mem_Icc.mp hn).2
      have diff := sub_nonneg.mpr (Real.log_le_log lo hi)
      rw [abs_of_nonneg diff]
      exact (mul_le_mul_of_nonneg_right (norm n) diff).trans_eq (one_mul _)
    · simp only [row_value,if_neg free,mul_zero,zero_mul,sub_self,abs_zero,le_refl]
  let E := ∑ m ∈ B,|roughPrimePowerReading y (X/m)-((X:ℝ)/m-y)|
  have primeErr : |L+D| ≤ E+(y:ℝ)*B.card := by
    have l := logarithmic_rough_prefix_at_quotient_readings hy X
    change L= -∑ m ∈ B,row y m*roughPrimePowerReading y (X/m) at l
    rw [l,neg_add_eq_sub,D,←sum_sub_distrib]
    apply (abs_sum_le_sum_abs ..).trans
    have per (m : ℕ) (_ : m ∈ B) : |row y m*((X:ℝ)/m)-row y m*roughPrimePowerReading y (X/m)| ≤
        |roughPrimePowerReading y (X/m)-((X:ℝ)/m-y)|+(y:ℝ) := by
      rw [←mul_sub,abs_mul]
      apply (mul_le_mul_of_nonneg_right (norm m) (abs_nonneg _)).trans
      rw [one_mul,abs_sub_comm]
      have hh := abs_sub_le (roughPrimePowerReading y (X/m)) ((X:ℝ)/m-y) ((X:ℝ)/m)
      simpa only [sub_sub_cancel_left,abs_neg,abs_of_nonneg y0.le] using hh
    exact (sum_le_sum per).trans_eq (by simp only [sum_add_distrib,sum_const,nsmul_eq_mul,E,mul_comm (B.card:ℝ)])
  have floor := round_smooth_count y t (div_nonneg (Nat.cast_nonneg X) y0.le)
  have ft : ⌊t⌋₊=X/y := by simp [t,Nat.floor_div_natCast]
  rw [ft] at floor
  have rwD : (y:ℝ)*(∑ m ∈ B,row y m*(t/m))=D := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    dsimp only [t]
    field_simp [y0.ne',(Nat.cast_pos.mpr (mem_Icc.mp (mem_filter.mp hm).1).1 : (0:ℝ)<m).ne']
  have round := mul_le_mul_of_nonneg_left floor y0.le
  change (y:ℝ)*|(∑ m ∈ B,row y m*(t/m))-(S.card:ℝ)| ≤ _ at round
  have mult (v : ℝ) : (y:ℝ)*|v|=|(y:ℝ)*v| := by rw [abs_mul,abs_of_nonneg y0.le]
  rw [mult] at round
  rw [mul_sub,rwD] at round
  have sumerr := abs_add_le (Real.log X*M-L) (L+D)
  have allerr := abs_add_le (Real.log X*M+D) ((y:ℝ)*S.card-D)
  rw [show Real.log X*M-L+(L+D)=Real.log X*M+D by ring] at sumerr
  rw [show Real.log X*M+D+(y*S.card-D)=Real.log X*M+y*S.card by ring,abs_sub_comm ((y:ℝ)*S.card)] at allerr
  change |Real.log X*M+(y:ℝ)*S.card| ≤ _+E+2*(y:ℝ)*B.card
  linarith only [weighted,primeErr,round,sumerr,allerr]

private theorem reading_between_prime_sums (y : ℕ) {t : ℝ} (hy : (y:ℝ) ≤ t) :
    Chebyshev.theta t-Chebyshev.theta y ≤ roughPrimePowerReading y ⌊t⌋₊ ∧
      roughPrimePowerReading y ⌊t⌋₊ ≤ Chebyshev.psi t-Chebyshev.psi y := by
  let J := Ioc y ⌊t⌋₊
  have yy := Nat.le_floor hy
  let g := fun d : ℕ => if IsFree (banned y) d then vonMangoldt d else 0
  have full (N : ℕ) : roughPrimePowerReading y N=∑ d ∈ Ioc 0 N,g d := by
    have interval : Icc 1 N=Ioc 0 N := by ext d; simp only [mem_Icc,mem_Ioc]; omega
    simp only [roughPrimePowerReading,freeSet,sum_filter,g,interval]
  have split (f : ℕ → ℝ) :
      (∑ d ∈ Ioc 0 ⌊t⌋₊,f d)-(∑ d ∈ Ioc 0 y,f d)=∑ d ∈ J,f d := by
    have h := sum_Ioc_consecutive f (Nat.zero_le y) yy
    change _+(∑ d ∈ J,f d)=_ at h
    linarith only [h]
  have read := split g
  rw [←full,←full,short_reading (le_refl y),sub_zero] at read
  rw [read]
  simp only [Chebyshev.theta,Chebyshev.psi,Nat.floor_natCast,sum_filter,split]
  constructor
  · apply sum_le_sum
    intro d hd
    by_cases prime : d.Prime
    · have free := (isFree_prime (banned y) prime).mpr (not_le.mpr (mem_Ioc.mp hd).1)
      rw [if_pos prime,g,if_pos free,vonMangoldt_apply_prime prime]
    · rw [if_neg prime,g]; split <;> first | exact vonMangoldt_nonneg | exact le_rfl
  · apply sum_le_sum
    intro d _
    dsimp only [g]; split <;> first | exact le_rfl | exact vonMangoldt_nonneg

private theorem uniform_prime_reading_error :
    ∃ C : ℝ,0<C ∧ ∃ Y : ℕ,4 ≤ Y ∧ ∀ y : ℕ,Y ≤ y → ∀ t : ℝ,(y:ℝ) ≤ t →
      |roughPrimePowerReading y ⌊t⌋₊-(t-y)| ≤ C*(t/Real.log t^2+y/Real.log y^2) := by
  obtain ⟨A,hA,T,hT,theta⟩ := RHTower.PrimeCells.exists_abs_theta_sub_le 2
  obtain ⟨B,hB,psi⟩ := AbsoluteGeometryOfSpecZ.exists_abs_sub_psi_mul_log_pow_le 0
  let C := A+B
  let Y := max 4 ⌈T⌉₊
  have cpos : 0<C := add_pos_of_pos_of_nonneg hA hB
  refine ⟨C,cpos,Y,le_max_left ..,?_⟩
  intro y hy t ht
  have tY : T ≤ (y:ℝ) := (Nat.le_ceil T).trans (Nat.cast_le.mpr ((le_max_right ..).trans hy))
  have bounds (u : ℝ) (hu : T ≤ u) :
      |Chebyshev.theta u-u| ≤ C*(u/Real.log u^2) ∧ |Chebyshev.psi u-u| ≤ C*(u/Real.log u^2) := by
    have pos : 1<u := by linarith only [hT,hu]
    have ul := Real.log_pos pos
    have nonneg : 0 ≤ u/Real.log u^2 := by positivity
    constructor
    · exact (theta u hu).trans ((le_of_eq (mul_div_assoc ..)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB) nonneg))
    · have hh := psi u pos.le
      simp only [pow_zero,mul_one,abs_sub_comm u] at hh
      have l2 : Real.log u^2 ≤ (1+Real.log u)^2 := by nlinarith only [ul.le]
      have smaller := (mul_le_mul_of_nonneg_left l2 (abs_nonneg (Chebyshev.psi u-u))).trans hh
      rw [mul_div_assoc',le_div_iff₀ (sq_pos_of_pos ul)]
      exact smaller.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) (zero_lt_one.trans pos).le)
  obtain ⟨a,b⟩ := bounds t (tY.trans ht)
  obtain ⟨d,e⟩ := bounds y tY
  have h := reading_between_prime_sums y ht
  rw [abs_le]
  constructor
  · linarith only [h.1,(abs_le.mp a).1,(abs_le.mp d).2]
  · linarith only [h.2,(abs_le.mp b).2,(abs_le.mp e).1]

/-- The reciprocal-log-square prime error summed across all quotient
endpoints. The potential 1/log(x/m) telescopes one integer at a time. -/
private theorem sum_quotient_log_errors {x : ℝ} {N : ℕ} (room : (N:ℝ)+1<x) :
    (∑ m ∈ Icc 1 N,1/((m:ℝ)*(Real.log (x/m))^2)) ≤
      2/Real.log (x/((N:ℝ)+1)) := by
  let pot := fun m : ℕ => 1/Real.log (x/m)
  have step (m : ℕ) (hm : m ∈ Icc 1 N) :
      1/((m:ℝ)*(Real.log (x/m))^2) ≤ 2*(pot (m+1)-pot m) := by
    have m1 : (1:ℝ) ≤ m := Nat.one_le_cast.mpr (mem_Icc.mp hm).1
    have mp : (0:ℝ)<m := zero_lt_one.trans_le m1
    have upper := (Nat.cast_le (α := ℝ)).mpr (mem_Icc.mp hm).2
    have mx : (m:ℝ)+1<x := lt_of_le_of_lt (by linarith only [upper]) room
    have mx0 : (0:ℝ)<(m:ℝ)+1 := by positivity
    have x0 := mx0.trans mx
    let a := Real.log (x/m)
    let b := Real.log (x/((m:ℝ)+1))
    have bpos : 0<b := Real.log_pos ((one_lt_div mx0).mpr mx)
    have order : b ≤ a := Real.log_le_log (div_pos x0 mx0)
      (div_le_div_of_nonneg_left x0.le mp (by linarith))
    have apos := bpos.trans_le order
    have changeLog : a-b= -Real.log ((m:ℝ)/(m+1)) := by
      simp only [a,b,Real.log_div x0.ne' mp.ne',Real.log_div x0.ne' mx0.ne',Real.log_div mp.ne' mx0.ne']
      ring
    have gap : 1/((m:ℝ)+1) ≤ a-b := by
      have logbound := Real.log_le_sub_one_of_pos (div_pos mp mx0)
      rw [changeLog]
      have rational : (m:ℝ)/(m+1)-1= -(1/(m+1)) := by field_simp; ring
      rw [rational] at logbound
      linarith only [logbound]
    have whole := (div_le_iff₀ mx0).mp gap
    have one : (1:ℝ) ≤ 2*m*(a-b) :=
      whole.trans (by nlinarith only [mul_le_mul_of_nonneg_right m1 (sub_nonneg.mpr order)])
    have numer : b ≤ 2*m*(a-b)*a := order.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right one apos.le)
    change 1/((m:ℝ)*a^2) ≤ 2*(1/Real.log (x/((m+1:ℕ):ℝ))-1/a)
    rw [Nat.cast_add,Nat.cast_one]
    change 1/((m:ℝ)*a^2) ≤ 2*(1/b-1/a)
    field_simp [mp.ne',bpos.ne',apos.ne',mp,bpos,apos]
    nlinarith only [numer]
  have telescope (k : ℕ) : (∑ m ∈ Icc 1 k,(pot (m+1)-pot m))=pot (k+1)-pot 1 := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_Icc_succ_top (by omega),ih]; ring
  have cost := sum_le_sum step
  rw [←mul_sum,telescope] at cost
  have first : 0 ≤ pot 1 := by
    dsimp only [pot]; rw [Nat.cast_one,div_one]
    exact one_div_nonneg.mpr (Real.log_nonneg (by linarith only [room,Nat.cast_nonneg N]))
  have last : pot (N+1)=1/Real.log (x/((N:ℝ)+1)) := by simp only [pot,Nat.cast_succ]
  rw [last] at cost
  linarith only [cost,first]

private def logVariation (y N : ℕ) : ℝ :=
  ∑ n ∈ freeSet y N,(Real.log N-Real.log n)

private theorem uniform_rough_count_and_variation {δ : ℝ} (hδ : 0<δ) :
    ∃ Z : ℕ,∃ K : ℝ,0 ≤ K ∧ ∀ y : ℕ,Z ≤ y → ∀ N : ℕ,
      ((freeSet y N).card:ℝ) ≤ δ*N+K ∧ logVariation y N ≤ δ*N+K*Real.log N := by
  obtain ⟨Z,hZ⟩ := (RHTower.WeilSingularArithmetic.tendsto_coprimeDensity_primorial.eventually_lt_const hδ).exists
  let Q := primorial Z
  have qp : 0<Q := primorial_pos _
  haveI : NeZero Q := ⟨qp.ne'⟩
  change RHTower.WeilSingularArithmetic.coprimeDensity Q<δ at hZ
  rw [RHTower.WeilSingularArithmetic.coprimeDensity_eq_totient_div] at hZ
  let K : ℝ := Q.totient
  refine ⟨Z,K,Nat.cast_nonneg _,?_⟩
  intro y zy
  have count (N : ℕ) : ((freeSet y N).card:ℝ) ≤ δ*N+K := by
    have sub : freeSet y N ⊆ (Icc 1 N).filter (fun n => Q.Coprime n) := by
      intro n hn
      obtain ⟨hi,free⟩ := mem_filter.mp hn
      exact mem_filter.mpr ⟨hi,RHTower.coprime_primorial_of_primeFactors_gt (mem_Icc.mp hi).1
        (fun p hp => zy.trans_lt (lt_of_not_ge (free.2 p hp)))⟩
    have total := ((Nat.cast_le (α := ℝ)).mpr (card_le_card sub)).trans (coprime_population_in_a_prefix Q qp N)
    have eq : (Q.totient:ℝ)*((N:ℝ)/Q+1)=((Q.totient:ℝ)/Q)*N+K := by dsimp only [K]; ring
    rw [eq] at total
    exact total.trans (add_le_add (mul_le_mul_of_nonneg_right hZ.le (Nat.cast_nonneg N)) le_rfl)
  intro N
  refine ⟨count N,?_⟩
  induction N with
  | zero => simp [logVariation,freeSet]
  | succ N ih =>
    by_cases nz : N=0
    · subst N
      simp [logVariation,freeSet,hδ.le]
    have np : (0:ℝ)<N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero nz)
    let d := Real.log ((N:ℝ)+1)-Real.log N
    have dn : 0 ≤ d := sub_nonneg.mpr (Real.log_le_log np (by linarith))
    have logbound := Real.log_le_sub_one_of_pos (div_pos (by positivity : 0<(N:ℝ)+1) np)
    rw [Real.log_div (by positivity : (N:ℝ)+1 ≠ 0) np.ne'] at logbound
    have cost : (N:ℝ)*d ≤ 1 := by
      have algebra : ((N:ℝ)+1)/N-1=1/N := by field_simp
      rw [algebra] at logbound
      exact (mul_comm ..).trans_le ((le_div_iff₀ np).mp logbound)
    have change_ : logVariation y (N+1)=logVariation y N+(freeSet y N).card*d := by
      have flat : ((freeSet y N).card:ℝ)*d=∑ m ∈ Icc 1 N,if IsFree (banned y) m then d else 0 := by
        rw [←sum_filter,sum_const,nsmul_eq_mul]
      rw [flat]
      simp only [logVariation,freeSet,sum_filter,sum_Icc_succ_top (by omega : 1 ≤ N+1),sub_self,ite_self,add_zero]
      rw [←sum_add_distrib]
      apply sum_congr rfl
      intro n _
      by_cases f : IsFree (banned y) n <;> simp [f,d,Nat.cast_succ] <;> ring
    have step := mul_le_mul_of_nonneg_right (count N) dn
    rw [change_,Nat.cast_succ]
    dsimp only [d] at step cost ⊢
    nlinarith only [ih,step,mul_le_mul_of_nonneg_left cost hδ.le]

private theorem prime_error_over_rough_cofactors :
    ∃ C : ℝ,0<C ∧ ∃ Y : ℕ,4 ≤ Y ∧ ∀ y X : ℕ,Y ≤ y → y ≤ X →
      (∑ m ∈ freeSet y (X/y),|roughPrimePowerReading y (X/m)-((X:ℝ)/m-y)|) ≤
      (C*(2/Real.log ((y:ℝ)/2)+1/Real.log y^2))*X := by
  obtain ⟨C,hC,Y,hY,bound⟩ := uniform_prime_reading_error
  refine ⟨C,hC,Y,hY,?_⟩
  intro y X hy yX
  let T := X/y
  have y4 : (4:ℝ) ≤ y := by exact_mod_cast hY.trans hy
  have y0 : (0:ℝ)<y := by linarith
  have X0 : (0:ℝ)<X := y0.trans_le (Nat.cast_le.mpr yX)
  have size : (T:ℝ)*(y:ℝ) ≤ X := by exact_mod_cast Nat.div_mul_le_self X y
  have one : (1:ℝ) ≤ T := Nat.one_le_cast.mpr ((Nat.le_div_iff_mul_le (by omega : 0<y)).mpr (by simpa using yX))
  have two := mul_le_mul_of_nonneg_right one y0.le
  have room : (T:ℝ)+1<X := by nlinarith only [size,one,two,y4,mul_le_mul_of_nonneg_left y4 (Nat.cast_nonneg T)]
  have far : (y:ℝ)/2 ≤ (X:ℝ)/(T+1) := (le_div_iff₀ (by positivity)).mpr (by linarith only [size,two])
  have logpos : 0<Real.log ((y:ℝ)/2) := Real.log_pos (by linarith only [y4])
  have logfar := Real.log_le_log (by positivity : (0:ℝ)<y/2) far
  have cost := (sum_quotient_log_errors room).trans
    (div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 2) logpos logfar)
  let f := fun m : ℕ => 1/((m:ℝ)*Real.log ((X:ℝ)/m)^2)
  have per (m : ℕ) (hm : m ∈ Icc 1 T) :
      |roughPrimePowerReading y (X/m)-((X:ℝ)/m-y)| ≤ C*((X:ℝ)*f m+y/Real.log y^2) := by
    have mp := (mem_Icc.mp hm).1
    have inside := (Nat.le_div_iff_mul_le (by omega : 0<y)).mp (mem_Icc.mp hm).2
    have enough : (y:ℝ) ≤ (X:ℝ)/m := (le_div_iff₀ (Nat.cast_pos.mpr mp)).mpr
      (by rw [mul_comm]; exact_mod_cast inside)
    have step := bound y hy _ enough
    rw [Nat.floor_div_natCast,Nat.floor_natCast] at step
    apply step.trans_eq
    dsimp only [f]; ring
  have small := sum_le_sum_of_subset_of_nonneg (filter_subset (IsFree (banned y)) (Icc 1 T))
    (fun m _ _ => abs_nonneg (roughPrimePowerReading y (X/m)-((X:ℝ)/m-y)))
  apply small.trans ((sum_le_sum per).trans ?_)
  rw [←mul_sum,sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
  have cof := mul_le_mul_of_nonneg_left cost X0.le
  have div := div_le_div_of_nonneg_right size (sq_nonneg (Real.log y))
  apply (mul_le_mul_of_nonneg_left (add_le_add cof (le_trans (le_of_eq (mul_div_assoc' ..)) div)) hC.le).trans_eq
  ring

/-- Uniform boundary law. The normalized logarithmic signed rough prefix
is the negative proportion of smooth integers at its quotient endpoint.
Both the prime cutoff and its quotient can grow arbitrarily slowly. -/
theorem signed_rough_prefix_tracks_smooth_population {ε : ℝ} (hε : 0<ε) :
    ∃ Z : ℕ,0<Z ∧ ∀ y X : ℕ,Z ≤ y → Z*y ≤ X →
      |Real.log X*coprimeMoebiusSum (primorial y) X+
        (y:ℝ)*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) (X/y)).card| ≤ ε*X := by
  let δ := ε/8
  have hd : 0<δ := by dsimp only [δ]; positivity
  obtain ⟨Z,K,hK,counts⟩ := uniform_rough_count_and_variation hd
  obtain ⟨C,hC,Y,hY,primeErr⟩ := prime_error_over_rough_cofactors
  let L := max 1 (4*C/δ)
  have hl : 0<L := zero_lt_one.trans_le (le_max_left ..)
  let D := fun n : ℕ => Real.log ((n:ℝ)/2)
  have logtop : Tendsto D atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_atTop.mpr fun b => (tendsto_natCast_atTop_atTop.eventually_ge_atTop (2*b)).mono
      (fun n hn => by dsimp only; linarith only [hn]))
  obtain ⟨A,logA⟩ := eventually_atTop.mp (logtop.eventually_ge_atTop L)
  have weak := Real.isLittleO_log_id_atTop.bound (div_pos hd (by positivity : (0:ℝ)<K+1))
  obtain ⟨B,logB⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop weak)
  let W := max (max (max Z Y) (max A B)) ⌈2*K/δ⌉₊
  have big : Y ≤ W := ((le_max_right Z Y).trans (le_max_left ..)).trans (le_max_left ..)
  have wpos : 0<W := lt_of_lt_of_le (by omega : 0<Y) big
  refine ⟨W,wpos,?_⟩
  intro y X wy wx
  have yX : y ≤ X := (Nat.le_mul_of_pos_left _ wpos).trans wx
  have yp : 0<y := wpos.trans_le wy
  have x0 := Nat.cast_nonneg (α := ℝ) X
  have Ly : L ≤ D y := logA _ ((((le_max_left A B).trans (le_max_right ..)).trans (le_max_left ..)).trans wy)
  have hylog := Real.log_le_log (by positivity : (0:ℝ)<y/2)
    (by linarith only [Nat.cast_nonneg (α := ℝ) y] : (y:ℝ)/2 ≤ y)
  have lg : 1 ≤ Real.log y := (le_max_left 1 _).trans (Ly.trans hylog)
  have square : D y ≤ Real.log y^2 := hylog.trans (by nlinarith only [lg,sq_nonneg (Real.log y-1)])
  have dl := (div_le_iff₀ hd).mp ((le_max_right 1 _).trans Ly)
  have fees : C*(2/D y+1/Real.log y^2) ≤ δ := by
    have dpos := hl.trans_le Ly
    have less := div_le_div_of_nonneg_left zero_le_one dpos square
    have sum := mul_le_mul_of_nonneg_left (add_le_add le_rfl less) hC.le
    apply sum.trans
    rw [←add_div,mul_div_assoc',div_le_iff₀ dpos]
    linarith only [dl,hC]
  have atZ : Z ≤ y := ((((le_max_left Z Y).trans (le_max_left ..)).trans (le_max_left ..)).trans wy)
  have c1 := (counts y atZ X).2
  have c2 := (counts y atZ (X/y)).1
  have c3 := (primeErr y X (big.trans wy) yX).trans (mul_le_mul_of_nonneg_right fees x0)
  have Bx : B ≤ X := (((((le_max_right A B).trans (le_max_right ..)).trans (le_max_left ..)).trans wy)).trans yX
  have ld := logB X Bx
  have logX := Real.log_nonneg ((Nat.one_le_cast.mpr (yp.trans_le yX)) : (1:ℝ) ≤ X)
  change ‖Real.log (X:ℝ)‖ ≤ δ/(K+1)*‖(X:ℝ)‖ at ld
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg logX,abs_of_nonneg x0,div_mul_eq_mul_div,
    le_div_iff₀ (by positivity)] at ld
  have kcap : 2*K/δ ≤ (W:ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.mpr (le_max_right ..))
  have kprice := (mul_le_mul_of_nonneg_right ((div_le_iff₀ hd).mp kcap) (Nat.cast_nonneg (α := ℝ) y)).trans
    (by have mult : (W:ℝ)*y ≤ X := by exact_mod_cast wx
        linarith only [mul_le_mul_of_nonneg_left mult hd.le] : _ ≤ δ*X)
  rw [prefix_eq_frozen_row]
  have paid := smooth_main_term_error_at_every_rough_cutoff yp X
  have quotient : (y:ℝ)*((X/y:ℕ):ℝ) ≤ X := by exact_mod_cast Nat.mul_div_le X y
  have rest := mul_le_mul_of_nonneg_left c2 (Nat.cast_nonneg (α := ℝ) y)
  change logVariation y X ≤ _ at c1
  change _ ≤ logVariation y X+_+_ at paid
  dsimp only [δ] at c1 c3 ld kprice rest ⊢
  nlinarith only [paid,c1,c3,ld,kprice,rest,logX,mul_le_mul_of_nonneg_left quotient hε.le,
    mul_nonneg hε.le x0]

#print axioms signed_rough_prefix_tracks_smooth_population

#print axioms smooth_main_term_error_at_every_rough_cutoff
end GaloisForLFunctions.RestrictedFactorizationCalculus
