import GaloisForLFunctions.RHTower.PMPowerDampedMobiusFiniteDeletion
import GaloisForLFunctions.RHTower.Sieve.MoebiusLogRecursion
import GaloisForLFunctions.RHTower.Sieve.SmoothSum
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheExplicitLogSquareRoughSet

/-!
# Centering the prime-power readings at their quotient floors

In the logarithmic Möbius identity with primes through y deleted, the
exact quotient floors recover the full smooth population at X/y. A
finite Euler product bounds this whole contribution at the log-square
cutoff, leaving a single signed sum of centered prime-power readings.
-/
noncomputable section

open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Classical ArithmeticFunction.Moebius
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

namespace RoughReading

/-- Primes through the fixed cutoff are excluded. -/
abbrev banned (y : ℕ) : Set ℕ := {p | p ≤ y}
/-- Möbius weight with the small primes deleted. -/
abbrev row (y n : ℕ) : ℝ := (mobiusAF (banned y) n : ℝ)
/-- Positive integers avoiding every excluded prime. -/
abbrev freeSet (y X : ℕ) := (Icc 1 X).filter (IsFree (banned y))

theorem row_value (y n : ℕ) :
    row y n=if IsFree (banned y) n then (μ n:ℝ) else 0 := by
  by_cases h : IsFree (banned y) n <;> simp [row,mobiusAF,pmul_apply,freeAF_apply,h]

end RoughReading

open RoughReading

/-- On positive integers the deleted Möbius function is the ordinary
Möbius indicator of coprimality to the primorial. -/
theorem primorial_indicator_eq_deleted_mobius (y n : ℕ) (pos : 1 ≤ n) :
    coprimeMoebiusIndicator (primorial y) n=row y n := by
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

/-- No surviving prime power lies at or below the first allowed wall. -/
theorem roughPrimePowerReading_eq_zero {y x : ℕ} (hx : x ≤ y) : roughPrimePowerReading y x=0 := by
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
    simp only [f,roughPrimePowerReading_eq_zero small.le,mul_zero]
  · have early := mem_Icc.mpr ⟨lo,le_of_not_gt late⟩
    have absent : ¬IsFree (banned y) m := fun h => outside (mem_filter.mpr ⟨early,h⟩)
    simp only [f,row_value,if_neg absent,zero_mul]

/-- Divisor inversion counts every smooth integer by the rough quotient floors. -/
theorem smooth_population_as_a_rough_floor_sum (y : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∑ m ∈ freeSet y ⌊t⌋₊,row y m*(⌊t/m⌋:ℝ))=
      ((RHTower.Sieve.smoothUpTo (Nat.primesLE y) ⌊t⌋₊).card:ℝ) := by
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
      ∑ n ∈ Icc 1 ⌊t⌋₊,((smoothAF (banned y) n:ℤ):ℝ) := by
    apply Complex.ofReal_injective
    push_cast
    exact eq
  change _=(S.card:ℝ)
  rw [←count,←realEq]
  apply sum_subset (filter_subset ..)
  intro n hn out
  rw [row_value,if_neg (fun h => out (mem_filter.mpr ⟨hn,h⟩)),zero_mul]

/-- The prime-power reading after subtracting the mass of the exact
quotient floor, weighted by the actual rough Möbius cofactors. -/
def centeredPrimePowerRemainder (y X : ℕ) :=
  ∑ m ∈ freeSet y (X/y),row y m*
    (roughPrimePowerReading y (X/m)-(y:ℝ)*(⌊((X:ℝ)/y)/m⌋:ℝ))

/-- The term removed by centering is exactly the ordinary smooth
population at X/y, with all repeated prime factors included. -/
theorem exact_centered_prime_power_remainder {y : ℕ} (hy : 0<y) (X : ℕ) :
    (∑ n ∈ Icc 1 X,row y n*Real.log n)+centeredPrimePowerRemainder y X=
      -(y:ℝ)*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) (X/y)).card := by
  have nonneg := div_nonneg (Nat.cast_nonneg (α := ℝ) X) (Nat.cast_nonneg y)
  have floor := smooth_population_as_a_rough_floor_sum y ((X:ℝ)/y) nonneg
  rw [Nat.floor_div_natCast,Nat.floor_natCast] at floor
  rw [logarithmic_rough_prefix_at_quotient_readings hy,centeredPrimePowerRemainder,←floor,neg_mul,mul_sum]
  simp only [mul_sub,sum_sub_distrib]
  have flat : (∑ m ∈ freeSet y (X/y),row y m*(y*(⌊((X:ℝ)/y)/m⌋:ℝ)))=
      ∑ m ∈ freeSet y (X/y),(y:ℝ)*(row y m*(⌊((X:ℝ)/y)/m⌋:ℝ)) := by
    apply sum_congr rfl; intro m _; ring
  rw [flat]; ring

private theorem smooth_count_by_deletion_price {s : ℝ} (hs : 0<s) (y T : ℕ) :
    ((RHTower.Sieve.smoothUpTo (Nat.primesLE y) T).card:ℝ) ≤
      (T:ℝ)^s*deletionPrice s y := by
  let S := RHTower.Sieve.smoothUpTo (Nat.primesLE y) T
  let g := fun n : ℕ => (n:ℝ)^(-s)
  have nonneg (n : ℕ) : 0 ≤ g n := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have euler := RHTower.Sieve.sum_smoothUpTo_le nonneg (by simp [g]) (fun a b _ => by
    simp only [g,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]) T
    (Nat.primesLE y) (fun p hp => Nat.prime_of_mem_primesLE hp)
  have point (n : ℕ) (hn : n ∈ S) : 1 ≤ (T:ℝ)^s*g n := by
    obtain ⟨⟨np,nt⟩,_⟩ := RHTower.Sieve.mem_smoothUpTo.mp hn
    have pow := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr nt) hs.le
    have pos := Real.rpow_pos_of_pos (Nat.cast_pos.mpr np) s
    dsimp only [g]; rw [Real.rpow_neg (Nat.cast_nonneg _),←div_eq_mul_inv]
    exact (one_le_div pos).mpr pow
  have cost (p : ℕ) (hp : p ∈ Nat.primesLE y) :
      (∑ i ∈ range (T+1),g (p^i)) ≤ (1-(1/(p:ℝ))^s)⁻¹ := by
    let r := (1/(p:ℝ))^s
    have small : r<1 := deletion_weight_lt_one hs (Nat.prime_of_mem_primesLE hp)
    have r0 : 0 ≤ r := Real.rpow_nonneg (by positivity) _
    have eq (i : ℕ) : g (p^i)=r^i := by
      have base : (p:ℝ)^(-s)=r := by
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        dsimp only [r]; rw [one_div,Real.inv_rpow (Nat.cast_nonneg _)]
      rw [←base]
      dsimp only [g]
      rw [Nat.cast_pow,←Real.rpow_natCast (p:ℝ) i,←Real.rpow_mul (Nat.cast_nonneg _),
        mul_comm (i:ℝ),Real.rpow_mul (Nat.cast_nonneg _),Real.rpow_natCast]
    simp only [eq]
    exact ((summable_geometric_of_lt_one r0 small).sum_le_tsum _ (fun i _ => pow_nonneg r0 i)).trans_eq
      (tsum_geometric_of_lt_one r0 small)
  have price := Finset.prod_le_prod (fun p (_ : p ∈ Nat.primesLE y) => sum_nonneg (fun i _ => nonneg (p^i))) cost
  have full := sum_le_sum point
  simp only [sum_const,nsmul_eq_mul,mul_one,←mul_sum] at full
  exact full.trans (mul_le_mul_of_nonneg_left (euler.trans price) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- At the log-square cutoff the entire smooth main term already costs
square root plus epsilon. Only the signed, centered prime-power reading
remains in the logarithmically weighted rough prefix. All smaller prime
cutoffs at that endpoint satisfy the same estimate. -/
theorem smooth_main_term_paid_at_the_log_square_cutoff {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ X : ℕ in atTop,∀ y : ℕ,y ≤ logSquareCutoff X →
      (y:ℝ)*(RHTower.Sieve.smoothUpTo (Nat.primesLE y) (X/y)).card ≤ (X:ℝ)^(1/2+ε) := by
  let s := 1/2+ε/2
  have hs : 1/2<s := lt_add_of_pos_right _ (half_pos hε)
  have sp : 0<s := (by norm_num : (0:ℝ)<1/2).trans hs
  filter_upwards [log_square_deletion_cost hs (half_pos hε),eventually_ge_atTop (1:ℕ)] with X limit hX
  intro y below
  let b := logSquareCutoff X
  let E := deletionPrice s b
  have E1 : 1 ≤ E := deletionPrice_one_le sp b
  have hi := Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr (Nat.div_le_self X y)) sp.le
  have bound := (smooth_count_by_deletion_price sp y (X/y)).trans
    (mul_le_mul hi (deletionPrice_mono sp below) (zero_le_one.trans (deletionPrice_one_le sp _))
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have enough : (y:ℝ)*E ≤ ((b:ℝ)+1)*E^2 := by
    have left : (y:ℝ) ≤ (b:ℝ)+1 := (Nat.cast_le.mpr below).trans (by linarith)
    have right : E ≤ E^2 := by nlinarith only [E1,sq_nonneg (E-1)]
    exact mul_le_mul left right (zero_le_one.trans E1) (by positivity)
  have budget : (y:ℝ)*E ≤ (X:ℝ)^(ε/2) := enough.trans limit
  have pay := mul_le_mul_of_nonneg_right budget (Real.rpow_nonneg (Nat.cast_nonneg X) s)
  have charged := mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg (α := ℝ) y)
  change _ ≤ (y:ℝ)*((X:ℝ)^s*E) at charged
  rw [←Real.rpow_add (Nat.cast_pos.mpr hX),show ε/2+s=1/2+ε by dsimp only [s]; ring] at pay
  exact charged.trans ((le_of_eq (by ring)).trans pay)

#print axioms exact_centered_prime_power_remainder
#print axioms smooth_main_term_paid_at_the_log_square_cutoff

end GaloisForLFunctions.RestrictedFactorizationCalculus
