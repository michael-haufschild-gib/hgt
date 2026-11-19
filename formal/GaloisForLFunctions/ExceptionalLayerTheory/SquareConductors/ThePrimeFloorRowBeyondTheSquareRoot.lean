import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsOfReciprocalPrimes
import GaloisForLFunctions.RHTower.BurnolCoPoissonFractionalKernel
import GaloisForLFunctions.ExceptionalLayerTheory.LogFactorialWeightsForTheMiddlePrimeInterval
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMidpointInTwoAdjacentGcdHorizons
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheSmallPrimeFactorsOfTheReflectedComposites

/-!
# The signed prime cofactor row beyond twice the square root

Each ordinary prime has the second difference of three quotient floors.
Their linear parts cancel. Oscillation of the three centered fractional
parts pays an interval of primes strictly beyond the elementary cutoff.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Net number of multiples of d in (3n,4n] minus those in (2n,3n]. -/
def midpointFloorWeight (n d : ℕ) : ℝ :=
  ((4*n/d:ℕ):ℝ)-2*((3*n/d:ℕ):ℝ)+((2*n/d:ℕ):ℝ)

/-- Signed ordinary-prime log price, with the prime interval left closed
and right open for concatenation. -/
def midpointFloorPrimeBlock (n A B : ℕ) : ℝ :=
  ∑ p ∈ (Ico A B).filter Nat.Prime,Real.log p*midpointFloorWeight n p

private theorem real_quotient_floor (T p : ℕ) :
    ((T/p:ℕ):ℝ) = (T:ℝ)/p-Int.fract ((T:ℝ)/p) := by
  have h := _root_.RHTower.natFloor_cast_eq_sub_fract (by positivity : 0 ≤ (T:ℝ)/p)
  rwa [Nat.floor_div_natCast,Nat.floor_natCast] at h

private theorem midpoint_saw (n p : ℕ) :
    midpointFloorWeight n p =
      2*(Int.fract ((3*(n:ℝ))/p)-1/2)-(Int.fract ((2*(n:ℝ))/p)-1/2)-
        (Int.fract ((4*(n:ℝ))/p)-1/2) := by
  simp only [midpointFloorWeight,real_quotient_floor,Nat.cast_mul,Nat.cast_ofNat]
  ring

/-- A power saving for the actual signed prime price up to every partial
endpoint when the three reciprocal frequencies lie near the square scale. -/
theorem midpoint_floor_prime_block_saving :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n A B : ℕ}, 1 ≤ A → A ≤ B → B ≤ 2*A →
      (A:ℝ)^(999/500:ℝ) ≤ 2*n → 4*(n:ℝ) ≤ (A:ℝ)^(1001/500:ℝ) →
      |midpointFloorPrimeBlock n A B| ≤ C*(A:ℝ)^(999/1000:ℝ) := by
  obtain ⟨K,hK,h⟩ := GaloisForLFunctions.PrimeExponentialSums.centered_fractional_reciprocal_prime_block
  refine ⟨4*K,by positivity,?_⟩
  intro n A B ha hab hb hlo hhi
  let F (k : ℝ) := ∑ p ∈ (Ico A B).filter Nat.Prime,Real.log p*(Int.fract (k*n/p)-1/2)
  have hE (k : ℝ) (hk : 2 ≤ k) (hk' : k ≤ 4) : |F k| ≤ K*(A:ℝ)^(999/1000:ℝ) :=
    h A B (k*n) ha hab hb (hlo.trans (mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg n)))
      ((mul_le_mul_of_nonneg_right hk' (Nat.cast_nonneg n)).trans hhi)
  have he : midpointFloorPrimeBlock n A B=2*F 3-F 2-F 4 := by
    simp only [midpointFloorPrimeBlock,F,mul_sum,←sum_sub_distrib]
    exact sum_congr rfl fun p _ => by rw [midpoint_saw]; ring
  have h2 := abs_le.mp (hE 2 (by norm_num) (by norm_num))
  have h3 := abs_le.mp (hE 3 (by norm_num) (by norm_num))
  have h4 := abs_le.mp (hE 4 (by norm_num) (by norm_num))
  rw [he,abs_le]
  constructor <;> linarith only [h2.1,h2.2,h3.1,h3.2,h4.1,h4.2]

private theorem floor_block_append (n : ℕ) {A B C : ℕ} (h : A ≤ B) (h' : B ≤ C) :
    midpointFloorPrimeBlock n A B+midpointFloorPrimeBlock n B C=midpointFloorPrimeBlock n A C := by
  simp only [midpointFloorPrimeBlock,sum_filter]
  exact sum_Ico_consecutive _ h h'

/-- Uniform geometric summation with the last partial interval retained. -/
private theorem dyadic_midpoint_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ B n A : ℕ, 1 ≤ A → A ≤ B →
      (B-1:ℕ) ≤ ⌊(n:ℝ)^(500/999:ℝ)⌋₊ → 4*(n:ℝ) ≤ (A:ℝ)^2 →
      |midpointFloorPrimeBlock n A B| ≤ K*(B:ℝ)^(999/1000:ℝ) := by
  let s : ℝ := 999/1000
  have hs : 0 < s := by norm_num [s]
  let q := (3/4:ℝ)^s
  have hq : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hs
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  obtain ⟨C,hC,hblock⟩ := midpoint_floor_prime_block_saving
  let K := C/(1-q)
  have hk0 : 0 ≤ K := div_nonneg hC (sub_nonneg.mpr hq.le)
  have hk : K*(1-q)=C := div_mul_cancel₀ _ (sub_ne_zero.mpr hq.ne')
  have hcK : C ≤ K := by linarith only [hk,mul_nonneg hk0 hq0]
  have hcomp : (K+C)*q ≤ K := by linarith only [hk,mul_le_of_le_one_right hC hq.le]
  refine ⟨K,hk0,?_⟩
  intro B
  induction B using Nat.strong_induction_on with
  | h B ih =>
    intro n A ha hab hcut hstart
    have hbound {X : ℕ} (hAX : A ≤ X) (hXB : X < B) (hshort : B ≤ 2*X) :
        |midpointFloorPrimeBlock n X B| ≤ C*(X:ℝ)^s := by
      have hXt : (X:ℝ) ≤ (n:ℝ)^(500/999:ℝ) := (Nat.cast_le.mpr
        ((show X ≤ B-1 by omega).trans hcut)).trans (Nat.floor_le (by positivity))
      have hLo := Real.rpow_le_rpow (Nat.cast_nonneg _) hXt (by norm_num : (0:ℝ) ≤ 999/500)
      rw [←Real.rpow_mul (Nat.cast_nonneg n),show (500/999:ℝ)*(999/500)=1 by norm_num,Real.rpow_one] at hLo
      have hpow := Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (ha.trans hAX))
        (by norm_num : (2:ℝ) ≤ 1001/500)
      rw [Real.rpow_two] at hpow
      have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (α:=ℝ) A) (Nat.cast_le.mpr hAX) 2
      exact hblock (ha.trans hAX) hXB.le hshort (by linarith only [hLo,Nat.cast_nonneg (α:=ℝ) n])
        ((hstart.trans hsq).trans hpow)
    rcases eq_or_lt_of_le hab with rfl | hAB
    · simp only [midpointFloorPrimeBlock,Ico_self,filter_empty,sum_empty,abs_zero]
      exact mul_nonneg hk0 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    · by_cases hshort : B ≤ 2*A
      · exact (hbound (le_refl A) hAB hshort).trans (mul_le_mul hcK
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hab) hs.le) (by positivity) hk0)
      · let M := (B+1)/2
        have hAM : A ≤ M := by dsimp only [M]; omega
        have hMB : M < B := by dsimp only [M]; omega
        have hhalf : B ≤ 2*M := by dsimp only [M]; omega
        have hfrac : 4*M ≤ 3*B := by dsimp only [M]; omega
        have hfrac' : (M:ℝ) ≤ (3/4:ℝ)*B := by
          have hh : 4*(M:ℝ) ≤ 3*B := by exact_mod_cast hfrac
          linarith only [hh]
        have hscale := Real.rpow_le_rpow (Nat.cast_nonneg _) hfrac' hs.le
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 3/4) (Nat.cast_nonneg B)] at hscale
        rw [←floor_block_append n hAM hMB.le]
        apply (abs_add_le _ _).trans
        have hleft := ih M hMB n A ha hAM ((show M-1 ≤ B-1 by omega).trans hcut) hstart
        have hright := hbound hAM hMB hhalf
        calc _ ≤ (K+C)*(M:ℝ)^s := (add_le_add hleft hright).trans_eq (add_mul ..).symm
             _ ≤ (K+C)*(q*(B:ℝ)^s) := mul_le_mul_of_nonneg_left hscale (add_nonneg hk0 hC)
             _ ≤ _ := by rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right hcomp (Real.rpow_nonneg (Nat.cast_nonneg _) _)

#print axioms midpoint_floor_prime_block_saving

/-- At every center and every partial prime endpoint between twice the
square root and n^(500/999), the actual signed cofactor price costs O(√n). -/
theorem prime_floor_shell_beyond_square_root :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n A B : ℕ}, 1 ≤ n → ⌊2*Real.sqrt n⌋₊ < A →
      B ≤ ⌊(n:ℝ)^(500/999:ℝ)⌋₊+1 → |midpointFloorPrimeBlock n A B| ≤ C*Real.sqrt n := by
  obtain ⟨K,hK,h⟩ := dyadic_midpoint_bound
  let s : ℝ := 999/1000
  have hs : 0 < s := by norm_num [s]
  refine ⟨K*(2:ℝ)^s,by positivity,?_⟩
  intro n A B hn hA hB
  by_cases hab : A ≤ B
  · have hl : 2*Real.sqrt n < (A:ℝ) := (Nat.floor_lt (by positivity)).mp hA
    have hsq := sq_le_sq' (by linarith only [hl,Real.sqrt_nonneg (n:ℝ)] : -(A:ℝ) ≤ 2*Real.sqrt n) hl.le
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)] at hsq
    have hstart : 4*(n:ℝ) ≤ (A:ℝ)^2 := by linarith only [hsq]
    have hbound := h B n A (by omega) hab (by omega) hstart
    have hcut : (⌊(n:ℝ)^(500/999:ℝ)⌋₊:ℝ) ≤ (n:ℝ)^(500/999:ℝ) := Nat.floor_le (by positivity)
    have hone := Real.one_le_rpow ((Nat.one_le_cast (α:=ℝ)).mpr hn) (by norm_num : (0:ℝ) ≤ 500/999)
    have hBr := (Nat.cast_le (α:=ℝ)).mpr hB
    rw [Nat.cast_add,Nat.cast_one] at hBr
    have hbnd := Real.rpow_le_rpow (Nat.cast_nonneg B)
      (by linarith only [hcut,hone,hBr] : (B:ℝ) ≤ 2*(n:ℝ)^(500/999:ℝ)) hs.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),←Real.rpow_mul (Nat.cast_nonneg n),
      show (500/999:ℝ)*s=1/2 by norm_num [s],←Real.sqrt_eq_rpow] at hbnd
    exact hbound.trans ((mul_le_mul_of_nonneg_left hbnd hK).trans_eq (mul_assoc ..).symm)
  · rw [midpointFloorPrimeBlock,Ico_eq_empty (by omega : ¬A<B),filter_empty,sum_empty,abs_zero]
    positivity

#print axioms prime_floor_shell_beyond_square_root

/-- Full factorial log ratio on the two adjacent intervals, with no
coprimality condition. -/
def completeMidpointFactorial (n : ℕ) : ℝ :=
  Real.log ((4*n).factorial:ℕ)-2*Real.log ((3*n).factorial:ℕ)+Real.log ((2*n).factorial:ℕ)

private theorem factorial_midpoint_inversion (n : ℕ) :
    ∑ q ∈ Ioc 0 (4*n),vonMangoldt q*midpointFloorWeight n q=completeMidpointFactorial n := by
  have hi (T : ℕ) : Icc 1 T=Ioc 0 T := by ext q; simp only [mem_Icc,mem_Ioc]; omega
  have row (k : ℕ) (hk : k ≤ 4) :
      (∑ q ∈ Ioc 0 (4*n),vonMangoldt q*((k*n/q:ℕ):ℝ))=Real.log ((k*n).factorial:ℕ) := by
    have h := mangoldt_floor (k*n) 1
    simp only [hi,Nat.div_one] at h
    rw [←h]
    symm
    apply sum_subset (Ioc_subset_Ioc_right (Nat.mul_le_mul_right n hk))
    intro q hq hnot
    have hq0 := (mem_Ioc.mp hq).1
    have hlt : k*n < q := by
      by_contra! hh
      exact hnot (mem_Ioc.mpr ⟨hq0,hh⟩)
    rw [Nat.div_eq_of_lt hlt,Nat.cast_zero,mul_zero]
  rw [completeMidpointFactorial,←row 4 (by decide),←row 3 (by decide),←row 2 (by decide),mul_sum,
    ←sum_sub_distrib,←sum_add_distrib]
  exact sum_congr rfl fun q _ => by rw [midpointFloorWeight]; ring

/-- All primes strictly between P and the last possible prime factor
of a composite. Unit cofactors cannot occur in this row. -/
def unrestrictedLargePrimePrice (n P : ℕ) : ℝ :=
  ∑ p ∈ (Ioc P (2*n)).filter Nat.Prime, Real.log p*midpointFloorWeight n p

private theorem singleton_floor_row {n : ℕ} (hn : 0 < n) :
    (∑ p ∈ (Ioc (2*n) (4*n)).filter Nat.Prime,Real.log p*midpointFloorWeight n p) =
      -primeMidpointPrice n := by
  let f (p : ℕ) : ℝ := if p.Prime then Real.log p*midpointFloorWeight n p else 0
  have unit {p : ℕ} (hp : p ∈ Ioc (2*n) (4*n)) :
      midpointFloorWeight n p = if p ≤ 3*n then -1 else 1 := by
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hp
    have hp0 : 0 < p := by omega
    have h4 : 4*n/p=1 := by
      have h1 : 1 ≤ 4*n/p := (Nat.le_div_iff_mul_le hp0).mpr (by omega)
      have h2 : 4*n/p < 2 := (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
      omega
    have h3 : 3*n/p < 2 := (Nat.div_lt_iff_lt_mul hp0).mpr (by omega)
    rw [midpointFloorWeight,h4,Nat.div_eq_of_lt hlo]
    split_ifs with hp3
    · have h1 : 1 ≤ 3*n/p := (Nat.le_div_iff_mul_le hp0).mpr (by omega)
      rw [show 3*n/p=1 by omega]; norm_num
    · rw [Nat.div_eq_of_lt (lt_of_not_ge hp3)]; norm_num
  have left : (∑ p ∈ Ioc (2*n) (3*n),f p)=
      -(∑ p ∈ (Ioc (2*n) (3*n)).filter Nat.Prime,Real.log p) := by
    rw [sum_filter,←sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hp
    simp only [f,unit (mem_Ioc.mpr ⟨hl,by omega⟩),if_pos hu]
    split_ifs <;> ring
  have right : (∑ p ∈ Ioc (3*n) (4*n),f p)=
      ∑ p ∈ (Ioc (3*n) (4*n)).filter Nat.Prime,Real.log p := by
    rw [sum_filter]
    apply sum_congr rfl
    intro p hp
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hp
    simp only [f,unit (mem_Ioc.mpr ⟨by omega,hu⟩),if_neg (not_le.mpr hl),mul_one]
  have h := sum_Ioc_consecutive f (show 2*n ≤ 3*n by omega) (show 3*n ≤ 4*n by omega)
  rw [sum_filter]
  change (∑ p ∈ Ioc (2*n) (4*n),f p)=_
  rw [←h,left,right,primeMidpointPrice]
  ring

/-- Removing cofactor coprimality replaces the primitive center by the
full factorial ratio. The entire omitted price costs the small Mangoldt
mass and the proper powers, with no divisor-count loss. -/
theorem unrestricted_large_prime_factorial_error {n P : ℕ} (hn : 0 < n) (hP : P ≤ 2*n) :
    |unrestrictedLargePrimePrice n P-completeMidpointFactorial n-primeMidpointPrice n| ≤
      Chebyshev.psi P+(Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ)) := by
  classical
  let f (q : ℕ) := vonMangoldt q*midpointFloorWeight n q
  let S := (Ioc P (4*n)).filter (fun q => ¬q.Prime)
  have bound {T : Finset ℕ} (ht : ∀ q ∈ T,0 < q) :
      |∑ q ∈ T,f q| ≤ ∑ q ∈ T,vonMangoldt q := by
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro q hq
    dsimp only [f]
    rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg]
    exact mul_le_of_le_one_right vonMangoldt_nonneg (abs_midpoint_division_le_one (ht q hq) n)
  have low := bound (T:=Ioc 0 P) (fun _ h => (mem_Ioc.mp h).1)
  have powc := bound (T:=S) (fun _ h => (Nat.zero_le P).trans_lt (mem_Ioc.mp (mem_filter.mp h).1).1)
  have hpp : (∑ q ∈ S,vonMangoldt q) ≤ Chebyshev.psi (4*n:ℕ)-Chebyshev.theta (4*n:ℕ) := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => vonMangoldt_nonneg)
    intro q hq
    obtain ⟨hi,hpr⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.zero_le P).trans_lt (mem_Ioc.mp hi).1,(mem_Ioc.mp hi).2⟩,hpr⟩
  have hfull := sum_Ioc_consecutive f (Nat.zero_le P) (show P ≤ 4*n by omega)
  have hs := sum_filter_add_sum_filter_not (Ioc P (4*n)) Nat.Prime f
  have hpr (q : ℕ) : (if q.Prime then f q else 0) =
      if q.Prime then Real.log q*midpointFloorWeight n q else 0 := by
    by_cases h : q.Prime <;> simp [h,f,vonMangoldt_apply_prime]
  have hsplit := sum_Ioc_consecutive (fun q : ℕ => if q.Prime then Real.log q*midpointFloorWeight n q else 0)
    hP (show 2*n ≤ 4*n by omega)
  simp only [←sum_filter] at hsplit
  have hscalar := singleton_floor_row hn
  have hprime : (∑ q ∈ (Ioc P (4*n)).filter Nat.Prime,f q)=
      unrestrictedLargePrimePrice n P-primeMidpointPrice n := by
    rw [sum_filter]
    simp only [hpr,←sum_filter]
    rw [←hsplit,hscalar,unrestrictedLargePrimePrice,sub_eq_add_neg]
  change _ + _ = ∑ q ∈ Ioc 0 (4*n),vonMangoldt q*midpointFloorWeight n q at hfull
  rw [factorial_midpoint_inversion] at hfull
  have he : unrestrictedLargePrimePrice n P-completeMidpointFactorial n-primeMidpointPrice n =
      -((∑ q ∈ Ioc 0 P,f q)+∑ q ∈ S,f q) := by
    change _ + (∑ q ∈ S,f q)=_ at hs
    linarith only [hfull,hs,hprime]
  rw [he,abs_neg]
  apply (abs_add_le _ _).trans
  apply add_le_add _ (powc.trans hpp)
  simpa only [Chebyshev.psi,Nat.floor_natCast] using low

#print axioms unrestricted_large_prime_factorial_error

/-- Every prime divider through n^(500/999) leaves the same factorial
center and midpoint to square-root error at every positive integer. -/
theorem midpoint_after_paid_prime_shell :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n Q : ℕ}, 1 ≤ n → ⌊2*Real.sqrt n⌋₊ ≤ Q →
      Q ≤ max ⌊2*Real.sqrt n⌋₊ ⌊(n:ℝ)^(500/999:ℝ)⌋₊ →
      |unrestrictedLargePrimePrice n Q-completeMidpointFactorial n-primeMidpointPrice n|
        ≤ C*Real.sqrt n := by
  obtain ⟨K,hK,hblock⟩ := prime_floor_shell_beyond_square_root
  obtain ⟨D,hD⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨14+2*|D|+K,by positivity,?_⟩
  intro n Q hn hPQ hQ
  let P := ⌊2*Real.sqrt n⌋₊
  change P ≤ Q at hPQ
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have hn0 : 0 < n := hn
  have hroot : Real.sqrt n ≤ (n:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/2:ℝ) ≤ 1)).trans_eq (Real.rpow_one _)
  have hcut : (P:ℝ) ≤ 2*Real.sqrt n := Nat.floor_le (by positivity)
  have hP : P ≤ 2*n := by
    exact_mod_cast hcut.trans (mul_le_mul_of_nonneg_left hroot (by norm_num : (0:ℝ) ≤ 2))
  have hboundQ : Q ≤ 2*n := by
    apply hQ.trans (max_le hP ?_)
    have hc := (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) (500/999:ℝ))).trans
      ((Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (500/999:ℝ)≤1)).trans_eq (Real.rpow_one _))
    exact (Nat.cast_le.mp hc).trans (by omega)
  let B := midpointFloorPrimeBlock n (P+1) (Q+1)
  have hB : |B| ≤ K*Real.sqrt n := by
    rcases le_max_iff.mp hQ with h | h
    · have he : Q=P := le_antisymm h hPQ
      simp only [B,he,midpointFloorPrimeBlock,Ico_self,filter_empty,sum_empty,abs_zero]
      positivity
    · exact hblock hn (Nat.lt_succ_self P) (Nat.add_le_add_right h 1)
  have hi : Ico (P+1) (Q+1)=Ioc P Q := by ext j; simp only [mem_Ico,mem_Ioc]; omega
  have hjoin : B+unrestrictedLargePrimePrice n Q=unrestrictedLargePrimePrice n P := by
    simp only [B,midpointFloorPrimeBlock,hi,unrestrictedLargePrimePrice,sum_filter]
    exact sum_Ioc_consecutive _ hPQ hboundQ
  have hi' : Ioc 0 P=Icc 1 P := by ext j; simp only [mem_Ico,mem_Icc,mem_Ioc]; omega
  have hψ : Chebyshev.psi P ≤ 7*P := by
    simpa only [Chebyshev.psi,Nat.floor_natCast,hi'] using _root_.RHTower.sum_vonMangoldt_Icc_le_seven P
  have hproper := hD ((4*n:ℕ):ℝ)
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
    show Real.sqrt 4 = 2 by norm_num] at hproper
  have habs := mul_le_mul_of_nonneg_right (le_abs_self D) (mul_nonneg (by norm_num : (0:ℝ)≤2) (Real.sqrt_nonneg (n:ℝ)))
  have herr := unrestricted_large_prime_factorial_error hn0 hP
  have hid : unrestrictedLargePrimePrice n Q-completeMidpointFactorial n-primeMidpointPrice n =
      (unrestrictedLargePrimePrice n P-completeMidpointFactorial n-primeMidpointPrice n)+(-B) := by
    linarith only [hjoin]
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_neg]
  have hr := add_le_add herr hB
  push_cast at hr
  linarith only [hr,hψ,hcut,hproper,habs]

#print axioms midpoint_after_paid_prime_shell

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
