import GaloisForLFunctions.RHTower.Sieve.Mertens
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Odd integer quotients in the fractional-part test

Doubling the numerator exposes one binary digit of every fractional weight
simultaneously. A large signed fractional sum forces a large odd-quotient
discrepancy with the same orientation. Primes below the square root of the
numerator have bounded cost in the square-root normalization.
-/

noncomputable section
open scoped Classical
open Filter Topology ArithmeticFunction
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- Ordinary primes with their logarithmic weight against one at every integer. -/
def ordinaryPrimeExcessCoeff (n : ℕ) : ℝ := (if n.Prime then Real.log n else 0)-1

/-- The ordinary-prime discrepancy on a finite set with an odd integer quotient. -/
def oddQuotientPrimeExcess (S : Finset ℕ) (H : ℕ) : ℝ :=
  ∑ n ∈ S, if H/n%2=1 then ordinaryPrimeExcessCoeff n else 0

/-- The ordinary-prime discrepancy with fractional weights. -/
def fractionalPrimeExcess (S : Finset ℕ) (y : ℝ) : ℝ :=
  ∑ n ∈ S, ordinaryPrimeExcessCoeff n*Int.fract (y/n)

private theorem fract_double_digit (x : ℝ) (hx : 0≤x) :
    2*Int.fract x-Int.fract (2*x) = ((⌊2*x⌋₊%2 : ℕ):ℝ) := by
  have hdiv := Nat.floor_div_natCast (2*x) 2
  rw [Nat.cast_ofNat,show 2*x/2=x by ring] at hdiv
  have hz : ⌊2*x⌋₊%2+2*⌊x⌋₊=⌊2*x⌋₊ := by rw [hdiv]; exact Nat.mod_add_div ..
  have he (z : ℝ) (h : 0≤z) : ((⌊z⌋₊:ℕ):ℝ)=z-Int.fract z := by
    rw [Int.self_sub_fract,← Int.natCast_floor_eq_floor h,Int.cast_natCast]
  have hcast : ((⌊2*x⌋₊%2:ℕ):ℝ)+2*(⌊x⌋₊:ℝ)=(⌊2*x⌋₊:ℝ) := by exact_mod_cast hz
  rw [he x hx,he (2*x) (by positivity)] at hcast
  linarith only [hcast]

theorem fractionalPrimeExcess_double (S : Finset ℕ) {y : ℝ} (hy : 0≤y) :
    2*fractionalPrimeExcess S y-fractionalPrimeExcess S (2*y)=oddQuotientPrimeExcess S ⌊2*y⌋₊ := by
  rw [fractionalPrimeExcess,fractionalPrimeExcess,oddQuotientPrimeExcess,Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hd := fract_double_digit (y/n) (div_nonneg hy (Nat.cast_nonneg n))
  rw [← mul_div_assoc,Nat.floor_div_natCast] at hd
  have hmod := Nat.mod_lt (⌊2*y⌋₊/n) (by decide : 0<2)
  by_cases h : ⌊2*y⌋₊/n%2=1
  · rw [if_pos h]; rw [h,Nat.cast_one] at hd
    linear_combination ordinaryPrimeExcessCoeff n*hd
  · have hz : ⌊2*y⌋₊/n%2=0 := by omega
    rw [if_neg h]; rw [hz,Nat.cast_zero] at hd
    linear_combination ordinaryPrimeExcessCoeff n*hd

private theorem fractional_abs_bound (S : Finset ℕ) (y : ℝ) :
    |fractionalPrimeExcess S y| ≤ ∑ n ∈ S, |ordinaryPrimeExcessCoeff n| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n _
  rw [abs_mul,abs_of_nonneg (Int.fract_nonneg (y/n))]
  exact mul_le_of_le_one_right (abs_nonneg _) (Int.fract_lt_one _).le

/-- Some binary digit has the original sign, with a gain measured at its own
numerator. Iterating a putative bound on every digit would force the bounded
fractional sum to grow at least as the square root of the doubled argument. -/
theorem exists_large_oddQuotientPrimeExcess (S : Finset ℕ) {y B s : ℝ} (hy : 0<y) (hB : 0<B)
    (hbig : 4*B*Real.sqrt y < s*fractionalPrimeExcess S y) :
    ∃ j : ℕ, let z := (2:ℝ)^(j+1)*y
      B*Real.sqrt z < s*oddQuotientPrimeExcess S ⌊z⌋₊ := by
  by_contra! h
  let q := fun j : ℕ => (2:ℝ)^j*y
  have hpos (j : ℕ) : 0<q j := by dsimp only [q]; positivity
  have hnext (j : ℕ) : q (j+1)=2*q j := by dsimp only [q]; rw [pow_succ]; ring
  have hgrow (j : ℕ) : 4*B*Real.sqrt (q j) < s*fractionalPrimeExcess S (q j) := by
    induction j with
    | zero => simpa only [q,pow_zero,one_mul] using hbig
    | succ j ih =>
      have hd := congrArg (s*·) (fractionalPrimeExcess_double S (hpos j).le)
      have hb : s*oddQuotientPrimeExcess S ⌊q (j+1)⌋₊ ≤ B*Real.sqrt (q (j+1)) := le_of_not_gt (h j)
      rw [hnext] at hb ⊢
      rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤2)] at hb ⊢
      have hroot : Real.sqrt 2 ≤ 8/5 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by norm_num⟩
      have he := mul_le_mul_of_nonneg_right hroot (mul_nonneg hB.le (Real.sqrt_nonneg (q j)))
      linarith only [hd,hb,ih,he]
  have hq : Tendsto q atTop atTop := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const hy
  have hu := (Real.tendsto_sqrt_atTop.comp hq).const_mul_atTop (show 0<4*B by positivity)
  obtain ⟨j,hj⟩ := (hu.eventually_ge_atTop (|s| *∑ n ∈ S, |ordinaryPrimeExcessCoeff n|)).exists
  exact (not_lt_of_ge hj) ((hgrow j).trans_le ((le_abs_self _).trans (by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (fractional_abs_bound _ _) (abs_nonneg s))))

private theorem coefficient_mass_le (S : Finset ℕ) (k : ℕ) (hsub : S ⊆ Finset.Ioc 0 k) :
    ∑ n ∈ S, |ordinaryPrimeExcessCoeff n| ≤ (1+Real.log 4)*k := by
  let P := S.filter Nat.Prime
  have hs (n : ℕ) (hn : n ∈ S) :
      |ordinaryPrimeExcessCoeff n| ≤ (if n.Prime then Real.log n else 0)+1 := by
    have hp : 0<n := (Finset.mem_Ioc.mp (hsub hn)).1
    have hnon : 0 ≤ (if n.Prime then Real.log (n:ℝ) else 0) := by
      split_ifs <;> first | exact Real.log_natCast_nonneg _ | exact le_rfl
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg hnon,abs_one])
  have hP : P ⊆ Nat.primesLE k := by
    intro n hn
    obtain ⟨hm,hp⟩ := Finset.mem_filter.mp hn
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Ioc.mp (hsub hm)).2,hp⟩
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hP
    (fun n _ _ => Real.log_natCast_nonneg n)
  have hc : S.card ≤ k := by simpa only [Nat.card_Ioc,Nat.sub_zero] using Finset.card_le_card hsub
  have hlog : (∑ n ∈ S, if n.Prime then Real.log (n:ℝ) else 0) ≤ k*Real.log 4 := by
    rw [← Finset.sum_filter]
    exact hsum.trans (_root_.RHTower.Sieve.sum_log_primesLE_le k)
  apply (Finset.sum_le_sum hs).trans
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
  linarith only [hlog,(show (S.card:ℝ)≤k by exact_mod_cast hc)]

/-- Absolute odd-quotient discrepancy on any subset of the first k positive integers. -/
theorem oddQuotientPrimeExcess_le (S : Finset ℕ) (k H : ℕ) (hsub : S ⊆ Finset.Ioc 0 k) :
    |oddQuotientPrimeExcess S H| ≤ (1+Real.log 4)*k := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply le_trans _ (coefficient_mass_le S k hsub)
  apply Finset.sum_le_sum
  intro n _
  split_ifs <;> first | exact le_rfl | simpa only [abs_zero] using abs_nonneg _

/-- Removing every integer up to the square root costs at most a fixed
multiple of that square root, even for arbitrary subsets of odd quotients. -/
theorem oddQuotientPrimeExcess_sqrt_cost (S : Finset ℕ) (hS : ∀ n ∈ S, 0<n) (H : ℕ) :
    |oddQuotientPrimeExcess S H-oddQuotientPrimeExcess (S.filter (fun n => Real.sqrt H < n)) H|
      ≤ (1+Real.log 4)*Real.sqrt H := by
  let k := ⌊Real.sqrt H⌋₊
  let P := fun n : ℕ => Real.sqrt H < n
  let f := fun n : ℕ => if H/n%2=1 then ordinaryPrimeExcessCoeff n else 0
  have he := Finset.sum_filter_add_sum_filter_not S P f
  change |(∑ n ∈ S, f n)-(∑ n ∈ S.filter P, f n)| ≤ _
  rw [← he,add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (g := fun n => |ordinaryPrimeExcessCoeff n|) (fun n _ => ?_)).trans
  · apply (coefficient_mass_le _ k (fun n hn => ?_)).trans
    · exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg _))
        (by positivity)
    · obtain ⟨hm,h⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_Ioc.mpr ⟨hS n hm,Nat.le_floor (le_of_not_gt h)⟩
  · dsimp only [f]; split_ifs <;> first | exact le_rfl | simpa only [abs_zero] using abs_nonneg _

#print axioms exists_large_oddQuotientPrimeExcess
#print axioms oddQuotientPrimeExcess_sqrt_cost
end GaloisForLFunctions.ExclusionOfTheCriticalState
