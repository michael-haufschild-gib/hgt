import GaloisForLFunctions.ExceptionalLayerTheory.SmoothCountsAndTheLargeFactorsOfTheCentralBinomialCoefficient
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusFiniteDeletion

/-!
# The first prime windows of the smooth Haar source

Before two primes above the cutoff can divide the same integer, the smooth
Haar source counts single large primes with odd quotient, up to the parity
of the endpoint. In the first doubling interval every such quotient is one.
-/

noncomputable section

open Finset Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem sum_smoothAF_eq_count (k y : ℕ) :
    (∑ n ∈ Icc 1 k, (CoprimeMobius.smoothAF (↑(Nat.primesLE y) : Set ℕ) n : ℂ)) =
      (smoothIntegerCount k y : ℂ) := by
  classical
  let E : Set ℕ := ↑(Nat.primesLE y)
  have he : (Icc 1 k).filter (CoprimeMobius.IsSmooth E) = Sieve.smoothUpTo (Nat.primesLE y) k := by
    ext n
    rw [mem_filter,Sieve.mem_smoothUpTo,mem_Icc]
    change ((1≤n ∧ n≤k) ∧ n≠0 ∧ n.primeFactors ⊆ Nat.primesLE y) ↔ _
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · exact fun h => ⟨h.1,Nat.ne_of_gt h.1.1,h.2⟩
  simp only [CoprimeMobius.smoothAF_apply,Int.cast_ite,Int.cast_one,Int.cast_zero]
  rw [← sum_filter,show (Icc 1 k).filter (CoprimeMobius.IsSmooth E)=_ from he]
  simp [smoothIntegerCount]

/-- The two smooth counts in the Haar source use the same integer endpoint
before and after division by two. -/
theorem smoothHaarSource_count_floor (y : ℕ) {t : ℝ} (ht : 0<t) :
    pmSmoothHaarSource (y+1) t =
      (smoothIntegerCount ⌊1/t⌋₊ y:ℂ)-2*(smoothIntegerCount (⌊1/t⌋₊/2) y:ℂ) := by
  have hf : ⌊1/(2*t)⌋₊=⌊1/t⌋₊/2 := by
    rw [show 1/(2*t)=(1/t)/(2:ℕ) by push_cast; ring,Nat.floor_div_natCast]
  rw [pmSmoothHaarSource_eq_counts _ ht,hf]
  change (∑ n ∈ Icc 1 _, (CoprimeMobius.smoothAF (↑(Nat.primesLE y):Set ℕ) n:ℂ)) -
    2*(∑ n ∈ Icc 1 _, (CoprimeMobius.smoothAF (↑(Nat.primesLE y):Set ℕ) n:ℂ)) = _
  rw [sum_smoothAF_eq_count,sum_smoothAF_eq_count]

/-- On the square-root window the source is the endpoint parity minus the
number of large primes whose quotient is odd. -/
theorem smoothHaarSource_eq_large_prime_count (y : ℕ) {t : ℝ} (ht : 0<t)
    (hs : ⌊1/t⌋₊<(y+1)^2) :
    pmSmoothHaarSource (y+1) t = (⌊1/t⌋₊%2:ℕ) -
      (((largePrimes ⌊1/t⌋₊ y).filter (fun p => 2∣⌊1/t⌋₊/p+1)).card:ℂ) := by
  let k := ⌊1/t⌋₊
  let P := largePrimes k y
  have hk := count_smooth_and_multiples (y := y) (B := k) le_rfl hs
  have hd := count_smooth_and_multiples (y := y) (B := k) (Nat.div_le_self k 2)
    ((Nat.div_le_self k 2).trans_lt hs)
  have hcell (p : ℕ) : k/p=2*((k/2)/p)+(if 2∣k/p+1 then 1 else 0) := by
    have he : (k/2)/p=(k/p)/2 := by rw [Nat.div_div_eq_div_mul,Nat.div_div_eq_div_mul,mul_comm 2 p]
    rw [he]
    split <;> omega
  have hsum : (∑ p ∈ P, k/p)=2*(∑ p ∈ P, (k/2)/p)+(P.filter (fun p => 2∣k/p+1)).card := by
    calc
      _ = ∑ p ∈ P, (2*((k/2)/p)+(if 2∣k/p+1 then 1 else 0)) := sum_congr rfl fun p _ => hcell p
      _ = _ := by rw [sum_add_distrib,← mul_sum,← sum_filter]; simp
  change _+ (∑ p ∈ P, _) = _ at hk hd
  rw [smoothHaarSource_count_floor y ht]
  change (smoothIntegerCount k y:ℂ)-2*(smoothIntegerCount (k/2) y:ℂ)=
    (k%2:ℕ)-(↑(P.filter (fun p => 2∣k/p+1)).card:ℂ)
  exact_mod_cast (show (smoothIntegerCount k y:ℤ)-2*(smoothIntegerCount (k/2) y:ℤ)=
    (k%2:ℕ)-(↑(P.filter (fun p => 2∣k/p+1)).card:ℤ) by omega)

/-- On the first doubling interval the smooth source recovers the entire
ordinary prime-count increment from the cutoff. -/
theorem smoothHaarSource_first_doubling (y : ℕ) {t : ℝ} (ht : 0<t)
    (hl : y≤⌊1/t⌋₊) (hu : ⌊1/t⌋₊≤2*y) :
    pmSmoothHaarSource (y+1) t = (⌊1/t⌋₊%2:ℕ)-
      ((Nat.primeCounting ⌊1/t⌋₊:ℂ)-(Nat.primeCounting y:ℂ)) := by
  let k := ⌊1/t⌋₊
  have hs : ⌊1/t⌋₊ < (y+1)^2 := by nlinarith only [hu,Nat.zero_le (y*y)]
  have hset : (largePrimes k y).filter (fun p => 2∣k/p+1) = Nat.primesLE k \ Nat.primesLE y := by
    ext p
    have he (hp : p≤k) (hy : y<p) : k/p=1 := by
      have hp0 : 0<p := Nat.zero_lt_of_lt hy
      have hlow := (Nat.one_le_div_iff hp0).mpr hp
      have hupper := (Nat.div_lt_iff_lt_mul hp0).mpr (show k<2*p by dsimp only [k]; omega)
      omega
    simp only [mem_filter,mem_largePrimes,mem_sdiff,Nat.mem_primesLE]
    constructor
    · exact fun h => ⟨h.1.1,fun hpy => h.1.2.not_ge hpy.1⟩
    · rintro ⟨hp,hpy⟩
      have hy : y<p := lt_of_not_ge (fun h => hpy ⟨h,hp.2⟩)
      exact ⟨⟨hp,hy⟩,by rw [he hp.1 hy]; norm_num⟩
  rw [smoothHaarSource_eq_large_prime_count y ht hs]
  change (k%2:ℕ)-(↑((largePrimes k y).filter (fun p => 2∣k/p+1)).card:ℂ)=_
  rw [hset,card_sdiff_of_subset (Nat.primesLE_mono hl),Nat.cast_sub (card_le_card (Nat.primesLE_mono hl))]
  simp only [Nat.primesLE_card_eq_primeCounting,k]

/-- The whole fixed interval of primes between two and three times N has
quotient one at every endpoint from three to four times N. -/
theorem smoothHaarSource_outer_window {N y : ℕ} (hy : y≤2*N) (hs : 4*N<(y+1)^2)
    {t : ℝ} (ht : 0<t) (hl : 3*N≤⌊1/t⌋₊) (hu : ⌊1/t⌋₊≤4*N) :
    ((Nat.primeCounting (3*N):ℝ)-Nat.primeCounting (2*N)-1 ≤ -(pmSmoothHaarSource (y+1) t).re) ∧
    (-(pmSmoothHaarSource (y+1) t).re ≤ Nat.primeCounting (4*N)) := by
  let k := ⌊1/t⌋₊
  let A := (largePrimes k y).filter (fun p => 2∣k/p+1)
  have hP : Nat.primesLE (2*N) ⊆ Nat.primesLE (3*N) := Nat.primesLE_mono (by omega)
  have hlow : Nat.primesLE (3*N) \ Nat.primesLE (2*N) ⊆ A := by
    intro p hp
    obtain ⟨h₃,h₂⟩ := mem_sdiff.mp hp
    obtain ⟨hp₃,hpr⟩ := Nat.mem_primesLE.mp h₃
    have hp₂ : 2*N<p := lt_of_not_ge fun h => h₂ (Nat.mem_primesLE.mpr ⟨h,hpr⟩)
    have hpk : p≤k := hp₃.trans hl
    have hdiv : k/p=1 := by
      have hlo := (Nat.one_le_div_iff hpr.pos).mpr hpk
      have hhi := (Nat.div_lt_iff_lt_mul hpr.pos).mpr (show k<2*p by dsimp only [k]; omega)
      omega
    exact mem_filter.mpr ⟨mem_largePrimes.mpr ⟨⟨hpk,hpr⟩,hy.trans_lt hp₂⟩,by rw [hdiv]; norm_num⟩
  have hupp : A ⊆ Nat.primesLE (4*N) := by
    intro p hp
    exact Nat.primesLE_mono hu (mem_filter.mp (mem_filter.mp hp).1).1
  have hc := card_le_card hlow
  rw [card_sdiff_of_subset hP] at hc
  have hcount := card_le_card hP
  simp only [Nat.primesLE_card_eq_primeCounting] at hc hcount
  have hu' := card_le_card hupp
  rw [Nat.primesLE_card_eq_primeCounting] at hu'
  have hlowR : (Nat.primeCounting (3*N):ℝ)-Nat.primeCounting (2*N)≤A.card := by
    rw [← Nat.cast_sub hcount]
    exact_mod_cast hc
  have hupperR : (A.card:ℝ)≤Nat.primeCounting (4*N) := by exact_mod_cast hu'
  have hmod : ((k%2:ℕ):ℝ)≤1 := by
    exact_mod_cast (show k%2≤1 by omega)
  have he : (pmSmoothHaarSource (y+1) t).re = ((k%2:ℕ):ℝ)-A.card := by
    rw [smoothHaarSource_eq_large_prime_count y ht (hu.trans_lt hs)]
    simp only [Complex.sub_re,Complex.natCast_re,k,A]
  rw [he]
  constructor <;> linarith only [hlowR,hupperR,hmod,Nat.cast_nonneg (α := ℝ) (k%2)]

#print axioms smoothHaarSource_outer_window
#print axioms smoothHaarSource_eq_large_prime_count
#print axioms smoothHaarSource_first_doubling

end GaloisForLFunctions.ExceptionalLayerTheory
