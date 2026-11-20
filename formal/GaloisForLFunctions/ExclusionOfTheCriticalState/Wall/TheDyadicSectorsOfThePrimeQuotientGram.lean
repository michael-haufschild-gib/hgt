import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePeriodGramOfOddPrimeQuotients
import GaloisForLFunctions.BiScaleUncertainty.BarbanVehovLogarithmicDiagonalAndKerPCauchyPinch

/-!
# Dyadic sectors of the prime-quotient Gram form

A quotient digit changes sign under translation by its denominator. The
surviving complete-period entry is the gcd-square Franel kernel precisely
when the denominators have the same two-adic order. The Jordan-totient
divisor transform diagonalizes the actual prime discrepancy on each such
class.
-/

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open Finset BiScaleUncertainty
noncomputable section
open scoped Classical

private theorem odd_reduced_iff_orders {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    ((n/n.gcd m)%2=1 ∧ (m/n.gcd m)%2=1) ↔ n.factorization 2=m.factorization 2 := by
  have odd_iff (x : ℕ) (hx : 0<x) : x%2=1 ↔ x.factorization 2=0 := by
    rw [Nat.factorization_eq_zero_iff]
    simp only [Nat.prime_two,not_true_eq_false,false_or,hx.ne',or_false]
    omega
  have hl := Nat.gcd_le_left m hn
  have hr := Nat.gcd_le_right n hm
  have hg := Nat.gcd_pos_of_pos_left m hn
  rw [odd_iff _ (Nat.div_pos hl hg),odd_iff _ (Nat.div_pos hr hg),
    Nat.factorization_div (Nat.gcd_dvd_left n m),Nat.factorization_div (Nat.gcd_dvd_right n m),
    Nat.factorization_gcd hn.ne' hm.ne']
  change (_ - min (n.factorization 2) (m.factorization 2) = 0 ∧
    _ - min (n.factorization 2) (m.factorization 2) = 0) ↔ _
  omega

/-- Two numerator sign readings correlate exactly at equal two-adic order. -/
theorem quotientGramMean_eq_franel {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    quotientGramMean n m = if n.factorization 2=m.factorization 2 then
      (n.gcd m : ℝ)^2/((n:ℝ)*m) else 0 := by
  simp only [quotientGramMean_gcd hn hm,odd_reduced_iff_orders hn hm]

/-- Coefficients retained at two-adic order v. -/
def dyadicQuotientBand (c : ℕ → ℝ) (v n : ℕ) : ℝ :=
  if n.factorization 2=v then c n else 0

/-- All two-adic orders occurring among the denominators. -/
def quotientOrders (N : ℕ) : Finset ℕ := (Icc 1 N).image fun n => n.factorization 2

/-- The complete-period covariance splits into independent two-adic classes.
Each class admits the existing Jordan-totient square decomposition. -/
theorem quotientGram_jordan_diagonal (c : ℕ → ℝ) (N : ℕ) :
    ∑ z ∈ (Icc 1 N) ×ˢ (Icc 1 N), c z.1*c z.2*quotientGramMean z.1 z.2 =
      ∑ v ∈ quotientOrders N, ∑ e ∈ Icc 1 N, jordanTotient2 e*
        (selbergMultiplesCoord N (dyadicQuotientBand c v) e)^2 := by
  let S := Icc 1 N
  let G (z : ℕ × ℕ) := (z.1.gcd z.2 : ℝ)^2/((z.1:ℝ)*z.2)
  have entries (z : ℕ × ℕ) (hz : z∈S ×ˢ S) :
      c z.1*c z.2*quotientGramMean z.1 z.2 =
        ∑ v ∈ quotientOrders N, dyadicQuotientBand c v z.1*dyadicQuotientBand c v z.2*G z := by
    obtain ⟨ha,hb⟩ := mem_product.mp hz
    have hv : z.1.factorization 2 ∈ quotientOrders N := mem_image.mpr ⟨z.1,ha,rfl⟩
    rw [sum_eq_single_of_mem (z.1.factorization 2) hv,
      quotientGramMean_eq_franel (mem_Icc.mp ha).1 (mem_Icc.mp hb).1]
    · by_cases he : z.1.factorization 2=z.2.factorization 2 <;> simp [dyadicQuotientBand,he,G,eq_comm]
    · intro v hv hne
      simp only [dyadicQuotientBand,if_neg (Ne.symm hne),zero_mul]
  rw [sum_congr rfl entries,sum_comm]
  exact sum_congr rfl fun v _ => franelGcdQuadraticForm_eq_jordanTotient2_diagonal N _

/-- The decomposition holds on a single common period, including for signed
prime coefficients. No limiting argument or positivity assumption on c enters. -/
theorem quotientReading_square_period (c : ℕ → ℝ) (N : ℕ) :
    let P := 2*N.factorial
    ∑ H ∈ range P, (∑ n ∈ Icc 1 N, c n*quotientSign n H)^2 =
      (P:ℝ)*∑ v ∈ quotientOrders N, ∑ e ∈ Icc 1 N, jordanTotient2 e*
        (selbergMultiplesCoord N (dyadicQuotientBand c v) e)^2 := by
  let P := 2*N.factorial
  let S := Icc 1 N
  have pair (z : ℕ × ℕ) (hz : z∈S ×ˢ S) :
      ∑ H ∈ range P, quotientSign z.1 H*quotientSign z.2 H = (P:ℝ)*quotientGramMean z.1 z.2 := by
    obtain ⟨ha,hb⟩ := mem_product.mp hz
    obtain ⟨ha₀,haN⟩ := mem_Icc.mp ha
    obtain ⟨hb₀,hbN⟩ := mem_Icc.mp hb
    have hd : 2*z.1.lcm z.2 ∣ P := Nat.mul_dvd_mul_left 2 (Nat.lcm_dvd
      (Nat.dvd_factorial ha₀ haN) (Nat.dvd_factorial hb₀ hbN))
    have h := quotientSign_terminal_error ha₀ hb₀ P
    simp only [Nat.mod_eq_zero_of_dvd hd,min_eq_left (Nat.zero_le _),Nat.cast_zero,zero_mul,
      abs_nonpos_iff,sub_eq_zero] at h
    exact h
  have expand (H : ℕ) : (∑ n ∈ S, c n*quotientSign n H)^2 =
      ∑ z ∈ S ×ˢ S, (c z.1*c z.2)*(quotientSign z.1 H*quotientSign z.2 H) := by
    rw [sq,sum_mul,sum_product]
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring
  rw [← quotientGram_jordan_diagonal]
  change (∑ H ∈ range P, (∑ n ∈ S, c n*quotientSign n H)^2) =
    (P:ℝ)*∑ z ∈ S ×ˢ S, c z.1*c z.2*quotientGramMean z.1 z.2
  rw [sum_congr rfl (fun H _ => expand H),sum_comm,mul_sum]
  exact sum_congr rfl fun z hz => by rw [← mul_sum,pair z hz]; ring

/-- Exact common-numerator second moment of twice the centered odd-quotient
ordinary prime excess on the whole fixed band. -/
theorem centeredPrimeReading_jordan_square (N : ℕ) :
    ∑ H ∈ range (2*N.factorial), (centeredQuotientReading (Icc 1 N) H)^2 =
      (2*N.factorial : ℕ)*∑ v ∈ quotientOrders N, ∑ e ∈ Icc 1 N, jordanTotient2 e*
        (selbergMultiplesCoord N (dyadicQuotientBand ordinaryPrimeExcessCoeff v) e)^2 := by
  simp_rw [centeredQuotientReading_eq]
  exact quotientReading_square_period _ _

/-- All odd-denominator readings reverse together after any odd common
multiple. Thus the genuinely prime part, away from 2, has just one binary
choice on each odd-step progression, regardless of its number of primes. -/
theorem odd_band_quotient_phase (S : Finset ℕ) (a : ℕ → ℝ) {U : ℕ} (hu : Odd U)
    (hd : ∀ n∈S, n∣U) (H q : ℕ) :
    (∑ n ∈ S, a n*quotientSign n (H+q*U)) =
      (-1:ℝ)^q*(∑ n ∈ S, a n*quotientSign n H) := by
  rw [mul_sum]
  refine sum_congr rfl fun n hn => ?_
  obtain ⟨v,hv⟩ := hd n hn
  have hnpos : 0<n := Nat.pos_of_dvd_of_pos (hd n hn) (by obtain ⟨i,hi⟩ := hu; omega)
  have hvodd : Odd v := (Nat.odd_mul.mp (hv ▸ hu)).2
  rw [show H+q*U=H+n*(v*q) by rw [hv]; ring,quotientSign_add_multiple hnpos,pow_mul,hvodd.neg_one_pow]
  ring

/-- For odd-denominator bands the two orientations are exact partners.
In each pair of numerators separated by the odd period, exactly one can
realize a strict positive/negative excursion if and only if the unsigned
amplitudes clear both thresholds and the two readings have opposite signs. -/
theorem odd_band_opposite_count (S : Finset ℕ) (a b : ℕ → ℝ) {U : ℕ} (hu : Odd U)
    (hd : ∀ n∈S, n∣U) (H : ℕ) {s t : ℝ} (hs : 0<s) (ht : 0<t) :
    let A := fun h => ∑ n ∈ S, a n*quotientSign n h
    let B := fun h => ∑ n ∈ S, b n*quotientSign n h
    ((range (2*U)).filter fun q => s≤A (H+q) ∧ B (H+q)≤ -t).card =
      ((range U).filter fun q => s≤|A (H+q)| ∧ t≤|B (H+q)| ∧ A (H+q)*B (H+q)<0).card := by
  let A := fun h => ∑ n ∈ S, a n*quotientSign n h
  let B := fun h => ∑ n ∈ S, b n*quotientSign n h
  have shift (q : ℕ) (c : ℕ → ℝ) :
      (∑ n ∈ S, c n*quotientSign n (H+(U+q))) = -(∑ n ∈ S, c n*quotientSign n (H+q)) := by
    simpa only [one_mul,pow_one,neg_one_mul,Nat.add_right_comm,Nat.add_assoc,Nat.add_comm U q] using
      odd_band_quotient_phase S c hu hd (H+q) 1
  let yes (u v : ℝ) : ℕ := if s≤u ∧ v≤ -t then 1 else 0
  let opp (u v : ℝ) : ℕ := if s≤|u| ∧ t≤|v| ∧ u*v<0 then 1 else 0
  have pair (u v : ℝ) : yes u v+yes (-u) (-v)=opp u v := by
    rcases le_total 0 u with hu|hu <;> rcases le_total 0 v with hv|hv
    · simp [yes,opp,abs_of_nonneg hu,abs_of_nonneg hv,not_lt.mpr (mul_nonneg hu hv),
        show ¬v≤ -t by linarith only [hv,ht],show ¬s≤ -u by linarith only [hu,hs]]
    · by_cases h : s≤u ∧ t≤ -v
      · have hneg := mul_neg_of_pos_of_neg (hs.trans_le h.1) (by linarith only [ht,h.2] : v<0)
        simp [yes,opp,abs_of_nonneg hu,abs_of_nonpos hv,h.1,h.2,hneg,
          show v≤ -t by linarith only [h.2],show ¬s≤ -u by linarith only [hu,hs]]
      · simp [yes,opp,abs_of_nonneg hu,abs_of_nonpos hv,show ¬(s≤u ∧ v≤ -t) by
          rintro ⟨h₁,h₂⟩; exact h ⟨h₁,by linarith only [h₂]⟩,
          show ¬(s≤u ∧ t≤ -v ∧ u*v<0) from fun he => h ⟨he.1,he.2.1⟩,
          show ¬s≤ -u by linarith only [hu,hs]]
    · by_cases h : s≤ -u ∧ t≤v
      · have hneg := mul_neg_of_neg_of_pos (by linarith only [hs,h.1] : u<0) (ht.trans_le h.2)
        simp [yes,opp,abs_of_nonpos hu,abs_of_nonneg hv,h.1,h.2,hneg,
          show ¬s≤u by linarith only [hu,hs]]
      · simp [yes,opp,abs_of_nonpos hu,abs_of_nonneg hv,h,
          show ¬(s≤ -u ∧ t≤v ∧ u*v<0) from fun he => h ⟨he.1,he.2.1⟩,
          show ¬s≤u by linarith only [hu,hs]]
    · simp [yes,opp,abs_of_nonpos hu,abs_of_nonpos hv,not_lt.mpr (mul_nonneg_of_nonpos_of_nonpos hu hv),
        show ¬s≤u by linarith only [hu,hs],show ¬t≤v by linarith only [hv,ht]]
  let E (q : ℕ) := s≤A (H+q) ∧ B (H+q)≤ -t
  let F (q : ℕ) := s≤|A (H+q)| ∧ t≤|B (H+q)| ∧ A (H+q)*B (H+q)<0
  change ((range (2*U)).filter E).card=((range U).filter F).card
  calc
    _ = ∑ q ∈ range (2*U), yes (A (H+q)) (B (H+q)) := (sum_boole (R:=ℕ) E _).symm
    _ = ∑ q ∈ range U, opp (A (H+q)) (B (H+q)) := by
      rw [Nat.two_mul,sum_range_add,← sum_add_distrib]
      refine sum_congr rfl fun q _ => ?_
      rw [show A (H+(U+q))= -A (H+q) from shift q a,show B (H+(U+q))= -B (H+q) from shift q b,pair]
    _ = _ := sum_boole (R:=ℕ) F _


end
end GaloisForLFunctions.ExclusionOfTheCriticalState
