import GaloisForLFunctions.CountingHolography.Sections.TheDenominatorOfTheArithmeticLogarithmicDerivative
import GaloisForLFunctions.CountingHolography.Sections.TheUnattainedFactorialMinimumOnSquareConductors

/-! # A single rational integrality test for factorial entropy

Allowing any finite horizon, the entropy coordinates are precisely those
with integral arithmetic logarithmic derivative. They can already be
realized by balanced factorial identities of price one.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticPositiveDuality AbsoluteGeometryOfSpecZ _root_.RHTower ArithmeticFunction

/-- A prescribed entropy is available at price one if and only if its
arithmetic logarithmic derivative is an integer. -/
theorem factorial_entropy_iff_integral_prime_reciprocal (a : Nat.Primes →₀ ℤ) :
    (∃ L, (0,primeLogValue a) ∈ factorialJointImage L) ↔ (primeReciprocalReading a).den=1 := by
  rw [primeReciprocalReading_den_one_iff]
  constructor
  · rintro ⟨L,c,hc,hb,he⟩
    let M := max 10 L
    have hz : (primeLogValue 0,primeLogValue a) ∈ factorialJointImage M := by
      rw [map_zero]
      exact ⟨c,fun j hj => hc j ((le_max_right 10 L).trans_lt hj),hb,he⟩
    have h := (factorialJointImage_iff_prime_coordinates (le_max_left 10 L) 0 a).mp hz
    exact fun p => (h p).2.1
  · intro h
    let L := max 10 (a.support.sup Subtype.val+1)
    have hz {p : Nat.Primes} (hp : L ≤ p) : a p=0 := by
      by_contra hn
      have hle := Finset.le_sup (f := Subtype.val) (Finsupp.mem_support_iff.mpr hn)
      exact (Nat.lt_succ_of_le hle).not_ge ((le_max_right 10 _).trans hp)
    refine ⟨L,?_⟩
    rw [← map_zero primeLogValue]
    apply (factorialJointImage_iff_prime_coordinates (le_max_left 10 _) 0 a).mpr
    intro p
    exact ⟨fun hp => ⟨rfl,hz hp.le⟩,h p,fun hp => by rw [hz hp.ge,Finsupp.zero_apply,mul_zero]⟩

/-- A half-price entropy is available at some finite horizon exactly for
squares of positive rationals with integral arithmetic logarithmic derivative. -/
theorem factorial_half_price_iff_square_integral_derivative {q : ℚ} (hq : 0 < q) :
    (∃ L, (Real.log (q:ℝ),Real.log (q:ℝ)/2)∈factorialJointImage L) ↔
    ∃ r : ℚ, 0 < r ∧ q=r^2 ∧ (primeReciprocalReading (valFinsupp r)).den=1 := by
  let a := valFinsupp q
  rw [← primeLogValue_valFinsupp hq]
  constructor
  · rintro ⟨L,c,hc,hb,hpair⟩
    let M := max 10 L
    have hreal : (primeLogValue a,primeLogValue a/2)∈factorialJointImage M :=
      ⟨c,fun j hj => hc j ((le_max_right 10 L).trans_lt hj),hb,hpair⟩
    have hd := (factorial_half_price_attainable_iff (le_max_left 10 L) a).mp hreal
    let b := a.mapRange (fun z : ℤ => z/2) (by decide)
    have hcoords (p : Nat.Primes) : a p=b p+b p ∧ (p:ℤ)∣b p := by
      obtain ⟨k,hk⟩ := (hd p).2
      change a p=a p/2+a p/2 ∧ (p:ℤ)∣a p/2
      rw [hk,mul_assoc]
      have he : 2*((p:ℤ)*k)/2=(p:ℤ)*k := by omega
      rw [he]
      exact ⟨by ring,dvd_mul_right _ _⟩
    let r : ℚ := ((finsuppUnit b : ℚˣ):ℚ)
    have hr : 0 < r := (finsuppUnit b).property
    have hb' : valFinsupp r=b := valFinsupp_finsuppUnit b
    have he : a=b+b := Finsupp.ext fun p => (hcoords p).1
    refine ⟨r,hr,?_,(primeReciprocalReading_den_one_iff _).mpr (fun p => by rw [hb']; exact (hcoords p).2)⟩
    have hlog : Real.log (q:ℝ)=Real.log ((r^2:ℚ):ℝ) := by
      rw [← primeLogValue_valFinsupp hq,← primeLogValue_valFinsupp (sq_pos_of_pos hr),sq,
        valFinsupp_mul hr.ne' hr.ne',hb']
      exact congrArg primeLogValue he
    exact_mod_cast Real.log_injOn_pos (show (0:ℝ) < (q:ℝ) by exact_mod_cast hq)
      (show (0:ℝ) < ((r^2:ℚ):ℝ) by exact_mod_cast sq_pos_of_pos hr) hlog
  · rintro ⟨r,hr,rfl,hd⟩
    let L := max 10 ((valFinsupp (r^2)).support.sup Subtype.val+1)
    refine ⟨L,(factorial_half_price_attainable_iff (le_max_left 10 _) _).mpr ?_⟩
    intro p
    refine ⟨fun hp => ?_,?_⟩
    · by_contra hz
      have h := le_sup (f := Subtype.val) (Finsupp.mem_support_iff.mpr hz)
      exact (Nat.lt_succ_of_le h).not_ge ((le_max_right 10 _).trans hp)
    · obtain ⟨k,hk⟩ := (primeReciprocalReading_den_one_iff _).mp hd p
      rw [sq,valFinsupp_mul hr.ne' hr.ne',Finsupp.add_apply,hk]
      exact ⟨k,by ring⟩

private theorem mem_derivative_den {q : ℚ} {p : ℕ} (hp : p.Prime) :
    p∈(primeReciprocalReading (valFinsupp q)).den.primeFactors ↔ ¬ (p:ℤ)∣deningerRatExp q p := by
  let z := primeReciprocalReading (valFinsupp q)
  have he := primeReciprocalReading_den_exponent (valFinsupp q) ⟨p,hp⟩
  change z.den.factorization p=if (p:ℤ)∣padicValRat p q then 0 else 1 at he
  rw [← deningerRatExp_apply_of_prime hp] at he
  change p∈z.den.primeFactors ↔ _
  constructor
  · intro h hd
    have hpos := hp.factorization_pos_of_dvd z.den_nz (Nat.dvd_of_mem_primeFactors h)
    rw [he,if_pos hd] at hpos
    exact hpos.false
  · intro hd
    rw [if_neg hd] at he
    exact Nat.mem_primeFactors.mpr ⟨hp,Nat.dvd_of_factorization_pos (by omega),z.den_nz⟩

/-- The reduced denominator of the derivative on the actual square
generators has quadratic log size, including every prime of the outer window. -/
theorem square_prime_reciprocal_den_order : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop,
    let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
    let d := (primeReciprocalReading (valFinsupp q)).den
    successorSquareWindowPrimes n⊆d.primeFactors ∧ (n:ℝ)^2/12 ≤ Real.log d ∧ Real.log d ≤ C*(n:ℝ)^2 := by
  obtain ⟨A,_,hA⟩ := successorSquare_window_bound
  obtain ⟨c,hc,he⟩ := successorSquare_outer_exponents_proper
  refine ⟨7*A^2,by positivity,?_⟩
  filter_upwards [he,successorSquare_denominator_window_mass,eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually_ge_atTop (1/c)] with n hn hm hp hlarge
  let q := ordinaryPrimeGenerator (n • successorSquareTriple n)
  let z := primeReciprocalReading (valFinsupp q)
  let S := z.den.primeFactors
  let L := 3*windowEnd ((2*n+1)^2+1)
  have hscale : (n:ℝ)^2 ≤ c*(n:ℝ)^3 := by
    have h := mul_le_mul_of_nonneg_right ((div_le_iff₀ hc).mp hlarge) (sq_nonneg (n:ℝ))
    linarith only [h]
  have hw : successorSquareWindowPrimes n⊆S := by
    intro p h
    have hprime := (mem_filter.mp h).2
    obtain ⟨hlo,hhi⟩ := hn hp hscale h
    apply (mem_derivative_den hprime).mpr
    rintro ⟨k,hk⟩
    change -(p:ℤ) < deningerRatExp q p at hlo
    change deningerRatExp q p < 0 at hhi
    rw [hk] at hlo hhi
    have hkneg : k < 0 := lt_of_not_ge fun h => hhi.not_ge (mul_nonneg (by positivity) h)
    have hmul := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) (show (0:ℤ) ≤ p by positivity)
    linarith only [hmul,hlo]
  have hS : S⊆ordinaryPrimeLags L := by
    intro p h
    by_contra hh
    have hp' := Nat.prime_of_mem_primeFactors h
    have hnd := (mem_derivative_den hp').mp h
    have hv := ordinaryPrimeGenerator_exponent (n • successorSquareTriple n) p
    change deningerRatExp q p=if p∈ordinaryPrimeLags L then _ else 0 at hv
    exact hnd (by rw [hv,if_neg hh]; exact dvd_zero _)
  have hsquare : Squarefree z.den := (range_primeReciprocalReading z).mp ⟨_,rfl⟩
  have hlog : Real.log z.den=∑ p ∈ S, Real.log p := by
    have h := congrArg (fun d : ℕ => Real.log (d:ℝ)) (Nat.prod_primeFactors_of_squarefree hsquare)
    rw [Nat.cast_prod,Real.log_prod (fun k h => (Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors h).pos).ne')] at h
    exact h.symm
  refine ⟨hw,?_,?_⟩
  · rw [hlog]
    exact ((div_le_div_of_nonneg_right (successorSquareWindowScale_bounds n).1 (by norm_num)).trans hm).trans
      (sum_le_sum_of_subset_of_nonneg hw fun p _ _ => Real.log_natCast_nonneg _)
  · rw [hlog]
    have hsum : (∑ p ∈ S, Real.log p) ≤ 7*(L:ℝ) := by
      calc _ = ∑ p ∈ S, vonMangoldt p := sum_congr rfl fun p h =>
                (vonMangoldt_apply_prime (Nat.prime_of_mem_primeFactors h)).symm
        _ ≤ _ := (sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => vonMangoldt_nonneg).trans (ordinaryPrimeLagSums L).1
    exact hsum.trans ((mul_le_mul_of_nonneg_left (hA hp) (by norm_num : (0:ℝ) ≤ 7)).trans_eq (by ring))

end GaloisForLFunctions.CountingHolography.Sections
