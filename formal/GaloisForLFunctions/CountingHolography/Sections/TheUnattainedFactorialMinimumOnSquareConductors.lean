import GaloisForLFunctions.CountingHolography.Sections.PrimeCoordinatesOfBalancedFactorialValues
import GaloisForLFunctions.CountingHolography.Sections.ANegativePrimeWindowAtEveryMultiplicity
import GaloisForLFunctions.ArithmeticPositiveDuality.ArchimedeanPositiveDefiniteFunctionsLiveOnTheKroneckerLine

/-! # Strict factorial minimax on square conductors

Every prime of the outer contact window has a negative valuation of modulus
less than the prime itself throughout the range m squared at most c n cubed.
Each such prime prevents an exact division of the price between Stirling
entropy and remainder, irrespective of the maximum factorial degree.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology AbsoluteGeometryOfSpecZ _root_.RHTower ArithmeticPositiveDuality

private theorem log_value {q : ℚ} (hq : 0 < q) : primeLogValue (valFinsupp q)=Real.log (q:ℝ) := by
  let u : posUnits := ⟨Units.mk0 q hq.ne',hq⟩
  simpa only [primeLogValue,Finsupp.linearCombination_apply,Finsupp.sum,zsmul_eq_mul] using
    (log_eq_sum_valFinsupp u).symm

/-- At a finite horizon the conditions on the ordinary rational price and
exponentiated entropy are entirely local at the primes. -/
theorem factorial_prices_iff_rational_valuations {L : ℕ} (hL : 10 ≤ L)
    {q E : ℚ} (hq : 0 < q) (hE : 0 < E) :
    (Real.log (q:ℝ),Real.log (E:ℝ)) ∈ factorialJointImage L ↔
      ∀ p : Nat.Primes, (L < p → padicValRat p q=0 ∧ padicValRat p E=0) ∧
        ((p:ℤ) ∣ padicValRat p E) ∧ ((p:ℕ)=L → padicValRat p E=(p:ℤ)*padicValRat p q) := by
  rw [← log_value hq,← log_value hE]
  exact factorialJointImage_iff_prime_coordinates hL _ _

private theorem no_half {q : ℚ} (hq : 0 < q) {p : ℕ} (hp : p.Prime)
    (hneg : deningerRatExp q p < 0) (hlo : -(p:ℤ) < deningerRatExp q p) (L : ℕ) :
    (Real.log (q:ℝ),Real.log (q:ℝ)/2) ∉ factorialJointImage L := by
  rintro ⟨c,hc,hb,he⟩
  let M := max 10 L
  have hm : (Real.log (q:ℝ),Real.log (q:ℝ)/2) ∈ factorialJointImage M :=
    ⟨c,fun j hj => hc j ((le_max_right 10 L).trans_lt hj),hb,he⟩
  rw [← log_value hq] at hm
  have hd := ((factorial_half_price_attainable_iff (le_max_left 10 L) (valFinsupp q)).mp hm ⟨p,hp⟩).2
  change 2*(p:ℤ) ∣ padicValRat p q at hd
  rw [← deningerRatExp_apply_of_prime hp] at hd
  obtain ⟨k,hk⟩ := hd
  have hp' : 0 < (p:ℤ) := Int.natCast_pos.mpr hp.pos
  have hk' : k < 0 := by
    by_contra! h
    rw [hk] at hneg
    exact hneg.not_ge (mul_nonneg (by positivity) h)
  have hmul := mul_le_mul_of_nonneg_left (show k ≤ -1 by omega) (show 0 ≤ 2*(p:ℤ) by positivity)
  linarith only [hlo,hk,hmul,hp']

/-- The entire negative prime window has nonzero valuations too small to
be divisible by the corresponding prime, uniformly up to m squared ≤ c n cubed. -/
theorem successorSquare_outer_exponents_proper :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ {m p : ℕ}, 0 < m → (m:ℝ)^2 ≤ c*(n:ℝ)^3 →
      p ∈ successorSquareWindowPrimes n →
      let v := deningerRatExp (ordinaryPrimeGenerator (m • successorSquareTriple n)) p
      -(p:ℤ) < v ∧ v < 0 := by
  obtain ⟨C,hC,h⟩ := contactMultiplicity_size
  have hC' : 0 < C := zero_lt_one.trans_le hC
  refine ⟨1/(256*C),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop 4] with n hn
  intro m p hm hmn hw
  let d := successorSquareTriple n
  let a := m • d
  let L := 3*windowEnd ((2*n+1)^2+1)
  let r := resolution a
  let q := ordinaryPrimeGenerator a
  let W := successorSquareWindowScale n
  let v := deningerRatExp q p
  obtain ⟨hi,hp⟩ := mem_filter.mp hw
  have hwB := successorSquareWindowScale_bounds n
  have hL : W/3 < (p:ℝ) := (Nat.floor_lt (by linarith only [hwB.2.1] : 0 ≤ W/3)).mp (mem_Ioc.mp hi).1
  have hnp : (n:ℝ)^2/3 < p := (div_le_div_of_nonneg_right hwB.1 (by norm_num)).trans_lt hL
  have hpr : p ∣ q.den := (dvd_prod_of_mem id hw).trans (successorSquare_window_product_dvd (by omega) hm)
  letI : Fact p.Prime := ⟨hp⟩
  have hv : v < 0 := by
    by_contra! hn'
    change 0 ≤ deningerRatExp q p at hn'
    rw [deningerRatExp_apply_of_prime hp q] at hn'
    exact (HTGeometry.Arithmetic.nonneg_val_iff_not_dvd_den p q).mp hn' hpr
  have hs : p ∈ (Icc 2 L).filter Nat.Prime := by
    by_contra hn'
    have hval := ordinaryPrimeGenerator_exponent a p
    rw [if_neg hn'] at hval
    exact hv.ne hval
  have hfloor : v=⌊contactMultiplicity (packet a) L r p⌋ := by
    rw [show v=deningerRatExp (ordinaryPrimeGenerator a) p from rfl,ordinaryPrimeGenerator_exponent,if_pos hs]
  have hn' : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hroot : (n:ℝ)/2 ≤ Real.sqrt p := by
    have hh : ((n:ℝ)/2)^2 ≤ p := by linarith only [hnp,sq_nonneg (n:ℝ)]
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ (n:ℝ)/2)] using Real.sqrt_le_sqrt hh
  have hbase := h _ d L r p
  have hmass := pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) (successorSquareTriple_mass n) 2
  have hraw : |contactMultiplicity (packet a) L r p| ≤ (n:ℝ)^2/8 := by
    rw [show a=m • d from rfl,packet_smul,contactMultiplicity_scale,abs_mul,abs_of_nonneg (sq_nonneg _)]
    have hpc : (m:ℝ)^2*(C*(4:ℝ)^2/Real.sqrt p) ≤ (n:ℝ)^2/8 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hp.pos))).mpr
      have hmn' : (m:ℝ)^2*(256*C) ≤ (n:ℝ)^3 := by
        apply (le_div_iff₀ (by positivity : 0<256*C)).mp
        simpa only [one_div,div_eq_mul_inv,mul_comm] using hmn
      linarith only [hmn',mul_le_mul_of_nonneg_left hroot (by positivity : 0 ≤ (n:ℝ)^2/8)]
    exact (mul_le_mul_of_nonneg_left (hbase.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hmass hC'.le) (Real.sqrt_nonneg _))) (sq_nonneg _)).trans hpc
  have hf := Int.sub_one_lt_floor (contactMultiplicity (packet a) L r p)
  rw [← hfloor] at hf
  have hn2 := mul_le_mul hn' hn' (by norm_num) (Nat.cast_nonneg n)
  have hsmall : -(p:ℝ) < (v:ℝ) := by
    linarith only [hn2,hnp,hraw,hf,neg_abs_le (contactMultiplicity (packet a) L r p)]
  exact ⟨by exact_mod_cast hsmall,hv⟩

/-- No finite factorial presentation of the ordinary generator in this
multiplicity range splits its logarithm into two equal Stirling terms. -/
theorem successorSquare_half_price_unattained :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, ∀ {m : ℕ}, 0 < m → (m:ℝ)^2 ≤ c*(n:ℝ)^3 →
      ∀ L : ℕ, let q := ordinaryPrimeGenerator (m • successorSquareTriple n)
        (Real.log (q:ℝ),Real.log (q:ℝ)/2) ∉ factorialJointImage L := by
  obtain ⟨c,hc,he⟩ := successorSquare_outer_exponents_proper
  refine ⟨c,hc,?_⟩
  filter_upwards [he,successorSquare_denominator_window_mass] with n h hmass
  intro m hm hmn L
  have hnon : (successorSquareWindowPrimes n).Nonempty := by
    by_contra! hempty
    rw [hempty,sum_empty] at hmass
    linarith only [hmass,(successorSquareWindowScale_bounds n).2.1]
  obtain ⟨p,hp⟩ := hnon
  obtain ⟨h₁,h₂⟩ := h hm hmn hp
  exact no_half (prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _)
    (mem_filter.mp hp).2 h₂ h₁ L

#print axioms factorial_prices_iff_rational_valuations
#print axioms successorSquare_outer_exponents_proper
#print axioms successorSquare_half_price_unattained

end GaloisForLFunctions.CountingHolography.Sections
