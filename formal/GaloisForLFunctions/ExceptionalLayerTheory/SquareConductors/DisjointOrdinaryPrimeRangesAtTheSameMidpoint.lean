import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimitivePrimePriceBeyondAMovingCofactorCut
import GaloisForLFunctions.RHTower.SqrtTelescopeSums

/-!
# Disjoint ranges of ordinary prime factors at one midpoint

A cutoff at Q costs VQ over V divisor rows. Summing the proper powers
at their divided endpoints costs √(nV). Thus the price can be read in
different prime ranges at the same power accuracy.
-/

noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Uniform error at two independent integer cuts. The proper-power cost
has square-root dependence on the number of cofactor divisors. -/
theorem two_cut_prime_price_error :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {n Q V : ℕ}, 0 < n → Q ≤ 2*n → 1 ≤ V → V ≤ 4*n →
      |remainingPrimitivePrimePrice n Q V-primitiveProjectedFactorial n V-primeMidpointPrice n| ≤
        squarefreeDivisorMass n*((V:ℝ)*(7*(Q:ℝ)+Real.log n)+A*Real.sqrt n*Real.sqrt V) := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨4*|C|,by positivity,?_⟩
  intro n Q V hn hQ hV hVn
  have hM : 0 ≤ squarefreeDivisorMass n := sum_nonneg fun _ _ => abs_nonneg _
  have hi : Ioc 0 Q=Icc 1 Q := by ext p; simp only [mem_Ioc,mem_Icc]; omega
  have hpsi : Chebyshev.psi Q ≤ 7*Q := by
    simpa only [Chebyshev.psi,Nat.floor_natCast,hi] using _root_.RHTower.sum_vonMangoldt_Icc_le_seven Q
  let K := 2*|C|*Real.sqrt n
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hrow (e : ℕ) : Chebyshev.psi (4*n/e:ℕ)-Chebyshev.theta (4*n/e:ℕ) ≤ K*(1/Real.sqrt e) := by
    have hc : ((4*n/e:ℕ):ℝ) ≤ ((4*n:ℕ):ℝ)/e := Nat.cast_div_le
    have hf : ((4*n/e:ℕ):ℝ) ≤ (4*(n:ℝ))/e := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hc
    have hs := Real.sqrt_le_sqrt hf
    rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by norm_num : (0:ℝ)≤4),
      show Real.sqrt 4=2 by norm_num] at hs
    exact (hC (4*n/e:ℕ)).trans ((mul_le_mul (le_abs_self C) hs (Real.sqrt_nonneg _) (abs_nonneg _)).trans_eq
      (by dsimp only [K]; ring))
  apply (remaining_prime_price_divided_error hn hQ hV hVn).trans
  rw [←mul_sum]
  apply mul_le_mul_of_nonneg_left _ hM
  calc _ ≤ ∑ e ∈ Icc 1 V, (7*(Q:ℝ)+Real.log n)+K*(1/Real.sqrt e) := by
             exact sum_le_sum fun e _ => by linarith only [hpsi,hrow e]
       _ = (V:ℝ)*(7*(Q:ℝ)+Real.log n)+K*∑ e ∈ Icc 1 V,1/Real.sqrt e := by
             rw [sum_add_distrib,←mul_sum,sum_const,Nat.card_Icc,Nat.add_one_sub_one,nsmul_eq_mul]
       _ ≤ _ := by
             have h := mul_le_mul_of_nonneg_left (_root_.RHTower.sum_inv_sqrt_le V) hK
             dsimp only [K] at h ⊢
             linarith only [h]

#print axioms two_cut_prime_price_error

/-- The lower prime exponent is a and the cofactor exponent is b−a.
Truncating the prime cut at 2n preserves the unit at the first endpoints. -/
def ordinaryPrimeBandPrice (b a : ℝ) (n : ℕ) : ℝ :=
  let x := 4*(n:ℝ)
  let Q := min (2*n) ⌊x^a⌋₊
  let V := ⌊x^(b-a)⌋₊
  remainingPrimitivePrimePrice n Q V-primitiveProjectedFactorial n V

/-- A price marked by a product in the original intervals can only use
primes between these two real endpoints. -/
theorem cofactor_prime_band_support {n p v : ℕ} (hn : 0 < n) (hv : 2 ≤ v) (hpv : p*v ≤ 4*n)
    {b a : ℝ} (hlo : min (2*n) ⌊(4*(n:ℝ))^a⌋₊ < p)
    (hhi : ⌊(4*(n:ℝ))^(b-a)⌋₊ < v) :
    (4*(n:ℝ))^a < p ∧ (p:ℝ) < (4*(n:ℝ))^(1-b+a) := by
  let x := 4*(n:ℝ)
  have hx : 0 < x := by dsimp only [x]; positivity
  have hp2 : p ≤ 2*n := by
    have h := (Nat.mul_le_mul_left p hv).trans hpv
    omega
  have hb : ⌊x^a⌋₊ < p := (min_lt_iff.mp hlo).resolve_left (not_lt.mpr hp2)
  have floor_lt {w : ℝ} {j : ℕ} (h : ⌊w⌋₊ < j) : w < (j:ℝ) :=
    (Nat.lt_floor_add_one w).trans_le (by exact_mod_cast h)
  refine ⟨floor_lt hb,?_⟩
  have hvx : x^(b-a) < (v:ℝ) := floor_lt hhi
  have ppos : 0 < (p:ℝ) := (Real.rpow_pos_of_pos hx _).trans (floor_lt hb)
  have he : x=x^(1-b+a)*x^(b-a) := by
    rw [←Real.rpow_add hx,show 1-b+a+(b-a)=1 by ring,Real.rpow_one]
  have hp' : (p:ℝ)*v ≤ x := by dsimp only [x]; exact_mod_cast hpv
  apply lt_of_mul_lt_mul_right _ (Real.rpow_nonneg hx.le (b-a))
  exact ((mul_lt_mul_of_pos_left hvx ppos).trans_le hp').trans_eq he

#print axioms cofactor_prime_band_support

/-- All translates of a prime interval of logarithmic width 1−b measure
the same midpoint with one error bound independent of the translate. -/
theorem ordinary_prime_bands_measure_midpoint {b ε : ℝ} (_hb : 1/2 ≤ b) (hb1 : b < 1)
    (he : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ), 1-b ≤ a → a ≤ b →
      ∀ (n : ℕ), 1 ≤ n → |ordinaryPrimeBandPrice b a n-primeMidpointPrice n| ≤ C*(n:ℝ)^(b+ε) := by
  obtain ⟨A,hA,hprice⟩ := two_cut_prime_price_error
  let g := 1-b
  have hg : 0 < g := sub_pos.mpr hb1
  let K := 7+1/g+A
  let D := _root_.RHTower.Sieve.divisorBoundConst ε
  have hD : 0 ≤ D := (_root_.RHTower.Sieve.divisorBoundConst_pos he).le
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨D*K*(4:ℝ)^b,by positivity,?_⟩
  intro a ha hab n hn
  let x := 4*(n:ℝ)
  let Q := min (2*n) ⌊x^a⌋₊
  let V := ⌊x^(b-a)⌋₊
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have hn0 := (Nat.cast_pos (α:=ℝ)).mpr hn
  have hx : 1 ≤ x := by dsimp only [x]; linarith only [hn1]
  have hx0 := zero_lt_one.trans_le hx
  have pos (t : ℝ) : 0 < x^t := Real.rpow_pos_of_pos hx0 _
  have mono {u v : ℝ} (h : u ≤ v) : x^u ≤ x^v := Real.rpow_le_rpow_of_exponent_le hx h
  have mult (u v : ℝ) : x^u*x^v=x^(u+v) := (Real.rpow_add hx0 _ _).symm
  have hQ : (Q:ℝ) ≤ x^a := ((Nat.cast_le (α:=ℝ)).mpr (min_le_right _ _)).trans (Nat.floor_le (pos a).le)
  have hV : (V:ℝ) ≤ x^(b-a) := Nat.floor_le (pos _).le
  have hV0 : 1 ≤ V := Nat.le_floor (by simpa only [Nat.cast_one] using Real.one_le_rpow hx (sub_nonneg.mpr hab))
  have hVn : V ≤ 4*n := by
    have h := hV.trans ((mono (by linarith only [ha,hb1] : b-a ≤ 1)).trans_eq (Real.rpow_one _))
    change (V:ℝ) ≤ 4*(n:ℝ) at h
    exact_mod_cast h
  have hprod : (V:ℝ)*Q ≤ x^b :=
    (mul_le_mul hV hQ (Nat.cast_nonneg _) (pos _).le).trans_eq (by rw [mult,sub_add_cancel])
  have hln : Real.log n ≤ Real.log x := Real.log_le_log hn0 (by dsimp only [x]; linarith only [hn1])
  have hlg := Real.log_le_sub_one_of_pos (pos g)
  rw [Real.log_rpow hx0] at hlg
  have hlog : Real.log n ≤ (1/g)*x^g := by
    rw [one_div_mul_eq_div,le_div_iff₀ hg]
    have h := mul_le_mul_of_nonneg_left hln hg.le
    linarith only [h,hlg]
  have hlogV : (V:ℝ)*Real.log n ≤ (1/g)*x^b := by
    apply (mul_le_mul hV hlog (Real.log_natCast_nonneg _) (pos _).le).trans
    rw [mul_left_comm,mult]
    exact mul_le_mul_of_nonneg_left (mono (by dsimp only [g]; linarith only [ha])) (by positivity)
  have hsV : Real.sqrt n*Real.sqrt V ≤ x^b := by
    simp only [Real.sqrt_eq_rpow]
    have hnX : (n:ℝ) ≤ x := by dsimp only [x]; linarith only [hn1]
    have h := mul_le_mul (Real.rpow_le_rpow hn0.le hnX (by norm_num : (0:ℝ)≤1/2))
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hV (by norm_num : (0:ℝ)≤1/2))
      (Real.rpow_nonneg (Nat.cast_nonneg V) _) (pos _).le
    rw [←Real.rpow_mul hx0.le,mult] at h
    exact h.trans (mono (by linarith only [ha]))
  have hm : squarefreeDivisorMass n ≤ D*(n:ℝ)^ε := by
    have h := sum_le_sum (s:=n.divisors) fun d _ =>
      (show |(ArithmeticFunction.moebius d:ℝ)| ≤ 1 by exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n:=d))
    simp only [sum_const,nsmul_eq_mul,mul_one] at h
    exact h.trans (_root_.RHTower.Sieve.card_divisors_le_rpow he (by omega))
  have htotal : (V:ℝ)*(7*(Q:ℝ)+Real.log n)+A*Real.sqrt n*Real.sqrt V ≤ K*x^b := by
    have hs := mul_le_mul_of_nonneg_left hsV hA
    dsimp only [K]
    linarith only [hprod,hlogV,hs]
  apply (hprice hn (min_le_left _ _) hV0 hVn).trans
  have hM : 0 ≤ squarefreeDivisorMass n := sum_nonneg fun _ _ => abs_nonneg _
  apply (mul_le_mul_of_nonneg_left htotal hM).trans
  apply (mul_le_mul_of_nonneg_right hm (mul_nonneg hK (pos _).le)).trans_eq
  dsimp only [x]
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) hn0.le,Real.rpow_add hn0]
  ring

#print axioms ordinary_prime_bands_measure_midpoint

/-- One may choose a different ordinary prime range at each midpoint.
The upper-bound threshold is unchanged because the approximation is uniform. -/
theorem one_prime_range_at_each_midpoint {b : ℝ} (hb : 1/2 ≤ b) (hb1 : b < 1) :
    (∀ t : ℝ, b<t → t<1 → ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∃ a : ℝ, 1-b ≤ a ∧ a ≤ b ∧ ordinaryPrimeBandPrice b a n ≤ C*(n:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ b := by
  rw [←prime_midpoint_upper_spectrum_iff hb]
  constructor
  · intro h t ht ht1
    obtain ⟨C,hC⟩ := h t ht ht1
    obtain ⟨A,_,hA⟩ := ordinary_prime_bands_measure_midpoint hb hb1 (sub_pos.mpr ht)
    refine ⟨C+A,fun n hn => ?_⟩
    obtain ⟨a,ha,hab,hbound⟩ := hC n hn
    have herr := (abs_le.mp (hA a ha hab n hn)).1
    rw [show b+(t-b)=t by ring] at herr
    linarith only [hbound,herr]
  · intro h t ht ht1
    obtain ⟨C,hC⟩ := h t ht ht1
    obtain ⟨A,_,hA⟩ := ordinary_prime_bands_measure_midpoint hb hb1 (sub_pos.mpr ht)
    have hlo : 1-b ≤ b := by linarith only [hb]
    refine ⟨C+A,fun n hn => ⟨b,hlo,le_rfl,?_⟩⟩
    have herr := (abs_le.mp (hA b hlo le_rfl n hn)).2
    rw [show b+(t-b)=t by ring] at herr
    linarith only [hC n hn,herr]

#print axioms one_prime_range_at_each_midpoint

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
