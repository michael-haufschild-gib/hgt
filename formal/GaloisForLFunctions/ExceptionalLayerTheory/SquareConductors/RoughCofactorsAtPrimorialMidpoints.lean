import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheTotientTermInTheReflectedCompositePrice
import Mathlib.NumberTheory.Primorial

/-!
# Rough cofactors at primorial midpoints

The nearest lower multiple of a logarithmic primorial costs only a
square-root error in the one-sided prime midpoint. Every primitive cofactor
at such a center avoids all primes up to the logarithmic sieve level.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Sieve level whose primorial is at most the fourth root of the center. -/
def midpointSieveLevel (n : ℕ) : ℕ := ⌊Real.log n/(4*Real.log 4)⌋₊

private theorem level_primorial_bound {n : ℕ} (hn : 1 ≤ n) :
    (primorial (midpointSieveLevel n):ℝ) ≤ (n:ℝ)^(1/4:ℝ) := by
  let y := midpointSieveLevel n
  have hn' := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hy : (y:ℝ) ≤ Real.log n/(4*Real.log 4) := Nat.floor_le (div_nonneg (Real.log_nonneg hn') (by positivity))
  have hh := Real.log_le_log (Nat.cast_pos.mpr (primorial_pos y))
    ((Nat.cast_le (α:=ℝ)).mpr (primorial_le_four_pow y))
  rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow] at hh
  apply (Real.log_le_log_iff (Nat.cast_pos.mpr (primorial_pos y))
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hn') _)).mp
  rw [Real.log_rpow (zero_lt_one.trans_le hn')]
  linarith only [hh,(le_div_iff₀ (show 0 < 4*Real.log 4 by positivity)).mp hy]

/-- Every integer has a lower primorial multiple within its fourth root.
The level is intrinsic to the sampled center. -/
theorem nearby_primorial_midpoint {n : ℕ} (hn : 1 < n) :
    ∃ m : ℕ, 1 < m ∧ m ≤ n ∧ primorial (midpointSieveLevel m) ∣ m ∧
      (n:ℝ)-(m:ℝ) ≤ (n:ℝ)^(1/4:ℝ) := by
  let L := primorial (midpointSieveLevel n)
  let m := n/L*L
  have hL : 0 < L := primorial_pos _
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn.le
  have hLr : (L:ℝ) ≤ (n:ℝ)^(1/4:ℝ) := level_primorial_bound hn.le
  have hLn : L ≤ n := Nat.cast_le.mp (hLr.trans
    ((Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1/4:ℝ) ≤ 1)).trans_eq (Real.rpow_one _)))
  have hm : m ≤ n := Nat.div_mul_le_self _ _
  have hm0 : 1 < m := by
    by_cases h : L=1
    · simpa only [m,h,Nat.div_one,Nat.mul_one] using hn
    · have hdiv : 1 ≤ n/L := (Nat.le_div_iff_mul_le hL).mpr (by simpa only [one_mul] using hLn)
      have he := Nat.mul_le_mul_right L hdiv
      rw [one_mul] at he
      change 1 < n/L*L
      exact (show 1 < L by omega).trans_le he
  have hlog := Real.log_le_log (Nat.cast_pos.mpr hm0.le) ((Nat.cast_le (α:=ℝ)).mpr hm)
  have hlevels : midpointSieveLevel m ≤ midpointSieveLevel n :=
    Nat.floor_mono (div_le_div_of_nonneg_right hlog (by positivity))
  have hmod := Nat.mod_add_div n L
  have hrem := Nat.mod_lt n hL
  have hdiff : n-m < L := by
    rw [Nat.mul_comm L] at hmod
    change n-(n/L)*L < L
    omega
  have hdiff' : (n:ℝ)-(m:ℝ) ≤ L := by
    have hsum : n ≤ L+m := by omega
    exact sub_le_iff_le_add.mpr (by exact_mod_cast hsum)
  exact ⟨m,hm0,hm,(primorial_dvd_primorial hlevels).trans (dvd_mul_left L (n/L)),hdiff'.trans hLr⟩

#print axioms nearby_primorial_midpoint

private theorem theta_integer_interval_bound {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta b-Chebyshev.theta a ≤ ((b:ℝ)-a)*Real.log b := by
  let f (p : ℕ) := if p.Prime then Real.log (p:ℝ) else 0
  have hf : (∑ p ∈ Ioc a b,f p) ≤ ∑ _ ∈ Ioc a b,Real.log b := by
    apply sum_le_sum
    intro p hp
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hp
    dsimp only [f]
    split_ifs
    · exact Real.log_le_log (Nat.cast_pos.mpr ((Nat.zero_le a).trans_lt hl)) (Nat.cast_le.mpr hu)
    · exact Real.log_natCast_nonneg _
  rw [sum_const,Nat.card_Ioc,nsmul_eq_mul,Nat.cast_sub hab] at hf
  have hj := sum_Ioc_consecutive f (Nat.zero_le a) hab
  simp only [Chebyshev.theta,Nat.floor_natCast,sum_filter]
  dsimp only [f] at hf hj
  linarith only [hf,hj]

private theorem midpoint_upper_shift {m n : ℕ} (hm : m ≤ n) :
    primeMidpointPrice n-primeMidpointPrice m ≤ 6*((n:ℝ)-m)*Real.log (3*(n:ℝ)) := by
  have hh := theta_integer_interval_bound (Nat.mul_le_mul_left 3 hm)
  have hout (k : ℕ) : Chebyshev.theta (k*m:ℕ) ≤ Chebyshev.theta (k*n:ℕ) :=
    Chebyshev.theta_mono ((Nat.cast_le (α:=ℝ)).mpr (Nat.mul_le_mul_left k hm))
  have h2 := hout 2
  have h4 := hout 4
  rw [prime_midpoint_price_eq,prime_midpoint_price_eq]
  push_cast at hh h2 h4 ⊢
  linarith only [hh,h2,h4]

/-- One-sided sampling costs O(√n) at every integer, with an absolute
constant independent of the shifts and of the target exponent. -/
theorem primorial_midpoint_upper_sampling {n : ℕ} (hn : 1 < n) :
    ∃ m : ℕ, 1 < m ∧ m ≤ n ∧ primorial (midpointSieveLevel m) ∣ m ∧
      primeMidpointPrice n ≤ primeMidpointPrice m+6*(Real.log 3+4)*Real.sqrt n := by
  obtain ⟨m,hm,hmn,hdiv,hgap⟩ := nearby_primorial_midpoint hn
  refine ⟨m,hm,hmn,hdiv,?_⟩
  let u := (n:ℝ)^(1/4:ℝ)
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn.le
  have hn' := zero_lt_one.trans_le hn1
  have hu : 1 ≤ u := Real.one_le_rpow hn1 (by norm_num)
  have hu0 := zero_lt_one.trans_le hu
  have hl := Real.log_le_sub_one_of_pos hu0
  have hlu : Real.log u=(1/4:ℝ)*Real.log n := Real.log_rpow hn' _
  have hL3 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3)
  have hg : Real.log (3*(n:ℝ)) ≤ (Real.log 3+4)*u := by
    rw [Real.log_mul (by norm_num) hn'.ne']
    linarith only [hl,hlu,le_mul_of_one_le_right hL3 hu]
  have hu2 : u*u=Real.sqrt n := by
    dsimp only [u]
    rw [←Real.rpow_add hn',show (1/4:ℝ)+1/4=1/2 by norm_num,←Real.sqrt_eq_rpow]
  have hpos : 0 ≤ Real.log (3*(n:ℝ)) := Real.log_nonneg (by linarith only [hn1])
  have h := mul_le_mul hgap hg hpos hu0.le
  change ((n:ℝ)-m)*Real.log (3*(n:ℝ)) ≤ u*((Real.log 3+4)*u) at h
  rw [show u*((Real.log 3+4)*u)=(Real.log 3+4)*(u*u) by ring,hu2] at h
  linarith only [midpoint_upper_shift hmn,h]

#print axioms primorial_midpoint_upper_sampling

/-- At a sampled center all prime divisors of a primitive proper cofactor
exceed the logarithmic level, even at a sharp product endpoint. -/
theorem primorial_midpoint_cofactor_range {b : ℝ} {m p v : ℕ} (hm : 1 < m)
    (hs : primorial (midpointSieveLevel m) ∣ m) (hv : 2 ≤ v) (hc : m.Coprime v)
    (hp : reflectedPrimeCut b m < p) (hcap : p*v ≤ 4*m) :
    midpointSieveLevel m < v.minFac ∧ (v:ℝ) < 2*(m:ℝ)^(1-b) := by
  refine ⟨?_,cofactor_below_reflected_prime_cut (by omega) hp hcap⟩
  have hprime := Nat.minFac_prime (by omega : v ≠ 1)
  have hcop : v.minFac.Coprime m := (hc.of_dvd_right (Nat.minFac_dvd v)).symm
  by_contra! h
  exact (hprime.coprime_iff_not_dvd.mp hcop) ((hprime.dvd_primorial_iff.mpr h).trans hs)

#print axioms primorial_midpoint_cofactor_range

/-- Bounding only the actual large-factor prices on primorial centers,
with their totient centers, has the exact original abscissa threshold. -/
theorem rough_cofactor_midpoint_upper_spectrum {b : ℝ} (hb : 1/2 ≤ b) (hb1 : b < 1) :
    (∀ t : ℝ,b < t → t < 1 → ∃ C : ℝ,∀ m : ℕ,1 < m → primorial (midpointSieveLevel m) ∣ m →
      largePrimeCofactorPrice m (reflectedPrimeCut b m)-reflectedDensity*m.totient ≤ C*(m:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ b := by
  rw [←prime_midpoint_upper_spectrum_iff hb]
  constructor
  · intro h t ht ht1
    obtain ⟨C,hC⟩ := h t ht ht1
    obtain ⟨K,hK,he⟩ := all_endpoint_large_cofactor_error hb hb1.le (sub_pos.mpr ht)
    let B := 6*(Real.log 3+4)
    have hB : 0 ≤ B := by dsimp only [B]; positivity
    refine ⟨|C|+K+B+|primeMidpointPrice 1|,?_⟩
    intro n hn
    rcases eq_or_lt_of_le hn with rfl | hn'
    · simp only [Nat.cast_one,Real.one_rpow,mul_one]
      linarith only [le_abs_self (primeMidpointPrice 1),abs_nonneg C,hK,hB]
    obtain ⟨m,hm,hmn,hprim,hs⟩ := primorial_midpoint_upper_sampling hn'
    have her := he m hm
    rw [show b+(t-b)=t by ring] at her
    have hmt := hC m hm hprim
    have hmid := (abs_le.mp her).1
    have hnon : 0 ≤ t := by linarith only [hb,ht]
    have hmn' := Real.rpow_le_rpow (Nat.cast_nonneg m) ((Nat.cast_le (α:=ℝ)).mpr hmn) hnon
    have hC' := mul_le_mul (le_abs_self C) hmn' (Real.rpow_nonneg (Nat.cast_nonneg m) t) (abs_nonneg C)
    have hK' := mul_le_mul_of_nonneg_left hmn' hK
    have hsqrt : Real.sqrt n ≤ (n:ℝ)^t := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) (hb.trans ht.le)
    have hB' := mul_le_mul_of_nonneg_left hsqrt hB
    change primeMidpointPrice n ≤ primeMidpointPrice m+B*Real.sqrt n at hs
    linarith only [hC',hK',hB',hmt,hmid,hs,mul_nonneg (abs_nonneg (primeMidpointPrice 1)) (Real.rpow_nonneg (Nat.cast_nonneg n) t)]
  · intro h t ht ht1
    obtain ⟨C,hC⟩ := h t ht ht1
    obtain ⟨K,_,he⟩ := all_endpoint_large_cofactor_error hb hb1.le (sub_pos.mpr ht)
    refine ⟨C+K,?_⟩
    intro m hm _
    have her := he m hm
    rw [show b+(t-b)=t by ring] at her
    linarith only [(abs_le.mp her).2,hC m hm.le]

#print axioms rough_cofactor_midpoint_upper_spectrum

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
