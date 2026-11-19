import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PrimeWindowsBelowTheOutermostZero
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PrimeSamplingDownToSevenTwelfths
import GaloisForLFunctions.RHTower.BeurlingDeletionSystemPrimes
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Exceptional counts at ordinary prime midpoints

If the zeta edge exceeds both the price exponent and the exceptional
count exponent, a smaller interval exponent still supplies enough
primes to meet the good set. Moving the midpoint there contradicts the
integer midpoint spectrum. The exceptional set can be chosen separately
for each price threshold.
-/

noncomputable section
open Filter Finset
open _root_.RHTower.BeurlingDeletion
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- An exceptional count of order x^e cannot exhaust any prime window
with positive logarithmic mass of strictly larger power order. -/
theorem surviving_primes_in_power_windows {α e : ℝ} (he : e < α) (ha : α < 1)
    (E : Set ℕ)
    (hs : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, deletedCount E x ≤ C*x^e)
    (hw : ∀ᶠ x : ℝ in atTop, x^α/2/2 ≤ Chebyshev.theta (x+x^α/2)-Chebyshev.theta x) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ p ∉ E ∧ x < p ∧ (p:ℝ) ≤ x+x^α := by
  classical
  obtain ⟨C,hC,hbound⟩ := hs
  obtain ⟨X,hX⟩ := eventually_atTop.mp hbound
  let d := (α-e)/2
  have hd : 0 < d := by dsimp only [d]; linarith only [he]
  let K := C*(1/d)*(2:ℝ)^(e+d)
  filter_upwards [hw,eventually_ge_atTop (max X 1),
    (tendsto_rpow_atTop hd).eventually_gt_atTop (4*K)] with x hwin hx hlarge
  have hx1 := (le_max_right X 1).trans hx
  have hx0 := zero_lt_one.trans_le hx1
  have hpow := (Real.rpow_le_rpow_of_exponent_le hx1 ha.le).trans_eq (Real.rpow_one _)
  have hr := Real.rpow_pos_of_pos hx0 α
  have h2 : x+x^α/2 ≤ 2*x := by linarith
  let P := (Ioc ⌊x⌋₊ ⌊x+x^α/2⌋₊).filter Nat.Prime
  rw [_root_.RHTower.Sieve.theta_sub_eq_sum_Ioc (by linarith only [hr])] at hwin
  change x^α/2/2 ≤ ∑ p ∈ P, Real.log p at hwin
  by_contra hnone
  have excl {p : ℕ} (hp : p ∈ P) :
      p ∈ (Nat.primesLE ⌊2*x⌋₊).filter (· ∈ E) ∧ (p:ℝ) ≤ 2*x := by
    obtain ⟨hi,hpr⟩ := mem_filter.mp hp
    obtain ⟨hlo,hhi⟩ := mem_Ioc.mp hi
    have hpx := (Nat.cast_le.mpr hhi).trans (Nat.floor_le (by positivity))
    have hpe : p ∈ E := by
      by_contra hnot
      exact hnone ⟨p,hpr,hnot,(Nat.floor_lt hx0.le).mp hlo,by linarith only [hpx,hr]⟩
    exact ⟨mem_filter.mpr ⟨Nat.mem_primesLE.mpr ⟨hhi.trans (Nat.floor_le_floor h2),hpr⟩,hpe⟩,hpx.trans h2⟩
  have hcard : (P.card:ℝ) ≤ deletedCount E (2*x) := by
    unfold deletedCount
    exact Nat.cast_le.mpr (card_le_card (fun p hp => (excl hp).1))
  have hcount := hX (2*x) (by linarith only [(le_max_left X 1).trans hx,hx0])
  have hl := _root_.RHTower.Mertens.log_le_rpow (x:=2*x) (by positivity) hd
  have ht : 0 ≤ Real.log (2*x) := Real.log_nonneg (by linarith only [hx1])
  have hbound : (∑ p ∈ P, Real.log p) ≤ K*x^(e+d) := by
    calc ∑ p ∈ P, Real.log p ≤ ∑ _p ∈ P, Real.log (2*x) :=
           sum_le_sum fun p hp => Real.log_le_log (Nat.cast_pos.mpr (mem_filter.mp hp).2.pos) (excl hp).2
         _ = (P.card:ℝ)*Real.log (2*x) := by rw [sum_const,nsmul_eq_mul]
         _ ≤ (C*(2*x)^e)*((1/d)*(2*x)^d) :=
           mul_le_mul (hcard.trans hcount) hl ht (by positivity)
         _ = K*x^(e+d) := by
           dsimp only [K]
           rw [mul_mul_mul_comm C _ (1/d),←Real.rpow_add (by positivity : 0<2*x),
             Real.mul_rpow (by norm_num : (0:ℝ)≤2) hx0.le]
           ring
  have hscale : x^(e+d)*x^d=x^α := by
    rw [←Real.rpow_add hx0,show e+d+d=α by dsimp only [d]; ring]
  have hgt := mul_lt_mul_of_pos_left hlarge (Real.rpow_pos_of_pos hx0 (e+d))
  rw [hscale] at hgt
  linarith only [hgt,hwin,hbound]

/-- Uniform control on the retained prime centers gives a strip bounded
by the larger of the price and deletion exponents, down to one half. -/
theorem midpoint_strip_after_sparse_deletion {e s : ℝ} (hs : 0 ≤ s)
    (E : Set ℕ) (he : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, deletedCount E x ≤ C*x^e)
    (hp : ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ∉ E → primeMidpointPrice p ≤ C*(p:ℝ)^s) :
    _root_.RHTower.zetaZeroAbscissa ≤ max (1/2) (max e s) := by
  by_contra! h
  set z := _root_.RHTower.zetaZeroAbscissa
  have hz : 1/2 < z := (le_max_left _ _).trans_lt h
  obtain ⟨g,hg,hgz,hwin⟩ := prime_windows_strictly_below_abscissa hz
  let b := max g (max e s)
  have hbz : b < z := max_lt hgz ((le_max_right _ _).trans_lt h)
  obtain ⟨C,hC⟩ := hp
  refine hbz.not_ge ((prime_midpoint_upper_spectrum_iff (b:=b) (hg.trans (le_max_left _ _))).mp ?_)
  intro t ht ht1
  obtain ⟨α,hα,hαt⟩ := exists_between ht
  have hsα : s < α := ((le_max_right e s).trans (le_max_right _ _)).trans_lt hα
  have hnear := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually
    (surviving_primes_in_power_windows (((le_max_left e s).trans (le_max_right _ _)).trans_lt hα)
      (hαt.trans ht1) E he (hwin α ((le_max_left _ _).trans_lt hα) (hαt.trans ht1)))
  obtain ⟨B,hB,hshift⟩ := midpoint_shift_on_power_window hαt ht1
  obtain ⟨N,hN⟩ := eventually_atTop.mp hnear
  let A := ∑ j ∈ range N, |primeMidpointPrice j|
  have hA : 0 ≤ A := sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨A+2*|C|+B,fun n hn => ?_⟩
  have hn1 := (Nat.one_le_cast (α:=ℝ)).mpr hn
  have ht0 := hs.trans (hsα.trans hαt).le
  have hnt := Real.one_le_rpow hn1 ht0
  by_cases hsmall : n < N
  · have hi : |primeMidpointPrice n| ≤ A := single_le_sum
      (fun j (_ : j ∈ range N) => abs_nonneg (primeMidpointPrice j)) (mem_range.mpr hsmall)
    exact ((le_abs_self _).trans hi).trans ((by linarith only [abs_nonneg C,hB] :
      A ≤ A+2*|C|+B).trans (le_mul_of_one_le_right (by positivity) hnt))
  · obtain ⟨p,hpr,hpE,hnp,hpx⟩ := hN n (le_of_not_gt hsmall)
    have hnpl : n < p := by exact_mod_cast hnp
    obtain ⟨h2p,herr⟩ := hshift hn hnpl hpx
    have hp1 := (Nat.one_le_cast (α:=ℝ)).mpr hpr.one_le
    have hp' := (Real.rpow_le_rpow_of_exponent_le hp1 (hsα.trans hαt).le).trans
      (Real.rpow_le_rpow (Nat.cast_nonneg p) h2p ht0)
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Nat.cast_nonneg n)] at hp'
    have h2t := (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ht1.le).trans_eq
      (Real.rpow_one _)
    have hCp := (hC p hpr hpE).trans (mul_le_mul (le_abs_self C)
      (hp'.trans (mul_le_mul_of_nonneg_right h2t (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
      (Real.rpow_nonneg (Nat.cast_nonneg p) _) (abs_nonneg C))
    linarith only [(abs_le.mp herr).2,hCp,mul_nonneg hA (Real.rpow_nonneg (Nat.cast_nonneg n) t)]

/-- Ordinary prime centers alone detect the entire one-sided midpoint
spectrum, including its critical-line endpoint. -/
theorem ordinary_prime_center_spectrum {b : ℝ} (hb : 1/2 ≤ b) :
    (∀ t : ℝ, b<t → t<1 → ∃ C : ℝ, ∀ p : ℕ, p.Prime → primeMidpointPrice p ≤ C*(p:ℝ)^t) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ b := by
  constructor
  · intro hp
    by_contra! hz
    obtain ⟨s,hbs,hsz⟩ := exists_between hz
    obtain ⟨C,hC⟩ := hp s hbs (hsz.trans_le _root_.RHTower.zetaZeroAbscissa_le_one)
    have hdel : ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ x : ℝ in atTop, deletedCount ∅ x ≤ D*x^b :=
      ⟨0,le_rfl,Eventually.of_forall (fun x => by simp [deletedCount])⟩
    have hstrip := midpoint_strip_after_sparse_deletion (s:=s) (by linarith only [hb,hbs])
      ∅ hdel ⟨C,fun p hpr _ => hC p hpr⟩
    rw [max_eq_right hbs.le,max_eq_right (hb.trans hbs.le)] at hstrip
    exact hsz.not_ge hstrip
  · intro hz t ht ht1
    obtain ⟨C,hC⟩ := (prime_midpoint_upper_spectrum_iff hb).mpr hz t ht ht1
    exact ⟨C,fun p hp => hC p hp.one_le⟩

/-- Below the zero edge, arbitrarily large cutoffs contain more than
K x^e prime centers exceeding C p^s, independently for all e,s below it. -/
theorem frequently_many_large_prime_midpoints {s e : ℝ} (hs : 0 ≤ s)
    (hz : max (1/2) (max e s) < _root_.RHTower.zetaZeroAbscissa) (C K : ℝ) (hK : 0 ≤ K) :
    ∃ᶠ x : ℝ in atTop, K*x^e < deletedCount {p | C*(p:ℝ)^s < primeMidpointPrice p} x := by
  intro h
  apply hz.not_ge
  exact midpoint_strip_after_sparse_deletion hs _ ⟨K,hK,h.mono fun x hx => le_of_not_gt hx⟩
    ⟨C,fun p _ hnot => le_of_not_gt hnot⟩

/-- A growth bound for the exceptional count at each threshold is
equivalent to the full strip, even with a different price constant at
each threshold. -/
theorem exceptional_count_midpoint_spectrum {b : ℝ} (hb : 1/2 ≤ b) :
    (∀ t : ℝ, b<t → t<1 → ∃ C K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
      deletedCount {p | C*(p:ℝ)^t < primeMidpointPrice p} x ≤ K*x^t) ↔
      _root_.RHTower.zetaZeroAbscissa ≤ b := by
  classical
  constructor
  · intro hc
    by_contra! hz
    obtain ⟨s,hbs,hsz⟩ := exists_between hz
    obtain ⟨C,K,hK,hbad⟩ := hc s hbs (hsz.trans_le _root_.RHTower.zetaZeroAbscissa_le_one)
    have hh := frequently_many_large_prime_midpoints (s:=s) (e:=s)
      (by linarith only [hb,hbs]) (by simpa only [max_self,max_eq_right (hb.trans hbs.le)] using hsz) C K hK
    exact hh (hbad.mono fun _ hu => not_lt.mpr hu)
  · intro hz t ht ht1
    obtain ⟨C,hC⟩ := (ordinary_prime_center_spectrum hb).mpr hz t ht ht1
    refine ⟨C,0,le_rfl,Eventually.of_forall fun x => ?_⟩
    simp [deletedCount]
    exact fun _ hp => hC _ (Nat.prime_of_mem_primesLE hp)

/-- RH is equivalent to controlling the counts of exceptional ordinary
prime centers at every exponent strictly above one half. -/
theorem exceptional_prime_midpoints_iff_rh :
    (∀ t : ℝ, 1/2<t → t<1 → ∃ C K : ℝ, 0 ≤ K ∧ ∀ᶠ x : ℝ in atTop,
      deletedCount {p | C*(p:ℝ)^t < primeMidpointPrice p} x ≤ K*x^t) ↔ RiemannHypothesis := by
  rw [exceptional_count_midpoint_spectrum le_rfl,
    ←_root_.RHTower.zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
  exact ⟨fun h => le_antisymm h _root_.RHTower.half_le_zetaZeroAbscissa,fun h => h.le⟩

#print axioms exceptional_count_midpoint_spectrum
#print axioms exceptional_prime_midpoints_iff_rh
#print axioms surviving_primes_in_power_windows
#print axioms midpoint_strip_after_sparse_deletion
#print axioms ordinary_prime_center_spectrum
#print axioms frequently_many_large_prime_midpoints

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
