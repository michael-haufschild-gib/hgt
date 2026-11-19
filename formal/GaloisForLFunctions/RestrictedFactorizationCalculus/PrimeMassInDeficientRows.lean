import GaloisForLFunctions.RestrictedFactorizationCalculus.TransportAcrossOrderedFibres
import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeSupplyAtTheCubeRootBoundary

/-!
# A prime-sized family of deficient products in each quotient

At scale t¹² choose the smaller prime in (2t⁴,t⁵]. The reciprocal mass of
this exponent interval is bounded below. Each such prime contributes a full
dyadic prime window of complementary factors. The cofactor obstruction holds
throughout, and the smaller prime is recovered from the product.
-/

noncomputable section

open Finset Filter RHTower RHTower.PrimeCells
open scoped Classical

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Prime products in a sharp octave with a prescribed smaller-factor window. -/
def pairBand (a b T : ℝ) : Finset ℕ :=
  (windowPrimes a b).biUnion fun q => (windowPrimes (T/q) (2*T/q)).image (q*·)

/-- Distinct smaller primes give disjoint product sets whenever their
complementary prime interval lies above them. -/
theorem card_pairBand {a b T : ℝ} (ha : 0≤a) (hb : 0≤b) (hT : 0≤T)
    (hsep : ∀ q ∈ windowPrimes a b, (q:ℝ) ≤ T/q) :
    (pairBand a b T).card = ∑ q ∈ windowPrimes a b, (windowPrimes (T/q) (2*T/q)).card := by
  unfold pairBand
  rw [card_biUnion]
  · apply sum_congr rfl
    intro q hq
    exact card_image_of_injOn (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left
      ((mem_windowPrimes ha hb).1 hq).1.pos h)
  · intro q hq p hp hne
    apply disjoint_left.mpr
    intro n hn hn'
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hn
    obtain ⟨v,hv,he⟩ := mem_image.mp hn'
    have recover {q r : ℕ} (hq : q ∈ windowPrimes a b)
        (hr : r ∈ windowPrimes (T/q) (2*T/q)) : stem (q*r) = q := by
      have hqp := ((mem_windowPrimes ha hb).1 hq).1
      obtain ⟨hrp,hlo,_⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hr
      have hqr : q<r := by exact_mod_cast (hsep q hq).trans_lt hlo
      exact stem_mul_of_largest hqp.ne_zero hrp (fun _ hd =>
        (Nat.le_of_dvd hqp.pos (Nat.dvd_of_mem_primeFactors hd)).trans_lt hqr)
    exact hne ((recover hq hr).symm.trans ((congrArg stem he.symm).trans (recover hp hv)))

/-- Ordered deficient semiprimes in a growing exponent interval. -/
def deficientProducts (t : ℝ) : Finset ℕ :=
  pairBand (2*t^4) (t^5) (t^12)

private theorem reciprocal_band {t : ℝ} (ht : 2 ≤ t)
    (hlog : 2*(Real.log 2 + Real.log 2 + Sieve.mertensBlockGapConst) ≤ Real.log t) :
    1/10 ≤ ∑ q ∈ windowPrimes (2*t^4) (t^5), 1/(q:ℝ) := by
  let A := ⌊2*t^4⌋₊
  let B := ⌊t^5⌋₊
  let Q := windowPrimes (2*t^4) (t^5)
  have ht0 : 0<t := by linarith only [ht]
  have ht1 : 1≤t := by linarith only [ht]
  have hlog0 := Real.log_pos (by linarith only [ht] : 1<t)
  have ht5 : 2 ≤ t^5 := ht.trans (by simpa only [pow_one] using pow_le_pow_right₀ ht1 (by decide : 1≤5))
  have hA1 : 1 ≤ A := (Nat.one_le_floor_iff _).2 (by
    have := one_le_pow₀ ht1 (n := 4)
    linarith only [this])
  have hAB : A ≤ B := Nat.floor_le_floor (by
    rw [pow_succ t 4]; simpa only [mul_comm (t^4)] using mul_le_mul_of_nonneg_right ht (pow_nonneg ht0.le 4))
  have hsub : Nat.primesLE A ⊆ Nat.primesLE B := fun p hp =>
    Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hAB,(Nat.mem_primesLE.mp hp).2⟩
  have hQ : Q = Nat.primesLE B \ Nat.primesLE A := windowPrimes_eq_primesLE_sdiff _ _
  have hu := Real.log_le_log (show (0:ℝ)<A by exact_mod_cast hA1) (Nat.floor_le (by positivity : 0≤2*t^4))
  have hl := Real.log_le_log (show 0<t^5/2 by positivity)
    (show t^5/2 ≤ (B:ℝ) by dsimp [B]; linarith only [Nat.lt_floor_add_one (t^5),ht5])
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hu
  rw [Real.log_div (by positivity) (by norm_num),Real.log_pow] at hl
  norm_num1 at hu hl
  have hm : Real.log t/2 ≤ ∑ q ∈ Q, Real.log q / q := by
    rw [hQ,sum_sdiff_eq_sub hsub]
    unfold Sieve.mertensBlockGapConst at hlog
    linarith only [Sieve.mertensFirst_lower (hA1.trans hAB),Sieve.mertensFirst_upper hA1,hlog,hu,hl]
  have hle : ∑ q ∈ Q, Real.log q / q ≤ (5*Real.log t) * ∑ q ∈ Q, 1/(q:ℝ) := by
    rw [mul_sum]
    refine sum_le_sum fun q hq => ?_
    obtain ⟨hp,_,hqhi⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hq
    have hq0 : (0:ℝ)<q := by exact_mod_cast hp.pos
    have h := Real.log_le_log hq0 hqhi
    rw [Real.log_pow] at h
    norm_num1 at h
    simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hq0.le)
  change 1/10 ≤ ∑ q ∈ Q, 1/(q:ℝ)
  apply le_of_mul_le_mul_left _ (show 0<5*Real.log t by positivity)
  linarith only [hm.trans hle]

/-- Uniform reciprocal mass on the deficient exponent band. -/
theorem eventually_deficient_band_reciprocal :
    ∀ᶠ t : ℝ in atTop, 1/10 ≤ ∑ p ∈ windowPrimes (2*t^4) (t^5), 1/(p:ℝ) := by
  filter_upwards [eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop
    (2*(Real.log 2 + Real.log 2 + Sieve.mertensBlockGapConst))] with t ht hl
  exact reciprocal_band ht hl

private theorem complementary_scale {t : ℝ} (ht : 2 ≤ t) {q : ℕ}
    (hq : q ∈ windowPrimes (2*t^4) (t^5)) :
    q.Prime ∧ t ≤ t^12/q ∧ (q:ℝ) < t^12/q := by
  have ht0 : 0<t := by linarith only [ht]
  have ht1 : 1≤t := by linarith only [ht]
  obtain ⟨hp,_,hu⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hq
  have hq0 : (0:ℝ)<q := by exact_mod_cast hp.pos
  have h7 : t^7 ≤ t^12/q := by
    rw [le_div_iff₀ hq0]
    calc _ ≤ t^7*t^5 := mul_le_mul_of_nonneg_left hu (by positivity)
         _ = _ := by ring
  have ht7 : t ≤ t^7 := by simpa only [pow_one] using pow_le_pow_right₀ ht1 (by decide : 1≤7)
  refine ⟨hp,ht7.trans h7,?_⟩
  exact hu.trans_lt ((pow_lt_pow_right₀ (by linarith only [ht]) (by decide : 5<7)).trans_le h7)

/-- Every represented product is ordered, has its smaller factor above twice
the cube root, and respects both sharp endpoints. -/
theorem deficientProducts_factors {t : ℝ} (ht : 2≤t) {w : ℕ} (hw : w ∈ deficientProducts t) :
    ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ q<r ∧ 2*t^4<q ∧ (q:ℝ)≤t^5 ∧
      w=q*r ∧ t^12<w ∧ (w:ℝ)≤2*t^12 := by
  obtain ⟨q,hq,hh⟩ := mem_biUnion.mp hw
  obtain ⟨r,hr,rfl⟩ := mem_image.mp hh
  obtain ⟨hp,hlo,hhi⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hq
  have ht0 : 0<t := by linarith only [ht]
  have hq0 : (0:ℝ)<q := by exact_mod_cast hp.pos
  obtain ⟨hrp,hrlo,hrhi⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hr
  refine ⟨q,r,hp,hrp,by exact_mod_cast ((complementary_scale ht hq).2.2.trans hrlo),
    hlo,hhi,rfl,?_,?_⟩
  · push_cast; rw [mul_comm]; exact (div_lt_iff₀ hq0).1 hrlo
  · push_cast; rw [mul_comm]; exact (le_div_iff₀ hq0).1 hrhi

/-- On every sufficiently large quotient octave, deficient products occupy
at least a constant times the usual prime-counting scale. -/
theorem eventually_deficientProducts_lower :
    ∀ᶠ t : ℝ in atTop, t^12 / (260*Real.log t) ≤ ((deficientProducts t).card:ℝ) := by
  obtain ⟨T,hcount⟩ := eventually_atTop.mp eventually_dyadic_prime_lower
  filter_upwards [eventually_ge_atTop (max 2 T),Real.tendsto_log_atTop.eventually_ge_atTop
    (2*(Real.log 2 + Real.log 2 + Sieve.mertensBlockGapConst))] with t ht hlog
  let Q := windowPrimes (2*t^4) (t^5)
  let R := fun q : ℕ => windowPrimes (t^12/q) (2*t^12/q)
  have ht2 : 2≤t := (le_max_left _ _).trans ht
  have ht0 : 0<t := by linarith only [ht2]
  have hlg := Real.log_pos (by linarith only [ht2] : 1<t)
  have hcard : (deficientProducts t).card = ∑ q ∈ Q, (R q).card := by
    exact card_pairBand (by positivity) (by positivity) (by positivity)
      (fun q hq => (complementary_scale ht2 hq).2.2.le)
  have hrow (q : ℕ) (hq : q ∈ Q) :
      t^12/(26*Real.log t) * (1/(q:ℝ)) ≤ ((R q).card:ℝ) := by
    obtain ⟨hp,htq,_⟩ := complementary_scale ht2 hq
    have hq0 : (0:ℝ)<q := by exact_mod_cast hp.pos
    let v := t^12/(q:ℝ)
    have hv : t≤v := htq
    have hv0 : 0<v := ht0.trans_le hv
    have h := hcount v (((le_max_right _ _).trans ht).trans hv)
    have hR : R q = windowPrimes v (2*v) := by dsimp [R,v]; rw [mul_div_assoc]
    rw [hR]
    refine le_trans ?_ h
    have hlogv : 0<Real.log (2*v) := Real.log_pos (by linarith only [hv,ht2])
    have hq1 : (1:ℝ)≤q := by exact_mod_cast hp.pos
    have hlogv' := Real.log_le_log (show 0<2*v by positivity)
      (mul_le_mul_of_nonneg_left (div_le_self (by positivity : 0≤t^12) hq1) (by norm_num : (0:ℝ)≤2))
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (pow_ne_zero 12 ht0.ne'),Real.log_pow] at hlogv'
    norm_num1 at hlogv'
    have hbound : Real.log (2*v) ≤ 13*Real.log t := by
      linarith only [hlogv',Real.log_le_log (by norm_num : (0:ℝ)<2) ht2]
    calc t^12/(26*Real.log t)*(1/(q:ℝ)) = v/(26*Real.log t) := by dsimp [v]; ring
         _ ≤ v/(2*Real.log (2*v)) := div_le_div_of_nonneg_left hv0.le (by positivity)
           (by linarith only [hbound])
         _ = (1/2)*v/Real.log (2*v) := by ring
         _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hv0]) hlogv.le
  rw [hcard,Nat.cast_sum]
  calc _ = t^12/(26*Real.log t)*(1/10) := by ring
       _ ≤ t^12/(26*Real.log t)*∑ q ∈ Q,1/(q:ℝ) :=
         mul_le_mul_of_nonneg_left (reciprocal_band ht2 hlog) (by positivity)
       _ ≤ _ := by rw [mul_sum]; exact sum_le_sum hrow

/-- The whole family fits into the prime row without collisions. -/
theorem eventually_deficientProducts_fit :
    ∀ᶠ u : ℝ in atTop, (deficientProducts u).card ≤ (windowPrimes (u^12) (2*u^12)).card := by
  obtain ⟨H,hH⟩ := eventually_atTop.mp (eventually_cubeProducts_capacity 0)
  filter_upwards [eventually_ge_atTop (max 2 H)] with u hu
  have hu2 := (le_max_left _ _).trans hu
  have hu0 : 0<u := by linarith only [hu2]
  have hu1 : 1≤u := by linarith only [hu2]
  have h2 : u≤u^2 := by simpa only [pow_one] using pow_le_pow_right₀ hu1 (by decide : 1≤2)
  have hsub : deficientProducts u ⊆ cubeProducts (u^2) (u^12) (2*u^12) := by
    intro w hw
    obtain ⟨q,hq,hr⟩ := mem_biUnion.mp hw
    obtain ⟨hp,hlo,hhi⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hq
    refine mem_biUnion.mpr ⟨q,(mem_windowPrimes (by positivity) (by positivity)).2 ⟨hp,?_,?_⟩,hr⟩
    · nlinarith only [hlo,pow_nonneg hu0.le 4]
    · have h5 := pow_le_pow_right₀ hu1 (by decide : 5≤6)
      nlinarith only [hhi,h5,pow_nonneg hu0.le 6]
  have h6 : (u^2)^6=u^12 := by ring
  apply (card_le_card hsub).trans
  exact hH (u^2) (((le_max_right _ _).trans hu).trans h2) (u^12) (2*u^12) h6.le
    (by linarith only [pow_nonneg hu0.le 12]) (by rw [h6])
    (by rw [pow_zero,div_one,h6]; linarith)

end GaloisForLFunctions.RestrictedFactorizationCalculus
