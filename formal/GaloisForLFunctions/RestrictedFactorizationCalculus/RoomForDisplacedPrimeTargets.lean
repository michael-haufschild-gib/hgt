import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeMassInDeficientRows

/-!
# Reassigning all displaced ordered edges within their original rows

At quotient scale t¹⁶, put the smaller prime of each replacement product
between t and t⁸. Three successive windows (v,v²] each have reciprocal
prime mass at least 3/8. Counting their complementary primes in the original
octave gives more distinct semiprimes than there are prime targets.
-/

noncomputable section

open Finset Filter RHTower RHTower.PrimeCells

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem reciprocal_doubled_exponent :
    ∀ᶠ v : ℝ in atTop, 3/8 ≤ ∑ p ∈ windowPrimes v (v^2), 1/(p:ℝ) := by
  filter_upwards [eventually_ge_atTop (2:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop
      (4*(Real.log 2+Sieve.mertensBlockGapConst))] with v hv hL
  let A := ⌊v⌋₊
  let B := ⌊v^2⌋₊
  have hv0 : 0 < v := by linarith only [hv]
  have hv1 : 1 ≤ v := by linarith only [hv]
  have hvs : v ≤ v^2 := by simpa only [pow_one] using pow_le_pow_right₀ hv1 (by decide : 1 ≤ 2)
  have hA : 1 ≤ A := (Nat.one_le_floor_iff _).2 hv1
  have hAB : A ≤ B := Nat.floor_le_floor hvs
  have hsub : Nat.primesLE A ⊆ Nat.primesLE B := fun p hp =>
    Nat.mem_primesLE.mpr ⟨(Nat.mem_primesLE.mp hp).1.trans hAB,(Nat.mem_primesLE.mp hp).2⟩
  have hup := Real.log_le_log (by exact_mod_cast hA : (0:ℝ) < A) (Nat.floor_le hv0.le)
  have hlo := Real.log_le_log (by positivity : 0 < v^2/2)
    (show v^2/2 ≤ (B:ℝ) by dsimp [B]; linarith only [hv,hvs,Nat.lt_floor_add_one (v^2)])
  rw [Real.log_div (by positivity) (by norm_num),Real.log_pow] at hlo
  norm_num1 at hlo
  have hm : 3/4*Real.log v ≤ ∑ p ∈ windowPrimes v (v^2), Real.log p/p := by
    rw [windowPrimes_eq_primesLE_sdiff,sum_sdiff_eq_sub hsub]
    unfold Sieve.mertensBlockGapConst at hL
    linarith only [Sieve.mertensFirst_lower (hA.trans hAB), Sieve.mertensFirst_upper hA,hup,hlo,hL]
  have hterm : ∑ p ∈ windowPrimes v (v^2), Real.log p/p ≤
      (2*Real.log v)*∑ p ∈ windowPrimes v (v^2), 1/(p:ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    obtain ⟨hpp,_,hpu⟩ := (mem_windowPrimes hv0.le (sq_nonneg v)).1 hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast hpp.pos
    have hz := Real.log_le_log hp0 hpu
    rw [Real.log_pow] at hz
    norm_num1 at hz
    simpa only [div_eq_mul_inv,one_mul] using mul_le_mul_of_nonneg_right hz (inv_nonneg.mpr hp0.le)
  have hvlog := Real.log_pos (by linarith only [hv] : 1 < v)
  apply le_of_mul_le_mul_left _ (show 0 < 2*Real.log v by positivity)
  linarith only [hm.trans hterm]

private theorem split_prime_sum (f : ℕ → ℝ) {a b d : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbd : b ≤ d) :
    ∑ p ∈ windowPrimes a d, f p = (∑ p ∈ windowPrimes a b, f p) + ∑ p ∈ windowPrimes b d, f p := by
  have hb := ha.trans hab
  have hd := hb.trans hbd
  have he : windowPrimes a d = windowPrimes a b ∪ windowPrimes b d := by
    apply Finset.ext
    intro p
    rw [mem_union,mem_windowPrimes ha hd,mem_windowPrimes ha hb,mem_windowPrimes hb hd]
    constructor
    · rintro ⟨hp,hlo,hhi⟩
      rcases le_or_gt (p:ℝ) b with h | h
      · exact Or.inl ⟨hp,hlo,h⟩
      · exact Or.inr ⟨hp,h,hhi⟩
    · rintro (⟨hp,hlo,hhi⟩ | ⟨hp,hlo,hhi⟩)
      · exact ⟨hp,hlo,hhi.trans hbd⟩
      · exact ⟨hp,hab.trans_lt hlo,hhi⟩
  rw [he,sum_union]
  exact disjoint_left.mpr (fun p hp hq =>
    ((mem_windowPrimes hb hd).1 hq).2.1.not_ge ((mem_windowPrimes ha hb).1 hp).2.2)

/-- Products whose smaller factors are large enough to leave the reserved
positive endpoints unused. -/
def replacementProducts (u : ℝ) := pairBand u (u^8) (u^16)

/-- The smaller factor lies above the reserved range and is strictly below
the complementary factor, even at the square-root endpoint. -/
theorem replacementProducts_factors {u : ℝ} (hu : 0 < u) {w : ℕ} (hw : w ∈ replacementProducts u) :
    ∃ q r : ℕ, q.Prime ∧ r.Prime ∧ u < q ∧ q < r ∧ w=q*r ∧ u^16 < w ∧ (w:ℝ) ≤ 2*u^16 := by
  obtain ⟨q,hq,hh⟩ := mem_biUnion.mp hw
  obtain ⟨r,hr,rfl⟩ := mem_image.mp hh
  obtain ⟨hp,hlo,hhi⟩ := (mem_windowPrimes hu.le (by positivity)).1 hq
  have hq0 : (0:ℝ) < q := by exact_mod_cast hp.pos
  obtain ⟨hrp,hrlo,hrhi⟩ := (mem_windowPrimes (by positivity) (by positivity)).1 hr
  have hsep : (q:ℝ) ≤ u^16/q := by
    rw [le_div_iff₀ hq0]
    calc (q:ℝ)*q ≤ u^8*u^8 := mul_le_mul hhi hhi hq0.le (by positivity)
         _ = _ := by ring
  refine ⟨q,r,hp,hrp,hlo,by exact_mod_cast hsep.trans_lt hrlo,rfl,?_,?_⟩
  · push_cast; rw [mul_comm]; exact (div_lt_iff₀ hq0).1 hrlo
  · push_cast; rw [mul_comm]; exact (le_div_iff₀ hq0).1 hrhi

/-- Every sufficiently large quotient octave has enough replacement semiprimes
to receive all its prime targets with distinct positive endpoints. -/
theorem eventually_replacement_capacity :
    ∀ᶠ u : ℝ in atTop, (windowPrimes (u^16) (2*u^16)).card ≤ (replacementProducts u).card := by
  obtain ⟨H,hH⟩ := eventually_atTop.mp eventually_dyadic_prime_lower
  obtain ⟨J,hJ⟩ := eventually_atTop.mp reciprocal_doubled_exponent
  obtain ⟨K,_,hK⟩ := exists_card_windowPrimes_le 0 (by norm_num : (0:ℝ) < 1/100)
  filter_upwards [eventually_ge_atTop (max 2 (max H (max J K)))] with u hu
  have hu2 := (le_max_left _ _).trans hu
  have hu1 : 1 ≤ u := by linarith only [hu2]
  have hu0 : 0 < u := by linarith only [hu2]
  have huH := (le_max_left _ _).trans ((le_max_right _ _).trans hu)
  have huJ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hu))
  have huK := (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hu))
  have powers {i j : ℕ} (h : i ≤ j) : u^i ≤ u^j := pow_le_pow_right₀ hu1 h
  have h2 : u ≤ u^2 := by simpa only [pow_one] using powers (by decide : 1 ≤ 2)
  have h24 := powers (by decide : 2 ≤ 4)
  have h48 := powers (by decide : 4 ≤ 8)
  have h816 := powers (by decide : 8 ≤ 16)
  have hu8 := (h2.trans h24).trans h48
  have hmass : 9/8 ≤ ∑ q ∈ windowPrimes u (u^8), 1/(q:ℝ) := by
    rw [split_prime_sum _ hu0.le (h2.trans h24) h48,split_prime_sum _ hu0.le h2 h24]
    have h := hJ (u^2) (huJ.trans h2)
    have h' := hJ (u^4) (huJ.trans (h2.trans h24))
    rw [←pow_mul] at h h'
    norm_num1 at h h'
    linarith only [hJ u huJ,h,h']
  let T := u^16
  have hT0 : 0 < T := pow_pos hu0 _
  have hlog := Real.log_pos (show 1 < T by linarith only [hu2,hu8,h816])
  have hrange {q : ℕ} (hq : q ∈ windowPrimes u (u^8)) :
      q.Prime ∧ (q:ℝ) ≤ u^8 ∧ u^8 ≤ T/q := by
    obtain ⟨hp,_,hi⟩ := (mem_windowPrimes hu0.le (by positivity)).1 hq
    have hp0 : (0:ℝ) < q := by exact_mod_cast hp.pos
    refine ⟨hp,hi,(le_div_iff₀ hp0).2 ?_⟩
    calc u^8*(q:ℝ) ≤ u^8*u^8 := mul_le_mul_of_nonneg_left hi (by positivity)
         _ = T := by dsimp [T]; ring
  have hcard : (replacementProducts u).card =
      ∑ q ∈ windowPrimes u (u^8), (windowPrimes (T/q) (2*T/q)).card :=
    card_pairBand hu0.le (by positivity) hT0.le (fun _ hq => (hrange hq).2.1.trans (hrange hq).2.2)
  have hrow (q : ℕ) (hq : q ∈ windowPrimes u (u^8)) :
      ((99/100)*T/Real.log T)*(1/(q:ℝ)) ≤ ((windowPrimes (T/q) (2*T/q)).card:ℝ) := by
    obtain ⟨hp,_,hqT⟩ := hrange hq
    have hq0 : (0:ℝ) < q := by exact_mod_cast hp.pos
    have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hp.two_le
    have hR := hH (T/q) (huH.trans (hu8.trans hqT))
    have hdouble : 2*(T/q) = 2*T/q := (mul_div_assoc _ _ _).symm
    rw [hdouble] at hR
    have hlogR := Real.log_pos (by linarith only [hu2,hu8,hqT] : 1 < 2*(T/q))
    have hL : Real.log (2*T/q) ≤ Real.log T := Real.log_le_log (by positivity)
      ((div_le_iff₀ hq0).2 (by nlinarith only [mul_le_mul_of_nonneg_right hq2 hT0.le]))
    rw [hdouble] at hlogR
    calc _ = ((99/100)*(T/q))/Real.log T := by ring
         _ ≤ _ := (div_le_div_of_nonneg_left (by positivity) hlogR hL).trans hR
  have hlow : ((99/100)*T/Real.log T)*(9/8) ≤ ((replacementProducts u).card:ℝ) := by
    rw [hcard,Nat.cast_sum]
    exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans (by rw [mul_sum]; exact sum_le_sum hrow)
  have hup := hK T (huK.trans (hu8.trans h816)) T (2*T) le_rfl (by linarith only [hT0]) le_rfl
    (by rw [Real.rpow_zero,div_one]; linarith)
  have hmain : (1+1/100)*(2*T-T)/Real.log T ≤ ((99/100)*T/Real.log T)*(9/8) := by
    calc _ ≤ ((99/100)*T*(9/8))/Real.log T :=
            div_le_div_of_nonneg_right (by linarith only [hT0]) hlog.le
         _ = _ := by ring
  exact_mod_cast hup.trans (hmain.trans hlow)

end GaloisForLFunctions.RestrictedFactorizationCalculus
