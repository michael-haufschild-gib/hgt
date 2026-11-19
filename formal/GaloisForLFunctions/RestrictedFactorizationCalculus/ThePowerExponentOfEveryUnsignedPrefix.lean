import GaloisForLFunctions.RestrictedFactorizationCalculus.TheTwoCutoffsAroundASmoothVertex
import GaloisForLFunctions.RestrictedFactorizationCalculus.DetectingPowerBoundsByOneExchange
import GaloisForLFunctions.RestrictedFactorizationCalculus.OneInvolutionForEverySharpPrefix

/-!
# Every unsigned prefix has exact power exponent one

Prime products with many factors force long moves. A count of fixed and
crossing vertices that saved any fixed power at every cutoff would leave
too few places to charge these products. The linear endpoint, and for one
involution a little-o improvement at that endpoint, are attained.
-/

noncomputable section

open Finset Filter RHTower RHTower.PrimeCells
open scoped Classical Topology
open GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem octave_prime_power_lower {s : ℝ} (hs : s<1) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ t : ℕ in atTop, c*(t:ℝ)^s ≤ ((windowPrimes (2*t) (4*t)).card:ℝ) := by
  obtain ⟨H,_,hH⟩ := exists_card_windowPrimes_div_ge 0 (ε := 1/2) (by norm_num)
  let a := 1-s
  have ha : 0<a := sub_pos.mpr hs
  let c := a/(4:ℝ)^a
  have hc : 0<c := div_pos ha (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop (max 2 ⌈H⌉₊)] with t ht
  have ht2 := (le_max_left _ _).trans ht
  have htR : (2:ℝ) ≤ t := by exact_mod_cast ht2
  have ht0 : (0:ℝ)<t := by linarith only [htR]
  let R := 4*(t:ℝ)
  have hR1 : 1<R := by dsimp only [R]; linarith only [htR]
  have hR : H ≤ R := by
    have hh := (Nat.le_ceil H).trans (Nat.cast_le.mpr ((le_max_right _ _).trans ht))
    dsimp only [R]; linarith only [hh,ht0]
  have hle : R ≤ 2*R := by linarith only [hR1]
  have hlen : R/Real.log R^(0:ℝ) ≤ 2*R-R := by rw [Real.rpow_zero,div_one]; linarith
  have hprime := hH R hR 2 (by norm_num) (by norm_num) R (2*R) le_rfl hle le_rfl hlen
  have h₁ : R/2=2*t := by dsimp [R]; ring
  have h₂ : 2*R/2=4*t := by dsimp [R]; ring
  rw [h₁,h₂] at hprime
  have hlogR := Real.log_pos hR1
  have hlog := Real.log_le_rpow_div (zero_lt_one.trans hR1).le ha
  have hpow : (t:ℝ)^s*(t:ℝ)^a=t := by rw [←Real.rpow_add ht0,show s+a=1 by dsimp [a]; ring,Real.rpow_one]
  have scale : c*(t:ℝ)^s*(R^a/a)=t := by
    apply Eq.trans _ hpow
    dsimp only [R,c]
    rw [Real.mul_rpow (by norm_num : 0 ≤ (4:ℝ)) ht0.le]
    field_simp [ha.ne',(Real.rpow_pos_of_pos (by norm_num : 0<(4:ℝ)) a).ne']
  calc c*(t:ℝ)^s ≤ (t:ℝ)/Real.log R := (le_div_iff₀ hlogR).2
         ((mul_le_mul_of_nonneg_left hlog (mul_nonneg hc.le (Real.rpow_nonneg ht0.le _))).trans_eq scale)
       _ = (1-1/2)*(2*R-R)/(2*Real.log R) := by dsimp only [R]; ring
       _ ≤ _ := hprime

/-- A genuine restricted involution admits no unsigned prefix estimate of
any positive power strictly smaller than one. This holds even without a
displacement restriction on its edges. -/
theorem unsigned_prefix_power_iff (F : ℕ → ℕ)
    (hF : ∀ n, Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)))
    {θ : ℝ} (hθ : 0<θ) :
    PrefixPower θ (fun x => ((prefixUnpaid F x).card:ℝ)) ↔ 1 ≤ θ := by
  constructor
  · rintro ⟨C,hC,hbound⟩
    by_contra! hlt
    let s := (1+θ)/2
    have hθs : θ<s := by dsimp only [s]; linarith only [hlt]
    have hs1 : s<1 := by dsimp only [s]; linarith only [hlt]
    have hs0 := hθ.trans hθs
    obtain ⟨d,hd⟩ := exists_nat_gt (2/(s-θ))
    let k := d+4
    have hdk : (d:ℝ) ≤ k := by dsimp only [k]; exact_mod_cast Nat.le_add_right d 4
    have hdiff := sub_pos.mpr hθs
    let e := s*(k:ℝ)-(2+(k:ℝ)*θ)
    have he : 0<e := by
      dsimp only [e]
      nlinarith only [(div_lt_iff₀ hdiff).1 hd,mul_le_mul_of_nonneg_right hdk hdiff.le]
    obtain ⟨c,hc,hpr⟩ := octave_prime_power_lower hs1
    let A := (c/2)^k
    let B := (k.factorial:ℝ)*2*(4:ℝ)^k*C*((4:ℝ)^k)^θ
    have hA : 0<A := pow_pos (half_pos hc) _
    have grow {r : ℝ} (hr : 0<r) : Tendsto (fun t : ℕ => (t:ℝ)^r) atTop atTop :=
      (tendsto_rpow_atTop hr).comp tendsto_natCast_atTop_atTop
    obtain ⟨t,ht,hprime,hbig,hover⟩ := ((eventually_ge_atTop (1:ℕ)).and
      (hpr.and (((grow hs0).eventually_ge_atTop (2*(k:ℝ)/c)).and
        ((grow he).eventually_gt_atTop (B/A))))).exists
    let P := (windowPrimes (2*t) (4*t)).card
    have ht0 : (0:ℝ)<t := Nat.cast_pos.mpr ht
    change c*(t:ℝ)^s ≤ P at hprime
    have hkP : (k:ℝ) ≤ P := by
      have hh := (div_le_iff₀ hc).1 hbig
      linarith only [hh,hprime,Nat.cast_nonneg (α := ℝ) k]
    have hkNat := Nat.cast_le.mp hkP
    have hrP : (c/2)*(t:ℝ)^s ≤ ((P+1-k:ℕ):ℝ) := by
      rw [Nat.cast_sub (hkNat.trans (Nat.le_succ _)),
        show ((P+1:ℕ):ℝ)=(P:ℝ)+1 from Nat.cast_succ P]
      have hh := (div_le_iff₀ hc).1 hbig
      linarith only [hh,hprime]
    have hdesc := Nat.pow_sub_le_descFactorial P k
    rw [Nat.descFactorial_eq_factorial_mul_choose] at hdesc
    have hbin : (P.choose k:ℝ)*(k.factorial:ℝ) ≥ ((c/2)*(t:ℝ)^s)^k := by
      apply (pow_le_pow_left₀ (mul_nonneg (half_pos hc).le (Real.rpow_nonneg ht0.le _)) hrP _).trans
      rw [mul_comm]
      exact_mod_cast hdesc
    obtain ⟨x,hx,hcut⟩ := exists_large_unpaid_cutoff F hF d t ht
    have hU : (x:ℝ) ≤ (4*(t:ℝ))^k := by exact_mod_cast hx
    have hcharge := hbound x
    rw [abs_of_nonneg (Nat.cast_nonneg _)] at hcharge
    have hcontrol := hcharge.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hU hθ.le) hC)
    change P.choose k ≤ 2*(4^k*t^2)*(prefixUnpaid F x).card at hcut
    have hcu : (P.choose k:ℝ) ≤ 2*((4:ℝ)^k*(t:ℝ)^2)*(prefixUnpaid F x).card := by
      exact_mod_cast hcut
    have hup := hcu.trans (mul_le_mul_of_nonneg_left hcontrol (by positivity))
    have htotal := hbin.trans (mul_le_mul_of_nonneg_right hup (Nat.cast_nonneg _))
    have split : ((4*(t:ℝ))^k)^θ=((4:ℝ)^k)^θ*(t:ℝ)^((k:ℝ)*θ) := by
      rw [mul_pow,Real.mul_rpow (by positivity) (by positivity),Real.rpow_natCast_mul ht0.le]
    have left : ((c/2)*(t:ℝ)^s)^k=A*(t:ℝ)^(s*(k:ℝ)) := by
      rw [mul_pow,Real.rpow_mul ht0.le,Real.rpow_natCast]
    have right : (t:ℝ)^(2+(k:ℝ)*θ)=(t:ℝ)^2*(t:ℝ)^((k:ℝ)*θ) := by
      rw [Real.rpow_add ht0,Real.rpow_two]
    have cancel : A*(t:ℝ)^e ≤ B := by
      apply le_of_mul_le_mul_right (a := (t:ℝ)^(2+(k:ℝ)*θ)) _ (Real.rpow_pos_of_pos ht0 _)
      rw [mul_assoc,←Real.rpow_add ht0,show e+(2+(k:ℝ)*θ)=s*(k:ℝ) by dsimp [e]; ring,right]
      rw [left,split] at htotal
      dsimp only [B]
      linarith only [htotal]
    exact (not_lt_of_ge cancel) (by simpa only [mul_comm ((t:ℝ)^e) A] using (div_lt_iff₀ hA).1 hover)
  · intro h
    refine ⟨1,zero_le_one,fun x => ?_⟩
    have hcard : (prefixUnpaid F x).card ≤ x := by
      have hsub : prefixUnpaid F x ⊆ Icc 1 x := (filter_subset ..).trans (filter_subset ..)
      simpa only [Nat.card_Icc,Nat.add_sub_cancel] using card_le_card hsub
    rw [abs_of_nonneg (Nat.cast_nonneg _),one_mul]
    by_cases hx : x=0
    · subst x
      simpa only [Nat.cast_zero,Real.zero_rpow hθ.ne'] using (Nat.cast_le (α := ℝ)).mpr hcard
    · have hx1 : (1:ℝ) ≤ x := by exact_mod_cast Nat.pos_of_ne_zero hx
      exact (Nat.cast_le.mpr hcard).trans (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hx1 h)

/-- The sublinear dyadic involution attains the exact boundary between a
vanishing unpaid fraction and every fixed power saving. -/
theorem unsigned_dyadic_power_boundary :
    (∀ ε : ℝ, 0<ε → ∀ᶠ x : ℕ in atTop, ((prefixUnpaid dyadicPrimeSwitch x).card:ℝ) ≤ ε*x) ∧
    (∀ θ : ℝ, 0<θ → (PrefixPower θ (fun x => ((prefixUnpaid dyadicPrimeSwitch x).card:ℝ)) ↔ 1 ≤ θ)) := by
  obtain ⟨hinv,hedge,_,hsmall⟩ := one_involution_with_sublinear_unpaid_prefix
  exact ⟨fun ε hε => (hsmall ε hε).mono (fun _ h => h.1),
    fun _ hθ => unsigned_prefix_power_iff _ (fun n _ => ⟨hinv n,hedge n⟩) hθ⟩

#print axioms unsigned_prefix_power_iff
#print axioms unsigned_dyadic_power_boundary

end GaloisForLFunctions.RestrictedFactorizationCalculus
