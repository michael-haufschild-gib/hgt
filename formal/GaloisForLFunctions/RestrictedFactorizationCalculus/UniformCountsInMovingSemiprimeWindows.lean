import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeWindowsInLogarithmicCoordinates
import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeMassInDeficientRows
import GaloisForLFunctions.RHTower.Sieve.PrimeCountRelativeWindow

/-!
# Uniform counts for moving semiprime windows

Count the larger prime in each complementary octave. The total relative
prime-count error is bounded by the mass of a positive logarithmic kernel.
Its primitive then counts all distinct ordered semiprimes, with an error
uniform in the two endpoints of the smaller-prime window.
-/

noncomputable section

open Finset Filter RHTower RHTower.PrimeCells

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- The relative prime-count error in a real octave tends uniformly to zero. -/
theorem eventually_dyadic_prime_relative {η : ℝ} (hη : 0 < η) :
    ∀ᶠ v : ℝ in atTop, |((windowPrimes v (2*v)).card:ℝ)-v/Real.log v| ≤ η*(v/Real.log v) := by
  obtain ⟨c,hc,h⟩ := Sieve.exists_card_primesIn_window
  filter_upwards [h η hη] with v hv
  have hp := hv 1 (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hc.le) (Real.sqrt_nonneg _))) le_rfl
  rw [one_mul,show (1:ℝ)+1=2 by norm_num,mul_comm v 2] at hp
  change (1-η)*(v/Real.log v) ≤ ((windowPrimes v (2*v)).card:ℝ) ∧
    ((windowPrimes v (2*v)).card:ℝ) ≤ (1+η)*(v/Real.log v) at hp
  rw [abs_le]
  constructor <;> linarith only [hp.1,hp.2]

/-- Uniform error in replacing a sum of larger-prime counts by its positive
logarithmic main terms. An upper bound on the smaller prime forces every
quotient scale beyond the same prime-number-theorem threshold. -/
private theorem normalized_pair_error {T η : ℝ} (hT : 1 < T) {a b : ℕ}
    (hbT : (b:ℝ)^2 ≤ T)
    (hcount : ∀ q ∈ windowPrimes a b, let v := T/q
      |((windowPrimes v (2*v)).card:ℝ)-v/Real.log v| ≤ η*(v/Real.log v)) :
    let h := Real.log T
    let Q := windowPrimes a b
    let W := ∑ q ∈ Q, h/(q*(h-Real.log q))
    |((pairBand a b T).card:ℝ)*h/T-W| ≤ η*W := by
  let h := Real.log T
  let Q := windowPrimes a b
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hl : 0 < h := Real.log_pos hT
  have sep {q : ℕ} (hq : q ∈ Q) : (q:ℝ) ≤ T/q := by
    obtain ⟨hp,_,hb⟩ := (mem_windowPrimes (Nat.cast_nonneg _) (Nat.cast_nonneg _)).1 hq
    rw [le_div_iff₀ (by exact_mod_cast hp.pos : (0:ℝ) < q)]
    exact (mul_le_mul hb hb (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans
      ((sq (b:ℝ)).symm.le.trans hbT)
  have term (q : ℕ) (hq : q ∈ Q) :
      |((windowPrimes (T/q) (2*T/q)).card:ℝ)*(h/T) - h/(q*(h-Real.log q))| ≤
        η*(h/(q*(h-Real.log q))) := by
    have hp := ((mem_windowPrimes (Nat.cast_nonneg _) (Nat.cast_nonneg _)).1 hq).1
    have hq0 : (0:ℝ) < q := by exact_mod_cast hp.pos
    have hq1 : (1:ℝ) < q := by exact_mod_cast hp.one_lt
    have hqL := Real.log_pos (hq1.trans_le (sep hq))
    have hlog : Real.log (T/q) = h-Real.log q := Real.log_div hT0.ne' hq0.ne'
    have hid : ((T/q)/Real.log (T/q))*(h/T) = h/(q*(h-Real.log q)) := by
      rw [hlog]; field_simp [hT0.ne',hq0.ne',hlog ▸ hqL.ne'] <;> ring
    have hc := mul_le_mul_of_nonneg_right (hcount q hq) (div_nonneg hl.le hT0.le)
    -- Put the positive normalization inside the absolute value on the left.
    have hs : 2*(T/(q:ℝ)) = 2*T/q := (mul_div_assoc ..).symm
    calc _ = |((windowPrimes (T/q) (2*T/q)).card:ℝ)-(T/q)/Real.log (T/q)|*(h/T) := by
               rw [←hid,←sub_mul,abs_mul,abs_of_pos (div_pos hl hT0)]
         _ ≤ (η*((T/q)/Real.log (T/q)))*(h/T) := by simpa only [hs] using hc
         _ = _ := by rw [mul_assoc,hid]
  dsimp only
  rw [card_pairBand (Nat.cast_nonneg _) (Nat.cast_nonneg _) hT0.le (fun _ hq => sep hq),Nat.cast_sum]
  change |(∑ q ∈ Q, ((windowPrimes (T/q) (2*T/q)).card:ℝ))*h/T -
    ∑ q ∈ Q, h/(q*(h-Real.log q))| ≤ η*∑ q ∈ Q, h/(q*(h-Real.log q))
  rw [mul_div_assoc,sum_mul,←sum_sub_distrib,mul_sum]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum term)

/-- The normalized number of distinct semiprimes converges to the difference
of the log-odds at the two smaller-factor exponents. Both endpoints may range
over the entire compact band, including the square-root boundary. -/
theorem eventually_uniform_semiprime_counts {d ε : ℝ} (hd : 0 < d) (hd' : d ≤ 1/2) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ a b : ℕ, 1 ≤ a → a ≤ b → d ≤ Real.log a/Real.log T → (b:ℝ)^2 ≤ T →
      |((pairBand a b T).card:ℝ)*Real.log T/T -
        (pairPrimitive (Real.log b/Real.log T)-pairPrimitive (Real.log a/Real.log T))| ≤ ε := by
  let e := d/2
  let B := 1/e^2
  let C := 2*B+3*(1/e^4)
  let η := (ε/2)/(B+1)
  let tol := min e (min 1 (min 1 (ε/2)/C))
  have he : 0 < e := half_pos hd
  have hB : 0 < B := one_div_pos.mpr (pow_pos he _)
  have hC : 0 < C := by dsimp [C]; positivity
  have hη : 0 < η := div_pos (half_pos hε) (by positivity)
  have ht : 0 < tol := lt_min he (lt_min zero_lt_one (div_pos (lt_min zero_lt_one (half_pos hε)) hC))
  obtain ⟨H,hH⟩ := eventually_atTop.mp (eventually_dyadic_prime_relative hη)
  let J := max 2 H
  have hJ : (2:ℝ) ≤ J := le_max_left _ _
  have hJ0 : 0 < J := by linarith only [hJ]
  filter_upwards [eventually_ge_atTop (J^2),Real.tendsto_log_atTop.eventually_ge_atTop
    ((Sieve.mertensBlockGapConst+Real.log 2)/tol)] with T hT hlarge
  intro a b ha hab hxa hbT
  let h := Real.log T
  let x := fun n : ℕ => Real.log n/h
  let δ := coordinateRadius h
  have hT1 : 1 < T := by nlinarith only [hT,hJ,sq_nonneg (J-2)]
  have hh : 0 < h := Real.log_pos hT1
  have hδ0 : 0 ≤ δ := div_nonneg (add_nonneg Sieve.mertensBlockGapConst_nonneg
    (Real.log_nonneg (by norm_num))) hh.le
  have hδ : δ ≤ tol := (div_le_iff₀ hh).2 (by
    simpa only [mul_comm] using (div_le_iff₀ ht).1 hlarge)
  have hδe : δ ≤ e := hδ.trans (min_le_left _ _)
  have hδ1 : δ ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have herr := (le_div_iff₀ hC).1 (hδ.trans ((min_le_right _ _).trans (min_le_right _ _)) :
    δ ≤ min 1 (ε/2)/C)
  have ha0 : (0:ℝ) < a := by exact_mod_cast ha
  have hb0 : (0:ℝ) < b := ha0.trans_le (Nat.cast_le.mpr hab)
  have hx : x a ≤ x b := div_le_div_of_nonneg_right (Real.log_le_log ha0 (Nat.cast_le.mpr hab)) hh.le
  have hxb : x b ≤ 1/2 := by
    have hlog := Real.log_le_log (pow_pos hb0 2) hbT
    rw [Real.log_pow] at hlog
    apply (div_le_iff₀ hh).2
    norm_num1 at hlog
    linarith only [hlog]
  change d ≤ x a at hxa
  have hcomp : x b+δ ≤ 1-e := by dsimp [e] at hδe ⊢; linarith only [hδe,hxb,hd']
  have hlo : e ≤ x a-δ := by dsimp [e] at hδe ⊢; linarith only [hδe,hxa]
  let W := ∑ q ∈ windowPrimes a b, h/(q*(h-Real.log q))
  let Δ := pairPrimitive (x b)-pairPrimitive (x a)
  have hQ : windowPrimes a b=Nat.primesLE b \ Nat.primesLE a := by
    rw [windowPrimes_eq_primesLE_sdiff,Nat.floor_natCast,Nat.floor_natCast]
  have quad := semiprime_logarithmic_weight hh he a b ha hab hlo hcomp
  rw [←hQ] at quad
  have hkernel : |W-Δ| ≤ min 1 (ε/2) := by
    apply quad.trans
    apply le_trans _ herr
    apply mul_le_mul_of_nonneg_left _ hδ0
    have ha_nonneg : 0 ≤ x a := hd.le.trans hxa
    have hlen : x b-x a+2*δ ≤ 3 := by linarith only [hxb,ha_nonneg,hδ1]
    have htest := mul_le_mul_of_nonneg_left hlen (by positivity : 0 ≤ 1/e^4)
    change 2*B+(1/e^4)*(x b-x a+2*δ) ≤ 2*B+3*(1/e^4)
    linarith only [htest]
  have hdmax := (pairPrimitive_increment he (by dsimp [e]; linarith only [hd,hxa]) hx
    (by linarith only [hcomp,hδ0])).2
  have hW : W ≤ B+1 := by
    have hdiff := (abs_le.mp hkernel).2.trans (min_le_left _ _)
    have hlen : (x b-x a)/e^2 ≤ 1/e^2 := div_le_div_of_nonneg_right
      (by linarith only [hxb,hxa,hd]) (sq_nonneg e)
    change Δ ≤ (x b-x a)/e^2 at hdmax
    linarith only [hdmax.trans hlen,hdiff]
  have hc := normalized_pair_error hT1 hbT (a := a) (fun q hq => by
    obtain ⟨hp,_,hqb⟩ := (mem_windowPrimes (Nat.cast_nonneg _) (Nat.cast_nonneg _)).1 hq
    have hq0 : (0:ℝ) < q := by exact_mod_cast hp.pos
    apply hH (T/q) ((le_max_right _ _).trans ?_)
    apply (le_div_iff₀ hq0).2
    rcases le_total J (q:ℝ) with h | h
    · exact (mul_le_mul (h.trans hqb) hqb hq0.le (Nat.cast_nonneg _)).trans
        ((sq (b:ℝ)).symm.le.trans hbT)
    · exact (mul_le_mul_of_nonneg_left h hJ0.le).trans ((sq J).symm.le.trans hT))
  change |((pairBand a b T).card:ℝ)*h/T-W| ≤ η*W at hc
  have hε' : η*(B+1)=ε/2 := div_mul_cancel₀ _ (by positivity)
  have hpart := hc.trans ((mul_le_mul_of_nonneg_left hW hη.le).trans_eq hε')
  exact (abs_sub_le _ W Δ).trans ((add_le_add hpart (hkernel.trans (min_le_right _ _))).trans_eq (by ring))

#print axioms eventually_uniform_semiprime_counts

end GaloisForLFunctions.RestrictedFactorizationCalculus
