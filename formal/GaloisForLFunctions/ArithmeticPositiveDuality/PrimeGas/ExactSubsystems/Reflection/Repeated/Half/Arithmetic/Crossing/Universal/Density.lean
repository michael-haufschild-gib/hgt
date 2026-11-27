import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Universal.Ratios
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Schedule.Alternation

/-! # Dense exceptional ratios from a fixed number of prime modes -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Universal

open Finset Real Set

/-- Two separated blind temperatures on nine primes can have their ratio in any
prescribed open interval above one. Both readings share the same energy scale. -/
theorem bad_between {a b : ℝ} (ha : 1<a) (ab : a<b) (M : ℕ) :
    ∃ (S : Finset Nat.Primes) (x y : ℝ), S.card=9 ∧ (∀ p ∈ S, M<p.val) ∧
      x∈Zeros.blind S ∧ y∈Zeros.blind S ∧ x/y∈Ioo a b := by
  obtain ⟨c,ac,cb⟩ := exists_between ab
  have a0 := zero_lt_one.trans ha
  have c1 := ha.trans ac
  have div : 1<c/a := (lt_div_iff₀ a0).mpr (by simpa only [one_mul] using ac)
  obtain ⟨δ,hδ,hsmall⟩ := exists_between (lt_min (sub_pos.mpr c1)
    (lt_min (sub_pos.mpr div) (sub_pos.mpr cb)))
  have dc : 1+δ<c := by linarith only [(lt_min_iff.mp hsmall).1]
  have da : (1+δ)*a<c := (lt_div_iff₀ a0).mp (by linarith only [(lt_min_iff.mp (lt_min_iff.mp hsmall).2).1])
  have db : c+δ<b := by linarith only [(lt_min_iff.mp (lt_min_iff.mp hsmall).2).2]
  let v : Fin 4 → ℝ := ![1,1+δ,c,c+δ]
  have mono : StrictMono v := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · change 1<1+δ; linarith only [hδ]
    · exact dc
    · change c<c+δ; linarith only [hδ]
  have vpos (i : Fin 4) : 0<v i := lt_of_lt_of_le (show 0<v 0 from zero_lt_one) (mono.monotone (Fin.zero_le i))
  let t : Fin 4 ↪o Ioi (0 : ℝ) := OrderEmbedding.ofStrictMono
    (fun i => (⟨v i,vpos i⟩ : Ioi (0 : ℝ))) (fun _ _ h => mono h)
  obtain ⟨S,K,size,above,pos,_,gap⟩ := Schedule.alternating_gaps (q := 3) (n := 9) le_rfl t M 0
  obtain ⟨y,hy,_,by'⟩ := gap 0
  obtain ⟨x,hx,_,bx⟩ := gap 2
  change y∈Ioo (1/K) ((1+δ)/K) at hy
  change x∈Ioo (c/K) ((c+δ)/K) at hx
  have yp := (one_div_pos.mpr pos).trans hy.1
  have xp := (div_pos (zero_lt_one.trans c1) pos).trans hx.1
  refine ⟨S,x,y,size,above,⟨xp,bx⟩,⟨yp,by'⟩,(lt_div_iff₀ yp).mpr ?_,(div_lt_iff₀ yp).mpr ?_⟩
  · calc
      a*y < a*((1+δ)/K) := mul_lt_mul_of_pos_left hy.2 a0
      _ = ((1+δ)*a)/K := by ring
      _ < c/K := (div_lt_div_iff_of_pos_right pos).mpr da
      _ < x := hx.1
  · calc
      x < (c+δ)/K := hx.2
      _ < b/K := (div_lt_div_iff_of_pos_right pos).mpr db
      _ = b*(1/K) := by ring
      _ < b*y := mul_lt_mul_of_pos_left hy.1 (a0.trans ab)

/-- Good and exceptional calibrations both occur in every interval above one. -/
theorem both_between {a b : ℝ} (ha : 1<a) (ab : a<b) :
    (∃ r ∈ Ioo a b, r∉exceptional) ∧ ∃ r ∈ Ioo a b, r∈exceptional := by
  obtain ⟨S,x,y,size,_,hx,hy,between⟩ := bad_between ha ab 0
  exact ⟨good_between ab,x/y,between,S,by omega,x,hx,y,hy,rfl⟩

#print axioms bad_between
#print axioms both_between

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Universal
