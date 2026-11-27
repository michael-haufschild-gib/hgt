import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Zeros.Bound
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Packets

/-! # Exceptional ratios for simultaneous thermal comparisons -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Universal

open Finset Real Set

/-- Ratios of positive blind temperatures on the same packet of at least three primes. -/
def exceptional : Set ℝ := {r | ∃ S : Finset Nat.Primes, 2<S.card ∧
  ∃ x ∈ Zeros.blind S, ∃ y ∈ Zeros.blind S, x/y=r}

theorem countable_exceptional : exceptional.Countable := by
  let ratios (S : Finset Nat.Primes) := (fun p : ℝ × ℝ => p.1/p.2) '' (Zeros.blind S ×ˢ Zeros.blind S)
  have eq : exceptional = ⋃ S : {S : Finset Nat.Primes // 2<S.card}, ratios S.val := by
    ext r
    constructor
    · rintro ⟨S,hs,x,hx,y,hy,h⟩
      exact mem_iUnion.mpr ⟨⟨S,hs⟩,⟨(x,y),⟨hx,hy⟩,h⟩⟩
    · intro h
      obtain ⟨S,p,hp,eqr⟩ := mem_iUnion.mp h
      exact ⟨S.val,S.property,p.1,hp.1,p.2,hp.2,eqr⟩
  rw [eq]
  apply Set.countable_iUnion
  intro S
  have finite := (Zeros.fixed_packet S.val S.property).1
  exact ((finite.prod finite).image _).countable

theorem exceptional_inv {r : ℝ} (h : r∈exceptional) : r⁻¹∈exceptional := by
  obtain ⟨S,hs,x,hx,y,hy,rfl⟩ := h
  exact ⟨S,hs,y,hy,x,hx,(inv_div x y).symm⟩

private theorem at_abs (S : Finset Nat.Primes) (t : ℝ) :
    Coincides (elementary (S := S)) |t| ↔ Coincides (elementary (S := S)) t := by
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h]
    simp only [Coincides,neg_neg]
    exact eq_comm

/-- Every real damping is separated by the two probes on every packet precisely
when their positive ratio avoids the countable exceptional set. -/
theorem detects_iff {r : ℝ} (hr : 0<r) :
    (∀ (S : Finset Nat.Primes), 2<S.card → ∀ d : ℝ,
      (Coincides (elementary (S := S)) d ∧ Coincides (elementary (S := S)) (r*d) ↔ d=0)) ↔
    r∉exceptional := by
  constructor
  · rintro all ⟨S,hs,x,hx,y,hy,eq⟩
    have scale : r*y=x := ((div_eq_iff hy.1.ne').mp eq).symm
    exact hy.1.ne' ((all S hs y).mp ⟨hy.2,by rw [scale]; exact hx.2⟩)
  · intro good S hs d
    constructor
    · rintro ⟨first,second⟩
      by_contra hn
      have a := abs_pos.mpr hn
      have b : Coincides (elementary (S := S)) (r*|d|) := by
        simpa only [abs_mul,abs_of_pos hr] using (at_abs S (r*d)).mpr second
      exact good ⟨S,hs,r*|d|,⟨mul_pos hr a,b⟩,|d|,⟨a,(at_abs S d).mpr first⟩,
        mul_div_cancel_right₀ r a.ne'⟩
    · rintro rfl
      simp only [mul_zero,Coincides,neg_zero,and_self]

/-- Each open interval of positive ratios contains a universal choice. -/
theorem good_between {a b : ℝ} (ab : a<b) : ∃ r ∈ Ioo a b, r∉exceptional := by
  obtain ⟨r,good,hr⟩ := (countable_exceptional.dense_compl ℝ).exists_between ab
  exact ⟨r,hr,good⟩

/-- Every individual positive probe admits a nonzero damping on a five-prime packet. -/
theorem one_probe_fails (u : ℝ) (hu : 0<u) (M : ℕ) :
    ∃ (S : Finset Nat.Primes) (d : ℝ), S.card=5 ∧ (∀ p ∈ S, M<p.val) ∧ 0<d ∧
      Coincides (elementary (S := S)) (u*d) := by
  obtain ⟨S,size,above,z,hz,_,blind⟩ := small_crossing 5 M le_rfl zero_lt_one
  exact ⟨S,z/u,size,above,div_pos hz.1 hu,by rwa [mul_div_cancel₀ z hu.ne']⟩

#print axioms countable_exceptional
#print axioms detects_iff
#print axioms good_between
#print axioms one_probe_fails

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Universal
