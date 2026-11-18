import GaloisForLFunctions.CountingHolography.Sections.TwoPlacePrecisionOnIntegerIntervals
import Mathlib.NumberTheory.Chebyshev

/-!
# Congruences after clearing a scalar denominator

Two coprime periods whose sum fits in an interval force a word to be
constant. For a rectangle embedding this forces almost every prime
between the narrow output length and half the input length to divide
any denominator clearing the narrow coordinate.
-/

namespace GaloisForLFunctions.CountingHolography.Sections

/-- The narrow coordinate multiplied by D respects congruences in the
two integer input coordinates, at every modulus. -/
def clearsSecond {n L s : ℕ} (f : Fin n × Fin n → Fin L × Fin s) (D : ℕ) : Prop :=
  ∀ (v : ℕ) x y, x.1.val ≡ y.1.val [MOD v] → x.2.val ≡ y.2.val [MOD v] →
    D*(f x).2.val ≡ D*(f y).2.val [MOD v]

/-- Extend the first P entries periodically. Each residue has a representative
whose Q-translate still lies in the original interval. The extension therefore
has both periods and is constant by the Chinese remainder theorem. -/
theorem constant_of_two_periods {α : Type*} {n P Q : ℕ} (f : Fin n → α)
    (hp : 0 < P) (hc : P.Coprime Q) (hn : P+Q ≤ n)
    (hP : ∀ x y : Fin n, x.val ≡ y.val [MOD P] → f x = f y)
    (hQ : ∀ x y : Fin n, x.val ≡ y.val [MOD Q] → f x = f y) :
    ∀ x y, f x = f y := by
  let low (a : ℕ) : Fin n := ⟨a%P,(Nat.mod_lt a hp).trans_le (by omega)⟩
  let g (a : ℕ) := f (low a)
  have hgP {a b : ℕ} (h : a ≡ b [MOD P]) : g a = g b := by
    exact congrArg f (Fin.ext h : low a = low b)
  have hlow (a : Fin n) : g a.val = f a := hP _ a (Nat.mod_modEq _ _)
  have hshift (a : ℕ) : g (a+Q) = g a := by
    let z : Fin n := ⟨a%P+Q, by have := Nat.mod_lt a hp; omega⟩
    calc g (a+Q) = g z.val := hgP ((Nat.mod_modEq _ _).symm.add_right Q)
      _ = f z := hlow z
      _ = f (low a) := hQ _ _ (by change (a%P+Q)%Q = (a%P)%Q; rw [Nat.add_mod_right])
  have hm (j : ℕ) : g (Q*j) = g 0 := by
    induction j with
    | zero => rw [Nat.mul_zero]
    | succ j ih => rw [Nat.mul_succ,hshift,ih]
  have hconst (a : ℕ) : g a = g 0 := by
    obtain ⟨z,hzP,hzQ⟩ := Nat.chineseRemainder hc a 0
    obtain ⟨j,hj⟩ := Nat.modEq_zero_iff_dvd.mp hzQ
    exact (hgP hzP.symm).trans (hj ▸ hm j)
  exact fun x y => (hlow x).symm.trans ((hconst _).trans ((hconst _).symm.trans (hlow y)))

/-- The sum of the two input periods suffices, including when their product
exceeds the interval length. -/
theorem input_lt_sum_of_periods {n L s P Q u v : ℕ} (e : (Fin n × Fin n) ↪ (Fin L × Fin s))
    (hc : P.Coprime Q) (hp : 0 < P) (hL : L < n*n) (hu : s ≤ u) (hv : s ≤ v)
    (hP : preservesSecondMod e P u) (hQ : preservesSecondMod e Q v) : n < P+Q := by
  by_contra! hn
  have eqP (x y : Fin n × Fin n) (hx : x.1.val ≡ y.1.val [MOD P]) (hy : x.2.val ≡ y.2.val [MOD P]) :
      (e x).2 = (e y).2 := Fin.ext ((hP x y hx hy).eq_of_lt_of_lt ((e x).2.isLt.trans_le hu) ((e y).2.isLt.trans_le hu))
  have eqQ (x y : Fin n × Fin n) (hx : x.1.val ≡ y.1.val [MOD Q]) (hy : x.2.val ≡ y.2.val [MOD Q]) :
      (e x).2 = (e y).2 := Fin.ext ((hQ x y hx hy).eq_of_lt_of_lt ((e x).2.isLt.trans_le hv) ((e y).2.isLt.trans_le hv))
  have he (x y : Fin n × Fin n) : (e x).2 = (e y).2 := by
    have row := constant_of_two_periods (fun i => (e (i,x.2)).2) hp hc hn
      (fun i j h => eqP _ _ h .rfl) (fun i j h => eqQ _ _ h .rfl)
    have col := constant_of_two_periods (fun j => (e (y.1,j)).2) hp hc hn
      (fun i j h => eqP _ _ .rfl h) (fun i j h => eqQ _ _ .rfl h)
    exact (row x.1 y.1).trans (col x.2 y.2)
  let e₁ : (Fin n × Fin n) ↪ Fin L :=
    ⟨fun x => (e x).1,fun x y h => e.injective (Prod.ext h (he x y))⟩
  exact hL.not_ge (by simpa only [Fintype.card_prod,Fintype.card_fin] using Fintype.card_le_of_embedding e₁)

/-- All but at most one prime in the central range divide a common
clearing denominator. -/
theorem missing_prime_unique {n L s D : ℕ} (e : (Fin n × Fin n) ↪ (Fin L × Fin s))
    (hL : L < n*n) (hD : clearsSecond e D) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hsp : s ≤ p) (hsq : s ≤ q)
    (hn : p+q ≤ n) (hDp : ¬ p ∣ D) (hDq : ¬ q ∣ D) : p = q := by
  by_contra hne
  have h (t : ℕ) (ht : t.Prime) (hd : ¬ t ∣ D) : preservesSecondMod e t t := fun x y hx hy =>
    Nat.ModEq.cancel_left_of_coprime (ht.coprime_iff_not_dvd.mpr hd) (hD t x y hx hy)
  exact hn.not_gt (input_lt_sum_of_periods e ((Nat.coprime_primes hp hq).mpr hne) hp.pos hL hsp hsq
    (h _ hp hDp) (h _ hq hDq))

/-- The missing prime costs at most a single scalar q ≤ 2X in the primorial. -/
theorem primorial_dvd_cleared {n L s D X : ℕ} (e : (Fin n × Fin n) ↪ (Fin L × Fin s))
    (hL : L < n*n) (hD : clearsSecond e D) (hd : 0 < D)
    (hX : 0 < X) (hs : s ≤ X) (hn : 4*X ≤ n) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 2*X ∧ primorial (2*X) ∣ primorial X * D * q := by
  have hp (p : ℕ) (hpp : p.Prime) (hpx : p ≤ X) : p ∣ primorial X := by
    rw [primorial_eq_prod_primesLE]
    exact Finset.dvd_prod_of_mem _ (Nat.mem_primesLE.mpr ⟨hpx,hpp⟩)
  have assemble (q : ℕ) (hq : 0 < q)
      (hall : ∀ p, p.Prime → p ≤ 2*X → p ∣ primorial X * D * q) :
      primorial (2*X) ∣ primorial X * D * q := by
    rw [primorial_eq_prod_primesLE, ← primeFactors_primorial (2*X)]
    apply (Nat.prod_primeFactors_dvd_iff (Nat.mul_pos (Nat.mul_pos (primorial_pos X) hd) hq).ne').mpr
    intro p h
    rw [primeFactors_primorial, Nat.mem_primesLE] at h
    exact h.2.mem_primeFactors (hall _ h.2 h.1) (Nat.mul_pos (Nat.mul_pos (primorial_pos X) hd) hq).ne'
  by_cases h : ∃ p : ℕ, p.Prime ∧ X < p ∧ p ≤ 2*X ∧ ¬ p ∣ D
  · obtain ⟨q,hq,hxq,hqx,hqD⟩ := h
    refine ⟨q,hq.pos,hqx,assemble q hq.pos fun p hpp hpx => ?_⟩
    by_cases hx : p ≤ X
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (hp _ hpp hx) _) _
    by_cases hpd : p ∣ D
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hpd _) _
    have he := missing_prime_unique e hL hD hpp hq (by omega) (by omega) (by omega) hpd hqD
    rw [he]
    exact dvd_mul_left _ _
  · refine ⟨1,by decide,by omega,assemble 1 (by decide) fun p hpp hpx => ?_⟩
    rw [mul_one]
    by_cases hx : p ≤ X
    · exact dvd_mul_of_dvd_left (hp _ hpp hx) _
    exact dvd_mul_of_dvd_right (Classical.byContradiction fun hd' => h ⟨p,hpp,by omega,hpx,hd'⟩) _

/-- The least common multiple of the possible positive input differences
clears all integer congruences of every map of the interval square. -/
theorem lcmUpto_clearsSecond {n L s : ℕ} (f : Fin n × Fin n → Fin L × Fin s) :
    clearsSecond f (Nat.lcmUpto (n-1)) := by
  intro v x y hx hy
  rcases eq_or_ne v 0 with rfl | hv
  · have he : x = y := Prod.ext (Fin.ext (by simpa using hx)) (Fin.ext (by simpa using hy))
    rw [he]
  by_cases h : v < n
  · have hd : v ∣ Nat.lcmUpto (n-1) := Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr (by omega : 1 ≤ v ∧ v ≤ n-1))
    exact (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hd _)).trans
      (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_of_dvd_left hd _)).symm
  · have he : x = y := Prod.ext
      (Fin.ext (hx.eq_of_lt_of_lt (by have := x.1.isLt; omega) (by have := y.1.isLt; omega)))
      (Fin.ext (hy.eq_of_lt_of_lt (by have := x.2.isLt; omega) (by have := y.2.isLt; omega)))
    rw [he]

#print axioms constant_of_two_periods
#print axioms primorial_dvd_cleared
#print axioms lcmUpto_clearsSecond

end GaloisForLFunctions.CountingHolography.Sections
