import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheArithmeticSquareIsCofree

/-!
# A perfect square keeps no contact

The jets of the archimedean fibre need an invertible Frobenius: on them `V_k = k F_k^{-1}`. The
contacts of the arithmetic square come from the Dwork congruences, in which `F_k` raises the
`p`-adic precision. The two requirements exclude each other.

* **The Frobenius-divisible elements of the arithmetic square are the constants**
  (`ghostComponent_eq_of_forall_exists_frobenius`): if `x = F_{p^j} y_j` for every prime power, then
  `x_{pn} − x_n` is divisible by every power of `p`, so `x_n = x_1` for all `n`.
* **A ring with surjective Frobenius lifts sees one graph**
  (`eq_of_surjective_frobeniusLifts`): if every `ψ_p` is surjective, then for every `ℤ`-point `f`
  and every `a`, `f(ψ_n a) = f(a)`. On a perfect ring with Frobenius lifts all the graphs coincide:
  it keeps no contact. The archimedean fibre and the finite fibres of the square cannot be put on
  one ring with Frobenius lifts by inverting the Frobenius.
-/

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- An integer divisible by every power of a prime is zero. -/
theorem eq_zero_of_forall_prime_pow_dvd {p : ℕ} (hp : p.Prime) {z : ℤ}
    (h : ∀ j : ℕ, (p : ℤ) ^ j ∣ z) : z = 0 := by
  by_contra hz
  have hd : p ^ z.natAbs ∣ z.natAbs := by
    have := h z.natAbs
    exact Int.natCast_dvd.mp (by exact_mod_cast this)
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hz) hd
  have hlt : z.natAbs < p ^ z.natAbs :=
    (Nat.lt_two_pow_self).trans_le (Nat.pow_le_pow_left hp.two_le _)
  omega

/-- If `x` is divisible by `F_{p^j}` for every `j`, then `x_{pn} = x_n`. -/
theorem ghostComponent_prime_mul_eq {x : ghostRing} {p : ℕ+} (hp : p.Prime)
    (h : ∀ j : ℕ, ∃ y : ghostRing, frobenius (p ^ j) y = x) (n : ℕ+) :
    ghostComponent (p * n) x = ghostComponent n x := by
  have hp' : (p : ℕ).Prime := hp
  refine sub_eq_zero.mp (eq_zero_of_forall_prime_pow_dvd hp' fun j => ?_)
  obtain ⟨y, rfl⟩ := h j
  have hy := y.2 p hp (p ^ j * n)
  rw [ghostComponent_frobenius, ghostComponent_frobenius, mul_left_comm]
  refine (pow_dvd_pow _ ?_).trans hy
  rw [PNat.mul_coe, PNat.pow_coe, Nat.factorization_mul (pow_ne_zero _ hp'.ne_zero) n.ne_zero,
    Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, hp'.factorization,
    Finsupp.single_eq_same, smul_eq_mul, mul_one]
  omega

/-- A sequence with `x_{pn} = x_n` for all primes `p` is constant. -/
theorem ghostComponent_eq_one_of_prime_mul {x : ghostRing}
    (h : ∀ p : ℕ+, p.Prime → ∀ n : ℕ+, ghostComponent (p * n) x = ghostComponent n x) (n : ℕ+) :
    ghostComponent n x = ghostComponent 1 x := by
  have key : ∀ k : ℕ, ∀ N : ℕ+, (N : ℕ) = k → ghostComponent N x = ghostComponent 1 x := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro N hN
      by_cases h1 : k = 1
      · have hN1 : N = 1 := PNat.eq (by rw [hN, h1]; rfl)
        rw [hN1]
      · have hp := Nat.minFac_prime h1
        obtain ⟨m, hm⟩ := Nat.minFac_dvd k
        have hk0 : 0 < k := hN ▸ N.pos
        have hm0 : 0 < m := by
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · rw [h0, mul_zero] at hm; omega
          · exact h0
        obtain ⟨P, hP⟩ : ∃ P : ℕ+, (P : ℕ) = k.minFac := ⟨⟨_, hp.pos⟩, rfl⟩
        obtain ⟨M, hM⟩ : ∃ M : ℕ+, (M : ℕ) = m := ⟨⟨m, hm0⟩, rfl⟩
        have hNPM : N = P * M := PNat.eq (by rw [PNat.mul_coe, hP, hM, hN]; exact hm)
        have hlt : m < k := by
          have := hp.one_lt
          calc m = 1 * m := (one_mul m).symm
            _ < k.minFac * m := Nat.mul_lt_mul_of_pos_right this hm0
            _ = k := hm.symm
        rw [hNPM, h P (show (P : ℕ).Prime from hP.symm ▸ hp) M]
        exact ih m hlt M hM
  exact key n n rfl

/-- **The Frobenius-divisible elements of the arithmetic square are the constants.** -/
theorem ghostComponent_eq_of_forall_exists_frobenius {x : ghostRing}
    (h : ∀ k : ℕ+, ∃ y : ghostRing, frobenius k y = x) (n : ℕ+) :
    ghostComponent n x = ghostComponent 1 x :=
  ghostComponent_eq_one_of_prime_mul
    (fun p hp m => ghostComponent_prime_mul_eq hp (fun j => h (p ^ j)) m) n

variable {A : Type*} [CommRing A]

/-- **A ring with surjective Frobenius lifts sees one graph.** If every `ψ_p` is surjective, every
`ℤ`-point is fixed by every `ψ_n`: `f(ψ_n a) = f(a)`. -/
theorem eq_of_surjective_frobeniusLifts (L : FrobeniusLifts A)
    (hsurj : ∀ p : ℕ+, p.Prime → Function.Surjective (L.ψ p)) (f : A →+* ℤ) (a : A) (n : ℕ+) :
    f (L.ψ n a) = f a := by
  have hpow : ∀ (p : ℕ+), p.Prime → ∀ j : ℕ, Function.Surjective (L.ψ (p ^ j)) := by
    intro p hp j
    induction j with
    | zero => intro b; exact ⟨b, by rw [pow_zero, L.ψ_one_apply]⟩
    | succ j ih =>
      intro b
      obtain ⟨c, hc⟩ := ih b
      obtain ⟨d, hd⟩ := hsurj p hp c
      exact ⟨d, by rw [pow_succ, L.ψ_mul_apply, hd, hc]⟩
  have h := ghostComponent_eq_one_of_prime_mul (x := ghostLift L f a)
    (fun p hp m => ghostComponent_prime_mul_eq hp (fun j => by
      obtain ⟨b, hb⟩ := hpow p hp j a
      exact ⟨ghostLift L f b, by rw [← ghostLift_frobenius, hb]⟩) m) n
  rwa [ghostComponent_ghostLift, ghostComponent_one_ghostLift] at h

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
