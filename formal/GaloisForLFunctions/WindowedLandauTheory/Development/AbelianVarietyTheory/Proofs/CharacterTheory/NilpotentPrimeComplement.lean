import Mathlib.GroupTheory.Nilpotent

/-! Projection onto the prime-to-`p` Sylow factors of a finite nilpotent group. -/

namespace GlobalTheory.CuspGL

/-- The prime-to-`p` projection leaves a commuting factor of `p`-power order. -/
theorem exists_primeComplement (G : Type) [Group G] [Finite G] [Group.IsNilpotent G]
    (p : ℕ) [hp : Fact p.Prime] :
    ∃ (H : Subgroup G) (π : G →* H), ¬ p ∣ Nat.card H ∧
      ∀ g : G, ∃ s : G, ∃ m : ℕ, g = (π g : G) * s ∧ Commute (π g : G) s ∧ s ^ p ^ m = 1 := by
  classical
  let I := (Nat.card G).primeFactors
  let J := {q : I // (q : ℕ) ≠ p}
  let U := ∀ q : I, ∀ P : Sylow (q : ℕ) G, P
  let W := ∀ q : J, ∀ P : Sylow (q.1 : ℕ) G, P
  let e : U ≃* G := Sylow.directProductOfNormal fun P => inferInstance
  let project : U →* W :=
    { toFun := fun x q P => x q.1 P
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let include : W →* U :=
    { toFun := fun x q P => if hq : (q : ℕ) ≠ p then x ⟨q, hq⟩ P else 1
      map_one' := by
        funext q P
        change (if hq : (q : ℕ) ≠ p then (1 : W) ⟨q, hq⟩ P else 1) = 1
        split_ifs <;> rfl
      map_mul' := fun x y => by
        funext q P
        change (if hq : (q : ℕ) ≠ p then (x * y) ⟨q, hq⟩ P else 1) =
          (if hq : (q : ℕ) ≠ p then x ⟨q, hq⟩ P else 1) *
            (if hq : (q : ℕ) ≠ p then y ⟨q, hq⟩ P else 1)
        split_ifs <;> simp }
  have hleft : Function.LeftInverse project include := by
    intro x
    funext q P
    change (if hq : (q.1 : ℕ) ≠ p then x ⟨q.1, hq⟩ P else 1) = x q P
    rw [dif_pos q.2]
  let embed := e.toMonoidHom.comp include
  let H := embed.range
  letI : Finite W := Finite.of_injective embed (e.injective.comp hleft.injective)
  have hcard : Nat.card W = Nat.card H := by
    apply Nat.card_eq_of_bijective embed.rangeRestrict
    exact ⟨fun x y h => hleft.injective (e.injective (congrArg Subtype.val h)),
      embed.rangeRestrict_surjective⟩
  have hW : ¬ p ∣ Nat.card W := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
    have he : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
    have hx₁ : x = 1 := by
      funext q P
      haveI : Fact (Nat.Prime (q.1 : ℕ)) := ⟨Nat.prime_of_mem_primeFactors q.1.2⟩
      obtain ⟨k, hk⟩ := P.isPGroup' (x q P)
      have hp' : (x q P) ^ p = 1 := congrFun (congrFun he q) P
      have hcop : Nat.Coprime ((q.1 : ℕ) ^ k) p :=
        ((Nat.coprime_primes Fact.out hp.out).mpr q.2).pow_left k
      exact orderOf_eq_one_iff.mp
        (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hp'))
    rw [hx₁, orderOf_one] at hx
    exact hp.out.ne_one hx.symm
  let π : G →* H := embed.rangeRestrict.comp (project.comp e.symm.toMonoidHom)
  refine ⟨H, π, hcard ▸ hW, ?_⟩
  intro g
  let x := e.symm g
  let s : U := fun q P => if (q : ℕ) ≠ p then 1 else x q P
  have hsplit : include (project x) * s = x := by
    funext q P
    change (if hq : (q : ℕ) ≠ p then x q P else 1) *
      (if (q : ℕ) ≠ p then 1 else x q P) = x q P
    split_ifs <;> simp
  have hcomm : Commute (include (project x)) s := by
    change include (project x) * s = s * include (project x)
    funext q P
    change (if hq : (q : ℕ) ≠ p then x q P else 1) * (if (q : ℕ) ≠ p then 1 else x q P) =
      (if (q : ℕ) ≠ p then 1 else x q P) * (if hq : (q : ℕ) ≠ p then x q P else 1)
    split_ifs <;> simp
  let m := (Nat.card G).factorization p
  have hs : s ^ p ^ m = 1 := by
    funext q P
    change (if (q : ℕ) ≠ p then 1 else x q P) ^ p ^ m = 1
    split_ifs with hq
    · exact one_pow _
    · have hq' : (q : ℕ) = p := not_ne_iff.mp hq
      haveI : Fact (Nat.Prime (q : ℕ)) := ⟨Nat.prime_of_mem_primeFactors q.2⟩
      have hc : Nat.card P = p ^ m := by rw [P.card_eq_multiplicity, hq']
      exact hc ▸ pow_card_eq_one' (x q P)
  refine ⟨e s, m, ?_, hcomm.map e.toMonoidHom, ?_⟩
  · change g = e (include (project x)) * e s
    rw [← e.map_mul, hsplit, e.apply_symm_apply]
  · rw [← e.map_pow, hs, e.map_one]

end GlobalTheory.CuspGL
