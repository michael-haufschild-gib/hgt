import GaloisForLFunctions.HTGeometry.HallSolvable.MinimalNormal
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# P. Hall's existence theorem for Hall subgroups of a solvable group

`exists_subgroup_card_of_coprime`: if `G` is a finite solvable group and `Nat.card G = m * k` with
`m` coprime to `k`, then `G` has a subgroup of order `m`.

The proof is the classical induction on `Nat.card G` through a minimal normal subgroup `N`, whose
order is a prime power `p ^ j` by `exists_abelian_normal_prime_pow_card`.  If `p ∣ m`, a Hall
subgroup of `G ⧸ N` pulls back to one of `G`.  If `p ∣ k`, the pullback `K` of a Hall subgroup of
`G ⧸ N` has order `m * p ^ j`; when `K` is proper we recurse into `K`, and otherwise `N` is itself
a normal Hall subgroup and Schur–Zassenhaus supplies a complement.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.HallSolvable

open Subgroup

variable {G : Type*} [Group G]

/-- The order of the preimage of a subgroup of `G ⧸ N`. -/
theorem card_comap_mk' [Finite G] (N : Subgroup G) [N.Normal] (Hb : Subgroup (G ⧸ N)) :
    Nat.card ↥(Hb.comap (QuotientGroup.mk' N)) = Nat.card ↥Hb * Nat.card ↥N := by
  have h1 : (Hb.comap (QuotientGroup.mk' N)).index = Hb.index :=
    Subgroup.index_comap_of_surjective Hb (QuotientGroup.mk'_surjective N)
  have h2 := Subgroup.card_mul_index (Hb.comap (QuotientGroup.mk' N))
  have h3 := Subgroup.card_mul_index Hb
  have h4 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
  have hpos : 0 < Hb.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card ↥(Hb.comap (QuotientGroup.mk' N)) * Hb.index
      = Nat.card G := by rw [← h1]; exact h2
    _ = Nat.card (G ⧸ N) * Nat.card ↥N := h4
    _ = Nat.card ↥Hb * Hb.index * Nat.card ↥N := by rw [h3]
    _ = Nat.card ↥Hb * Nat.card ↥N * Hb.index := by ring

private theorem hallExistsAux (r : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] [IsSolvable G] (m k : ℕ),
      Nat.card G = r → Nat.card G = m * k → Nat.Coprime m k →
      ∃ H : Subgroup G, Nat.card ↥H = m := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro G _ _ _ m k hr hmk hcop
    have hGpos : 0 < Nat.card G := Nat.card_pos
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · simp [h] at hmk; omega
      · exact h
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h] at hmk; omega
      · exact h
    rcases eq_or_ne (Nat.card G) 1 with h1 | h1
    · refine ⟨⊥, ?_⟩
      rw [Subgroup.card_bot]
      have : m ∣ 1 := ⟨k, by rw [← hmk, h1]⟩
      exact (Nat.eq_one_of_dvd_one this).symm ▸ rfl
    · haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨N, p, j, hNnorm, hNbot, hp, hj, hNcard, hNcomm⟩ :=
        exists_abelian_normal_prime_pow_card (G := G)
      haveI : N.Normal := hNnorm
      have hpjpos : 0 < p ^ j := pow_pos hp.pos j
      have hpjgt : 1 < p ^ j := Nat.one_lt_pow hj.ne' hp.one_lt
      have hNdvd : p ^ j ∣ m * k := by
        rw [← hmk, ← hNcard]; exact Subgroup.card_subgroup_dvd_card N
      have hpdvd : p ∣ m * k := dvd_trans (dvd_pow_self p hj.ne') hNdvd
      -- the quotient
      have hquotcard : Nat.card (G ⧸ N) * p ^ j = Nat.card G := by
        rw [← hNcard]; exact (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
      haveI : Finite (G ⧸ N) := inferInstance
      rcases (hp.dvd_mul).mp hpdvd with hpm | hpk
      · -- `p ∣ m`
        have hpk' : ¬ p ∣ k := fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd
          (Nat.Coprime.coprime_dvd_left hpm hcop) h)
        have hcoppk : Nat.Coprime (p ^ j) k :=
          Nat.Coprime.pow_left j (hp.coprime_iff_not_dvd.mpr hpk')
        obtain ⟨m', hm'⟩ : p ^ j ∣ m := hcoppk.dvd_of_dvd_mul_right hNdvd
        have hqc : Nat.card (G ⧸ N) = m' * k := by
          refine Nat.eq_of_mul_eq_mul_right hpjpos ?_
          rw [hquotcard, hmk, hm']; ring
        have hlt : Nat.card (G ⧸ N) < r := by
          rw [← hr, ← hquotcard]
          have : 0 < Nat.card (G ⧸ N) := Nat.card_pos
          nlinarith
        have hcop' : Nat.Coprime m' k :=
          Nat.Coprime.coprime_dvd_left ⟨p ^ j, by rw [hm']; ring⟩ hcop
        obtain ⟨Hb, hHb⟩ := ih (Nat.card (G ⧸ N)) hlt (G ⧸ N) m' k rfl hqc hcop'
        refine ⟨Hb.comap (QuotientGroup.mk' N), ?_⟩
        rw [card_comap_mk', hHb, hNcard, hm']; ring
      · -- `p ∣ k`
        have hpm' : ¬ p ∣ m := fun h =>
          hp.one_lt.ne' ((Nat.Coprime.coprime_dvd_left h hcop).eq_one_of_dvd hpk)
        have hcoppm : Nat.Coprime (p ^ j) m :=
          Nat.Coprime.pow_left j (hp.coprime_iff_not_dvd.mpr hpm')
        obtain ⟨k', hk'⟩ : p ^ j ∣ k :=
          hcoppm.dvd_of_dvd_mul_right (by rwa [mul_comm] at hNdvd)
        have hqc : Nat.card (G ⧸ N) = m * k' := by
          refine Nat.eq_of_mul_eq_mul_right hpjpos ?_
          rw [hquotcard, hmk, hk']; ring
        have hk'pos : 0 < k' := by
          rcases Nat.eq_zero_or_pos k' with h | h
          · rw [h, mul_zero] at hk'; omega
          · exact h
        rcases eq_or_ne k' 1 with hk1 | hk1
        · -- `N` is a normal Hall subgroup: use Schur–Zassenhaus
          have hNk : Nat.card ↥N = k := by rw [hNcard, hk', hk1, mul_one]
          have hindex : N.index = m := by
            refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < Nat.card ↥N) ?_
            rw [Subgroup.card_mul_index, hmk, hNk]; ring
          have hcopN : Nat.Coprime (Nat.card ↥N) N.index := by rw [hNk, hindex]; exact hcop.symm
          obtain ⟨H, hH⟩ := Subgroup.exists_right_complement'_of_coprime hcopN
          refine ⟨H, ?_⟩
          refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < Nat.card ↥N) ?_
          rw [hH.card_mul, hmk, hNk]; ring
        · -- recurse into the proper subgroup `K`
          have hlt : Nat.card (G ⧸ N) < r := by
            rw [← hr, ← hquotcard]
            have : 0 < Nat.card (G ⧸ N) := Nat.card_pos
            nlinarith
          have hcop' : Nat.Coprime m k' :=
            Nat.Coprime.coprime_dvd_left (dvd_refl m) (Nat.Coprime.coprime_dvd_right
              ⟨p ^ j, by rw [hk']; ring⟩ hcop)
          obtain ⟨Kb, hKb⟩ := ih (Nat.card (G ⧸ N)) hlt (G ⧸ N) m k' rfl hqc hcop'
          set K : Subgroup G := Kb.comap (QuotientGroup.mk' N) with hK
          have hKcard : Nat.card ↥K = m * p ^ j := by
            rw [hK, card_comap_mk', hKb, hNcard]
          have hKlt : Nat.card ↥K < r := by
            rw [hKcard, ← hr, hmk, hk']
            have : 1 < k' := by omega
            nlinarith
          haveI : IsSolvable ↥K := inferInstance
          obtain ⟨H', hH'⟩ := ih (Nat.card ↥K) hKlt ↥K m (p ^ j) rfl hKcard hcoppm.symm
          refine ⟨H'.map K.subtype, ?_⟩
          rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective K), hH']

/-- **P. Hall's existence theorem.**  A finite solvable group whose order factors as `m * k` with
`m` and `k` coprime has a subgroup of order `m`. -/
theorem exists_subgroup_card_of_coprime {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {m k : ℕ} (hmk : Nat.card G = m * k) (hcop : Nat.Coprime m k) :
    ∃ H : Subgroup G, Nat.card ↥H = m :=
  hallExistsAux (Nat.card G) G m k rfl hmk hcop

end GaloisForLFunctions.HTGeometry.HallSolvable
