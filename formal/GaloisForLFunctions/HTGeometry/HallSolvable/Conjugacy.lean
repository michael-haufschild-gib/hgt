import GaloisForLFunctions.HTGeometry.HallSolvable.Existence
import GaloisForLFunctions.HTGeometry.HallSolvable.ComplementConjugacy

/-!
# P. Hall's conjugacy theorem for Hall subgroups of a solvable group

`conj_eq_of_card_eq_of_coprime`: if `G` is a finite solvable group, `Nat.card G = m * k` with `m`
coprime to `k`, and `H`, `K` are subgroups of order `m`, then `K` is a conjugate of `H`.

The induction runs through a minimal normal subgroup `N` of order `p ^ j`.  If `p ∣ m`, then every
subgroup of order `m` contains `N`, and conjugacy descends from `G ⧸ N`.  If `p ∣ k`, the images of
`H` and `K` in `G ⧸ N` again have order `m`, so after conjugating we may assume `H ⊔ N = K ⊔ N =: L`;
if `L` is proper we recurse into `L`, and otherwise `H` and `K` are complements of the abelian normal
subgroup `N` and `exists_conj_eq_of_isComplement'` applies.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.HallSolvable

open Subgroup

variable {G : Type*} [Group G]

theorem conj_comp_conj (g₁ g₂ : G) :
    ((MulAut.conj g₂).toMonoidHom).comp ((MulAut.conj g₁).toMonoidHom)
      = (MulAut.conj (g₂ * g₁)).toMonoidHom := by
  ext x
  show g₂ * (g₁ * x * g₁⁻¹) * g₂⁻¹ = g₂ * g₁ * x * (g₂ * g₁)⁻¹
  group

theorem map_conj_map_conj (S : Subgroup G) (g₁ g₂ : G) :
    (S.map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj g₂).toMonoidHom
      = S.map (MulAut.conj (g₂ * g₁)).toMonoidHom := by
  rw [Subgroup.map_map, conj_comp_conj]

theorem map_conj_map {G' : Type*} [Group G'] (f : G →* G') (S : Subgroup G) (g : G) :
    (S.map (MulAut.conj g).toMonoidHom).map f
      = (S.map f).map (MulAut.conj (f g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  show f (g * x * g⁻¹) = f g * f x * (f g)⁻¹
  simp

theorem card_map_conj [Finite G] (S : Subgroup G) (g : G) :
    Nat.card ↥(S.map (MulAut.conj g).toMonoidHom) = Nat.card ↥S :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem normal_map_conj (N : Subgroup G) [hN : N.Normal] (g : G) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  ext x
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact hN.conj_mem n hn g
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, ?_⟩
    · simpa using hN.conj_mem x hx g⁻¹
    · show g * (g⁻¹ * x * g) * g⁻¹ = x
      group

/-- The order of `S ⊔ N` for `N` normal, expressed through the image of `S` in `G ⧸ N`. -/
theorem card_sup_normal [Finite G] (N : Subgroup G) [N.Normal] (S : Subgroup G) :
    Nat.card ↥(S ⊔ N) = Nat.card ↥(S.map (QuotientGroup.mk' N)) * Nat.card ↥N := by
  have h := card_comap_mk' N (S.map (QuotientGroup.mk' N))
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h

private theorem hallConjAux (r : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] [IsSolvable G] (m k : ℕ),
      Nat.card G = r → Nat.card G = m * k → Nat.Coprime m k →
      ∀ H K : Subgroup G, Nat.card ↥H = m → Nat.card ↥K = m →
      ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro G _ _ _ m k hr hmk hcop H K hH hK
    have hGpos : 0 < Nat.card G := Nat.card_pos
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, zero_mul] at hmk; omega
      · exact h
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hmk; omega
      · exact h
    rcases eq_or_ne (Nat.card G) 1 with h1 | h1
    · have hHb : H = ⊥ :=
        Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_one (h1 ▸ Subgroup.card_subgroup_dvd_card H))
      have hKb : K = ⊥ :=
        Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_one (h1 ▸ Subgroup.card_subgroup_dvd_card K))
      exact ⟨1, by rw [hHb, hKb, Subgroup.map_bot]⟩
    · haveI : Nontrivial G := Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨N, p, j, hNnorm, hNbot, hp, hj, hNcard, hNcomm⟩ :=
        exists_abelian_normal_prime_pow_card (G := G)
      haveI : N.Normal := hNnorm
      haveI : IsMulCommutative ↥N := IsMulCommutative.of_setLike_mul_comm hNcomm
      have hpjpos : 0 < p ^ j := pow_pos hp.pos j
      have hpjgt : 1 < p ^ j := Nat.one_lt_pow hj.ne' hp.one_lt
      have hNdvd : p ^ j ∣ m * k := by
        rw [← hmk, ← hNcard]; exact Subgroup.card_subgroup_dvd_card N
      have hpdvd : p ∣ m * k := dvd_trans (dvd_pow_self p hj.ne') hNdvd
      have hquotcard : Nat.card (G ⧸ N) * p ^ j = Nat.card G := by
        rw [← hNcard]; exact (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
      -- lift a conjugating element from the quotient
      have hlift : ∀ (m' k' : ℕ), Nat.card (G ⧸ N) = m' * k' → Nat.Coprime m' k' →
          Nat.card ↥(H.map (QuotientGroup.mk' N)) = m' →
          Nat.card ↥(K.map (QuotientGroup.mk' N)) = m' →
          ∃ g : G, K ⊔ N = (H.map (MulAut.conj g).toMonoidHom) ⊔ N := by
        intro m' k' hq hcq hHi hKi
        have hlt : Nat.card (G ⧸ N) < r := by
          rw [← hr, ← hquotcard]
          have : 0 < Nat.card (G ⧸ N) := Nat.card_pos
          nlinarith
        obtain ⟨gb, hgb⟩ := ih (Nat.card (G ⧸ N)) hlt (G ⧸ N) m' k' rfl hq hcq
          (H.map (QuotientGroup.mk' N)) (K.map (QuotientGroup.mk' N)) hHi hKi
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N gb
        refine ⟨g, ?_⟩
        have hEq : K.map (QuotientGroup.mk' N)
            = (H.map (MulAut.conj g).toMonoidHom).map (QuotientGroup.mk' N) := by
          rw [map_conj_map]; exact hgb
        have := congrArg (fun T => Subgroup.comap (QuotientGroup.mk' N) T) hEq
        simpa only [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] using this
      rcases (hp.dvd_mul).mp hpdvd with hpm | hpk
      · -- `p ∣ m`: every subgroup of order `m` contains `N`
        have hpk' : ¬ p ∣ k := fun h =>
          hp.one_lt.ne' ((Nat.Coprime.coprime_dvd_left hpm hcop).eq_one_of_dvd h)
        have hcoppk : Nat.Coprime (p ^ j) k :=
          Nat.Coprime.pow_left j (hp.coprime_iff_not_dvd.mpr hpk')
        obtain ⟨m', hm'⟩ : p ^ j ∣ m := hcoppk.dvd_of_dvd_mul_right hNdvd
        have hNle : ∀ S : Subgroup G, Nat.card ↥S = m → N ≤ S := by
          intro S hS
          have h1 : Nat.card ↥(S ⊔ N) = Nat.card ↥(S.map (QuotientGroup.mk' N)) * p ^ j := by
            rw [card_sup_normal, hNcard]
          have hdvd1 : Nat.card ↥(S.map (QuotientGroup.mk' N)) ∣ m :=
            hS ▸ Subgroup.card_map_dvd S _
          have hcop1 : Nat.Coprime (Nat.card ↥(S ⊔ N)) k := by
            rw [h1]
            exact Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_left hdvd1 hcop) hcoppk
          have hdvdG : Nat.card ↥(S ⊔ N) ∣ m * k := hmk ▸ Subgroup.card_subgroup_dvd_card _
          have hdvdm : Nat.card ↥(S ⊔ N) ∣ m := hcop1.dvd_of_dvd_mul_right hdvdG
          have hSle : m ∣ Nat.card ↥(S ⊔ N) := hS ▸ Subgroup.card_dvd_of_le le_sup_left
          have hEqCard : Nat.card ↥(S ⊔ N) = m := Nat.dvd_antisymm hdvdm hSle
          have hEq : S = S ⊔ N := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hEqCard, hS])
          exact hEq ▸ le_sup_right
        have hNH : N ≤ H := hNle H hH
        have hNK : N ≤ K := hNle K hK
        have himg : ∀ S : Subgroup G, Nat.card ↥S = m → N ≤ S →
            Nat.card ↥(S.map (QuotientGroup.mk' N)) = m' := by
          intro S hS hNS
          have h1 : Nat.card ↥(S ⊔ N) = Nat.card ↥(S.map (QuotientGroup.mk' N)) * p ^ j := by
            rw [card_sup_normal, hNcard]
          rw [sup_eq_left.mpr hNS, hS, hm'] at h1
          exact (Nat.eq_of_mul_eq_mul_right hpjpos (by linarith [h1])).symm
        have hq : Nat.card (G ⧸ N) = m' * k := by
          refine Nat.eq_of_mul_eq_mul_right hpjpos ?_
          rw [hquotcard, hmk, hm']; ring
        have hcq : Nat.Coprime m' k :=
          Nat.Coprime.coprime_dvd_left ⟨p ^ j, by rw [hm']; ring⟩ hcop
        obtain ⟨g, hg⟩ := hlift m' k hq hcq (himg H hH hNH) (himg K hK hNK)
        refine ⟨g, ?_⟩
        have hNH1 : N ≤ H.map (MulAut.conj g).toMonoidHom := by
          rw [← normal_map_conj N g]
          exact Subgroup.map_mono hNH
        rwa [sup_eq_left.mpr hNK, sup_eq_left.mpr hNH1] at hg
      · -- `p ∣ k`
        have hpm' : ¬ p ∣ m := fun h =>
          hp.one_lt.ne' ((Nat.Coprime.coprime_dvd_left h hcop).eq_one_of_dvd hpk)
        have hcopmpj : Nat.Coprime m (p ^ j) :=
          (Nat.Coprime.pow_left j (hp.coprime_iff_not_dvd.mpr hpm')).symm
        obtain ⟨k', hk'⟩ : p ^ j ∣ k :=
          hcopmpj.symm.dvd_of_dvd_mul_right (by rwa [mul_comm] at hNdvd)
        have hq : Nat.card (G ⧸ N) = m * k' := by
          refine Nat.eq_of_mul_eq_mul_right hpjpos ?_
          rw [hquotcard, hmk, hk']; ring
        have hcq : Nat.Coprime m k' :=
          Nat.Coprime.coprime_dvd_right ⟨p ^ j, by rw [hk']; ring⟩ hcop
        have himg : ∀ S : Subgroup G, Nat.card ↥S = m →
            Nat.card ↥(S.map (QuotientGroup.mk' N)) = m := by
          intro S hS
          have h1 : Nat.card ↥(S ⊔ N) = Nat.card ↥(S.map (QuotientGroup.mk' N)) * p ^ j := by
            rw [card_sup_normal, hNcard]
          have hdvd1 : Nat.card ↥(S.map (QuotientGroup.mk' N)) ∣ m :=
            hS ▸ Subgroup.card_map_dvd S _
          have hdvd2 : m ∣ Nat.card ↥(S.map (QuotientGroup.mk' N)) * p ^ j := by
            rw [← h1]; exact hS ▸ Subgroup.card_dvd_of_le le_sup_left
          exact Nat.dvd_antisymm hdvd1 (hcopmpj.dvd_of_dvd_mul_right hdvd2)
        obtain ⟨g, hg⟩ := hlift m k' hq hcq (himg H hH) (himg K hK)
        have hH₁ : Nat.card ↥(H.map (MulAut.conj g).toMonoidHom) = m := by
          rw [card_map_conj, hH]
        have hLcard : Nat.card ↥(K ⊔ N) = m * p ^ j := by
          rw [card_sup_normal, himg K hK, hNcard]
        have hKL : K ≤ K ⊔ N := le_sup_left
        have hH₁L : H.map (MulAut.conj g).toMonoidHom ≤ K ⊔ N := by
          rw [hg]; exact le_sup_left
        rcases eq_or_ne k' 1 with hk1 | hk1
        · -- `N` is a Hall subgroup and the two subgroups are complements
          have hdisj : ∀ S : Subgroup G, Nat.card ↥S = m → N.IsComplement' S := by
            intro S hS
            refine Subgroup.isComplement'_iff_card_mul_and_disjoint.mpr ⟨?_, ?_⟩
            · rw [hNcard, hS, hmk, hk', hk1, mul_one]; ring
            · refine disjoint_iff.mpr (Subgroup.card_eq_one.mp ?_)
              refine Nat.eq_one_of_dvd_one ?_
              refine dvd_trans (Nat.dvd_gcd ?_ ?_) (dvd_of_eq hcopmpj)
              · exact hS ▸ Subgroup.card_dvd_of_le inf_le_right
              · exact hNcard ▸ Subgroup.card_dvd_of_le inf_le_left
          obtain ⟨u, _, hu⟩ := exists_conj_eq_of_isComplement' (N := N)
            (hdisj _ hH₁) (hdisj K hK) (by rw [hNcard, hH₁]; exact hcopmpj.symm)
          exact ⟨u * g, by rw [hu, map_conj_map_conj]⟩
        · -- recurse into the proper subgroup `K ⊔ N`
          have hk'1 : 1 < k' := by
            rcases Nat.eq_zero_or_pos k' with h | h
            · rw [h, mul_zero] at hk'; omega
            · omega
          have hLlt : Nat.card ↥(K ⊔ N) < r := by
            rw [hLcard, ← hr, hmk, hk']
            nlinarith
          haveI : IsSolvable ↥(K ⊔ N) := inferInstance
          have hcardsub : ∀ S : Subgroup G, S ≤ K ⊔ N →
              Nat.card ↥(S.subgroupOf (K ⊔ N)) = Nat.card ↥S := by
            intro S hSL
            have h := Subgroup.card_map_of_injective (K := S.subgroupOf (K ⊔ N))
              (Subgroup.subtype_injective (K ⊔ N))
            rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSL] at h
            exact h.symm
          obtain ⟨g', hg'⟩ := ih (Nat.card ↥(K ⊔ N)) hLlt ↥(K ⊔ N) m (p ^ j) rfl hLcard hcopmpj
            ((H.map (MulAut.conj g).toMonoidHom).subgroupOf (K ⊔ N)) (K.subgroupOf (K ⊔ N))
            (by rw [hcardsub _ hH₁L, hH₁]) (by rw [hcardsub K hKL, hK])
          have h0 : Subgroup.map (K ⊔ N).subtype (K.subgroupOf (K ⊔ N))
              = Subgroup.map (K ⊔ N).subtype
                (Subgroup.map (MulAut.conj g').toMonoidHom
                  ((H.map (MulAut.conj g).toMonoidHom).subgroupOf (K ⊔ N))) := by
            rw [hg']
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKL, map_conj_map,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hH₁L] at h0
          exact ⟨(K ⊔ N).subtype g' * g,
            h0.trans (map_conj_map_conj H g ((K ⊔ N).subtype g'))⟩

/-- **P. Hall's conjugacy theorem.**  In a finite solvable group of order `m * k` with `m` coprime
to `k`, any two subgroups of order `m` are conjugate. -/
theorem conj_eq_of_card_eq_of_coprime {G : Type u} [Group G] [Finite G] [IsSolvable G]
    {m k : ℕ} (hmk : Nat.card G = m * k) (hcop : Nat.Coprime m k)
    {H K : Subgroup G} (hH : Nat.card ↥H = m) (hK : Nat.card ↥K = m) :
    ∃ g : G, K = H.map (MulAut.conj g).toMonoidHom :=
  hallConjAux (Nat.card G) G m k rfl hmk hcop H K hH hK

end GaloisForLFunctions.HTGeometry.HallSolvable
