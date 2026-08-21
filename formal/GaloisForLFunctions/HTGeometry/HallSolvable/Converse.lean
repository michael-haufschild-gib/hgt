import GaloisForLFunctions.HTGeometry.HallSolvable.Wielandt
import GaloisForLFunctions.HTGeometry.HallSolvable.PiSubgroup
import GaloisForLFunctions.HTGeometry.GroupCharacter.BurnsideUniverse
import Mathlib.Data.Nat.Factorization.Basic

/-!
# The converse of P. Hall's theorem

A finite group with the Hall property — a subgroup of order `m` for every factorisation
`card G = m * k` into coprime factors — is solvable.  Together with `exists_subgroup_card_of_coprime`
this gives Hall's characterisation of solvability.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.HallSolvable

open Subgroup

/-- `G` has the Hall property: a subgroup of order `m` for every coprime factorisation. -/
def HasHallProperty (G : Type u) [Group G] : Prop :=
  ∀ m k : ℕ, Nat.card G = m * k → Nat.Coprime m k → ∃ H : Subgroup G, Nat.card ↥H = m

variable {G : Type u} [Group G] [Finite G]

/-- Hall subgroups of a group with the Hall property again have the Hall property. -/
theorem hasHallProperty_of_hallSubgroup (h : HasHallProperty G) {A : Subgroup G}
    (hA : Nat.Coprime (Nat.card ↥A) A.index) : HasHallProperty ↥A := by
  intro n n' hcard hcop
  have hGcard : Nat.card G = Nat.card ↥A * A.index := (Subgroup.card_mul_index A).symm
  have hApos : 0 < A.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hcopn' : Nat.Coprime n' A.index :=
    Nat.Coprime.coprime_dvd_left ⟨n, by rw [hcard]; ring⟩ hA
  obtain ⟨K, hK⟩ := h (n * A.index) n' (by rw [hGcard, hcard]; ring)
    (Nat.Coprime.mul_left hcop hcopn'.symm)
  have hApos0 : 0 < Nat.card ↥A := Nat.card_pos
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0, zero_mul] at hcard; omega
    · exact h0
  have hn'pos : 0 < n' := by
    rcases Nat.eq_zero_or_pos n' with h0 | h0
    · rw [h0, mul_zero] at hcard; omega
    · exact h0
  have hKindex : K.index = n' := by
    have h1 : Nat.card ↥K * K.index = Nat.card G := Subgroup.card_mul_index K
    rw [hK, hGcard, hcard] at h1
    have h2 : (n * A.index) * K.index = (n * A.index) * n' := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have hinf : (K ⊓ A).index = n' * A.index := by
    rw [index_inf_eq_mul (by rw [hKindex]; exact hcopn'), hKindex]
  have hinfcard : Nat.card ↥(K ⊓ A) = n := by
    have h1 : Nat.card ↥(K ⊓ A) * (K ⊓ A).index = Nat.card G := Subgroup.card_mul_index _
    rw [hinf, hGcard, hcard] at h1
    have h2 : Nat.card ↥(K ⊓ A) * (n' * A.index) = n * (n' * A.index) := by rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h2
  refine ⟨(K ⊓ A).subgroupOf A, ?_⟩
  have h2 := Subgroup.card_map_of_injective (K := (K ⊓ A).subgroupOf A)
    (Subgroup.subtype_injective A)
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (inf_le_right : K ⊓ A ≤ A)] at h2
  rw [← h2, hinfcard]

/-- A group whose order has at most two prime divisors is solvable. -/
theorem isSolvable_of_primeFactors_card_le_two
    (h : (Nat.card G).primeFactors.card ≤ 2) : IsSolvable G := by
  classical
  have hGne : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
  have hfact : Nat.card G = ∏ r ∈ (Nat.card G).primeFactors, r ^ (Nat.card G).factorization r :=
    Nat.prod_primeFactors_pow_factorization hGne
  interval_cases hc : (Nat.card G).primeFactors.card
  · rw [Finset.card_eq_zero.mp hc, Finset.prod_empty] at hfact
    exact GroupCharacter.isSolvable_of_card_dvd_two_prime_powers (p := 2) (q := 2)
      (a := 0) (b := 0) Nat.prime_two Nat.prime_two (by rw [hfact]; norm_num)
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
    have hpprime : p.Prime :=
      Nat.prime_of_mem_primeFactors (by rw [hp]; exact Finset.mem_singleton_self p)
    rw [hp, Finset.prod_singleton] at hfact
    set a := (Nat.card G).factorization p with ha
    refine GroupCharacter.isSolvable_of_card_dvd_two_prime_powers (p := p) (q := p)
      (a := a) (b := 0) hpprime hpprime ?_
    rw [pow_zero, mul_one]
    exact hfact.dvd
  · obtain ⟨p, q, hpq, hset⟩ := Finset.card_eq_two.mp hc
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors (by rw [hset]; simp)
    rw [hset, Finset.prod_pair hpq] at hfact
    exact GroupCharacter.isSolvable_of_card_dvd_two_prime_powers hpprime hqprime hfact.dvd

private theorem converseAux (r : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = r → HasHallProperty G → IsSolvable G := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro G _ _ hr hHall
    classical
    have hGne : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
    by_cases hle : (Nat.card G).primeFactors.card ≤ 2
    · exact isSolvable_of_primeFactors_card_le_two hle
    push_neg at hle
    have key : ∀ p : ℕ, p ∈ (Nat.card G).primeFactors →
        ∃ H : Subgroup G, IsSolvable ↥H ∧ H.index = p ^ ((Nat.card G).factorization p) := by
      intro p hpm
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hpm
      have hpdvd : p ∣ Nat.card G := Nat.dvd_of_mem_primeFactors hpm
      have hapos : 0 < (Nat.card G).factorization p := hp.factorization_pos_of_dvd hGne hpdvd
      have hkpos : 0 < p ^ ((Nat.card G).factorization p) := pow_pos hp.pos _
      have hk1 : 1 < p ^ ((Nat.card G).factorization p) := Nat.one_lt_pow hapos.ne' hp.one_lt
      have hmk : Nat.card G
          = (Nat.card G / p ^ ((Nat.card G).factorization p)) * p ^ ((Nat.card G).factorization p) :=
        (Nat.div_mul_cancel (Nat.ordProj_dvd _ _)).symm
      have hcop : Nat.Coprime (Nat.card G / p ^ ((Nat.card G).factorization p))
          (p ^ ((Nat.card G).factorization p)) :=
        Nat.Coprime.pow_right _ (Nat.coprime_ordCompl hp hGne).symm
      have hmpos : 0 < Nat.card G / p ^ ((Nat.card G).factorization p) := by
        rcases Nat.eq_zero_or_pos (Nat.card G / p ^ ((Nat.card G).factorization p)) with h0 | h0
        · rw [h0, zero_mul] at hmk; omega
        · exact h0
      obtain ⟨H, hH⟩ := hHall _ _ hmk hcop
      have hindex : H.index = p ^ ((Nat.card G).factorization p) := by
        have h1 : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
        rw [hH] at h1
        exact Nat.eq_of_mul_eq_mul_left hmpos (h1.trans hmk)
      have hlt : Nat.card ↥H < r := by
        rw [← hr, hH]
        nlinarith [hmk]
      have hHall' : HasHallProperty ↥H :=
        hasHallProperty_of_hallSubgroup hHall (by rw [hH, hindex]; exact hcop)
      exact ⟨H, ih _ hlt ↥H rfl hHall', hindex⟩
    -- three distinct primes give three solvable subgroups of pairwise coprime indices
    obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hle
    obtain ⟨p₁, p₂, p₃, h12, h13, h23, hteq⟩ := Finset.card_eq_three.mp htc
    have hm1 : p₁ ∈ (Nat.card G).primeFactors := hts (by rw [hteq]; simp)
    have hm2 : p₂ ∈ (Nat.card G).primeFactors := hts (by rw [hteq]; simp)
    have hm3 : p₃ ∈ (Nat.card G).primeFactors := hts (by rw [hteq]; simp)
    obtain ⟨H₁, hH₁s, hH₁i⟩ := key p₁ hm1
    obtain ⟨H₂, hH₂s, hH₂i⟩ := key p₂ hm2
    obtain ⟨H₃, hH₃s, hH₃i⟩ := key p₃ hm3
    haveI := hH₁s; haveI := hH₂s; haveI := hH₃s
    have hcp : ∀ {a b : ℕ}, a ∈ (Nat.card G).primeFactors → b ∈ (Nat.card G).primeFactors →
        a ≠ b → Nat.Coprime (a ^ ((Nat.card G).factorization a)) (b ^ ((Nat.card G).factorization b)) :=
      fun ha hb hab => Nat.Coprime.pow _ _
        ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors ha)
          (Nat.prime_of_mem_primeFactors hb)).mpr hab)
    exact isSolvable_of_three_coprime_index H₁ H₂ H₃
      (by rw [hH₁i, hH₂i]; exact hcp hm1 hm2 h12)
      (by rw [hH₁i, hH₃i]; exact hcp hm1 hm3 h13)
      (by rw [hH₂i, hH₃i]; exact hcp hm2 hm3 h23)

/-- **The converse of P. Hall's theorem.**  A finite group with the Hall property is solvable. -/
theorem isSolvable_of_hasHallProperty (h : HasHallProperty G) : IsSolvable G :=
  converseAux (Nat.card G) G rfl h

/-- **P. Hall's characterisation of solvability.** -/
theorem isSolvable_iff_hasHallProperty : IsSolvable G ↔ HasHallProperty G := by
  refine ⟨fun _ m k hmk hcop => exists_subgroup_card_of_coprime hmk hcop,
    isSolvable_of_hasHallProperty⟩

/-- **Solvability is equivalent to the existence of Hall `π`-subgroups for every set of primes.**
This is P. Hall's characterisation of solvable groups: the forward direction is `E_pi`, the
converse is Hall's 1937 theorem. -/
theorem isSolvable_iff_forall_exists_isHallPiSubgroup :
    IsSolvable G ↔ ∀ π : Set ℕ, ∃ H : Subgroup G, IsHallPiSubgroup π H := by
  refine ⟨fun _ π => exists_isHallPiSubgroup π, fun h => ?_⟩
  refine isSolvable_of_hasHallProperty fun m k hmk hcop => ?_
  obtain ⟨H, hH1, hH2⟩ := h {p : ℕ | p.Prime ∧ p ∣ m}
  refine ⟨H, ?_⟩
  refine pi_factorization_unique (Subgroup.card_mul_index H).symm hmk hH1 hH2 ?_ ?_
  · intro p hp hpm
    exact ⟨hp, hpm⟩
  · intro p hp hpk hmem
    exact hp.one_lt.ne' ((Nat.Coprime.coprime_dvd_left hmem.2 hcop).eq_one_of_dvd hpk)

end GaloisForLFunctions.HTGeometry.HallSolvable
