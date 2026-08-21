import GaloisForLFunctions.HTGeometry.HallSolvable.CoprimeIndex
import GaloisForLFunctions.HTGeometry.HallSolvable.MinimalNormal
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Wielandt's theorem

A finite group with three solvable subgroups of pairwise coprime indices is solvable.
-/

universe u

namespace GaloisForLFunctions.HTGeometry.HallSolvable

open Subgroup
open scoped Pointwise

variable {G : Type u} [Group G]

/-- The conjugate of a subgroup. -/
def conjSub (g : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub {g : G} {K : Subgroup G} {x : G} :
    x ∈ conjSub g K ↔ ∃ y ∈ K, g * y * g⁻¹ = x := Iff.rfl

theorem card_conjSub [Finite G] (g : G) (K : Subgroup G) :
    Nat.card ↥(conjSub g K) = Nat.card ↥K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem index_conjSub [Finite G] (g : G) (K : Subgroup G) : (conjSub g K).index = K.index := by
  have h1 := Subgroup.card_mul_index (conjSub g K)
  have h2 := Subgroup.card_mul_index K
  rw [card_conjSub] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)

theorem isSolvable_conjSub (g : G) (K : Subgroup G) [IsSolvable ↥K] :
    IsSolvable ↥(conjSub g K) := by
  have e : ↥K ≃* ↥(conjSub g K) :=
    Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  exact solvable_of_surjective (f := e.toMonoidHom) e.surjective

/-- A subgroup whose index is prime to `p` contains a Sylow `p`-subgroup of the whole group. -/
theorem exists_sylow_le [Finite G] {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hpK : ¬ p ∣ K.index) : ∃ P : Sylow p G, (P : Subgroup G) ≤ K := by
  obtain ⟨Q₀⟩ : Nonempty (Sylow p ↥K) := inferInstance
  have hcardQ : Nat.card ↥((Q₀ : Subgroup ↥K).map K.subtype)
      = p ^ (Nat.card ↥K).factorization p := by
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective K)]
    exact Q₀.card_eq_multiplicity
  have hfact : (Nat.card ↥K).factorization p = (Nat.card G).factorization p := by
    have h1 : Nat.card ↥K * K.index = Nat.card G := Subgroup.card_mul_index K
    rw [← h1, Nat.factorization_mul (Nat.card_pos (α := ↥K)).ne'
      (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := K))).ne']
    simp [Nat.factorization_eq_zero_of_not_dvd hpK]
  refine ⟨Sylow.ofCard ((Q₀ : Subgroup ↥K).map K.subtype) (by rw [hcardQ, hfact]), ?_⟩
  rw [Sylow.coe_ofCard]
  rintro x ⟨y, -, rfl⟩
  exact y.2

/-- The key step of Wielandt's theorem. -/
theorem exists_normal_of_pair [Finite G] {H K : Subgroup G} [IsSolvable ↥K]
    {M : Subgroup G} (hMne : M ≠ ⊥)
    (hMnorm : ∀ h ∈ H, ∀ m ∈ M, h * m * h⁻¹ ∈ M)
    {p : ℕ} (hp : p.Prime) (hMp : IsPGroup p ↥M)
    (hpK : ¬ p ∣ K.index) (hcop : Nat.Coprime K.index H.index) (hKtop : K ≠ ⊤) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ ∧ IsSolvable ↥N := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hMP⟩ := IsPGroup.exists_le_sylow hMp
  obtain ⟨Q, hQK⟩ := exists_sylow_le hpK
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hPconj : (P : Subgroup G) ≤ conjSub g K := by
    rw [← hg]
    intro x hx
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hQK hy, rfl⟩
  have hMK : M ≤ conjSub g K := le_trans hMP hPconj
  have hprod : (↑(conjSub g K) : Set G) * (↑H : Set G) = Set.univ :=
    mul_eq_univ_of_coprime_index (by rw [index_conjSub]; exact hcop)
  have hconj : ∀ x : G, ∀ m ∈ M, x * m * x⁻¹ ∈ conjSub g K := by
    intro x m hm
    have hx : x ∈ (↑(conjSub g K) : Set G) * (↑H : Set G) := by rw [hprod]; trivial
    obtain ⟨k, hk, h, hh, rfl⟩ := Set.mem_mul.mp hx
    have h1 : h * m * h⁻¹ ∈ M := hMnorm h hh m hm
    have h2 : (k * h) * m * (k * h)⁻¹ = k * (h * m * h⁻¹) * k⁻¹ := by group
    rw [h2]
    exact (conjSub g K).mul_mem ((conjSub g K).mul_mem hk (hMK h1)) ((conjSub g K).inv_mem hk)
  have hle : Subgroup.normalClosure (↑M : Set G) ≤ conjSub g K := by
    rw [Subgroup.normalClosure]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, hc⟩ := isConj_iff.mp hax
    rw [← hc]
    exact hconj c a ha
  haveI : IsSolvable ↥(conjSub g K) := isSolvable_conjSub g K
  refine ⟨Subgroup.normalClosure (↑M : Set G), inferInstance, ?_, ?_, ?_⟩
  · intro hbot
    refine hMne (eq_bot_iff.mpr fun x hx => ?_)
    have hmem : x ∈ Subgroup.normalClosure (↑M : Set G) := Subgroup.subset_normalClosure hx
    rw [hbot] at hmem
    exact hmem
  · intro htop
    refine hKtop ?_
    have : conjSub g K = ⊤ := eq_top_iff.mpr (htop ▸ hle)
    have hidx : K.index = 1 := by rw [← index_conjSub g K, this, Subgroup.index_top]
    exact Subgroup.index_eq_one.mp hidx
  · exact solvable_of_solvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)

private theorem wielandtAux (r : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G] (H K L : Subgroup G),
      IsSolvable ↥H → IsSolvable ↥K → IsSolvable ↥L → Nat.card G = r →
      Nat.Coprime H.index K.index → Nat.Coprime H.index L.index →
      Nat.Coprime K.index L.index → IsSolvable G := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro G _ _ H K L hH hK hL hr hHK hHL hKL
    classical
    have htop : ∀ A : Subgroup G, IsSolvable ↥A → A = ⊤ → IsSolvable G := by
      intro A hA hAtop
      subst hAtop
      exact solvable_of_surjective (f := (Subgroup.topEquiv (G := G)).toMonoidHom)
        Subgroup.topEquiv.surjective
    by_cases hKt : K = ⊤
    · exact htop K hK hKt
    by_cases hLt : L = ⊤
    · exact htop L hL hLt
    have hHb : H ≠ ⊥ := by
      intro hb
      refine hKt (Subgroup.index_eq_one.mp ?_)
      have h1 : H.index = Nat.card G := by rw [hb]; exact Subgroup.index_bot
      rw [h1] at hHK
      exact hHK.symm.eq_one_of_dvd (Subgroup.index_dvd_card K)
    haveI : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hHb
    obtain ⟨N₀, p, k, hN₀norm, hN₀bot, hp, hk, hN₀card, hN₀comm⟩ :=
      exists_abelian_normal_prime_pow_card (G := ↥H)
    have hMcard : Nat.card ↥(N₀.map H.subtype) = p ^ k := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective H)]
      exact hN₀card
    have hMne : N₀.map H.subtype ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hMcard
      have : 1 < p ^ k := Nat.one_lt_pow hk.ne' hp.one_lt
      omega
    have hMp : IsPGroup p ↥(N₀.map H.subtype) := IsPGroup.of_card hMcard
    have hMnorm : ∀ h ∈ H, ∀ m ∈ N₀.map H.subtype, h * m * h⁻¹ ∈ N₀.map H.subtype := by
      rintro h hh _ ⟨n, hn, rfl⟩
      exact ⟨⟨h, hh⟩ * n * ⟨h, hh⟩⁻¹, hN₀norm.conj_mem n hn ⟨h, hh⟩, rfl⟩
    have hcase : ¬ p ∣ K.index ∨ ¬ p ∣ L.index := by
      by_contra hcon
      push_neg at hcon
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hKL ▸ Nat.dvd_gcd hcon.1 hcon.2))
    obtain ⟨N, hNnorm, hNbot, hNtop, hNsolv⟩ :
        ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ ∧ IsSolvable ↥N := by
      rcases hcase with h | h
      · exact exists_normal_of_pair hMne hMnorm hp hMp h hHK.symm hKt
      · exact exists_normal_of_pair hMne hMnorm hp hMp h hHL.symm hLt
    haveI := hNnorm
    haveI := hNsolv
    -- the quotient is smaller and inherits the hypotheses
    have hidxN : Nat.card (G ⧸ N) = N.index := (Subgroup.index_eq_card N).symm
    have hlt : Nat.card (G ⧸ N) < r := by
      rw [← hr, hidxN]
      have h1 : Nat.card ↥N * N.index = Nat.card G := Subgroup.card_mul_index N
      have h2 : 1 < Nat.card ↥N := (Subgroup.one_lt_card_iff_ne_bot N).mpr hNbot
      have h3 : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      nlinarith
    have hindexmap : ∀ A : Subgroup G, (A.map (QuotientGroup.mk' N)).index ∣ A.index := by
      intro A
      rw [Subgroup.index_map, QuotientGroup.ker_mk', MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N), Subgroup.index_top, mul_one]
      exact Subgroup.index_dvd_of_le le_sup_left
    have hsolvmap : ∀ A : Subgroup G, IsSolvable ↥A → IsSolvable ↥(A.map (QuotientGroup.mk' N)) := by
      intro A hA
      exact solvable_of_surjective (f := (QuotientGroup.mk' N).subgroupMap A)
        (MonoidHom.subgroupMap_surjective _ _)
    haveI : IsSolvable (G ⧸ N) :=
      ih _ hlt (G ⧸ N) (H.map (QuotientGroup.mk' N)) (K.map (QuotientGroup.mk' N))
        (L.map (QuotientGroup.mk' N)) (hsolvmap H hH) (hsolvmap K hK) (hsolvmap L hL) rfl
        (Nat.Coprime.coprime_dvd_left (hindexmap H)
          (Nat.Coprime.coprime_dvd_right (hindexmap K) hHK))
        (Nat.Coprime.coprime_dvd_left (hindexmap H)
          (Nat.Coprime.coprime_dvd_right (hindexmap L) hHL))
        (Nat.Coprime.coprime_dvd_left (hindexmap K)
          (Nat.Coprime.coprime_dvd_right (hindexmap L) hKL))
    exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
      (by rw [QuotientGroup.ker_mk', N.range_subtype])

/-- **Wielandt's theorem.**  A finite group with three solvable subgroups of pairwise coprime
indices is solvable. -/
theorem isSolvable_of_three_coprime_index {G : Type u} [Group G] [Finite G]
    (H K L : Subgroup G) [IsSolvable ↥H] [IsSolvable ↥K] [IsSolvable ↥L]
    (hHK : Nat.Coprime H.index K.index) (hHL : Nat.Coprime H.index L.index)
    (hKL : Nat.Coprime K.index L.index) : IsSolvable G :=
  wielandtAux (Nat.card G) G H K L ‹_› ‹_› ‹_› rfl hHK hHL hKL

end GaloisForLFunctions.HTGeometry.HallSolvable
