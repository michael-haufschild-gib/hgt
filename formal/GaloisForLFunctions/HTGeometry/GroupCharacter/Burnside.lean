import GaloisForLFunctions.HTGeometry.GroupCharacter.BurnsideKey
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Solvable

/-!
# Burnside's `p ^ a q ^ b` theorem

A finite group whose order has at most two prime divisors is solvable.
-/

namespace GaloisForLFunctions.HTGeometry.GroupCharacter

open MonoidAlgebra

variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

/-- The class equation. -/
theorem card_conjClass (x : G) :
    (conjClass x).card = (Subgroup.centralizer ({x} : Set G)).index := by
  classical
  have hset : ((conjClass x : Finset G) : Set G) = MulAction.orbit (ConjAct G) x := by
    ext y
    simp only [conjClass, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      MulAction.mem_orbit_iff, Set.mem_range, ConjAct.smul_def]
    exact ⟨fun ⟨g, hg⟩ => ⟨ConjAct.toConjAct g, by simpa using hg⟩,
      fun ⟨c, hc⟩ => ⟨ConjAct.ofConjAct c, hc⟩⟩
  have h1 : Nat.card (MulAction.orbit (ConjAct G) x)
      = (MulAction.stabilizer (ConjAct G) x).index := by
    rw [Subgroup.index]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) x)
  have h2 : (MulAction.stabilizer (ConjAct G) x).index
      = (Subgroup.centralizer ({x} : Set G)).index := by
    rw [ConjAct.stabilizer_eq_centralizer]
    rfl
  rw [← h2, ← h1, ← hset]
  exact (Nat.card_eq_finsetCard _).symm

/-- If the conjugacy class of `x` is a singleton then `x` is central. -/
theorem mem_center_of_card_conjClass_eq_one {x : G} (h : (conjClass x).card = 1) :
    ∀ g : G, g * x = x * g := by
  classical
  intro g
  have hx : x ∈ conjClass x := self_mem_conjClass x
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h
  have hgx : g * x * g⁻¹ ∈ conjClass x :=
    Finset.mem_image.mpr ⟨g, Finset.mem_univ g, rfl⟩
  rw [hy, Finset.mem_singleton] at hx hgx
  have : g * x * g⁻¹ = x := by rw [hgx, hx]
  calc g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [this]

private theorem burnsideAux (r : ℕ) :
    ∀ (G : Type) [Group G] [Fintype G] (p q a b : ℕ), p.Prime → q.Prime →
      Nat.card G = r → Nat.card G ∣ p ^ a * q ^ b → IsSolvable G := by
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro G _ _ p q a b hp hq hr hdvd
    classical
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact q.Prime := ⟨hq⟩
    have hcardpos : 0 < Nat.card G := Nat.card_pos
    -- passing to a proper nontrivial normal subgroup
    have hstep : ∀ H : Subgroup G, H.Normal → H ≠ ⊥ → H ≠ ⊤ → IsSolvable G := by
      intro H hHn hHb hHt
      haveI := hHn
      have hHdvd : Nat.card ↥H ∣ Nat.card G := Subgroup.card_subgroup_dvd_card H
      have hHlt : Nat.card ↥H < r := by
        rw [← hr]
        refine lt_of_le_of_ne (Nat.le_of_dvd hcardpos hHdvd) ?_
        intro h
        exact hHt (Subgroup.eq_top_of_card_eq H h)
      have hidx : Nat.card (G ⧸ H) = H.index := (Subgroup.index_eq_card H).symm
      have hQlt : Nat.card (G ⧸ H) < r := by
        rw [← hr, hidx]
        have h1 : Nat.card ↥H * H.index = Nat.card G := Subgroup.card_mul_index H
        have h2 : 1 < Nat.card ↥H := (Subgroup.one_lt_card_iff_ne_bot H).mpr hHb
        have h3 : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
        nlinarith
      haveI : IsSolvable ↥H := ih _ hHlt ↥H p q a b hp hq rfl (hHdvd.trans hdvd)
      haveI : IsSolvable (G ⧸ H) := ih _ hQlt (G ⧸ H) p q a b hp hq rfl
        (by rw [hidx]; exact (Subgroup.index_dvd_card H).trans hdvd)
      exact solvable_of_ker_le_range H.subtype (QuotientGroup.mk' H)
        (by rw [QuotientGroup.ker_mk', H.range_subtype])
    -- abelian groups are solvable
    have habel : (∀ x y : G, x * y = y * x) → IsSolvable G := fun h => isSolvable_of_comm h
    by_cases hqd : q ∣ Nat.card G
    swap
    · obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow hp).mp
        (Nat.Coprime.dvd_of_dvd_mul_right
          (Nat.Coprime.pow_right b ((hq.coprime_iff_not_dvd.mpr hqd).symm)) hdvd)
      haveI : Group.IsNilpotent G := (IsPGroup.of_card hm).isNilpotent
      exact IsNilpotent.to_isSolvable
    by_cases hpd : p ∣ Nat.card G
    swap
    · obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow hq).mp
        (Nat.Coprime.dvd_of_dvd_mul_left
          (Nat.Coprime.pow_right a ((hp.coprime_iff_not_dvd.mpr hpd).symm)) hdvd)
      haveI : Group.IsNilpotent G := (IsPGroup.of_card hm).isNilpotent
      exact IsNilpotent.to_isSolvable
    -- both primes divide the order
    obtain ⟨Q⟩ : Nonempty (Sylow q G) := inferInstance
    haveI : Nontrivial ↥(Q : Subgroup G) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr (Q.ne_bot_of_dvd_card hqd)
    haveI : Nontrivial ↥(Subgroup.center ↥(Q : Subgroup G)) :=
      IsPGroup.center_nontrivial Q.isPGroup'
    obtain ⟨z', hz'⟩ := exists_ne (1 : ↥(Subgroup.center ↥(Q : Subgroup G)))
    set z : G := ((z' : ↥(Q : Subgroup G)) : G) with hzdef
    have hz1 : z ≠ 1 := by
      intro h
      refine hz' ?_
      refine Subtype.ext (Subtype.ext ?_)
      exact h
    have hQC : (Q : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have := Subgroup.mem_center_iff.mp z'.2 ⟨y, hy⟩
      have h2 := congrArg (Subtype.val (p := fun g => g ∈ (Q : Subgroup G))) this
      simpa [hzdef] using h2.symm
    have hidxQ : ¬ q ∣ (Subgroup.centralizer ({z} : Set G)).index := by
      intro h
      exact Q.not_dvd_index (h.trans (Subgroup.index_dvd_of_le hQC))
    have hclassdvd : (conjClass z).card ∣ p ^ a := by
      rw [card_conjClass]
      refine Nat.Coprime.dvd_of_dvd_mul_right ?_
        ((Subgroup.index_dvd_card _).trans hdvd)
      exact Nat.Coprime.pow_right b ((hq.coprime_iff_not_dvd.mpr hidxQ).symm)
    obtain ⟨k, _, hkc⟩ := (Nat.dvd_prime_pow hp).mp hclassdvd
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · -- `z` is central
      rw [hk0, pow_zero] at hkc
      have hcen : ∀ g : G, g * z = z * g := mem_center_of_card_conjClass_eq_one hkc
      have hzmem : z ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr (fun g => hcen g)
      have hcenbot : Subgroup.center G ≠ ⊥ := by
        intro h
        rw [h, Subgroup.mem_bot] at hzmem
        exact hz1 hzmem
      by_cases htop : Subgroup.center G = ⊤
      · refine habel fun u v => ?_
        have : u ∈ Subgroup.center G := by rw [htop]; trivial
        exact (Subgroup.mem_center_iff.mp this v).symm
      · exact hstep (Subgroup.center G) inferInstance hcenbot htop
    · obtain ⟨H, hHn, hHb, hHt⟩ :=
        exists_proper_normal_of_conjClass_prime_pow z hz1 hp hk0 hkc
      exact hstep H hHn hHb hHt

omit [DecidableEq G] in
/-- **Burnside's `p ^ a q ^ b` theorem.**  A finite group whose order has at most two prime
divisors is solvable. -/
theorem isSolvable_of_card_dvd_prime_pow_mul_prime_pow {p q a b : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hdvd : Nat.card G ∣ p ^ a * q ^ b) : IsSolvable G :=
  burnsideAux (Nat.card G) G p q a b hp hq rfl hdvd

end GaloisForLFunctions.HTGeometry.GroupCharacter
