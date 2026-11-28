import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EllipticCharacterSums
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularSquaringOrbits
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters

/-! Full-degree units of a finite field detect regular Frobenius orbits
from their character sums. Character orthogonality treats the general
case, and cyclic translations handle the four small cases. -/

noncomputable section

open Finset GlobalTheory.Published

namespace GlobalTheory.EllipticCharacters

variable {g : ℕ} [Fact g.Prime] {n : ℕ} {K : Type} [Field K] [Algebra (ZMod g) K]

private theorem card_unitGroup_eq [Fintype K] [Fintype Kˣ] (hd : Module.finrank (ZMod g) K = n) :
    Fintype.card Kˣ = g ^ n - 1 := by
  rw [← Nat.card_eq_fintype_card, Nat.card_units, Nat.card_eq_fintype_card,
    Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, hd]

theorem exists_fullDegree_unit_sum_ne_zero (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    (θ : Kˣ →* ℂˣ) (hθ : IsRegularChar g n θ) :
    ∃ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n ∧
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) ≠ 0 := by
  classical
  letI := finite_of_rank_eq hn hd
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite Kˣ
  by_contra! hnone
  obtain ⟨D, hD, -, hcard⟩ := exists_properDegreeUnitCover hn hd
  let S := frobeniusCharacterOrbit g n θ
  have hs : #S = n := card_frobeniusCharacterOrbit hθ
  have hsupp (z : Kˣ) (hz : z ∉ D) : orbitSumDifference S ∅ z = 0 := by
    rw [orbitSumDifference, sum_empty, sub_zero, sum_frobeniusCharacterOrbit hθ]
    exact hnone z (hD z hz)
  have hbound := card_le_of_difference_supported S ∅ (by simp) D hsupp (by simpa [hs] using hn)
  rw [card_unitGroup_eq hd, card_empty, add_zero, hs] at hbound
  have hg := (Fact.out : g.Prime).two_le
  have hstrict := degree_mul_properSubfieldBound_lt g n hg hn
  have hc := Nat.mul_le_mul_right n hcard
  rw [mul_comm n _] at hstrict
  omega

theorem exists_frobeniusPower_of_elliptic_sums_eq
    (hn : 0 < n) (hd : Module.finrank (ZMod g) K = n)
    (θ ψ : Kˣ →* ℂˣ) (hθ : IsRegularChar g n θ) (hψ : IsRegularChar g n ψ)
    (he : ∀ z : Kˣ, (minpoly (ZMod g) (z : K)).natDegree = n →
      ∑ j ∈ range n, ((θ (z ^ g ^ j) : ℂˣ) : ℂ) =
        ∑ j ∈ range n, ((ψ (z ^ g ^ j) : ℂˣ) : ℂ)) :
    ∃ j < n, ψ = θ ^ g ^ j := by
  classical
  letI := finite_of_rank_eq hn hd
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite Kˣ
  by_contra hne
  obtain ⟨D, hD, hzD, hcard⟩ := exists_properDegreeUnitCover hn hd
  let S := frobeniusCharacterOrbit g n θ
  let T := frobeniusCharacterOrbit g n ψ
  have hs : #S = n := card_frobeniusCharacterOrbit hθ
  have ht : #T = n := card_frobeniusCharacterOrbit hψ
  have hdis : Disjoint S T := disjoint_frobeniusCharacterOrbits hn hd θ ψ hne
  have hsupp (z : Kˣ) (hz : z ∉ D) : orbitSumDifference S T z = 0 := by
    rw [orbitSumDifference, sum_frobeniusCharacterOrbit hθ, sum_frobeniusCharacterOrbit hψ,
      he z (hD z hz), sub_self]
  let X := Kˣ →* ℂˣ
  have hcu := card_unitGroup_eq hd
  by_cases hex : (g = 2 ∧ n = 2) ∨ (g = 3 ∧ n = 2) ∨ (g = 2 ∧ n = 4) ∨ (g = 2 ∧ n = 6)
  · obtain ⟨e, hed, hex⟩ := exceptional_twistExponent g n hex
    obtain ⟨η, hgen, hmod⟩ := exists_character_generator (G := Kˣ)
    let τ : X := η ^ e
    let f : Fin (Fintype.card Kˣ) → X := fun j => η ^ (j : ℕ)
    have hfb : Function.Bijective f := by
      refine ⟨fun i j h => Fin.ext ?_, ?_⟩
      · have h' := (hmod i j).mp h
        rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at h'
      · intro χ
        obtain ⟨j, hj, hχ⟩ := hgen χ
        exact ⟨⟨j, hj⟩, hχ.symm⟩
    letI : Fintype X := Fintype.ofEquiv _ (Equiv.ofBijective f hfb)
    have hX : Fintype.card X = Fintype.card Kˣ := by
      rw [← Fintype.card_congr (Equiv.ofBijective f hfb), Fintype.card_fin]
    have hoη : orderOf η = Fintype.card Kˣ := by
      rw [← hX, ← Nat.card_eq_fintype_card]
      apply orderOf_eq_card_of_forall_mem_zpowers
      intro χ
      obtain ⟨j, hj, hχ⟩ := hgen χ
      exact Subgroup.mem_zpowers_iff.mpr ⟨j, by rw [zpow_natCast]; exact hχ.symm⟩
    haveI : IsCyclic X := isCyclic_of_orderOf_eq_card (η : X)
      (hoη.trans (hX.symm.trans Nat.card_eq_fintype_card.symm))
    have hτ : ∀ z ∈ D, τ z = 1 := by
      intro z hz
      obtain ⟨p, hp, hz⟩ := hzD z hz
      obtain ⟨k, hk⟩ := hed p hp
      change (η ^ e) z = 1
      rw [MonoidHom.pow_apply, ← map_pow, hk, pow_mul, hz, one_pow, map_one]
    have hm := translate_mem_of_difference_supported S T hdis D hsupp τ hτ
    have hS := card_eq_orderOf_mul_card_image_quotient S τ (fun x hx => (hm x).1 hx)
    have ho : orderOf τ = (g ^ n - 1) / Nat.gcd (g ^ n - 1) e := by
      calc
        orderOf τ = orderOf (η : X) / Nat.gcd (orderOf (η : X)) e := orderOf_pow (η : X)
        _ = _ := by rw [hoη, hcu]
    rcases hex with hbad | ⟨rfl, rfl, hthree⟩
    · exact hbad ⟨_, by rw [← ho, ← hs]; exact hS⟩
    · have hX' : Fintype.card X = 63 := hX.trans hcu
      have hτ' : orderOf τ = 3 := ho.trans hthree
      have hsame := (squaringOrbit_eq_orderNine hX' θ τ hτ' hθ (fun x hx => (hm x).1 hx)).trans
        (squaringOrbit_eq_orderNine hX' ψ τ hτ' hψ (fun x hx => (hm x).2 hx)).symm
      have hST : S = T := hsame
      have hmem : θ ∈ S := mem_frobeniusCharacterOrbit.mpr ⟨0, hn, MonoidHom.ext fun z => by
        simp only [pow_zero, MonoidHom.pow_apply, pow_one]⟩
      exact Finset.disjoint_left.mp hdis hmem (hST ▸ hmem)
  · have hbound := card_le_of_difference_supported S T hdis D hsupp (by rw [hs, ht]; omega)
    rw [hcu, hs, ht] at hbound
    have hstrict := two_mul_degree_mul_properSubfieldBound_lt g n (Fact.out : g.Prime).two_le hn hex
    have hc := Nat.mul_le_mul_right (n + n) hcard
    rw [mul_comm (2 * n) _, two_mul] at hstrict
    omega

end GlobalTheory.EllipticCharacters
