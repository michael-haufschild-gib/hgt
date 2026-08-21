import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Conjugacy of complements to an abelian normal subgroup of coprime index

Mathlib proves the *existence* half of the Schur–Zassenhaus theorem
(`Subgroup.exists_right_complement'_of_coprime`) but exports no conjugacy statement.  This file
supplies the conjugacy half in the case that is needed for P. Hall's theorem: `N` normal and
**abelian**, with `Nat.card N` coprime to the common order of the complements.

The proof is the classical cocycle-averaging argument.  If `K` is a complement of `N`, then for
every `g : G` there is a unique `γ g ∈ N` with `γ g * g ∈ K`, and `γ` satisfies the cocycle identity
`γ (g₁ * g₂) = γ g₁ * (g₁ * γ g₂ * g₁⁻¹)`.  Averaging that identity over a subgroup `H` of order `m`
which is also a complement gives `(γ h) ^ m = a * (h * a * h⁻¹)⁻¹` where `a = ∏_{h ∈ H} γ h`.
Because `x ↦ x ^ m` is bijective on `N`, writing `a = u⁻¹ ^ m` turns this into
`γ h = u⁻¹ * (h * u * h⁻¹)`, i.e. `u⁻¹ * h * u ∈ K` for every `h ∈ H`, so `K` is the conjugate
`u⁻¹ H u`.
-/

namespace GaloisForLFunctions.HTGeometry.HallSolvable

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- Conjugation by `g`, viewed as an endomorphism of a normal subgroup. -/
def conjOn (N : Subgroup G) [hN : N.Normal] (g : G) : ↥N →* ↥N where
  toFun n := ⟨g * (n : G) * g⁻¹, hN.conj_mem _ n.2 g⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

@[simp] theorem coe_conjOn (N : Subgroup G) [N.Normal] (g : G) (n : ↥N) :
    ((conjOn N g n : ↥N) : G) = g * (n : G) * g⁻¹ := rfl

/-- For a complement `K` of a normal subgroup `N`, every `g : G` has a unique `n ∈ N`
with `n * g ∈ K`. -/
theorem existsUnique_mem_mul_mem {N K : Subgroup G} (hK : N.IsComplement' K) (g : G) :
    ∃! n : ↥N, ((n : G) * g) ∈ K := by
  obtain ⟨⟨n₀, k₀⟩, h₀, huniq⟩ := hK.existsUnique g
  simp only at h₀
  refine ⟨⟨(n₀ : G)⁻¹, N.inv_mem n₀.2⟩, ?_, ?_⟩
  · show ((n₀ : G)⁻¹ * g) ∈ K
    have hgk : (n₀ : G)⁻¹ * g = (k₀ : G) := by rw [← h₀]; group
    rw [hgk]; exact k₀.2
  · rintro ⟨n, hn⟩ hmem
    have hmem' : n * g ∈ K := hmem
    have hpair := huniq (⟨n⁻¹, N.inv_mem hn⟩, ⟨n * g, hmem'⟩) (by simp)
    have h1 : n⁻¹ = (n₀ : G) := congrArg (fun p => ((p.1 : G))) hpair
    refine Subtype.ext ?_
    show n = (n₀ : G)⁻¹
    rw [← h1, inv_inv]

/-- **Conjugacy of complements to an abelian normal subgroup of coprime index.**
If `N` is normal and abelian and `H`, `K` are complements of `N` whose common order is coprime to
`Nat.card N`, then `K` is a conjugate of `H` by an element of `N`. -/
theorem exists_conj_eq_of_isComplement' [Finite G] {N : Subgroup G} [N.Normal]
    [IsMulCommutative ↥N] {H K : Subgroup G} (hH : N.IsComplement' H) (hK : N.IsComplement' K)
    (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥H)) :
    ∃ u : G, u ∈ N ∧ K = H.map (MulAut.conj u).toMonoidHom := by
  classical
  letI : Fintype ↥H := Fintype.ofFinite _
  set m : ℕ := Nat.card ↥H with hm
  -- the cocycle
  have hex : ∀ g : G, ∃ n : ↥N, ((n : G) * g) ∈ K := fun g =>
    ⟨(existsUnique_mem_mul_mem hK g).choose, (existsUnique_mem_mul_mem hK g).choose_spec.1⟩
  choose γ hγ using hex
  have huniq : ∀ (g : G) (n : ↥N), ((n : G) * g) ∈ K → n = γ g := fun g n hn =>
    (existsUnique_mem_mul_mem hK g).unique hn (hγ g)
  have hcocycle : ∀ g₁ g₂ : G, γ (g₁ * g₂) = γ g₁ * conjOn N g₁ (γ g₂) := by
    intro g₁ g₂
    refine (huniq _ _ ?_).symm
    have hrw : ((γ g₁ * conjOn N g₁ (γ g₂) : ↥N) : G) * (g₁ * g₂)
        = ((γ g₁ : G) * g₁) * ((γ g₂ : G) * g₂) := by
      simp only [Subgroup.coe_mul, coe_conjOn]
      group
    rw [hrw]
    exact K.mul_mem (hγ g₁) (hγ g₂)
  -- averaging
  set a : ↥N := ∏ h : ↥H, γ (h : G) with ha
  have haverage : ∀ h ∈ H, a = (γ h) ^ m * conjOn N h a := by
    intro h hh
    have hreindex : (∏ h₂ : ↥H, γ (h * (h₂ : G))) = a := by
      rw [ha]
      exact Fintype.prod_equiv (Equiv.mulLeft (⟨h, hh⟩ : ↥H))
        (fun h₂ : ↥H => γ (h * (h₂ : G))) (fun h₂ : ↥H => γ (h₂ : G)) (fun _ => rfl)
    calc a = ∏ h₂ : ↥H, γ (h * (h₂ : G)) := hreindex.symm
      _ = ∏ h₂ : ↥H, (γ h * conjOn N h (γ (h₂ : G))) :=
          Finset.prod_congr rfl fun h₂ _ => hcocycle h (h₂ : G)
      _ = (γ h) ^ m * conjOn N h a := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ha, map_prod, hm,
            Nat.card_eq_fintype_card]
  -- solve the coboundary equation
  obtain ⟨u, hu⟩ : ∃ u : ↥N, u ^ m = a⁻¹ :=
    ⟨(powCoprime hcop).symm a⁻¹, by
      simpa [powCoprime_apply] using (powCoprime hcop).apply_symm_apply a⁻¹⟩
  have hinj : Function.Injective (fun x : ↥N => x ^ m) := by
    intro x y hxy
    refine (powCoprime hcop).injective ?_
    rw [powCoprime_apply, powCoprime_apply]
    exact hxy
  have hkey : ∀ h ∈ H, γ h = u⁻¹ * conjOn N h u := by
    intro h hh
    refine hinj ?_
    show (γ h) ^ m = (u⁻¹ * conjOn N h u) ^ m
    have h1 : (γ h) ^ m = a * (conjOn N h a)⁻¹ := eq_mul_inv_of_mul_eq (haverage h hh).symm
    have h2 : (u⁻¹ * conjOn N h u) ^ m = (u ^ m)⁻¹ * conjOn N h (u ^ m) := by
      rw [mul_pow, ← inv_pow, map_pow]
    rw [h1, h2, hu, map_inv, inv_inv]
  -- conclude
  set v : G := ((u : G))⁻¹ with hv
  have hvN : v ∈ N := N.inv_mem u.2
  have hsub : H.map (MulAut.conj v).toMonoidHom ≤ K := by
    rintro x ⟨h, hh, rfl⟩
    have hconj : (MulAut.conj v).toMonoidHom h = v * h * v⁻¹ := rfl
    have h1 : ((γ h : ↥N) : G) * h = (MulAut.conj v).toMonoidHom h := by
      rw [hconj, hkey h hh, hv]
      simp only [Subgroup.coe_mul, coe_conjOn, Subgroup.coe_inv]
      group
    rw [← h1]
    exact hγ h
  have hcardHK : Nat.card ↥K = Nat.card ↥H := by
    have hNpos : 0 < Nat.card ↥N := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_left hNpos (hH.card_mul.trans hK.card_mul.symm)).symm
  have hcardMap : Nat.card ↥(H.map (MulAut.conj v).toMonoidHom) = Nat.card ↥H :=
    Subgroup.card_map_of_injective (f := (MulAut.conj v).toMonoidHom) (MulAut.conj v).injective
  exact ⟨v, hvN, (Subgroup.eq_of_le_of_card_ge hsub (by rw [hcardMap, hcardHK])).symm⟩

end GaloisForLFunctions.HTGeometry.HallSolvable
