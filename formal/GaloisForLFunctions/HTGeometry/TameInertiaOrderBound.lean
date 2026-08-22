import GaloisForLFunctions.HTGeometry.TameInertiaCyclic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# A fixed element bounds the order of a tame group

`TameInertiaCyclic` turns a tame action on a discrete valuation ring into an injective character
`residueRatioHom : Γ →* ResidueField W`.  This module reads that character against an element the
group fixes.

If `x = π ^ n * u` is fixed and `u` is a unit, then applying `g` gives
`π ^ n * u = π ^ n * ratioElt π g ^ n * (g • u)`, and cancelling `π ^ n` and passing to residues —
where `g • u` and `u` agree, the action being trivial there — leaves
`residueRatioHom g ^ n = 1`.  So the character lands in the `n`-th roots of unity, of which a field
has at most `n`, and faithfulness turns that into a bound on the group:

```text
residueRatioHom_pow_eq_one_of_smul_eq   the character is an `n`-th root of unity
natCard_le_of_smul_eq_of_eq_pow_mul     ** |Γ| ≤ n **
natCard_le_addVal_of_smul_eq            ** |Γ| ≤ addVal W x, for any fixed nonzero nonunit x **
```

This is the cheap half of the fundamental identity `|I| = e`: applied to the image of a uniformizer
of a subfield fixed by `Γ`, it bounds the inertia group of that subfield by the ramification index
over it.  The other half — surjectivity of the character — is the ideal-theoretic input and is not
proved here.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
variable {Γ : Type*} [Group Γ] [MulSemiringAction Γ W]

omit [IsDomain W] [IsDiscreteValuationRing W] in
theorem smul_pow_eq {g : Γ} (x : W) (n : ℕ) : g • x ^ n = (g • x) ^ n :=
  map_pow (MulSemiringAction.toRingHom Γ W g) x n

/-- A fixed element of divisorial order `n` forces the tame ratio character into `n`-th roots of
unity. -/
theorem residueRatioHom_pow_eq_one_of_smul_eq
    {π : W} (hπ : Irreducible π)
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W)
    {x u : W} {n : ℕ} (hu : IsUnit u) (hx : x = π ^ n * u)
    (hfix : ∀ g : Γ, g • x = x) (g : Γ) :
    (residueRatioHom hπ hres g) ^ n = 1 := by
  have hπ0 : (π : W) ^ n ≠ 0 := pow_ne_zero _ hπ.ne_zero
  have hxx : π ^ n * u = π ^ n * ((ratioElt π g) ^ n * (g • u)) := by
    calc π ^ n * u = x := hx.symm
      _ = g • x := (hfix g).symm
      _ = g • (π ^ n * u) := by rw [hx]
      _ = (g • π ^ n) * (g • u) := by rw [smul_mul']
      _ = ((g • π) ^ n) * (g • u) := by rw [smul_pow_eq]
      _ = (π * ratioElt π g) ^ n * (g • u) := by rw [smul_eq_mul_ratioElt]
      _ = π ^ n * ((ratioElt π g) ^ n * (g • u)) := by rw [mul_pow]; ring
  have hcancel : u = (ratioElt π g) ^ n * (g • u) := mul_left_cancel₀ hπ0 hxx
  have hres' := congrArg (IsLocalRing.residue W) hcancel
  rw [map_mul, map_pow, residue_smul_eq hres] at hres'
  have hne : IsLocalRing.residue W u ≠ 0 := (hu.map _).ne_zero
  have hfin : (IsLocalRing.residue W (ratioElt π g)) ^ n * IsLocalRing.residue W u
      = 1 * IsLocalRing.residue W u := by rw [one_mul]; exact hres'.symm
  rw [residueRatioHom_apply]
  exact mul_right_cancel₀ hne hfin

/-- **A fixed element of order `n` bounds a tame group by `n`.** -/
theorem natCard_le_of_smul_eq_of_eq_pow_mul
    [CharZero (IsLocalRing.ResidueField W)] [Finite Γ] [FaithfulSMul Γ W]
    {π : W} (hπ : Irreducible π)
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W)
    {x u : W} {n : ℕ} (hn : 0 < n) (hu : IsUnit u) (hx : x = π ^ n * u)
    (hfix : ∀ g : Γ, g • x = x) :
    Nat.card Γ ≤ n := by
  classical
  have hinj := residueRatioHom_injective (Γ := Γ) hπ hres
  have hmem : ∀ g : Γ, residueRatioHom hπ hres g ∈
      (Polynomial.nthRoots n (1 : IsLocalRing.ResidueField W)).toFinset := by
    intro g
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact residueRatioHom_pow_eq_one_of_smul_eq hπ hres hu hx hfix g
  have hcard : Nat.card Γ ≤
      Nat.card {y // y ∈ (Polynomial.nthRoots n (1 : IsLocalRing.ResidueField W)).toFinset} :=
    Nat.card_le_card_of_injective
      (fun g : Γ => (⟨residueRatioHom hπ hres g, hmem g⟩ :
        {y // y ∈ (Polynomial.nthRoots n (1 : IsLocalRing.ResidueField W)).toFinset}))
      (fun a b hab => hinj (congrArg Subtype.val hab))
  rw [Nat.card_eq_finsetCard] at hcard
  refine hcard.trans (le_trans (Multiset.toFinset_card_le _) ?_)
  exact Polynomial.card_nthRoots n 1

/-- **The divisorial order of a fixed element bounds a tame group.**  If a finite group acts
faithfully on a discrete valuation ring by ring automorphisms, trivially on a residue field of
characteristic zero, then every fixed nonzero nonunit has divisorial order at least the order of
the group. -/
theorem natCard_le_addVal_of_smul_eq
    [CharZero (IsLocalRing.ResidueField W)] [Finite Γ] [FaithfulSMul Γ W]
    {π : W} (hπ : Irreducible π)
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W)
    {x : W} (hx0 : x ≠ 0) (hxnu : ¬ IsUnit x) (hfix : ∀ g : Γ, g • x = x) :
    (Nat.card Γ : ℕ∞) ≤ addVal W x := by
  obtain ⟨n, u, hnu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hval : addVal W x = n := addVal_def x u hπ n hnu
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exact absurd (by rw [hnu, h, pow_zero, mul_one]; exact u.isUnit) hxnu
    · exact h
  have hle := natCard_le_of_smul_eq_of_eq_pow_mul hπ hres hn u.isUnit
    (show x = π ^ n * (u : W) by rw [hnu]; ring) hfix
  rw [hval]
  exact_mod_cast hle

end GaloisForLFunctions.HTGeometry
