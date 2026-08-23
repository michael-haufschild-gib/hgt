import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Tame rigidity: automorphisms of a discrete valuation ring in residue characteristic zero

`Mathlib/RingTheory/Valuation/RamificationGroup.lean` defines the decomposition and inertia
subgroups but leaves the higher ramification filtration as a `TODO`, so the classical consequence
"tame inertia is cyclic" is unavailable.  The two theorems below supply its whole content, and by
an argument that never mentions the filtration.

Let a group act on a discrete valuation ring `W` by ring automorphisms, trivially on the residue
field, and let the residue field have characteristic zero.  For an element `g` of finite order `N`
and a uniformizer `π`, write `gπ − π = u π^k` with `u` a unit.  Every power of `g` moves `π` by an
element divisible by `π ^ 2` as soon as `g` does, so

```text
g^j (u π^k) = (g^j u) (g^j π)^k ≡ u π^k         (mod π^{k+1})
g^N π − π   = Σ_{j<N} g^j (g π − π) ≡ N u π^k   (mod π^{k+1})
```

and `g^N = 1` forces `π ∣ N`, impossible in residue characteristic zero.  Hence:

```text
smul_uniformizer_eq_self_of_sq_dvd
    ** π² ∣ gπ − π  ⟹  gπ = π **                (no wild inertia)
smul_eq_self_of_smul_uniformizer_eq_self
    ** gπ = π  ⟹  g acts as the identity **     (tame rigidity)
```

Together they say that the ratio `gπ / π` read in the residue field detects `g` completely: the
inertia group embeds into the units of the residue field.  Every step is a divisibility, so no
valuation sums, no quotient groups and no completeness are used.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDiscreteValuationRing

variable {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
variable {Γ : Type*} [Group Γ] [MulSemiringAction Γ W]

/-- A ring automorphism of a discrete valuation ring preserves its additive valuation. -/
theorem addVal_ringEquiv (e : W ≃+* W) (x : W) : addVal W (e x) = addVal W x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible W
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have heϖ : Irreducible (e ϖ) := hϖ.map e
  have heu : IsUnit (e (u : W)) := u.isUnit.map e
  obtain ⟨u', hu'⟩ := heu
  rw [map_mul, map_pow, addVal_def' u hϖ n, ← hu', addVal_def' u' heϖ n]

/-- A ring automorphism preserves the additive valuation. -/
theorem addVal_smul (g : Γ) (x : W) : addVal W (g • x) = addVal W x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible W
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have hgϖ : Irreducible (g • ϖ) := hϖ.map (MulSemiringAction.toRingEquiv Γ W g)
  have hgu : IsUnit (g • (u : W)) := u.isUnit.map (MulSemiringAction.toRingEquiv Γ W g)
  obtain ⟨u', hu'⟩ := hgu
  rw [smul_mul', smul_pow', addVal_def' u hϖ n, ← hu', addVal_def' u' hgϖ n]

/-- In a discrete valuation ring a uniformizer divides every element of the maximal ideal. -/
theorem dvd_of_mem_maximalIdeal {π x : W} (hπ : Irreducible π) (hx : x ∈ IsLocalRing.maximalIdeal W) :
    π ∣ x := by
  refine addVal_le_iff_dvd.mp ?_
  rw [addVal_uniformizer hπ]
  refine Order.one_le_iff_ne_zero.mpr ?_
  rw [Ne, addVal_eq_zero_iff]
  exact fun h => (IsLocalRing.notMem_maximalIdeal.mpr h) hx

/-- Every element divides its image under an automorphism, up to associates. -/
theorem dvd_smul_self (x : W) (g : Γ) : x ∣ g • x := by
  refine addVal_le_iff_dvd.mp ?_
  rw [addVal_smul]

/-- If an automorphism moves a uniformizer only to second order, so does each of its powers. -/
theorem sq_dvd_smul_pow_sub {π : W} {g : Γ} (h2 : π ^ 2 ∣ g • π - π) (j : ℕ) :
    π ^ 2 ∣ g ^ j • π - π := by
  induction j with
  | zero => simp
  | succ j ih =>
      have hstep : g ^ (j + 1) • π - π = g • (g ^ j • π - π) + (g • π - π) := by
        rw [smul_sub, smul_smul, ← pow_succ']
        ring
      rw [hstep]
      refine dvd_add ?_ h2
      obtain ⟨c, hc⟩ := ih
      have hdvd : (g • π) ^ 2 ∣ g • (g ^ j • π - π) :=
        ⟨g • c, by rw [hc, smul_mul', smul_pow']⟩
      exact dvd_trans (pow_dvd_pow_of_dvd (dvd_smul_self π g) 2) hdvd

/-- **Tameness in residue characteristic zero.**  A finite-order ring automorphism that acts
trivially on the residue field and moves a uniformizer only to second order fixes it. -/
theorem smul_uniformizer_eq_self_of_sq_dvd [CharZero (IsLocalRing.ResidueField W)]
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W)
    {g : Γ} {N : ℕ} (hN : 0 < N) (hgN : g ^ N = 1)
    {π : W} (hπ : Irreducible π) (h2 : π ^ 2 ∣ g • π - π) :
    g • π = π := by
  classical
  by_contra hne
  have hd : g • π - π ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨k, u, hu⟩ := eq_unit_mul_pow_irreducible hd hπ
  have hk2 : 2 ≤ k := by
    have hle : addVal W ((π : W) ^ 2) ≤ addVal W (g • π - π) := addVal_le_iff_dvd.mpr h2
    rw [hu, addVal_def' u hπ k, hπ.addVal_pow 2] at hle
    exact_mod_cast hle
  have hpow : ∀ j : ℕ, π ^ (k + 1) ∣ g ^ j • (g • π - π) - (g • π - π) := by
    intro j
    have hεdvd : π ^ 2 ∣ g ^ j • π - π := sq_dvd_smul_pow_sub h2 j
    have hπdvd : π ∣ g ^ j • π := dvd_smul_self π (g ^ j)
    have hgeom : π ^ (k + 1) ∣ (g ^ j • π) ^ k - π ^ k := by
      have hfac := geom_sum₂_mul (g ^ j • π) π k
      have hsum : π ^ (k - 1) ∣ ∑ i ∈ Finset.range k, (g ^ j • π) ^ i * π ^ (k - 1 - i) := by
        refine Finset.dvd_sum fun i hi => ?_
        have hik : i ≤ k - 1 := by
          have := Finset.mem_range.mp hi
          omega
        have h1 : (π : W) ^ i ∣ (g ^ j • π) ^ i := pow_dvd_pow_of_dvd hπdvd i
        have h2' : (π : W) ^ (k - 1) = π ^ i * π ^ (k - 1 - i) := by
          rw [← pow_add]
          congr 1
          omega
        rw [h2']
        exact mul_dvd_mul h1 dvd_rfl
      have hmul := mul_dvd_mul hsum hεdvd
      rw [hfac, ← pow_add] at hmul
      have hkk : k - 1 + 2 = k + 1 := by omega
      rwa [hkk] at hmul
    have hunit : π ∣ g ^ j • (u : W) - (u : W) := dvd_of_mem_maximalIdeal hπ (hres _ _)
    have hexp : g ^ j • (g • π - π) = (g ^ j • (u : W)) * (g ^ j • π) ^ k := by
      rw [hu, smul_mul', smul_pow']
    rw [hexp, hu]
    obtain ⟨a, ha⟩ := hunit
    obtain ⟨b, hb⟩ := hgeom
    have hrewrite : (g ^ j • (u : W)) * (g ^ j • π) ^ k - (u : W) * π ^ k
        = (u : W) * ((g ^ j • π) ^ k - π ^ k)
          + (g ^ j • (u : W) - (u : W)) * ((g ^ j • π) ^ k - π ^ k)
          + (g ^ j • (u : W) - (u : W)) * π ^ k := by ring
    rw [hrewrite, hb, ha]
    exact dvd_add (dvd_add ⟨(u : W) * b, by ring⟩ ⟨π * a * b, by ring⟩) ⟨a, by ring⟩
  have htel : ∀ n : ℕ, ∑ j ∈ Finset.range n, g ^ j • (g • π - π) = g ^ n • π - π := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        have hshift : g ^ n • (g • π - π) = g ^ (n + 1) • π - g ^ n • π := by
          rw [smul_sub, smul_smul, ← pow_succ]
        rw [hshift]
        ring
  have hzero : ∑ j ∈ Finset.range N, g ^ j • (g • π - π) = 0 := by
    rw [htel N, hgN, one_smul, sub_self]
  have hsplit : ∑ j ∈ Finset.range N, (g ^ j • (g • π - π) - (g • π - π))
      = (∑ j ∈ Finset.range N, g ^ j • (g • π - π)) - (N : W) * (g • π - π) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hdvdsum : π ^ (k + 1) ∣ ∑ j ∈ Finset.range N, (g ^ j • (g • π - π) - (g • π - π)) :=
    Finset.dvd_sum fun j _ => hpow j
  have hNd : π ^ (k + 1) ∣ (N : W) * (g • π - π) := by
    have hEq : (N : W) * (g • π - π)
        = -∑ j ∈ Finset.range N, (g ^ j • (g • π - π) - (g • π - π)) := by
      rw [hsplit, hzero]
      ring
    rw [hEq]
    exact dvd_neg.mpr hdvdsum
  rw [hu] at hNd
  have hcancel : π ∣ (N : W) * (u : W) := by
    obtain ⟨c, hc⟩ := hNd
    refine ⟨c, ?_⟩
    have hπk : (π : W) ^ k ≠ 0 := pow_ne_zero _ hπ.ne_zero
    apply mul_left_cancel₀ hπk
    rw [show (π : W) ^ k * ((N : W) * (u : W)) = (N : W) * ((u : W) * π ^ k) by ring, hc]
    ring
  have hNunit : ¬ IsUnit ((N : W) * (u : W)) := fun h =>
    hπ.not_isUnit (isUnit_of_dvd_unit hcancel h)
  have hNmem : (N : W) ∈ IsLocalRing.maximalIdeal W := by
    by_contra h
    exact hNunit ((IsLocalRing.notMem_maximalIdeal.mp h).mul u.isUnit)
  have hres0 : ((N : ℕ) : IsLocalRing.ResidueField W) = 0 := by
    rw [← map_natCast (IsLocalRing.residue W) N]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hNmem
  exact absurd hres0 (Nat.cast_ne_zero.mpr hN.ne')

/-- **Tame rigidity.**  A finite-order ring automorphism acting trivially on the residue field and
fixing one uniformizer is the identity, when the residue field has characteristic zero. -/
theorem smul_eq_self_of_smul_uniformizer_eq_self [CharZero (IsLocalRing.ResidueField W)]
    (hres : ∀ (h : Γ) (x : W), h • x - x ∈ IsLocalRing.maximalIdeal W)
    {g : Γ} {N : ℕ} (hN : 0 < N) (hgN : g ^ N = 1)
    {π : W} (hπ : Irreducible π) (hfix : g • π = π) (x : W) :
    g • x = x := by
  classical
  by_contra hne
  have hd : g • x - x ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨k, u, hu⟩ := eq_unit_mul_pow_irreducible hd hπ
  have hfixp : ∀ j : ℕ, g ^ j • π = π := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← smul_smul, hfix, ih]
  have hpow : ∀ j : ℕ, π ^ (k + 1) ∣ g ^ j • (g • x - x) - (g • x - x) := by
    intro j
    have hexp : g ^ j • (g • x - x) = (g ^ j • (u : W)) * π ^ k := by
      rw [hu, smul_mul', smul_pow', hfixp]
    rw [hexp, hu]
    obtain ⟨a, ha⟩ := dvd_of_mem_maximalIdeal hπ (hres (g ^ j) (u : W))
    refine ⟨a, ?_⟩
    rw [show (g ^ j • (u : W)) * π ^ k - (u : W) * π ^ k
        = (g ^ j • (u : W) - (u : W)) * π ^ k by ring, ha]
    ring
  have htel : ∀ n : ℕ, ∑ j ∈ Finset.range n, g ^ j • (g • x - x) = g ^ n • x - x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        have hshift : g ^ n • (g • x - x) = g ^ (n + 1) • x - g ^ n • x := by
          rw [smul_sub, smul_smul, ← pow_succ]
        rw [hshift]
        ring
  have hzero : ∑ j ∈ Finset.range N, g ^ j • (g • x - x) = 0 := by
    rw [htel N, hgN, one_smul, sub_self]
  have hsplit : ∑ j ∈ Finset.range N, (g ^ j • (g • x - x) - (g • x - x))
      = (∑ j ∈ Finset.range N, g ^ j • (g • x - x)) - (N : W) * (g • x - x) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hNd : π ^ (k + 1) ∣ (N : W) * (g • x - x) := by
    have hEq : (N : W) * (g • x - x)
        = -∑ j ∈ Finset.range N, (g ^ j • (g • x - x) - (g • x - x)) := by
      rw [hsplit, hzero]
      ring
    rw [hEq]
    exact dvd_neg.mpr (Finset.dvd_sum fun j _ => hpow j)
  rw [hu] at hNd
  have hcancel : π ∣ (N : W) * (u : W) := by
    obtain ⟨c, hc⟩ := hNd
    refine ⟨c, ?_⟩
    have hπk : (π : W) ^ k ≠ 0 := pow_ne_zero _ hπ.ne_zero
    apply mul_left_cancel₀ hπk
    rw [show (π : W) ^ k * ((N : W) * (u : W)) = (N : W) * ((u : W) * π ^ k) by ring, hc]
    ring
  have hNunit : ¬ IsUnit ((N : W) * (u : W)) := fun h =>
    hπ.not_isUnit (isUnit_of_dvd_unit hcancel h)
  have hNmem : (N : W) ∈ IsLocalRing.maximalIdeal W := by
    by_contra h
    exact hNunit ((IsLocalRing.notMem_maximalIdeal.mp h).mul u.isUnit)
  have hres0 : ((N : ℕ) : IsLocalRing.ResidueField W) = 0 := by
    rw [← map_natCast (IsLocalRing.residue W) N]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hNmem
  exact absurd hres0 (Nat.cast_ne_zero.mpr hN.ne')

end GaloisForLFunctions.HTGeometry
