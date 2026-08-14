import GaloisForLFunctions.HTGeometry.HurwitzTriangleCoverTower

/-!
# Monodromy data of unramified covers of the modular orbifold

The modular orbifold is the `(2,3,∞)` sphere orbifold: two elliptic points of orders `2` and `3`
and one cusp.  An unramified degree-`D` cover of it is a transitive pair of permutations `X`, `Y`
of the sheets with `X` a fixed-point-free involution and `Y` fixed-point-free of order three; the
third monodromy `X · Y` is unconstrained, and its cycles are the cusps, with cycle lengths the
cusp widths.

The Euler characteristic of the covering surface, computed from the lifted triangulation, gives
the exact modular storage law

```text
D = 6 (2g + s − 2),
```

with `s` the number of cusps.  Its integrality again comes from the orientation constraint
`sign X · sign Y = sign (X·Y)`.

Every `(2,3,c)` cover is in particular a modular cover, so the tower of `(2,3,7)` covers supplies
modular covers of unbounded degree.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv Equiv.Perm Finset

/-- Monodromy data of an unramified cover of the modular `(2,3,∞)` orbifold. -/
structure ModularCover (S : Type*) [Fintype S] [DecidableEq S] where
  /-- monodromy of the order-two elliptic point -/
  X : Perm S
  /-- monodromy of the order-three elliptic point -/
  Y : Perm S
  freeX : IsFreeOfOrder X 2
  freeY : IsFreeOfOrder Y 3
  /-- the cover is connected -/
  transitive : ∀ s t : S, ∃ g ∈ Subgroup.closure ({X, Y} : Set (Perm S)), g s = t

namespace ModularCover

variable {S : Type*} [Fintype S] [DecidableEq S] (M : ModularCover S)

/-- The degree of the cover. -/
def degree (_ : ModularCover S) : ℕ := Fintype.card S

/-- The number of points over the order-two elliptic point. -/
def fibreX : ℕ := M.X.cycleType.card

/-- The number of points over the order-three elliptic point. -/
def fibreY : ℕ := M.Y.cycleType.card

/-- The number of cusps: the cycles of `X · Y`, fixed points included. -/
def cuspCount : ℕ :=
  (Fintype.card S - (M.X * M.Y).support.card) + (M.X * M.Y).cycleType.card

theorem two_mul_fibreX : 2 * M.fibreX = M.degree :=
  (M.freeX.card_eq_mul_cycleType_card (by norm_num)).symm

theorem three_mul_fibreY : 3 * M.fibreY = M.degree :=
  (M.freeY.card_eq_mul_cycleType_card (by norm_num)).symm

/-- The Euler characteristic of the covering surface, from the lifted triangulation. -/
def eulerChar : ℤ := (M.fibreX : ℤ) + (M.fibreY : ℤ) + (M.cuspCount : ℤ) - (M.degree : ℤ)

/-- **Orientability.**  The Euler characteristic of a modular cover is even. -/
theorem even_eulerChar : Even M.eulerChar := by
  have h2 : 2 * M.fibreX = M.degree := M.two_mul_fibreX
  have h3 : 3 * M.fibreY = M.degree := M.three_mul_fibreY
  have hne3 : ¬ Even 3 := by decide
  have hDeven : Even M.degree := ⟨M.fibreX, by omega⟩
  -- signs
  have hY : Equiv.Perm.sign M.Y = 1 :=
    MonodromyCover.sign_eq_one_of_odd M.freeY (by norm_num) ⟨1, by norm_num⟩
  have hXZ : Equiv.Perm.sign M.X = Equiv.Perm.sign (M.X * M.Y) := by
    have hmul : Equiv.Perm.sign M.X * Equiv.Perm.sign M.Y = Equiv.Perm.sign (M.X * M.Y) :=
      (map_mul Equiv.Perm.sign M.X M.Y).symm
    rw [hY, mul_one] at hmul
    exact hmul
  rw [M.freeX.sign_eq (by norm_num), Equiv.Perm.sign_of_cycleType,
    Equiv.Perm.sum_cycleType] at hXZ
  have hiff : Even ((2 + 1) * M.fibreX)
      ↔ Even ((M.X * M.Y).support.card + (M.X * M.Y).cycleType.card) :=
    units_neg_one_pow_eq_iff.mp hXZ
  have hleft : Even ((2 + 1) * M.fibreX) ↔ Even M.fibreX := by
    rw [show (2 + 1) * M.fibreX = 3 * M.fibreX from rfl, Nat.even_mul]
    exact ⟨fun h => h.resolve_left hne3, fun h => Or.inr h⟩
  -- cusp parity
  have hsupp : (M.X * M.Y).support.card ≤ Fintype.card S := by
    simpa using Finset.card_le_univ (M.X * M.Y).support
  have hcusp : M.cuspCount + (M.X * M.Y).support.card
      = Fintype.card S + (M.X * M.Y).cycleType.card := by
    simp only [cuspCount]
    omega
  have hDcard : M.degree = Fintype.card S := rfl
  have hcuspPar : Even M.cuspCount ↔ Even M.fibreX := by
    have hcomb : Even ((M.X * M.Y).support.card + (M.X * M.Y).cycleType.card) ↔ Even M.fibreX :=
      hiff.symm.trans hleft
    rw [Nat.even_iff] at hDeven
    rw [Nat.even_iff, Nat.even_iff] at hcomb
    rw [Nat.even_iff, Nat.even_iff]
    rw [hDcard] at hDeven
    omega
  -- assemble
  obtain ⟨jy, hjy⟩ : Even M.fibreY := by
    obtain ⟨j, hj⟩ := hDeven
    have h3f : Even (3 * M.fibreY) := ⟨j, by omega⟩
    exact (Nat.even_mul.mp h3f).resolve_left hne3
  rcases Nat.even_or_odd M.fibreX with hu | hu
  · obtain ⟨ju, hju⟩ := hu
    obtain ⟨js, hjs⟩ := hcuspPar.mpr ⟨ju, hju⟩
    refine ⟨(jy : ℤ) + js - ju, ?_⟩
    have h1 : (M.fibreX : ℤ) = ju + ju := by exact_mod_cast hju
    have h2' : (M.fibreY : ℤ) = jy + jy := by exact_mod_cast hjy
    have h3' : (M.cuspCount : ℤ) = js + js := by exact_mod_cast hjs
    have h4 : (2 : ℤ) * M.fibreX = M.degree := by exact_mod_cast h2
    simp only [eulerChar]
    linarith
  · obtain ⟨ju, hju⟩ := hu
    have hsodd : Odd M.cuspCount := by
      rcases Nat.even_or_odd M.cuspCount with hs | hs
      · exact absurd (hcuspPar.mp hs) (by simpa [Nat.not_even_iff_odd] using ⟨ju, hju⟩)
      · exact hs
    obtain ⟨js, hjs⟩ := hsodd
    refine ⟨(jy : ℤ) + js - ju, ?_⟩
    have h1 : (M.fibreX : ℤ) = 2 * ju + 1 := by exact_mod_cast hju
    have h2' : (M.fibreY : ℤ) = jy + jy := by exact_mod_cast hjy
    have h3' : (M.cuspCount : ℤ) = 2 * js + 1 := by exact_mod_cast hjs
    have h4 : (2 : ℤ) * M.fibreX = M.degree := by exact_mod_cast h2
    simp only [eulerChar]
    linarith

/-- **Exact modular storage.**  A connected unramified cover of the modular orbifold has integral
genus `g` and degree exactly `6(2g + s − 2)`, where `s` is its number of cusps. -/
theorem modular_capacity_exact :
    ∃ g : ℤ, M.eulerChar = 2 - 2 * g ∧
      (M.degree : ℤ) = 6 * (2 * g + (M.cuspCount : ℤ) - 2) := by
  obtain ⟨k, hk⟩ := M.even_eulerChar
  refine ⟨1 - k, by omega, ?_⟩
  have h2 : (2 : ℤ) * M.fibreX = M.degree := by exact_mod_cast M.two_mul_fibreX
  have h3 : (3 : ℤ) * M.fibreY = M.degree := by exact_mod_cast M.three_mul_fibreY
  simp only [eulerChar] at hk
  linarith

end ModularCover

/-- Every `(2,3,c)` cover is in particular an unramified cover of the modular orbifold. -/
def MonodromyCover.toModularCover {c : ℕ} {S : Type*} [Fintype S] [DecidableEq S]
    (F : MonodromyCover 2 3 c S) : ModularCover S where
  X := F.X
  Y := F.Y
  freeX := F.freeX
  freeY := F.freeY
  transitive := F.transitive

@[simp] theorem MonodromyCover.toModularCover_degree {c : ℕ} {S : Type*} [Fintype S]
    [DecidableEq S] (F : MonodromyCover 2 3 c S) :
    (F.toModularCover).degree = F.degree := rfl

end GaloisForLFunctions.HTGeometry
