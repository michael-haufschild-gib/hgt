import GaloisForLFunctions.HTGeometry.FreeCyclicOrbits

/-!
# Monodromy data of an unramified cover of a triangle orbifold

A degree-`D` covering of the sphere orbifold with three marked points of orders `a`, `b`, `c`
which is unramified away from the marked fibres is the same thing as a transitive pair of
permutations `X`, `Y` of the `D` sheets with `X ^ a = Y ^ b = (X * Y) ^ c = 1` and with every
nontrivial power of `X`, `Y`, `X * Y` fixed-point-free.  The three fibres over the marked points
are the orbit sets of `X`, `Y` and `X * Y`.

This file records that dictionary and the two exact storage laws it produces.

* `MonodromyCover.a_mul_fibreX` and companions — the fibre counts `a·f_a = b·f_b = c·f_c = D`.
* `MonodromyCover.eulerChar` — the Euler characteristic of the covering surface, computed from
  the lifted triangulation of the base sphere (`V = 3`, `E = 3`, `F = 2`): the marked fibres
  contribute `f_a + f_b + f_c` vertices, each base edge lifts to `D` edges and each base face to
  `D` faces.
* `MonodromyCover.hurwitz_capacity_exact` — for signature `(2,3,7)`: `D = 42 (2g − 2)`, the
  saturation of the Hurwitz threshold, with an integral genus `g`.  Integrality is not free: it
  comes from the orientation (sign) constraint `sign X · sign Y = sign (X·Y)`, which forces
  `84 ∣ D`.
* `MonodromyCover.modular_capacity_exact` — for signature `(2,3,n)`: `D = 6 (2g + s − 2)` with
  `s = f_n` the number of cusps, the exact modular saturation.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv Equiv.Perm Finset

/-- Monodromy data of an unramified degree-`card S` cover of the `(a,b,c)` sphere orbifold. -/
structure MonodromyCover (a b c : ℕ) (S : Type*) [Fintype S] [DecidableEq S] where
  /-- monodromy of a small loop around the first marked point -/
  X : Perm S
  /-- monodromy of a small loop around the second marked point -/
  Y : Perm S
  freeX : IsFreeOfOrder X a
  freeY : IsFreeOfOrder Y b
  freeZ : IsFreeOfOrder (X * Y) c
  /-- the cover is connected -/
  transitive : ∀ s t : S, ∃ g ∈ Subgroup.closure ({X, Y} : Set (Perm S)), g s = t

namespace MonodromyCover

variable {a b c : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

/-- The degree of the cover. -/
def degree (_ : MonodromyCover a b c S) : ℕ := Fintype.card S

/-- Number of points in the fibre over the first marked point. -/
def fibreX (F : MonodromyCover a b c S) : ℕ := F.X.cycleType.card

/-- Number of points in the fibre over the second marked point. -/
def fibreY (F : MonodromyCover a b c S) : ℕ := F.Y.cycleType.card

/-- Number of points in the fibre over the third marked point. -/
def fibreZ (F : MonodromyCover a b c S) : ℕ := (F.X * F.Y).cycleType.card

variable (F : MonodromyCover a b c S)

theorem a_mul_fibreX (ha : 2 ≤ a) : a * F.fibreX = F.degree :=
  (F.freeX.card_eq_mul_cycleType_card ha).symm

theorem b_mul_fibreY (hb : 2 ≤ b) : b * F.fibreY = F.degree :=
  (F.freeY.card_eq_mul_cycleType_card hb).symm

theorem c_mul_fibreZ (hc : 2 ≤ c) : c * F.fibreZ = F.degree :=
  (F.freeZ.card_eq_mul_cycleType_card hc).symm

/-- The Euler characteristic of the covering surface, from the lifted triangulation. -/
def eulerChar : ℤ := (F.fibreX : ℤ) + (F.fibreY : ℤ) + (F.fibreZ : ℤ) - (F.degree : ℤ)

theorem sign_X_mul_sign_Y : Equiv.Perm.sign F.X * Equiv.Perm.sign F.Y
    = Equiv.Perm.sign (F.X * F.Y) := (map_mul Equiv.Perm.sign F.X F.Y).symm

end MonodromyCover

/-- `(-1) ^ k = 1` in the units of `ℤ` exactly for even `k`. -/
theorem units_neg_one_pow_eq_one_iff {k : ℕ} : ((-1 : ℤˣ)) ^ k = 1 ↔ Even k :=
  neg_one_pow_eq_one_iff_even (by decide)

/-- Two powers of `-1` agree exactly when the exponents have the same parity. -/
theorem units_neg_one_pow_eq_iff {k m : ℕ} :
    ((-1 : ℤˣ)) ^ k = ((-1 : ℤˣ)) ^ m ↔ (Even k ↔ Even m) := by
  constructor
  · intro h
    constructor
    · intro hk
      refine units_neg_one_pow_eq_one_iff.mp ?_
      rw [← h]
      exact hk.neg_one_pow
    · intro hm
      refine units_neg_one_pow_eq_one_iff.mp ?_
      rw [h]
      exact hm.neg_one_pow
  · intro h
    rcases Nat.even_or_odd k with hk | hk
    · exact hk.neg_one_pow.trans (h.mp hk).neg_one_pow.symm
    · have hm : Odd m := by
        rcases Nat.even_or_odd m with hm | hm
        · exact absurd (h.mpr hm) (by simpa [Nat.not_even_iff_odd] using hk)
        · exact hm
      exact hk.neg_one_pow.trans hm.neg_one_pow.symm

namespace MonodromyCover

variable {a b c : ℕ} {S : Type*} [Fintype S] [DecidableEq S]

/-- The sign of a free permutation of odd order is trivial. -/
theorem sign_eq_one_of_odd {σ : Perm S} {m : ℕ} (h : IsFreeOfOrder σ m) (hm : 2 ≤ m)
    (hodd : Odd m) : Equiv.Perm.sign σ = 1 := by
  rw [h.sign_eq hm]
  refine units_neg_one_pow_eq_one_iff.mpr ?_
  obtain ⟨j, hj⟩ := hodd
  exact ⟨(j + 1) * σ.cycleType.card, by rw [hj]; ring⟩

end MonodromyCover

section Hurwitz

variable {S : Type*} [Fintype S] [DecidableEq S] (F : MonodromyCover 2 3 7 S)

/-- **Orientability.**  In a `(2,3,7)` cover the first fibre count is even: the two odd-order
monodromies have trivial sign, so the involution `X` must be an even permutation, i.e. it has an
even number of two-cycles. -/
theorem MonodromyCover.even_fibreX_237 : Even F.fibreX := by
  have hY : Equiv.Perm.sign F.Y = 1 :=
    MonodromyCover.sign_eq_one_of_odd F.freeY (by norm_num) ⟨1, by norm_num⟩
  have hZ : Equiv.Perm.sign (F.X * F.Y) = 1 :=
    MonodromyCover.sign_eq_one_of_odd F.freeZ (by norm_num) ⟨3, by norm_num⟩
  have hX : Equiv.Perm.sign F.X = 1 := by
    have := F.sign_X_mul_sign_Y
    rw [hY, hZ, mul_one] at this
    exact this
  rw [F.freeX.sign_eq (by norm_num)] at hX
  have h3 : ((-1 : ℤˣ)) ^ ((2 + 1) * F.fibreX) = 1 := hX
  obtain ⟨k, hk⟩ := units_neg_one_pow_eq_one_iff.mp h3
  have h3f : Even (3 * F.fibreX) := ⟨k, by omega⟩
  have hne : ¬ Even 3 := by decide
  exact (Nat.even_mul.mp h3f).resolve_left hne

/-- `84` divides the degree of a `(2,3,7)` cover. -/
theorem MonodromyCover.eightyFour_dvd_degree_237 : 84 ∣ F.degree := by
  obtain ⟨k, hk⟩ := F.even_fibreX_237
  have h2 : 2 * F.fibreX = F.degree := F.a_mul_fibreX (by norm_num)
  have h3 : 3 * F.fibreY = F.degree := F.b_mul_fibreY (by norm_num)
  have h7 : 7 * F.fibreZ = F.degree := F.c_mul_fibreZ (by norm_num)
  have h4 : 4 ∣ F.degree := ⟨k, by omega⟩
  have h3' : (3 : ℕ) ∣ F.degree := ⟨F.fibreY, h3.symm⟩
  have h7' : (7 : ℕ) ∣ F.degree := ⟨F.fibreZ, h7.symm⟩
  omega

/-- **Exact Hurwitz storage.**  A connected unramified `(2,3,7)` cover has integral genus `g` and
degree exactly `42 (2g − 2)`; equivalently its Euler characteristic is `−D/42`. -/
theorem MonodromyCover.hurwitz_capacity_exact :
    ∃ g : ℤ, F.eulerChar = 2 - 2 * g ∧ (F.degree : ℤ) = 42 * (2 * g - 2) := by
  have h2 : 2 * F.fibreX = F.degree := F.a_mul_fibreX (by norm_num)
  have h3 : 3 * F.fibreY = F.degree := F.b_mul_fibreY (by norm_num)
  have h7 : 7 * F.fibreZ = F.degree := F.c_mul_fibreZ (by norm_num)
  obtain ⟨m, hm⟩ := F.eightyFour_dvd_degree_237
  refine ⟨1 + (m : ℤ), ?_, ?_⟩
  · have h2' : (2 : ℤ) * F.fibreX = F.degree := by exact_mod_cast h2
    have h3' : (3 : ℤ) * F.fibreY = F.degree := by exact_mod_cast h3
    have h7' : (7 : ℤ) * F.fibreZ = F.degree := by exact_mod_cast h7
    have hm' : (F.degree : ℤ) = 84 * m := by exact_mod_cast hm
    simp only [MonodromyCover.eulerChar]
    linarith
  · have hm' : (F.degree : ℤ) = 84 * m := by exact_mod_cast hm
    rw [hm']; ring

/-- The fibre-count and Riemann–Hurwitz hypotheses of the projective capacity theorem, produced
by an actual connected `(2,3,7)` cover. -/
theorem MonodromyCover.hurwitz_riemannHurwitz :
    ∃ g : ℤ, (2 : ℤ) * F.fibreX = F.degree ∧ (3 : ℤ) * F.fibreY = F.degree ∧
      (7 : ℤ) * F.fibreZ = F.degree ∧
      2 * g - 2 = -2 * (F.degree : ℤ) + F.fibreX + 2 * F.fibreY + 6 * F.fibreZ := by
  obtain ⟨g, hchi, _⟩ := F.hurwitz_capacity_exact
  have h2' : (2 : ℤ) * F.fibreX = F.degree := by exact_mod_cast F.a_mul_fibreX (by norm_num)
  have h3' : (3 : ℤ) * F.fibreY = F.degree := by exact_mod_cast F.b_mul_fibreY (by norm_num)
  have h7' : (7 : ℤ) * F.fibreZ = F.degree := by exact_mod_cast F.c_mul_fibreZ (by norm_num)
  refine ⟨g, h2', h3', h7', ?_⟩
  simp only [MonodromyCover.eulerChar] at hchi
  linarith

end Hurwitz

section Modular

variable {n : ℕ} {S : Type*} [Fintype S] [DecidableEq S] (F : MonodromyCover 2 3 n S)

/-- **Orientability, modular signature.**  In a `(2,3,n)` cover the Euler characteristic is
even. -/
theorem MonodromyCover.even_eulerChar_23n (hn : 2 ≤ n) : Even F.eulerChar := by
  have h2 : 2 * F.fibreX = F.degree := F.a_mul_fibreX (by norm_num)
  have h3 : 3 * F.fibreY = F.degree := F.b_mul_fibreY (by norm_num)
  have hnn : n * F.fibreZ = F.degree := F.c_mul_fibreZ hn
  have hY : Equiv.Perm.sign F.Y = 1 :=
    MonodromyCover.sign_eq_one_of_odd F.freeY (by norm_num) ⟨1, by norm_num⟩
  have hXZ : Equiv.Perm.sign F.X = Equiv.Perm.sign (F.X * F.Y) := by
    have := F.sign_X_mul_sign_Y
    rw [hY, mul_one] at this
    exact this
  rw [F.freeX.sign_eq (by norm_num), F.freeZ.sign_eq hn] at hXZ
  -- parity bookkeeping
  have hpar : ((-1 : ℤˣ)) ^ ((2 + 1) * F.fibreX) = ((-1 : ℤˣ)) ^ ((n + 1) * F.fibreZ) := hXZ
  have hiff : Even ((2 + 1) * F.fibreX) ↔ Even ((n + 1) * F.fibreZ) :=
    units_neg_one_pow_eq_iff.mp hpar
  have hne3 : ¬ Even 3 := by decide
  have hDeven : Even F.degree := ⟨F.fibreX, by omega⟩
  have hleft : Even ((2 + 1) * F.fibreX) ↔ Even F.fibreX := by
    rw [show (2 + 1) * F.fibreX = 3 * F.fibreX from rfl, Nat.even_mul]
    exact ⟨fun h => h.resolve_left hne3, fun h => Or.inr h⟩
  have hright : Even ((n + 1) * F.fibreZ) ↔ Even F.fibreZ := by
    have hsplit : (n + 1) * F.fibreZ = F.degree + F.fibreZ := by
      rw [add_mul, one_mul, hnn]
    rw [hsplit, Nat.even_add]
    exact ⟨fun h => h.mp hDeven, fun h => ⟨fun _ => h, fun _ => hDeven⟩⟩
  have hkey : Even F.fibreX ↔ Even F.fibreZ := hleft.symm.trans (hiff.trans hright)
  have hY2 : Even F.fibreY := by
    obtain ⟨j, hj⟩ := hDeven
    have h3f : Even (3 * F.fibreY) := ⟨j, by omega⟩
    exact (Nat.even_mul.mp h3f).resolve_left hne3
  obtain ⟨jw, hjw⟩ := hY2
  have h2z : (2 : ℤ) * F.fibreX = F.degree := by exact_mod_cast h2
  have hjwz : (F.fibreY : ℤ) = jw + jw := by exact_mod_cast hjw
  rcases Nat.even_or_odd F.fibreX with hu | hu
  · obtain ⟨ju, hju⟩ := hu
    obtain ⟨jv, hjv⟩ := hkey.mp ⟨ju, hju⟩
    refine ⟨(jw : ℤ) + jv - ju, ?_⟩
    have hjuz : (F.fibreX : ℤ) = ju + ju := by exact_mod_cast hju
    have hjvz : (F.fibreZ : ℤ) = jv + jv := by exact_mod_cast hjv
    simp only [MonodromyCover.eulerChar]
    linarith
  · obtain ⟨ju, hju⟩ := hu
    have hvodd : Odd F.fibreZ := by
      rcases Nat.even_or_odd F.fibreZ with hv | hv
      · exact absurd (hkey.mpr hv) (by simpa [Nat.not_even_iff_odd] using ⟨ju, hju⟩)
      · exact hv
    obtain ⟨jv, hjv⟩ := hvodd
    refine ⟨(jw : ℤ) + jv - ju, ?_⟩
    have hjuz : (F.fibreX : ℤ) = 2 * ju + 1 := by exact_mod_cast hju
    have hjvz : (F.fibreZ : ℤ) = 2 * jv + 1 := by exact_mod_cast hjv
    simp only [MonodromyCover.eulerChar]
    linarith

/-- **Exact modular storage.**  A connected unramified `(2,3,n)` cover, i.e. a torsion-free
modular curve with all cusps of width `n`, satisfies `D = 6(2g + s − 2)` with `s = f_n` cusps. -/
theorem MonodromyCover.modular_capacity_exact (hn : 2 ≤ n) :
    ∃ g : ℤ, F.eulerChar = 2 - 2 * g ∧
      (F.degree : ℤ) = 6 * (2 * g + (F.fibreZ : ℤ) - 2) := by
  obtain ⟨k, hk⟩ := F.even_eulerChar_23n hn
  refine ⟨1 - k, ?_, ?_⟩
  · omega
  · have h2' : (2 : ℤ) * F.fibreX = F.degree := by exact_mod_cast F.a_mul_fibreX (by norm_num)
    have h3' : (3 : ℤ) * F.fibreY = F.degree := by exact_mod_cast F.b_mul_fibreY (by norm_num)
    simp only [MonodromyCover.eulerChar] at hk
    linarith

/-- The degree ordering of the modular phase is exactly the ordering by Euler capacity. -/
theorem modular_storage_order_iff {S₁ S₂ : Type*} [Fintype S₁] [DecidableEq S₁] [Fintype S₂]
    [DecidableEq S₂] {n₁ n₂ : ℕ} (F₁ : MonodromyCover 2 3 n₁ S₁) (F₂ : MonodromyCover 2 3 n₂ S₂)
    (g₁ g₂ : ℤ) (h₁ : (F₁.degree : ℤ) = 6 * (2 * g₁ + (F₁.fibreZ : ℤ) - 2))
    (h₂ : (F₂.degree : ℤ) = 6 * (2 * g₂ + (F₂.fibreZ : ℤ) - 2)) :
    (F₁.degree : ℤ) < (F₂.degree : ℤ) ↔
      2 * g₁ + (F₁.fibreZ : ℤ) < 2 * g₂ + (F₂.fibreZ : ℤ) := by
  constructor <;> intro h <;> omega

end Modular

end GaloisForLFunctions.HTGeometry
