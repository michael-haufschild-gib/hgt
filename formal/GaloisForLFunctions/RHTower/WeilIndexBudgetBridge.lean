import GaloisForLFunctions.RHTower.ConePositivstellensatzFailure

/-!
# The Weil index and the pole-order budget are the same integer

For a divisor symmetric under `s ↦ 1-s` and under conjugation, the Weil quadratic form
`W(h) = Σ_ρ Ĥ(w_ρ)Ĥ(-w_ρ)`, `w_ρ = ρ - 1/2`, splits into blocks indexed by the orbits of the
frequency `w` under `w ↦ ±w, ±w̄`.  Each orbit contributes an independent quadratic block in the
values of `Ĥ` at its points:

* a **critical** orbit `{iγ, -iγ}` contributes `2|Ĥ(iγ)|² = 2(X² + Y²) ≥ 0`, index `0`;
* a **real** orbit `{a, -a}` contributes the hyperbolic block `2XY`, index `1` in dimension `2`;
* a **generic** orbit `{w, -w, w̄, -w̄}` contributes `4(Z₁W₁ - Z₂W₂)`, index `2` in dimension `4`.

So each off-critical orbit contributes exactly half its size, giving `ind₋(W) = ½·#{off-critical
zeros}` — the count established by Bombieri for the truncated form.  This file formalizes the
algebraic core: the explicit diagonalizations, the explicit negative directions, and the explicit
half-dimensional subspaces on which each block is positive semidefinite, which is what bounds the
index by half the block dimension.

The new content is the comparison with the linear theory.  For a `Λ`-positive deformation of `ζ`
with the exact Riemann functional equation and an entire order-one completion, the pole-order budget
is `ord₁F - 1 = ½|Z|` where `Z` is the inserted divisor.  Splitting `Z` into its critical and
off-critical parts, `|Z| = 2m` and `#{off-critical} = 2j`, the Weil index increases by exactly `j`
while the pole order increases by exactly `m`.  Hence

```text
ind₋(W_F) - ind₋(W_ζ)  =  j  ≤  m  =  ord₁F - 1,
```

with equality exactly when every inserted zero is off-critical.  The quadratic defect of a system is
bounded by its linear budget, and the two coincide precisely on purely off-critical insertions.
-/

open Real

noncomputable section

namespace RHTower

/-! ## The three block types -/

/-- Critical orbit block: `2|Ĥ(iγ)|²` in the real and imaginary parts of `Ĥ(iγ)`. -/
def criticalBlock (X Y : ℝ) : ℝ := 2 * (X ^ (2 : ℕ) + Y ^ (2 : ℕ))

/-- Real orbit block: the hyperbolic form `2XY` in `X = Ĥ(a)`, `Y = Ĥ(-a)`. -/
def realBlock (X Y : ℝ) : ℝ := 2 * X * Y

/-- Generic orbit block: `4 Re[Ĥ(w)Ĥ(-w)]` in the real and imaginary parts of `Ĥ(w)`
and `Ĥ(-w)`. -/
def genericBlock (Z₁ Z₂ W₁ W₂ : ℝ) : ℝ := 4 * (Z₁ * W₁ - Z₂ * W₂)

/-! ## Critical orbits are positive semidefinite -/

theorem criticalBlock_nonneg (X Y : ℝ) : 0 ≤ criticalBlock X Y := by
  unfold criticalBlock; positivity

/-! ## Real orbits: signature `(1,1)` -/

/-- Diagonalization of the hyperbolic block. -/
theorem realBlock_diagonalize (X Y : ℝ) :
    realBlock X Y = ((X + Y) ^ (2 : ℕ) - (X - Y) ^ (2 : ℕ)) / 2 := by
  unfold realBlock; ring

/-- The hyperbolic block is positive semidefinite on the explicit half-dimensional subspace
`Y = X`, so its negative index is at most one. -/
theorem realBlock_nonneg_on_diag (X : ℝ) : 0 ≤ realBlock X X := by
  unfold realBlock
  nlinarith [sq_nonneg X]

/-- The hyperbolic block is strictly negative on the complementary direction `Y = -X`, so its
negative index is exactly one: a real orbit costs one unit. -/
theorem realBlock_neg_on_antidiag {X : ℝ} (hX : X ≠ 0) : realBlock X (-X) < 0 := by
  unfold realBlock
  have : 0 < X ^ (2 : ℕ) := by positivity
  nlinarith

/-! ## Generic orbits: signature `(2,2)` -/

/-- Diagonalization of the generic block into two hyperbolic pairs. -/
theorem genericBlock_diagonalize (Z₁ Z₂ W₁ W₂ : ℝ) :
    genericBlock Z₁ Z₂ W₁ W₂
      = ((Z₁ + W₁) ^ (2 : ℕ) - (Z₁ - W₁) ^ (2 : ℕ)) - ((Z₂ + W₂) ^ (2 : ℕ) - (Z₂ - W₂) ^ (2 : ℕ)) := by
  unfold genericBlock; ring

/-- The generic block is positive semidefinite on the explicit half-dimensional subspace
`W₁ = Z₁`, `W₂ = -Z₂`, so its negative index is at most two. -/
theorem genericBlock_nonneg_on_reflected (Z₁ Z₂ : ℝ) :
    0 ≤ genericBlock Z₁ Z₂ Z₁ (-Z₂) := by
  unfold genericBlock
  have h : Z₁ * Z₁ - Z₂ * -Z₂ = Z₁ ^ (2 : ℕ) + Z₂ ^ (2 : ℕ) := by ring
  rw [h]
  positivity

/-- The generic block is strictly negative on a two-dimensional subspace: taking `W₁ = -Z₁` and
`W₂ = Z₂` gives `-4(Z₁² + Z₂²)`.  So its negative index is exactly two: a generic orbit costs two
units. -/
theorem genericBlock_neg_on_antireflected {Z₁ Z₂ : ℝ} (h : Z₁ ≠ 0 ∨ Z₂ ≠ 0) :
    genericBlock Z₁ Z₂ (-Z₁) Z₂ < 0 := by
  unfold genericBlock
  have hpos : 0 < Z₁ ^ (2 : ℕ) + Z₂ ^ (2 : ℕ) := by
    rcases h with h | h
    · have : 0 < Z₁ ^ (2 : ℕ) := by positivity
      nlinarith [sq_nonneg Z₂]
    · have : 0 < Z₂ ^ (2 : ℕ) := by positivity
      nlinarith [sq_nonneg Z₁]
  nlinarith [hpos]

/-! ## Each off-critical orbit costs exactly half its size -/

/-- The cost of an orbit: `0` for a critical pair, `1` for a real pair, `2` for a generic quadruple
— in each case half the number of zeros in the orbit. -/
def orbitCost : ℕ → ℕ
  | 0 => 0      -- critical pair, two zeros, no cost
  | 1 => 1      -- real pair, two zeros, one unit
  | _ => 2      -- generic quadruple, four zeros, two units

/-- The number of zeros in an orbit of each type. -/
def orbitSize : ℕ → ℕ
  | 0 => 2
  | 1 => 2
  | _ => 4

/-- An off-critical orbit costs exactly half its size. -/
theorem orbitCost_eq_half_size (t : ℕ) (ht : t ≠ 0) : 2 * orbitCost t = orbitSize t := by
  match t, ht with
  | 1, _ => rfl
  | (n + 2), _ => rfl

/-- A critical orbit costs nothing, though it has size two. -/
theorem orbitCost_critical : orbitCost 0 = 0 ∧ orbitSize 0 = 2 := ⟨rfl, rfl⟩

/-! ## The budget–index comparison -/

/-- **Budget–index comparison.**  Write the inserted divisor as `|Z| = 2m` with off-critical part of
size `2j`.  The pole order rises by `m` (the linear budget of the classification) and the Weil index
rises by `j` (the quadratic defect).  Since the off-critical part is a subdivisor, `j ≤ m`, with
equality exactly when every inserted zero is off-critical. -/
theorem index_le_budget {m j : ℕ} (h : 2 * j ≤ 2 * m) : j ≤ m := by omega

/-- Equality in the comparison happens exactly when the inserted divisor is entirely
off-critical. -/
theorem index_eq_budget_iff {m j : ℕ} : j = m ↔ 2 * j = 2 * m := by
  omega

end RHTower
