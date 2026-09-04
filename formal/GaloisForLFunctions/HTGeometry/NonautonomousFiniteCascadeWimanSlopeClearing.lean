import GaloisForLFunctions.HTGeometry.NonautonomousFiniteCascadeWimanComponents
import GaloisForLFunctions.HTGeometry.WimanRamifiedCascadeObservability

/-!
# Exact ramification clearing for finite Wiman cascades

The rational Wiman slope attached to a velocity is cleared by using its denominator as the
ramification index of the adjacent input-state coordinate.  In the reversed cascade ordering,
the signed adjacent Hahn exponent is the negative numerator.  Thus the analytic inequality
`p + 1 > 0` becomes exactly the integral charge inequality required by the signed Wiman
observability theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- Ramification indices which clear a finite family of adjacent rational slopes.  Coordinate zero
has no preceding slope; every later coordinate uses the denominator of its unique predecessor. -/
def wimanSlopeRamification {n : ℕ} (p : Fin (n + 1) → ℚ)
    (m : Fin (n + 1)) : ℕ :=
  if hm : m = 0 then 1 else (p ⟨(m : ℕ) - 1, by omega⟩).den

/-- Signed adjacent exponent after clearing the rational slope. -/
def wimanSlopeTail {n : ℕ} (p : Fin (n + 1) → ℚ)
    (j : Fin (n + 1)) : ℤ :=
  -(p j).num

theorem wimanSlopeRamification_pos {n : ℕ} (p : Fin (n + 1) → ℚ)
    (m : Fin (n + 1)) :
    0 < wimanSlopeRamification p m := by
  rw [wimanSlopeRamification]
  split_ifs
  · omega
  · exact (p _).den_pos

theorem wimanSlopeRamification_succ {n : ℕ} (p : Fin (n + 1) → ℚ)
    (j : Fin (n + 1)) (h : (j : ℕ) + 1 < n + 1) :
    wimanSlopeRamification p ⟨(j : ℕ) + 1, h⟩ = (p j).den := by
  rw [wimanSlopeRamification, dif_neg]
  · congr 2
  · intro hz
    have := congrArg Fin.val hz
    simp at this

/-- The signed integral tail represents exactly minus ramification times the rational slope. -/
theorem wimanSlopeTail_eq_neg_ramification_mul {n : ℕ}
    (p : Fin (n + 1) → ℚ) (j : Fin (n + 1))
    (h : (j : ℕ) + 1 < n + 1) :
    ((wimanSlopeTail p j : ℤ) : ℚ) =
      -((wimanSlopeRamification p ⟨(j : ℕ) + 1, h⟩ : ℕ) : ℚ) * p j := by
  rw [wimanSlopeTail, wimanSlopeRamification_succ]
  push_cast
  rw [neg_mul, Rat.den_mul_eq_num]

/-- Positivity of every rational Wiman charge is precisely the integral charge condition after
denominator clearing. -/
theorem ramifiedWimanChargesPositive_wimanSlope {n : ℕ}
    (p : Fin (n + 1) → ℚ) (hp : ∀ j, 0 < ((p j : ℚ) : ℝ) + 1) :
    RamifiedWimanChargesPositive (wimanSlopeRamification p) (wimanSlopeTail p) := by
  intro j h
  rw [wimanSlopeTail, wimanSlopeRamification_succ]
  have hpQ : (-1 : ℚ) < p j := by
    exact_mod_cast (by linarith [hp j] : (-1 : ℝ) < (p j : ℝ))
  have hdenQ : (0 : ℚ) < (p j).den := by
    exact_mod_cast (p j).den_pos
  have hmul := mul_lt_mul_of_pos_left hpQ hdenQ
  rw [Rat.den_mul_eq_num] at hmul
  have hz : -((p j).den : ℤ) < (p j).num := by
    exact_mod_cast
      (by simpa using hmul : (-((p j).den : ℚ)) < ((p j).num : ℚ))
  omega

/-! ## Canonical clearing for the actual finite cascade -/

/-- Chosen Wiman slopes in the reversed velocity order used by the ramified product cascade. -/
noncomputable def nonautonomousFiniteCascadeWimanSlopeInVelocityOrder
    {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1)
    (j : Fin (n + 1)) : ℚ :=
  (nonautonomousFiniteCascadeWimanData hall h1 j.rev).slope

/-- Canonical state ramification attached to the actual finite cascade's Wiman slopes. -/
noncomputable def nonautonomousFiniteCascadeWimanRamification
    {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    Fin (n + 1) → ℕ :=
  wimanSlopeRamification
    (nonautonomousFiniteCascadeWimanSlopeInVelocityOrder hall h1)

/-- Canonical signed adjacent exponents attached to the actual finite cascade. -/
noncomputable def nonautonomousFiniteCascadeWimanTail
    {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    Fin (n + 1) → ℤ :=
  wimanSlopeTail
    (nonautonomousFiniteCascadeWimanSlopeInVelocityOrder hall h1)

/-- Chosen nonzero Wiman edge coefficients in reversed velocity order. -/
noncomputable def nonautonomousFiniteCascadeWimanCoefficientInVelocityOrder
    {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1)
    (j : Fin (n + 1)) : ℂ :=
  (nonautonomousFiniteCascadeWimanData hall h1 j.rev).root

theorem nonautonomousFiniteCascadeWimanRamification_pos
    {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1)
    (j : Fin (n + 1)) :
    0 < nonautonomousFiniteCascadeWimanRamification hall h1 j :=
  wimanSlopeRamification_pos _ j

theorem nonautonomousFiniteCascadeWimanChargesPositive
    {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1) :
    RamifiedWimanChargesPositive
      (nonautonomousFiniteCascadeWimanRamification hall h1)
      (nonautonomousFiniteCascadeWimanTail hall h1) := by
  apply ramifiedWimanChargesPositive_wimanSlope
  intro j
  exact nonautonomousFiniteCascadeWimanData_charge_pos hall h1 j.rev

theorem nonautonomousFiniteCascadeWimanCoefficientInVelocityOrder_ne_zero
    {f : ℕ → ℂ → ℂ} {n : ℕ}
    (hall : ∀ i : ℕ, TranscendentalEntire (f i))
    (h1 : ∀ k, k < n + 1 → DifferentiallyAlgebraicOfOrder (f k) 1)
    (j : Fin (n + 1)) :
    nonautonomousFiniteCascadeWimanCoefficientInVelocityOrder hall h1 j ≠ 0 :=
  nonautonomousFiniteCascadeWimanData_root_ne_zero hall h1 j.rev

end

end GaloisForLFunctions.HTGeometry
