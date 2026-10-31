import GaloisForLFunctions.HeckeKreinToeplitz.Index.ColumnProjections
import GaloisForLFunctions.HeckeKreinToeplitz.Index.ProjectionFunctoriality

/-!
# Order of periodic moving forms

Nested fixed projections differ by a vector in the smaller action’s moving space. Nonnegativity there reverses the order of the complementary quadratic forms.
-/

open Module
noncomputable section
namespace GaloisForLFunctions.HeckeKreinToeplitz
variable {G : Type*} [Group G]

/-- A power's larger fixed space adds only nonnegative directions when the moving space is positive. -/
theorem kernelColumnPairing_projection_re_le_of_power {k : G → ℂ} (hk : IsHermKernel k)
    (g h : G) (n : ℕ) (hg : g = h ^ n)
    (hpg : ∀ x : kernelColumnSpan k,
      ∃ m : ℕ, m ≠ 0 ∧ ((kernelColumnRepresentation k g) ^ m) x = x)
    (hph : ∀ x : kernelColumnSpan k,
      ∃ m : ℕ, m ≠ 0 ∧ ((kernelColumnRepresentation k h) ^ m) x = x)
    (hpos : ∀ x ∈ LinearMap.range (kernelColumnRepresentation k h + (-1 : ℂ) • 1),
      0 ≤ (kernelColumnPairing k x x).re) (x : kernelColumnSpan k) :
    (kernelColumnPairing k
      (locallyPeriodicProjection (kernelColumnRepresentation k h) hph x)
      (locallyPeriodicProjection (kernelColumnRepresentation k h) hph x)).re ≤
    (kernelColumnPairing k
      (locallyPeriodicProjection (kernelColumnRepresentation k g) hpg x)
      (locallyPeriodicProjection (kernelColumnRepresentation k g) hpg x)).re := by
  let P := locallyPeriodicProjection (kernelColumnRepresentation k h) hph
  let Q := locallyPeriodicProjection (kernelColumnRepresentation k g) hpg
  have hpU : ∀ v : kernelColumnSpan k, ∃ m : ℕ, m ≠ 0 ∧
      (((kernelColumnRepresentation k h) ^ n) ^ m) v = v := by
    simpa only [hg, map_pow] using hpg
  have hnest : P (Q x) = P x := by
    have he := (locallyPeriodicProjection_pow_nested
      (kernelColumnRepresentation k h) hph n hpU x).2
    simpa only [P, Q, hg, map_pow] using he
  have hsplit := kernelColumnPairing_projection_decomposition hk h hph (Q x) (Q x)
  change kernelColumnPairing k (Q x) (Q x) =
    kernelColumnPairing k (P (Q x)) (P (Q x)) +
      kernelColumnPairing k (Q x - P (Q x)) (Q x - P (Q x)) at hsplit
  have hmem : Q x - P (Q x) ∈
      LinearMap.range (kernelColumnRepresentation k h + (-1 : ℂ) • 1) := by
    have he : Q x - P (Q x) = Q x + (-1 : ℂ) • P (Q x) := by
      apply Subtype.ext
      funext a
      change (Q x : G → ℂ) a - (P (Q x) : G → ℂ) a =
        (Q x : G → ℂ) a + (-1 : ℂ) * (P (Q x) : G → ℂ) a
      ring
    rw [he]
    exact add_neg_locallyPeriodicProjection_mem_range (kernelColumnRepresentation k h) hph (Q x)
  have hnonneg := hpos _ hmem
  rw [hnest] at hsplit hnonneg
  have he := congrArg Complex.re hsplit
  rw [Complex.add_re] at he
  change (kernelColumnPairing k (P x) (P x)).re ≤ (kernelColumnPairing k (Q x) (Q x)).re
  linarith only [he, hnonneg]

/-- Moving quadratic forms increase when a cyclic subgroup is enlarged. -/
theorem kernelColumnPairing_moving_re_le_of_power {k : G → ℂ} (hk : IsHermKernel k)
    (g h : G) (n : ℕ) (hg : g = h ^ n)
    (hpg : ∀ x : kernelColumnSpan k,
      ∃ m : ℕ, m ≠ 0 ∧ ((kernelColumnRepresentation k g) ^ m) x = x)
    (hph : ∀ x : kernelColumnSpan k,
      ∃ m : ℕ, m ≠ 0 ∧ ((kernelColumnRepresentation k h) ^ m) x = x)
    (hpos : ∀ x ∈ LinearMap.range (kernelColumnRepresentation k h + (-1 : ℂ) • 1),
      0 ≤ (kernelColumnPairing k x x).re) (x : kernelColumnSpan k) :
    (kernelColumnPairing k
      (x - locallyPeriodicProjection (kernelColumnRepresentation k g) hpg x)
      (x - locallyPeriodicProjection (kernelColumnRepresentation k g) hpg x)).re ≤
    (kernelColumnPairing k
      (x - locallyPeriodicProjection (kernelColumnRepresentation k h) hph x)
      (x - locallyPeriodicProjection (kernelColumnRepresentation k h) hph x)).re := by
  have hp := kernelColumnPairing_projection_re_le_of_power hk g h n hg hpg hph hpos x
  have heG := congrArg Complex.re (kernelColumnPairing_projection_decomposition hk g hpg x x)
  have heH := congrArg Complex.re (kernelColumnPairing_projection_decomposition hk h hph x x)
  simp only [Complex.add_re] at heG heH
  linarith only [hp, heG, heH]

#print axioms kernelColumnPairing_projection_re_le_of_power
#print axioms kernelColumnPairing_moving_re_le_of_power
end GaloisForLFunctions.HeckeKreinToeplitz
