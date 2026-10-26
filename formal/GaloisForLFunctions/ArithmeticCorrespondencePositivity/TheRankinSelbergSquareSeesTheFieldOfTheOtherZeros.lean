import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

/-!
# The Rankin–Selberg square sees the field of the other zeros

The Rankin–Selberg source `Λ ⋆ Λ` has Dirichlet series `(ζ′/ζ)²`: it is the carrier the report
names first as a candidate for positivity beyond isotropy (B3.17), because it is not closed under
point convolution. Its polar structure at a zero is computed here on a finite configuration
`F(s) = Σ_j m_j/(s − z_j)` of distinct points.

* **The square is non-local at the polar level** (`sq_sum_eq_partial_fractions`). For `s` off the
  configuration,
  `F(s)² = Σ_j m_j²/(s − z_j)² + Σ_j 2 m_j E_j/(s − z_j)`, `E_j = Σ_{k ≠ j} m_k/(z_j − z_k)`:
  the simple-pole coefficient at `z_j` is `2 m_j` times the **field** of all the other points at
  `z_j` (`fieldAt`).
* **Critical configurations are in transverse equilibrium** (`re_fieldAt_eq_zero_of_critical`):
  with real multiplicities and every point on `Re s = ½`, `Re E_j = 0`.
* **The deepest off-line point feels a positive field** (`re_fieldAt_pos_of_deepest`): if `z_j` has
  maximal real part `½ + δ`, `δ > 0`, the multiplicities are nonnegative and its reflection
  `1 − z̄_j` carries positive multiplicity, then `Re E_j > 0`: every point contributes
  `m_k Re(z_j − z_k)/|z_j − z_k|² ≥ 0`, and the reflection contributes `m/(2δ)`.

So the Rankin–Selberg square attaches to each zero a quantity that is neither isotropic nor
point-local: the transverse field of the whole configuration. It vanishes when every zero is
critical and is positive at the deepest off-line zero; on configurations with several off-line
pairs of different depths it has no sign elsewhere. A positivity theorem for `Λ ⋆ Λ` beyond
isotropy would have to control this field at the zeros — a spectral quantity that the
multiplicative structure of `Λ ⋆ Λ` (an external square, gauge invariant) does not see.
-/

open Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **field** of the other points at `z_j`: `E_j = Σ_{k ≠ j} m_k/(z_j − z_k)`. -/
noncomputable def fieldAt (m z : ι → ℂ) (j : ι) : ℂ := ∑ k ∈ univ.erase j, m k / (z j - z k)

/-- **The square of a finite polar source in partial fractions.** -/
theorem sq_sum_eq_partial_fractions (m z : ι → ℂ) (hz : Function.Injective z) (s : ℂ)
    (hs : ∀ j, s ≠ z j) :
    (∑ j, m j / (s - z j)) ^ 2 =
      ∑ j, m j ^ 2 / (s - z j) ^ 2 + ∑ j, 2 * m j * fieldAt m z j / (s - z j) := by
  have hsz : ∀ j, s - z j ≠ 0 := fun j => sub_ne_zero.mpr (hs j)
  -- expand the square into the diagonal and the off-diagonal pairs
  have hexp : (∑ j, m j / (s - z j)) ^ 2 =
      ∑ j, m j ^ 2 / (s - z j) ^ 2 +
        ∑ j, ∑ k ∈ univ.erase j, m j / (s - z j) * (m k / (s - z k)) := by
    rw [sq, sum_mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    rw [← add_sum_erase _ _ (mem_univ j)]
    congr 1
    rw [div_mul_div_comm, ← sq, ← sq]
  -- each off-diagonal product is a difference of simple fractions
  have hpair : ∀ j k, j ≠ k → m j / (s - z j) * (m k / (s - z k)) =
      m j * m k / (z j - z k) * (1 / (s - z j)) - m j * m k / (z j - z k) * (1 / (s - z k)) := by
    intro j k hjk
    have hd : z j - z k ≠ 0 := sub_ne_zero.mpr fun h => hjk (hz h)
    have h1 := hsz j
    have h2 := hsz k
    field_simp
    ring
  have hoff : ∑ j, ∑ k ∈ univ.erase j, m j / (s - z j) * (m k / (s - z k)) =
      ∑ j, 2 * m j * fieldAt m z j / (s - z j) := by
    -- the sum over ordered pairs `j ≠ k`
    have h1 : ∑ j, ∑ k ∈ univ.erase j, m j / (s - z j) * (m k / (s - z k)) =
        ∑ j, ∑ k ∈ univ.erase j, m j * m k / (z j - z k) * (1 / (s - z j)) -
          ∑ j, ∑ k ∈ univ.erase j, m j * m k / (z j - z k) * (1 / (s - z k)) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun k hk => hpair j k (ne_of_mem_erase hk).symm
    -- swapping the roles of `j` and `k` in the second sum
    have h2 : ∑ j, ∑ k ∈ univ.erase j, m j * m k / (z j - z k) * (1 / (s - z k)) =
        -∑ j, ∑ k ∈ univ.erase j, m j * m k / (z j - z k) * (1 / (s - z j)) := by
      have hsym : ∀ f : ι → ι → ℂ, ∑ j, ∑ k ∈ univ.erase j, f j k = ∑ j, ∑ k ∈ univ.erase j, f k j := by
        intro f
        have e : ∀ g : ι → ι → ℂ, ∑ j, ∑ k ∈ univ.erase j, g j k = ∑ j, ∑ k, g j k - ∑ j, g j j := by
          intro g
          rw [← sum_sub_distrib]
          exact sum_congr rfl fun j _ => sum_erase_eq_sub (mem_univ j)
        rw [e f, e (fun j k => f k j), sum_comm]
      rw [hsym, ← sum_neg_distrib]
      refine sum_congr rfl fun j _ => ?_
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun k hk => ?_
      have hd : z k - z j ≠ 0 := sub_ne_zero.mpr fun h => (ne_of_mem_erase hk) (hz h)
      have hd' : z j - z k ≠ 0 := sub_ne_zero.mpr fun h => (ne_of_mem_erase hk) (hz h).symm
      field_simp
      ring
    rw [h1, h2, sub_neg_eq_add, ← two_mul, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [fieldAt, mul_sum, sum_div]
    refine sum_congr rfl fun k _ => ?_
    ring
  rw [hexp, hoff]

/-- **Critical configurations are in transverse equilibrium.** With real multiplicities and every
point on the critical line, the field has zero real part. -/
theorem re_fieldAt_eq_zero_of_critical (m z : ι → ℂ) (hm : ∀ k, (m k).im = 0)
    (hz : ∀ k, (z k).re = 1 / 2) (j : ι) : (fieldAt m z j).re = 0 := by
  rw [fieldAt, Complex.re_sum]
  refine sum_eq_zero fun k _ => ?_
  have hd : (z j - z k).re = 0 := by rw [Complex.sub_re, hz, hz]; ring
  rw [Complex.div_re, hd, mul_zero, zero_div, hm, zero_mul, zero_div, add_zero]

/-- **The deepest off-line point feels a positive field.** If `z_j` has maximal real part
`½ + δ`, `δ > 0`, all multiplicities are nonnegative reals and the reflection `1 − z̄_j` occurs with
positive multiplicity, then `Re E_j > 0`. -/
theorem re_fieldAt_pos_of_deepest (m z : ι → ℂ)
    (hm : ∀ k, 0 ≤ (m k).re ∧ (m k).im = 0) (j : ι) (hδ : 1 / 2 < (z j).re)
    (hmax : ∀ k, (z k).re ≤ (z j).re) (j' : ι) (hj' : z j' = 1 - conj (z j)) (hmj' : 0 < (m j').re) :
    0 < (fieldAt m z j).re := by
  have hjj' : j' ≠ j := by
    intro h
    have := congrArg Complex.re hj'
    rw [h, Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    linarith
  have hterm : ∀ k ∈ univ.erase j, 0 ≤ (m k / (z j - z k)).re := by
    intro k hk
    rw [Complex.div_re, (hm k).2, zero_mul, zero_div, add_zero]
    refine div_nonneg (mul_nonneg (hm k).1 ?_) (Complex.normSq_nonneg _)
    rw [Complex.sub_re]; linarith [hmax k]
  rw [fieldAt, Complex.re_sum]
  refine lt_of_lt_of_le ?_ (single_le_sum hterm (mem_erase.mpr ⟨hjj', mem_univ j'⟩))
  -- the reflection contributes `m/(2δ)`
  have hd : z j - z j' = ((2 * (z j).re - 1 : ℝ) : ℂ) := by
    rw [hj']; apply Complex.ext <;> simp; ring
  rw [hd, Complex.div_re, (hm j').2, zero_mul, zero_div, add_zero, Complex.ofReal_re,
    Complex.normSq_ofReal]
  have h2 : 0 < 2 * (z j).re - 1 := by linarith
  exact div_pos (mul_pos hmj' h2) (mul_pos h2 h2)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
