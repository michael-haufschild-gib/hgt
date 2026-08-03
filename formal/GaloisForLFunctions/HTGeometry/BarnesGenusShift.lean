import GaloisForLFunctions.HTGeometry.BarnesLadderDecomposition

/-!
# Changing the genus of a cone atom costs a polynomial

The slice left over by the Barnes ladder is the cone of the deleted frame, but its atoms carry the
genus of the *ambient* frame, one higher than the genus that the lower step of the hierarchy uses.
Raising the genus by one changes an atom by a term with no `z + w` in the denominator:

```text
A^{p+1}_n(z) - A^p_n(z) = -(-z/w_n)^p / w_n,
```

because `(-z/w) - 1 = -(z + w)/w` cancels the denominator.  Summed over the cone at the critical
genus those corrections converge absolutely, and the sum is a constant times `z^p`: a polynomial.

So the genus mismatch between the slice and the lower source is a polynomial, which is
differentially algebraic and therefore invisible to the annihilator statements taken modulo the
differentially algebraic sector.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-! ## Atoms of arbitrary genus -/

/-- The rational atom of genus `p` at one exponent vector. -/
def barnesAtomPow (ω : ι → ℂ) (p : ℕ) (n : ι → ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 0 else (-(z / conePeriod ω n)) ^ p / (conePeriod ω n + z)

omit [Nonempty ι] in
theorem barnesAtom_eq_barnesAtomPow (ω : ι → ℂ) (n : ι → ℕ) (z : ℂ) :
    barnesAtom ω n z = barnesAtomPow ω (Fintype.card ι) n z := rfl

/-- The genus-raising correction of one atom. -/
def barnesGenusCorrection (ω : ι → ℂ) (n : ι → ℕ) (z : ℂ) : ℂ :=
  if n = 0 then 0 else (-(z / conePeriod ω n)) ^ Fintype.card ι / conePeriod ω n

/-! ## The genus shift of one atom -/

omit [Nonempty ι] in
/-- **Raising the genus by one costs a term without the pole.** -/
theorem barnesAtomPow_succ_sub (ω : ι → ℂ) (p : ℕ) {n : ι → ℕ} (hn : n ≠ 0) (z : ℂ)
    (hw : conePeriod ω n ≠ 0) (hz : conePeriod ω n + z ≠ 0) :
    barnesAtomPow ω (p + 1) n z - barnesAtomPow ω p n z =
      -((-(z / conePeriod ω n)) ^ p / conePeriod ω n) := by
  rw [barnesAtomPow, if_neg hn, barnesAtomPow, if_neg hn, div_sub_div_same, pow_succ]
  rw [div_eq_iff hz]
  field_simp
  ring

/-! ## Summability of the corrections -/

theorem summable_barnesGenusCorrection (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (z : ℂ) :
    Summable fun n : ι → ℕ => barnesGenusCorrection ω n z := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_conePeriod_inv_pow ω hω).mul_left (‖z‖ ^ Fintype.card ι))
  by_cases h : n = 0
  · rw [barnesGenusCorrection, if_pos h, if_pos h, norm_zero, mul_zero]
  · rw [barnesGenusCorrection, if_neg h, if_neg h, norm_div, norm_pow, norm_neg, norm_div,
      div_pow, div_div, ← pow_succ, div_eq_mul_inv]

/-! ## The genus shift of the whole series -/

theorem barnesAtomPow_succ_eq (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {z : ℂ}
    (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0) (n : ι → ℕ) :
    barnesAtomPow ω (Fintype.card ι + 1) n z =
      barnesAtom ω n z - barnesGenusCorrection ω n z := by
  by_cases h : n = 0
  · rw [barnesAtomPow, if_pos h, barnesAtom, if_pos h, barnesGenusCorrection, if_pos h, sub_zero]
  · have hsub := barnesAtomPow_succ_sub ω (Fintype.card ι) h z
      (conePeriod_ne_zero ω hω h) (hpole n h)
    rw [barnesAtom_eq_barnesAtomPow, barnesGenusCorrection, if_neg h]
    linear_combination hsub

theorem summable_barnesAtomPow_succ (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {z : ℂ}
    (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0) :
    Summable fun n : ι → ℕ => barnesAtomPow ω (Fintype.card ι + 1) n z := by
  refine Summable.congr ((summable_barnesAtom ω hω z).sub
    (summable_barnesGenusCorrection ω hω z)) fun n => ?_
  exact (barnesAtomPow_succ_eq ω hω hpole n).symm

/-- **The genus shift of the atom series.**  Raising the genus by one subtracts the convergent
correction series, whose terms have no pole. -/
theorem tsum_barnesAtomPow_succ (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {z : ℂ}
    (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0) :
    (∑' n : ι → ℕ, barnesAtomPow ω (Fintype.card ι + 1) n z) =
      (∑' n : ι → ℕ, barnesAtom ω n z) -
        ∑' n : ι → ℕ, barnesGenusCorrection ω n z := by
  rw [tsum_congr (barnesAtomPow_succ_eq ω hω hpole),
    Summable.tsum_sub (summable_barnesAtom ω hω z) (summable_barnesGenusCorrection ω hω z)]

/-! ## The correction series is a monomial -/

/-- The cone zeta value at the critical exponent. -/
def coneZeta (ω : ι → ℂ) : ℂ :=
  ∑' n : ι → ℕ, (if n = 0 then 0 else (conePeriod ω n ^ (Fintype.card ι + 1))⁻¹)

theorem summable_coneZetaTerm (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) :
    Summable fun n : ι → ℕ =>
      (if n = 0 then 0 else (conePeriod ω n ^ (Fintype.card ι + 1))⁻¹) := by
  refine Summable.of_norm ?_
  refine (summable_conePeriod_inv_pow ω hω).congr fun n => ?_
  by_cases h : n = 0
  · rw [if_pos h, if_pos h, norm_zero]
  · rw [if_neg h, if_neg h, norm_inv, norm_pow]

omit [Nonempty ι] in
theorem barnesGenusCorrection_eq (ω : ι → ℂ) (n : ι → ℕ) (z : ℂ) :
    barnesGenusCorrection ω n z =
      ((-1) ^ Fintype.card ι * z ^ Fintype.card ι) *
        (if n = 0 then 0 else (conePeriod ω n ^ (Fintype.card ι + 1))⁻¹) := by
  by_cases h : n = 0
  · rw [barnesGenusCorrection, if_pos h, if_pos h, mul_zero]
  · rw [barnesGenusCorrection, if_neg h, if_neg h, neg_pow, div_pow, pow_succ]
    ring

omit [Nonempty ι] in
/-- **The genus correction is a monomial.**  Summed over the cone, the genus-raising corrections
give a constant multiple of `z^N`, hence a polynomial: the genus mismatch between a slice and the
lower source is differentially algebraic. -/
theorem tsum_barnesGenusCorrection_eq (ω : ι → ℂ) (z : ℂ) :
    (∑' n : ι → ℕ, barnesGenusCorrection ω n z) =
      (-1) ^ Fintype.card ι * z ^ Fintype.card ι * coneZeta ω := by
  rw [tsum_congr (barnesGenusCorrection_eq ω · z), coneZeta,
    tsum_mul_left]

end

end GaloisForLFunctions
