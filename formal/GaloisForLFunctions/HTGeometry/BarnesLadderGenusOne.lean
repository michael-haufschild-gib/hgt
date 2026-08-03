import GaloisForLFunctions.HTGeometry.BarnesSliceReindex

/-!
# At genus one the ladder correction is independent of the argument

The ladder correction of one atom is the difference of two numerators over the common denominator
`D = w_{n+e_j} + z`.  Both numerators are polynomials in `D` with constant term one, because

```text
-(z + ω_j)/w_n = 1 - D/w_n,      -z/w_{n+e_j} = 1 - D/w_{n+e_j},
```

so the difference is divisible by `D` and the quotient is a polynomial in `D`.  At genus one that
polynomial is the constant

```text
1/w_{n+e_j} - 1/w_n,
```

with no `z` left at all: the genus-one ladder correction is a telescoping difference of inverse cone
values.  This is the structural reason the order-one source has a rational shift difference.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The numerators as polynomials in the common denominator -/

theorem neg_div_eq_one_sub_denom (ω : ι → ℂ) (n : ι → ℕ) (j : ι) (z : ℂ)
    (hw : conePeriod ω n ≠ 0) :
    -((z + ω j) / conePeriod ω n) =
      1 - (conePeriod ω (n + Pi.single j 1) + z) / conePeriod ω n := by
  rw [conePeriod_add_single]
  field_simp
  ring

theorem neg_div_shift_eq_one_sub_denom (ω : ι → ℂ) (n : ι → ℕ) (j : ι) (z : ℂ)
    (hw : conePeriod ω (n + Pi.single j 1) ≠ 0) :
    -(z / conePeriod ω (n + Pi.single j 1)) =
      1 - (conePeriod ω (n + Pi.single j 1) + z) / conePeriod ω (n + Pi.single j 1) := by
  field_simp
  ring

/-! ## The genus-one correction -/

/-- **The genus-one ladder correction is a telescoping difference.**  When there is a single
structural direction the correction carries no dependence on the argument at all. -/
theorem barnesAtom_shift_sub_card_one (ω : ι → ℂ) (hcard : Fintype.card ι = 1)
    {n : ι → ℕ} (hn : n ≠ 0) (j : ι) (z : ℂ)
    (hw : conePeriod ω n ≠ 0) (hw' : conePeriod ω (n + Pi.single j 1) ≠ 0)
    (hD : conePeriod ω (n + Pi.single j 1) + z ≠ 0) :
    barnesAtom ω n (z + ω j) - barnesAtom ω (n + Pi.single j 1) z =
      (conePeriod ω (n + Pi.single j 1))⁻¹ - (conePeriod ω n)⁻¹ := by
  have hshift : conePeriod ω (n + Pi.single j 1) = conePeriod ω n + ω j :=
    conePeriod_add_single ω n j
  rw [barnesAtom_shift_sub ω hn j z, hcard, pow_one, pow_one, div_eq_iff hD]
  rw [hshift] at hw' hD ⊢
  field_simp
  ring

/-- **The genus-one correction is independent of the argument.** -/
theorem barnesAtom_shift_sub_card_one_const (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (hcard : Fintype.card ι = 1) {n : ι → ℕ} (hn : n ≠ 0) (j : ι) (z z' : ℂ)
    (hD : conePeriod ω (n + Pi.single j 1) + z ≠ 0)
    (hD' : conePeriod ω (n + Pi.single j 1) + z' ≠ 0) :
    barnesAtom ω n (z + ω j) - barnesAtom ω (n + Pi.single j 1) z =
      barnesAtom ω n (z' + ω j) - barnesAtom ω (n + Pi.single j 1) z' := by
  haveI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hw : conePeriod ω n ≠ 0 := conePeriod_ne_zero ω hω hn
  have hw' : conePeriod ω (n + Pi.single j 1) ≠ 0 :=
    conePeriod_ne_zero ω hω (add_single_ne_zero n j)
  rw [barnesAtom_shift_sub_card_one ω hcard hn j z hw hw' hD,
    barnesAtom_shift_sub_card_one ω hcard hn j z' hw hw' hD']

end

end GaloisForLFunctions
