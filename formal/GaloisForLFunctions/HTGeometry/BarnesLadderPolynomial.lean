import GaloisForLFunctions.HTGeometry.BarnesLadderCoefficients

/-!
# The ladder correction is a polynomial

Expanding the factored correction term by term in powers of the argument separates the cone
dependence from the argument dependence completely:

```text
t_n u_n^k v_n^{N-1-k} = (-1)^{N-1} (z + ω_j)^k z^{N-1-k} · c_{n,k},
```

with `c_{n,k}` the ladder coefficient, which carries no `z` at all.  Since the `k`-sum is finite and
each coefficient family is summable, the sum over the cone can be taken inside, and the correction
series becomes the explicit rational atom at the unit exponent plus a polynomial in the argument
with constant coefficients.

This is the last analytic ingredient of the ladder: the correction of the shift difference is
differentially algebraic at every genus.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-! ## Separating the argument from the cone -/

omit [Nonempty ι] in
theorem barnesLadderTerm_eq (ω : ι → ℂ) {n : ι → ℕ} (hn : n ≠ 0) (j : ι) (z : ℂ)
    (hw : conePeriod ω n ≠ 0) (hw' : conePeriod ω (n + Pi.single j 1) ≠ 0)
    {k m : ℕ} (hN : Fintype.card ι = k + 1 + m) :
    ((conePeriod ω (n + Pi.single j 1))⁻¹ - (conePeriod ω n)⁻¹) *
        ((-((z + ω j) / conePeriod ω n)) ^ k *
          (-(z / conePeriod ω (n + Pi.single j 1))) ^ (Fintype.card ι - 1 - k)) =
      ((-1) ^ (Fintype.card ι - 1) * (z + ω j) ^ k * z ^ (Fintype.card ι - 1 - k)) *
        barnesLadderCoefficient ω j k n := by
  have h1 : Fintype.card ι - 1 - k = m := by omega
  have h2 : Fintype.card ι - k = m + 1 := by omega
  have h3 : Fintype.card ι - 1 = k + m := by omega
  have hu : (-((z + ω j) / conePeriod ω n)) ^ k
      = (-1) ^ k * ((z + ω j) ^ k / conePeriod ω n ^ k) := by
    rw [neg_pow, div_pow]
  have hv : (-(z / conePeriod ω (n + Pi.single j 1))) ^ m
      = (-1) ^ m * (z ^ m / conePeriod ω (n + Pi.single j 1) ^ m) := by
    rw [neg_pow, div_pow]
  rw [conePeriod_inv_sub_inv ω n j hw hw', barnesLadderCoefficient, if_neg hn, h1, h2, h3,
    hu, hv, pow_add]
  field_simp
  ring

/-! ## The correction series termwise -/

theorem barnesLadderCorrection_term (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (j : ι) {z : ℂ}
    (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0) (n : ι → ℕ) :
    (if n = 0 then 0
      else barnesAtom ω n (z + ω j) - barnesAtom ω (n + Pi.single j 1) z) =
      ∑ k ∈ Finset.range (Fintype.card ι),
        ((-1) ^ (Fintype.card ι - 1) * (z + ω j) ^ k * z ^ (Fintype.card ι - 1 - k)) *
          barnesLadderCoefficient ω j k n := by
  by_cases hn : n = 0
  · rw [if_pos hn]
    refine (Finset.sum_eq_zero fun k _ => ?_).symm
    rw [barnesLadderCoefficient, if_pos hn, mul_zero]
  · rw [if_neg hn]
    have hw : conePeriod ω n ≠ 0 := conePeriod_ne_zero ω hω hn
    have hw' : conePeriod ω (n + Pi.single j 1) ≠ 0 :=
      conePeriod_ne_zero ω hω (add_single_ne_zero n j)
    rw [barnesAtom_shift_sub_eq_geom ω hn j z hw hw' (hpole _ (add_single_ne_zero n j)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = k + 1 + m := by
      have := Finset.mem_range.mp hk
      exact ⟨Fintype.card ι - k - 1, by omega⟩
    exact barnesLadderTerm_eq ω hn j z hw hw' hm

/-! ## The correction is a polynomial -/

/-- **The ladder correction is a polynomial.**  Off the zero exponent vector the correction series
is a polynomial in the argument whose coefficients are convergent sums over the cone. -/
theorem tsum_barnesLadderCorrection_eq (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (j : ι) {z : ℂ}
    (hpole : ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + z ≠ 0) :
    (∑' n : ι → ℕ, (barnesAtom ω n (z + ω j) - barnesAtom ω (n + Pi.single j 1) z)) =
      -barnesAtom ω (Pi.single j 1) z +
        ∑ k ∈ Finset.range (Fintype.card ι),
          ((-1) ^ (Fintype.card ι - 1) * (z + ω j) ^ k * z ^ (Fintype.card ι - 1 - k)) *
            ∑' n : ι → ℕ, barnesLadderCoefficient ω j k n := by
  have hsummable : Summable fun n : ι → ℕ =>
      barnesAtom ω n (z + ω j) - barnesAtom ω (n + Pi.single j 1) z :=
    (summable_barnesAtom ω hω (z + ω j)).sub (summable_barnesAtom_add_single ω hω z j)
  have hzeroterm : barnesAtom ω (0 : ι → ℕ) (z + ω j) -
      barnesAtom ω ((0 : ι → ℕ) + Pi.single j 1) z = -barnesAtom ω (Pi.single j 1) z := by
    rw [barnesAtom, if_pos rfl, zero_add, zero_sub]
  rw [Summable.tsum_eq_add_tsum_ite hsummable (0 : ι → ℕ), hzeroterm,
    tsum_congr (barnesLadderCorrection_term ω hω j hpole),
    Summable.tsum_finsetSum (fun k hk => (summable_barnesLadderCoefficient ω hω j
      (Finset.mem_range.mp hk)).mul_left _)]
  refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
  rw [tsum_mul_left]

end

end GaloisForLFunctions
