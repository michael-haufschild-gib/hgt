import GaloisForLFunctions.RHTower.Sieve.FibreDiagonalExplicit

/-!
# The reduction closes on the off-diagonal

Assembling the split, the symmetry and the explicit diagonal bound:

```text
AveragedMeanSquare f hh    ⟸    the off-diagonal is `o(h²√x)` ,
```

for any unit-bounded `f` and any window law with `hh → ∞`.  The diagonal contributes at most
`(3/2)/h + 6/√x` to the normalised quantity, which vanishes unconditionally.

Together with the corpus's `averagedShortInterval_of_meanSquare` and
`MRBilinear_moebius_of_averaged`, this reduces `MRBilinear μ hh` — and with it the two Route E
sign-density theorems — to the single statement that the triangular-weighted average of binary
correlations of `μ` over shifts `1 ≤ k ≲ h` is `o(h²√x)`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset Filter Topology

/-- The off-diagonal half of the fibre mean square, normalised. -/
def OffDiagonalVanishes (f : ℕ → ℝ) (hh : ℝ → ℝ) : Prop :=
  Tendsto (fun x : ℝ =>
      (2 * ∑ m ∈ Finset.Icc 1 ⌊x + hh x * Real.sqrt x⌋₊,
          ∑ n ∈ (Finset.Icc 1 ⌊x + hh x * Real.sqrt x⌋₊).filter (fun n => n < m),
            f m * f n
              * (((outerBlock x (hh x)).filter
                  (fun a => m ∈ innerFibre x (hh x) a ∧ n ∈ innerFibre x (hh x) a)).card : ℝ))
        / (hh x ^ (2 : ℕ) * Real.sqrt x)) atTop (𝓝 0)

/-- **The reduction closes.** -/
theorem averagedMeanSquare_of_offDiagonal {f : ℕ → ℝ} (hf : ∀ n, |f n| ≤ 1) {hh : ℝ → ℝ}
    (hgrow : Tendsto hh atTop atTop) (hoff : OffDiagonalVanishes f hh) :
    AveragedMeanSquare f hh := by
  classical
  -- the diagonal's normalised majorant
  have hmaj : Tendsto (fun x : ℝ => (3 / 2) / hh x + 6 / Real.sqrt x) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (3 / 2 : ℝ) / hh x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hgrow
    have h2 : Tendsto (fun x : ℝ => (6 : ℝ) / Real.sqrt x) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_sqrt_atTop
    have := h1.add h2
    simpa using this
  -- the diagonal, normalised, is squeezed by it
  have hdiag : Tendsto (fun x : ℝ =>
      (∑ m ∈ Finset.Icc 1 ⌊x + hh x * Real.sqrt x⌋₊,
          f m * f m
            * (((outerBlock x (hh x)).filter
                (fun a => m ∈ innerFibre x (hh x) a ∧ m ∈ innerFibre x (hh x) a)).card : ℝ))
        / (hh x ^ (2 : ℕ) * Real.sqrt x)) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [Filter.eventually_ge_atTop (4 : ℝ), hgrow.eventually_ge_atTop 1]
        with x hx hhx
      have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
      have hnum : (0 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 ⌊x + hh x * Real.sqrt x⌋₊,
          f m * f m
            * (((outerBlock x (hh x)).filter
                (fun a => m ∈ innerFibre x (hh x) a ∧ m ∈ innerFibre x (hh x) a)).card : ℝ) := by
        refine Finset.sum_nonneg fun m _ => ?_
        have hK : (0 : ℝ) ≤ (((outerBlock x (hh x)).filter
            (fun a => m ∈ innerFibre x (hh x) a ∧ m ∈ innerFibre x (hh x) a)).card : ℝ) :=
          Nat.cast_nonneg _
        nlinarith [hK, sq_nonneg (f m)]
      have hden : (0 : ℝ) ≤ hh x ^ (2 : ℕ) * Real.sqrt x := by positivity
      exact div_nonneg hnum hden
    · filter_upwards [Filter.eventually_ge_atTop (4 : ℝ), hgrow.eventually_ge_atTop 1]
        with x hx hhx
      have hs0 : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
      have hs1 : (1 : ℝ) ≤ Real.sqrt x := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by linarith)
      have hbase := fibre_diag_sum_explicit_le (f := f) hf hx (by linarith : (0 : ℝ) ≤ hh x)
      have hden : (0 : ℝ) < hh x ^ (2 : ℕ) * Real.sqrt x := by positivity
      rw [div_le_iff₀ hden]
      have hcrude : (Real.sqrt x / 2 + hh x + 1) * (2 * hh x + 1)
          ≤ ((3 / 2) / hh x + 6 / Real.sqrt x) * (hh x ^ (2 : ℕ) * Real.sqrt x) := by
        have hprod : ((3 / 2) / hh x + 6 / Real.sqrt x) * (hh x ^ (2 : ℕ) * Real.sqrt x)
            = (3 / 2) * hh x * Real.sqrt x + 6 * hh x ^ (2 : ℕ) := by
          field_simp
        rw [hprod]
        nlinarith [hhx, hs1, hs0]
      linarith [hbase, hcrude]
  -- assemble
  have hsplit : ∀ x : ℝ,
      (∑ a ∈ outerBlock x (hh x), (∑ b ∈ innerFibre x (hh x) a, f b) ^ (2 : ℕ))
          / (hh x ^ (2 : ℕ) * Real.sqrt x)
        = (∑ m ∈ Finset.Icc 1 ⌊x + hh x * Real.sqrt x⌋₊,
              f m * f m
                * (((outerBlock x (hh x)).filter
                    (fun a => m ∈ innerFibre x (hh x) a
                      ∧ m ∈ innerFibre x (hh x) a)).card : ℝ))
              / (hh x ^ (2 : ℕ) * Real.sqrt x)
          + (2 * ∑ m ∈ Finset.Icc 1 ⌊x + hh x * Real.sqrt x⌋₊,
                ∑ n ∈ (Finset.Icc 1 ⌊x + hh x * Real.sqrt x⌋₊).filter (fun n => n < m),
                  f m * f n
                    * (((outerBlock x (hh x)).filter
                        (fun a => m ∈ innerFibre x (hh x) a
                          ∧ n ∈ innerFibre x (hh x) a)).card : ℝ))
              / (hh x ^ (2 : ℕ) * Real.sqrt x) := by
    intro x
    rw [sum_fibreSq_diag_split f x (hh x),
      sum_offdiag_eq_two_mul (T := Finset.Icc 1 ⌊x + hh x * Real.sqrt x⌋₊)
        (g := fun m n => f m * f n
          * (((outerBlock x (hh x)).filter
              (fun a => m ∈ innerFibre x (hh x) a ∧ n ∈ innerFibre x (hh x) a)).card : ℝ))
        (fun m n => by rw [fibre_kernel_symm x (hh x) m n]; ring)]
    rw [add_div]
  rw [AveragedMeanSquare]
  refine Tendsto.congr (fun x => (hsplit x).symm) ?_
  have := hdiag.add hoff
  simpa using this

end RHTower.Sieve

end
