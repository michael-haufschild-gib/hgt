import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-!
# The grouped alternating harmonic series

The pairwise-grouped alternating harmonic series sums to `log 2`:

```
∑_{k ≥ 0} (1/(2k+1) - 1/(2k+2)) = log 2.
```

Mathlib carries the harmonic numbers and the Euler--Mascheroni limit `harmonic n - log (n+1) → γ`
but not this value.  The partial sums telescope to `harmonic (2n) - harmonic n`, and writing that
as the difference of two Euler--Mascheroni increments cancels `γ` and leaves
`log (2n+1) - log (n+1) → log 2`.

Grouping is essential: the ungrouped alternating series is only conditionally convergent, whereas
the grouped terms `1/((2k+1)(2k+2))` are positive and summable, so the value is a genuine `HasSum`.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- The `k`-th grouped term `1/(2k+1) - 1/(2k+2)`. -/
noncomputable def alternatingHarmonicPair (k : ℕ) : ℝ :=
  1 / (2 * (k : ℝ) + 1) - 1 / (2 * (k : ℝ) + 2)

theorem alternatingHarmonicPair_eq (k : ℕ) :
    alternatingHarmonicPair k = 1 / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) := by
  have h1 : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < 2 * (k : ℝ) + 2 := by positivity
  rw [alternatingHarmonicPair]
  field_simp
  ring

theorem alternatingHarmonicPair_pos (k : ℕ) : 0 < alternatingHarmonicPair k := by
  rw [alternatingHarmonicPair_eq]
  positivity

/-- The partial sums telescope into a difference of harmonic numbers. -/
theorem sum_alternatingHarmonicPair_eq (n : ℕ) :
    ∑ k ∈ Finset.range n, alternatingHarmonicPair k
      = (harmonic (2 * n) : ℝ) - (harmonic n : ℝ) := by
  induction n with
  | zero => simp [harmonic_zero]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have h2 : 2 * (n + 1) = (2 * n + 1) + 1 := by ring
      rw [h2, harmonic_succ, harmonic_succ, harmonic_succ]
      push_cast
      rw [alternatingHarmonicPair]
      have h1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
      have h2' : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
      have h3 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      field_simp
      ring

/-- The harmonic difference tends to `log 2`. -/
theorem tendsto_harmonic_two_mul_sub_harmonic :
    Tendsto (fun n : ℕ => (harmonic (2 * n) : ℝ) - (harmonic n : ℝ)) atTop
      (𝓝 (Real.log 2)) := by
  have hbase := Real.tendsto_harmonic_sub_log_add_one
  have hdouble : Tendsto (fun n : ℕ => (harmonic (2 * n) : ℝ) - Real.log (2 * (n : ℝ) + 1))
      atTop (𝓝 Real.eulerMascheroniConstant) := by
    have hcomp := hbase.comp (tendsto_atTop_atTop_of_monotone
      (fun a b hab => Nat.mul_le_mul_left 2 hab)
      (fun b => ⟨b, by omega⟩) : Tendsto (fun n : ℕ => 2 * n) atTop atTop)
    refine hcomp.congr fun n => ?_
    simp only [Function.comp_apply]
    push_cast
    ring_nf
  have hlogratio : Tendsto (fun n : ℕ => Real.log (2 * (n : ℝ) + 1) - Real.log ((n : ℝ) + 1))
      atTop (𝓝 (Real.log 2)) := by
    have hquot : ∀ n : ℕ, Real.log (2 * (n : ℝ) + 1) - Real.log ((n : ℝ) + 1)
        = Real.log ((2 * (n : ℝ) + 1) / ((n : ℝ) + 1)) := by
      intro n
      rw [Real.log_div (by positivity) (by positivity)]
    have hratio : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 2) := by
      have hrw : ∀ n : ℕ, (2 * (n : ℝ) + 1) / ((n : ℝ) + 1) = 2 - 1 / ((n : ℝ) + 1) := by
        intro n
        have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        field_simp
        ring
      have hinv : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa [hrw] using (tendsto_const_nhds (x := (2 : ℝ))).sub hinv
    have := (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp hratio
    exact (this.congr fun n => (hquot n).symm)
  have hsplit : ∀ n : ℕ, (harmonic (2 * n) : ℝ) - (harmonic n : ℝ)
      = ((harmonic (2 * n) : ℝ) - Real.log (2 * (n : ℝ) + 1))
        - ((harmonic n : ℝ) - Real.log ((n : ℝ) + 1))
        + (Real.log (2 * (n : ℝ) + 1) - Real.log ((n : ℝ) + 1)) := by
    intro n
    ring
  have hbase' : Tendsto (fun n : ℕ => (harmonic n : ℝ) - Real.log ((n : ℝ) + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    refine hbase.congr fun n => ?_
    ring
  have hcomb := ((hdouble.sub hbase').add hlogratio)
  simpa [hsplit] using hcomb.congr fun n => (hsplit n).symm

theorem summable_alternatingHarmonicPair : Summable alternatingHarmonicPair := by
  have hmaj : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    have h := (Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two
    refine ((summable_nat_add_iff 1).2 h).congr fun k => ?_
    push_cast
    ring_nf
  refine Summable.of_nonneg_of_le (fun k => (alternatingHarmonicPair_pos k).le)
    (fun k => ?_) hmaj
  rw [alternatingHarmonicPair_eq, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- **The grouped alternating harmonic series.** -/
theorem hasSum_alternatingHarmonicPair :
    HasSum alternatingHarmonicPair (Real.log 2) := by
  refine (summable_alternatingHarmonicPair.hasSum_iff_tendsto_nat).mpr ?_
  refine tendsto_harmonic_two_mul_sub_harmonic.congr fun n => ?_
  exact (sum_alternatingHarmonicPair_eq n).symm

theorem tsum_alternatingHarmonicPair :
    ∑' k : ℕ, alternatingHarmonicPair k = Real.log 2 :=
  hasSum_alternatingHarmonicPair.tsum_eq

end GaloisForLFunctions.HTGeometry
