import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The Etemadi weight recursion

Kim–Mer–Pálfia (arXiv:2607.29142), Lemma 5.2, rewrites the stochastic-approximation recursion

`sₙ = (1 - α/n) sₙ₋₁ + (α/n) bₙ₋₁`,  `0 < α < 1`,

as a weighted average `sₙ = Wₙ⁻¹ (s₀ + ∑_{i<n} wᵢ bᵢ)` whose weights are monotone and whose total
mass `Wₙ` diverges — exactly the hypotheses of Etemadi's weighted strong law.

Here `∏_{j≤n}(1 - α/j)` is `etemadiProd`, `wᵢ` is `etemadiWeight`, and
`Wₙ = (etemadiProd α n)⁻¹` is `etemadiTotal`.  The identity `Wₙ = 1 + ∑_{i<n} wᵢ` (with the
initial datum `s₀` carrying weight one) is `etemadiTotal_eq`.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

/-- The finite product `∏_{j=1}^{n} (1 - α/j)`. -/
noncomputable def etemadiProd (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => etemadiProd α n * (1 - α / (n + 1))

/-- The Etemadi weight `wᵢ = (α/(i+1)) / ∏_{j=1}^{i+1} (1 - α/j)`. -/
noncomputable def etemadiWeight (α : ℝ) (i : ℕ) : ℝ := (α / (i + 1)) / etemadiProd α (i + 1)

/-- The total weight `Wₙ = (∏_{j=1}^{n} (1 - α/j))⁻¹`. -/
noncomputable def etemadiTotal (α : ℝ) (n : ℕ) : ℝ := (etemadiProd α n)⁻¹

variable {α : ℝ}

@[simp] lemma etemadiProd_zero : etemadiProd α 0 = 1 := rfl

lemma etemadiProd_succ (n : ℕ) :
    etemadiProd α (n + 1) = etemadiProd α n * (1 - α / (n + 1)) := rfl

lemma one_sub_div_pos (hα1 : α < 1) (n : ℕ) : 0 < 1 - α / (n + 1) := by
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have : α / (n + 1) < 1 := by
    rw [div_lt_one h1]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  linarith

lemma etemadiProd_pos (hα1 : α < 1) : ∀ n, 0 < etemadiProd α n
  | 0 => by simp
  | n + 1 => by
    rw [etemadiProd_succ]
    exact mul_pos (etemadiProd_pos hα1 n) (one_sub_div_pos hα1 n)

lemma etemadiProd_le_one (hα : 0 ≤ α) (hα1 : α < 1) : ∀ n, etemadiProd α n ≤ 1
  | 0 => by simp
  | n + 1 => by
    rw [etemadiProd_succ]
    have h1 : (1 : ℝ) - α / (n + 1) ≤ 1 := by
      have : (0 : ℝ) ≤ α / (n + 1) := by positivity
      linarith
    calc etemadiProd α n * (1 - α / (n + 1)) ≤ etemadiProd α n * 1 :=
          mul_le_mul_of_nonneg_left h1 (etemadiProd_pos hα1 n).le
      _ ≤ 1 := by simpa using etemadiProd_le_one hα hα1 n

lemma etemadiWeight_pos (hα : 0 < α) (hα1 : α < 1) (i : ℕ) : 0 < etemadiWeight α i := by
  unfold etemadiWeight
  have h1 : (0 : ℝ) < (i : ℝ) + 1 := by positivity
  exact div_pos (by positivity) (etemadiProd_pos hα1 (i + 1))

/-- **The recursion as a weighted average.** -/
theorem etemadi_recursion (hα1 : α < 1) {s b : ℕ → ℝ}
    (hs : ∀ n : ℕ, s (n + 1) = (1 - α / (n + 1)) * s n + (α / (n + 1)) * b n) :
    ∀ n : ℕ, s n = etemadiProd α n * (s 0 + ∑ i ∈ Finset.range n, etemadiWeight α i * b i)
  | 0 => by simp
  | n + 1 => by
    have hPpos : 0 < etemadiProd α (n + 1) := etemadiProd_pos hα1 (n + 1)
    have hw : etemadiProd α n * (1 - α / ((n : ℝ) + 1)) * etemadiWeight α n
        = α / ((n : ℝ) + 1) := by
      unfold etemadiWeight
      rw [← etemadiProd_succ]
      field_simp
    rw [hs n, etemadi_recursion hα1 hs n, Finset.sum_range_succ, etemadiProd_succ]
    linear_combination (-(b n)) * hw

/-- **Total weight identity**: `Wₙ = 1 + ∑_{i<n} wᵢ`, the initial datum carrying weight one. -/
theorem etemadiTotal_eq (hα1 : α < 1) :
    ∀ n : ℕ, etemadiTotal α n = 1 + ∑ i ∈ Finset.range n, etemadiWeight α i
  | 0 => by simp [etemadiTotal]
  | n + 1 => by
    have hPn : 0 < etemadiProd α n := etemadiProd_pos hα1 n
    have hPn1 : 0 < etemadiProd α (n + 1) := etemadiProd_pos hα1 (n + 1)
    have hne : ((n : ℝ) + 1) - α ≠ 0 := by
      have := one_sub_div_pos hα1 n
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : α / ((n : ℝ) + 1) < 1 := by linarith
      rw [div_lt_one h1] at h2
      linarith
    rw [Finset.sum_range_succ, ← add_assoc, ← etemadiTotal_eq hα1 n]
    unfold etemadiTotal etemadiWeight
    rw [etemadiProd_succ]
    field_simp
    ring

/-- The weights are decreasing. -/
theorem etemadiWeight_antitone (hα : 0 < α) (hα1 : α < 1) : Antitone (etemadiWeight α) := by
  refine antitone_nat_of_succ_le fun i => ?_
  have hPn1 : 0 < etemadiProd α (i + 1) := etemadiProd_pos hα1 (i + 1)
  have hf : (0 : ℝ) < 1 - α / ((i : ℝ) + 1 + 1) := by
    have := one_sub_div_pos hα1 (i + 1)
    push_cast at this ⊢
    linarith
  have hi : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  unfold etemadiWeight
  rw [etemadiProd_succ]
  push_cast
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hkey : α / ((i : ℝ) + 1 + 1) ≤ α / ((i : ℝ) + 1) * (1 - α / ((i : ℝ) + 1 + 1)) := by
    rw [← sub_nonneg]
    have hdiff : α / ((i : ℝ) + 1) * (1 - α / ((i : ℝ) + 1 + 1)) - α / ((i : ℝ) + 1 + 1)
        = (α * (1 - α)) / (((i : ℝ) + 1) * ((i : ℝ) + 1 + 1)) := by
      field_simp
      ring
    rw [hdiff]
    apply div_nonneg (by nlinarith [hα, hα1]) (by positivity)
  nlinarith [hPn1, hkey]

/-- The total weight diverges. -/
theorem etemadiTotal_tendsto_atTop (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (etemadiTotal α) atTop atTop := by
  have hlb : ∀ n : ℕ, 1 + α * (∑ i ∈ Finset.range n, (1 : ℝ) / (i + 1)) ≤ etemadiTotal α n := by
    intro n
    rw [etemadiTotal_eq hα1 n, Finset.mul_sum]
    refine add_le_add le_rfl (Finset.sum_le_sum fun i _ => ?_)
    have hPle : etemadiProd α (i + 1) ≤ 1 := etemadiProd_le_one hα.le hα1 (i + 1)
    have hPpos : 0 < etemadiProd α (i + 1) := etemadiProd_pos hα1 (i + 1)
    have hi : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    unfold etemadiWeight
    rw [le_div_iff₀ hPpos]
    calc α * ((1 : ℝ) / (i + 1)) * etemadiProd α (i + 1)
        ≤ α * ((1 : ℝ) / (i + 1)) * 1 := by
          exact mul_le_mul_of_nonneg_left hPle (by positivity)
      _ = α / (i + 1) := by ring
  refine tendsto_atTop_mono hlb ?_
  exact tendsto_atTop_add_const_left _ 1
    (Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop hα)

end GaloisForLFunctions.HTGeometry.BuresWasserstein
