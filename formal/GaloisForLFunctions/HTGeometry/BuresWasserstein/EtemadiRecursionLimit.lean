import GaloisForLFunctions.HTGeometry.BuresWasserstein.EtemadiWeightRecursion
import GaloisForLFunctions.HTGeometry.EtemadiWeightedAverage

/-!
# The Etemadi recursion converges to the Cesàro limit of its driving sequence

Combining the weighted-average form of the recursion

`sₙ = (1 - α/n) sₙ₋₁ + (α/n) bₙ₋₁`,  `0 < α < 1`,

with Etemadi's weighted extension of the Cesàro limit gives: if the Cesàro averages of `b`
converge to `b₀`, then `sₙ → b₀`.

The two Etemadi conditions are verified outright for the weights of the recursion: they are
antitone, so the total-variation condition is automatic, and the boundary condition reduces to
`∏_{j≤n}(1 - α/j) ≤ 1 - α`, which holds from the first factor on.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry.BuresWasserstein

open GaloisForLFunctions.HTGeometry.Etemadi

variable {α : ℝ}

/-- From the first factor on the product is at most `1 - α`. -/
lemma etemadiProd_succ_le (hα : 0 ≤ α) (hα1 : α < 1) :
    ∀ n : ℕ, etemadiProd α (n + 1) ≤ 1 - α
  | 0 => by
    rw [etemadiProd_succ]
    norm_num
  | n + 1 => by
    rw [etemadiProd_succ]
    have hP : etemadiProd α (n + 1) ≤ 1 - α := etemadiProd_succ_le hα hα1 n
    have hPpos : 0 < etemadiProd α (n + 1) := etemadiProd_pos hα1 (n + 1)
    have h1 : (1 : ℝ) - α / (((n + 1 : ℕ) : ℝ) + 1) ≤ 1 := by
      have hnn : (0 : ℝ) ≤ α / (((n + 1 : ℕ) : ℝ) + 1) := by positivity
      linarith
    calc etemadiProd α (n + 1) * (1 - α / (((n + 1 : ℕ) : ℝ) + 1))
        ≤ etemadiProd α (n + 1) * 1 := mul_le_mul_of_nonneg_left h1 hPpos.le
      _ = etemadiProd α (n + 1) := mul_one _
      _ ≤ 1 - α := hP

/-- The total weight of the recursion, without the initial datum. -/
lemma totalWeight_etemadi (hα1 : α < 1) (n : ℕ) :
    totalWeight (etemadiWeight α) n = etemadiTotal α n - 1 := by
  have h := etemadiTotal_eq hα1 n
  unfold totalWeight
  linarith

/-- **The first Etemadi condition** for the weights of the recursion, with constant one. -/
lemma etemadi_weight_cond (hα : 0 < α) (hα1 : α < 1) (n : ℕ) :
    (n : ℝ) * etemadiWeight α (n - 1) ≤ 1 * totalWeight (etemadiWeight α) n := by
  rcases n with _ | m
  · simp [totalWeight]
  · have hP : 0 < etemadiProd α (m + 1) := etemadiProd_pos hα1 (m + 1)
    have hPle : etemadiProd α (m + 1) ≤ 1 - α := etemadiProd_succ_le hα.le hα1 m
    have hsum : totalWeight (etemadiWeight α) (m + 1) = (etemadiProd α (m + 1))⁻¹ - 1 := by
      have h := etemadiTotal_eq hα1 (m + 1)
      unfold etemadiTotal at h
      unfold totalWeight
      linarith
    have hlhs : ((m + 1 : ℕ) : ℝ) * etemadiWeight α m = α / etemadiProd α (m + 1) := by
      unfold etemadiWeight
      have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
      push_cast
      field_simp
    simp only [Nat.add_sub_cancel]
    rw [hlhs, hsum, one_mul, div_le_iff₀ hP]
    have hexp : ((etemadiProd α (m + 1))⁻¹ - 1) * etemadiProd α (m + 1)
        = 1 - etemadiProd α (m + 1) := by
      field_simp
    rw [hexp]
    linarith

/-- **The recursion converges to the Cesàro limit of its driving sequence.** -/
theorem tendsto_of_etemadiRecursion (hα : 0 < α) (hα1 : α < 1) {s b : ℕ → ℝ} {b₀ : ℝ}
    (hs : ∀ n : ℕ, s (n + 1) = (1 - α / (n + 1)) * s n + (α / (n + 1)) * b n)
    (hb : Tendsto (fun n : ℕ => partialSum b n / (n : ℝ)) atTop (𝓝 b₀)) :
    Tendsto s atTop (𝓝 b₀) := by
  have hwpos : ∀ n, 0 < etemadiWeight α n := fun n => etemadiWeight_pos hα hα1 n
  have hanti : Antitone (etemadiWeight α) := etemadiWeight_antitone hα hα1
  have hTnn : ∀ n, 0 ≤ totalWeight (etemadiWeight α) n := fun n =>
    Finset.sum_nonneg fun i _ => (hwpos i).le
  have hTtop : Tendsto (totalWeight (etemadiWeight α)) atTop atTop := by
    have h := etemadiTotal_tendsto_atTop hα hα1
    have h2 : Tendsto (fun n => etemadiTotal α n + (-1)) atTop atTop :=
      tendsto_atTop_add_const_right _ (-1) h
    refine h2.congr fun n => ?_
    rw [totalWeight_etemadi hα1 n]
    ring
  have hA : Tendsto (fun n => (∑ i ∈ Finset.range n, etemadiWeight α i * b i)
      / totalWeight (etemadiWeight α) n) atTop (𝓝 b₀) :=
    tendsto_weightedAverage_of_antitone hwpos hanti hTtop (etemadi_weight_cond hα hα1) hb
  have h1Ttop : Tendsto (fun n => 1 + totalWeight (etemadiWeight α) n) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 hTtop
  -- the recursion as a weighted average
  have hrec : ∀ n, s n = (s 0 + ∑ i ∈ Finset.range n, etemadiWeight α i * b i)
      / (1 + totalWeight (etemadiWeight α) n) := by
    intro n
    have h := etemadi_recursion hα1 hs n
    have hP : 0 < etemadiProd α n := etemadiProd_pos hα1 n
    have h1 : 1 + totalWeight (etemadiWeight α) n = (etemadiProd α n)⁻¹ := by
      rw [totalWeight_etemadi hα1 n]
      unfold etemadiTotal
      ring
    have hPne : etemadiProd α n ≠ 0 := ne_of_gt hP
    rw [h, h1]
    field_simp
  -- the two limits
  have hzero : Tendsto (fun n => s 0 / (1 + totalWeight (etemadiWeight α) n)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds h1Ttop
  have hratio : Tendsto (fun n => totalWeight (etemadiWeight α) n
      / (1 + totalWeight (etemadiWeight α) n)) atTop (𝓝 1) := by
    have h2 : Tendsto (fun n => 1 - 1 / (1 + totalWeight (etemadiWeight α) n))
        atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub (Filter.Tendsto.div_atTop tendsto_const_nhds h1Ttop)
    rw [sub_zero] at h2
    refine h2.congr fun n => ?_
    have hpos : (0 : ℝ) < 1 + totalWeight (etemadiWeight α) n := by
      have := hTnn n; linarith
    field_simp
    ring
  have hlim : Tendsto (fun n => s 0 / (1 + totalWeight (etemadiWeight α) n)
      + ((∑ i ∈ Finset.range n, etemadiWeight α i * b i)
          / totalWeight (etemadiWeight α) n)
        * (totalWeight (etemadiWeight α) n / (1 + totalWeight (etemadiWeight α) n)))
      atTop (𝓝 (0 + b₀ * 1)) := hzero.add (hA.mul hratio)
  have heq : ∀ n : ℕ, 1 ≤ n → s 0 / (1 + totalWeight (etemadiWeight α) n)
      + ((∑ i ∈ Finset.range n, etemadiWeight α i * b i)
          / totalWeight (etemadiWeight α) n)
        * (totalWeight (etemadiWeight α) n / (1 + totalWeight (etemadiWeight α) n)) = s n := by
    intro n hn
    have hTpos : 0 < totalWeight (etemadiWeight α) n := by
      unfold totalWeight
      exact Finset.sum_pos (fun i _ => hwpos i) ⟨0, Finset.mem_range.mpr hn⟩
    have hpos : (0 : ℝ) < 1 + totalWeight (etemadiWeight α) n := by linarith
    rw [hrec n]
    field_simp
  have hfinal : Tendsto s atTop (𝓝 (0 + b₀ * 1)) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact heq n hn
  simpa using hfinal

end GaloisForLFunctions.HTGeometry.BuresWasserstein
