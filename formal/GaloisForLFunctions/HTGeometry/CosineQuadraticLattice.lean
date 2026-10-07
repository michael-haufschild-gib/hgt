import GaloisForLFunctions.HTGeometry.DiscreteDilationGerm
import Mathlib.Analysis.Complex.Basic

/-! # Exact stabilization of a vanishing correction to an integer-valued quadratic

Third differences remove the quadratic. Closed discreteness of the integer
lattice gives exact zero, and three successive constant-tail arguments
remove the vanishing correction. This is a classical discrete lemma.
-/

namespace GaloisForLFunctions.HTGeometry.CosineQuadraticLattice

open Filter
open scoped Topology

noncomputable section

def difference (f : ℕ → ℂ) (n : ℕ) : ℂ := f (n + 1) - f n

theorem difference_limit {f : ℕ → ℂ} {c : ℂ} (hf : Tendsto f atTop (𝓝 c)) :
    Tendsto (difference f) atTop (𝓝 0) := by
  change Tendsto (fun n => f (n + 1) - f n) atTop (𝓝 0)
  convert! (hf.comp (tendsto_add_atTop_nat 1)).sub hf using 1
  simp

theorem eventually_zero_of_difference {f : ℕ → ℂ} (hf : Tendsto f atTop (𝓝 0))
    (hd : ∀ᶠ n in atTop, difference f n = 0) : ∀ᶠ n in atTop, f n = 0 := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hd
  have hconst : ∀ n, N ≤ n → f n = f N := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      exact (sub_eq_zero.mp (hN n hn)).trans ih
  have heq : f =ᶠ[atTop] fun _ => f N := eventually_atTop.mpr ⟨N, hconst⟩
  have hz : f N = 0 := tendsto_nhds_unique tendsto_const_nhds (hf.congr' heq)
  filter_upwards [heq] with n hn
  exact hn.trans hz

theorem difference_integer {f : ℕ → ℂ}
    (hf : ∀ᶠ n in atTop, f n ∈ Set.range (Int.cast : ℤ → ℂ)) :
    ∀ᶠ n in atTop, difference f n ∈ Set.range (Int.cast : ℤ → ℂ) := by
  filter_upwards [(tendsto_add_atTop_nat 1).eventually hf, hf] with n ha hb
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  refine ⟨a - b, ?_⟩
  dsimp [difference]
  push_cast
  rw [ha, hb]

theorem quadratic_difference_cancel (a b c : ℂ) (e : ℕ → ℂ) :
    difference (difference (difference (fun n : ℕ => a * (n : ℂ) ^ 2 + b * n + c + e n))) =
      difference (difference (difference e)) := by
  funext n
  simp only [difference]
  push_cast
  ring

theorem eventually_zero_of_quadratic_integer_values (a b c : ℂ) {e : ℕ → ℂ}
    (he : Tendsto e atTop (𝓝 0))
    (hz : ∀ᶠ (n : ℕ) in atTop, a * (n : ℂ) ^ 2 + b * n + c + e n ∈
      Set.range (Int.cast : ℤ → ℂ)) : ∀ᶠ n in atTop, e n = 0 := by
  have hmem := difference_integer (difference_integer (difference_integer hz))
  rw [quadratic_difference_cancel] at hmem
  have hlim := difference_limit (difference_limit (difference_limit he))
  have hzero := DiscreteDilationGerm.eventually_eq_of_closed_discrete
    Complex.isClosed_range_intCast
    Complex.isClosedEmbedding_intCast.isEmbedding.isInducing.isDiscrete_range hlim hmem
  exact eventually_zero_of_difference he
    (eventually_zero_of_difference (difference_limit he)
      (eventually_zero_of_difference (difference_limit (difference_limit he)) hzero))

end

end GaloisForLFunctions.HTGeometry.CosineQuadraticLattice
