import GaloisForLFunctions.RHTower.AbelTailLSeries
import GaloisForLFunctions.TransHorizonIncidenceMechanics.APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa

/-!
# Ordered Dirichlet sums and the summatory Mellin pairing

The increment series is absolutely summable whenever the summatory source
grows more slowly than the Mellin exponent. Finite Abel summation therefore
identifies the ordered source limit without assuming absolute convergence
of the source series.
-/

noncomputable section

open Finset Filter Topology Complex

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open GaloisForLFunctions.TransHorizonIncidenceMechanics

/-- The step-function Mellin pairing is the shifted Abel increment series. -/
theorem complexMellinPairing_sourcePartialSum_eq {b : ℕ → ℝ} {C θ : ℝ}
    (hC : 0 ≤ C) (hb : ∀ N : ℕ, |RHTower.sourcePartialSum b N| ≤ C * (N : ℝ) ^ θ)
    {s : ℂ} (hs : 0 < s.re) (hθs : θ < s.re) :
    complexMellinPairing (RHTower.sourcePartialSum b) s =
      RHTower.abelTailSeries (RHTower.sourcePartialSum b) s := by
  let F := fun n : ℕ => (RHTower.sourcePartialSum b n : ℂ) * complexMellinCell s n
  have he (k : ℕ) :
      RHTower.coeffPartial (fun i => (b (i + 1) : ℂ)) (k + 1) *
        ((((k : ℝ) + 1 : ℝ) : ℂ) ^ (-s) - (((k : ℝ) + 2 : ℝ) : ℂ) ^ (-s)) = F (k + 1) := by
    rw [RHTower.coeffPartial_ofReal]
    dsimp only [F, complexMellinCell]
    simp only [Nat.cast_add, Nat.cast_one]
    congr 2
    congr 1
    ring
  have hsucc : Summable (fun k : ℕ => F (k + 1)) :=
    (RHTower.summable_abelTail hC hb hs hθs).congr he
  have hsum : Summable F := (summable_nat_add_iff 1).mp hsucc
  have hzero : F 0 = 0 := by simp [F, RHTower.sourcePartialSum]
  change (∑' n : ℕ, F n) = _
  rw [hsum.tsum_eq_zero_add, hzero, zero_add, RHTower.abelTailSeries]
  apply tsum_congr
  intro k
  rw [← he, RHTower.coeffPartial_ofReal]

/-- Ordered Dirichlet sums converge to the Mellin pairing of the summatory
source on every half-plane strictly beyond its power-growth threshold. -/
theorem tendsto_orderedDirichlet_complexMellinPairing {b : ℕ → ℝ} {C θ : ℝ}
    (hC : 0 ≤ C) (hb : ∀ N : ℕ, |RHTower.sourcePartialSum b N| ≤ C * (N : ℝ) ^ θ)
    {s : ℂ} (hs : 0 < s.re) (hθs : θ < s.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, (b n : ℂ) * (n : ℂ) ^ (-s)) atTop
      (𝓝 (complexMellinPairing (RHTower.sourcePartialSum b) s)) := by
  have hr := (RHTower.summable_abelTail hC hb hs hθs).hasSum.tendsto_sum_nat.comp
    (tendsto_sub_atTop_nat 1)
  have h := (RHTower.tendsto_abelTail_boundary hb hθs).add hr
  rw [zero_add] at h
  have h' : Tendsto (fun N : ℕ => ∑ i ∈ range N,
      (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-s) * (b (i + 1) : ℂ)) atTop
      (𝓝 (RHTower.abelTailSeries (RHTower.sourcePartialSum b) s)) := by
    have hconv := h.congr fun N =>
      (RHTower.sum_eq_abelPartial (fun i => (b (i + 1) : ℂ)) s N).symm
    simpa only [RHTower.abelTailSeries, RHTower.coeffPartial_ofReal] using hconv
  rw [← complexMellinPairing_sourcePartialSum_eq hC hb hs hθs] at h'
  refine h'.congr fun N => ?_
  rw [← RHTower.sum_range_succ_eq_sum_Icc (fun n => (b n : ℂ) * (n : ℂ) ^ (-s)) N]
  apply sum_congr rfl
  intro n _
  simp only [Nat.cast_add, Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast,
    Complex.ofReal_one, mul_comm]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
