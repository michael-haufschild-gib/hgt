import GaloisForLFunctions.RHTower.Sieve.VinogradovRationalSeparation
import GaloisForLFunctions.RHTower.Sieve.LargeSieveExpSum

namespace RHTower.Sieve

open scoped BigOperators InnerProductSpace

noncomputable section

theorem finitePhaseProgression_eq_expSum_one (H : ℕ) (x : ℝ) :
    finitePhaseProgression H x = expSum H (fun _ => 1) x := by
  unfold finitePhaseProgression expSum circleFreq finitePhaseChar
  apply Finset.sum_congr rfl
  intro n _
  rw [one_mul, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

def vinogradovSeparatedBlockCost (H q : ℕ) : ℝ :=
  2 * ((H : ℝ) + 2 * (q : ℝ) * (1 + Real.log ((q : ℝ) + 1)))

/-- Fejér mass on one half-denominator block.  Existing separated large
sieve supplies the only analytic estimate; arithmetic separation comes from
`rationalApprox_halfBlock_separated`. -/
theorem sum_finiteFejerKernel_halfBlock_le
    {H q a : ℕ} (hH : H ≠ 0) (hq : 0 < q)
    {α : ℝ} (hcop : Nat.Coprime a q)
    (happrox : |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2)
    (s : Finset ℕ)
    (hdiam : ∀ n ∈ s, ∀ m ∈ s,
      |(n : ℝ) - (m : ℝ)| ≤ (q : ℝ) / 2) :
    (∑ n ∈ s, finiteFejerKernel H (α * (n : ℝ))) ≤
      vinogradovSeparatedBlockCost H q := by
  let δ : ℝ := 1 / (2 * (q : ℝ))
  let c : Fin H → ℂ := fun _ => 1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1R : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hδ0 : 0 < δ := by simp [δ]; positivity
  have hδhalf : δ ≤ (1 : ℝ) / 2 := by
    simp only [δ]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))
      (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hsep : ∀ n ∈ s, ∀ m ∈ s, n ≠ m →
      δ ≤ toIntDist (α * (m : ℝ) - α * (n : ℝ)) := by
    intro n hn m hm hnm
    exact rationalApprox_halfBlock_separated hq hcop happrox hnm.symm
      (by simpa [abs_sub_comm] using hdiam n hn m hm)
  have hlarge := largeSieve_separated_explicit H s
    (fun n : ℕ => α * (n : ℝ)) hδ0 hδhalf hsep (conjVec H c)
  simp_rw [norm_inner_expRow_conjVec H _ c] at hlarge
  rw [norm_sq_conjVec] at hlarge
  have hcenergy : (∑ n : Fin H, ‖c n‖ ^ 2) = (H : ℝ) := by
    simp [c]
  rw [hcenergy] at hlarge
  have hHr : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  have hscale : (0 : ℝ) ≤ 2 / (H : ℝ) := by positivity
  calc
    (∑ n ∈ s, finiteFejerKernel H (α * (n : ℝ))) =
        (2 / (H : ℝ)) *
          ∑ n ∈ s, ‖expSum H c (α * (n : ℝ))‖ ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _
      simp only [finiteFejerKernel, Complex.normSq_eq_norm_sq]
      rw [finitePhaseProgression_eq_expSum_one]
    _ ≤ (2 / (H : ℝ)) *
        (((H : ℝ) + (1 / δ) *
          (1 + Real.log (1 / (2 * δ) + 1))) * (H : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hlarge hscale
    _ = vinogradovSeparatedBlockCost H q := by
      unfold vinogradovSeparatedBlockCost δ
      field_simp

end

end RHTower.Sieve
