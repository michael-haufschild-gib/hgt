import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic

/-!
# Full three-frequency Schwartz lattice domination

A finite Schwartz seminorm controls the independently weighted integer triple.
No relation among the three coordinates and no summability premise is imposed.
-/

noncomputable section
open Filter Set
open scoped BigOperators Topology SchwartzMap
namespace RHTower.BAGTrace

/-- Three independent frequencies, with no resonance restriction. -/
def ramanujanTripleWeight (x : ℝ × ℝ × ℝ) : ℝ :=
  (1 + |x.1|) * (1 + |x.2.1|) * (1 + |x.2.2|)

def ramanujanTripleLattice (n : ℤ × ℤ × ℤ) : ℝ × ℝ × ℝ :=
  (n.1, n.2.1, n.2.2)

def ramanujanTripleSeminorm : Seminorm ℂ (𝓢(ℝ × ℝ × ℝ, ℂ)) :=
  (Finset.Iic (9, 0)).sup (fun m => SchwartzMap.seminorm ℂ m.1 m.2)

private theorem tripleWeight_pos (x : ℝ × ℝ × ℝ) : 0 < ramanujanTripleWeight x := by
  unfold ramanujanTripleWeight
  positivity

private theorem tripleWeight_le (x : ℝ × ℝ × ℝ) :
    ramanujanTripleWeight x ≤ (1 + ‖x‖)^3 := by
  have h1 : |x.1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le x
  have h2 : |x.2.1| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using (norm_fst_le x.2).trans (norm_snd_le x)
  have h3 : |x.2.2| ≤ ‖x‖ := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le x.2).trans (norm_snd_le x)
  calc
    _ ≤ (1 + ‖x‖) * (1 + ‖x‖) * (1 + ‖x‖) := by
      unfold ramanujanTripleWeight
      gcongr
    _ = _ := by ring

/-- Explicit finite-seminorm domination of the full three-frequency lattice. -/
theorem ramanujanTripleSchwartz_weighted_le
    (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) (x : ℝ × ℝ × ℝ) :
    ‖Φ x‖ * ramanujanTripleWeight x ≤
      (2^9 * ramanujanTripleSeminorm Φ) / (ramanujanTripleWeight x)^2 := by
  have hw := tripleWeight_pos x
  apply (le_div_iff₀ (pow_pos hw 2)).mpr
  have hs := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ)
    (m := (9,0)) (k := 9) (n := 0) le_rfl le_rfl Φ x
  simp only [norm_iteratedFDeriv_zero] at hs
  have hp := pow_le_pow_left₀ hw.le (tripleWeight_le x) 3
  calc
    _ = (ramanujanTripleWeight x)^3 * ‖Φ x‖ := by ring
    _ ≤ ((1 + ‖x‖)^3)^3 * ‖Φ x‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
    _ = (1 + ‖x‖)^9 * ‖Φ x‖ := by ring
    _ ≤ _ := hs

private theorem summable_lattice_reciprocal :
    Summable (fun n : ℤ => 1 / (1 + |(n : ℝ)|)^2) := by
  have hnat : Summable (fun n : ℕ => 1 / (1 + (n : ℝ))^2) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    simpa only [Real.rpow_two, sq_abs, add_comm] using h
  rw [summable_int_iff_summable_nat_and_neg]
  simpa using And.intro hnat hnat

private theorem summable_triple_reciprocal :
    Summable (fun n : ℤ × ℤ × ℤ => 1 / (ramanujanTripleWeight (ramanujanTripleLattice n))^2) := by
  let b : ℤ → ℝ := fun n => 1 / (1 + |(n : ℝ)|)^2
  have hb : Summable b := summable_lattice_reciprocal
  have hb0 : 0 ≤ b := fun n => by dsimp [b]; positivity
  have hbb := hb.mul_of_nonneg hb hb0 hb0
  have h := hb.mul_of_nonneg hbb hb0 (fun n => mul_nonneg (hb0 _) (hb0 _))
  apply h.congr
  intro n
  dsimp [b, ramanujanTripleWeight, ramanujanTripleLattice]
  simp only [mul_pow, one_div, mul_inv_rev]
  ring

/-- Absolute summability is proved for every Schwartz test, not supplied as a premise. -/
theorem summable_ramanujanTripleSchwartz_weighted (Φ : 𝓢(ℝ × ℝ × ℝ, ℂ)) :
    Summable (fun n : ℤ × ℤ × ℤ =>
      ‖Φ (ramanujanTripleLattice n)‖ * ramanujanTripleWeight (ramanujanTripleLattice n)) := by
  have hmajor := summable_triple_reciprocal.mul_left (2^9 * ramanujanTripleSeminorm Φ)
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (norm_nonneg _) (tripleWeight_pos _).le) (fun n => ?_) hmajor
  simpa only [mul_one_div] using ramanujanTripleSchwartz_weighted_le Φ (ramanujanTripleLattice n)


/-- The complete weighted lattice sum is controlled by one fixed finite
Schwartz seminorm, with a constant independent of the input test. -/
theorem ramanujanTripleSchwartz_weighted_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ Φ : 𝓢(ℝ × ℝ × ℝ, ℂ),
      (∑' n : ℤ × ℤ × ℤ, ‖Φ (ramanujanTripleLattice n)‖ *
        ramanujanTripleWeight (ramanujanTripleLattice n)) ≤ C*ramanujanTripleSeminorm Φ := by
  let W : ℝ := ∑' n : ℤ × ℤ × ℤ, 1/(ramanujanTripleWeight (ramanujanTripleLattice n))^2
  have hW : 0 ≤ W := tsum_nonneg (fun n => by positivity)
  refine ⟨2^9*W+1,by positivity,fun Φ => ?_⟩
  have hmajor := summable_triple_reciprocal.mul_left (2^9*ramanujanTripleSeminorm Φ)
  calc
    _ ≤ ∑' n : ℤ × ℤ × ℤ, (2^9*ramanujanTripleSeminorm Φ)*
        (1/(ramanujanTripleWeight (ramanujanTripleLattice n))^2) :=
      (summable_ramanujanTripleSchwartz_weighted Φ).tsum_le_tsum
        (fun n => by
          simpa only [mul_one_div] using
            (ramanujanTripleSchwartz_weighted_le Φ (ramanujanTripleLattice n))) hmajor
    _ = (2^9*W)*ramanujanTripleSeminorm Φ := by rw [tsum_mul_left]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (apply_nonneg _ _)

end RHTower.BAGTrace
