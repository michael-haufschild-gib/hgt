import GaloisForLFunctions.HTGeometry.BohrSpectrum

/-!
# Simultaneous almost periods of a finite family of characters

A single character is periodic, and two almost-periodic functions have a relatively dense set of
common almost periods.  Iterating that over the coordinates makes the vector of characters attached
to a finite frequency family almost periodic, so its almost periods are relatively dense — in
particular arbitrarily large.

Evaluating an almost period at the origin gives the recurrence statement itself: for any finite
family of real frequencies and any tolerance there are arbitrarily large times at which every
character returns simultaneously to `1`.  This is the simultaneous Dirichlet approximation used by
almost-periodic revival arguments, obtained without any Diophantine input.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions

open HTGeometry

/-- The vector of characters attached to a finite frequency family. -/
def bohrCharVector {n : ℕ} (u : Fin n → ℝ) (t : ℝ) : Fin n → ℂ :=
  fun j => bohrChar (u j) t

theorem continuous_bohrCharVector {n : ℕ} (u : Fin n → ℝ) : Continuous (bohrCharVector u) :=
  continuous_pi fun j => continuous_bohrChar (u j)

theorem bohrCharVector_zero {n : ℕ} (u : Fin n → ℝ) (j : Fin n) : bohrCharVector u 0 j = 1 := by
  rw [bohrCharVector, bohrChar]
  norm_num

/-- **The vector of characters is almost periodic.** -/
theorem isBohrAlmostPeriodic_bohrCharVector :
    ∀ (n : ℕ) (u : Fin n → ℝ), IsBohrAlmostPeriodic (bohrCharVector u) := by
  intro n
  induction n with
  | zero =>
      intro u ε hε
      refine ⟨1, one_pos, fun a => ⟨a, ⟨le_refl a, by linarith⟩, fun x => ?_⟩⟩
      have hzero : bohrCharVector u (x + a) - bohrCharVector u x = 0 := by
        funext j
        exact j.elim0
      rw [hzero, norm_zero]
      exact hε.le
  | succ n ih =>
      intro u ε hε
      obtain ⟨L, hL, hdense⟩ := exists_common_almostPeriods
        (continuous_bohrChar (u 0)) (isBohrAlmostPeriodic_bohrChar (u 0))
        (continuous_bohrCharVector (Fin.tail u)) (ih (Fin.tail u)) hε
      refine ⟨L, hL, fun a => ?_⟩
      obtain ⟨τ, hτmem, h0, hT⟩ := hdense a
      refine ⟨τ, hτmem, fun x => ?_⟩
      rw [pi_norm_le_iff_of_nonneg hε.le]
      intro j
      refine Fin.cases ?_ ?_ j
      · exact h0 x
      · intro i
        have hx := hT x
        rw [pi_norm_le_iff_of_nonneg hε.le] at hx
        exact hx i

/-- **Simultaneous recurrence.**  For any finite family of real frequencies, any tolerance and any
threshold there is a time beyond the threshold at which every character is within the tolerance
of `1`. -/
theorem exists_large_simultaneous_almostPeriod {n : ℕ} (u : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε)
    (R : ℝ) :
    ∃ ξ : ℝ, R ≤ ξ ∧
      ∀ j, ‖Complex.exp (Complex.I * ((ξ : ℂ) * ((u j : ℝ) : ℂ))) - 1‖ ≤ ε := by
  obtain ⟨L, hL, hdense⟩ := isBohrAlmostPeriodic_bohrCharVector n (fun j => -(u j)) ε hε
  obtain ⟨τ, hτmem, hτ⟩ := hdense R
  refine ⟨τ, hτmem.1, fun j => ?_⟩
  have hx := hτ 0
  rw [pi_norm_le_iff_of_nonneg hε.le] at hx
  have hj := hx j
  simp only [Pi.sub_apply, zero_add, bohrCharVector_zero] at hj
  have hval : bohrCharVector (fun j => -(u j)) τ j
      = Complex.exp (Complex.I * ((τ : ℂ) * ((u j : ℝ) : ℂ))) := by
    rw [bohrCharVector, bohrChar]
    push_cast
    ring_nf
  rwa [hval] at hj

/-! ## Atomic revival -/

/-- **The atomic symbol revives.**  At arbitrarily large times the symbol of a finite atomic weight
returns to its total mass, with error controlled by the total absolute mass.  This is the mechanism
behind almost-periodic revival: an atomic convolution cannot converge in operator norm to an
absolutely continuous limit, because its symbol keeps coming back to full strength. -/
theorem exists_large_atomicSymbol_revival {n : ℕ} (u : Fin n → ℝ) (m : Fin n → ℂ)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ ξ : ℝ, R ≤ ξ ∧
      ‖(∑ j, m j * Complex.exp (Complex.I * ((ξ : ℂ) * ((u j : ℝ) : ℂ)))) - ∑ j, m j‖
        ≤ (∑ j, ‖m j‖) * ε := by
  obtain ⟨ξ, hξR, hξ⟩ := exists_large_simultaneous_almostPeriod u hε R
  refine ⟨ξ, hξR, ?_⟩
  have hsub : (∑ j, m j * Complex.exp (Complex.I * ((ξ : ℂ) * ((u j : ℝ) : ℂ)))) - ∑ j, m j
      = ∑ j, m j * (Complex.exp (Complex.I * ((ξ : ℂ) * ((u j : ℝ) : ℂ))) - 1) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsub]
  refine le_trans (norm_sum_le _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hξ j) (norm_nonneg _)

end GaloisForLFunctions
