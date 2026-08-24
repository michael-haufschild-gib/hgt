import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicCancellation
import GaloisForLFunctions.HTGeometry.HypertranscendentalExponentialPencil

/-!
# Uniqueness of a differentially algebraic exponential-pencil parameter

For nonzero entire `W` and hypertranscendental entire `h`, at most one parameter `t` makes
`W exp(t h)` differentially algebraic.  Two such parameters would allow cancellation of the first
entire pencil member inside the global meromorphic field, forcing `exp((u-t)h)` to be DA, contrary
to the exact exponential hypertranscendence equivalence.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

def entireExponentialPencil (W h : ℂ → ℂ) (t : ℂ) (z : ℂ) : ℂ :=
  W z * Complex.exp (t * h z)

theorem analyticOnNhd_entireExponentialPencil {W h : ℂ → ℂ}
    (hW : AnalyticOnNhd ℂ W Set.univ) (hh : AnalyticOnNhd ℂ h Set.univ) (t : ℂ) :
    AnalyticOnNhd ℂ (entireExponentialPencil W h t) Set.univ :=
  hW.mul ((analyticOnNhd_const.mul hh).cexp)

theorem entireExponentialPencil_ne_zero_value {W h : ℂ → ℂ}
    {z₀ : ℂ} (hW₀ : W z₀ ≠ 0) (t : ℂ) :
    entireExponentialPencil W h t z₀ ≠ 0 :=
  mul_ne_zero hW₀ (Complex.exp_ne_zero _)

theorem differentiallyAlgebraic_entireExponentialPencil_unique
    {W h : ℂ → ℂ}
    (hW : AnalyticOnNhd ℂ W Set.univ)
    (hh : AnalyticOnNhd ℂ h Set.univ)
    (hWne : ∃ z, W z ≠ 0)
    (hHT : Hypertranscendental h)
    {t u : ℂ}
    (ht : DifferentiallyAlgebraic (entireExponentialPencil W h t))
    (hu : DifferentiallyAlgebraic (entireExponentialPencil W h u)) :
    t = u := by
  by_contra htu
  have hdiff : u - t ≠ 0 := sub_ne_zero.mpr (Ne.symm htu)
  let G : ℂ → ℂ := fun z => Complex.exp ((u - t) * h z)
  have hG : AnalyticOnNhd ℂ G Set.univ :=
    (analyticOnNhd_const.mul hh).cexp
  have hrel : ∀ z, entireExponentialPencil W h t z * G z =
      entireExponentialPencil W h u z := by
    intro z
    dsimp [entireExponentialPencil, G]
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  obtain ⟨z₀, hz₀⟩ := hWne
  have hleftne : ∃ z, entireExponentialPencil W h t z ≠ 0 :=
    ⟨z₀, entireExponentialPencil_ne_zero_value hz₀ t⟩
  have hGDA : DifferentiallyAlgebraic G :=
    differentiallyAlgebraic_right_of_mul_eq
      (analyticOnNhd_entireExponentialPencil hW hh t) hG
      (analyticOnNhd_entireExponentialPencil hW hh u) hleftne hrel ht hu
  have hGHT : Hypertranscendental G := by
    simpa [G] using
      (hypertranscendental_cexp_const_mul_iff hh (c := u - t) hdiff).2 hHT
  exact hGHT hGDA

/-- Some real pencil parameter is hypertranscendental; the two parameters `0` and `1` suffice. -/
theorem exists_real_hypertranscendental_entireExponentialPencil
    {W h : ℂ → ℂ}
    (hW : AnalyticOnNhd ℂ W Set.univ)
    (hh : AnalyticOnNhd ℂ h Set.univ)
    (hWne : ∃ z, W z ≠ 0)
    (hHT : Hypertranscendental h) :
    ∃ t : ℝ, Hypertranscendental (entireExponentialPencil W h (t : ℂ)) := by
  by_cases hzero : DifferentiallyAlgebraic (entireExponentialPencil W h 0)
  · refine ⟨1, fun hone => ?_⟩
    have hEq : (0 : ℂ) = 1 :=
      differentiallyAlgebraic_entireExponentialPencil_unique hW hh hWne hHT hzero hone
    norm_num at hEq
  · exact ⟨0, hzero⟩

end

end GaloisForLFunctions.HTGeometry
