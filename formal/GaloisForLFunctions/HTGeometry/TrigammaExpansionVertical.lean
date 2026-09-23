import GaloisForLFunctions.HTGeometry.DigammaExpansionDefect
import GaloisForLFunctions.RHTower.TrigammaVertical

/-!
# The trigamma expansion to any order on a vertical line

The differentiated recurrence is `ψ′(z+1) − ψ′(z) = −1/z²`, so an approximation `Q(1/z)` has defect
`−w² − (Q(w/(1+w)) − Q(w))` with `w = 1/z`: the same general defect as for the digamma, with the
seed `−w²`, which already vanishes to second order.  The induction and the telescoping estimate then
give the trigamma expansion to any prescribed order, uniformly in the abscissa.

The first jet is the pattern for all of them: each polygamma satisfies the same recurrence with an
explicit monomial seed.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The defect of a trigamma approximation is the general defect with seed `-w²`. -/
theorem deriv_digamma_genDefect_eq (Q : Polynomial ℂ) {z : ℂ} (hre : 0 < z.re) :
    (deriv Complex.digamma (z + 1) - Q.eval (1 / (z + 1)))
        - (deriv Complex.digamma z - Q.eval (1 / z))
      = genDefect (fun w : ℂ => -w ^ (2 : ℕ)) Q (1 / z) := by
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0] at hre
    simp at hre
  have hz1 : z + 1 ≠ 0 := by
    intro h0
    have hzr : (z + 1).re = 0 := by rw [h0]; simp
    simp only [Complex.add_re, Complex.one_re] at hzr
    linarith
  have hrec := RHTower.deriv_digamma_apply_add_nat hre 1
  simp only [Nat.cast_one, Finset.sum_range_one, Nat.cast_zero, add_zero] at hrec
  have hquot : 1 / (z + 1) = (1 / z) / (1 + 1 / z) := by
    field_simp
  rw [hrec, hquot, genDefect]
  have hsq : -((1 / z) ^ (2 : ℕ)) = -(z ^ (2 : ℕ))⁻¹ := by
    rw [div_pow, one_pow]
    simp
  rw [hsq]
  ring

/-- **The trigamma expansion to any prescribed order on a vertical line.**  For every `N` there is a
polynomial `Q` with zero constant term such that `ψ′(σ+it) = Q(1/(σ+it)) + O(t^{-(N+1)})`, uniformly
in the abscissa. -/
theorem exists_deriv_digamma_expansion (N : ℕ) :
    ∃ (Q : Polynomial ℂ) (C T : ℝ), Q.eval 0 = 0 ∧ 0 ≤ C ∧ 2 ≤ T ∧
      ∀ σ t : ℝ, 0 < σ → T ≤ t →
        ‖deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
            - Q.eval (1 / ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ C / t ^ (N + 1) := by
  have hseed : ∀ᶠ w in nhds (0 : ℂ), (fun w : ℂ => -w ^ (2 : ℕ)) w = w ^ (2 : ℕ) * (-1 : ℂ) := by
    filter_upwards with w
    ring
  obtain ⟨Q, g, hQ0, hg, hfac⟩ :=
    exists_genDefect_factor (F := fun w : ℂ => -w ^ (2 : ℕ)) (g₀ := fun _ => (-1 : ℂ))
      analyticAt_const hseed N
  obtain ⟨C, r, hC, hr, hbound⟩ := exists_bound_of_factor hg hfac
  refine ⟨Q, 4 * C, max 2 (1 / r), hQ0, by positivity, le_max_left _ _, ?_⟩
  intro σ t hσ ht
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htr : 1 / r ≤ t := le_trans (le_max_right _ _) ht
  set R : ℂ → ℂ := fun z => deriv Complex.digamma z - Q.eval (1 / z) with hR
  set E : ℂ → ℂ := fun z => genDefect (fun w : ℂ => -w ^ (2 : ℕ)) Q (1 / z) with hE
  have hzre : ∀ n : ℕ, (0 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re := by
    intro n
    have hval : ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)).re = σ + n := by simp
    rw [hval]
    positivity
  have hznorm : ∀ n : ℕ, (2 : ℝ) ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
    fun n => le_trans ht2 (norm_vertical_add_nat_ge_im (σ := σ) t n)
  have hzbig : ∀ n : ℕ, 1 / r ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ :=
    fun n => le_trans htr (norm_vertical_add_nat_ge_im (σ := σ) t n)
  have hmain := norm_le_of_shift_defect (R := R) (E := E) (C := C) hσ hC
    (p := N + 2) (by omega) ht2 ?_ ?_ ?_
  · have hpow : (N + 2) - 1 = N + 1 := by omega
    rw [hpow] at hmain
    simpa [hR] using hmain
  · intro n
    have hshift : (σ : ℂ) + (t : ℂ) * Complex.I + ((n : ℂ) + 1)
        = ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)) + 1 := by ring
    rw [hshift, hR, hE]
    exact deriv_digamma_genDefect_eq Q (hzre n)
  · intro n
    have hwnorm : ‖1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))‖
        = 1 / ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
      rw [norm_div, norm_one]
    have hzpos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
      have := hznorm n
      linarith
    have hwle : ‖1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))‖ ≤ r := by
      rw [hwnorm, div_le_iff₀ hzpos]
      have hb := hzbig n
      rw [div_le_iff₀ hr] at hb
      nlinarith
    have hb := hbound _ hwle
    rw [hE]
    refine le_trans hb ?_
    rw [hwnorm, div_pow, one_pow, mul_one_div]
  · have hderiv : Tendsto (fun n : ℕ =>
        deriv Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))) atTop (nhds 0) :=
      RHTower.deriv_digamma_add_nat_tendsto _
    have hinv : Tendsto (fun n : ℕ => 1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)))
        atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _)
        (g := fun n : ℕ => 1 / (σ + n)) (fun n => ?_) ?_
      · have hge : σ + n ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ)‖ := by
          simpa using norm_vertical_add_nat_ge_re (σ := σ) t n
        have hpos : (0 : ℝ) < σ + n := by positivity
        rw [norm_div, norm_one]
        rw [div_le_div_iff₀ (by linarith) hpos]
        nlinarith
      · have hdiv : Tendsto (fun n : ℕ => σ + (n : ℝ)) atTop atTop :=
          tendsto_atTop_add_const_left _ σ tendsto_natCast_atTop_atTop
        exact Tendsto.congr (fun n => by simp [one_div]) hdiv.inv_tendsto_atTop
    have hpoly : Tendsto (fun n : ℕ => Q.eval (1 / ((σ : ℂ) + (t : ℂ) * Complex.I + (n : ℂ))))
        atTop (nhds 0) := by
      have hcont : ContinuousAt (fun z : ℂ => Q.eval z) 0 :=
        (analyticAt_polyEval Q 0).continuousAt
      have hcomp := hcont.tendsto.comp hinv
      rw [hQ0] at hcomp
      simpa [Function.comp_def] using hcomp
    have hcomb := hderiv.sub hpoly
    rw [sub_zero] at hcomb
    refine hcomb.congr fun n => ?_
    rw [hR]

end

end GaloisForLFunctions.HTGeometry
