import GaloisForLFunctions.RHTower.LevinsonLittlewoodZeroCount
import GaloisForLFunctions.RHTower.LevinsonEntireDetector

/-!
# The detector zero mass inside the counting rectangle, from a mollified mean square

Levinson's method needs an upper bound for the zero mass of the entire detector
`G♯ = (s−1)²(ζ + λζ′)` inside `[½,4] × [T₁,T₂]`.  Multiplying by an arbitrary entire mollifier `Ψ`
only increases the analytic order at every point, so the mass is bounded by Littlewood's identity
for `G♯·Ψ` on the *wider* rectangle `[σ₀,4] × [T₁,T₂]` with `σ₀ < ½`: every zero counted on the left
has horizontal weight at least `½ − σ₀`.

The output is the exact budget the window inequality consumes: the mean square of `G♯·Ψ` on the
Levinson abscissa, a pointwise lower bound on the far-right edge, and the two remaining boundary
integrals.
-/

open Complex MeasureTheory Set Filter intervalIntegral Topology
open scoped Interval

namespace RHTower

noncomputable section

/-- **The detector zero mass is bounded by the mollified Littlewood budget.** -/
theorem levinsonGEntire_zeroMass_le_of_meanSquare
    {lam : ℂ} (hlam : lam ≠ 0) {Ψ : ℂ → ℂ} (hΨ : AnalyticOnNhd ℂ Ψ Set.univ)
    (hΨne : ∃ z : ℂ, Ψ z ≠ 0)
    {σ₀ T₁ T₂ Msq A : ℝ} (hσ₀ : σ₀ < 1 / 2) (hT : T₁ < T₂)
    (hbot : ∀ x ∈ uIcc σ₀ (4 : ℝ),
      levinsonGEntire lam ((x : ℂ) + (T₁ : ℂ) * I) * Ψ ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ uIcc σ₀ (4 : ℝ),
      levinsonGEntire lam ((x : ℂ) + (T₂ : ℂ) * I) * Ψ ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0)
    (hrightne : ∀ t ∈ uIcc T₁ T₂,
      levinsonGEntire lam (((4 : ℝ) : ℂ) + (t : ℂ) * I) * Ψ (((4 : ℝ) : ℂ) + (t : ℂ) * I) ≠ 0)
    (hA : 0 < A)
    (hAle : ∀ t ∈ uIcc T₁ T₂,
      A ≤ ‖levinsonGEntire lam (((4 : ℝ) : ℂ) + (t : ℂ) * I)
            * Ψ (((4 : ℝ) : ℂ) + (t : ℂ) * I)‖)
    (hMsq : (∫ t in T₁..T₂,
        ‖levinsonGEntire lam ((σ₀ : ℂ) + (t : ℂ) * I) * Ψ ((σ₀ : ℂ) + (t : ℂ) * I)‖ ^ (2 : ℕ)) ≤ Msq)
    (Z : Finset ℂ)
    (hZ : ∀ z : ℂ, z ∈ Z ↔ z ∈ (uIcc (1 / 2 : ℝ) 4 ×ℂ uIcc T₁ T₂) ∧ levinsonGEntire lam z = 0) :
    2 * Real.pi * ((1 / 2 - σ₀) *
        (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire lam) w).toNat : ℝ)))
      ≤ (T₂ - T₁) / 2 * Real.log (Msq / (T₂ - T₁)) - (T₂ - T₁) * Real.log A
          + (4 - σ₀) * (∫ t in T₁..T₂,
              (logDeriv (fun z => levinsonGEntire lam z * Ψ z)
                (((4 : ℝ) : ℂ) + (t : ℂ) * I)).re)
          + (∫ x in σ₀..(4 : ℝ), (x - σ₀) *
              (logDeriv (fun z => levinsonGEntire lam z * Ψ z)
                ((x : ℂ) + (T₁ : ℂ) * I)).im)
          - ∫ x in σ₀..(4 : ℝ), (x - σ₀) *
              (logDeriv (fun z => levinsonGEntire lam z * Ψ z)
                ((x : ℂ) + (T₂ : ℂ) * I)).im := by
  classical
  set F : ℂ → ℂ := fun z => levinsonGEntire lam z * Ψ z with hF
  have hGan : AnalyticOnNhd ℂ (levinsonGEntire lam) Set.univ := analyticOnNhd_levinsonGEntire lam
  have hFan : AnalyticOnNhd ℂ F Set.univ := fun z hz => (hGan z hz).mul (hΨ z hz)
  obtain ⟨zg, hzg⟩ := exists_levinsonGEntire_ne_zero hlam
  obtain ⟨zp, hzp⟩ := hΨne
  have hGorder : ∀ w : ℂ, analyticOrderAt (levinsonGEntire lam) w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hGan ⟨zg, hzg⟩ w
  have hPorder : ∀ w : ℂ, analyticOrderAt Ψ w ≠ ⊤ := fun w =>
    analyticOrderAt_ne_top_of_entire_exists_ne_zero hΨ ⟨zp, hzp⟩ w
  have hFne : ∃ z : ℂ, F z ≠ 0 := by
    by_cases hex : ∃ z : ℂ, F z ≠ 0
    · exact hex
    exfalso
    have hcon : ∀ z : ℂ, F z = 0 := by
      intro z
      by_contra hz
      exact hex ⟨z, hz⟩
    have : analyticOrderAt F 0 = ⊤ := by
      have hEq : F = fun _ => (0 : ℂ) := funext hcon
      rw [hEq]
      simpa using (analyticOrderAt_eq_top (f := fun _ : ℂ => (0 : ℂ)) (z₀ := (0 : ℂ))).mpr
        (by filter_upwards with _ using rfl)
    have hmul : analyticOrderAt F 0
        = analyticOrderAt (levinsonGEntire lam) 0 + analyticOrderAt Ψ 0 :=
      analyticOrderAt_mul (hGan 0 (Set.mem_univ _)) (hΨ 0 (Set.mem_univ _))
    rw [hmul] at this
    exact (WithTop.add_ne_top.mpr ⟨hGorder 0, hPorder 0⟩) this
  have hσ₀4 : σ₀ < (4 : ℝ) := by linarith
  obtain ⟨Z', hZ', hbound⟩ :=
    exists_entire_zeroCount_le_of_meanSquare (f := F) (σ := (1 / 2 : ℝ)) hFan hFne
      hσ₀4 hT hbot htop hrightne hA hAle hMsq
  -- every detector zero of the counting rectangle lies in the filtered zero set of `F`
  have hsub : Z ⊆ Z'.filter (fun w => (1 / 2 : ℝ) ≤ w.re) := by
    intro w hw
    obtain ⟨hwmem, hwzero⟩ := (hZ w).mp hw
    have hre := (Complex.mem_reProdIm.mp hwmem).1
    have him := (Complex.mem_reProdIm.mp hwmem).2
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 4)] at hre
    refine Finset.mem_filter.mpr ⟨?_, hre.1⟩
    refine (hZ' w).mpr ⟨?_, by simp [hF, hwzero]⟩
    refine Complex.mem_reProdIm.mpr ⟨?_, him⟩
    rw [uIcc_of_le hσ₀4.le]
    exact ⟨le_trans hσ₀.le hre.1, hre.2⟩
  have horder : ∀ w ∈ Z, ((analyticOrderAt (levinsonGEntire lam) w).toNat : ℝ)
      ≤ ((analyticOrderAt F w).toNat : ℝ) := by
    intro w _
    have hmul : analyticOrderAt F w
        = analyticOrderAt (levinsonGEntire lam) w + analyticOrderAt Ψ w :=
      analyticOrderAt_mul (hGan w (Set.mem_univ _)) (hΨ w (Set.mem_univ _))
    rw [hmul, ENat.toNat_add (hGorder w) (hPorder w)]
    push_cast
    have : (0 : ℝ) ≤ ((analyticOrderAt Ψ w).toNat : ℝ) := Nat.cast_nonneg _
    linarith
  have hsum : (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire lam) w).toNat : ℝ))
      ≤ ∑ w ∈ Z'.filter (fun w => (1 / 2 : ℝ) ≤ w.re), ((analyticOrderAt F w).toNat : ℝ) := by
    refine le_trans (Finset.sum_le_sum horder) ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun w _ _ => Nat.cast_nonneg _)
  have hscale : (1 / 2 - σ₀) *
      (∑ w ∈ Z, ((analyticOrderAt (levinsonGEntire lam) w).toNat : ℝ))
      ≤ (1 / 2 - σ₀) *
      (∑ w ∈ Z'.filter (fun w => (1 / 2 : ℝ) ≤ w.re), ((analyticOrderAt F w).toNat : ℝ)) :=
    mul_le_mul_of_nonneg_left hsum (by linarith)
  have hfinal := mul_le_mul_of_nonneg_left hscale (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  exact le_trans hfinal hbound

end

end RHTower
