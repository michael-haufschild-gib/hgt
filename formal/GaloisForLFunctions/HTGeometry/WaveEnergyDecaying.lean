import GaloisForLFunctions.HTGeometry.WaveEnergyFluxIntegrable
import GaloisForLFunctions.HTGeometry.WaveEnergyDerivativeIntegrable
import Mathlib.Analysis.ODE.Gronwall

/-!
# The energy estimate for a decaying solution

Assembling the integrable forms of the Green identity, the flux identity and the differentiation of
the energy gives the estimate without any support hypothesis. What replaces compact support is a
bundle of integrability and domination conditions — exactly the conditions a Fourier synthesis
supplies — collected here as `DecayingSolution`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ContDiff

section Decaying

variable {d : ℕ} {u V : ℝ × (Fin d → ℝ) → ℝ}

/-- A smooth solution whose energy, fluxes and time derivative are integrable on every slice, with a
local dominating function in time. This is what a decaying solution supplies in place of compact
spatial support. -/
structure DecayingSolution (u V : ℝ × (Fin d → ℝ) → ℝ) : Prop where
  /-- The field is smooth. -/
  smooth : ContDiff ℝ ∞ u
  /-- It solves the clock equation. -/
  solves : SolvesWaveEq u V
  /-- Its energy density is integrable on every slice. -/
  energyInt : ∀ t : ℝ, Integrable (fun x : Fin d → ℝ => energyDensity u (t, x))
    (volume : Measure (Fin d → ℝ))
  /-- The three products the Green identity consumes are integrable. -/
  greenInt₁ : ∀ (t : ℝ) (i : Fin d), Integrable
    (fun x : Fin d → ℝ => coordPartial i (coordPartial i (slice u t)) x
      * slice (waveDirDeriv (timeDir d) u) t x) (volume : Measure (Fin d → ℝ))
  /-- The gradient pairing is integrable. -/
  greenInt₂ : ∀ (t : ℝ) (i : Fin d), Integrable
    (fun x : Fin d → ℝ => coordPartial i (slice u t) x
      * coordPartial i (slice (waveDirDeriv (timeDir d) u) t) x) (volume : Measure (Fin d → ℝ))
  /-- And the first-derivative product. -/
  greenInt₃ : ∀ (t : ℝ) (i : Fin d), Integrable
    (fun x : Fin d → ℝ => coordPartial i (slice u t) x
      * slice (waveDirDeriv (timeDir d) u) t x) (volume : Measure (Fin d → ℝ))
  /-- The zeroth-order term is integrable. -/
  fluxInt : ∀ t : ℝ, Integrable
    (fun x : Fin d → ℝ => (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x)))
    (volume : Measure (Fin d → ℝ))
  /-- The time derivative of the energy density is locally dominated. -/
  dominated : ∀ t : ℝ, ∃ bound : (Fin d → ℝ) → ℝ,
    Integrable bound (volume : Measure (Fin d → ℝ)) ∧
      ∀ s ∈ Metric.ball t 1, ∀ x : Fin d → ℝ,
        ‖waveDirDeriv (timeDir d) (energyDensity u) (s, x)‖ ≤ bound x

/-- **The energy dominates the flux**, for integrable data. -/
theorem abs_integral_flux_le_of_integrable
    (hfluxint : ∀ t : ℝ, Integrable
      (fun x : Fin d → ℝ => (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x)))
      (volume : Measure (Fin d → ℝ)))
    (hdensint : ∀ t : ℝ, Integrable (fun x : Fin d → ℝ => energyDensity u (t, x))
      (volume : Measure (Fin d → ℝ)))
    {M : ℝ} (hM : ∀ p, |V p| ≤ M) (t : ℝ) :
    |2 * ∫ x : Fin d → ℝ, (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|
      ≤ (M + 1) * waveEnergy u t := by
  have hpt : ∀ x : Fin d → ℝ,
      |(V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|
        ≤ (M + 1) / 2 * energyDensity u (t, x) := by
    intro x
    have h1 : |V (t, x) + 1| ≤ M + 1 := by
      have hMle := abs_le.mp (hM (t, x))
      rw [abs_le]
      constructor <;> linarith [hMle.1, hMle.2]
    have hsq : 2 * (|u (t, x)| * |waveDirDeriv (timeDir d) u (t, x)|)
        ≤ (u (t, x)) ^ (2 : ℕ) + (waveDirDeriv (timeDir d) u (t, x)) ^ (2 : ℕ) := by
      have h := two_mul_le_add_sq |u (t, x)| |waveDirDeriv (timeDir d) u (t, x)|
      rw [sq_abs, sq_abs] at h
      linarith
    have hdens : (u (t, x)) ^ (2 : ℕ) + (waveDirDeriv (timeDir d) u (t, x)) ^ (2 : ℕ)
        ≤ energyDensity u (t, x) := by
      have hsum : 0 ≤ ∑ i : Fin d, (waveDirDeriv (spaceDir d i) u (t, x)) ^ (2 : ℕ) :=
        Finset.sum_nonneg fun i _ => sq_nonneg _
      rw [energyDensity]
      linarith
    have h2 : |u (t, x)| * |waveDirDeriv (timeDir d) u (t, x)| ≤ energyDensity u (t, x) / 2 := by
      linarith
    calc |(V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|
        = |V (t, x) + 1| * (|u (t, x)| * |waveDirDeriv (timeDir d) u (t, x)|) := by
          rw [abs_mul, abs_mul]
      _ ≤ (M + 1) * (energyDensity u (t, x) / 2) := by
          refine mul_le_mul h1 h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ?_
          have := hM (t, x)
          have habs := abs_nonneg (V (t, x))
          linarith
      _ = (M + 1) / 2 * energyDensity u (t, x) := by ring
  have hmono : (∫ x : Fin d → ℝ,
      |(V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|)
      ≤ ∫ x : Fin d → ℝ, (M + 1) / 2 * energyDensity u (t, x) :=
    integral_mono (hfluxint t).abs ((hdensint t).const_mul _) hpt
  have hnorm : |∫ x : Fin d → ℝ,
      (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|
      ≤ ∫ x : Fin d → ℝ,
          |(V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))| := by
    simpa [Real.norm_eq_abs] using
      norm_integral_le_integral_norm
        (f := fun x : Fin d → ℝ =>
          (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x)))
  rw [integral_const_mul] at hmono
  rw [abs_mul, abs_two]
  have hfin : |∫ x : Fin d → ℝ,
      (V (t, x) + 1) * (u (t, x) * waveDirDeriv (timeDir d) u (t, x))|
      ≤ (M + 1) / 2 * waveEnergy u t := le_trans hnorm hmono
  rw [waveEnergy] at hfin ⊢
  linarith

/-- **The energy estimate for a decaying solution.** No support hypothesis: the compact set is
replaced by integrability of the energy and the fluxes, and by a local dominating function. -/
theorem waveEnergy_le_exp_of_decaying (h : DecayingSolution u V) {M : ℝ} (hM : ∀ p, |V p| ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    waveEnergy u t ≤ waveEnergy u 0 * Real.exp ((M + 1) * t) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM (0, 0))
  have hKne : (M + 1) ≠ 0 := by linarith
  have hderiv : ∀ s : ℝ, HasDerivAt (waveEnergy u)
      (2 * ∫ x : Fin d → ℝ,
        (V (s, x) + 1) * (u (s, x) * waveDirDeriv (timeDir d) u (s, x))) s := by
    intro s
    obtain ⟨bound, hbint, hb⟩ := h.dominated s
    have hd := hasDerivAt_waveEnergy_of_dominated h.smooth s hbint hb (h.energyInt s)
    rwa [integral_dirDeriv_energyDensity_of_integrable h.smooth h.solves s
      (h.greenInt₁ s) (h.greenInt₂ s) (h.greenInt₃ s) ((h.fluxInt s).const_mul 2)] at hd
  have hcont : ContinuousOn (waveEnergy u) (Set.Icc 0 t) :=
    fun s _ => ((hderiv s).continuousAt).continuousWithinAt
  have ha : ‖waveEnergy u 0‖ ≤ waveEnergy u 0 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (waveEnergy_nonneg u 0)]
  have hbound : ∀ s ∈ Set.Ico (0 : ℝ) t,
      ‖2 * ∫ x : Fin d → ℝ,
        (V (s, x) + 1) * (u (s, x) * waveDirDeriv (timeDir d) u (s, x))‖
        ≤ (M + 1) * ‖waveEnergy u s‖ + 0 := by
    intro s _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (waveEnergy_nonneg u s), add_zero]
    exact abs_integral_flux_le_of_integrable h.fluxInt h.energyInt hM s
  have hgb := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s _ => (hderiv s).hasDerivWithinAt) ha hbound t (Set.mem_Icc.mpr ⟨ht, le_rfl⟩)
  rw [gronwallBound_of_K_ne_0 hKne, Real.norm_eq_abs,
    abs_of_nonneg (waveEnergy_nonneg u t)] at hgb
  simpa using hgb

/-! ## Vanishing -/

theorem energyDensity_eq_zero_of_waveEnergy_eq_zero_of_integrable (hu : ContDiff ℝ ∞ u)
    {t : ℝ} (hint : Integrable (fun x : Fin d → ℝ => energyDensity u (t, x))
      (volume : Measure (Fin d → ℝ))) (h : waveEnergy u t = 0) (x : Fin d → ℝ) :
    energyDensity u (t, x) = 0 := by
  have hmap : Continuous fun y : Fin d → ℝ => ((t, y) : ℝ × (Fin d → ℝ)) := by fun_prop
  have hcont : Continuous fun y : Fin d → ℝ => energyDensity u (t, y) :=
    (contDiff_energyDensity hu).continuous.comp hmap
  have hae : (fun y : Fin d → ℝ => energyDensity u (t, y))
      =ᵐ[(volume : Measure (Fin d → ℝ))] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => energyDensity_nonneg u (t, y)) hint).mp h
  have heq : (fun y : Fin d → ℝ => energyDensity u (t, y)) = 0 :=
    (hcont.ae_eq_iff_eq (volume : Measure (Fin d → ℝ)) continuous_zero).mp hae
  exact congrFun heq x

/-- **A decaying solution whose energy vanishes at one time vanishes at every later time.** -/
theorem eq_zero_of_waveEnergy_zero_of_decaying (h : DecayingSolution u V) {M : ℝ}
    (hM : ∀ p, |V p| ≤ M) (h0 : waveEnergy u 0 = 0) {t : ℝ} (ht : 0 ≤ t) (x : Fin d → ℝ) :
    u (t, x) = 0 := by
  have hle := waveEnergy_le_exp_of_decaying h hM ht
  rw [h0, zero_mul] at hle
  have ht0 : waveEnergy u t = 0 := le_antisymm hle (waveEnergy_nonneg u t)
  have hden := energyDensity_eq_zero_of_waveEnergy_eq_zero_of_integrable h.smooth
    (h.energyInt t) ht0 x
  have hsum : 0 ≤ ∑ i : Fin d, (waveDirDeriv (spaceDir d i) u (t, x)) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [energyDensity] at hden
  have hsq : (u (t, x)) ^ (2 : ℕ) = 0 := by
    nlinarith [sq_nonneg (waveDirDeriv (timeDir d) u (t, x)), sq_nonneg (u (t, x))]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq

end Decaying

end GaloisForLFunctions.HTGeometry
