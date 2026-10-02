import GaloisForLFunctions.RHTower.ZetaChiRealDualAtomUniform
import GaloisForLFunctions.RHTower.ZetaChiDualWeightedInteriorMean

open Complex Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower


/-- Exact positive-real ratio scaling of the literal dual coefficient. -/
theorem zetaChi_dual_ratio_atom_eq (s : ℂ) {x ξ : ℝ} (hx : 0 < x) (hξ : 0 < ξ) (t : ℝ) :
    (ξ : ℂ) ^ (1 - s) *
      (zetaChi (s + (t : ℂ) * I) * ((ξ * x : ℝ) : ℂ) ^ (s - 1) *
        bourgainOscillation (t * Real.log (ξ * x))) =
      zetaChi (s + (t : ℂ) * I) * (x : ℂ) ^ (s - 1) *
        bourgainOscillation (t * Real.log (ξ * x)) := by
  have hp : (((ξ * x : ℝ) : ℂ)) ^ (s - 1) =
      (ξ : ℂ) ^ (s - 1) * (x : ℂ) ^ (s - 1) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hξ.le hx.le]
  have he : (ξ : ℂ) ^ (1 - s) * (ξ : ℂ) ^ (s - 1) = 1 := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hξ.ne'),
      show (1 - s) + (s - 1) = (0 : ℂ) by ring, Complex.cpow_zero]
  rw [hp]
  calc
    _ = ((ξ : ℂ) ^ (1 - s) * (ξ : ℂ) ^ (s - 1)) *
        (zetaChi (s + (t : ℂ) * I) * (x : ℂ) ^ (s - 1) *
          bourgainOscillation (t * Real.log (ξ * x))) := by ring
    _ = _ := by rw [he, one_mul]

/-- Multiplying the original atom by a positive-ratio frequency gives exactly
its physical Dirichlet cross atom. -/
theorem zetaChiDualInteriorAtom_mul_frequency (s : ℂ) {n : ℕ} (hn : 0 < n)
    {ξ : ℝ} (hξ : 0 < ξ) (t : ℝ) :
    zetaChiDualInteriorAtom s n t * bourgainOscillation (t * Real.log ξ) =
      zetaChi (s + (t : ℂ) * I) * (n : ℂ) ^ (s - 1) *
        bourgainOscillation (t * Real.log (ξ * n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_mul hξ.ne' hnR.ne']
  unfold zetaChiDualInteriorAtom bourgainOscillation
  rw [mul_add, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

/-- Uniform signed stationary approximation for every actual positive-ratio
Dirichlet cross atom, retaining its full complex coefficient and error. -/
theorem exists_zetaChi_dual_ratio_atom_disc_uniform
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ n : ℕ, 0 < n → ∀ ξ : ℝ, 0 < ξ →
      (m : ℝ) ^ 10 + (m : ℝ) ^ 6 ≤ 2 * Real.pi * (ξ * n) →
      2 * Real.pi * (ξ * n) + (m : ℝ) ^ 6 ≤ 2 * (m : ℝ) ^ 10 →
      ‖(∫ t in (m : ℝ) ^ 10..(2 * (m : ℝ) ^ 10),
          zetaChiDualInteriorAtom s n t * bourgainOscillation (t * Real.log ξ)) -
        (ξ : ℂ) ^ (1 - s) * (((2 * Real.pi : ℝ) : ℂ) *
          bourgainOscillation (2 * Real.pi * (ξ * n)))‖ ≤
        ‖(ξ : ℂ) ^ (1 - s)‖ * (D / m) := by
  obtain ⟨D, hD, hb⟩ := exists_zetaChi_real_dual_atom_disc_uniform c hr hc0 hc1
  refine ⟨D, hD, ?_⟩
  filter_upwards [hb] with m hm
  intro s hs n hn ξ hξ hlo hup
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbnd := hm s hs (ξ * n) hlo hup
  have hscaled := mul_le_mul_of_nonneg_left hbnd (norm_nonneg ((ξ : ℂ) ^ (1 - s)))
  rw [← norm_mul, mul_sub, ← intervalIntegral.integral_const_mul] at hscaled
  have heq (t : ℝ) : (ξ : ℂ) ^ (1 - s) *
      (zetaChi (s + (t : ℂ) * I) * ((ξ * n : ℝ) : ℂ) ^ (s - 1) *
        bourgainOscillation (t * Real.log (ξ * n))) =
      zetaChiDualInteriorAtom s n t * bourgainOscillation (t * Real.log ξ) := by
    rw [zetaChi_dual_ratio_atom_eq s hnR hξ t,
      zetaChiDualInteriorAtom_mul_frequency s hn hξ t]
    norm_cast
  rw [intervalIntegral.integral_congr (fun t _ => heq t)] at hscaled
  exact hscaled

end RHTower
