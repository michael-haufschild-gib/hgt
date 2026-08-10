import GaloisForLFunctions.RHTower.GaussComponentSampledRatio
import GaloisForLFunctions.RHTower.GaussComponentPhaseResidue
import GaloisForLFunctions.HTGeometry.UnimodularInverseLimit

/-!
# The prime-lattice sampled ratio law

Sampling the finite-shift ratio law at the prime logarithmic lattice `t_n = 2π(n+1)/log p`
identifies the limiting rotation with the circle point already used by the harmonic logarithmic
equidistribution: for every fixed shift `j`,

`ρ(t_{n+j}) / ρ(t_n) - exp(2π i j δ_n) → 0`,  `δ_n = (log(n+1) - log log p)/(m log p)`.

The rotation exponent is exactly `gaussComponentPhaseRate · log(n+1) + gaussComponentPhaseOffset`,
so the sampled ratio is governed by the same phase point that drives the residue computation.
-/

namespace RHTower

open Filter Topology

noncomputable section

/-- The prime logarithmic sampling height `t_n = 2π(n+1)/log p`. -/
def gaussPrimeSampleHeight (p : Nat.Primes) (n : ℕ) : ℝ :=
  2 * Real.pi * ((n : ℝ) + 1) / Real.log (p : ℝ)

/-- The prime logarithmic shift `2πj/log p`. -/
def gaussPrimeSampleShift (p : Nat.Primes) (j : ℕ) : ℝ :=
  2 * Real.pi * (j : ℝ) / Real.log (p : ℝ)

theorem gaussPrimeSampleShift_nonneg (p : Nat.Primes) (j : ℕ) :
    0 ≤ gaussPrimeSampleShift p j := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.prop.one_lt)
  rw [gaussPrimeSampleShift]
  positivity

theorem gaussPrimeSampleHeight_pos (p : Nat.Primes) (n : ℕ) :
    0 < gaussPrimeSampleHeight p n := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [gaussPrimeSampleHeight]
  positivity

theorem gaussPrimeSampleHeight_add_shift (p : Nat.Primes) (n j : ℕ) :
    gaussPrimeSampleHeight p n + gaussPrimeSampleShift p j =
      gaussPrimeSampleHeight p (n + j) := by
  rw [gaussPrimeSampleHeight, gaussPrimeSampleShift, gaussPrimeSampleHeight]
  push_cast
  ring

theorem tendsto_gaussPrimeSampleHeight (p : Nat.Primes) :
    Tendsto (fun n : ℕ => gaussPrimeSampleHeight p n) atTop atTop := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hbase : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ => 2 * Real.pi * ((n : ℝ) + 1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hpi hbase
  simpa [gaussPrimeSampleHeight] using hmul.atTop_div_const hlog

/-- The shifted clock at a sample height is the prime phase point, rotated `j` times. -/
theorem gaussPrimeSampleShift_mul_clock
    {m : ℕ} (hm : 1 ≤ m) (p : Nat.Primes) (n j : ℕ) :
    ((gaussPrimeSampleShift p j : ℝ) : ℂ) *
        gaussComponentVerticalClock m (gaussPrimeSampleHeight p n) =
      2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
        ((gaussComponentPhaseRate m p * Real.log ((n : ℝ) + 1) +
          gaussComponentPhaseOffset m p : ℝ) : ℂ) := by
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hpi : 0 < 2 * Real.pi := by positivity
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hheight : gaussPrimeSampleHeight p n / (2 * Real.pi)
      = ((n : ℝ) + 1) / Real.log (p : ℝ) := by
    rw [gaussPrimeSampleHeight]
    field_simp
  have hlogheight : Real.log (gaussPrimeSampleHeight p n / (2 * Real.pi))
      = Real.log ((n : ℝ) + 1) - Real.log (Real.log (p : ℝ)) := by
    rw [hheight, Real.log_div hn.ne' hlog.ne']
  rw [gaussComponentVerticalClock_eq, hlogheight, gaussPrimeSampleShift,
    gaussComponentPhaseRate, gaussComponentPhaseOffset]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  push_cast
  field_simp
  ring

/-- **Prime-lattice ratio law.**  For every fixed shift, the sampled Gauss-component ratio is
asymptotically the rotation by `2π i j δ_n`. -/
theorem gaussComponentPrimeSample_ratio_sub_phase_tendsto_zero
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (j : ℕ) :
    Tendsto (fun n : ℕ =>
      gaussComponentVerticalValue k (gaussPrimeSampleHeight p (n + j)) /
          gaussComponentVerticalValue k (gaussPrimeSampleHeight p n) -
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
          ((gaussComponentPhaseRate m p * Real.log ((n : ℝ) + 1) +
            gaussComponentPhaseOffset m p : ℝ) : ℂ)))
      atTop (nhds 0) := by
  have hbase := gaussComponentVerticalValue_ratio_sub_clock_tendsto_zero hm k
    (h := gaussPrimeSampleShift p j) (gaussPrimeSampleShift_nonneg p j)
  have hcomp := hbase.comp (tendsto_gaussPrimeSampleHeight p)
  refine hcomp.congr ?_
  intro n
  simp only [Function.comp_def]
  rw [gaussPrimeSampleHeight_add_shift p n j, gaussPrimeSampleShift_mul_clock hm p n j]

/-- The sampled rotation is unimodular. -/
theorem norm_gaussPrimeSamplePhase {m : ℕ} (p : Nat.Primes) (j n : ℕ) :
    ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
      ((gaussComponentPhaseRate m p * Real.log ((n : ℝ) + 1) +
        gaussComponentPhaseOffset m p : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hform : (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
      ((gaussComponentPhaseRate m p * Real.log ((n : ℝ) + 1) +
        gaussComponentPhaseOffset m p : ℝ) : ℂ))
      = ((2 * Real.pi * (j : ℝ) *
          (gaussComponentPhaseRate m p * Real.log ((n : ℝ) + 1) +
            gaussComponentPhaseOffset m p) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hform]
  simp

/-- **Backward prime-lattice ratio law.**  The reciprocal sampled ratio is asymptotically the
inverse rotation, so the ratio law is available at negative shifts as well. -/
theorem gaussComponentPrimeSample_inv_ratio_sub_phase_tendsto_zero
    {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) (j : ℕ) :
    Tendsto (fun n : ℕ =>
      gaussComponentVerticalValue k (gaussPrimeSampleHeight p n) /
          gaussComponentVerticalValue k (gaussPrimeSampleHeight p (n + j)) -
        Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) *
          ((gaussComponentPhaseRate m p * Real.log ((n : ℝ) + 1) +
            gaussComponentPhaseOffset m p : ℝ) : ℂ))))
      atTop (nhds 0) := by
  have hforward := gaussComponentPrimeSample_ratio_sub_phase_tendsto_zero hm k p j
  have ha : ∀ n : ℕ,
      gaussComponentVerticalValue k (gaussPrimeSampleHeight p (n + j)) /
        gaussComponentVerticalValue k (gaussPrimeSampleHeight p n) ≠ 0 := by
    intro n
    exact div_ne_zero
      (gaussComponentVerticalValue_ne_zero hm k (gaussPrimeSampleHeight_pos p (n + j)))
      (gaussComponentVerticalValue_ne_zero hm k (gaussPrimeSampleHeight_pos p n))
  have hinv := GaloisForLFunctions.tendsto_inv_sub_inv_of_tendsto_sub_zero ha
    (fun n => norm_gaussPrimeSamplePhase (m := m) p j n) hforward
  refine hinv.congr ?_
  intro n
  rw [inv_div, ← Complex.exp_neg]

end

end RHTower
