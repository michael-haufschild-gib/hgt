import GaloisForLFunctions.RHTower.ArithmeticCotangentPhaseTransport
import GaloisForLFunctions.RHTower.EulerDeletionPowerSumRemainder

/-!
# Cotangent transport for the literal logarithmic lattice

The phase is `t / (2π) * log ((n + j) / n)` for `n > 0`. Its increments are positive,
strictly decreasing, and less than `t / (2π(n + j))`. The corrected unweighted prefix has
strict negative sign at every cutoff with at least two samples when `0 < t < 2πn`.
At arbitrary positive height it is nonincreasing beyond each explicit subresonant head.

The exact weighted formula is identified with the actual power-sum remainder, zeta term,
power normalization, and endpoint kernel at `s = σ - it`. This identity allows all real
`σ` and `t`, including resonances. The actual weight drift and finite head still need a
separate source comparison; neither the proposed linear remainder cutoff nor RH is proved.

As in the transport module, Lean cutoff `M` means `M + 1` samples.
-/

set_option autoImplicit false
open scoped BigOperators
open Complex Real

namespace RHTower.LogarithmicCotangent
noncomputable section
open RHTower.PhaseCotangent RHTower.DeletionMixedRefinement

/-- Literal lattice phase anchored at the integer `n`, measured in turns. -/
def logarithmicPhase (n : ℕ) (t : ℝ) (j : ℕ) : ℝ :=
  t / (2 * Real.pi) * (Real.log ((n : ℝ) + j) - Real.log n)

/-- Literal real power weight, with no replacement by constant amplitude. -/
def powerWeight (n : ℕ) (σ : ℝ) (j : ℕ) : ℝ := ((n : ℝ) + j) ^ (-σ)

/-- The anchor carries zero relative phase. -/
theorem logarithmicPhase_zero (n : ℕ) (t : ℝ) : logarithmicPhase n t 0 = 0 := by
  simp [logarithmicPhase]

/-- The logarithmic difference is the literal ratio clock at a positive anchor. -/
theorem logarithmicPhase_eq_log_ratio {n : ℕ} (hn : 0 < n) (t : ℝ) (j : ℕ) :
    logarithmicPhase n t j = t / (2 * Real.pi) * Real.log (((n : ℝ) + j) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_div (by positivity) hn'.ne']
  rfl

/-- Cancellation of the normalization by `2π` gives the actual logarithmic angle. -/
theorem logarithmicPhase_angle (n : ℕ) (t : ℝ) (j : ℕ) :
    2 * Real.pi * logarithmicPhase n t j =
      t * (Real.log ((n : ℝ) + j) - Real.log n) := by
  unfold logarithmicPhase
  field_simp

/-- Exact phase increment between consecutive arithmetic samples. -/
theorem logarithmicPhase_increment {n : ℕ} (hn : 0 < n) (t : ℝ) (j : ℕ) :
    logarithmicPhase n t (j+1) - logarithmicPhase n t j =
      t / (2 * Real.pi) * Real.log (1 + 1 / ((n : ℝ) + j)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (0 : ℝ) < (n : ℝ) + j := by positivity
  have hr : (1 : ℝ) + 1 / ((n : ℝ) + j) =
      ((n : ℝ) + (j+1 : ℕ)) / ((n : ℝ) + j) := by
    push_cast
    field_simp
    ring
  rw [hr, Real.log_div (by positivity) hx.ne']
  unfold logarithmicPhase
  ring

/-- Every logarithmic increment is positive at positive height. -/
theorem logarithmicPhase_increment_pos {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    0 < logarithmicPhase n t (j+1) - logarithmicPhase n t j := by
  rw [logarithmicPhase_increment hn]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  apply mul_pos (div_pos ht (by positivity))
  apply Real.log_pos
  have : (0 : ℝ) < 1 / ((n : ℝ) + j) := by positivity
  linarith

/-- Uniform strict upper bound at every sample and positive height. -/
theorem logarithmicPhase_increment_lt {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) (j : ℕ) :
    logarithmicPhase n t (j+1) - logarithmicPhase n t j <
      t / (2 * Real.pi * ((n : ℝ) + j)) := by
  rw [logarithmicPhase_increment hn]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (0 : ℝ) < (n : ℝ) + j := by positivity
  have hi : (0 : ℝ) < 1 / ((n : ℝ) + j) := by positivity
  have hlog := Real.log_lt_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((n : ℝ) + j))
    (by linarith : (1 : ℝ) + 1 / ((n : ℝ) + j) ≠ 1)
  have h := mul_lt_mul_of_pos_left hlog (div_pos ht (by positivity : (0:ℝ)<2*Real.pi))
  calc
    _ < t / (2 * Real.pi) * (1 + 1 / ((n : ℝ) + j) - 1) := h
    _ = _ := by field_simp; ring

/-- The actual logarithmic increments strictly decrease along the integer lattice. -/
theorem logarithmicPhase_increment_strictAnti {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : 0 < t) (j : ℕ) :
    logarithmicPhase n t (j+2) - logarithmicPhase n t (j+1) <
      logarithmicPhase n t (j+1) - logarithmicPhase n t j := by
  rw [show j+2=j+1+1 by omega, logarithmicPhase_increment hn, logarithmicPhase_increment hn]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (0 : ℝ) < (n : ℝ) + j := by positivity
  apply mul_lt_mul_of_pos_left _ (div_pos ht (by positivity))
  apply Real.log_lt_log (by positivity)
  have hi : (1 : ℝ) / ((n : ℝ) + (j+1 : ℕ)) < 1 / ((n : ℝ) + j) := by
    apply (one_div_lt_one_div (by positivity) hx).mpr
    push_cast
    linarith
  linarith

/-- An explicit local height threshold places the increment in the first winding band. -/
theorem logarithmicPhase_increment_lt_one {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : 0 < t) (j : ℕ) (hband : t < 2 * Real.pi * ((n : ℝ) + j)) :
    logarithmicPhase n t (j+1) - logarithmicPhase n t j < 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact lt_trans (logarithmicPhase_increment_lt hn ht j)
    ((div_lt_one (by positivity)).mpr hband)

/-- No resonant sample occurs beyond the explicit local height threshold. -/
theorem logarithmicPhase_chord_nonzero {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : 0 < t) (j : ℕ) (hband : t < 2 * Real.pi * ((n : ℝ) + j)) :
    Real.sin (Real.pi * (logarithmicPhase n t (j+1) - logarithmicPhase n t j)) ≠ 0 :=
  (RHTower.Sieve.sin_pi_mul_pos (logarithmicPhase_increment_pos hn ht j)
    (logarithmicPhase_increment_lt_one hn ht j hband)).ne'

/-- Beyond that threshold the unweighted cotangent cost has its favorable sign. -/
theorem logarithmicPhase_cotangent_step_pos {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : 0 < t) (j : ℕ) (hband : t < 2 * Real.pi * ((n : ℝ) + j)) :
    0 < chordCotangent (logarithmicPhase n t) (j+1) -
      chordCotangent (logarithmicPhase n t) j := by
  exact sub_pos.mpr (cotangent_strictAnti
    (logarithmicPhase_increment_pos hn ht (j+1))
    (logarithmicPhase_increment_strictAnti hn ht j)
    (logarithmicPhase_increment_lt_one hn ht j hband))

/-- Every finite corrected prefix with at least two samples is strictly negative below `2πn`. -/
theorem logarithmicPhase_defect_neg {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : 0 < t) (hband : t < 2 * Real.pi * n) {M : ℕ} (hM : 0 < M) :
    phaseDefect (logarithmicPhase n t) M < 0 := by
  apply phaseDefect_neg hM (logarithmicPhase_zero n t)
    (fun j _ => logarithmicPhase_increment_pos hn ht j)
  · intro j hj
    apply logarithmicPhase_increment_lt_one hn ht j
    have hj' : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    nlinarith [Real.pi_pos]
  · intro j hj
    exact logarithmicPhase_increment_strictAnti hn ht j

/-- Exact complex-power identification, retaining both the anchor rotation and power weight. -/
theorem rotated_power_eq {n : ℕ} (hn : 0 < n) (σ t : ℝ) (j : ℕ) :
    Complex.exp (-(((t * Real.log n : ℝ) : ℂ) * Complex.I)) *
      (((n : ℝ) + j : ℝ) : ℂ) ^ (-((σ : ℂ) - (t : ℂ) * Complex.I)) =
      (powerWeight n σ j : ℂ) * phaseUnit (logarithmicPhase n t) j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (0 : ℝ) < (n : ℝ) + j := by positivity
  have hxC : (((n : ℝ) + j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero hxC, ← Complex.ofReal_log hx.le,
    powerWeight, Real.rpow_def_of_pos hx, Complex.ofReal_exp,
    phaseUnit, logarithmicPhase_angle, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The unit-anchored weighted sine sum is the imaginary part of the actual Dirichlet prefix. -/
theorem rawPrefix_im_eq (σ t : ℝ) (N : ℕ) :
    (rawPrefix ((σ : ℂ) - (t : ℂ) * Complex.I) N).im =
      ∑ j ∈ Finset.range N, powerWeight 1 σ j * Real.sin (2 * Real.pi * logarithmicPhase 1 t j) := by
  unfold rawPrefix
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hk : kernel ((σ : ℂ) - (t : ℂ) * Complex.I) (j+1) =
      (powerWeight 1 σ j : ℂ) * phaseUnit (logarithmicPhase 1 t) j := by
    have h := rotated_power_eq (n := 1) (by omega) σ t j
    simpa [kernel, add_comm] using h
  rw [hk, Complex.mul_im, phaseUnit_im]
  simp

/-- The actual source remainder plus every normalization and endpoint term. -/
def sourcePhaseDefect (σ t : ℝ) (M : ℕ) : ℝ :=
  let s : ℂ := (σ : ℂ) - (t : ℂ) * Complex.I
  (powerSumRemainder s (M+1) + riemannZeta s +
      ((M+1 : ℕ) : ℂ) ^ (1-s) / (1-s) + kernel s (M+1) / 2).im +
    powerWeight 1 σ M * Real.sin (2 * Real.pi * logarithmicPhase 1 t (M+1)) / 2 -
    powerWeight 1 σ M * chordCotangent (logarithmicPhase 1 t) M *
      (1 - Real.cos (2 * Real.pi * logarithmicPhase 1 t (M+1))) / 2

/-- Every source normalization and endpoint term is retained in the weighted defect. -/
theorem sourcePhaseDefect_eq_weighted (σ t : ℝ) (M : ℕ) :
    sourcePhaseDefect σ t M =
      weightedPhaseDefect (logarithmicPhase 1 t) (powerWeight 1 σ) M := by
  have he (s : ℂ) : powerSumRemainder s (M+1) + riemannZeta s +
      ((M+1 : ℕ) : ℂ) ^ (1-s) / (1-s) + kernel s (M+1) / 2 = rawPrefix s (M+1) := by
    unfold powerSumRemainder
    ring
  dsimp only [sourcePhaseDefect, weightedPhaseDefect]
  rw [he, rawPrefix_im_eq]

/-- Universal source identity: actual remainder, zeta, normalization, drifts, and resonances. -/
theorem sourcePhaseDefect_eq (σ t : ℝ) (M : ℕ) :
    sourcePhaseDefect σ t M =
      (∑ j ∈ Finset.range M,
        ((powerWeight 1 σ (j+1) - powerWeight 1 σ j) *
          Real.sin (2 * Real.pi * logarithmicPhase 1 t (j+1)) / 2 -
        (powerWeight 1 σ (j+1) * chordCotangent (logarithmicPhase 1 t) (j+1) -
          powerWeight 1 σ j * chordCotangent (logarithmicPhase 1 t) j) *
          (1 - Real.cos (2 * Real.pi * logarithmicPhase 1 t (j+1))) / 2)) +
      resonantPhasePrefix (logarithmicPhase 1 t) (powerWeight 1 σ) M := by
  rw [sourcePhaseDefect_eq_weighted]
  exact weightedPhaseDefect_eq _ M (logarithmicPhase_zero 1 t)


/-- After the explicit head, each extra sample weakly decreases the corrected unweighted defect. -/
theorem logarithmicPhase_defect_step_le {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : 0 < t) (M : ℕ) (hband : t < 2 * Real.pi * ((n : ℝ) + M)) :
    phaseDefect (logarithmicPhase n t) (M+1) ≤ phaseDefect (logarithmicPhase n t) M := by
  have hb : t < 2 * Real.pi * ((n : ℝ) + (M+1 : ℕ)) := by
    push_cast
    nlinarith [Real.pi_pos]
  rw [phaseDefect_step M (logarithmicPhase_zero n t)
    (logarithmicPhase_chord_nonzero hn ht (M+1) hb)]
  have hq := logarithmicPhase_cotangent_step_pos hn ht M hband
  have hc := Real.cos_le_one (2 * Real.pi * logarithmicPhase n t (M+1))
  have hp := mul_nonneg hq.le (sub_nonneg.mpr hc)
  linarith

/-- At every positive height the actual corrected unweighted head bounds all later cutoffs. -/
theorem logarithmicPhase_defect_le_head {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : 0 < t) {J M : ℕ} (hband : t < 2 * Real.pi * ((n : ℝ) + J)) (hJM : J ≤ M) :
    phaseDefect (logarithmicPhase n t) M ≤ phaseDefect (logarithmicPhase n t) J := by
  induction M, hJM using Nat.le_induction with
  | base => exact le_rfl
  | succ M hJM ih =>
    apply le_trans (logarithmicPhase_defect_step_le hn ht M _) ih
    have hjm : (J : ℝ) ≤ M := by exact_mod_cast hJM
    nlinarith [Real.pi_pos]

/-- At an exact closing phase the terminal correction vanishes and the literal sine sum is negative. -/
theorem logarithmicPhase_closed_prefix_neg {n : ℕ} (hn : 0 < n) {t : ℝ}
    (ht : 0 < t) (hband : t < 2 * Real.pi * n) {M : ℕ} (hM : 0 < M) (K : ℤ)
    (hclosed : t * Real.log (((n : ℝ) + (M+1 : ℕ)) / n) = (K : ℝ) * (2 * Real.pi)) :
    (∑ j ∈ Finset.range (M+1), Real.sin (t * Real.log (((n : ℝ) + j) / n))) < 0 := by
  have hang : 2 * Real.pi * logarithmicPhase n t (M+1) = (K : ℝ) * (2 * Real.pi) := by
    rw [logarithmicPhase_eq_log_ratio hn]
    convert hclosed using 1; field_simp
  have hs : Real.sin (2 * Real.pi * logarithmicPhase n t (M+1)) = 0 := by
    rw [hang]
    simpa using Real.sin_int_mul_two_pi_sub 0 K
  have hc : Real.cos (2 * Real.pi * logarithmicPhase n t (M+1)) = 1 := by
    rw [hang, Real.cos_int_mul_two_pi]
  have h := logarithmicPhase_defect_neg hn ht hband hM
  simp only [phaseDefect, weightedPhaseDefect, one_mul, hs, hc, sub_self, mul_zero,
    zero_div, add_zero, sub_zero] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [logarithmicPhase_eq_log_ratio hn]
  field_simp

end
end RHTower.LogarithmicCotangent
