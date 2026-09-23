import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenGroundState

/-!
# Polynomial and curvature bootstrap for the theta Born/Witten state

The exact square-root theta source state is promoted to the polynomial test vectors used by the
quantum-mechanical bootstrap.  The file identifies the full theta source as a sum of pure-state
densities, proves its logarithmic Witten curvature, classifies the half-line Robin anomaly, and
connects the resulting position moments directly to the existing prime-archimedean Hankel consumer.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Logarithmic curvature of the exact Born/Witten density. -/
def thetaCuspBornWittenLogCurvature (n : ℕ) (x : ℝ) : ℝ :=
  2 * thetaCuspBornWittenCurvature n x

/-- Negative logarithm of the exact Born/Witten density. -/
def thetaCuspBornWittenLogDensityPotential (n : ℕ) (x : ℝ) : ℝ :=
  -Real.log (thetaCuspBornWittenAmplitude n x ^ (2 : ℕ))

/-- Polynomial bootstrap vector dressed by the exact Born/Witten ground state. -/
def thetaCuspBornWittenDressedPolynomial
    (n : ℕ) (P : ℝ[X]) (x : ℝ) : ℝ :=
  P.eval x * thetaCuspBornWittenAmplitude n x

theorem thetaCuspBornWittenAmplitude_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspBornWittenAmplitude n x := by
  have hq := thetaCuspBornWittenWeight_pos hn hx
  have hψ : 0 < thetaCuspMorseGroundState n x := by
    simpa only [thetaCuspMorseGroundState] using
      thetaCuspMorseZeroMode_pos (5 / 4 : ℝ) hn x
  unfold thetaCuspBornWittenAmplitude
  positivity

theorem thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq_of_nonneg
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x n =
      Real.pi * thetaCuspBornWittenAmplitude n x ^ (2 : ℕ) := by
  cases n with
  | zero =>
      simp [thetaCuspSourceTerm, thetaCuspSeed, thetaCuspBornWittenAmplitude,
        thetaCuspMorseGroundState, thetaCuspMorseZeroMode]
  | succ n =>
      exact thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq (by omega) hx

/-- The full positive theta source is a sum of exact Born/Witten pure-state densities. -/
theorem thetaCuspFullSource_eq_pi_mul_tsum_bornWittenAmplitude_sq
    {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspFullSource x =
      Real.pi * ∑' n : ℕ, thetaCuspBornWittenAmplitude n x ^ (2 : ℕ) := by
  unfold thetaCuspFullSource
  rw [tsum_congr (fun n =>
    thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq_of_nonneg n hx),
    tsum_mul_left]

theorem hasDerivAt_thetaCuspBornWittenLogDensityPotential
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspBornWittenLogDensityPotential n)
      (2 * thetaCuspBornWittenSuperpotential n x) x := by
  have hχ := hasDerivAt_thetaCuspBornWittenAmplitude hn hx
  have hχpos := thetaCuspBornWittenAmplitude_pos hn hx
  have hsq := hχ.pow 2
  have hlog := hsq.log (pow_ne_zero 2 hχpos.ne')
  change HasDerivAt
    (-(fun y : ℝ =>
      Real.log ((thetaCuspBornWittenAmplitude n ^ (2 : ℕ)) y)))
    (2 * thetaCuspBornWittenSuperpotential n x) x
  exact hlog.neg.congr_deriv
    (g' := 2 * thetaCuspBornWittenSuperpotential n x) (by
      field_simp [hχpos.ne']
      simp only [Pi.pow_apply]
      ring)

theorem hasDerivAt_two_thetaCuspBornWittenSuperpotential
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => 2 * thetaCuspBornWittenSuperpotential n y)
      (thetaCuspBornWittenLogCurvature n x) x := by
  simpa only [thetaCuspBornWittenLogCurvature] using
    (hasDerivAt_thetaCuspBornWittenSuperpotential hn hx).const_mul 2

theorem thetaCuspBornWittenLogCurvature_floor
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    4 * Real.pi * (n : ℝ) ^ (2 : ℕ) ≤ thetaCuspBornWittenLogCurvature n x := by
  have h := thetaCuspBornWittenCurvature_floor hn hx
  simp only [thetaCuspBornWittenLogCurvature]
  nlinarith

theorem hasDerivAt_thetaCuspBornWittenDressedPolynomial
    {n : ℕ} (hn : 0 < n) (P : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspBornWittenDressedPolynomial n P)
      (P.derivative.eval x * thetaCuspBornWittenAmplitude n x -
        thetaCuspBornWittenSuperpotential n x *
          thetaCuspBornWittenDressedPolynomial n P x) x := by
  have hP := P.hasDerivAt x
  have hχ := hasDerivAt_thetaCuspBornWittenAmplitude hn hx
  change HasDerivAt
    (fun y : ℝ => P.eval y * thetaCuspBornWittenAmplitude n y)
    (P.derivative.eval x * thetaCuspBornWittenAmplitude n x -
      thetaCuspBornWittenSuperpotential n x *
        (P.eval x * thetaCuspBornWittenAmplitude n x)) x
  exact (hP.mul hχ).congr_deriv
    (g' := P.derivative.eval x * thetaCuspBornWittenAmplitude n x -
      thetaCuspBornWittenSuperpotential n x *
        (P.eval x * thetaCuspBornWittenAmplitude n x)) (by ring)

theorem thetaCuspBornWitten_supercharge_dressedPolynomial
    {n : ℕ} (hn : 0 < n) (P : ℝ[X]) {x : ℝ} (hx : 0 ≤ x) :
    deriv (thetaCuspBornWittenDressedPolynomial n P) x +
        thetaCuspBornWittenSuperpotential n x *
          thetaCuspBornWittenDressedPolynomial n P x =
      P.derivative.eval x * thetaCuspBornWittenAmplitude n x := by
  rw [(hasDerivAt_thetaCuspBornWittenDressedPolynomial hn P hx).deriv]
  ring

theorem thetaCuspBornWitten_robinDefect_dressedPolynomial
    {n : ℕ} (hn : 0 < n) (P : ℝ[X]) :
    deriv (thetaCuspBornWittenDressedPolynomial n P) 0 +
        thetaCuspBornWittenSuperpotential n 0 *
          thetaCuspBornWittenDressedPolynomial n P 0 =
      P.derivative.eval 0 * thetaCuspBornWittenAmplitude n 0 := by
  exact thetaCuspBornWitten_supercharge_dressedPolynomial hn P (by norm_num)

theorem thetaCuspBornWitten_robinDefect_eq_zero_iff
    {n : ℕ} (hn : 0 < n) (P : ℝ[X]) :
    deriv (thetaCuspBornWittenDressedPolynomial n P) 0 +
          thetaCuspBornWittenSuperpotential n 0 *
            thetaCuspBornWittenDressedPolynomial n P 0 = 0 ↔
      P.derivative.eval 0 = 0 := by
  rw [thetaCuspBornWitten_robinDefect_dressedPolynomial hn]
  exact mul_eq_zero.trans
    (or_iff_left (thetaCuspBornWittenAmplitude_pos hn (by norm_num)).ne')

theorem thetaCuspBornWittenMomentTestPolynomial_robinDefect
    (j : ℕ) {n : ℕ} (hn : 0 < n) :
    deriv (thetaCuspBornWittenDressedPolynomial n
          (thetaCuspMorseMomentTestPolynomial j)) 0 +
        thetaCuspBornWittenSuperpotential n 0 *
          thetaCuspBornWittenDressedPolynomial n
            (thetaCuspMorseMomentTestPolynomial j) 0 =
      if j = 0 then thetaCuspBornWittenAmplitude n 0 else 0 := by
  rw [thetaCuspBornWitten_robinDefect_dressedPolynomial hn,
    thetaCuspMorseMomentTestPolynomial_derivative_eval]
  cases j with
  | zero => simp
  | succ j => simp

/-- Every even central Xi jet is a countable sum of exact Born/Witten position moments.  This is
the direct interface from the pure-state decomposition to the all-order cumulant and Taylor
machinery; it introduces no spectral realization of `XiC`. -/
theorem iteratedDeriv_XiC_zero_eq_tsum_bornWittenAmplitude_sq (j : ℕ) :
    iteratedDeriv (2 * j) XiC 0 =
      (((-1 : ℝ) ^ j *
        ∑' n : ℕ, 2 * Real.pi *
          ∫ x : ℝ in Ioi 0,
            x ^ (2 * j) * thetaCuspBornWittenAmplitude n x ^ (2 : ℕ) : ℝ) : ℂ) := by
  rw [iteratedDeriv_XiC_zero_eq_rawEvenMoment,
    thetaCuspRawEvenMoment_eq_tsum_integral_bornWittenAmplitude_sq]

/-- Direct pure-state replacement for the two remaining hypotheses in the linear
prime-archimedean Hankel consumer. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_bornWittenAmplitude
    (hupper :
      14 * ((3005 / 2997 : ℝ) *
          (∫ x : ℝ in Ioi 0, x ^ (4 : ℕ) * thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ))) ^ (2 : ℕ) ≤
        9 *
          (∫ x : ℝ in Ioi 0, x ^ (2 : ℕ) * thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ)) *
          (∫ x : ℝ in Ioi 0, x ^ (6 : ℕ) * thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ)))
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          (∫ x : ℝ in Ioi 0, thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ))) *
          ((3005 / 2997 : ℝ) *
            (∫ x : ℝ in Ioi 0, x ^ (4 : ℕ) * thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ))) ≤
        45 *
          (∫ x : ℝ in Ioi 0,
            x ^ (2 : ℕ) * thetaCuspBornWittenAmplitude 1 x ^ (2 : ℕ)) ^ (2 : ℕ)) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  apply forall_primeArchSourceTraceHankel_linear_nonneg_of_morseBorn
  · rw [thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq,
      thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq,
      thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq]
    norm_num only [Nat.reduceMul]
    exact hupper
  · rw [thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq,
      thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq,
      thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq]
    norm_num only [Nat.reduceMul, pow_zero, one_mul]
    exact hrelaxed

end
end RHTower
