import GaloisForLFunctions.RHTower.PrimeArchThetaMorseAnomalousDarboux

/-!
# The theta source as an exact Witten ground-state density

The positive observable multiplying the Morse ground state can be absorbed into the wavefunction.
For every positive theta atom this produces a source-defined half-line Witten zero mode whose
square is exactly the theta source density.  Its logarithmic superpotential has an explicit
strictly positive derivative, so the source comes with a pointwise curvature certificate rather
than only a positive-observable representation.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive observable multiplying the original Morse ground-state density. -/
def thetaCuspBornWittenWeight (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspMorseSuperpotential (5 / 4 : ℝ) n x - 1 / 4

/-- The observable-weighted theta amplitude. -/
def thetaCuspBornWittenAmplitude (n : ℕ) (x : ℝ) : ℝ :=
  2 * Real.sqrt (thetaCuspBornWittenWeight n x) *
    thetaCuspMorseGroundState n x

/-- Superpotential of the observable-weighted theta amplitude. -/
def thetaCuspBornWittenSuperpotential (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspMorseSuperpotential (5 / 4 : ℝ) n x -
    thetaCuspMorseScale n x / thetaCuspBornWittenWeight n x

/-- Exact derivative of the observable-weighted superpotential. -/
def thetaCuspBornWittenCurvature (n : ℕ) (x : ℝ) : ℝ :=
  2 * thetaCuspMorseScale n x +
    3 * thetaCuspMorseScale n x / thetaCuspBornWittenWeight n x ^ 2

/-- Lower supersymmetric potential selected by the weighted theta amplitude. -/
def thetaCuspBornWittenPotentialMinus (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspBornWittenSuperpotential n x ^ 2 -
    thetaCuspBornWittenCurvature n x

/-- Partner supersymmetric potential selected by the weighted theta amplitude. -/
def thetaCuspBornWittenPotentialPlus (n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspBornWittenSuperpotential n x ^ 2 +
    thetaCuspBornWittenCurvature n x

theorem thetaCuspBornWittenWeight_eq (n : ℕ) (x : ℝ) :
    thetaCuspBornWittenWeight n x = thetaCuspMorseScale n x - 3 / 2 := by
  simp only [thetaCuspBornWittenWeight, thetaCuspMorseSuperpotential]
  ring

theorem thetaCuspBornWittenWeight_pos
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    0 < thetaCuspBornWittenWeight n x := by
  exact thetaCuspMorseBornObservable_pos hn hx

theorem hasDerivAt_thetaCuspBornWittenWeight (n : ℕ) (x : ℝ) :
    HasDerivAt (thetaCuspBornWittenWeight n)
      (2 * thetaCuspMorseScale n x) x := by
  exact (hasDerivAt_thetaCuspMorseSuperpotential (5 / 4 : ℝ) n x).sub_const (1 / 4)

/-- The squared weighted amplitude is exactly the original positive-observable Born density. -/
theorem thetaCuspBornWittenAmplitude_sq
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspBornWittenAmplitude n x ^ 2 =
      4 * thetaCuspBornWittenWeight n x * thetaCuspMorseGroundState n x ^ 2 := by
  have hq := (thetaCuspBornWittenWeight_pos hn hx).le
  rw [thetaCuspBornWittenAmplitude, mul_pow, mul_pow, Real.sq_sqrt hq]
  ring

/-- Every positive theta atom is exactly `pi` times one pure Witten-state density. -/
theorem thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    thetaCuspSourceTerm x n =
      Real.pi * thetaCuspBornWittenAmplitude n x ^ 2 := by
  rw [thetaCuspSourceTerm_eq_morseBornObservable,
    thetaCuspBornWittenAmplitude_sq hn hx]
  simp only [thetaCuspBornWittenWeight]
  ring

/-- Exact first-order Witten equation for the source amplitude. -/
theorem hasDerivAt_thetaCuspBornWittenAmplitude
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspBornWittenAmplitude n)
      (-thetaCuspBornWittenSuperpotential n x *
        thetaCuspBornWittenAmplitude n x) x := by
  have hqpos := thetaCuspBornWittenWeight_pos hn hx
  have hq := hasDerivAt_thetaCuspBornWittenWeight n x
  have hsqrt := hq.sqrt hqpos.ne'
  have hpsi := hasDerivAt_thetaCuspMorseGroundState n x
  convert (hsqrt.const_mul 2).mul hpsi using 1
  simp only [thetaCuspBornWittenAmplitude, thetaCuspBornWittenSuperpotential]
  have hsqrtPos : 0 < Real.sqrt (thetaCuspBornWittenWeight n x) :=
    Real.sqrt_pos.2 hqpos
  have hsqrtSq : Real.sqrt (thetaCuspBornWittenWeight n x) ^ 2 =
      thetaCuspBornWittenWeight n x := Real.sq_sqrt hqpos.le
  field_simp [hsqrtPos.ne', hqpos.ne']
  rw [hsqrtSq]
  ring

theorem thetaCuspBornWitten_supercharge_zero
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    deriv (thetaCuspBornWittenAmplitude n) x +
        thetaCuspBornWittenSuperpotential n x *
          thetaCuspBornWittenAmplitude n x = 0 := by
  rw [(hasDerivAt_thetaCuspBornWittenAmplitude hn hx).deriv]
  ring

/-- The new superpotential has an exact positive curvature formula. -/
theorem hasDerivAt_thetaCuspBornWittenSuperpotential
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (thetaCuspBornWittenSuperpotential n)
      (thetaCuspBornWittenCurvature n x) x := by
  have hqpos := thetaCuspBornWittenWeight_pos hn hx
  have hscale := hasDerivAt_thetaCuspMorseScale n x
  have hweight := hasDerivAt_thetaCuspBornWittenWeight n x
  have hquot := hscale.div hweight hqpos.ne'
  have hW := hasDerivAt_thetaCuspMorseSuperpotential (5 / 4 : ℝ) n x
  convert hW.sub hquot using 1
  simp only [thetaCuspBornWittenCurvature]
  rw [thetaCuspBornWittenWeight_eq]
  field_simp [show thetaCuspMorseScale n x - 3 / 2 ≠ 0 by
    simpa only [← thetaCuspBornWittenWeight_eq] using hqpos.ne']
  ring

theorem deriv_thetaCuspBornWittenSuperpotential
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    deriv (thetaCuspBornWittenSuperpotential n) x =
      thetaCuspBornWittenCurvature n x :=
  (hasDerivAt_thetaCuspBornWittenSuperpotential hn hx).deriv

theorem thetaCuspMorseScale_pi_mul_sq_le
    {n : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    Real.pi * (n : ℝ) ^ 2 ≤ thetaCuspMorseScale n x := by
  have hexp : (1 : ℝ) ≤ Real.exp x := Real.one_le_exp hx
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hmul : (n : ℝ) ≤ (n : ℝ) * Real.exp x := by
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hexp)]
  have hsq : (n : ℝ) ^ 2 ≤ ((n : ℝ) * Real.exp x) ^ 2 := by
    nlinarith
  simpa only [thetaCuspMorseScale] using
    mul_le_mul_of_nonneg_left hsq Real.pi_pos.le

/-- Uniform positive curvature of the pure theta source state. -/
theorem thetaCuspBornWittenCurvature_floor
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    2 * Real.pi * (n : ℝ) ^ 2 ≤ thetaCuspBornWittenCurvature n x := by
  have hqpos := thetaCuspBornWittenWeight_pos hn hx
  have ht := thetaCuspMorseScale_pi_mul_sq_le (n := n) hx
  have hscaleNonneg : 0 ≤ thetaCuspMorseScale n x := by
    simp only [thetaCuspMorseScale]
    positivity
  have hcorr : 0 ≤
      3 * thetaCuspMorseScale n x / thetaCuspBornWittenWeight n x ^ 2 := by
    positivity
  simp only [thetaCuspBornWittenCurvature]
  nlinarith

theorem thetaCuspBornWittenPotentialPlus_floor
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    2 * Real.pi * (n : ℝ) ^ 2 ≤ thetaCuspBornWittenPotentialPlus n x := by
  have hcurv := thetaCuspBornWittenCurvature_floor hn hx
  simp only [thetaCuspBornWittenPotentialPlus]
  nlinarith [sq_nonneg (thetaCuspBornWittenSuperpotential n x)]

theorem hasDerivAt_neg_thetaCuspBornWittenSuperpotential_mul_amplitude
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ =>
      -thetaCuspBornWittenSuperpotential n y * thetaCuspBornWittenAmplitude n y)
      (thetaCuspBornWittenPotentialMinus n x *
        thetaCuspBornWittenAmplitude n x) x := by
  have hB := hasDerivAt_thetaCuspBornWittenSuperpotential hn hx
  have hchi := hasDerivAt_thetaCuspBornWittenAmplitude hn hx
  convert hB.neg.mul hchi using 1
  simp only [thetaCuspBornWittenPotentialMinus, Pi.neg_apply]
  ring

/-- Factorized zero-energy equation for the observable-weighted theta source.  The differentiated
first-order right-hand side is exactly the lower Witten Hamiltonian term. -/
theorem thetaCuspBornWitten_factorized_schrodinger_zero
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    -deriv (fun y : ℝ =>
        -thetaCuspBornWittenSuperpotential n y *
          thetaCuspBornWittenAmplitude n y) x +
        thetaCuspBornWittenPotentialMinus n x *
          thetaCuspBornWittenAmplitude n x = 0 := by
  rw [(hasDerivAt_neg_thetaCuspBornWittenSuperpotential_mul_amplitude hn hx).deriv]
  ring

/-- The pure-state density obeys the exact first-order logarithmic curvature equation. -/
theorem hasDerivAt_thetaCuspBornWittenAmplitude_sq
    {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => thetaCuspBornWittenAmplitude n y ^ 2)
      (-2 * thetaCuspBornWittenSuperpotential n x *
        thetaCuspBornWittenAmplitude n x ^ 2) x := by
  convert (hasDerivAt_thetaCuspBornWittenAmplitude hn hx).pow 2 using 1
  all_goals ring

/-- Existing Morse Born moments are ordinary position moments of the exact pure Witten state. -/
theorem thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq
    (j n : ℕ) :
    thetaCuspMorseBornMoment j n =
      ∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspBornWittenAmplitude n x ^ 2 := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCuspMorseBornMoment, thetaCuspBornWittenAmplitude,
      thetaCuspMorseGroundState, thetaCuspMorseZeroMode]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    rw [thetaCuspMorseBornMoment]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [thetaCuspBornWittenAmplitude_sq hnpos hx.le]
    simp only [thetaCuspBornWittenWeight]
    ring

/-- Every theta atom moment is a pure-state position moment, with no remaining observable
insertion. -/
theorem thetaCuspAtomRawEvenMoment_eq_integral_bornWittenAmplitude_sq
    (j n : ℕ) :
    thetaCuspAtomRawEvenMoment j n =
      2 * Real.pi *
        ∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspBornWittenAmplitude n x ^ 2 := by
  rw [thetaCuspAtomRawEvenMoment_eq_morseBornMoment,
    thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq]

/-- The full theta-cusp raw moment is a countable sum of exact pure-state position moments. -/
theorem thetaCuspRawEvenMoment_eq_tsum_integral_bornWittenAmplitude_sq (j : ℕ) :
    thetaCuspRawEvenMoment j =
      ∑' n : ℕ, 2 * Real.pi *
        ∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspBornWittenAmplitude n x ^ 2 := by
  rw [thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment]
  apply tsum_congr
  intro n
  exact thetaCuspAtomRawEvenMoment_eq_integral_bornWittenAmplitude_sq j n

end

end RHTower
