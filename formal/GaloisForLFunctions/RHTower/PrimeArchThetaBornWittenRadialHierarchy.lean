import GaloisForLFunctions.RHTower.PrimeArchThetaBornWittenSourceMoment

/-!
# Radial Born--Witten hierarchy of the theta-cusp source

Multiplication by `x ^ k` turns the exact theta-cusp Born/Witten state into a radial
supersymmetric ground state.  Its superpotential acquires the centrifugal term `-k / x`, its
curvature acquires `k / x ^ 2`, and its ordinary position moments are precisely the `k`-shifted
theta-cusp atom moments.

Consequently every even central Xi jet is a countable sum of squared norms of radial zero modes.
For `k = 1`, the remaining first-atom inequality in the linear prime-archimedean Hankel consumer
is the degree-two moment inequality of the Dirichlet state `x * chi_1`.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The `k`-th radial theta-cusp state. -/
def thetaCuspBornWittenRadialAmplitude (k n : ℕ) (x : ℝ) : ℝ :=
  x ^ k * thetaCuspBornWittenAmplitude n x

/-- Radial superpotential, including the exact centrifugal `-k/x` term. -/
def thetaCuspBornWittenRadialSuperpotential (k n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspBornWittenSuperpotential n x - (k : ℝ) / x

/-- Exact derivative of the radial superpotential on the open half-line. -/
def thetaCuspBornWittenRadialCurvature (k n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspBornWittenCurvature n x + (k : ℝ) / x ^ 2

/-- Negative logarithm of the radial state density. -/
def thetaCuspBornWittenRadialLogDensityPotential (k n : ℕ) (x : ℝ) : ℝ :=
  -Real.log (thetaCuspBornWittenRadialAmplitude k n x ^ 2)

/-- Log-density curvature of the radial state. -/
def thetaCuspBornWittenRadialLogCurvature (k n : ℕ) (x : ℝ) : ℝ :=
  2 * thetaCuspBornWittenRadialCurvature k n x

/-- Lower factorized Hamiltonian potential of the radial state. -/
def thetaCuspBornWittenRadialPotentialMinus (k n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspBornWittenRadialSuperpotential k n x ^ 2 -
    thetaCuspBornWittenRadialCurvature k n x

/-- Partner factorized Hamiltonian potential of the radial state. -/
def thetaCuspBornWittenRadialPotentialPlus (k n : ℕ) (x : ℝ) : ℝ :=
  thetaCuspBornWittenRadialSuperpotential k n x ^ 2 +
    thetaCuspBornWittenRadialCurvature k n x

/-- The `2j`-th position moment of the `k`-th radial state. -/
def thetaCuspBornWittenRadialRawMoment (j k n : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0,
    x ^ (2 * j) * thetaCuspBornWittenRadialAmplitude k n x ^ 2

/-- Total squared norm of the radial zero modes of index `j`. -/
def thetaCuspBornWittenRadialNorm (j : ℕ) : ℝ :=
  ∑' n : ℕ, 2 * Real.pi * thetaCuspBornWittenRadialRawMoment 0 j n

theorem thetaCuspBornWittenRadialAmplitude_sq (k n : ℕ) (x : ℝ) :
    thetaCuspBornWittenRadialAmplitude k n x ^ 2 =
      x ^ (2 * k) * thetaCuspBornWittenAmplitude n x ^ 2 := by
  simp only [thetaCuspBornWittenRadialAmplitude, mul_pow]
  rw [show 2 * k = k * 2 by omega, pow_mul]

/-- The radial density is exactly the source density with the moment weight absorbed into the
wavefunction. -/
theorem thetaCusp_pow_mul_sourceTerm_eq_pi_mul_radialAmplitude_sq
    (k : ℕ) {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    x ^ (2 * k) * thetaCuspSourceTerm x n =
      Real.pi * thetaCuspBornWittenRadialAmplitude k n x ^ 2 := by
  rw [thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq hn hx,
    thetaCuspBornWittenRadialAmplitude_sq]
  ring

theorem thetaCuspBornWittenRadialAmplitude_pos
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    0 < thetaCuspBornWittenRadialAmplitude k n x := by
  exact mul_pos (pow_pos hx k) (thetaCuspBornWittenAmplitude_pos hn hx.le)

/-- Positive radial index replaces the base Robin trace by a Dirichlet trace. -/
theorem thetaCuspBornWittenRadialAmplitude_zero
    {k : ℕ} (hk : 0 < k) (n : ℕ) :
    thetaCuspBornWittenRadialAmplitude k n 0 = 0 := by
  simp [thetaCuspBornWittenRadialAmplitude, Nat.ne_of_gt hk]

/-- Exact first-order radial Witten equation on the open half-line. -/
theorem hasDerivAt_thetaCuspBornWittenRadialAmplitude
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspBornWittenRadialAmplitude k n)
      (-thetaCuspBornWittenRadialSuperpotential k n x *
        thetaCuspBornWittenRadialAmplitude k n x) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ k)
      ((k : ℝ) * x ^ (k - 1)) x := hasDerivAt_pow k x
  have hamp := hasDerivAt_thetaCuspBornWittenAmplitude hn hx.le
  convert hpow.mul hamp using 1
  simp only [thetaCuspBornWittenRadialAmplitude,
    thetaCuspBornWittenRadialSuperpotential]
  field_simp [hx.ne']
  cases k with
  | zero => simp; ring
  | succ k =>
      simp only [Nat.cast_succ, Nat.succ_sub_one, pow_succ]
      ring

theorem thetaCuspBornWittenRadial_supercharge_zero
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    deriv (thetaCuspBornWittenRadialAmplitude k n) x +
        thetaCuspBornWittenRadialSuperpotential k n x *
          thetaCuspBornWittenRadialAmplitude k n x = 0 := by
  rw [(hasDerivAt_thetaCuspBornWittenRadialAmplitude hn hx).deriv]
  ring

/-- The inverse-square centrifugal curvature is exact, not a comparison estimate. -/
theorem hasDerivAt_thetaCuspBornWittenRadialSuperpotential
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspBornWittenRadialSuperpotential k n)
      (thetaCuspBornWittenRadialCurvature k n x) x := by
  have hB := hasDerivAt_thetaCuspBornWittenSuperpotential hn hx.le
  have hinv := (hasDerivAt_id x).inv hx.ne'
  have hkinv := hinv.const_mul (k : ℝ)
  convert hB.sub hkinv using 1
  simp only [thetaCuspBornWittenRadialCurvature, div_eq_mul_inv, id_eq]
  ring

theorem deriv_thetaCuspBornWittenRadialSuperpotential
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    deriv (thetaCuspBornWittenRadialSuperpotential k n) x =
      thetaCuspBornWittenRadialCurvature k n x :=
  (hasDerivAt_thetaCuspBornWittenRadialSuperpotential hn hx).deriv

/-- The radial state retains the source curvature floor and gains `k/x^2`. -/
theorem thetaCuspBornWittenRadialCurvature_floor
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    2 * Real.pi * (n : ℝ) ^ 2 + (k : ℝ) / x ^ 2 ≤
      thetaCuspBornWittenRadialCurvature k n x := by
  have h := thetaCuspBornWittenCurvature_floor hn hx.le
  simp only [thetaCuspBornWittenRadialCurvature]
  linarith

theorem hasDerivAt_thetaCuspBornWittenRadialLogDensityPotential
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (thetaCuspBornWittenRadialLogDensityPotential k n)
      (2 * thetaCuspBornWittenRadialSuperpotential k n x) x := by
  have hamp := hasDerivAt_thetaCuspBornWittenRadialAmplitude (k := k) hn hx
  have hamppos := thetaCuspBornWittenRadialAmplitude_pos (k := k) hn hx
  have hsq := hamp.pow 2
  have hlog := hsq.log (pow_ne_zero 2 hamppos.ne')
  convert hlog.neg using 1
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one]
  field_simp [hamppos.ne']

theorem hasDerivAt_two_thetaCuspBornWittenRadialSuperpotential
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => 2 * thetaCuspBornWittenRadialSuperpotential k n y)
      (thetaCuspBornWittenRadialLogCurvature k n x) x := by
  simpa only [thetaCuspBornWittenRadialLogCurvature] using
    (hasDerivAt_thetaCuspBornWittenRadialSuperpotential hn hx).const_mul 2

/-- Log-density curvature gains the exact radial term `2k/x^2`. -/
theorem thetaCuspBornWittenRadialLogCurvature_floor
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    4 * Real.pi * (n : ℝ) ^ 2 + 2 * (k : ℝ) / x ^ 2 ≤
      thetaCuspBornWittenRadialLogCurvature k n x := by
  have h := thetaCuspBornWittenRadialCurvature_floor (k := k) hn hx
  calc
    4 * Real.pi * (n : ℝ) ^ 2 + 2 * (k : ℝ) / x ^ 2 =
        2 * (2 * Real.pi * (n : ℝ) ^ 2 + (k : ℝ) / x ^ 2) := by ring
    _ ≤ 2 * thetaCuspBornWittenRadialCurvature k n x :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ = thetaCuspBornWittenRadialLogCurvature k n x := rfl

/-- Exact centrifugal decomposition of the lower radial partner. -/
theorem thetaCuspBornWittenRadialPotentialMinus_eq
    {k n : ℕ} {x : ℝ} (hx : x ≠ 0) :
    thetaCuspBornWittenRadialPotentialMinus k n x =
      thetaCuspBornWittenPotentialMinus n x -
        2 * (k : ℝ) * thetaCuspBornWittenSuperpotential n x / x +
        (k : ℝ) * ((k : ℝ) - 1) / x ^ 2 := by
  simp only [thetaCuspBornWittenRadialPotentialMinus,
    thetaCuspBornWittenRadialSuperpotential,
    thetaCuspBornWittenRadialCurvature,
    thetaCuspBornWittenPotentialMinus]
  field_simp [hx]
  ring

/-- Exact centrifugal decomposition of the upper radial partner. -/
theorem thetaCuspBornWittenRadialPotentialPlus_eq
    {k n : ℕ} {x : ℝ} (hx : x ≠ 0) :
    thetaCuspBornWittenRadialPotentialPlus k n x =
      thetaCuspBornWittenPotentialPlus n x -
        2 * (k : ℝ) * thetaCuspBornWittenSuperpotential n x / x +
        (k : ℝ) * ((k : ℝ) + 1) / x ^ 2 := by
  simp only [thetaCuspBornWittenRadialPotentialPlus,
    thetaCuspBornWittenRadialSuperpotential,
    thetaCuspBornWittenRadialCurvature,
    thetaCuspBornWittenPotentialPlus]
  field_simp [hx]
  ring

theorem hasDerivAt_neg_thetaCuspBornWittenRadialSuperpotential_mul_amplitude
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ =>
      -thetaCuspBornWittenRadialSuperpotential k n y *
        thetaCuspBornWittenRadialAmplitude k n y)
      (thetaCuspBornWittenRadialPotentialMinus k n x *
        thetaCuspBornWittenRadialAmplitude k n x) x := by
  have hB := hasDerivAt_thetaCuspBornWittenRadialSuperpotential (k := k) hn hx
  have hamp := hasDerivAt_thetaCuspBornWittenRadialAmplitude (k := k) hn hx
  convert hB.neg.mul hamp using 1
  simp only [thetaCuspBornWittenRadialPotentialMinus, Pi.neg_apply]
  ring

/-- Every radial member satisfies its exact factorized zero-energy Schrödinger equation. -/
theorem thetaCuspBornWittenRadial_factorized_schrodinger_zero
    {k n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    -deriv (fun y : ℝ =>
        -thetaCuspBornWittenRadialSuperpotential k n y *
          thetaCuspBornWittenRadialAmplitude k n y) x +
        thetaCuspBornWittenRadialPotentialMinus k n x *
          thetaCuspBornWittenRadialAmplitude k n x = 0 := by
  rw [(hasDerivAt_neg_thetaCuspBornWittenRadialSuperpotential_mul_amplitude
    hn hx).deriv]
  ring

/-- Radial position moments are the shifted position moments of the base state. -/
theorem thetaCuspBornWittenRadialRawMoment_eq_shifted
    (j k n : ℕ) :
    thetaCuspBornWittenRadialRawMoment j k n =
      ∫ x : ℝ in Ioi 0,
        x ^ (2 * (j + k)) * thetaCuspBornWittenAmplitude n x ^ 2 := by
  unfold thetaCuspBornWittenRadialRawMoment
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  rw [thetaCuspBornWittenRadialAmplitude_sq]
  rw [show 2 * (j + k) = 2 * j + 2 * k by omega, pow_add]
  ring

/-- The `j`-th moment of the `k`-th radial state is exactly atom moment `j+k`. -/
theorem thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment
    (j k n : ℕ) :
    thetaCuspAtomRawEvenMoment (j + k) n =
      2 * Real.pi * thetaCuspBornWittenRadialRawMoment j k n := by
  rw [thetaCuspAtomRawEvenMoment_eq_integral_bornWittenAmplitude_sq,
    thetaCuspBornWittenRadialRawMoment_eq_shifted]

/-- Any raw moment tail can be read in the radial sector indexed by a smaller moment order. -/
theorem thetaCuspRawEvenMoment_eq_tsum_radialBornWittenRawMoment
    {j k : ℕ} (hk : k ≤ j) :
    thetaCuspRawEvenMoment j =
      ∑' n : ℕ, 2 * Real.pi *
        thetaCuspBornWittenRadialRawMoment (j - k) k n := by
  rw [thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment]
  apply tsum_congr
  intro n
  simpa only [Nat.sub_add_cancel hk] using
    thetaCuspAtomRawEvenMoment_eq_radialBornWittenRawMoment (j - k) k n

/-- The `2j`-th theta moment is the total squared norm of the `j`-th radial zero modes. -/
theorem thetaCuspRawEvenMoment_eq_tsum_radialBornWitten_norm (j : ℕ) :
    thetaCuspRawEvenMoment j =
      ∑' n : ℕ, 2 * Real.pi *
        thetaCuspBornWittenRadialRawMoment 0 j n := by
  simpa only [Nat.sub_self] using
    thetaCuspRawEvenMoment_eq_tsum_radialBornWittenRawMoment (le_refl j)

theorem thetaCuspBornWittenRawMoment_eq_tsum_radialBornWitten_norm (j : ℕ) :
    thetaCuspBornWittenRawMoment j =
      ∑' n : ℕ, 2 * Real.pi *
        thetaCuspBornWittenRadialRawMoment 0 j n := by
  rw [thetaCuspBornWittenRawMoment_eq_thetaCuspRawEvenMoment,
    thetaCuspRawEvenMoment_eq_tsum_radialBornWitten_norm]

theorem thetaCuspBornWittenRadialNorm_eq_rawMoment (j : ℕ) :
    thetaCuspBornWittenRadialNorm j = thetaCuspBornWittenRawMoment j := by
  rw [thetaCuspBornWittenRadialNorm,
    thetaCuspBornWittenRawMoment_eq_tsum_radialBornWitten_norm]

/-- The normalized prime-archimedean source value is exactly a quadratic expression in three
radial zero-mode norms. -/
theorem thetaCuspBornWittenQuadraticSource_eq_radialNorm :
    thetaCuspBornWittenQuadraticSource =
      (thetaCuspBornWittenRadialNorm 1 /
          thetaCuspBornWittenRadialNorm 0) ^ 2 / 2 -
        (thetaCuspBornWittenRadialNorm 2 /
          thetaCuspBornWittenRadialNorm 0) / 6 := by
  simp only [thetaCuspBornWittenQuadraticSource,
    thetaCuspBornWittenRadialNorm_eq_rawMoment]

theorem normalizedPrimeArchMoment_one_eq_radialBornWittenNorm :
    normalizedPrimeArchMoment 1 =
      (thetaCuspBornWittenRadialNorm 1 /
          thetaCuspBornWittenRadialNorm 0) ^ 2 / 2 -
        (thetaCuspBornWittenRadialNorm 2 /
          thetaCuspBornWittenRadialNorm 0) / 6 := by
  rw [normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource,
    thetaCuspBornWittenQuadraticSource_eq_radialNorm]

/-- Every even central Xi jet is a signed sum of radial zero-mode squared norms. -/
theorem iteratedDeriv_XiC_zero_eq_tsum_radialBornWitten_norm (j : ℕ) :
    iteratedDeriv (2 * j) XiC 0 =
      (((-1 : ℝ) ^ j *
        ∑' n : ℕ, 2 * Real.pi *
          thetaCuspBornWittenRadialRawMoment 0 j n : ℝ) : ℂ) := by
  rw [iteratedDeriv_XiC_zero_eq_rawEvenMoment,
    thetaCuspRawEvenMoment_eq_tsum_radialBornWitten_norm]

theorem iteratedDeriv_XiC_zero_eq_radialBornWittenNorm (j : ℕ) :
    iteratedDeriv (2 * j) XiC 0 =
      (((-1 : ℝ) ^ j * thetaCuspBornWittenRadialNorm j : ℝ) : ℂ) := by
  rw [iteratedDeriv_XiC_zero_eq_tsum_radialBornWitten_norm,
    thetaCuspBornWittenRadialNorm]

/-- Direct radial-state interface to the two live first-atom hypotheses.  The upper ratio is the
ordinary degree-two moment ratio of the `k=1` Dirichlet state; the relaxed fourth-moment condition
is the corresponding `k=0` condition. -/
theorem forall_primeArchSourceTraceHankel_linear_nonneg_of_radialBornWittenAmplitude
    (hupper :
      14 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 1 1 1) ^ 2 ≤
        9 * thetaCuspBornWittenRadialRawMoment 0 1 1 *
          thetaCuspBornWittenRadialRawMoment 2 1 1)
    (hrelaxed :
      16 * ((3005 / 2997 : ℝ) *
          thetaCuspBornWittenRadialRawMoment 0 0 1) *
          ((3005 / 2997 : ℝ) *
            thetaCuspBornWittenRadialRawMoment 2 0 1) ≤
        45 * thetaCuspBornWittenRadialRawMoment 1 0 1 ^ 2) :
    ∀ a b : ℝ, 0 ≤ (primeArchSourceTraceHankel (C a + C b * X)).re := by
  apply forall_primeArchSourceTraceHankel_linear_nonneg_of_bornWittenAmplitude
  · rw [thetaCuspBornWittenRadialRawMoment_eq_shifted,
      thetaCuspBornWittenRadialRawMoment_eq_shifted,
      thetaCuspBornWittenRadialRawMoment_eq_shifted] at hupper
    norm_num only [Nat.reduceAdd, Nat.reduceMul, pow_zero, one_mul] at hupper
    exact hupper
  · rw [thetaCuspBornWittenRadialRawMoment_eq_shifted,
      thetaCuspBornWittenRadialRawMoment_eq_shifted,
      thetaCuspBornWittenRadialRawMoment_eq_shifted] at hrelaxed
    norm_num only [Nat.reduceAdd, Nat.reduceMul, pow_zero, one_mul] at hrelaxed
    exact hrelaxed

end

end RHTower
