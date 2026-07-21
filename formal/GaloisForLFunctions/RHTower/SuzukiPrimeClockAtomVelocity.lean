import GaloisForLFunctions.RHTower.SuzukiPrimeTangentTomography
import GaloisForLFunctions.RHTower.SuzukiHerglotzBoundaryStates

namespace GaloisForLFunctions.RHTower

open Complex Filter Finset Set Topology

noncomputable section

/-! ## Reflected prime-step geometry -/

/-- Closed-form source ratio of one reflected prime-step pair at a free clock pole. -/
def suzukiPrimeClockReflectedRatio
    (Q M C y : ℂ) : ℂ :=
  -C * (Q / M + M + y + Q * y⁻¹) / (Q + 1)

/-- Swapping the clock phase with its inverse removes the scalar `M` terms and leaves exactly the
odd phase multiplied by the free hyperbolic defect factor. -/
theorem suzukiPrimeClockReflectedRatio_sub
    {Q M C y : ℂ} (hQ : Q + 1 ≠ 0) (hy : y ≠ 0) :
    suzukiPrimeClockReflectedRatio Q M C y⁻¹ -
        suzukiPrimeClockReflectedRatio Q M C y =
      -C * ((Q - 1) / (Q + 1)) * (y - y⁻¹) := by
  simp only [suzukiPrimeClockReflectedRatio, inv_inv]
  field_simp [hQ, hy]
  ring

/-- The projective pole normalization cancels the same geometric factor exposed by reflection. -/
theorem suzukiPrimeClockGeometry_cancel
    {a κ C y : ℂ} (ha : a ≠ 0) (hκ : κ ≠ 0) :
    -(-C * κ * (y - y⁻¹)) / (2 * I * a * κ) =
      (C / a) * ((y - y⁻¹) / (2 * I)) := by
  field_simp [ha, hκ, Complex.I_ne_zero]

/-- **Prime-step to atom-velocity transference.**  The reflected source ratio and the free-clock
pole normalization contain the same geometric factor, so it cancels exactly. -/
theorem suzukiPrimeClockReflectedRatio_velocity
    {a Q M C y κ : ℂ} (ha : a ≠ 0) (hQ : Q + 1 ≠ 0) (hy : y ≠ 0)
    (hκ : κ ≠ 0) (hκeq : κ = (Q - 1) / (Q + 1)) :
    -(suzukiPrimeClockReflectedRatio Q M C y⁻¹ -
        suzukiPrimeClockReflectedRatio Q M C y) /
        (2 * I * a * κ) =
      (C / a) * ((y - y⁻¹) / (2 * I)) := by
  rw [suzukiPrimeClockReflectedRatio_sub hQ hy, ← hκeq]
  exact suzukiPrimeClockGeometry_cancel ha hκ

/-! ## Half-shifted finite phase packets -/

/-- A finite two-sided phase packet evaluated at the half-shifted clock index. -/
def suzukiFiniteHalfShiftSinePhaseCarrier {ι : Type*}
    (s : Finset ι) (c q r : ι → ℂ) (n : ℕ) : ℂ :=
  suzukiFinitePhaseCarrier s (fun j => c j * r j / (2 * I)) q n -
    suzukiFinitePhaseCarrier s (fun j => c j * (r j)⁻¹ / (2 * I))
      (fun j => (q j)⁻¹) n

theorem suzukiFiniteHalfShiftSinePhaseCarrier_eq_sum {ι : Type*}
    (s : Finset ι) (c q r : ι → ℂ) (n : ℕ) :
    suzukiFiniteHalfShiftSinePhaseCarrier s c q r n =
      ∑ j ∈ s, c j * (r j * q j ^ n - (r j)⁻¹ * (q j)⁻¹ ^ n) / (2 * I) := by
  simp only [suzukiFiniteHalfShiftSinePhaseCarrier, suzukiFinitePhaseCarrier]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  field_simp

/-- Demodulating a finite phase packet at an external unit phase gives zero when no packet phase
equals the target. -/
theorem tendsto_suzukiFinitePhaseCarrier_external_bohrCoefficient_zero
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {c q : ι → ℂ} {p : ℂ}
    (hpNorm : ‖p‖ = 1) (hqnorm : ∀ j ∈ s, ‖q j‖ = 1)
    (hsep : ∀ j ∈ s, q j ≠ p) :
    Tendsto
      (fun N => suzukiCesaroMean
        (fun n => suzukiFinitePhaseCarrier s c q n * p⁻¹ ^ n) N)
      atTop (𝓝 0) := by
  have hp0 : p ≠ 0 := norm_ne_zero_iff.mp (by rw [hpNorm]; norm_num)
  have hrewrite (N : ℕ) :
      suzukiCesaroMean
          (fun n => suzukiFinitePhaseCarrier s c q n * p⁻¹ ^ n) N =
        ∑ j ∈ s, c j * suzukiCesaroMean (fun n => (q j * p⁻¹) ^ n) N := by
    calc
      suzukiCesaroMean
          (fun n => suzukiFinitePhaseCarrier s c q n * p⁻¹ ^ n) N =
        suzukiCesaroMean
          (fun n => ∑ j ∈ s, c j * (q j * p⁻¹) ^ n) N := by
            apply congrArg (fun u : ℕ → ℂ => suzukiCesaroMean u N)
            funext n
            simp only [suzukiFinitePhaseCarrier, sum_mul]
            apply sum_congr rfl
            intro j hj
            rw [mul_assoc, ← mul_pow]
      _ = ∑ j ∈ s, suzukiCesaroMean
          (fun n => c j * (q j * p⁻¹) ^ n) N :=
        suzukiCesaroMean_sum s _ N
      _ = ∑ j ∈ s, c j * suzukiCesaroMean
          (fun n => (q j * p⁻¹) ^ n) N := by
        apply sum_congr rfl
        intro j hj
        exact suzukiCesaroMean_smul _ _ _
  have hterm (j : ι) (hj : j ∈ s) :
      Tendsto
        (fun N => c j * suzukiCesaroMean (fun n => (q j * p⁻¹) ^ n) N)
        atTop (𝓝 0) := by
    have hratioNorm : ‖q j * p⁻¹‖ = 1 := by
      rw [norm_mul, norm_inv, hqnorm j hj, hpNorm]
      norm_num
    have hratioNe : q j * p⁻¹ ≠ 1 := by
      intro h
      apply hsep j hj
      calc
        q j = (q j * p⁻¹) * p := by field_simp
        _ = p := by rw [h, one_mul]
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => c j) atTop (𝓝 (c j))).mul
        (tendsto_suzukiCesaroMean_geometric_zero hratioNorm hratioNe)
  have hsumlim := tendsto_finsetSum s (fun j hj => hterm j hj)
  rw [show (fun N => suzukiCesaroMean
      (fun n => suzukiFinitePhaseCarrier s c q n * p⁻¹ ^ n) N) =
      (fun N => ∑ j ∈ s, c j *
        suzukiCesaroMean (fun n => (q j * p⁻¹) ^ n) N) from funext hrewrite]
  simpa using hsumlim

/-- Bohr recovery for a finite half-shifted sine packet. -/
theorem tendsto_suzukiFiniteHalfShiftSinePhaseCarrier_bohrCoefficient
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {c q r : ι → ℂ} {m : ι}
    (hm : m ∈ s) (hqnorm : ∀ j ∈ s, ‖q j‖ = 1)
    (hsep : ∀ j ∈ s, j ≠ m → q j ≠ q m)
    (hminus : ∀ j ∈ s, (q j)⁻¹ ≠ q m) :
    Tendsto
      (fun N => suzukiCesaroMean
        (fun n => suzukiFiniteHalfShiftSinePhaseCarrier s c q r n *
          (q m)⁻¹ ^ n) N)
      atTop (𝓝 (c m * r m / (2 * I))) := by
  have hplus := tendsto_suzukiFinitePhaseCarrier_bohrCoefficient hm hqnorm hsep
      (c := fun j => c j * r j / (2 * I))
  have hminusZero := tendsto_suzukiFinitePhaseCarrier_external_bohrCoefficient_zero
      (show ‖q m‖ = 1 from hqnorm m hm)
      (fun j hj => by rw [norm_inv, hqnorm j hj]; norm_num)
      hminus
      (c := fun j => c j * (r j)⁻¹ / (2 * I))
  have hrewrite (N : ℕ) :
      suzukiCesaroMean
          (fun n => suzukiFiniteHalfShiftSinePhaseCarrier s c q r n *
            (q m)⁻¹ ^ n) N =
        suzukiCesaroMean
          (fun n => suzukiFinitePhaseCarrier s (fun j => c j * r j / (2 * I)) q n *
            (q m)⁻¹ ^ n) N -
        suzukiCesaroMean
          (fun n => suzukiFinitePhaseCarrier s (fun j => c j * (r j)⁻¹ / (2 * I))
            (fun j => (q j)⁻¹) n * (q m)⁻¹ ^ n) N := by
    simp only [suzukiFiniteHalfShiftSinePhaseCarrier, suzukiCesaroMean,
      sub_mul, sum_sub_distrib, mul_sub]
  rw [show (fun N => suzukiCesaroMean
      (fun n => suzukiFiniteHalfShiftSinePhaseCarrier s c q r n *
        (q m)⁻¹ ^ n) N) =
      (fun N => suzukiCesaroMean
          (fun n => suzukiFinitePhaseCarrier s (fun j => c j * r j / (2 * I)) q n *
            (q m)⁻¹ ^ n) N -
        suzukiCesaroMean
          (fun n => suzukiFinitePhaseCarrier s (fun j => c j * (r j)⁻¹ / (2 * I))
            (fun j => (q j)⁻¹) n * (q m)⁻¹ ^ n) N) from funext hrewrite]
  simpa only [sub_zero] using hplus.sub hminusZero

/-! ## Suzuki prime clock-atom velocity -/

/-- Half phase at the `m`th prime logarithm. -/
def suzukiPrimeClockHalfPhase (a : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (((Real.pi * Real.log m / (2 * a) : ℝ) : ℂ) * I)

theorem norm_suzukiPrimeClockHalfPhase (a : ℝ) (m : ℕ) :
    ‖suzukiPrimeClockHalfPhase a m‖ = 1 := by
  let r : ℝ := Real.pi * Real.log m / (2 * a)
  rw [suzukiPrimeClockHalfPhase, Complex.norm_exp]
  change Real.exp (((r : ℂ) * I).re) = 1
  rw [Complex.mul_re]
  simp only [ofReal_re, I_re, mul_zero, ofReal_im, I_im, zero_mul, sub_zero]
  exact Real.exp_zero

theorem suzukiPrimeClockHalfPhase_sq (a : ℝ) (m : ℕ) :
    suzukiPrimeClockHalfPhase a m ^ 2 = suzukiPrimeTangentPhase a m := by
  rw [suzukiPrimeClockHalfPhase, suzukiPrimeTangentPhase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Critical prime amplitude in the first Suzuki clock-atom velocity field. -/
def suzukiPrimeClockAtomAmplitude (a : ℝ) (m : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt m / (a * Real.sqrt m)

theorem suzukiPrimeClockAtomAmplitude_ne_zero_iff_primePow
    {a : ℝ} {m : ℕ} (ha : a ≠ 0) (hm : 2 ≤ m) :
    suzukiPrimeClockAtomAmplitude a m ≠ 0 ↔ IsPrimePow m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hsqrt : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.2 hmpos).ne'
  have hden : a * Real.sqrt (m : ℝ) ≠ 0 := mul_ne_zero ha hsqrt
  have hLambda : ArithmeticFunction.vonMangoldt m ≠ 0 ↔ IsPrimePow m :=
    (suzukiPrimeTangentWeight_ne_zero_iff hm).symm.trans
      (suzukiPrimeTangentWeight_ne_zero_iff_primePow hm)
  constructor
  · intro hamp
    apply hLambda.mp
    intro hzero
    apply hamp
    simp [suzukiPrimeClockAtomAmplitude, hzero]
  · intro hp
    exact div_ne_zero (hLambda.mpr hp) hden

/-- Arithmetic part of Suzuki's first free-clock pole velocity. -/
def suzukiPrimeClockAtomVelocity (a : ℝ) (s : Finset ℕ) (k : ℕ) : ℂ :=
  suzukiFiniteHalfShiftSinePhaseCarrier s
    (fun m => (suzukiPrimeClockAtomAmplitude a m : ℂ))
    (suzukiPrimeTangentPhase a)
    (suzukiPrimeClockHalfPhase a) k

/-- Nonresonant Bohr demodulation recovers the half-phase-weighted critical prime amplitude. -/
theorem tendsto_suzukiPrimeClockAtomVelocity_bohrCoefficient
    {a : ℝ} {s : Finset ℕ} {m : ℕ} (hm : m ∈ s)
    (hsep : ∀ j ∈ s, j ≠ m →
      suzukiPrimeTangentPhase a j ≠ suzukiPrimeTangentPhase a m)
    (hminus : ∀ j ∈ s,
      (suzukiPrimeTangentPhase a j)⁻¹ ≠ suzukiPrimeTangentPhase a m) :
    Tendsto
      (fun N => suzukiCesaroMean
        (fun k => suzukiPrimeClockAtomVelocity a s k *
          (suzukiPrimeTangentPhase a m)⁻¹ ^ k) N)
      atTop (𝓝 ((suzukiPrimeClockAtomAmplitude a m : ℂ) *
        suzukiPrimeClockHalfPhase a m / (2 * I))) := by
  exact tendsto_suzukiFiniteHalfShiftSinePhaseCarrier_bohrCoefficient hm
    (fun j hj => norm_suzukiPrimeTangentPhase a j) hsep hminus

/-- Normalize a prime clock-velocity Bohr coefficient back to `Λ(m)`. -/
def suzukiPrimeClockAtomNormalize (a : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  2 * I * ((a * Real.sqrt m : ℝ) : ℂ) *
    (suzukiPrimeClockHalfPhase a m)⁻¹ * z

/-- **Exact prime recovery from Suzuki divisor velocities.** -/
theorem tendsto_suzukiPrimeClockAtomVelocity_normalized_bohrCoefficient
    {a : ℝ} {s : Finset ℕ} {m : ℕ} (ha : a ≠ 0) (hm : m ∈ s) (hm2 : 2 ≤ m)
    (hsep : ∀ j ∈ s, j ≠ m →
      suzukiPrimeTangentPhase a j ≠ suzukiPrimeTangentPhase a m)
    (hminus : ∀ j ∈ s,
      (suzukiPrimeTangentPhase a j)⁻¹ ≠ suzukiPrimeTangentPhase a m) :
    Tendsto
      (fun N => suzukiPrimeClockAtomNormalize a m
        (suzukiCesaroMean
          (fun k => suzukiPrimeClockAtomVelocity a s k *
            (suzukiPrimeTangentPhase a m)⁻¹ ^ k) N))
      atTop (𝓝 (ArithmeticFunction.vonMangoldt m : ℂ)) := by
  have hbohr := tendsto_suzukiPrimeClockAtomVelocity_bohrCoefficient hm hsep hminus
  have hhalf : suzukiPrimeClockHalfPhase a m ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [norm_suzukiPrimeClockHalfPhase]; norm_num)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm2)
  have hsqrt : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.2 hmpos).ne'
  have hconst : Tendsto
      (fun _ : ℕ => (2 * I * ((a * Real.sqrt m : ℝ) : ℂ) *
        (suzukiPrimeClockHalfPhase a m)⁻¹)) atTop
      (𝓝 (2 * I * ((a * Real.sqrt m : ℝ) : ℂ) *
        (suzukiPrimeClockHalfPhase a m)⁻¹)) := tendsto_const_nhds
  have hmap := hconst.mul hbohr
  have hlimit :
      (2 * I * ((a * Real.sqrt m : ℝ) : ℂ) *
          (suzukiPrimeClockHalfPhase a m)⁻¹) *
        ((suzukiPrimeClockAtomAmplitude a m : ℂ) *
          suzukiPrimeClockHalfPhase a m / (2 * I)) =
        (ArithmeticFunction.vonMangoldt m : ℂ) := by
    simp only [suzukiPrimeClockAtomAmplitude]
    push_cast
    field_simp [ha, hsqrt, hhalf, Complex.I_ne_zero]
  rw [hlimit] at hmap
  simpa only [suzukiPrimeClockAtomNormalize, mul_assoc] using hmap

/-- One finite-aperture nonresonance certificate recovers every prime amplitude in the clock-atom
velocity packet. -/
theorem tendsto_suzukiPrimeClockAtomVelocity_normalized_bohrCoefficient_of_nonresonant
    {a : ℝ} {s : Finset ℕ} (ha : a ≠ 0)
    (hres : SuzukiPrimeTangentNonresonant a s)
    {m : ℕ} (hm : m ∈ s) (hm2 : 2 ≤ m) :
    Tendsto
      (fun N => suzukiPrimeClockAtomNormalize a m
        (suzukiCesaroMean
          (fun k => suzukiPrimeClockAtomVelocity a s k *
            (suzukiPrimeTangentPhase a m)⁻¹ ^ k) N))
      atTop (𝓝 (ArithmeticFunction.vonMangoldt m : ℂ)) := by
  exact tendsto_suzukiPrimeClockAtomVelocity_normalized_bohrCoefficient
    ha hm hm2 (hres m hm).1 (hres m hm).2

end

end GaloisForLFunctions.RHTower
