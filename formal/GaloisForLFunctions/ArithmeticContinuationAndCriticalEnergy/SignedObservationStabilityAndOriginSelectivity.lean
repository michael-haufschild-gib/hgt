import GaloisForLFunctions.ArithmeticCompensationTheory.AChangeOfOriginCostsAQuadraticConstant
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SingleDampingSublinearPairingAndBlockEnergy

/-!
# A Stability Theorem for a Signed Observation: Dilation-Step Recovery, Origin Sensitivity, and Selectivity

This module resolves Open Problem 9 of the `ArithmeticContinuationAndCriticalEnergy` programme:

> Find an observation map that is both origin-sensitive and sign-reading, and prove a quantitative
> stability estimate for it in the receiver's norm — the missing half of the recovery theorems.

## Mathematical resolution

1. **The dilation-step signed observation and exact recovery (`dilationStepObservation`,
   `dilationStepObservation_injective_of_eq_zero`).**
   For an integer dilation scale `q ≥ 2`, the **dilation-step observation**
   `dilationStepObservation q v n = v n − v ⌊n/q⌋` reads each cell against its parent on the
   integer dilation tree rooted at `n = 0`. Since `⌊n/q⌋ < n` for every `n ≥ 1` and `q ≥ 2`, any
   root-anchored row (`v 0 = 0`) is uniquely reconstructed from `dilationStepObservation q v` by
   strong induction along the dilation tree (`dilationStepObservation_eq_zero_iff`,
   `dilationStepObservation_injective_of_eq_zero`), and the root-augmented pair
   `(v 0, dilationStepObservation q v)` is injective on all sequences `ℕ → ℝ`
   (`anchoredDilationStepObservation_injective`).

2. **Horizon-uniform two-sided quantitative stability in the receiver's pronic norm
   (`dilationStepObservation_two_sided_stability`).**
   For every `q ≥ 2`, every horizon `T : ℕ`, and every pair of rows `u, v : ℕ → ℝ` with `u 0 = v 0`,
   the dilation Hardy inequality and pronic self-similarity yield the horizon-free two-sided
   Lipschitz stability estimate:
   `(2(1 + 1/q))⁻¹ ‖O_q u − O_q v‖_T² ≤ ‖u − v‖_T² ≤ (q / (√q − 1)²) ‖O_q u − O_q v‖_T²`.
   This supplies the quantitative stability half missing from the logarithmic moment recovery
   theorems, with explicit constants depending only on `q` and completely independent of the
   horizon `T` and the damping `ε`.

3. **Quantitative origin-sensitivity and stability under origin shifts
   (`originShiftObservation_two_sided_stability`, `originShiftObservation_sharp_constant`).**
   For the origin-shift observation `originShiftObservation k v n = v (n + k)`, the pronic norm
   satisfies the two-sided stability bounds
   `‖u − v‖_{T+k}² ≤ ‖u − v‖_k² + ‖S_k u − S_k v‖_T²` and
   `‖S_k u − S_k v‖_T² ≤ ((k+1)(k+2)/2) ‖u − v‖_{T+k}²`,
   with the quadratic origin-sensitivity factor `(k+1)(k+2)/2` attained on the cell indicator
   `δ_{k+1}`.

4. **Sign-reading selectivity against both the size-blind majorant and the Ramanujan-isometric
   parity twin (`not_bddAbove_dilationStepObservation_majorant`,
   `dilationStepObservation_parityTwin_ge`,
   `exists_dilationStepObservation_vk_band_and_parityTwin_separation`).**
   On the actual damped Möbius source `A_ε = pmPowerDampedCenteredDivisorPrefix ε`,
   `dilationStepObservation q A_ε n` is the signed centred divisor block sum
   `∑_{n/q < j ≤ n} pmPowerDampedCenteredDivisorCoeff ε j`, whose pronic norm squared equals
   `dampedBlockEnergy q ε T`. Consequently:
   - a horizon-uniform bound on `‖O_q A_ε‖_T²` is equivalent to `Admits dampedMobiusEnergy ε`
     (`admits_iff_bounded_dilationStepObservation`), and holds unconditionally on `(Θ − ½, ∞)` and
     on the Vinogradov–Korobov band;
   - on the size-blind majorant `A_ε^{maj}` (`0 < ε ≤ ½`), `‖O_q A_ε^{maj}‖_T²` is unbounded in `T`
     (`not_bddAbove_dilationStepObservation_majorant`);
   - on the Ramanujan-isometric parity twin `parityTwinWeight ε` (`ε₀ ≤ ε ≤ ½`), which shares all
     diagonal Ramanujan amplitudes `w(e)²` with the Möbius weight, `‖O_q A_{c'_ε}‖_T²` grows at
     least logarithmically (`≥ ((√q − 1)² / q) · c_twin · (log(T+1) − log 100)`) while `‖O_q A_ε‖_T²`
     is uniformly bounded across the Vinogradov–Korobov band
     (`exists_dilationStepObservation_vk_band_and_parityTwin_separation`).
-/

open Finset Filter Topology RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section

/-! ## 1. The dilation-step signed observation and exact recovery -/

/-- The **dilation-step signed observation** at integer scale `q`:
`O_q(v)(n) = v(n) − v(⌊n/q⌋)`. -/
def dilationStepObservation (q : ℕ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  v n - v (n / q)

/-- The **origin-shifted observation** by `k` cells: `S_k(v)(n) = v(n + k)`. -/
def originShiftObservation (k : ℕ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  v (n + k)

@[simp]
theorem dilationStepObservation_zero (q : ℕ) (v : ℕ → ℝ) :
    dilationStepObservation q v 0 = 0 := by
  simp [dilationStepObservation]

theorem dilationStepObservation_add (q : ℕ) (u v : ℕ → ℝ) (n : ℕ) :
    dilationStepObservation q (u + v) n =
      dilationStepObservation q u n + dilationStepObservation q v n := by
  simp only [dilationStepObservation, Pi.add_apply]
  ring

theorem dilationStepObservation_sub (q : ℕ) (u v : ℕ → ℝ) (n : ℕ) :
    dilationStepObservation q (u - v) n =
      dilationStepObservation q u n - dilationStepObservation q v n := by
  simp only [dilationStepObservation, Pi.sub_apply]
  ring

theorem dilationStepObservation_sub_fun (q : ℕ) (u v : ℕ → ℝ) :
    dilationStepObservation q (u - v) =
      dilationStepObservation q u - dilationStepObservation q v := by
  ext n
  exact dilationStepObservation_sub q u v n

theorem originShiftObservation_sub_fun (k : ℕ) (u v : ℕ → ℝ) :
    originShiftObservation k (u - v) =
      originShiftObservation k u - originShiftObservation k v := by
  ext n
  simp [originShiftObservation]

/-- **Exact kernel triviality on root-anchored rows.** For `q ≥ 2` and `v 0 = 0`,
`dilationStepObservation q v = 0` if and only if `v = 0`. -/
theorem dilationStepObservation_eq_zero_iff {q : ℕ} (hq : 2 ≤ q) {v : ℕ → ℝ}
    (hv0 : v 0 = 0) :
    dilationStepObservation q v = 0 ↔ v = 0 := by
  constructor
  · intro h
    ext n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases eq_or_ne n 0 with rfl | hn
      · exact hv0
      · have hdiv : n / q < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hq
        have hprev : v (n / q) = 0 := ih (n / q) hdiv
        have hn_obs : dilationStepObservation q v n = 0 := congr_fun h n
        unfold dilationStepObservation at hn_obs
        change v n = 0
        linarith
  · rintro rfl
    ext n
    simp [dilationStepObservation]

/-- **Exact recovery / injectivity on rows with the same root value.** For `q ≥ 2`, if
`u 0 = v 0` and `dilationStepObservation q u = dilationStepObservation q v`, then `u = v`. -/
theorem dilationStepObservation_injective_of_eq_zero {q : ℕ} (hq : 2 ≤ q)
    {u v : ℕ → ℝ} (h0 : u 0 = v 0)
    (hobs : dilationStepObservation q u = dilationStepObservation q v) :
    u = v := by
  have hsub0 : (u - v) 0 = 0 := by simp [h0]
  have hsub_obs : dilationStepObservation q (u - v) = 0 := by
    rw [dilationStepObservation_sub_fun, hobs, sub_self]
  have hzero := (dilationStepObservation_eq_zero_iff hq hsub0).mp hsub_obs
  ext n
  have hn : (u - v) n = 0 := congr_fun hzero n
  simp only [Pi.sub_apply] at hn
  linarith

/-- **Full injectivity of the root-anchored dilation-step observation `(v 0, O_q v)`.** -/
theorem anchoredDilationStepObservation_injective {q : ℕ} (hq : 2 ≤ q) :
    Function.Injective (fun v : ℕ → ℝ => (v 0, dilationStepObservation q v)) := by
  intro u v h
  rw [Prod.mk.injEq] at h
  exact dilationStepObservation_injective_of_eq_zero hq h.1 h.2

/-! ## 2. Quantitative two-sided stability in the receiver's pronic norm -/

/-- The squared pronic norm of `dilationStepObservation q v` is `dilationStepEnergy q T v`. -/
theorem pronicNorm_dilationStepObservation_sq_eq (q T : ℕ) (v : ℕ → ℝ) :
    pronicNorm T (dilationStepObservation q v) ^ 2 = dilationStepEnergy q T v := by
  rw [pronicNorm_sq, dilationStepEnergy]
  rfl

/-- **Two-sided quantitative stability of `dilationStepObservation` in the pronic norm.**
For every integer scale `q ≥ 2`, every horizon `T : ℕ`, and every pair of rows `u, v : ℕ → ℝ`
with `u 0 = v 0`, the pronic distance `‖u − v‖_T²` and the observation distance
`‖O_q u − O_q v‖_T²` satisfy the horizon-uniform two-sided inequality:
`(2(1 + 1/q))⁻¹ ‖O_q u − O_q v‖_T² ≤ ‖u − v‖_T² ≤ (q / (√q − 1)²) ‖O_q u − O_q v‖_T²`. -/
theorem dilationStepObservation_two_sided_stability {q : ℕ} (hq : 2 ≤ q) (T : ℕ)
    {u v : ℕ → ℝ} (h0 : u 0 = v 0) :
    (1 / (2 * (1 + 1 / (q : ℝ)))) *
        pronicNorm T (dilationStepObservation q u - dilationStepObservation q v) ^ 2 ≤
      pronicNorm T (u - v) ^ 2 ∧
    pronicNorm T (u - v) ^ 2 ≤
      ((q : ℝ) / (Real.sqrt (q : ℝ) - 1) ^ 2) *
        pronicNorm T (dilationStepObservation q u - dilationStepObservation q v) ^ 2 := by
  have hsub0 : (u - v) 0 = 0 := by simp [h0]
  rw [← dilationStepObservation_sub_fun, pronicNorm_dilationStepObservation_sq_eq]
  have hupper := pronicNorm_sq_le_dilationStepEnergy hq T (u - v) hsub0
  have hlower := dilationStepEnergy_le (by omega : 1 ≤ q) T (u - v) hsub0
  have hq0 : (0 : ℝ) < q := by positivity
  have hcpos : (0 : ℝ) < 2 * (1 + 1 / (q : ℝ)) := by positivity
  refine ⟨?_, hupper⟩
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hcpos]
  linarith

/-! ## 3. Quantitative origin-sensitivity and stability under origin shifts -/

theorem pronicNorm_sq_eq_pronicEnergy (T : ℕ) (v : ℕ → ℝ) :
    pronicNorm T v ^ 2 = pronicEnergy v T := by
  rw [pronicNorm_sq, pronicEnergy]

/-- **Two-sided quantitative stability under an origin shift by `k` cells.**
For any `u, v : ℕ → ℝ`, shift `k : ℕ`, and horizon `T : ℕ`:
1. `‖S_k u − S_k v‖_T² ≤ ((k + 1)(k + 2) / 2) ‖u − v‖_{T+k}²`;
2. `‖u − v‖_{T+k}² ≤ ‖u − v‖_k² + ‖S_k u − S_k v‖_T²`. -/
theorem originShiftObservation_two_sided_stability (k T : ℕ) (u v : ℕ → ℝ) :
    pronicNorm T (originShiftObservation k u - originShiftObservation k v) ^ 2 ≤
      ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 * pronicNorm (T + k) (u - v) ^ 2 ∧
    pronicNorm (T + k) (u - v) ^ 2 ≤
      pronicNorm k (u - v) ^ 2 +
        pronicNorm T (originShiftObservation k u - originShiftObservation k v) ^ 2 := by
  rw [← originShiftObservation_sub_fun, pronicNorm_sq_eq_pronicEnergy,
    pronicNorm_sq_eq_pronicEnergy, pronicNorm_sq_eq_pronicEnergy]
  exact ⟨pronicEnergy_shift_le (u - v) k T, pronicEnergy_le_head_add_shift (u - v) k T⟩

/-- **Sharpness of the quadratic origin-sensitivity constant `(k+1)(k+2)/2`.** On the indicator
row of cell `k + 1`, shifting the origin by `k` cells multiplies the pronic energy by the exact
factor `(k+1)(k+2)/2`. -/
theorem originShiftObservation_sharp_constant (k T : ℕ) (hT : 1 ≤ T) :
    pronicNorm T (originShiftObservation k (fun n => if n = k + 1 then (1 : ℝ) else 0)) ^ 2 =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 *
        pronicNorm (T + k) (fun n => if n = k + 1 then (1 : ℝ) else 0) ^ 2 := by
  rw [pronicNorm_sq_eq_pronicEnergy, pronicNorm_sq_eq_pronicEnergy]
  exact pronicEnergy_shift_indicator k T hT

/-! ## 4. Sign-reading selectivity on the actual source vs. the majorant and parity-twin adversaries -/

/-- On the actual centred source `A_ε = pmPowerDampedCenteredDivisorPrefix ε`, the dilation-step
observation at cell `n` is the localized block sum over `(⌊n/q⌋, n]`. -/
theorem dilationStepObservation_centeredPrefix_eq_blockSum (q : ℕ) (ε : ℝ) (n : ℕ) :
    dilationStepObservation q (pmPowerDampedCenteredDivisorPrefix ε) n =
      ∑ j ∈ Ioc (n / q) n, pmPowerDampedCenteredDivisorCoeff ε j :=
  pmPowerDampedCenteredDivisorPrefix_sub_eq_blockSum ε (Nat.div_le_self n q)

/-- The squared pronic norm of `dilationStepObservation q A_ε` is `dampedBlockEnergy q ε T`. -/
theorem pronicNorm_dilationStepObservation_centeredPrefix_sq_eq (q : ℕ) (ε : ℝ) (T : ℕ) :
    pronicNorm T (dilationStepObservation q (pmPowerDampedCenteredDivisorPrefix ε)) ^ 2 =
      dampedBlockEnergy q ε T := by
  rw [pronicNorm_dilationStepObservation_sq_eq, dampedBlockEnergy_eq_dilationStepEnergy]

/-- **Equivalence with critical admission.** For every integer scale `q ≥ 2` and damping `ε : ℝ`,
the damped Möbius source is admitted at `ε` if and only if its dilation-step observation has
horizon-uniformly bounded pronic norm. -/
theorem admits_iff_bounded_dilationStepObservation {q : ℕ} (hq : 2 ≤ q) (ε : ℝ) :
    Admits dampedMobiusEnergy ε ↔
      ∃ B : ℝ, ∀ T : ℕ,
        pronicNorm T (dilationStepObservation q (pmPowerDampedCenteredDivisorPrefix ε)) ^ 2 ≤ B := by
  simp_rw [pronicNorm_dilationStepObservation_centeredPrefix_sq_eq]
  exact admits_dampedMobiusEnergy_iff_admits_blockEnergy hq ε

/-- **Selectivity against the size-blind majorant adversary.** For every `q ≥ 2` and
`0 < ε ≤ 1/2`, the dilation-step observation of `majorantCenteredPrefix ε` has unbounded pronic
norm across horizons. -/
theorem not_bddAbove_dilationStepObservation_majorant {q : ℕ} (hq : 2 ≤ q)
    {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    ¬ ∃ B : ℝ, ∀ T : ℕ,
      pronicNorm T (dilationStepObservation q (majorantCenteredPrefix ε)) ^ 2 ≤ B := by
  rintro ⟨B, hB⟩
  have hmaj : Admits majorantEnergy ε := by
    refine ⟨((q : ℝ) / (Real.sqrt (q : ℝ) - 1) ^ 2) * B, fun T => ?_⟩
    have h0 : majorantCenteredPrefix ε 0 = 0 := by simp [majorantCenteredPrefix]
    have hhardy := pronicNorm_sq_le_dilationStepEnergy hq T (majorantCenteredPrefix ε) h0
    rw [← pronicNorm_dilationStepObservation_sq_eq] at hhardy
    have hq0 : (0 : ℝ) < q := by positivity
    have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    have hs1 : 1 < Real.sqrt (q : ℝ) := by
      have : Real.sqrt 1 < Real.sqrt (q : ℝ) := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
      simpa using this
    have hcpos : (0 : ℝ) ≤ (q : ℝ) / (Real.sqrt (q : ℝ) - 1) ^ 2 := by
      have : (0 : ℝ) < Real.sqrt (q : ℝ) - 1 := by linarith
      positivity
    have hE : majorantEnergy ε T = pronicNorm T (majorantCenteredPrefix ε) ^ 2 := by
      rw [pronicNorm_sq]; rfl
    rw [hE]
    exact hhardy.trans (mul_le_mul_of_nonneg_left (hB T) hcpos)
  exact not_admits_majorantEnergy hε0 hε hmaj

/-- **Selectivity against the Ramanujan-isometric parity-twin adversary.** For every `q ≥ 2`,
`ε₀ > 0`, and `ε ∈ [ε₀, 1/2]`, the dilation-step observation of the parity-twin prefix
`weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε)` grows at least like
`((√q − 1)² / q) · ((K⋆(ε₀)/16)² / 4) · (log(T+1) − log 100)`. -/
theorem dilationStepObservation_parityTwin_ge {q : ℕ} (hq : 2 ≤ q)
    {ε₀ ε : ℝ} (hε₀ : 0 < ε₀) (hε_ge : ε₀ ≤ ε) (hε2 : ε ≤ 1 / 2) (T : ℕ) :
    ((Real.sqrt (q : ℝ) - 1) ^ 2 / (q : ℝ)) *
        ((twinDriftConstantAt ε₀ / 16) ^ 2 / 4) *
          (Real.log ((T : ℝ) + 1) - Real.log 100) ≤
      pronicNorm T
        (dilationStepObservation q
          (weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε))) ^ 2 := by
  set v := weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε)
  have hv0 : v 0 = 0 := by simp [v, weightCenteredPrefix]
  have hhardy := pronicNorm_sq_le_dilationStepEnergy hq T v hv0
  rw [← pronicNorm_dilationStepObservation_sq_eq] at hhardy
  have hE : weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T =
      pronicNorm T v ^ 2 := by
    rw [pronicNorm_sq, weightPronicEnergy]
  have htwin := parityTwin_receiver_ge_of_pos hε₀ hε_ge hε2 T
  rw [hE] at htwin
  have hq0 : (0 : ℝ) < q := by positivity
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hs1 : 1 < Real.sqrt (q : ℝ) := by
    have : Real.sqrt 1 < Real.sqrt (q : ℝ) := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    simpa using this
  have hs1' : Real.sqrt (q : ℝ) - 1 ≠ 0 := by linarith
  have hs_pos : (0 : ℝ) < (Real.sqrt (q : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hfac_pos : (0 : ℝ) < (Real.sqrt (q : ℝ) - 1) ^ 2 / (q : ℝ) := div_pos hs_pos hq0
  have hcomb := htwin.trans hhardy
  have hmul := mul_le_mul_of_nonneg_left hcomb hfac_pos.le
  have hcancel : ((Real.sqrt (q : ℝ) - 1) ^ 2 / (q : ℝ)) *
      (((q : ℝ) / (Real.sqrt (q : ℝ) - 1) ^ 2) *
        pronicNorm T (dilationStepObservation q v) ^ 2) =
      pronicNorm T (dilationStepObservation q v) ^ 2 := by
    field_simp [hq0.ne', hs1']
  linarith

/-- **Simultaneous Vinogradov–Korobov stability on the actual source and logarithmic divergence on
the parity twin.** For every integer scale `q ≥ 2` and damping floor `ε₀ > 0`, there exist
`B ≥ 0` and `c_obs > 0` such that for every horizon `T : ℕ` and every `ε ∈ [ε₀, 1/2]` in the
Vinogradov–Korobov band `1/2 − κ σ(T)/(480 log T) ≤ ε`:
1. `‖O_q A_ε‖_T² ≤ B` on the actual Möbius source;
2. `c_obs * (log(T+1) − log 100) ≤ ‖O_q A_{c'_ε}‖_T²` on the Ramanujan-isometric parity twin. -/
theorem exists_dilationStepObservation_vk_band_and_parityTwin_separation
    {q : ℕ} (hq : 2 ≤ q) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ B c_obs : ℝ, 0 ≤ B ∧ 0 < c_obs ∧
      ∀ (T : ℕ) (ε : ℝ), ε₀ ≤ ε → ε ≤ 1 / 2 →
        1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
          pronicNorm T (dilationStepObservation q (pmPowerDampedCenteredDivisorPrefix ε)) ^ 2 ≤ B ∧
          c_obs * (Real.log ((T : ℝ) + 1) - Real.log 100) ≤
            pronicNorm T
              (dilationStepObservation q
                (weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε))) ^ 2 := by
  obtain ⟨B, hB0, hB⟩ := exists_dampedBlockEnergy_le_on_vinogradovKorobovBand (q := q) (by omega) hε₀
  have hq0 : (0 : ℝ) < q := by positivity
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hs1 : 1 < Real.sqrt (q : ℝ) := by
    have : Real.sqrt 1 < Real.sqrt (q : ℝ) := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    simpa using this
  have hs_pos : (0 : ℝ) < (Real.sqrt (q : ℝ) - 1) ^ 2 := sq_pos_of_pos (by linarith)
  have hK0 : 0 < twinDriftConstantAt ε₀ := twinDriftConstantAt_pos hε₀
  set c_obs := ((Real.sqrt (q : ℝ) - 1) ^ 2 / (q : ℝ)) * ((twinDriftConstantAt ε₀ / 16) ^ 2 / 4)
  refine ⟨2 * (1 + 1 / (q : ℝ)) * B, c_obs, by positivity, by positivity,
    fun T ε hε_ge hε2 hband => ?_⟩
  rw [pronicNorm_dilationStepObservation_centeredPrefix_sq_eq]
  exact ⟨hB T ε hε_ge hε2 hband, dilationStepObservation_parityTwin_ge hq hε₀ hε_ge hε2 T⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
