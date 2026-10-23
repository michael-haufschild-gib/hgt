import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheProbeReceiverEnergyMeasuresTheModulusOfZeta
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerShiftsItsPoleOffTheRealAbscissa

/-!
# Oscillating Probe Source Estimates, the Sub-Half Energy Gap, and Collar / Finiteness Limitations

This module establishes three unconditional results for sub-half oscillating probes
`c_{ε,t}(d) = d^{-ε} cos(t log d)` (`0 < ε < 1/2`, `t ∈ ℝ`, `ρ = 1 − ε + it`):

1. **Source-estimate characterizations, the polynomial energy gap, and absence of a remaining
   source sign (`§1`).**
   - A uniform source prefix bound `|A_{ε,t}(n)| ≤ K (√n)^{1−ε}` (`n ≥ 1`) is **equivalent** to
     receiver boundedness (`not_receiverBounded_oscillatingSmoothPower_iff_forall_exists_prefix_gt`):
     any proof that `c_{ε,t}` is unpaid must show that `|A_{ε,t}(n)| / (√n)^{1−ε}` is unbounded.
   - For `0 < ε < 1/2` and `t ≠ 0`, there is a **strict polynomial energy gap of order `T^{1−2ε}`**
     between paid and unpaid probes (`probeEnergy_dichotomy_sub_half`):
     either `ζ(ρ) = 0` and `E_{ε,t}(T) ≤ K_ρ² (1 + 1/ε) = O(1)` for all `T`, or `ζ(ρ) ≠ 0` and
     `λ_{ε,t} T^{1−2ε} ≤ E_{ε,t}(T) ≤ Λ_{ε,t} T^{1−2ε}` eventually with
     `λ_{ε,t} = probeEnergyLowerRate ε t > 0`.
   - Consequently, `ReceiverBounded (oscillatingSmoothPower ε t)` holds if and only if
     `E_{ε,t}(T) / T^{1−2ε} → 0` (`receiverBounded_oscillatingSmoothPower_iff_tendsto_energy_div_rpow_zero`):
     no intermediate growth rate between `O(1)` and `Θ(T^{1−2ε})` exists. Because the leading
     energy rate `probeEnergyLowerRate ε t` is a positive multiple of the norm-square
     `‖ζ(ρ)/ρ‖² ≥ 0`, the `ζ`-zero equivalence reduces admission to the vanishing of a
     nonnegative modulus square and supplies no further sign to rule out `ζ(ρ) = 0`.

2. **Quantitative power-growth source lower bounds on zero-free boxes and the Vinogradov–Korobov
   collar (`§2`).**
   Throughout every bounded-height zero-free collar (`exists_eventually_probeEnergy_ge_box`),
   the high-ordinate Vinogradov–Korobov strip (`exists_eventually_probeEnergy_ge_vk`), and the
   all-frequency uniform Vinogradov–Korobov collar (`exists_eventually_probeEnergy_ge_vk_uniform`),
   the receiver energy satisfies the explicit power lower bound
   `E_{ε,t}(T) ≥ probeEnergyLowerRate ε t · T^{1−2ε}` with `probeEnergyLowerRate ε t > 0`
   and `E_{ε,t}(T) → +∞`.

3. **Why finite admitted-parameter sets and near-`ε = 0` collars do not exclude all
   `0 < ε < 1/2` (`§3`).**
   For every target parameter `(ε₁, t₁)` with `0 < ε₁ < 1/2`, the 3-term Euler-factor kernel
   `plantedEulerKernel ε₁ t₁` supported on `{1, 2, 4}` with leading coefficient `k(1) = 1`
   has complex pole value
   `K(ρ) = (1 − 2^{ρ₁ − ρ})(1 − 2^{\overline{ρ₁} − ρ})` (`complexPoleValue_plantedEulerKernel_eq_mul`).
   On the family `w_{ε,t} = plantedEulerKernel ε₁ t₁ ⋆ oscillatingSmoothPower ε t`:
   - `K(1 − ε + it) ≠ 0` for every `ε ≠ ε₁` and every `t ∈ ℝ`
     (`complexPoleValue_plantedEulerKernel_ne_zero_of_ne`), so on `(0, 1/2) \ {ε₁}` the probe
     `w_{ε,t}` has the exact same admission locus as `c_{ε,t}`: it is unconditionally unpaid on
     every near-`ε = 0` sub-collar `0 < ε < ε₁` inside the Vinogradov–Korobov / compact-box region,
     has only finitely many admitted dampings `ε ∈ (0, 1/2)` at each frequency `t`, and has only
     finitely many admitted frequencies `t ∈ [−T, T]` at each damping `ε ≠ ε₁`;
   - yet at `(ε₁, t₁)` itself, `K(1 − ε₁ + it₁) = 0`, so `w_{ε₁,t₁}` is **unconditionally paid**
     (`receiverBounded_plantedEulerKernel_at_target` and
     `plantedEulerKernel_collar_and_finiteness_obstruction`).
-/

open Complex Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### §1. Source-estimate characterizations and the sub-half polynomial energy gap -/

/-- The asymptotic lower energy rate constant of `oscillatingSmoothPower ε t` below half damping:
`λ_{ε,t} = (‖ζ(ρ)/ρ‖² / 4) (1/(1 − 2ε) − 1/‖1 − 2ε + 2it‖)`. -/
def probeEnergyLowerRate (ε t : ℝ) : ℝ :=
  ‖probeAmp ε t‖ ^ 2 / 4 * (1 / (1 - 2 * ε) - 1 / ‖probeCrossExponent ε t‖)

/-- The asymptotic upper energy rate constant of `oscillatingSmoothPower ε t` below half damping:
`Λ_{ε,t} = 2 ‖ζ(ρ)/ρ‖² / (1 − 2ε)`. -/
def probeEnergyUpperRate (ε t : ℝ) : ℝ :=
  2 * ‖probeAmp ε t‖ ^ 2 / (1 - 2 * ε)

/-- At a zero of `ζ(1 − ε + it)`, both asymptotic energy rate constants vanish. -/
theorem probeEnergyLowerRate_eq_zero_of_zeta_eq_zero {ε t : ℝ}
    (hz : riemannZeta (oscillationExponent ε t) = 0) :
    probeEnergyLowerRate ε t = 0 := by
  unfold probeEnergyLowerRate probeAmp
  simp [hz]

/-- Below half damping and off the real axis (`t ≠ 0`), `probeEnergyLowerRate ε t > 0` whenever
`ζ(1 − ε + it) ≠ 0`. -/
theorem probeEnergyLowerRate_pos {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ} (ht : t ≠ 0)
    (hz : riemannZeta (oscillationExponent ε t) ≠ 0) :
    0 < probeEnergyLowerRate ε t := by
  have hγ0 : 0 < 1 - 2 * ε := by linarith
  have hρ0 : oscillationExponent ε t ≠ 0 := oscillationExponent_ne_zero (by linarith) t
  have ha0 : 0 < ‖probeAmp ε t‖ := norm_pos_iff.mpr (div_ne_zero hz hρ0)
  have hnβ : 1 - 2 * ε < ‖probeCrossExponent ε t‖ := by
    have hsq : ‖probeCrossExponent ε t‖ ^ 2 = (1 - 2 * ε) ^ 2 + (2 * t) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [probeCrossExponent]
      ring
    have h4 : 0 < (2 * t) ^ 2 := by positivity
    nlinarith [norm_nonneg (probeCrossExponent ε t)]
  have hdiv : 1 / ‖probeCrossExponent ε t‖ < 1 / (1 - 2 * ε) :=
    one_div_lt_one_div_of_lt hγ0 hnβ
  have hsub : 0 < 1 / (1 - 2 * ε) - 1 / ‖probeCrossExponent ε t‖ := sub_pos.mpr hdiv
  unfold probeEnergyLowerRate
  positivity

/-- Below half damping and off the real axis (`t ≠ 0`), `probeEnergyLowerRate ε t > 0` if and only
if `ζ(1 − ε + it) ≠ 0`: the leading energy rate is a positive multiple of the nonnegative
modulus-square `‖ζ(ρ)/ρ‖²`, supplying no sign beyond nonvanishing of `ζ(ρ)`. -/
theorem probeEnergyLowerRate_pos_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ}
    (ht : t ≠ 0) :
    0 < probeEnergyLowerRate ε t ↔ riemannZeta (oscillationExponent ε t) ≠ 0 := by
  constructor
  · intro hpos hz
    rw [probeEnergyLowerRate_eq_zero_of_zeta_eq_zero hz] at hpos
    exact lt_irrefl 0 hpos
  · exact probeEnergyLowerRate_pos hε hε2 ht

/-- **A source prefix bound `|A_{ε,t}(n)| ≤ K (√n)^{1−ε}` implies receiver boundedness.** -/
theorem receiverBounded_oscillatingSmoothPower_of_abs_weightCenteredPrefix_le {ε K : ℝ}
    (hε : 0 < ε) (t : ℝ)
    (hprefix : ∀ n : ℕ, 1 ≤ n →
      |weightCenteredPrefix (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n| ≤ K * Real.sqrt n ^ (1 - ε)) :
    ReceiverBounded (oscillatingSmoothPower ε t) := by
  refine ⟨K ^ 2 * (1 + 1 / ε), fun T => ?_⟩
  rw [weightPronicEnergy]
  exact sum_sq_le_of_abs_le_sqrt_rpow hε hprefix T

/-- **Every paid sub-half oscillating probe satisfies the uniform source prefix bound
`|A_{ε,t}(n)| ≤ floorSumRate ρ · (√n)^{1−ε}`.** -/
theorem abs_weightCenteredPrefix_oscillatingSmoothPower_le_of_receiverBounded {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (t : ℝ)
    (hB : ReceiverBounded (oscillatingSmoothPower ε t)) {n : ℕ} (hn : 1 ≤ n) :
    |weightCenteredPrefix (oscillatingSmoothPower ε t)
      (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n| ≤
      floorSumRate (oscillationExponent ε t) * Real.sqrt n ^ (1 - ε) := by
  have hz := zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower hε hε2 t hB
  have h := abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le hε (by linarith) t hn
  rwa [hz, zero_mul, zero_div, zero_re, sub_zero] at h

/-- **Source-prefix characterization of unpaid sub-half oscillating probes.** For `0 < ε ≤ 1/2`
and `t ∈ ℝ`, `oscillatingSmoothPower ε t` is unpaid if and only if for every constant `K`, its
centred prefix exceeds `K (√n)^{1−ε}` at some `n ≥ 1`. -/
theorem not_receiverBounded_oscillatingSmoothPower_iff_forall_exists_prefix_gt {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (t : ℝ) :
    ¬ ReceiverBounded (oscillatingSmoothPower ε t) ↔
      ∀ K : ℝ, ∃ n : ℕ, 1 ≤ n ∧
        K * Real.sqrt n ^ (1 - ε) <
          |weightCenteredPrefix (oscillatingSmoothPower ε t)
            (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n| := by
  constructor
  · intro hnot K
    by_contra! hle
    exact hnot (receiverBounded_oscillatingSmoothPower_of_abs_weightCenteredPrefix_le hε t hle)
  · intro hall hB
    obtain ⟨n, hn1, hgt⟩ := hall (floorSumRate (oscillationExponent ε t))
    have hle :=
      abs_weightCenteredPrefix_oscillatingSmoothPower_le_of_receiverBounded hε hε2 t hB hn1
    linarith

/-- **The sub-half energy-gap dichotomy.** For `0 < ε < 1/2` and `t ≠ 0`, there is no intermediate
growth regime between `O(1)` and `Θ(T^{1−2ε})`:
* either `ζ(1 − ε + it) = 0`, `c_{ε,t}` is paid, its energy is bounded by
  `floorSumRate ρ ^ 2 * (1 + 1/ε)` at every cutoff `T`, and its prefix is bounded by
  `floorSumRate ρ * (√n)^{1−ε}` for every `n ≥ 1`;
* or `ζ(1 − ε + it) ≠ 0`, `c_{ε,t}` is unpaid, `probeEnergyLowerRate ε t > 0`, and eventually
  `probeEnergyLowerRate ε t · T^{1−2ε} ≤ E_{ε,t}(T) ≤ probeEnergyUpperRate ε t · T^{1−2ε}`. -/
theorem probeEnergy_dichotomy_sub_half {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ}
    (ht : t ≠ 0) :
    (riemannZeta (oscillationExponent ε t) = 0 ∧
      ReceiverBounded (oscillatingSmoothPower ε t) ∧
      (∀ T : ℕ, weightPronicEnergy (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T ≤
        floorSumRate (oscillationExponent ε t) ^ 2 * (1 + 1 / ε)) ∧
      (∀ n : ℕ, 1 ≤ n →
        |weightCenteredPrefix (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n| ≤
          floorSumRate (oscillationExponent ε t) * Real.sqrt n ^ (1 - ε))) ∨
    (riemannZeta (oscillationExponent ε t) ≠ 0 ∧
      ¬ ReceiverBounded (oscillatingSmoothPower ε t) ∧
      0 < probeEnergyLowerRate ε t ∧
      ∀ᶠ T : ℕ in atTop,
        probeEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε) ≤
          weightPronicEnergy (oscillatingSmoothPower ε t)
            (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T ∧
        weightPronicEnergy (oscillatingSmoothPower ε t)
            (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T ≤
          probeEnergyUpperRate ε t * (T : ℝ) ^ (1 - 2 * ε)) := by
  rcases eq_or_ne (riemannZeta (oscillationExponent ε t)) 0 with hz | hz
  · left
    have hB := receiverBounded_oscillatingSmoothPower_of_zeta_eq_zero hε (by linarith) t hz
    have hpre : ∀ n : ℕ, 1 ≤ n →
        |weightCenteredPrefix (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n| ≤
          floorSumRate (oscillationExponent ε t) * Real.sqrt n ^ (1 - ε) :=
      fun n hn =>
        abs_weightCenteredPrefix_oscillatingSmoothPower_le_of_receiverBounded hε hε2.le t hB hn
    refine ⟨hz, hB, fun T => ?_, hpre⟩
    rw [weightPronicEnergy]
    exact sum_sq_le_of_abs_le_sqrt_rpow hε hpre T
  · right
    have hnotB : ¬ ReceiverBounded (oscillatingSmoothPower ε t) := fun hB =>
      hz (zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower hε hε2.le t hB)
    exact ⟨hz, hnotB, probeEnergyLowerRate_pos hε hε2 ht hz,
      eventually_probeEnergy_le_and_ge hε hε2 ht hz⟩

/-- **Little-`o` energy collapse below half damping.** For `0 < ε < 1/2` and `t ≠ 0`, the sub-half
probe `oscillatingSmoothPower ε t` has `O(1)` receiver energy if and only if its energy is merely
`o(T^{1−2ε})`. -/
theorem receiverBounded_oscillatingSmoothPower_iff_tendsto_energy_div_rpow_zero {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ} (ht : t ≠ 0) :
    ReceiverBounded (oscillatingSmoothPower ε t) ↔
      Tendsto (fun T : ℕ =>
        weightPronicEnergy (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T / (T : ℝ) ^ (1 - 2 * ε))
        atTop (𝓝 0) := by
  set γ := 1 - 2 * ε with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  constructor
  · rintro ⟨E, hE⟩
    have hE0 : 0 ≤ E :=
      (sum_nonneg fun n _ => by positivity).trans (hE 0)
    have hlim : Tendsto (fun T : ℕ => E * (T : ℝ) ^ (-γ)) atTop (𝓝 0) := by
      simpa using
        ((tendsto_rpow_neg_atTop hγ0).comp tendsto_natCast_atTop_atTop).const_mul E
    refine squeeze_zero' (Eventually.of_forall fun T => ?_) ?_ hlim
    · exact div_nonneg (sum_nonneg fun n _ => by positivity)
        (Real.rpow_nonneg (Nat.cast_nonneg T) _)
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
      rw [Real.rpow_neg hT0.le, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right (hE T) (Real.rpow_nonneg hT0.le _)
  · intro hlim
    by_contra hnotB
    have hz : riemannZeta (oscillationExponent ε t) ≠ 0 := fun hz =>
      hnotB (receiverBounded_oscillatingSmoothPower_of_zeta_eq_zero hε (by linarith) t hz)
    have hpos : 0 < probeEnergyLowerRate ε t := probeEnergyLowerRate_pos hε hε2 ht hz
    have hev1 := eventually_probeEnergy_le_and_ge hε hε2 ht hz
    have hev2 := (Metric.tendsto_nhds.mp hlim) (probeEnergyLowerRate ε t / 2) (by linarith)
    obtain ⟨T, ⟨⟨hlo, _⟩, hup⟩, hT1⟩ :=
      ((hev1.and hev2).and (eventually_ge_atTop 1)).exists
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
    have hTγ : 0 < (T : ℝ) ^ γ := Real.rpow_pos_of_pos hT0 _
    rw [Real.dist_eq, sub_zero, abs_lt] at hup
    have hdiv : probeEnergyLowerRate ε t ≤
        weightPronicEnergy (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T / (T : ℝ) ^ γ :=
      (le_div_iff₀ hTγ).mpr hlo
    linarith [hup.2]

/-- **Power-growth characterization of unpaid sub-half probes.** For `0 < ε < 1/2` and `t ≠ 0`,
`oscillatingSmoothPower ε t` is unpaid if and only if its receiver energy grows at least as
`c · T^{1−2ε}` for some `c > 0`. -/
theorem not_receiverBounded_oscillatingSmoothPower_iff_eventually_energy_ge {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ} (ht : t ≠ 0) :
    ¬ ReceiverBounded (oscillatingSmoothPower ε t) ↔
      ∃ c > 0, ∀ᶠ T : ℕ in atTop,
        c * (T : ℝ) ^ (1 - 2 * ε) ≤
          weightPronicEnergy (oscillatingSmoothPower ε t)
            (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T := by
  constructor
  · intro hnotB
    have hz : riemannZeta (oscillationExponent ε t) ≠ 0 := fun hz =>
      hnotB (receiverBounded_oscillatingSmoothPower_of_zeta_eq_zero hε (by linarith) t hz)
    refine ⟨probeEnergyLowerRate ε t, probeEnergyLowerRate_pos hε hε2 ht hz, ?_⟩
    filter_upwards [eventually_probeEnergy_le_and_ge hε hε2 ht hz] with T hT
    exact hT.1
  · rintro ⟨c, hc, hev⟩ hB
    have hlim :=
      (receiverBounded_oscillatingSmoothPower_iff_tendsto_energy_div_rpow_zero hε hε2 ht).mp hB
    have hev2 := (Metric.tendsto_nhds.mp hlim) (c / 2) (by linarith)
    obtain ⟨T, ⟨hlo, hup⟩, hT1⟩ := ((hev.and hev2).and (eventually_ge_atTop 1)).exists
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
    have hTγ : 0 < (T : ℝ) ^ (1 - 2 * ε) := Real.rpow_pos_of_pos hT0 _
    rw [Real.dist_eq, sub_zero, abs_lt] at hup
    have hdiv : c ≤
        weightPronicEnergy (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T / (T : ℝ) ^ (1 - 2 * ε) :=
      (le_div_iff₀ hTγ).mpr hlo
    linarith [hup.2]

/-! ### §2. Quantitative power-growth source bounds on zero-free boxes and the VK collar -/

/-- **Quantitative `T^{1−2ε}` energy growth on bounded frequency boxes.** For every height `T`,
there is `δ > 0` such that on `0 < ε < min δ (1/2)` and `0 < |t| ≤ T`, `probeEnergyLowerRate ε t > 0`
and eventually `E_{ε,t}(N) ≥ probeEnergyLowerRate ε t · N^{1−2ε}`. -/
theorem exists_eventually_probeEnergy_ge_box (T : ℝ) :
    ∃ δ > 0, ∀ ε t : ℝ, 0 < ε → ε < min δ (1 / 2) → t ≠ 0 → |t| ≤ T →
      0 < probeEnergyLowerRate ε t ∧
      ∀ᶠ N : ℕ in atTop,
        probeEnergyLowerRate ε t * (N : ℝ) ^ (1 - 2 * ε) ≤
          weightPronicEnergy (oscillatingSmoothPower ε t)
            (∑' d : ℕ, oscillatingSmoothPower ε t d / d) N := by
  obtain ⟨δ, hδ, hbox⟩ := exists_delta_not_receiverBounded_oscillatingSmoothPower_box T
  refine ⟨δ, hδ, fun ε t hε hεm ht0 ht => ?_⟩
  have hε2 : ε < 1 / 2 := hεm.trans_le (min_le_right _ _)
  have hnotB : ¬ ReceiverBounded (oscillatingSmoothPower ε t) :=
    hbox ε t hε hεm.le ht
  have hz : riemannZeta (oscillationExponent ε t) ≠ 0 := fun hz =>
    hnotB (receiverBounded_oscillatingSmoothPower_of_zeta_eq_zero hε (by linarith) t hz)
  refine ⟨probeEnergyLowerRate_pos hε hε2 ht0 hz, ?_⟩
  filter_upwards [eventually_probeEnergy_le_and_ge hε hε2 ht0 hz] with N hN
  exact hN.1

/-- **Quantitative `T^{1−2ε}` energy growth on the Vinogradov–Korobov sub-half strip.** -/
theorem exists_eventually_probeEnergy_ge_vk :
    ∃ T₀ : ℝ, Real.exp (Real.exp 1) ≤ T₀ ∧ ∀ ε t : ℝ, T₀ ≤ |t| → 0 < ε →
      ε < min (1 / 2) (RHTower.vkHadamardWidth |t|) →
      0 < probeEnergyLowerRate ε t ∧
      ∀ᶠ N : ℕ in atTop,
        probeEnergyLowerRate ε t * (N : ℝ) ^ (1 - 2 * ε) ≤
          weightPronicEnergy (oscillatingSmoothPower ε t)
            (∑' d : ℕ, oscillatingSmoothPower ε t d / d) N := by
  obtain ⟨T₀, hT₀, hvk⟩ := exists_not_receiverBounded_oscillatingSmoothPower_vk
  refine ⟨T₀, hT₀, fun ε t ht hε hεw => ?_⟩
  have hε2 : ε < 1 / 2 := hεw.trans_le (min_le_left _ _)
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at ht
    linarith [Real.exp_pos (Real.exp 1)]
  have hnotB := hvk ε t ht hε hεw
  have hz : riemannZeta (oscillationExponent ε t) ≠ 0 := fun hz =>
    hnotB (receiverBounded_oscillatingSmoothPower_of_zeta_eq_zero hε (by linarith) t hz)
  refine ⟨probeEnergyLowerRate_pos hε hε2 ht0 hz, ?_⟩
  filter_upwards [eventually_probeEnergy_le_and_ge hε hε2 ht0 hz] with N hN
  exact hN.1

/-- **Uniform all-frequency Vinogradov–Korobov `T^{1−2ε}` energy lower bound.** -/
theorem exists_eventually_probeEnergy_ge_vk_uniform :
    ∃ δ K₀ : ℝ, 0 < δ ∧ Real.exp (Real.exp 30) ≤ K₀ ∧
      ∀ (ε t K : ℝ), K₀ ≤ K → t ≠ 0 → |t| ≤ K → 0 < ε →
        ε < min (1 / 2) (min δ (RHTower.vkHadamardWidth (K + 1)) / 4) →
        0 < probeEnergyLowerRate ε t ∧
        ∀ᶠ N : ℕ in atTop,
          probeEnergyLowerRate ε t * (N : ℝ) ^ (1 - 2 * ε) ≤
            weightPronicEnergy (oscillatingSmoothPower ε t)
              (∑' d : ℕ, oscillatingSmoothPower ε t d / d) N := by
  obtain ⟨δ, K₀, hδ, hK₀, hvk⟩ := exists_not_receiverBounded_oscillatingSmoothPower_vk_uniform
  refine ⟨δ, K₀, hδ, hK₀, fun ε t K hK ht0 ht hε hεw => ?_⟩
  have hε2 : ε < 1 / 2 := hεw.trans_le (min_le_left _ _)
  have hnotB := hvk ε t K hK ht hε hεw.le
  have hz : riemannZeta (oscillationExponent ε t) ≠ 0 := fun hz =>
    hnotB (receiverBounded_oscillatingSmoothPower_of_zeta_eq_zero hε (by linarith) t hz)
  refine ⟨probeEnergyLowerRate_pos hε hε2 ht0 hz, ?_⟩
  filter_upwards [eventually_probeEnergy_le_and_ge hε hε2 ht0 hz] with N hN
  exact hN.1

/-! ### §3. Planted Euler-factor kernels: why collars and finiteness do not exclude all `0 < ε < 1/2` -/

/-- The 3-term real Euler-factor kernel planted at `(ε₁, t₁)`:
`k(1) = 1`, `k(2) = −2 Re(2^{1−ε₁+it₁})`, `k(4) = (2^{1−ε₁})²`, and `k(j) = 0` otherwise. -/
def plantedEulerKernel (ε₁ t₁ : ℝ) (j : ℕ) : ℝ :=
  if j = 1 then 1
  else if j = 2 then -2 * (((2 : ℝ) : ℂ) ^ oscillationExponent ε₁ t₁).re
  else if j = 4 then ((2 : ℝ) ^ (1 - ε₁)) ^ 2
  else 0

@[simp]
theorem plantedEulerKernel_one (ε₁ t₁ : ℝ) : plantedEulerKernel ε₁ t₁ 1 = 1 := rfl

theorem plantedEulerKernel_eq_zero_of_not_mem (ε₁ t₁ : ℝ) {j : ℕ}
    (hj : j ∉ ({1, 2, 4} : Finset ℕ)) :
    plantedEulerKernel ε₁ t₁ j = 0 := by
  simp only [mem_insert, mem_singleton, not_or] at hj
  rcases hj with ⟨h1, h2, h4⟩
  simp [plantedEulerKernel, h1, h2, h4]

/-- Being finitely supported on `{1, 2, 4}`, `plantedEulerKernel ε₁ t₁` lies in the critical
Wiener algebra. -/
theorem criticalWiener_plantedEulerKernel (ε₁ t₁ : ℝ) :
    CriticalWiener (plantedEulerKernel ε₁ t₁) := by
  refine summable_of_ne_finset_zero (s := ({1, 2, 4} : Finset ℕ)) fun j hj => ?_
  rw [plantedEulerKernel_eq_zero_of_not_mem ε₁ t₁ hj, abs_zero, zero_mul]

/-- `(4 : ℂ)^w = ((2 : ℂ)^w)^2` for every complex exponent `w`. -/
theorem four_cpow_eq_sq (w : ℂ) : ((4 : ℝ) : ℂ) ^ w = (((2 : ℝ) : ℂ) ^ w) ^ 2 := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h4 : (0 : ℝ) < 4 := by norm_num
  rw [sq, Complex.cpow_def_of_ne_zero (by exact_mod_cast h4.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast h2.ne'), ← Complex.exp_add,
    ← Complex.ofReal_log h4.le, ← Complex.ofReal_log h2.le,
    show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul h2.ne' h2.ne']
  congr 1
  push_cast
  ring

/-- **Exact quadratic factorization of the planted Euler-factor Dirichlet polynomial.** For every
`ρ ∈ ℂ`, with `u = 2^{1−ε₁+it₁}` and `z = 2^{-ρ}`,
`complexPoleValue (plantedEulerKernel ε₁ t₁) ρ = (1 − u z)(1 − ū z)`. -/
theorem complexPoleValue_plantedEulerKernel_eq_mul (ε₁ t₁ : ℝ) (ρ : ℂ) :
    complexPoleValue (plantedEulerKernel ε₁ t₁) ρ =
      (1 - ((2 : ℝ) : ℂ) ^ oscillationExponent ε₁ t₁ * ((2 : ℝ) : ℂ) ^ (-ρ)) *
      (1 - starRingEnd ℂ (((2 : ℝ) : ℂ) ^ oscillationExponent ε₁ t₁) *
        ((2 : ℝ) : ℂ) ^ (-ρ)) := by
  unfold complexPoleValue
  rw [tsum_eq_sum (s := ({1, 2, 4} : Finset ℕ)) fun j hj => by
    rw [plantedEulerKernel_eq_zero_of_not_mem ε₁ t₁ hj, Complex.ofReal_zero, zero_mul]]
  have hsum :
      ∑ j ∈ ({1, 2, 4} : Finset ℕ),
        (plantedEulerKernel ε₁ t₁ j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) =
      (plantedEulerKernel ε₁ t₁ 1 : ℂ) * ((1 : ℝ) : ℂ) ^ (-ρ) +
      (plantedEulerKernel ε₁ t₁ 2 : ℂ) * ((2 : ℝ) : ℂ) ^ (-ρ) +
      (plantedEulerKernel ε₁ t₁ 4 : ℂ) * ((4 : ℝ) : ℂ) ^ (-ρ) := by
    simp [add_assoc]
  rw [hsum]
  set u : ℂ := ((2 : ℝ) : ℂ) ^ oscillationExponent ε₁ t₁ with hu
  set z : ℂ := ((2 : ℝ) : ℂ) ^ (-ρ) with hz
  have hu_norm : ‖u‖ = (2 : ℝ) ^ (1 - ε₁) := by
    rw [hu, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2),
      oscillationExponent_re]
  have hu_add : ((2 * u.re : ℝ) : ℂ) = u + starRingEnd ℂ u := by
    apply Complex.ext <;> simp [two_mul]
  have hu_mul : ((((2 : ℝ) ^ (1 - ε₁)) ^ 2 : ℝ) : ℂ) = u * starRingEnd ℂ u := by
    rw [← hu_norm, ← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  have h1 : (plantedEulerKernel ε₁ t₁ 1 : ℂ) * ((1 : ℝ) : ℂ) ^ (-ρ) = 1 := by
    simp [plantedEulerKernel]
  have h2 : (plantedEulerKernel ε₁ t₁ 2 : ℂ) * ((2 : ℝ) : ℂ) ^ (-ρ) =
      -(u + starRingEnd ℂ u) * z := by
    have hp2 : plantedEulerKernel ε₁ t₁ 2 = -2 * u.re := by
      simp [plantedEulerKernel, hu]
    rw [hp2, ← hz, show (-2 * u.re : ℝ) = -(2 * u.re) by ring, Complex.ofReal_neg, hu_add]
  have h4 : (plantedEulerKernel ε₁ t₁ 4 : ℂ) * ((4 : ℝ) : ℂ) ^ (-ρ) =
      (u * starRingEnd ℂ u) * z ^ 2 := by
    have hp4 : plantedEulerKernel ε₁ t₁ 4 = ((2 : ℝ) ^ (1 - ε₁)) ^ 2 := by
      simp [plantedEulerKernel]
    rw [hp4, four_cpow_eq_sq (-ρ), ← hz, hu_mul]
  rw [h1, h2, h4]
  ring

/-- At the planted target `ρ₁ = 1 − ε₁ + it₁`, the complex pole value of
`plantedEulerKernel ε₁ t₁` vanishes. -/
theorem complexPoleValue_plantedEulerKernel_eq_zero_at_target (ε₁ t₁ : ℝ) :
    complexPoleValue (plantedEulerKernel ε₁ t₁) (oscillationExponent ε₁ t₁) = 0 := by
  rw [complexPoleValue_plantedEulerKernel_eq_mul]
  have hcancel :
      ((2 : ℝ) : ℂ) ^ oscillationExponent ε₁ t₁ *
        ((2 : ℝ) : ℂ) ^ (-oscillationExponent ε₁ t₁) = 1 := by
    rw [← Complex.cpow_add _ _ (by norm_num : ((2 : ℝ) : ℂ) ≠ 0), add_neg_cancel,
      Complex.cpow_zero]
  rw [hcancel, sub_self, zero_mul]

/-- At every damping `ε ≠ ε₁` and every frequency `t ∈ ℝ`, the complex pole value of
`plantedEulerKernel ε₁ t₁` is strictly nonzero because `‖2^{ρ₁ − ρ}‖ = 2^{ε − ε₁} ≠ 1`. -/
theorem complexPoleValue_plantedEulerKernel_ne_zero_of_ne (ε₁ t₁ : ℝ) {ε : ℝ} (hε : ε ≠ ε₁)
    (t : ℝ) :
    complexPoleValue (plantedEulerKernel ε₁ t₁) (oscillationExponent ε t) ≠ 0 := by
  rw [complexPoleValue_plantedEulerKernel_eq_mul]
  set u : ℂ := ((2 : ℝ) : ℂ) ^ oscillationExponent ε₁ t₁ with hu
  set z : ℂ := ((2 : ℝ) : ℂ) ^ (-oscillationExponent ε t) with hz
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hu_norm : ‖u‖ = (2 : ℝ) ^ (1 - ε₁) := by
    rw [hu, Complex.norm_cpow_eq_rpow_re_of_pos h2pos, oscillationExponent_re]
  have hz_norm : ‖z‖ = (2 : ℝ) ^ (-(1 - ε)) := by
    rw [hz, Complex.norm_cpow_eq_rpow_re_of_pos h2pos, neg_re, oscillationExponent_re]
  have hprod_norm : (2 : ℝ) ^ (1 - ε₁) * (2 : ℝ) ^ (-(1 - ε)) ≠ 1 := by
    rw [← Real.rpow_add h2pos, show 1 - ε₁ + -(1 - ε) = ε - ε₁ by ring]
    rcases lt_or_gt_of_ne hε with hlt | hgt
    · exact (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)).ne
    · exact (Real.one_lt_rpow (by norm_num) (by linarith)).ne'
  have huz : 1 - u * z ≠ 0 := by
    intro h0
    have heq : u * z = 1 := (sub_eq_zero.mp h0).symm
    have hnorm := congrArg norm heq
    rw [norm_mul, hu_norm, hz_norm, norm_one] at hnorm
    exact hprod_norm hnorm
  have hcz : 1 - starRingEnd ℂ u * z ≠ 0 := by
    intro h0
    have heq : starRingEnd ℂ u * z = 1 := (sub_eq_zero.mp h0).symm
    have hnorm := congrArg norm heq
    rw [norm_mul, Complex.norm_conj, hu_norm, hz_norm, norm_one] at hnorm
    exact hprod_norm hnorm
  exact mul_ne_zero huz hcz

/-- **Unconditional admission at the planted sub-half target `(ε₁, t₁)`.** For every
`0 < ε₁ < 1/2` and `t₁ ∈ ℝ`, the convolved oscillating probe
`plantedEulerKernel ε₁ t₁ ⋆ oscillatingSmoothPower ε₁ t₁` has bounded receiver. -/
theorem receiverBounded_plantedEulerKernel_at_target {ε₁ : ℝ} (hε₁ : 0 < ε₁) (hε₁2 : ε₁ < 1 / 2)
    (t₁ : ℝ) :
    ReceiverBounded
      (RHTower.dirichletConv (plantedEulerKernel ε₁ t₁) (oscillatingSmoothPower ε₁ t₁)) := by
  rw [receiverBounded_dirichletConv_oscillatingSmoothPower_iff hε₁ hε₁2 t₁
    (criticalWiener_plantedEulerKernel ε₁ t₁)]
  exact Or.inl (complexPoleValue_plantedEulerKernel_eq_zero_at_target ε₁ t₁)

/-- **Away from the planted damping `ε₁`, `plantedEulerKernel ε₁ t₁` preserves the exact
admission locus of `oscillatingSmoothPower ε t`.** -/
theorem receiverBounded_plantedEulerKernel_iff_of_ne (ε₁ t₁ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) (hne : ε ≠ ε₁) (t : ℝ) :
    ReceiverBounded
      (RHTower.dirichletConv (plantedEulerKernel ε₁ t₁) (oscillatingSmoothPower ε t)) ↔
      ReceiverBounded (oscillatingSmoothPower ε t) := by
  rw [receiverBounded_dirichletConv_oscillatingSmoothPower_iff hε hε2 t
    (criticalWiener_plantedEulerKernel ε₁ t₁),
    receiverBounded_oscillatingSmoothPower_iff hε hε2.le t, oscillationExponent]
  exact or_iff_right (complexPoleValue_plantedEulerKernel_ne_zero_of_ne ε₁ t₁ hne t)

/-- **At every frequency `t ∈ ℝ`, the set of admitted sub-half dampings for
`plantedEulerKernel ε₁ t₁ ⋆ oscillatingSmoothPower ε t` is finite.** -/
theorem finite_damping_receiverBounded_plantedEulerKernel (ε₁ t₁ t : ℝ) :
    {ε : ℝ | 0 < ε ∧ ε < 1 / 2 ∧
      ReceiverBounded
        (RHTower.dirichletConv (plantedEulerKernel ε₁ t₁) (oscillatingSmoothPower ε t))}.Finite := by
  refine ((Set.finite_singleton ε₁).union
    (finite_damping_receiverBounded_oscillatingSmoothPower t)).subset fun ε hε => ?_
  rcases hε with ⟨hε0, hε2, hB⟩
  by_cases hne : ε = ε₁
  · exact Or.inl hne
  · exact Or.inr ⟨hε0, hε2.le,
      (receiverBounded_plantedEulerKernel_iff_of_ne ε₁ t₁ hε0 hε2 hne t).mp hB⟩

/-- **At every sub-half damping `ε ≠ ε₁` and height `T`, the set of admitted frequencies in
`[−T, T]` for `plantedEulerKernel ε₁ t₁ ⋆ oscillatingSmoothPower ε t` is finite.** -/
theorem finite_freq_receiverBounded_plantedEulerKernel (ε₁ t₁ : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) (hne : ε ≠ ε₁) (T : ℝ) :
    {t : ℝ | |t| ≤ T ∧
      ReceiverBounded
        (RHTower.dirichletConv (plantedEulerKernel ε₁ t₁) (oscillatingSmoothPower ε t))}.Finite := by
  refine (finite_freq_receiverBounded_oscillatingSmoothPower hε hε2.le T).subset fun t ht => ?_
  exact ⟨ht.1, (receiverBounded_plantedEulerKernel_iff_of_ne ε₁ t₁ hε hε2 hne t).mp ht.2⟩

/-- **Why near-`ε = 0` collars and finite admitted-parameter sets do not exclude all
`0 < ε < 1/2`.** For every target `(ε₁, t₁)` with `0 < ε₁ < 1/2` and every frequency box `T ≥ |t₁|`,
the family `w_{ε,t} = plantedEulerKernel ε₁ t₁ ⋆ oscillatingSmoothPower ε t` simultaneously
satisfies:
1. **Unconditional non-admission on a near-`ε = 0` collar** `0 < ε < min ε₁ (min δ (1/2))` across
   the box `|t| ≤ T` (with `δ > 0`) and on the sub-`ε₁` Vinogradov–Korobov collar;
2. **Finiteness of admitted dampings `ε ∈ (0, 1/2)`** at every frequency `t ∈ ℝ`, and **finiteness
   of admitted frequencies `t ∈ [−T, T]`** at every damping `ε ∈ (0, 1/2) \ {ε₁}`;
3. **Unconditional admission at `(ε₁, t₁)`** inside `(0, 1/2) × [−T, T]`. -/
theorem plantedEulerKernel_collar_and_finiteness_obstruction {ε₁ : ℝ} (hε₁ : 0 < ε₁)
    (hε₁2 : ε₁ < 1 / 2) (t₁ T : ℝ) :
    (∃ δ > 0, ∀ ε t : ℝ, 0 < ε → ε < min ε₁ (min δ (1 / 2)) → |t| ≤ T →
      ¬ ReceiverBounded
        (RHTower.dirichletConv (plantedEulerKernel ε₁ t₁) (oscillatingSmoothPower ε t))) ∧
    (∀ t : ℝ,
      {ε : ℝ | 0 < ε ∧ ε < 1 / 2 ∧
        ReceiverBounded
          (RHTower.dirichletConv (plantedEulerKernel ε₁ t₁) (oscillatingSmoothPower ε t))}.Finite) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ε ≠ ε₁ →
      {t : ℝ | |t| ≤ T ∧
        ReceiverBounded
          (RHTower.dirichletConv (plantedEulerKernel ε₁ t₁) (oscillatingSmoothPower ε t))}.Finite) ∧
    ReceiverBounded
      (RHTower.dirichletConv (plantedEulerKernel ε₁ t₁) (oscillatingSmoothPower ε₁ t₁)) := by
  obtain ⟨δ, hδ, hbox⟩ := exists_delta_not_receiverBounded_oscillatingSmoothPower_box T
  refine ⟨⟨δ, hδ, fun ε t hε hεm ht hB => ?_⟩,
    finite_damping_receiverBounded_plantedEulerKernel ε₁ t₁,
    fun ε hε hε2 hne => finite_freq_receiverBounded_plantedEulerKernel ε₁ t₁ hε hε2 hne T,
    receiverBounded_plantedEulerKernel_at_target hε₁ hε₁2 t₁⟩
  have hlt1 : ε < ε₁ := hεm.trans_le (min_le_left _ _)
  have hlt2 : ε < min δ (1 / 2) := hεm.trans_le (min_le_right _ _)
  have hε2 : ε < 1 / 2 := hlt2.trans_le (min_le_right _ _)
  have hB0 := (receiverBounded_plantedEulerKernel_iff_of_ne ε₁ t₁ hε hε2 hlt1.ne t).mp hB
  exact hbox ε t hε hlt2.le ht hB0

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
