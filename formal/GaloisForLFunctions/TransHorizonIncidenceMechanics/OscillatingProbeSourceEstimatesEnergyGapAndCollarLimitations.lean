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

4. **Source decomposition into fractional-part sawtooth sum and universal tail drift: pure source
   estimates at `t = 0` and anti-phase cancellation (`§4`).**
   - Every oscillating prefix splits identically into two source components
     (`weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail`):
     `A_{ε,t}(n) = S_{ε,t}(n) + T_{ε,t}(n)`, where
     `S_{ε,t}(n) = Σ_{d ≤ n} c_{ε,t}(d) (⌊n/d⌋ − n/d)` is the fractional-part sawtooth sum and
     `T_{ε,t}(n) = n (Σ_{d ≤ n} c_{ε,t}(d)/d − Σ_{d ≥ 1} c_{ε,t}(d)/d)` is the universal tail drift.
   - At `t = 0`, both components have nonpositive sign (`oscillatingSawtoothPrefix_zero_nonpos` and
     `oscillatingTailDrift_zero_le`), giving the one-sided source bound
     `A_{ε,0}(n) ≤ −2^{-(1+ε)} n^{1−ε}` (`weightCenteredPrefix_oscillatingSmoothPower_zero_le`),
     the harmonic energy lower bound
     `E_{ε,0}(T) ≥ (2^{-(1+ε)})² / 2 · H_T` (`probeEnergy_zero_ge_harmonic`), and a pure
     source-estimate proof of `¬ ReceiverBounded (oscillatingSmoothPower ε 0)` for all
     `0 < ε ≤ 1/2` (`not_receiverBounded_oscillatingSmoothPower_zero_from_source`) without invoking
     `ζ(1 − ε) ≠ 0`.
   - For general `t ∈ ℝ`, the universal tail drift tracks `Re(n^ρ / (ρ − 1))` to within
     `O(n^{-ε})` (`abs_oscillatingTailDrift_sub_le`), while the sawtooth sum tracks
     `Re((ζ(ρ)/ρ − 1/(ρ − 1)) n^ρ)` to within `O((√n)^{1−ε})` (`abs_oscillatingSawtoothPrefix_sub_le`).
   - Consequently, for **every** `0 < ε ≤ 1/2` and **every** `t ∈ ℝ` (independently of `ζ(ρ)`),
     the universal source tail `T_{ε,t}` has unbounded pronic norm
     (`not_bdd_pronicNorm_oscillatingTailDrift`), and `c_{ε,t}` is paid if and only if the sawtooth
     sum `S_{ε,t}` cancels `T_{ε,t}` in `L²(pronic)` (`receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_sawtooth_add_tail`),
     in which case `S_{ε,t}` is also unconditionally unbounded in pronic norm
     (`not_bdd_pronicNorm_oscillatingSawtoothPrefix_of_receiverBounded`) and locked in anti-phase
     `S_{ε,t}(n) = −Re(n^ρ/(ρ − 1)) + O((√n)^{1−ε})`.

5. **The alternate Route MC receiver: short/long sawtooth split, quantitative tail energy, and
   nonzero-frequency sawtooth/tail non-cancellation (`§5`).**
   - Splitting `S_{ε,t}(n) = S^{\mathrm{short}}_{ε,t}(n) + S^{\mathrm{long}}_{ε,t}(n)` at the
     hyperbola threshold `⌊√n⌋` (`oscillatingSawtoothPrefix_eq_short_add_long`), the short-modulus
     sawtooth sum `1 ≤ d ≤ ⌊√n⌋` satisfies
     `|S^{\mathrm{short}}_{ε,t}(n)| ≤ (1 + 1/(1 − ε)) (√n)^{1−ε}` (`abs_oscillatingShortSawtooth_le`)
     and has uniformly bounded pronic norm `≤ (1 + 1/(1 − ε)) √(1 + 1/ε)` for every `0 < ε < 1` and
     `t ∈ ℝ` (`pronicNorm_oscillatingShortSawtooth_le`). Hence sawtooth/tail cancellation occurs if
     and only if the **long-modulus** sawtooth sum `⌊√n⌋ < d ≤ n` cancels the tail drift `d > n`
     (`receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_longSawtooth_add_tail`).
   - For every `0 < ε < 1/2` and `t ≠ 0` (independently of `ζ(ρ)`), the universal tail drift has
     strictly positive lower energy rate `tailEnergyLowerRate ε t > 0` (`tailEnergyLowerRate_pos`)
     and satisfies the two-sided power law
     `tailEnergyLowerRate ε t · T^{1−2ε} ≤ ‖T_{ε,t}‖_T² ≤ tailEnergyUpperRate ε t · T^{1−2ε}`
     eventually (`eventually_oscillatingTailDrift_energy_le_and_ge`).
   - In the pronic inner product `pronicInner`, the receiver energy polarizes as
     `E_{ε,t}(T) = ‖S_{ε,t}‖_T² + 2 ⟨S_{ε,t}, T_{ε,t}⟩_T + ‖T_{ε,t}‖_T²`
     (`weightPronicEnergy_oscillatingSmoothPower_eq_sawtooth_tail_polarization`). Any imperfect
     anti-alignment `−⟨S_{ε,t}, T_{ε,t}⟩_T ≤ θ ‖S_{ε,t}‖_T ‖T_{ε,t}‖_T` with `θ < 1` forces
     `E_{ε,t}(T) ≥ (1 − θ²) ‖T_{ε,t}‖_T²` (`weightPronicEnergy_ge_one_sub_sq_mul_tail_of_pronicInner_le`)
     and excludes admission (`not_receiverBounded_of_sawtooth_tail_inner_le`).
   - Because `t = 0` source exclusion is closed directly from floor/tail arithmetic, the alternate
     Route MC receiver for RH reduces to excluding sawtooth/tail (or long-sawtooth/tail)
     cancellation for nonzero frequencies `t ≠ 0` across `0 < ε < 1/2`
     (`riemannHypothesis_iff_forall_ne_zero_not_bdd_sawtooth_add_tail`,
     `riemannHypothesis_iff_forall_ne_zero_not_bdd_longSawtooth_add_tail`, and the master theorem
     `routeMC_alternate_receiver_sawtooth_tail_master`).
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

/-! ### §4. Source decomposition into sawtooth sum and tail drift: pure source estimates at `t = 0` and anti-phase cancellation -/

/-- The fractional-part (sawtooth) source sum of `oscillatingSmoothPower ε t`:
`S_{ε,t}(n) = Σ_{d ≤ n} c_{ε,t}(d) (⌊n/d⌋ − n/d) = −Σ_{d ≤ n} c_{ε,t}(d) {n/d}`. -/
def oscillatingSawtoothPrefix (ε t : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 n, oscillatingSmoothPower ε t d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d)

/-- The universal source tail drift of `oscillatingSmoothPower ε t`:
`T_{ε,t}(n) = n (Σ_{d ≤ n} c_{ε,t}(d)/d − Σ_{d ≥ 1} c_{ε,t}(d)/d) = −n Σ_{d > n} c_{ε,t}(d)/d`. -/
def oscillatingTailDrift (ε t : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (∑ d ∈ Icc 1 n, oscillatingSmoothPower ε t d / d -
    ∑' d : ℕ, oscillatingSmoothPower ε t d / d)

/-- **Exact source decomposition of the centred prefix.** For every `ε, t ∈ ℝ` and `n ∈ ℕ`,
`A_{ε,t}(n) = S_{ε,t}(n) + T_{ε,t}(n)`. -/
theorem weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail (ε t : ℝ) (n : ℕ) :
    weightCenteredPrefix (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n =
      oscillatingSawtoothPrefix ε t n + oscillatingTailDrift ε t n := by
  rw [weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
    oscillatingSawtoothPrefix, oscillatingTailDrift]
  have hsub :
      ∑ d ∈ Icc 1 n, oscillatingSmoothPower ε t d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d) =
        ∑ d ∈ Icc 1 n, oscillatingSmoothPower ε t d * ((n / d : ℕ) : ℝ) -
          ∑ d ∈ Icc 1 n, oscillatingSmoothPower ε t d * ((n : ℝ) / d) := by
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun d _ => by ring
  have h1 : (n : ℝ) * ∑ d ∈ Icc 1 n, oscillatingSmoothPower ε t d / d =
      ∑ d ∈ Icc 1 n, oscillatingSmoothPower ε t d * ((n : ℝ) / d) := by
    rw [mul_sum]
    exact sum_congr rfl fun d _ => by ring
  rw [hsub, ← h1]
  ring

/-- At `t = 0`, `oscillatingSmoothPower ε 0 d = d^{-ε}`. -/
theorem oscillatingSmoothPower_zero_eq_rpow (ε : ℝ) (d : ℕ) :
    oscillatingSmoothPower ε 0 d = (d : ℝ) ^ (-ε) := by
  simp [oscillatingSmoothPower]

/-- At `t = 0`, every summand of `oscillatingSawtoothPrefix ε 0 n` is nonpositive because
`d^{-ε} ≥ 0` and `⌊n/d⌋ ≤ n/d`. -/
theorem oscillatingSawtoothPrefix_zero_nonpos (ε : ℝ) (n : ℕ) :
    oscillatingSawtoothPrefix ε 0 n ≤ 0 := by
  unfold oscillatingSawtoothPrefix
  refine sum_nonpos fun d _ => ?_
  rw [oscillatingSmoothPower_zero_eq_rpow]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    (sub_nonpos.mpr Nat.cast_div_le)

/-- **One-sided dyadic source lower bound for the tail drift at `t = 0`.** For `ε > 0` and `n ≥ 1`,
the single dyadic tail block `d ∈ [n + 1, 2n]` forces
`T_{ε,0}(n) ≤ −2^{-(1+ε)} n^{1−ε}`, with no reference to `ζ(s)`. -/
theorem oscillatingTailDrift_zero_le {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    oscillatingTailDrift ε 0 n ≤ -(2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set g : ℕ → ℝ := fun d => oscillatingSmoothPower ε 0 d / d with hg
  have hg_sum : Summable g := (hasSum_oscillatingSmoothPower_div hε 0).summable
  have hg_nonneg : ∀ d : ℕ, 0 ≤ g d := fun d => by
    simp only [hg, oscillatingSmoothPower_zero_eq_rpow]
    exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _) (Nat.cast_nonneg d)
  have htsum : ∑ d ∈ Icc 1 (2 * n), g d ≤ ∑' d : ℕ, g d :=
    hg_sum.sum_le_tsum (Icc 1 (2 * n)) fun d _ => hg_nonneg d
  have hsplit : Icc 1 (2 * n) = Icc 1 n ∪ Ioc n (2 * n) := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 n) (Ioc n (2 * n)) :=
    disjoint_left.mpr fun d h1 h2 => by simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj] at htsum
  have hblock : (n : ℝ) * (2 * (n : ℝ)) ^ (-(1 + ε)) ≤ ∑ d ∈ Ioc n (2 * n), g d := by
    have hterm : ∀ d ∈ Ioc n (2 * n), (2 * (n : ℝ)) ^ (-(1 + ε)) ≤ g d := by
      intro d hd
      rw [mem_Ioc] at hd
      have hd1 : 1 ≤ d := by omega
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have hd2n : (d : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hd.2
      have hgd : g d = (d : ℝ) ^ (-(1 + ε)) := by
        simp only [hg, oscillatingSmoothPower_zero_eq_rpow]
        rw [div_eq_mul_inv, ← Real.rpow_neg_one (d : ℝ), ← Real.rpow_add hd0]
        congr 1; ring
      rw [hgd]
      exact Real.rpow_le_rpow_of_nonpos hd0 hd2n (by linarith)
    calc (n : ℝ) * (2 * (n : ℝ)) ^ (-(1 + ε))
        = ∑ _d ∈ Ioc n (2 * n), (2 * (n : ℝ)) ^ (-(1 + ε)) := by
          rw [sum_const, Nat.card_Ioc, show 2 * n - n = n by omega, nsmul_eq_mul]
      _ ≤ ∑ d ∈ Ioc n (2 * n), g d := sum_le_sum hterm
  have hdiff : ∑ d ∈ Icc 1 n, g d - ∑' d : ℕ, g d ≤ -(n : ℝ) * (2 * (n : ℝ)) ^ (-(1 + ε)) := by
    linarith
  have hpow : (n : ℝ) * (-(n : ℝ) * (2 * (n : ℝ)) ^ (-(1 + ε))) =
      -(2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn0.le]
    have hn_pow : (n : ℝ) ^ (1 - ε) = (n : ℝ) ^ (-(1 + ε)) * (n : ℝ) * (n : ℝ) := by
      rw [show 1 - ε = -(1 + ε) + 1 + 1 by ring, Real.rpow_add_one hn0.ne',
        Real.rpow_add_one hn0.ne']
    rw [hn_pow]
    ring
  unfold oscillatingTailDrift
  calc (n : ℝ) * (∑ d ∈ Icc 1 n, g d - ∑' d : ℕ, g d)
      ≤ (n : ℝ) * (-(n : ℝ) * (2 * (n : ℝ)) ^ (-(1 + ε))) :=
        mul_le_mul_of_nonneg_left hdiff hn0.le
    _ = -(2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) := hpow

/-- **Pure one-sided source bound for the centred prefix at `t = 0`.** For `ε > 0` and `n ≥ 1`,
`A_{ε,0}(n) ≤ −2^{-(1+ε)} n^{1−ε}` directly from `⌊n/d⌋ ≤ n/d` and the dyadic tail block. -/
theorem weightCenteredPrefix_oscillatingSmoothPower_zero_le {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : 1 ≤ n) :
    weightCenteredPrefix (oscillatingSmoothPower ε 0)
        (∑' d : ℕ, oscillatingSmoothPower ε 0 d / d) n ≤
      -(2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) := by
  rw [weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail]
  linarith [oscillatingSawtoothPrefix_zero_nonpos ε n, oscillatingTailDrift_zero_le hε hn]

/-- **Pure source-estimate harmonic lower bound for the receiver energy at `t = 0`.** For
`0 < ε ≤ 1/2` and every cutoff `T`, `E_{ε,0}(T) ≥ ((2^{-(1+ε)})² / 2) Σ_{n ≤ T} 1/n`. -/
theorem probeEnergy_zero_ge_harmonic {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (T : ℕ) :
    ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) ≤
      weightPronicEnergy (oscillatingSmoothPower ε 0)
        (∑' d : ℕ, oscillatingSmoothPower ε 0 d / d) T := by
  set c := (2 : ℝ) ^ (-(1 + ε)) with hc
  have hc0 : 0 ≤ c := by positivity
  rw [weightPronicEnergy, mul_sum]
  refine sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpre := weightCenteredPrefix_oscillatingSmoothPower_zero_le hε hn1
  have habs : c * (n : ℝ) ^ (1 - ε) ≤
      |weightCenteredPrefix (oscillatingSmoothPower ε 0)
        (∑' d : ℕ, oscillatingSmoothPower ε 0 d / d) n| := by
    calc c * (n : ℝ) ^ (1 - ε)
        ≤ -weightCenteredPrefix (oscillatingSmoothPower ε 0)
            (∑' d : ℕ, oscillatingSmoothPower ε 0 d / d) n := by linarith
      _ ≤ _ := neg_le_abs _
  have hsq : (c * (n : ℝ) ^ (1 - ε)) ^ 2 ≤
      weightCenteredPrefix (oscillatingSmoothPower ε 0)
        (∑' d : ℕ, oscillatingSmoothPower ε 0 d / d) n ^ 2 := by
    rw [← sq_abs (weightCenteredPrefix _ _ _)]
    exact pow_le_pow_left₀ (by positivity) habs 2
  have hpow : (n : ℝ) ≤ ((n : ℝ) ^ (1 - ε)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (n : ℝ) ^ ((1 - ε) * ((2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hnR (by push_cast; linarith)
  have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
  rw [le_div_iff₀ hpr]
  calc c ^ 2 / 2 * (1 / (n : ℝ)) * ((n : ℝ) * ((n : ℝ) + 1))
      = c ^ 2 * ((n : ℝ) + 1) / 2 := by field_simp
    _ ≤ c ^ 2 * (n : ℝ) := by
        have : (n : ℝ) + 1 ≤ 2 * (n : ℝ) := by linarith
        nlinarith [sq_nonneg c]
    _ ≤ c ^ 2 * ((n : ℝ) ^ (1 - ε)) ^ 2 := mul_le_mul_of_nonneg_left hpow (sq_nonneg c)
    _ = (c * (n : ℝ) ^ (1 - ε)) ^ 2 := by ring
    _ ≤ weightCenteredPrefix (oscillatingSmoothPower ε 0)
          (∑' d : ℕ, oscillatingSmoothPower ε 0 d / d) n ^ 2 := hsq

/-- **Pure source-estimate proof that `oscillatingSmoothPower ε 0` is unpaid on `0 < ε ≤ 1/2`.**
Unlike `not_receiverBounded_oscillatingSmoothPower_zero`, this proof uses only the one-sided
floor/dyadic-tail source bound `weightCenteredPrefix_oscillatingSmoothPower_zero_le` and harmonic
divergence, without invoking `riemannZeta`. -/
theorem not_receiverBounded_oscillatingSmoothPower_zero_from_source {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    ¬ ReceiverBounded (oscillatingSmoothPower ε 0) := by
  rintro ⟨E, hE⟩
  set c := ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨T, -, hT⟩ := not_bddAbove_sum_Icc_one_div (E / c)
  have hlo := probeEnergy_zero_ge_harmonic hε hε2 T
  have hup := hE T
  rw [div_lt_iff₀ hc0] at hT
  rw [← hc] at hlo
  nlinarith

/-- The rate constant for the universal source tail drift:
`K^{\mathrm{tail}}_ρ = ‖2 − ρ‖ (1 + 1 / Re(2 − ρ))`. -/
def tailDriftRate (ρ : ℂ) : ℝ := ‖2 - ρ‖ * (1 + 1 / (2 - ρ).re)

theorem tailDriftRate_nonneg {ρ : ℂ} (hre : 0 < (2 - ρ).re) : 0 ≤ tailDriftRate ρ := by
  unfold tailDriftRate
  have : 0 ≤ 1 + 1 / (2 - ρ).re := by have := one_div_pos.mpr hre; linarith
  positivity

/-- For `ε > 0`, the universal source tail drift is the real part of
`n (P_{2−ρ}(n) − ζ(2 − ρ))`. -/
theorem oscillatingTailDrift_eq_re {ε : ℝ} (hε : 0 < ε) (t : ℝ) (n : ℕ) :
    oscillatingTailDrift ε t n =
      (((n : ℝ) : ℂ) * (cpowPartialSum (2 - oscillationExponent ε t) n -
        riemannZeta (2 - oscillationExponent ε t))).re := by
  set ρ := oscillationExponent ε t with hρ
  rw [oscillatingTailDrift, (hasSum_oscillatingSmoothPower_div hε t).tsum_eq,
    Complex.re_ofReal_mul, Complex.sub_re, cpowPartialSum, Complex.re_sum]
  congr 2
  refine sum_congr rfl fun d hd => ?_
  have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hdC : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  rw [oscillatingSmoothPower_eq_re hε, ← hρ, ← Complex.div_ofReal_re]
  congr 1
  rw [show -(2 - ρ) = (ρ - 1) - 1 by ring, Complex.cpow_sub (ρ - 1) 1 hdC,
    Complex.cpow_one]

/-- **Exact source asymptotic of the universal tail drift.** For `ε > 0`, `t ∈ ℝ`, and `n ≥ 1`,
`|T_{ε,t}(n) − Re(n^ρ / (ρ − 1))| ≤ tailDriftRate ρ · n^{-ε}`. -/
theorem abs_oscillatingTailDrift_sub_le {ε : ℝ} (hε : 0 < ε) (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |oscillatingTailDrift ε t n -
      (((n : ℝ) : ℂ) ^ oscillationExponent ε t / (oscillationExponent ε t - 1)).re| ≤
      tailDriftRate (oscillationExponent ε t) * (n : ℝ) ^ (-ε) := by
  set ρ := oscillationExponent ε t with hρ
  set w := 2 - ρ with hw
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnC : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hwre : w.re = 1 + ε := by
    rw [hw, sub_re, oscillationExponent_re]; norm_num; ring
  have hw0 : 0 < w.re := by linarith
  have hw1 : w ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [hwre, one_re] at this
    linarith
  have hrate := norm_czetaStripRemainder_sub_le hw0 hw1 hn
  have hcpow : ((n : ℝ) : ℂ) * (((n : ℝ) : ℂ) ^ (1 - w) / (1 - w)) =
      ((n : ℝ) : ℂ) ^ ρ / (ρ - 1) := by
    have h1w : 1 - w = ρ - 1 := by rw [hw]; ring
    have hadd : ((n : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (ρ - 1) = ((n : ℝ) : ℂ) ^ ρ := by
      rw [Complex.cpow_sub ρ 1 hnC, Complex.cpow_one, mul_div_cancel₀ _ hnC]
    rw [h1w, mul_div_assoc', hadd]
  have hid : ((n : ℝ) : ℂ) * (cpowPartialSum w n - riemannZeta w) -
      ((n : ℝ) : ℂ) ^ ρ / (ρ - 1) =
      ((n : ℝ) : ℂ) * (czetaStripRemainder w n - riemannZeta w) := by
    calc ((n : ℝ) : ℂ) * (cpowPartialSum w n - riemannZeta w) - ((n : ℝ) : ℂ) ^ ρ / (ρ - 1)
        = ((n : ℝ) : ℂ) * (cpowPartialSum w n - riemannZeta w) -
            ((n : ℝ) : ℂ) * (((n : ℝ) : ℂ) ^ (1 - w) / (1 - w)) := by rw [hcpow]
      _ = ((n : ℝ) : ℂ) *
            (cpowPartialSum w n - ((n : ℝ) : ℂ) ^ (1 - w) / (1 - w) - riemannZeta w) := by ring
      _ = ((n : ℝ) : ℂ) * (czetaStripRemainder w n - riemannZeta w) := by
            simp only [czetaStripRemainder, cpowPartialSum]
  rw [oscillatingTailDrift_eq_re hε t n, ← hρ, ← hw, ← Complex.sub_re, hid]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn0]
  have hpow : (n : ℝ) * (n : ℝ) ^ (-w.re) = (n : ℝ) ^ (-ε) := by
    rw [hwre, show (n : ℝ) * (n : ℝ) ^ (-(1 + ε)) = (n : ℝ) ^ (-(1 + ε)) * (n : ℝ) by ring,
      ← Real.rpow_add_one hn0.ne']
    congr 1; ring
  calc (n : ℝ) * ‖czetaStripRemainder w n - riemannZeta w‖
      ≤ (n : ℝ) * (‖w‖ * ((1 + 1 / w.re) * (n : ℝ) ^ (-w.re))) :=
        mul_le_mul_of_nonneg_left hrate hn0.le
    _ = tailDriftRate ρ * ((n : ℝ) * (n : ℝ) ^ (-w.re)) := by
        rw [tailDriftRate, ← hw]; ring
    _ = tailDriftRate ρ * (n : ℝ) ^ (-ε) := by rw [hpow]

/-- For `0 < ε ≤ 1` and `n ≥ 1`, the tail drift remainder is also bounded by
`tailDriftRate ρ · (√n)^{1−ε}`. -/
theorem abs_oscillatingTailDrift_sub_le_sqrt_rpow {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    |oscillatingTailDrift ε t n -
      (((n : ℝ) : ℂ) ^ oscillationExponent ε t / (oscillationExponent ε t - 1)).re| ≤
      tailDriftRate (oscillationExponent ε t) * Real.sqrt n ^ (1 - ε) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hrpow : (n : ℝ) ^ (-ε) ≤ Real.sqrt n ^ (1 - ε) := by
    calc (n : ℝ) ^ (-ε) ≤ (n : ℝ) ^ (0 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
      _ = 1 := Real.rpow_zero _
      _ ≤ Real.sqrt n ^ (1 - ε) :=
          Real.one_le_rpow (Real.one_le_sqrt.mpr hn1) (by linarith)
  have hre : 0 < (2 - oscillationExponent ε t).re := by
    rw [sub_re, oscillationExponent_re]; norm_num; linarith
  exact (abs_oscillatingTailDrift_sub_le hε t hn).trans
    (mul_le_mul_of_nonneg_left hrpow (tailDriftRate_nonneg hre))

/-- **Exact source asymptotic of the fractional-part sawtooth sum.** For `0 < ε < 1`, `t ∈ ℝ`, and
`n ≥ 1`, `S_{ε,t}(n)` tracks `Re((ζ(ρ)/ρ − 1/(ρ − 1)) n^ρ)` to within
`(floorSumRate ρ + tailDriftRate ρ) (√n)^{1−ε}`. -/
theorem abs_oscillatingSawtoothPrefix_sub_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (t : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    |oscillatingSawtoothPrefix ε t n -
      ((riemannZeta (oscillationExponent ε t) / oscillationExponent ε t -
        1 / (oscillationExponent ε t - 1)) * ((n : ℝ) : ℂ) ^ oscillationExponent ε t).re| ≤
      (floorSumRate (oscillationExponent ε t) + tailDriftRate (oscillationExponent ε t)) *
        Real.sqrt n ^ (1 - ε) := by
  set ρ := oscillationExponent ε t with hρ
  have hpre := abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le hε hε1 t hn
  have htail := abs_oscillatingTailDrift_sub_le_sqrt_rpow hε hε1.le t hn
  have hid : oscillatingSawtoothPrefix ε t n -
      ((riemannZeta ρ / ρ - 1 / (ρ - 1)) * ((n : ℝ) : ℂ) ^ ρ).re =
      (weightCenteredPrefix (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n -
        (riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ).re) -
      (oscillatingTailDrift ε t n - (((n : ℝ) : ℂ) ^ ρ / (ρ - 1)).re) := by
    rw [weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail]
    have hre : ((riemannZeta ρ / ρ - 1 / (ρ - 1)) * ((n : ℝ) : ℂ) ^ ρ).re =
        (riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ).re - (((n : ℝ) : ℂ) ^ ρ / (ρ - 1)).re := by
      rw [← Complex.sub_re]
      congr 1; ring
    rw [hre]; ring
  rw [hid]
  calc _ ≤ |weightCenteredPrefix (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n -
          (riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ).re| +
        |oscillatingTailDrift ε t n - (((n : ℝ) : ℂ) ^ ρ / (ρ - 1)).re| := abs_sub _ _
    _ ≤ floorSumRate ρ * Real.sqrt n ^ (1 - ε) + tailDriftRate ρ * Real.sqrt n ^ (1 - ε) :=
        add_le_add hpre htail
    _ = (floorSumRate ρ + tailDriftRate ρ) * Real.sqrt n ^ (1 - ε) := by ring

/-- **General necessity lemma for oscillating power modes in `L²(pronic)`.** For `0 < ε ≤ 1/2`,
`t ∈ ℝ`, and `a ∈ ℂ`, if `f : ℕ → ℝ` satisfies `|f(n) − Re(a n^{1−ε+it})| ≤ K (√n)^{1−ε}` for all
`n ≥ 1` and `pronicNorm f` is uniformly bounded, then `a = 0` (when `t = 0`, `a.re = 0`). -/
theorem eq_zero_of_bdd_pronicNorm_of_abs_sub_re_cpow_le {ε K : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (t : ℝ) {a : ℂ} {f : ℕ → ℝ} (ht0_re : t = 0 → a.re = 0 → a = 0)
    (hrem : ∀ n : ℕ, 1 ≤ n →
      |f n - (a * ((n : ℝ) : ℂ) ^ oscillationExponent ε t).re| ≤ K * Real.sqrt n ^ (1 - ε))
    (hbdd : ∃ B₀ : ℝ, ∀ T : ℕ, pronicNorm f T ≤ B₀) :
    a = 0 := by
  obtain ⟨B₀, hB₀⟩ := hbdd
  set ρ := oscillationExponent ε t with hρ
  set M : ℕ → ℝ := fun n => (a * ((n : ℝ) : ℂ) ^ ρ).re with hM
  set B := B₀ + |K| * Real.sqrt (1 + 1 / ε) with hBdef
  have hMnorm : ∀ T, pronicNorm M T ≤ B := by
    intro T
    have h1 : pronicNorm f T ≤ B₀ := hB₀ T
    have h2 : pronicNorm (fun n => f n - M n) T ≤ |K| * Real.sqrt (1 + 1 / ε) := by
      have h := sum_sq_le_of_abs_le_sqrt_rpow hε (f := fun n => f n - M n) hrem T
      rw [pronicNorm]
      calc Real.sqrt _ ≤ Real.sqrt (K ^ 2 * (1 + 1 / ε)) := Real.sqrt_le_sqrt h
        _ = |K| * Real.sqrt (1 + 1 / ε) := by
            rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq_eq_abs]
    have h3 := pronicNorm_add_le f (fun n => (-1) * (f n - M n)) T
    rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h3
    have h4 : pronicNorm M T = pronicNorm (fun n => f n + (-1) * (f n - M n)) T :=
      pronicNorm_congr fun n _ => by ring
    rw [h4, hBdef]
    linarith
  set u : ℕ → ℝ := fun n => (a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re with hu
  have hMu : ∀ n : ℕ, 1 ≤ n → M n = (n : ℝ) ^ (1 - ε) * u n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsplit : ((n : ℝ) : ℂ) ^ ρ =
        (((n : ℝ) ^ (1 - ε) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
      rw [hρ, oscillationExponent, Complex.cpow_add _ _ (by exact_mod_cast hn0.ne'),
        Complex.ofReal_cpow hn0.le]
    simp only [hM, hu]
    rw [hsplit, mul_left_comm, Complex.re_ofReal_mul]
  have hlow : ∀ T : ℕ, ∑ n ∈ Icc 1 T, u n ^ 2 / n ≤ 2 * B ^ 2 := by
    intro T
    have hMsq : ∑ n ∈ Icc 1 T, M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ B ^ 2 := by
      have h := hMnorm T
      rw [pronicNorm] at h
      have hs0 : 0 ≤ ∑ n ∈ Icc 1 T, M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
        sum_nonneg fun n _ => by positivity
      calc _ = Real.sqrt (∑ n ∈ Icc 1 T, M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) ^ 2 :=
            (Real.sq_sqrt hs0).symm
        _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    have hterm : ∀ n ∈ Icc 1 T, u n ^ 2 / n ≤ 2 * (M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hpow : (n : ℝ) ≤ ((n : ℝ) ^ (1 - ε)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ ((1 - ε) * ((2 : ℕ) : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hnR (by push_cast; linarith)
      rw [hMu n hn1, mul_pow, div_le_iff₀ hn0, mul_comm 2, mul_assoc]
      have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hpr]
      have hu2 : 0 ≤ u n ^ 2 := sq_nonneg _
      calc u n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) ≤ u n ^ 2 * (2 * (n : ℝ) * n) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hu2
        _ = ((n : ℝ) * u n ^ 2) * (2 * n) := by ring
        _ ≤ (((n : ℝ) ^ (1 - ε)) ^ 2 * u n ^ 2) * (2 * n) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hu2) (by positivity)
    calc _ ≤ ∑ n ∈ Icc 1 T, 2 * (M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := sum_le_sum hterm
      _ = 2 * ∑ n ∈ Icc 1 T, M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by rw [mul_sum]
      _ ≤ 2 * B ^ 2 := by linarith
  have husq : ∀ n : ℕ, 1 ≤ n → u n ^ 2 =
      (‖a‖ ^ 2 + (a ^ 2 * ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I)).re) / 2 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    set z := a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) with hz
    have hw : ‖((n : ℝ) : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]; simp
    have hz2 : z ^ 2 = a ^ 2 * ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) := by
      rw [hz, mul_pow, sq (((n : ℝ) : ℂ) ^ ((t : ℂ) * I)),
        ← Complex.cpow_add _ _ (by exact_mod_cast hn0.ne')]
      push_cast; ring_nf
    have hnorm : ‖z‖ ^ 2 = ‖a‖ ^ 2 := by rw [hz, norm_mul, hw, mul_one]
    have hre : ∀ x : ℂ, x.re ^ 2 = (‖x‖ ^ 2 + (x ^ 2).re) / 2 := fun x => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq x, Complex.mul_re]; ring
    show z.re ^ 2 = _
    rw [hre z, hnorm, hz2]
  have hsum : ∀ T : ℕ, ∑ n ∈ Icc 1 T, u n ^ 2 / n =
      ‖a‖ ^ 2 / 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) +
        (a ^ 2 * ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ)).re / 2 := by
    intro T
    rw [mul_sum, mul_sum, Complex.re_sum, sum_div, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn1 := (mem_Icc.mp hn).1
    have hdiv : (a ^ 2 * (((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ))).re =
        (a ^ 2 * ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I)).re / n := by
      rw [← mul_div_assoc, Complex.div_ofReal_re]
    rw [husq n hn1, hdiv]
    ring
  rcases eq_or_ne t 0 with ht0 | ht0
  · refine ht0_re ht0 ?_
    by_contra hare
    have hu0 : ∀ n : ℕ, u n = a.re := fun n => by simp [hu, ht0]
    have ha2 : 0 < a.re ^ 2 := sq_pos_of_ne_zero hare
    obtain ⟨T, -, hT⟩ := not_bddAbove_sum_Icc_one_div (2 * B ^ 2 / a.re ^ 2)
    have h := hlow T
    have heq : ∑ n ∈ Icc 1 T, u n ^ 2 / n = a.re ^ 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) := by
      rw [mul_sum]; exact sum_congr rfl fun n _ => by rw [hu0]; ring
    rw [heq] at h
    rw [div_lt_iff₀ ha2] at hT
    linarith
  · by_contra ha0
    set w : ℂ := 1 - ((2 * t : ℝ) : ℂ) * I with hw
    have hwre : 0 < w.re := by simp [hw]
    have hwne : w ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp [hw] at this
      exact ht0 this
    set B₂ := 1 / ‖((2 * t : ℝ) : ℂ) * I‖ + ‖riemannZeta w‖ + partialSumRate w with hB₂
    have hS : ∀ T : ℕ, 1 ≤ T →
        ‖∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ)‖ ≤ B₂ := by
      intro T hT
      have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
      have hcp : ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ) =
          cpowPartialSum w T := by
        rw [cpowPartialSum]
        refine sum_congr rfl fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hnC : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
        rw [hw, show -(1 - ((2 * t : ℝ) : ℂ) * I) = ((2 * t : ℝ) : ℂ) * I - 1 by ring,
          Complex.cpow_sub _ _ hnC, Complex.cpow_one]
      have h := norm_cpowPartialSum_sub_le hwre hwne hT le_rfl (by linarith)
      rw [show (1 : ℂ) - w = ((2 * t : ℝ) : ℂ) * I by rw [hw]; ring] at h
      have hT1 : ‖((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I)‖ = 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hT0]; simp
      have hTpow : (T : ℝ) ^ (-w.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT) (by linarith)
      have hrate0 := partialSumRate_nonneg hwre
      rw [hcp]
      calc ‖cpowPartialSum w T‖ ≤ ‖((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
            (((2 * t : ℝ) : ℂ) * I)‖ + ‖riemannZeta w‖ +
            ‖cpowPartialSum w T - ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
              (((2 * t : ℝ) : ℂ) * I) - riemannZeta w‖ := by
            have e : cpowPartialSum w T = ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
                (((2 * t : ℝ) : ℂ) * I) + riemannZeta w +
                (cpowPartialSum w T - ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
                  (((2 * t : ℝ) : ℂ) * I) - riemannZeta w) := by ring
            exact (congrArg norm e).le.trans
              ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
        _ ≤ 1 / ‖((2 * t : ℝ) : ℂ) * I‖ + ‖riemannZeta w‖ + partialSumRate w * 1 := by
            rw [norm_div, hT1]
            gcongr
            exact h.trans (mul_le_mul_of_nonneg_left hTpow hrate0)
        _ = B₂ := by rw [mul_one]
    have hna : 0 < ‖a‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr ha0)
    obtain ⟨T, hT1, hT⟩ := not_bddAbove_sum_Icc_one_div ((4 * B ^ 2 + ‖a‖ ^ 2 * B₂) / ‖a‖ ^ 2)
    have h := hlow T
    rw [hsum T] at h
    have hre : |(a ^ 2 * ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ)).re| ≤
        ‖a‖ ^ 2 * B₂ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hS T hT1) (by positivity)
    rw [div_lt_iff₀ hna] at hT
    have := (abs_le.mp hre).1
    nlinarith

/-- **The universal source tail drift `oscillatingTailDrift ε t` is unconditionally unbounded in
`L²(pronic)` for every `0 < ε ≤ 1/2` and every `t ∈ ℝ`.** Its leading coefficient
`1/(ρ − 1) = 1/(−ε + it)` is strictly nonzero regardless of whether `ζ(ρ) = 0`. -/
theorem not_bdd_pronicNorm_oscillatingTailDrift {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (t : ℝ) :
    ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (oscillatingTailDrift ε t) T ≤ B := by
  intro hbdd
  set ρ := oscillationExponent ε t with hρ
  have hρ1 : ρ - 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [sub_re, oscillationExponent_re, one_re, zero_re] at this
    linarith
  have ha0 : (1 : ℂ) / (ρ - 1) ≠ 0 := one_div_ne_zero hρ1
  refine ha0 (eq_zero_of_bdd_pronicNorm_of_abs_sub_re_cpow_le hε hε2 t
    (f := oscillatingTailDrift ε t) (K := tailDriftRate ρ) ?_ ?_ hbdd)
  · intro ht0 hre
    have hρ0 : ρ - 1 = ((-ε : ℝ) : ℂ) := by
      rw [hρ, oscillationExponent, ht0]
      push_cast; ring
    rw [hρ0, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re] at hre
    exfalso
    exact (div_ne_zero one_ne_zero (neg_ne_zero.mpr hε.ne')) hre
  · intro n hn
    have h := abs_oscillatingTailDrift_sub_le_sqrt_rpow hε (by linarith) t hn
    rwa [show ((n : ℝ) : ℂ) ^ ρ / (ρ - 1) = (1 / (ρ - 1)) * ((n : ℝ) : ℂ) ^ ρ by ring] at h

/-- **Anti-phase cancellation characterization of receiver boundedness.** For every `ε, t ∈ ℝ`,
`oscillatingSmoothPower ε t` has bounded receiver if and only if the fractional-part sawtooth sum
`S_{ε,t}` cancels the universal tail drift `T_{ε,t}` in `L²(pronic)`. -/
theorem receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_sawtooth_add_tail (ε t : ℝ) :
    ReceiverBounded (oscillatingSmoothPower ε t) ↔
      ∃ B : ℝ, ∀ T : ℕ,
        pronicNorm (fun n => oscillatingSawtoothPrefix ε t n + oscillatingTailDrift ε t n) T ≤ B := by
  have hcongr : ∀ T : ℕ,
      pronicNorm (weightCenteredPrefix (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d)) T =
      pronicNorm (fun n => oscillatingSawtoothPrefix ε t n + oscillatingTailDrift ε t n) T :=
    fun T => pronicNorm_congr fun n _ =>
      weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail ε t n
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨Real.sqrt E, fun T => ?_⟩
    rw [← hcongr T]
    have h := hE T
    rw [weightPronicEnergy_eq_sq_pronicNorm] at h
    have h' := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_sq (pronicNorm_nonneg _ _)] at h'
  · rintro ⟨B, hB⟩
    refine ⟨B ^ 2, fun T => ?_⟩
    rw [weightPronicEnergy_eq_sq_pronicNorm, hcongr T]
    exact pow_le_pow_left₀ (pronicNorm_nonneg _ _) (hB T) 2

/-- **Any paid sub-half oscillating probe has an unconditionally unbounded sawtooth sum locked in
anti-phase with the tail drift.** If `0 < ε ≤ 1/2` and `ReceiverBounded (oscillatingSmoothPower ε t)`,
then `S_{ε,t}` satisfies `|S_{ε,t}(n) + Re(n^ρ/(ρ − 1))| ≤ (K_ρ + K^{\mathrm{tail}}_ρ) (√n)^{1−ε}`
and has unbounded pronic norm. -/
theorem not_bdd_pronicNorm_oscillatingSawtoothPrefix_of_receiverBounded {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (t : ℝ) (hB : ReceiverBounded (oscillatingSmoothPower ε t)) :
    (∀ n : ℕ, 1 ≤ n →
      |oscillatingSawtoothPrefix ε t n +
        (((n : ℝ) : ℂ) ^ oscillationExponent ε t / (oscillationExponent ε t - 1)).re| ≤
        (floorSumRate (oscillationExponent ε t) + tailDriftRate (oscillationExponent ε t)) *
          Real.sqrt n ^ (1 - ε)) ∧
    ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (oscillatingSawtoothPrefix ε t) T ≤ B := by
  have hz := zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower hε hε2 t hB
  refine ⟨fun n hn => ?_, fun ⟨B₁, hB₁⟩ => ?_⟩
  · have h := abs_oscillatingSawtoothPrefix_sub_le hε (by linarith) t hn
    rw [hz, zero_div, zero_sub] at h
    rwa [show - (1 / (oscillationExponent ε t - 1)) * ((n : ℝ) : ℂ) ^ oscillationExponent ε t =
      -(((n : ℝ) : ℂ) ^ oscillationExponent ε t / (oscillationExponent ε t - 1)) by ring,
      Complex.neg_re, sub_neg_eq_add] at h
  · obtain ⟨B₂, hB₂⟩ :=
      (receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_sawtooth_add_tail ε t).mp hB
    refine not_bdd_pronicNorm_oscillatingTailDrift hε hε2 t ⟨B₂ + B₁, fun T => ?_⟩
    have h1 := pronicNorm_add_le
      (fun n => oscillatingSawtoothPrefix ε t n + oscillatingTailDrift ε t n)
      (fun n => (-1) * oscillatingSawtoothPrefix ε t n) T
    rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h1
    have h2 : pronicNorm (oscillatingTailDrift ε t) T =
        pronicNorm (fun n => (oscillatingSawtoothPrefix ε t n + oscillatingTailDrift ε t n) +
          (-1) * oscillatingSawtoothPrefix ε t n) T :=
      pronicNorm_congr fun n _ => by ring
    rw [h2]
    linarith [hB₂ T, hB₁ T]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
