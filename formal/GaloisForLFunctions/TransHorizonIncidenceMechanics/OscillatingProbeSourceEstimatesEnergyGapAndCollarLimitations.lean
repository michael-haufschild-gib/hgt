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

/-! ### §5. The alternate Route MC receiver: short/long sawtooth split, quantitative tail energy, and nonzero-frequency sawtooth/tail non-cancellation -/

/-- The short-modulus fractional-part sawtooth sum (`1 ≤ d ≤ ⌊√n⌋`):
`S^{\mathrm{short}}_{ε,t}(n) = Σ_{1 ≤ d ≤ ⌊√n⌋} c_{ε,t}(d) (⌊n/d⌋ − n/d)`. -/
def oscillatingShortSawtooth (ε t : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 (Nat.sqrt n), oscillatingSmoothPower ε t d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d)

/-- The long-modulus fractional-part sawtooth sum (`⌊√n⌋ < d ≤ n`):
`S^{\mathrm{long}}_{ε,t}(n) = Σ_{⌊√n⌋ < d ≤ n} c_{ε,t}(d) (⌊n/d⌋ − n/d)`. -/
def oscillatingLongSawtooth (ε t : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Ioc (Nat.sqrt n) n, oscillatingSmoothPower ε t d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d)

/-- **Hyperbola split of the sawtooth prefix into short and long moduli.** -/
theorem oscillatingSawtoothPrefix_eq_short_add_long (ε t : ℝ) (n : ℕ) :
    oscillatingSawtoothPrefix ε t n =
      oscillatingShortSawtooth ε t n + oscillatingLongSawtooth ε t n := by
  unfold oscillatingSawtoothPrefix oscillatingShortSawtooth oscillatingLongSawtooth
  have hsn : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have hsplit : Icc 1 n = Icc 1 (Nat.sqrt n) ∪ Ioc (Nat.sqrt n) n := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 (Nat.sqrt n)) (Ioc (Nat.sqrt n) n) :=
    disjoint_left.mpr fun d h1 h2 => by simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  rw [hsplit, sum_union hdisj]

/-- **The short-modulus sawtooth sum is `O((√n)^{1−ε})` unconditionally.** For `0 < ε < 1`,
`t ∈ ℝ`, and `n ≥ 1`, `|S^{\mathrm{short}}_{ε,t}(n)| ≤ (1 + 1/(1 − ε)) (√n)^{1−ε}`. -/
theorem abs_oscillatingShortSawtooth_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (t : ℝ) {n : ℕ}
    (hn : 1 ≤ n) :
    |oscillatingShortSawtooth ε t n| ≤ (1 + 1 / (1 - ε)) * Real.sqrt n ^ (1 - ε) := by
  have h1ε : 0 < 1 - ε := by linarith
  set s := Nat.sqrt n with hs
  have hs1 : 1 ≤ s := by rw [hs]; exact Nat.sqrt_pos.mpr hn
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hsr : (s : ℝ) ≤ Real.sqrt n := by rw [hs]; exact Real.nat_sqrt_le_real_sqrt
  have hr1 : (1 : ℝ) ≤ Real.sqrt n := le_trans (by exact_mod_cast hs1) hsr
  have hterm : ∀ d ∈ Icc 1 s,
      |oscillatingSmoothPower ε t d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d)| ≤ (d : ℝ) ^ (-ε) := by
    intro d hd
    have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    rw [abs_mul]
    have hc : |oscillatingSmoothPower ε t d| ≤ (d : ℝ) ^ (-ε) := by
      have h := dampedClass_one_oscillatingSmoothPower ε t d
      simpa using h
    have hfr : |((n / d : ℕ) : ℝ) - (n : ℝ) / d| ≤ 1 := abs_natDiv_sub_div_le n d hd1
    calc |oscillatingSmoothPower ε t d| * |((n / d : ℕ) : ℝ) - (n : ℝ) / d|
        ≤ (d : ℝ) ^ (-ε) * 1 :=
          mul_le_mul hc hfr (abs_nonneg _) (Real.rpow_nonneg hd0.le _)
      _ = (d : ℝ) ^ (-ε) := mul_one _
  have hhead := RHTower.sum_rpow_neg_head_le hε hε1 s
  have hsσ : (s : ℝ) ^ (1 - ε) ≤ Real.sqrt n ^ (1 - ε) :=
    Real.rpow_le_rpow hs0.le hsr h1ε.le
  have h1σ : 1 ≤ Real.sqrt n ^ (1 - ε) := Real.one_le_rpow hr1 h1ε.le
  unfold oscillatingShortSawtooth
  rw [← hs]
  calc |∑ d ∈ Icc 1 s, oscillatingSmoothPower ε t d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d)|
      ≤ ∑ d ∈ Icc 1 s, |oscillatingSmoothPower ε t d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 s, (d : ℝ) ^ (-ε) := sum_le_sum hterm
    _ ≤ 1 + (s : ℝ) ^ (1 - ε) / (1 - ε) := hhead
    _ ≤ (1 + 1 / (1 - ε)) * Real.sqrt n ^ (1 - ε) := by
        rw [add_mul, one_mul, div_eq_mul_one_div, mul_comm ((s : ℝ) ^ (1 - ε))]
        have : 1 / (1 - ε) * (s : ℝ) ^ (1 - ε) ≤ 1 / (1 - ε) * Real.sqrt n ^ (1 - ε) :=
          mul_le_mul_of_nonneg_left hsσ (by positivity)
        linarith

/-- **The short-modulus sawtooth sum has uniformly bounded pronic norm for every `0 < ε < 1` and
`t ∈ ℝ`.** Short moduli `1 ≤ d ≤ ⌊√n⌋` never contribute to sub-half divergence or to the
`T^{1−2ε}` sawtooth/tail cancellation. -/
theorem pronicNorm_oscillatingShortSawtooth_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (t : ℝ)
    (T : ℕ) :
    pronicNorm (oscillatingShortSawtooth ε t) T ≤
      (1 + 1 / (1 - ε)) * Real.sqrt (1 + 1 / ε) := by
  have h1ε : 0 ≤ 1 + 1 / (1 - ε) := by
    have : 0 < 1 - ε := by linarith
    positivity
  have h := sum_sq_le_of_abs_le_sqrt_rpow hε
    (fun n hn => abs_oscillatingShortSawtooth_le hε hε1 t hn) T
  rw [pronicNorm]
  calc Real.sqrt _ ≤ Real.sqrt ((1 + 1 / (1 - ε)) ^ 2 * (1 + 1 / ε)) := Real.sqrt_le_sqrt h
    _ = (1 + 1 / (1 - ε)) * Real.sqrt (1 + 1 / ε) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h1ε]

/-- **Receiver boundedness reduces to long-modulus sawtooth / tail cancellation.** Because
`S^{\mathrm{short}}_{ε,t}` has uniformly bounded pronic norm, `oscillatingSmoothPower ε t` is paid
if and only if `S^{\mathrm{long}}_{ε,t} + T_{ε,t}` has bounded pronic norm. -/
theorem receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_longSawtooth_add_tail {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (t : ℝ) :
    ReceiverBounded (oscillatingSmoothPower ε t) ↔
      ∃ B : ℝ, ∀ T : ℕ,
        pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ≤ B := by
  rw [receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_sawtooth_add_tail]
  set C := (1 + 1 / (1 - ε)) * Real.sqrt (1 + 1 / ε) with hC
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B + C, fun T => ?_⟩
    have h1 := pronicNorm_add_le
      (fun n => oscillatingSawtoothPrefix ε t n + oscillatingTailDrift ε t n)
      (fun n => (-1) * oscillatingShortSawtooth ε t n) T
    rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h1
    have h2 : pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T =
        pronicNorm (fun n => (oscillatingSawtoothPrefix ε t n + oscillatingTailDrift ε t n) +
          (-1) * oscillatingShortSawtooth ε t n) T :=
      pronicNorm_congr fun n _ => by
        rw [oscillatingSawtoothPrefix_eq_short_add_long]; ring
    rw [h2]
    linarith [hB T, pronicNorm_oscillatingShortSawtooth_le hε hε1 t T]
  · rintro ⟨B, hB⟩
    refine ⟨C + B, fun T => ?_⟩
    have h1 := pronicNorm_add_le
      (oscillatingShortSawtooth ε t)
      (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T
    have h2 : pronicNorm (fun n => oscillatingSawtoothPrefix ε t n + oscillatingTailDrift ε t n) T =
        pronicNorm (fun n => oscillatingShortSawtooth ε t n +
          (oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n)) T :=
      pronicNorm_congr fun n _ => by
        rw [oscillatingSawtoothPrefix_eq_short_add_long]; ring
    rw [h2]
    linarith [hB T, pronicNorm_oscillatingShortSawtooth_le hε hε1 t T]

/-- The universal amplitude `a_{\mathrm{tail}} = 1/(ρ − 1) = 1/(−ε + it)` of the tail drift. -/
def tailDriftAmp (ε t : ℝ) : ℂ := 1 / (oscillationExponent ε t - 1)

/-- The main term `M_{\mathrm{tail}}(n) = Re(n^ρ / (ρ − 1))` of the universal tail drift. -/
def tailDriftMain (ε t : ℝ) (n : ℕ) : ℝ :=
  (tailDriftAmp ε t * ((n : ℝ) : ℂ) ^ oscillationExponent ε t).re

/-- The universal asymptotic lower energy rate of `oscillatingTailDrift ε t` below half damping:
`λ^{\mathrm{tail}}_{ε,t} = (‖1/(ρ − 1)‖² / 4) (1/(1 − 2ε) − 1/‖1 − 2ε + 2it‖)`. -/
def tailEnergyLowerRate (ε t : ℝ) : ℝ :=
  ‖tailDriftAmp ε t‖ ^ 2 / 4 * (1 / (1 - 2 * ε) - 1 / ‖probeCrossExponent ε t‖)

/-- The universal asymptotic upper energy rate of `oscillatingTailDrift ε t` below half damping:
`Λ^{\mathrm{tail}}_{ε,t} = 2 ‖1/(ρ − 1)‖² / (1 − 2ε)`. -/
def tailEnergyUpperRate (ε t : ℝ) : ℝ :=
  2 * ‖tailDriftAmp ε t‖ ^ 2 / (1 - 2 * ε)

/-- The energy profile of `oscillatingTailDrift ε t` below half damping. -/
def tailEnergyProfile (ε t : ℝ) (T : ℕ) : ℝ :=
  ‖tailDriftAmp ε t‖ ^ 2 / (2 * (1 - 2 * ε)) +
    (tailDriftAmp ε t ^ 2 * ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
      probeCrossExponent ε t).re / 2

/-- The profile remainder rate for `oscillatingTailDrift ε t` below half damping. -/
def tailProfileRate (ε t : ℝ) : ℝ :=
  ‖tailDriftAmp ε t‖ ^ 2 / 2 *
    ((‖riemannZeta (1 - ((1 - 2 * ε : ℝ) : ℂ))‖ + partialSumRate (1 - ((1 - 2 * ε : ℝ) : ℂ)) +
        (1 + 1 / (1 - (1 - 2 * ε)))) +
      (‖riemannZeta (1 - probeCrossExponent ε t)‖ + partialSumRate (1 - probeCrossExponent ε t) +
        (1 + 1 / (1 - (1 - 2 * ε)))))

/-- **Unlike `probeEnergyLowerRate`, `tailEnergyLowerRate ε t > 0` unconditionally for every
`0 < ε < 1/2` and every `t ≠ 0`, with no `ζ(ρ) ≠ 0` hypothesis.** -/
theorem tailEnergyLowerRate_pos {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ} (ht : t ≠ 0) :
    0 < tailEnergyLowerRate ε t := by
  have hγ0 : 0 < 1 - 2 * ε := by linarith
  have hρ1 : oscillationExponent ε t - 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    rw [sub_re, oscillationExponent_re, one_re, zero_re] at this
    linarith
  have ha0 : 0 < ‖tailDriftAmp ε t‖ := norm_pos_iff.mpr (one_div_ne_zero hρ1)
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
  unfold tailEnergyLowerRate
  positivity

theorem tailDriftMain_sq_div (ε t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    tailDriftMain ε t n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
      ‖tailDriftAmp ε t‖ ^ 2 / 2 * ((n : ℝ) ^ (1 - 2 * ε) / ((n : ℝ) + 1)) +
        (tailDriftAmp ε t ^ 2 * (((n : ℝ) : ℂ) ^ probeCrossExponent ε t /
          (((n : ℝ) + 1 : ℝ) : ℂ))).re / 2 := by
  set a := tailDriftAmp ε t with ha
  set x : ℝ := (n : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; exact_mod_cast hn
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hsplit : (x : ℂ) ^ oscillationExponent ε t =
      ((x ^ (1 - ε) : ℝ) : ℂ) * (x : ℂ) ^ ((t : ℂ) * I) := by
    rw [oscillationExponent, Complex.cpow_add _ _ hxC, Complex.ofReal_cpow hx0.le]
  have hM : tailDriftMain ε t n = x ^ (1 - ε) * (a * (x : ℂ) ^ ((t : ℂ) * I)).re := by
    simp only [tailDriftMain, ← ha, ← hx]
    rw [hsplit, mul_left_comm, Complex.re_ofReal_mul]
  have hw : ‖(x : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp
  have hz2 : (a * (x : ℂ) ^ ((t : ℂ) * I)) ^ 2 = a ^ 2 * (x : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) := by
    rw [mul_pow, sq ((x : ℂ) ^ ((t : ℂ) * I)), ← Complex.cpow_add _ _ hxC]
    push_cast; ring_nf
  have hu2 : (a * (x : ℂ) ^ ((t : ℂ) * I)).re ^ 2 =
      (‖a‖ ^ 2 + (a ^ 2 * (x : ℂ) ^ (((2 * t : ℝ) : ℂ) * I)).re) / 2 := by
    rw [re_sq_eq_half, norm_mul, hw, mul_one, hz2]
  have hpow : (x ^ (1 - ε)) ^ 2 = x * x ^ (1 - 2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le,
      show (1 - ε) * ((2 : ℕ) : ℝ) = 1 + (1 - 2 * ε) by push_cast; ring, Real.rpow_add hx0,
      Real.rpow_one]
  have hcross : (x : ℂ) ^ probeCrossExponent ε t =
      ((x ^ (1 - 2 * ε) : ℝ) : ℂ) * (x : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) := by
    rw [probeCrossExponent, Complex.cpow_add _ _ hxC, Complex.ofReal_cpow hx0.le]
  have hre : (a ^ 2 * ((x : ℂ) ^ probeCrossExponent ε t / ((x + 1 : ℝ) : ℂ))).re =
      x ^ (1 - 2 * ε) / (x + 1) * (a ^ 2 * (x : ℂ) ^ (((2 * t : ℝ) : ℂ) * I)).re := by
    rw [hcross, ← Complex.re_ofReal_mul]
    congr 1
    push_cast
    ring
  rw [hM, mul_pow, hu2, hpow, hre]
  field_simp

theorem sq_pronicNorm_tailDriftMain (ε t : ℝ) (T : ℕ) :
    pronicNorm (tailDriftMain ε t) T ^ 2 =
      ‖tailDriftAmp ε t‖ ^ 2 / 2 * ∑ n ∈ Icc 1 T, (n : ℝ) ^ (1 - 2 * ε) / ((n : ℝ) + 1) +
        (tailDriftAmp ε t ^ 2 * ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ probeCrossExponent ε t /
          (((n : ℝ) + 1 : ℝ) : ℂ)).re / 2 := by
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity), mul_sum, mul_sum,
    Complex.re_sum, sum_div, ← sum_add_distrib]
  exact sum_congr rfl fun n hn => tailDriftMain_sq_div ε t (mem_Icc.mp hn).1

theorem abs_pronicNorm_oscillatingTailDrift_sub_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (t : ℝ)
    (T : ℕ) :
    |pronicNorm (oscillatingTailDrift ε t) T - pronicNorm (tailDriftMain ε t) T| ≤
      |tailDriftRate (oscillationExponent ε t)| * Real.sqrt (1 + 1 / ε) := by
  refine (abs_pronicNorm_sub_le _ _ T).trans ?_
  have hrem : ∀ n, 1 ≤ n →
      |oscillatingTailDrift ε t n - tailDriftMain ε t n| ≤
        tailDriftRate (oscillationExponent ε t) * Real.sqrt n ^ (1 - ε) := by
    intro n hn
    have h := abs_oscillatingTailDrift_sub_le_sqrt_rpow hε hε1 t hn
    have e : tailDriftMain ε t n =
        (((n : ℝ) : ℂ) ^ oscillationExponent ε t / (oscillationExponent ε t - 1)).re := by
      unfold tailDriftMain tailDriftAmp; congr 1; ring
    rwa [e]
  have h := sum_sq_le_of_abs_le_sqrt_rpow hε
    (f := fun n => oscillatingTailDrift ε t n - tailDriftMain ε t n) hrem T
  rw [pronicNorm]
  calc Real.sqrt _ ≤ Real.sqrt (tailDriftRate (oscillationExponent ε t) ^ 2 * (1 + 1 / ε)) :=
        Real.sqrt_le_sqrt h
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem abs_sq_pronicNorm_tailDriftMain_sub_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (t : ℝ)
    {T : ℕ} (hT : 1 ≤ T) :
    |pronicNorm (tailDriftMain ε t) T ^ 2 - (T : ℝ) ^ (1 - 2 * ε) * tailEnergyProfile ε t T| ≤
      tailProfileRate ε t := by
  set a := tailDriftAmp ε t with ha
  set β := probeCrossExponent ε t with hβ
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hβre : β.re = 1 - 2 * ε := probeCrossExponent_re ε t
  have hS0 : ∑ n ∈ Icc 1 T, (n : ℝ) ^ (1 - 2 * ε) / ((n : ℝ) + 1) =
      (∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ (((1 - 2 * ε : ℝ) : ℂ)) / (((n : ℝ) + 1 : ℝ) : ℂ)).re := by
    rw [Complex.re_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [← Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.div_ofReal_re, Complex.ofReal_re]
  have h0 := norm_sum_cpow_div_succ_sub_le (β := ((1 - 2 * ε : ℝ) : ℂ))
    (by simp; linarith) (by simp; linarith) hT
  have h1 := norm_sum_cpow_div_succ_sub_le (β := β) (by rw [hβre]; linarith)
    (by rw [hβre]; linarith) hT
  simp only [Complex.ofReal_re] at h0
  rw [hβre] at h1
  set E0 := ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ (((1 - 2 * ε : ℝ) : ℂ)) / (((n : ℝ) + 1 : ℝ) : ℂ) -
    ((T : ℝ) : ℂ) ^ (((1 - 2 * ε : ℝ) : ℂ)) / (((1 - 2 * ε : ℝ) : ℂ)) with hE0
  set E1 := ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ β / (((n : ℝ) + 1 : ℝ) : ℂ) -
    ((T : ℝ) : ℂ) ^ β / β with hE1
  have hmain0 : (((T : ℝ) : ℂ) ^ (((1 - 2 * ε : ℝ) : ℂ)) / (((1 - 2 * ε : ℝ) : ℂ))).re =
      (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) := by
    rw [← Complex.ofReal_cpow hT0.le, ← Complex.ofReal_div, Complex.ofReal_re]
  have hTβ : ((T : ℝ) : ℂ) ^ β = (((T : ℝ) ^ (1 - 2 * ε) : ℝ) : ℂ) *
      ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) := by
    rw [hβ, probeCrossExponent, Complex.cpow_add _ _ (by exact_mod_cast hT0.ne'),
      Complex.ofReal_cpow hT0.le]
  have hmain1 : (a ^ 2 * (((T : ℝ) : ℂ) ^ β / β)).re =
      (T : ℝ) ^ (1 - 2 * ε) * (a ^ 2 * ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) / β).re := by
    rw [hTβ, ← Complex.re_ofReal_mul]
    congr 1; ring
  have hid : pronicNorm (tailDriftMain ε t) T ^ 2 -
      (T : ℝ) ^ (1 - 2 * ε) * tailEnergyProfile ε t T =
      ‖a‖ ^ 2 / 2 * E0.re + (a ^ 2 * E1).re / 2 := by
    rw [sq_pronicNorm_tailDriftMain, hS0, tailEnergyProfile, ← ha, ← hβ]
    have e0 : (∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ (((1 - 2 * ε : ℝ) : ℂ)) /
        (((n : ℝ) + 1 : ℝ) : ℂ)).re = E0.re + (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) := by
      rw [hE0, sub_re, hmain0]; ring
    have e1 : (a ^ 2 * ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ β / (((n : ℝ) + 1 : ℝ) : ℂ)).re =
        (a ^ 2 * E1).re + (T : ℝ) ^ (1 - 2 * ε) *
          (a ^ 2 * ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) / β).re := by
      rw [← hmain1, ← add_re, hE1]
      congr 1; ring
    rw [e0, e1]
    have h12 : (1 - 2 * ε) ≠ 0 := by linarith
    field_simp; ring
  rw [hid]
  have hb0 : |E0.re| ≤ ‖riemannZeta (1 - ((1 - 2 * ε : ℝ) : ℂ))‖ +
      partialSumRate (1 - ((1 - 2 * ε : ℝ) : ℂ)) + (1 + 1 / (1 - (1 - 2 * ε))) :=
    (Complex.abs_re_le_norm _).trans h0
  have hb1 : |(a ^ 2 * E1).re| ≤ ‖a‖ ^ 2 * (‖riemannZeta (1 - β)‖ + partialSumRate (1 - β) +
      (1 + 1 / (1 - (1 - 2 * ε)))) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have ha2 : 0 ≤ ‖a‖ ^ 2 / 2 := by positivity
  calc |‖a‖ ^ 2 / 2 * E0.re + (a ^ 2 * E1).re / 2|
      ≤ ‖a‖ ^ 2 / 2 * |E0.re| + |(a ^ 2 * E1).re| / 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg ha2, abs_div, abs_two]
    _ ≤ tailProfileRate ε t := by
        rw [tailProfileRate, ← ha, ← hβ]
        linarith [mul_le_mul_of_nonneg_left hb0 ha2]

theorem abs_tailEnergyProfile_le {ε : ℝ} (hε2 : ε < 1 / 2) (t : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    |tailEnergyProfile ε t T| ≤ ‖tailDriftAmp ε t‖ ^ 2 / (1 - 2 * ε) := by
  set a := tailDriftAmp ε t with ha
  have hγ0 : 0 < 1 - 2 * ε := by linarith
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hnβ : 1 - 2 * ε ≤ ‖probeCrossExponent ε t‖ := by
    have := Complex.re_le_norm (probeCrossExponent ε t)
    rwa [probeCrossExponent_re] at this
  have hnT : ‖((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hT0]; simp
  have h2 : |(a ^ 2 * ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
      probeCrossExponent ε t).re| ≤ ‖a‖ ^ 2 / (1 - 2 * ε) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, norm_mul, norm_pow, hnT, mul_one]
    exact div_le_div_of_nonneg_left (by positivity) hγ0 hnβ
  unfold tailEnergyProfile
  rw [← ha]
  have h1 : 0 ≤ ‖a‖ ^ 2 / (2 * (1 - 2 * ε)) := by positivity
  calc |‖a‖ ^ 2 / (2 * (1 - 2 * ε)) + (a ^ 2 * ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
        probeCrossExponent ε t).re / 2|
      ≤ ‖a‖ ^ 2 / (2 * (1 - 2 * ε)) + ‖a‖ ^ 2 / (1 - 2 * ε) / 2 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_of_nonneg h1, abs_div, abs_two]
        linarith
    _ = ‖a‖ ^ 2 / (1 - 2 * ε) := by field_simp; ring

theorem tailEnergyProfile_ge {ε : ℝ} (_hε2 : ε < 1 / 2) (t : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    ‖tailDriftAmp ε t‖ ^ 2 / 2 * (1 / (1 - 2 * ε) - 1 / ‖probeCrossExponent ε t‖) ≤
      tailEnergyProfile ε t T := by
  set a := tailDriftAmp ε t with ha
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hnT : ‖((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hT0]; simp
  have h2 : |(a ^ 2 * ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
      probeCrossExponent ε t).re| ≤ ‖a‖ ^ 2 / ‖probeCrossExponent ε t‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, norm_mul, norm_pow, hnT, mul_one]
  unfold tailEnergyProfile
  rw [← ha]
  have h3 := (abs_le.mp h2).1
  have e1 : ‖a‖ ^ 2 / 2 * (1 / (1 - 2 * ε) - 1 / ‖probeCrossExponent ε t‖) =
      ‖a‖ ^ 2 / (2 * (1 - 2 * ε)) - ‖a‖ ^ 2 / ‖probeCrossExponent ε t‖ / 2 := by
    field_simp
  rw [e1]
  linarith

/-- **Asymptotic profile convergence for the universal tail drift below half damping.** -/
theorem tendsto_oscillatingTailDrift_energy_div_sub_profile {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) (t : ℝ) :
    Tendsto (fun T : ℕ =>
      pronicNorm (oscillatingTailDrift ε t) T ^ 2 / (T : ℝ) ^ (1 - 2 * ε) -
        tailEnergyProfile ε t T) atTop (𝓝 0) := by
  set a := tailDriftAmp ε t with ha
  set γ := 1 - 2 * ε with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  set B := |tailDriftRate (oscillationExponent ε t)| * Real.sqrt (1 + 1 / ε) with hB
  set C := tailProfileRate ε t with hC
  set Φm := ‖a‖ ^ 2 / γ with hΦm
  have hB0 : 0 ≤ B := by positivity
  have hC0 : 0 ≤ C :=
    (abs_nonneg _).trans (abs_sq_pronicNorm_tailDriftMain_sub_le hε hε2 t (T := 1) le_rfl)
  have hΦ : ∀ T : ℕ, 1 ≤ T → |tailEnergyProfile ε t T| ≤ Φm := fun T hT => by
    rw [hΦm, ha, hγ]; exact abs_tailEnergyProfile_le hε2 t hT
  have hbound : ∀ T : ℕ, 1 ≤ T →
      |pronicNorm (oscillatingTailDrift ε t) T ^ 2 / (T : ℝ) ^ γ -
        tailEnergyProfile ε t T| ≤
        (C + B * (2 * Real.sqrt C + B)) * (T : ℝ) ^ (-γ) +
          2 * B * Real.sqrt Φm * (T : ℝ) ^ (-(γ / 2)) := by
    intro T hT
    have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
    have hTγ : 0 < (T : ℝ) ^ γ := Real.rpow_pos_of_pos hT0 _
    have h1 := abs_pronicNorm_oscillatingTailDrift_sub_le hε (by linarith) t T
    have h2 := abs_sq_pronicNorm_tailDriftMain_sub_le hε hε2 t hT
    rw [← hγ, ← hC] at h2
    rw [← hB] at h1
    set x := pronicNorm (tailDriftMain ε t) T with hx
    have hx0 : 0 ≤ x := pronicNorm_nonneg _ _
    have h3 := abs_sq_sub_le_of_abs_sub_le hx0 h1 h2
    have hxle : x ≤ Real.sqrt Φm * (T : ℝ) ^ (γ / 2) + Real.sqrt C := by
      have hp : (Real.sqrt Φm * (T : ℝ) ^ (γ / 2)) ^ 2 = (T : ℝ) ^ γ * Φm := by
        rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hT0.le,
          show γ / 2 * ((2 : ℕ) : ℝ) = γ by push_cast; ring]
        ring
      have hq : Real.sqrt C ^ 2 = C := Real.sq_sqrt hC0
      have hpq : 0 ≤ Real.sqrt Φm * (T : ℝ) ^ (γ / 2) := by positivity
      have hx2 : x ^ 2 ≤ (Real.sqrt Φm * (T : ℝ) ^ (γ / 2) + Real.sqrt C) ^ 2 := by
        have h2' := (abs_le.mp h2).2
        have hΦT := (abs_le.mp (hΦ T hT)).2
        nlinarith [mul_le_mul_of_nonneg_left hΦT hTγ.le, mul_nonneg hpq (Real.sqrt_nonneg C)]
      calc x = Real.sqrt (x ^ 2) := (Real.sqrt_sq hx0).symm
        _ ≤ Real.sqrt ((Real.sqrt Φm * (T : ℝ) ^ (γ / 2) + Real.sqrt C) ^ 2) :=
          Real.sqrt_le_sqrt hx2
        _ = _ := Real.sqrt_sq (by positivity)
    rw [show pronicNorm (oscillatingTailDrift ε t) T ^ 2 / (T : ℝ) ^ γ - tailEnergyProfile ε t T =
        (pronicNorm (oscillatingTailDrift ε t) T ^ 2 -
          (T : ℝ) ^ γ * tailEnergyProfile ε t T) / (T : ℝ) ^ γ by field_simp,
      abs_div, abs_of_pos hTγ, div_le_iff₀ hTγ]
    have hTm : (T : ℝ) ^ (-γ) * (T : ℝ) ^ γ = 1 := by
      rw [← Real.rpow_add hT0]; simp
    have hTm2 : (T : ℝ) ^ (-(γ / 2)) * (T : ℝ) ^ γ = (T : ℝ) ^ (γ / 2) := by
      rw [← Real.rpow_add hT0]; ring_nf
    have hrhs : ((C + B * (2 * Real.sqrt C + B)) * (T : ℝ) ^ (-γ) +
        2 * B * Real.sqrt Φm * (T : ℝ) ^ (-(γ / 2))) * (T : ℝ) ^ γ =
        C + B * (2 * Real.sqrt C + B) + 2 * B * Real.sqrt Φm * (T : ℝ) ^ (γ / 2) := by
      rw [add_mul, mul_assoc, hTm, mul_assoc (2 * B * Real.sqrt Φm), hTm2, mul_one]
    rw [hrhs]
    calc _ ≤ C + B * (2 * x + B) := h3
      _ ≤ C + B * (2 * (Real.sqrt Φm * (T : ℝ) ^ (γ / 2) + Real.sqrt C) + B) := by gcongr
      _ = C + B * (2 * Real.sqrt C + B) + 2 * B * Real.sqrt Φm * (T : ℝ) ^ (γ / 2) := by ring
  have hlim : Tendsto (fun T : ℕ => (C + B * (2 * Real.sqrt C + B)) * (T : ℝ) ^ (-γ) +
      2 * B * Real.sqrt Φm * (T : ℝ) ^ (-(γ / 2))) atTop (𝓝 0) := by
    have t1 := (tendsto_rpow_neg_atTop hγ0).comp tendsto_natCast_atTop_atTop
    have t2 := (tendsto_rpow_neg_atTop (by linarith : 0 < γ / 2)).comp tendsto_natCast_atTop_atTop
    simpa using (t1.const_mul (C + B * (2 * Real.sqrt C + B))).add
      (t2.const_mul (2 * B * Real.sqrt Φm))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with T hT
  rw [Real.norm_eq_abs]
  exact hbound T hT

/-- **Unconditional two-sided `T^{1−2ε}` energy growth of the universal tail drift.** For every
`0 < ε < 1/2` and every `t ≠ 0` (independently of `ζ(ρ)`), eventually
`tailEnergyLowerRate ε t · T^{1−2ε} ≤ ‖T_{ε,t}‖_T² ≤ tailEnergyUpperRate ε t · T^{1−2ε}`. -/
theorem eventually_oscillatingTailDrift_energy_le_and_ge {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {t : ℝ} (ht : t ≠ 0) :
    ∀ᶠ T : ℕ in atTop,
      tailEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε) ≤
        pronicNorm (oscillatingTailDrift ε t) T ^ 2 ∧
      pronicNorm (oscillatingTailDrift ε t) T ^ 2 ≤
        tailEnergyUpperRate ε t * (T : ℝ) ^ (1 - 2 * ε) := by
  set a := tailDriftAmp ε t with ha
  set γ := 1 - 2 * ε with hγ
  have hγ0 : 0 < γ := by rw [hγ]; linarith
  have hlow0 : 0 < tailEnergyLowerRate ε t := tailEnergyLowerRate_pos hε hε2 ht
  set lam := ‖a‖ ^ 2 / 2 * (1 / γ - 1 / ‖probeCrossExponent ε t‖) with hlam
  have hlam_eq : lam = 2 * tailEnergyLowerRate ε t := by
    rw [hlam, tailEnergyLowerRate, ← ha, ← hγ]; ring
  have hlam0 : 0 < lam := by linarith
  have hlim := tendsto_oscillatingTailDrift_energy_div_sub_profile hε hε2 t
  rw [← hγ] at hlim
  have hev := (Metric.tendsto_nhds.mp hlim) (lam / 2) (by linarith)
  filter_upwards [hev, eventually_ge_atTop 1] with T hT hT1
  rw [Real.dist_eq, sub_zero] at hT
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT1
  have hTγ : 0 < (T : ℝ) ^ γ := Real.rpow_pos_of_pos hT0 _
  have hlo := tailEnergyProfile_ge hε2 t hT1
  have hhi := (abs_le.mp (abs_tailEnergyProfile_le hε2 t hT1)).2
  rw [← ha, ← hγ] at hlo hhi
  rw [← hlam] at hlo
  have hlamm : lam ≤ ‖a‖ ^ 2 / γ := by
    rw [hlam]
    have : 0 ≤ 1 / ‖probeCrossExponent ε t‖ := by positivity
    have : ‖a‖ ^ 2 / 2 * (1 / γ - 1 / ‖probeCrossExponent ε t‖) ≤ ‖a‖ ^ 2 / 2 * (1 / γ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e : ‖a‖ ^ 2 / 2 * (1 / γ) ≤ ‖a‖ ^ 2 / γ := by
      rw [div_mul_div_comm, mul_one]
      exact div_le_div_of_nonneg_left (by positivity) hγ0 (by linarith)
    linarith
  set E := pronicNorm (oscillatingTailDrift ε t) T ^ 2 with hE
  have hq := abs_lt.mp hT
  have hlow : tailEnergyLowerRate ε t ≤ E / (T : ℝ) ^ γ := by linarith [hq.1]
  have hupp : E / (T : ℝ) ^ γ ≤ tailEnergyUpperRate ε t := by
    rw [tailEnergyUpperRate, ← ha, ← hγ]
    have : 2 * ‖a‖ ^ 2 / γ = ‖a‖ ^ 2 / γ + ‖a‖ ^ 2 / γ := by ring
    linarith [hq.2]
  rw [le_div_iff₀ hTγ] at hlow
  rw [div_le_iff₀ hTγ] at hupp
  exact ⟨hlow, hupp⟩

/-- The finite-horizon pronic inner product `⟨f, g⟩_T = Σ_{1 ≤ n ≤ T} f(n) g(n) / (n(n + 1))`. -/
def pronicInner (f g : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ n ∈ Icc 1 T, f n * g n / ((n : ℝ) * ((n : ℝ) + 1))

/-- **Polarization identity for `pronicNorm` and `pronicInner`.** -/
theorem pronicNorm_add_sq_eq (f g : ℕ → ℝ) (T : ℕ) :
    pronicNorm (fun n => f n + g n) T ^ 2 =
      pronicNorm f T ^ 2 + 2 * pronicInner f g T + pronicNorm g T ^ 2 := by
  rw [pronicNorm, pronicNorm, pronicNorm, pronicInner,
    Real.sq_sqrt (sum_nonneg fun n _ => by positivity),
    Real.sq_sqrt (sum_nonneg fun n _ => by positivity),
    Real.sq_sqrt (sum_nonneg fun n _ => by positivity),
    mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  ring

/-- **Cauchy–Schwarz inequality for `pronicInner`.** -/
theorem abs_pronicInner_le_mul_pronicNorm (f g : ℕ → ℝ) (T : ℕ) :
    |pronicInner f g T| ≤ pronicNorm f T * pronicNorm g T := by
  have hupper : ∀ u v : ℕ → ℝ, pronicInner u v T ≤ pronicNorm u T * pronicNorm v T := by
    intro u v
    have htri := pronicNorm_add_le u v T
    have hsq := pow_le_pow_left₀ (pronicNorm_nonneg _ _) htri 2
    rw [pronicNorm_add_sq_eq] at hsq
    nlinarith
  rw [abs_le]
  refine ⟨?_, hupper f g⟩
  have hneg := hupper (fun n => (-1) * f n) g
  have hinner : pronicInner (fun n => (-1) * f n) g T = -pronicInner f g T := by
    unfold pronicInner
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun n _ => by ring
  rw [hinner, pronicNorm_smul, abs_neg, abs_one, one_mul] at hneg
  linarith

/-- **Exact polarization of the oscillating probe energy into sawtooth energy, sawtooth–tail
inner product, and tail energy.** -/
theorem weightPronicEnergy_oscillatingSmoothPower_eq_sawtooth_tail_polarization (ε t : ℝ)
    (T : ℕ) :
    weightPronicEnergy (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T =
      pronicNorm (oscillatingSawtoothPrefix ε t) T ^ 2 +
        2 * pronicInner (oscillatingSawtoothPrefix ε t) (oscillatingTailDrift ε t) T +
        pronicNorm (oscillatingTailDrift ε t) T ^ 2 := by
  rw [weightPronicEnergy_eq_sq_pronicNorm,
    pronicNorm_congr fun n _ =>
      weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail ε t n,
    pronicNorm_add_sq_eq]

/-- **Quantitative anti-alignment lower bound.** If at cutoff `T` the sawtooth–tail inner product
satisfies `−⟨S_{ε,t}, T_{ε,t}⟩_T ≤ θ ‖S_{ε,t}‖_T ‖T_{ε,t}‖_T`, then completing the square gives
`E_{ε,t}(T) ≥ (1 − θ²) ‖T_{ε,t}‖_T²`. -/
theorem weightPronicEnergy_ge_one_sub_sq_mul_tail_of_pronicInner_le (ε t θ : ℝ) (T : ℕ)
    (hinner : -pronicInner (oscillatingSawtoothPrefix ε t) (oscillatingTailDrift ε t) T ≤
      θ * pronicNorm (oscillatingSawtoothPrefix ε t) T *
        pronicNorm (oscillatingTailDrift ε t) T) :
    (1 - θ ^ 2) * pronicNorm (oscillatingTailDrift ε t) T ^ 2 ≤
      weightPronicEnergy (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T := by
  rw [weightPronicEnergy_oscillatingSmoothPower_eq_sawtooth_tail_polarization]
  set x := pronicNorm (oscillatingSawtoothPrefix ε t) T
  set y := pronicNorm (oscillatingTailDrift ε t) T
  have hsq : 0 ≤ (x - θ * y) ^ 2 := sq_nonneg (x - θ * y)
  nlinarith

/-- **Imperfect sawtooth/tail anti-alignment (`|θ| < 1`) forces `T^{1−2ε}` energy growth and
excludes admission.** For `0 < ε < 1/2` and `t ≠ 0`, if eventually
`−⟨S_{ε,t}, T_{ε,t}⟩_T ≤ θ ‖S_{ε,t}‖_T ‖T_{ε,t}‖_T` with `-1 < θ < 1`, then eventually
`E_{ε,t}(T) ≥ (1 − θ²) tailEnergyLowerRate ε t · T^{1−2ε}` and `oscillatingSmoothPower ε t` is
unpaid. -/
theorem not_receiverBounded_of_sawtooth_tail_inner_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {t : ℝ} (ht : t ≠ 0) {θ : ℝ} (hθ_lo : -1 < θ) (hθ_hi : θ < 1)
    (hinner : ∀ᶠ T : ℕ in atTop,
      -pronicInner (oscillatingSawtoothPrefix ε t) (oscillatingTailDrift ε t) T ≤
        θ * pronicNorm (oscillatingSawtoothPrefix ε t) T *
          pronicNorm (oscillatingTailDrift ε t) T) :
    (∀ᶠ T : ℕ in atTop,
      (1 - θ ^ 2) * tailEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε) ≤
        weightPronicEnergy (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T) ∧
    ¬ ReceiverBounded (oscillatingSmoothPower ε t) := by
  have h1θ : 0 < 1 - θ ^ 2 := by
    have hprod : 0 < (1 - θ) * (1 + θ) := mul_pos (sub_pos.mpr hθ_hi) (by linarith)
    linarith [show (1 - θ) * (1 + θ) = 1 - θ ^ 2 by ring]
  have htail_pos : 0 < tailEnergyLowerRate ε t := tailEnergyLowerRate_pos hε hε2 ht
  have hev : ∀ᶠ T : ℕ in atTop,
      (1 - θ ^ 2) * tailEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε) ≤
        weightPronicEnergy (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T := by
    filter_upwards [hinner, eventually_oscillatingTailDrift_energy_le_and_ge hε hε2 ht] with T
      hin htail
    have hcomp := weightPronicEnergy_ge_one_sub_sq_mul_tail_of_pronicInner_le ε t θ T hin
    calc (1 - θ ^ 2) * tailEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε)
        = (1 - θ ^ 2) * (tailEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε)) := by ring
      _ ≤ (1 - θ ^ 2) * pronicNorm (oscillatingTailDrift ε t) T ^ 2 :=
          mul_le_mul_of_nonneg_left htail.1 h1θ.le
      _ ≤ weightPronicEnergy (oscillatingSmoothPower ε t)
            (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T := hcomp
  refine ⟨hev, ?_⟩
  rw [not_receiverBounded_oscillatingSmoothPower_iff_eventually_energy_ge hε hε2 ht]
  exact ⟨(1 - θ ^ 2) * tailEnergyLowerRate ε t, mul_pos h1θ htail_pos, hev⟩

/-- **The alternate Route MC receiver for RH in sawtooth/tail form (`t ≠ 0` only).** Because
`t = 0` is unconditionally closed from one-sided floor/tail source estimates, the Riemann
hypothesis holds if and only if for every `0 < ε < 1/2` and every `t ≠ 0`, the sawtooth sum
`S_{ε,t}` fails to cancel the tail drift `T_{ε,t}` in `L²(pronic)`. -/
theorem riemannHypothesis_iff_forall_ne_zero_not_bdd_sawtooth_add_tail :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, t ≠ 0 →
        ¬ ∃ B : ℝ, ∀ T : ℕ,
          pronicNorm (fun n => oscillatingSawtoothPrefix ε t n + oscillatingTailDrift ε t n) T ≤
            B := by
  rw [riemannHypothesis_iff_forall_not_receiverBounded_oscillatingSmoothPower]
  constructor
  · intro hRH ε hε hε2 t _ht
    rw [← receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_sawtooth_add_tail]
    exact hRH ε hε hε2 t
  · intro h ε hε hε2 t
    rcases eq_or_ne t 0 with rfl | ht
    · exact not_receiverBounded_oscillatingSmoothPower_zero_from_source hε hε2.le
    · rw [receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_sawtooth_add_tail]
      exact h ε hε hε2 t ht

/-- **The alternate Route MC receiver for RH in long-modulus sawtooth / tail form (`t ≠ 0` only).**
Because the short-modulus sawtooth sum `1 ≤ d ≤ ⌊√n⌋` is unconditionally bounded in `L²(pronic)`
and `t = 0` is closed from floor/tail arithmetic, RH holds if and only if for every `0 < ε < 1/2`
and every `t ≠ 0`, `S^{\mathrm{long}}_{ε,t} + T_{ε,t}` has unbounded pronic norm. -/
theorem riemannHypothesis_iff_forall_ne_zero_not_bdd_longSawtooth_add_tail :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, t ≠ 0 →
        ¬ ∃ B : ℝ, ∀ T : ℕ,
          pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ≤
            B := by
  rw [riemannHypothesis_iff_forall_ne_zero_not_bdd_sawtooth_add_tail]
  constructor
  · intro hRH ε hε hε2 t ht
    rw [← receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_longSawtooth_add_tail hε
      (by linarith) t,
      receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_sawtooth_add_tail]
    exact hRH ε hε hε2 t ht
  · intro h ε hε hε2 t ht
    rw [← receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_sawtooth_add_tail,
      receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_longSawtooth_add_tail hε
        (by linarith) t]
    exact h ε hε hε2 t ht

/-- **Master theorem for the Route MC alternate oscillating-probe receiver.** Packages:
1. **Nonzero-`t` sawtooth/tail non-cancellation receiver for RH:** RH holds iff for all
   `0 < ε < 1/2` and `t ≠ 0`, `S^{\mathrm{long}}_{ε,t} + T_{ε,t}` has unbounded pronic norm;
2. **`t = 0` source exclusion closed without `ζ`:** for all `0 < ε ≤ 1/2`,
   `E_{ε,0}(T) ≥ ((2^{-(1+ε)})² / 2) Σ_{n ≤ T} 1/n` and `¬ ReceiverBounded (c_{ε,0})` directly from
   floor/tail arithmetic;
3. **Unconditional `Θ(T^{1−2ε})` tail divergence and short-sawtooth boundedness:** for all
   `0 < ε < 1/2` and `t ≠ 0`, `‖S^{\mathrm{short}}_{ε,t}‖_T ≤ (1 + 1/(1 − ε)) √(1 + 1/ε)` while
   `0 < tailEnergyLowerRate ε t` and eventually
   `tailEnergyLowerRate ε t · T^{1−2ε} ≤ ‖T_{ε,t}‖_T² ≤ tailEnergyUpperRate ε t · T^{1−2ε}`;
4. **Absence of a remaining source sign from the `ζ`-zero equivalence:** for all `0 < ε < 1/2` and
   `t ≠ 0`, `0 < probeEnergyLowerRate ε t ↔ ζ(1 − ε + it) ≠ 0`, and any paid probe has an
   unbounded sawtooth sum locked in anti-phase with `T_{ε,t}`;
5. **Collar and finiteness non-implication:** for every `(ε₁, t₁) ∈ (0, 1/2) × ℝ` and height `T`,
   the planted 3-term Euler-factor family `plantedEulerKernel ε₁ t₁ ⋆ c_{ε,t}` satisfies
   near-`ε = 0` collar exclusion and slicewise finiteness away from `ε₁`, yet is paid at
   `(ε₁, t₁)`. -/
theorem routeMC_alternate_receiver_sawtooth_tail_master :
    (RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, t ≠ 0 →
        ¬ ∃ B : ℝ, ∀ T : ℕ,
          pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ≤
            B) ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      (∀ T : ℕ,
        ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) ≤
          weightPronicEnergy (oscillatingSmoothPower ε 0)
            (∑' d : ℕ, oscillatingSmoothPower ε 0 d / d) T) ∧
      ¬ ReceiverBounded (oscillatingSmoothPower ε 0)) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, t ≠ 0 →
      (∀ T : ℕ,
        pronicNorm (oscillatingShortSawtooth ε t) T ≤
          (1 + 1 / (1 - ε)) * Real.sqrt (1 + 1 / ε)) ∧
      0 < tailEnergyLowerRate ε t ∧
      ∀ᶠ T : ℕ in atTop,
        tailEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε) ≤
          pronicNorm (oscillatingTailDrift ε t) T ^ 2 ∧
        pronicNorm (oscillatingTailDrift ε t) T ^ 2 ≤
          tailEnergyUpperRate ε t * (T : ℝ) ^ (1 - 2 * ε)) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, t ≠ 0 →
      (0 < probeEnergyLowerRate ε t ↔ riemannZeta (oscillationExponent ε t) ≠ 0) ∧
      (ReceiverBounded (oscillatingSmoothPower ε t) →
        ¬ ∃ B : ℝ, ∀ T : ℕ, pronicNorm (oscillatingSawtoothPrefix ε t) T ≤ B)) ∧
    (∀ ε₁ : ℝ, 0 < ε₁ → ε₁ < 1 / 2 → ∀ t₁ T : ℝ,
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
        (RHTower.dirichletConv (plantedEulerKernel ε₁ t₁) (oscillatingSmoothPower ε₁ t₁))) := by
  refine ⟨riemannHypothesis_iff_forall_ne_zero_not_bdd_longSawtooth_add_tail,
    fun ε hε hε2 => ⟨probeEnergy_zero_ge_harmonic hε hε2,
      not_receiverBounded_oscillatingSmoothPower_zero_from_source hε hε2⟩,
    fun ε hε hε2 t ht => ⟨pronicNorm_oscillatingShortSawtooth_le hε (by linarith) t,
      tailEnergyLowerRate_pos hε hε2 ht,
      eventually_oscillatingTailDrift_energy_le_and_ge hε hε2 ht⟩,
    fun ε hε hε2 t ht => ⟨probeEnergyLowerRate_pos_iff hε hε2 ht,
      fun hB => (not_bdd_pronicNorm_oscillatingSawtoothPrefix_of_receiverBounded hε hε2.le t hB).2⟩,
    fun ε₁ hε₁ hε₁2 t₁ T => plantedEulerKernel_collar_and_finiteness_obstruction hε₁ hε₁2 t₁ T⟩

/-! ### §6. Long-modulus sawtooth / tail pronic anti-alignment gap and why separate tail growth, finite admitted-parameter sets, and near-zero collars do not supply it -/

/-- At `t = 0`, every summand of `oscillatingLongSawtooth ε 0 n` is nonpositive because
`d^{-ε} ≥ 0` and `⌊n/d⌋ ≤ n/d`. -/
theorem oscillatingLongSawtooth_zero_nonpos (ε : ℝ) (n : ℕ) :
    oscillatingLongSawtooth ε 0 n ≤ 0 := by
  unfold oscillatingLongSawtooth
  refine sum_nonpos fun d _ => ?_
  rw [oscillatingSmoothPower_zero_eq_rpow]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    (sub_nonpos.mpr Nat.cast_div_le)

/-- **At `t = 0`, the long-modulus sawtooth sum and tail drift are aligned
(`⟨S^{\mathrm{long}}_{ε,0}, T_{ε,0}⟩_T ≥ 0`), so the strict pronic anti-alignment gap holds with
`θ = 0`.** -/
theorem pronicInner_longSawtooth_tail_zero_nonneg {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    0 ≤ pronicInner (oscillatingLongSawtooth ε 0) (oscillatingTailDrift ε 0) T := by
  unfold pronicInner
  refine sum_nonneg fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hS : oscillatingLongSawtooth ε 0 n ≤ 0 := oscillatingLongSawtooth_zero_nonpos ε n
  have hT : oscillatingTailDrift ε 0 n ≤ 0 := by
    have h1 := oscillatingTailDrift_zero_le hε hn1
    have h2 : 0 ≤ (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) := by positivity
    linarith
  exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos hS hT) (by positivity)

/-- **Harmonic lower bound for the tail pronic energy at `t = 0`.** For `0 < ε ≤ 1/2` and every
cutoff `T`, `‖T_{ε,0}‖_T² ≥ ((2^{-(1+ε)})² / 2) Σ_{n ≤ T} 1/n`. -/
theorem pronicNorm_tail_zero_sq_ge_harmonic {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (T : ℕ) :
    ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) ≤
      pronicNorm (oscillatingTailDrift ε 0) T ^ 2 := by
  set c := (2 : ℝ) ^ (-(1 + ε)) with hc
  rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity), mul_sum]
  refine sum_le_sum fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpre := oscillatingTailDrift_zero_le hε hn1
  have habs : c * (n : ℝ) ^ (1 - ε) ≤ |oscillatingTailDrift ε 0 n| := by
    calc c * (n : ℝ) ^ (1 - ε)
        ≤ -oscillatingTailDrift ε 0 n := by linarith
      _ ≤ _ := neg_le_abs _
  have hsq : (c * (n : ℝ) ^ (1 - ε)) ^ 2 ≤ oscillatingTailDrift ε 0 n ^ 2 := by
    rw [← sq_abs (oscillatingTailDrift ε 0 n)]
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
    _ ≤ oscillatingTailDrift ε 0 n ^ 2 := hsq

/-- **Harmonic lower bound for long-modulus sawtooth + tail at `t = 0`.** Because
`⟨S^{\mathrm{long}}_{ε,0}, T_{ε,0}⟩_T ≥ 0`, `‖S^{\mathrm{long}}_{ε,0} + T_{ε,0}‖_T² ≥ ‖T_{ε,0}‖_T²`
for every `T`, and `S^{\mathrm{long}}_{ε,0} + T_{ε,0}` is unconditionally unbounded in `L²(pronic)`. -/
theorem pronicNorm_longSawtooth_add_tail_zero_sq_ge_harmonic {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    (∀ T : ℕ,
      ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) ≤
        pronicNorm (fun n => oscillatingLongSawtooth ε 0 n + oscillatingTailDrift ε 0 n) T ^ 2) ∧
    ¬ ∃ B : ℝ, ∀ T : ℕ,
      pronicNorm (fun n => oscillatingLongSawtooth ε 0 n + oscillatingTailDrift ε 0 n) T ≤ B := by
  have hlo : ∀ T : ℕ,
      ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) ≤
        pronicNorm (fun n => oscillatingLongSawtooth ε 0 n + oscillatingTailDrift ε 0 n) T ^ 2 := by
    intro T
    rw [pronicNorm_add_sq_eq]
    have h1 : 0 ≤ pronicNorm (oscillatingLongSawtooth ε 0) T ^ 2 := sq_nonneg _
    have h2 : 0 ≤ pronicInner (oscillatingLongSawtooth ε 0) (oscillatingTailDrift ε 0) T :=
      pronicInner_longSawtooth_tail_zero_nonneg hε T
    have h3 := pronicNorm_tail_zero_sq_ge_harmonic hε hε2 T
    linarith
  refine ⟨hlo, ?_⟩
  rw [← receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_longSawtooth_add_tail hε
    (by linarith) 0]
  exact not_receiverBounded_oscillatingSmoothPower_zero_from_source hε hε2

/-- **Exact source asymptotic of the long-modulus sawtooth sum.** For `0 < ε < 1`, `t ∈ ℝ`, and
`n ≥ 1`, `S^{\mathrm{long}}_{ε,t}(n)` tracks `Re((ζ(ρ)/ρ − 1/(ρ − 1)) n^ρ)` to within
`(floorSumRate ρ + tailDriftRate ρ + 1 + 1/(1 − ε)) (√n)^{1−ε}`. -/
theorem abs_oscillatingLongSawtooth_sub_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (t : ℝ)
    {n : ℕ} (hn : 1 ≤ n) :
    |oscillatingLongSawtooth ε t n -
      ((riemannZeta (oscillationExponent ε t) / oscillationExponent ε t -
        1 / (oscillationExponent ε t - 1)) * ((n : ℝ) : ℂ) ^ oscillationExponent ε t).re| ≤
      (floorSumRate (oscillationExponent ε t) + tailDriftRate (oscillationExponent ε t) +
        (1 + 1 / (1 - ε))) * Real.sqrt n ^ (1 - ε) := by
  set ρ := oscillationExponent ε t with hρ
  have hsaw := abs_oscillatingSawtoothPrefix_sub_le hε hε1 t hn
  have hshort := abs_oscillatingShortSawtooth_le hε hε1 t hn
  have hid : oscillatingLongSawtooth ε t n -
      ((riemannZeta ρ / ρ - 1 / (ρ - 1)) * ((n : ℝ) : ℂ) ^ ρ).re =
      (oscillatingSawtoothPrefix ε t n -
        ((riemannZeta ρ / ρ - 1 / (ρ - 1)) * ((n : ℝ) : ℂ) ^ ρ).re) -
      oscillatingShortSawtooth ε t n := by
    rw [oscillatingSawtoothPrefix_eq_short_add_long]; ring
  rw [hid]
  calc _ ≤ |oscillatingSawtoothPrefix ε t n -
          ((riemannZeta ρ / ρ - 1 / (ρ - 1)) * ((n : ℝ) : ℂ) ^ ρ).re| +
        |oscillatingShortSawtooth ε t n| := abs_sub _ _
    _ ≤ (floorSumRate ρ + tailDriftRate ρ) * Real.sqrt n ^ (1 - ε) +
          (1 + 1 / (1 - ε)) * Real.sqrt n ^ (1 - ε) := add_le_add hsaw hshort
    _ = (floorSumRate ρ + tailDriftRate ρ + (1 + 1 / (1 - ε))) * Real.sqrt n ^ (1 - ε) := by ring

/-- **Quantitative Cauchy–Schwarz anti-alignment lower bound on long moduli.** If at cutoff `T`
`−⟨S^{\mathrm{long}}_{ε,t}, T_{ε,t}⟩_T ≤ θ ‖S^{\mathrm{long}}_{ε,t}‖_T ‖T_{ε,t}‖_T`, then
completing the square gives
`(1 − θ²) ‖T_{ε,t}‖_T² ≤ ‖S^{\mathrm{long}}_{ε,t} + T_{ε,t}‖_T²`. -/
theorem pronicNorm_longSawtooth_add_tail_sq_ge_of_pronicInner_le (ε t θ : ℝ) (T : ℕ)
    (hinner : -pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
      θ * pronicNorm (oscillatingLongSawtooth ε t) T *
        pronicNorm (oscillatingTailDrift ε t) T) :
    (1 - θ ^ 2) * pronicNorm (oscillatingTailDrift ε t) T ^ 2 ≤
      pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ^ 2 := by
  rw [pronicNorm_add_sq_eq]
  set x := pronicNorm (oscillatingLongSawtooth ε t) T
  set y := pronicNorm (oscillatingTailDrift ε t) T
  have hsq : 0 ≤ (x - θ * y) ^ 2 := sq_nonneg (x - θ * y)
  nlinarith

/-- **Quantitative quadratic anti-alignment lower bound on long moduli.** If at cutoff `T`
`−2 ⟨S^{\mathrm{long}}_{ε,t}, T_{ε,t}⟩_T ≤ θ (‖S^{\mathrm{long}}_{ε,t}‖_T² + ‖T_{ε,t}‖_T²)`, then
`(1 − θ) (‖S^{\mathrm{long}}_{ε,t}‖_T² + ‖T_{ε,t}‖_T²) ≤ ‖S^{\mathrm{long}}_{ε,t} + T_{ε,t}‖_T²`. -/
theorem pronicNorm_longSawtooth_add_tail_sq_ge_of_two_mul_pronicInner_le (ε t θ : ℝ) (T : ℕ)
    (hinner : -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
      θ * (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
        pronicNorm (oscillatingTailDrift ε t) T ^ 2)) :
    (1 - θ) * (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
      pronicNorm (oscillatingTailDrift ε t) T ^ 2) ≤
      pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ^ 2 := by
  rw [pronicNorm_add_sq_eq]
  linarith

/-- **Frequent strict Cauchy–Schwarz anti-alignment on long moduli excludes cancellation and
admission.** For `0 < ε < 1/2`, `t ≠ 0`, and `-1 < θ < 1`, if
`−⟨S^{\mathrm{long}}_{ε,t}, T_{ε,t}⟩_T ≤ θ ‖S^{\mathrm{long}}_{ε,t}‖_T ‖T_{ε,t}‖_T` holds even
frequently as `T → ∞`, then `S^{\mathrm{long}}_{ε,t} + T_{ε,t}` has unbounded pronic norm and
`oscillatingSmoothPower ε t` is unpaid. -/
theorem not_bdd_longSawtooth_add_tail_of_frequently_pronicInner_le {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) {t : ℝ} (ht : t ≠ 0) {θ : ℝ} (hθ_lo : -1 < θ) (hθ_hi : θ < 1)
    (hfreq : ∃ᶠ T : ℕ in atTop,
      -pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
        θ * pronicNorm (oscillatingLongSawtooth ε t) T *
          pronicNorm (oscillatingTailDrift ε t) T) :
    (¬ ∃ B : ℝ, ∀ T : ℕ,
      pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ≤ B) ∧
    ¬ ReceiverBounded (oscillatingSmoothPower ε t) := by
  have h1θ : 0 < 1 - θ ^ 2 := by
    have hprod : 0 < (1 - θ) * (1 + θ) := mul_pos (sub_pos.mpr hθ_hi) (by linarith)
    linarith [show (1 - θ) * (1 + θ) = 1 - θ ^ 2 by ring]
  have htail_pos : 0 < tailEnergyLowerRate ε t := tailEnergyLowerRate_pos hε hε2 ht
  set c := (1 - θ ^ 2) * tailEnergyLowerRate ε t with hc
  have hc0 : 0 < c := mul_pos h1θ htail_pos
  have hnotBdd : ¬ ∃ B : ℝ, ∀ T : ℕ,
      pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ≤ B := by
    rintro ⟨B, hB⟩
    have hrpow : Tendsto (fun T : ℕ => (T : ℝ) ^ (1 - 2 * ε)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith : 0 < 1 - 2 * ε)).comp tendsto_natCast_atTop_atTop
    have hev_big : ∀ᶠ T : ℕ in atTop, (B ^ 2 + 1) / c ≤ (T : ℝ) ^ (1 - 2 * ε) :=
      tendsto_atTop.mp hrpow ((B ^ 2 + 1) / c)
    obtain ⟨T, hin, htail, hbig⟩ :=
      (hfreq.and_eventually
        ((eventually_oscillatingTailDrift_energy_le_and_ge hε hε2 ht).and hev_big)).exists
    have hcomp := pronicNorm_longSawtooth_add_tail_sq_ge_of_pronicInner_le ε t θ T hin
    have hlow : c * (T : ℝ) ^ (1 - 2 * ε) ≤
        pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ^ 2 := by
      calc c * (T : ℝ) ^ (1 - 2 * ε)
          = (1 - θ ^ 2) * (tailEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε)) := by rw [hc]; ring
        _ ≤ (1 - θ ^ 2) * pronicNorm (oscillatingTailDrift ε t) T ^ 2 :=
            mul_le_mul_of_nonneg_left htail.1 h1θ.le
        _ ≤ _ := hcomp
    have hup : pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ^ 2 ≤
        B ^ 2 := pow_le_pow_left₀ (pronicNorm_nonneg _ _) (hB T) 2
    rw [div_le_iff₀ hc0] at hbig
    linarith
  refine ⟨hnotBdd, ?_⟩
  rwa [receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_longSawtooth_add_tail hε
    (by linarith) t]

/-- **Eventual strict Cauchy–Schwarz anti-alignment on long moduli forces `T^{1−2ε}` growth of
`‖S^{\mathrm{long}}_{ε,t} + T_{ε,t}‖_T²` and excludes admission.** -/
theorem not_receiverBounded_of_longSawtooth_tail_inner_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {t : ℝ} (ht : t ≠ 0) {θ : ℝ} (hθ_lo : -1 < θ) (hθ_hi : θ < 1)
    (hinner : ∀ᶠ T : ℕ in atTop,
      -pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
        θ * pronicNorm (oscillatingLongSawtooth ε t) T *
          pronicNorm (oscillatingTailDrift ε t) T) :
    (∀ᶠ T : ℕ in atTop,
      (1 - θ ^ 2) * tailEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε) ≤
        pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ^ 2) ∧
    (¬ ∃ B : ℝ, ∀ T : ℕ,
      pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ≤ B) ∧
    ¬ ReceiverBounded (oscillatingSmoothPower ε t) := by
  have h1θ : 0 < 1 - θ ^ 2 := by
    have hprod : 0 < (1 - θ) * (1 + θ) := mul_pos (sub_pos.mpr hθ_hi) (by linarith)
    linarith [show (1 - θ) * (1 + θ) = 1 - θ ^ 2 by ring]
  have hev : ∀ᶠ T : ℕ in atTop,
      (1 - θ ^ 2) * tailEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε) ≤
        pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ^ 2 := by
    filter_upwards [hinner, eventually_oscillatingTailDrift_energy_le_and_ge hε hε2 ht] with T
      hin htail
    have hcomp := pronicNorm_longSawtooth_add_tail_sq_ge_of_pronicInner_le ε t θ T hin
    calc (1 - θ ^ 2) * tailEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε)
        = (1 - θ ^ 2) * (tailEnergyLowerRate ε t * (T : ℝ) ^ (1 - 2 * ε)) := by ring
      _ ≤ (1 - θ ^ 2) * pronicNorm (oscillatingTailDrift ε t) T ^ 2 :=
          mul_le_mul_of_nonneg_left htail.1 h1θ.le
      _ ≤ _ := hcomp
  exact ⟨hev, not_bdd_longSawtooth_add_tail_of_frequently_pronicInner_le hε hε2 ht hθ_lo hθ_hi
    hinner.frequently⟩

/-- **General asymptotic 1:1 anti-alignment law under bounded sum and diverging tail.** If
`‖u + v‖_T ≤ B` for all `T` while `‖v‖_T → ∞`, then `‖u‖_T` is unbounded, `‖u‖_T / ‖v‖_T → 1`,
and both the quadratic anti-alignment ratio `−2⟨u, v⟩_T / (‖u‖_T² + ‖v‖_T²)` and the
Cauchy–Schwarz anti-alignment ratio `−⟨u, v⟩_T / (‖u‖_T ‖v‖_T)` converge to `1`. -/
theorem tendsto_pronicNorm_and_inner_div_of_add_bdd {u v : ℕ → ℝ} {B : ℝ}
    (hB : ∀ T : ℕ, pronicNorm (fun n => u n + v n) T ≤ B)
    (hv : Tendsto (fun T : ℕ => pronicNorm v T) atTop atTop) :
    (¬ ∃ B₁ : ℝ, ∀ T : ℕ, pronicNorm u T ≤ B₁) ∧
    Tendsto (fun T : ℕ => pronicNorm u T / pronicNorm v T) atTop (𝓝 1) ∧
    Tendsto (fun T : ℕ =>
      -2 * pronicInner u v T / (pronicNorm u T ^ 2 + pronicNorm v T ^ 2)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℕ =>
      -pronicInner u v T / (pronicNorm u T * pronicNorm v T)) atTop (𝓝 1) := by
  set B₀ := max B 0 with hB₀
  have hB₀_nonneg : 0 ≤ B₀ := le_max_right B 0
  have hB₀_bound : ∀ T : ℕ, pronicNorm (fun n => u n + v n) T ≤ B₀ :=
    fun T => (hB T).trans (le_max_left B 0)
  have hdiff : ∀ T : ℕ, |pronicNorm u T - pronicNorm v T| ≤ B₀ := by
    intro T
    have h1 : pronicNorm u T ≤ B₀ + pronicNorm v T := by
      have ht := pronicNorm_add_le (fun n => u n + v n) (fun n => (-1) * v n) T
      rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at ht
      have heq : pronicNorm u T =
          pronicNorm (fun n => (u n + v n) + (-1) * v n) T :=
        pronicNorm_congr fun n _ => by ring
      linarith [hB₀_bound T]
    have h2 : pronicNorm v T ≤ B₀ + pronicNorm u T := by
      have ht := pronicNorm_add_le (fun n => u n + v n) (fun n => (-1) * u n) T
      rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at ht
      have heq : pronicNorm v T =
          pronicNorm (fun n => (u n + v n) + (-1) * u n) T :=
        pronicNorm_congr fun n _ => by ring
      linarith [hB₀_bound T]
    rw [abs_le]
    constructor <;> linarith
  have hnotBdd : ¬ ∃ B₁ : ℝ, ∀ T : ℕ, pronicNorm u T ≤ B₁ := by
    rintro ⟨B₁, hB₁⟩
    obtain ⟨T, hT⟩ := (tendsto_atTop.mp hv (B₀ + B₁ + 1)).exists
    have h2 := (abs_le.mp (hdiff T)).1
    have huT := hB₁ T
    linarith
  have hinv : Tendsto (fun T : ℕ => (pronicNorm v T)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hv
  have hlim1 : Tendsto (fun T : ℕ => pronicNorm u T / pronicNorm v T) atTop (𝓝 1) := by
    suffices hsub : Tendsto (fun T : ℕ => pronicNorm u T / pronicNorm v T - 1) atTop (𝓝 0) by
      simpa using hsub.add_const 1
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmaj : Tendsto (fun T : ℕ => B₀ * (pronicNorm v T)⁻¹) atTop (𝓝 0) := by
      simpa using hinv.const_mul B₀
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj
    filter_upwards [tendsto_atTop.mp hv 1] with T hT
    have hv0 : 0 < pronicNorm v T := by linarith
    rw [Real.norm_eq_abs,
      show pronicNorm u T / pronicNorm v T - 1 =
        (pronicNorm u T - pronicNorm v T) / pronicNorm v T by field_simp,
      abs_div, abs_of_pos hv0, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_right (hdiff T) hv0.le
  have hmaj2 : Tendsto (fun T : ℕ => B₀ ^ 2 * (pronicNorm v T)⁻¹) atTop (𝓝 0) := by
    simpa using hinv.const_mul (B₀ ^ 2)
  have hlim2 : Tendsto (fun T : ℕ =>
      -2 * pronicInner u v T / (pronicNorm u T ^ 2 + pronicNorm v T ^ 2)) atTop (𝓝 1) := by
    suffices hsub : Tendsto (fun T : ℕ =>
        -2 * pronicInner u v T / (pronicNorm u T ^ 2 + pronicNorm v T ^ 2) - 1) atTop (𝓝 0) by
      simpa using hsub.add_const 1
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj2
    filter_upwards [tendsto_atTop.mp hv 1] with T hT
    set x := pronicNorm u T
    set y := pronicNorm v T
    set z := pronicNorm (fun n => u n + v n) T
    have hy0 : 0 < y := by linarith
    have hxy : y ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg x]
    have hxy0 : 0 < x ^ 2 + y ^ 2 := by linarith
    have hpol := pronicNorm_add_sq_eq u v T
    have hz2 : z ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ (pronicNorm_nonneg _ _) (hB₀_bound T) 2
    have heq : -2 * pronicInner u v T / (x ^ 2 + y ^ 2) - 1 = -(z ^ 2 / (x ^ 2 + y ^ 2)) := by
      rw [div_sub_one hxy0.ne', hpol]
      ring
    rw [Real.norm_eq_abs, heq, abs_neg, abs_div, abs_of_nonneg (sq_nonneg z),
      abs_of_pos hxy0, ← div_eq_mul_inv]
    calc z ^ 2 / (x ^ 2 + y ^ 2) ≤ B₀ ^ 2 / (x ^ 2 + y ^ 2) :=
          div_le_div_of_nonneg_right hz2 hxy0.le
      _ ≤ B₀ ^ 2 / y := div_le_div_of_nonneg_left (sq_nonneg B₀) hy0 hxy
  have hlim3 : Tendsto (fun T : ℕ =>
      -pronicInner u v T / (pronicNorm u T * pronicNorm v T)) atTop (𝓝 1) := by
    suffices hsub : Tendsto (fun T : ℕ =>
        -pronicInner u v T / (pronicNorm u T * pronicNorm v T) - 1) atTop (𝓝 0) by
      simpa using hsub.add_const 1
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hmaj2
    filter_upwards [tendsto_atTop.mp hv (B₀ + 1)] with T hT
    set x := pronicNorm u T
    set y := pronicNorm v T
    set z := pronicNorm (fun n => u n + v n) T
    have hy0 : 0 < y := by linarith
    have hx1 : 1 ≤ x := by
      have := (abs_le.mp (hdiff T)).1
      linarith
    have hxy : y ≤ x * y := by nlinarith
    have hxy0 : 0 < x * y := by linarith
    have hpol := pronicNorm_add_sq_eq u v T
    have hz2 : z ^ 2 ≤ B₀ ^ 2 := pow_le_pow_left₀ (pronicNorm_nonneg _ _) (hB₀_bound T) 2
    have hcs := (abs_le.mp (abs_pronicInner_le_mul_pronicNorm u v T)).1
    have hnum0 : 0 ≤ x * y + pronicInner u v T := by linarith
    have hnum_le : x * y + pronicInner u v T ≤ B₀ ^ 2 := by
      have hsq : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
      nlinarith
    have heq : -pronicInner u v T / (x * y) - 1 = -((x * y + pronicInner u v T) / (x * y)) := by
      rw [div_sub_one hxy0.ne']
      ring
    rw [Real.norm_eq_abs, heq, abs_neg, abs_div, abs_of_nonneg hnum0,
      abs_of_pos hxy0, ← div_eq_mul_inv]
    calc (x * y + pronicInner u v T) / (x * y) ≤ B₀ ^ 2 / (x * y) :=
          div_le_div_of_nonneg_right hnum_le hxy0.le
      _ ≤ B₀ ^ 2 / y := div_le_div_of_nonneg_left (sq_nonneg B₀) hy0 hxy
  exact ⟨hnotBdd, hlim1, hlim2, hlim3⟩

/-- The tail pronic norm `‖T_{ε,t}‖_T` diverges to `+∞` for every `0 < ε < 1/2` and `t ≠ 0`. -/
theorem tendsto_pronicNorm_oscillatingTailDrift_atTop {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun T : ℕ => pronicNorm (oscillatingTailDrift ε t) T) atTop atTop := by
  rw [tendsto_atTop]
  intro M
  have hc0 : 0 < tailEnergyLowerRate ε t := tailEnergyLowerRate_pos hε hε2 ht
  have hrpow : Tendsto (fun T : ℕ => (T : ℝ) ^ (1 - 2 * ε)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 1 - 2 * ε)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_oscillatingTailDrift_energy_le_and_ge hε hε2 ht,
    tendsto_atTop.mp hrpow ((max M 0) ^ 2 / tailEnergyLowerRate ε t)] with T htail hT
  rw [div_le_iff₀ hc0] at hT
  have hsq : (max M 0) ^ 2 ≤ pronicNorm (oscillatingTailDrift ε t) T ^ 2 := by
    linarith [htail.1]
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq (le_max_right M 0), Real.sqrt_sq (pronicNorm_nonneg _ _)] at hsqrt
  exact (le_max_left M 0).trans hsqrt

/-- **Why separate tail growth does not supply the long-modulus anti-alignment gap.** For every
`0 < ε < 1/2` and `t ≠ 0`, `‖T_{ε,t}‖_T → ∞` at rate `Θ(T^{1/2−ε})`, yet whenever
`oscillatingSmoothPower ε t` is paid (`ReceiverBounded`), `S^{\mathrm{long}}_{ε,t}` is unbounded
with `‖S^{\mathrm{long}}_{ε,t}‖_T / ‖T_{ε,t}‖_T → 1` and both pronic anti-alignment ratios
`−2⟨S^{\mathrm{long}}_{ε,t}, T_{ε,t}⟩_T / (‖S^{\mathrm{long}}_{ε,t}‖_T² + ‖T_{ε,t}‖_T²)` and
`−⟨S^{\mathrm{long}}_{ε,t}, T_{ε,t}⟩_T / (‖S^{\mathrm{long}}_{ε,t}‖_T ‖T_{ε,t}‖_T)` converge to
`1`. -/
theorem tendsto_longSawtooth_tail_antiAlignment_one_of_receiverBounded {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) {t : ℝ} (ht : t ≠ 0)
    (hB : ReceiverBounded (oscillatingSmoothPower ε t)) :
    (¬ ∃ B₁ : ℝ, ∀ T : ℕ, pronicNorm (oscillatingLongSawtooth ε t) T ≤ B₁) ∧
    Tendsto (fun T : ℕ =>
      pronicNorm (oscillatingLongSawtooth ε t) T /
        pronicNorm (oscillatingTailDrift ε t) T) atTop (𝓝 1) ∧
    Tendsto (fun T : ℕ =>
      -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T /
        (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
          pronicNorm (oscillatingTailDrift ε t) T ^ 2)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℕ =>
      -pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T /
        (pronicNorm (oscillatingLongSawtooth ε t) T *
          pronicNorm (oscillatingTailDrift ε t) T)) atTop (𝓝 1) := by
  obtain ⟨B, hB'⟩ :=
    (receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_longSawtooth_add_tail hε
      (by linarith) t).mp hB
  exact tendsto_pronicNorm_and_inner_div_of_add_bdd hB'
    (tendsto_pronicNorm_oscillatingTailDrift_atTop hε hε2 ht)

/-- **Exact equivalence between non-admission (`ζ(1 − ε + it) ≠ 0`) and a strict quadratic pronic
anti-alignment gap on long moduli.** For `0 < ε < 1/2` and `t ≠ 0`, `oscillatingSmoothPower ε t`
is unpaid if and only if there exists `θ < 1` such that eventually
`−2 ⟨S^{\mathrm{long}}_{ε,t}, T_{ε,t}⟩_T ≤ θ (‖S^{\mathrm{long}}_{ε,t}‖_T² + ‖T_{ε,t}‖_T²)`. -/
theorem not_receiverBounded_iff_exists_longSawtooth_tail_antiAlignment_gap {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ} (ht : t ≠ 0) :
    ¬ ReceiverBounded (oscillatingSmoothPower ε t) ↔
      ∃ θ < 1, ∀ᶠ T : ℕ in atTop,
        -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
          θ * (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
            pronicNorm (oscillatingTailDrift ε t) T ^ 2) := by
  constructor
  · intro hnotB
    have hz : riemannZeta (oscillationExponent ε t) ≠ 0 := fun hz =>
      hnotB (receiverBounded_oscillatingSmoothPower_of_zeta_eq_zero hε (by linarith) t hz)
    set c₀ := probeEnergyLowerRate ε t with hc₀
    set C₀ := probeEnergyUpperRate ε t with hC₀
    set c_tail := tailEnergyLowerRate ε t with hc_tail
    set C_tail := tailEnergyUpperRate ε t with hC_tail
    set C_short := (1 + 1 / (1 - ε)) * Real.sqrt (1 + 1 / ε) with hC_short
    have hc₀_pos : 0 < c₀ := probeEnergyLowerRate_pos hε hε2 ht hz
    have hc_tail_pos : 0 < c_tail := tailEnergyLowerRate_pos hε hε2 ht
    have hC₀_nonneg : 0 ≤ C₀ := by
      rw [hC₀, probeEnergyUpperRate]
      have : 0 < 1 - 2 * ε := by linarith
      positivity
    have hC_tail_nonneg : 0 ≤ C_tail := by
      rw [hC_tail, tailEnergyUpperRate]
      have : 0 < 1 - 2 * ε := by linarith
      positivity
    set M := 4 * C₀ + c₀ + 3 * C_tail with hM
    have hM_pos : 0 < M := by linarith
    refine ⟨1 - c₀ / (4 * M), by linarith [div_pos hc₀_pos (by linarith : 0 < 4 * M)], ?_⟩
    have hrpow : Tendsto (fun T : ℕ => (T : ℝ) ^ (1 - 2 * ε)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith : 0 < 1 - 2 * ε)).comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_probeEnergy_le_and_ge hε hε2 ht hz,
      eventually_oscillatingTailDrift_energy_le_and_ge hε hε2 ht,
      tendsto_atTop.mp hrpow (4 * C_short ^ 2 / c₀)] with T hprobe htail hT_big
    rw [div_le_iff₀ hc₀_pos] at hT_big
    set x := pronicNorm (oscillatingLongSawtooth ε t) T
    set y := pronicNorm (oscillatingTailDrift ε t) T
    set z := pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T
    set w := pronicNorm (weightCenteredPrefix (oscillatingSmoothPower ε t)
      (∑' d : ℕ, oscillatingSmoothPower ε t d / d)) T
    set s := pronicNorm (oscillatingShortSawtooth ε t) T
    have hw_sq : weightPronicEnergy (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T = w ^ 2 :=
      weightPronicEnergy_eq_sq_pronicNorm _ _ T
    have hs_le : s ≤ C_short := pronicNorm_oscillatingShortSawtooth_le hε (by linarith) t T
    have hs_sq : s ^ 2 ≤ C_short ^ 2 :=
      pow_le_pow_left₀ (pronicNorm_nonneg _ _) hs_le 2
    have hw_le_sz : w ≤ s + z := by
      have hcongr : w = pronicNorm (fun n => oscillatingShortSawtooth ε t n +
          (oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n)) T :=
        pronicNorm_congr fun n _ => by
          rw [weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail,
            oscillatingSawtoothPrefix_eq_short_add_long]; ring
      rw [hcongr]
      exact pronicNorm_add_le _ _ T
    have hz_le_ws : z ≤ w + s := by
      have ht1 := pronicNorm_add_le
        (weightCenteredPrefix (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d))
        (fun n => (-1) * oscillatingShortSawtooth ε t n) T
      rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at ht1
      have hcongr : z = pronicNorm (fun n =>
          weightCenteredPrefix (oscillatingSmoothPower ε t)
            (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n +
          (-1) * oscillatingShortSawtooth ε t n) T :=
        pronicNorm_congr fun n _ => by
          rw [weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail,
            oscillatingSawtoothPrefix_eq_short_add_long]; ring
      rwa [hcongr]
    have hx_le_zy : x ≤ z + y := by
      have ht1 := pronicNorm_add_le
        (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n)
        (fun n => (-1) * oscillatingTailDrift ε t n) T
      rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at ht1
      have hcongr : x = pronicNorm (fun n =>
          (oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) +
          (-1) * oscillatingTailDrift ε t n) T :=
        pronicNorm_congr fun n _ => by ring
      rwa [hcongr]
    have hw2_le : w ^ 2 ≤ 2 * s ^ 2 + 2 * z ^ 2 := by
      have h1 : w ^ 2 ≤ (s + z) ^ 2 := pow_le_pow_left₀ (pronicNorm_nonneg _ _) hw_le_sz 2
      nlinarith [sq_nonneg (s - z)]
    have hz2_le : z ^ 2 ≤ 2 * w ^ 2 + 2 * s ^ 2 := by
      have h1 : z ^ 2 ≤ (w + s) ^ 2 := pow_le_pow_left₀ (pronicNorm_nonneg _ _) hz_le_ws 2
      nlinarith [sq_nonneg (w - s)]
    have hx2_le : x ^ 2 ≤ 2 * z ^ 2 + 2 * y ^ 2 := by
      have h1 : x ^ 2 ≤ (z + y) ^ 2 := pow_le_pow_left₀ (pronicNorm_nonneg _ _) hx_le_zy 2
      nlinarith [sq_nonneg (z - y)]
    have hw_lo : c₀ * (T : ℝ) ^ (1 - 2 * ε) ≤ w ^ 2 := by
      rw [← hw_sq]; exact hprobe.1
    have hw_hi : w ^ 2 ≤ C₀ * (T : ℝ) ^ (1 - 2 * ε) := by
      rw [← hw_sq]; exact hprobe.2
    have hz_lo : c₀ / 4 * (T : ℝ) ^ (1 - 2 * ε) ≤ z ^ 2 := by linarith
    have hxy_hi : x ^ 2 + y ^ 2 ≤ M * (T : ℝ) ^ (1 - 2 * ε) := by
      rw [hM]; linarith [htail.2]
    have hratio : c₀ / (4 * M) * (x ^ 2 + y ^ 2) ≤ z ^ 2 := by
      have h1 : c₀ / (4 * M) * (x ^ 2 + y ^ 2) ≤ c₀ / (4 * M) * (M * (T : ℝ) ^ (1 - 2 * ε)) :=
        mul_le_mul_of_nonneg_left hxy_hi (by positivity)
      have h2 : c₀ / (4 * M) * (M * (T : ℝ) ^ (1 - 2 * ε)) = c₀ / 4 * (T : ℝ) ^ (1 - 2 * ε) := by
        field_simp [hM_pos.ne']
      linarith
    have hpol : z ^ 2 = x ^ 2 + 2 * pronicInner (oscillatingLongSawtooth ε t)
        (oscillatingTailDrift ε t) T + y ^ 2 := pronicNorm_add_sq_eq _ _ T
    linarith
  · rintro ⟨θ, hθ, hev⟩ hB
    have hlim := (tendsto_longSawtooth_tail_antiAlignment_one_of_receiverBounded hε hε2 ht hB).2.2.1
    have htail_top := tendsto_pronicNorm_oscillatingTailDrift_atTop hε hε2 ht
    have hev_lim := (Metric.tendsto_nhds.mp hlim) ((1 - θ) / 2) (by linarith)
    obtain ⟨T, ⟨hin, hclose⟩, hT1⟩ :=
      ((hev.and hev_lim).and (tendsto_atTop.mp htail_top 1)).exists
    rw [Real.dist_eq, abs_lt] at hclose
    set D := pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
      pronicNorm (oscillatingTailDrift ε t) T ^ 2
    have hD0 : 0 < D := by
      have : 0 ≤ pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 := sq_nonneg _
      nlinarith
    have hdiv : -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T / D ≤ θ :=
      (div_le_iff₀ hD0).mpr hin
    linarith [hclose.1]

/-- **The Riemann hypothesis is equivalent to a strict quadratic pronic anti-alignment gap between
the long-modulus sawtooth sum and the tail drift for every `0 < ε < 1/2` and `t ≠ 0`.** -/
theorem riemannHypothesis_iff_forall_ne_zero_exists_longSawtooth_tail_antiAlignment_gap :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, t ≠ 0 →
        ∃ θ < 1, ∀ᶠ T : ℕ in atTop,
          -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
            θ * (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
              pronicNorm (oscillatingTailDrift ε t) T ^ 2) := by
  rw [riemannHypothesis_iff_forall_ne_zero_not_bdd_longSawtooth_add_tail]
  constructor
  · intro hRH ε hε hε2 t ht
    rw [← not_receiverBounded_iff_exists_longSawtooth_tail_antiAlignment_gap hε hε2 ht,
      receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_longSawtooth_add_tail hε
        (by linarith) t]
    exact hRH ε hε hε2 t ht
  · intro h ε hε hε2 t ht
    rw [← receiverBounded_oscillatingSmoothPower_iff_bdd_pronicNorm_longSawtooth_add_tail hε
      (by linarith) t,
      not_receiverBounded_iff_exists_longSawtooth_tail_antiAlignment_gap hε hε2 ht]
    exact h ε hε hε2 t ht

/-- **On the Vinogradov–Korobov near-zero collar, the strict quadratic pronic anti-alignment gap on
long moduli holds unconditionally.** -/
theorem exists_longSawtooth_tail_antiAlignment_gap_vk :
    ∃ T₀ : ℝ, Real.exp (Real.exp 1) ≤ T₀ ∧ ∀ ε t : ℝ, T₀ ≤ |t| → 0 < ε →
      ε < min (1 / 2) (RHTower.vkHadamardWidth |t|) →
      ∃ θ < 1, ∀ᶠ T : ℕ in atTop,
        -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
          θ * (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
            pronicNorm (oscillatingTailDrift ε t) T ^ 2) := by
  obtain ⟨T₀, hT₀, hvk⟩ := exists_not_receiverBounded_oscillatingSmoothPower_vk
  refine ⟨T₀, hT₀, fun ε t ht hε hεw => ?_⟩
  have hε2 : ε < 1 / 2 := hεw.trans_le (min_le_left _ _)
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at ht
    linarith [Real.exp_pos (Real.exp 1)]
  exact (not_receiverBounded_iff_exists_longSawtooth_tail_antiAlignment_gap hε hε2 ht0).mp
    (hvk ε t ht hε hεw)

/-- **Master theorem for long-modulus sawtooth / tail non-cancellation and the pronic
anti-alignment gap.** Packages:
1. **Short moduli and `t = 0` are paid:** for all `0 < ε < 1` and `t ∈ ℝ`,
   `‖S^{\mathrm{short}}_{ε,t}‖_T ≤ (1 + 1/(1 − ε)) √(1 + 1/ε)`; for all `0 < ε ≤ 1/2`,
   `⟨S^{\mathrm{long}}_{ε,0}, T_{ε,0}⟩_T ≥ 0` (anti-alignment gap with `θ = 0`),
   `‖S^{\mathrm{long}}_{ε,0} + T_{ε,0}‖_T² ≥ ((2^{-(1+ε)})² / 2) Σ_{n ≤ T} 1/n`, and
   `¬ ReceiverBounded (c_{ε,0})`;
2. **Sufficiency of a frequent Cauchy–Schwarz anti-alignment gap on long moduli:** for any
   `0 < ε < 1/2`, `t ≠ 0`, and `-1 < θ < 1`, if frequently
   `−⟨S^{\mathrm{long}}_{ε,t}, T_{ε,t}⟩_T ≤ θ ‖S^{\mathrm{long}}_{ε,t}‖_T ‖T_{ε,t}‖_T`, then
   `S^{\mathrm{long}}_{ε,t} + T_{ε,t}` is unbounded in `L²(pronic)` and `c_{ε,t}` is unpaid;
3. **Exact equivalence of the quadratic pronic anti-alignment gap on long moduli with non-admission
   and RH:** RH holds iff for all `0 < ε < 1/2` and `t ≠ 0`, there exists `θ < 1` such that
   eventually `−2⟨S^{\mathrm{long}}_{ε,t}, T_{ε,t}⟩_T ≤ θ (‖S^{\mathrm{long}}_{ε,t}‖_T² + ‖T_{ε,t}‖_T²)`;
4. **Separate tail growth does not supply the anti-alignment gap:** for all `0 < ε < 1/2` and
   `t ≠ 0`, `0 < tailEnergyLowerRate ε t` and `‖T_{ε,t}‖_T → ∞`, yet whenever `c_{ε,t}` is paid,
   `‖S^{\mathrm{long}}_{ε,t}‖_T / ‖T_{ε,t}‖_T → 1` and both anti-alignment ratios converge to `1`;
5. **Finite admitted-parameter sets and near-zero collars do not supply the anti-alignment gap
   across `0 < ε < 1/2`:** for every `(ε₁, t₁) ∈ (0, 1/2) × ℝ` and height `T`, the planted 3-term
   Euler-factor family `plantedEulerKernel ε₁ t₁ ⋆ c_{ε,t}` satisfies near-`ε = 0` collar exclusion
   and slicewise finiteness away from `ε₁`, yet is paid at `(ε₁, t₁)`. -/
theorem routeMC_longSawtooth_tail_antiAlignment_master :
    ((∀ ε : ℝ, 0 < ε → ε < 1 → ∀ t : ℝ, ∀ T : ℕ,
        pronicNorm (oscillatingShortSawtooth ε t) T ≤
          (1 + 1 / (1 - ε)) * Real.sqrt (1 + 1 / ε)) ∧
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        (∀ T : ℕ, 0 ≤ pronicInner (oscillatingLongSawtooth ε 0) (oscillatingTailDrift ε 0) T) ∧
        (∀ T : ℕ,
          ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) ≤
            pronicNorm (fun n => oscillatingLongSawtooth ε 0 n + oscillatingTailDrift ε 0 n) T ^ 2) ∧
        ¬ ReceiverBounded (oscillatingSmoothPower ε 0))) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, t ≠ 0 → ∀ θ : ℝ, -1 < θ → θ < 1 →
      (∃ᶠ T : ℕ in atTop,
        -pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
          θ * pronicNorm (oscillatingLongSawtooth ε t) T *
            pronicNorm (oscillatingTailDrift ε t) T) →
      (¬ ∃ B : ℝ, ∀ T : ℕ,
        pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ≤ B) ∧
      ¬ ReceiverBounded (oscillatingSmoothPower ε t)) ∧
    (RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, t ≠ 0 →
        ∃ θ < 1, ∀ᶠ T : ℕ in atTop,
          -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
            θ * (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
              pronicNorm (oscillatingTailDrift ε t) T ^ 2)) ∧
    (∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, t ≠ 0 →
      0 < tailEnergyLowerRate ε t ∧
      Tendsto (fun T : ℕ => pronicNorm (oscillatingTailDrift ε t) T) atTop atTop ∧
      (ReceiverBounded (oscillatingSmoothPower ε t) →
        Tendsto (fun T : ℕ =>
          pronicNorm (oscillatingLongSawtooth ε t) T /
            pronicNorm (oscillatingTailDrift ε t) T) atTop (𝓝 1) ∧
        Tendsto (fun T : ℕ =>
          -pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T /
            (pronicNorm (oscillatingLongSawtooth ε t) T *
              pronicNorm (oscillatingTailDrift ε t) T)) atTop (𝓝 1))) ∧
    (∀ ε₁ : ℝ, 0 < ε₁ → ε₁ < 1 / 2 → ∀ t₁ T : ℝ,
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
        (RHTower.dirichletConv (plantedEulerKernel ε₁ t₁) (oscillatingSmoothPower ε₁ t₁))) := by
  refine ⟨⟨fun ε hε hε1 t T => pronicNorm_oscillatingShortSawtooth_le hε hε1 t T,
      fun ε hε hε2 => ⟨pronicInner_longSawtooth_tail_zero_nonneg hε,
        (pronicNorm_longSawtooth_add_tail_zero_sq_ge_harmonic hε hε2).1,
        not_receiverBounded_oscillatingSmoothPower_zero_from_source hε hε2⟩⟩,
    fun ε hε hε2 t ht θ hθ_lo hθ_hi hfreq =>
      not_bdd_longSawtooth_add_tail_of_frequently_pronicInner_le hε hε2 ht hθ_lo hθ_hi hfreq,
    riemannHypothesis_iff_forall_ne_zero_exists_longSawtooth_tail_antiAlignment_gap,
    fun ε hε hε2 t ht => ⟨tailEnergyLowerRate_pos hε hε2 ht,
      tendsto_pronicNorm_oscillatingTailDrift_atTop hε hε2 ht,
      fun hB => ⟨(tendsto_longSawtooth_tail_antiAlignment_one_of_receiverBounded hε hε2 ht hB).2.1,
        (tendsto_longSawtooth_tail_antiAlignment_one_of_receiverBounded hε hε2 ht hB).2.2.2⟩⟩,
    fun ε₁ hε₁ hε₁2 t₁ T => plantedEulerKernel_collar_and_finiteness_obstruction hε₁ hε₁2 t₁ T⟩

/-! ### §7. Source-derived amplitude mismatch vs. phase decorrelation, explicit quadratic gap coefficient `θ(ε, t)`, and collar vs. interior status -/

/-- **Exact decomposition of `‖u + v‖_T²` into nonnegative amplitude-mismatch and
phase-decorrelation defects.** For every `u, v : ℕ → ℝ` and `T ∈ ℕ`:
`‖u + v‖_T² = (‖u‖_T − ‖v‖_T)² + 2 (‖u‖_T ‖v‖_T + ⟨u, v⟩_T)`, where both summands are `≥ 0`. -/
theorem pronicNorm_add_sq_eq_amp_mismatch_add_decorrelation (u v : ℕ → ℝ) (T : ℕ) :
    pronicNorm (fun n => u n + v n) T ^ 2 =
      (pronicNorm u T - pronicNorm v T) ^ 2 +
        2 * (pronicNorm u T * pronicNorm v T + pronicInner u v T) ∧
    0 ≤ (pronicNorm u T - pronicNorm v T) ^ 2 ∧
    0 ≤ 2 * (pronicNorm u T * pronicNorm v T + pronicInner u v T) := by
  have hpol := pronicNorm_add_sq_eq u v T
  have hcs := (abs_le.mp (abs_pronicInner_le_mul_pronicNorm u v T)).1
  refine ⟨by linarith, sq_nonneg _, by linarith⟩

/-- **Source-derived pronic amplitude mismatch implies a strict quadratic anti-alignment gap
`θ = 1 − δ²/6 < 1` independently of phase correlation.** If `0 < δ ≤ 1` and
`δ ‖v‖_T ≤ |‖u‖_T − ‖v‖_T|`, then
`(δ² / 6) (‖u‖_T² + ‖v‖_T²) ≤ (‖u‖_T − ‖v‖_T)² ≤ ‖u + v‖_T²` and
`−2 ⟨u, v⟩_T ≤ (1 − δ² / 6) (‖u‖_T² + ‖v‖_T²)`. -/
theorem two_mul_neg_pronicInner_le_of_abs_pronicNorm_sub_ge (u v : ℕ → ℝ) (T : ℕ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hmis : δ * pronicNorm v T ≤ |pronicNorm u T - pronicNorm v T|) :
    δ ^ 2 / 6 * (pronicNorm u T ^ 2 + pronicNorm v T ^ 2) ≤
      (pronicNorm u T - pronicNorm v T) ^ 2 ∧
    (pronicNorm u T - pronicNorm v T) ^ 2 ≤ pronicNorm (fun n => u n + v n) T ^ 2 ∧
    -2 * pronicInner u v T ≤
      (1 - δ ^ 2 / 6) * (pronicNorm u T ^ 2 + pronicNorm v T ^ 2) ∧
    1 - δ ^ 2 / 6 < 1 := by
  set x := pronicNorm u T
  set y := pronicNorm v T
  have hy0 : 0 ≤ y := pronicNorm_nonneg v T
  have hsq_mis : (δ * y) ^ 2 ≤ (x - y) ^ 2 := by
    rw [← sq_abs (x - y)]
    exact pow_le_pow_left₀ (mul_nonneg hδ0.le hy0) hmis 2
  have hδ2_le : δ ^ 2 ≤ 1 := by nlinarith
  have hδ2_pos : 0 < δ ^ 2 := sq_pos_of_pos hδ0
  have h1 : δ ^ 2 / 6 * (x ^ 2 + y ^ 2) ≤ (x - y) ^ 2 := by
    have hid : 6 * (x - y) ^ 2 - δ ^ 2 * (x ^ 2 + y ^ 2) =
        2 * (1 - δ ^ 2) * (x - y) ^ 2 + 4 * ((x - y) ^ 2 - (δ * y) ^ 2) +
          δ ^ 2 * ((x - 2 * y) ^ 2 + y ^ 2) := by ring
    have hnonneg : 0 ≤ 6 * (x - y) ^ 2 - δ ^ 2 * (x ^ 2 + y ^ 2) := by
      rw [hid]
      have t1 : 0 ≤ 2 * (1 - δ ^ 2) * (x - y) ^ 2 :=
        mul_nonneg (by linarith) (sq_nonneg (x - y))
      have t2 : 0 ≤ 4 * ((x - y) ^ 2 - (δ * y) ^ 2) := by linarith
      have t3 : 0 ≤ δ ^ 2 * ((x - 2 * y) ^ 2 + y ^ 2) :=
        mul_nonneg hδ2_pos.le (add_nonneg (sq_nonneg (x - 2 * y)) (sq_nonneg y))
      linarith
    linarith
  have hdecomp := pronicNorm_add_sq_eq_amp_mismatch_add_decorrelation u v T
  have hpol := pronicNorm_add_sq_eq u v T
  refine ⟨h1, by linarith [hdecomp.1, hdecomp.2.2], ?_, by linarith⟩
  linarith [hdecomp.1, hdecomp.2.2]

/-- **Source-derived pronic phase decorrelation implies a strict quadratic anti-alignment gap
`θ = 1 − δ < 1` independently of amplitude balance.** If `0 < δ ≤ 1` and
`−⟨u, v⟩_T ≤ (1 − δ) ‖u‖_T ‖v‖_T`, then
`δ (‖u‖_T² + ‖v‖_T²) ≤ ‖u + v‖_T²` and
`−2 ⟨u, v⟩_T ≤ (1 − δ) (‖u‖_T² + ‖v‖_T²)`. -/
theorem two_mul_neg_pronicInner_le_of_phase_decorrelation (u v : ℕ → ℝ) (T : ℕ) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hdec : -pronicInner u v T ≤ (1 - δ) * pronicNorm u T * pronicNorm v T) :
    δ * (pronicNorm u T ^ 2 + pronicNorm v T ^ 2) ≤
      pronicNorm (fun n => u n + v n) T ^ 2 ∧
    -2 * pronicInner u v T ≤
      (1 - δ) * (pronicNorm u T ^ 2 + pronicNorm v T ^ 2) ∧
    1 - δ < 1 := by
  set x := pronicNorm u T
  set y := pronicNorm v T
  have hpol := pronicNorm_add_sq_eq u v T
  have h1 : δ * (x ^ 2 + y ^ 2) ≤ pronicNorm (fun n => u n + v n) T ^ 2 := by
    rw [hpol]
    have hsq : 0 ≤ (1 - δ) * (x - y) ^ 2 := mul_nonneg (by linarith) (sq_nonneg (x - y))
    nlinarith
  refine ⟨h1, by linarith, by linarith⟩

/-- **Either source-derived amplitude mismatch or source-derived phase decorrelation on long moduli
yields the explicit quadratic gap `θ = 1 − δ²/6 < 1` and excludes cancellation.** For
`0 < ε < 1/2`, `t ≠ 0`, and `0 < δ ≤ 1`, if eventually at cutoff `T` either
`δ ‖T_{ε,t}‖_T ≤ |‖S^{\mathrm{long}}_{ε,t}‖_T − ‖T_{ε,t}‖_T|` or
`−⟨S^{\mathrm{long}}_{ε,t}, T_{ε,t}⟩_T ≤ (1 − δ) ‖S^{\mathrm{long}}_{ε,t}‖_T ‖T_{ε,t}‖_T`, then
eventually `−2⟨S^{\mathrm{long}}_{ε,t}, T_{ε,t}⟩_T ≤ (1 − δ²/6) (‖S^{\mathrm{long}}_{ε,t}‖_T² + ‖T_{ε,t}‖_T²)`
and `oscillatingSmoothPower ε t` is unpaid. -/
theorem not_receiverBounded_of_longSawtooth_tail_amp_mismatch_or_decorrelation {ε : ℝ}
    (hε : 0 < ε) (hε2 : ε < 1 / 2) {t : ℝ} (ht : t ≠ 0) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsrc : ∀ᶠ T : ℕ in atTop,
      δ * pronicNorm (oscillatingTailDrift ε t) T ≤
        |pronicNorm (oscillatingLongSawtooth ε t) T -
          pronicNorm (oscillatingTailDrift ε t) T| ∨
      -pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
        (1 - δ) * pronicNorm (oscillatingLongSawtooth ε t) T *
          pronicNorm (oscillatingTailDrift ε t) T) :
    (∀ᶠ T : ℕ in atTop,
      -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
        (1 - δ ^ 2 / 6) * (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
          pronicNorm (oscillatingTailDrift ε t) T ^ 2)) ∧
    ¬ ReceiverBounded (oscillatingSmoothPower ε t) := by
  have hδ2_le : δ ^ 2 / 6 ≤ δ := by nlinarith
  have hev : ∀ᶠ T : ℕ in atTop,
      -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
        (1 - δ ^ 2 / 6) * (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
          pronicNorm (oscillatingTailDrift ε t) T ^ 2) := by
    filter_upwards [hsrc] with T hT
    rcases hT with hmis | hdec
    · exact (two_mul_neg_pronicInner_le_of_abs_pronicNorm_sub_ge
        (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T hδ0 hδ1 hmis).2.2.1
    · have h := (two_mul_neg_pronicInner_le_of_phase_decorrelation
        (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T hδ0 hδ1 hdec).2.1
      have hsum0 : 0 ≤ pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
          pronicNorm (oscillatingTailDrift ε t) T ^ 2 := by positivity
      calc -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T
          ≤ (1 - δ) * (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
              pronicNorm (oscillatingTailDrift ε t) T ^ 2) := h
        _ ≤ (1 - δ ^ 2 / 6) * (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
              pronicNorm (oscillatingTailDrift ε t) T ^ 2) :=
            mul_le_mul_of_nonneg_right (by linarith) hsum0
  refine ⟨hev, ?_⟩
  rw [not_receiverBounded_iff_exists_longSawtooth_tail_antiAlignment_gap hε hε2 ht]
  exact ⟨1 - δ ^ 2 / 6, by nlinarith [sq_pos_of_pos hδ0], hev⟩

/-- The complex harmonic amplitude of `oscillatingLongSawtooth ε t`:
`a_{\mathrm{long}}(ε, t) = ζ(ρ)/ρ − 1/(ρ − 1)`. -/
def longSawtoothAmp (ε t : ℝ) : ℂ :=
  riemannZeta (oscillationExponent ε t) / oscillationExponent ε t -
    1 / (oscillationExponent ε t - 1)

/-- **Harmonic decomposition of `‖ζ(ρ)/ρ‖²` into long-sawtooth/tail amplitude mismatch and phase
decorrelation.** For every `ε, t ∈ ℝ`:
`‖ζ(ρ)/ρ‖² = (‖a_{\mathrm{long}}‖ − ‖a_{\mathrm{tail}}‖)² + 2(‖a_{\mathrm{long}}‖ ‖a_{\mathrm{tail}}‖ + Re(a_{\mathrm{long}} \overline{a_{\mathrm{tail}}}))`,
with both summands nonnegative. -/
theorem norm_sq_longSawtoothAmp_add_tailDriftAmp_eq (ε t : ℝ) :
    longSawtoothAmp ε t + tailDriftAmp ε t =
      riemannZeta (oscillationExponent ε t) / oscillationExponent ε t ∧
    ‖riemannZeta (oscillationExponent ε t) / oscillationExponent ε t‖ ^ 2 =
      (‖longSawtoothAmp ε t‖ - ‖tailDriftAmp ε t‖) ^ 2 +
        2 * (‖longSawtoothAmp ε t‖ * ‖tailDriftAmp ε t‖ +
          (longSawtoothAmp ε t * starRingEnd ℂ (tailDriftAmp ε t)).re) ∧
    0 ≤ (‖longSawtoothAmp ε t‖ - ‖tailDriftAmp ε t‖) ^ 2 ∧
    0 ≤ ‖longSawtoothAmp ε t‖ * ‖tailDriftAmp ε t‖ +
      (longSawtoothAmp ε t * starRingEnd ℂ (tailDriftAmp ε t)).re := by
  set z := longSawtoothAmp ε t
  set w := tailDriftAmp ε t
  have hsum : z + w = riemannZeta (oscillationExponent ε t) / oscillationExponent ε t := by
    simp only [z, w, longSawtoothAmp, tailDriftAmp]; ring
  have hpol : ‖z + w‖ ^ 2 = ‖z‖ ^ 2 + ‖w‖ ^ 2 + 2 * (z * starRingEnd ℂ w).re := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  have hcs : |(z * starRingEnd ℂ w).re| ≤ ‖z‖ * ‖w‖ := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, RCLike.norm_conj]
  refine ⟨hsum, ?_, sq_nonneg _, by linarith [(abs_le.mp hcs).1]⟩
  rw [← hsum, hpol]
  ring

/-- The explicit long-sawtooth/tail quadratic gap coefficient `θ(ε, t)` for `0 < ε < 1/2`:
`θ_{\mathrm{long}}(ε, t) = 1 − probeEnergyLowerRate ε t / (4 (4 probeEnergyUpperRate ε t + probeEnergyLowerRate ε t + 3 tailEnergyUpperRate ε t))`. -/
def longSawtoothTailGapTheta (ε t : ℝ) : ℝ :=
  1 - probeEnergyLowerRate ε t /
    (4 * (4 * probeEnergyUpperRate ε t + probeEnergyLowerRate ε t +
      3 * tailEnergyUpperRate ε t))

/-- **Unconditional eventual long-sawtooth/tail quadratic bound with explicit coefficient
`longSawtoothTailGapTheta ε t`, and exact characterization of `longSawtoothTailGapTheta ε t < 1`
via harmonic amplitude mismatch or phase decorrelation.** For every `0 < ε < 1/2` and `t ≠ 0`:
1. `longSawtoothTailGapTheta ε t ≤ 1`, and eventually
   `−2 ⟨S^{\mathrm{long}}_{ε,t}, T_{ε,t}⟩_T ≤ longSawtoothTailGapTheta ε t · (‖S^{\mathrm{long}}_{ε,t}‖_T² + ‖T_{ε,t}‖_T²)`;
2. `longSawtoothTailGapTheta ε t < 1` iff `¬ ReceiverBounded (oscillatingSmoothPower ε t)` iff
   either `‖longSawtoothAmp ε t‖ ≠ ‖tailDriftAmp ε t‖` (harmonic amplitude mismatch) or
   `−Re(longSawtoothAmp ε t · \overline{tailDriftAmp ε t}) < ‖longSawtoothAmp ε t‖ ‖tailDriftAmp ε t‖`
   (harmonic phase decorrelation). -/
theorem eventually_longSawtooth_tail_quadratic_gap {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {t : ℝ} (ht : t ≠ 0) :
    longSawtoothTailGapTheta ε t ≤ 1 ∧
    (∀ᶠ T : ℕ in atTop,
      -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
        longSawtoothTailGapTheta ε t *
          (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
            pronicNorm (oscillatingTailDrift ε t) T ^ 2)) ∧
    (longSawtoothTailGapTheta ε t < 1 ↔ ¬ ReceiverBounded (oscillatingSmoothPower ε t)) ∧
    (longSawtoothTailGapTheta ε t < 1 ↔
      (‖longSawtoothAmp ε t‖ ≠ ‖tailDriftAmp ε t‖ ∨
        -(longSawtoothAmp ε t * starRingEnd ℂ (tailDriftAmp ε t)).re <
          ‖longSawtoothAmp ε t‖ * ‖tailDriftAmp ε t‖)) := by
  set c₀ := probeEnergyLowerRate ε t with hc₀
  set C₀ := probeEnergyUpperRate ε t with hC₀
  set C_tail := tailEnergyUpperRate ε t with hC_tail
  set M := 4 * C₀ + c₀ + 3 * C_tail with hM
  have hC₀_nonneg : 0 ≤ C₀ := by
    rw [hC₀, probeEnergyUpperRate]
    have : 0 < 1 - 2 * ε := by linarith
    positivity
  have hc₀_nonneg : 0 ≤ c₀ := by
    rcases eq_or_ne (riemannZeta (oscillationExponent ε t)) 0 with hz | hz
    · rw [hc₀, probeEnergyLowerRate, probeAmp, hz]; simp
    · exact (probeEnergyLowerRate_pos hε hε2 ht hz).le
  have hC_tail_pos : 0 < C_tail := by
    rw [hC_tail, tailEnergyUpperRate]
    have hγ : 0 < 1 - 2 * ε := by linarith
    have hρ1 : oscillationExponent ε t - 1 ≠ 0 := by
      intro h0
      have := congrArg Complex.re h0
      rw [sub_re, oscillationExponent_re, one_re, zero_re] at this
      linarith
    have ha0 : 0 < ‖tailDriftAmp ε t‖ := norm_pos_iff.mpr (one_div_ne_zero hρ1)
    positivity
  have hM_pos : 0 < M := by linarith
  have hθ_le : longSawtoothTailGapTheta ε t ≤ 1 := by
    rw [longSawtoothTailGapTheta, ← hc₀, ← hC₀, ← hC_tail, ← hM]
    have : 0 ≤ c₀ / (4 * M) := div_nonneg hc₀_nonneg (by linarith)
    linarith
  have hev : ∀ᶠ T : ℕ in atTop,
      -2 * pronicInner (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T ≤
        longSawtoothTailGapTheta ε t *
          (pronicNorm (oscillatingLongSawtooth ε t) T ^ 2 +
            pronicNorm (oscillatingTailDrift ε t) T ^ 2) := by
    rcases eq_or_ne (riemannZeta (oscillationExponent ε t)) 0 with hz | hz
    · have hc₀_zero : c₀ = 0 := by rw [hc₀, probeEnergyLowerRate, probeAmp, hz]; simp
      have hθ_one : longSawtoothTailGapTheta ε t = 1 := by
        rw [longSawtoothTailGapTheta, ← hc₀, hc₀_zero, zero_div, sub_zero]
      rw [hθ_one]
      refine Eventually.of_forall fun T => ?_
      have hpol := pronicNorm_add_sq_eq (oscillatingLongSawtooth ε t) (oscillatingTailDrift ε t) T
      have hsq : 0 ≤ pronicNorm (fun n =>
          oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T ^ 2 := sq_nonneg _
      linarith
    · have hc₀_pos : 0 < c₀ := probeEnergyLowerRate_pos hε hε2 ht hz
      set C_short := (1 + 1 / (1 - ε)) * Real.sqrt (1 + 1 / ε) with hC_short
      have hrpow : Tendsto (fun T : ℕ => (T : ℝ) ^ (1 - 2 * ε)) atTop atTop :=
        (tendsto_rpow_atTop (by linarith : 0 < 1 - 2 * ε)).comp tendsto_natCast_atTop_atTop
      filter_upwards [eventually_probeEnergy_le_and_ge hε hε2 ht hz,
        eventually_oscillatingTailDrift_energy_le_and_ge hε hε2 ht,
        tendsto_atTop.mp hrpow (4 * C_short ^ 2 / c₀)] with T hprobe htail hT_big
      rw [div_le_iff₀ hc₀_pos] at hT_big
      set x := pronicNorm (oscillatingLongSawtooth ε t) T
      set y := pronicNorm (oscillatingTailDrift ε t) T
      set z := pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) T
      set w := pronicNorm (weightCenteredPrefix (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d)) T
      set s := pronicNorm (oscillatingShortSawtooth ε t) T
      have hw_sq : weightPronicEnergy (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) T = w ^ 2 :=
        weightPronicEnergy_eq_sq_pronicNorm _ _ T
      have hs_le : s ≤ C_short := pronicNorm_oscillatingShortSawtooth_le hε (by linarith) t T
      have hs_sq : s ^ 2 ≤ C_short ^ 2 :=
        pow_le_pow_left₀ (pronicNorm_nonneg _ _) hs_le 2
      have hw_le_sz : w ≤ s + z := by
        have hcongr : w = pronicNorm (fun n => oscillatingShortSawtooth ε t n +
            (oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n)) T :=
          pronicNorm_congr fun n _ => by
            rw [weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail,
              oscillatingSawtoothPrefix_eq_short_add_long]; ring
        rw [hcongr]
        exact pronicNorm_add_le _ _ T
      have hz_le_ws : z ≤ w + s := by
        have ht1 := pronicNorm_add_le
          (weightCenteredPrefix (oscillatingSmoothPower ε t)
            (∑' d : ℕ, oscillatingSmoothPower ε t d / d))
          (fun n => (-1) * oscillatingShortSawtooth ε t n) T
        rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at ht1
        have hcongr : z = pronicNorm (fun n =>
            weightCenteredPrefix (oscillatingSmoothPower ε t)
              (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n +
            (-1) * oscillatingShortSawtooth ε t n) T :=
          pronicNorm_congr fun n _ => by
            rw [weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail,
              oscillatingSawtoothPrefix_eq_short_add_long]; ring
        rwa [hcongr]
      have hx_le_zy : x ≤ z + y := by
        have ht1 := pronicNorm_add_le
          (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n)
          (fun n => (-1) * oscillatingTailDrift ε t n) T
        rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at ht1
        have hcongr : x = pronicNorm (fun n =>
            (oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n) +
            (-1) * oscillatingTailDrift ε t n) T :=
          pronicNorm_congr fun n _ => by ring
        rwa [hcongr]
      have hw2_le : w ^ 2 ≤ 2 * s ^ 2 + 2 * z ^ 2 := by
        have h1 : w ^ 2 ≤ (s + z) ^ 2 := pow_le_pow_left₀ (pronicNorm_nonneg _ _) hw_le_sz 2
        nlinarith [sq_nonneg (s - z)]
      have hz2_le : z ^ 2 ≤ 2 * w ^ 2 + 2 * s ^ 2 := by
        have h1 : z ^ 2 ≤ (w + s) ^ 2 := pow_le_pow_left₀ (pronicNorm_nonneg _ _) hz_le_ws 2
        nlinarith [sq_nonneg (w - s)]
      have hx2_le : x ^ 2 ≤ 2 * z ^ 2 + 2 * y ^ 2 := by
        have h1 : x ^ 2 ≤ (z + y) ^ 2 := pow_le_pow_left₀ (pronicNorm_nonneg _ _) hx_le_zy 2
        nlinarith [sq_nonneg (z - y)]
      have hw_lo : c₀ * (T : ℝ) ^ (1 - 2 * ε) ≤ w ^ 2 := by
        rw [← hw_sq]; exact hprobe.1
      have hw_hi : w ^ 2 ≤ C₀ * (T : ℝ) ^ (1 - 2 * ε) := by
        rw [← hw_sq]; exact hprobe.2
      have hz_lo : c₀ / 4 * (T : ℝ) ^ (1 - 2 * ε) ≤ z ^ 2 := by linarith
      have hxy_hi : x ^ 2 + y ^ 2 ≤ M * (T : ℝ) ^ (1 - 2 * ε) := by
        rw [hM]; linarith [htail.2]
      have hratio : c₀ / (4 * M) * (x ^ 2 + y ^ 2) ≤ z ^ 2 := by
        have h1 : c₀ / (4 * M) * (x ^ 2 + y ^ 2) ≤ c₀ / (4 * M) * (M * (T : ℝ) ^ (1 - 2 * ε)) :=
          mul_le_mul_of_nonneg_left hxy_hi (by positivity)
        have h2 : c₀ / (4 * M) * (M * (T : ℝ) ^ (1 - 2 * ε)) = c₀ / 4 * (T : ℝ) ^ (1 - 2 * ε) := by
          field_simp [hM_pos.ne']
        linarith
      have hpol : z ^ 2 = x ^ 2 + 2 * pronicInner (oscillatingLongSawtooth ε t)
          (oscillatingTailDrift ε t) T + y ^ 2 := pronicNorm_add_sq_eq _ _ T
      rw [longSawtoothTailGapTheta, ← hc₀, ← hC₀, ← hC_tail, ← hM]
      linarith
  have hlt_iff : longSawtoothTailGapTheta ε t < 1 ↔ ¬ ReceiverBounded (oscillatingSmoothPower ε t) := by
    rw [longSawtoothTailGapTheta, ← hc₀, ← hC₀, ← hC_tail, ← hM]
    have h4M : 0 < 4 * M := by linarith
    have hdiv_pos : 1 - c₀ / (4 * M) < 1 ↔ 0 < c₀ := by
      constructor
      · intro h
        have : 0 < c₀ / (4 * M) := by linarith
        exact (div_pos_iff_of_pos_right h4M).mp this
      · intro h
        linarith [div_pos h h4M]
    rw [hdiv_pos, hc₀, probeEnergyLowerRate_pos_iff hε hε2 ht,
      receiverBounded_oscillatingSmoothPower_iff hε hε2.le t, oscillationExponent]
  have hharm_iff : longSawtoothTailGapTheta ε t < 1 ↔
      (‖longSawtoothAmp ε t‖ ≠ ‖tailDriftAmp ε t‖ ∨
        -(longSawtoothAmp ε t * starRingEnd ℂ (tailDriftAmp ε t)).re <
          ‖longSawtoothAmp ε t‖ * ‖tailDriftAmp ε t‖) := by
    rw [hlt_iff, receiverBounded_oscillatingSmoothPower_iff hε hε2.le t, ← oscillationExponent]
    have hρ0 : oscillationExponent ε t ≠ 0 := oscillationExponent_ne_zero (by linarith) t
    have hdecomp := norm_sq_longSawtoothAmp_add_tailDriftAmp_eq ε t
    constructor
    · intro hz
      have hquot : riemannZeta (oscillationExponent ε t) / oscillationExponent ε t ≠ 0 :=
        div_ne_zero hz hρ0
      have hsq_pos : 0 < ‖riemannZeta (oscillationExponent ε t) / oscillationExponent ε t‖ ^ 2 :=
        sq_pos_of_pos (norm_pos_iff.mpr hquot)
      by_contra hnot
      rcases not_or.mp hnot with ⟨hnot1, hnot2⟩
      rw [not_ne_iff] at hnot1
      rw [not_lt] at hnot2
      have h1 : (‖longSawtoothAmp ε t‖ - ‖tailDriftAmp ε t‖) ^ 2 = 0 := by
        rw [hnot1, sub_self, sq, mul_zero]
      have h2 : ‖longSawtoothAmp ε t‖ * ‖tailDriftAmp ε t‖ +
          (longSawtoothAmp ε t * starRingEnd ℂ (tailDriftAmp ε t)).re ≤ 0 := by
        linarith
      linarith [hdecomp.2.1]
    · intro hsrc hz
      have hquot : riemannZeta (oscillationExponent ε t) / oscillationExponent ε t = 0 := by
        rw [hz, zero_div]
      have hsq_zero : ‖riemannZeta (oscillationExponent ε t) / oscillationExponent ε t‖ ^ 2 = 0 := by
        rw [hquot, norm_zero, sq, mul_zero]
      rcases hsrc with hmis | hdec
      · have hpos : 0 < (‖longSawtoothAmp ε t‖ - ‖tailDriftAmp ε t‖) ^ 2 :=
          sq_pos_of_ne_zero (sub_ne_zero.mpr hmis)
        linarith [hdecomp.2.1, hdecomp.2.2.2]
      · linarith [hdecomp.2.1, hdecomp.2.2.1]
  exact ⟨hθ_le, hev, hlt_iff, hharm_iff⟩

/-- **On the high-height Vinogradov–Korobov collar and on every bounded-height zero-free collar,
the explicit quadratic gap `longSawtoothTailGapTheta ε t < 1` holds unconditionally.** -/
theorem longSawtoothTailGapTheta_lt_one_vk_and_box :
    (∃ T₀ : ℝ, Real.exp (Real.exp 1) ≤ T₀ ∧ ∀ ε t : ℝ, T₀ ≤ |t| → 0 < ε →
      ε < min (1 / 2) (RHTower.vkHadamardWidth |t|) →
      longSawtoothTailGapTheta ε t < 1) ∧
    (∀ T : ℝ, ∃ δ > 0, ∀ ε t : ℝ, 0 < ε → ε < min δ (1 / 2) → t ≠ 0 → |t| ≤ T →
      longSawtoothTailGapTheta ε t < 1) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨T₀, hT₀, hvk⟩ := exists_not_receiverBounded_oscillatingSmoothPower_vk
    refine ⟨T₀, hT₀, fun ε t ht hε hεw => ?_⟩
    have hε2 : ε < 1 / 2 := hεw.trans_le (min_le_left _ _)
    have ht0 : t ≠ 0 := by
      intro h0; rw [h0, abs_zero] at ht; linarith [Real.exp_pos (Real.exp 1)]
    exact (eventually_longSawtooth_tail_quadratic_gap hε hε2 ht0).2.2.1.mpr (hvk ε t ht hε hεw)
  · intro T
    obtain ⟨δ, hδ, hbox⟩ := exists_delta_not_receiverBounded_oscillatingSmoothPower_box T
    refine ⟨δ, hδ, fun ε t hε hεm ht0 ht => ?_⟩
    have hε2 : ε < 1 / 2 := hεm.trans_le (min_le_right _ _)
    exact (eventually_longSawtooth_tail_quadratic_gap hε hε2 ht0).2.2.1.mpr
      (hbox ε t hε hεm.le ht)

/-- **Across the full sub-half strip `0 < ε < 1/2, t ≠ 0`, `longSawtoothTailGapTheta ε t < 1` is
equivalent to the Riemann hypothesis.** -/
theorem riemannHypothesis_iff_forall_ne_zero_longSawtoothTailGapTheta_lt_one :
    RiemannHypothesis ↔
      ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → ∀ t : ℝ, t ≠ 0 →
        longSawtoothTailGapTheta ε t < 1 := by
  rw [riemannHypothesis_iff_forall_not_receiverBounded_oscillatingSmoothPower]
  constructor
  · intro hRH ε hε hε2 t ht
    exact (eventually_longSawtooth_tail_quadratic_gap hε hε2 ht).2.2.1.mpr (hRH ε hε hε2 t)
  · intro h ε hε hε2 t
    rcases eq_or_ne t 0 with rfl | ht
    · exact not_receiverBounded_oscillatingSmoothPower_zero_from_source hε hε2.le
    · exact (eventually_longSawtooth_tail_quadratic_gap hε hε2 ht).2.2.1.mp (h ε hε hε2 t ht)

/-- **Exact hyperbola merge of long-sawtooth linear drift with the tail drift.** For every
`ε, t ∈ ℝ` and `n ∈ ℕ`, the linear subtraction `−n Σ_{⌊√n⌋ < d ≤ n} c_{ε,t}(d)/d` inside
`oscillatingLongSawtooth ε t n` identically absorbs `oscillatingTailDrift ε t n` and shifts the
tail cutoff from `d = n` down to the hyperbola threshold `d = ⌊√n⌋`, leaving the integer-quotient
sum `Σ_{⌊√n⌋ < d ≤ n} c_{ε,t}(d) ⌊n/d⌋` plus the rescaled square-root tail
`(n / ⌊√n⌋) T_{ε,t}(⌊√n⌋)`. -/
theorem oscillatingLongSawtooth_add_tail_eq_quotientSum_add_sqrtTail (ε t : ℝ) (n : ℕ) :
    oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n =
      (∑ d ∈ Ioc (Nat.sqrt n) n, oscillatingSmoothPower ε t d * ((n / d : ℕ) : ℝ)) +
        (n : ℝ) * (∑ d ∈ Icc 1 (Nat.sqrt n), oscillatingSmoothPower ε t d / d -
          ∑' d : ℕ, oscillatingSmoothPower ε t d / d) := by
  unfold oscillatingLongSawtooth oscillatingTailDrift
  have hsn : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  have hsplit : Icc 1 n = Icc 1 (Nat.sqrt n) ∪ Ioc (Nat.sqrt n) n := by
    ext d; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  have hdisj : Disjoint (Icc 1 (Nat.sqrt n)) (Ioc (Nat.sqrt n) n) :=
    disjoint_left.mpr fun d h1 h2 => by simp only [mem_Icc, mem_Ioc] at h1 h2; omega
  have hsub : ∑ d ∈ Ioc (Nat.sqrt n) n,
        oscillatingSmoothPower ε t d * (((n / d : ℕ) : ℝ) - (n : ℝ) / d) =
      ∑ d ∈ Ioc (Nat.sqrt n) n, oscillatingSmoothPower ε t d * ((n / d : ℕ) : ℝ) -
        (n : ℝ) * ∑ d ∈ Ioc (Nat.sqrt n) n, oscillatingSmoothPower ε t d / d := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun d _ => by ring
  rw [hsub, hsplit, sum_union hdisj]
  ring

/-- **Source-only finite Euler–Maclaurin packet approximation of `S^{\mathrm{long}}_{ε,t} + T_{ε,t}`.**
Without invoking `riemannZeta` in the main term, for `0 < ε < 1`, `t ∈ ℝ`, and `n ≥ 1`,
`S^{\mathrm{long}}_{ε,t}(n) + T_{ε,t}(n)` tracks the finite short-quotient Euler–Maclaurin packet
`Re(czetaStripRemainder ρ (⌊√n⌋) · n^ρ / ρ)` to within
`(floorSumRate ρ + 3 (1 + 1/(1 − ε))) (√n)^{1−ε}`. -/
theorem abs_longSawtooth_add_tail_sub_czetaStripRemainder_le {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (t : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n -
      (czetaStripRemainder (oscillationExponent ε t) (Nat.sqrt n) *
        ((n : ℝ) : ℂ) ^ oscillationExponent ε t / oscillationExponent ε t).re| ≤
      (floorSumRate (oscillationExponent ε t) + 3 * (1 + 1 / (1 - ε))) *
        Real.sqrt n ^ (1 - ε) := by
  set ρ := oscillationExponent ε t with hρ
  set s := Nat.sqrt n with hs
  set r := Real.sqrt n with hr
  have hs1 : 1 ≤ s := by rw [hs]; exact Nat.sqrt_pos.mpr hn
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs1
  have hsr : (s : ℝ) ≤ r := by rw [hs, hr]; exact Real.nat_sqrt_le_real_sqrt
  have hrs : r < (s : ℝ) + 1 := by rw [hs, hr]; exact Real.real_sqrt_lt_nat_sqrt_succ
  have hr0 : 0 < r := lt_of_lt_of_le hs0 hsr
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hρre : ρ.re = 1 - ε := oscillationExponent_re ε t
  have hρ0 : 0 < ρ.re := by rw [hρre]; linarith
  have hρ1 : ρ ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [hρre, one_re] at this
    linarith
  have hρ_ne : ρ ≠ 0 := oscillationExponent_ne_zero hε1 t
  have hρ_norm : 0 < ‖ρ‖ := norm_pos_iff.mpr hρ_ne
  have hpre := abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le hε hε1 t hn
  have hshort := abs_oscillatingShortSawtooth_le hε hε1 t hn
  have hcz := norm_czetaStripRemainder_sub_le hρ0 hρ1 hs1
  rw [hρre] at hcz
  have hr2s : r ≤ 2 * (s : ℝ) := by
    have : (1 : ℝ) ≤ s := by exact_mod_cast hs1
    linarith
  have hr_pow : r ^ (1 - ε) ≤ 2 * (s : ℝ) ^ (1 - ε) := by
    calc r ^ (1 - ε) ≤ (2 * (s : ℝ)) ^ (1 - ε) :=
          Real.rpow_le_rpow hr0.le hr2s (by linarith)
      _ = (2 : ℝ) ^ (1 - ε) * (s : ℝ) ^ (1 - ε) :=
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hs0.le
      _ ≤ (2 : ℝ) ^ (1 : ℝ) * (s : ℝ) ^ (1 - ε) :=
          mul_le_mul_of_nonneg_right
            (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)) (by positivity)
      _ = 2 * (s : ℝ) ^ (1 - ε) := by rw [Real.rpow_one]
  have hn_pow : (n : ℝ) ^ (1 - ε) = r ^ (1 - ε) * r ^ (1 - ε) := by
    have hr2 : (n : ℝ) = r * r := by
      rw [← sq, hr, Real.sq_sqrt (Nat.cast_nonneg n)]
    rw [hr2, Real.mul_rpow hr0.le hr0.le]
  have hrem_cz : |((czetaStripRemainder ρ s - riemannZeta ρ) *
      ((n : ℝ) : ℂ) ^ ρ / ρ).re| ≤ 2 * (1 + 1 / (1 - ε)) * r ^ (1 - ε) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0, hρre, hn_pow]
    have hmul : ‖czetaStripRemainder ρ s - riemannZeta ρ‖ * (r ^ (1 - ε) * r ^ (1 - ε)) / ‖ρ‖ ≤
        (‖ρ‖ * ((1 + 1 / (1 - ε)) * (s : ℝ) ^ (-(1 - ε)))) *
          (r ^ (1 - ε) * (2 * (s : ℝ) ^ (1 - ε))) / ‖ρ‖ := by
      refine div_le_div_of_nonneg_right ?_ hρ_norm.le
      exact mul_le_mul hcz (mul_le_mul_of_nonneg_left hr_pow (by positivity))
        (by positivity) (by positivity)
    have hss : (s : ℝ) ^ (-(1 - ε)) * (s : ℝ) ^ (1 - ε) = 1 := by
      rw [← Real.rpow_add hs0, neg_add_cancel, Real.rpow_zero]
    calc ‖czetaStripRemainder ρ s - riemannZeta ρ‖ * (r ^ (1 - ε) * r ^ (1 - ε)) / ‖ρ‖
        ≤ (‖ρ‖ * ((1 + 1 / (1 - ε)) * (s : ℝ) ^ (-(1 - ε)))) *
            (r ^ (1 - ε) * (2 * (s : ℝ) ^ (1 - ε))) / ‖ρ‖ := hmul
      _ = 2 * (1 + 1 / (1 - ε)) * r ^ (1 - ε) * ((s : ℝ) ^ (-(1 - ε)) * (s : ℝ) ^ (1 - ε)) := by
          field_simp [hρ_norm.ne']
      _ = 2 * (1 + 1 / (1 - ε)) * r ^ (1 - ε) := by rw [hss, mul_one]
  have hid : oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n -
      (czetaStripRemainder ρ s * ((n : ℝ) : ℂ) ^ ρ / ρ).re =
      (weightCenteredPrefix (oscillatingSmoothPower ε t)
        (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n -
        (riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ).re) -
      oscillatingShortSawtooth ε t n -
      ((czetaStripRemainder ρ s - riemannZeta ρ) * ((n : ℝ) : ℂ) ^ ρ / ρ).re := by
    rw [weightCenteredPrefix_oscillatingSmoothPower_eq_sawtooth_add_tail,
      oscillatingSawtoothPrefix_eq_short_add_long]
    have hre : ((czetaStripRemainder ρ s - riemannZeta ρ) * ((n : ℝ) : ℂ) ^ ρ / ρ).re =
        (czetaStripRemainder ρ s * ((n : ℝ) : ℂ) ^ ρ / ρ).re -
          (riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ).re := by
      rw [← Complex.sub_re]
      congr 1; ring
    rw [hre]; ring
  rw [hid]
  calc _ ≤ |weightCenteredPrefix (oscillatingSmoothPower ε t)
            (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n -
          (riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ).re -
          oscillatingShortSawtooth ε t n| +
        |((czetaStripRemainder ρ s - riemannZeta ρ) * ((n : ℝ) : ℂ) ^ ρ / ρ).re| := abs_sub _ _
    _ ≤ |weightCenteredPrefix (oscillatingSmoothPower ε t)
          (∑' d : ℕ, oscillatingSmoothPower ε t d / d) n -
          (riemannZeta ρ * ((n : ℝ) : ℂ) ^ ρ / ρ).re| +
        |oscillatingShortSawtooth ε t n| +
        |((czetaStripRemainder ρ s - riemannZeta ρ) * ((n : ℝ) : ℂ) ^ ρ / ρ).re| :=
        add_le_add_left (abs_sub _ _) _
    _ ≤ floorSumRate ρ * r ^ (1 - ε) + (1 + 1 / (1 - ε)) * r ^ (1 - ε) +
        2 * (1 + 1 / (1 - ε)) * r ^ (1 - ε) :=
        add_le_add (add_le_add hpre hshort) hrem_cz
    _ = (floorSumRate ρ + 3 * (1 + 1 / (1 - ε))) * r ^ (1 - ε) := by ring

/-- **Uniform pronic-norm bound for the remainder between `S^{\mathrm{long}}_{ε,t} + T_{ε,t}` and the
finite short-quotient Euler–Maclaurin packet.** -/
theorem pronicNorm_longSawtooth_add_tail_sub_czetaStripRemainder_le {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε < 1) (t : ℝ) (T : ℕ) :
    pronicNorm (fun n => oscillatingLongSawtooth ε t n + oscillatingTailDrift ε t n -
      (czetaStripRemainder (oscillationExponent ε t) (Nat.sqrt n) *
        ((n : ℝ) : ℂ) ^ oscillationExponent ε t / oscillationExponent ε t).re) T ≤
      (floorSumRate (oscillationExponent ε t) + 3 * (1 + 1 / (1 - ε))) *
        Real.sqrt (1 + 1 / ε) := by
  set K := floorSumRate (oscillationExponent ε t) + 3 * (1 + 1 / (1 - ε)) with hK
  have hK0 : 0 ≤ K := by
    have hρ0 : 0 < (oscillationExponent ε t).re := by
      rw [oscillationExponent_re]; linarith
    have hρ1 : (oscillationExponent ε t).re < 1 := by
      rw [oscillationExponent_re]; linarith
    have hf0 : 0 ≤ floorSumRate (oscillationExponent ε t) := floorSumRate_nonneg hρ0 hρ1
    have h1ε : 0 < 1 - ε := by linarith
    positivity
  have h := sum_sq_le_of_abs_le_sqrt_rpow hε
    (fun n hn => abs_longSawtooth_add_tail_sub_czetaStripRemainder_le hε hε1 t hn) T
  rw [pronicNorm]
  calc Real.sqrt _ ≤ Real.sqrt (K ^ 2 * (1 + 1 / ε)) := Real.sqrt_le_sqrt h
    _ = K * Real.sqrt (1 + 1 / ε) := by
        rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK0]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
