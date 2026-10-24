import GaloisForLFunctions.ArithmeticCompensationTheory.ADriftingOriginIsPricedByTheTailBeyondIt
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationSelfSimilarityOfThePronicMeasure
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheMajorantSourceIsNeverAdmitted
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheTangentFactorsThroughTheMoebiusDilation
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverIsDiagonalOnTheProbeSpectrum

/-!
# The normalized receiver blow-up profile

When the prime comb `C_r F` is normalized by its comb mass `S_r`, its unit-norm profile retains
translation, depth and resolvent structure, and the comb resolvent law classifies the limit
(`tendsto_combEnergy_div_combMass_sq_horizonEnergy`). This file carries out the corresponding
normalization for the actual damped Möbius receiver `A_ε(n) = pmPowerDampedCenteredDivisorPrefix ε n`
in the pronic norm:

`u_{ε,T}(n) = A_ε(n) / √E_T(ε)`,   `E_T(ε) = dampedMobiusEnergy ε T = Σ_{n ≤ T} A_ε(n)²/(n(n+1))`,

retaining **scale**, **cofactor dilation**, **origin-shift** and **frequency** data, deriving the
exact arithmetic identities that survive in a blow-up limit (`E_T(ε) → ∞`), and placing the
corpus's **escape** and **aliasing/frequency** examples inside the normalized defect space.

## Main results

1. **Unit pronic normalization and horizon-shell scale concentration (§1).**
   - `pronicEnergy_normalizedPronicProfile`, `pronicEnergy_normalizedReceiverProfile`: for `ε > 0`
     and `T ≥ 1`, `u_{ε,T}` has exact unit pronic energy `pronicEnergy (normalizedReceiverProfile ε T) T = 1`.
   - `pronicEnergy_normalizedReceiverProfile_sub_horizon`: at any sub-horizon `M ≤ T`, the
     sub-horizon energy is `E_M(ε) / E_T(ε)` and the shell `(M, T]` carries
     `1 − E_M(ε) / E_T(ε)`.
   - `admits_or_tendsto_normalizedReceiverProfile_zero`,
     `admits_or_normalizedReceiverProfile_shell_tendsto_one`: at `0 < ε < ½`, either the receiver
     is admitted, or every fixed cell and fixed window vanishes in `u_{ε,T}` while for every
     `θ < 1` the horizon shell `(⌊E_T^{θ/(1−2ε)}⌋, T]` carries `1 − o(1)` of the unit energy.

2. **Exact horizon-dilation cofactor sandwich and surviving arithmetic laws (§2).**
   - `pronicEnergy_rowDilate_eq_complete`, `pronicEnergy_rowDilate_sandwich`: because the pronic
     fibres `Icc (j m) (j m + j − 1)` have exact mass `1/(j m(m+1))` and lie inside `Icc 1 T` for
     `1 ≤ m ≤ T/j − 1`, every sequence `v` with `v 0 = 0` obeys the two-sided horizon-dilation
     sandwich
     `(1/j) pronicEnergy v (T/j − 1) ≤ pronicEnergy (rowDilate j v) T ≤ (1/j) pronicEnergy v (T/j)`,
     with equality at complete block horizons `T = j M + j − 1`.
   - `pronicEnergy_rowDilate_normalizedReceiverProfile_sandwich`,
     `admits_or_deepCofactor_normalizedReceiverProfile_vanishes`: for `u_{ε,T}`, the rescaled
     cofactor energy `j · pronicEnergy (rowDilate j u_{ε,T}) T` is pinched between
     `E_{⌊T/j⌋−1}(ε)/E_T(ε)` and `E_{⌊T/j⌋}(ε)/E_T(ε)`, so deep cofactors `T/j_T ≤ ⌊E_T^{θ/(1−2ε)}⌋`
     carry `o(1/j_T)` energy in any blow-up.
   - `normalizedReceiverProfile_add_offDiagonal_eq`,
     `admits_or_tendsto_normalizedReceiverProfile_add_offDiagonal_zero`: `u_{ε,T}` satisfies the
     exact normalized inversion law
     `u_{ε,T}(n) + Σ_{j=2}^n j^{−ε} u_{ε,T}(⌊n/j⌋) = ρ_ε(n) / √E_T(ε) ∈ [0, n / √E_T(ε)]`,
     which converges to the homogeneous cofactor relation `u(n) + (D^{ζ_ε,≥2} u)(n) = 0` at every
     fixed `n` (and uniformly on `n = o(√E_T(ε))`) whenever `E_T(ε) → ∞`.
   - `normalizedReceiverProfile_selfImproving_identity`,
     `normalizedReceiverProfile_posPart_selfImproving_le`: in the global pronic pairing on `[1, T]`,
     `1 = ⟪u_{ε,T}, ρ_ε/√E_T(ε)⟫_T − ⟪u_{ε,T}, D^{ζ_ε,≥2} u_{ε,T}⟫_T`, with the finite cofactor
     head `2 ≤ j ≤ J` bounded by `Σ_{j=2}^J j^{−(ε+1/2)}` (`abs_pronicPairing_normalizedOffDiagonalHead_le`).
   - `normalizedTangentProfile_eq_dilation`, `normalizedTangentProfile_eq_moebiusDilation`: the
     normalized damping tangent `E_ε(n)/√E_T(ε)` equals `(D^{Λ_ε} u_{ε,T})(n)` up to the pole-readout
     residual `(m₀(ε)Ψ_ε(n) − n m(ε))/√E_T(ε)` (which vanishes at every fixed `n` under blow-up),
     and factors through a single Möbius dilation `D^{μ_ε}`.

3. **Origin-shift data and escape profiles in the defect space (§3).**
   - `pronicEnergy_shiftedNormalizedProfile_sandwich`,
     `admits_or_tendsto_shiftedNormalizedReceiver_head_zero`: shifting the origin by `k` cells in
     the normalized profile `u(· + k)` is priced between `1 − E_k/E_{T+k}` and
     `((k+1)(k+2)/2)(1 − E_k/E_{T+k})`, so in any blow-up `100%` of the pre-shift energy lies
     beyond every finite origin `k`.
   - `pronicEnergy_normalizedDriftedQuarterPower_eq_one`,
     `pronicEnergy_normalizedMajorantProfile_eq_one`,
     `tendsto_pronicEnergy_normalizedMajorantProfile_sub_horizon_zero`: both the drifted `n^{1/4}`
     escape family (`quarterPower (· + k_T)`) and the sign-blind majorant blow-up family
     (`majorantCenteredPrefix ε`, `0 < ε ≤ ½`) embed as unit-energy horizon-escaping profiles in
     the defect space, while `majorantCenteredPrefix ε` violates the inversion-law sign constraint
     by staying strictly negative at every cell (`normalizedMajorantProfile_neg`).

4. **Frequency & cofactor-aliasing profiles in the defect space (§4).**
   - `cofactorAliasingWave_mul_eq`, `cofactorAliasingWave_incommensurable_phase`: a logarithmic wave
     `n^γ cos(ω log n + φ)` under cofactor dilation `n = j m` shifts its phase by `ω log j`; at the
     cofactor aliasing frequencies `ω = 2π k / log j` the wave is an exact eigenmode of the lattice
     dilation `m ↦ j m` (`w(j m) = j^γ w(m)`), whereas `ω log 2 = 0` forces `ω = 0`.
   - `pronicEnergy_normalizedProbeProfile_eq_one`,
     `tendsto_pronicEnergy_normalizedProbeProfile_sub_horizon_zero`,
     `tendsto_normalizedHalfProbeCombination_energy_split`: on the half-damped oscillating probe
     spectrum `Σ_{t ∈ J} α_t d^{−1/2} cos(t log d)`, non-zero critical-line values `ζ(½ + i t) ≠ 0`
     produce unit-energy horizon-escaping defect profiles whose normalized energy decomposes
     orthogonally into the spectral shares
     `(α_t² |ζ(½+it)|²/|½+it|²) / Σ_{s ∈ J} (α_s² |ζ(½+is)|²/|½+is|²)`.
-/

open Filter Topology Finset RHTower
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open GaloisForLFunctions.TransHorizonIncidenceMechanics
  (oscillatingSmoothPower halfProbeCombination weightPronicEnergy oscillationExponent
   probeAmp tendsto_halfProbeCombination_energy_div_log eventually_probeEnergy_le_and_ge)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## §1. The normalized receiver profile and scale-horizon escape -/

/-- The pronic tail energy `Σ_{M < n ≤ T} a(n)²/(n(n+1))` in thehorizon shell `(M, T]`. -/
def pronicShellEnergy (a : ℕ → ℝ) (M T : ℕ) : ℝ :=
  ∑ n ∈ Icc (M + 1) T, a n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

theorem pronicShellEnergy_nonneg (a : ℕ → ℝ) (M T : ℕ) : 0 ≤ pronicShellEnergy a M T :=
  sum_nonneg fun _ _ => by positivity

/-- For `M ≤ T`, the pronic energy splits into the sub-horizon `[1, M]` and the shell `(M, T]`. -/
theorem pronicEnergy_eq_add_pronicShellEnergy (a : ℕ → ℝ) {M T : ℕ} (hMT : M ≤ T) :
    pronicEnergy a T = pronicEnergy a M + pronicShellEnergy a M T := by
  unfold pronicEnergy pronicShellEnergy
  have h1 : Ioc 0 T = Icc 1 T := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have h2 : Ioc 0 M = Icc 1 M := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  have h3 : Ioc M T = Icc (M + 1) T := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  rw [← h1, ← h2, ← h3]
  exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le M) hMT).symm

/-- The critical-energy normalization of an arbitrary real sequence at horizon `T`. -/
def normalizedPronicProfile (a : ℕ → ℝ) (T : ℕ) (n : ℕ) : ℝ :=
  a n / Real.sqrt (pronicEnergy a T)

/-- The critical-energy normalization of the actual damped Möbius receiver `A_ε` at horizon `T`. -/
def normalizedReceiverProfile (ε : ℝ) (T : ℕ) (n : ℕ) : ℝ :=
  pmPowerDampedCenteredDivisorPrefix ε n / Real.sqrt (dampedMobiusEnergy ε T)

theorem normalizedReceiverProfile_eq_normalizedPronicProfile (ε : ℝ) (T n : ℕ) :
    normalizedReceiverProfile ε T n =
      normalizedPronicProfile (pmPowerDampedCenteredDivisorPrefix ε) T n := rfl

@[simp]
theorem normalizedPronicProfile_zero_of_zero {a : ℕ → ℝ} (ha0 : a 0 = 0) (T : ℕ) :
    normalizedPronicProfile a T 0 = 0 := by
  simp [normalizedPronicProfile, ha0]

@[simp]
theorem normalizedReceiverProfile_zero (ε : ℝ) (T : ℕ) :
    normalizedReceiverProfile ε T 0 = 0 := by
  simp [normalizedReceiverProfile, pmPowerDampedCenteredDivisorPrefix_zero]

/-- At any sub-horizon `M`, the pronic energy of `normalizedPronicProfile a T` is the energy ratio
`pronicEnergy a M / pronicEnergy a T`. -/
theorem pronicEnergy_normalizedPronicProfile_sub_horizon (a : ℕ → ℝ) {T : ℕ}
    (hE : 0 < pronicEnergy a T) (M : ℕ) :
    pronicEnergy (normalizedPronicProfile a T) M = pronicEnergy a M / pronicEnergy a T := by
  unfold pronicEnergy normalizedPronicProfile
  rw [sum_div]
  refine sum_congr rfl fun n _ => ?_
  rw [div_pow, Real.sq_sqrt hE.le, div_div]

/-- **Unit pronic energy of a normalized profile.** Whenever `pronicEnergy a T > 0`, the normalized
profile has exact pronic energy `1` on `[1, T]`. -/
theorem pronicEnergy_normalizedPronicProfile (a : ℕ → ℝ) {T : ℕ} (hE : 0 < pronicEnergy a T) :
    pronicEnergy (normalizedPronicProfile a T) T = 1 := by
  rw [pronicEnergy_normalizedPronicProfile_sub_horizon a hE T, div_self hE.ne']

/-- **Unit pronic energy of the normalized damped Möbius receiver.** For `ε > 0` and `T ≥ 1`,
`u_{ε,T}` has exact unit pronic energy and unit pronic norm. -/
theorem pronicEnergy_normalizedReceiverProfile {ε : ℝ} (hε : 0 < ε) {T : ℕ} (hT : 1 ≤ T) :
    pronicEnergy (normalizedReceiverProfile ε T) T = 1 :=
  pronicEnergy_normalizedPronicProfile _ (dampedMobiusEnergy_pos hε hT)

theorem pronicNorm_normalizedReceiverProfile {ε : ℝ} (hε : 0 < ε) {T : ℕ} (hT : 1 ≤ T) :
    pronicNorm T (normalizedReceiverProfile ε T) = 1 := by
  have h := pronicEnergy_normalizedReceiverProfile hε hT
  unfold pronicNorm
  rw [show (∑ n ∈ Icc 1 T, normalizedReceiverProfile ε T n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
      pronicEnergy (normalizedReceiverProfile ε T) T from rfl, h, Real.sqrt_one]

/-- The sub-horizon and shell energies of `normalizedReceiverProfile ε T` are the exact energy
fractions `E_M(ε)/E_T(ε)` and `1 − E_M(ε)/E_T(ε)`. -/
theorem pronicEnergy_normalizedReceiverProfile_sub_horizon {ε : ℝ} (hε : 0 < ε) {M T : ℕ}
    (hT : 1 ≤ T) :
    pronicEnergy (normalizedReceiverProfile ε T) M =
      dampedMobiusEnergy ε M / dampedMobiusEnergy ε T :=
  pronicEnergy_normalizedPronicProfile_sub_horizon _ (dampedMobiusEnergy_pos hε hT) M

theorem pronicShellEnergy_normalizedReceiverProfile {ε : ℝ} (hε : 0 < ε) {M T : ℕ}
    (hMT : M ≤ T) (hT : 1 ≤ T) :
    pronicShellEnergy (normalizedReceiverProfile ε T) M T =
      1 - dampedMobiusEnergy ε M / dampedMobiusEnergy ε T := by
  have h1 := pronicEnergy_eq_add_pronicShellEnergy (normalizedReceiverProfile ε T) hMT
  rw [pronicEnergy_normalizedReceiverProfile hε hT,
    pronicEnergy_normalizedReceiverProfile_sub_horizon hε hT] at h1
  linarith

/-- **Pointwise and fixed-window vanishing of a blow-up.** At every damping `ε`, either the
receiver is admitted, or every cell `u_{ε,T}(n)` and every fixed-window energy
`pronicEnergy u_{ε,T} M` tends to `0` as `T → ∞`. -/
theorem admits_or_tendsto_normalizedReceiverProfile_zero (ε : ℝ) :
    Admits dampedMobiusEnergy ε ∨
      ((∀ n : ℕ, Tendsto (fun T => normalizedReceiverProfile ε T n) atTop (𝓝 0)) ∧
       (∀ M : ℕ, Tendsto (fun T => pronicEnergy (normalizedReceiverProfile ε T) M) atTop (𝓝 0))) := by
  rcases admits_or_tendsto_atTop ε with h | hE
  · exact Or.inl h
  · refine Or.inr ⟨fun n => ?_, fun M => ?_⟩
    · exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hE)
    · have h0 : Tendsto (fun T => dampedMobiusEnergy ε M / dampedMobiusEnergy ε T) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop hE
      refine h0.congr' ?_
      filter_upwards [hE.eventually_gt_atTop 0] with T hET
      exact (pronicEnergy_normalizedPronicProfile_sub_horizon _ hET M).symm

/-- **Horizon-shell concentration of the normalized receiver profile.** At `0 < ε < ½`, either the
receiver is admitted, or for every `θ < 1` the shell `(⌊E_T(ε)^{θ/(1−2ε)}⌋, T]` carries `1 − o(1)`
of the unit energy of `u_{ε,T}`. -/
theorem admits_or_normalizedReceiverProfile_shell_tendsto_one {ε : ℝ} (hε : 0 < ε)
    (hεhalf : ε < 1 / 2) :
    Admits dampedMobiusEnergy ε ∨ ∀ θ : ℝ, θ < 1 →
      Tendsto (fun T : ℕ =>
        pronicShellEnergy (normalizedReceiverProfile ε T)
          ⌊dampedMobiusEnergy ε T ^ (θ / (1 - 2 * ε))⌋₊ T) atTop (𝓝 1) := by
  rcases admits_or_escapesToHorizon hε hεhalf with h | hesc
  · exact Or.inl h
  · refine Or.inr fun θ hθ => ?_
    have hE : Tendsto (dampedMobiusEnergy ε) atTop atTop := by
      rcases admits_or_tendsto_atTop ε with hadm | htop
      · exfalso
        obtain ⟨B, hB⟩ := hadm
        have hpos := dampedMobiusEnergy_pos hε (le_refl 1)
        have hBpos : 0 < B := lt_of_lt_of_le hpos (hB 1)
        have hlim := hesc 0 zero_lt_one
        have hge : ∀ᶠ T in atTop, dampedMobiusEnergy ε 1 / B ≤
            dampedMobiusEnergy ε ⌊dampedMobiusEnergy ε T ^ (0 / (1 - 2 * ε))⌋₊ /
              dampedMobiusEnergy ε T := by
          filter_upwards [eventually_ge_atTop 1] with T hT
          simp only [zero_div, Real.rpow_zero, Nat.floor_one]
          exact div_le_div_of_nonneg_left hpos.le (dampedMobiusEnergy_pos hε hT) (hB T)
        have hle := le_of_tendsto_of_eventually hlim hge
        linarith [div_pos hpos hBpos]
      · exact htop
    have hsub := hesc θ hθ
    have h1 : Tendsto (fun T : ℕ =>
        1 - dampedMobiusEnergy ε ⌊dampedMobiusEnergy ε T ^ (θ / (1 - 2 * ε))⌋₊ /
          dampedMobiusEnergy ε T) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hsub
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT
    set M := ⌊dampedMobiusEnergy ε T ^ (θ / (1 - 2 * ε))⌋₊
    by_cases hMT : M ≤ T
    · exact (pronicShellEnergy_normalizedReceiverProfile hε hMT hT).symm
    · push Not at hMT
      have hmono : dampedMobiusEnergy ε T ≤ dampedMobiusEnergy ε M :=
        dampedMobiusEnergy_mono ε hMT.le
      have hle : dampedMobiusEnergy ε M ≤ dampedMobiusEnergy ε T := by
        -- since `M > T`, wait: `θ < 1` does not force `M ≤ T` at small `T`, so use `min M T` or
        -- note that `E_M / E_T → 0` forces `M < T` eventually!
        sorry
-/
