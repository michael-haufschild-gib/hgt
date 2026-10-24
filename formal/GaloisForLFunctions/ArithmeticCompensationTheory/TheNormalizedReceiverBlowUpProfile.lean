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
  (oscillatingSmoothPower halfProbeCombination weightPronicEnergy weightCenteredPrefix
   oscillationExponent probeAmp tendsto_halfProbeCombination_energy_div_log
   tendsto_probeEnergy_half_div_log eventually_probeEnergy_le_and_ge)

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## §1. The normalized receiver profile and scale-horizon escape -/

/-- The pronic tail energy `Σ_{M < n ≤ T} a(n)²/(n(n+1))` in the horizon shell `(M, T]`. -/
def pronicShellEnergy (a : ℕ → ℝ) (M T : ℕ) : ℝ :=
  ∑ n ∈ Icc (M + 1) T, a n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))

theorem pronicShellEnergy_nonneg (a : ℕ → ℝ) (M T : ℕ) : 0 ≤ pronicShellEnergy a M T :=
  sum_nonneg fun _ _ => by positivity

@[simp]
theorem pronicEnergy_zero (a : ℕ → ℝ) : pronicEnergy a 0 = 0 := by
  simp [pronicEnergy]

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
    have hsub := hesc θ hθ
    have h1 : Tendsto (fun T : ℕ =>
        1 - dampedMobiusEnergy ε ⌊dampedMobiusEnergy ε T ^ (θ / (1 - 2 * ε))⌋₊ /
          dampedMobiusEnergy ε T) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub hsub
    rw [sub_zero] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop 1,
        (tendsto_order.mp hsub).2 1 zero_lt_one] with T hT hlt1
    set M := ⌊dampedMobiusEnergy ε T ^ (θ / (1 - 2 * ε))⌋₊
    have hET0 : 0 < dampedMobiusEnergy ε T := dampedMobiusEnergy_pos hε hT
    have hMT : M ≤ T := by
      by_contra hcon
      push Not at hcon
      have hmono := dampedMobiusEnergy_mono ε hcon.le
      have hdiv : 1 ≤ dampedMobiusEnergy ε M / dampedMobiusEnergy ε T :=
        (one_le_div hET0).mpr hmono
      linarith
    exact (pronicShellEnergy_normalizedReceiverProfile hε hMT hT).symm

/-! ## §2. Cofactor self-similarity, exact horizon-dilation sandwich & surviving identities -/

/-- **Exact cofactor self-similarity on complete dilation blocks.** At the complete block horizon
`T = j * M + j − 1`, every fibre `1 ≤ m ≤ M` is complete and the dilated pronic energy is
*exactly* `(1/j) pronicEnergy v M`. -/
theorem pronicEnergy_rowDilate_eq_complete {j : ℕ} (hj : 1 ≤ j) (M : ℕ) (v : ℕ → ℝ)
    (hv0 : v 0 = 0) :
    pronicEnergy (rowDilate j v) (j * M + j - 1) = (1 / (j : ℝ)) * pronicEnergy v M := by
  unfold pronicEnergy
  have hmaps : ∀ n ∈ Icc 1 (j * M + j - 1), n / j ∈ range (M + 1) := by
    intro n hn
    rw [mem_Icc] at hn
    rw [mem_range]
    have hlt : n < (M + 1) * j := by
      have : (M + 1) * j = j * M + j := by ring
      omega
    exact (Nat.div_lt_iff_lt_mul (by omega : 0 < j)).mpr hlt
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun n => rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))]
  have hfiber : ∀ m ∈ range (M + 1),
      (∑ n ∈ (Icc 1 (j * M + j - 1)).filter (fun n => n / j = m),
          rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) =
        (1 / (j : ℝ)) * (if m = 0 then 0 else v m ^ 2 / ((m : ℝ) * ((m : ℝ) + 1))) := by
    intro m hm
    rw [mem_range] at hm
    rcases Nat.eq_zero_or_pos m with rfl | hm1
    · have hzero : ∀ n ∈ (Icc 1 (j * M + j - 1)).filter (fun n => n / j = 0),
          rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) = 0 := by
        intro n hn
        rw [Finset.mem_filter] at hn
        rw [rowDilate, hn.2, hv0]
        simp
      rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
      simp
    · rw [if_neg (by omega : m ≠ 0)]
      have hset : (Icc 1 (j * M + j - 1)).filter (fun n => n / j = m) =
          Icc (j * m) (j * m + j - 1) := by
        ext n
        rw [Finset.mem_filter, mem_Icc, mem_Icc]
        constructor
        · rintro ⟨_, hdiv⟩
          have hge : j * m ≤ n := by rw [← hdiv]; exact Nat.mul_div_le n j
          have hlt : n < (m + 1) * j := by
            rw [← Nat.div_lt_iff_lt_mul (by omega : 0 < j)]
            omega
          have heq : (m + 1) * j = j * m + j := by ring
          exact ⟨hge, by omega⟩
        · rintro ⟨hge, hle⟩
          have hjm1 : 1 ≤ j * m := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
          have hleM : j * m + j - 1 ≤ j * M + j - 1 := by
            have : j * m ≤ j * M := Nat.mul_le_mul_left j (by omega : m ≤ M)
            omega
          refine ⟨⟨by omega, by omega⟩, ?_⟩
          refine Nat.div_eq_of_lt_le ?_ ?_
          · rw [mul_comm]; exact hge
          · have : (m + 1) * j = j * m + j := by ring
            omega
      rw [hset]
      have hconst : ∀ n ∈ Icc (j * m) (j * m + j - 1),
          rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
            v m ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
        intro n hn
        have hn' : n ∈ (Icc 1 (j * M + j - 1)).filter (fun n => n / j = m) := by
          rwa [hset]
        rw [Finset.mem_filter] at hn'
        rw [rowDilate, hn'.2]
        ring
      rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, sum_Icc_pronic_dilation_fibre hj hm1]
      field_simp
  rw [Finset.sum_congr rfl hfiber, ← Finset.mul_sum]
  congr 1
  have hins : (range (M + 1) : Finset ℕ) = insert 0 (Icc 1 M) := by
    ext m
    rw [mem_range, Finset.mem_insert, mem_Icc]
    omega
  rw [hins, Finset.sum_insert (by simp), if_pos rfl, zero_add]
  exact Finset.sum_congr rfl fun m hm => by
    rw [mem_Icc] at hm
    rw [if_neg (by omega : m ≠ 0)]

/-- **Two-sided horizon-dilation sandwich on the pronic measure.** For every `j ≥ 1`, `T : ℕ` and
`v` with `v 0 = 0`,
`(1/j) pronicEnergy v (T/j − 1) ≤ pronicEnergy (rowDilate j v) T ≤ (1/j) pronicEnergy v (T/j)`. -/
theorem pronicEnergy_rowDilate_sandwich {j : ℕ} (hj : 1 ≤ j) (T : ℕ) (v : ℕ → ℝ)
    (hv0 : v 0 = 0) :
    (1 / (j : ℝ)) * pronicEnergy v (T / j - 1) ≤ pronicEnergy (rowDilate j v) T ∧
      pronicEnergy (rowDilate j v) T ≤ (1 / (j : ℝ)) * pronicEnergy v (T / j) := by
  constructor
  · rcases Nat.eq_zero_or_pos (T / j) with hdiv0 | hdiv1
    · rw [hdiv0, Nat.zero_sub, pronicEnergy_zero, mul_zero]
      exact pronicEnergy_nonneg _ _
    · rw [← pronicEnergy_rowDilate_eq_complete hj (T / j - 1) v hv0]
      refine pronicEnergy_mono (rowDilate j v) ?_
      have hmul : j * (T / j - 1) + j = j * (T / j) := by
        calc j * (T / j - 1) + j = j * (T / j - 1 + 1) := by ring
          _ = j * (T / j) := by rw [Nat.sub_add_cancel hdiv1]
      have hle : j * (T / j) ≤ T := Nat.mul_div_le T j
      omega
  · rw [← pronicEnergy_rowDilate_eq_complete hj (T / j) v hv0]
    refine pronicEnergy_mono (rowDilate j v) ?_
    have hlt : T < j * (T / j) + j := by
      have h1 := Nat.div_add_mod T j
      have h2 := Nat.mod_lt T (by omega : 0 < j)
      omega
    omega

/-- **Refined pronic dilation contraction.** Dilation by `j` bounds the pronic norm at horizon `T`
by `(1/√j) pronicNorm (T/j) v`. -/
theorem pronicNorm_rowDilate_le_div {j : ℕ} (hj : 1 ≤ j) (T : ℕ) (v : ℕ → ℝ) (hv0 : v 0 = 0) :
    pronicNorm T (rowDilate j v) ≤ (1 / Real.sqrt (j : ℝ)) * pronicNorm (T / j) v := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hsq : pronicNorm T (rowDilate j v) ^ 2 ≤
      ((1 / Real.sqrt (j : ℝ)) * pronicNorm (T / j) v) ^ 2 := by
    rw [mul_pow, div_pow, one_pow, Real.sq_sqrt hj0.le, pronicNorm_sq, pronicNorm_sq]
    exact (pronicEnergy_rowDilate_sandwich hj T v hv0).2
  exact (pow_le_pow_iff_left₀ (pronicNorm_nonneg _ _)
    (mul_nonneg (by positivity) (pronicNorm_nonneg _ _)) two_ne_zero).mp hsq

/-- **Cofactor energy sandwich for the normalized receiver profile.** For `ε > 0`, `j ≥ 1`, `T ≥ 1`,
the rescaled cofactor energy `j · pronicEnergy (rowDilate j u_{ε,T}) T` lies between
`E_{⌊T/j⌋−1}(ε)/E_T(ε)` and `E_{⌊T/j⌋}(ε)/E_T(ε)`. -/
theorem pronicEnergy_rowDilate_normalizedReceiverProfile_sandwich {ε : ℝ} (hε : 0 < ε)
    {j T : ℕ} (hj : 1 ≤ j) (hT : 1 ≤ T) :
    dampedMobiusEnergy ε (T / j - 1) / dampedMobiusEnergy ε T ≤
        (j : ℝ) * pronicEnergy (rowDilate j (normalizedReceiverProfile ε T)) T ∧
      (j : ℝ) * pronicEnergy (rowDilate j (normalizedReceiverProfile ε T)) T ≤
        dampedMobiusEnergy ε (T / j) / dampedMobiusEnergy ε T := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hsand := pronicEnergy_rowDilate_sandwich hj T (normalizedReceiverProfile ε T)
    (normalizedReceiverProfile_zero ε T)
  rw [pronicEnergy_normalizedReceiverProfile_sub_horizon hε hT,
    pronicEnergy_normalizedReceiverProfile_sub_horizon hε hT] at hsand
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hsand.1 hj0.le
    rwa [← mul_assoc, mul_one_div_cancel hj0.ne', one_mul] at h1
  · have h2 := mul_le_mul_of_nonneg_left hsand.2 hj0.le
    rwa [← mul_assoc, mul_one_div_cancel hj0.ne', one_mul] at h2

/-- **Deep cofactors vanish on a blow-up.** At `0 < ε < ½`, either the receiver is admitted, or
for every `θ < 1` and every cofactor sequence `j_T ≥ 1` folding `[1, T]` below the escape scale
(`T / j_T ≤ ⌊E_T(ε)^{θ/(1−2ε)}⌋`), the rescaled cofactor energy
`j_T · pronicEnergy (rowDilate (j_T) u_{ε,T}) T` tends to `0`. -/
theorem admits_or_deepCofactor_normalizedReceiverProfile_vanishes {ε : ℝ} (hε : 0 < ε)
    (hεhalf : ε < 1 / 2) :
    Admits dampedMobiusEnergy ε ∨ ∀ (θ : ℝ), θ < 1 → ∀ (j : ℕ → ℕ),
      (∀ T, 1 ≤ j T) →
      (∀ T, T / j T ≤ ⌊dampedMobiusEnergy ε T ^ (θ / (1 - 2 * ε))⌋₊) →
      Tendsto (fun T => (j T : ℝ) *
        pronicEnergy (rowDilate (j T) (normalizedReceiverProfile ε T)) T) atTop (𝓝 0) := by
  rcases admits_or_escapesToHorizon hε hεhalf with h | hesc
  · exact Or.inl h
  · refine Or.inr fun θ hθ j hj hle => ?_
    refine squeeze_zero' ?_ ?_ (hesc θ hθ)
    · filter_upwards [eventually_ge_atTop 1] with T _
      exact mul_nonneg (Nat.cast_nonneg _) (pronicEnergy_nonneg _ _)
    · filter_upwards [eventually_ge_atTop 1] with T hT
      have h2 := (pronicEnergy_rowDilate_normalizedReceiverProfile_sandwich hε (hj T) hT).2
      refine h2.trans ?_
      exact div_le_div_of_nonneg_right (dampedMobiusEnergy_mono ε (hle T))
        (dampedMobiusEnergy_nonneg ε T)

/-- The off-diagonal unit dilation operator `(D^{ζ_ε,≥2} v)(n) = Σ_{j=2}^n j^{−ε} v(⌊n/j⌋)` on an
arbitrary profile `v`. -/
def properUnitDilation (ε : ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Icc 2 n, (j : ℝ) ^ (-ε) * v (n / j)

theorem properUnitDilation_centeredPrefix (ε : ℝ) (n : ℕ) :
    properUnitDilation ε (pmPowerDampedCenteredDivisorPrefix ε) n =
      offDiagonalUnitDilation ε n := rfl

theorem properUnitDilation_normalizedReceiverProfile (ε : ℝ) (T n : ℕ) :
    properUnitDilation ε (normalizedReceiverProfile ε T) n =
      offDiagonalUnitDilation ε n / Real.sqrt (dampedMobiusEnergy ε T) := by
  unfold properUnitDilation offDiagonalUnitDilation normalizedReceiverProfile
  rw [sum_div]
  exact sum_congr rfl fun j _ => mul_div_assoc _ _ _

/-- **The exact normalized dilation inversion law.** For every `ε > 0`, `T ≥ 1` and `n ≥ 1`,
`u_{ε,T}(n) + (D^{ζ_ε,≥2} u_{ε,T})(n) = ρ_ε(n) / √E_T(ε)`. -/
theorem normalizedReceiverProfile_add_properUnitDilation_eq (ε : ℝ) (T : ℕ) {n : ℕ}
    (hn : 1 ≤ n) :
    normalizedReceiverProfile ε T n +
        properUnitDilation ε (normalizedReceiverProfile ε T) n =
      inversionDefect ε n / Real.sqrt (dampedMobiusEnergy ε T) := by
  rw [properUnitDilation_normalizedReceiverProfile, normalizedReceiverProfile, ← add_div]
  congr 1
  have h1 := sum_rpow_mul_centeredPrefix_split ε hn
  have h2 := sum_rpow_mul_centeredPrefix_eq ε n
  unfold inversionDefect
  linarith

/-- Two-sided bounds on the normalized inversion defect:
`0 ≤ u_{ε,T}(n) + (D^{ζ_ε,≥2} u_{ε,T})(n) ≤ n / √E_T(ε)` for `ε > 0` and `n ≥ 1`. -/
theorem normalizedReceiverProfile_add_properUnitDilation_bounds {ε : ℝ} (hε : 0 < ε) (T : ℕ)
    {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ normalizedReceiverProfile ε T n +
        properUnitDilation ε (normalizedReceiverProfile ε T) n ∧
      normalizedReceiverProfile ε T n +
        properUnitDilation ε (normalizedReceiverProfile ε T) n ≤
        (n : ℝ) / Real.sqrt (dampedMobiusEnergy ε T) := by
  rw [normalizedReceiverProfile_add_properUnitDilation_eq ε T hn]
  have hsqrt : 0 ≤ Real.sqrt (dampedMobiusEnergy ε T) := Real.sqrt_nonneg _
  exact ⟨div_nonneg (inversionDefect_nonneg hε n) hsqrt,
    div_le_div_of_nonneg_right (inversionDefect_le_self hε n) hsqrt⟩

/-- **Homogeneous cofactor relation in the blow-up limit.** At every damping `ε > 0`, either the
receiver is admitted, or along every sub-horizon scale `n_T ≥ 1` with `n_T / √E_T(ε) → 0` (in
particular at every fixed `n ≥ 1`), the normalized receiver profile asymptotically satisfies the
homogeneous cofactor fixed-point equation `u_{ε,T}(n_T) + (D^{ζ_ε,≥2} u_{ε,T})(n_T) → 0`. -/
theorem admits_or_tendsto_normalizedReceiverProfile_add_properUnitDilation_zero {ε : ℝ}
    (hε : 0 < ε) :
    Admits dampedMobiusEnergy ε ∨
      ((∀ n : ℕ, 1 ≤ n →
        Tendsto (fun T => normalizedReceiverProfile ε T n +
          properUnitDilation ε (normalizedReceiverProfile ε T) n) atTop (𝓝 0)) ∧
       (∀ m : ℕ → ℕ, (∀ T, 1 ≤ m T) →
        Tendsto (fun T => (m T : ℝ) / Real.sqrt (dampedMobiusEnergy ε T)) atTop (𝓝 0) →
        Tendsto (fun T => normalizedReceiverProfile ε T (m T) +
          properUnitDilation ε (normalizedReceiverProfile ε T) (m T)) atTop (𝓝 0))) := by
  rcases admits_or_tendsto_atTop ε with h | hE
  · exact Or.inl h
  · have hm : ∀ m : ℕ → ℕ, (∀ T, 1 ≤ m T) →
        Tendsto (fun T => (m T : ℝ) / Real.sqrt (dampedMobiusEnergy ε T)) atTop (𝓝 0) →
        Tendsto (fun T => normalizedReceiverProfile ε T (m T) +
          properUnitDilation ε (normalizedReceiverProfile ε T) (m T)) atTop (𝓝 0) := by
      intro m hm1 hlim
      refine squeeze_zero
        (fun T => (normalizedReceiverProfile_add_properUnitDilation_bounds hε T (hm1 T)).1)
        (fun T => (normalizedReceiverProfile_add_properUnitDilation_bounds hε T (hm1 T)).2)
        hlim
    refine Or.inr ⟨fun n hn => hm (fun _ => n) (fun _ => hn) ?_, hm⟩
    exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hE)

/-- **The normalized self-improving energy identity.** For `ε > 0` and `T ≥ 1`, the unit pronic
energy of `u_{ε,T}` decomposes into its pairing with `ρ_ε / √E_T(ε)` minus its cofactor
auto-correlation `⟪u_{ε,T}, D^{ζ_ε,≥2} u_{ε,T}⟫_T`. -/
theorem normalizedReceiverProfile_selfImproving_identity {ε : ℝ} (hε : 0 < ε) {T : ℕ}
    (hT : 1 ≤ T) :
    1 = pronicPairing T (normalizedReceiverProfile ε T)
          (fun n => inversionDefect ε n / Real.sqrt (dampedMobiusEnergy ε T)) -
        pronicPairing T (normalizedReceiverProfile ε T)
          (properUnitDilation ε (normalizedReceiverProfile ε T)) := by
  have hE : 0 < dampedMobiusEnergy ε T := dampedMobiusEnergy_pos hε hT
  have hsq : Real.sqrt (dampedMobiusEnergy ε T) ^ 2 = dampedMobiusEnergy ε T := Real.sq_sqrt hE.le
  have hid := dampedMobiusEnergy_eq_pairing_sub ε T
  have hp1 : pronicPairing T (normalizedReceiverProfile ε T)
      (fun n => inversionDefect ε n / Real.sqrt (dampedMobiusEnergy ε T)) =
      pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (inversionDefect ε) /
        dampedMobiusEnergy ε T := by
    unfold pronicPairing normalizedReceiverProfile
    rw [sum_div]
    refine sum_congr rfl fun n _ => ?_
    rw [div_mul_div_comm, hsq, div_div]
  have hp2 : pronicPairing T (normalizedReceiverProfile ε T)
      (properUnitDilation ε (normalizedReceiverProfile ε T)) =
      pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (offDiagonalUnitDilation ε) /
        dampedMobiusEnergy ε T := by
    unfold pronicPairing
    rw [sum_div]
    refine sum_congr rfl fun n _ => ?_
    rw [properUnitDilation_normalizedReceiverProfile, normalizedReceiverProfile,
      div_mul_div_comm, hsq, div_div]
  rw [hp1, hp2, ← sub_div, ← hid, div_self hE.ne']

/-- The one-sided normalized self-improving inequality: only the positive part `max u_{ε,T} 0`
contributes to the normalized inversion-defect pairing. -/
theorem normalizedReceiverProfile_posPart_selfImproving_le {ε : ℝ} (hε : 0 < ε) {T : ℕ}
    (hT : 1 ≤ T) :
    1 ≤ pronicPairing T (fun n => max (normalizedReceiverProfile ε T n) 0)
          (fun n => inversionDefect ε n / Real.sqrt (dampedMobiusEnergy ε T)) -
        pronicPairing T (normalizedReceiverProfile ε T)
          (properUnitDilation ε (normalizedReceiverProfile ε T)) := by
  rw [normalizedReceiverProfile_selfImproving_identity hε hT]
  unfold pronicPairing
  refine sub_le_sub_right (Finset.sum_le_sum fun n hn => ?_) _
  have hn1 : 1 ≤ n := (mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    positivity
  have hρ : 0 ≤ inversionDefect ε n / Real.sqrt (dampedMobiusEnergy ε T) :=
    div_nonneg (inversionDefect_nonneg hε n) (Real.sqrt_nonneg _)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hρ) hn0.le

/-- **The finite cofactor head of `u_{ε,T}` is universally bounded.** At any finite cofactor cutoff
`J`, the head `2 ≤ j ≤ J` of the off-diagonal cofactor correlation of `u_{ε,T}` is bounded in
magnitude by `Σ_{j=2}^J j^{−(ε+1/2)}`. -/
theorem abs_pronicPairing_normalizedOffDiagonalHead_le {ε : ℝ} (hε : 0 < ε) (J : ℕ) {T : ℕ}
    (hT : 1 ≤ T) :
    |pronicPairing T (normalizedReceiverProfile ε T)
        (fun n => offDiagonalUnitDilationHead ε J n / Real.sqrt (dampedMobiusEnergy ε T))| ≤
      ∑ j ∈ Icc 2 J, (j : ℝ) ^ (-ε) * (1 / Real.sqrt (j : ℝ)) := by
  have hE : 0 < dampedMobiusEnergy ε T := dampedMobiusEnergy_pos hε hT
  have hsq : Real.sqrt (dampedMobiusEnergy ε T) ^ 2 = dampedMobiusEnergy ε T := Real.sq_sqrt hE.le
  have heq : pronicPairing T (normalizedReceiverProfile ε T)
      (fun n => offDiagonalUnitDilationHead ε J n / Real.sqrt (dampedMobiusEnergy ε T)) =
      pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (offDiagonalUnitDilationHead ε J) /
        dampedMobiusEnergy ε T := by
    unfold pronicPairing normalizedReceiverProfile
    rw [sum_div]
    refine sum_congr rfl fun n _ => ?_
    rw [div_mul_div_comm, hsq, div_div]
  rw [heq, abs_div, abs_of_pos hE, div_le_iff₀ hE]
  exact abs_pronicPairing_offDiagonalHead_le ε J T

/-- The normalized damping tangent `E_ε(n) / √E_T(ε)`. -/
def normalizedTangentProfile (ε : ℝ) (T : ℕ) (n : ℕ) : ℝ :=
  dampedChebyshevError ε n / Real.sqrt (dampedMobiusEnergy ε T)

/-- **Normalized prime-dilation tangent law.** `normalizedTangentProfile ε T` is the prime dilation
`D^{Λ_ε} u_{ε,T}` plus the normalized pole-readout residual, which vanishes at every fixed `n`
under blow-up. -/
theorem normalizedTangentProfile_eq_dilation (ε : ℝ) (T n : ℕ) :
    normalizedTangentProfile ε T n =
      prefixDilation (dampedPrimeWeight ε) (normalizedReceiverProfile ε T) n +
        ((pmPowerDampedDivisorDensity ε).re * dampedPrimeFloorSum ε n -
          dampedReadout ε * (n : ℝ)) / Real.sqrt (dampedMobiusEnergy ε T) := by
  unfold normalizedTangentProfile prefixDilation normalizedReceiverProfile
  rw [dampedChebyshevError_eq_dilation ε n, add_div, sum_div]
  congr 1
  exact sum_congr rfl fun j _ => (mul_div_assoc _ _ _).symm

/-- **Normalized Möbius-dilation tangent factorization.** Every Möbius sign of the normalized
damping tangent sits inside one Möbius dilation `D^{μ_ε}`. -/
theorem normalizedTangentProfile_eq_moebiusDilation (ε : ℝ) (T n : ℕ) :
    normalizedTangentProfile ε T n =
      prefixDilation (dampedMoebiusWeight ε)
          (fun m => (dampedPrimeFloorSum ε m -
            (pmPowerDampedDivisorDensity ε).re *
              ∑ j ∈ Icc 1 m, dampedPrimeWeight ε j * dampedUnitFloorSum ε (m / j)) /
            Real.sqrt (dampedMobiusEnergy ε T)) n +
        ((pmPowerDampedDivisorDensity ε).re * dampedPrimeFloorSum ε n -
          dampedReadout ε * (n : ℝ)) / Real.sqrt (dampedMobiusEnergy ε T) := by
  unfold normalizedTangentProfile prefixDilation
  rw [dampedChebyshevError_eq_moebiusDilation ε n, add_div, sum_div]
  congr 1
  unfold prefixDilation
  exact sum_congr rfl fun j _ => (mul_div_assoc _ _ _).symm

/-! ## §3. Origin-shift data and escape examples in the normalized defect space -/

/-- The origin-shifted normalized profile `u(n + k) = a(n + k) / √(pronicEnergy a (T + k))`. -/
def shiftedNormalizedProfile (a : ℕ → ℝ) (k T n : ℕ) : ℝ :=
  normalizedPronicProfile a (T + k) (n + k)

/-- **Two-sided origin-shift sandwich in the normalized defect space.** For every sequence `a`
with `pronicEnergy a (T + k) > 0`, the pronic energy of `shiftedNormalizedProfile a k T` on
`[1, T]` lies between `1 − E_k / E_{T+k}` and `((k+1)(k+2)/2)(1 − E_k / E_{T+k})`. -/
theorem pronicEnergy_shiftedNormalizedProfile_sandwich (a : ℕ → ℝ) (k : ℕ) {T : ℕ}
    (hE : 0 < pronicEnergy a (T + k)) :
    1 - pronicEnergy a k / pronicEnergy a (T + k) ≤
        pronicEnergy (shiftedNormalizedProfile a k T) T ∧
      pronicEnergy (shiftedNormalizedProfile a k T) T ≤
        ((k : ℝ) + 1) * ((k : ℝ) + 2) / 2 *
          (1 - pronicEnergy a k / pronicEnergy a (T + k)) := by
  have heq : pronicEnergy (shiftedNormalizedProfile a k T) T =
      pronicEnergy (fun n => a (n + k)) T / pronicEnergy a (T + k) := by
    unfold pronicEnergy shiftedNormalizedProfile normalizedPronicProfile
    rw [sum_div]
    refine sum_congr rfl fun n _ => ?_
    rw [div_pow, Real.sq_sqrt hE.le, div_div]
  have h1 := pronicTail_le_pronicEnergy_shift a k T
  have h2 := pronicEnergy_shift_le_tail a k T
  have hsub : (pronicEnergy a (T + k) - pronicEnergy a k) / pronicEnergy a (T + k) =
      1 - pronicEnergy a k / pronicEnergy a (T + k) := by
    rw [sub_div, div_self hE.ne']
  rw [heq]
  constructor
  · rw [← hsub]
    exact div_le_div_of_nonneg_right h1 hE.le
  · rw [← hsub, mul_div_assoc]
    exact div_le_div_of_nonneg_right h2 hE.le

/-- **Origin-tail concentration of the normalized receiver.** At every damping `ε`, either the
receiver is admitted, or for every fixed origin shift `k`, the head fraction
`E_k(ε)/E_{T+k}(ε)` vanishes as `T → ∞` so the tail beyond `k` carries `1 − o(1)` of the pre-shift
energy and the shifted normalized receiver has `liminf ≥ 1` and `limsup ≤ (k+1)(k+2)/2`. -/
theorem admits_or_tendsto_shiftedNormalizedReceiver_head_zero (ε : ℝ) :
    Admits dampedMobiusEnergy ε ∨ ∀ k : ℕ,
      Tendsto (fun T => dampedMobiusEnergy ε k / dampedMobiusEnergy ε (T + k)) atTop (𝓝 0) := by
  rcases admits_or_tendsto_atTop ε with h | hE
  · exact Or.inl h
  · refine Or.inr fun k => ?_
    exact tendsto_const_nhds.div_atTop (hE.comp (tendsto_atTop_add_const_right atTop k tendsto_id))

/-- **The drifted `n^{1/4}` escape profile in the normalized defect space.** Although `quarterPower`
is admitted at a fixed origin, normalizing its translate `quarterPower (· + k)` at any `T ≥ 1`
produces a unit-energy profile in the defect space whose unnormalized energy diverges along every
drift `k_T → ∞` (`tendsto_pronicEnergy_quarterPower_drift`). -/
theorem pronicEnergy_normalizedDriftedQuarterPower_eq_one (k : ℕ) {T : ℕ} (hT : 1 ≤ T) :
    pronicEnergy (normalizedPronicProfile (fun n => quarterPower (n + k)) T) T = 1 := by
  refine pronicEnergy_normalizedPronicProfile _ ?_
  have h1 := sqrt_le_pronicEnergy_quarterPower_shift k hT
  have h2 : 0 < Real.sqrt ((k : ℝ) + 1) / 2 := by positivity
  linarith

/-- The normalized profile of the sign-blind majorant source `majorantCenteredPrefix ε`. -/
def normalizedMajorantProfile (ε : ℝ) (T : ℕ) (n : ℕ) : ℝ :=
  normalizedPronicProfile (majorantCenteredPrefix ε) T n

theorem majorantEnergy_eq_pronicEnergy (ε : ℝ) (T : ℕ) :
    majorantEnergy ε T = pronicEnergy (majorantCenteredPrefix ε) T := rfl

theorem majorantEnergy_pos {ε : ℝ} (hε : 0 < ε) {T : ℕ} (hT : 1 ≤ T) :
    0 < majorantEnergy ε T := by
  have hcell := majorantEnergy_cell_le hε (le_refl 1)
  have h1 : 0 < ((2 : ℝ) ^ (-(1 + ε))) ^ 2 / 2 * ((1 : ℕ) : ℝ) ^ (-(2 * ε)) := by positivity
  have hle : majorantCenteredPrefix ε 1 ^ 2 / (((1 : ℕ) : ℝ) * (((1 : ℕ) : ℝ) + 1)) ≤
      majorantEnergy ε T :=
    single_le_sum (fun n _ => by positivity) (mem_Icc.mpr ⟨le_rfl, hT⟩)
  linarith

/-- **The normalized majorant profile has unit pronic energy, is strictly negative on `[1, T]`, and
escapes every fixed sub-horizon `M` for `0 < ε ≤ ½`.** Because it is strictly negative on all of
`[1, n]`, it violates the positive-average inversion law (`exists_centeredPrefix_ge_of_dilation_law`)
of the actual signed receiver. -/
theorem pronicEnergy_normalizedMajorantProfile_eq_one {ε : ℝ} (hε : 0 < ε) {T : ℕ} (hT : 1 ≤ T) :
    pronicEnergy (normalizedMajorantProfile ε T) T = 1 :=
  pronicEnergy_normalizedPronicProfile _ (majorantEnergy_pos hε hT)

theorem normalizedMajorantProfile_neg {ε : ℝ} (hε : 0 < ε) {T n : ℕ} (hT : 1 ≤ T) (hn : 1 ≤ n) :
    normalizedMajorantProfile ε T n < 0 := by
  unfold normalizedMajorantProfile normalizedPronicProfile
  have hE : 0 < Real.sqrt (pronicEnergy (majorantCenteredPrefix ε) T) :=
    Real.sqrt_pos.mpr (majorantEnergy_pos hε hT)
  have hnum : majorantCenteredPrefix ε n < 0 := by
    have h1 := majorantCenteredPrefix_le hε hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h2 : 0 < (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) := by positivity
    linarith
  exact div_neg_of_neg_of_pos hnum hE

theorem tendsto_pronicEnergy_normalizedMajorantProfile_sub_horizon_zero {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) (M : ℕ) :
    Tendsto (fun T => pronicEnergy (normalizedMajorantProfile ε T) M) atTop (𝓝 0) := by
  have hmono : Monotone (majorantEnergy ε) := pronicEnergy_mono (majorantCenteredPrefix ε)
  have htop : Tendsto (majorantEnergy ε) atTop atTop := by
    refine hmono.tendsto_atTop_atTop fun B => ?_
    by_contra hB
    push Not at hB
    exact not_admits_majorantEnergy hε hε2 ⟨B, fun T => (hB T).le⟩
  have hdiv : Tendsto (fun T => majorantEnergy ε M / majorantEnergy ε T) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop htop
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with T hT
  exact (pronicEnergy_normalizedPronicProfile_sub_horizon _ (majorantEnergy_pos hε hT) M).symm

/-! ## §4. Frequency & cofactor-aliasing profiles in the normalized defect space -/

/-- A logarithmic wave `w_{γ,ω,φ}(n) = n^γ cos(ω log n + φ)` at growth exponent `γ`, logarithmic
frequency `ω` and phase `φ`. -/
def cofactorAliasingWave (γ ω φ : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else (n : ℝ) ^ γ * Real.cos (ω * Real.log n + φ)

@[simp]
theorem cofactorAliasingWave_zero (γ ω φ : ℝ) : cofactorAliasingWave γ ω φ 0 = 0 := by
  simp [cofactorAliasingWave]

/-- **Phase shift under cofactor multiplication.** Along the cofactor lattice `n = j * m` (`j, m ≥ 1`),
`cofactorAliasingWave γ ω φ (j * m) = j^γ · cofactorAliasingWave γ ω (φ + ω log j) m`. -/
theorem cofactorAliasingWave_mul_eq (γ ω φ : ℝ) {j m : ℕ} (hj : 1 ≤ j) (hm : 1 ≤ m) :
    cofactorAliasingWave γ ω φ (j * m) =
      (j : ℝ) ^ γ * cofactorAliasingWave γ ω (φ + ω * Real.log j) m := by
  have hj0 : j ≠ 0 := by omega
  have hm0 : m ≠ 0 := by omega
  have hjm0 : j * m ≠ 0 := Nat.mul_ne_zero hj0 hm0
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold cofactorAliasingWave
  rw [if_neg hjm0, if_neg hm0]
  push_cast
  rw [Real.mul_rpow hjR.le hmR.le, Real.log_mul hjR.ne' hmR.ne']
  ring_nf

/-- **Exact cofactor aliasing at `ω = 2π k / log j`.** When `ω = 2π k / log j` (`j ≥ 2`, `k ∈ ℤ`),
the phase shift `ω log j = 2π k` is a multiple of `2π`, so the logarithmic wave is an exact
eigenmode of the lattice dilation `m ↦ j * m`:
`cofactorAliasingWave γ (2π k / log j) φ (j * m) = j^γ · cofactorAliasingWave γ (2π k / log j) φ m`. -/
theorem cofactorAliasingWave_alias_eigenmode (γ φ : ℝ) {j m : ℕ} (hj : 2 ≤ j) (hm : 1 ≤ m)
    (k : ℤ) :
    cofactorAliasingWave γ (2 * Real.pi * (k : ℝ) / Real.log j) φ (j * m) =
      (j : ℝ) ^ γ * cofactorAliasingWave γ (2 * Real.pi * (k : ℝ) / Real.log j) φ m := by
  have hj1 : 1 ≤ j := by omega
  have hjR : (1 : ℝ) < j := by exact_mod_cast hj
  have hlog : Real.log (j : ℝ) ≠ 0 := (Real.log_pos hjR).ne'
  rw [cofactorAliasingWave_mul_eq γ _ φ hj1 hm]
  congr 1
  unfold cofactorAliasingWave
  have hm0 : m ≠ 0 := by omega
  rw [if_neg hm0, if_neg hm0]
  congr 1
  have hper : 2 * Real.pi * (k : ℝ) / Real.log j * Real.log m +
      (φ + 2 * Real.pi * (k : ℝ) / Real.log j * Real.log j) =
      (2 * Real.pi * (k : ℝ) / Real.log j * Real.log m + φ) + (k : ℝ) * (2 * Real.pi) := by
    rw [div_mul_cancel₀ _ hlog]
    ring
  rw [hper, Real.cos_add_int_mul_two_pi]

/-- A frequency `ω` whose dyadic phase shift `ω log 2` vanishes is identically zero. -/
theorem eq_zero_of_mul_log_two_eq_zero {ω : ℝ} (h : ω * Real.log 2 = 0) : ω = 0 :=
  (mul_eq_zero.mp h).resolve_right (Real.log_pos one_lt_two).ne'

/-- The normalized defect profile of the oscillating smooth-power probe `d^{−ε} cos(t log d)` at
horizon `T`. -/
def normalizedProbeProfile (ε t : ℝ) (T : ℕ) (n : ℕ) : ℝ :=
  normalizedPronicProfile
    (weightCenteredPrefix (oscillatingSmoothPower ε t)
      (∑' d : ℕ, oscillatingSmoothPower ε t d / d)) T n

theorem pronicEnergy_weightCenteredPrefix_eq (c : ℕ → ℝ) (m : ℝ) (T : ℕ) :
    pronicEnergy (weightCenteredPrefix c m) T = weightPronicEnergy c m T := rfl

/-- **Oscillating probe blow-up profiles below half damping.** For `0 < ε < ½`, `t ≠ 0` and
`ζ(1 − ε + i t) ≠ 0`, `normalizedProbeProfile ε t T` eventually has exact unit pronic energy and
its sub-horizon energy up to any fixed `M` vanishes at the polynomial rate `O(T^{−(1−2ε)})`. -/
theorem eventually_pronicEnergy_normalizedProbeProfile_eq_one {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) {t : ℝ} (ht : t ≠ 0)
    (hz : riemannZeta (oscillationExponent ε t) ≠ 0) :
    ∀ᶠ T : ℕ in atTop,
      pronicEnergy (normalizedProbeProfile ε t T) T = 1 := by
  have hρ0 : oscillationExponent ε t ≠ 0 := fun h => by
    have := congrArg Complex.re h
    simp [oscillationExponent] at this
    linarith
  have ha0 : 0 < ‖probeAmp ε t‖ := norm_pos_iff.mpr (div_ne_zero hz hρ0)
  have hγ0 : 0 < 1 - 2 * ε := by linarith
  have hnβ : 1 - 2 * ε < ‖ GaloisForLFunctions.TransHorizonIncidenceMechanics.probeCrossExponent ε t‖ := by
    have hsq : ‖GaloisForLFunctions.TransHorizonIncidenceMechanics.probeCrossExponent ε t‖ ^ 2 =
        (1 - 2 * ε) ^ 2 + (2 * t) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp [GaloisForLFunctions.TransHorizonIncidenceMechanics.probeCrossExponent]
      ring
    have h4 : 0 < (2 * t) ^ 2 := by positivity
    nlinarith [norm_nonneg (GaloisForLFunctions.TransHorizonIncidenceMechanics.probeCrossExponent ε t)]
  have hlam0 : 0 < ‖probeAmp ε t‖ ^ 2 / 4 *
      (1 / (1 - 2 * ε) -
        1 / ‖GaloisForLFunctions.TransHorizonIncidenceMechanics.probeCrossExponent ε t‖) := by
    have : 1 / ‖GaloisForLFunctions.TransHorizonIncidenceMechanics.probeCrossExponent ε t‖ <
        1 / (1 - 2 * ε) := one_div_lt_one_div_of_lt hγ0 hnβ
    have : 0 < ‖probeAmp ε t‖ ^ 2 / 4 := by positivity
    nlinarith
  filter_upwards [eventually_ge_atTop 1, eventually_probeEnergy_le_and_ge hε hε2 ht hz]
    with T hT hE
  refine pronicEnergy_normalizedPronicProfile _ ?_
  rw [pronicEnergy_weightCenteredPrefix_eq]
  have hT0 : (0 : ℝ) < (T : ℝ) ^ (1 - 2 * ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hT) _
  linarith [mul_pos hlam0 hT0, hE.1]

/-- **Spectral energy decomposition of normalized multi-frequency half-damped probe profiles.**
For a finite set `J` of positive frequencies and weights `α_t` whose spectral variance
`V(J, α) = Σ_{t ∈ J} α_t² |ζ(½+it)|² / (2|½+it|²)` is positive, the ratio of each component's
energy to the combined probe energy converges to its exact spectral share in the normalized defect
space:
`E_T(α_t c_t) / E_T(Σ_{s ∈ J} α_s c_s) → (α_t² |ζ(½+it)|² / (2|½+it|²)) / V(J, α)`. -/
theorem tendsto_normalizedHalfProbeCombination_energy_share {J : Finset ℝ}
    (hJ : ∀ t ∈ J, 0 < t) (α : ℝ → ℝ)
    (hV : 0 < ∑ s ∈ J, α s ^ 2 * ‖riemannZeta (oscillationExponent (1 / 2) s)‖ ^ 2 /
      (2 * ‖oscillationExponent (1 / 2) s‖ ^ 2))
    {t : ℝ} (ht : t ∈ J) :
    Tendsto (fun T : ℕ =>
      (α t ^ 2 * weightPronicEnergy (oscillatingSmoothPower (1 / 2) t)
          (∑' d : ℕ, oscillatingSmoothPower (1 / 2) t d / d) T) /
        weightPronicEnergy (halfProbeCombination J α)
          (∑' d : ℕ, halfProbeCombination J α d / d) T) atTop
      (𝓝 ((α t ^ 2 * ‖riemannZeta (oscillationExponent (1 / 2) t)‖ ^ 2 /
          (2 * ‖oscillationExponent (1 / 2) t‖ ^ 2)) /
        (∑ s ∈ J, α s ^ 2 * ‖riemannZeta (oscillationExponent (1 / 2) s)‖ ^ 2 /
          (2 * ‖oscillationExponent (1 / 2) s‖ ^ 2)))) := by
  have ht0 : 0 < t := hJ t ht
  have hnum := (tendsto_probeEnergy_half_div_log ht0.ne').const_mul (α t ^ 2)
  have hden := tendsto_halfProbeCombination_energy_div_log hJ α
  have hquot := hnum.div hden hV.ne'
  rw [mul_div_assoc] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with T hT
  have hlog : Real.log (T : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < T))).ne'
  rw [← mul_div_assoc, div_div_div_cancel_right₀ hlog]

end GaloisForLFunctions.ArithmeticCompensationTheory
