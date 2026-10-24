import GaloisForLFunctions.BezoutValuationIncidence.AllDampingVinogradovKorobovBandAndInteriorGrowth
import GaloisForLFunctions.BezoutValuationIncidence.TheReceiverAndTheColumnsOfTheDampingChain
import GaloisForLFunctions.BezoutValuationIncidence.PronicDualNormOfTheEntranceLaw
import GaloisForLFunctions.BezoutValuationIncidence.DampingWorkAsArithmeticMarkovBoundaryFlux
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampingAverageOfTheRelativeLossSuffices

/-!
# The Damping Chain in Receiver Coordinates, the Size-Bias `h`-Transform, and Paired Markov Work

In `SignedArithmeticEnergyIncidence.TheReceiverIsTheChainOrbitOfTheReciprocal` and
`TheSourceIsTheDampedMoebiusResidueSeries`, the centered arithmetic damping chain `C_η = P_η - e_η`
was shown to map the reciprocal observable `r(k) = 1/(k+1)` to the normalized centered divisor
prefix `(C_η r)(n) = A_η(n+1)/(n+1)`, which expands into the damped Möbius residue-mode series

`(C_η r)(n) = ∑_{d ≥ 1} μ(d) d^{-η} v_d(n)`,   `v_d(n) = ⌊(n+1)/d⌋/(n+1) - 1/d`.

Because backward continuation on `C_η` is ill-posed (`not_backward_stable_l2`), the triangle
inequality `∑_d d^{-η} ‖v_d‖_{ℓ²}` converges only for `η > 1/2` (`summable_signBlind_iff`), and
replacing `μ(d)` by `+1` diverges for all `0 < η ≤ 1/2` (`not_summable_positiveTwin`), any bound on
the chain orbit below half damping must retain the Möbius signs `μ(d)` and the mixed Gram terms
`⟨v_d, v_e⟩`. Likewise, on the pronic space `ℓ²(1/(k(k+1)))`, the unscaled entrance functional is
unbounded below half damping (`not_summable_arithmeticDampingEntrance_pronicDual`), while in
`DampingWorkAsArithmeticMarkovBoundaryFlux` the boundary flux and nonnegative jump energy of the
finite downward-jump generator must remain paired.

This module resolves all three components of the damping-chain programme in receiver coordinates:

1. **Exact Signed Residue-Mode Gram Expansion with Constant Horizon Tail & Unconditional Sub-Half-Damping Bounds (§1):**
   - For every damping `η ∈ ℝ`, modulus cutoff `D ∈ ℕ`, and index `n < D`, every modulus `d > n + 1`
     has `⌊(n+1)/d⌋ = 0`, so `v_d(n) = -1/d` is independent of `n`. Consequently, the finite
     residue-mode prefix `S_{η, D}(n) = ∑_{d ∈ Icc 1 D} μ(d) d^{-η} v_d(n)` differs from the
     normalized centered divisor prefix `A_η(n+1)/(n+1)` by an **exact `n`-independent constant tail**
     (`normalizedCenteredPrefix_eq_residuePartialPrefix_sub_tail`):
     `A_η(n+1)/(n+1) = S_{η, D}(n) + δ_η(D)`,
     where `δ_η(D) = ∑_{d ∈ Icc 1 D} μ(d) d^{-1-η} - ρ_η` is the exact Bézout boundary defect
     `pmBezoutBoundaryDefect η D` from `SignedModulusSumOfTheInteriorMartingale`.
   - Squaring and summing over `n < T` (`T ≤ D`) yields the exact signed residue-mode Gram identity
     (`orbit_partial_energy_eq_residueGram_add_boundaryDefect`), retaining all diagonal (`d = e`)
     and mixed (`d ≠ e`) finite-horizon Gram inner products `G_T(d, e) = ∑_{n < T} v_d(n) v_e(n)`
     together with the exact linear and quadratic boundary-defect drift.
   - Combining this orbit identity with `AllDampingVinogradovKorobovBandAndInteriorGrowth` and
     `TheReceiverAndTheColumnsOfTheDampingChain` yields **unconditional sub-half-damping bounds**
     for both the reciprocal orbit `∑_{n < T} (C_η r)(n)²` and every column `∑_{n < T} C_η(n, k)²`
     uniformly on the Vinogradov–Korobov band `η ∈ [η₀, 1/2]`, `η ≥ 1/2 - κ σ(T)/(480 log T)`
     (`exists_orbit_and_columns_le_on_vinogradovKorobovBand_of_pos`) and with
     `O_η(T^{1-2η} exp(-κ σ(T)/270))` growth at every fixed `0 < η < 1/2`
     (`eventually_orbit_and_columns_le_growth_of_pos`).

2. **The Size-Bias `h`-Transform (`h(k) = 1/(k+1)`) and Pronic-`ℓ²` Hilbert–Schmidt / Poincaré Equivalence (§2):**
   - Conjugating by the reciprocal ground state `h(k) = 1/(k+1)` defines the size-bias `h`-transform
     `(ℋ U)(k) = U(k)/(k+1)` with inverse `(ℋ⁻¹ b)(k) = (k+1) b(k)`, mapping the unit-pronic-norm
     constant ground state `1(k) = 1` (`∑_{k < T} 1/((k+1)(k+2)) = 1 - 1/(T+1)`) to the reciprocal
     observable `r(k) = 1/(k+1)` (`sizeBiasHTransform_const_one`).
   - Unlike the unscaled entrance functional (which diverges on pronic `ℓ²` for `0 < η ≤ 1/2`), the
     `h`-transformed entrance functional `ℰ_η^{(h)}(U) = ∑_k (e_η(k+1)/(k+1)) U(k)` is **bounded on
     the pronic space at every positive damping `η > 0`**
     (`exists_sizeBiasHEntrance_pronicStateEnergy_bound`,
     `summable_sizeBiasHEntrance_mul_of_pronic_summable`).
   - Under the `h`-transform, the centered damping matrix becomes
     `K_η^{(h)}(n, k) = ((n+1)/(k+1)) C_η(n, k)`. It maps the constant ground state `1` to the
     centered divisor prefix `(C_η^{(h)} 1)(n) = A_η(n+1)` with pronic norm squared equal to the
     exact discrete receiver energy `E_T(η)` (`pronicStateEnergy_hTransformed_const_one`), and has
     eigenmodes `V_d(n) = (n+1) v_d(n) = -{(n+1)/d}` with eigenvalue `d^{-η}`.
   - Crucially, dividing column `k` by `k + 1` lowers its column exponent from `(k+1)^{1-2η}` to
     `(k+1)^{-1-2η}`, which is **summable over `k ∈ ℕ` for every `η > 0`**! Consequently, at any
     fixed `η > 0`, receiver admission `η ∈ receiverDampings` is equivalent to:
     (i) the Poincaré / contraction bound for `C_η^{(h)}` on the ground state `1` in pronic `ℓ²`;
     (ii) pronic-`ℓ²` boundedness of the first `h`-transformed column `k = 0`;
     (iii) pronic-`ℓ²` boundedness of every `h`-transformed column `k ∈ ℕ`; and
     (iv) **uniform Hilbert–Schmidt boundedness** `∑_{k=0}^∞ ‖col_k(K_η^{(h)})‖_{pronic, T}² ≤ B`
          from `ℓ²(ℕ)` into `ℓ²_pronic(ℕ)` (`mem_receiverDampings_iff_hTransformed_hilbertSchmidt`).

3. **Exact Integrated Paired Markov Boundary-Flux Balance and Infinite-Horizon Limit (§3):**
   - For the finite downward-jump Markov generator of `DampingWorkAsArithmeticMarkovBoundaryFlux`,
     the paired Markov work
     `W_T^{Markov}(x) = Flux_T(v_x) - Jump_T(v_x) - 2 m(x) ∑_{n=1}^T (n/(n+1)) v_x(n)`
     is continuous on `(0, ∞)` and integrates over any damping interval `0 < δ ≤ η` to the exact
     energy difference (`integral_arithmeticDampingMarkovWork_eq_energy_sub`):
     `∫_δ^η W_T^{Markov}(x) dx = E_T(η) - E_T(δ)`.
   - Rearranging gives the exact integrated dissipation law
     (`integral_jumpEnergy_add_energy_eq_flux_sub_forcing`):
     `∫_δ^η Jump_T(v_x) dx + E_T(η) - E_T(δ) = ∫_δ^η (Flux_T(v_x) - 2 m(x) ∑_{n=1}^T (n/(n+1)) v_x(n)) dx`.
   - For any admitted dampings `δ, η ∈ receiverDampings` (hence unconditionally for all
     `Θ - 1/2 < δ ≤ η` and all `1/2 ≤ δ ≤ η`), the integrated paired Markov work is bounded
     uniformly in the horizon `T` and converges as `T → ∞` to `E_∞(η) - E_∞(δ)`
     (`tendsto_integral_arithmeticDampingMarkovWork_atTop`). Moreover, when `η ∈ receiverDampings`
     and `0 < δ ≤ η`, a horizon-uniform bound on `-∫_δ^η W_T^{Markov}(x) dx` is **necessary and
     sufficient** for `δ ∈ receiverDampings` and is equivalent to `AveragedDampingContinuation δ η`
     (`mem_receiverDampings_iff_integral_markovWork_bound`).
-/

open Finset Filter Topology Real MeasureTheory Set RHTower RHTower.Sieve ArithmeticFunction
open scoped BigOperators ZeroAtInfty
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.SignedArithmeticEnergyIncidence
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Signed Residue-Mode Gram Expansion with Constant Horizon Tail & Sub-Half-Damping Bounds -/

/-- The `d`-th damped Möbius residue-mode term `μ(d) d^{-η} v_d(n)` at damping `η` and index `n`. -/
def dampedMoebiusResidueTerm (η : ℝ) (d n : ℕ) : ℝ :=
  ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η) * normalizedResidueProfile d n

/-- The finite residue-mode prefix at damping `η`, modulus cutoff `D`, and index `n`:
`S_{η, D}(n) = ∑_{d ∈ Icc 1 D} μ(d) d^{-η} v_d(n)`. -/
def residuePartialPrefix (η : ℝ) (D n : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, dampedMoebiusResidueTerm η d n

/-- The exact Bézout boundary defect `δ_η(D) = ∑_{d ∈ Icc 1 D} μ(d) d^{-1-η} - ρ_η` of the finite
residue-mode truncation at modulus cutoff `D`. -/
def dampingBoundaryDefect (η : ℝ) (D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-1 - η) -
    (pmPowerDampedDivisorDensity η).re

/-- The finite-horizon Gram matrix of the normalized residue modes `v_d` and `v_e`:
`G_T(d, e) = ∑_{n < T} v_d(n) v_e(n)`. -/
def residueModeFiniteGram (T d e : ℕ) : ℝ :=
  ∑ n ∈ range T, normalizedResidueProfile d n * normalizedResidueProfile e n

theorem residueModeFiniteGram_comm (T d e : ℕ) :
    residueModeFiniteGram T d e = residueModeFiniteGram T e d := by
  unfold residueModeFiniteGram
  exact sum_congr rfl fun n _ => mul_comm _ _

theorem residueModeFiniteGram_diag_nonneg (T d : ℕ) :
    0 ≤ residueModeFiniteGram T d d :=
  sum_nonneg fun _ _ => mul_self_nonneg _

theorem residueModeFiniteGram_diag_le {d : ℕ} (hd : 0 < d) (T : ℕ) :
    residueModeFiniteGram T d d ≤ 2 / (d : ℝ) := by
  unfold residueModeFiniteGram
  simpa only [sq] using sum_range_sq_normalizedResidueProfile_le hd T

/-- For any `m ≤ D`, summing `μ(d) d^{-η} ⌊m/d⌋` over `d ∈ Icc 1 D` equals the raw divisor prefix
`∑_{k ∈ Icc 1 m} pmPowerDampedDivisorCoeff η k`, because every divisor `d > m` has `⌊m/d⌋ = 0`. -/
private theorem sum_Icc_moebius_rpow_floor_eq_divisorPrefix (η : ℝ) {m D : ℕ} (hmD : m ≤ D) :
    ∑ d ∈ Finset.Icc 1 D, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η) * ((m / d : ℕ) : ℝ) =
      ∑ k ∈ Finset.Icc 1 m, pmPowerDampedDivisorCoeff η k := by
  have htrunc :
      ∑ d ∈ Finset.Icc 1 D, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η) * ((m / d : ℕ) : ℝ) =
        ∑ d ∈ Finset.Icc 1 m, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η) * ((m / d : ℕ) : ℝ) := by
    symm
    refine sum_subset (Finset.Icc_subset_Icc le_rfl hmD) fun d hd hnot => ?_
    have hdm : m < d := by
      rw [Finset.mem_Icc] at hd hnot
      omega
    rw [Nat.div_eq_of_lt hdm]
    simp
  rw [htrunc]
  have hswap := Sieve.sum_divisors_swap m
    (fun d _k => ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η))
  simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] at hswap
  refine (sum_congr rfl fun d _ => by ring).trans hswap.symm

/-- **Exact Constant-Tail Identity for the Finite Residue-Mode Expansion:**
For every `η ∈ ℝ`, modulus cutoff `D ∈ ℕ`, and index `n < D` (so `n + 1 ≤ D`), the normalized
centered divisor prefix `A_η(n+1)/(n+1)` equals the finite residue-mode prefix
`residuePartialPrefix η D n` plus the **`n`-independent** Bézout boundary defect
`dampingBoundaryDefect η D = ∑_{d ∈ Icc 1 D} μ(d) d^{-1-η} - ρ_η`. -/
theorem normalizedCenteredPrefix_eq_residuePartialPrefix_add_boundaryDefect
    (η : ℝ) {D n : ℕ} (hnD : n < D) :
    pmPowerDampedCenteredDivisorPrefix η (n + 1) / ((n : ℝ) + 1) =
      residuePartialPrefix η D n + dampingBoundaryDefect η D := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hterm : ∀ d ∈ Finset.Icc 1 D,
      dampedMoebiusResidueTerm η d n =
        (((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η) * (((n + 1) / d : ℕ) : ℝ)) / ((n : ℝ) + 1) -
          ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-1 - η) := by
    intro d hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hpow : (d : ℝ) ^ (-1 - η) = (d : ℝ) ^ (-η) / (d : ℝ) := by
      rw [show -1 - η = -η - 1 by ring, Real.rpow_sub hd0, Real.rpow_one]
    unfold dampedMoebiusResidueTerm normalizedResidueProfile
    rw [hcast, hpow]
    ring
  unfold residuePartialPrefix dampingBoundaryDefect
  rw [sum_congr rfl hterm, sum_sub_distrib, ← sum_div,
    sum_Icc_moebius_rpow_floor_eq_divisorPrefix η (by omega : n + 1 ≤ D),
    RHTower.pmPowerDampedCenteredDivisorPrefix_eq, hcast]
  field_simp [hn1.ne']
  ring

/-- For `η > 0` and `n < D`, the reciprocal chain orbit `(C_η r)(n)` splits into the finite
residue-mode prefix `residuePartialPrefix η D n` and the constant Bézout boundary defect
`dampingBoundaryDefect η D`. -/
theorem centeredOperator_reciprocal_eq_residuePartialPrefix_add_boundaryDefect
    {η : ℝ} (hη : 0 < η) {D n : ℕ} (hnD : n < D) :
    arithmeticDampingCenteredOperator hη reciprocalObservable n =
      residuePartialPrefix η D n + dampingBoundaryDefect η D := by
  rw [centeredOperator_reciprocal_apply]
  exact normalizedCenteredPrefix_eq_residuePartialPrefix_add_boundaryDefect η hnD

/-- The square of the finite residue-mode prefix summed over `n < T` equals the bilinear Gram form
of the Möbius weights `μ(d) d^{-η}` against `residueModeFiniteGram T d e`. -/
theorem sum_range_residuePartialPrefix_sq_eq_gram (η : ℝ) (D T : ℕ) :
    ∑ n ∈ range T, residuePartialPrefix η D n ^ 2 =
      ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        (((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η)) *
          (((moebius e : ℤ) : ℝ) * (e : ℝ) ^ (-η)) *
          residueModeFiniteGram T d e := by
  have hpt : ∀ n : ℕ,
      residuePartialPrefix η D n ^ 2 =
        ∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
          (((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η)) *
            (((moebius e : ℤ) : ℝ) * (e : ℝ) ^ (-η)) *
            (normalizedResidueProfile d n * normalizedResidueProfile e n) := by
    intro n
    unfold residuePartialPrefix dampedMoebiusResidueTerm
    rw [sq, sum_mul]
    refine sum_congr rfl fun d _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun e _ => by ring
  simp_rw [hpt]
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun e _ => ?_
  unfold residueModeFiniteGram
  rw [← mul_sum]

/-- **Exact Signed Residue-Mode Gram Identity for the Reciprocal Orbit (`T ≤ D`):**
For every `η > 0` and every horizon `T ≤ D`, the partial `ℓ²` energy of the reciprocal chain orbit
`∑_{n < T} (C_η r)(n)²` decomposes identically into the finite signed residue-mode Gram form
(retaining all diagonal `d = e` and mixed `d ≠ e` terms) plus the linear and quadratic drift of the
constant Bézout boundary defect `δ_η(D) = dampingBoundaryDefect η D`. -/
theorem orbit_partial_energy_eq_residueGram_add_boundaryDefect
    {η : ℝ} (hη : 0 < η) {T D : ℕ} (hTD : T ≤ D) :
    ∑ n ∈ range T, arithmeticDampingCenteredOperator hη reciprocalObservable n ^ 2 =
      (∑ d ∈ Finset.Icc 1 D, ∑ e ∈ Finset.Icc 1 D,
        (((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η)) *
          (((moebius e : ℤ) : ℝ) * (e : ℝ) ^ (-η)) *
          residueModeFiniteGram T d e) +
      2 * dampingBoundaryDefect η D *
        (∑ d ∈ Finset.Icc 1 D, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η) *
          ∑ n ∈ range T, normalizedResidueProfile d n) +
      (T : ℝ) * dampingBoundaryDefect η D ^ 2 := by
  have hrew :
      ∑ n ∈ range T, arithmeticDampingCenteredOperator hη reciprocalObservable n ^ 2 =
        ∑ n ∈ range T, (residuePartialPrefix η D n + dampingBoundaryDefect η D) ^ 2 := by
    refine sum_congr rfl fun n hn => ?_
    rw [centeredOperator_reciprocal_eq_residuePartialPrefix_add_boundaryDefect hη
      (lt_of_lt_of_le (mem_range.mp hn) hTD)]
  have hexp :
      ∑ n ∈ range T, (residuePartialPrefix η D n + dampingBoundaryDefect η D) ^ 2 =
        (∑ n ∈ range T, residuePartialPrefix η D n ^ 2) +
          2 * dampingBoundaryDefect η D * (∑ n ∈ range T, residuePartialPrefix η D n) +
          (T : ℝ) * dampingBoundaryDefect η D ^ 2 := by
    have h1 : ∀ n : ℕ,
        (residuePartialPrefix η D n + dampingBoundaryDefect η D) ^ 2 =
          residuePartialPrefix η D n ^ 2 +
            2 * dampingBoundaryDefect η D * residuePartialPrefix η D n +
            dampingBoundaryDefect η D ^ 2 := fun n => by ring
    simp_rw [h1, sum_add_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have hlin :
      ∑ n ∈ range T, residuePartialPrefix η D n =
        ∑ d ∈ Finset.Icc 1 D, ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η) *
          ∑ n ∈ range T, normalizedResidueProfile d n := by
    unfold residuePartialPrefix dampedMoebiusResidueTerm
    rw [sum_comm]
    refine sum_congr rfl fun d _ => ?_
    rw [← mul_sum]
  rw [hrew, hexp, sum_range_residuePartialPrefix_sq_eq_gram, hlin]

/-- **Unconditional Sub-Half-Damping Bounds on the Reciprocal Orbit and Every Chain Column on the
Vinogradov–Korobov Band (`exists_orbit_and_columns_le_on_vinogradovKorobovBand_of_pos`):**
For every damping floor `η₀ ∈ (0, 1/2]`, there exists a horizon-independent constant `B ≥ 0` such
that for every horizon `T ∈ ℕ` and every `η ∈ [η₀, 1/2]` on the Vinogradov–Korobov band
`η ≥ 1/2 - κ σ(T)/(480 log T)` (with `hη : 0 < η`),
1. `∑_{n < T} (C_η r)(n)² ≤ 2 B`, and
2. for every column `k ∈ ℕ`, `∑_{n < T} C_η(n, k)² ≤ 16 (B + ρ_η²) (k + 1)^{1 - 2η}`. -/
theorem exists_orbit_and_columns_le_on_vinogradovKorobovBand_of_pos {η₀ : ℝ} (hη₀ : 0 < η₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (T : ℕ) (η : ℝ) (hη : 0 < η), η₀ ≤ η → η ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ η →
        (∑ n ∈ range T, arithmeticDampingCenteredOperator hη reciprocalObservable n ^ 2 ≤ 2 * B) ∧
        (∀ k : ℕ, ∑ n ∈ range T, arithmeticDampingCenteredRow η n k ^ 2 ≤
          16 * (B + (pmPowerDampedDivisorDensity η).re ^ 2) * ((k : ℝ) + 1) ^ (1 - 2 * η)) := by
  obtain ⟨B, hB0, hB⟩ := exists_receiver_le_on_vinogradovKorobovBand_of_pos hη₀
  refine ⟨B, hB0, fun T η hη hη_ge hη2 hband => ?_⟩
  have hET := hB T η hη_ge hη2 hband
  constructor
  · have horbit :
        ∑ n ∈ range T, arithmeticDampingCenteredOperator hη reciprocalObservable n ^ 2 =
          ∑ n ∈ range T, (pmPowerDampedCenteredDivisorPrefix η (n + 1) / ((n : ℝ) + 1)) ^ 2 :=
      sum_congr rfl fun n _ => by rw [centeredOperator_reciprocal_apply]
    rw [horbit]
    exact (sum_range_div_sq_le_two_mul_pmPowerDampedDivisorDiscreteEnergy η T).trans
      (by linarith)
  · intro k
    exact (sum_range_arithmeticDampingCenteredRow_sq_le hη.le k T).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _))

/-- **Unconditional Sub-Half-Damping Growth of the Reciprocal Orbit and Every Chain Column
(`eventually_orbit_and_columns_le_growth_of_pos`):**
For **every** fixed `0 < η < 1/2`, there exists `C ≥ 0` such that for all sufficiently large `T ∈ ℕ`,
1. `∑_{n < T} (C_η r)(n)² ≤ 2 C T^{1-2η} exp(-κ σ(T)/270)`, and
2. for every column `k ∈ ℕ`,
   `∑_{n < T} C_η(n, k)² ≤ 16 (C T^{1-2η} exp(-κ σ(T)/270) + ρ_η²) (k + 1)^{1 - 2η}`. -/
theorem eventually_orbit_and_columns_le_growth_of_pos {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop,
      (∑ n ∈ range T, arithmeticDampingCenteredOperator hη reciprocalObservable n ^ 2 ≤
        2 * C * (T : ℝ) ^ (1 - 2 * η) * Real.exp (-(vkKappa * vkScale T / 270))) ∧
      (∀ k : ℕ, ∑ n ∈ range T, arithmeticDampingCenteredRow η n k ^ 2 ≤
        16 * (C * (T : ℝ) ^ (1 - 2 * η) * Real.exp (-(vkKappa * vkScale T / 270)) +
          (pmPowerDampedDivisorDensity η).re ^ 2) * ((k : ℝ) + 1) ^ (1 - 2 * η)) := by
  obtain ⟨C, hC0, hC⟩ := eventually_receiver_le_growth_of_pos hη hη2
  refine ⟨C, hC0, ?_⟩
  filter_upwards [hC] with T hET
  constructor
  · have horbit :
        ∑ n ∈ range T, arithmeticDampingCenteredOperator hη reciprocalObservable n ^ 2 =
          ∑ n ∈ range T, (pmPowerDampedCenteredDivisorPrefix η (n + 1) / ((n : ℝ) + 1)) ^ 2 :=
      sum_congr rfl fun n _ => by rw [centeredOperator_reciprocal_apply]
    rw [horbit]
    calc ∑ n ∈ range T, (pmPowerDampedCenteredDivisorPrefix η (n + 1) / ((n : ℝ) + 1)) ^ 2
        ≤ 2 * pmPowerDampedDivisorDiscreteEnergy η T :=
          sum_range_div_sq_le_two_mul_pmPowerDampedDivisorDiscreteEnergy η T
      _ ≤ 2 * (C * (T : ℝ) ^ (1 - 2 * η) * Real.exp (-(vkKappa * vkScale T / 270))) :=
          mul_le_mul_of_nonneg_left hET (by norm_num)
      _ = 2 * C * (T : ℝ) ^ (1 - 2 * η) * Real.exp (-(vkKappa * vkScale T / 270)) := by ring
  · intro k
    exact (sum_range_arithmeticDampingCenteredRow_sq_le hη.le k T).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _))

/-! ## §2. The Size-Bias `h`-Transform and Pronic-`ℓ²` Hilbert–Schmidt / Poincaré Equivalence -/

/-- **The Size-Bias `h`-Transform (`sizeBiasHTransform`):**
Divides a state vector `U : ℕ → ℝ` (at 0-indexed state `k`, corresponding to positive integer
`k + 1`) by `k + 1`: `(ℋ U)(k) = U(k) / (k + 1)`. -/
def sizeBiasHTransform (U : ℕ → ℝ) (k : ℕ) : ℝ :=
  U k / ((k : ℝ) + 1)

/-- **The Inverse Size-Bias `h`-Transform (`sizeBiasHInverse`):**
Multiplies a normalized observable `b : ℕ → ℝ` by `k + 1`: `(ℋ⁻¹ b)(k) = (k + 1) b(k)`. -/
def sizeBiasHInverse (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * b k

@[simp] theorem sizeBiasHTransform_inverse (b : ℕ → ℝ) (k : ℕ) :
    sizeBiasHTransform (sizeBiasHInverse b) k = b k := by
  unfold sizeBiasHTransform sizeBiasHInverse
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  exact mul_div_cancel_left₀ (b k) hk1

@[simp] theorem sizeBiasHInverse_transform (U : ℕ → ℝ) (k : ℕ) :
    sizeBiasHInverse (sizeBiasHTransform U) k = U k := by
  unfold sizeBiasHInverse sizeBiasHTransform
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  exact mul_div_cancel₀ (U k) hk1

/-- The size-bias `h`-transform maps the constant ground state `1` to the reciprocal observable
`r(k) = 1/(k+1)`. -/
@[simp] theorem sizeBiasHTransform_const_one (k : ℕ) :
    sizeBiasHTransform (fun _ => 1) k = reciprocalObservable k := rfl

/-- The 0-indexed finite-horizon pronic energy of a state vector `U : ℕ → ℝ`:
`‖U‖_{pronic, T}² = ∑_{n < T} U(n)² / ((n + 1)(n + 2))`. -/
def pronicStateEnergy (T : ℕ) (U : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range T, U n ^ 2 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

theorem pronicStateEnergy_nonneg (T : ℕ) (U : ℕ → ℝ) :
    0 ≤ pronicStateEnergy T U :=
  sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (by positivity)

/-- **Exact `h`-Transform Norm Identity:**
The pronic state energy of `U` equals the `(n+1)/(n+2)`-weighted `ℓ²` norm of `ℋ U`. -/
theorem pronicStateEnergy_eq_weighted_sizeBiasHTransform (T : ℕ) (U : ℕ → ℝ) :
    pronicStateEnergy T U =
      ∑ n ∈ range T, (((n : ℝ) + 1) / ((n : ℝ) + 2)) * (sizeBiasHTransform U n) ^ 2 := by
  unfold pronicStateEnergy sizeBiasHTransform
  refine sum_congr rfl fun n _ => ?_
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hn1, hn2]

/-- Two-sided equivalence between `pronicStateEnergy T U` and the unweighted `ℓ²` norm of `ℋ U`. -/
theorem pronicStateEnergy_le_sum_sizeBiasHTransform_sq (T : ℕ) (U : ℕ → ℝ) :
    pronicStateEnergy T U ≤ ∑ n ∈ range T, (sizeBiasHTransform U n) ^ 2 := by
  rw [pronicStateEnergy_eq_weighted_sizeBiasHTransform]
  refine sum_le_sum fun n _ => ?_
  have hle : ((n : ℝ) + 1) / ((n : ℝ) + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  exact mul_le_of_le_one_left (sq_nonneg _) hle

theorem sum_sizeBiasHTransform_sq_le_two_mul_pronicStateEnergy (T : ℕ) (U : ℕ → ℝ) :
    ∑ n ∈ range T, (sizeBiasHTransform U n) ^ 2 ≤ 2 * pronicStateEnergy T U := by
  rw [pronicStateEnergy_eq_weighted_sizeBiasHTransform, mul_sum]
  refine sum_le_sum fun n _ => ?_
  have hn2 : (0 : ℝ) < (n : ℝ) + 2 := by positivity
  have hle : 1 ≤ 2 * (((n : ℝ) + 1) / ((n : ℝ) + 2)) := by
    rw [ ← mul_div_assoc, le_div_iff₀ hn2]; linarith
  calc (sizeBiasHTransform U n) ^ 2
      = 1 * (sizeBiasHTransform U n) ^ 2 := (one_mul _).symm
    _ ≤ (2 * (((n : ℝ) + 1) / ((n : ℝ) + 2))) * (sizeBiasHTransform U n) ^ 2 :=
        mul_le_mul_of_nonneg_right hle (sq_nonneg _)
    _ = 2 * ((((n : ℝ) + 1) / ((n : ℝ) + 2)) * (sizeBiasHTransform U n) ^ 2) := by ring

/-- The constant ground state `1(n) = 1` has exact finite-horizon pronic energy `1 - 1/(T+1) ≤ 1`. -/
theorem pronicStateEnergy_const_one (T : ℕ) :
    pronicStateEnergy T (fun _ => 1) = 1 - 1 / ((T : ℝ) + 1) ∧
      pronicStateEnergy T (fun _ => 1) ≤ 1 := by
  have heq : pronicStateEnergy T (fun _ => 1) = 1 - 1 / ((T : ℝ) + 1) := by
    unfold pronicStateEnergy
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, ih]
      have hT1 : (T : ℝ) + 1 ≠ 0 := by positivity
      have hT2 : (T : ℝ) + 2 ≠ 0 := by positivity
      have hcast : ((T + 1 : ℕ) : ℝ) + 1 = (T : ℝ) + 2 := by push_cast; ring
      rw [hcast]
      field_simp [hT1, hT2]
      ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have : (0 : ℝ) ≤ 1 / ((T : ℝ) + 1) := by positivity
  linarith

/-- **Pronic Boundedness of the `h`-Transformed Entrance Functional at Every Positive Damping
(`exists_sizeBiasHEntrance_pronicStateEnergy_bound`):**
While the unscaled entrance functional diverges on the pronic space for `0 < η ≤ 1/2`
(`exists_pronicPairing_gt`), the `h`-transformed entrance functional
`U ↦ ∑_k (e_η(k+1)/(k+1)) U(k) = ∑_k e_η(k+1) (ℋ U)(k)`
is bounded against `pronicStateEnergy T U` at **every** positive damping `η > 0` (including all
`0 < η ≤ 1/2`). -/
theorem exists_sizeBiasHEntrance_pronicStateEnergy_bound {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℕ) (U : ℕ → ℝ),
      |∑ k ∈ range T, (arithmeticDampingEntrance η (k + 1) / ((k : ℝ) + 1)) * U k| ≤
        C * Real.sqrt (pronicStateEnergy T U) := by
  have hsum0 := summable_arithmeticDampingEntrance_reciprocal_pronicDual hη
  have hsum : Summable (fun k : ℕ =>
      (arithmeticDampingEntrance η (k + 1) / ((k : ℝ) + 1)) ^ 2 *
        (((k : ℝ) + 1) * ((k : ℝ) + 2))) := by
    refine ((summable_nat_add_iff 1).mpr hsum0).congr fun k => ?_
    push_cast
    ring_nf
  set D : ℕ → ℝ := fun k =>
    (arithmeticDampingEntrance η (k + 1) / ((k : ℝ) + 1)) ^ 2 *
      (((k : ℝ) + 1) * ((k : ℝ) + 2))
  have hDnn : ∀ k, 0 ≤ D k := fun k => mul_nonneg (sq_nonneg _) (by positivity)
  refine ⟨Real.sqrt (∑' k, D k), Real.sqrt_nonneg _, fun T U => ?_⟩
  set f : ℕ → ℝ := fun k =>
    (arithmeticDampingEntrance η (k + 1) / ((k : ℝ) + 1)) *
      Real.sqrt (((k : ℝ) + 1) * ((k : ℝ) + 2))
  set g : ℕ → ℝ := fun k =>
    U k / Real.sqrt (((k : ℝ) + 1) * ((k : ℝ) + 2))
  have hfg : ∀ k, f k * g k = (arithmeticDampingEntrance η (k + 1) / ((k : ℝ) + 1)) * U k := by
    intro k
    have hw : (0 : ℝ) < ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
    have hne : Real.sqrt (((k : ℝ) + 1) * ((k : ℝ) + 2)) ≠ 0 := (Real.sqrt_pos.mpr hw).ne'
    dsimp [f, g]
    field_simp [hne]
  have hf2 : ∀ k, f k ^ 2 = D k := by
    intro k
    have hw : (0 : ℝ) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
    dsimp [f, D]
    rw [mul_pow, Real.sq_sqrt hw]
  have hg2 : ∀ k, g k ^ 2 = U k ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
    intro k
    have hw : (0 : ℝ) ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
    dsimp [g]
    rw [div_pow, Real.sq_sqrt hw]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range T) f g
  have hA : ∑ k ∈ range T, f k ^ 2 ≤ ∑' k, D k := by
    simpa [hf2] using hsum.sum_le_tsum (range T) fun k _ => hDnn k
  have hAnn : 0 ≤ ∑ k ∈ range T, f k ^ 2 := sum_nonneg fun k _ => sq_nonneg _
  have hsq :
      |∑ k ∈ range T, (arithmeticDampingEntrance η (k + 1) / ((k : ℝ) + 1)) * U k| ≤
        Real.sqrt ((∑ k ∈ range T, f k ^ 2) * ∑ k ∈ range T, g k ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    calc (∑ k ∈ range T, (arithmeticDampingEntrance η (k + 1) / ((k : ℝ) + 1)) * U k) ^ 2
        = (∑ k ∈ range T, f k * g k) ^ 2 := by simp [hfg]
      _ ≤ _ := hcs
  refine hsq.trans ?_
  rw [Real.sqrt_mul hAnn]
  have hg_sum : ∑ k ∈ range T, g k ^ 2 = pronicStateEnergy T U :=
    sum_congr rfl fun k _ => hg2 k
  rw [hg_sum]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hA) (Real.sqrt_nonneg _)

/-- For every `η > 0` and every pronic-square-summable state `U`, the `h`-transformed entrance
series `∑_k (e_η(k+1)/(k+1)) |U(k)|` converges. -/
theorem summable_sizeBiasHEntrance_mul_of_pronic_summable {η : ℝ} (hη : 0 < η)
    {U : ℕ → ℝ} (hU : Summable (fun k : ℕ => U k ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2)))) :
    Summable (fun k : ℕ => (arithmeticDampingEntrance η (k + 1) / ((k : ℝ) + 1)) * |U k|) := by
  obtain ⟨C, hC0, hC⟩ := exists_sizeBiasHEntrance_pronicStateEnergy_bound hη
  have hnn : ∀ k : ℕ, 0 ≤ (arithmeticDampingEntrance η (k + 1) / ((k : ℝ) + 1)) * |U k| := by
    intro k
    have he := arithmeticDampingEntrance_nonneg hη (k + 1)
    positivity
  refine summable_of_sum_range_le hnn (c := C * Real.sqrt (∑' k, U k ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2))))
    fun T => ?_
  have h1 := hC T (fun k => |U k|)
  have habs :
      |∑ k ∈ range T, (arithmeticDampingEntrance η (k + 1) / ((k : ℝ) + 1)) * (|U k|)| =
        ∑ k ∈ range T, (arithmeticDampingEntrance η (k + 1) / ((k : ℝ) + 1)) * (|U k|) :=
    abs_of_nonneg (sum_nonneg fun k _ => hnn k)
  have hpr : pronicStateEnergy T (fun k => |U k|) = pronicStateEnergy T U := by
    unfold pronicStateEnergy
    exact sum_congr rfl fun k _ => by rw [sq_abs]
  rw [habs, hpr] at h1
  refine h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC0)
  exact hU.sum_le_tsum (range T) fun k _ => div_nonneg (sq_nonneg _) (by positivity)

/-- **The `h`-Transformed Centered Damping Matrix (`hTransformedCenteredRow`):**
`K_η^{(h)}(n, k) = ((n + 1) / (k + 1)) C_η(n, k)`. -/
def hTransformedCenteredRow (η : ℝ) (n k : ℕ) : ℝ :=
  (((n : ℝ) + 1) / ((k : ℝ) + 1)) * arithmeticDampingCenteredRow η n k

/-- **The `h`-Transformed Centered Damping Action (`hTransformedCenteredAction`):**
`(C_η^{(h)} U)(n) = ∑'_{k=0}^∞ K_η^{(h)}(n, k) U(k) = (n + 1) ∑'_{k=0}^∞ C_η(n, k) (ℋ U)(k)`. -/
def hTransformedCenteredAction (η : ℝ) (U : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, hTransformedCenteredRow η n k * U k

/-- Exact conjugation identity: for any `b ∈ C₀(ℕ, ℝ)`,
`hTransformedCenteredAction η (sizeBiasHInverse b) n = (sizeBiasHInverse (C_η b)) n`. -/
theorem hTransformedCenteredAction_sizeBiasHInverse {η : ℝ} (hη : 0 < η)
    (b : C₀(ℕ, ℝ)) (n : ℕ) :
    hTransformedCenteredAction η (sizeBiasHInverse b) n =
      sizeBiasHInverse (arithmeticDampingCenteredOperator hη b) n := by
  unfold hTransformedCenteredAction hTransformedCenteredRow sizeBiasHInverse
  rw [arithmeticDampingCenteredOperator_apply, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hk1]

/-- **Ground-State Image of the `h`-Transformed Chain:**
The `h`-transformed centered damping chain maps the constant ground state `1(k) = 1` to the
centered divisor prefix `A_η(n + 1)`. -/
theorem hTransformedCenteredAction_const_one {η : ℝ} (hη : 0 < η) (n : ℕ) :
    hTransformedCenteredAction η (fun _ => 1) n =
      pmPowerDampedCenteredDivisorPrefix η (n + 1) := by
  have h1 : (fun _ : ℕ => (1 : ℝ)) = sizeBiasHInverse reciprocalObservable := by
    funext k
    unfold sizeBiasHInverse
    rw [reciprocalObservable_apply]
    have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
    exact (mul_one_div_cancel hk1).symm
  rw [h1, hTransformedCenteredAction_sizeBiasHInverse hη]
  unfold sizeBiasHInverse
  rw [centeredOperator_reciprocal_apply]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  exact mul_div_cancel₀ _ hn1

/-- **Exact Pronic Norm of the Ground-State Image:**
For every `η > 0` and horizon `T ∈ ℕ`, the pronic state energy of `C_η^{(h)} 1` is **identically**
the discrete receiver energy `E_T(η)`! -/
theorem pronicStateEnergy_hTransformed_const_one {η : ℝ} (hη : 0 < η) (T : ℕ) :
    pronicStateEnergy T (hTransformedCenteredAction η (fun _ => 1)) =
      pmPowerDampedDivisorDiscreteEnergy η T := by
  unfold pronicStateEnergy pmPowerDampedDivisorDiscreteEnergy
  rw [RHTower.sum_Icc_eq_sum_range_shift]
  refine sum_congr rfl fun n _ => ?_
  rw [hTransformedCenteredAction_const_one hη]
  push_cast
  ring_nf

/-- **The `h`-Transformed Residue Eigenmodes (`hTransformedResidueMode`):**
`V_d(n) = (n + 1) v_d(n) = ⌊(n + 1) / d⌋ - (n + 1) / d = -{(n + 1) / d}`. -/
def hTransformedResidueMode (d n : ℕ) : ℝ :=
  sizeBiasHInverse (normalizedResidueMode d) n

/-- The `h`-transformed residue modes `V_d` are eigenvectors of `C_η^{(h)}` with eigenvalue `d^{-η}`. -/
theorem hTransformedCenteredAction_hTransformedResidueMode
    {η : ℝ} (hη : 0 < η) {d : ℕ} (hd : 0 < d) (n : ℕ) :
    hTransformedCenteredAction η (hTransformedResidueMode d) n =
      (d : ℝ) ^ (-η) * hTransformedResidueMode d n := by
  unfold hTransformedResidueMode
  rw [hTransformedCenteredAction_sizeBiasHInverse hη,
    centeredOperator_normalizedResidueMode hη hd]
  unfold sizeBiasHInverse
  simp [ZeroAtInftyContinuousMap.smul_apply, smul_eq_mul]
  ring

/-- **Column Pronic Energy Bound for the `h`-Transformed Chain (`pronicStateEnergy_hTransformed_col_le`):**
For every `η ≥ 0`, column `k ∈ ℕ`, and horizon `T ∈ ℕ`, dividing column `k` by `k + 1` in the
`h`-transform lowers the column growth exponent from `(k + 1)^{1 - 2η}` to `(k + 1)^{-1 - 2η}`:
`pronicStateEnergy T (fun n => hTransformedCenteredRow η n k) ≤ 16 (E_T(η) + ρ_η²) (k + 1)^{-1 - 2η}`. -/
theorem pronicStateEnergy_hTransformed_col_le {η : ℝ} (hη : 0 ≤ η) (k T : ℕ) :
    pronicStateEnergy T (fun n => hTransformedCenteredRow η n k) ≤
      16 * (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) *
        ((k : ℝ) + 1) ^ (-1 - 2 * η) := by
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hle1 := pronicStateEnergy_le_sum_sizeBiasHTransform_sq T
    (fun n => hTransformedCenteredRow η n k)
  have htr : ∀ n : ℕ,
      (sizeBiasHTransform (fun m => hTransformedCenteredRow η m k) n) ^ 2 =
        arithmeticDampingCenteredRow η n k ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    intro n
    unfold sizeBiasHTransform hTransformedCenteredRow
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hn1, hk1.ne']
  simp_rw [htr, ← sum_div] at hle1
  have hcol := sum_range_arithmeticDampingCenteredRow_sq_le hη k T
  have hdiv := div_le_div_of_nonneg_right hcol (sq_nonneg ((k : ℝ) + 1))
  have hpow : ((k : ℝ) + 1) ^ (1 - 2 * η) / ((k : ℝ) + 1) ^ 2 =
      ((k : ℝ) + 1) ^ (-1 - 2 * η) := by
    rw [← Real.rpow_natCast ((k : ℝ) + 1) 2, ← Real.rpow_sub hk1]
    congr 1; push_cast; ring
  calc pronicStateEnergy T (fun n => hTransformedCenteredRow η n k)
      ≤ (∑ n ∈ range T, arithmeticDampingCenteredRow η n k ^ 2) / ((k : ℝ) + 1) ^ 2 := hle1
    _ ≤ (16 * (pmPowerDampedDivisorDiscreteEnergy η T +
          (pmPowerDampedDivisorDensity η).re ^ 2) *
          ((k : ℝ) + 1) ^ (1 - 2 * η)) / ((k : ℝ) + 1) ^ 2 := hdiv
    _ = 16 * (pmPowerDampedDivisorDiscreteEnergy η T +
          (pmPowerDampedDivisorDensity η).re ^ 2) *
          (((k : ℝ) + 1) ^ (1 - 2 * η) / ((k : ℝ) + 1) ^ 2) := by ring
    _ = 16 * (pmPowerDampedDivisorDiscreteEnergy η T +
          (pmPowerDampedDivisorDensity η).re ^ 2) *
          ((k : ℝ) + 1) ^ (-1 - 2 * η) := by rw [hpow]

/-- **Reverse Coercive Bound from the First `h`-Transformed Column (`k = 0`):**
For every `η ≥ 0` and horizon `T ∈ ℕ`, the pronic state energy of the first `h`-transformed column
`n ↦ K_η^{(h)}(n, 0)` bounds the entire discrete receiver energy `E_T(η)`:
`E_T(η) ≤ 48 * pronicStateEnergy T (fun n => hTransformedCenteredRow η n 0) + 24 ρ_η²`. -/
theorem pmPowerDampedDivisorDiscreteEnergy_le_hTransformed_first_col {η : ℝ} (hη : 0 ≤ η) (T : ℕ) :
    pmPowerDampedDivisorDiscreteEnergy η T ≤
      48 * pronicStateEnergy T (fun n => hTransformedCenteredRow η n 0) +
        24 * (pmPowerDampedDivisorDensity η).re ^ 2 := by
  have h1 := pmPowerDampedDivisorDiscreteEnergy_le_first_column_sum hη T
  have h2 := sum_sizeBiasHTransform_sq_le_two_mul_pronicStateEnergy T
    (fun n => hTransformedCenteredRow η n 0)
  have htr : ∀ n : ℕ,
      sizeBiasHTransform (fun m => hTransformedCenteredRow η m 0) n =
        arithmeticDampingCenteredRow η n 0 := by
    intro n
    unfold sizeBiasHTransform hTransformedCenteredRow
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    simp [hn1]
  simp_rw [htr] at h2
  linarith

/-- For every `η > 0` and horizon `T ∈ ℕ`, the column pronic energies of the `h`-transformed chain
are summable over `k ∈ ℕ`, with total Hilbert–Schmidt sum at most
`16 (E_T(η) + ρ_η²) ∑'_{k=0}^∞ (k + 1)^{-1 - 2η}`. -/
theorem summable_and_tsum_pronicStateEnergy_hTransformed_col_le {η : ℝ} (hη : 0 < η) (T : ℕ) :
    Summable (fun k : ℕ => pronicStateEnergy T (fun n => hTransformedCenteredRow η n k)) ∧
      (∑' k : ℕ, pronicStateEnergy T (fun n => hTransformedCenteredRow η n k)) ≤
        16 * (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) *
          ∑' k : ℕ, ((k : ℝ) + 1) ^ (-1 - 2 * η) := by
  have hp : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ (-1 - 2 * η)) := by
    have h0 : Summable (fun m : ℕ => (m : ℝ) ^ (-1 - 2 * η)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    exact ((summable_nat_add_iff 1).mpr h0).congr fun k => by push_cast; rfl
  have hmaj : Summable (fun k : ℕ =>
      16 * (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) *
        ((k : ℝ) + 1) ^ (-1 - 2 * η)) := hp.mul_left _
  have hnn : ∀ k : ℕ, 0 ≤ pronicStateEnergy T (fun n => hTransformedCenteredRow η n k) :=
    fun k => pronicStateEnergy_nonneg T _
  have hle : ∀ k : ℕ, pronicStateEnergy T (fun n => hTransformedCenteredRow η n k) ≤
      16 * (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) *
        ((k : ℝ) + 1) ^ (-1 - 2 * η) :=
    fun k => pronicStateEnergy_hTransformed_col_le hη.le k T
  have hs : Summable (fun k : ℕ => pronicStateEnergy T (fun n => hTransformedCenteredRow η n k)) :=
    Summable.of_nonneg_of_le hnn hle hmaj
  refine ⟨hs, ?_⟩
  calc (∑' k : ℕ, pronicStateEnergy T (fun n => hTransformedCenteredRow η n k))
      ≤ ∑' k : ℕ, 16 * (pmPowerDampedDivisorDiscreteEnergy η T +
          (pmPowerDampedDivisorDensity η).re ^ 2) * ((k : ℝ) + 1) ^ (-1 - 2 * η) :=
        hs.tsum_le_tsum hle hmaj
    _ = 16 * (pmPowerDampedDivisorDiscreteEnergy η T + (pmPowerDampedDivisorDensity η).re ^ 2) *
          ∑' k : ℕ, ((k : ℝ) + 1) ^ (-1 - 2 * η) := tsum_mul_left

/-- **Four-Way Pronic-`ℓ²` Poincaré and Hilbert–Schmidt Equivalence for the `h`-Transformed Chain
(`mem_receiverDampings_iff_hTransformed_hilbertSchmidt`):**
For every `η > 0`, the following are equivalent:
1. `η ∈ receiverDampings`;
2. **Ground-State Poincaré Bound:** `∃ λ ≥ 0, ∀ T, pronicStateEnergy T (C_η^{(h)} 1) ≤ λ`;
3. **First-Column Pronic Bound:** `∃ B₀ ≥ 0, ∀ T, pronicStateEnergy T (col_0(K_η^{(h)})) ≤ B₀`;
4. **Uniform Hilbert–Schmidt Bound (`ℓ²(ℕ) → ℓ²_pronic(ℕ)`):**
   `∃ B ≥ 0, ∀ T, ∑'_{k=0}^∞ pronicStateEnergy T (col_k(K_η^{(h)})) ≤ B`. -/
theorem mem_receiverDampings_iff_hTransformed_hilbertSchmidt {η : ℝ} (hη : 0 < η) :
    (η ∈ receiverDampings ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ ∀ T : ℕ,
        pronicStateEnergy T (hTransformedCenteredAction η (fun _ => 1)) ≤ lam) ∧
    (η ∈ receiverDampings ↔
      ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ T : ℕ,
        pronicStateEnergy T (fun n => hTransformedCenteredRow η n 0) ≤ B₀) ∧
    (η ∈ receiverDampings ↔
      ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℕ,
        (∑' k : ℕ, pronicStateEnergy T (fun n => hTransformedCenteredRow η n k)) ≤ B) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [receiverDampings, Set.mem_setOf_eq, hη, true_and,
      pronicStateEnergy_hTransformed_const_one hη]
    constructor
    · rintro ⟨B, hB⟩
      exact ⟨B, le_trans (pmPowerDampedDivisorDiscreteEnergy_nonneg η 0) (hB 0), hB⟩
    · rintro ⟨lam, _, hlam⟩
      exact ⟨lam, hlam⟩
  · simp only [receiverDampings, Set.mem_setOf_eq, hη, true_and]
    constructor
    · rintro ⟨B, hB⟩
      have hB0 : 0 ≤ B := le_trans (pmPowerDampedDivisorDiscreteEnergy_nonneg η 0) (hB 0)
      refine ⟨16 * (B + (pmPowerDampedDivisorDensity η).re ^ 2), by positivity, fun T => ?_⟩
      have h := pronicStateEnergy_hTransformed_col_le hη.le 0 T
      simp only [Nat.cast_zero, zero_add, Real.one_rpow, mul_one] at h
      exact h.trans (by linarith [hB T])
    · rintro ⟨B₀, _, hB₀⟩
      refine ⟨48 * B₀ + 24 * (pmPowerDampedDivisorDensity η).re ^ 2, fun T => ?_⟩
      linarith [pmPowerDampedDivisorDiscreteEnergy_le_hTransformed_first_col hη.le T, hB₀ T]
  · simp only [receiverDampings, Set.mem_setOf_eq, hη, true_and]
    constructor
    · rintro ⟨B, hB⟩
      have hB0 : 0 ≤ B := le_trans (pmPowerDampedDivisorDiscreteEnergy_nonneg η 0) (hB 0)
      have htsum_nn : 0 ≤ ∑' k : ℕ, ((k : ℝ) + 1) ^ (-1 - 2 * η) :=
        tsum_nonneg fun k => Real.rpow_nonneg (by positivity) _
      refine ⟨16 * (B + (pmPowerDampedDivisorDensity η).re ^ 2) *
        ∑' k : ℕ, ((k : ℝ) + 1) ^ (-1 - 2 * η), by positivity, fun T => ?_⟩
      exact (summable_and_tsum_pronicStateEnergy_hTransformed_col_le hη T).2.trans
        (mul_le_mul_of_nonneg_right (by linarith [hB T]) htsum_nn)
    · rintro ⟨B, _, hB⟩
      refine ⟨48 * B + 24 * (pmPowerDampedDivisorDensity η).re ^ 2, fun T => ?_⟩
      have hs := (summable_and_tsum_pronicStateEnergy_hTransformed_col_le hη T).1
      have h0 : pronicStateEnergy T (fun n => hTransformedCenteredRow η n 0) ≤
          ∑' k : ℕ, pronicStateEnergy T (fun n => hTransformedCenteredRow η n k) := by
        simpa using hs.sum_le_tsum ({0} : Finset ℕ) fun k _ => pronicStateEnergy_nonneg T _
      linarith [pmPowerDampedDivisorDiscreteEnergy_le_hTransformed_first_col hη.le T, h0, hB T]

/-! ## §3. Exact Integrated Paired Markov Boundary-Flux Balance and Infinite-Horizon Limit -/

/-- **The Paired Markov Boundary-Flux Work (`arithmeticDampingMarkovWork`):**
The exact right-hand side of the pronic Markov energy balance
`hasDerivAt_pmPowerDampedDivisorDiscreteEnergy_markov` at damping `x` and horizon `T`:
counting-measure boundary flux, minus nonnegative jump energy, minus density forcing. -/
def arithmeticDampingMarkovWork (x : ℝ) (T : ℕ) : ℝ :=
  arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean x) T -
    arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean x) T -
    2 * dampedReadout x *
      ∑ n ∈ Icc 1 T, ((n : ℝ) / (n + 1)) * arithmeticDampingCenteredMean x n

/-- For every `x > 0` and horizon `T ∈ ℕ`, the paired Markov work `arithmeticDampingMarkovWork x T`
equals `2 * signedDampingWork x T` (`dampedMobiusEnergyDeriv T x`). -/
theorem arithmeticDampingMarkovWork_eq_two_mul_signedDampingWork {x : ℝ} (hx : 0 < x) (T : ℕ) :
    arithmeticDampingMarkovWork x T = 2 * signedDampingWork x T :=
  (two_mul_signedDampingWork_eq_markov hx T).symm

/-- `arithmeticDampingMarkovWork · T` is continuous on `(0, ∞)` and interval-integrable on every
compact interval `[δ, η] ⊂ (0, ∞)`. -/
theorem continuousOn_arithmeticDampingMarkovWork (T : ℕ) :
    ContinuousOn (fun x => arithmeticDampingMarkovWork x T) (Ioi 0) := by
  refine ((continuousOn_signedDampingWork T).const_mul 2).congr fun x hx => ?_
  exact arithmeticDampingMarkovWork_eq_two_mul_signedDampingWork hx T

theorem intervalIntegrable_arithmeticDampingMarkovWork {δ η : ℝ} (hδ : 0 < δ) (hδη : δ ≤ η)
    (T : ℕ) :
    IntervalIntegrable (fun x => arithmeticDampingMarkovWork x T) volume δ η := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hδη]
  exact (continuousOn_arithmeticDampingMarkovWork T).mono fun x hx =>
    mem_Ioi.mpr (lt_of_lt_of_le hδ hx.1)

/-- **Fundamental Theorem of Calculus for the Paired Markov Boundary-Flux Work
(`integral_arithmeticDampingMarkovWork_eq_energy_sub`):**
Over any damping interval `0 < δ ≤ η` and at every horizon `T ∈ ℕ`, the integral of the paired
Markov boundary-flux work equals the exact receiver energy difference `E_T(η) - E_T(δ)`. -/
theorem integral_arithmeticDampingMarkovWork_eq_energy_sub {δ η : ℝ} (hδ : 0 < δ) (hδη : δ ≤ η)
    (T : ℕ) :
    ∫ x in δ..η, arithmeticDampingMarkovWork x T =
      pmPowerDampedDivisorDiscreteEnergy η T - pmPowerDampedDivisorDiscreteEnergy δ T := by
  have hsub : ∀ x ∈ uIcc δ η, 0 < x := by
    rw [uIcc_of_le hδη]
    exact fun x hx => lt_of_lt_of_le hδ hx.1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => hasDerivAt_pmPowerDampedDivisorDiscreteEnergy_markov (hsub x hx) T)
    (intervalIntegrable_arithmeticDampingMarkovWork hδ hδη T)

/-- **Horizon-Uniform Bound and Infinite-Horizon Limit of the Integrated Paired Markov Work
(`tendsto_integral_arithmeticDampingMarkovWork_atTop`):**
Whenever `δ, η ∈ receiverDampings` with `δ ≤ η` (and in particular unconditionally for all
`Θ - 1/2 < δ ≤ η` and all `1/2 ≤ δ ≤ η`), the integrated paired Markov boundary-flux work is
bounded uniformly across all horizons `T ∈ ℕ` and converges as `T → ∞` to the exact infinite-horizon
pronic energy difference `E_∞(η) - E_∞(δ)`. -/
theorem tendsto_integral_arithmeticDampingMarkovWork_atTop {δ η : ℝ}
    (hδ : δ ∈ receiverDampings) (hη : η ∈ receiverDampings) (hδη : δ ≤ η) :
    (∃ M : ℝ, 0 ≤ M ∧ ∀ T : ℕ, |∫ x in δ..η, arithmeticDampingMarkovWork x T| ≤ M) ∧
    Tendsto (fun T : ℕ => ∫ x in δ..η, arithmeticDampingMarkovWork x T) atTop
      (𝓝 ((∑' n : ℕ, pmPowerDampedCenteredDivisorPrefix η (n + 1) ^ 2 /
          (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) -
        (∑' n : ℕ, pmPowerDampedCenteredDivisorPrefix δ (n + 1) ^ 2 /
          (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))))) := by
  have hδ0 : 0 < δ := hδ.1
  obtain ⟨Bδ, hBδ⟩ := hδ.2
  obtain ⟨Bη, hBη⟩ := hη.2
  have hBδ0 : 0 ≤ Bδ := le_trans (pmPowerDampedDivisorDiscreteEnergy_nonneg δ 0) (hBδ 0)
  have hBη0 : 0 ≤ Bη := le_trans (pmPowerDampedDivisorDiscreteEnergy_nonneg η 0) (hBη 0)
  refine ⟨⟨Bη + Bδ, by positivity, fun T => ?_⟩, ?_⟩
  · rw [integral_arithmeticDampingMarkovWork_eq_energy_sub hδ0 hδη T]
    have h1 := pmPowerDampedDivisorDiscreteEnergy_nonneg η T
    have h2 := pmPowerDampedDivisorDiscreteEnergy_nonneg δ T
    have h3 := hBη T
    have h4 := hBδ T
    rw [abs_le]
    constructor <;> linarith
  · have hsum_η : Summable (fun n : ℕ =>
        pmPowerDampedCenteredDivisorPrefix η (n + 1) ^ 2 /
          (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) := by
      refine summable_of_sum_range_le (fun _ => div_nonneg (sq_nonneg _) (by positivity))
        (c := Bη) fun T => ?_
      simpa only [pmPowerDampedDivisorDiscreteEnergy, RHTower.sum_Icc_eq_sum_range_shift] using hBη T
    have hsum_δ : Summable (fun n : ℕ =>
        pmPowerDampedCenteredDivisorPrefix δ (n + 1) ^ 2 /
          (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))) := by
      refine summable_of_sum_range_le (fun _ => div_nonneg (sq_nonneg _) (by positivity))
        (c := Bδ) fun T => ?_
      simpa only [pmPowerDampedDivisorDiscreteEnergy, RHTower.sum_Icc_eq_sum_range_shift] using hBδ T
    have htend_η : Tendsto (fun T : ℕ => pmPowerDampedDivisorDiscreteEnergy η T) atTop
        (𝓝 (∑' n : ℕ, pmPowerDampedCenteredDivisorPrefix η (n + 1) ^ 2 /
          (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)))) := by
      refine hsum_η.hasSum.tendsto_sum_nat.congr fun T => ?_
      simp [pmPowerDampedDivisorDiscreteEnergy, RHTower.sum_Icc_eq_sum_range_shift]
    have htend_δ : Tendsto (fun T : ℕ => pmPowerDampedDivisorDiscreteEnergy δ T) atTop
        (𝓝 (∑' n : ℕ, pmPowerDampedCenteredDivisorPrefix δ (n + 1) ^ 2 /
          (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)))) := by
      refine hsum_δ.hasSum.tendsto_sum_nat.congr fun T => ?_
      simp [pmPowerDampedDivisorDiscreteEnergy, RHTower.sum_Icc_eq_sum_range_shift]
    simpa only [integral_arithmeticDampingMarkovWork_eq_energy_sub hδ0 hδη] using
      htend_η.sub htend_δ

/-- **Equivalence of Receiver Admission, Integrated Paired Markov Work Bound, and Averaged
Damping Continuation (`mem_receiverDampings_iff_integral_markovWork_bound`):**
For any admitted endpoint `η ∈ receiverDampings` and any `0 < δ ≤ η`, the following are equivalent:
1. `δ ∈ receiverDampings`;
2. the negative integrated paired Markov boundary-flux work is bounded uniformly in `T`:
   `∃ C : ℝ, ∀ T : ℕ, -∫ x in δ..η, arithmeticDampingMarkovWork x T ≤ C`;
3. `AveragedDampingContinuation δ η` holds on `[δ, η]`. -/
theorem mem_receiverDampings_iff_integral_markovWork_bound {δ η : ℝ}
    (hδ : 0 < δ) (hδη : δ ≤ η) (hη : η ∈ receiverDampings) :
    (δ ∈ receiverDampings ↔
      ∃ C : ℝ, ∀ T : ℕ, -∫ x in δ..η, arithmeticDampingMarkovWork x T ≤ C) ∧
    (δ ∈ receiverDampings ↔ AveragedDampingContinuation δ η) := by
  obtain ⟨_, Bη, hBη⟩ := hη
  have hBη0 : 0 ≤ Bη := le_trans (pmPowerDampedDivisorDiscreteEnergy_nonneg η 0) (hBη 0)
  refine ⟨?_, ?_⟩
  · constructor
    · rintro ⟨_, Bδ, hBδ⟩
      refine ⟨Bδ, fun T => ?_⟩
      rw [integral_arithmeticDampingMarkovWork_eq_energy_sub hδ hδη T]
      linarith [pmPowerDampedDivisorDiscreteEnergy_nonneg η T, hBδ T]
    · rintro ⟨C, hC⟩
      refine ⟨hδ, Bη + C, fun T => ?_⟩
      have h := hC T
      rw [integral_arithmeticDampingMarkovWork_eq_energy_sub hδ hδη T] at h
      linarith [hBη T]
  · constructor
    · rintro ⟨_, Bδ, hBδ⟩
      have hBδ0 : 0 ≤ Bδ := le_trans (pmPowerDampedDivisorDiscreteEnergy_nonneg δ 0) (hBδ 0)
      rw [AveragedDampingContinuation,
        averagedContinuation_iff_ratio_bound hδη
          (fun ε _ T => dampedMobiusEnergy_nonneg ε T)
          (fun T _ hε => hasDerivAt_dampedMobiusEnergy_deriv (lt_of_lt_of_le hδ hε.1) T)
          (fun T => intervalIntegrable_relativeLoss_dampedMobiusEnergy hδ hδη T)]
      refine ⟨1 + Bδ, fun T => ?_⟩
      have hEη : 0 ≤ dampedMobiusEnergy η T := dampedMobiusEnergy_nonneg η T
      have hEδ : dampedMobiusEnergy δ T ≤ Bδ := hBδ T
      nlinarith
    · intro havg
      have hadm_η : Admits dampedMobiusEnergy η := ⟨Bη, hBη⟩
      have hadm_δ := admits_of_averagedDampingContinuation hδ hδη hadm_η havg
      exact (mem_receiverDampings_iff_admits hδ).mpr hadm_δ

end

end GaloisForLFunctions.BezoutValuationIncidence
