import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HeightUniformVisibilityAndOffLineDensity
import GaloisForLFunctions.SquareRootThreshold.OrderOfTheExplicitVisibilityLags

/-!
# Eliminating the `log γ₀` Turán Tail Factor Without Bounded On-Line Density

In `HeightUniformVisibilityAndOffLineDensity`, the local off-line zero bound
`OffLineCopiesLocallyBounded M` (which constrains only zeros with `Re ρ ≠ ½` in unit height windows
and places **no bound on on-line zero density**) replaced the companion count `P = ⌈80 log(180 Γ)⌉`
by `M` and the core coefficient bound by `2 M (e^{w/2} B_w)²`, but left `log γ₀` / `log Γ` inside:
1. the exponentially-amplified Riemann–von Mangoldt cubic potential tail
   `3840 log(180(|Im z₁| + 6)) ‖D(z₁)‖ e^κ` (`6144 log(180(Γ + 6))`) of the Turán / Fejér
   power-window cluster inequality `zeta_powCluster_le`, `zeta_full_cluster_collapse`, and
   `zeta_partial_elimination_le`;
2. the record-depth condition `2 log(160 log(180 Γ) K₀ / a_w²) ≤ Re z₀ · V` and the phase-coherence
   scale `H₀² ≤ (a_w²/(2e)) / (40 log(180 Γ)) - K₀ / (1 + γ₀)⁴`.

This module eliminates the residual `log γ₀` / `log Γ` factor from the Riemann–von Mangoldt tail of
the Turán inequality and across the entire one-parameter and modulated visibility hierarchy without
any bound on on-line density:

1. **On-line exponential damping and the height-uniform off-line cubic potential (§1)**
   (`exp_sub_sigma_mul_le_one_of_re_nonpos`, `loud_bound_split_offLine`,
   `sum_offLine_inv_cube_le_of_offLineCopiesLocallyBounded`,
   `tsum_offLine_inv_cube_le_of_offLineCopiesLocallyBounded`,
   `zeta_powCluster_le_of_offLineCopiesLocallyBounded`, `clusterBracket_offLine_le`,
   `zeta_partial_elimination_le_of_offLineCopiesLocallyBounded`,
   `zeta_full_cluster_collapse_of_offLineCopiesLocallyBounded`, `xi_ratio_offLine_le`):
   At the shifted evaluation point `s = σ + i Im z₁` with `σ = Re z₁ - κ/V > 0` right of the
   critical line, every on-line zero (`Re z = 0`) and left zero (`Re z < 0`) satisfies
   `(Re z - σ) V ≤ -σ V < 0`, so `e^{(Re z - σ) V} ≤ 1` and
   `‖D(z)‖ (e^{(Re z - σ) V} + 1) ≤ 2 ‖D(z)‖`. Thus on-line zeros contribute **zero** to the
   exponentially-amplified record-loudness cubic potential tail `‖D(z₁)‖ e^κ ∑ ‖z - s‖⁻³`, which runs
   exclusively over strictly off-line right zeros (`Re z > 0`). Under `OffLineCopiesLocallyBounded M`,
   this off-line cubic potential is at most `6 M (1/r³ + 3) ≤ 24 M / r³` uniformly in height,
   replacing `3840 log(180(|Im z₁| + 6))` by `24 M` (`39 M` after dividing by `e^κ - 1`).

2. **Complete elimination of `log Γ` in the one-parameter (`c = 0`) visibility and horizon laws (§2)**
   (`norm_evenCoeff_zero_le_of_near_of_offLineCopiesLocallyBounded`,
   `le_norm_paperFT_of_loud_zero_of_offLineCopiesLocallyBounded`,
   `one_param_record_visible_of_offLineCopiesLocallyBounded`,
   `one_param_record_visible_at_explicit_lag_of_offLineCopiesLocallyBounded`,
   `sqrt_mul_recordScaleOffLine_inv_eq`,
   `one_param_near_top_visible_at_explicit_lag_of_offLineCopiesLocallyBounded`):
   In the unmodulated family `modScaledBump w 0`, the unamplified mass `|M_0| + W ≤ m₀` is already a
   height-independent constant of `w`. Removing the `6144 log(180(Γ + 6))` cubic potential tail and
   bounding off-line multiplicities by `M` eliminates `recordHeightOf w a` and
   `oneParamRecordHeight w η` from every constant and hypothesis. In particular, the phase-coherence
   scale is `H₀(a) = √(a / (2(M + 1)))`, eliminating the super-polynomial coherence drift
   `√a · V(a, σ) → ∞` of `tendsto_sqrt_mul_recordLag`.

3. **Exact off-line/on-line mass decomposition and on-line non-cancellation law (§3)**
   (`onLineEvenMass`, `offLineEvenMass`,
   `tsum_norm_evenCoeff_eq_onLineEvenMass_add_offLineEvenMass`,
   `evenCoeff_modScaledBump_onLine_eq_norm`,
   `two_re_lagStructure_zero_eq_onLineEvenMass_add_offLine`,
   `offLineEvenMass_le_of_offLineCopiesLocallyBounded`):
   For any modulated bump `modScaledBump w c`, the total off-line coefficient mass `offLineEvenMass w c`
   is bounded by `24 M² (e^{w/2} B_w)²` uniformly in `c ∈ ℝ`, while every on-line coefficient
   (`Re z = 0`) is real and nonnegative (`D_c(iγ) = ‖D_c(iγ)‖ ≥ 0`), so on-line zeros in `2 Re S(0)`
   never cancel.

4. **Modulated (`c = γ₀`) visibility in terms of on-line mass and doubly-logarithmic lag (§4)**
   (`norm_evenCoeff_modScaledBump_le_decay_of_offLineCopiesLocallyBounded`,
   `norm_evenCoeff_modScaledBump_center_ge_of_offLineCopiesLocallyBounded`,
   `near_top_record_facts_of_offLineCopiesLocallyBounded`,
   `re_twin_mul_conj_nonneg_of_offLineCopiesLocallyBounded`,
   `zeta_near_top_cluster_collapse_tail_free_of_offLineCopiesLocallyBounded`,
   `zeta_attained_top_visible_log_of_offLineCopiesLocallyBounded`,
   `zeta_near_top_visible_tail_free_of_offLineCopiesLocallyBounded`,
   `zeta_near_top_visible_at_explicit_onLineMass_lag`,
   `zeta_near_top_visible_at_loglog_lag_of_offLineCopiesLocallyBounded`):
   Because the center zero `z₀`, the Legendre record `z₁`, and all core companions are strictly
   off-line (`Re z > 0`), `recordHeightEnvelope w γ₀` disappears from the record depth condition,
   phase coherence, core mass, and cubic potential tail. The modulated visibility lag is therefore
   explicit in `(M, onLineEvenMass w γ₀, Re z₀)` with zero `log γ₀` factor, and substituting the
   unconditional bound `onLineEvenMass w γ₀ = O_w(log γ₀)` (which enters only inside `⌈log₂ Y⌉₊` of
   `explicitOrder`) reduces the visibility lag from `O_w((log γ₀)² log log γ₀ / δ₀ + √(log γ₀))`
   to the doubly-logarithmic scale `O_{w, M}((1 + log log γ₀) / δ₀)`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open PolarSurfaceHodgeIndex TheScalingSurface TheHodgeDefectCountsTheRightZeros
open TheReflectionSectorsOfTheHodgeDefect TheDegreeFiltrationOfTheHodgeDefect
open WhatTheFailureOfTheHodgeIndexMeasures TheVisibilityDegreeOfAnIsolatedPair
open TheVisibilityDegreeOfRightZeros RiemannRochForZAndTheReflectedPrimePolarLedger
open HeightUniformVisibilityAndOffLineDensity
open SquareRootThreshold Zeta23 _root_.RHTower

/-! ### 1. On-line exponential damping and the height-uniform off-line cubic potential -/

/-- **On-line exponential damping at a right-half-plane evaluation point.** For any exponent `z ∈ ℂ`
on or left of the critical line (`Re z ≤ 0`, in particular every on-line zero `Re z = 0`), any
evaluation abscissa `σ > 0`, and any lag `V ≥ 0`, the exponential weight `e^{(Re z - σ) V}` is at
most `1`. -/
theorem exp_sub_sigma_mul_le_one_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) {σ V : ℝ}
    (hσ : 0 < σ) (hV : 0 ≤ V) :
    Real.exp ((z.re - σ) * V) ≤ 1 :=
  Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (by linarith) hV)

/-- **On-line/off-line splitting of the Legendre record loudness bound.** If `z₁` is a right-half-plane
record at lag `V ≥ 0` and `σ = Re z₁ - κ / V > 0`, then for every exponent `z` with `D z ≠ 0`,
`‖D z‖ e^{(Re z - σ) V} ≤ (if 0 < Re z then ‖D z₁‖ e^κ else 0) + ‖D z‖`. In particular, on-line
zeros (`Re z = 0`) and left zeros (`Re z < 0`) contribute `0` to the amplified `‖D z₁‖ e^κ` term. -/
theorem loud_bound_split_offLine {D : ℂ → ℂ} {z₁ : ℂ} {V κ σ : ℝ} (hV : 0 < V)
    (hσdef : σ = z₁.re - κ / V) (hσ : 0 < σ)
    (hrec : ∀ z : ℂ, D z ≠ 0 → 0 < z.re →
      ‖D z‖ * Real.exp (z.re * V) ≤ ‖D z₁‖ * Real.exp (z₁.re * V))
    {z : ℂ} (hz : D z ≠ 0) :
    ‖D z‖ * Real.exp ((z.re - σ) * V) ≤
      (if 0 < z.re then ‖D z₁‖ * Real.exp κ else 0) + ‖D z‖ := by
  by_cases hre : 0 < z.re
  · rw [if_pos hre]
    have h := hrec z hz hre
    have hθV : κ / V * V = κ := div_mul_cancel₀ κ hV.ne'
    have e1 : ‖D z‖ * Real.exp ((z.re - σ) * V) =
        ‖D z‖ * Real.exp (z.re * V) * Real.exp (-σ * V) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; ring
    have e2 : ‖D z₁‖ * Real.exp κ =
        ‖D z₁‖ * Real.exp (z₁.re * V) * Real.exp (-σ * V) := by
      rw [mul_assoc, ← Real.exp_add]; congr 2; rw [hσdef]; linarith [hθV]
    rw [e1, e2]
    have hmul := mul_le_mul_of_nonneg_right h (Real.exp_pos (-σ * V)).le
    linarith [norm_nonneg (D z)]
  · rw [if_neg hre, zero_add]
    push Not at hre
    exact mul_le_of_le_one_right (norm_nonneg (D z))
      (exp_sub_sigma_mul_le_one_of_re_nonpos hre hσ hV.le)

/-- **Height-uniform cubic potential of strictly off-line exponents.** Under
`OffLineCopiesLocallyBounded M` (with no bound on on-line zero density), any finite set `S` of
strictly off-line exponents (`Re z ≠ 0`, `½ + z ∈ zetaZeroConfig.carrier`) at distance `≥ r > 0`
from `s ∈ ℂ` satisfies `∑_{z ∈ S} ‖z - s‖⁻³ ≤ 3 M (1/r³ + 3)`, completely independent of `Im s`. -/
theorem sum_offLine_inv_cube_le_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {s : ℂ} {r : ℝ} (hr : 0 < r) (S : Finset ℂ)
    (hS : ∀ z ∈ S, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ z.re ≠ 0 ∧ r ≤ ‖z - s‖) :
    ∑ z ∈ S, 1 / ‖z - s‖ ^ 3 ≤ 3 * M * (1 / r ^ 3 + 3) := by
  classical
  set j : ℂ → ℤ := fun z => ⌊z.im - s.im⌋ with hj
  set J := S.image j with hJ
  rw [← Finset.sum_fiberwise_of_maps_to (g := j) (t := J) fun z hz => Finset.mem_image_of_mem _ hz]
  have hfib : ∀ k ∈ J, ∑ z ∈ S with j z = k, 1 / ‖z - s‖ ^ 3 ≤
      M * (((|k| : ℝ) + 1) / max r (windowDist k) ^ 3) := by
    intro k _
    set Sk := S.filter fun z => j z = k with hSk
    have hwin : ∀ z ∈ Sk, (k : ℝ) ≤ z.im - s.im ∧ z.im - s.im < k + 1 := fun z hz => by
      rw [hSk, Finset.mem_filter] at hz
      have h1 := Int.floor_le (z.im - s.im)
      have h2 := Int.lt_floor_add_one (z.im - s.im)
      rw [hj] at hz; simp only at hz; rw [hz.2] at *
      exact ⟨by linarith, by linarith⟩
    have hcard_nat : Sk.card ≤ M :=
      card_offLine_window_le_of_offLineCopiesLocallyBounded hM (s.im + k) Sk fun z hz => by
        have hw := hwin z hz
        have hzS := hS z (Finset.mem_filter.mp hz).1
        refine ⟨hzS.1, hzS.2.1, ?_⟩
        rw [abs_le]
        constructor <;> linarith [hw.1, hw.2]
    have hcard : (Sk.card : ℝ) ≤ M * ((|k| : ℝ) + 1) := by
      have h1 : (Sk.card : ℝ) ≤ M := by exact_mod_cast hcard_nat
      have h2 : (1 : ℝ) ≤ (|k| : ℝ) + 1 := by linarith [abs_nonneg (k : ℝ)]
      calc (Sk.card : ℝ) ≤ M * 1 := by linarith
        _ ≤ M * ((|k| : ℝ) + 1) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg M)
    have hterm : ∀ z ∈ Sk, 1 / ‖z - s‖ ^ 3 ≤ 1 / max r (windowDist k) ^ 3 := fun z hz => by
      have hd : windowDist k ≤ ‖z - s‖ := by
        have hw := hwin z hz
        have him : |z.im - s.im| ≤ ‖z - s‖ := by
          have := Complex.abs_im_le_norm (z - s); simpa using this
        refine le_trans ?_ him
        unfold windowDist
        split_ifs with hk
        · have h0 : (0 : ℝ) ≤ k := by exact_mod_cast hk
          rw [abs_of_nonneg (by linarith [hw.1])]; exact hw.1
        · push Not at hk
          have : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast (show k + 1 ≤ 0 by omega)
          rw [abs_of_neg (by linarith)]; linarith
      have hmax : max r (windowDist k) ≤ ‖z - s‖ :=
        max_le (hS z (Finset.mem_filter.mp hz).1).2.2 hd
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
        (pow_le_pow_left₀ (le_max_of_le_left hr.le) hmax 3)
    calc ∑ z ∈ Sk, 1 / ‖z - s‖ ^ 3 ≤ ∑ _z ∈ Sk, 1 / max r (windowDist k) ^ 3 :=
          Finset.sum_le_sum hterm
      _ = Sk.card * (1 / max r (windowDist k) ^ 3) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M * ((|k| : ℝ) + 1)) * (1 / max r (windowDist k) ^ 3) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = M * (((|k| : ℝ) + 1) / max r (windowDist k) ^ 3) := by ring
  calc ∑ k ∈ J, ∑ z ∈ S with j z = k, 1 / ‖z - s‖ ^ 3
      ≤ ∑ k ∈ J, M * (((|k| : ℝ) + 1) / max r (windowDist k) ^ 3) := Finset.sum_le_sum hfib
    _ = M * ∑ k ∈ J, ((|k| : ℝ) + 1) / max r (windowDist k) ^ 3 := by rw [Finset.mul_sum]
    _ ≤ M * (3 * (1 / r ^ 3 + 3)) :=
        mul_le_mul_of_nonneg_left (sum_window_weight_le hr J) (Nat.cast_nonneg M)
    _ = 3 * M * (1 / r ^ 3 + 3) := by ring

/-- **Series form of the height-uniform off-line cubic potential.** Under
`OffLineCopiesLocallyBounded M`, any predicate `p : ℂ → Prop` selecting strictly off-line exponents
(`Re z ≠ 0`, `½ + z ∈ zetaZeroConfig.carrier`) at distance `≥ r > 0` from `s` has summable inverse-cube
potential bounded by `3 M (1/r³ + 3)` uniformly in `Im s`. -/
theorem tsum_offLine_inv_cube_le_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {s : ℂ} {r : ℝ} (hr : 0 < r)
    (p : ℂ → Prop) [DecidablePred p]
    (hp : ∀ z, p z → (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ z.re ≠ 0 ∧ r ≤ ‖z - s‖) :
    Summable (fun z : ℂ => if p z then 1 / ‖z - s‖ ^ 3 else 0) ∧
      ∑' z : ℂ, (if p z then 1 / ‖z - s‖ ^ 3 else 0) ≤ 3 * M * (1 / r ^ 3 + 3) := by
  classical
  have hfin : ∀ u : Finset ℂ, ∑ z ∈ u, (if p z then 1 / ‖z - s‖ ^ 3 else 0) ≤
      3 * M * (1 / r ^ 3 + 3) := fun u => by
    rw [← Finset.sum_filter]
    exact sum_offLine_inv_cube_le_of_offLineCopiesLocallyBounded hM hr _
      fun z hz => hp z (Finset.mem_filter.mp hz).2
  have h0 : ∀ z : ℂ, 0 ≤ (if p z then 1 / ‖z - s‖ ^ 3 else 0) := fun z => by
    split_ifs <;> positivity
  exact ⟨summable_of_sum_le h0 hfin, tsum_le_of_sum_le (summable_of_sum_le h0 hfin) hfin⟩

/-- The height-independent off-line cubic potential `Π_M(r) = 6 M (1/r³ + 3)` replacing
`twinPotential r γ` under `OffLineCopiesLocallyBounded M`. -/
def offLineTwinPotential (M : ℕ) (r : ℝ) : ℝ :=
  6 * M * (1 / r ^ 3 + 3)

/-- For `0 < r ≤ 1`, `offLineTwinPotential M r ≤ 24 M / r³`. -/
theorem offLineTwinPotential_le {M : ℕ} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    offLineTwinPotential M r ≤ 24 * M / r ^ 3 := by
  unfold offLineTwinPotential
  have hr3 : r ^ 3 ≤ 1 := pow_le_one₀ hr.le hr1
  have h1 : (1 : ℝ) ≤ 1 / r ^ 3 := one_le_div (by positivity) |>.mpr hr3
  have h2 : 1 / r ^ 3 + 3 ≤ 4 * (1 / r ^ 3) := by linarith
  calc 6 * (M : ℝ) * (1 / r ^ 3 + 3) ≤ 6 * (M : ℝ) * (4 * (1 / r ^ 3)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 24 * M / r ^ 3 := by ring

/-- Helper: any exponent `z` with `evenCoeff zetaZeroConfig b z ≠ 0` gives a zero `½ + z` in
`zetaZeroConfig.carrier`. -/
theorem add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero {b : ℝ → ℂ} {z : ℂ}
    (hz : evenCoeff zetaZeroConfig b z ≠ 0) :
    (1 / 2 + z) ∈ zetaZeroConfig.carrier := by
  rcases mem_of_evenCoeff_ne_zero hz with h | h
  · exact h
  · have hconj := conj_mem_zetaZeroConfig h
    have e : conj (1 / 2 + conj z) = 1 / 2 + z := by apply Complex.ext <;> simp
    rwa [e] at hconj

/-- **Turán / Fejér power-window cluster inequality for `ζ` without `log γ₀` in the cubic potential
tail.** Under `OffLineCopiesLocallyBounded M` (with no bound on on-line zero density), on-line zeros
(`Re z = 0`) are exponentially damped at `s = (Re z₁ - κ/V) + i Im z₁` and contribute `0` to the
record-loudness cubic potential tail. This replaces `twinPotential r (Im z₁)` in `zeta_powCluster_le`
by the height-independent quantity `offLineTwinPotential M r = 6 M (1/r³ + 3)`. -/
theorem zeta_powCluster_le_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {j : ℕ} (hj : 1 ≤ j) {V : ℝ} (hV : π * j ≤ V)
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hσ : 0 < z₁.re - κ / V) (hr : 0 < r) (hr4 : r ≤ 4)
    (hVr : 4 * π * j ≤ V * r) (S : Finset ℂ)
    (hiso : ∀ z, z ∉ S → evenCoeff zetaZeroConfig b z ≠ 0 →
      r ≤ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖) :
    ‖∑ z ∈ S, evenCoeff zetaZeroConfig b z *
        fejerPowWin j V (z - ((z₁.re - κ / V : ℝ) + z₁.im * I))‖ ≤
      (2 * j).factorial * (π / V) ^ (2 * j) *
        (|2 * (lagStructure zetaZeroConfig b 0).re| *
            (2 / (z₁.re - κ / V) ^ (2 * j + 1) + 2 * (4 / 3) ^ j / 4 ^ (2 * j + 1)) +
          (4 / 3) ^ j * (‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp κ *
              (offLineTwinPotential M r / r ^ (2 * j - 2)) +
            2 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) *
              (1 / 4 ^ (2 * j + 1) + 1 / r ^ (2 * j + 1)))) := by
  classical
  set D := evenCoeff zetaZeroConfig b with hDdef
  set M₀ : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM₀
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set σ : ℝ := z₁.re - κ / V with hσdef
  have hk0 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  set s : ℂ := (σ : ℂ) + z₁.im * I with hs
  have hsre : s.re = σ := by simp [hs]
  have hsim : s.im = z₁.im := by simp [hs]
  set ck : ℝ := (4 / 3) ^ j with hck
  set uk : ℝ := (2 * j).factorial * (π / V) ^ (2 * j) with huk
  have hck0 : 0 < ck := by positivity
  have huk0 : 0 < uk := by positivity
  have hcore := norm_sum_evenCoeff_mul_fejerPowWin_le zetaZeroConfig temperedConfig_zetaZeroConfig
    hb hbs hV0.le j hm S σ z₁.im
  rw [← hs] at hcore
  have hkern : ∀ {z u : ℂ} {d : ℝ}, 0 < d → 4 * π * j ≤ V * d → u.re = σ → D z ≠ 0 →
      d ≤ ‖z - u‖ → ‖D z‖ * ‖fejerPowWin j V (z - u)‖ ≤
        ck * uk * (‖D z₁‖ * Real.exp κ *
            ((if 0 < z.re then 1 / ‖z - u‖ ^ 3 else 0) / d ^ (2 * j - 2)) +
          2 * ‖D z‖ / d ^ (2 * j + 1)) := by
    intro z u d hd hVd hu hz hgap
    have hzu : 0 < ‖z - u‖ := lt_of_lt_of_le hd hgap
    have h4 : 4 * π * j ≤ V * ‖z - u‖ := hVd.trans (mul_le_mul_of_nonneg_left hgap hV0.le)
    have hdec := norm_fejerPowWin_le_decay hV0 j (norm_pos_iff.mp hzu) h4
    rw [Complex.sub_re, hu] at hdec
    have hp1 := one_div_pow_le_cube hd hgap hj
    have hp2 : 1 / ‖z - u‖ ^ (2 * j + 1) ≤ 1 / d ^ (2 * j + 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hd.le hgap _)
    have hl := loud_bound_split_offLine hV0 hσdef hσ hrec hz
    calc ‖D z‖ * ‖fejerPowWin j V (z - u)‖
        ≤ ‖D z‖ * ((4 / 3) ^ j * (2 * j).factorial * (π / V) ^ (2 * j) *
            (Real.exp ((z.re - σ) * V) + 1) / ‖z - u‖ ^ (2 * j + 1)) :=
          mul_le_mul_of_nonneg_left hdec (norm_nonneg _)
      _ = ck * uk * ((‖D z‖ * Real.exp ((z.re - σ) * V) + ‖D z‖) *
            (1 / ‖z - u‖ ^ (2 * j + 1))) := by rw [hck, huk]; field_simp
      _ ≤ ck * uk * (((if 0 < z.re then ‖D z₁‖ * Real.exp κ else 0) + 2 * ‖D z‖) *
            (1 / ‖z - u‖ ^ (2 * j + 1))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          linarith
      _ ≤ ck * uk * (‖D z₁‖ * Real.exp κ *
            ((if 0 < z.re then 1 / ‖z - u‖ ^ 3 else 0) / d ^ (2 * j - 2)) +
            2 * ‖D z‖ / d ^ (2 * j + 1)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [add_mul, show 2 * ‖D z‖ / d ^ (2 * j + 1) = 2 * ‖D z‖ * (1 / d ^ (2 * j + 1)) by
            ring]
          refine add_le_add ?_ (mul_le_mul_of_nonneg_left hp2 (by positivity))
          by_cases hre : 0 < z.re
          · simp only [if_pos hre]
            exact mul_le_mul_of_nonneg_left hp1 (by positivity)
          · simp only [if_neg hre, zero_mul, zero_div, mul_zero, le_rfl]
  have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig hb hbs
  obtain ⟨hs0, hP0b⟩ := tsum_offLine_inv_cube_le_of_offLineCopiesLocallyBounded hM
    (s := (σ : ℂ)) (r := 4) (by norm_num) (fun z => D z ≠ 0 ∧ 0 < z.re)
    fun z hz => ⟨add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hz.1, hz.2.ne',
      (four_le_abs_im_of_evenCoeff_zeta hz.1).trans (by
        have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this)⟩
  obtain ⟨hs1, hP1b⟩ := tsum_offLine_inv_cube_le_of_offLineCopiesLocallyBounded hM
    (s := s) hr (fun z => D z ≠ 0 ∧ 0 < z.re ∧ z ∉ S)
    fun z hz => ⟨add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hz.1, hz.2.1.ne',
      hiso z hz.2.2 hz.1⟩
  set P0 : ℝ := ∑' z : ℂ, (if D z ≠ 0 ∧ 0 < z.re then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) with hP0
  set P1 : ℝ := ∑' z : ℂ, (if D z ≠ 0 ∧ 0 < z.re ∧ z ∉ S then 1 / ‖z - s‖ ^ 3 else 0) with hP1
  have hV4 : 4 * π * j ≤ V * 4 := by linarith
  have hP0_sum : ∑' z : ℂ, ‖D z‖ * ‖fejerPowWin j V (z - σ)‖ ≤
      ck * uk * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * j - 2)) + 2 * W / 4 ^ (2 * j + 1)) := by
    have hle : ∀ z : ℂ, ‖D z‖ * ‖fejerPowWin j V (z - σ)‖ ≤ ck * uk *
        (‖D z₁‖ * Real.exp κ *
          ((if D z ≠ 0 ∧ 0 < z.re then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) / 4 ^ (2 * j - 2)) +
          2 * ‖D z‖ / 4 ^ (2 * j + 1)) := fun z => by
      by_cases hz : D z = 0
      · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, false_and, if_false,
          zero_div, mul_zero, zero_add]
        positivity
      · have h := hkern (by norm_num) hV4 (by simp) hz
          ((four_le_abs_im_of_evenCoeff_zeta hz).trans (by
            have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this))
        by_cases hre : 0 < z.re <;> simp only [hz, not_false_eq_true, hre, and_self, and_false,
          if_true, if_false] at h ⊢ <;> exact h
    have hR : Summable fun z : ℂ => ck * uk *
        (‖D z₁‖ * Real.exp κ *
          ((if D z ≠ 0 ∧ 0 < z.re then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) / 4 ^ (2 * j - 2)) +
          2 * ‖D z‖ / 4 ^ (2 * j + 1)) :=
      (((hs0.div_const _).mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le (fun _ => by positivity) hle) hR).trans
      (le_of_eq ?_)
    rw [tsum_mul_left, Summable.tsum_add ((hs0.div_const _).mul_left _)
      ((hsD.mul_left 2).div_const _), tsum_mul_left, tsum_div_const, tsum_div_const, tsum_mul_left]
  have hP1_sum : ∑' z : ℂ, (if z ∈ S then 0 else ‖D z‖ * ‖fejerPowWin j V (z - s)‖) ≤
      ck * uk * (‖D z₁‖ * Real.exp κ * (P1 / r ^ (2 * j - 2)) + 2 * W / r ^ (2 * j + 1)) := by
    have hle : ∀ z : ℂ, (if z ∈ S then 0 else ‖D z‖ * ‖fejerPowWin j V (z - s)‖) ≤ ck * uk *
        (‖D z₁‖ * Real.exp κ *
          ((if D z ≠ 0 ∧ 0 < z.re ∧ z ∉ S then 1 / ‖z - s‖ ^ 3 else 0) /
          r ^ (2 * j - 2)) + 2 * ‖D z‖ / r ^ (2 * j + 1)) := fun z => by
      by_cases hzS : z ∈ S
      · rw [if_pos hzS]; split_ifs <;> positivity
      · rw [if_neg hzS]
        by_cases hz : D z = 0
        · simp only [hz, norm_zero, zero_mul, ne_eq, not_true_eq_false, false_and, if_false,
            zero_div, mul_zero, zero_add]
          positivity
        · have h := hkern hr hVr hsre hz (hiso z hzS hz)
          by_cases hre : 0 < z.re <;> simp only [hz, hzS, not_false_eq_true, hre, and_self,
            and_false, false_and, if_true, if_false] at h ⊢ <;> exact h
    have hR : Summable fun z : ℂ => ck * uk *
        (‖D z₁‖ * Real.exp κ *
          ((if D z ≠ 0 ∧ 0 < z.re ∧ z ∉ S then 1 / ‖z - s‖ ^ 3 else 0) /
          r ^ (2 * j - 2)) + 2 * ‖D z‖ / r ^ (2 * j + 1)) :=
      (((hs1.div_const _).mul_left _).add ((hsD.mul_left 2).div_const _)).mul_left _
    refine (Summable.tsum_le_tsum hle (hR.of_nonneg_of_le
      (fun _ => by positivity) hle) hR).trans (le_of_eq ?_)
    rw [tsum_mul_left, Summable.tsum_add ((hs1.div_const _).mul_left _)
      ((hsD.mul_left 2).div_const _), tsum_mul_left, tsum_div_const, tsum_div_const, tsum_mul_left]
  have hE1 : ‖fejerPowWin j V (-(σ : ℂ))‖ ≤ uk * (2 / σ ^ (2 * j + 1)) := by
    have := norm_fejerPowWin_neg_le hV0 j hσ
    rw [huk]; refine this.trans (le_of_eq ?_); ring
  have hE2 : ‖fejerPowWin j V (-s)‖ ≤ uk * (2 * ck / 4 ^ (2 * j + 1)) := by
    have h4 : (4 : ℝ) ≤ ‖s‖ := (four_le_abs_im_of_evenCoeff_zeta hz₁).trans (by
      rw [← hsim]; exact Complex.abs_im_le_norm s)
    have hs0' : -s ≠ 0 := fun h => by
      rw [neg_eq_zero] at h; rw [h, norm_zero] at h4; norm_num at h4
    have hdec := norm_fejerPowWin_le_decay hV0 j hs0' (by
      rw [norm_neg]; exact hV4.trans (mul_le_mul_of_nonneg_left h4 hV0.le))
    rw [norm_neg, Complex.neg_re, hsre] at hdec
    refine hdec.trans ?_
    have he : Real.exp (-σ * V) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hσ.le) hV0.le)
    have hpow : (4 : ℝ) ^ (2 * j + 1) ≤ ‖s‖ ^ (2 * j + 1) := pow_le_pow_left₀ (by norm_num) h4 _
    calc (4 / 3) ^ j * ((2 * j).factorial : ℝ) * (π / V) ^ (2 * j) * (Real.exp (-σ * V) + 1) /
          ‖s‖ ^ (2 * j + 1)
        ≤ (4 / 3) ^ j * ((2 * j).factorial : ℝ) * (π / V) ^ (2 * j) * 2 / 4 ^ (2 * j + 1) := by
          gcongr; linarith
      _ = uk * (2 * ck / 4 ^ (2 * j + 1)) := by rw [huk, hck]; ring
  set Pb : ℝ := offLineTwinPotential M r with hPb
  have hPle : P0 + P1 ≤ Pb := by
    have hr4_cube : 1 / (4 : ℝ) ^ 3 ≤ 1 / r ^ 3 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hr.le hr4 3)
    have h0 : P0 ≤ 3 * M * (1 / r ^ 3 + 3) :=
      hP0b.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    rw [hPb, offLineTwinPotential]
    linarith [hP1b]
  have hP0' : 0 ≤ P0 := tsum_nonneg fun z => by split_ifs <;> positivity
  have hr4' : 1 / (4 : ℝ) ^ (2 * j - 2) ≤ 1 / r ^ (2 * j - 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hr.le hr4 _)
  have hPr : P0 / 4 ^ (2 * j - 2) + P1 / r ^ (2 * j - 2) ≤ Pb / r ^ (2 * j - 2) := by
    have h1 : P0 / 4 ^ (2 * j - 2) ≤ P0 / r ^ (2 * j - 2) := by
      rw [div_eq_mul_one_div, div_eq_mul_one_div P0]
      exact mul_le_mul_of_nonneg_left hr4' hP0'
    calc P0 / 4 ^ (2 * j - 2) + P1 / r ^ (2 * j - 2) ≤ P0 / r ^ (2 * j - 2) + P1 / r ^ (2 * j - 2) := by
          linarith
      _ = (P0 + P1) / r ^ (2 * j - 2) := by rw [add_div]
      _ ≤ Pb / r ^ (2 * j - 2) := div_le_div_of_nonneg_right hPle (by positivity)
  have hDe : 0 ≤ ‖D z₁‖ * Real.exp κ := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine hcore.trans ?_
  have h1 : |M₀| * (‖fejerPowWin j V (-(σ : ℂ))‖ + ‖fejerPowWin j V (-s)‖) ≤
      uk * (|M₀| * (2 / σ ^ (2 * j + 1) + 2 * ck / 4 ^ (2 * j + 1))) := by
    calc |M₀| * (‖fejerPowWin j V (-(σ : ℂ))‖ + ‖fejerPowWin j V (-s)‖) ≤
          |M₀| * (uk * (2 / σ ^ (2 * j + 1)) + uk * (2 * ck / 4 ^ (2 * j + 1))) :=
          mul_le_mul_of_nonneg_left (add_le_add hE1 hE2) (abs_nonneg M₀)
      _ = _ := by ring
  have h2 : ck * uk * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * j - 2)) + 2 * W / 4 ^ (2 * j + 1)) +
      ck * uk * (‖D z₁‖ * Real.exp κ * (P1 / r ^ (2 * j - 2)) + 2 * W / r ^ (2 * j + 1)) ≤
      uk * (ck * (‖D z₁‖ * Real.exp κ * (Pb / r ^ (2 * j - 2)) +
        2 * W * (1 / 4 ^ (2 * j + 1) + 1 / r ^ (2 * j + 1)))) := by
    have := mul_le_mul_of_nonneg_left hPr hDe
    have e : ck * uk * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * j - 2)) + 2 * W / 4 ^ (2 * j + 1)) +
        ck * uk * (‖D z₁‖ * Real.exp κ * (P1 / r ^ (2 * j - 2)) + 2 * W / r ^ (2 * j + 1)) =
        uk * (ck * (‖D z₁‖ * Real.exp κ * (P0 / 4 ^ (2 * j - 2) + P1 / r ^ (2 * j - 2)) +
          2 * W * (1 / 4 ^ (2 * j + 1) + 1 / r ^ (2 * j + 1)))) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ huk0.le
    have := mul_le_mul_of_nonneg_left this hck0.le
    linarith
  linarith

/-- **Height-uniform cluster bracket bound.** With `offLineTwinPotential M r`, the cluster bracket
satisfies `n_j ≤ (4/3)^j (4|M₀| + 4W + 24 M D e^κ) / r^{2j+1}` for `j ≥ 1`, `0 < r ≤ min(1, σ)`,
eliminating `3840 log(180(|γ| + 6))`. -/
theorem clusterBracket_offLine_le {M : ℕ} {j : ℕ} (hj : 1 ≤ j) {M₀ W D σ κ r : ℝ}
    (hW : 0 ≤ W) (hD : 0 ≤ D) (hr : 0 < r) (hr1 : r ≤ 1) (hrσ : r ≤ σ) :
    clusterBracket j M₀ W D σ κ r (offLineTwinPotential M r) ≤
      (4 / 3) ^ j * (4 * |M₀| + 4 * W + 24 * M * D * Real.exp κ) / r ^ (2 * j + 1) := by
  unfold clusterBracket
  set t : ℝ := 1 / r ^ (2 * j + 1) with ht
  set cj : ℝ := (4 / 3) ^ j with hcj
  have hcj1 : 1 ≤ cj := one_le_pow₀ (by norm_num)
  have h1 : 2 / σ ^ (2 * j + 1) ≤ 2 * t := by
    rw [ht, mul_one_div]
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hr.le hrσ _)
  have h4 : 1 / (4 : ℝ) ^ (2 * j + 1) ≤ t :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hr.le (by linarith) _)
  have hPu := offLineTwinPotential_le (M := M) hr hr1
  have hPr : offLineTwinPotential M r / r ^ (2 * j - 2) ≤ 24 * M * t := by
    rw [div_le_iff₀ (by positivity), ht]
    refine hPu.trans (le_of_eq ?_)
    rw [show 2 * j + 1 = 3 + (2 * j - 2) by omega, pow_add]
    field_simp
  have hDe : 0 ≤ D * Real.exp κ := mul_nonneg hD (Real.exp_pos _).le
  have hM1 : |M₀| * (2 / σ ^ (2 * j + 1) + 2 * cj / 4 ^ (2 * j + 1)) ≤ |M₀| * (4 * cj * t) := by
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg M₀)
    have h5 : 2 * cj / (4 : ℝ) ^ (2 * j + 1) ≤ 2 * cj * t := by
      rw [show 2 * cj / (4 : ℝ) ^ (2 * j + 1) = 2 * cj * (1 / 4 ^ (2 * j + 1)) by ring]
      exact mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 : 2 * t ≤ 2 * cj * t := by nlinarith [ show 0 < t by positivity ]
    linarith
  have hD1 : cj * (D * Real.exp κ * (offLineTwinPotential M r / r ^ (2 * j - 2))) ≤
      cj * (D * Real.exp κ * (24 * M * t)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPr hDe) (by positivity)
  have hW1 : cj * (2 * W * (1 / 4 ^ (2 * j + 1) + 1 / r ^ (2 * j + 1))) ≤ cj * (2 * W * (2 * t)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by rw [← ht]; linarith) (by positivity))
      (by positivity)
  have e : cj * (4 * |M₀| + 4 * W + 24 * M * D * Real.exp κ) / r ^ (2 * j + 1) =
      |M₀| * (4 * cj * t) + cj * (D * Real.exp κ * (24 * M * t)) + cj * (2 * W * (2 * t)) := by
    rw [ht]; ring
  rw [e, mul_add]
  linarith

/-- **Partial cluster elimination without `log γ₀` in the cubic potential tail.** Under
`OffLineCopiesLocallyBounded M`, eliminating a subset `SL ⊆ S` through the Fejér orders
`k, …, k + |SL|` replaces the `3840 log(180(|Im z₁| + 6)) ‖D(z₁)‖ e^κ` tail in
`zeta_partial_elimination_le` by `24 M ‖D(z₁)‖ e^κ`. -/
theorem zeta_partial_elimination_le_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ}
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hr1 : r ≤ 1) (hrσ : r ≤ z₁.re - κ / V) {k : ℕ}
    (hk : 1 ≤ k) (S SL : Finset ℂ) (hSL : SL ⊆ S)
    (hSr : ∀ z ∈ S, ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ ≤ r)
    (hiso : ∀ z, z ∉ S → evenCoeff zetaZeroConfig b z ≠ 0 →
      r ≤ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖)
    (hV : π * (k + SL.card : ℕ) ≤ V) (hVr : 4 * π * (k + SL.card : ℕ) ≤ V * r) :
    ‖∑ z ∈ S.filter (fun z => z ∉ SL), evenCoeff zetaZeroConfig b z *
        (∏ y ∈ SL, ((y - ((z₁.re - κ / V : ℝ) + z₁.im * I)) ^ 2 -
          (z - ((z₁.re - κ / V : ℝ) + z₁.im * I)) ^ 2)) *
        fejerPowWin (k + SL.card) V (z - ((z₁.re - κ / V : ℝ) + z₁.im * I))‖ ≤
      (2 * (k + SL.card)).factorial * (π / V) ^ (2 * (k + SL.card)) *
        ((8 / 3) ^ SL.card * (4 / 3) ^ k *
          (4 * |2 * (lagStructure zetaZeroConfig b 0).re| +
            4 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) +
            24 * M * ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp κ) / r ^ (2 * k + 1)) := by
  classical
  set D := evenCoeff zetaZeroConfig b with hDdef
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  set p := SL.card with hp
  set M₀ : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM₀
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set Ξ : ℝ := 4 * |M₀| + 4 * W + 24 * M * ‖D z₁‖ * Real.exp κ with hΞ
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
  have hΞ0 : 0 ≤ Ξ := by rw [hΞ]; positivity
  have hσ : 0 < z₁.re - κ / V := lt_of_lt_of_le hr hrσ
  set x : ℂ → ℂ := fun z => z - s with hx
  have hA : ∀ m' : ℕ, k ≤ m' → m' ≤ k + p → ‖elimSeq V S D x [] m'‖ ≤
      (2 * m').factorial * (π / V) ^ (2 * m') * ((4 / 3) ^ m' * Ξ / r ^ (2 * m' + 1)) := by
    intro m' h1 h2
    have hm1 : 1 ≤ m' := le_trans hk h1
    have hm'r : (m' : ℝ) ≤ (k + p : ℕ) := by exact_mod_cast h2
    have hcl := zeta_powCluster_le_of_offLineCopiesLocallyBounded hM hb hbs (j := m') hm1
      (by nlinarith [Real.pi_pos]) hm hz₁ hrec hκ hσ hr (by linarith) (by nlinarith [Real.pi_pos])
      S hiso
    have hbr := clusterBracket_offLine_le (M := M) (j := m') hm1 (M₀ := M₀) (W := W)
      (D := ‖D z₁‖) (κ := κ) hW0 (norm_nonneg _) hr hr1 hrσ
    have e : elimSeq V S D x [] m' = ∑ z ∈ S, D z * fejerPowWin m' V (z - s) := by
      simp [elimSeq, hx]
    rw [e]
    exact hcl.trans (mul_le_mul_of_nonneg_left hbr (by positivity))
  set ys : List ℂ := SL.toList.map fun z => x z ^ 2 with hys
  have hlen : ys.length = p := by rw [hys, List.length_map, Finset.length_toList]
  have hysr : ∀ y ∈ ys, ‖y‖ ≤ r ^ 2 := by
    intro y hy
    rw [hys, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Finset.mem_toList] at hz
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hSr z (hSL hz)) 2
  have hΦ := norm_elimSeq_le hV0 hr hΞ0 S D x ys k hysr (by rw [hlen]; exact hVr)
    (fun m' h1 h2 => hA m' h1 (by rw [hlen] at h2; exact h2))
  rw [hlen] at hΦ
  have hprod : ∀ z, ((SL.toList.map fun z => x z ^ 2).map fun y => y - x z ^ 2).prod =
      ∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2) := fun z => by
    rw [List.map_map]; exact Finset.prod_map_toList _ _
  have hval : elimSeq V S D x ys k = ∑ z ∈ S.filter (fun z => z ∉ SL),
      D z * (∏ y ∈ SL, (x y ^ 2 - x z ^ 2)) * fejerPowWin (k + p) V (x z) := by
    unfold elimSeq
    rw [hlen, hys]
    simp_rw [hprod]
    rw [← Finset.sum_filter_add_sum_filter_not S (fun z => z ∈ SL)]
    have h0 : ∑ z ∈ S.filter (fun z => z ∈ SL),
        D z * (∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2)) * fejerPowWin (k + p) V (x z) = 0 :=
      Finset.sum_eq_zero fun z hz => by
        have : ∏ z' ∈ SL, (x z' ^ 2 - x z ^ 2) = 0 :=
          Finset.prod_eq_zero (f := fun z' => x z' ^ 2 - x z ^ 2) (Finset.mem_filter.mp hz).2
            (sub_self _)
        rw [this, mul_zero, zero_mul]
    rw [h0, zero_add]
  rwa [hval] at hΦ

/-- **Full cluster elimination without `log γ₀` in the cubic potential tail.** Under
`OffLineCopiesLocallyBounded M`, eliminating all companions of `z₁` in `S` replaces
`3840 log(180(|Im z₁| + 6)) ‖D(z₁)‖ e^κ` in `zeta_full_cluster_collapse` by
`24 M ‖D(z₁)‖ e^κ`. -/
theorem zeta_full_cluster_collapse_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ}
    (hm : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump b v (-1)) (twoBump b v (-1))).re)
    {z₁ : ℂ} (hz₁ : evenCoeff zetaZeroConfig b z₁ ≠ 0)
    (hrec : ∀ z : ℂ, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V))
    {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hr1 : r ≤ 1) (hrσ : r ≤ z₁.re - κ / V) {k : ℕ}
    (hk : 1 ≤ k) (S : Finset ℂ) (hz₁S : z₁ ∈ S)
    (hSr : ∀ z ∈ S, ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖ ≤ r)
    (hiso : ∀ z, z ∉ S → evenCoeff zetaZeroConfig b z ≠ 0 →
      r ≤ ‖z - ((z₁.re - κ / V : ℝ) + z₁.im * I)‖)
    (hV : π * (k + (S.erase z₁).card : ℕ) ≤ V) (hVr : 4 * π * (k + (S.erase z₁).card : ℕ) ≤ V * r)
    {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ z ∈ S.erase z₁, ε ≤ ‖(z - ((z₁.re - κ / V : ℝ) + z₁.im * I)) + ((κ / V : ℝ) : ℂ)‖) :
    ‖evenCoeff zetaZeroConfig b z₁‖ * (∏ z ∈ S.erase z₁, ‖z - z₁‖) * ε ^ (S.erase z₁).card *
        ‖fejerPowWin (k + (S.erase z₁).card) V ((κ / V : ℝ) : ℂ)‖ ≤
      (2 * (k + (S.erase z₁).card)).factorial * (π / V) ^ (2 * (k + (S.erase z₁).card)) *
        ((8 / 3) ^ (S.erase z₁).card * (4 / 3) ^ k *
          (4 * |2 * (lagStructure zetaZeroConfig b 0).re| +
            4 * (∑' z : ℂ, ‖evenCoeff zetaZeroConfig b z‖) +
            24 * M * ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp κ) / r ^ (2 * k + 1)) := by
  classical
  set D := evenCoeff zetaZeroConfig b with hDdef
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  set SL := S.erase z₁ with hSL
  set p := SL.card with hp
  set M₀ : ℝ := 2 * (lagStructure zetaZeroConfig b 0).re with hM₀
  set W : ℝ := ∑' z : ℂ, ‖D z‖ with hW
  set Ξ : ℝ := 4 * |M₀| + 4 * W + 24 * M * ‖D z₁‖ * Real.exp κ with hΞ
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hV0 : 0 < V := lt_of_lt_of_le (by positivity) hV
  have hW0 : 0 ≤ W := tsum_nonneg fun z => norm_nonneg _
  have hΞ0 : 0 ≤ Ξ := by rw [hΞ]; positivity
  have hσ : 0 < z₁.re - κ / V := lt_of_lt_of_le hr hrσ
  set x : ℂ → ℂ := fun z => z - s with hx
  have hA : ∀ m' : ℕ, k ≤ m' → m' ≤ k + p → ‖elimSeq V S D x [] m'‖ ≤
      (2 * m').factorial * (π / V) ^ (2 * m') * ((4 / 3) ^ m' * Ξ / r ^ (2 * m' + 1)) := by
    intro m' h1 h2
    have hm1 : 1 ≤ m' := le_trans hk h1
    have hm'r : (m' : ℝ) ≤ (k + p : ℕ) := by exact_mod_cast h2
    have hcl := zeta_powCluster_le_of_offLineCopiesLocallyBounded hM hb hbs (j := m') hm1
      (by nlinarith [Real.pi_pos]) hm hz₁ hrec hκ hσ hr (by linarith) (by nlinarith [Real.pi_pos])
      S hiso
    have hbr := clusterBracket_offLine_le (M := M) (j := m') hm1 (M₀ := M₀) (W := W)
      (D := ‖D z₁‖) (κ := κ) hW0 (norm_nonneg _) hr hr1 hrσ
    have e : elimSeq V S D x [] m' = ∑ z ∈ S, D z * fejerPowWin m' V (z - s) := by
      simp [elimSeq, hx]
    rw [e]
    exact hcl.trans (mul_le_mul_of_nonneg_left hbr (by positivity))
  set ys : List ℂ := SL.toList.map fun z => x z ^ 2 with hys
  have hlen : ys.length = p := by rw [hys, List.length_map, Finset.length_toList]
  have hysr : ∀ y ∈ ys, ‖y‖ ≤ r ^ 2 := by
    intro y hy
    rw [hys, List.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Finset.mem_toList, hSL, Finset.mem_erase] at hz
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hSr z hz.2) 2
  have hΦ := norm_elimSeq_le hV0 hr hΞ0 S D x ys k hysr (by rw [hlen]; exact hVr)
    (fun m' h1 h2 => hA m' h1 (by rw [hlen] at h2; exact h2))
  rw [hlen] at hΦ
  have hz₁L : z₁ ∉ SL := Finset.notMem_erase z₁ S
  have hdecomp := elimSeq_eq_record_add V S SL D x hz₁S hz₁L k
  rw [← hys] at hdecomp
  have hR : (S.filter fun z => z ∉ SL).erase z₁ = ∅ := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_filter, hSL, Finset.notMem_empty, iff_false, not_and]
    intro h1 h2 h3
    exact h3 h1 h2
  rw [hR, Finset.sum_empty, add_zero] at hdecomp
  have hx₁ : x z₁ = ((κ / V : ℝ) : ℂ) := by
    simp only [hx]; apply Complex.ext <;> simp [hs]
  have hprod : (∏ z ∈ SL, ‖z - z₁‖) * ε ^ p ≤ ‖∏ z' ∈ SL, (x z' ^ 2 - x z₁ ^ 2)‖ := by
    rw [norm_prod, hp, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun _ _ => by positivity) fun z hz => ?_
    have e : x z ^ 2 - x z₁ ^ 2 = (z - z₁) * (x z + ((κ / V : ℝ) : ℂ)) := by
      rw [hx₁]; simp only [hx]
      have : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
      linear_combination (z - s + ((κ / V : ℝ) : ℂ)) * this
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_left (hε z hz) (norm_nonneg _)
  have hrecn := congrArg norm hdecomp
  rw [norm_mul, norm_mul, hx₁] at hrecn
  rw [hx₁] at hprod
  calc ‖D z₁‖ * (∏ z ∈ SL, ‖z - z₁‖) * ε ^ p * ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖
      = ‖D z₁‖ * ((∏ z ∈ SL, ‖z - z₁‖) * ε ^ p) * ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
        ring
    _ ≤ ‖D z₁‖ * ‖∏ z' ∈ SL, (x z' ^ 2 - ((κ / V : ℝ) : ℂ) ^ 2)‖ *
          ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by gcongr
    _ = ‖elimSeq V S D x ys k‖ := hrecn.symm
    _ ≤ _ := hΦ

/-- **Noise-to-record ratio without `log γ₀`.** For `κ ≥ 1`, `D ≥ ε₀ > 0`, `W ≥ 0`, and
`|M₀| + W ≤ m₀`, the off-line noise bracket `4|M₀| + 4W + 24 M D e^κ` satisfies
`4|M₀| + 4W + 24 M D e^κ ≤ (4 m₀ / ((e - 1) ε₀) + 39 M) (D (e^κ - 1))` (with `24 · (8/5) ≤ 39`). -/
theorem xi_ratio_offLine_le {M : ℕ} {M₀ W D κ ε₀ m₀ : ℝ} (hκ : 1 ≤ κ) (hε₀ : 0 < ε₀)
    (hD : ε₀ ≤ D) (hW : 0 ≤ W) (hMW : |M₀| + W ≤ m₀) :
    4 * |M₀| + 4 * W + 24 * M * D * Real.exp κ ≤
      (4 * m₀ / ((Real.exp 1 - 1) * ε₀) + 39 * M) * (D * (Real.exp κ - 1)) := by
  have he1 : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hE1 : Real.exp 1 - 1 ≤ Real.exp κ - 1 := by linarith [Real.exp_le_exp.mpr hκ]
  have hD0 : 0 < D := lt_of_lt_of_le hε₀ hD
  have hm00 : 0 ≤ m₀ := le_trans (add_nonneg (abs_nonneg M₀) hW) hMW
  have hratio : Real.exp κ ≤ 8 / 5 * (Real.exp κ - 1) := by
    have : (8 : ℝ) / 3 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    linarith
  have hm1 : 4 * |M₀| + 4 * W ≤ 4 * m₀ / ((Real.exp 1 - 1) * ε₀) * (D * (Real.exp κ - 1)) := by
    have h1 : ε₀ * (Real.exp 1 - 1) ≤ D * (Real.exp κ - 1) :=
      mul_le_mul hD hE1 he1.le hD0.le
    have e : 4 * m₀ / ((Real.exp 1 - 1) * ε₀) * (ε₀ * (Real.exp 1 - 1)) = 4 * m₀ := by
      field_simp
    have h2 : 0 ≤ 4 * m₀ / ((Real.exp 1 - 1) * ε₀) := by positivity
    have := mul_le_mul_of_nonneg_left h1 h2
    linarith
  have hm2 : 24 * (M : ℝ) * D * Real.exp κ ≤ 39 * M * (D * (Real.exp κ - 1)) := by
    have h1 := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 24 * (M : ℝ) * D by positivity)
    have h2 : 0 ≤ (M : ℝ) * (D * (Real.exp κ - 1)) := by positivity
    linarith
  linarith

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
