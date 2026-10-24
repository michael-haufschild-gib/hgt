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

open Complex MeasureTheory Real Set Filter Topology Finset Matrix
open scoped Real ComplexConjugate
open Zeta23 RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.SquareRootThreshold
  GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

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
  have h0 : 0 ≤ fun z : ℂ => if p z then 1 / ‖z - s‖ ^ 3 else 0 := fun z => by
    simp only [Pi.zero_apply]; split_ifs <;> positivity
  have hs := summable_of_sum_le h0 hfin
  exact ⟨hs, hs.tsum_le_of_sum_le hfin⟩

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
      · have h := hkern (by norm_num) hV4 (Complex.ofReal_re σ) hz
          ((four_le_abs_im_of_evenCoeff_zeta hz).trans (by
            have := Complex.abs_im_le_norm (z - (σ : ℂ)); simpa using this))
        have heq : (if D z ≠ 0 ∧ 0 < z.re then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) =
            (if 0 < z.re then 1 / ‖z - (σ : ℂ)‖ ^ 3 else 0) := by
          by_cases hre : 0 < z.re
          · rw [if_pos ⟨hz, hre⟩, if_pos hre]
          · rw [if_neg (fun h' => hre h'.2), if_neg hre]
        rw [heq]
        exact h
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
          have heq : (if D z ≠ 0 ∧ 0 < z.re ∧ z ∉ S then 1 / ‖z - s‖ ^ 3 else 0) =
              (if 0 < z.re then 1 / ‖z - s‖ ^ 3 else 0) := by
            by_cases hre : 0 < z.re
            · rw [if_pos ⟨hz, hre, hzS⟩, if_pos hre]
            · rw [if_neg (fun h' => hre h'.2.1), if_neg hre]
          rw [heq]
          exact h
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
    have h2 : 0 ≤ 4 * m₀ / ((Real.exp 1 - 1) * ε₀) := div_nonneg (by linarith) (by positivity)
    have := mul_le_mul_of_nonneg_left h1 h2
    linarith
  have hm2 : 24 * (M : ℝ) * D * Real.exp κ ≤ 39 * M * (D * (Real.exp κ - 1)) := by
    have h1 := mul_le_mul_of_nonneg_left hratio (show 0 ≤ 24 * (M : ℝ) * D by positivity)
    have h2 : 0 ≤ (M : ℝ) * (D * (Real.exp κ - 1)) :=
      mul_nonneg (Nat.cast_nonneg M) (mul_nonneg hD0.le (by linarith))
    linarith
  linarith

/-! ### 2. Complete elimination of `log Γ` in the one-parameter (`c = 0`) visibility and horizon laws -/

/-- **Height-free comparability of unmodulated coefficients near a loud record.** Under
`OffLineCopiesLocallyBounded M`, any strictly off-line zero `½ + z` (`Re z ≠ 0`) near `z₁` satisfies
`‖D(z)‖ ≤ (25/16) M ‖D(z₁)‖`, completely eliminating `125/2 · log(180 Γ')` from
`norm_evenCoeff_zero_le_of_near`. -/
theorem norm_evenCoeff_zero_le_of_near_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₁ z : ℂ}
    (hz₁ : (1 / 2 + z₁) ∈ zetaZeroConfig.carrier) (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier)
    (hz_off : z.re ≠ 0) {H₀ : ℝ} (hh₁ : H₀ ≤ ‖paperFT (scaledBump w) (-(I * z₁))‖)
    (hL : 8 * w * Real.exp (w / 2) * bumpMass w * ‖z - z₁‖ ≤ H₀) (hwz : w * ‖z - z₁‖ ≤ 1) :
    ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ ≤
      25 / 16 * M * ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ := by
  have hdiff := norm_paperFT_sub_le_quarter hw hz₁ hh₁ hL hwz
  set h₁ := paperFT (scaledBump w) (-(I * z₁)) with hh₁def
  set h₂ := paperFT (scaledBump w) (-(I * z)) with hh₂def
  have hh₂ : ‖h₂‖ ≤ 5 / 4 * ‖h₁‖ := by
    have := norm_sub_norm_le h₂ h₁; linarith
  have hD : ∀ y, (1 / 2 + y) ∈ zetaZeroConfig.carrier →
      ‖evenCoeff zetaZeroConfig (modScaledBump w 0) y‖ =
        2 * zetaZeroConfig.mult (1 / 2 + y) * ‖paperFT (scaledBump w) (-(I * y))‖ ^ 2 :=
    fun y hy => by
      rw [evenCoeff_modScaledBump_zero_eq_two_mul hw hy, norm_mul, norm_pow, Complex.norm_natCast]
      push_cast; ring
  rw [hD z hz, hD z₁ hz₁, ← hh₁def, ← hh₂def]
  have hmM : (zetaZeroConfig.mult (1 / 2 + z) : ℝ) ≤ M := by
    exact_mod_cast mult_offLine_zeta_le_of_offLineCopiesLocallyBounded hM hz (by
      intro h; apply hz_off; have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
      linarith)
  have hm1 : (1 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + z₁) := by
    exact_mod_cast zetaZeroConfig.one_le_mult _ hz₁
  have hsq : ‖h₂‖ ^ 2 ≤ 25 / 16 * ‖h₁‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hh₂ 2; nlinarith
  have h1 : 2 * (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * ‖h₂‖ ^ 2 ≤
      2 * (M : ℝ) * (25 / 16 * ‖h₁‖ ^ 2) :=
    mul_le_mul (by linarith) hsq (sq_nonneg _) (by positivity)
  have h2 : 2 * ‖h₁‖ ^ 2 ≤ 2 * (zetaZeroConfig.mult (1 / 2 + z₁) : ℝ) * ‖h₁‖ ^ 2 := by
    have := sq_nonneg ‖h₁‖; nlinarith
  have h3 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 25 / 16 * (M : ℝ) by positivity)
  linarith

/-- **Height-free transform lower bound for a loud off-line unmodulated coefficient.** Under
`OffLineCopiesLocallyBounded M`, any strictly off-line zero `½ + y` (`Re y ≠ 0`) with
`‖D(y)‖ ≥ ε₀` and `H₀² ≤ ε₀ / (2(M + 1))` satisfies `H₀ ≤ ‖h_w(-i y)‖`, eliminating
`80 log(180 Γ')` from `le_norm_paperFT_of_loud_zero`. -/
theorem le_norm_paperFT_of_loud_zero_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {y : ℂ}
    (hy : (1 / 2 + y) ∈ zetaZeroConfig.carrier) (hy_off : y.re ≠ 0) {ε₀ H₀ : ℝ}
    (hD : ε₀ ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w 0) y‖)
    (hH : H₀ ^ 2 ≤ ε₀ / (2 * (M + 1))) :
    H₀ ≤ ‖paperFT (scaledBump w) (-(I * y))‖ := by
  have hmM : (zetaZeroConfig.mult (1 / 2 + y) : ℝ) ≤ M := by
    exact_mod_cast mult_offLine_zeta_le_of_offLineCopiesLocallyBounded hM hy (by
      intro h; apply hy_off; have e : (1 / 2 + y).re = 1 / 2 + y.re := by simp
      linarith)
  have hDn : ‖evenCoeff zetaZeroConfig (modScaledBump w 0) y‖ =
      2 * zetaZeroConfig.mult (1 / 2 + y) * ‖paperFT (scaledBump w) (-(I * y))‖ ^ 2 := by
    rw [evenCoeff_modScaledBump_zero_eq_two_mul hw hy, norm_mul, norm_pow, Complex.norm_natCast]
    push_cast; ring
  have hpos : (0 : ℝ) < 2 * (M + 1) := by positivity
  have h1 : ε₀ / (2 * (M + 1)) ≤ ‖paperFT (scaledBump w) (-(I * y))‖ ^ 2 := by
    rw [div_le_iff₀ hpos]
    have h2 : 2 * (zetaZeroConfig.mult (1 / 2 + y) : ℝ) *
        ‖paperFT (scaledBump w) (-(I * y))‖ ^ 2 ≤
        2 * (M + 1) * ‖paperFT (scaledBump w) (-(I * y))‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) (hH.trans h1)

/-- The height-independent noise constant
`M_off(M, w, a) = 4 m₀ / ((e - 1) a) + 39 M + 1` of the one-parameter family under
`OffLineCopiesLocallyBounded M`, eliminating `6144 log(180(Γ + 6))`. -/
def recordNoiseOffLine (M : ℕ) (w a : ℝ) : ℝ :=
  4 * (32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + Real.log 4)) / ((Real.exp 1 - 1) * a) +
    39 * M + 1

/-- The height-independent collapse bound
`B_off(M, w, a, κ₀; k, p) = (8/3)^p (4/3)^k (2κ₀) (4κ₀² + 4π²(k + p)²)^{k+p} M_off(M, w, a)`
for a loud record of the unmodulated family under `OffLineCopiesLocallyBounded M`. -/
def recordCollapseBoundOffLine (M : ℕ) (w a κ₀ : ℝ) (k p : ℕ) : ℝ :=
  (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀) * (4 * κ₀ ^ 2 + 4 * π ^ 2 * (k + p : ℕ) ^ 2) ^ (k + p) *
    recordNoiseOffLine M w a

theorem recordCollapseBoundOffLine_one (M : ℕ) (w a : ℝ) (k p : ℕ) :
    recordCollapseBoundOffLine M w a 1 k p = (8 / 3) ^ p * (4 / 3) ^ k * 2 *
      (4 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) * recordNoiseOffLine M w a := by
  rw [recordCollapseBoundOffLine]; ring

/-- **A loud record of the one-parameter family is visible without any height bound `Γ`.**
Under `OffLineCopiesLocallyBounded M`, let `z₁` be the Legendre record of `modScaledBump w 0` at lag
`V` with `‖D(z₁)‖ ≥ a > 0` and `Re z₁ ≥ σ` (`0 < σ ≤ ½`). Every companion in the disc of radius
`r + 2κ₀/V ≤ 3σ/8` around `z₁` has `Re z ≥ 5σ/8 > 0`, so `T.card ≤ M`, `H₀² ≤ a / (2(M + 1))`,
core mass `≤ (M + 1) (25/16 · M) ‖D(z₁)‖`, and `recordCollapseBoundOffLine M w a κ₀ k p` are all
completely independent of `Im z₁`. -/
theorem one_param_record_visible_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {V : ℝ} (hV : 0 < V) {z₁ : ℂ}
    (hz₁ : evenCoeff zetaZeroConfig (modScaledBump w 0) z₁ ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 2) (hre₁ : σ ≤ z₁.re) {a : ℝ} (ha : 0 < a)
    (hD₁ : a ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖)
    (hrec : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * Real.exp (z₁.re * V))
    {κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀)
    (hκV : 2 * κ₀ / V ≤ σ / 8) (hVk : π * (k + M : ℕ) ≤ V)
    (hVr : 4 * π * (k + M : ℕ) ≤ V * (σ / 4)) {H₀ : ℝ}
    (hH : H₀ ^ 2 ≤ a / (2 * (M + 1)))
    {ρ G : ℝ} (hρ : 0 < ρ) (hG : 1 ≤ G) (hρV : ρ * V ≤ 1) (hρw : w * ρ ≤ 1)
    (hρL : 8 * w * Real.exp (w / 2) * bumpMass w * ρ ≤ H₀) (hρr : ρ ≤ σ / 8)
    (hηm : ((1 + coreFactorPerturbation M κ₀ V ρ G) * (2 * (ρ * V)) +
        coreFactorPerturbation M κ₀ V ρ G) * ((M + 1) * (25 / 16 * M)) ≤ 1 / 2)
    (hmain : ∀ p : ℕ, p ≤ M → 2 * recordCollapseBoundOffLine M w a κ₀ k p <
      (ρ * κ₀ / (2 * (M + 1) * G ^ M)) ^ p * V ^ (2 * k + p + 1) * (σ / 4) ^ (2 * k + 1)) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  by_contra hneg
  push Not at hneg
  classical
  set b := modScaledBump w 0 with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set r : ℝ := σ / 4 with hr
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; linarith
  have hmem : ∀ x : ℂ, D x ≠ 0 → (1 / 2 + x) ∈ zetaZeroConfig.carrier :=
    fun _ hx => add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hx
  have hκ₀0 : 0 < κ₀ := by linarith
  have h2κ : 2 * κ₀ / V ≤ r / 2 := by rw [hr]; linarith
  set R₀ : ℝ := r + 2 * κ₀ / V with hR₀
  set T : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b z₁ R₀).toFinset.erase z₁ with hT
  have hTcard : T.card ≤ M := by
    refine card_offLine_window_le_of_offLineCopiesLocallyBounded hM z₁.im T fun z hz => ?_
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset] at hz
    obtain ⟨-, hDz, hzr⟩ := hz
    refine ⟨hmem z hDz, ?_, ?_⟩
    · have h1 := Complex.abs_re_le_norm (z - z₁)
      rw [Complex.sub_re] at h1
      have h2 := neg_abs_le (z.re - z₁.re)
      have h3 : R₀ ≤ σ / 2 := by rw [hR₀, hr]; linarith
      intro h0
      linarith
    · have h1 := Complex.abs_im_le_norm (z - z₁)
      rw [Complex.sub_im] at h1
      have h2 : R₀ ≤ 1 := by rw [hR₀]; linarith
      linarith
  obtain ⟨κ, hκ1, hκ2, hmirror⟩ := exists_depth_avoiding_mirrors T z₁ hTcard hκ₀0 hV
  set ε : ℝ := κ₀ / (2 * (M + 1) * V) with hε
  have hκ0 : 0 < κ := by linarith
  have hκV' : κ / V ≤ 2 * κ₀ / V := div_le_div_of_nonneg_right hκ2 hV.le
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  have hz₁s : ‖z₁ - s‖ = κ / V := by
    have : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hκ0 hV)]
  set S : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b s r).toFinset with hS
  have hz₁S : z₁ ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]; exact ⟨hz₁, by rw [hz₁s]; linarith⟩
  have hSr : ∀ z ∈ S, ‖z - s‖ ≤ r := fun z hz => by
    rw [hS, Set.Finite.mem_toFinset] at hz; exact hz.2
  have hiso : ∀ z, z ∉ S → D z ≠ 0 → r ≤ ‖z - s‖ := fun z hz hDz => by
    rw [hS, Set.Finite.mem_toFinset] at hz
    by_contra h; push Not at h; exact hz ⟨hDz, h.le⟩
  have hST : S.erase z₁ ⊆ T := fun z hz => by
    rw [Finset.mem_erase] at hz
    have hzS := hz.2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset]
    refine ⟨hz.1, hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    have := hSr z hz.2
    rw [hR₀]; linarith
  have hrσ : r ≤ z₁.re - κ / V := by rw [hr] at h2κ ⊢; linarith
  obtain ⟨j, hjP, hann⟩ := exists_empty_annulus T z₁ hTcard hρ hG
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = ρ / G ^ (j + 1) := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = ρ / G ^ j := ⟨_, rfl⟩
  rw [← hρ₀, ← hρ₁] at hann
  have hG0 : 0 < G := by linarith only [hG]
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀]; positivity
  have hρ₀ρ : ρ₀ ≤ ρ := by rw [hρ₀]; exact div_le_self hρ.le (one_le_pow₀ hG)
  have hρ₁ρ₀ : ρ₁ = G * ρ₀ := by rw [hρ₁, hρ₀, pow_succ]; field_simp
  have hρ₁P : ρ / G ^ M ≤ ρ₁ := by
    rw [hρ₁]; exact div_le_div_of_nonneg_left hρ.le (by positivity) (pow_le_pow_right₀ hG hjP)
  obtain ⟨SL, hSL⟩ : ∃ SL : Finset ℂ, SL = (S.erase z₁).filter fun z => ρ₁ < ‖z - z₁‖ :=
    ⟨_, rfl⟩
  have hSLmem : ∀ z, z ∈ SL ↔ (z ≠ z₁ ∧ z ∈ S) ∧ ρ₁ < ‖z - z₁‖ := fun z => by
    rw [hSL, Finset.mem_filter, Finset.mem_erase]
  have hSLS : SL ⊆ S := fun z hz => ((hSLmem z).mp hz).1.2
  have hSLT : SL ⊆ T := fun z hz => hST (Finset.mem_erase.mpr ((hSLmem z).mp hz).1)
  have hpP : SL.card ≤ M := (Finset.card_le_card hSLT).trans hTcard
  have hpP' : ((k + SL.card : ℕ) : ℝ) ≤ (k + M : ℕ) := by exact_mod_cast (by omega : k + SL.card ≤ k + M)
  have hPE := zeta_partial_elimination_le_of_offLineCopiesLocallyBounded hM
    (contDiff_modScaledBump_two w _) (modScaledBump_support hw _) hneg hz₁ hrec hκ0 hr0 hr1 hrσ hk
    S SL hSLS hSr hiso (le_trans (mul_le_mul_of_nonneg_left hpP' Real.pi_pos.le) hVk)
    (le_trans (mul_le_mul_of_nonneg_left hpP' (by positivity)) hVr)
  rw [← hs] at hPE
  have hz₁C : z₁ ∈ S.filter fun z => z ∉ SL :=
    Finset.mem_filter.mpr ⟨hz₁S, fun h => ((hSLmem z₁).mp h).1.1 rfl⟩
  have hcρ₀ : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖c - z₁‖ ≤ ρ₀ := fun c hc => by
    obtain ⟨hcS, hcL⟩ := Finset.mem_filter.mp hc
    by_cases hne : c = z₁
    · rw [hne, sub_self, norm_zero]; exact hρ₀0.le
    · rcases hann c (hST (Finset.mem_erase.mpr ⟨hne, hcS⟩)) with h | h
      · exact h
      · exact absurd ((hSLmem c).mpr ⟨⟨hne, hcS⟩, h⟩) hcL
  have hcρ : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖c - z₁‖ ≤ ρ := fun c hc => (hcρ₀ c hc).trans hρ₀ρ
  have hθc : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
  have hε0' : 0 < ε := by rw [hε]; positivity
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁ρ₀]; positivity
  have hbig : ∀ y ∈ SL, ρ₁ * ε ≤ ‖(y - s) ^ 2 - (z₁ - s) ^ 2‖ := fun y hy => by
    have e : (y - s) ^ 2 - (z₁ - s) ^ 2 = (y - z₁) * ((y - z₁) + ((2 * κ / V : ℝ) : ℂ)) := by
      have e1 : y - s = (y - z₁) + ((κ / V : ℝ) : ℂ) := by rw [← hθc]; ring
      rw [e1, hθc]; push_cast; ring
    rw [e, norm_mul]
    exact mul_le_mul ((hSLmem y).mp hy).2.le (hmirror y (hSLT hy)) hε0'.le (norm_nonneg _)
  have hDS : ∀ c ∈ S, D c ≠ 0 := fun c hc => by
    rw [hS, Set.Finite.mem_toFinset] at hc; exact hc.1
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hz₁_off : z₁.re ≠ 0 := by linarith
  have hh₁ := le_norm_paperFT_of_loud_zero_of_offLineCopiesLocallyBounded hM hw (hmem z₁ hz₁)
    hz₁_off hD₁ hH
  have hcoh : ∀ c ∈ S.filter (fun z => z ∉ SL), 0 ≤ (D c * conj (D z₁)).re := fun c hc => by
    have hcS := (Finset.mem_filter.mp hc).1
    have hcz := hcρ c hc
    exact re_one_param_mul_conj_nonneg hw (hmem z₁ hz₁) (hmem c (hDS c hcS)) hh₁
      (le_trans (mul_le_mul_of_nonneg_left hcz (mul_nonneg (by positivity) hJ0)) hρL)
      (le_trans (mul_le_mul_of_nonneg_left hcz hw.le) hρw)
  obtain ⟨Dm, hDm⟩ : ∃ Dm : ℝ, Dm = 25 / 16 * M * ‖D z₁‖ := ⟨_, rfl⟩
  have hDc : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤ Dm := fun c hc => by
    have hcS := (Finset.mem_filter.mp hc).1
    have hcz := hcρ c hc
    have hc_off : c.re ≠ 0 := by
      have h1 := Complex.abs_re_le_norm (c - z₁)
      rw [Complex.sub_re] at h1
      have h2 := neg_abs_le (c.re - z₁.re)
      intro h0
      linarith
    rw [hDm]
    exact norm_evenCoeff_zero_le_of_near_of_offLineCopiesLocallyBounded hM hw (hmem z₁ hz₁)
      (hmem c (hDS c hcS)) hc_off hh₁
      (le_trans (mul_le_mul_of_nonneg_left hcz (mul_nonneg (by positivity) hJ0)) hρL)
      (le_trans (mul_le_mul_of_nonneg_left hcz hw.le) hρw)
  have hCcard : (S.filter fun z => z ∉ SL).card ≤ M + 1 :=
    (Finset.card_filter_le _ _).trans (by
      rw [← Finset.card_erase_add_one hz₁S]
      exact Nat.succ_le_succ ((Finset.card_le_card hST).trans hTcard))
  have hsumD : ∑ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤ (M + 1) * Dm := by
    have h := Finset.sum_le_card_nsmul _ (fun c => ‖D c‖) Dm hDc
    rw [nsmul_eq_mul] at h
    have hD0 : 0 ≤ Dm := le_trans (norm_nonneg _) (hDc z₁ hz₁C)
    have hc : ((S.filter fun z => z ∉ SL).card : ℝ) ≤ M + 1 := by exact_mod_cast hCcard
    exact h.trans (mul_le_mul_of_nonneg_right hc hD0)
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = (4 * κ₀ / V + ρ) * (2 * (M + 1) * V) / (G * κ₀) := ⟨_, rfl⟩
  have ht₀0 : 0 ≤ t₀ := by rw [ht₀]; positivity
  have hτ : (1 + t₀) ^ SL.card - 1 ≤ coreFactorPerturbation M κ₀ V ρ G := by
    rw [coreFactorPerturbation, ← ht₀]
    have := pow_le_pow_right₀ (by linarith only [ht₀0] : (1 : ℝ) ≤ 1 + t₀) hpP
    linarith only [this]
  have hmass : ((1 + coreFactorPerturbation M κ₀ V ρ G) * (2 * (ρ * V)) +
      coreFactorPerturbation M κ₀ V ρ G) * ∑ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤
        ‖D z₁‖ / 2 := by
    have hτ0 : 0 ≤ coreFactorPerturbation M κ₀ V ρ G := by
      have := one_le_pow₀ (n := SL.card) (by linarith only [ht₀0] : (1 : ℝ) ≤ 1 + t₀)
      linarith only [this, hτ]
    have hη0 : 0 ≤ (1 + coreFactorPerturbation M κ₀ V ρ G) * (2 * (ρ * V)) +
        coreFactorPerturbation M κ₀ V ρ G := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsumD hη0
    have h2 := mul_le_mul_of_nonneg_right hηm (norm_nonneg (D z₁))
    rw [hDm] at h1
    linarith only [h1, h2]
  have hgap : ρ₀ * (2 * (κ / V) + ρ₀) ≤ t₀ * (ρ₁ * ε) := by
    rw [ht₀, hρ₁ρ₀, hε]
    exact core_gap_arith hρ₀0.le hρ₀ρ hG0 hκ₀0 hV (Nat.cast_nonneg M) hκ2
  have hθ0 : 0 < κ / V := div_pos hκ0 hV
  have hcore_ge := eliminated_core_ge hz₁C D (k + SL.card) hV hθc hθ0.le hρ₀0.le
    (mul_pos hρ₁0 hε0') hbig hcρ₀ hgap hτ (mul_le_mul_of_nonneg_right hρ₀ρ hV.le) hρV hcoh hmass
  have hcol := hcore_ge.trans hPE
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = SL.card := ⟨_, rfl⟩
  rw [← hp] at hcol hpP
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) := ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : ℝ, Q₂ = (4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (2 * (k + p)).factorial * (π / V) ^ (2 * (k + p)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]; exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos Real.pi_pos hV) _)
  have hbase : ∀ t : ℝ, 0 < t → 0 < t ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := fun t ht =>
    add_pos_of_pos_of_nonneg (pow_pos ht 2)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg π)) (sq_nonneg _))
  have hQ0 : 0 < Q := by rw [hQ]; exact pow_pos (hbase κ hκ0) _
  have hKlow : u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q) ≤
      ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (norm_fejerPowWin_ofReal_ge hV (k + p) hθ0)
    have hVne : V ≠ 0 := hV.ne'
    have e : (κ / V) ^ 2 + (2 * π * ((k + p : ℕ) : ℝ) / V) ^ 2 =
        (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) / V ^ 2 := by
      field_simp; ring
    rw [e, div_mul_cancel₀ κ hVne, hu, hQ, div_pow, div_pow, ← pow_mul V 2 (k + p), pow_succ]
    field_simp
  rw [← hu] at hcol
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = 32 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + Real.log 4) := ⟨_, rfl⟩
  have hWb := tsum_norm_evenCoeff_modScaledBump_le hw 0
  have hMb := abs_two_re_lagStructure_zero_le zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w 0) (modScaledBump_support hw 0)
  rw [abs_zero, zero_add] at hWb
  have hW0 : 0 ≤ ∑' z : ℂ, ‖D z‖ := tsum_nonneg fun z => norm_nonneg _
  have hMW : |2 * (lagStructure zetaZeroConfig b 0).re| + ∑' z : ℂ, ‖D z‖ ≤ m₀ := by
    rw [hm₀]; linarith only [hWb, hMb]
  have hκ1' : 1 ≤ κ := hκ₀.trans hκ1
  have hΞ := xi_ratio_offLine_le (M := M) hκ1' ha hD₁ hW0 hMW
  have hQQ : κ * Q ≤ 2 * κ₀ * Q₂ := by
    have hq : Q ≤ Q₂ := by
      rw [hQ, hQ₂]
      refine pow_le_pow_left₀ (hbase κ hκ0).le ?_ _
      have h2 : κ ^ 2 ≤ (2 * κ₀) ^ 2 := pow_le_pow_left₀ hκ0.le hκ2 2
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [h2, e]
    exact mul_le_mul hκ2 hq hQ0.le (by linarith only [hκ₀0])
  have he1 : 0 < Real.exp 1 - 1 := by linarith only [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hm00 : 0 ≤ m₀ := le_trans (add_nonneg (abs_nonneg _) hW0) hMW
  have hE : 0 < Real.exp κ - 1 := by linarith only [Real.add_one_lt_exp hκ0.ne', hκ0]
  have hc0 : (0 : ℝ) ≤ (8 / 3) ^ p * (4 / 3) ^ k :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  have hPr0 : 0 ≤ ρ₁ ^ p / 2 := by positivity
  have hN0 : 0 ≤ recordNoiseOffLine M w a * 1 := by
    rw [mul_one, recordNoiseOffLine, ← hm₀]
    have : 0 ≤ 4 * m₀ / ((Real.exp 1 - 1) * a) := div_nonneg (by linarith) (by positivity)
    positivity
  have hΞ' : 4 * |2 * (lagStructure zetaZeroConfig b 0).re| + 4 * ∑' z : ℂ, ‖D z‖ +
      24 * M * ‖D z₁‖ * Real.exp κ ≤
        recordNoiseOffLine M w a * 1 * (‖D z₁‖ * (Real.exp κ - 1)) := by
    rw [mul_one, recordNoiseOffLine, ← hm₀]
    have : 0 ≤ ‖D z₁‖ * (Real.exp κ - 1) := mul_nonneg (norm_nonneg _) hE.le
    linarith [hΞ]
  have hcol' : ‖D z₁‖ * (ρ₁ ^ p / 2) * ε ^ p * ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ ≤
      u * ((8 / 3) ^ p * (4 / 3) ^ k *
        (4 * |2 * (lagStructure zetaZeroConfig b 0).re| + 4 * (∑' z : ℂ, ‖D z‖) +
          24 * M * ‖D z₁‖ * Real.exp κ) / r ^ (2 * k + 1)) :=
    le_trans (le_of_eq (by rw [mul_pow]; ring)) hcol
  have hfin := cluster_log_arith (D := ‖D z₁‖) (u := u) (E := Real.exp κ - 1)
    (norm_pos_iff.mpr hz₁) hu0 hE hε0'.le hPr0 hr0 hV (mul_pos hκ0 hQ0) hcol' hKlow hΞ' hc0 hQQ
    hN0 (p := p) (m := 2 * (k + p) + 1) (k := k)
  have e : ε ^ p * V ^ (2 * (k + p) + 1) = (κ₀ / (2 * (M + 1))) ^ p * V ^ (2 * k + p + 1) := by
    have hVne : V ≠ 0 := hV.ne'
    rw [hε, show 2 * (k + p) + 1 = (2 * k + p + 1) + p by ring, pow_add, div_pow, div_pow, mul_pow]
    field_simp
  have hb : (ρ₁ ^ p * (κ₀ / (2 * (M + 1))) ^ p) / 2 * (V ^ (2 * k + p + 1) * r ^ (2 * k + 1)) ≤
      recordCollapseBoundOffLine M w a κ₀ k p :=
    calc (ρ₁ ^ p * (κ₀ / (2 * (M + 1))) ^ p) / 2 * (V ^ (2 * k + p + 1) * r ^ (2 * k + 1))
        = ρ₁ ^ p / 2 * (ε ^ p * V ^ (2 * (k + p) + 1)) * r ^ (2 * k + 1) := by rw [e]; ring
      _ = ρ₁ ^ p / 2 * ε ^ p * V ^ (2 * (k + p) + 1) * r ^ (2 * k + 1) := by ring
      _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (recordNoiseOffLine M w a * 1) := hfin
      _ = recordCollapseBoundOffLine M w a κ₀ k p := by
          rw [recordCollapseBoundOffLine, ← hQ₂]; ring
  have hab : (ρ * κ₀ / (2 * (M + 1) * G ^ M)) ^ p ≤ ρ₁ ^ p * (κ₀ / (2 * (M + 1))) ^ p := by
    rw [← mul_pow]
    have e2 : ρ * κ₀ / (2 * (M + 1) * G ^ M) = ρ / G ^ M * (κ₀ / (2 * (M + 1))) := by
      field_simp
    refine pow_le_pow_left₀ (by positivity) ?_ p
    rw [e2]
    exact mul_le_mul_of_nonneg_right hρ₁P (by positivity)
  exact visible_final_arith hab (by positivity) hb (hmain p hpP)

/-- The height-independent coherence product `c_off(M) = 1 / (10(M + 1)(25/16 · M) + 1)` of the
one-parameter family under `OffLineCopiesLocallyBounded M`. -/
def recordCoherenceOffLine (M : ℕ) : ℝ :=
  explicitCoherence 1 (25 / 16 * M) M

/-- The height-independent Fejér order `k_off(M, w, a)` for a record of loudness `a` under
`OffLineCopiesLocallyBounded M`. -/
def recordOrderOffLine (M : ℕ) (w a : ℝ) : ℕ :=
  explicitOrder (recordNoiseOffLine M w a) (recordCoherenceOffLine M) M

/-- The height-independent phase-coherence scale `H₀(M, a) = √(a / (2(M + 1)))` under
`OffLineCopiesLocallyBounded M`, eliminating `log(180 Γ(a))` from `recordScale`. -/
def recordScaleOffLine (M : ℕ) (a : ℝ) : ℝ :=
  Real.sqrt (a / (2 * (M + 1)))

/-- The explicit visibility lag `V_off(M, w, a, σ)` of a loud record of the unmodulated family
under `OffLineCopiesLocallyBounded M`, completely free of `recordHeightOf w a`. -/
def recordLagOffLine (M : ℕ) (w a σ : ℝ) : ℝ :=
  4 / σ * (13 * π * recordOrderOffLine M w a + 4) +
    w + 8 * w * Real.exp (w / 2) * bumpMass w / recordScaleOffLine M a

/-- **A loud record of the one-parameter family is visible at the height-free explicit lag
`recordLagOffLine M w a σ`.** Under `OffLineCopiesLocallyBounded M`, if the Legendre record `z₁` of
`modScaledBump w 0` at lag `V ≥ recordLagOffLine M w a σ` has `‖D(z₁)‖ ≥ a > 0` and
`Re z₁ ≥ σ` (`0 < σ ≤ ½`), then `P_v < 0` for some `v ∈ [0, V]`, with no height hypothesis
`|Im z₁| ≤ Γ(a)`. -/
theorem one_param_record_visible_at_explicit_lag_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {V : ℝ} {z₁ : ℂ}
    (hz₁ : evenCoeff zetaZeroConfig (modScaledBump w 0) z₁ ≠ 0) {σ : ℝ} (hσ : 0 < σ)
    (hσ1 : σ ≤ 1 / 2) (hre₁ : σ ≤ z₁.re) {a : ℝ} (ha : 0 < a)
    (hD₁ : a ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖)
    (hrec : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → 0 < z.re →
      ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * Real.exp (z₁.re * V))
    (hV : recordLagOffLine M w a σ ≤ V) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  have hDm0 : 0 ≤ (25 / 16 * (M : ℝ)) := by positivity
  have hNpos : 0 < recordNoiseOffLine M w a := by
    unfold recordNoiseOffLine
    have hC := xiLineTwoLogDerivConstant_nonneg
    have h4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have he1 : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
    positivity
  obtain ⟨hc0, hc1, hca, hG1, hq0, hq1, hPk, hk1, hY⟩ :=
    explicit_parameter_facts one_pos hDm0 hNpos M
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = explicitCoherence 1 (25 / 16 * M) M := ⟨_, rfl⟩
  rw [← hc] at hc0 hc1 hca hG1 hq0 hq1 hPk hk1 hY
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = explicitOrder (recordNoiseOffLine M w a) c M := ⟨_, rfl⟩
  rw [← hk] at hPk hk1 hY
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = explicitGap c M := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = explicitRatio c M := ⟨_, rfl⟩
  have hqe : q = c / (2 * (M + 1) * G ^ M) := by rw [hq, explicitRatio, ← hG]
  rw [← hG] at hG1
  rw [← hq] at hq0 hq1 hY
  have hkk : recordOrderOffLine M w a = k := by rw [hk, hc]; rfl
  obtain ⟨H₀, hH₀⟩ : ∃ H₀ : ℝ, H₀ = recordScaleOffLine M a := ⟨_, rfl⟩
  rw [recordLagOffLine, hkk, ← hH₀] at hV
  have hH₀0 : 0 < H₀ := by rw [hH₀, recordScaleOffLine]; exact Real.sqrt_pos.mpr (by positivity)
  have hH₀sq : H₀ ^ 2 = a / (2 * (M + 1)) := by
    rw [hH₀, recordScaleOffLine]; exact Real.sq_sqrt (by positivity)
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hJ'0 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w := mul_nonneg (by positivity) hJ0
  have hπk : 0 ≤ 13 * π * k := by positivity
  have hT2 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w / H₀ := div_nonneg hJ'0 hH₀0.le
  have h8 : 0 ≤ 4 / σ * (13 * π * k + 4) := by positivity
  have hVw : w ≤ V := by linarith only [hV, h8, hT2]
  have hV0 : 0 < V := lt_of_lt_of_le hw hVw
  have hVJ : 8 * w * Real.exp (w / 2) * bumpMass w / H₀ ≤ V := by linarith only [hV, h8, hw]
  have hσV : 4 * (13 * π * k + 4) ≤ σ * V := by
    have h1 : 4 / σ * (13 * π * k + 4) ≤ V := by linarith only [hV, hT2, hw]
    have h2 := mul_le_mul_of_nonneg_left h1 hσ.le
    have e : σ * (4 / σ * (13 * π * k + 4)) = 4 * (13 * π * k + 4) := by field_simp
    linarith only [h2, e]
  have hσV2 : σ * V ≤ V / 2 := by nlinarith
  have hkP : ((k + M : ℕ) : ℝ) ≤ 2 * k := by
    push_cast; have : (M : ℝ) ≤ k := by exact_mod_cast hPk
    linarith
  have hπkP := mul_le_mul_of_nonneg_left hkP Real.pi_pos.le
  have hκV : 2 * 1 / V ≤ σ / 8 := by
    rw [div_le_div_iff₀ hV0 (by norm_num)]; linarith only [hσV, hπk]
  have hVk : π * (k + M : ℕ) ≤ V := by linarith only [hπkP, hσV, hσV2, hπk]
  have hVr : 4 * π * (k + M : ℕ) ≤ V * (σ / 4) := by linarith only [hπkP, hσV, hπk]
  have hρ : 0 < c / V := div_pos hc0 hV0
  have hρV : c / V * V ≤ 1 := by rw [div_mul_cancel₀ c hV0.ne']; exact hc1
  have hρw : w * (c / V) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hV0]
    have := mul_le_mul_of_nonneg_left hc1 hw.le
    linarith only [this, hVw]
  have hρL : 8 * w * Real.exp (w / 2) * bumpMass w * (c / V) ≤ H₀ := by
    rw [mul_div_assoc', div_le_iff₀ hV0]
    have h1 : 8 * w * Real.exp (w / 2) * bumpMass w ≤ V * H₀ := by
      have := mul_le_mul_of_nonneg_right hVJ hH₀0.le
      rwa [div_mul_cancel₀ _ hH₀0.ne'] at this
    have h2 := mul_le_mul_of_nonneg_left hc1 hJ'0
    linarith only [h1, h2]
  have hρr : c / V ≤ σ / 8 := by
    rw [div_le_div_iff₀ hV0 (by norm_num)]; linarith only [hσV, hπk, hc1]
  have hηm : ((1 + coreFactorPerturbation M 1 V (c / V) G) * (2 * (c / V * V)) +
      coreFactorPerturbation M 1 V (c / V) G) * ((M + 1) * (25 / 16 * M)) ≤ 1 / 2 := by
    rw [div_mul_cancel₀ c hV0.ne', hG]
    have hτ := coreFactorPerturbation_le hc0 hc1 hV0 M
    have h1 : coreFactorPerturbation M 1 V (c / V) (explicitGap c M) * (2 * c) ≤ 1 * (2 * c) :=
      mul_le_mul_of_nonneg_right (hτ.trans hc1) (by positivity)
    have hτ' : (1 + coreFactorPerturbation M 1 V (c / V) (explicitGap c M)) * (2 * c) +
        coreFactorPerturbation M 1 V (c / V) (explicitGap c M) ≤ 5 * c := by
      linarith only [h1, hτ]
    have hm : 0 ≤ ((M : ℝ) + 1) * (25 / 16 * M) := by positivity
    have h2 := mul_le_mul_of_nonneg_right hτ' hm
    linarith only [h2, hca]
  have hmain : ∀ p : ℕ, p ≤ M → 2 * recordCollapseBoundOffLine M w a 1 k p <
      (c / V * 1 / (2 * (M + 1) * G ^ M)) ^ p * V ^ (2 * k + p + 1) * (σ / 4) ^ (2 * k + 1) := by
    intro p hp
    have hG0 : 0 < G := lt_of_lt_of_le one_pos hG1
    have hD0 : (2 * ((M : ℝ) + 1) * G ^ M) ≠ 0 := by positivity
    have e : (c / V * 1 / (2 * (M + 1) * G ^ M)) ^ p * V ^ (2 * k + p + 1) * (σ / 4) ^ (2 * k + 1) =
        q ^ p * (V * (σ / 4)) ^ (2 * k + 1) := by
      have e0 : c / V * 1 / (2 * (M + 1) * G ^ M) = c / (2 * (M + 1) * G ^ M) / V := by ring
      have hVp : V ^ p ≠ 0 := pow_ne_zero _ hV0.ne'
      rw [hqe, e0, div_pow, show 2 * k + p + 1 = (2 * k + 1) + p by ring, pow_add, mul_pow]
      field_simp
    rw [e, recordCollapseBoundOffLine_one]
    have hX : 13 * π * k ≤ V * (σ / 4) := by linarith only [hσV]
    exact collapse_form_lt hp hPk hk1 hq0 hq1 hX hNpos hY
  exact one_param_record_visible_of_offLineCopiesLocallyBounded hM hw hV0 hz₁ hσ hσ1 hre₁ ha hD₁
    hrec hk1 le_rfl hκV hVk hVr hH₀sq.le hρ hG1 hρV hρw hρL hρr hηm hmain

/-- **Elimination of the super-polynomial coherence drift as `a → 0⁺`.** Without bounded off-line
copies, `√a · recordLag w a σ → +∞` as `a → 0⁺` (`tendsto_sqrt_mul_recordLag`) because
`recordScale w a` contains `log(180 Γ(a)) ≍ log(1/a)`. With `recordScaleOffLine M a = √(a / (2(M + 1)))`,
the coherence-drift term `√a · (8 w e^{w/2} J_w / recordScaleOffLine M a)` equals the `a`-independent
constant `8 w e^{w/2} J_w √(2(M + 1))` for all `a > 0`. -/
theorem sqrt_mul_recordScaleOffLine_inv_eq (M : ℕ) (w : ℝ) {a : ℝ} (ha : 0 < a) :
    Real.sqrt a * (8 * w * Real.exp (w / 2) * bumpMass w / recordScaleOffLine M a) =
      8 * w * Real.exp (w / 2) * bumpMass w * Real.sqrt (2 * (M + 1)) := by
  rw [recordScaleOffLine, Real.sqrt_div ha.le]
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  have hsm : Real.sqrt (2 * (M + 1)) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp

/-- **Where the record of the one-parameter family sits without `oneParamRecordHeight`.** Under
`OffLineCopiesLocallyBounded M`, if `½ + z₀` is a `1/V`-near-top zero right of the line with
`‖h_w(-i z₀)‖ ≥ η > 0`, then the Legendre record `z₁` of `modScaledBump w 0` satisfies
`‖D(z₁)‖ ≥ 2η² / e` and `Re z₁ ≥ Re z₀ / 2` as soon as
`2 log(M (e^{w/2} B_w)² / η²) ≤ Re z₀ · V`, completely eliminating `oneParamRecordHeight w η` from
`one_param_record_facts`. -/
theorem one_param_record_facts_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w V : ℝ} (hw : 0 < w) (hV : 0 < V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re) {η : ℝ} (hη : 0 < η)
    (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    (htop : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → z.re ≤ z₀.re + 1 / V)
    (hV2 : 2 * Real.log (M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / η ^ 2) ≤ z₀.re * V) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w 0) z₁ ≠ 0 ∧ z₀.re / 2 ≤ z₁.re ∧
      2 * η ^ 2 / Real.exp 1 ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ ∧
      ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * Real.exp (z₁.re * V) := by
  set D := evenCoeff zetaZeroConfig (modScaledBump w 0) with hDdef
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  have hD₀ : 2 * η ^ 2 ≤ ‖D z₀‖ := by
    refine le_trans ?_ (two_mul_sq_le_norm_evenCoeff_zero hw hz₀)
    have := pow_le_pow_left₀ hη.le hηle 2
    linarith
  have hD₀ne : D z₀ ≠ 0 := fun h => by
    rw [h, norm_zero] at hD₀; nlinarith [pow_pos hη 2]
  obtain ⟨z₁, hz₁, hre₁, hD₁', hrec⟩ := exists_loud_record (contDiff_modScaledBump_two w 0)
    (modScaledBump_support hw 0) hV hD₀ne hre₀ htop
  have hD₁ : 2 * η ^ 2 / Real.exp 1 ≤ ‖D z₁‖ :=
    le_trans (div_le_div_of_nonneg_right hD₀ (Real.exp_pos 1).le) hD₁'
  refine ⟨z₁, hz₁, ?_, hD₁, hrec⟩
  have hDmax : ‖D z₁‖ ≤ 2 * M * K₀ :=
    norm_evenCoeff_modScaledBump_le_of_offLineCopiesLocallyBounded hM hw 0 hre₁.ne'
  have h1 := hrec z₀ hD₀ne hre₀
  have hD1pos : 0 < ‖D z₁‖ := norm_pos_iff.mpr hz₁
  have hMKpos : 0 < (M : ℝ) * K₀ := by linarith
  have h2 : Real.exp ((z₀.re - z₁.re) * V) ≤ M * K₀ / η ^ 2 := by
    have hE0 := Real.exp_pos (z₀.re * V)
    have hE1 := Real.exp_pos (z₁.re * V)
    have e : Real.exp ((z₀.re - z₁.re) * V) = Real.exp (z₀.re * V) / Real.exp (z₁.re * V) := by
      rw [← Real.exp_sub]; ring_nf
    rw [e, div_le_iff₀ hE1]
    have hchain : 2 * η ^ 2 * Real.exp (z₀.re * V) ≤ 2 * M * K₀ * Real.exp (z₁.re * V) :=
      calc 2 * η ^ 2 * Real.exp (z₀.re * V) ≤ ‖D z₀‖ * Real.exp (z₀.re * V) :=
            mul_le_mul_of_nonneg_right hD₀ hE0.le
        _ ≤ ‖D z₁‖ * Real.exp (z₁.re * V) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_right hDmax hE1.le
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hη 2)]
    linarith
  have h3 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp] at h3
  nlinarith

/-- The explicit visibility lag `V_0,off(M, w, η, δ₀)` of a `1/V`-near-top zero in the one-parameter
family under `OffLineCopiesLocallyBounded M`, completely free of `oneParamRecordHeight w η`. -/
def oneParamLagOffLine (M : ℕ) (w η δ₀ : ℝ) : ℝ :=
  max (recordLagOffLine M w (2 * η ^ 2 / Real.exp 1) (δ₀ / 2))
    (2 / δ₀ * |Real.log (M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / η ^ 2)|)

/-- **The one-parameter family sees near-top zeros at the height-free explicit lag
`oneParamLagOffLine M w η z₀.re`.** Under `OffLineCopiesLocallyBounded M`, any `1/V`-near-top zero
`½ + z₀` right of the line with `0 < η ≤ ‖h_w(-i z₀)‖` and `V ≥ oneParamLagOffLine M w η z₀.re`
produces `P_v < 0` for some `v ∈ [0, V]`. -/
theorem one_param_near_top_visible_at_explicit_lag_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖)
    {V : ℝ} (hV : oneParamLagOffLine M w η z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  have hVrec : recordLagOffLine M w (2 * η ^ 2 / Real.exp 1) (z₀.re / 2) ≤ V :=
    (le_max_left _ _).trans hV
  have hVlog : 2 / z₀.re * |Real.log (M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / η ^ 2)| ≤ V :=
    (le_max_right _ _).trans hV
  have hV0 : 0 < V := by
    have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
    have hH0 : 0 < recordScaleOffLine M (2 * η ^ 2 / Real.exp 1) := by
      unfold recordScaleOffLine; exact Real.sqrt_pos.mpr (by positivity)
    have h1 : 0 ≤ 4 / (z₀.re / 2) *
        (13 * π * recordOrderOffLine M w (2 * η ^ 2 / Real.exp 1) + 4) := by positivity
    have h2 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w /
        recordScaleOffLine M (2 * η ^ 2 / Real.exp 1) := by positivity
    unfold recordLagOffLine at hVrec
    linarith
  have hV2 : 2 * Real.log (M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / η ^ 2) ≤ z₀.re * V := by
    have h1 := mul_le_mul_of_nonneg_left hVlog hre₀.le
    have e : z₀.re * (2 / z₀.re * |Real.log (M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / η ^ 2)|) =
        2 * |Real.log (M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / η ^ 2)| := by field_simp
    have h2 := le_abs_self (Real.log (M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / η ^ 2))
    linarith
  have htop' : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 →
      z.re ≤ z₀.re + 1 / V := fun z hz => by
    have := htop _ (add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hz)
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    linarith
  obtain ⟨z₁, hz₁, hre₁, hD₁, hrec⟩ :=
    one_param_record_facts_of_offLineCopiesLocallyBounded hM hw hV0 hz₀ hre₀ hη hηle htop' hV2
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1 : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  exact one_param_record_visible_at_explicit_lag_of_offLineCopiesLocallyBounded hM hw hz₁
    (half_pos hre₀) (by linarith) hre₁ (by positivity) hD₁ hrec hVrec

/-! ### 3. Exact off-line/on-line mass decomposition and on-line non-cancellation law -/

/-- The total on-line coefficient mass `W_on(w, c) = ∑_{Re z = 0} ‖D_c(z)‖` of the bump of width `w`
modulated to height `c`. -/
def onLineEvenMass (w c : ℝ) : ℝ :=
  ∑' z : ℂ, if z.re = 0 then ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ else 0

/-- The total strictly off-line coefficient mass `W_off(w, c) = ∑_{Re z ≠ 0} ‖D_c(z)‖` of the bump
of width `w` modulated to height `c`. -/
def offLineEvenMass (w c : ℝ) : ℝ :=
  ∑' z : ℂ, if z.re = 0 then 0 else ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖

theorem onLineEvenMass_nonneg (w c : ℝ) : 0 ≤ onLineEvenMass w c :=
  tsum_nonneg fun z => by split_ifs <;> positivity

theorem offLineEvenMass_nonneg (w c : ℝ) : 0 ≤ offLineEvenMass w c :=
  tsum_nonneg fun z => by split_ifs <;> positivity

/-- **Exact on-line/off-line decomposition of the total modulated coefficient mass.** -/
theorem tsum_norm_evenCoeff_eq_onLineEvenMass_add_offLineEvenMass {w : ℝ} (hw : 0 < w) (c : ℝ) :
    ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ =
      onLineEvenMass w c + offLineEvenMass w c := by
  classical
  set D := evenCoeff zetaZeroConfig (modScaledBump w c) with hD
  have hs := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c)
  have hs_on : Summable (fun z : ℂ => if z.re = 0 then ‖D z‖ else 0) :=
    hs.of_nonneg_of_le (fun z => by split_ifs <;> positivity)
      (fun z => by split_ifs <;> [exact le_rfl; exact norm_nonneg _])
  have hs_off : Summable (fun z : ℂ => if z.re = 0 then 0 else ‖D z‖) :=
    hs.of_nonneg_of_le (fun z => by split_ifs <;> positivity)
      (fun z => by split_ifs <;> [exact norm_nonneg _; exact le_rfl])
  unfold onLineEvenMass offLineEvenMass
  rw [← hD, ← Summable.tsum_add hs_on hs_off]
  refine tsum_congr fun z => ?_
  split_ifs <;> ring

/-- **Unconditional logarithmic bound on the on-line coefficient mass.** -/
theorem onLineEvenMass_le_log {w : ℝ} (hw : 0 < w) (c : ℝ) :
    onLineEvenMass w c ≤
      16 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
        (xiLineTwoLogDerivConstant + Real.log (|c| + 4)) := by
  have h1 := tsum_norm_evenCoeff_modScaledBump_le hw c
  rw [tsum_norm_evenCoeff_eq_onLineEvenMass_add_offLineEvenMass hw c] at h1
  linarith [offLineEvenMass_nonneg w c]

/-- For any real argument `x ∈ ℝ`, `h_w(x)` is real (`conj h_w(x) = h_w(x)`), so its square equals
`‖h_w(x)‖²`. -/
theorem paperFT_scaledBump_ofReal_sq_eq_norm_sq (w x : ℝ) :
    paperFT (scaledBump w) (x : ℂ) ^ 2 = ((‖paperFT (scaledBump w) (x : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
  have hconj : conj (paperFT (scaledBump w) (x : ℂ)) = paperFT (scaledBump w) (x : ℂ) := by
    rw [conj_paperFT_scaledBump, Complex.conj_ofReal]
  rw [sq, ← hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **On-line non-cancellation law for modulated bumps.** At every on-line exponent `z` (`Re z = 0`),
the modulated coefficient `evenCoeff Z (modScaledBump w c) z` is a nonnegative real number equal to
its norm `‖evenCoeff Z (modScaledBump w c) z‖`. -/
theorem evenCoeff_modScaledBump_onLine_eq_norm (Z : ZeroConfig) {w : ℝ} (hw : 0 < w) (c : ℝ)
    {z : ℂ} (hz : z.re = 0) :
    evenCoeff Z (modScaledBump w c) z = ((‖evenCoeff Z (modScaledBump w c) z‖ : ℝ) : ℂ) := by
  have hlag : ∀ y : ℂ, y.re = 0 → ∃ r : ℝ, 0 ≤ r ∧
      lagCoeff Z (modScaledBump w c) y = (r : ℂ) := fun y hy => by
    by_cases hc : (1 / 2 + y) ∈ Z.carrier
    · refine ⟨(Z.mult (1 / 2 + y) : ℝ) *
        ‖paperFT (scaledBump w) ((y.im - c : ℝ) : ℂ)‖ ^ 2, by positivity, ?_⟩
      rw [lagCoeff_modScaledBump Z hw c hc]
      have harg : -(I * y) - (c : ℂ) = ((y.im - c : ℝ) : ℂ) := by
        apply Complex.ext <;> simp [hy]
      rw [harg, paperFT_scaledBump_ofReal_sq_eq_norm_sq]
      push_cast; ring
    · exact ⟨0, le_rfl, by rw [lagCoeff, Set.indicator_of_notMem hc, Complex.ofReal_zero]⟩
  obtain ⟨r₁, hr₁0, hr₁⟩ := hlag z hz
  obtain ⟨r₂, hr₂0, hr₂⟩ := hlag (conj z) (by simp [hz])
  have hev : evenCoeff Z (modScaledBump w c) z = ((r₁ + r₂ : ℝ) : ℂ) := by
    rw [evenCoeff, hr₁, hr₂, Complex.conj_ofReal, Complex.ofReal_add]
  have hnorm : ‖evenCoeff Z (modScaledBump w c) z‖ = r₁ + r₂ := by
    rw [hev, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  rw [hev, hnorm]

/-- **Exact on-line/off-line identity for `2 Re S(0)`.** Because every on-line coefficient has
`Re D_c(z) = ‖D_c(z)‖ ≥ 0`, on-line zeros in `2 Re S(0)` never cancel:
`2 Re S(0) = onLineEvenMass w c + ∑_{Re z ≠ 0} Re D_c(z)`. -/
theorem two_re_lagStructure_zero_eq_onLineEvenMass_add_offLine {w : ℝ} (hw : 0 < w) (c : ℝ) :
    2 * (lagStructure zetaZeroConfig (modScaledBump w c) 0).re =
      onLineEvenMass w c +
        ∑' z : ℂ, if z.re = 0 then 0 else (evenCoeff zetaZeroConfig (modScaledBump w c) z).re := by
  classical
  set b := modScaledBump w c with hb
  set D := evenCoeff zetaZeroConfig b with hD
  have h0 := two_re_lagStructure_eq zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c) 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
  have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c)
  have hs_re : Summable (fun z : ℂ => (D z).re) :=
    (Complex.hasSum_re h0.1.hasSum).summable
  have hs_on : Summable (fun z : ℂ => if z.re = 0 then ‖D z‖ else 0) :=
    hsD.of_nonneg_of_le (fun z => by split_ifs <;> positivity)
      (fun z => by split_ifs <;> [exact le_rfl; exact norm_nonneg _])
  have hs_off : Summable (fun z : ℂ => if z.re = 0 then 0 else (D z).re) :=
    Summable.of_norm_bounded hsD fun z => by
      split_ifs
      · rw [Real.norm_zero]; exact norm_nonneg _
      · rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have hre_eq : 2 * (lagStructure zetaZeroConfig b 0).re = ∑' z : ℂ, (D z).re := by
    have := congrArg Complex.re h0.2
    simpa [Complex.re_tsum h0.1] using this
  rw [hre_eq]
  unfold onLineEvenMass
  rw [← hb, ← hD, ← Summable.tsum_add hs_on hs_off]
  refine tsum_congr fun z => ?_
  by_cases hz : z.re = 0
  · rw [if_pos hz, if_pos hz, add_zero, hD, hb,
      evenCoeff_modScaledBump_onLine_eq_norm zetaZeroConfig hw c hz, Complex.ofReal_re]
  · rw [if_neg hz, if_neg hz, zero_add]

/-- **Deviation of `2 Re S(0)` from the on-line mass is bounded by the off-line mass.** -/
theorem abs_two_re_lagStructure_zero_sub_onLineEvenMass_le {w : ℝ} (hw : 0 < w) (c : ℝ) :
    |2 * (lagStructure zetaZeroConfig (modScaledBump w c) 0).re - onLineEvenMass w c| ≤
      offLineEvenMass w c := by
  classical
  set D := evenCoeff zetaZeroConfig (modScaledBump w c) with hD
  have h := two_re_lagStructure_zero_eq_onLineEvenMass_add_offLine hw c
  have heq : 2 * (lagStructure zetaZeroConfig (modScaledBump w c) 0).re - onLineEvenMass w c =
      ∑' z : ℂ, if z.re = 0 then 0 else (D z).re := by linarith
  rw [heq, ← Real.norm_eq_abs]
  have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c)
  have hs_off : Summable (fun z : ℂ => if z.re = 0 then 0 else ‖D z‖) :=
    hsD.of_nonneg_of_le (fun z => by split_ifs <;> positivity)
      (fun z => by split_ifs <;> [exact norm_nonneg _; exact le_rfl])
  have hpt : ∀ z : ℂ, ‖if z.re = 0 then (0 : ℝ) else (D z).re‖ ≤
      (if z.re = 0 then 0 else ‖D z‖) := fun z => by
    split_ifs
    · simp
    · rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have hs_re : Summable (fun z : ℂ => ‖if z.re = 0 then (0 : ℝ) else (D z).re‖) :=
    hs_off.of_nonneg_of_le (fun _ => norm_nonneg _) hpt
  exact (norm_tsum_le_tsum_norm hs_re).trans (Summable.tsum_le_tsum hpt hs_re hs_off)

/-- **Height-uniform inverse-fourth-power sum over strictly off-line exponents.** Under
`OffLineCopiesLocallyBounded M`, any finite set `S` of strictly off-line exponents (`Re z ≠ 0`,
`½ + z ∈ zetaZeroConfig.carrier`) satisfies `∑_{z ∈ S} (1 + |Im z - c|)⁻⁴ ≤ 12 M`, uniformly in the
center `c ∈ ℝ`. -/
theorem sum_offLine_inv_four_le_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) (c : ℝ) (S : Finset ℂ)
    (hS : ∀ z ∈ S, (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ z.re ≠ 0) :
    ∑ z ∈ S, 1 / (1 + |z.im - c|) ^ 4 ≤ 12 * M := by
  classical
  set j : ℂ → ℤ := fun z => ⌊z.im - c⌋ with hj
  set J := S.image j with hJ
  rw [← Finset.sum_fiberwise_of_maps_to (g := j) (t := J) fun z hz => Finset.mem_image_of_mem _ hz]
  have hfib : ∀ k ∈ J, ∑ z ∈ S with j z = k, 1 / (1 + |z.im - c|) ^ 4 ≤
      M * (((|k| : ℝ) + 1) / max 1 (windowDist k) ^ 3) := by
    intro k _
    set Sk := S.filter fun z => j z = k with hSk
    have hwin : ∀ z ∈ Sk, (k : ℝ) ≤ z.im - c ∧ z.im - c < k + 1 := fun z hz => by
      rw [hSk, Finset.mem_filter] at hz
      have h1 := Int.floor_le (z.im - c)
      have h2 := Int.lt_floor_add_one (z.im - c)
      rw [hj] at hz; simp only at hz; rw [hz.2] at *
      exact ⟨by linarith, by linarith⟩
    have hcard_nat : Sk.card ≤ M :=
      card_offLine_window_le_of_offLineCopiesLocallyBounded hM (c + k) Sk fun z hz => by
        have hw := hwin z hz
        have hzS := hS z (Finset.mem_filter.mp hz).1
        refine ⟨hzS.1, hzS.2, ?_⟩
        rw [abs_le]
        constructor <;> linarith [hw.1, hw.2]
    have hcard : (Sk.card : ℝ) ≤ M * ((|k| : ℝ) + 1) := by
      have h1 : (Sk.card : ℝ) ≤ M := by exact_mod_cast hcard_nat
      have h2 : (1 : ℝ) ≤ (|k| : ℝ) + 1 := by linarith [abs_nonneg (k : ℝ)]
      calc (Sk.card : ℝ) ≤ M * 1 := by linarith
        _ ≤ M * ((|k| : ℝ) + 1) := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg M)
    have hterm : ∀ z ∈ Sk, 1 / (1 + |z.im - c|) ^ 4 ≤ 1 / max 1 (windowDist k) ^ 3 := fun z hz => by
      have hd : windowDist k ≤ 1 + |z.im - c| := by
        have hw := hwin z hz
        unfold windowDist
        split_ifs with hk
        · have h0 : (0 : ℝ) ≤ k := by exact_mod_cast hk
          rw [abs_of_nonneg (by linarith [hw.1])]; linarith [hw.1]
        · push Not at hk
          have : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast (show k + 1 ≤ 0 by omega)
          rw [abs_of_neg (by linarith)]; linarith
      have hmax : max 1 (windowDist k) ≤ 1 + |z.im - c| :=
        max_le (by linarith [abs_nonneg (z.im - c)]) hd
      have hpow : max 1 (windowDist k) ^ 3 ≤ (1 + |z.im - c|) ^ 4 :=
        (pow_le_pow_left₀ (le_max_left 1 _) hmax 3).trans
          (pow_le_pow_right₀ (by linarith [abs_nonneg (z.im - c)]) (by omega))
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
    calc ∑ z ∈ Sk, 1 / (1 + |z.im - c|) ^ 4 ≤ ∑ _z ∈ Sk, 1 / max 1 (windowDist k) ^ 3 :=
          Finset.sum_le_sum hterm
      _ = Sk.card * (1 / max 1 (windowDist k) ^ 3) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M * ((|k| : ℝ) + 1)) * (1 / max 1 (windowDist k) ^ 3) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = M * (((|k| : ℝ) + 1) / max 1 (windowDist k) ^ 3) := by ring
  calc ∑ k ∈ J, ∑ z ∈ S with j z = k, 1 / (1 + |z.im - c|) ^ 4
      ≤ ∑ k ∈ J, M * (((|k| : ℝ) + 1) / max 1 (windowDist k) ^ 3) := Finset.sum_le_sum hfib
    _ = M * ∑ k ∈ J, ((|k| : ℝ) + 1) / max 1 (windowDist k) ^ 3 := by rw [Finset.mul_sum]
    _ ≤ M * (3 * (1 / 1 ^ 3 + 3)) :=
        mul_le_mul_of_nonneg_left (sum_window_weight_le one_pos J) (Nat.cast_nonneg M)
    _ = 12 * M := by ring

/-- **Height-uniform bound on the total off-line modulated coefficient mass.** Under
`OffLineCopiesLocallyBounded M`, `offLineEvenMass w c ≤ 24 M² (e^{w/2} B_w)²` uniformly for all
modulation centers `c ∈ ℝ`. -/
theorem offLineEvenMass_le_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) (c : ℝ) :
    offLineEvenMass w c ≤ 24 * (M : ℝ) ^ 2 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := by
  classical
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  have hK0 : 0 ≤ K₀ := by positivity
  have hlag_sum : ∀ F : Finset ℂ,
      ∑ z ∈ F, (if z.re = 0 then 0 else ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖) ≤
        12 * (M : ℝ) ^ 2 * K₀ := fun F => by
    set S := F.filter (fun z => (1 / 2 + z) ∈ zetaZeroConfig.carrier ∧ z.re ≠ 0) with hS
    have h1 : ∑ z ∈ F, (if z.re = 0 then 0 else ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖) ≤
        ∑ z ∈ S, (M : ℝ) * K₀ * (1 / (1 + |z.im - c|) ^ 4) := by
      rw [hS, Finset.sum_filter]
      refine Finset.sum_le_sum fun z _ => ?_
      by_cases hz : z.re = 0
      · simp [hz]
      · rw [if_neg hz]
        by_cases hc : (1 / 2 + z) ∈ zetaZeroConfig.carrier
        · rw [if_pos ⟨hc, hz⟩]
          have hle := norm_lagCoeff_modScaledBump_le zetaZeroConfig hw c hc
          have hm : (zetaZeroConfig.mult (1 / 2 + z) : ℝ) ≤ M := by
            exact_mod_cast mult_offLine_zeta_le_of_offLineCopiesLocallyBounded hM hc (by
              intro h; apply hz; have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
              linarith)
          calc ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖
              ≤ (zetaZeroConfig.mult (1 / 2 + z) : ℝ) * K₀ / (1 + |z.im - c|) ^ 4 := hle
            _ ≤ (M : ℝ) * K₀ / (1 + |z.im - c|) ^ 4 := by gcongr
            _ = (M : ℝ) * K₀ * (1 / (1 + |z.im - c|) ^ 4) := by ring
        · rw [if_neg (fun h => hc h.1), lagCoeff, Set.indicator_of_notMem hc, norm_zero]
    have h2 := sum_offLine_inv_four_le_of_offLineCopiesLocallyBounded hM c S
      fun z hz => (Finset.mem_filter.mp hz).2
    calc ∑ z ∈ F, (if z.re = 0 then 0 else ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖)
        ≤ ∑ z ∈ S, (M : ℝ) * K₀ * (1 / (1 + |z.im - c|) ^ 4) := h1
      _ = (M : ℝ) * K₀ * ∑ z ∈ S, 1 / (1 + |z.im - c|) ^ 4 := by rw [Finset.mul_sum]
      _ ≤ (M : ℝ) * K₀ * (12 * M) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 12 * (M : ℝ) ^ 2 * K₀ := by ring
  have hfin : ∀ F : Finset ℂ,
      ∑ z ∈ F, (if z.re = 0 then 0 else ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖) ≤
        24 * (M : ℝ) ^ 2 * K₀ := fun F => by
    have hconj : Function.Injective fun z : ℂ => conj z := star_injective
    have hpt : ∀ z : ℂ, (if z.re = 0 then 0 else ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖) ≤
        (if z.re = 0 then 0 else ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖) +
          (if (conj z).re = 0 then 0 else
            ‖lagCoeff zetaZeroConfig (modScaledBump w c) (conj z)‖) := fun z => by
      simp only [Complex.conj_re]
      split_ifs
      · linarith
      · rw [evenCoeff]
        exact (norm_add_le _ _).trans (le_of_eq (by rw [Complex.norm_conj]))
    calc ∑ z ∈ F, (if z.re = 0 then 0 else ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖)
        ≤ ∑ z ∈ F, ((if z.re = 0 then 0 else ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖) +
            (if (conj z).re = 0 then 0 else
              ‖lagCoeff zetaZeroConfig (modScaledBump w c) (conj z)‖)) :=
          Finset.sum_le_sum fun z _ => hpt z
      _ = ∑ z ∈ F, (if z.re = 0 then 0 else ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖) +
            ∑ z ∈ F.image (fun z => conj z),
              (if z.re = 0 then 0 else ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖) := by
          rw [Finset.sum_add_distrib, Finset.sum_image fun a _ b _ h => hconj h]
      _ ≤ 12 * (M : ℝ) ^ 2 * K₀ + 12 * (M : ℝ) ^ 2 * K₀ :=
          add_le_add (hlag_sum F) (hlag_sum _)
      _ = 24 * (M : ℝ) ^ 2 * K₀ := by ring
  have hsD := summable_norm_evenCoeff zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c)
  have hs_off : Summable (fun z : ℂ =>
      if z.re = 0 then 0 else ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖) :=
    hsD.of_nonneg_of_le (fun z => by split_ifs <;> positivity)
      (fun z => by split_ifs <;> [exact norm_nonneg _; exact le_rfl])
  exact hs_off.tsum_le_of_sum_le hfin

/-- **Combined mass bound in terms of on-line mass and local off-line multiplicity.** Under
`OffLineCopiesLocallyBounded M`, the unamplified mass terms `|2 Re S(0)| + ∑ ‖D_c(z)‖` of any
modulated bump `modScaledBump w c` are at most `2 · onLineEvenMass w c + 48 M² (e^{w/2} B_w)²`,
isolating the on-line zero mass as the sole height-dependent datum. -/
theorem mass_le_onLineEvenMass_add_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) (c : ℝ) :
    |2 * (lagStructure zetaZeroConfig (modScaledBump w c) 0).re| +
        ∑' z : ℂ, ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      2 * onLineEvenMass w c + 48 * (M : ℝ) ^ 2 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := by
  have h1 := abs_two_re_lagStructure_zero_le zetaZeroConfig temperedConfig_zetaZeroConfig
    (contDiff_modScaledBump_two w c) (modScaledBump_support hw c)
  have h2 := tsum_norm_evenCoeff_eq_onLineEvenMass_add_offLineEvenMass hw c
  have h3 := offLineEvenMass_le_of_offLineCopiesLocallyBounded hM hw c
  linarith

/-! ### 4. Modulated (`c = γ₀`) visibility in terms of on-line mass and doubly-logarithmic lag -/

/-- **Two-sided decay of strictly off-line modulated coefficients without `log |Im z|`.** Under
`OffLineCopiesLocallyBounded M`, every strictly off-line exponent `z` (`Re z ≠ 0`) satisfies
`‖D_c(z)‖ ≤ M (e^{w/2} B_w)² ((1 + |Im z - c|)⁻⁴ + (1 + |Im z + c|)⁻⁴)`, replacing
`40 log(180 |Im z|)` in `norm_evenCoeff_modScaledBump_le` by `M`. -/
theorem norm_evenCoeff_modScaledBump_le_decay_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) (c : ℝ) {z : ℂ} (hz : z.re ≠ 0) :
    ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      (M : ℝ) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
        (1 / (1 + |z.im - c|) ^ 4 + 1 / (1 + |z.im + c|) ^ 4) := by
  set K := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 : ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      (M : ℝ) * K / (1 + |z.im - c|) ^ 4 := by
    by_cases hc : (1 / 2 + z) ∈ zetaZeroConfig.carrier
    · refine (norm_lagCoeff_modScaledBump_le zetaZeroConfig hw c hc).trans ?_
      have hm : (zetaZeroConfig.mult (1 / 2 + z) : ℝ) ≤ M := by
        exact_mod_cast mult_offLine_zeta_le_of_offLineCopiesLocallyBounded hM hc (by
          intro h; apply hz; have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
          linarith)
      gcongr
    · rw [lagCoeff, Set.indicator_of_notMem hc, norm_zero]; positivity
  have h2 : ‖lagCoeff zetaZeroConfig (modScaledBump w c) (conj z)‖ ≤
      (M : ℝ) * K / (1 + |z.im + c|) ^ 4 := by
    by_cases hc : (1 / 2 + conj z) ∈ zetaZeroConfig.carrier
    · refine (norm_lagCoeff_modScaledBump_le zetaZeroConfig hw c hc).trans ?_
      have hm : (zetaZeroConfig.mult (1 / 2 + conj z) : ℝ) ≤ M := by
        exact_mod_cast mult_offLine_zeta_le_of_offLineCopiesLocallyBounded hM hc (by
          intro h; apply hz; have e : (1 / 2 + conj z).re = 1 / 2 + z.re := by simp
          linarith)
      rw [Complex.conj_im, show |-z.im - c| = |z.im + c| by
        rw [show -z.im - c = -(z.im + c) by ring, abs_neg]]
      gcongr
    · rw [lagCoeff, Set.indicator_of_notMem hc, norm_zero]; positivity
  calc ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖
      ≤ ‖lagCoeff zetaZeroConfig (modScaledBump w c) z‖ +
          ‖lagCoeff zetaZeroConfig (modScaledBump w c) (conj z)‖ := by
        rw [evenCoeff]; exact (norm_add_le _ _).trans (le_of_eq (by rw [Complex.norm_conj]))
    _ ≤ _ := by
        rw [mul_add, mul_one_div, mul_one_div]; exact add_le_add h1 h2

/-- **Center coefficient lower bound without `log z₀.im`.** Under `OffLineCopiesLocallyBounded M`,
for a zero `½ + z₀` right of the line (`Re z₀ > 0`, `Im z₀ > 0`), the reflected zero `½ + z̄₀` is
also off-line and has multiplicity `≤ M`, so
`‖D_{Im z₀}(z₀)‖ ≥ a_w² - M (e^{w/2} B_w)² / (1 + 2 Im z₀)⁴`. -/
theorem norm_evenCoeff_modScaledBump_center_ge_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre : 0 < z₀.re) (him : 0 < z₀.im) :
    centerAmplitude w ^ 2 -
        (M : ℝ) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + 2 * z₀.im) ^ 4 ≤
      ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₀‖ := by
  have hmain : centerAmplitude w ^ 2 ≤
      ‖lagCoeff zetaZeroConfig (modScaledBump w z₀.im) z₀‖ := by
    rw [lagCoeff_modScaledBump zetaZeroConfig hw _ hz₀, norm_mul, norm_pow, Complex.norm_natCast]
    have hpt : -(I * z₀) - (z₀.im : ℂ) = ((-z₀.re : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hpt]
    have hstrip := zetaZeroConfig.strip _ hz₀
    have hre2 : z₀.re ≤ 1 / 2 := by
      have h2 : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
      linarith [hstrip.2, h2]
    have hlow := norm_paperFT_scaledBump_I_mul_ge hw (-z₀.re)
    have hb : centerAmplitude w ≤
        4 * w * (Real.exp (-(w * |-z₀.re|)) * (∫ u, weilBump u)) := by
      unfold centerAmplitude
      have hint : 0 ≤ ∫ u, weilBump u := integral_nonneg fun u => weilBump.nonneg
      gcongr
      rw [abs_neg, abs_of_pos hre]; nlinarith
    have hm : (1 : ℝ) ≤ zetaZeroConfig.mult (1 / 2 + z₀) := by
      exact_mod_cast zetaZeroConfig.one_le_mult _ hz₀
    have h0 : 0 ≤ centerAmplitude w := (centerAmplitude_pos hw).le
    have hsq := pow_le_pow_left₀ h0 (hb.trans hlow) 2
    calc centerAmplitude w ^ 2
        ≤ ‖paperFT (scaledBump w) (((-z₀.re : ℝ) : ℂ) * I)‖ ^ 2 := hsq
      _ ≤ (zetaZeroConfig.mult (1 / 2 + z₀) : ℝ) *
            ‖paperFT (scaledBump w) (((-z₀.re : ℝ) : ℂ) * I)‖ ^ 2 :=
          le_mul_of_one_le_left (by positivity) hm
  have hconj : ‖lagCoeff zetaZeroConfig (modScaledBump w z₀.im) (conj z₀)‖ ≤
      (M : ℝ) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + 2 * z₀.im) ^ 4 := by
    by_cases hc : (1 / 2 + conj z₀) ∈ zetaZeroConfig.carrier
    · refine (norm_lagCoeff_modScaledBump_le zetaZeroConfig hw _ hc).trans ?_
      have hm : (zetaZeroConfig.mult (1 / 2 + conj z₀) : ℝ) ≤ M := by
        exact_mod_cast mult_offLine_zeta_le_of_offLineCopiesLocallyBounded hM hc (by
          intro h; have e : (1 / 2 + conj z₀).re = 1 / 2 + z₀.re := by simp
          linarith)
      rw [Complex.conj_im, show |-z₀.im - z₀.im| = 2 * z₀.im by
        rw [show -z₀.im - z₀.im = -(2 * z₀.im) by ring, abs_neg, abs_of_pos (by linarith)]]
      gcongr
    · rw [lagCoeff, Set.indicator_of_notMem hc, norm_zero]; positivity
  calc centerAmplitude w ^ 2 -
        (M : ℝ) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + 2 * z₀.im) ^ 4
      ≤ ‖lagCoeff zetaZeroConfig (modScaledBump w z₀.im) z₀‖ -
          ‖lagCoeff zetaZeroConfig (modScaledBump w z₀.im) (conj z₀)‖ := by linarith
    _ ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₀‖ := by
        rw [evenCoeff]
        have := norm_sub_norm_le (lagCoeff zetaZeroConfig (modScaledBump w z₀.im) z₀)
          (-conj (lagCoeff zetaZeroConfig (modScaledBump w z₀.im) (conj z₀)))
        rw [norm_neg, Complex.norm_conj, sub_neg_eq_add] at this
        exact this

/-- **Loud off-line coefficients sit near `±c` without `log(90 c)`.** Under
`OffLineCopiesLocallyBounded M`, any strictly off-line exponent `z` (`Re z ≠ 0`) with
`‖D_c(z)‖ ≥ ε` and `2 M (e^{w/2} B_w)² / (1 + c / 2)⁴ < ε` satisfies `c / 2 ≤ |Im z|`. -/
theorem half_le_abs_im_of_norm_evenCoeff_modScaledBump_ge_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w c ε : ℝ} (hw : 0 < w) (hc : 0 < c) {z : ℂ}
    (hz : z.re ≠ 0) (hge : ε ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖)
    (hsmall : 2 * (M : ℝ) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + c / 2) ^ 4 < ε) :
    c / 2 ≤ |z.im| := by
  by_contra hy; push Not at hy
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  have hd1 : c / 2 ≤ |z.im - c| := by
    have := abs_sub_abs_le_abs_sub c z.im
    rw [abs_of_pos hc, abs_sub_comm] at this; linarith
  have hd2 : c / 2 ≤ |z.im + c| := by
    have := abs_sub_abs_le_abs_sub c (-z.im)
    rw [abs_of_pos hc, abs_neg, sub_neg_eq_add, add_comm] at this; linarith
  have hb := norm_evenCoeff_modScaledBump_le_decay_of_offLineCopiesLocallyBounded hM hw c hz
  rw [← hK₀] at hb
  have hq : (0 : ℝ) < (1 + c / 2) ^ 4 := by positivity
  have hi1 : 1 / (1 + |z.im - c|) ^ 4 ≤ 1 / (1 + c / 2) ^ 4 :=
    div_le_div_of_nonneg_left (by norm_num) hq (pow_le_pow_left₀ (by positivity) (by linarith) 4)
  have hi2 : 1 / (1 + |z.im + c|) ^ 4 ≤ 1 / (1 + c / 2) ^ 4 :=
    div_le_div_of_nonneg_left (by norm_num) hq (pow_le_pow_left₀ (by positivity) (by linarith) 4)
  have hle : ‖evenCoeff zetaZeroConfig (modScaledBump w c) z‖ ≤
      2 * (M : ℝ) * K₀ / (1 + c / 2) ^ 4 := by
    refine hb.trans ?_
    calc (M : ℝ) * K₀ * (1 / (1 + |z.im - c|) ^ 4 + 1 / (1 + |z.im + c|) ^ 4)
        ≤ (M : ℝ) * K₀ * (1 / (1 + c / 2) ^ 4 + 1 / (1 + c / 2) ^ 4) :=
          mul_le_mul_of_nonneg_left (add_le_add hi1 hi2) (by positivity)
      _ = 2 * (M : ℝ) * K₀ / (1 + c / 2) ^ 4 := by ring
  linarith

/-- The threshold height `T_off(M, w) = 1 + 192(M + 1)(e^{w/2} B_w)² / a_w²` beyond which the
reflected term of any off-line zero is negligible at the center, loud off-line records sit at
`|Im z₁| ≥ γ₀ / 2`, and the reflected-zero error in phase coherence is at most `H₀² / 16`. -/
def nearTopHeightOffLine (M : ℕ) (w : ℝ) : ℝ :=
  1 + 192 * (M + 1) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2

theorem nearTopHeightOffLine_conditions {M : ℕ} {w γ : ℝ} (hw : 0 < w)
    (hγ : nearTopHeightOffLine M w ≤ γ) :
    1 ≤ γ ∧
      (M : ℝ) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + 2 * γ) ^ 4 ≤
        centerAmplitude w ^ 2 / 2 ∧
      2 * (M : ℝ) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + γ / 2) ^ 4 <
        centerAmplitude w ^ 2 / (2 * Real.exp 1) ∧
      ((M : ℝ) + 1) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + γ) ^ 4 ≤
        centerAmplitude w ^ 2 / (2 * Real.exp 1) / 32 := by
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  set a := centerAmplitude w with ha
  have ha0 : 0 < a := centerAmplitude_pos hw
  have hK0 : 0 ≤ K₀ := by positivity
  have hT : 1 + 192 * ((M : ℝ) + 1) * K₀ / a ^ 2 ≤ γ := hγ
  have hγ1 : 1 ≤ γ := by
    have : 0 ≤ 192 * ((M : ℝ) + 1) * K₀ / a ^ 2 := by positivity
    linarith
  have h1γ : 192 * ((M : ℝ) + 1) * K₀ < a ^ 2 * (1 + γ) := by
    have hlt : 192 * ((M : ℝ) + 1) * K₀ / a ^ 2 < 1 + γ := by linarith
    rwa [div_lt_iff₀ (by positivity)] at hlt
  have hpow1 : 1 + γ ≤ (1 + γ) ^ 4 := by
    simpa using pow_le_pow_right₀ (by linarith : 1 ≤ 1 + γ) (by omega : 1 ≤ 4)
  have hpow2 : 1 + γ ≤ (1 + 2 * γ) ^ 4 :=
    (by linarith : 1 + γ ≤ 1 + 2 * γ).trans
      (by simpa using pow_le_pow_right₀ (by linarith : 1 ≤ 1 + 2 * γ) (by omega : 1 ≤ 4))
  have hpowhalf : 1 + γ ≤ (1 + γ / 2) ^ 4 := by
    have hsq : 1 + γ ≤ (1 + γ / 2) ^ 2 := by nlinarith [sq_nonneg γ]
    exact hsq.trans (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + γ / 2) (by omega : 2 ≤ 4))
  have hE : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hE0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  refine ⟨hγ1, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_left hpow2 (show 0 ≤ a ^ 2 / 2 by positivity)
    nlinarith
  · rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hpowhalf (show 0 ≤ a ^ 2 by positivity)
    nlinarith
  · rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hpow1 (show 0 ≤ a ^ 2 by positivity)
    nlinarith

/-- **Where the loud record of a near-top zero sits without `recordHeightEnvelope`.** Under
`OffLineCopiesLocallyBounded M`, for a `1/V`-near-top zero `½ + z₀` right of the line above
`nearTopHeightOffLine M w`, the Legendre record `z₁` of `modScaledBump w z₀.im` has
`‖D(z₁)‖ ≥ a_w² / (2e)`, `|Im z₁| ≥ z₀.im / 2`, and `Re z₁ ≥ Re z₀ / 2` as soon as
`2 log(4 M (e^{w/2} B_w)² / a_w²) ≤ Re z₀ · V`, completely eliminating `recordHeightEnvelope w z₀.im`
from `near_top_record_facts`. -/
theorem near_top_record_facts_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w V : ℝ} (hw : 0 < w) (hV : 0 < V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeightOffLine M w ≤ z₀.im)
    (htop : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → z.re ≤ z₀.re + 1 / V)
    (hV2 : 2 * Real.log (4 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
        centerAmplitude w ^ 2) ≤ z₀.re * V) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ z₀.re / 2 ≤ z₁.re ∧
      z₀.im / 2 ≤ |z₁.im| ∧
      centerAmplitude w ^ 2 / (2 * Real.exp 1) ≤
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ ∧
      ∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ * Real.exp (z₁.re * V) := by
  obtain ⟨hγ1, hΓ, hsmall, -⟩ := nearTopHeightOffLine_conditions hw hTw
  have hpos₀ : 0 < z₀.im := by linarith
  set D := evenCoeff zetaZeroConfig (modScaledBump w z₀.im) with hDdef
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  set a := centerAmplitude w with ha
  have ha0 : 0 < a := centerAmplitude_pos hw
  have hD₀ : a ^ 2 / 2 ≤ ‖D z₀‖ := by
    have := norm_evenCoeff_modScaledBump_center_ge_of_offLineCopiesLocallyBounded hM hw hz₀ hre₀ hpos₀
    linarith
  have hD₀ne : D z₀ ≠ 0 := fun h => by rw [h, norm_zero] at hD₀; nlinarith [pow_pos ha0 2]
  obtain ⟨z₁, hz₁, hre₁, hD₁', hrec⟩ := exists_loud_record (contDiff_modScaledBump_two w z₀.im)
    (modScaledBump_support hw z₀.im) hV hD₀ne hre₀ htop
  have hD₁ : a ^ 2 / (2 * Real.exp 1) ≤ ‖D z₁‖ := by
    refine le_trans (le_of_eq ?_) (le_trans (div_le_div_of_nonneg_right hD₀ (Real.exp_pos 1).le) hD₁')
    ring
  have hlow : z₀.im / 2 ≤ |z₁.im| :=
    half_le_abs_im_of_norm_evenCoeff_modScaledBump_ge_of_offLineCopiesLocallyBounded hM hw hpos₀
      hre₁.ne' hD₁ hsmall
  refine ⟨z₁, hz₁, ?_, hlow, hD₁, hrec⟩
  have hDmax : ‖D z₁‖ ≤ 2 * M * K₀ :=
    norm_evenCoeff_modScaledBump_le_of_offLineCopiesLocallyBounded hM hw z₀.im hre₁.ne'
  have h1 := hrec z₀ hD₀ne hre₀
  have hD1pos : 0 < ‖D z₁‖ := norm_pos_iff.mpr hz₁
  have h2 : Real.exp ((z₀.re - z₁.re) * V) ≤ 4 * M * K₀ / a ^ 2 := by
    have hE0 := Real.exp_pos (z₀.re * V)
    have hE1 := Real.exp_pos (z₁.re * V)
    have e : Real.exp ((z₀.re - z₁.re) * V) = Real.exp (z₀.re * V) / Real.exp (z₁.re * V) := by
      rw [← Real.exp_sub]; ring_nf
    rw [e, div_le_iff₀ hE1]
    have hchain : a ^ 2 / 2 * Real.exp (z₀.re * V) ≤ 2 * M * K₀ * Real.exp (z₁.re * V) :=
      calc a ^ 2 / 2 * Real.exp (z₀.re * V) ≤ ‖D z₀‖ * Real.exp (z₀.re * V) :=
            mul_le_mul_of_nonneg_right hD₀ hE0.le
        _ ≤ ‖D z₁‖ * Real.exp (z₁.re * V) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_right hDmax hE1.le
    rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos ha0 2)]
    linarith
  have h3 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp] at h3
  nlinarith

/-- **Height-free transform lower bound for a loud off-line modulated coefficient.** Under
`OffLineCopiesLocallyBounded M`, any strictly off-line zero `½ + y` (`Re y ≠ 0`, `Im y ≥ 0`) with
`‖D_c(y)‖ ≥ ε₀` and `H₀² ≤ ε₀ / (M + 1) - (e^{w/2} B_w)² / (1 + c)⁴` satisfies
`H₀ ≤ ‖h_w(-i y - c)‖`, completely eliminating `40 log(180 Γ')` from `le_norm_paperFT_of_loud`. -/
theorem le_norm_paperFT_of_loud_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {c : ℝ} (hc : 0 ≤ c) {y : ℂ}
    (hy : (1 / 2 + y) ∈ zetaZeroConfig.carrier) (hy_off : y.re ≠ 0) (him : 0 ≤ y.im)
    {ε₀ H₀ : ℝ} (hD : ε₀ ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w c) y‖)
    (hH : H₀ ^ 2 ≤ ε₀ / (M + 1) - (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + c) ^ 4) :
    H₀ ≤ ‖paperFT (scaledBump w) (-(I * y) - c)‖ := by
  have hstrip := zetaZeroConfig.strip _ hy
  have hre : |y.re| ≤ 1 / 2 := by
    have e : (1 / 2 + y).re = 1 / 2 + y.re := by simp
    rw [abs_le]; constructor <;> linarith [hstrip.1, hstrip.2]
  have hmM : (zetaZeroConfig.mult (1 / 2 + y) : ℝ) ≤ M := by
    exact_mod_cast mult_offLine_zeta_le_of_offLineCopiesLocallyBounded hM hy (by
      intro h; apply hy_off; have e : (1 / 2 + y).re = 1 / 2 + y.re := by simp
      linarith)
  have hdec := evenCoeff_modScaledBump_eq_mult_mul hw c hy
  set h := paperFT (scaledBump w) (-(I * y) - c) with hh
  set ε := conj (paperFT (scaledBump w) (-(I * conj y) - c) ^ 2) with hε
  have hεn := norm_reflected_le hw hc him hre
  rw [← hε] at hεn
  have hDn : ‖evenCoeff zetaZeroConfig (modScaledBump w c) y‖ ≤
      (zetaZeroConfig.mult (1 / 2 + y) : ℝ) * (‖h‖ ^ 2 + ‖ε‖) := by
    rw [hdec, norm_mul, Complex.norm_natCast]
    refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (le_of_eq ?_)) (Nat.cast_nonneg _)
    rw [norm_pow]
  have hpos : (0 : ℝ) < M + 1 := by positivity
  have h1 : ε₀ / (M + 1) ≤ ‖h‖ ^ 2 + ‖ε‖ := by
    rw [div_le_iff₀ hpos]
    have h2 : (zetaZeroConfig.mult (1 / 2 + y) : ℝ) * (‖h‖ ^ 2 + ‖ε‖) ≤
        ((M : ℝ) + 1) * (‖h‖ ^ 2 + ‖ε‖) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith [hD.trans hDn]
  have h2 : H₀ ^ 2 ≤ ‖h‖ ^ 2 := by linarith
  exact le_of_sq_le_sq (by simpa using h2) (norm_nonneg _) |>.trans le_rfl

/-- **Coherence of an off-line record and its near companion without `log(180 Γ)`.** Under
`OffLineCopiesLocallyBounded M`, if `½ + z₁` is strictly off-line (`Re z₁ ≠ 0`) with
`|Im z₁| ≥ γ₀ / 2` and `‖D_{γ₀}(z₁)‖ ≥ ε₀`, then any zero `½ + z` within `‖z - z₁‖ ≤ ½` has
`Re(D_{γ₀}(z) conj D_{γ₀}(z₁)) ≥ 0` as soon as `H₀² ≤ ε₀ / (M + 1) - K₀ / (1 + γ₀)⁴`,
`K₀ / (1 + γ₀)⁴ ≤ H₀² / 16`, `8 w e^{w/2} J_w ‖z - z₁‖ ≤ H₀`, and `w ‖z - z₁‖ ≤ 1`. -/
theorem re_twin_mul_conj_nonneg_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {γ₀ : ℝ} (hγ₀ : 1 ≤ γ₀) {z₁ z : ℂ}
    (hz₁ : (1 / 2 + z₁) ∈ zetaZeroConfig.carrier) (hz₁_off : z₁.re ≠ 0)
    (hz : (1 / 2 + z) ∈ zetaZeroConfig.carrier)
    (hlow : γ₀ / 2 ≤ |z₁.im|) (hzz : ‖z - z₁‖ ≤ 1 / 2) {ε₀ H₀ : ℝ} (hH₀ : 0 < H₀)
    (hD : ε₀ ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w γ₀) z₁‖)
    (hH : H₀ ^ 2 ≤ ε₀ / (M + 1) - (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + γ₀) ^ 4)
    (hK : (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + γ₀) ^ 4 ≤ H₀ ^ 2 / 16)
    (hL : 8 * w * Real.exp (w / 2) * bumpMass w * ‖z - z₁‖ ≤ H₀) (hwz : w * ‖z - z₁‖ ≤ 1) :
    0 ≤ (evenCoeff zetaZeroConfig (modScaledBump w γ₀) z *
      conj (evenCoeff zetaZeroConfig (modScaledBump w γ₀) z₁)).re := by
  have hc : (0 : ℝ) ≤ γ₀ := by linarith
  have hconjmem : ∀ y, (1 / 2 + y) ∈ zetaZeroConfig.carrier →
      (1 / 2 + conj y) ∈ zetaZeroConfig.carrier := fun y hy => by
    have := conj_mem_zetaZeroConfig hy
    have e : conj (1 / 2 + y) = 1 / 2 + conj y := by apply Complex.ext <;> simp
    rwa [e] at this
  have himz : |z.im - z₁.im| ≤ 1 / 2 := by
    have := Complex.abs_im_le_norm (z - z₁); rw [Complex.sub_im] at this; linarith
  rcases le_or_gt 0 z₁.im with hpos | hneg
  · have him₁ : 0 ≤ z₁.im := hpos
    have him : 0 ≤ z.im := by
      rw [abs_of_nonneg hpos] at hlow; rw [abs_le] at himz; linarith
    have hh₁ := le_norm_paperFT_of_loud_of_offLineCopiesLocallyBounded hM hw hc hz₁ hz₁_off
      him₁ hD hH
    exact re_evenCoeff_mul_conj_nonneg hw hc hz₁ hz him₁ him hH₀ hh₁ hK hL hwz
  · have him₁ : 0 ≤ (conj z₁).im := by rw [Complex.conj_im]; linarith
    have him : 0 ≤ (conj z).im := by
      rw [Complex.conj_im]; rw [abs_of_neg hneg] at hlow; rw [abs_le] at himz; linarith
    have hD' : ε₀ ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w γ₀) (conj z₁)‖ := by
      rw [evenCoeff_conj, Complex.norm_conj]; exact hD
    have hzz' : ‖conj z - conj z₁‖ = ‖z - z₁‖ := by rw [← map_sub, Complex.norm_conj]
    have hh₁ := le_norm_paperFT_of_loud_of_offLineCopiesLocallyBounded hM hw hc (hconjmem z₁ hz₁)
      (by simpa using hz₁_off) him₁ hD' hH
    have h := re_evenCoeff_mul_conj_nonneg hw hc (hconjmem z₁ hz₁) (hconjmem z hz) him₁ him hH₀
      hh₁ hK (by rw [hzz']; exact hL) (by rw [hzz']; exact hwz)
    rw [evenCoeff_conj, evenCoeff_conj, Complex.conj_conj, show conj (evenCoeff zetaZeroConfig
      (modScaledBump w γ₀) z) * evenCoeff zetaZeroConfig (modScaledBump w γ₀) z₁ =
      conj (evenCoeff zetaZeroConfig (modScaledBump w γ₀) z *
        conj (evenCoeff zetaZeroConfig (modScaledBump w γ₀) z₁)) by
      rw [map_mul, Complex.conj_conj], Complex.conj_re] at h
    exact h

/-- The modulated noise constant `M_mod,off(M, w, W_on)` under `OffLineCopiesLocallyBounded M` and
`onLineEvenMass w γ₀ ≤ W_on`, replacing the `6144 log(180(Γ + 6))` cubic potential tail by `39 M`
and isolating `W_on` as the sole height-dependent datum. -/
def nearTopNoiseOffLine (M : ℕ) (w W_on : ℝ) : ℝ :=
  4 * (2 * W_on + 48 * (M : ℝ) ^ 2 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2) /
      ((Real.exp 1 - 1) * (centerAmplitude w ^ 2 / (2 * Real.exp 1))) +
    39 * M + 1

/-- The modulated cluster-collapse bound under `OffLineCopiesLocallyBounded M` and
`onLineEvenMass w γ₀ ≤ W_on`, with no `log γ₀` factor in the cubic potential tail. -/
def clusterCollapseBoundOffLine (M : ℕ) (w W_on κ₀ : ℝ) (k p : ℕ) : ℝ :=
  (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀) * (4 * κ₀ ^ 2 + 4 * π ^ 2 * (k + p : ℕ) ^ 2) ^ (k + p) *
    nearTopNoiseOffLine M w W_on

theorem clusterCollapseBoundOffLine_one (M : ℕ) (w W_on : ℝ) (k p : ℕ) :
    clusterCollapseBoundOffLine M w W_on 1 k p = (8 / 3) ^ p * (4 / 3) ^ k * 2 *
      (4 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) * nearTopNoiseOffLine M w W_on := by
  rw [clusterCollapseBoundOffLine]; ring

/-- **Tail-free near-top cluster collapse in terms of `onLineEvenMass`.** Under
`OffLineCopiesLocallyBounded M` and `onLineEvenMass w z₀.im ≤ W_on`, both the companion count `M`
and the cubic potential tail `39 M` are height-uniform, and `recordHeightEnvelope w z₀.im` is
eliminated from `hV2` and `clusterCollapseBoundOffLine`. -/
theorem zeta_near_top_cluster_collapse_tail_free_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeightOffLine M w ≤ z₀.im) {V W_on : ℝ} (hV : 0 < V)
    (hW_on : onLineEvenMass w z₀.im ≤ W_on)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    (hneg : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re)
    {κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀)
    (hV2 : 2 * Real.log (4 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
        centerAmplitude w ^ 2) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : π * (k + M : ℕ) ≤ V)
    (hVr : 4 * π * (k + M : ℕ) ≤ V * (z₀.re / 8)) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁ ≠ 0 ∧ z₀.re / 2 ≤ z₁.re ∧
      z₀.im / 2 ≤ |z₁.im| ∧
      (∀ z, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z₁‖ * Real.exp (z₁.re * V)) ∧
      ∃ C : Finset ℂ, z₁ ∉ C ∧ C.card ≤ M ∧
        (∀ z ∈ C, evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 ∧
          ‖z - z₁‖ ≤ z₀.re / 8 + 2 * κ₀ / V) ∧
        (∀ z, z ≠ z₁ → evenCoeff zetaZeroConfig (modScaledBump w z₀.im) z ≠ 0 →
          ‖z - z₁‖ ≤ z₀.re / 8 - 2 * κ₀ / V → z ∈ C) ∧
        (∏ z ∈ C, ‖z - z₁‖) * (κ₀ / (2 * (M + 1))) ^ C.card * V ^ (2 * k + C.card + 1) *
            (z₀.re / 8) ^ (2 * k + 1) ≤ clusterCollapseBoundOffLine M w W_on κ₀ k C.card := by
  classical
  set b := modScaledBump w z₀.im with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set r : ℝ := z₀.re / 8 with hr
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1' : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; linarith [hre₀1']
  have hmem : ∀ x : ℂ, D x ≠ 0 → (1 / 2 + x) ∈ zetaZeroConfig.carrier :=
    fun _ hx => add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hx
  have htop' : ∀ z, D z ≠ 0 → z.re ≤ z₀.re + 1 / V := fun z hz => by
    have := htop _ (hmem z hz)
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    linarith
  obtain ⟨z₁, hz₁, hre₁, hlow, hD₁, hrec⟩ :=
    near_top_record_facts_of_offLineCopiesLocallyBounded hM hw hV hz₀ hre₀ hTw htop' hV2
  refine ⟨z₁, hz₁, hre₁, hlow, hrec, ?_⟩
  have hκ₀0 : 0 < κ₀ := by linarith
  have h2κ : 2 * κ₀ / V ≤ r / 2 := by rw [hr]; linarith
  set R₀ : ℝ := r + 2 * κ₀ / V with hR₀
  set T : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b z₁ R₀).toFinset.erase z₁ with hT
  have hTcard : T.card ≤ M := by
    refine card_offLine_window_le_of_offLineCopiesLocallyBounded hM z₁.im T fun z hz => ?_
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset] at hz
    obtain ⟨-, hDz, hzr⟩ := hz
    refine ⟨hmem z hDz, ?_, ?_⟩
    · have h1 := Complex.abs_re_le_norm (z - z₁)
      rw [Complex.sub_re] at h1
      have h2 := neg_abs_le (z.re - z₁.re)
      have h3 : R₀ ≤ z₀.re / 4 := by rw [hR₀, hr]; linarith
      intro h0; linarith
    · have h1 := Complex.abs_im_le_norm (z - z₁)
      rw [Complex.sub_im] at h1
      have h2 : R₀ ≤ 1 := by rw [hR₀]; linarith
      linarith
  obtain ⟨κ, hκ1, hκ2, hmirror⟩ := exists_depth_avoiding_mirrors T z₁ hTcard hκ₀0 hV
  set ε : ℝ := κ₀ / (2 * (M + 1) * V) with hε
  have hκ0 : 0 < κ := by linarith
  have hκV' : κ / V ≤ 2 * κ₀ / V := div_le_div_of_nonneg_right hκ2 hV.le
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  have hz₁s : ‖z₁ - s‖ = κ / V := by
    have : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hκ0 hV)]
  set S : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b s r).toFinset with hS
  have hz₁S : z₁ ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]; exact ⟨hz₁, by rw [hz₁s]; linarith⟩
  have hSr : ∀ z ∈ S, ‖z - s‖ ≤ r := fun z hz => by
    rw [hS, Set.Finite.mem_toFinset] at hz; exact hz.2
  have hiso : ∀ z, z ∉ S → D z ≠ 0 → r ≤ ‖z - s‖ := fun z hz hDz => by
    rw [hS, Set.Finite.mem_toFinset] at hz
    by_contra h; push Not at h; exact hz ⟨hDz, h.le⟩
  have hST : S.erase z₁ ⊆ T := fun z hz => by
    rw [Finset.mem_erase] at hz
    have hzS := hz.2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset]
    refine ⟨hz.1, hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    have := hSr z hz.2
    rw [hR₀]; linarith
  set p := (S.erase z₁).card with hp
  have hpP : p ≤ M := (Finset.card_le_card hST).trans hTcard
  have hpP' : ((k + p : ℕ) : ℝ) ≤ (k + M : ℕ) := by exact_mod_cast (by omega : k + p ≤ k + M)
  have hrσ : r ≤ z₁.re - κ / V := by rw [hr] at h2κ ⊢; linarith
  have hεz : ∀ z ∈ S.erase z₁, ε ≤ ‖(z - s) + ((κ / V : ℝ) : ℂ)‖ := fun z hz => by
    have e : (z - s) + ((κ / V : ℝ) : ℂ) = (z - z₁) + ((2 * κ / V : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [hs]; ring
      · simp [hs]
    rw [e]; exact hmirror z (hST hz)
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hcol := zeta_full_cluster_collapse_of_offLineCopiesLocallyBounded hM
    (contDiff_modScaledBump_two w _) (modScaledBump_support hw _) hneg hz₁ hrec hκ0 hr0 hr1 hrσ hk
    S hz₁S hSr hiso (le_trans (mul_le_mul_of_nonneg_left hpP' Real.pi_pos.le) hVk)
    (le_trans (mul_le_mul_of_nonneg_left hpP' (by positivity)) hVr) hε0 hεz
  rw [← hp] at hcol
  refine ⟨S.erase z₁, Finset.notMem_erase z₁ S, hpP, fun z hz => ?_, fun z hz1 hDz hzr => ?_, ?_⟩
  · have hzS := (Finset.mem_erase.mp hz).2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    refine ⟨hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    linarith [hzS.2]
  · refine Finset.mem_erase.mpr ⟨hz1, ?_⟩
    rw [hS, Set.Finite.mem_toFinset]
    refine ⟨hDz, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z z₁ s
    rw [hz₁s] at h1
    linarith
  rw [← hp]
  have hθ0 : 0 < κ / V := div_pos hκ0 hV
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) := ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : ℝ, Q₂ = (4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (2 * (k + p)).factorial * (π / V) ^ (2 * (k + p)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]; exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos Real.pi_pos hV) _)
  have hbase : ∀ t : ℝ, 0 < t → 0 < t ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := fun t ht =>
    add_pos_of_pos_of_nonneg (pow_pos ht 2)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg π)) (sq_nonneg _))
  have hQ0 : 0 < Q := by rw [hQ]; exact pow_pos (hbase κ hκ0) _
  have hK : u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q) ≤
      ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (norm_fejerPowWin_ofReal_ge hV (k + p) hθ0)
    have hVne : V ≠ 0 := hV.ne'
    have e : (κ / V) ^ 2 + (2 * π * ((k + p : ℕ) : ℝ) / V) ^ 2 =
        (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) / V ^ 2 := by
      field_simp; ring
    rw [e, div_mul_cancel₀ κ hVne, hu, hQ, div_pow, div_pow, ← pow_mul V 2 (k + p), pow_succ]
    field_simp
  rw [← hu] at hcol
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ,
      m₀ = 2 * W_on + 48 * (M : ℝ) ^ 2 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := ⟨_, rfl⟩
  have hMW_base := mass_le_onLineEvenMass_add_of_offLineCopiesLocallyBounded hM hw z₀.im
  have hMW : |2 * (lagStructure zetaZeroConfig b 0).re| + ∑' z : ℂ, ‖D z‖ ≤ m₀ := by
    rw [hm₀]; linarith
  have hW0 : 0 ≤ ∑' z : ℂ, ‖D z‖ := tsum_nonneg fun z => norm_nonneg _
  have ha0 : 0 < centerAmplitude w ^ 2 / (2 * Real.exp 1) := by
    have := centerAmplitude_pos hw; positivity
  have hκ1' : 1 ≤ κ := hκ₀.trans hκ1
  have hΞ := xi_ratio_offLine_le (M := M) hκ1' ha0 hD₁ hW0 hMW
  have hQQ : κ * Q ≤ 2 * κ₀ * Q₂ := by
    have hq : Q ≤ Q₂ := by
      rw [hQ, hQ₂]
      refine pow_le_pow_left₀ (hbase κ hκ0).le ?_ _
      have h2 : κ ^ 2 ≤ (2 * κ₀) ^ 2 := pow_le_pow_left₀ hκ0.le hκ2 2
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [h2, e]
    exact mul_le_mul hκ2 hq hQ0.le (by linarith only [hκ₀0])
  have he1 : 0 < Real.exp 1 - 1 := by linarith only [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hm00 : 0 ≤ m₀ := le_trans (add_nonneg (abs_nonneg _) hW0) hMW
  have hE : 0 < Real.exp κ - 1 := by linarith only [Real.add_one_lt_exp hκ0.ne', hκ0]
  have hc0 : (0 : ℝ) ≤ (8 / 3) ^ p * (4 / 3) ^ k :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  have hPr0 : 0 ≤ ∏ z ∈ S.erase z₁, ‖z - z₁‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hN0 : 0 ≤ nearTopNoiseOffLine M w W_on * 1 := by
    rw [mul_one, nearTopNoiseOffLine, ← hm₀]
    have : 0 ≤ 4 * m₀ / ((Real.exp 1 - 1) * (centerAmplitude w ^ 2 / (2 * Real.exp 1))) :=
      div_nonneg (by linarith) (by positivity)
    positivity
  have hΞ' : 4 * |2 * (lagStructure zetaZeroConfig b 0).re| + 4 * ∑' z : ℂ, ‖D z‖ +
      24 * M * ‖D z₁‖ * Real.exp κ ≤
        nearTopNoiseOffLine M w W_on * 1 * (‖D z₁‖ * (Real.exp κ - 1)) := by
    rw [mul_one, nearTopNoiseOffLine, ← hm₀]
    have : 0 ≤ ‖D z₁‖ * (Real.exp κ - 1) := mul_nonneg (norm_nonneg _) hE.le
    linarith [hΞ]
  have hfin := cluster_log_arith (D := ‖D z₁‖) (u := u) (E := Real.exp κ - 1)
    (norm_pos_iff.mpr hz₁) hu0 hE hε0 hPr0 hr0 hV (mul_pos hκ0 hQ0) hcol hK hΞ' hc0 hQQ
    hN0 (p := p) (m := 2 * (k + p) + 1) (k := k)
  have e : ε ^ p * V ^ (2 * (k + p) + 1) = (κ₀ / (2 * (M + 1))) ^ p * V ^ (2 * k + p + 1) := by
    have hVne : V ≠ 0 := hV.ne'
    rw [hε, show 2 * (k + p) + 1 = (2 * k + p + 1) + p by ring, pow_add, div_pow, div_pow, mul_pow]
    field_simp
  calc (∏ z ∈ S.erase z₁, ‖z - z₁‖) * (κ₀ / (2 * (M + 1))) ^ p * V ^ (2 * k + p + 1) * r ^ (2 * k + 1)
      = (∏ z ∈ S.erase z₁, ‖z - z₁‖) * ε ^ p * V ^ (2 * (k + p) + 1) * r ^ (2 * k + 1) := by
        rw [mul_assoc (∏ z ∈ S.erase z₁, ‖z - z₁‖), ← e]; ring
    _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (nearTopNoiseOffLine M w W_on * 1) := hfin
    _ = clusterCollapseBoundOffLine M w W_on κ₀ k p := by
        rw [clusterCollapseBoundOffLine, ← hQ₂]; ring

/-- **Tail-free near-top visibility in terms of `onLineEvenMass`.** Under
`OffLineCopiesLocallyBounded M` and `onLineEvenMass w z₀.im ≤ W_on`, the `log γ₀` / `log Γ` factors
are eliminated from the companion count `M`, the cubic potential tail `39 M`, the record-depth
condition `hV2`, the phase-coherence scale `H₀`, and the core mass bound. -/
theorem zeta_near_top_visible_tail_free_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeightOffLine M w ≤ z₀.im) {V W_on : ℝ} (hV : 0 < V)
    (hW_on : onLineEvenMass w z₀.im ≤ W_on)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V)
    {κ₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hκ₀ : 1 ≤ κ₀)
    (hV2 : 2 * Real.log (4 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 /
        centerAmplitude w ^ 2) ≤ z₀.re * V)
    (hκV : 2 * κ₀ / V ≤ z₀.re / 16) (hVk : π * (k + M : ℕ) ≤ V)
    (hVr : 4 * π * (k + M : ℕ) ≤ V * (z₀.re / 8)) {H₀ : ℝ} (hH₀ : 0 < H₀)
    (hH : H₀ ^ 2 ≤ centerAmplitude w ^ 2 / (2 * Real.exp 1) / (M + 1) -
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4)
    (hK : (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4 ≤ H₀ ^ 2 / 16)
    {ρ G : ℝ} (hρ : 0 < ρ) (hG : 1 ≤ G) (hρV : ρ * V ≤ 1) (hρw : w * ρ ≤ 1)
    (hρL : 8 * w * Real.exp (w / 2) * bumpMass w * ρ ≤ H₀) (hρr : ρ ≤ z₀.re / 16)
    (hη : ((1 + coreFactorPerturbation M κ₀ V ρ G) * (2 * (ρ * V)) +
        coreFactorPerturbation M κ₀ V ρ G) * ((M + 1) * (2 * M *
          (Real.exp (w / 2) * scaledBumpDecay w) ^ 2)) ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) / 2)
    (hmain : ∀ p : ℕ, p ≤ M → 2 * clusterCollapseBoundOffLine M w W_on κ₀ k p <
      (ρ * κ₀ / (2 * (M + 1) * G ^ M)) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1)) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re < 0 := by
  by_contra hneg
  push Not at hneg
  classical
  set b := modScaledBump w z₀.im with hbdef
  set D := evenCoeff zetaZeroConfig b with hDdef
  set r : ℝ := z₀.re / 8 with hr
  obtain ⟨hγ1, -, -, -⟩ := nearTopHeightOffLine_conditions hw hTw
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1' : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have hr0 : 0 < r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr]; linarith [hre₀1']
  have hmem : ∀ x : ℂ, D x ≠ 0 → (1 / 2 + x) ∈ zetaZeroConfig.carrier :=
    fun _ hx => add_half_mem_zetaZeroConfig_of_evenCoeff_ne_zero hx
  have htop' : ∀ z, D z ≠ 0 → z.re ≤ z₀.re + 1 / V := fun z hz => by
    have := htop _ (hmem z hz)
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    linarith
  obtain ⟨z₁, hz₁, hre₁, hlow, hD₁, hrec⟩ :=
    near_top_record_facts_of_offLineCopiesLocallyBounded hM hw hV hz₀ hre₀ hTw htop' hV2
  have hκ₀0 : 0 < κ₀ := by linarith
  have h2κ : 2 * κ₀ / V ≤ r / 2 := by rw [hr]; linarith
  set R₀ : ℝ := r + 2 * κ₀ / V with hR₀
  set T : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b z₁ R₀).toFinset.erase z₁ with hT
  have hTcard : T.card ≤ M := by
    refine card_offLine_window_le_of_offLineCopiesLocallyBounded hM z₁.im T fun z hz => ?_
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset] at hz
    obtain ⟨-, hDz, hzr⟩ := hz
    refine ⟨hmem z hDz, ?_, ?_⟩
    · have h1 := Complex.abs_re_le_norm (z - z₁)
      rw [Complex.sub_re] at h1
      have h2 := neg_abs_le (z.re - z₁.re)
      have h3 : R₀ ≤ z₀.re / 4 := by rw [hR₀, hr]; linarith
      intro h0; linarith
    · have h1 := Complex.abs_im_le_norm (z - z₁)
      rw [Complex.sub_im] at h1
      have h2 : R₀ ≤ 1 := by rw [hR₀]; linarith
      linarith
  obtain ⟨κ, hκ1, hκ2, hmirror⟩ := exists_depth_avoiding_mirrors T z₁ hTcard hκ₀0 hV
  set ε : ℝ := κ₀ / (2 * (M + 1) * V) with hε
  have hκ0 : 0 < κ := by linarith
  have hκV' : κ / V ≤ 2 * κ₀ / V := div_le_div_of_nonneg_right hκ2 hV.le
  set s : ℂ := ((z₁.re - κ / V : ℝ) : ℂ) + z₁.im * I with hs
  have hz₁s : ‖z₁ - s‖ = κ / V := by
    have : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hκ0 hV)]
  set S : Finset ℂ := (finite_evenCoeff_ball zetaZeroConfig b s r).toFinset with hS
  have hz₁S : z₁ ∈ S := by
    rw [hS, Set.Finite.mem_toFinset]; exact ⟨hz₁, by rw [hz₁s]; linarith⟩
  have hSr : ∀ z ∈ S, ‖z - s‖ ≤ r := fun z hz => by
    rw [hS, Set.Finite.mem_toFinset] at hz; exact hz.2
  have hiso : ∀ z, z ∉ S → D z ≠ 0 → r ≤ ‖z - s‖ := fun z hz hDz => by
    rw [hS, Set.Finite.mem_toFinset] at hz
    by_contra h; push Not at h; exact hz ⟨hDz, h.le⟩
  have hST : S.erase z₁ ⊆ T := fun z hz => by
    rw [Finset.mem_erase] at hz
    have hzS := hz.2
    rw [hS, Set.Finite.mem_toFinset] at hzS
    rw [hT, Finset.mem_erase, Set.Finite.mem_toFinset]
    refine ⟨hz.1, hzS.1, ?_⟩
    have h1 := norm_sub_le_norm_sub_add_norm_sub z s z₁
    rw [norm_sub_rev s z₁, hz₁s] at h1
    have := hSr z hz.2
    rw [hR₀]; linarith
  have hrσ : r ≤ z₁.re - κ / V := by rw [hr] at h2κ ⊢; linarith
  obtain ⟨j, hjP, hann⟩ := exists_empty_annulus T z₁ hTcard hρ hG
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ₀ : ℝ, ρ₀ = ρ / G ^ (j + 1) := ⟨_, rfl⟩
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = ρ / G ^ j := ⟨_, rfl⟩
  rw [← hρ₀, ← hρ₁] at hann
  have hG0 : 0 < G := by linarith only [hG]
  have hρ₀0 : 0 < ρ₀ := by rw [hρ₀]; positivity
  have hρ₀ρ : ρ₀ ≤ ρ := by rw [hρ₀]; exact div_le_self hρ.le (one_le_pow₀ hG)
  have hρ₁ρ₀ : ρ₁ = G * ρ₀ := by rw [hρ₁, hρ₀, pow_succ]; field_simp
  have hρ₁P : ρ / G ^ M ≤ ρ₁ := by
    rw [hρ₁]; exact div_le_div_of_nonneg_left hρ.le (by positivity) (pow_le_pow_right₀ hG hjP)
  obtain ⟨SL, hSL⟩ : ∃ SL : Finset ℂ, SL = (S.erase z₁).filter fun z => ρ₁ < ‖z - z₁‖ :=
    ⟨_, rfl⟩
  have hSLmem : ∀ z, z ∈ SL ↔ (z ≠ z₁ ∧ z ∈ S) ∧ ρ₁ < ‖z - z₁‖ := fun z => by
    rw [hSL, Finset.mem_filter, Finset.mem_erase]
  have hSLS : SL ⊆ S := fun z hz => ((hSLmem z).mp hz).1.2
  have hSLT : SL ⊆ T := fun z hz => hST (Finset.mem_erase.mpr ((hSLmem z).mp hz).1)
  have hpP : SL.card ≤ M := (Finset.card_le_card hSLT).trans hTcard
  have hpP' : ((k + SL.card : ℕ) : ℝ) ≤ (k + M : ℕ) := by exact_mod_cast (by omega : k + SL.card ≤ k + M)
  have hPE := zeta_partial_elimination_le_of_offLineCopiesLocallyBounded hM
    (contDiff_modScaledBump_two w _) (modScaledBump_support hw _) hneg hz₁ hrec hκ0 hr0 hr1 hrσ hk
    S SL hSLS hSr hiso (le_trans (mul_le_mul_of_nonneg_left hpP' Real.pi_pos.le) hVk)
    (le_trans (mul_le_mul_of_nonneg_left hpP' (by positivity)) hVr)
  rw [← hs] at hPE
  have hz₁C : z₁ ∈ S.filter fun z => z ∉ SL :=
    Finset.mem_filter.mpr ⟨hz₁S, fun h => ((hSLmem z₁).mp h).1.1 rfl⟩
  have hcρ₀ : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖c - z₁‖ ≤ ρ₀ := fun c hc => by
    obtain ⟨hcS, hcL⟩ := Finset.mem_filter.mp hc
    by_cases hne : c = z₁
    · rw [hne, sub_self, norm_zero]; exact hρ₀0.le
    · rcases hann c (hST (Finset.mem_erase.mpr ⟨hne, hcS⟩)) with h | h
      · exact h
      · exact absurd ((hSLmem c).mpr ⟨⟨hne, hcS⟩, h⟩) hcL
  have hcρ : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖c - z₁‖ ≤ ρ := fun c hc => (hcρ₀ c hc).trans hρ₀ρ
  have hθc : z₁ - s = ((κ / V : ℝ) : ℂ) := by apply Complex.ext <;> simp [hs]
  have hε0' : 0 < ε := by rw [hε]; positivity
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁ρ₀]; positivity
  have hbig : ∀ y ∈ SL, ρ₁ * ε ≤ ‖(y - s) ^ 2 - (z₁ - s) ^ 2‖ := fun y hy => by
    have e : (y - s) ^ 2 - (z₁ - s) ^ 2 = (y - z₁) * ((y - z₁) + ((2 * κ / V : ℝ) : ℂ)) := by
      have e1 : y - s = (y - z₁) + ((κ / V : ℝ) : ℂ) := by rw [← hθc]; ring
      rw [e1, hθc]; push_cast; ring
    rw [e, norm_mul]
    exact mul_le_mul ((hSLmem y).mp hy).2.le (hmirror y (hSLT hy)) hε0'.le (norm_nonneg _)
  have hDS : ∀ c ∈ S, D c ≠ 0 := fun c hc => by
    rw [hS, Set.Finite.mem_toFinset] at hc; exact hc.1
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hz₁_off : z₁.re ≠ 0 := by linarith
  have hcoh : ∀ c ∈ S.filter (fun z => z ∉ SL), 0 ≤ (D c * conj (D z₁)).re := fun c hc => by
    have hcS := (Finset.mem_filter.mp hc).1
    have hcz := hcρ c hc
    exact re_twin_mul_conj_nonneg_of_offLineCopiesLocallyBounded hM hw hγ1 (hmem z₁ hz₁) hz₁_off
      (hmem c (hDS c hcS)) hlow (by linarith only [hcz, hρr, hre₀1']) hH₀ hD₁ hH hK
      (le_trans (mul_le_mul_of_nonneg_left hcz (mul_nonneg (by positivity) hJ0)) hρL)
      (le_trans (mul_le_mul_of_nonneg_left hcz hw.le) hρw)
  obtain ⟨Dm, hDm⟩ : ∃ Dm : ℝ,
      Dm = 2 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := ⟨_, rfl⟩
  rw [← hDm] at hη
  have hDc : ∀ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤ Dm := fun c hc => by
    have hcz := hcρ c hc
    have h1 := Complex.abs_re_le_norm (c - z₁)
    rw [Complex.sub_re] at h1
    have h2 := neg_abs_le (c.re - z₁.re)
    have hcre : c.re ≠ 0 := by intro h0; linarith
    rw [hDm]
    exact norm_evenCoeff_modScaledBump_le_of_offLineCopiesLocallyBounded hM hw z₀.im hcre
  have hCcard : (S.filter fun z => z ∉ SL).card ≤ M + 1 :=
    (Finset.card_filter_le _ _).trans (by
      rw [← Finset.card_erase_add_one hz₁S]
      exact Nat.succ_le_succ ((Finset.card_le_card hST).trans hTcard))
  have hsumD : ∑ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤ (M + 1) * Dm := by
    have h := Finset.sum_le_card_nsmul _ (fun c => ‖D c‖) Dm hDc
    rw [nsmul_eq_mul] at h
    have hD0 : 0 ≤ Dm := le_trans (norm_nonneg _) (hDc z₁ hz₁C)
    have hc : ((S.filter fun z => z ∉ SL).card : ℝ) ≤ M + 1 := by exact_mod_cast hCcard
    exact h.trans (mul_le_mul_of_nonneg_right hc hD0)
  obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, t₀ = (4 * κ₀ / V + ρ) * (2 * (M + 1) * V) / (G * κ₀) := ⟨_, rfl⟩
  have ht₀0 : 0 ≤ t₀ := by rw [ht₀]; positivity
  have hτ : (1 + t₀) ^ SL.card - 1 ≤ coreFactorPerturbation M κ₀ V ρ G := by
    rw [coreFactorPerturbation, ← ht₀]
    have := pow_le_pow_right₀ (by linarith only [ht₀0] : (1 : ℝ) ≤ 1 + t₀) hpP
    linarith only [this]
  have hτ0 : 0 ≤ coreFactorPerturbation M κ₀ V ρ G := by
    have := one_le_pow₀ (n := SL.card) (by linarith only [ht₀0] : (1 : ℝ) ≤ 1 + t₀)
    linarith only [this, hτ]
  have hmass : ((1 + coreFactorPerturbation M κ₀ V ρ G) * (2 * (ρ * V)) +
      coreFactorPerturbation M κ₀ V ρ G) * ∑ c ∈ S.filter (fun z => z ∉ SL), ‖D c‖ ≤
        ‖D z₁‖ / 2 := by
    have hη0 : 0 ≤ (1 + coreFactorPerturbation M κ₀ V ρ G) * (2 * (ρ * V)) +
        coreFactorPerturbation M κ₀ V ρ G := by positivity
    have h1 := mul_le_mul_of_nonneg_left hsumD hη0
    linarith only [h1, hη, hD₁]
  have hgap : ρ₀ * (2 * (κ / V) + ρ₀) ≤ t₀ * (ρ₁ * ε) := by
    rw [ht₀, hρ₁ρ₀, hε]
    exact core_gap_arith hρ₀0.le hρ₀ρ hG0 hκ₀0 hV (Nat.cast_nonneg M) hκ2
  have hθ0 : 0 < κ / V := div_pos hκ0 hV
  have hcore_ge := eliminated_core_ge hz₁C D (k + SL.card) hV hθc hθ0.le hρ₀0.le
    (mul_pos hρ₁0 hε0') hbig hcρ₀ hgap hτ (mul_le_mul_of_nonneg_right hρ₀ρ hV.le) hρV hcoh hmass
  have hcol := hcore_ge.trans hPE
  obtain ⟨p, hp⟩ : ∃ p : ℕ, p = SL.card := ⟨_, rfl⟩
  rw [← hp] at hcol hpP
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) := ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q₂ : ℝ, Q₂ = (4 * κ₀ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) ^ (k + p) :=
    ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = (2 * (k + p)).factorial * (π / V) ^ (2 * (k + p)) := ⟨_, rfl⟩
  have hu0 : 0 < u := by
    rw [hu]; exact mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (pow_pos (div_pos Real.pi_pos hV) _)
  have hbase : ∀ t : ℝ, 0 < t → 0 < t ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2 := fun t ht =>
    add_pos_of_pos_of_nonneg (pow_pos ht 2)
      (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg π)) (sq_nonneg _))
  have hQ0 : 0 < Q := by rw [hQ]; exact pow_pos (hbase κ hκ0) _
  have hKlow : u * (Real.exp κ - 1) * V ^ (2 * (k + p) + 1) / (κ * Q) ≤
      ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ := by
    refine le_trans (le_of_eq ?_) (norm_fejerPowWin_ofReal_ge hV (k + p) hθ0)
    have hVne : V ≠ 0 := hV.ne'
    have e : (κ / V) ^ 2 + (2 * π * ((k + p : ℕ) : ℝ) / V) ^ 2 =
        (κ ^ 2 + 4 * π ^ 2 * ((k + p : ℕ) : ℝ) ^ 2) / V ^ 2 := by
      field_simp; ring
    rw [e, div_mul_cancel₀ κ hVne, hu, hQ, div_pow, div_pow, ← pow_mul V 2 (k + p), pow_succ]
    field_simp
  rw [← hu] at hcol
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ,
      m₀ = 2 * W_on + 48 * (M : ℝ) ^ 2 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 := ⟨_, rfl⟩
  have hMW_base := mass_le_onLineEvenMass_add_of_offLineCopiesLocallyBounded hM hw z₀.im
  have hMW : |2 * (lagStructure zetaZeroConfig b 0).re| + ∑' z : ℂ, ‖D z‖ ≤ m₀ := by
    rw [hm₀]; linarith
  have hW0 : 0 ≤ ∑' z : ℂ, ‖D z‖ := tsum_nonneg fun z => norm_nonneg _
  have ha0 : 0 < centerAmplitude w ^ 2 / (2 * Real.exp 1) := by
    have := centerAmplitude_pos hw; positivity
  have hκ1' : 1 ≤ κ := hκ₀.trans hκ1
  have hΞ := xi_ratio_offLine_le (M := M) hκ1' ha0 hD₁ hW0 hMW
  have hQQ : κ * Q ≤ 2 * κ₀ * Q₂ := by
    have hq : Q ≤ Q₂ := by
      rw [hQ, hQ₂]
      refine pow_le_pow_left₀ (hbase κ hκ0).le ?_ _
      have h2 : κ ^ 2 ≤ (2 * κ₀) ^ 2 := pow_le_pow_left₀ hκ0.le hκ2 2
      have e : (2 * κ₀) ^ 2 = 4 * κ₀ ^ 2 := by ring
      linarith only [h2, e]
    exact mul_le_mul hκ2 hq hQ0.le (by linarith only [hκ₀0])
  have he1 : 0 < Real.exp 1 - 1 := by linarith only [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hm00 : 0 ≤ m₀ := le_trans (add_nonneg (abs_nonneg _) hW0) hMW
  have hE : 0 < Real.exp κ - 1 := by linarith only [Real.add_one_lt_exp hκ0.ne', hκ0]
  have hc0 : (0 : ℝ) ≤ (8 / 3) ^ p * (4 / 3) ^ k :=
    mul_nonneg (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  have hPr0 : 0 ≤ ρ₁ ^ p / 2 := by positivity
  have hN0 : 0 ≤ nearTopNoiseOffLine M w W_on * 1 := by
    rw [mul_one, nearTopNoiseOffLine, ← hm₀]
    have : 0 ≤ 4 * m₀ / ((Real.exp 1 - 1) * (centerAmplitude w ^ 2 / (2 * Real.exp 1))) :=
      div_nonneg (by linarith) (by positivity)
    positivity
  have hΞ' : 4 * |2 * (lagStructure zetaZeroConfig b 0).re| + 4 * ∑' z : ℂ, ‖D z‖ +
      24 * M * ‖D z₁‖ * Real.exp κ ≤
        nearTopNoiseOffLine M w W_on * 1 * (‖D z₁‖ * (Real.exp κ - 1)) := by
    rw [mul_one, nearTopNoiseOffLine, ← hm₀]
    have : 0 ≤ ‖D z₁‖ * (Real.exp κ - 1) := mul_nonneg (norm_nonneg _) hE.le
    linarith [hΞ]
  have hcol' : ‖D z₁‖ * (ρ₁ ^ p / 2) * ε ^ p * ‖fejerPowWin (k + p) V ((κ / V : ℝ) : ℂ)‖ ≤
      u * ((8 / 3) ^ p * (4 / 3) ^ k *
        (4 * |2 * (lagStructure zetaZeroConfig b 0).re| + 4 * (∑' z : ℂ, ‖D z‖) +
          24 * M * ‖D z₁‖ * Real.exp κ) / r ^ (2 * k + 1)) :=
    le_trans (le_of_eq (by rw [mul_pow]; ring)) hcol
  have hfin := cluster_log_arith (D := ‖D z₁‖) (u := u) (E := Real.exp κ - 1)
    (norm_pos_iff.mpr hz₁) hu0 hE hε0'.le hPr0 hr0 hV (mul_pos hκ0 hQ0) hcol' hKlow hΞ' hc0 hQQ
    hN0 (p := p) (m := 2 * (k + p) + 1) (k := k)
  have e : ε ^ p * V ^ (2 * (k + p) + 1) = (κ₀ / (2 * (M + 1))) ^ p * V ^ (2 * k + p + 1) := by
    have hVne : V ≠ 0 := hV.ne'
    rw [hε, show 2 * (k + p) + 1 = (2 * k + p + 1) + p by ring, pow_add, div_pow, div_pow, mul_pow]
    field_simp
  have hb : (ρ₁ ^ p * (κ₀ / (2 * (M + 1))) ^ p) / 2 * (V ^ (2 * k + p + 1) * r ^ (2 * k + 1)) ≤
      clusterCollapseBoundOffLine M w W_on κ₀ k p :=
    calc (ρ₁ ^ p * (κ₀ / (2 * (M + 1))) ^ p) / 2 * (V ^ (2 * k + p + 1) * r ^ (2 * k + 1))
        = ρ₁ ^ p / 2 * (ε ^ p * V ^ (2 * (k + p) + 1)) * r ^ (2 * k + 1) := by rw [e]; ring
      _ = ρ₁ ^ p / 2 * ε ^ p * V ^ (2 * (k + p) + 1) * r ^ (2 * k + 1) := by ring
      _ ≤ (8 / 3) ^ p * (4 / 3) ^ k * (2 * κ₀ * Q₂) * (nearTopNoiseOffLine M w W_on * 1) := hfin
      _ = clusterCollapseBoundOffLine M w W_on κ₀ k p := by
          rw [clusterCollapseBoundOffLine, ← hQ₂]; ring
  have hab : (ρ * κ₀ / (2 * (M + 1) * G ^ M)) ^ p ≤ ρ₁ ^ p * (κ₀ / (2 * (M + 1))) ^ p := by
    rw [← mul_pow]
    have e2 : ρ * κ₀ / (2 * (M + 1) * G ^ M) = ρ / G ^ M * (κ₀ / (2 * (M + 1))) := by
      field_simp
    refine pow_le_pow_left₀ (by positivity) ?_ p
    rw [e2]
    exact mul_le_mul_of_nonneg_right hρ₁P (by positivity)
  exact visible_final_arith hab (by positivity) hb (hmain p hpP)

/-- The height-independent coherence product `c_mod,off(M, w)` of the modulated family under
`OffLineCopiesLocallyBounded M`, replacing `nearTopMass w γ₀` and `explicitCount Γ` by
`2 M (e^{w/2} B_w)²` and `M`. -/
def nearTopCoherenceOffLine (M : ℕ) (w : ℝ) : ℝ :=
  explicitCoherence (centerAmplitude w ^ 2 / (2 * Real.exp 1))
    (2 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2) M

/-- The height-independent phase-coherence scale `H₀_mod,off(M, w) = √(a_w²/(2e) / (2(M + 1)))`
of the modulated family under `OffLineCopiesLocallyBounded M`, eliminating `80 log(180 Γ)`. -/
def nearTopScaleOffLine (M : ℕ) (w : ℝ) : ℝ :=
  Real.sqrt (centerAmplitude w ^ 2 / (2 * Real.exp 1) / (2 * (M + 1)))

/-- The Fejér order `k_mod,off(M, w, W_on)` of the modulated family under
`OffLineCopiesLocallyBounded M` and `onLineEvenMass w γ₀ ≤ W_on`, in which `W_on` enters only
logarithmically through `⌈log₂ Y⌉₊`. -/
def nearTopOrderOffLine (M : ℕ) (w W_on : ℝ) : ℕ :=
  explicitOrder (nearTopNoiseOffLine M w W_on) (nearTopCoherenceOffLine M w) M

/-- The explicit modulated visibility lag `V_mod,off(M, w, W_on, δ₀)` under
`OffLineCopiesLocallyBounded M` and `onLineEvenMass w γ₀ ≤ W_on`, completely free of `log γ₀`
outside `nearTopOrderOffLine M w W_on`. -/
def nearTopLagOffLine (M : ℕ) (w W_on δ₀ : ℝ) : ℝ :=
  8 / δ₀ * (13 * π * nearTopOrderOffLine M w W_on + 4 +
    |Real.log (4 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2)|) +
    w + 8 * w * Real.exp (w / 2) * bumpMass w / nearTopScaleOffLine M w

/-- **Near-top zeros of `ζ` are visible at an explicit lag in `(M, W_on, Re z₀)` without any
`log γ₀` factor.** Under `OffLineCopiesLocallyBounded M` and `onLineEvenMass w z₀.im ≤ W_on`
(`W_on ≥ 0`), any `1/V`-near-top zero `½ + z₀` right of the line above `nearTopHeightOffLine M w`
with `V ≥ nearTopLagOffLine M w W_on z₀.re` makes a difference test of the bump modulated to
`z₀.im` Weil negative at a lag `v ∈ [0, V]`. -/
theorem zeta_near_top_visible_at_explicit_onLineMass_lag {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeightOffLine M w ≤ z₀.im) {W_on : ℝ}
    (hW_on : onLineEvenMass w z₀.im ≤ W_on)
    {V : ℝ} (hV : nearTopLagOffLine M w W_on z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re < 0 := by
  obtain ⟨hγ1, -, -, hB32⟩ := nearTopHeightOffLine_conditions hw hTw
  have ha0 : 0 < centerAmplitude w ^ 2 / (2 * Real.exp 1) := by
    have := centerAmplitude_pos hw; positivity
  set Dm : ℝ := 2 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hDm
  have hDm0 : 0 ≤ Dm := by positivity
  have hW_on0 : 0 ≤ W_on := (onLineEvenMass_nonneg w z₀.im).trans hW_on
  have hNpos : 0 < nearTopNoiseOffLine M w W_on := by
    unfold nearTopNoiseOffLine
    have he1 : 0 < Real.exp 1 - 1 := by linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
    positivity
  obtain ⟨hc0, hc1, hca, hG1, hq0, hq1, hPk, hk1, hY⟩ :=
    explicit_parameter_facts ha0 hDm0 hNpos M
  obtain ⟨c, hc⟩ : ∃ c : ℝ,
      c = explicitCoherence (centerAmplitude w ^ 2 / (2 * Real.exp 1)) Dm M := ⟨_, rfl⟩
  rw [← hc] at hc0 hc1 hca hG1 hq0 hq1 hPk hk1 hY
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = explicitOrder (nearTopNoiseOffLine M w W_on) c M := ⟨_, rfl⟩
  rw [← hk] at hPk hk1 hY
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = explicitGap c M := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = explicitRatio c M := ⟨_, rfl⟩
  have hqe : q = c / (2 * (M + 1) * G ^ M) := by rw [hq, explicitRatio, ← hG]
  rw [← hG] at hG1
  rw [← hq] at hq0 hq1 hY
  have hkk : nearTopOrderOffLine M w W_on = k := by rw [hk, hc]; rfl
  obtain ⟨H₀, hH₀⟩ : ∃ H₀ : ℝ, H₀ = nearTopScaleOffLine M w := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ,
      ℓ = Real.log (4 * M * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / centerAmplitude w ^ 2) :=
    ⟨_, rfl⟩
  rw [nearTopLagOffLine, hkk, ← hH₀, ← hℓ] at hV
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1 : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  have hH₀0 : 0 < H₀ := by rw [hH₀, nearTopScaleOffLine]; exact Real.sqrt_pos.mpr (by positivity)
  have hH₀sq : H₀ ^ 2 = centerAmplitude w ^ 2 / (2 * Real.exp 1) / (2 * (M + 1)) := by
    rw [hH₀, nearTopScaleOffLine]; exact Real.sq_sqrt (by positivity)
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have hJ'0 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w := mul_nonneg (by positivity) hJ0
  have hπk : 0 ≤ 13 * π * k := by positivity
  have hℓa := abs_nonneg ℓ
  have hT2 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w / H₀ := div_nonneg hJ'0 hH₀0.le
  have h8 : 0 ≤ 8 / z₀.re * (13 * π * k + 4 + |ℓ|) := by positivity
  have hVw : w ≤ V := by linarith only [hV, h8, hT2]
  have hV0 : 0 < V := lt_of_lt_of_le hw hVw
  have hVJ : 8 * w * Real.exp (w / 2) * bumpMass w / H₀ ≤ V := by linarith only [hV, h8, hw]
  have hδV : 8 * (13 * π * k + 4 + |ℓ|) ≤ z₀.re * V := by
    have h1 : 8 / z₀.re * (13 * π * k + 4 + |ℓ|) ≤ V := by linarith only [hV, hT2, hw]
    have h2 := mul_le_mul_of_nonneg_left h1 hre₀.le
    have e : z₀.re * (8 / z₀.re * (13 * π * k + 4 + |ℓ|)) = 8 * (13 * π * k + 4 + |ℓ|) := by
      field_simp
    linarith only [h2, e]
  have hδV2 : z₀.re * V ≤ V / 2 := by nlinarith
  have hkP : ((k + M : ℕ) : ℝ) ≤ 2 * k := by
    push_cast; have : (M : ℝ) ≤ k := by exact_mod_cast hPk
    linarith
  have hπkP := mul_le_mul_of_nonneg_left hkP Real.pi_pos.le
  have hB4 : (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4 ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) / (2 * (M + 1)) / 16 := by
    have hM1 : (0 : ℝ) < M + 1 := by positivity
    rw [div_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)] at hB32
    linarith
  have e1 : centerAmplitude w ^ 2 / (2 * Real.exp 1) / (M + 1) =
      2 * (centerAmplitude w ^ 2 / (2 * Real.exp 1) / (2 * (M + 1))) := by
    field_simp; ring
  have hpos2M : 0 < centerAmplitude w ^ 2 / (2 * Real.exp 1) / (2 * (M + 1)) := by positivity
  have hH : H₀ ^ 2 ≤ centerAmplitude w ^ 2 / (2 * Real.exp 1) / (M + 1) -
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4 := by
    rw [hH₀sq, e1]; linarith only [hB4, hpos2M]
  have hK : (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (1 + z₀.im) ^ 4 ≤ H₀ ^ 2 / 16 := by
    rw [hH₀sq]; exact hB4
  have hV2 : 2 * ℓ ≤ z₀.re * V := by linarith only [hδV, le_abs_self ℓ, hπk, hℓa]
  have hκV : 2 * 1 / V ≤ z₀.re / 16 := by
    rw [div_le_div_iff₀ hV0 (by norm_num)]; linarith only [hδV, hπk, hℓa]
  have hVk : π * (k + M : ℕ) ≤ V := by linarith only [hπkP, hδV, hδV2, hℓa, hπk]
  have hVr : 4 * π * (k + M : ℕ) ≤ V * (z₀.re / 8) := by
    linarith only [hπkP, hδV, hℓa, hπk]
  have hρ : 0 < c / V := div_pos hc0 hV0
  have hρV : c / V * V ≤ 1 := by rw [div_mul_cancel₀ c hV0.ne']; exact hc1
  have hρw : w * (c / V) ≤ 1 := by
    rw [mul_div_assoc', div_le_one hV0]
    have := mul_le_mul_of_nonneg_left hc1 hw.le
    linarith only [this, hVw]
  have hρL : 8 * w * Real.exp (w / 2) * bumpMass w * (c / V) ≤ H₀ := by
    rw [mul_div_assoc', div_le_iff₀ hV0]
    have h1 : 8 * w * Real.exp (w / 2) * bumpMass w ≤ V * H₀ := by
      have := mul_le_mul_of_nonneg_right hVJ hH₀0.le
      rwa [div_mul_cancel₀ _ hH₀0.ne'] at this
    have h2 := mul_le_mul_of_nonneg_left hc1 hJ'0
    linarith only [h1, h2]
  have hρr : c / V ≤ z₀.re / 16 := by
    rw [div_le_div_iff₀ hV0 (by norm_num)]; linarith only [hδV, hπk, hℓa, hc1]
  have hη : ((1 + coreFactorPerturbation M 1 V (c / V) G) * (2 * (c / V * V)) +
      coreFactorPerturbation M 1 V (c / V) G) * ((M + 1) * Dm) ≤
      centerAmplitude w ^ 2 / (2 * Real.exp 1) / 2 := by
    rw [div_mul_cancel₀ c hV0.ne', hG]
    have hτ := coreFactorPerturbation_le hc0 hc1 hV0 M
    have h1 : coreFactorPerturbation M 1 V (c / V) (explicitGap c M) * (2 * c) ≤ 1 * (2 * c) :=
      mul_le_mul_of_nonneg_right (hτ.trans hc1) (by positivity)
    have hτ' : (1 + coreFactorPerturbation M 1 V (c / V) (explicitGap c M)) * (2 * c) +
        coreFactorPerturbation M 1 V (c / V) (explicitGap c M) ≤ 5 * c := by
      linarith only [h1, hτ]
    have hm : 0 ≤ ((M : ℝ) + 1) * Dm := by positivity
    have h2 := mul_le_mul_of_nonneg_right hτ' hm
    linarith only [h2, hca]
  have hmain : ∀ p : ℕ, p ≤ M → 2 * clusterCollapseBoundOffLine M w W_on 1 k p <
      (c / V * 1 / (2 * (M + 1) * G ^ M)) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1) := by
    intro p hp
    have hG0 : 0 < G := lt_of_lt_of_le one_pos hG1
    have e : (c / V * 1 / (2 * (M + 1) * G ^ M)) ^ p * V ^ (2 * k + p + 1) * (z₀.re / 8) ^ (2 * k + 1) =
        q ^ p * (V * (z₀.re / 8)) ^ (2 * k + 1) := by
      have e0 : c / V * 1 / (2 * (M + 1) * G ^ M) = c / (2 * (M + 1) * G ^ M) / V := by ring
      have hVp : V ^ p ≠ 0 := pow_ne_zero _ hV0.ne'
      rw [hqe, e0, div_pow, show 2 * k + p + 1 = (2 * k + 1) + p by ring, pow_add, mul_pow]
      field_simp
    rw [e, clusterCollapseBoundOffLine_one]
    have hX : 13 * π * k ≤ V * (z₀.re / 8) := by linarith only [hδV, hℓa]
    exact collapse_form_lt hp hPk hk1 hq0 hq1 hX hNpos hY
  exact zeta_near_top_visible_tail_free_of_offLineCopiesLocallyBounded hM hw hz₀ hre₀ hTw hV0
    hW_on htop hk1 le_rfl (by rw [← hℓ]; exact hV2) hκV hVk hVr hH₀0 hH hK hρ hG1 hρV hρw hρL
    hρr hη hmain

/-- The doubly-logarithmic modulated visibility lag `V_loglog(M, w, γ₀, δ₀)` under
`OffLineCopiesLocallyBounded M` (with no bound on on-line density), obtained by substituting the
unconditional Lorentzian bound `onLineEvenMass w γ₀ ≤ 16 (e^{w/2} B_w)² (C_ξ + log(|γ₀| + 4))`
into `nearTopLagOffLine`. Because `W_on` enters only inside `⌈log₂ Y⌉₊`,
`V_loglog(M, w, γ₀, δ₀) = O_{w, M}((1 + log log γ₀) / δ₀)`. -/
def nearTopLogLogLagOffLine (M : ℕ) (w γ₀ δ₀ : ℝ) : ℝ :=
  nearTopLagOffLine M w
    (16 * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 *
      (xiLineTwoLogDerivConstant + Real.log (|γ₀| + 4))) δ₀

/-- **Eliminating the `log γ₀` Turán tail reduces the modulated visibility lag to the
doubly-logarithmic scale `O_{w, M}((1 + log log γ₀) / δ₀)` without any bound on on-line density.**
Under `OffLineCopiesLocallyBounded M`, any `1/V`-near-top zero `½ + z₀` right of the line above
`nearTopHeightOffLine M w` with `V ≥ nearTopLogLogLagOffLine M w z₀.im z₀.re` makes a difference
test of the bump modulated to `z₀.im` Weil negative at a lag `v ∈ [0, V]`. -/
theorem zeta_near_top_visible_at_loglog_lag_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeightOffLine M w ≤ z₀.im)
    {V : ℝ} (hV : nearTopLogLogLagOffLine M w z₀.im z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re < 0 :=
  zeta_near_top_visible_at_explicit_onLineMass_lag hM hw hz₀ hre₀ hTw
    (onLineEvenMass_le_log hw z₀.im) hV htop

/-- **Depth gap below the doubly-logarithmic lag.** Under `OffLineCopiesLocallyBounded M`, if the
difference tests of the bump modulated to `γ₀ = Im z₀ ≥ nearTopHeightOffLine M w` are Weil
nonnegative on `[0, V]` with `V ≥ nearTopLogLogLagOffLine M w z₀.im z₀.re`, then some zero `ρ` lies
more than `1/V` to the right of `½ + z₀`. -/
theorem zeta_depth_gap_of_loglog_lag_positivity_of_offLineCopiesLocallyBounded {M : ℕ}
    (hM : OffLineCopiesLocallyBounded M) {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    (hTw : nearTopHeightOffLine M w ≤ z₀.im)
    {V : ℝ} (hV : nearTopLogLogLagOffLine M w z₀.im z₀.re ≤ V)
    (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w z₀.im) v (-1))
      (twoBump (modScaledBump w z₀.im) v (-1))).re) :
    ∃ ρ ∈ zetaZeroConfig.carrier, z₀.re + 1 / V < ρ.re - 1 / 2 := by
  by_contra h
  push Not at h
  obtain ⟨v, hv, hneg⟩ :=
    zeta_near_top_visible_at_loglog_lag_of_offLineCopiesLocallyBounded hM hw hz₀ hre₀ hTw hV h
  exact absurd (hpos v hv) (not_le.mpr hneg)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
