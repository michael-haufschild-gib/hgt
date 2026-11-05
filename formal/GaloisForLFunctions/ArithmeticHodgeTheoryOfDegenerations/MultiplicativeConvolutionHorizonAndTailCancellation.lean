import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.StageTransportAndEnteringConductorLaw
import GaloisForLFunctions.ArithmeticIncidencePositivity.MultiPrimeDilationModulusAndIteratedWeilFloors
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.WindowGrowthIsATranslationContraction
import GaloisForLFunctions.CohomologyOfWindowsOfSpecZ.ShortWindowsCarryAtMostOneNegativeSquare

/-!
# Multiplicative-Convolution Horizon Test Vectors, Direct `O(1)` Coupling, and Critical-Curve Tail Cancellation

Orthogonal conductor-`p` horizon twists `twistedWeights g (primeTwist p) N` have mean zero on
residue classes and therefore decouple from the untwisted horizon block `horizonWeights h N` at
second order (`graded_layer_criticalCurve_exact`), contributing only `O(1 / K)` along critical
curves `c_N^8 / log N → K` and failing for large `K` whenever `weilQuad (halfWeight h) < 0`
(`conductorGrading_obstruction_to_enteringConductor_payment`).

Replacing orthogonal twists by the **non-orthogonal multiplicative-convolution (Dirichlet-shift)
horizon family**
`dirichletShiftWeights d g₀ N n = 1_{d ∣ n} · g₀(log(n / N) + log d) / √n`
(`d ≥ 2`, `g₀` supported in `[-A, 0]`) resolves this decoupling and characterizes the exact head
obstruction:

1. **Multiplicative-convolution scale identity and exact Ramanujan decomposition**
   (`dirichletShiftWeights_mul_sq_eq`, `shiftedHorizonProfile_eq_zero_of_gt_neg_log`,
   `dirichletShiftWeights_eq_horizon_add_twisted`). At `N = d² M` and `n = d m`,
   `dirichletShiftWeights d g₀ (d² M) (d m) = d^{-1/2} horizonWeights g₀ M m` is the exact
   Dirichlet shift `δ_d ★ x^{(M)}` of the stage-`M` untwisted horizon vector. Algebraically,
   `1_{d ∣ n} = d⁻¹ + d⁻¹ c_d(n)` decomposes `dirichletShiftWeights d g₀` into a **nonzero**
   conductor-`1` horizon component `d⁻¹ g₀(· + log d)` on `[-(A + log d), -log d]` plus a
   conductor-`d` component `(d⁻¹ g₀(· + log d)) · c_d(n)`.

2. **Direct `O(1)` Weil polarization coupling, critical-curve limit, and pure-tail `O(1)`
   annihilation** (`dirichletShift_orderOne_crossTerm_eq`, `dirichletShift_criticalCurve_exact`,
   `dirichletShift_criticalCurve_prime`, `pureTail_exact_orderOne_annihilation`). Along any
   critical curve `c_N^8 / log N → K > 0`, the combined untwisted + Dirichlet-shift horizon block
   converges to
   `windowPencil K (halfWeight (h + d⁻¹ g₀(· + log d))) + ((d⁸ - 1) · 7 J(1) / K) M₈(halfWeight (d⁻¹ g₀(· + log d)))`,
   carrying the explicit `O(1)` bilinear cross-term
   `2 splineAtom d⁻¹ weilPair (halfWeight h) (halfWeight (g₀(· + log d)))`. Any `h` supported on
   the tail `[-(A + log d), -log d]` is annihilated identically at `O(1)` by
   `g₀(u) = -d · h(u - log d)`, yielding a strictly positive limit for all `K > 0`.

3. **Sharp head-obstruction necessity, open-head stabilization, unconditional `d = 2`
   arbitrary-aperture stabilization, and global RH equivalence**
   (`dirichletShift_head_obstruction_necessity`,
   `exists_dirichletShift_eventually_pos_of_windowThreshold_add_pos_eq_top`,
   `windowThreshold_eq_top_of_le_two_mul_weilFloorApertureTower`,
   `exists_primeTwo_dirichletShift_eventually_pos_all_criticalCurves`,
   `forall_divisor_dirichletShift_stabilizes_iff_riemannHypothesis`). Since `g₀(y + log d)`
   vanishes on the head `(-log d, 0]`, universal critical-curve stabilization across `A ≥ 0`
   requires `windowThreshold (log d) = ⊤`. Conversely, whenever `windowThreshold (log d + ε) = ⊤`
   for some `ε > 0`, a single `K`-independent profile `g₀` on `[-A, 0]` makes `weilQuad` of the
   combined complete test eventually strictly positive along every critical curve for **all**
   `K > 0`. For `d = 2`, `log 2 < 2 · weilFloorApertureTower 0` discharges the open-head hypothesis
   unconditionally for **every** `A ≥ 0` and **every** `K > 0`; globally across `d ≥ 2` (or across
   all primes `p`), universal stabilization is equivalent to `RiemannHypothesis`.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ
open ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
open CanonicalSystemOfTheWindowTower ArithmeticIncidencePositivity

/-! ### 1. Multiplicative-convolution horizon weights and Ramanujan decomposition -/

/-- Log-shifted horizon profile `g_d(y) = g₀(y + log d)`, transporting support in `[-A, 0]` to the
tail sub-interval `[-(A + log d), -log d]` of `[-(A + log d), 0]`. -/
def shiftedHorizonProfile (d : ℕ) (g₀ : ℝ → ℝ) (y : ℝ) : ℝ :=
  g₀ (y + Real.log d)

/-- Non-orthogonal multiplicative-convolution (Dirichlet-shift) horizon weights
`y_n = 1_{d ∣ n} · g₀(log(n / N) + log d) / √n`. -/
def dirichletShiftWeights (d : ℕ) (g₀ : ℝ → ℝ) (N n : ℕ) : ℝ :=
  if d ∣ n then horizonWeights (shiftedHorizonProfile d g₀) N n else 0

theorem contDiff_shiftedHorizonProfile (d : ℕ) {g₀ : ℝ → ℝ} (hg₀ : ContDiff ℝ 2 g₀) :
    ContDiff ℝ 2 (shiftedHorizonProfile d g₀) :=
  hg₀.comp (contDiff_id.add contDiff_const)

/-- **Exact multiplicative-convolution scale law.** At `N = d² M` and `n = d m` (`1 ≤ d, M, m`),
`dirichletShiftWeights d g₀ (d² M) (d m) = d^{-1/2} horizonWeights g₀ M m`: applying the Dirichlet
shift `δ_d ★ (-)` to a stage-`M` untwisted horizon vector produces `dirichletShiftWeights` at
stage `d² M`. -/
theorem dirichletShiftWeights_mul_sq_eq {d M m : ℕ} (hd : 1 ≤ d) (hM : 1 ≤ M) (hm : 1 ≤ m)
    (g₀ : ℝ → ℝ) :
    dirichletShiftWeights d g₀ (d ^ 2 * M) (d * m) =
      (1 / Real.sqrt d) * horizonWeights g₀ M m := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold dirichletShiftWeights horizonWeights shiftedHorizonProfile
  rw [if_pos (dvd_mul_right d m)]
  have hlog : Real.log ((d * m : ℕ) : ℝ) - Real.log ((d ^ 2 * M : ℕ) : ℝ) + Real.log d =
      Real.log m - Real.log M := by
    push_cast
    rw [Real.log_mul hd0.ne' hm0.ne', Real.log_mul (pow_pos hd0 2).ne' hM0.ne', Real.log_pow]
    push_cast
    ring
  have hsq : Real.sqrt ((d * m : ℕ) : ℝ) = Real.sqrt d * Real.sqrt m := by
    push_cast
    exact Real.sqrt_mul hd0.le m
  rw [hlog, hsq]
  ring

/-- **Head-vanishing law.** Whenever `g₀` vanishes outside `[-A, 0]`, `shiftedHorizonProfile d g₀`
vanishes identically on the open head `(-log d, ∞)` (in particular on `(-log d, 0]`). -/
theorem shiftedHorizonProfile_eq_zero_of_gt_neg_log {A : ℝ} {d : ℕ} {g₀ : ℝ → ℝ}
    (hgsupp : ∀ u, u ∉ Icc (-A) 0 → g₀ u = 0) {y : ℝ} (hy : -Real.log d < y) :
    shiftedHorizonProfile d g₀ y = 0 :=
  hgsupp (y + Real.log d) fun hm => by linarith [hm.2]

/-- Transport of compact window support: if `g₀` vanishes outside `[-A, 0]` and `1 ≤ d`, then
`shiftedHorizonProfile d g₀` vanishes outside `[-(A + log d), 0]`. -/
theorem shiftedHorizonProfile_eq_zero_of_notMem {A : ℝ} {d : ℕ} (hd : 1 ≤ d) {g₀ : ℝ → ℝ}
    (hgsupp : ∀ u, u ∉ Icc (-A) 0 → g₀ u = 0) {y : ℝ}
    (hy : y ∉ Icc (-(A + Real.log d)) 0) :
    shiftedHorizonProfile d g₀ y = 0 := by
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
  refine hgsupp (y + Real.log d) fun hm => hy ⟨by linarith [hm.1], by linarith [hm.2]⟩

/-- **Exact Ramanujan-divisibility decomposition.** For `1 ≤ d`, `dirichletShiftWeights d g₀` splits
into the nonzero conductor-`1` untwisted horizon block of `d⁻¹ g₀(· + log d)` plus the conductor-`d`
twisted block `(d⁻¹ g₀(· + log d)) · primeTwist d`. -/
theorem dirichletShiftWeights_eq_horizon_add_twisted {d : ℕ} (hd : 1 ≤ d) (g₀ : ℝ → ℝ)
    (N n : ℕ) :
    dirichletShiftWeights d g₀ N n =
      horizonWeights (fun y => (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y) N n +
        twistedWeights (fun y => (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y) (primeTwist d) N n := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  unfold dirichletShiftWeights twistedWeights horizonWeights primeTwist
  split_ifs with hdvd
  · field_simp [hd0]; ring
  · field_simp [hd0]; ring

/-! ### 2. Direct `O(1)` Weil coupling, critical-curve limit, and pure-tail annihilation -/

private theorem contDiff_halfWeight_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 2 (halfWeight f) :=
  (Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul hf

private theorem isWindowTest_halfWeight_of_supp {B : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ y, y ∉ Icc (-B) 0 → f y = 0) :
    IsWindowTest B (halfWeight f) :=
  ⟨contDiff_halfWeight_of_contDiff hf, fun y hy => by simp [halfWeight, hsupp y hy]⟩

theorem halfWeight_add_smul (f g : ℝ → ℝ) (t : ℝ) :
    halfWeight (fun y => f y + t * g y) = fun y => halfWeight f y + t * halfWeight g y := by
  funext y; unfold halfWeight; ring

/-- **Direct `O(1)` bilinear Weil coupling.** Combining `horizonWeights h` on `[-(A + log d), 0]`
with `dirichletShiftWeights d g₀` (`g₀` on `[-A, 0]`) shifts the `O(1)` Weil term in `windowPencil`
by the explicit polarization cross-term
`2 splineAtom d⁻¹ weilPair (halfWeight h) (halfWeight (shiftedHorizonProfile d g₀))` plus the
quadratic shift `splineAtom d⁻² weilQuad (halfWeight (shiftedHorizonProfile d g₀))`. -/
theorem dirichletShift_orderOne_crossTerm_eq {d : ℕ} (hd : 1 ≤ d) {A : ℝ}
    {h g₀ : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (hg₀ : ContDiff ℝ 2 g₀)
    (hsupp : ∀ y, y ∉ Icc (-(A + Real.log d)) 0 → h y = 0)
    (hgsupp : ∀ u, u ∉ Icc (-A) 0 → g₀ u = 0) :
    splineAtom *
        weilQuad (halfWeight (fun y => h y + (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y)) =
      splineAtom * weilQuad (halfWeight h) +
        2 * splineAtom * (d : ℝ)⁻¹ *
          weilPair (halfWeight h) (halfWeight (shiftedHorizonProfile d g₀)) +
        splineAtom * ((d : ℝ)⁻¹) ^ 2 *
          weilQuad (halfWeight (shiftedHorizonProfile d g₀)) := by
  have hHr : halfWeight h ∈ realTests :=
    mem_realTests_of_windowTest (isWindowTest_halfWeight_of_supp hh hsupp)
  have hGr : halfWeight (shiftedHorizonProfile d g₀) ∈ realTests :=
    mem_realTests_of_windowTest (isWindowTest_halfWeight_of_supp
      (contDiff_shiftedHorizonProfile d hg₀)
      fun y hy => shiftedHorizonProfile_eq_zero_of_notMem hd hgsupp hy)
  rw [halfWeight_add_smul, weilQuad_add_smul hHr hGr ((d : ℝ)⁻¹)]
  ring

/-- **Exact critical-curve asymptotic for untwisted + multiplicative-convolution horizon blocks.**
For every divisor `1 < d`, along any critical curve `c_N^8 / log N → K > 0`, the combined weight
`horizonWeights h N + dirichletShiftWeights d g₀ N` converges to
`windowPencil K (halfWeight (h + d⁻¹ g₀(· + log d)))` plus the strictly positive conductor-`d`
Jordan block `((d⁸ - 1) · 7 J(1) / K) M₈(halfWeight (d⁻¹ g₀(· + log d)))`. -/
theorem dirichletShift_criticalCurve_exact {A : ℝ} (hA : 0 ≤ A) {d : ℕ} (hd : 1 < d)
    {h g₀ : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (hg₀ : ContDiff ℝ 2 g₀)
    (hsupp : ∀ y, y ∉ Icc (-(A + Real.log d)) 0 → h y = 0)
    (hgsupp : ∀ u, u ∉ Icc (-A) 0 → g₀ u = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N
        (fun n => horizonWeights h N n + dirichletShiftWeights d g₀ N n)
        (atomDilate tiltedUnitSpline (c N / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2)) atTop
      (𝓝 (windowPencil K (halfWeight (fun y => h y + (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y)) +
        ((d : ℝ) ^ 8 - 1) * 7 * tiltedJordanOne / K *
          exponentialMass 8 (halfWeight (fun y => (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y)))) := by
  have hd1 : 1 ≤ d := hd.le
  have hB : 0 ≤ A + Real.log d := add_nonneg hA (Real.log_nonneg (by exact_mod_cast hd1))
  set g_eff : ℝ → ℝ := fun y => (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y
  set h_eff : ℝ → ℝ := fun y => h y + g_eff y
  have hg_eff : ContDiff ℝ 2 g_eff := contDiff_const.mul (contDiff_shiftedHorizonProfile d hg₀)
  have hh_eff : ContDiff ℝ 2 h_eff := hh.add hg_eff
  have hg_eff_supp : ∀ y, y ∉ Icc (-(A + Real.log d)) 0 → g_eff y = 0 := fun y hy => by
    dsimp only [g_eff]; rw [shiftedHorizonProfile_eq_zero_of_notMem hd1 hgsupp hy, mul_zero]
  have hh_eff_supp : ∀ y, y ∉ Icc (-(A + Real.log d)) 0 → h_eff y = 0 := fun y hy => by
    dsimp only [h_eff]; rw [hsupp y hy, hg_eff_supp y hy, add_zero]
  have hw_eq : ∀ N, (fun n => horizonWeights h N n + dirichletShiftWeights d g₀ N n) =
      fun n => horizonWeights h_eff N n + twistedWeights g_eff (primeTwist d) N n := fun N => by
    funext n
    rw [dirichletShiftWeights_eq_horizon_add_twisted hd1 g₀ N n]
    dsimp only [h_eff, g_eff]
    unfold horizonWeights
    ring
  simp_rw [hw_eq]
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N) atTop (𝓝 K) := by
    refine hcrit.congr fun N => ?_
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hlim := graded_layer_criticalCurve_of_regularBulk contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (q := 8) (by norm_num) hC
    tiltedUnitSpline_decay (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
    hh_eff hg_eff hB hh_eff_supp hg_eff_supp hc1 hK hcrit' hd
  have hd8 : (d : ℝ) ^ ((7 : ℝ) + 1) = (d : ℝ) ^ (8 : ℕ) := by
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hint : ∀ k : ℝ → ℝ, ∫ y, Real.exp (-(((7 : ℝ) + 1) * y)) * halfWeight k y ^ 2 =
      exponentialMass 8 (halfWeight k) := fun k => by
    unfold exponentialMass; congr 1; funext y; norm_num
  rw [hd8, hint h_eff, hint g_eff] at hlim
  convert hlim using 2
  unfold windowPencil splineAtom
  ring

/-- Prime-conductor specialization of `dirichletShift_criticalCurve_exact`, matching the Jordan
normalization `7 ((p - 1) J(p)) / K` of `conductorGrading_obstruction_to_enteringConductor_payment`. -/
theorem dirichletShift_criticalCurve_prime {A : ℝ} (hA : 0 ≤ A) {p : ℕ} (hp : p.Prime)
    {h g₀ : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (hg₀ : ContDiff ℝ 2 g₀)
    (hsupp : ∀ y, y ∉ Icc (-(A + Real.log p)) 0 → h y = 0)
    (hgsupp : ∀ u, u ∉ Icc (-A) 0 → g₀ u = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K)) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N
        (fun n => horizonWeights h N n + dirichletShiftWeights p g₀ N n)
        (atomDilate tiltedUnitSpline (c N / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2)) atTop
      (𝓝 (windowPencil K (halfWeight (fun y => h y + (p : ℝ)⁻¹ * shiftedHorizonProfile p g₀ y)) +
        7 * (((p : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient p) / K *
          exponentialMass 8 (halfWeight (fun y => (p : ℝ)⁻¹ * shiftedHorizonProfile p g₀ y)))) := by
  have hlim := dirichletShift_criticalCurve_exact hA hp.one_lt hh hg₀ hsupp hgsupp hc1 hK hcrit
  rw [jordanCoefficient_prime hp]
  convert hlim using 2
  ring

/-- **Exact `O(1)` annihilation of pure-tail horizon profiles.** For every `1 < d`, `0 ≤ A`, and
nonzero `h ∈ C²` supported in the tail `[-(A + log d), -log d]` (even if `weilQuad (halfWeight h) < 0`),
choosing `g₀(u) = -d · h(u - log d)` cancels `h + d⁻¹ g₀(· + log d)` identically, reducing the
critical-curve limit to `((d⁸ - 1) · 7 J(1) / K) M₈(halfWeight h) > 0` for **every** `K > 0`. -/
theorem pureTail_exact_orderOne_annihilation {A : ℝ} (hA : 0 ≤ A) {d : ℕ} (hd : 1 < d)
    {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (htail : ∀ y, y ∉ Icc (-(A + Real.log d)) (-Real.log d) → h y = 0)
    (hne : halfWeight h ≠ 0) :
    let g₀ : ℝ → ℝ := fun u => -(d : ℝ) * h (u - Real.log d)
    ContDiff ℝ 2 g₀ ∧ (∀ u, u ∉ Icc (-A) 0 → g₀ u = 0) ∧
      (∀ y, h y + (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y = 0) ∧
      ∀ {K : ℝ}, 0 < K → ∀ {c : ℕ → ℝ}, (∀ N, 1 ≤ c N) →
        Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K) →
        Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N
            (fun n => horizonWeights h N n + dirichletShiftWeights d g₀ N n)
            (atomDilate tiltedUnitSpline (c N / N))) /
              ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2)) atTop
          (𝓝 (((d : ℝ) ^ 8 - 1) * 7 * tiltedJordanOne / K *
            exponentialMass 8 (halfWeight h))) ∧
        0 < ((d : ℝ) ^ 8 - 1) * 7 * tiltedJordanOne / K *
          exponentialMass 8 (halfWeight h) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hlogd : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd.le)
  set g₀ : ℝ → ℝ := fun u => -(d : ℝ) * h (u - Real.log d)
  have hg₀ : ContDiff ℝ 2 g₀ := contDiff_const.mul (hh.comp (contDiff_id.sub contDiff_const))
  have hsupp : ∀ y, y ∉ Icc (-(A + Real.log d)) 0 → h y = 0 := fun y hy =>
    htail y fun hm => hy ⟨hm.1, by linarith [hm.2]⟩
  have hgsupp : ∀ u, u ∉ Icc (-A) 0 → g₀ u = 0 := fun u hu => by
    dsimp only [g₀]
    rw [htail (u - Real.log d) fun hm => hu ⟨by linarith [hm.1], by linarith [hm.2]⟩, mul_zero]
  have hgeff : (fun y => (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y) = fun y => -h y := by
    funext y; dsimp only [g₀, shiftedHorizonProfile]; rw [add_sub_cancel_right]; field_simp [hd0]
  have hcancel : ∀ y, h y + (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y = 0 := fun y => by
    have := congrFun hgeff y
    change (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y = -h y at this
    linarith
  refine ⟨hg₀, hgsupp, hcancel, fun {K} hK {c} hc1 hcrit => ?_⟩
  have hlim := dirichletShift_criticalCurve_exact hA hd hh hg₀ hsupp hgsupp hc1 hK hcrit
  have hz : halfWeight (fun y => h y + (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y) = 0 := by
    funext y; simp [halfWeight, hcancel y]
  have hpen0 : windowPencil K (0 : ℝ → ℝ) = 0 := by
    have hQ0 : weilQuad (0 : ℝ → ℝ) = 0 := by
      have hz : ∀ t : ℝ, (fun u => (0 : ℝ → ℝ) u + t * (0 : ℝ → ℝ) u) = (0 : ℝ → ℝ) := fun t => by
        funext u; simp
      have h1 := weilQuad_add_smul realTests.zero_mem realTests.zero_mem 1
      have h2 := weilQuad_add_smul realTests.zero_mem realTests.zero_mem (-1)
      rw [hz 1] at h1
      rw [hz (-1)] at h2
      linarith
    have hM0 : exponentialMass 8 (0 : ℝ → ℝ) = 0 := by simp [exponentialMass]
    simp [windowPencil, hQ0, hM0]
  have hMneg : exponentialMass 8 (halfWeight fun y => -h y) = exponentialMass 8 (halfWeight h) := by
    unfold exponentialMass halfWeight; congr 1; funext y; ring
  rw [hz, hpen0, zero_add, hgeff, hMneg] at hlim
  have hH : IsWindowTest (A + Real.log d) (halfWeight h) := isWindowTest_halfWeight_of_supp hh hsupp
  have hM_pos := exponentialMass_pos hH hne
  have hd8_pos : 0 < (d : ℝ) ^ 8 - 1 := by
    have h2d : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hpow : (2 : ℝ) ^ 8 ≤ (d : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) h2d 8
    linarith [show (1 : ℝ) < (2 : ℝ) ^ 8 by norm_num]
  have hJ := tiltedJordanOne_pos
  exact ⟨hlim, by positivity⟩

/-! ### 3. Head-obstruction necessity, open-head stabilization, `d = 2` theorem, and RH equivalence -/

/-- **Head-obstruction necessity law.** Because `shiftedHorizonProfile d g₀` vanishes on
`(-log d, 0]` whenever `g₀` is supported in `[-A, 0]` (and vanishes everywhere at `A = 0`), if
for every `A ≥ 0` and every nonzero horizon test `h` on `[-(A + log d), 0]` some `g₀` on `[-A, 0]`
keeps the critical-curve limit nonnegative across all `K > 0`, then `windowThreshold (log d) = ⊤`. -/
theorem dirichletShift_head_obstruction_necessity {d : ℕ}
    (hstab : ∀ A : ℝ, 0 ≤ A → ∀ h : ℝ → ℝ, ContDiff ℝ 2 h →
      (∀ y, y ∉ Icc (-(A + Real.log d)) 0 → h y = 0) → halfWeight h ≠ 0 →
      ∃ g₀ : ℝ → ℝ, ContDiff ℝ 2 g₀ ∧ (∀ u, u ∉ Icc (-A) 0 → g₀ u = 0) ∧
        ∀ K : ℝ, 0 < K →
          0 ≤ windowPencil K (halfWeight (fun y => h y + (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y)) +
            ((d : ℝ) ^ 8 - 1) * 7 * tiltedJordanOne / K *
              exponentialMass 8 (halfWeight (fun y => (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y))) :
    windowThreshold (Real.log d) = ⊤ := by
  rw [windowThreshold_eq_top_iff]
  intro H hH
  by_contra hneg
  push Not at hneg
  have hH_ne : H ≠ 0 := by
    rintro rfl
    have hf := weilQuad_ge_neg_exponentialMass hH (by norm_num : (1 : ℝ) < 8)
    have h0 : exponentialMass 8 (0 : ℝ → ℝ) = 0 := by simp [exponentialMass]
    rw [h0, mul_zero, neg_zero] at hf
    linarith
  set h : ℝ → ℝ := fun y => Real.exp (-(y / 2)) * H y
  have hh : ContDiff ℝ 2 h :=
    (Real.contDiff_exp.comp (contDiff_id.div_const 2).neg).mul hH.contDiff
  have hsupp0 : ∀ y, y ∉ Icc (-(0 + Real.log d)) 0 → h y = 0 := fun y hy => by
    rw [zero_add] at hy; simp [h, hH.vanish y hy]
  have hhw : halfWeight h = H := halfWeight_inv
  obtain ⟨g₀, hg₀, hgsupp, hK_all⟩ := hstab 0 le_rfl h hh hsupp0 (hhw.symm ▸ hH_ne)
  -- A continuous function vanishing off `[-0, 0] = {0}` vanishes identically on `ℝ`
  have hg₀_zero : ∀ u, g₀ u = 0 := fun u => by
    by_cases hu : u = 0
    · subst hu
      have hlim1 : Tendsto g₀ (𝓝[>] 0) (𝓝 (g₀ 0)) :=
        hg₀.continuous.continuousAt.mono_left nhdsWithin_le_nhds
      have hlim0 : Tendsto g₀ (𝓝[>] 0) (𝓝 0) :=
        tendsto_const_nhds.congr' (eventually_nhdsWithin_iff.mpr
          (Eventually.of_forall fun v (hv : 0 < v) =>
            (hgsupp v fun hm => by linarith [hm.2]).symm))
      exact tendsto_nhds_unique hlim1 hlim0
    · refine hgsupp u fun hm => hu ?_
      linarith [hm.1, hm.2]
  have hgeff0 : (fun y => (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y) = 0 := by
    funext y; simp [shiftedHorizonProfile, hg₀_zero]
  have hheff : (fun y => h y + (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y) = h := by
    funext y; simp [shiftedHorizonProfile, hg₀_zero]
  have hM0 : exponentialMass 8 (halfWeight (0 : ℝ → ℝ)) = 0 := by
    simp [exponentialMass, halfWeight]
  have hq : 0 < -weilQuad H := neg_pos.mpr hneg
  have hκ := splineAtom_pos
  have hJ := tiltedJordanOne_pos
  have hM_nn : 0 ≤ exponentialMass 8 H :=
    integral_nonneg fun y => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  set K₀ := testCriticalMultiple H + 1
  have htc_nn : 0 ≤ testCriticalMultiple H := by unfold testCriticalMultiple; positivity
  have hK₀_pos : 0 < K₀ := by dsimp only [K₀]; linarith
  have hnn := hK_all K₀ hK₀_pos
  rw [hheff, hhw, hgeff0, hM0, mul_zero, add_zero] at hnn
  have hlt : testCriticalMultiple H < K₀ := by dsimp only [K₀]; linarith
  rw [testCriticalMultiple, div_lt_iff₀ (mul_pos hκ hq)] at hlt
  unfold windowPencil at hnn
  have hdiv_lt : 7 * tiltedJordanOne / K₀ * exponentialMass 8 H < splineAtom * (-weilQuad H) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hK₀_pos]
    linarith
  linarith

/-- **Open-head stabilization theorem.** Whenever `1 < d` and `windowThreshold (log d + ε) = ⊤` for
some `ε > 0`, for **every** `A ≥ 0` and **every** `h ∈ C²` supported in `[-(A + log d), 0]` with
`halfWeight h ≠ 0` (even if `weilQuad (halfWeight h) < 0`!), there exists a single `K`-independent
profile `g₀ ∈ C²` supported in `[-A, 0]` such that for **every** `K > 0` and **every** critical
curve `c_N^8 / log N → K`:
1. the critical-curve limit of `horizonWeights h N + dirichletShiftWeights d g₀ N` is strictly
   positive, and
2. eventually in `N`, `0 < weilQuad (atomicTest N (horizonWeights h N + dirichletShiftWeights d g₀ N) ...)`. -/
theorem exists_dirichletShift_eventually_pos_of_windowThreshold_add_pos_eq_top {d : ℕ} (hd : 1 < d)
    {ε : ℝ} (hε : 0 < ε) (htop : windowThreshold (Real.log d + ε) = ⊤)
    {A : ℝ} (hA : 0 ≤ A) {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ y, y ∉ Icc (-(A + Real.log d)) 0 → h y = 0) (hne : halfWeight h ≠ 0) :
    ∃ g₀ : ℝ → ℝ, ContDiff ℝ 2 g₀ ∧ (∀ u, u ∉ Icc (-A) 0 → g₀ u = 0) ∧
      ∀ {K : ℝ}, 0 < K →
        0 < windowPencil K (halfWeight (fun y => h y + (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y)) +
            ((d : ℝ) ^ 8 - 1) * 7 * tiltedJordanOne / K *
              exponentialMass 8 (halfWeight (fun y => (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y)) ∧
        ∀ {c : ℕ → ℝ}, (∀ N, 1 ≤ c N) →
          Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K) →
          ∀ᶠ N : ℕ in atTop,
            0 < weilQuad (atomicTest N
              (fun n => horizonWeights h N n + dirichletShiftWeights d g₀ N n)
              (atomDilate tiltedUnitSpline (c N / N))) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  set a : ℝ := -(Real.log d + ε)
  set b : ℝ := -Real.log d
  have hab : a < b := by dsimp only [a, b]; linarith
  set g₀ : ℝ → ℝ := fun u => -(d : ℝ) * cutoff a b (u - Real.log d) * h (u - Real.log d)
  have hg₀ : ContDiff ℝ 2 g₀ :=
    (contDiff_const.mul ((contDiff_cutoff a b).comp (contDiff_id.sub contDiff_const))).mul
      (hh.comp (contDiff_id.sub contDiff_const))
  have hgsupp : ∀ u, u ∉ Icc (-A) 0 → g₀ u = 0 := fun u hu => by
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    dsimp only [g₀]
    rcases hu with hlt | hgt
    · rw [hsupp (u - Real.log d) fun hm => by linarith [hm.1], mul_zero]
    · rw [cutoff_of_ge hab (by dsimp only [b]; linarith), mul_zero, zero_mul]
  set g_eff : ℝ → ℝ := fun y => (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y
  set h_head : ℝ → ℝ := fun y => h y + g_eff y
  have hgeff_eq : ∀ y, g_eff y = -cutoff a b y * h y := fun y => by
    dsimp only [g_eff, g₀, shiftedHorizonProfile]
    rw [add_sub_cancel_right]
    field_simp [hd0]
  have hhhead_eq : ∀ y, h_head y = (1 - cutoff a b y) * h y := fun y => by
    dsimp only [h_head]; rw [hgeff_eq y]; ring
  have hg_eff_diff : ContDiff ℝ 2 g_eff :=
    contDiff_const.mul (contDiff_shiftedHorizonProfile d hg₀)
  have hh_head_diff : ContDiff ℝ 2 h_head := hh.add hg_eff_diff
  have hH_head : IsWindowTest (Real.log d + ε) (halfWeight h_head) := by
    refine isWindowTest_halfWeight_of_supp hh_head_diff fun y hy => ?_
    rw [mem_Icc, not_and_or, not_le, not_le] at hy
    rw [hhhead_eq y]
    rcases hy with hlt | hgt
    · rw [cutoff_of_le hab (by dsimp only [a]; linarith), sub_self, zero_mul]
    · rw [hsupp y fun hm => by linarith [hm.2], mul_zero]
  have hG_eff : IsWindowTest (A + Real.log d) (halfWeight g_eff) := by
    refine isWindowTest_halfWeight_of_supp hg_eff_diff fun y hy => ?_
    rw [hgeff_eq y, hsupp y hy, mul_zero]
  have hQ_head_nn : 0 ≤ weilQuad (halfWeight h_head) :=
    windowThreshold_eq_top_iff.mp htop (halfWeight h_head) hH_head
  have hne_split : halfWeight h_head ≠ 0 ∨ halfWeight g_eff ≠ 0 := by
    by_contra hboth
    push Not at hboth
    apply hne
    funext y
    have h1 := congrFun hboth.1 y
    have h2 := congrFun hboth.2 y
    dsimp only [halfWeight, h_head, Pi.zero_apply] at h1 h2 ⊢
    linarith
  have hd8_pos : 0 < (d : ℝ) ^ 8 - 1 := by
    have h2d : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hpow : (2 : ℝ) ^ 8 ≤ (d : ℝ) ^ 8 := pow_le_pow_left₀ (by norm_num) h2d 8
    linarith [show (1 : ℝ) < (2 : ℝ) ^ 8 by norm_num]
  refine ⟨g₀, hg₀, hgsupp, fun {K} hK => ?_⟩
  have hκ := splineAtom_pos
  have hJ := tiltedJordanOne_pos
  have hQ_term : 0 ≤ splineAtom * weilQuad (halfWeight h_head) := mul_nonneg hκ.le hQ_head_nn
  have hMh_nn : 0 ≤ exponentialMass 8 (halfWeight h_head) :=
    integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hMg_nn : 0 ≤ exponentialMass 8 (halfWeight g_eff) :=
    integral_nonneg fun _ => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hlim_pos :
      0 < windowPencil K (halfWeight h_head) +
        ((d : ℝ) ^ 8 - 1) * 7 * tiltedJordanOne / K * exponentialMass 8 (halfWeight g_eff) := by
    unfold windowPencil
    rcases hne_split with hh_ne | hg_ne
    · have hMh_pos := exponentialMass_pos hH_head hh_ne
      have h1 : 0 < 7 * tiltedJordanOne / K * exponentialMass 8 (halfWeight h_head) := by positivity
      have h2 : 0 ≤ ((d : ℝ) ^ 8 - 1) * 7 * tiltedJordanOne / K *
          exponentialMass 8 (halfWeight g_eff) := by positivity
      linarith
    · have hMg_pos := exponentialMass_pos hG_eff hg_ne
      have h1 : 0 ≤ 7 * tiltedJordanOne / K * exponentialMass 8 (halfWeight h_head) := by positivity
      have h2 : 0 < ((d : ℝ) ^ 8 - 1) * 7 * tiltedJordanOne / K *
          exponentialMass 8 (halfWeight g_eff) := by positivity
      linarith
  refine ⟨hlim_pos, fun {c} hc1 hcrit => ?_⟩
  have hlim := dirichletShift_criticalCurve_exact hA hd hh hg₀ hsupp hgsupp hc1 hK hcrit
  filter_upwards [hlim.eventually (Ioi_mem_nhds hlim_pos)] with N hN_pos
  change 0 < (c N)⁻¹ * (weilQuad (atomicTest N
      (fun n => horizonWeights h N n + dirichletShiftWeights d g₀ N n)
      (atomDilate tiltedUnitSpline (c N / N))) /
        ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) at hN_pos
  by_contra hQ_np
  push Not at hQ_np
  have hc_nn : 0 ≤ (c N)⁻¹ := inv_nonneg.mpr (zero_le_one.trans (hc1 N))
  have hint_nn : 0 ≤ ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hprod_np : (c N)⁻¹ * (weilQuad (atomicTest N
      (fun n => horizonWeights h N n + dirichletShiftWeights d g₀ N n)
      (atomDilate tiltedUnitSpline (c N / N))) /
        ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hc_nn (div_nonpos_of_nonpos_of_nonneg hQ_np hint_nn)
  linarith

/-- Centering `H ∈ W_A` into `[-A/2, A/2]` transports the infinite-tower Weil floor
`weilFloorTowerConst k` to every window `A ≤ 2 * weilFloorApertureTower k`. -/
theorem weilQuad_ge_of_le_two_mul_weilFloorApertureTower (k : ℕ) {A : ℝ}
    (hA : A ≤ 2 * weilFloorApertureTower k) {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    weilFloorTowerConst k * (∫ u, H u ^ 2) ≤ weilQuad H := by
  set f : ℝ → ℝ := fun u => H (u - A / 2)
  have hfd : ContDiff ℝ 2 f := hH.contDiff.comp (contDiff_id.sub contDiff_const)
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_Icc (a := -(A / 2)) (b := A / 2)) fun u hu =>
      hH.vanish (u - A / 2) fun hm => hu ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have hfs : ∀ u, weilFloorApertureTower k < |u| → f u = 0 := fun u hu => by
    refine hH.vanish (u - A / 2) fun hm => ?_
    rcases lt_abs.mp hu with hpos | hneg
    · linarith [hm.2]
    · linarith [hm.1]
  have hfloor := fullZeroForm_ge_of_support_le_weilFloorApertureTower k hfd hfc hfs
  have hpair : weilPair f f = ArithmeticCriticalityTheory.fullZeroForm f :=
    LatticeSectionTheory.WindowJumpCounts.weilPair_eq_fullZeroForm ⟨hfd, hfc⟩
  have hquad : weilPair f f = weilQuad H := weilQuad_comp_sub H (A / 2)
  have hmass : (∫ u, f u ^ 2) = ∫ u, H u ^ 2 :=
    integral_sub_right_eq_self (μ := volume) (fun u => H u ^ 2) (A / 2)
  rw [hmass, ← hpair, hquad] at hfloor
  exact hfloor

/-- **Infinite-tower unconditional horizon threshold.** For every `k : ℕ` and every window length
`A ≤ 2 * weilFloorApertureTower k` (strictly exceeding `2 * enlargedWeilFloorAperture` and
`2 * successorWeilFloorAperture` for `k ≥ 1`), `windowThreshold A = ⊤`. -/
theorem windowThreshold_eq_top_of_le_two_mul_weilFloorApertureTower (k : ℕ) {A : ℝ}
    (hA : A ≤ 2 * weilFloorApertureTower k) :
    windowThreshold A = ⊤ :=
  windowThreshold_eq_top_iff.mpr fun H hH => by
    have hf := weilQuad_ge_of_le_two_mul_weilFloorApertureTower k hA hH
    have hnn : 0 ≤ weilFloorTowerConst k * ∫ u, H u ^ 2 :=
      mul_nonneg (weilFloorTowerConst_pos k).le (integral_nonneg fun _ => sq_nonneg _)
    linarith

/-- **Unconditional `d = 2` arbitrary-aperture critical-curve stabilization.**
Unlike orthogonal `twistedWeights g (primeTwist 2) N` (which fail for large `K` whenever
`weilQuad (halfWeight h) < 0` by `conductorGrading_obstruction_to_enteringConductor_payment`),
for **every** aperture `A ≥ 0` and **every** `h ∈ C²` supported in `[-(A + log 2), 0]` with
`halfWeight h ≠ 0`, there exists a single `K`-independent profile `g₀ ∈ C²` supported in `[-A, 0]`
such that `horizonWeights h N + dirichletShiftWeights 2 g₀ N` has strictly positive critical-curve
limit and eventually strictly positive `weilQuad (atomicTest ...)` along **every** critical curve
`c_N^8 / log N → K` for **all** `K > 0`. -/
theorem exists_primeTwo_dirichletShift_eventually_pos_all_criticalCurves
    {A : ℝ} (hA : 0 ≤ A) {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ y, y ∉ Icc (-(A + Real.log (2 : ℕ))) 0 → h y = 0) (hne : halfWeight h ≠ 0) :
    ∃ g₀ : ℝ → ℝ, ContDiff ℝ 2 g₀ ∧ (∀ u, u ∉ Icc (-A) 0 → g₀ u = 0) ∧
      ∀ {K : ℝ}, 0 < K →
        0 < windowPencil K (halfWeight (fun y => h y + (2 : ℝ)⁻¹ * shiftedHorizonProfile 2 g₀ y)) +
            7 * (((2 : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient 2) / K *
              exponentialMass 8 (halfWeight (fun y => (2 : ℝ)⁻¹ * shiftedHorizonProfile 2 g₀ y)) ∧
        ∀ {c : ℕ → ℝ}, (∀ N, 1 ≤ c N) →
          Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K) →
          ∀ᶠ N : ℕ in atTop,
            0 < weilQuad (atomicTest N
              (fun n => horizonWeights h N n + dirichletShiftWeights 2 g₀ N n)
              (atomDilate tiltedUnitSpline (c N / N))) := by
  set ε₂ : ℝ := 2 * weilFloorApertureTower 0 - Real.log (2 : ℕ)
  have hlog2_lt : Real.log (2 : ℕ) < 2 * weilFloorApertureTower 0 := by
    calc Real.log (2 : ℕ) = Real.log 2 := by norm_num
      _ < 181 / 250 := by linarith [Real.log_two_lt_d9]
      _ < 2 * enlargedWeilFloorAperture := by linarith [enlargedWeilFloorAperture_bounds.1]
      _ < 2 * weilFloorApertureTower 0 := by
        linarith [enlargedWeilFloorAperture_lt_weilFloorApertureTower 0]
  have hε₂ : 0 < ε₂ := by dsimp only [ε₂]; linarith
  have htop : windowThreshold (Real.log (2 : ℕ) + ε₂) = ⊤ := by
    have heq : Real.log (2 : ℕ) + ε₂ = 2 * weilFloorApertureTower 0 := by dsimp only [ε₂]; ring
    rw [heq]
    exact windowThreshold_eq_top_of_le_two_mul_weilFloorApertureTower 0 le_rfl
  obtain ⟨g₀, hg₀, hgsupp, hpos⟩ :=
    exists_dirichletShift_eventually_pos_of_windowThreshold_add_pos_eq_top
      (by decide : 1 < 2) hε₂ htop hA hh hsupp hne
  refine ⟨g₀, hg₀, hgsupp, fun {K} hK => ?_⟩
  obtain ⟨hlim_pos, hev⟩ := hpos hK
  push_cast at hlim_pos
  have hjeq : ((2 : ℝ) ^ 8 - 1) * 7 * tiltedJordanOne =
      7 * (((2 : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient 2) := by
    have hj2 := jordanCoefficient_prime Nat.prime_two
    push_cast at hj2
    linarith [hj2]
  rw [hjeq] at hlim_pos
  exact ⟨hlim_pos, hev⟩

/-- **Global equivalence across divisors `d ≥ 2` and across primes `p` with `RiemannHypothesis`.**
Universal critical-curve stabilization by `dirichletShiftWeights d g₀` across all `d ≥ 2` (or all
primes `p`) and all `A ≥ 0` holds if and only if `∀ d ≥ 2, windowThreshold (log d) = ⊤`, and if
and only if `RiemannHypothesis`. -/
theorem forall_divisor_dirichletShift_stabilizes_iff_riemannHypothesis :
    ((∀ d : ℕ, 1 < d → ∀ A : ℝ, 0 ≤ A → ∀ h : ℝ → ℝ, ContDiff ℝ 2 h →
        (∀ y, y ∉ Icc (-(A + Real.log d)) 0 → h y = 0) → halfWeight h ≠ 0 →
        ∃ g₀ : ℝ → ℝ, ContDiff ℝ 2 g₀ ∧ (∀ u, u ∉ Icc (-A) 0 → g₀ u = 0) ∧
          ∀ K : ℝ, 0 < K →
            0 < windowPencil K
                (halfWeight (fun y => h y + (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y)) +
              ((d : ℝ) ^ 8 - 1) * 7 * tiltedJordanOne / K *
                exponentialMass 8
                  (halfWeight (fun y => (d : ℝ)⁻¹ * shiftedHorizonProfile d g₀ y))) ↔
      RiemannHypothesis) ∧
    ((∀ p : ℕ, p.Prime → ∀ A : ℝ, 0 ≤ A → ∀ h : ℝ → ℝ, ContDiff ℝ 2 h →
        (∀ y, y ∉ Icc (-(A + Real.log p)) 0 → h y = 0) → halfWeight h ≠ 0 →
        ∃ g₀ : ℝ → ℝ, ContDiff ℝ 2 g₀ ∧ (∀ u, u ∉ Icc (-A) 0 → g₀ u = 0) ∧
          ∀ K : ℝ, 0 < K →
            0 < windowPencil K
                (halfWeight (fun y => h y + (p : ℝ)⁻¹ * shiftedHorizonProfile p g₀ y)) +
              7 * (((p : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient p) / K *
                exponentialMass 8
                  (halfWeight (fun y => (p : ℝ)⁻¹ * shiftedHorizonProfile p g₀ y))) ↔
      RiemannHypothesis) := by
  constructor
  · constructor
    · intro hdiv
      rw [riemannHypothesis_iff_windowThreshold_eq_top]
      intro A hA
      set d : ℕ := ⌈Real.exp A⌉₊ + 2
      have hd : 1 < d := by dsimp only [d]; omega
      have htop_d : windowThreshold (Real.log d) = ⊤ :=
        dirichletShift_head_obstruction_necessity fun B hB h hh hsupp hne => by
          obtain ⟨g₀, hg₀, hgsupp, hpos⟩ := hdiv d hd B hB h hh hsupp hne
          exact ⟨g₀, hg₀, hgsupp, fun K hK => (hpos K hK).le⟩
      have hle : A ≤ Real.log d := by
        have hexp_le : Real.exp A ≤ d := by
          calc Real.exp A ≤ (⌈Real.exp A⌉₊ : ℝ) := Nat.le_ceil _
            _ ≤ ((⌈Real.exp A⌉₊ + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right _ 2
        simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos A) hexp_le
      exact top_unique (htop_d ▸ windowThreshold_antitone hle)
    · intro hrh d hd A hA h hh hsupp hne
      have htop1 : windowThreshold (Real.log d + 1) = ⊤ :=
        riemannHypothesis_iff_windowThreshold_eq_top.mp hrh (Real.log d + 1)
          (add_nonneg (Real.log_nonneg (by exact_mod_cast hd.le)) zero_le_one)
      obtain ⟨g₀, hg₀, hgsupp, hpos⟩ :=
        exists_dirichletShift_eventually_pos_of_windowThreshold_add_pos_eq_top
          hd zero_lt_one htop1 hA hh hsupp hne
      exact ⟨g₀, hg₀, hgsupp, fun K hK => (hpos hK).1⟩
  · have hj_prime : ∀ {p : ℕ}, p.Prime →
        ((p : ℝ) ^ 8 - 1) * 7 * tiltedJordanOne =
          7 * (((p : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient p) := by
      intro p hp
      linarith [jordanCoefficient_prime hp]
    constructor
    · intro hprime
      rw [riemannHypothesis_iff_windowThreshold_eq_top]
      intro A hA
      obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes ⌈Real.exp A⌉₊
      have htop_p : windowThreshold (Real.log p) = ⊤ :=
        dirichletShift_head_obstruction_necessity fun B hB h hh hsupp hne => by
          obtain ⟨g₀, hg₀, hgsupp, hpos⟩ := hprime p hp B hB h hh hsupp hne
          refine ⟨g₀, hg₀, hgsupp, fun K hK => ?_⟩
          rw [hj_prime hp]
          exact (hpos K hK).le
      have hle : A ≤ Real.log p := by
        have hexp_le : Real.exp A ≤ p :=
          (Nat.le_ceil _).trans (by exact_mod_cast hp_ge)
        simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos A) hexp_le
      exact top_unique (htop_p ▸ windowThreshold_antitone hle)
    · intro hrh p hp A hA h hh hsupp hne
      have htop1 : windowThreshold (Real.log p + 1) = ⊤ :=
        riemannHypothesis_iff_windowThreshold_eq_top.mp hrh (Real.log p + 1)
          (add_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_lt.le)) zero_le_one)
      obtain ⟨g₀, hg₀, hgsupp, hpos⟩ :=
        exists_dirichletShift_eventually_pos_of_windowThreshold_add_pos_eq_top
          hp.one_lt zero_lt_one htop1 hA hh hsupp hne
      refine ⟨g₀, hg₀, hgsupp, fun K hK => ?_⟩
      have hposK := (hpos hK).1
      rw [hj_prime hp] at hposK
      exact hposK

#print axioms dirichletShiftWeights_mul_sq_eq
#print axioms dirichletShiftWeights_eq_horizon_add_twisted
#print axioms dirichletShift_orderOne_crossTerm_eq
#print axioms dirichletShift_criticalCurve_exact
#print axioms dirichletShift_criticalCurve_prime
#print axioms pureTail_exact_orderOne_annihilation
#print axioms dirichletShift_head_obstruction_necessity
#print axioms exists_dirichletShift_eventually_pos_of_windowThreshold_add_pos_eq_top
#print axioms windowThreshold_eq_top_of_le_two_mul_weilFloorApertureTower
#print axioms exists_primeTwo_dirichletShift_eventually_pos_all_criticalCurves
#print axioms forall_divisor_dirichletShift_stabilizes_iff_riemannHypothesis

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

end
