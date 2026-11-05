import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalThresholdOfAWindow
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CompleteWeilCriticalMultipleAndWindowCorollaries
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonLayerIsGradedByConductor
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTransferAcrossAStage
import GaloisForLFunctions.WindowTowerOfSpecZ.TheFirstFoldPaysANegativeFrozenDirection

/-!
# Stage Transport of the Window Threshold and Entering-Conductor Obstructions

Across each integer stage `N → N + 1` (`B` with `windowLevel B = N + 1`), the critical window
threshold `windowThreshold B = R₁(B)` obeys an exact stage-transfer identity, an unconditional
super-`log 2` prime-entry propagation, two structural obstructions refuting uncoupled stage loans
and orthogonal conductor-`p` payment at `R = ∞`, an unconditional fixed-critical-multiple complete
family floor across all prime entries, and an exact single-prime transport equivalence with
`RiemannHypothesis`:

1. **Exact stage-transfer law and unconditional super-`log 2` transport**
   (`windowThreshold_eq_top_iff_stage_fold_payment`,
   `composite_stage_windowThreshold_eq_top_iff`,
   `stageTransport_windowThreshold_eq_top_of_endCoercive`,
   `unconditional_superLogTwo_primeTwo_transport`). At a composite stage `¬ IsPrimePow (N + 1)`,
   the fold increment vanishes identically (`R₁(B) = ⊤ ↔ stageForm N ≥ 0`). At a prime-power entry,
   `R₁(B) = ⊤` holds iff `stageForm N H + w_{N+1} foldEnergy B (log(N+1)) H` dominates the new
   end mass `w_{N+1} ∫ m_{log(N+1)} H²`. Unconditionally, setting
   `A₀ = 2 * enlargedWeilFloorAperture - log 2 > 0`, `R₁(A₀) = ⊤` propagates across the full
   `log 2` prime step to `R₁(A₀ + log 2) = ⊤` (`A₀ + log 2 > log 2`).

2. **Two exact obstructions: failure of the uncoupled stage loan and zero cross-conductor payment**
   (`firstFold_stageLoan_obstruction_on_positive_window`,
   `conductorGrading_obstruction_to_enteringConductor_payment`). Already at `B = 21 / 20 > log 2`
   (`windowLevel (21 / 20) = 2`), there exists `H ∈ IsWindowTest (21 / 20)` with
   `stageForm 1 H < 0 < weilQuad H`: positivity across the `p = 2` entry is paid strictly by the
   signed fold energy rather than by coercivity of `stageForm 1`. Moreover, along any critical curve
   `c_N^8 / log N → K`, the untwisted horizon profile `h` and the entering-conductor `p` Ramanujan
   profile `g` decouple at second order (`graded_layer_criticalCurve_exact`), so whenever
   `weilQuad (halfWeight h) < 0` on `[-(A + log p), 0]`, for every `g` there exists an explicit
   threshold `K_* > 0` above which `weilQuad` of the combined untwisted + conductor-`p` test is
   eventually strictly negative: positive diagonal energy in conductor `p` cannot pay a negative
   conductor-`1` window mode as `K → ∞`.

3. **Unconditional fixed-multiple propagation and global prime-transport equivalence**
   (`exists_uniform_criticalMultiple_across_all_primeEntries`,
   `stageTransport_across_prime_iff_riemannHypothesis`). Below `apertureIndependentThreshold > 0`
   and at the complete-Weil critical multiple `2 K₁ (log N)^{1/8}`, positivity holds unconditionally
   across every prime entry `A + log p`. Propagating `R₁(A) = ⊤ → R₁(A + log p) = ⊤` across all
   `A ≥ 0` for any single prime `p` is unconditionally equivalent to propagation across all primes,
   to `∀ A ≥ 0, R₁(A) = ⊤`, and to `RiemannHypothesis`.
-/

set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory Set

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ
open RHTower.WeilMarkovPole (primeJumpWeight primeJumpWeight_nonneg)
open ArithmeticElectrostatics RenormalizedArithmeticPotentialTheory
  CriticalArithmeticCorrelationTheory

/-! ### 1. Exact stage-transfer characterization and unconditional super-`log 2` transport -/

/-- **Exact stage-fold characterization of `windowThreshold B = ⊤`.**
On a window of stage level `windowLevel B = N + 1` (`1 ≤ N`), `windowThreshold B = ⊤` holds if and
only if the previous-stage datum `stageForm N H` plus the entering fold energy pays the new end
mass `primeJumpWeight (N + 1) * ∫ inWindowCount B (log(N + 1)) H²` on every window test `H`. -/
theorem windowThreshold_eq_top_iff_stage_fold_payment {B : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hB : windowLevel B = N + 1) :
    windowThreshold B = ⊤ ↔
      ∀ H : ℝ → ℝ, IsWindowTest B H →
        primeJumpWeight (N + 1) *
            (∫ u, inWindowCount B (Real.log (N + 1 : ℕ)) u * H u ^ 2) ≤
          stageForm N H +
            primeJumpWeight (N + 1) * foldEnergy B (Real.log (N + 1 : ℕ)) H := by
  rw [windowThreshold_eq_top_iff]
  refine forall_congr' fun H => imp_congr_right fun hH => ?_
  rw [weilQuad_eq_stageForm_add_fold hH hN hB]
  constructor <;> intro h <;> linarith

/-- **Composite stages carry zero fold cost.** If `windowLevel B = N + 1` (`1 ≤ N`) and `N + 1` is
not a prime power, `windowThreshold B = ⊤` iff `0 ≤ stageForm N H` on `IsWindowTest B`. -/
theorem composite_stage_windowThreshold_eq_top_iff {B : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hB : windowLevel B = N + 1) (hpp : ¬ IsPrimePow (N + 1)) :
    windowThreshold B = ⊤ ↔ ∀ H : ℝ → ℝ, IsWindowTest B H → 0 ≤ stageForm N H := by
  rw [windowThreshold_eq_top_iff]
  refine forall_congr' fun H => imp_congr_right fun hH => ?_
  rw [weilQuad_eq_stageForm_of_not_primePow hH hN hB hpp]

/-- **End-coercive stage transport.** If `stageForm N` pays the entering end mass on
`[-(A + log p), 0]` (`windowLevel (A + log p) = N + 1`), then `windowThreshold (A + log p) = ⊤`. -/
theorem stageTransport_windowThreshold_eq_top_of_endCoercive {A : ℝ} {p N : ℕ} (hN : 1 ≤ N)
    (hlev : windowLevel (A + Real.log p) = N + 1)
    (hend : ∀ H : ℝ → ℝ, IsWindowTest (A + Real.log p) H →
      primeJumpWeight (N + 1) *
        (∫ u, inWindowCount (A + Real.log p) (Real.log (N + 1 : ℕ)) u * H u ^ 2) ≤
        stageForm N H) :
    windowThreshold (A + Real.log p) = ⊤ :=
  windowThreshold_eq_top_iff.mpr fun H hH =>
    weilQuad_nonneg_of_endCoercive hH hN hlev (hend H hH)

/-- **Unconditional super-`log 2` transport across the entry of `p = 2`.**
At `A₀ = 2 * enlargedWeilFloorAperture - log 2`, `0 < A₀`, `log 2 < A₀ + log 2`, and both
`windowThreshold A₀ = ⊤` and `windowThreshold (A₀ + log 2) = ⊤` hold unconditionally. -/
theorem unconditional_superLogTwo_primeTwo_transport :
    let A₀ := 2 * ArithmeticIncidencePositivity.enlargedWeilFloorAperture - Real.log 2
    0 < A₀ ∧ Real.log 2 < A₀ + Real.log 2 ∧
      windowThreshold A₀ = ⊤ ∧ windowThreshold (A₀ + Real.log 2) = ⊤ := by
  dsimp only
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt : Real.log 2 < 2 * ArithmeticIncidencePositivity.enlargedWeilFloorAperture := by
    linarith [Real.log_two_lt_d9, ArithmeticIncidencePositivity.enlargedWeilFloorAperture_bounds.1]
  have hA₀_pos : 0 < 2 * ArithmeticIncidencePositivity.enlargedWeilFloorAperture - Real.log 2 := by
    linarith
  have hsum : 2 * ArithmeticIncidencePositivity.enlargedWeilFloorAperture - Real.log 2 +
      Real.log 2 = 2 * ArithmeticIncidencePositivity.enlargedWeilFloorAperture := sub_add_cancel _ _
  refine ⟨hA₀_pos, by linarith,
    windowThreshold_eq_top_of_le_enlarged (by linarith), ?_⟩
  rw [hsum]
  exact windowThreshold_eq_top_of_le_enlarged le_rfl

/-! ### 2. Structural obstructions: uncoupled stage-loan failure and conductor-grading decoupling -/

/-- **Obstruction to uncoupled stage loans at the first prime fold (`B = 21 / 20`).**
On `[-21/20, 0]` (`windowLevel (21 / 20) = 2`, the entry stage of `p = 2`), there exists a window
test `H` with `stageForm 1 H < 0 < weilQuad H`, forcing the signed fold energy
`primeJumpWeight 2 * foldEnergy (21 / 20) (log 2) H` to strictly exceed
`-stageForm 1 H + primeJumpWeight 2 * ∫ inWindowCount (21 / 20) (log 2) H² > 0`. -/
theorem firstFold_stageLoan_obstruction_on_positive_window :
    windowLevel (21 / 20) = 2 ∧
      ∃ H : ℝ → ℝ, IsWindowTest (21 / 20) H ∧ stageForm 1 H < 0 ∧ 0 < weilQuad H ∧
        0 < -stageForm 1 H +
            primeJumpWeight 2 * (∫ u, inWindowCount (21 / 20) (Real.log (2 : ℕ)) u * H u ^ 2) ∧
        -stageForm 1 H +
            primeJumpWeight 2 * (∫ u, inWindowCount (21 / 20) (Real.log (2 : ℕ)) u * H u ^ 2) <
          primeJumpWeight 2 * foldEnergy (21 / 20) (Real.log (2 : ℕ)) H := by
  have hlev : windowLevel (21 / 20) = 2 := by
    unfold windowLevel
    refine (Nat.floor_eq_iff (Real.exp_pos (21 / 20 : ℝ)).le).mpr ⟨?_, ?_⟩
    · have h : Real.log 2 ≤ (21 / 20 : ℝ) := by linarith only [Real.log_two_lt_d9]
      simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2), Nat.cast_ofNat] using
        Real.exp_le_exp.mpr h
    · have h : (21 / 20 : ℝ) < Real.log 3 := by linarith only [Real.log_three_gt_d9]
      simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3), Nat.cast_ofNat,
        show (2 : ℝ) + 1 = 3 by norm_num] using Real.exp_lt_exp.mpr h
  obtain ⟨H, hH, hneg, hpos⟩ := exists_first_stage_negative_frozen_positive_complete
  have hid := weilQuad_eq_stageForm_add_fold hH (N := 1) le_rfl hlev
  norm_num only [Nat.reduceAdd] at hid
  have hw2 : 0 ≤ primeJumpWeight 2 := primeJumpWeight_nonneg 2
  have hend_nn : 0 ≤ ∫ u, inWindowCount (21 / 20) (Real.log (2 : ℕ)) u * H u ^ 2 := by
    refine integral_nonneg fun u => mul_nonneg ?_ (sq_nonneg _)
    unfold inWindowCount
    exact add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
  have hprod_nn : 0 ≤ primeJumpWeight 2 *
      (∫ u, inWindowCount (21 / 20) (Real.log (2 : ℕ)) u * H u ^ 2) :=
    mul_nonneg hw2 hend_nn
  refine ⟨hlev, H, hH, hneg, hpos, by linarith, by linarith⟩

/-- **Conductor-grading obstruction to paying `R₁(A + log p) = ⊤` at the entering conductor.**
Along any critical curve `c_N^8 / log N → K` (`1 ≤ c_N`, `0 < K`), the combined untwisted profile
`h` and prime-`p` Ramanujan profile `g` supported in `[-(A + log p), 0]` decouple at second order
into `windowPencil K (halfWeight h)` plus the conductor-`p` block
`7 ((p - 1) J(p) / K) M₈(halfWeight g)`. Consequently, if `weilQuad (halfWeight h) < 0`, then for
every `g` there exists an explicit threshold `K_* > 0` such that for every `K > K_*`, eventually in
`N` the combined complete Weil energy `weilQuad (atomicTest ...)` is strictly negative. -/
theorem conductorGrading_obstruction_to_enteringConductor_payment {A : ℝ} (hA : 0 ≤ A)
    {p : ℕ} (hp : p.Prime) {h g : ℝ → ℝ} (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g)
    (hsupp : ∀ y, y ∉ Icc (-(A + Real.log p)) 0 → h y = 0)
    (hgsupp : ∀ y, y ∉ Icc (-(A + Real.log p)) 0 → g y = 0) :
    (∀ {c : ℕ → ℝ}, (∀ N, 1 ≤ c N) → ∀ {K : ℝ}, 0 < K →
      Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K) →
      Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N
          (fun n => horizonWeights h N n + twistedWeights g (primeTwist p) N n)
          (atomDilate tiltedUnitSpline (c N / N))) /
            ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2)) atTop
        (𝓝 (windowPencil K (halfWeight h) +
          7 * (((p : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient p) / K *
            exponentialMass 8 (halfWeight g)))) ∧
    (weilQuad (halfWeight h) < 0 →
      ∃ K_star : ℝ, 0 < K_star ∧ ∀ {K : ℝ}, K_star < K →
        ∀ {c : ℕ → ℝ}, (∀ N, 1 ≤ c N) →
          Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K) →
          ∀ᶠ N : ℕ in atTop,
            weilQuad (atomicTest N
              (fun n => horizonWeights h N n + twistedWeights g (primeTwist p) N n)
              (atomDilate tiltedUnitSpline (c N / N))) < 0) := by
  have hB : 0 ≤ A + Real.log p :=
    add_nonneg hA (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
  have hlim_all : ∀ {c : ℕ → ℝ}, (∀ N, 1 ≤ c N) → ∀ {K : ℝ}, 0 < K →
      Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K) →
      Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N
          (fun n => horizonWeights h N n + twistedWeights g (primeTwist p) N n)
          (atomDilate tiltedUnitSpline (c N / N))) /
            ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2)) atTop
        (𝓝 (windowPencil K (halfWeight h) +
          7 * (((p : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient p) / K *
            exponentialMass 8 (halfWeight g))) := by
    intro c hc1 K hK hcrit
    simpa only [windowPencil, splineAtom, exponentialMass] using
      graded_layer_criticalCurve_exact hh hg hB hsupp hgsupp hc1 hK hcrit hp
  refine ⟨hlim_all, fun hQ => ?_⟩
  set C_num : ℝ :=
    7 * tiltedJordanOne * exponentialMass 8 (halfWeight h) +
      7 * (((p : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient p) *
        exponentialMass 8 (halfWeight g) + 1
  have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
    linarith
  have hJp : 0 < ArithmeticDegenerationTheory.jordanCoefficient p :=
    ArithmeticDegenerationTheory.jordanCoefficient_pos hp.pos
  have hMh_nn : 0 ≤ exponentialMass 8 (halfWeight h) :=
    integral_nonneg fun y => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hMg_nn : 0 ≤ exponentialMass 8 (halfWeight g) :=
    integral_nonneg fun y => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hC_pos : 0 < C_num := by
    have := tiltedJordanOne_pos
    dsimp only [C_num]
    positivity
  have hden_pos : 0 < splineAtom * (-weilQuad (halfWeight h)) :=
    mul_pos splineAtom_pos (neg_pos.mpr hQ)
  refine ⟨C_num / (splineAtom * (-weilQuad (halfWeight h))), div_pos hC_pos hden_pos, ?_⟩
  intro K hK c hc1 hcrit
  have hK_pos : 0 < K := lt_trans (div_pos hC_pos hden_pos) hK
  have hlt_lim :
      windowPencil K (halfWeight h) +
        7 * (((p : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient p) / K *
          exponentialMass 8 (halfWeight g) < 0 := by
    have hmul : C_num < K * (splineAtom * (-weilQuad (halfWeight h))) :=
      (div_lt_iff₀ hden_pos).mp hK
    unfold windowPencil
    have hsum_eq :
        7 * tiltedJordanOne / K * exponentialMass 8 (halfWeight h) +
          7 * (((p : ℝ) - 1) * ArithmeticDegenerationTheory.jordanCoefficient p) / K *
            exponentialMass 8 (halfWeight g) =
        (C_num - 1) / K := by
      dsimp only [C_num]; ring
    rw [add_assoc, hsum_eq]
    have hdiv_lt : (C_num - 1) / K < splineAtom * (-weilQuad (halfWeight h)) := by
      rw [div_lt_iff₀ hK_pos]
      linarith
    linarith
  have hev := (hlim_all hc1 hK_pos hcrit).eventually (Iio_mem_nhds hlt_lim)
  filter_upwards [hev] with N hN_neg
  change (c N)⁻¹ * (weilQuad (atomicTest N
      (fun n => horizonWeights h N n + twistedWeights g (primeTwist p) N n)
      (atomDilate tiltedUnitSpline (c N / N))) /
        ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) < 0 at hN_neg
  by_contra hQ_nn
  push Not at hQ_nn
  have hc_nn : 0 ≤ (c N)⁻¹ := inv_nonneg.mpr (zero_le_one.trans (hc1 N))
  have hint_nn : 0 ≤ ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hprod_nn : 0 ≤ (c N)⁻¹ * (weilQuad (atomicTest N
      (fun n => horizonWeights h N n + twistedWeights g (primeTwist p) N n)
      (atomDilate tiltedUnitSpline (c N / N))) /
        ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) :=
    mul_nonneg hc_nn (div_nonneg hQ_nn hint_nn)
  linarith

/-! ### 3. Unconditional fixed-multiple propagation and global prime-transport equivalence -/

/-- **Unconditional fixed-critical-multiple propagation across all prime entries.**
The positive aperture-independent threshold `apertureIndependentThreshold > 0` bounds
`windowThreshold (A + log p)` from below for every `A : ℝ` and every `p : ℕ`, while there exists
`K₁ > 0` (`2 K₁ ≤ 1`) at which `completeWeilMatrix tiltedUnitSpline (2 K₁ (log N)^{1/8}) N` is
eventually positive definite on the whole prime-horizon space. -/
theorem exists_uniform_criticalMultiple_across_all_primeEntries :
    0 < apertureIndependentThreshold ∧
      (∀ (A : ℝ) (p : ℕ),
        (apertureIndependentThreshold : EReal) ≤ windowThreshold (A + Real.log p)) ∧
      (∃ K₁ : ℝ, 0 < K₁ ∧ 2 * K₁ ≤ 1 ∧
        ∀ᶠ N : ℕ in atTop,
          (completeWeilMatrix tiltedUnitSpline
            (2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ)) N).PosDef) := by
  have hR₀_pos : 0 < apertureIndependentThreshold := by
    unfold apertureIndependentThreshold
    have := tiltedJordanOne_pos
    have := splineAtom_pos
    have := exponentialWeilFloor_pos (by norm_num : (1 : ℝ) < 8)
    positivity
  obtain ⟨K₁, hK₁_pos, h2K₁, hev⟩ :=
    exists_completeWeilMatrix_tiltedUnitSpline_eventually_posDef_at_critical_multiple
  exact ⟨hR₀_pos, fun A p => apertureIndependentThreshold_le_windowThreshold (A + Real.log p),
    K₁, hK₁_pos, h2K₁, hev.mono fun _ h => h.2⟩

/-- **Global equivalence of `R₁(A) = ⊤` stage transport across prime entries.**
For any fixed prime `p`, propagating `windowThreshold A = ⊤ → windowThreshold (A + log p) = ⊤`
across all `A ≥ 0` is unconditionally equivalent to propagation across every prime `q`, to
`∀ A ≥ 0, windowThreshold A = ⊤`, and to `RiemannHypothesis`. -/
theorem stageTransport_across_prime_iff_riemannHypothesis {p : ℕ} (hp : p.Prime) :
    ((∀ A : ℝ, 0 ≤ A → windowThreshold A = ⊤ → windowThreshold (A + Real.log p) = ⊤) ↔
      (∀ q : ℕ, q.Prime → ∀ A : ℝ, 0 ≤ A →
        windowThreshold A = ⊤ → windowThreshold (A + Real.log q) = ⊤)) ∧
    ((∀ A : ℝ, 0 ≤ A → windowThreshold A = ⊤ → windowThreshold (A + Real.log p) = ⊤) ↔
      (∀ A : ℝ, 0 ≤ A → windowThreshold A = ⊤)) ∧
    ((∀ A : ℝ, 0 ≤ A → windowThreshold A = ⊤ → windowThreshold (A + Real.log p) = ⊤) ↔
      RiemannHypothesis) := by
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hstep_to_all :
      (∀ A : ℝ, 0 ≤ A → windowThreshold A = ⊤ → windowThreshold (A + Real.log p) = ⊤) →
        ∀ A : ℝ, 0 ≤ A → windowThreshold A = ⊤ := by
    intro hstep
    have hnat : ∀ n : ℕ, windowThreshold ((n : ℝ) * Real.log p) = ⊤ := by
      intro n
      induction n with
      | zero =>
          simpa using windowThreshold_eq_top_of_le (A := 0) (by norm_num)
      | succ k ih =>
          have hk_nn : 0 ≤ (k : ℝ) * Real.log p := mul_nonneg (Nat.cast_nonneg k) hlogp.le
          have hnext := hstep ((k : ℝ) * Real.log p) hk_nn ih
          simpa [Nat.cast_succ, add_mul, one_mul] using hnext
    intro A hA
    obtain ⟨n, hn⟩ := exists_nat_gt (A / Real.log p)
    have hle : A ≤ (n : ℝ) * Real.log p := ((div_lt_iff₀ hlogp).mp hn).le
    exact top_unique (hnat n ▸ windowThreshold_antitone hle)
  have hall_to_multi :
      (∀ A : ℝ, 0 ≤ A → windowThreshold A = ⊤) →
        ∀ q : ℕ, q.Prime → ∀ A : ℝ, 0 ≤ A →
          windowThreshold A = ⊤ → windowThreshold (A + Real.log q) = ⊤ := by
    intro hall q hq A hA _
    exact hall (A + Real.log q) (add_nonneg hA (Real.log_nonneg (by exact_mod_cast hq.one_lt.le)))
  have h12 :
      (∀ A : ℝ, 0 ≤ A → windowThreshold A = ⊤ → windowThreshold (A + Real.log p) = ⊤) ↔
        (∀ A : ℝ, 0 ≤ A → windowThreshold A = ⊤) :=
    ⟨hstep_to_all, fun hall A hA _ => hall (A + Real.log p) (add_nonneg hA hlogp.le)⟩
  refine ⟨⟨fun h => hall_to_multi (hstep_to_all h), fun hm => hm p hp⟩,
    h12, h12.trans riemannHypothesis_iff_windowThreshold_eq_top.symm⟩

#print axioms windowThreshold_eq_top_iff_stage_fold_payment
#print axioms composite_stage_windowThreshold_eq_top_iff
#print axioms stageTransport_windowThreshold_eq_top_of_endCoercive
#print axioms unconditional_superLogTwo_primeTwo_transport
#print axioms firstFold_stageLoan_obstruction_on_positive_window
#print axioms conductorGrading_obstruction_to_enteringConductor_payment
#print axioms exists_uniform_criticalMultiple_across_all_primeEntries
#print axioms stageTransport_across_prime_iff_riemannHypothesis

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

end
