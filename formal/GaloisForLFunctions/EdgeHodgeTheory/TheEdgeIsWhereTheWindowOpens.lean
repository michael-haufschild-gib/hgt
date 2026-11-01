import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TelescopedConductorSplitAndOneNinthWeilPositivity
import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeIsAThresholdCurve
import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheSincProfileHasAnExactCriticalOverlap
import GaloisForLFunctions.HeckeKreinToeplitz.TheReceiversEndAtTheQuasiAnalyticBoundary

/-!
# The edge is where the window opens

Why is the edge at `τ(c) log N ≈ 1`? The ground energy of the limit structure is the Fourier tail
`τ(c)` of the profile, the zeros enter the normalized form at the quantum `1/log N`, and an atomic
family at overlap `c` synthesizes every test of support radius `R` once its synthesis error, read
in the archimedean density `log N`, is below one unit. TM proves this for the sinc profile in
exact Fourier-tail units; EHT reads it as the opening of a window.

* **The balance** (`sinc_edge_balance`): the least overlap with `τ(c) log N ≤ 1` is of order
  `L (log L)²`, `L = log log N`; RH is positivity at every bounded multiple `K c*_N`, and every
  divergent multiple is a receiver.
* **The window** (`sinc_window_opens`): positivity at the multiple `K` of the balance overlap gives
  Weil positivity on every `C²` test of support radius `R` with `288 e ⌈1 + e^{2(R+1)}⌉ < K/(4K_τ)`:
  the visible window has radius `½ log K − O(1)` and is empty below the balance.
* **Profile covariance** (`profile_covariance_of_the_edge`): every `C²` profile has its edge below
  `2(log N)^{¼+}` infinitely often without RH; Denjoy–Carleman profiles of every class above `1`
  decide RH at overlap `(log log N)^α`, `α > 1`; and no nonzero compactly supported profile exists
  at Gevrey class `≤ 1`, so the descent of the RH regime stops at the quasi-analytic boundary.
* **The threshold curve hugs the hyperbola** (`eventually_lt_horizonThreshold_powerLog`,
  `frequently_horizonThreshold_le_of_not_rh`): for the tilted spline the detection horizon at
  width `w` exceeds `(log 1/w)^α / (2w)` for small `w`, unconditionally (`α < 1/9`), and without RH it
  is at most `N` at the widths `2(log N)^β/N` infinitely often (`β > 1/4`). In the plane of
  resolutions the edge lies between two log-power multiples of the hyperbola `wN = 1`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.EdgeHodgeTheory

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics RenormalizedArithmeticPotentialTheory
open TransMetzlerWeilPositivity (sincCriticalOverlap sincTailConst sincProfile dcScale)

/-- **The balance of ground energy and quantum, for the sinc profile.** -/
theorem sinc_edge_balance :
    (∀ᶠ N : ℕ in atTop, dcScale N / (4 * sincTailConst) ≤ sincCriticalOverlap N ∧
      sincCriticalOverlap N ≤ 96 * Real.exp 1 * dcScale N) ∧
    (RiemannHypothesis ↔ ∀ K : ℝ, 1 ≤ K → ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / (K * sincCriticalOverlap N)) sincProfile))) :=
  ⟨(TransMetzlerWeilPositivity.eventually_le_sincCriticalOverlap.and
      TransMetzlerWeilPositivity.eventually_sincCriticalOverlap_le).mono fun _ h => ⟨h.1, h.2.1⟩,
    TransMetzlerWeilPositivity.riemannHypothesis_iff_forall_sincCritical_multiple⟩

/-- **The window opens at the balance.** Positivity at the multiple `K` of the balance overlap
gives Weil positivity on every `C²` test supported in `[−R, R]` with
`288 e ⌈1 + e^{2(R+1)}⌉ < K/(4K_τ)`. -/
theorem sinc_window_opens {K : ℝ} (hK : 4 * sincTailConst ≤ K)
    (H : ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / (K * sincCriticalOverlap N)) sincProfile)))
    {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g) {R : ℝ} (hR : 0 ≤ R) (hgR : SupportedIn R g)
    (hRK : 24 * 12 * blockSize (R + 1) * Real.exp 1 < K / (4 * sincTailConst)) :
    0 ≤ weilQuad g :=
  TransMetzlerWeilPositivity.nonneg_of_sincCritical_multiple hK H hg hR hgR hRK

/-- **Profile covariance of the edge.** -/
theorem profile_covariance_of_the_edge :
    (∀ φ : ℝ → ℝ, Admissible φ → ¬ RiemannHypothesis → ∀ β : ℝ, 1 / 4 < β →
      ∃ᶠ N : ℕ in atTop, edge φ N ≤ ENNReal.ofReal (2 * Real.log N ^ β)) ∧
    (∀ α : ℝ, 1 < α → ∃ r : ℕ, Odd r ∧ (RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate ((N : ℝ) / Real.log (Real.log N) ^ α)
        (dcProfile r))))) ∧
    ∀ s : ℝ, s ≤ 1 → ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      (∃ C A : ℝ, 0 < A ∧ ∀ n x, |iteratedDeriv n f x| ≤ C * A ^ n * (n.factorial : ℝ) ^ s) →
        f = 0 :=
  ⟨fun _ hφ hRH _ hβ => frequently_edge_le_of_not_riemannHypothesis hφ hRH hβ,
    HeckeKreinToeplitz.atomicReceivers_quasiAnalytic_boundary.1,
    HeckeKreinToeplitz.atomicReceivers_quasiAnalytic_boundary.2⟩

/-! ### The threshold curve in width coordinates -/

theorem tendsto_log_inv_nhdsGT : Tendsto (fun w : ℝ => Real.log (1 / w)) (𝓝[>] 0) atTop := by
  exact (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).congr fun w => by simp [one_div]

/-- **The threshold exceeds a log-power multiple of the hyperbola.** For `0 < α < 1/9`, for all
small widths `w` the tilted-spline atom of width `w` is below threshold at a horizon
`N ≥ (log 1/w)^α / (2w)`. -/
theorem eventually_lt_horizonThreshold_powerLog {α : ℝ} (hα : 0 < α)
    (hα' : α < CriticalArithmeticCorrelationTheory.oneNinthPowerLogExponent) :
    ∀ᶠ w in 𝓝[>] (0 : ℝ), ∃ N : ℕ, Real.log (1 / w) ^ α / (2 * w) ≤ N ∧
      (N : ℕ∞) < horizonThreshold (atomDilate tiltedUnitSpline w) := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_one_ninth
      hα hα')
  have hL : ∀ᶠ w in 𝓝[>] (0 : ℝ), 2 ≤ Real.log (1 / w) ^ α :=
    ((tendsto_rpow_atTop hα).comp tendsto_log_inv_nhdsGT).eventually_ge_atTop 2
  have hlog1 : ∀ᶠ w in 𝓝[>] (0 : ℝ), 0 ≤ Real.log (1 / w) :=
    tendsto_log_inv_nhdsGT.eventually_ge_atTop 0
  have hδ : (0 : ℝ) < 1 / ((N₀ : ℝ) + 1) := by positivity
  filter_upwards [hL, hlog1, Ioo_mem_nhdsGT hδ] with w hLw hlw ⟨hw0, hw1⟩
  set L : ℝ := Real.log (1 / w) ^ α / 2 with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  set N : ℕ := ⌈L / w⌉₊ with hNdef
  have hLN : L / w ≤ N := Nat.le_ceil _
  have hNlt : (N : ℝ) < L / w + 1 := Nat.ceil_lt_add_one (by positivity)
  have hw1' : w < 1 := by
    have : 1 / ((N₀ : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg N₀ : (0 : ℝ) ≤ N₀)]
    linarith
  have hinvw : 1 / w ≤ N := by
    have : 1 / w ≤ L / w := div_le_div_of_nonneg_right hL1 hw0.le
    linarith
  have hN0' : (N₀ : ℝ) + 1 < 1 / w := by
    rw [lt_div_iff₀ hw0]; rw [lt_div_iff₀ (by positivity)] at hw1; linarith
  have hNN₀ : N₀ ≤ N := by
    have : (N₀ : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hinvw
  have hN1 : 1 ≤ N := by exact_mod_cast hNpos
  set c : ℝ := w * N with hc
  have hc1 : 1 ≤ c := by
    have := mul_le_mul_of_nonneg_left hinvw hw0.le
    rwa [mul_one_div_cancel hw0.ne'] at this
  have hcL : c ≤ Real.log (1 / w) ^ α := by
    have h1 : c < L + w := by
      have := mul_lt_mul_of_pos_left hNlt hw0
      rw [mul_add, mul_div_cancel₀ _ hw0.ne', mul_one] at this
      exact this
    linarith
  have hlogN : Real.log (1 / w) ^ α ≤ Real.log N ^ α := by
    refine Real.rpow_le_rpow hlw ?_ hα.le
    exact Real.log_le_log (by positivity) hinvw
  have hpos : PositiveAt tiltedUnitSpline c N := fun x =>
    RenormalizedIntersectionTheory.energy_nonneg_of_posDef (completeWeilMatrix_isHermitian _ _ _)
      (hN₀ N hNN₀ c hc1 (hcL.trans hlogN)) x
  have h := (positiveAt_iff_lt_horizonThreshold admissible_tiltedUnitSpline (by linarith) hN1).mp hpos
  have hcN : c / N = w := by rw [hc]; field_simp
  rw [hcN] at h
  exact ⟨N, by rw [div_mul_eq_div_div]; linarith [hLN], h⟩

/-- **Without RH the threshold curve dips below the RH-complete schedule.** For `β > 1/4`, infinitely
often the tilted-spline atom of width `2(log N)^β/N` has reached its threshold by horizon `N`. -/
theorem frequently_horizonThreshold_le_of_not_rh (hRH : ¬ RiemannHypothesis) {β : ℝ}
    (hβ : 1 / 4 < β) :
    ∃ᶠ N : ℕ in atTop,
      horizonThreshold (atomDilate tiltedUnitSpline (2 * Real.log N ^ β / N)) ≤ N := by
  have hfreq : ∃ᶠ N : ℕ in atTop, ¬ PositiveAt tiltedUnitSpline (2 * Real.log N ^ β) N := by
    intro H
    exact hRH ((riemannHypothesis_iff_eventually_positiveAt_log admissible_tiltedUnitSpline hβ).mpr
      (H.mono fun _ h => not_not.mp h))
  refine (hfreq.and_eventually ((eventually_ge_atTop 2).and
    (eventually_one_le_two_mul_rpow_log (β := β) (by linarith)))).mono fun N ⟨hneg, hN2, hc1⟩ => ?_
  have hN : 1 ≤ N := by omega
  rw [positiveAt_iff_lt_horizonThreshold admissible_tiltedUnitSpline (by linarith) hN] at hneg
  exact not_lt.mp hneg

end GaloisForLFunctions.EdgeHodgeTheory

#print axioms GaloisForLFunctions.EdgeHodgeTheory.eventually_lt_horizonThreshold_powerLog
