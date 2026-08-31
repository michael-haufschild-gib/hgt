import GaloisForLFunctions.RHTower.SoninCofinalReporterClockCommutatorSeam
import GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryContraction
import GaloisForLFunctions.RHTower.PrimeGammaCofinalBocksteinDiagonalCompact
import GaloisForLFunctions.RHTower.RouteRCofinalSieveHarmonicResidue

/-!
# Uniform moving diagonal clocks on the cofinal Sonin source

The existing Sonin source pullbacks converge strongly to the identity and therefore commute
asymptotically with each fixed bounded arithmetic clock.  This file proves the stronger moving-clock
law needed by critical and first-wall schedules: on one fixed `ell²` source, the commutator tends to
zero for an arbitrary sequence of coordinatewise contractions.

The point is not abstract strong convergence, which is insufficient for moving bounded operators.
Coordinatewise source structure makes the claim true.  A finite coordinate head is controlled
uniformly because only finitely many basis errors occur, while both orders contract the common
`ell²` tail.  The result applies both to arbitrary moving Möbius complex clocks and to the literal
moving Route-R Gamma-Bockstein diagonal.
-/

open Complex Filter Topology
open scoped ENNReal InnerProductSpace

noncomputable section

namespace RHTower

open ContinuousLinearMap InnerProductSpace

/-- **Moving diagonal-clock uniformity.**  The cofinal positive Sonin pullback asymptotically
commutes, on every fixed source vector, with every moving coordinatewise `ell²` contraction.
No convergence of the multipliers is assumed. -/
theorem tendsto_norm_soninCofinalPositiveSourcePullback_commutator_lpCoordinatewiseContraction
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (m : ℕ → ℕ → ℂ) (hm : ∀ N i, ‖m N i‖ ≤ 1)
    (x : MobiusClockSourceL2) :
    Tendsto (fun N =>
      ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N
          (lpCoordinatewiseContraction (m N) (hm N) x) -
        lpCoordinatewiseContraction (m N) (hm N)
          (soninCofinalPositiveSourcePullback a c d r hc hcd hr N x)‖)
      atTop (nhds 0) := by
  let P : ℕ → MobiusClockSourceL2 →L[ℂ] MobiusClockSourceL2 := fun N =>
    soninCofinalPositiveSourcePullback a c d r hc hcd hr N
  let D : ℕ → MobiusClockSourceL2 →L[ℂ] MobiusClockSourceL2 := fun N =>
    lpCoordinatewiseContraction (m N) (hm N)
  let e : ℕ → MobiusClockSourceL2 := fun i => lp.single 2 i 1
  have hP (z : MobiusClockSourceL2) :
      Tendsto (fun N => ‖P N z - z‖) atTop (nhds 0) := by
    exact tendsto_norm_soninCofinalPositiveSourcePullback_sub
      a c d r ha hc hcd hda hr harc z
  have hPcontract (N : ℕ) (z : MobiusClockSourceL2) : ‖P N z‖ ≤ ‖z‖ := by
    exact norm_soninCofinalPositiveSourcePullback_apply_le
      a c d r hc hcd hr N z
  have hDcontract (N : ℕ) (z : MobiusClockSourceL2) : ‖D N z‖ ≤ ‖z‖ := by
    exact norm_lpCoordinatewiseContraction_apply_le (m N) (hm N) z
  have hpartial :
      Tendsto (fun k => ∑ i ∈ Finset.range k, lp.single 2 i (x i))
        atTop (nhds x) :=
    (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) x).tendsto_sum_nat
  rw [Metric.tendsto_atTop]
  intro ε hε
  have htailEvent : ∀ᶠ k in atTop,
      ‖x - ∑ i ∈ Finset.range k, lp.single 2 i (x i)‖ < ε / 8 := by
    have hball := hpartial.eventually
      (Metric.ball_mem_nhds x (by positivity : 0 < ε / 8))
    filter_upwards [hball] with k hk
    simpa [dist_eq_norm, norm_sub_rev] using hk
  obtain ⟨k, hk⟩ := eventually_atTop.1 htailEvent
  let y : MobiusClockSourceL2 :=
    ∑ i ∈ Finset.range k, lp.single 2 i (x i)
  have hxy : ‖x - y‖ < ε / 8 := hk k le_rfl
  have hsingle (N i : ℕ) :
      D N (lp.single 2 i (x i)) =
        (m N i * x i) • e i := by
    apply lp.ext
    funext j
    by_cases hij : i = j
    · subst j
      simp [D, e, lpCoordinatewiseContraction_apply]
    · simp [D, e, lpCoordinatewiseContraction_apply, lp.single_apply, hij]
  have hDy (N : ℕ) :
      D N y = ∑ i ∈ Finset.range k, (m N i * x i) • e i := by
    change D N (∑ i ∈ Finset.range k, lp.single 2 i (x i)) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hsingle N i
  have hheadPullback :
      Tendsto (fun N => ‖P N (D N y) - D N y‖) atTop (nhds 0) := by
    let U : ℕ → ℝ := fun N =>
      ∑ i ∈ Finset.range k, ‖x i‖ * ‖P N (e i) - e i‖
    have hU : Tendsto U atTop (nhds 0) := by
      have hsum := tendsto_finsetSum (Finset.range k)
        (f := fun i N => ‖x i‖ * ‖P N (e i) - e i‖)
        (a := fun _ => 0)
        (fun i _ => by simpa using (hP (e i)).const_mul ‖x i‖)
      simpa [U] using hsum
    apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_) hU
    rw [hDy, map_sum, ← Finset.sum_sub_distrib]
    calc
      ‖∑ i ∈ Finset.range k,
          (P N ((m N i * x i) • e i) - (m N i * x i) • e i)‖ ≤
          ∑ i ∈ Finset.range k,
            ‖P N ((m N i * x i) • e i) - (m N i * x i) • e i‖ :=
        norm_sum_le _ _
      _ = ∑ i ∈ Finset.range k,
          ‖m N i * x i‖ * ‖P N (e i) - e i‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, ← smul_sub, norm_smul]
      _ ≤ U N := by
        apply Finset.sum_le_sum
        intro i hi
        gcongr
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg (x i)) (hm N i)
  have hheadClock :
      Tendsto (fun N => ‖D N y - D N (P N y)‖) atTop (nhds 0) := by
    have hclock : Tendsto (fun N => ‖D N (y - P N y)‖) atTop (nhds 0) := by
      apply squeeze_zero (fun N => norm_nonneg _) (fun N => hDcontract N _) ?_
      simpa [norm_sub_rev] using hP y
    simpa only [map_sub] using hclock
  have hhead : Tendsto (fun N => ‖P N (D N y) - D N (P N y)‖)
      atTop (nhds 0) := by
    apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
      (by simpa using hheadPullback.add hheadClock)
    calc
      ‖P N (D N y) - D N (P N y)‖ =
          ‖(P N (D N y) - D N y) +
            (D N y - D N (P N y))‖ := by
        congr 1
        abel
      _ ≤ ‖P N (D N y) - D N y‖ +
          ‖D N y - D N (P N y)‖ := norm_add_le _ _
  have hheadEvent : ∀ᶠ N in atTop,
      ‖P N (D N y) - D N (P N y)‖ < ε / 2 := by
    have hball := hhead.eventually
      (Metric.ball_mem_nhds 0 (half_pos hε))
    filter_upwards [hball] with N hN
    simpa [dist_eq_norm] using hN
  apply eventually_atTop.1
  filter_upwards [hheadEvent] with N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  have htail :
      ‖P N (D N (x - y)) - D N (P N (x - y))‖ < ε / 2 := by
    calc
      ‖P N (D N (x - y)) - D N (P N (x - y))‖ ≤
          ‖P N (D N (x - y))‖ + ‖D N (P N (x - y))‖ := norm_sub_le _ _
      _ ≤ ‖D N (x - y)‖ + ‖P N (x - y)‖ :=
        add_le_add (hPcontract N _) (hDcontract N _)
      _ ≤ ‖x - y‖ + ‖x - y‖ :=
        add_le_add (hDcontract N _) (hPcontract N _)
      _ < ε / 2 := by linarith
  have hsplit :
      P N (D N x) - D N (P N x) =
        (P N (D N y) - D N (P N y)) +
          (P N (D N (x - y)) - D N (P N (x - y))) := by
    rw [show D N x = D N y + D N (x - y) by
      rw [map_sub]
      module]
    rw [show P N x = P N y + P N (x - y) by
      rw [map_sub]
      module]
    rw [map_add, map_add]
    module
  change ‖P N (D N x) - D N (P N x)‖ < ε
  rw [hsplit]
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)

/-- Every moving bounded Möbius complex clock asymptotically commutes with the cofinal Sonin
pullback on a fixed source.  Both safe half-plane parameters may vary arbitrarily with depth. -/
theorem tendsto_norm_soninCofinalComplexClockCommutator_apply_moving
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (sigma : ℕ → ℝ) (u : ℕ → ℂ)
    (hsigma : ∀ N, 1 < sigma N) (hu : ∀ N, 0 ≤ (u N).re)
    (x : MobiusClockSourceL2) :
    Tendsto (fun N =>
      ‖soninCofinalComplexClockCommutator
        a c d r hc hcd hr N (sigma N) (u N)
          (hsigma N) (hu N) x‖) atTop (nhds 0) := by
  let m : ℕ → ℕ → ℂ := fun N i =>
    mobiusCriticalComplexClockFactor (sigma N) (u N) i
  have hm : ∀ N i, ‖m N i‖ ≤ 1 := fun N i =>
    norm_mobiusCriticalComplexClockFactor_le_one (hsigma N) (hu N) i
  have hclock (N : ℕ) :
      lpCoordinatewiseContraction (m N) (hm N) =
        mobiusCriticalComplexClockDamping
          (sigma N) (u N) (hsigma N) (hu N) := by
    apply ContinuousLinearMap.ext
    intro z
    apply lp.ext
    funext i
    rfl
  have h :=
    tendsto_norm_soninCofinalPositiveSourcePullback_commutator_lpCoordinatewiseContraction
      a c d r ha hc hcd hda hr harc m hm x
  simpa only [hclock, soninCofinalComplexClockCommutator,
    ContinuousLinearMap.comp_apply, sub_apply] using h

/-- **Route-R/Sonin moving-wall splice.**  Even when the horizontal grade varies arbitrarily in
the open critical strip, the literal coefficient-faithful Gamma-Bockstein diagonal asymptotically
commutes with the same cofinal Sonin pullback. -/
theorem tendsto_norm_soninCofinalPrimeGammaBocksteinCommutator_apply_moving
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    (t : ℕ → ℝ) (ht : ∀ N, |t N| < 1)
    (x : MobiusClockSourceL2) :
    Tendsto (fun N =>
      ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N
          (primeGammaCofinalBocksteinDiagonalOperator (t N) (ht N) x) -
        primeGammaCofinalBocksteinDiagonalOperator (t N) (ht N)
          (soninCofinalPositiveSourcePullback a c d r hc hcd hr N x)‖)
      atTop (nhds 0) := by
  let m : ℕ → ℕ → ℂ := fun N i =>
    primeGammaCofinalBocksteinDiagonalMultiplier (t N) i
  have hm : ∀ N i, ‖m N i‖ ≤ 1 := fun N i =>
    norm_primeGammaCofinalBocksteinDiagonalMultiplier_le_one (ht N) i
  have hclock (N : ℕ) :
      lpCoordinatewiseContraction (m N) (hm N) =
        primeGammaCofinalBocksteinDiagonalOperator (t N) (ht N) := by
    apply ContinuousLinearMap.ext
    intro z
    apply lp.ext
    funext i
    rfl
  have h :=
    tendsto_norm_soninCofinalPositiveSourcePullback_commutator_lpCoordinatewiseContraction
      a c d r ha hc hcd hda hr harc m hm x
  simpa only [hclock] using h

/-- Moving diagonal commutation does not erase Route R's positive-grade harmonic residue: on the
same literal Gamma-Bockstein coefficients, the Sonin commutator tends to zero while the restarted
Euler reporter retains residue `-1`. -/
theorem soninCofinalPrimeGammaBocksteinCommutator_zero_but_reporter_neg_one_of_pos
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    {t : ℝ} (ht : 0 < t) (htStrip : |t| < 1)
    (x : MobiusClockSourceL2) :
    Tendsto (fun N =>
      ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N
          (primeGammaCofinalBocksteinDiagonalOperator t htStrip x) -
        primeGammaCofinalBocksteinDiagonalOperator t htStrip
          (soninCofinalPositiveSourcePullback a c d r hc hcd hr N x)‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun N => routeRCofinalSieveHarmonicReporter nthPrimeEquiv N
          (routeRPrimeGammaCriticalWallField t))
        atTop (nhds (-1)) := by
  constructor
  · simpa using
      (tendsto_norm_soninCofinalPrimeGammaBocksteinCommutator_apply_moving
        a c d r ha hc hcd hda hr harc (fun _ => t) (fun _ => htStrip) x)
  · exact tendsto_routeRPrimeGammaCriticalWallReporter_neg_one_of_pos
      nthPrimeEquiv ht

/-- Negative grades give the opposite quantized separation: the same moving diagonal commutator
vanishes while the coefficient-faithful restarted reporter retains residue `+1`. -/
theorem soninCofinalPrimeGammaBocksteinCommutator_zero_but_reporter_one_of_neg
    (a c d r : ℝ) (ha : 0 < a) (hc : 0 < c) (hcd : c < d)
    (hda : d < a) (hr : 1 < r) (harc : a < r * c)
    {t : ℝ} (ht : t < 0) (htStrip : |t| < 1)
    (x : MobiusClockSourceL2) :
    Tendsto (fun N =>
      ‖soninCofinalPositiveSourcePullback a c d r hc hcd hr N
          (primeGammaCofinalBocksteinDiagonalOperator t htStrip x) -
        primeGammaCofinalBocksteinDiagonalOperator t htStrip
          (soninCofinalPositiveSourcePullback a c d r hc hcd hr N x)‖)
        atTop (nhds 0) ∧
      Tendsto
        (fun N => routeRCofinalSieveHarmonicReporter nthPrimeEquiv N
          (routeRPrimeGammaCriticalWallField t))
        atTop (nhds 1) := by
  constructor
  · simpa using
      (tendsto_norm_soninCofinalPrimeGammaBocksteinCommutator_apply_moving
        a c d r ha hc hcd hda hr harc (fun _ => t) (fun _ => htStrip) x)
  · exact tendsto_routeRPrimeGammaCriticalWallReporter_one_of_neg
      nthPrimeEquiv ht

end RHTower
