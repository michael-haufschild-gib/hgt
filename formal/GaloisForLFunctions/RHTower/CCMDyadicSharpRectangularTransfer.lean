import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowDirichlet
import GaloisForLFunctions.RHTower.CCMSharpRectangularSewing
import GaloisForLFunctions.RHTower.CCMSharpPrimeWindowSubpowerGate
import GaloisForLFunctions.RHTower.XiHurwitzPrincipalPhaseGrowth

/-!
# Dyadic sharp-to-rectangular value transfer

The continuous dyadic sharp window at logarithmic height `x` is exactly the integer window at
`floor (exp x)`: natural floor commutes with division by two.  Hence an eventual upper bound for
the integer von-Mangoldt windows extends without a rounding loss to a continuous lower bound for
the sharp prime--polar coefficient.  The sharp-to-rectangular sewing law then transfers that
pointwise bound to the completed critical-Mellin adjacent block.

This supplies an exact value-level comparison between the new sharp RH gate and the older
rectangular source target.  It does not assume a Guinand--Weil identity for the rectangular
piecewise-linear autocorrelation.
-/

open Finset Set MeasureTheory ArithmeticFunction

noncomputable section

namespace RHTower

private theorem dyadicTransfer_integrableOn_criticalMellinCompletedError_Ioc
    {a b : ℝ} :
    IntegrableOn criticalMellinCompletedError (Ioc a b) := by
  rw [show criticalMellinCompletedError = fun h : ℝ =>
      4 * Real.sinh (h / 2) - criticalMellinPrimeMass h by
    funext h
    exact criticalMellinCompletedError_eq_polar_sub_primeMass h]
  apply IntegrableOn.sub
  · exact (continuous_const.mul
      (Real.continuous_sinh.comp
        (continuous_id.div_const 2))).continuousOn.integrableOn_Icc.mono_set
          (fun h hh => ⟨hh.1.le, hh.2⟩)
  · exact integrableOn_criticalMellinPrimeMass_Ioc

private theorem dyadicTransfer_integrableOn_comp_sub_Ioc
    (f : ℝ → ℝ) (a b L : ℝ)
    (hf : IntegrableOn f (Ioc (a - L) (b - L))) :
    IntegrableOn (fun h => f (h - L)) (Ioc a b) := by
  have hmp := measurePreserving_add_right (volume : Measure ℝ) (-L)
  have hi := (hmp.integrableOn_comp_preimage
    (measurableEmbedding_addRight (-L))
    (f := f) (s := Ioc (a - L) (b - L))).mpr hf
  have hpre : (fun h : ℝ => h + -L) ⁻¹' Ioc (a - L) (b - L) = Ioc a b := by
    ext h
    simp only [Set.mem_preimage, Set.mem_Ioc]
    constructor <;> intro hh <;> constructor <;> linarith [hh.1, hh.2]
  rw [hpre] at hi
  simpa only [Function.comp_apply, sub_eq_add_neg] using hi

private theorem dyadicTransfer_integrableOn_sharpPlusEndpoint_Ioc
    (L a b : ℝ) :
    IntegrableOn
      (fun h => sharpPrimePolarCoefficient L h +
        sharpPrimeWindowEndpointCorrection L h) (Ioc a b) := by
  have hpoint : (fun h : ℝ =>
      sharpPrimePolarCoefficient L h +
        sharpPrimeWindowEndpointCorrection L h) =
      fun h : ℝ => 2 *
        (criticalMellinCompletedError h -
          criticalMellinCompletedError (h - L)) := by
    funext h
    rw [sharpPrimePolarCoefficient_eq_completedErrorIncrement]
    ring
  rw [hpoint]
  have hdiff : IntegrableOn
      (fun h : ℝ => criticalMellinCompletedError h -
        criticalMellinCompletedError (h - L)) (Ioc a b) := by
    apply IntegrableOn.sub
    · exact dyadicTransfer_integrableOn_criticalMellinCompletedError_Ioc
    · apply dyadicTransfer_integrableOn_comp_sub_Ioc
      exact dyadicTransfer_integrableOn_criticalMellinCompletedError_Ioc
  exact hdiff.const_mul 2

/-- The continuous dyadic moving window has no floor error: it is literally the integer window at
`floor (exp x)`. -/
theorem sharpMovingPrimeWindowMass_logTwo_eq_dyadicWeightedPrimeWindow_floorExp (x : ℝ) :
    sharpMovingPrimeWindowMass (Real.log 2) x =
      dyadicWeightedPrimeWindow ⌊Real.exp x⌋₊ := by
  rw [sharpMovingPrimeWindowMass_eq_sum_Ioc
    (Real.log_nonneg (by norm_num)),
    dyadicWeightedPrimeWindow_eq_floorSum]
  have hsub : Real.exp (x - Real.log 2) = Real.exp x / 2 := by
    rw [Real.exp_sub, Real.exp_log (by norm_num)]
  rw [hsub, Nat.floor_div_ofNat, Nat.floor_div_ofNat]
  simp

/-- Exact continuous dyadic sharp coefficient through the integer weighted-prime window. -/
theorem sharpPrimePolarCoefficient_logTwo_eq_floorExp (x : ℝ) :
    sharpPrimePolarCoefficient (Real.log 2) x =
      4 * (1 - (Real.sqrt 2)⁻¹) * Real.exp (x / 2) -
        2 * dyadicWeightedPrimeWindow ⌊Real.exp x⌋₊ := by
  rw [sharpPrimePolarCoefficient,
    sharpMovingPrimeWindowMass_logTwo_eq_dyadicWeightedPrimeWindow_floorExp]
  have hhalf : Real.exp (Real.log 2 / 2) = Real.sqrt 2 := by
    rw [← Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.exp_log (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))]
  have hshift : Real.exp ((x - Real.log 2) / 2) =
      Real.exp (x / 2) * (Real.sqrt 2)⁻¹ := by
    rw [show (x - Real.log 2) / 2 = x / 2 - Real.log 2 / 2 by ring,
      Real.exp_sub, hhalf]
    ring
  rw [hshift]
  ring

/-- An integer dyadic-window upper bound extends to every logarithmic height, with the same power
exponent and only the algebraically forced factor two in the sharp source coefficient. -/
theorem continuous_sharpPrimePolarCoefficient_lower_of_dyadicWeightedPrimeWindow_upper
    {N : ℕ} {C epsilon : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (hwindow : ∀ n : ℕ, N ≤ n →
      dyadicWeightedPrimeWindow n ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
          C * (n : ℝ) ^ epsilon)
    {x : ℝ} (hxN : N ≤ ⌊Real.exp x⌋₊) :
    0 ≤ sharpPrimePolarCoefficient (Real.log 2) x +
      2 * C * Real.exp (epsilon * x) := by
  let n : ℕ := ⌊Real.exp x⌋₊
  have hwin := hwindow n (by simpa only [n] using hxN)
  have hnle : (n : ℝ) ≤ Real.exp x := by
    dsimp only [n]
    exact Nat.floor_le (Real.exp_pos x).le
  have hsqrt : Real.sqrt n ≤ Real.exp (x / 2) := by
    rw [Real.exp_half]
    exact Real.sqrt_le_sqrt hnle
  have hsqrtTwo : 1 ≤ Real.sqrt 2 := by
    exact (Real.one_le_sqrt (x := 2)).2 (by norm_num)
  have hfactor : 0 ≤ 1 - (Real.sqrt 2)⁻¹ := by
    rw [sub_nonneg]
    exact (inv_le_one₀ (Real.sqrt_pos.mpr (by norm_num))).2 hsqrtTwo
  have hmain :
      2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.exp (x / 2) := by
    gcongr
  have hpow0 : (n : ℝ) ^ epsilon ≤ (Real.exp x) ^ epsilon :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) hnle hepsilon
  have hpow : C * (n : ℝ) ^ epsilon ≤ C * Real.exp (epsilon * x) := by
    calc
      C * (n : ℝ) ^ epsilon ≤ C * (Real.exp x) ^ epsilon :=
        mul_le_mul_of_nonneg_left hpow0 hC
      _ = C * Real.exp (epsilon * x) := by
        rw [← Real.exp_mul]
        congr 2
        ring
  rw [sharpPrimePolarCoefficient_logTwo_eq_floorExp]
  change 0 ≤
    4 * (1 - (Real.sqrt 2)⁻¹) * Real.exp (x / 2) -
      2 * dyadicWeightedPrimeWindow n +
        2 * C * Real.exp (epsilon * x)
  linarith

/-- Sewing one continuous dyadic sharp lower bound over an aperture gives the corresponding
one-sided lower bound for the completed critical-Mellin adjacent block. -/
theorem criticalMellinAdjacentBlock_lower_of_dyadicWeightedPrimeWindow_upper
    {N : ℕ} {C epsilon : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (hwindow : ∀ n : ℕ, N ≤ n →
      dyadicWeightedPrimeWindow n ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
          C * (n : ℝ) ^ epsilon)
    {x : ℝ} (hxN : N ≤ ⌊Real.exp (x - Real.log 2)⌋₊) :
    0 ≤ criticalMellinAdjacentBlock (Real.log 2) x +
      C * Real.log 2 * Real.exp (epsilon * x) := by
  let f : ℝ → ℝ := fun h =>
    sharpPrimePolarCoefficient (Real.log 2) h +
      sharpPrimeWindowEndpointCorrection (Real.log 2) h
  let c : ℝ := -2 * C * Real.exp (epsilon * x)
  have hcInt : IntegrableOn (fun _ : ℝ => c)
      (Ioc (x - Real.log 2) x) :=
    integrableOn_const (ne_of_lt measure_Ioc_lt_top)
  have hfInt : IntegrableOn f (Ioc (x - Real.log 2) x) := by
    exact dyadicTransfer_integrableOn_sharpPlusEndpoint_Ioc
      (Real.log 2) (x - Real.log 2) x
  have hpoint : ∀ᵐ h ∂volume.restrict (Ioc (x - Real.log 2) x),
      (fun _ : ℝ => c) h ≤ f h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with h hh
    have hfloor : N ≤ ⌊Real.exp h⌋₊ := by
      exact hxN.trans (Nat.floor_mono (Real.exp_le_exp.mpr hh.1.le))
    have hsharp := continuous_sharpPrimePolarCoefficient_lower_of_dyadicWeightedPrimeWindow_upper
      hC hepsilon hwindow hfloor
    have hendpoint := sharpPrimeWindowEndpointCorrection_nonneg
      (L := Real.log 2) (x := h)
      (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
    have hexp : Real.exp (epsilon * h) ≤ Real.exp (epsilon * x) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hh.2 hepsilon
    have hscaled := mul_le_mul_of_nonneg_left hexp
      (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hC)
    dsimp only [c, f]
    nlinarith
  have hmono := MeasureTheory.integral_mono_ae hcInt hfInt hpoint
  have hsew := sharpPrimePolarIntegral_eq_twice_adjacentBlock
    (Real.log 2) x
  change (∫ h in Ioc (x - Real.log 2) x, c) ≤
      ∫ h in Ioc (x - Real.log 2) x, f h at hmono
  rw [hsew] at hmono
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hconst : (∫ _h in Ioc (x - Real.log 2) x, c) =
      Real.log 2 * c := by
    simp only [MeasureTheory.integral_const]
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc]
    · rw [ENNReal.toReal_ofReal]
      · simp only [smul_eq_mul]
        congr 1
        ring
      · linarith
  rw [hconst] at hmono
  dsimp only [c] at hmono
  nlinarith

/-- Integer-logarithmic specialization of the sharp-to-adjacent-block transfer. -/
theorem criticalMellinAdjacentBlock_logSample_lower_of_dyadicWeightedPrimeWindow_upper
    {N : ℕ} {C epsilon : ℝ} (hC : 0 ≤ C) (hepsilon : 0 ≤ epsilon)
    (hwindow : ∀ m : ℕ, N ≤ m →
      dyadicWeightedPrimeWindow m ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt m +
          C * (m : ℝ) ^ epsilon)
    {n : ℕ} (hn : 0 < n) (hN : 2 * N ≤ n) :
    0 ≤ criticalMellinAdjacentBlock (Real.log 2) (Real.log n) +
      C * Real.log 2 * (n : ℝ) ^ epsilon := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hfloor : ⌊Real.exp (Real.log n - Real.log 2)⌋₊ = n / 2 := by
    rw [Real.exp_sub, Real.exp_log hnreal, Real.exp_log (by norm_num),
      Nat.floor_div_ofNat, Nat.floor_natCast]
  have hxN : N ≤ ⌊Real.exp (Real.log n - Real.log 2)⌋₊ := by
    rw [hfloor]
    omega
  have h := criticalMellinAdjacentBlock_lower_of_dyadicWeightedPrimeWindow_upper
    hC hepsilon hwindow hxN
  convert h using 1
  rw [Real.rpow_def_of_pos hnreal]
  congr 3
  ring

/-- The all-epsilon dyadic prime-window inequality discharges the all-epsilon adjacent-block
source estimate, with the explicit constant conversion `D_epsilon = C_epsilon * log 2`. -/
theorem criticalMellinAdjacentBlock_subpowerLower_of_dyadicWeightedPrimeWindow_subpowerUpper
    {N : ℕ}
    (hwindow : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        dyadicWeightedPrimeWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            C * (n : ℝ) ^ epsilon) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℕ, max 1 (2 * N) ≤ n →
        0 ≤ criticalMellinAdjacentBlock (Real.log 2) (Real.log n) +
          D * (n : ℝ) ^ epsilon := by
  intro epsilon hepsilon
  obtain ⟨C, hC, htail⟩ := hwindow epsilon hepsilon
  let D : ℝ := C * Real.log 2
  have hD : 0 ≤ D := mul_nonneg hC (Real.log_nonneg (by norm_num))
  refine ⟨D, hD, fun n hn => ?_⟩
  have hnpos : 0 < n := by omega
  have hnN : 2 * N ≤ n := (Nat.le_max_right 1 (2 * N)).trans hn
  have h := criticalMellinAdjacentBlock_logSample_lower_of_dyadicWeightedPrimeWindow_upper
    hC hepsilon.le htail hnpos hnN
  simpa only [D, mul_assoc] using h

/-- Direct, unbundled theorem surface for the rectangular lower-tail law.  For every positive
width, RH is equivalent to an eventual all-epsilon lower bound written with the literal real power
`n ^ epsilon`; no named proposition interface remains in the statement. -/
theorem riemannHypothesis_iff_exists_eventually_xiRectangularWeilLogCoefficient_subpowerLower
    {L : ℝ} (hL : 0 < L) :
    RiemannHypothesis ↔
      ∃ N : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
          0 ≤ (xiRectangularWeilLogCoefficient L n).re +
            C * (n : ℝ) ^ epsilon := by
  rw [riemannHypothesis_iff_exists_rectangularWeilTailSubpowerLower hL]
  constructor
  · rintro ⟨N, hlower⟩
    refine ⟨N, fun epsilon hepsilon => ?_⟩
    obtain ⟨C, hC, htail⟩ := hlower epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    have h := htail n hn
    rcases n.eq_zero_or_pos with rfl | hnpos
    · simpa [powerCorrectionCoefficient, Real.zero_rpow hepsilon.ne'] using h
    · simpa [powerCorrectionCoefficient, Nat.ne_of_gt hnpos] using h
  · rintro ⟨N, hlower⟩
    refine ⟨N, fun epsilon hepsilon => ?_⟩
    obtain ⟨C, hC, htail⟩ := hlower epsilon hepsilon
    refine ⟨C, hC, fun n hn => ?_⟩
    have h := htail n hn
    rcases n.eq_zero_or_pos with rfl | hnpos
    · simpa [powerCorrectionCoefficient, Real.zero_rpow hepsilon.ne'] using h
    · simpa [powerCorrectionCoefficient, Nat.ne_of_gt hnpos] using h

/-- Independently of the still-open rectangular source identity, the dyadic sharp inequality
already implies RH and therefore supplies the abstract rectangular Weil lower tail at every
positive width. -/
theorem exists_rectangularWeilTailSubpowerLower_of_dyadicWeightedPrimeWindow_subpowerUpper
    {N : ℕ} {L : ℝ} (hL : 0 < L)
    (hwindow : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        dyadicWeightedPrimeWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            C * (n : ℝ) ^ epsilon) :
    ∃ M : ℕ, XiRectangularWeilTailSubpowerLower L M := by
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_upper hwindow
  exact (riemannHypothesis_iff_exists_rectangularWeilTailSubpowerLower hL).mp hRH

/-- Direct theorem surface: the dyadic prime-window inequality supplies the literal rectangular
`Q(L,n) ≥ -C_epsilon n^epsilon` tail at every positive width. -/
theorem exists_eventually_xiRectangularWeilLogCoefficient_subpowerLower_of_dyadicWeightedPrimeWindow
    {N : ℕ} {L : ℝ} (hL : 0 < L)
    (hwindow : ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, N ≤ n →
        dyadicWeightedPrimeWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            C * (n : ℝ) ^ epsilon) :
    ∃ M : ℕ, ∀ epsilon : ℝ, 0 < epsilon →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, M ≤ n →
        0 ≤ (xiRectangularWeilLogCoefficient L n).re +
          C * (n : ℝ) ^ epsilon := by
  have hRH : RiemannHypothesis :=
    riemannHypothesis_of_eventually_dyadicWeightedPrimeWindow_upper hwindow
  exact
    (riemannHypothesis_iff_exists_eventually_xiRectangularWeilLogCoefficient_subpowerLower
      hL).mp hRH

end RHTower
