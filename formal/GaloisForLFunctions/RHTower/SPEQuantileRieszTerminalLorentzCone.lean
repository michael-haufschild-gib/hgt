import GaloisForLFunctions.RHTower.SPEQuantileRieszTerminalSquareLaw
import GaloisForLFunctions.RHTower.SuzukiBoundaryExcursionJuliaKreinLightLift
import GaloisForLFunctions.RHTower.RoutePJuliaKreinHistoryPort

/-!
# SP-E terminal completed Lorentz cone

At every literal cutoff, the completed zero-boundary coordinate and the signed terminal
error/atom displacement form a strictly timelike pair.  This is an exact source identity:
its two null coordinates respectively recover the retained literal head mass and the physical
square-root threshold.  Thus it supplies a cofinal source Krein coordinate without discarding
the terminal sign.

It does not yet transport the ordered SP-E history current through the Route-P action; that
remaining compatibility is the substantive cofinal-lift problem.
-/

open scoped BigOperators
open Complex Matrix
open Filter

namespace RHTower

noncomputable section

/-- At cutoff `K + 3`, the quantile polar coordinate is its two initial empty cells plus the
literal finite head mass. -/
theorem ccmActualHeadQuantilePolarCoordinate_terminal_eq_two_add_headMass (K : ℕ) :
    ccmActualHeadQuantilePolarCoordinate (K + 3) =
      2 + ccmActualHeadParabolicMass K := by
  have hzero : criticalMellinAtomWeight 0 = 0 := by
    unfold criticalMellinAtomWeight
    have hΛ : (ArithmeticFunction.vonMangoldt 0 : ℝ) = 0 := by
      norm_num [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    rw [hΛ]
    ring
  have hone : criticalMellinAtomWeight 1 = 0 := by
    unfold criticalMellinAtomWeight
    norm_num [ArithmeticFunction.vonMangoldt_apply_one]
  have hsplit : Finset.range (K + 3) =
      insert 0 (insert 1 (Finset.Ico 2 (K + 3))) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]
    omega
  have hshift :
      (∑ n ∈ Finset.range (K + 1), criticalMellinAtomWeight (n + 2)) =
        ∑ n ∈ Finset.Ico 2 (K + 3), criticalMellinAtomWeight n := by
    refine Finset.sum_bij (fun n _ => n + 2) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_range, Finset.mem_Ico] at hn ⊢
      omega
    · intro a ha b hb hab
      omega
    · intro n hn
      simp only [Finset.mem_Ico] at hn
      refine ⟨n - 2, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro n hn
      rfl
  rw [ccmActualHeadQuantilePolarCoordinate_eq_two_add_cumulative]
  unfold ccmOutgoingPrimeCumulative ccmActualHeadParabolicMass
  rw [hsplit, Finset.sum_insert, Finset.sum_insert, hzero, hone, zero_add, hshift]
  · ring
  · simp
  · simp

/-- The signed terminal displacement is the physical threshold less the literal head mass. -/
theorem speQuantileRieszTerminalErrorDisplacement_eq_threshold_sub_headMass (K : ℕ) :
    speQuantileRieszTerminalErrorDisplacement K =
      2 * (Real.sqrt ((K + 3 : ℕ) : ℝ) - 1) - ccmActualHeadParabolicMass K := by
  rw [speQuantileRieszTerminalErrorDisplacement_eq_physicalMismatch,
    ccmActualHeadQuantilePolarCoordinate_terminal_eq_two_add_headMass]
  ring

/-- The completed zero-boundary is the literal head mass plus the physical threshold. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_eq_headMass_add_threshold
    (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0 =
      ccmActualHeadParabolicMass K +
        2 * (Real.sqrt ((K + 3 : ℕ) : ℝ) - 1) := by
  have hclock : Real.log ((K : ℝ) + 3) =
      Real.log ((K + 3 : ℕ) : ℝ) := by norm_num
  rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_zero,
    ccmActualHeadQuantilePolarCoordinate_two, hclock,
    ccmActualHeadPolarMassCoordinate_log_nat (K + 3) (by omega)]
  ring

/-- The future null coordinate of the terminal pair is exactly twice the retained head mass. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_sub_errorDisplacement
    (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0 -
        speQuantileRieszTerminalErrorDisplacement K =
      2 * ccmActualHeadParabolicMass K := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_eq_headMass_add_threshold,
    speQuantileRieszTerminalErrorDisplacement_eq_threshold_sub_headMass]
  ring

/-- The past null coordinate of the terminal pair is the physical square-root threshold. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_add_errorDisplacement
    (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0 +
        speQuantileRieszTerminalErrorDisplacement K =
      4 * (Real.sqrt ((K + 3 : ℕ) : ℝ) - 1) := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_eq_headMass_add_threshold,
    speQuantileRieszTerminalErrorDisplacement_eq_threshold_sub_headMass]
  ring

/-- The terminal pair has an exact positive Lorentz square, not merely a nonnegative one. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_sq_sub_errorDisplacement_sq
    (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0 ^ (2 : ℕ) -
        speQuantileRieszTerminalErrorDisplacement K ^ (2 : ℕ) =
      8 * ccmActualHeadParabolicMass K * (Real.sqrt ((K + 3 : ℕ) : ℝ) - 1) := by
  rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_eq_headMass_add_threshold,
    speQuantileRieszTerminalErrorDisplacement_eq_threshold_sub_headMass]
  ring

/-- The source terminal pair is strictly timelike at every cutoff. -/
theorem ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_strictTimelike
    (K : ℕ) :
    0 < ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0 -
          speQuantileRieszTerminalErrorDisplacement K ∧
      0 < ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0 +
          speQuantileRieszTerminalErrorDisplacement K ∧
      0 < ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0 ^ (2 : ℕ) -
          speQuantileRieszTerminalErrorDisplacement K ^ (2 : ℕ) := by
  have hmass : 0 < ccmActualHeadParabolicMass K := ccmActualHeadParabolicMass_pos K
  have hN : (1 : ℝ) < ((K + 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < K + 3 by omega)
  have hsquare : 1 < (Real.sqrt ((K + 3 : ℕ) : ℝ)) ^ (2 : ℕ) := by
    rw [Real.sq_sqrt (by positivity)]
    exact hN
  have hsqrt : 1 < Real.sqrt ((K + 3 : ℕ) : ℝ) := by
    have hnonneg : 0 ≤ Real.sqrt ((K + 3 : ℕ) : ℝ) := Real.sqrt_nonneg _
    nlinarith
  constructor
  · rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_sub_errorDisplacement]
    positivity
  constructor
  · rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_add_errorDisplacement]
    positivity
  · rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_sq_sub_errorDisplacement_sq]
    positivity

/-- The target P-G105F Julia quadratic form evaluated on a two-channel coordinate. -/
def speQuantileRieszTerminalPJuliaQuadratic (v : Fin 2 → ℂ) : ℂ :=
  ∑ i, ∑ j, star (v i) * routePPrimitiveBurnolJuliaKreinBlock i j * v j

private def terminalJuliaCoordinatesOf (B D : ℝ) : Fin 2 → ℂ :=
  ![(8 * B - Real.sqrt 63 * D : ℝ), (D / 8 : ℝ)]

private def terminalJuliaSourceVectorOf (B D : ℝ) : Fin 3 → ℂ :=
  ![(B : ℝ), (D / 8 : ℝ), (Real.sqrt 63 * D / 8 : ℝ)]

/-- The cofinal terminal coordinate in the actual two-channel P Julia target. -/
def speQuantileRieszTerminalPJuliaCoordinates (K : ℕ) : Fin 2 → ℂ :=
  terminalJuliaCoordinatesOf
    (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0)
    (speQuantileRieszTerminalErrorDisplacement K)

/-- The corresponding source coordinate splits the signed terminal displacement over the two
negative directions forced by the literal four-label lift. -/
def speQuantileRieszTerminalPJuliaSourceCoordinates (K : ℕ) : Fin 3 → ℂ :=
  terminalJuliaSourceVectorOf
    (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0)
    (speQuantileRieszTerminalErrorDisplacement K)

private theorem ccmActualHeadParabolicMass_succ_terminal (K : ℕ) :
    ccmActualHeadParabolicMass (K + 1) =
      ccmActualHeadParabolicMass K + criticalMellinAtomWeight (K + 3) := by
  unfold ccmActualHeadParabolicMass
  rw [Finset.sum_range_succ]

private theorem terminalBoundary_succ_sub (K : ℕ) :
    ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary (K + 1)
        (Real.log (K + 1 + 3)) 0 -
      ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0 =
      criticalMellinAtomWeight (K + 3) +
        2 * (Real.sqrt ((K + 4 : ℕ) : ℝ) - Real.sqrt ((K + 3 : ℕ) : ℝ)) := by
  rw [show ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary (K + 1)
        (Real.log ((K : ℝ) + 1 + 3)) 0 =
      ccmActualHeadParabolicMass (K + 1) +
        2 * (Real.sqrt ((K + 4 : ℕ) : ℝ) - 1) by
      convert ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_eq_headMass_add_threshold
        (K + 1) using 1; norm_num,
    ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_eq_headMass_add_threshold K,
    ccmActualHeadParabolicMass_succ_terminal]
  norm_num
  ring

private theorem terminalErrorDisplacement_succ_sub (K : ℕ) :
    speQuantileRieszTerminalErrorDisplacement (K + 1) -
      speQuantileRieszTerminalErrorDisplacement K =
      2 * (Real.sqrt ((K + 4 : ℕ) : ℝ) - Real.sqrt ((K + 3 : ℕ) : ℝ)) -
        criticalMellinAtomWeight (K + 3) := by
  rw [speQuantileRieszTerminalErrorDisplacement_eq_threshold_sub_headMass,
    speQuantileRieszTerminalErrorDisplacement_eq_threshold_sub_headMass,
    ccmActualHeadParabolicMass_succ_terminal]
  norm_num
  ring

private theorem terminalJuliaCoordinatesOf_lift (B D : ℝ) :
    _root_.GaloisForLFunctions.RHTower.suzukiBoundaryExcursionFourLabelLightKreinLift *ᵥ
        terminalJuliaCoordinatesOf B D =
      terminalJuliaSourceVectorOf B D := by
  ext i
  fin_cases i <;>
    simp [terminalJuliaCoordinatesOf, terminalJuliaSourceVectorOf,
      _root_.GaloisForLFunctions.RHTower.suzukiBoundaryExcursionFourLabelLightKreinLift,
      Matrix.mulVec, routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
  all_goals ring

private theorem terminalJuliaCoordinatesOf_sub (B₁ D₁ B₀ D₀ : ℝ) :
    terminalJuliaCoordinatesOf B₁ D₁ - terminalJuliaCoordinatesOf B₀ D₀ =
      terminalJuliaCoordinatesOf (B₁ - B₀) (D₁ - D₀) := by
  ext i
  fin_cases i <;>
    simp [terminalJuliaCoordinatesOf]
  all_goals ring

/-- The existing four-label source lift carries every terminal P coordinate exactly.  The
previously finite signature repair is therefore a genuine cofinal endpoint carrier once the
terminal signed coordinate is distributed over its forced negative sector. -/
theorem speQuantileRieszTerminalPJuliaCoordinates_lift (K : ℕ) :
    _root_.GaloisForLFunctions.RHTower.suzukiBoundaryExcursionFourLabelLightKreinLift *ᵥ
        speQuantileRieszTerminalPJuliaCoordinates K =
      speQuantileRieszTerminalPJuliaSourceCoordinates K := by
  exact terminalJuliaCoordinatesOf_lift _ _

/-- The cofinal terminal P coordinate has an exact two-source affine cutoff increment: a new
prime-power atom and the physical square-root-wall increment.  Hence a full P history lift must
transport both channels, rather than a clock-retuned prime coordinate alone. -/
theorem speQuantileRieszTerminalPJuliaCoordinates_succ_sub (K : ℕ) :
    speQuantileRieszTerminalPJuliaCoordinates (K + 1) -
        speQuantileRieszTerminalPJuliaCoordinates K =
      terminalJuliaCoordinatesOf
        (criticalMellinAtomWeight (K + 3) +
          2 * (Real.sqrt ((K + 4 : ℕ) : ℝ) - Real.sqrt ((K + 3 : ℕ) : ℝ)))
        (2 * (Real.sqrt ((K + 4 : ℕ) : ℝ) - Real.sqrt ((K + 3 : ℕ) : ℝ)) -
          criticalMellinAtomWeight (K + 3)) := by
  change terminalJuliaCoordinatesOf
      (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary (K + 1)
        (Real.log (((K + 1 : ℕ) : ℝ) + 3)) 0)
      (speQuantileRieszTerminalErrorDisplacement (K + 1)) -
    terminalJuliaCoordinatesOf
      (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log ((K : ℝ) + 3)) 0)
      (speQuantileRieszTerminalErrorDisplacement K) = _
  rw [terminalJuliaCoordinatesOf_sub]
  have hclock : Real.log (((K + 1 : ℕ) : ℝ) + 3) =
      Real.log ((K : ℝ) + 1 + 3) := by norm_num
  rw [hclock, terminalBoundary_succ_sub,
    terminalErrorDisplacement_succ_sub]

private def terminalJuliaChildControl (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![64 * v 0, 0]

private def terminalJuliaNegativePivotControl (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![0, -v 1]

private theorem routePJuliaKrein_channel_controls_span (v : Fin 2 → ℂ) :
    routePJuliaKreinChildHistoryStep *ᵥ terminalJuliaChildControl v +
        routePJuliaKreinNegativePivotHistoryStep *ᵥ terminalJuliaNegativePivotControl v = v := by
  ext i
  fin_cases i <;>
    simp [routePJuliaKreinChildHistoryStep, routePJuliaKreinNegativePivotHistoryStep,
      terminalJuliaChildControl, terminalJuliaNegativePivotControl,
      routePPrimitiveGammaJuliaSignedChannelDiagonal,
      routePPrimitiveBurnolJuliaKreinBlock]
  all_goals ring

/-- The two literal P channel steps controllably realize the exact terminal cutoff increment.
This is a source-defined affine control identity, not yet an ordered-history intertwiner. -/
theorem speQuantileRieszTerminalPJuliaCoordinates_succ_sub_as_channelControls (K : ℕ) :
    speQuantileRieszTerminalPJuliaCoordinates (K + 1) -
        speQuantileRieszTerminalPJuliaCoordinates K =
      routePJuliaKreinChildHistoryStep *ᵥ terminalJuliaChildControl
        (speQuantileRieszTerminalPJuliaCoordinates (K + 1) -
          speQuantileRieszTerminalPJuliaCoordinates K) +
      routePJuliaKreinNegativePivotHistoryStep *ᵥ terminalJuliaNegativePivotControl
        (speQuantileRieszTerminalPJuliaCoordinates (K + 1) -
          speQuantileRieszTerminalPJuliaCoordinates K) := by
  symm
  exact routePJuliaKrein_channel_controls_span _

private theorem terminalPJuliaCoordinates_zero_re_eq (K : ℕ) :
    (speQuantileRieszTerminalPJuliaCoordinates K 0).re =
      (8 + Real.sqrt 63) * ccmActualHeadParabolicMass K +
        2 * (8 - Real.sqrt 63) * (Real.sqrt ((K + 3 : ℕ) : ℝ) - 1) := by
  change 8 * ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K
      (Real.log ((K : ℝ) + 3)) 0 -
      Real.sqrt 63 * speQuantileRieszTerminalErrorDisplacement K = _
  rw [ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_eq_headMass_add_threshold,
    speQuantileRieszTerminalErrorDisplacement_eq_threshold_sub_headMass]
  ring

/-- The cofinal terminal endpoint cannot live in a bounded/Bessel P carrier: its literal first
P Julia coordinate escapes to `+infinity` already before the ordered-history current is added. -/
theorem tendsto_speQuantileRieszTerminalPJuliaCoordinates_zero_re_atTop :
    Tendsto (fun K : ℕ => (speQuantileRieszTerminalPJuliaCoordinates K 0).re) atTop atTop := by
  have hsqrt_sq : Real.sqrt 63 ^ (2 : ℕ) = 63 := Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 63 := Real.sqrt_nonneg _
  have hcoef : 0 < 8 - Real.sqrt 63 := by nlinarith
  have hscale : 0 < 2 * (8 - Real.sqrt 63) := by positivity
  have hcast : Tendsto (fun K : ℕ => ((K + 3 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      (tendsto_atTop_add_const_right atTop (3 : ℝ) tendsto_natCast_atTop_atTop)
  have hsqrt : Tendsto (fun K : ℕ => Real.sqrt ((K + 3 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hcast
  have hshift : Tendsto
      (fun K : ℕ => Real.sqrt ((K + 3 : ℕ) : ℝ) - 1) atTop atTop := by
    convert tendsto_atTop_add_const_right atTop (-1 : ℝ) hsqrt using 1; ring
  have hbase : Tendsto
      (fun K : ℕ => 2 * (8 - Real.sqrt 63) *
        (Real.sqrt ((K + 3 : ℕ) : ℝ) - 1)) atTop atTop :=
    Tendsto.const_mul_atTop hscale hshift
  refine tendsto_atTop_mono (fun K => ?_) hbase
  rw [terminalPJuliaCoordinates_zero_re_eq]
  have hmass : 0 ≤ ccmActualHeadParabolicMass K :=
    (ccmActualHeadParabolicMass_pos K).le
  have hpositive : 0 ≤ (8 + Real.sqrt 63) * ccmActualHeadParabolicMass K := by
    positivity
  linarith

private theorem terminalJuliaCoordinatesOf_quadratic (B D : ℝ) :
    speQuantileRieszTerminalPJuliaQuadratic (terminalJuliaCoordinatesOf B D) =
      ((B ^ (2 : ℕ) - D ^ (2 : ℕ) : ℝ) : ℂ) := by
  have hsqrt : Real.sqrt 63 ^ (2 : ℕ) = 63 := Real.sq_sqrt (by norm_num)
  have hstar8 : (starRingEnd ℂ) (8 : ℂ) = 8 := by
    simp only [starRingEnd_apply, star_ofNat]
  have hBre : ((B : ℂ) ^ (2 : ℕ)).re = B ^ (2 : ℕ) := by
    rw [← Complex.ofReal_pow]
    rfl
  have hDre : ((D : ℂ) ^ (2 : ℕ)).re = D ^ (2 : ℕ) := by
    rw [← Complex.ofReal_pow]
    rfl
  have hBim : ((B : ℂ) ^ (2 : ℕ)).im = 0 := by
    rw [← Complex.ofReal_pow]
    rfl
  have hDim : ((D : ℂ) ^ (2 : ℕ)).im = 0 := by
    rw [← Complex.ofReal_pow]
    rfl
  apply Complex.ext
  · simp [speQuantileRieszTerminalPJuliaQuadratic, terminalJuliaCoordinatesOf,
      routePPrimitiveBurnolJuliaKreinBlock, Fin.sum_univ_two,
      routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
    rw [hstar8]
    norm_num
    ring_nf
    rw [hBre, hDre]
    nlinarith [hsqrt]
  · simp [speQuantileRieszTerminalPJuliaQuadratic, terminalJuliaCoordinatesOf,
      routePPrimitiveBurnolJuliaKreinBlock, Fin.sum_univ_two,
      routeEPCubicFourthDepthJuliaDefect_eq_sqrt63_div_eight]
    rw [hstar8]
    norm_num
    rw [hBim, hDim]
    ring

/-- The P Julia quadratic of the cofinal terminal coordinate is the source terminal Lorentz
square.  No boundedness or RH hypothesis is used. -/
theorem speQuantileRieszTerminalPJuliaQuadratic_eq_terminalLorentzSquare (K : ℕ) :
    speQuantileRieszTerminalPJuliaQuadratic (speQuantileRieszTerminalPJuliaCoordinates K) =
      ((ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0 ^ (2 : ℕ) -
        speQuantileRieszTerminalErrorDisplacement K ^ (2 : ℕ) : ℝ) : ℂ) := by
  exact terminalJuliaCoordinatesOf_quadratic _ _

/-- The actual P target coordinate is strictly timelike at every finite cutoff. -/
theorem speQuantileRieszTerminalPJuliaQuadratic_re_pos (K : ℕ) :
    0 < (speQuantileRieszTerminalPJuliaQuadratic
      (speQuantileRieszTerminalPJuliaCoordinates K)).re := by
  rw [speQuantileRieszTerminalPJuliaQuadratic_eq_terminalLorentzSquare]
  change 0 <
    ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary K (Real.log (K + 3)) 0 ^ (2 : ℕ) -
      speQuantileRieszTerminalErrorDisplacement K ^ (2 : ℕ)
  exact
    (ccmActualHeadMatchedCompletedQuantileParabolicSourceBoundary_terminal_strictTimelike K).2.2

end

end RHTower
