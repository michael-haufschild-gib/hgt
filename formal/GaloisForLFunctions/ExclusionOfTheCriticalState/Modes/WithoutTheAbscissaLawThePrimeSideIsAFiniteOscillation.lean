import GaloisForLFunctions.ExclusionOfTheCriticalState.Decay.WithoutTheAbscissaLawTheWindowMassesHaveTheRateOfTheZeros
import GaloisForLFunctions.ExclusionOfTheCriticalState.Modes.TheHeatedProfileBeyondTheWallGrowsAtTheRateOfTheZeros
import GaloisForLFunctions.ZeroConfigurationGeometry.TheOneOffsAreFiniteOscillationsOfThePrimeError
import GaloisForLFunctions.RHTower.JointAncestryRealAmplitudeDetection

/-!
# Without the abscissa law the prime side of the state is a finite oscillation

The asymptotic abscissa law fails exactly when \`ψ(x) − x\` is a single finite oscillation
\`x^Θ T(log x) + O(x^{Θ−η})\` (\`not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation\`); the
zeros then have an isolated finite top on \`Re ρ = Θ\`. Its reflection \`1 − ρ\` is an isolated
bottom: a finite set of centred zeros on \`Re z = −(Θ − ½)\`, all others at \`Re z ≥ −κ₂\` with
\`κ₂ < Θ − ½\` (\`exists_isolated_bottom_of_not_asymptoticAbscissaLaw\`).

* **The prime side** (\`criticalState_heatedBeyondWall_finiteOscillation\`). The heated profile beyond
  the wall is the sum of its zero modes \`a⁻¹ L F(z) e^{εz² − zT}\` plus the heated confined state
  (\`criticalState_hasSum_heated_zeroSeries\`). Without the abscissa law

    \`F⁺_ε(T) = a⁻¹ Σ_{z in the bottom} L F(z) e^{εz² − zT} + O(e^{κ₂T})\`,  \`T ≥ 0\`:

  a finite oscillation of modulus \`e^{(Θ−½)T}\` whose frequencies \`−Im z\` are the ordinates of the
  top zeros. The prime number theorem averaged by \`F\` has the shape of its remainder.
* **Real-amplitude positivity fails at every level** (\`not_jasRealPositiveAbove_of_not_asymptoticAbscissaLaw\`):
  the top zeros are the farthest from the line, so they are detected on the primes above every \`X\`
  at every \`σ ∈ (Θ − ½, Θ + ½)\`.
* **Stage 2** (\`b13_iff_finiteOffLine_not_primeErrorIsFiniteOscillation\`). In the finite stratum the
  zeros approach the line, so B13 holds iff under a finite layer \`ψ(x) − x\` is never a single
  finite oscillation at leading order.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Finset

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri HTGeometry _root_.RHTower

/-! ### The isolated bottom -/

/-- **The reflected top.** Without the abscissa law a finite nonempty set \`B\` of zero copies has
centred real part \`−(Θ − ½)\`, and every other centred zero has real part \`≥ −κ₂\`,
\`0 ≤ κ₂ < Θ − ½\`. -/
theorem exists_isolated_bottom_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) :
    ∃ (B : Finset XiZeroCopy) (κ₂ : ℝ), B.Nonempty ∧ 0 ≤ κ₂ ∧
      κ₂ < zetaZeroAbscissa - 1 / 2 ∧
      (∀ q ∈ B, (centredZero q).re = -(zetaZeroAbscissa - 1 / 2)) ∧
      ∀ q ∉ B, -κ₂ ≤ (centredZero q).re := by
  classical
  rw [InfiniteRankWeilTheory.asymptoticAbscissaLaw_zetaConfig_iff,
    InfiniteRankWeilTheory.not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨S, Θ, Θ₂, hSne, hΘ, hΘ₂, hS, hrest⟩ := hnot
  have habs := zetaZeroAbscissa_eq_of_isolatedTop hSne hΘ hΘ₂ hS hrest
  set r : XiZeroCopy ≃ XiZeroCopy := xiZeroCopyReflectEquiv
  have hsymm : ∀ q, ((r.symm q).1 : ℂ) = 1 - (q.1 : ℂ) := fun q => by
    have h := xiZeroCopy_reflect_val (r.symm q)
    rw [show xiZeroCopyReflectEquiv (r.symm q) = q from r.apply_symm_apply q] at h
    linear_combination h
  have hcz : ∀ q : XiZeroCopy, (centredZero q).re = ((q.1 : ℂ)).re - 1 / 2 := fun q => by
    simp [centredZero]
  refine ⟨S.map r.toEmbedding, max (Θ₂ - 1 / 2) 0, hSne.map, le_max_right _ _, ?_, ?_, ?_⟩
  · rw [habs]; exact max_lt (by linarith) (by linarith)
  · intro q hq
    have hq' : r.symm q ∈ S := (Finset.mem_map_equiv).1 hq
    have h1 : ((r.symm q).1 : ℂ).re = Θ := hS _ hq'
    rw [hsymm, Complex.sub_re, Complex.one_re] at h1
    rw [hcz, habs]; linarith
  · intro q hq
    have hq' : r.symm q ∉ S := fun h => hq ((Finset.mem_map_equiv).2 h)
    have h1 : ((r.symm q).1 : ℂ).re ≤ Θ₂ := hrest _ hq'
    rw [hsymm, Complex.sub_re, Complex.one_re] at h1
    rw [hcz]
    have := le_max_left (Θ₂ - 1 / 2) 0
    linarith

/-! ### The prime side as a finite oscillation -/

/-- **E-M14: without the abscissa law the heated prime side of the state is a finite oscillation
at the rate \`Θ − ½\`.** With \`B\` the bottom of the centred zeros (\`Re z = −(Θ − ½)\`) and
\`κ₂ < Θ − ½\` the bound of the others, for every \`ε > 0\` and \`T ≥ 0\`

  \`‖F⁺_ε(T) − a⁻¹ Σ_{q ∈ B} L F(z_q) e^{εz_q² − z_q T}‖ ≤ C e^{κ₂T}\`. -/
theorem criticalState_heatedBeyondWall_finiteOscillation (hnot : ¬ RHTower.AsymptoticAbscissaLaw)
    {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ (B : Finset XiZeroCopy) (κ₂ : ℝ), B.Nonempty ∧ 0 ≤ κ₂ ∧
      κ₂ < zetaZeroAbscissa - 1 / 2 ∧
      (∀ q ∈ B, (centredZero q).re = -(zetaZeroAbscissa - 1 / 2)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
        ‖heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T -
            (criticalAliasCoefficient W₀ : ℂ)⁻¹ * ∑ q ∈ B,
              negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q)‖ ≤
          C * Real.exp (κ₂ * T) := by
  classical
  obtain ⟨B, κ₂, hBne, hκ₂0, hκ₂, hB, hrest⟩ := exists_isolated_bottom_of_not_asymptoticAbscissaLaw hnot
  refine ⟨B, κ₂, hBne, hκ₂0, hκ₂, hB, fun ε hε => ?_⟩
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have ha := criticalAliasCoefficient_positive hW
  have ha' : (criticalAliasCoefficient W₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  have hp : ∀ q : XiZeroCopy, (1 / 2 : ℝ) ≤ ‖(-1 : ℂ) - centredZero q‖ := fun q => by
    have hre := (abs_lt.mp (abs_re_centredZero_lt q)).1
    have h := Complex.abs_re_le_norm ((-1 : ℂ) - centredZero q)
    rw [Complex.sub_re, Complex.neg_re, Complex.one_re, abs_of_neg (by linarith)] at h
    linarith
  have hs := summable_norm_mul_inv_sub_centredZero
    (criticalState_summable_norm_sq_zeroValues hW hthreshold hF) (by norm_num : (0 : ℝ) < 1 / 2) hp
  set K : ℝ := Real.exp (ε / 4) * (3 / 2 + 1 / (4 * ε))
  set M : ℝ := ∑' q : XiZeroCopy, ‖negativeHalfLineLaplace (cx F) (centredZero q) *
    ((-1 : ℂ) - centredZero q)⁻¹‖
  set H : ℝ := (2 * Real.pi)⁻¹ * Real.sqrt (Real.pi / ε) * Real.exp (64 * ε) * ∫ u, |F u|
  have hK0 : 0 ≤ K := by positivity
  have hH0 : 0 ≤ H := by positivity
  refine ⟨(criticalAliasCoefficient W₀)⁻¹ * (K * M) + H, fun T hT => ?_⟩
  set f : XiZeroCopy → ℂ := fun q =>
    negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q)
  have hsum := criticalState_hasSum_heated_zeroSeries hW hthreshold hF hε T
  have hfs : Summable fun q => ‖f q‖ :=
    criticalState_summable_norm_heatedZeroModes hW hthreshold hF hε T
  -- the modes off the bottom
  set g : XiZeroCopy → ℂ := fun q => if q ∈ B then 0 else f q
  have hB0 : HasSum (fun q => if q ∈ B then f q else 0) (∑ q ∈ B, f q) := by
    have h : HasSum (fun q : XiZeroCopy => if q ∈ B then f q else 0)
        (∑ q ∈ B, (if q ∈ B then f q else 0)) :=
      hasSum_sum_of_ne_finset_zero fun q hq => by simp [hq]
    have e : (∑ q ∈ B, (if q ∈ B then f q else 0)) = ∑ q ∈ B, f q :=
      Finset.sum_congr rfl fun q hq => if_pos hq
    rwa [e] at h
  have hg : HasSum g ((criticalAliasCoefficient W₀ : ℂ) *
      (heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ)) - ∑ q ∈ B, f q) := by
    have h := hsum.sub hB0
    refine h.congr_fun fun q => ?_
    by_cases hq : q ∈ B <;> simp [g, f, hq]
  have hgb : ∀ q, ‖g q‖ ≤ K * Real.exp (κ₂ * T) *
      ‖negativeHalfLineLaplace (cx F) (centredZero q) * ((-1 : ℂ) - centredZero q)⁻¹‖ := by
    intro q
    by_cases hq : q ∈ B
    · simp only [g, hq, if_true, norm_zero]; positivity
    · simp only [g, f, hq, if_false]
      have hT' : Real.exp (-((centredZero q).re * T)) ≤ Real.exp (κ₂ * T) :=
        Real.exp_le_exp.mpr (by nlinarith [hrest q hq])
      rw [norm_mul, norm_mul]
      calc ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ * ‖stateHeatSymbol ε T (centredZero q)‖
          ≤ ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ *
              (K * ‖((-1 : ℂ) - centredZero q)⁻¹‖ * Real.exp (κ₂ * T)) :=
            mul_le_mul_of_nonneg_left ((norm_stateHeatSymbol_centredZero_le hε T q).trans
              (mul_le_mul_of_nonneg_left hT' (by positivity))) (norm_nonneg _)
        _ = _ := by ring
  have hgs : Summable fun q => ‖g q‖ :=
    hfs.of_nonneg_of_le (fun q => norm_nonneg _) fun q => by
      by_cases hq : q ∈ B
      · simp [g, hq]
      · simp [g, hq]
  have hZ : ‖(criticalAliasCoefficient W₀ : ℂ) *
      (heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ)) - ∑ q ∈ B, f q‖ ≤
        K * Real.exp (κ₂ * T) * M := by
    rw [← hg.tsum_eq, ← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hgs).trans (Summable.tsum_le_tsum hgb hgs (hs.mul_left _))
  have hst : ‖((heatedState ε F T : ℝ) : ℂ)‖ ≤ H * Real.exp (κ₂ * T) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (abs_heatedState_le_of_nonneg hd hε hT).trans
      (le_mul_of_one_le_right hH0 (Real.one_le_exp (by positivity)))
  have hid : heatedBeyondWall ε W₀ hd T - (criticalAliasCoefficient W₀ : ℂ)⁻¹ * ∑ q ∈ B, f q =
      (criticalAliasCoefficient W₀ : ℂ)⁻¹ * ((criticalAliasCoefficient W₀ : ℂ) *
        (heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ)) - ∑ q ∈ B, f q) +
          ((heatedState ε F T : ℝ) : ℂ) := by
    rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ ha', one_mul]; ring
  rw [hid]
  calc _ ≤ ‖(criticalAliasCoefficient W₀ : ℂ)⁻¹ * ((criticalAliasCoefficient W₀ : ℂ) *
        (heatedBeyondWall ε W₀ hd T - ((heatedState ε F T : ℝ) : ℂ)) - ∑ q ∈ B, f q)‖ +
          ‖((heatedState ε F T : ℝ) : ℂ)‖ := norm_add_le _ _
    _ ≤ (criticalAliasCoefficient W₀)⁻¹ * (K * Real.exp (κ₂ * T) * M) + H * Real.exp (κ₂ * T) := by
        refine add_le_add ?_ hst
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ha.le]
        exact mul_le_mul_of_nonneg_left hZ (inv_nonneg.mpr ha.le)
    _ = ((criticalAliasCoefficient W₀)⁻¹ * (K * M) + H) * Real.exp (κ₂ * T) := by ring

/-- **The prime side of the state follows the prime error.** If \`ψ(x) − x\` is a single finite
oscillation at leading order, a critical state exists and its heated prime side is a finite
oscillation at the rate \`Θ − ½\`. -/
theorem exists_criticalState_heatedBeyondWall_finiteOscillation
    (hosc : ZeroConfigurationGeometry.PrimeErrorIsFiniteOscillation) :
    ∃ (W₀ : ℝ) (F : ℝ → ℝ) (hF : IsCriticalHalfLineGroundState W₀ F), 0 < W₀ ∧
      (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal) ∧
      ∃ (B : Finset XiZeroCopy) (κ₂ : ℝ), B.Nonempty ∧ 0 ≤ κ₂ ∧
        κ₂ < zetaZeroAbscissa - 1 / 2 ∧
        (∀ q ∈ B, (centredZero q).re = -(zetaZeroAbscissa - 1 / 2)) ∧
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ T : ℝ, 0 ≤ T →
          ‖heatedBeyondWall ε W₀ (criticalHalfLineEnergyDomain_of_groundState hF) T -
              (criticalAliasCoefficient W₀ : ℂ)⁻¹ * ∑ q ∈ B,
                negativeHalfLineLaplace (cx F) (centredZero q) *
                  stateHeatSymbol ε T (centredZero q)‖ ≤
            C * Real.exp (κ₂ * T) := by
  have hnot := ZeroConfigurationGeometry.not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation.2 hosc
  have hnotRH : ¬ RiemannHypothesis := fun hRH => hnot (asymptoticAbscissaLaw_of_riemannHypothesis hRH)
  obtain ⟨W₀, F, hW, hthreshold, hF⟩ :=
    (riemannHypothesis_or_exists_criticalHalfLineGroundState).resolve_left hnotRH
  exact ⟨W₀, F, hF, hW, hthreshold,
    criticalState_heatedBeyondWall_finiteOscillation hnot hW hthreshold hF⟩

/-! ### Real-amplitude positivity and stage 2 -/

/-- **Without the abscissa law real-amplitude positivity fails above every level** at every
\`σ ∈ (Θ − ½, Θ + ½)\`: the top zeros have the largest distance from the line. -/
theorem not_jasRealPositiveAbove_of_not_asymptoticAbscissaLaw
    (hnot : ¬ RHTower.AsymptoticAbscissaLaw) {σ : ℝ} (hσ0 : zetaZeroAbscissa - 1 / 2 < σ)
    (hσ1 : σ < zetaZeroAbscissa + 1 / 2) (X : ℕ) : ¬ JasRealPositiveAbove X σ := by
  rw [InfiniteRankWeilTheory.asymptoticAbscissaLaw_zetaConfig_iff,
    InfiniteRankWeilTheory.not_asymptoticAbscissaLaw_iff_hasIsolatedTop] at hnot
  obtain ⟨S, Θ, Θ₂, hSne, hΘ, hΘ₂, hS, hrest⟩ := hnot
  have habs := zetaZeroAbscissa_eq_of_isolatedTop hSne hΘ hΘ₂ hS hrest
  obtain ⟨q₀, hq₀⟩ := hSne
  have h0 : ((q₀.1 : ℂ)).re = Θ := hS q₀ hq₀
  have hle : ∀ q : XiZeroCopy, ((q.1 : ℂ)).re ≤ Θ := fun q => by
    by_cases hq : q ∈ S
    · exact (hS q hq).le
    · exact (hrest q hq).trans hΘ₂.le
  have hd0 : |(q₀.1 : ℂ).re - 1 / 2| = Θ - 1 / 2 := by
    rw [h0, abs_of_pos (by linarith)]
  have hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := by
    intro q
    have h1 := hle q
    have h2 := hle (xiZeroCopyReflectEquiv q)
    rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re] at h2
    rw [hd0, abs_le]
    constructor <;> linarith
  rw [habs] at hσ0 hσ1
  exact not_jasRealPositiveAbove_of_maximal_offLine q₀ (by rw [h0]; exact hΘ.ne') hmax
    (by rw [hd0]; exact hσ0) (by rw [hd0]; linarith) X

/-- **Stage 2 with the prime error as a finite oscillation.** B13 holds iff under a finite layer
\`ψ(x) − x\` is never a single finite oscillation at leading order. -/
theorem b13_iff_finiteOffLine_not_primeErrorIsFiniteOscillation :
    (InfiniteRankWeilTheory.FiniteOffLine → RiemannHypothesis) ↔
      (InfiniteRankWeilTheory.FiniteOffLine →
        ¬ ZeroConfigurationGeometry.PrimeErrorIsFiniteOscillation) := by
  constructor
  · intro h hfin hosc
    exact ZeroConfigurationGeometry.not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation.2 hosc
      (asymptoticAbscissaLaw_of_riemannHypothesis (h hfin))
  · intro h hfin
    have hAAL : RHTower.AsymptoticAbscissaLaw := by
      by_contra hnot
      exact h hfin
        (ZeroConfigurationGeometry.not_asymptoticAbscissaLaw_iff_primeErrorIsFiniteOscillation.1 hnot)
    exact RHTower.riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw.mpr
      ⟨InfiniteRankWeilTheory.zerosApproachLine_of_finiteOffLine hfin, hAAL⟩

end GaloisForLFunctions.ExclusionOfTheCriticalState
