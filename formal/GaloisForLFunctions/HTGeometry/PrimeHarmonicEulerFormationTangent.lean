import GaloisForLFunctions.HTGeometry.PrimeHarmonicEndHaarFrame
import GaloisForLFunctions.RHTower.PoissonScaleHistoryFrame

/-!
# Euler formation, end-tangent selection and the Poisson mother

* **Energy laws.**  The literal Euler coefficients `λ ≡ 1` obey Mertens' energy law with `κ = 1`,
  and so does every Dirichlet character, with only the conductor primes removed.
* **End-tangent selection.**  Under an energy law with `κ > 0`, the end measures `μ_{a,L}` have a
  finite nonzero limit on the end windows `[0, δ]` exactly at grade `a = 0`; the functional
  equation exchanges `a` and `-a`, and both orientations have finite nonzero end tangents iff
  `a = 0`.
* **Full Euler formation.**  At prime-power depth `m ≥ 2` the literal amplitudes
  `p^{-m/2}/m · e^{-iτ m log p}` at clocks `log (m log p) - L` form a square-summable residual frame
  whose trace norm tends to zero; the full prime-power formation has the same nonzero Haar
  tangent as its principal layer.
* **Poisson mother.**  `F(x) = 2 e^x exp (-e^x)` is a `W^{1,1} ∩ L²` window with `‖F‖₁ = 2` and
  `‖F'‖₁ = 4/e`, so the neutral bound reads `‖A_{0,L} - A_H‖ ≤ (16/e) ε_L`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ### Energy laws -/

/-- The literal Euler coefficients `λ ≡ 1` obey **Mertens' energy law**
`∑_{p ≤ x} 1/p = log log x + M + o(1)`. -/
theorem hasPrimeEnergyLaw_one :
    HasPrimeEnergyLaw (fun _ => 1) 1 _root_.RHTower.mertensSecondConstant := by
  have heq : ∀ x : ℝ, primeEnergySum (fun _ => 1) x = _root_.RHTower.primeRecipSum ⌊x⌋₊ := by
    intro x
    unfold primeEnergySum _root_.RHTower.primeRecipSum _root_.RHTower.primeRecipWeight
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  unfold HasPrimeEnergyLaw
  simp_rw [heq, one_mul]
  exact _root_.RHTower.tendsto_primeRecipSum_floor_sub_logLog

/-- `log log ⌊x⌋ - log log x → 0`. -/
theorem tendsto_logLog_floor_sub :
    Tendsto (fun x : ℝ => Real.log (Real.log ⌊x⌋₊) - Real.log (Real.log x)) atTop (𝓝 0) := by
  have h1 := _root_.RHTower.tendsto_primeRecipSum_floor_sub_logLog
  have h2 := _root_.RHTower.tendsto_primeRecipSum_sub_logLog.comp (tendsto_nat_floor_atTop (α := ℝ))
  have := h1.sub h2
  rw [sub_self] at this
  refine this.congr fun x => ?_
  simp only [Function.comp_apply]
  ring

/-- Every Dirichlet character obeys the energy law with `κ = 1`, the level primes removed. -/
theorem hasPrimeEnergyLaw_dirichletCharacter {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    HasPrimeEnergyLaw (fun n => χ (n : ZMod q)) 1
      (_root_.RHTower.mertensSecondConstant -
        _root_.RHTower.dirichletCharacterLevelPrimeCorrectionTotal q) := by
  have heq : ∀ x : ℝ, primeEnergySum (fun n => χ (n : ZMod q)) x =
      _root_.RHTower.dirichletCharacterPrimeRecipEnergy χ ⌊x⌋₊ := fun x => rfl
  have h1 := (_root_.RHTower.tendsto_dirichletCharacterPrimeRecipEnergy_sub_logLog χ).comp
    (tendsto_nat_floor_atTop (α := ℝ))
  have h2 := h1.add tendsto_logLog_floor_sub
  rw [add_zero] at h2
  unfold HasPrimeEnergyLaw
  refine h2.congr fun x => ?_
  simp only [Function.comp_apply, heq, one_mul]
  ring

/-! ### End-tangent selection -/

/-- The end measures have a **finite nonzero end tangent** at grade `a`: a measure `ν`, finite on
the windows `[0, δ]` and nonzero on one of them, with `μ_{a,L}[0, δ] → ν[0, δ]` for every
`δ > 0`. -/
def HasFiniteNonzeroEndTangent (coef : ℕ → ℂ) (a : ℝ) : Prop :=
  ∃ ν : Measure ℝ, (∀ δ, ν (Icc 0 δ) ≠ ⊤) ∧ (∃ δ > 0, ν (Icc 0 δ) ≠ 0) ∧
    ∀ δ > 0, Tendsto (fun L => primeEndMeasure coef a L (Icc 0 δ)) atTop (𝓝 (ν (Icc 0 δ)))

/-- At neutral grade the end measures converge to `κ dy` on every window. -/
theorem tendsto_primeEndMeasure_zero_Icc {coef : ℕ → ℂ} {κ C : ℝ}
    (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 ≤ κ) {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto (fun L => primeEndMeasure coef 0 L (Icc 0 δ)) atTop
      (𝓝 ((ENNReal.ofReal κ • (volume : Measure ℝ)) (Icc 0 δ))) := by
  have hreal : Tendsto (fun L => (primeEndMeasure coef 0 L).real (Icc 0 δ)) atTop
      (𝓝 (κ * δ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun L => abs_primeEndMeasure_zero_Icc_sub_le_discrepancy hlaw L hδ)
      (tendsto_neutralDiscrepancy hlaw)
  have hval : (ENNReal.ofReal κ • (volume : Measure ℝ)) (Icc 0 δ) = ENNReal.ofReal (κ * δ) := by
    rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc, sub_zero,
      ← ENNReal.ofReal_mul hκ]
  rw [hval]
  refine (ENNReal.tendsto_ofReal hreal).congr fun L => ?_
  rw [measureReal_def, ENNReal.ofReal_toReal (primeEndMeasure_Icc_ne_top coef 0 L δ)]

/-- **End-tangent selection**: under an energy law with `κ > 0`, a finite nonzero end tangent
exists exactly at grade `a = 0`. -/
theorem hasFiniteNonzeroEndTangent_iff {coef : ℕ → ℂ} {κ C : ℝ}
    (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 < κ) (a : ℝ) :
    HasFiniteNonzeroEndTangent coef a ↔ a = 0 := by
  constructor
  · rintro ⟨ν, hfin, ⟨δ₀, hδ₀, hne⟩, hlim⟩
    by_contra ha
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · have h1 := hlim δ₀ hδ₀
      have h2 := tendsto_primeEndMeasure_Icc_of_neg hlaw hκ hneg hδ₀
      exact hfin δ₀ (tendsto_nhds_unique h1 h2)
    · have h1 := hlim δ₀ hδ₀
      have h2 : Tendsto (fun L => primeEndMeasure coef a L (Icc 0 δ₀)) atTop (𝓝 0) :=
        tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
          (tendsto_primeEndMeasure_univ_of_pos hlaw hκ.le hpos) (fun _ => bot_le)
          (fun L => measure_mono (subset_univ _))
      exact hne (tendsto_nhds_unique h1 h2)
  · rintro rfl
    refine ⟨ENNReal.ofReal κ • volume, fun δ => smul_volume_Icc_ne_top κ δ, ⟨1, one_pos, ?_⟩,
      fun δ hδ => tendsto_primeEndMeasure_zero_Icc hlaw hκ.le hδ.le⟩
    rw [Measure.smul_apply, smul_eq_mul, Real.volume_Icc, sub_zero, ENNReal.ofReal_one, mul_one]
    exact (ENNReal.ofReal_pos.mpr hκ).ne'

/-- **The functional-equation selection law**: the orientations `a` and `-a` both have finite
nonzero end tangents iff `a = 0`. -/
theorem hasFiniteNonzeroEndTangent_both_iff {coef : ℕ → ℂ} {κ C : ℝ}
    (hlaw : HasPrimeEnergyLaw coef κ C) (hκ : 0 < κ) (a : ℝ) :
    HasFiniteNonzeroEndTangent coef a ∧ HasFiniteNonzeroEndTangent coef (-a) ↔ a = 0 := by
  rw [hasFiniteNonzeroEndTangent_iff hlaw hκ, hasFiniteNonzeroEndTangent_iff hlaw hκ, neg_eq_zero,
    and_self]

/-! ### The full prime-power Euler formation -/

/-- A prime power `p^{k+2}` of depth `m = k + 2 ≥ 2` beyond the end clock. -/
def IsEndPrimePower (L : ℝ) (q : ℕ × ℕ) : Prop :=
  q.1.Prime ∧ endClock L < (q.1 : ℝ) ^ (q.2 + 2)

theorem IsEndPrimePower.log_pos {L : ℝ} {q : ℕ × ℕ} (hq : IsEndPrimePower L q) :
    0 < Real.log q.1 :=
  Real.log_pos (by exact_mod_cast hq.1.one_lt)

theorem IsEndPrimePower.clock_pos {L : ℝ} {q : ℕ × ℕ} (hq : IsEndPrimePower L q) :
    0 < Real.log (((q.2 : ℝ) + 2) * Real.log q.1) - L := by
  have hn : (0 : ℝ) < q.1 := by exact_mod_cast hq.1.pos
  have h1 : Real.log (endClock L) < Real.log ((q.1 : ℝ) ^ (q.2 + 2)) :=
    Real.log_lt_log (endClock_pos L) hq.2
  rw [Real.log_pow, endClock, Real.log_exp] at h1
  push_cast at h1
  have h2 : Real.log (Real.exp L) < Real.log (((q.2 : ℝ) + 2) * Real.log q.1) :=
    Real.log_lt_log (Real.exp_pos L) h1
  rw [Real.log_exp] at h2
  linarith

open Classical in
/-- The clock coordinate `log (m log p) - L` of a depth-`m` prime power (zero elsewhere). -/
def higherEulerClock (L : ℝ) (q : ℕ × ℕ) : ℝ :=
  if IsEndPrimePower L q then Real.log (((q.2 : ℝ) + 2) * Real.log q.1) - L else 0

theorem higherEulerClock_nonneg (L : ℝ) (q : ℕ × ℕ) : 0 ≤ higherEulerClock L q := by
  unfold higherEulerClock
  split_ifs with h
  · exact h.clock_pos.le
  · exact le_rfl

open Classical in
/-- The literal unsquared Euler amplitude `p^{-m/2}/m · e^{-iτ m log p}` at depth `m = k + 2`. -/
def higherEulerCoeff (L τ : ℝ) (q : ℕ × ℕ) : ℂ :=
  if IsEndPrimePower L q then
    (((q.1 : ℝ) ^ (-(((q.2 : ℝ) + 2) / 2)) / ((q.2 : ℝ) + 2) : ℝ) : ℂ) *
      Complex.exp (-(((τ * (((q.2 : ℝ) + 2) * Real.log q.1) : ℝ)) : ℂ) * Complex.I)
  else 0

open Classical in
theorem norm_higherEulerCoeff_sq (L τ : ℝ) (q : ℕ × ℕ) :
    ‖higherEulerCoeff L τ q‖ ^ 2 =
      if IsEndPrimePower L q then (q.1 : ℝ) ^ (-((q.2 : ℝ) + 2)) / ((q.2 : ℝ) + 2) ^ 2 else 0 := by
  unfold higherEulerCoeff
  split_ifs with h
  · have hn : (0 : ℝ) ≤ q.1 := Nat.cast_nonneg _
    have hexp : ‖Complex.exp (-(((τ * (((q.2 : ℝ) + 2) * Real.log q.1) : ℝ)) : ℂ) *
        Complex.I)‖ = 1 := by
      rw [show -(((τ * (((q.2 : ℝ) + 2) * Real.log q.1) : ℝ)) : ℂ) * Complex.I =
        ((-(τ * (((q.2 : ℝ) + 2) * Real.log q.1)) : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I]
    have hm : (0 : ℝ) < (q.2 : ℝ) + 2 := by positivity
    rw [norm_mul, hexp, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.rpow_nonneg hn _) hm.le), div_pow,
      ← Real.rpow_mul_natCast hn]
    congr 2
    push_cast
    ring
  · simp

/-- The prime-power weight `p^{-m}/m²` at depth `m = k + 2`. -/
def eulerResidualWeight (q : ℕ × ℕ) : ℝ :=
  if q.1.Prime then (q.1 : ℝ) ^ (-((q.2 : ℝ) + 2)) / ((q.2 : ℝ) + 2) ^ 2 else 0

theorem eulerResidualWeight_nonneg (q : ℕ × ℕ) : 0 ≤ eulerResidualWeight q := by
  unfold eulerResidualWeight
  split_ifs
  · exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)
  · exact le_rfl

/-- **`∑_p ∑_{m ≥ 2} p^{-m}/m² < ∞`.** -/
theorem summable_eulerResidualWeight : Summable eulerResidualWeight := by
  have hbound : Summable fun q : ℕ × ℕ => (1 / (q.1 : ℝ) ^ 2) * (1 / 2 : ℝ) ^ q.2 :=
    Summable.mul_of_nonneg (Real.summable_one_div_nat_pow.mpr one_lt_two) summable_geometric_two
      (fun n => by positivity) (fun k => by positivity)
  refine Summable.of_nonneg_of_le eulerResidualWeight_nonneg (fun q => ?_) hbound
  unfold eulerResidualWeight
  split_ifs with hp
  · have hn2 : (2 : ℝ) ≤ q.1 := by exact_mod_cast hp.two_le
    have hn0 : (0 : ℝ) < q.1 := by linarith
    have hm : (1 : ℝ) ≤ ((q.2 : ℝ) + 2) ^ 2 := by nlinarith [(Nat.cast_nonneg q.2 : (0 : ℝ) ≤ q.2)]
    have hrpow : (q.1 : ℝ) ^ (-((q.2 : ℝ) + 2)) = 1 / (q.1 : ℝ) ^ 2 * (1 / (q.1 : ℝ)) ^ q.2 := by
      rw [show -((q.2 : ℝ) + 2) = -((q.2 + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hn0.le,
        Real.rpow_natCast, pow_add, one_div_pow]
      field_simp
    calc (q.1 : ℝ) ^ (-((q.2 : ℝ) + 2)) / ((q.2 : ℝ) + 2) ^ 2
        ≤ (q.1 : ℝ) ^ (-((q.2 : ℝ) + 2)) :=
          div_le_self (Real.rpow_nonneg hn0.le _) hm
      _ = 1 / (q.1 : ℝ) ^ 2 * (1 / (q.1 : ℝ)) ^ q.2 := hrpow
      _ ≤ 1 / (q.1 : ℝ) ^ 2 * (1 / 2) ^ q.2 := by
          gcongr
  · positivity

open Classical in
theorem norm_higherEulerCoeff_sq_le (L τ : ℝ) (q : ℕ × ℕ) :
    ‖higherEulerCoeff L τ q‖ ^ 2 ≤ eulerResidualWeight q := by
  rw [norm_higherEulerCoeff_sq]
  split_ifs with h
  · rw [eulerResidualWeight, if_pos h.1]
  · exact eulerResidualWeight_nonneg q

/-- The **residual Euler mass** `∑_{p^m > X_L, m ≥ 2} p^{-m}/m²`. -/
def eulerResidualMass (L : ℝ) : ℝ := ∑' q, ‖higherEulerCoeff L 0 q‖ ^ 2

theorem summable_norm_higherEulerCoeff_sq (L τ : ℝ) :
    Summable fun q => ‖higherEulerCoeff L τ q‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (norm_higherEulerCoeff_sq_le L τ)
    summable_eulerResidualWeight

theorem tsum_norm_higherEulerCoeff_sq (L τ : ℝ) :
    ∑' q, ‖higherEulerCoeff L τ q‖ ^ 2 = eulerResidualMass L := by
  unfold eulerResidualMass
  simp_rw [norm_higherEulerCoeff_sq]

/-- **The residual Euler boundary vanishes**: `eulerResidualMass L → 0`. -/
theorem tendsto_eulerResidualMass : Tendsto eulerResidualMass atTop (𝓝 0) := by
  classical
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun L q => ‖higherEulerCoeff L 0 q‖ ^ 2) (g := fun _ => (0 : ℝ))
    summable_eulerResidualWeight (fun q => ?_) (.of_forall fun L q => ?_)
  · simp only [tsum_zero] at h
    exact h
  · obtain ⟨L₀, hL₀⟩ := (tendsto_endClock.eventually_ge_atTop
      ((q.1 : ℝ) ^ (q.2 + 2))).exists_forall_of_atTop
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop L₀] with L hL
    rw [norm_higherEulerCoeff_sq, if_neg fun hq => absurd (hL₀ L hL) (not_le.mpr hq.2)]
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_higherEulerCoeff_sq_le L 0 q

namespace SobolevTranslateWindow

variable {h h' : ℝ → ℂ}

/-- The **residual Euler frame** of depths `m ≥ 2`. -/
def eulerResidualFrame (W : SobolevTranslateWindow h h') (L τ : ℝ) :
    ℕ × ℕ → Lp ℂ 2 (volume : Measure ℝ) :=
  translateSystem W.toL2 (higherEulerCoeff L τ) (higherEulerClock L)

theorem hasSum_norm_eulerResidualFrame_sq (W : SobolevTranslateWindow h h') (L τ : ℝ) :
    HasSum (fun q => ‖W.eulerResidualFrame L τ q‖ ^ 2) (‖W.toL2‖ ^ 2 * eulerResidualMass L) := by
  have hs := (summable_norm_higherEulerCoeff_sq L τ).hasSum
  rw [tsum_norm_higherEulerCoeff_sq] at hs
  have heq : (fun q => ‖W.eulerResidualFrame L τ q‖ ^ 2) =
      fun q => ‖W.toL2‖ ^ 2 * ‖higherEulerCoeff L τ q‖ ^ 2 := by
    funext q
    rw [eulerResidualFrame, translateSystem, norm_smul, norm_translateRight, mul_pow, mul_comm]
  rw [heq]
  exact hs.mul_left _

/-- The **full prime-power Euler frame**: the principal layer `m = 1` joined with all depths
`m ≥ 2`. -/
def fullEulerFrame (W : SobolevTranslateWindow h h') (L τ : ℝ) :
    ℕ ⊕ (ℕ × ℕ) → Lp ℂ 2 (volume : Measure ℝ) :=
  Sum.elim (W.endFrame (fun _ => 1) 0 L τ) (W.eulerResidualFrame L τ)

theorem isBesselFamily_eulerResidualFrame (W : SobolevTranslateWindow h h') (L τ : ℝ) :
    IsBesselFamily (W.eulerResidualFrame L τ) (∑' q, ‖W.eulerResidualFrame L τ q‖ ^ 2) :=
  isBesselFamily_of_summable_sq (W.hasSum_norm_eulerResidualFrame_sq L τ).summable

theorem isBesselFamily_fullEulerFrame (W : SobolevTranslateWindow h h') (L τ : ℝ) :
    IsBesselFamily (W.fullEulerFrame L τ)
      ((1 * (∫ x, ‖h x‖) ^ 2 + neutralDiscrepancy (fun _ => 1) 1 L *
          (2 * ((∫ x, ‖h x‖) * ∫ x, ‖h' x‖))) + ∑' q, ‖W.eulerResidualFrame L τ q‖ ^ 2) :=
  isBesselFamily_sumElim (W.isBesselFamily_endFrame_zero hasPrimeEnergyLaw_one zero_le_one L τ)
    (W.isBesselFamily_eulerResidualFrame L τ)

/-- The frame operator of the full Euler formation. -/
def fullEulerFrameOp (W : SobolevTranslateWindow h h') (L τ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  besselFrameOp _ (W.isBesselFamily_fullEulerFrame L τ)

/-- The residual frame operator of depths `m ≥ 2`. -/
def eulerResidualFrameOp (W : SobolevTranslateWindow h h') (L τ : ℝ) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  besselFrameOp _ (W.isBesselFamily_eulerResidualFrame L τ)

/-- **Principal plus residual**: `A^{full}_{0,L} = A_{0,L} + R_L`. -/
theorem fullEulerFrameOp_eq (W : SobolevTranslateWindow h h') (L τ : ℝ) :
    W.fullEulerFrameOp L τ =
      W.neutralEndFrameOp hasPrimeEnergyLaw_one zero_le_one L τ + W.eulerResidualFrameOp L τ :=
  besselFrameOp_sumElim _ _ _

/-- **Every depth `m ≥ 2` is trace class**, with `‖R_L‖₁ ≤ ‖h‖₂² ∑_{p^m > X_L, m ≥ 2} p^{-m}/m²`. -/
theorem eulerResidualFrameOp_traceClass (W : SobolevTranslateWindow h h') (L τ : ℝ) :
    _root_.RHTower.MemSchattenClass 1 (W.eulerResidualFrameOp L τ) ∧
      _root_.RHTower.traceNorm _ (W.eulerResidualFrameOp L τ) ≤
        ‖W.toL2‖ ^ 2 * eulerResidualMass L := by
  have hs := W.hasSum_norm_eulerResidualFrame_sq L τ
  obtain ⟨h1, h2⟩ := traceNorm_besselFrameOp_le (W.isBesselFamily_eulerResidualFrame L τ)
    hs.summable
  exact ⟨h1, h2.trans (le_of_eq hs.tsum_eq)⟩

theorem tendsto_traceNorm_eulerResidualFrameOp (W : SobolevTranslateWindow h h') (τ : ℝ) :
    Tendsto (fun L => _root_.RHTower.traceNorm _ (W.eulerResidualFrameOp L τ)) atTop (𝓝 0) := by
  have hup := tendsto_eulerResidualMass.const_mul (‖W.toL2‖ ^ 2)
  rw [mul_zero] at hup
  exact squeeze_zero (fun L => _root_.RHTower.traceNorm_nonneg _)
    (fun L => (W.eulerResidualFrameOp_traceClass L τ).2) hup

/-- **The full Euler formation has the same Haar tangent as its principal layer**:
`‖A^{full}_{0,L} - A_H‖ → 0`. -/
theorem tendsto_fullEulerFrameOp (W : SobolevTranslateWindow h h') (τ : ℝ) :
    Tendsto (fun L => ‖W.fullEulerFrameOp L τ - W.haarFrameOp‖) atTop (𝓝 0) := by
  have h1 := W.tendsto_neutralEndFrameOp hasPrimeEnergyLaw_one zero_le_one τ
  have h2 := W.tendsto_traceNorm_eulerResidualFrameOp τ
  have hsum := h1.add h2
  rw [add_zero] at hsum
  refine squeeze_zero (fun _ => norm_nonneg _) (fun L => ?_) hsum
  have hR : ‖W.eulerResidualFrameOp L τ‖ ≤
      _root_.RHTower.traceNorm _ (W.eulerResidualFrameOp L τ) :=
    _root_.RHTower.norm_le_traceNorm ((W.eulerResidualFrameOp_traceClass L τ).1.congr
      fun n => Real.rpow_one _)
  rw [fullEulerFrameOp_eq]
  calc ‖W.neutralEndFrameOp hasPrimeEnergyLaw_one zero_le_one L τ + W.eulerResidualFrameOp L τ -
        W.haarFrameOp‖
      = ‖(W.neutralEndFrameOp hasPrimeEnergyLaw_one zero_le_one L τ -
          ((1 : ℝ) : ℂ) • W.haarFrameOp) + W.eulerResidualFrameOp L τ‖ := by
        congr 1
        rw [Complex.ofReal_one, one_smul]
        abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add le_rfl hR)

end SobolevTranslateWindow

/-! ### The Poisson mother -/

/-- The derivative `F'(x) = 2 e^x e^{-e^x} (1 - e^x)` of the Poisson mother. -/
def poissonMotherDeriv (x : ℝ) : ℝ :=
  2 * Real.exp x * Real.exp (-Real.exp x) * (1 - Real.exp x)

theorem hasDerivAt_poissonLogScaleMother (x : ℝ) :
    HasDerivAt _root_.RHTower.poissonLogScaleMother (poissonMotherDeriv x) x := by
  have h1 := Real.hasDerivAt_exp x
  have h2 : HasDerivAt (fun y => Real.exp (-Real.exp y)) (Real.exp (-Real.exp x) * -Real.exp x) x :=
    h1.neg.exp
  have h3 := (h1.const_mul 2).mul h2
  show HasDerivAt (fun y => 2 * Real.exp y * Real.exp (-Real.exp y)) _ x
  refine h3.congr_deriv ?_
  unfold poissonMotherDeriv
  ring

theorem poissonLogScaleMother_pos (x : ℝ) : 0 < _root_.RHTower.poissonLogScaleMother x := by
  unfold _root_.RHTower.poissonLogScaleMother
  positivity

theorem poissonLogScaleMother_le_two_exp (x : ℝ) :
    _root_.RHTower.poissonLogScaleMother x ≤ 2 * Real.exp x := by
  unfold _root_.RHTower.poissonLogScaleMother
  have : Real.exp (-Real.exp x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.exp_pos x])
  have := Real.exp_pos x
  nlinarith

theorem poissonLogScaleMother_le_two_exp_neg {x : ℝ} (hx : 0 ≤ x) :
    _root_.RHTower.poissonLogScaleMother x ≤ 2 * Real.exp (-x) := by
  unfold _root_.RHTower.poissonLogScaleMother
  have hq := Real.quadratic_le_exp_of_nonneg hx
  have h1 : x + -Real.exp x ≤ -x := by nlinarith
  have h2 : Real.exp x * Real.exp (-Real.exp x) ≤ Real.exp (-x) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr h1
  linarith

theorem poissonLogScaleMother_le_two (x : ℝ) : _root_.RHTower.poissonLogScaleMother x ≤ 2 := by
  unfold _root_.RHTower.poissonLogScaleMother
  have h1 : x + -Real.exp x ≤ 0 := by linarith [Real.add_one_le_exp x]
  have h2 : Real.exp x * Real.exp (-Real.exp x) ≤ 1 := by
    rw [← Real.exp_add]
    exact Real.exp_le_one_iff.mpr h1
  linarith

theorem continuous_poissonLogScaleMother : Continuous _root_.RHTower.poissonLogScaleMother := by
  unfold _root_.RHTower.poissonLogScaleMother
  fun_prop

theorem continuous_poissonMotherDeriv : Continuous poissonMotherDeriv := by
  unfold poissonMotherDeriv
  fun_prop

theorem integrable_poissonLogScaleMother : Integrable _root_.RHTower.poissonLogScaleMother := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  constructor
  · refine ((integrableOn_exp_Iic 0).const_mul 2).mono'
      continuous_poissonLogScaleMother.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Iic).mpr (.of_forall fun x _ => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (poissonLogScaleMother_pos x)]
    exact poissonLogScaleMother_le_two_exp x
  · have hint : IntegrableOn (fun x => Real.exp (-1 * x)) (Ioi 0) :=
      exp_neg_integrableOn_Ioi 0 one_pos
    refine (hint.const_mul 2).mono' continuous_poissonLogScaleMother.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).mpr (.of_forall fun x hx => ?_))
    rw [Real.norm_eq_abs, abs_of_pos (poissonLogScaleMother_pos x), neg_one_mul]
    exact poissonLogScaleMother_le_two_exp_neg (le_of_lt hx)

theorem tendsto_poissonLogScaleMother_atTop :
    Tendsto _root_.RHTower.poissonLogScaleMother atTop (𝓝 0) := by
  have h : Tendsto (fun x => 2 * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul 2
  exact squeeze_zero' (.of_forall fun x => (poissonLogScaleMother_pos x).le)
    ((eventually_ge_atTop 0).mono fun x hx => poissonLogScaleMother_le_two_exp_neg hx) h

theorem tendsto_poissonLogScaleMother_atBot :
    Tendsto _root_.RHTower.poissonLogScaleMother atBot (𝓝 0) := by
  have h : Tendsto (fun x => 2 * Real.exp x) atBot (𝓝 0) := by
    simpa using Real.tendsto_exp_atBot.const_mul 2
  exact squeeze_zero (fun x => (poissonLogScaleMother_pos x).le) poissonLogScaleMother_le_two_exp h

/-- `‖F‖₁ = 2`. -/
theorem integral_poissonLogScaleMother : ∫ x, _root_.RHTower.poissonLogScaleMother x = 2 := by
  have hG : ∀ x, HasDerivAt (fun y => -2 * Real.exp (-Real.exp y))
      (_root_.RHTower.poissonLogScaleMother x) x := by
    intro x
    have h := (((Real.hasDerivAt_exp x).neg).exp).const_mul (-2)
    refine h.congr_deriv ?_
    unfold _root_.RHTower.poissonLogScaleMother
    simp only [Pi.neg_apply]
    ring
  have hbot : Tendsto (fun y => -2 * Real.exp (-Real.exp y)) atBot (𝓝 (-2)) := by
    have h1 : Tendsto (fun y => Real.exp (-Real.exp y)) atBot (𝓝 1) := by
      have h0 : Tendsto (fun y => -Real.exp y) atBot (𝓝 0) := by
        simpa using Real.tendsto_exp_atBot.neg
      have := (Real.continuous_exp.tendsto 0).comp h0
      simpa [Function.comp_def] using this
    simpa using h1.const_mul (-2)
  have htop : Tendsto (fun y => -2 * Real.exp (-Real.exp y)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp Real.tendsto_exp_atTop).const_mul (-2)
    simpa [Function.comp_def] using this
  rw [integral_of_hasDerivAt_of_tendsto hG integrable_poissonLogScaleMother hbot htop]
  ring

theorem poissonMotherDeriv_nonneg_of_nonpos {x : ℝ} (hx : x ≤ 0) : 0 ≤ poissonMotherDeriv x := by
  unfold poissonMotherDeriv
  have : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hx
  have := poissonLogScaleMother_pos x
  unfold _root_.RHTower.poissonLogScaleMother at this
  exact mul_nonneg this.le (by linarith)

theorem poissonMotherDeriv_nonpos_of_nonneg {x : ℝ} (hx : 0 ≤ x) : poissonMotherDeriv x ≤ 0 := by
  unfold poissonMotherDeriv
  have : 1 ≤ Real.exp x := Real.one_le_exp hx
  have := poissonLogScaleMother_pos x
  unfold _root_.RHTower.poissonLogScaleMother at this
  exact mul_nonpos_of_nonneg_of_nonpos this.le (by linarith)

theorem abs_poissonMotherDeriv_le_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    |poissonMotherDeriv x| ≤ 2 * Real.exp x := by
  rw [abs_of_nonneg (poissonMotherDeriv_nonneg_of_nonpos hx)]
  refine le_trans ?_ (poissonLogScaleMother_le_two_exp x)
  unfold poissonMotherDeriv _root_.RHTower.poissonLogScaleMother
  have h1 : 0 < 2 * Real.exp x * Real.exp (-Real.exp x) := by positivity
  have h2 : 0 < Real.exp x := Real.exp_pos x
  nlinarith

theorem integrableOn_poissonMotherDeriv_Iic : IntegrableOn poissonMotherDeriv (Iic 0) :=
  ((integrableOn_exp_Iic 0).const_mul 2).mono' continuous_poissonMotherDeriv.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Iic).mpr (.of_forall fun _ hx =>
      abs_poissonMotherDeriv_le_of_nonpos hx))

theorem integrableOn_poissonMotherDeriv_Ioi : IntegrableOn poissonMotherDeriv (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonpos continuous_poissonLogScaleMother.continuousWithinAt
    (fun x _ => hasDerivAt_poissonLogScaleMother x)
    (fun _ hx => poissonMotherDeriv_nonpos_of_nonneg (le_of_lt hx))
    tendsto_poissonLogScaleMother_atTop

theorem integrable_poissonMotherDeriv : Integrable poissonMotherDeriv := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨integrableOn_poissonMotherDeriv_Iic, integrableOn_poissonMotherDeriv_Ioi⟩

theorem poissonLogScaleMother_zero : _root_.RHTower.poissonLogScaleMother 0 = 2 / Real.exp 1 := by
  unfold _root_.RHTower.poissonLogScaleMother
  rw [Real.exp_zero, mul_one, Real.exp_neg]
  ring

/-- `‖F'‖₁ = 4/e`. -/
theorem integral_abs_poissonMotherDeriv : ∫ x, |poissonMotherDeriv x| = 4 / Real.exp 1 := by
  rw [← setIntegral_univ, ← Iic_union_Ioi (a := (0 : ℝ)),
    setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi
      integrableOn_poissonMotherDeriv_Iic.abs integrableOn_poissonMotherDeriv_Ioi.abs]
  have hI : ∫ x in Iic 0, |poissonMotherDeriv x| = 2 / Real.exp 1 := by
    rw [setIntegral_congr_fun measurableSet_Iic fun x hx =>
      abs_of_nonneg (poissonMotherDeriv_nonneg_of_nonpos hx),
      integral_Iic_of_hasDerivAt_of_tendsto continuous_poissonLogScaleMother.continuousWithinAt
        (fun x _ => hasDerivAt_poissonLogScaleMother x) integrableOn_poissonMotherDeriv_Iic
        tendsto_poissonLogScaleMother_atBot, sub_zero, poissonLogScaleMother_zero]
  have hJ : ∫ x in Ioi 0, |poissonMotherDeriv x| = 2 / Real.exp 1 := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx =>
      abs_of_nonpos (poissonMotherDeriv_nonpos_of_nonneg (le_of_lt hx)), integral_neg,
      integral_Ioi_of_hasDerivAt_of_nonpos continuous_poissonLogScaleMother.continuousWithinAt
        (fun x _ => hasDerivAt_poissonLogScaleMother x)
        (fun _ hx => poissonMotherDeriv_nonpos_of_nonneg (le_of_lt hx))
        tendsto_poissonLogScaleMother_atTop, zero_sub, neg_neg, poissonLogScaleMother_zero]
  rw [hI, hJ]
  ring

/-- **The Poisson mother is a `W^{1,1} ∩ L²` window.** -/
theorem poissonMotherWindow :
    SobolevTranslateWindow (fun x => (_root_.RHTower.poissonLogScaleMother x : ℂ))
      (fun x => (poissonMotherDeriv x : ℂ)) where
  integrable := integrable_poissonLogScaleMother.ofReal
  memLp_two := by
    refine (memLp_two_iff_integrable_sq_norm
      (Complex.continuous_ofReal.comp continuous_poissonLogScaleMother).aestronglyMeasurable).mpr ?_
    refine (integrable_poissonLogScaleMother.const_mul 2).mono'
      ((Complex.continuous_ofReal.comp
        continuous_poissonLogScaleMother).norm.pow 2).aestronglyMeasurable
      (.of_forall fun x => ?_)
    simp only [Function.comp_apply, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (poissonLogScaleMother_pos x)]
    rw [sq]
    exact mul_le_mul_of_nonneg_right (poissonLogScaleMother_le_two x)
      (poissonLogScaleMother_pos x).le
  integrable_deriv := integrable_poissonMotherDeriv.ofReal
  sub_eq_integral x y := by
    rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hasDerivAt_poissonLogScaleMother t)
      (continuous_poissonMotherDeriv.intervalIntegrable x y)]
    push_cast
    ring

theorem poissonMotherWindow_toL2_ne_zero : poissonMotherWindow.toL2 ≠ 0 := by
  intro h0
  have hae : (fun x => (_root_.RHTower.poissonLogScaleMother x : ℂ)) =ᵐ[volume] 0 :=
    poissonMotherWindow.coeFn_toL2.symm.trans (Lp.eq_zero_iff_ae_eq_zero.mp h0)
  have hnull : volume {x : ℝ | (_root_.RHTower.poissonLogScaleMother x : ℂ) ≠ 0} = 0 :=
    ae_iff.mp hae
  have hall : {x : ℝ | (_root_.RHTower.poissonLogScaleMother x : ℂ) ≠ 0} = univ := by
    ext x
    simp only [mem_setOf_eq, mem_univ, iff_true, ne_eq, Complex.ofReal_eq_zero]
    exact (poissonLogScaleMother_pos x).ne'
  rw [hall, Real.volume_univ] at hnull
  exact ENNReal.top_ne_zero hnull

theorem integral_norm_poissonMotherWindow :
    ∫ x, ‖(_root_.RHTower.poissonLogScaleMother x : ℂ)‖ = 2 := by
  simp_rw [Complex.norm_real, Real.norm_eq_abs]
  rw [← integral_poissonLogScaleMother]
  exact integral_congr_ae (.of_forall fun x => abs_of_pos (poissonLogScaleMother_pos x))

theorem integral_norm_poissonMotherWindow_deriv :
    ∫ x, ‖(poissonMotherDeriv x : ℂ)‖ = 4 / Real.exp 1 := by
  simp_rw [Complex.norm_real, Real.norm_eq_abs]
  exact integral_abs_poissonMotherDeriv

/-- **The Poisson-mother neutral bound**: `‖A_{0,L} - A_H‖ ≤ (16/e) ε_L`. -/
theorem poissonMother_neutral_bound (L τ : ℝ) :
    ‖poissonMotherWindow.neutralEndFrameOp hasPrimeEnergyLaw_one zero_le_one L τ -
        ((1 : ℝ) : ℂ) • poissonMotherWindow.haarFrameOp‖ ≤
      neutralDiscrepancy (fun _ => 1) 1 L * (16 / Real.exp 1) := by
  refine (poissonMotherWindow.norm_neutralEndFrameOp_sub_le hasPrimeEnergyLaw_one zero_le_one
    L τ).trans (le_of_eq ?_)
  rw [integral_norm_poissonMotherWindow, integral_norm_poissonMotherWindow_deriv]
  ring

/-! ### The trichotomy and the route-independent instance -/

namespace SobolevTranslateWindow

variable {h h' : ℝ → ℂ}

/-- **The prime-harmonic Haar-frame trichotomy** for the literal Euler coefficients and any
nonzero `W^{1,1} ∩ L²` window:
* `a = 0`: `‖A_{0,L} - A_H‖ ≤ 2 ε_L ‖h‖₁ ‖h'‖₁ → 0`, with `A_H ≠ 0`;
* `a > 0`: `A_{a,L}` is trace class and `‖A_{a,L}‖₁ → 0`;
* `a < 0`: the frame operator of every fixed end window `[0, δ]` has norm `→ ∞`. -/
theorem primeHarmonicHaarFrameTrichotomy (W : SobolevTranslateWindow h h') (hw : W.toL2 ≠ 0)
    (τ : ℝ) :
    (∀ L, ‖W.neutralEndFrameOp hasPrimeEnergyLaw_one zero_le_one L τ -
        ((1 : ℝ) : ℂ) • W.haarFrameOp‖ ≤
      neutralDiscrepancy (fun _ => 1) 1 L * (2 * ((∫ x, ‖h x‖) * ∫ x, ‖h' x‖))) ∧
    Tendsto (fun L => ‖W.neutralEndFrameOp hasPrimeEnergyLaw_one zero_le_one L τ -
        ((1 : ℝ) : ℂ) • W.haarFrameOp‖) atTop (𝓝 0) ∧
    W.haarFrameOp ≠ 0 ∧
    (∀ a (ha : 0 < a), Tendsto (fun L => _root_.RHTower.traceNorm _
        (W.positiveEndFrameOp hasPrimeEnergyLaw_one zero_le_one ha L τ)) atTop (𝓝 0)) ∧
    (∀ a, a < 0 → ∀ δ, 0 < δ →
      Tendsto (fun L => ‖W.endWindowFrameOp (fun _ => 1) a L τ δ‖) atTop atTop) :=
  ⟨fun L => W.norm_neutralEndFrameOp_sub_le hasPrimeEnergyLaw_one zero_le_one L τ,
    W.tendsto_neutralEndFrameOp hasPrimeEnergyLaw_one zero_le_one τ,
    W.haarFrameOp_ne_zero hw,
    fun _ ha => W.tendsto_traceNorm_positiveEndFrameOp hasPrimeEnergyLaw_one zero_le_one ha τ,
    fun _ ha _ hδ => W.tendsto_norm_endWindowFrameOp hw hasPrimeEnergyLaw_one one_pos ha τ hδ⟩

/-- **The route-independent prediction for Dirichlet characters**: the twisted end frames have the
same Haar tangent, `‖A^χ_{0,L} - A_H‖ → 0`. -/
theorem tendsto_dirichletEndFrameOp (W : SobolevTranslateWindow h h') {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (τ : ℝ) :
    Tendsto (fun L => ‖W.neutralEndFrameOp (hasPrimeEnergyLaw_dirichletCharacter χ) zero_le_one
        L τ - ((1 : ℝ) : ℂ) • W.haarFrameOp‖) atTop (𝓝 0) :=
  W.tendsto_neutralEndFrameOp _ _ τ

end SobolevTranslateWindow

end GaloisForLFunctions.HTGeometry
