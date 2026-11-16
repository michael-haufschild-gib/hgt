import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing
import GaloisForLFunctions.RHTower.XiSliceEventualPositivityFiniteOffLine
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The zero Parseval identity of the critical state

The Gaussian-summed zero norm of the critical state `F`,
`S(ε) = Σ_z L F(z) L F(−z) e^{εz²} → −a ∫ F² e^{−8u}` (`criticalState_tendsto_zeroNorm`), splits
into the zeros on the line (`Re z = 0`) and those off it. On the line `−z = z̄` and `F` is real, so
a term is `e^{−ε (Im z)²} |L F(z)|²`: nonnegative, at most `|L F(z)|²`, increasing as `ε ↓ 0`.

* **Equivalence** (`criticalState_onLine_summable_iff`). The on-line zero values are square-summable
  exactly when the off-line part of `S(ε)` converges as `ε → 0⁺`; then
  `Σ_{on} |L F(z)|² + lim_{ε→0⁺} Σ_{off} = −a ∫ F² e^{−8u}`
  (`criticalState_onLine_parseval_of_tendsto`, `criticalState_tendsto_offLine_of_summable`).
* **A finite layer** (`criticalState_zeroParseval_of_finiteOffLine`). With finitely many zero copies
  off the line the off-line part is a finite sum, so
  `Σ_{on} |L F(z)|² + Σ_{off} L F(z) L F(−z) = −a ∫ F² e^{−8u}`, and the off-line block carries the
  whole negative mass (`criticalState_re_offLine_le_of_finiteOffLine`).
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### On-line terms -/

/-- The zero copies on the critical line: centred coordinate with real part `0`. -/
def onLineCopies : Set XiZeroCopy := {q | (centredZero q).re = 0}

/-- The term `L F(z) L F(−z) e^{εz²}` of the Gaussian-summed zero norm at one copy. -/
def zeroNormTerm (F : ℝ → ℝ) (ε : ℝ) (q : XiZeroCopy) : ℂ :=
  negativeHalfLineLaplace (cx F) (centredZero q) *
    negativeHalfLineLaplace (cx F) (-centredZero q) * Complex.exp ((ε : ℂ) * centredZero q ^ 2)

/-- The squared zero value `|L F(z)|²` at one copy. -/
def zeroValueMass (F : ℝ → ℝ) (q : XiZeroCopy) : ℝ :=
  ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ ^ 2

/-- The Gaussian weight `e^{−ε (Im z)²}` of an on-line copy. -/
def onLineWeight (ε : ℝ) (q : XiZeroCopy) : ℝ := Real.exp (-(ε * (centredZero q).im ^ 2))

theorem zeroValueMass_nonneg (F : ℝ → ℝ) (q : XiZeroCopy) : 0 ≤ zeroValueMass F q :=
  sq_nonneg _

theorem onLineWeight_pos (ε : ℝ) (q : XiZeroCopy) : 0 < onLineWeight ε q := Real.exp_pos _

theorem onLineWeight_le_one {ε : ℝ} (hε : 0 ≤ ε) (q : XiZeroCopy) : onLineWeight ε q ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hε (sq_nonneg _)))

/-- On the line `−z = z̄`, so the term is `e^{−ε (Im z)²} |L F(z)|²`. -/
theorem zeroNormTerm_of_mem_onLineCopies (F : ℝ → ℝ) (ε : ℝ) {q : XiZeroCopy}
    (hq : q ∈ onLineCopies) :
    zeroNormTerm F ε q = ((onLineWeight ε q * zeroValueMass F q : ℝ) : ℂ) := by
  have hre : (centredZero q).re = 0 := hq
  have hneg : -centredZero q = (starRingEnd ℂ) (centredZero q) := by
    apply Complex.ext <;> simp [hre]
  have hsq : (ε : ℂ) * centredZero q ^ 2 = ((-(ε * (centredZero q).im ^ 2) : ℝ) : ℂ) := by
    apply Complex.ext <;> simp [sq, hre]
  unfold zeroNormTerm onLineWeight zeroValueMass
  rw [hneg, show cx F = fun u => (F u : ℂ) from rfl, negativeHalfLineLaplace_real_conj,
    Complex.mul_conj', hsq, ← Complex.ofReal_exp]
  push_cast
  ring

/-! ### Splitting the zero norm -/

variable {W₀ : ℝ} {F : ℝ → ℝ}

/-- The confinement value `−a ∫ F² e^{−8u}`, the limit of the zero norm. -/
def stateZeroNormLimit (W₀ : ℝ) (F : ℝ → ℝ) : ℝ :=
  -(criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)))

theorem criticalState_summable_zeroNormTerm (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    (hF : IsCriticalHalfLineGroundState W₀ F) {ε : ℝ} (hε : 0 < ε) :
    Summable (zeroNormTerm F ε) :=
  (criticalState_hasSum_zeroPairing_heated hW ht hF
    (criticalHalfLineEnergyDomain_of_groundState hF) hε).summable

theorem criticalState_tendsto_tsum_zeroNormTerm (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    (hF : IsCriticalHalfLineGroundState W₀ F) :
    Tendsto (fun ε : ℝ => ∑' q, zeroNormTerm F ε q) (𝓝[>] 0)
      (𝓝 ((stateZeroNormLimit W₀ F : ℝ) : ℂ)) :=
  criticalState_tendsto_zeroNorm hW ht hF

/-- The weighted on-line masses are summable wherever the zero norm is. -/
theorem summable_onLine_of_summable {ε : ℝ} (hs : Summable (zeroNormTerm F ε)) :
    Summable fun q : onLineCopies => onLineWeight ε q * zeroValueMass F q := by
  rw [← Complex.summable_ofReal]
  exact (hs.subtype (· ∈ onLineCopies)).congr fun q => zeroNormTerm_of_mem_onLineCopies F ε q.2

/-- The zero norm is its real on-line part plus its off-line part. -/
theorem tsum_zeroNormTerm_eq_onLine_add {ε : ℝ} (hs : Summable (zeroNormTerm F ε)) :
    ∑' q, zeroNormTerm F ε q =
      ((∑' q : onLineCopies, onLineWeight ε q * zeroValueMass F q : ℝ) : ℂ) +
        ∑' q : ↑onLineCopiesᶜ, zeroNormTerm F ε q := by
  rw [← hs.tsum_subtype_add_tsum_subtype_compl onLineCopies, Complex.ofReal_tsum]
  congr 1
  exact tsum_congr fun q => zeroNormTerm_of_mem_onLineCopies F ε q.2

/-- Each on-line weight tends to `1` as `ε → 0⁺`. -/
theorem tendsto_onLineWeight (q : XiZeroCopy) :
    Tendsto (fun ε : ℝ => onLineWeight ε q) (𝓝[>] 0) (𝓝 1) := by
  have hc : Continuous fun ε : ℝ => onLineWeight ε q := by
    unfold onLineWeight; fun_prop
  have h := hc.tendsto 0
  simp only [onLineWeight, zero_mul, neg_zero, Real.exp_zero] at h
  exact h.mono_left nhdsWithin_le_nhds

/-! ### The Parseval identity -/

/-- **Off-line convergence gives on-line square-summability and the Parseval identity.** If the
off-line part of the zero norm converges to `L` as `ε → 0⁺`, the on-line zero values are
square-summable and `Σ_{on} |L F(z)|² + L = −a ∫ F² e^{−8u}`. -/
theorem criticalState_onLine_parseval_of_tendsto (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    (hF : IsCriticalHalfLineGroundState W₀ F) {L : ℂ}
    (hL : Tendsto (fun ε : ℝ => ∑' q : ↑onLineCopiesᶜ, zeroNormTerm F ε q) (𝓝[>] 0) (𝓝 L)) :
    Summable (fun q : onLineCopies => zeroValueMass F q) ∧
      ((∑' q : onLineCopies, zeroValueMass F q : ℝ) : ℂ) + L = (stateZeroNormLimit W₀ F : ℂ) := by
  set V : ℂ := (stateZeroNormLimit W₀ F : ℂ)
  let R : ℝ → ℝ := fun ε => ∑' q : onLineCopies, onLineWeight ε q * zeroValueMass F q
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  -- the real on-line part converges to `V − L`
  have hR : Tendsto (fun ε => (R ε : ℂ)) (𝓝[>] 0) (𝓝 (V - L)) := by
    refine ((criticalState_tendsto_tsum_zeroNormTerm hW ht hF).sub hL).congr' ?_
    filter_upwards [hpos] with ε hε
    rw [tsum_zeroNormTerm_eq_onLine_add (criticalState_summable_zeroNormTerm hW ht hF hε)]
    ring
  have hRre : Tendsto R (𝓝[>] 0) (𝓝 (V - L).re) :=
    Tendsto.congr (fun ε => by simp only [Function.comp_apply, Complex.ofReal_re])
      ((Complex.continuous_re.tendsto _).comp hR)
  have him : (V - L).im = 0 := by
    have h := (Complex.continuous_im.tendsto _).comp hR
    simp only [Function.comp_def, Complex.ofReal_im] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  set M := (V - L).re
  -- every finite on-line block is at most `M`
  have hblock : ∀ T : Finset onLineCopies, ∑ q ∈ T, zeroValueMass F q ≤ M := by
    intro T
    have hT : Tendsto (fun ε => ∑ q ∈ T, onLineWeight ε q * zeroValueMass F q) (𝓝[>] 0)
        (𝓝 (∑ q ∈ T, zeroValueMass F q)) := by
      refine tendsto_finsetSum T fun q _ => ?_
      simpa using (tendsto_onLineWeight (q : XiZeroCopy)).mul_const (zeroValueMass F q)
    refine le_of_tendsto_of_tendsto hT hRre ?_
    filter_upwards [hpos] with ε hε
    exact (summable_onLine_of_summable (criticalState_summable_zeroNormTerm hW ht hF hε)).sum_le_tsum
      T fun q _ => mul_nonneg (onLineWeight_pos ε q).le (zeroValueMass_nonneg F q)
  have hsum : Summable (fun q : onLineCopies => zeroValueMass F q) :=
    summable_of_sum_le (fun q => zeroValueMass_nonneg F q) hblock
  have hle : ∑' q : onLineCopies, zeroValueMass F q ≤ M :=
    Real.tsum_le_of_sum_le (fun q => zeroValueMass_nonneg F q) hblock
  have hge : M ≤ ∑' q : onLineCopies, zeroValueMass F q := by
    refine le_of_tendsto hRre ?_
    filter_upwards [hpos] with ε hε
    refine (summable_onLine_of_summable
      (criticalState_summable_zeroNormTerm hW ht hF hε)).tsum_le_tsum (fun q => ?_) hsum
    exact mul_le_of_le_one_left (zeroValueMass_nonneg F q) (onLineWeight_le_one hε.le q)
  refine ⟨hsum, ?_⟩
  have hM : ((M : ℝ) : ℂ) = V - L := Complex.ext (by simp [M]) (by simp [him])
  rw [le_antisymm hle hge, hM]
  ring

/-- **On-line square-summability gives off-line convergence.** If the on-line zero values are
square-summable, the off-line part of the zero norm converges to
`−a ∫ F² e^{−8u} − Σ_{on} |L F(z)|²`. -/
theorem criticalState_tendsto_offLine_of_summable (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    (hF : IsCriticalHalfLineGroundState W₀ F)
    (hs : Summable (fun q : onLineCopies => zeroValueMass F q)) :
    Tendsto (fun ε : ℝ => ∑' q : ↑onLineCopiesᶜ, zeroNormTerm F ε q) (𝓝[>] 0)
      (𝓝 ((stateZeroNormLimit W₀ F : ℂ) - ((∑' q : onLineCopies, zeroValueMass F q : ℝ) : ℂ))) := by
  have hpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε := self_mem_nhdsWithin
  -- dominated convergence for the on-line part, bounded by the masses
  have hR : Tendsto (fun ε : ℝ => ∑' q : onLineCopies, onLineWeight ε q * zeroValueMass F q)
      (𝓝[>] 0) (𝓝 (∑' q : onLineCopies, zeroValueMass F q)) := by
    refine tendsto_tsum_of_dominated_convergence hs (fun q => ?_) ?_
    · simpa using (tendsto_onLineWeight (q : XiZeroCopy)).mul_const (zeroValueMass F q)
    · filter_upwards [hpos] with ε hε q
      rw [Real.norm_of_nonneg (mul_nonneg (onLineWeight_pos ε q).le (zeroValueMass_nonneg F q))]
      exact mul_le_of_le_one_left (zeroValueMass_nonneg F q) (onLineWeight_le_one hε.le q)
  refine ((criticalState_tendsto_tsum_zeroNormTerm hW ht hF).sub
    ((Complex.continuous_ofReal.tendsto _).comp hR)).congr' ?_
  filter_upwards [hpos] with ε hε
  simp only [Function.comp_def]
  rw [tsum_zeroNormTerm_eq_onLine_add (criticalState_summable_zeroNormTerm hW ht hF hε)]
  ring

/-- **The on-line zero values are square-summable exactly when the off-line part of the zero norm
converges.** -/
theorem criticalState_onLine_summable_iff (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    (hF : IsCriticalHalfLineGroundState W₀ F) :
    Summable (fun q : onLineCopies => zeroValueMass F q) ↔
      ∃ L : ℂ, Tendsto (fun ε : ℝ => ∑' q : ↑onLineCopiesᶜ, zeroNormTerm F ε q) (𝓝[>] 0) (𝓝 L) :=
  ⟨fun hs => ⟨_, criticalState_tendsto_offLine_of_summable hW ht hF hs⟩,
    fun ⟨_, hL⟩ => (criticalState_onLine_parseval_of_tendsto hW ht hF hL).1⟩

/-! ### A finite layer -/

/-- A copy is off the line exactly when its spectral point is not real. -/
theorem compl_onLineCopies_finite_of_finiteOffLine (h : BacklundConverse.FiniteOffLine) :
    (onLineCopiesᶜ).Finite := by
  refine h.subset fun q hq h0 => hq ?_
  have him : (xiSpectralPoint q).im = -(centredZero q).re := by
    simp [xiSpectralPoint, centredZero, Complex.mul_im]
  change (centredZero q).re = 0
  linarith

/-- With finitely many copies off the line the off-line part of the zero norm converges to
`Σ_{off} L F(z) L F(−z)`. -/
theorem tendsto_offLine_of_finite (hfin : (onLineCopiesᶜ).Finite) :
    Tendsto (fun ε : ℝ => ∑' q : ↑onLineCopiesᶜ, zeroNormTerm F ε q) (𝓝[>] 0)
      (𝓝 (∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q))) := by
  haveI := hfin.to_subtype
  let c : XiZeroCopy → ℂ := fun q =>
    negativeHalfLineLaplace (cx F) (centredZero q) * negativeHalfLineLaplace (cx F) (-centredZero q)
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Ioo (0 : ℝ) 1 :=
    inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds one_pos))
  refine tendsto_tsum_of_dominated_convergence (bound := fun q : ↑onLineCopiesᶜ =>
      ‖c q‖ * Real.exp |(centredZero q ^ 2).re|) Summable.of_finite (fun q => ?_) ?_
  · have hc : Continuous fun ε : ℝ => c q * Complex.exp ((ε : ℂ) * centredZero q ^ 2) := by
      fun_prop
    have h := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [hsmall] with ε hε q
    change ‖c q * Complex.exp ((ε : ℂ) * centredZero q ^ 2)‖ ≤ _
    rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    calc ε * (centredZero q ^ 2).re ≤ ε * |(centredZero q ^ 2).re| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hε.1.le
      _ ≤ 1 * |(centredZero q ^ 2).re| := mul_le_mul_of_nonneg_right hε.2.le (abs_nonneg _)
      _ = |(centredZero q ^ 2).re| := one_mul _

/-- **The zero Parseval identity of a finite layer.** If only finitely many zero copies lie off the
line, the on-line zero values of the critical state are square-summable and
`Σ_{on} |L F(z)|² + Σ_{off} L F(z) L F(−z) = −a ∫ F² e^{−8u}`. -/
theorem criticalState_zeroParseval_of_finiteOffLine (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    (hF : IsCriticalHalfLineGroundState W₀ F) (hfin : BacklundConverse.FiniteOffLine) :
    Summable (fun q : onLineCopies => zeroValueMass F q) ∧
      ((∑' q : onLineCopies, zeroValueMass F q : ℝ) : ℂ) +
        ∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx F) (-centredZero q) = (stateZeroNormLimit W₀ F : ℂ) :=
  criticalState_onLine_parseval_of_tendsto hW ht hF
    (tendsto_offLine_of_finite (compl_onLineCopies_finite_of_finiteOffLine hfin))

/-- Under a finite layer the off-line block carries the whole negative mass:
`Re Σ_{off} L F(z) L F(−z) ≤ −a ∫ F² e^{−8u} < 0`. -/
theorem criticalState_re_offLine_le_of_finiteOffLine (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    (hF : IsCriticalHalfLineGroundState W₀ F) (hfin : BacklundConverse.FiniteOffLine) :
    (∑' q : ↑onLineCopiesᶜ, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx F) (-centredZero q)).re ≤ stateZeroNormLimit W₀ F := by
  obtain ⟨-, h⟩ := criticalState_zeroParseval_of_finiteOffLine hW ht hF hfin
  have hre := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re] at hre
  have hnn : 0 ≤ ∑' q : onLineCopies, zeroValueMass F q :=
    tsum_nonneg fun q => zeroValueMass_nonneg F q
  linarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
