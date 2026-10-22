import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixCompleteIntegrandAdmission

/-!
# The original regulator--depth crossover

The actual admitted Gamma-six tail operator retains a joint regulator/depth factor
`6^(-M*epsilon)`. Exact original-coordinate Gibbs sums are identified with integrals
of the complete regulated source before summation and limit interchange.

For positive regulators tending to zero, division by the explicit attenuation
recovers the original nonzero normalized boundary coefficient. A finite limit of
`M*epsilon` retains the corresponding nonzero exponential multiple; divergence to
infinity suppresses the normalized measurement. Finite diagonal repairs preserve
the literal regulated reader after sufficiently late original cutoffs. Every Xi
divisor retains its adjacent zero/nonzero internal conormal pair along every such
regulator path, including paths with a vanishing joint limiting measurement.

This is a source-side classification. It does not identify the source reader with
the fixed Burnol/Deninger reader at an original horizontal anchor or prove RH.
-/

open Complex Real Filter Topology
open scoped BigOperators
namespace RHTower
noncomputable section

/-- Gibbs shell with its starting depth factor removed, retaining every original coordinate. -/
def deningerGammaSixNormalizedGibbsShell (m : ℕ) (ε : ℝ) : ℝ :=
  ∑ a ∈ Finset.Ico (6 ^ m : ℕ) (6 ^ (m + 1)),
    if 6 ∣ a then (((a : ℝ) / (6 : ℝ) ^ m) ^ (-ε)) * (a : ℝ)⁻¹ else 0

theorem deningerGammaSixNormalizedGibbsShell_bounds
    (m : ℕ) (hm : 1 ≤ m) {ε : ℝ} (hε : 0 ≤ ε) :
    (6 : ℝ) ^ (-ε) * deningerGammaSixDivisibleShellMass (m - 1) ≤
      deningerGammaSixNormalizedGibbsShell m ε ∧
    deningerGammaSixNormalizedGibbsShell m ε ≤ deningerGammaSixDivisibleShellMass (m - 1) := by
  classical
  have hratio (a : ℕ) (ha : a ∈ Finset.Ico (6 ^ m) (6 ^ (m + 1))) :
      1 ≤ (a : ℝ) / (6 : ℝ) ^ m ∧ (a : ℝ) / (6 : ℝ) ^ m ≤ 6 := by
    have hlo : (6 : ℝ) ^ m ≤ (a : ℝ) := by exact_mod_cast (Finset.mem_Ico.1 ha).1
    have hhi : (a : ℝ) ≤ (6 : ℝ) ^ (m + 1) := by exact_mod_cast (Finset.mem_Ico.1 ha).2.le
    constructor
    · rw [le_div_iff₀ (by positivity), one_mul]
      exact hlo
    · rw [div_le_iff₀ (by positivity)]
      simpa only [pow_succ, mul_comm] using hhi
  rw [← deningerGammaSixDivisibleShellMass_eq_sum m hm]
  unfold deningerGammaSixNormalizedGibbsShell
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a ha
    split_ifs with hd
    · exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one (hratio a ha).1)
          (hratio a ha).2 (neg_nonpos.mpr hε)) (by positivity)
    · simp
  · apply Finset.sum_le_sum
    intro a ha
    split_ifs with hd
    · exact mul_le_of_le_one_left (by positivity)
        (Real.rpow_le_one_of_one_le_of_nonpos (hratio a ha).1 (neg_nonpos.mpr hε))
    · exact le_rfl

theorem tendsto_deningerGammaSixNormalizedGibbsShell_joint
    (d : ℕ → ℕ) (ε : ℕ → ℝ) (hd : Tendsto d atTop atTop)
    (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ᶠ M : ℕ in atTop, 0 ≤ ε M) :
    Tendsto (fun M => deningerGammaSixNormalizedGibbsShell (d M) (ε M)) atTop
      (𝓝 (Real.log 6 / 6)) := by
  have hmass := tendsto_deningerGammaSixDivisibleShellMass.comp
    ((tendsto_sub_atTop_nat 1).comp hd)
  have hweight : Tendsto (fun M => (6 : ℝ) ^ (-ε M)) atTop (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ => (6 : ℝ) ^ (-x)) 0 := by fun_prop (disch := positivity)
    simpa only [Function.comp_def, neg_zero, Real.rpow_zero] using hc.tendsto.comp hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [one_mul] using hweight.mul hmass) hmass
  · filter_upwards [hd.eventually_ge_atTop 1, hpos] with M hM he
    exact (deningerGammaSixNormalizedGibbsShell_bounds (d M) hM he).1
  · filter_upwards [hd.eventually_ge_atTop 1, hpos] with M hM he
    exact (deningerGammaSixNormalizedGibbsShell_bounds (d M) hM he).2

/-- Normalized shell masses remain nonnegative before the complex source is restored. -/
theorem deningerGammaSixNormalizedGibbsShell_nonneg (m : ℕ) (ε : ℝ) :
    0 ≤ deningerGammaSixNormalizedGibbsShell m ε := by
  classical
  unfold deningerGammaSixNormalizedGibbsShell
  apply Finset.sum_nonneg
  intro a ha
  split_ifs <;> positivity

/-- One bound controls every original shell and every nonnegative regulator. -/
theorem deningerGammaSixNormalizedGibbsShell_uniform_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (m : ℕ) (ε : ℝ), 1 ≤ m → 0 ≤ ε →
      ‖deningerGammaSixNormalizedGibbsShell m ε‖ ≤ B := by
  obtain ⟨B, hB⟩ := (Metric.isBounded_range_of_tendsto
    deningerGammaSixDivisibleShellMass tendsto_deningerGammaSixDivisibleShellMass).exists_norm_le
  refine ⟨B, (norm_nonneg _).trans (hB _ ⟨0, rfl⟩), ?_⟩
  intro m ε hm hε
  rw [Real.norm_of_nonneg (deningerGammaSixNormalizedGibbsShell_nonneg m ε)]
  exact (deningerGammaSixNormalizedGibbsShell_bounds m hm hε).2.trans
    ((le_norm_self _).trans (hB _ ⟨m - 1, rfl⟩))

/-- The complete moving tail after extracting the original starting-depth Gibbs factor. -/
def deningerGammaSixRegulatedMovingTail (M : ℕ) (w : ℂ) (ε : ℝ) : ℂ :=
  ∑' j : ℕ, deningerGammaSixSuccessorRatio w ^ j *
    (((6 : ℝ) ^ (-(j : ℝ) * ε) : ℝ) : ℂ) *
    (mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ (M + j) (mobiusThetaCenteredParameter w) *
      deningerGammaSixTensorRemainderMultiplier (M + j) w w) *
    (deningerGammaSixNormalizedGibbsShell (M + j) ε : ℂ)

theorem tendsto_deningerGammaSixRegulatedMovingTail
    {w : ℂ} (hw : 0 < (mobiusThetaCenteredParameter w).re)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 ≤ ε M) :
    Tendsto (fun M => deningerGammaSixRegulatedMovingTail M w (ε M)) atTop
      (𝓝 ((1 - deningerGammaSixSuccessorRatio w)⁻¹ *
        ((2 * (((ArithmeticFunction.moebius (mobiusSuccessor 6) : ℤ) : ℂ))) *
          ((Real.log 6 / 6 : ℝ) : ℂ)))) := by
  let a : ℕ → ℂ := fun m =>
    mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ m (mobiusThetaCenteredParameter w) *
      deningerGammaSixTensorRemainderMultiplier m w w
  have ha := tendsto_deningerGammaSixTensorRemainderMultiplier_normalized hw
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto a ha).exists_norm_le
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA _ ⟨0, rfl⟩)
  obtain ⟨B, hB0, hB⟩ := deningerGammaSixNormalizedGibbsShell_uniform_bound
  have hq := norm_deningerGammaSixSuccessorRatio_lt_one hw
  have hs : Summable (fun j : ℕ => ‖deningerGammaSixSuccessorRatio w‖ ^ j * (A * B)) := by
    simpa only [norm_pow] using (summable_geometric_of_norm_lt_one hq).norm.mul_right (A * B)
  have ht := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) hs
    (f := fun (M j : ℕ) => deningerGammaSixSuccessorRatio w ^ j *
      (((6 : ℝ) ^ (-(j : ℝ) * ε M) : ℝ) : ℂ) * a (M + j) *
      (deningerGammaSixNormalizedGibbsShell (M + j) (ε M) : ℂ))
    (g := fun j : ℕ => deningerGammaSixSuccessorRatio w ^ j *
      ((2 * (((ArithmeticFunction.moebius (mobiusSuccessor 6) : ℤ) : ℂ))) *
        ((Real.log 6 / 6 : ℝ) : ℂ))) ?_ ?_
  · simpa only [deningerGammaSixRegulatedMovingTail, a, tsum_mul_right,
      tsum_geometric_of_norm_lt_one hq, mul_assoc] using ht
  · intro j
    have hweight : Tendsto (fun M => (((6 : ℝ) ^ (-(j : ℝ) * ε M) : ℝ) : ℂ)) atTop (𝓝 1) := by
      have hc : ContinuousAt (fun x : ℝ => (6 : ℝ) ^ (-(j : ℝ) * x)) 0 := by
        fun_prop (disch := positivity)
      simpa only [Function.comp_def, mul_zero, Real.rpow_zero, Complex.ofReal_one] using
        (hc.tendsto.comp hε).ofReal
    have hmass := (tendsto_deningerGammaSixNormalizedGibbsShell_joint
      (fun M => M + j) ε (tendsto_add_atTop_nat j) hε hpos).ofReal
    have hpoint := ((hweight.mul (ha.comp (tendsto_add_atTop_nat j))).mul hmass).const_mul
      (deningerGammaSixSuccessorRatio w ^ j)
    simpa only [one_mul, mul_assoc, Function.comp_def, a] using hpoint
  · filter_upwards [hpos, eventually_ge_atTop 1] with M hM hM1
    intro j
    have hwgt : ‖(((6 : ℝ) ^ (-(j : ℝ) * ε M) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg j)) hM)
    have ham := hA _ ⟨M + j, rfl⟩
    have hmass : ‖(deningerGammaSixNormalizedGibbsShell (M + j) (ε M) : ℂ)‖ ≤ B := by
      rw [Complex.norm_real]
      exact hB _ _ (by omega) hM
    have hb := mul_le_mul (mul_le_mul hwgt ham (norm_nonneg _) (by norm_num)) hmass
      (norm_nonneg _) (by simpa only [one_mul] using hA0)
    simp only [one_mul] at hb
    simp only [norm_mul, norm_pow]
    calc
      _ = ‖deningerGammaSixSuccessorRatio w‖ ^ j *
          (‖(((6 : ℝ) ^ (-(j : ℝ) * ε M) : ℝ) : ℂ)‖ * ‖a (M + j)‖ *
            ‖(deningerGammaSixNormalizedGibbsShell (M + j) (ε M) : ℂ)‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)

/-- The Gibbs weight on every original divisible coordinate, before normalization. -/
def deningerGammaSixGibbsShell (m : ℕ) (ε : ℝ) : ℝ :=
  ∑ a ∈ Finset.Ico (6 ^ m : ℕ) (6 ^ (m + 1)),
    if 6 ∣ a then (a : ℝ) ^ (-ε) * (a : ℝ)⁻¹ else 0

theorem deningerGammaSixGibbsShell_factor (m : ℕ) (ε : ℝ) :
    deningerGammaSixGibbsShell m ε = (6 : ℝ) ^ (-(m : ℝ) * ε) *
      deningerGammaSixNormalizedGibbsShell m ε := by
  classical
  unfold deningerGammaSixGibbsShell deningerGammaSixNormalizedGibbsShell
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs with hd
  · rw [Real.div_rpow (by positivity) (by positivity),
      show -(m : ℝ) * ε = (m : ℝ) * (-ε) by ring,
      Real.rpow_natCast_mul (by norm_num)]
    have hn : ((6 : ℝ) ^ m) ^ (-ε) ≠ 0 := ne_of_gt (by positivity)
    field_simp
  · simp

def deningerGammaSixRegulatedTailTerm (k l M : ℕ) (w : ℂ) (ε : ℝ) (n : ℕ) : ℂ :=
  (Complex.ofReal (((n + 216 : ℕ) : ℝ) ^ (-ε))) * deningerGammaSixIntegralTailTerm k l M w n

theorem summable_deningerGammaSixRegulatedTailTerm
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    {ε : ℝ} (hε : 0 ≤ ε) :
    Summable (deningerGammaSixRegulatedTailTerm k l M w ε) := by
  apply (summable_deningerGammaSixIntegralTailTerm_of_admitted k l M hw hrw had).norm.of_norm_bounded
  intro n
  unfold deningerGammaSixRegulatedTailTerm
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; omega) (neg_nonpos.mpr hε))

theorem deningerGammaSixRegulatedTailTerm_fiber
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hM : 3 ≤ M) (m : ℕ) (ε : ℝ) :
    (∑' n : deningerGammaSixDepthFiber m, deningerGammaSixRegulatedTailTerm k l M w ε n) =
      if M ≤ m then (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
        deningerGammaSixTensorRemainderMultiplier m w w *
          (deningerGammaSixGibbsShell m ε : ℂ) else 0 := by
  simp_rw [deningerGammaSixRegulatedTailTerm, deningerGammaSixIntegralTailTerm_depth]
  by_cases hMm : M ≤ m
  · simp only [if_pos hMm]
    have hm : 3 ≤ m := hM.trans hMm
    have hfiber : (∑' n : deningerGammaSixDepthFiber m,
        (Complex.ofReal ((((n : ℕ) + 216 : ℕ) : ℝ) ^ (-ε))) *
          (if 6 ∣ (n : ℕ) + 216 then deningerGammaSixIntegralRemainder k l w w n else 0)) =
        (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
          deningerGammaSixTensorRemainderMultiplier m w w *
            ∑' n : deningerGammaSixDepthFiber m,
              if 6 ∣ (n : ℕ) + 216 then
                (Complex.ofReal ((((n : ℕ) + 216 : ℕ) : ℝ) ^ (-ε))) *
                  (((n : ℕ) + 216 : ℕ) : ℂ)⁻¹ else 0 := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro n
      have ha : 1 / (deningerGammaSixShellDepth n : ℝ) < (mobiusThetaCenteredParameter w).re := by
        rw [show deningerGammaSixShellDepth n = m from n.property]
        exact had m hMm
      rw [deningerGammaSixIntegralRemainder_eq_shell_multiplier_of_admitted k l hw n ha,
        show deningerGammaSixShellDepth n = m from n.property]
      split_ifs <;> ring
    rw [hfiber]
    congr 1
    rw [deningerGammaSixDepthFiber_eq_shellCoordinates hm]
    rw [Finset.tsum_subtype' (deningerGammaSixShellCoordinates m)
      (fun n : ℕ => if 6 ∣ n + 216 then
        (Complex.ofReal (((n + 216 : ℕ) : ℝ) ^ (-ε))) * (((n + 216 : ℕ) : ℂ))⁻¹ else 0)]
    have hlo := deningerGammaSix_pow_three_le hm
    have hhi := deningerGammaSix_pow_three_le (show 3 ≤ m + 1 by omega)
    have hshift := Finset.sum_Ico_add'
      (fun a : ℕ => if 6 ∣ a then (Complex.ofReal ((a : ℝ) ^ (-ε))) * (a : ℂ)⁻¹ else 0)
      (6 ^ m - 216) (6 ^ (m + 1) - 216) (c := 216)
    rw [Nat.sub_add_cancel hlo, Nat.sub_add_cancel hhi] at hshift
    change (∑ n ∈ Finset.Ico (6 ^ m - 216) (6 ^ (m + 1) - 216),
      if 6 ∣ n + 216 then (Complex.ofReal (((n + 216 : ℕ) : ℝ) ^ (-ε))) *
        ((n + 216 : ℕ) : ℂ)⁻¹ else 0) = _
    rw [hshift]
    unfold deningerGammaSixGibbsShell
    push_cast
    simp only [apply_ite, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_zero]
  · simp only [if_neg hMm, mul_zero, tsum_zero]

theorem deningerGammaSixRegulatedTailTerm_tsum
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hM : 3 ≤ M) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑' n : ℕ, deningerGammaSixRegulatedTailTerm k l M w ε n) =
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
        ∑' j : ℕ, deningerGammaSixTensorRemainderMultiplier (M + j) w w *
          (deningerGammaSixGibbsShell (M + j) ε : ℂ) := by
  have hs := summable_deningerGammaSixRegulatedTailTerm k l M hw hrw had hε
  have hf := hs.hasSum.tsum_fiberwise deningerGammaSixShellDepth
  change HasSum (fun m : ℕ => ∑' n : deningerGammaSixDepthFiber m,
    deningerGammaSixRegulatedTailTerm k l M w ε n)
      (∑' n : ℕ, deningerGammaSixRegulatedTailTerm k l M w ε n) at hf
  rw [← hf.tsum_eq]
  simp_rw [deningerGammaSixRegulatedTailTerm_fiber k l M hw had hM]
  have hinj : Function.Injective (fun j : ℕ => M + j) := fun _ _ h => Nat.add_left_cancel h
  have he := hinj.tsum_eq (f := fun m : ℕ =>
    if M ≤ m then (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
      deningerGammaSixTensorRemainderMultiplier m w w *
        (deningerGammaSixGibbsShell m ε : ℂ) else 0) (by
          intro m hm
          have hMm : M ≤ m := by
            by_contra h
            exact hm (if_neg h)
          exact ⟨m - M, by change M + (m - M) = m; omega⟩)
  rw [← he]
  simp only [Nat.le_add_right, if_true, mul_assoc, tsum_mul_left]

/-- Reindex the actual projected Gibbs trace on the original integral coordinates. -/
theorem deningerGammaSixIntegralTailOperator_gibbsTrace
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hM : 3 ≤ M) (ε : ℝ) :
    (∑' a : PNat, deningerOrdinaryIntegerGibbsDiagonal ((1 + ε) / 2) a
      (deningerGammaSixIntegralTailOperator k l M w *
        deningerOrdinaryIntegerDivisibilityProjection (6 : PNat))) =
      ∑' n : ℕ, deningerGammaSixRegulatedTailTerm k l M w ε n := by
  classical
  let R := deningerGammaSixIntegralOperator k l w w -
    (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen
  let f : PNat → ℂ := fun a => if 6 ^ M ≤ (a : ℕ) ∧ (6 : PNat) ∣ a then
    (Complex.ofReal (((a : ℕ) : ℝ) ^ (-ε))) * deningerOrdinaryIntegerDiagonalCoefficient a R else 0
  have hf : (∑' a : PNat, deningerOrdinaryIntegerGibbsDiagonal ((1 + ε) / 2) a
      (deningerGammaSixIntegralTailOperator k l M w *
        deningerOrdinaryIntegerDivisibilityProjection (6 : PNat))) = ∑' a : PNat, f a := by
    simp only [deningerOrdinaryIntegerGibbsDiagonal_abel,
      deningerOrdinaryIntegerDiagonalCoefficient_rightProjection,
      deningerGammaSixIntegralTailOperator, deningerOrdinaryIntegerDiagonalCoefficient_tailProjection]
    apply tsum_congr
    intro a
    dsimp only [f, R]
    split_ifs <;> simp_all
  rw [hf]
  let g : ℕ → PNat := fun n => ⟨n + 216, by omega⟩
  have hg : Function.Injective g := by
    intro i j h
    have he := congrArg (fun a : PNat => (a : ℕ)) h
    change i + 216 = j + 216 at he
    omega
  have hsupp : Function.support f ⊆ Set.range g := by
    intro a ha
    have hpow : 6 ^ M ≤ (a : ℕ) := by
      by_contra h
      exact ha (by simp only [f, h, false_and, if_false])
    have hlow := deningerGammaSix_pow_three_le hM
    refine ⟨(a : ℕ) - 216, ?_⟩
    apply Subtype.ext
    change (a : ℕ) - 216 + 216 = (a : ℕ)
    exact Nat.sub_add_cancel (hlow.trans hpow)
  rw [← hg.tsum_eq hsupp]
  apply tsum_congr
  intro n
  dsimp only [f, g]
  unfold deningerGammaSixRegulatedTailTerm
  by_cases hn : 6 ^ M ≤ n + 216
  · have ha := had _ ((deningerGammaSixTailCut_iff_depth M n).1 hn)
    rw [show deningerOrdinaryIntegerDiagonalCoefficient ⟨n + 216, by omega⟩ R =
      deningerGammaSixIntegralRemainder k l w w n from
        deningerGammaSixIntegralCorrection_tail_of_admitted k l hw hw n ha ha]
    unfold deningerGammaSixIntegralTailTerm
    split_ifs <;> simp_all [PNat.dvd_iff]
  · simp only [deningerGammaSixIntegralTailTerm, PNat.mk_coe, hn, false_and, if_false, mul_zero]

/-- The complete source's weighted sum, with both normalization factors kept explicit. -/
theorem deningerGammaSixRegulatedTailTerm_normalized
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hM : 3 ≤ M) {ε : ℝ} (hε : 0 ≤ ε) :
    mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w) *
      (∑' n : ℕ, deningerGammaSixRegulatedTailTerm k l M w ε n) =
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
        (Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ) * ε))) * deningerGammaSixRegulatedMovingTail M w ε := by
  rw [deningerGammaSixRegulatedTailTerm_tsum k l M hw hrw had hM hε,
    deningerGammaSixRegulatedMovingTail]
  simp_rw [deningerGammaSixGibbsShell_factor]
  let N := mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w)
  let c := iteratedDeriv k XiC w * iteratedDeriv l XiC w
  let b := Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ) * ε))
  change N * (c * ∑' j : ℕ, _) = (c * b) * ∑' j : ℕ, _
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro j
  have hsplit : (6 : ℝ) ^ (-((M + j : ℕ) : ℝ) * ε) =
      (6 : ℝ) ^ (-(M : ℝ) * ε) * (6 : ℝ) ^ (-(j : ℝ) * ε) := by
    rw [show -((M + j : ℕ) : ℝ) * ε = -(M : ℝ) * ε + -(j : ℝ) * ε by push_cast; ring,
      Real.rpow_add (by norm_num)]
  rw [hsplit]
  push_cast
  have hN := deningerGammaSixSuccessorNormalizer_shift_cancel M j w
  dsimp only [N, c, b]
  linear_combination
    (c * deningerGammaSixTensorRemainderMultiplier (M + j) w w *
      (Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ) * ε))) * (Complex.ofReal ((6 : ℝ) ^ (-(j : ℝ) * ε))) *
        (deningerGammaSixNormalizedGibbsShell (M + j) ε : ℂ)) * hN.symm

/-- Exact regulated second-defect factorization for the admitted original tail operator. -/
theorem deningerGammaSixIntegralTailOperator_regulated_factor
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hM : 3 ≤ M) {ε : ℝ} (hε : 0 < ε) :
    mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w) *
      deningerOrdinaryIntegerAbelDefect ε (6 : PNat)
        (deningerGammaSixIntegralTailOperator k l M w) / (ε : ℂ) ^ 2 =
      ((((6 : ℝ) ^ ε - 1) / ε : ℝ) : ℂ) *
        (((ε * deningerOrdinaryIntegerGibbsPartition ((1 + ε) / 2))⁻¹ : ℝ) : ℂ) *
        ((iteratedDeriv k XiC w * iteratedDeriv l XiC w) *
          (Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ) * ε))) * deningerGammaSixRegulatedMovingTail M w ε) := by
  have hs := deningerGammaSixIntegralTailOperator_summable_of_admitted k l M hw hrw had
  have hT := deningerOrdinaryIntegerSummableDiagonal_mem_gibbsDomain
    (by linarith : 1 / 2 ≤ (1 + ε) / 2) _ hs
  rw [deningerOrdinaryIntegerAbelDefect_eq ⟨_, hT⟩ (6 : PNat), deningerOrdinaryIntegerAbelReader,
    deningerGammaSixIntegralTailOperator_gibbsTrace k l M hw had hM ε,
    ← deningerGammaSixRegulatedTailTerm_normalized k l M hw hrw had hM hε.le]
  push_cast
  simp only [mul_inv_rev, div_eq_mul_inv, ← inv_pow]
  ring


open MeasureTheory

/-- Apply the regulator and ordinary divisibility filter to the admitted original integrand. -/
def deningerGammaSixRegulatedSource (k l M : ℕ) (w z : ℂ) (ε : ℝ)
    (n : ℕ) (xy : ℝ × ℝ) : ℂ :=
  (Complex.ofReal (((n + 216 : ℕ) : ℝ) ^ (-ε))) *
    (if 6 ∣ n + 216 then deningerGammaSixAdmittedRemainderIntegrand k l M w z n xy else 0)

theorem deningerGammaSixRegulatedSource_tsum_data
    (k l M : ℕ) {w z : ℂ} (hw : |w.im| < 1) (hz : |z.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (hrz : 0 < (mobiusThetaCenteredParameter z).re) {ε : ℝ} (hε : 0 ≤ ε) :
    Summable (fun n : ℕ => ∫ xy : ℝ × ℝ,
      ‖deningerGammaSixRegulatedSource k l M w z ε n xy‖ ∂(volume.prod volume)) ∧
    Integrable (fun xy => ∑' n : ℕ, deningerGammaSixRegulatedSource k l M w z ε n xy)
      (volume.prod volume) ∧
    (∫ xy : ℝ × ℝ, (∑' n : ℕ, deningerGammaSixRegulatedSource k l M w z ε n xy)
      ∂(volume.prod volume)) = ∑' n : ℕ,
        ∫ xy : ℝ × ℝ, deningerGammaSixRegulatedSource k l M w z ε n xy ∂(volume.prod volume) := by
  classical
  have hi : ∀ n : ℕ, Integrable (deningerGammaSixRegulatedSource k l M w z ε n)
      (volume.prod volume) := by
    intro n
    unfold deningerGammaSixRegulatedSource
    apply Integrable.const_mul
    split_ifs
    · exact integrable_deningerGammaSixAdmittedRemainderIntegrand k l M n hw hz
    · exact integrable_zero _ _ _
  have hs : Summable (fun n : ℕ => ∫ xy : ℝ × ℝ,
      ‖deningerGammaSixRegulatedSource k l M w z ε n xy‖ ∂(volume.prod volume)) := by
    apply (deningerGammaSixAdmittedRemainderIntegrand_divisible_tsum_data k l M 6 hw hz hrw hrz).1.of_nonneg_of_le
      (fun n => integral_nonneg (fun xy => norm_nonneg _))
    intro n
    simp only [deningerGammaSixRegulatedSource, norm_mul]
    rw [integral_const_mul]
    apply mul_le_of_le_one_left (integral_nonneg (fun xy => norm_nonneg _))
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_cast; omega) (neg_nonpos.mpr hε)
  exact ⟨hs, GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hi hs,
    (integral_tsum_of_summable_integral_norm hi hs).symm⟩

theorem deningerGammaSixRegulatedTailTerm_eq_integral
    (k l M : ℕ) (w : ℂ)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (ε : ℝ) (n : ℕ) :
    deningerGammaSixRegulatedTailTerm k l M w ε n =
      ∫ xy : ℝ × ℝ, deningerGammaSixRegulatedSource k l M w w ε n xy ∂(volume.prod volume) := by
  classical
  unfold deningerGammaSixRegulatedTailTerm deningerGammaSixRegulatedSource
  rw [integral_const_mul]
  congr 1
  by_cases hq : 6 ∣ n + 216
  · simp only [hq, if_true]
    rw [integral_deningerGammaSixAdmittedRemainderIntegrand_eq_cutoff k l M w w
      (fun m hm => ⟨had m hm, had m hm⟩)]
    simp only [deningerGammaSixIntegralTailTerm, hq, and_true]
  · simp only [hq, if_false, integral_zero, deningerGammaSixIntegralTailTerm, and_false]

/-- The actual projected Gibbs trace is the integral of the complete regulated source sum. -/
theorem deningerGammaSixIntegralTailOperator_gibbsTrace_eq_complete_integral
    (k l M : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (had : ∀ m : ℕ, M ≤ m → 1 / (m : ℝ) < (mobiusThetaCenteredParameter w).re)
    (hM : 3 ≤ M) {ε : ℝ} (hε : 0 ≤ ε) :
    (∑' a : PNat, deningerOrdinaryIntegerGibbsDiagonal ((1 + ε) / 2) a
      (deningerGammaSixIntegralTailOperator k l M w *
        deningerOrdinaryIntegerDivisibilityProjection (6 : PNat))) =
      ∫ xy : ℝ × ℝ, (∑' n : ℕ, deningerGammaSixRegulatedSource k l M w w ε n xy)
        ∂(volume.prod volume) := by
  rw [deningerGammaSixIntegralTailOperator_gibbsTrace k l M hw had hM ε,
    (deningerGammaSixRegulatedSource_tsum_data k l M hw hw hrw hrw hε).2.2]
  exact tsum_congr (deningerGammaSixRegulatedTailTerm_eq_integral k l M w had ε)
/-- Finite regulator--depth products retain their exact exponential attenuation. -/
theorem tendsto_deningerGammaSixIntegralTailOperator_crossover
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M)
    {τ : ℝ} (hτ : Tendsto (fun M : ℕ => (M : ℝ) * ε M) atTop (𝓝 τ)) :
    Tendsto (fun M => mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M
      (mobiusThetaCenteredParameter w) *
        deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat)
          (deningerGammaSixIntegralTailOperator k l M w) / (ε M : ℂ) ^ 2) atTop
      (𝓝 ((Complex.ofReal ((6 : ℝ) ^ (-τ))) * deningerGammaSixTailBoundaryLimit k l w)) := by
  have hpath : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hε, hpos⟩
  have hgain := ((tendsto_deningerOrdinaryIntegerAbelGain_slope (6 : PNat)).comp hpath).ofReal
  have hpart := ((tendsto_deningerOrdinaryIntegerGibbsPartition_abel_residue.comp hpath).inv₀
    (by norm_num : (1 : ℝ) ≠ 0)).ofReal
  have hweight : Tendsto (fun M : ℕ => (Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ) * ε M)))) atTop
      (𝓝 (Complex.ofReal ((6 : ℝ) ^ (-τ)))) := by
    have hc : ContinuousAt (fun x : ℝ => (6 : ℝ) ^ (-x)) τ := by fun_prop (disch := positivity)
    simpa only [Function.comp_def, neg_mul] using (hc.tendsto.comp hτ).ofReal
  have htail := tendsto_deningerGammaSixRegulatedMovingTail hrw ε hε (hpos.mono (fun _ h => h.le))
  have ht := (hgain.mul hpart).mul
    ((hweight.const_mul (iteratedDeriv k XiC w * iteratedDeriv l XiC w)).mul htail)
  have hresult := ht.congr' (by
    filter_upwards [hpos, eventually_deningerGammaSixSourceDepth_admitted hrw hrw] with M he had
    exact (deningerGammaSixIntegralTailOperator_regulated_factor k l M hw hrw
      (fun m hm => (had.2 m hm).1) had.1 he).symm)
  simpa only [deningerGammaSixTailBoundaryLimit, inv_one, Complex.ofReal_one, one_mul, mul_one,
    show (((6 : PNat) : ℕ) : ℝ) = 6 from rfl, mul_assoc, mul_left_comm, mul_comm] using hresult

/-- Sending the retained product to infinity suppresses the same regulated operator response. -/
theorem tendsto_deningerGammaSixIntegralTailOperator_crossover_infinite
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M)
    (hτ : Tendsto (fun M : ℕ => (M : ℝ) * ε M) atTop atTop) :
    Tendsto (fun M => mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M
      (mobiusThetaCenteredParameter w) *
        deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat)
          (deningerGammaSixIntegralTailOperator k l M w) / (ε M : ℂ) ^ 2) atTop (𝓝 0) := by
  have hpath : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hε, hpos⟩
  have hgain := ((tendsto_deningerOrdinaryIntegerAbelGain_slope (6 : PNat)).comp hpath).ofReal
  have hpart := ((tendsto_deningerOrdinaryIntegerGibbsPartition_abel_residue.comp hpath).inv₀
    (by norm_num : (1 : ℝ) ≠ 0)).ofReal
  have hweight : Tendsto (fun M : ℕ => (Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ) * ε M)))) atTop (𝓝 0) := by
    have h := ((tendsto_rpow_atTop_of_base_gt_one 6 (by norm_num)).comp hτ).inv_tendsto_atTop
    simpa only [neg_mul, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 6), Complex.ofReal_zero,
      Pi.inv_apply, Function.comp_def, Complex.ofReal_inv] using h.ofReal
  have htail := tendsto_deningerGammaSixRegulatedMovingTail hrw ε hε (hpos.mono (fun _ h => h.le))
  have ht := (hgain.mul hpart).mul
    ((hweight.const_mul (iteratedDeriv k XiC w * iteratedDeriv l XiC w)).mul htail)
  simp only [mul_zero, zero_mul] at ht
  apply ht.congr'
  filter_upwards [hpos, eventually_deningerGammaSixSourceDepth_admitted hrw hrw] with M he had
  exact (deningerGammaSixIntegralTailOperator_regulated_factor k l M hw hrw
    (fun m hm => (had.2 m hm).1) had.1 he).symm

/-- The literal Abel defect reads the diagonal of the original operator. -/
theorem deningerOrdinaryIntegerAbelDefect_congr_diagonal
    (T S : DeningerOrdinaryIntegerEnd)
    (h : ∀ a : PNat, deningerOrdinaryIntegerDiagonalCoefficient a T =
      deningerOrdinaryIntegerDiagonalCoefficient a S) (ε : ℝ) (n : PNat) :
    deningerOrdinaryIntegerAbelDefect ε n T = deningerOrdinaryIntegerAbelDefect ε n S := by
  unfold deningerOrdinaryIntegerAbelDefect deningerOrdinaryIntegerAbelReader
  simp only [deningerOrdinaryIntegerGibbsDiagonal_abel,
    deningerOrdinaryIntegerDiagonalCoefficient_compression,
    deningerOrdinaryIntegerDiagonalCoefficient_rightProjection, h]

/-- A finite diagonal repair disappears from every regulated reader at sufficiently late cutoffs. -/
theorem eventually_deningerOrdinaryIntegerAbelDefect_finite_tail_repair
    (T F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite) :
    ∀ᶠ M : ℕ in atTop, ∀ (ε : ℝ) (n : PNat),
      deningerOrdinaryIntegerAbelDefect ε n
        (deningerOrdinaryIntegerTailProjection (6 ^ M) * (T + F)) =
      deningerOrdinaryIntegerAbelDefect ε n
        (deningerOrdinaryIntegerTailProjection (6 ^ M) * T) := by
  filter_upwards [eventually_deningerOrdinaryInteger_finite_tail_diagonal_zero F hF] with M hM
  intro ε n
  apply deningerOrdinaryIntegerAbelDefect_congr_diagonal
  intro a
  rw [mul_add, map_add, hM, add_zero]

/-- Finite diagonal repairs preserve the finite-product crossover at the same original anchor. -/
theorem tendsto_deningerGammaSixIntegral_finite_repair_crossover
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (F : DeningerOrdinaryIntegerEnd)
    (hF : (Function.support (fun a : PNat => deningerOrdinaryIntegerDiagonalCoefficient a F)).Finite)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M)
    {τ : ℝ} (hτ : Tendsto (fun M : ℕ => (M : ℝ) * ε M) atTop (𝓝 τ)) :
    Tendsto (fun M => mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M
      (mobiusThetaCenteredParameter w) *
        deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat)
          (deningerOrdinaryIntegerTailProjection (6 ^ M) *
            ((deningerGammaSixIntegralOperator k l w w + F) -
              (iteratedDeriv k XiC w * iteratedDeriv l XiC w) •
                deningerOrdinaryIntegerReciprocalGreen)) / (ε M : ℂ) ^ 2) atTop
      (𝓝 ((Complex.ofReal ((6 : ℝ) ^ (-τ))) * deningerGammaSixTailBoundaryLimit k l w)) := by
  have he := eventually_deningerOrdinaryIntegerAbelDefect_finite_tail_repair
    (deningerGammaSixIntegralOperator k l w w -
      (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) F hF
  apply (tendsto_deningerGammaSixIntegralTailOperator_crossover k l hw hrw ε hε hpos hτ).congr'
  filter_upwards [he] with M hM
  rw [show (deningerGammaSixIntegralOperator k l w w + F) -
    (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen =
      (deningerGammaSixIntegralOperator k l w w -
        (iteratedDeriv k XiC w * iteratedDeriv l XiC w) • deningerOrdinaryIntegerReciprocalGreen) + F by abel,
    hM]
  rfl

/-- No finite regulator--depth product erases the original nonzero top Xi jet. -/
theorem deningerGammaSixTailBoundaryLimit_crossover_top_ne_zero
    (rho : XiDivisorSupport) (τ : ℝ) :
    (Complex.ofReal ((6 : ℝ) ^ (-τ))) *
      deningerGammaSixTailBoundaryLimit (xiSupportMultiplicity rho) (xiSupportMultiplicity rho)
        (xiSpectralPointSupport rho) ≠ 0 := by
  have hrw : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  apply mul_ne_zero
  · exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) (-τ)))
  · exact deningerGammaSixTailBoundaryLimit_ne_zero _ _ hrw
      (mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
        (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho))

/-- Actual regulated convergence and nonvanishing at every original Xi divisor. -/
theorem deningerGammaSixIntegralTailOperator_crossover_all_divisors
    (rho : XiDivisorSupport) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M)
    {τ : ℝ} (hτ : Tendsto (fun M : ℕ => (M : ℝ) * ε M) atTop (𝓝 τ)) :
    Tendsto (fun M => mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M
      (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)) *
        deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat)
          (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) M
            (xiSpectralPointSupport rho)) / (ε M : ℂ) ^ 2) atTop
      (𝓝 ((Complex.ofReal ((6 : ℝ) ^ (-τ))) *
        deningerGammaSixTailBoundaryLimit (xiSupportMultiplicity rho) (xiSupportMultiplicity rho)
          (xiSpectralPointSupport rho))) ∧
    (Complex.ofReal ((6 : ℝ) ^ (-τ))) *
      deningerGammaSixTailBoundaryLimit (xiSupportMultiplicity rho) (xiSupportMultiplicity rho)
        (xiSpectralPointSupport rho) ≠ 0 := by
  have hrw : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  exact ⟨tendsto_deningerGammaSixIntegralTailOperator_crossover _ _
    (abs_im_xiSpectralPointSupport_lt_one rho) hrw ε hε hpos hτ,
    deningerGammaSixTailBoundaryLimit_crossover_top_ne_zero rho τ⟩

/-- The exact attenuation accounts for every positive regulator path tending to zero.
This explicit diagnostic normalization does not redefine the fixed reader. -/
theorem tendsto_deningerGammaSixIntegralTailOperator_crossover_deattenuated
    (k l : ℕ) {w : ℂ} (hw : |w.im| < 1)
    (hrw : 0 < (mobiusThetaCenteredParameter w).re)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    Tendsto (fun M => (mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M
      (mobiusThetaCenteredParameter w) *
        deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat)
          (deningerGammaSixIntegralTailOperator k l M w) / (ε M : ℂ) ^ 2) /
            (Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ) * ε M)))) atTop
      (𝓝 (deningerGammaSixTailBoundaryLimit k l w)) := by
  have hpath : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr ⟨hε, hpos⟩
  have hgain := ((tendsto_deningerOrdinaryIntegerAbelGain_slope (6 : PNat)).comp hpath).ofReal
  have hpart := ((tendsto_deningerOrdinaryIntegerGibbsPartition_abel_residue.comp hpath).inv₀
    (by norm_num : (1 : ℝ) ≠ 0)).ofReal
  have htail := tendsto_deningerGammaSixRegulatedMovingTail hrw ε hε (hpos.mono (fun _ h => h.le))
  have ht := (hgain.mul hpart).mul
    (htail.const_mul (iteratedDeriv k XiC w * iteratedDeriv l XiC w))
  have hresult := ht.congr' (f₂ := fun M =>
    (mobiusThetaSuccessorSpectralNormalizer ⟨6, by omega⟩ M (mobiusThetaCenteredParameter w) *
      deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat)
        (deningerGammaSixIntegralTailOperator k l M w) / (ε M : ℂ)^(2 : ℕ)) /
          (Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ) * ε M)))) (by
    filter_upwards [hpos, eventually_deningerGammaSixSourceDepth_admitted hrw hrw] with M he had
    rw [deningerGammaSixIntegralTailOperator_regulated_factor k l M hw hrw
      (fun m hm => (had.2 m hm).1) had.1 he]
    have hn : (Complex.ofReal ((6 : ℝ) ^ (-(M : ℝ) * ε M))) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6) (-(M : ℝ) * ε M)))
    rw [eq_div_iff hn]
    simp only [Function.comp_def, Complex.ofReal_inv,
      show (((6 : PNat) : ℕ) : ℝ) = 6 from rfl]
    ring)
  simpa only [deningerGammaSixTailBoundaryLimit, inv_one, Complex.ofReal_one, one_mul, mul_one,
    show (((6 : PNat) : ℕ) : ℝ) = 6 from rfl, mul_assoc, mul_left_comm, mul_comm] using hresult

/-- Decay in a joint limiting reader does not kill the actual top-jet defect at late depths. -/
theorem eventually_deningerGammaSixIntegralTailOperator_regulated_top_ne_zero
    (rho : XiDivisorSupport) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    ∀ᶠ M : ℕ in atTop,
      deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat)
        (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) M
          (xiSpectralPointSupport rho)) ≠ 0 := by
  have hrw : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  have hK := deningerGammaSixTailBoundaryLimit_ne_zero _ _ hrw
    (mul_ne_zero (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho)
      (iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho))
  have ht := (tendsto_deningerGammaSixIntegralTailOperator_crossover_deattenuated _ _
    (abs_im_xiSpectralPointSupport_lt_one rho) hrw ε hε hpos).eventually_ne hK
  filter_upwards [ht] with M hM
  intro hz
  exact hM (by rw [hz, mul_zero, zero_div, zero_div])

/-- Every regulator path tending to zero retains the actual adjacent conormal pair. -/
theorem eventually_deningerGammaSixIntegralTailOperator_regulated_conormal_pair
    (rho : XiDivisorSupport) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hpos : ∀ᶠ M : ℕ in atTop, 0 < ε M) :
    ∀ᶠ M : ℕ in atTop,
      deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat)
        (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho - 1) (xiSupportMultiplicity rho) M
          (xiSpectralPointSupport rho)) = 0 ∧
      deningerOrdinaryIntegerAbelDefect (ε M) (6 : PNat)
        (deningerGammaSixIntegralTailOperator (xiSupportMultiplicity rho) (xiSupportMultiplicity rho) M
          (xiSpectralPointSupport rho)) ≠ 0 := by
  have hrw : 0 < (mobiusThetaCenteredParameter (xiSpectralPointSupport rho)).re := by
    rw [mobiusThetaCenteredParameter_xiSpectralPointSupport]
    exact (xi_divisor_support_re_mem_open_unit rho).1
  have hlower := iteratedDeriv_XiC_eq_zero_before_supportMultiplicity rho
    (Nat.sub_lt (xiSupportMultiplicity_pos rho) (by omega : 0 < 1))
  filter_upwards [hpos, eventually_deningerGammaSixSourceDepth_admitted hrw hrw,
    eventually_deningerGammaSixIntegralTailOperator_regulated_top_ne_zero rho ε hε hpos]
      with M he had htop
  refine ⟨?_, htop⟩
  have hf := deningerGammaSixIntegralTailOperator_regulated_factor
    (xiSupportMultiplicity rho - 1) (xiSupportMultiplicity rho) M
    (abs_im_xiSpectralPointSupport_lt_one rho) hrw
    (fun m hm => (had.2 m hm).1) had.1 he
  simp only [hlower, zero_mul, mul_zero] at hf
  have hε0 : (ε M : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt he
  rcases div_eq_zero_iff.mp hf with hn | hn
  · exact (mul_eq_zero.mp hn).resolve_left
      (deningerGammaSixSuccessorNormalizer_ne_zero M (xiSpectralPointSupport rho))
  · exact False.elim ((pow_ne_zero 2 hε0) hn)

end
end RHTower
