import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCompleteCriticalResidueIsSupportedAtThePole
import GaloisForLFunctions.ArithmeticDegenerationTheory.TheLimitingMixedStructure
import GaloisForLFunctions.RHTower.PoleSelfEnergyLimit
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# The critical conductor form retains the polar genus

At every positive critical ratio, each fixed conductor block converges
to its positive Jordan diagonal plus a nonnegative polar term. The
convergence yields eventual positivity uniform over that block's
coefficients; the conductor cutoff remains fixed.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticDegenerationTheory
open RenormalizedArithmeticPotentialTheory ArithmeticHodgeTheoryOfDegenerations
  SpacingScaleHarmonicAnalysis HodgeTheoryWithoutVarieties CriticalArithmeticCorrelationTheory

/-- The polar coefficient retained at a positive critical ratio. -/
def criticalGenusCoefficient (R : ℝ) : ℝ :=
  R * ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) * RHTower.poleSharpConstant

theorem criticalGenusCoefficient_nonneg {R : ℝ} (hR : 0 ≤ R) :
    0 ≤ criticalGenusCoefficient R := by
  unfold criticalGenusCoefficient
  exact mul_nonneg (mul_nonneg hR (div_nonneg (sq_nonneg _) integral_tiltedUnitSpline_sq_pos.le))
    RHTower.poleSharpConstant_pos.le

/-- At every positive critical ratio the fixed conductor form retains a positive polar term. -/
theorem tendsto_critical_rescaledConductorGram {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {m l : ℕ} (hm : 0 < m) (hl : 0 < l) :
    Tendsto (fun N : ℕ => rescaledConductorGram (c N) N m l) atTop
      (𝓝 ((if m = l then jordanCoefficient m else 0) +
        (if m = 1 ∧ l = 1 then criticalGenusCoefficient R else 0))) := by
  have hcinf := (criticalCurve_facts hc hR hcrit).1
  have hres := tendsto_critical_completeWeil_residual contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos hc hR hcrit hm hl
  have hdev : Tendsto (fun N : ℕ => c N ^ (7 : ℝ) * conductorDeviation (c N) N m l)
      atTop (𝓝 (if m = 1 ∧ l = 1 then criticalGenusCoefficient R else 0)) := by
    have h := hcrit.mul hres
    have hval : R * (if m = 1 ∧ l = 1 then
        ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2)) *
          (2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) else 0) =
        (if m = 1 ∧ l = 1 then criticalGenusCoefficient R else 0) := by
      unfold criticalGenusCoefficient RHTower.poleSharpConstant
      split_ifs <;> ring
    rw [hval] at h
    apply h.congr'
    filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0]
      with N hL
    change 0 < Real.log (N : ℝ) at hL
    have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
    simp only [conductorDeviation, conductorEntry, inner_sub_left, real_inner_smul_left]
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) from rfl, Real.rpow_natCast]
    field_simp [hL.ne', hc0.ne']
  have hJ := (tendsto_rpow_seven_mul_completedConductorEnergy_jordan m).comp hcinf
  have hG : Tendsto (fun N : ℕ => ⟪normalizedRamanujanHorizonVector m N,
      normalizedRamanujanHorizonVector l N⟫) atTop (𝓝 (if m = l then 1 else 0)) := by
    simp_rw [normalizedRamanujanHorizonVector_inner]
    exact tendsto_ramanujanPoleProfile_gram hm hl
  have h := (hJ.mul hG).add hdev
  have hval : jordanCoefficient m * (if m = l then 1 else 0) =
      (if m = l then jordanCoefficient m else 0) := by split_ifs <;> simp
  rw [hval] at h
  exact h.congr fun N => by
    simp only [Function.comp_def, rescaledConductorGram, conductorDeviation]
    ring

/-- A finite conductor packet has its Jordan form plus the polar genus at every critical ratio. -/
theorem tendsto_critical_rescaled_packet {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {S : Finset ℕ} (hS : ∀ e ∈ S, 0 < e) (b : ℕ → ℝ) :
    Tendsto (fun N : ℕ => ∑ e ∈ S, ∑ l ∈ S,
      b e * b l * rescaledConductorGram (c N) N e l) atTop
      (𝓝 ((∑ e ∈ S, jordanCoefficient e * b e ^ 2) +
        (if 1 ∈ S then criticalGenusCoefficient R * b 1 ^ 2 else 0))) := by
  have h := tendsto_finsetSum S fun e he => tendsto_finsetSum S fun l hl =>
    (tendsto_critical_rescaledConductorGram hc hR hcrit (hS e he) (hS l hl)).const_mul (b e * b l)
  have hdiag : (∑ e ∈ S, ∑ l ∈ S, b e * b l *
      (if e = l then jordanCoefficient e else 0)) = ∑ e ∈ S, jordanCoefficient e * b e ^ 2 := by
    apply sum_congr rfl
    intro e he
    rw [sum_eq_single_of_mem e he (fun l _ hne => by simp only [if_neg (Ne.symm hne), mul_zero])]
    simp only [if_true]
    ring
  have hpolar : (∑ e ∈ S, ∑ l ∈ S, b e * b l *
      (if e = 1 ∧ l = 1 then criticalGenusCoefficient R else 0)) =
      (if 1 ∈ S then criticalGenusCoefficient R * b 1 ^ 2 else 0) := by
    by_cases h1 : 1 ∈ S
    · rw [if_pos h1, sum_eq_single_of_mem 1 h1]
      · rw [sum_eq_single_of_mem 1 h1]
        · rw [if_pos ⟨rfl, rfl⟩]
          ring
        · intro l hl hl1
          rw [if_neg (fun h => hl1 h.2), mul_zero]
      · intro e he he1
        apply sum_eq_zero
        intro l hl
        rw [if_neg (fun h => he1 h.1), mul_zero]
    · rw [if_neg h1]
      apply sum_eq_zero
      intro e he
      apply sum_eq_zero
      intro l hl
      rw [if_neg (fun h : e = 1 ∧ l = 1 => h1 (h.1 ▸ he)), mul_zero]
  have hval : (∑ e ∈ S, ∑ l ∈ S, b e * b l *
      ((if e = l then jordanCoefficient e else 0) +
        (if e = 1 ∧ l = 1 then criticalGenusCoefficient R else 0))) =
      (∑ e ∈ S, jordanCoefficient e * b e ^ 2) +
        (if 1 ∈ S then criticalGenusCoefficient R * b 1 ^ 2 else 0) := by
    simp only [mul_add, sum_add_distrib]
    rw [hdiag, hpolar]
  rwa [hval] at h

/-- Every nonzero fixed packet stays positive at every positive critical ratio. -/
theorem eventually_pos_critical_packet {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {S : Finset ℕ} (hS : ∀ e ∈ S, 0 < e) {b : ℕ → ℝ} (hb : ∃ e ∈ S, b e ≠ 0) :
    ∀ᶠ N : ℕ in atTop, 0 < ∑ e ∈ S, ∑ l ∈ S, b e * b l * conductorEntry (c N) N e l := by
  have hdiag : 0 < ∑ e ∈ S, jordanCoefficient e * b e ^ 2 := by
    obtain ⟨e, he, hbe⟩ := hb
    refine sum_pos' (fun e he => mul_nonneg (jordanCoefficient_pos (hS e he)).le (sq_nonneg _))
      ⟨e, he, mul_pos (jordanCoefficient_pos (hS e he)) (sq_pos_of_ne_zero hbe)⟩
  have hpolar : 0 ≤ if 1 ∈ S then criticalGenusCoefficient R * b 1 ^ 2 else 0 := by
    split_ifs
    · exact mul_nonneg (criticalGenusCoefficient_nonneg hR.le) (sq_nonneg _)
    · exact le_rfl
  filter_upwards [(tendsto_critical_rescaled_packet hc hR hcrit hS b).eventually
    (lt_mem_nhds (add_pos_of_pos_of_nonneg hdiag hpolar))] with N hN
  have hc7 : 0 < c N ^ (7 : ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans_le (hc N)) _
  have heq : (∑ e ∈ S, ∑ l ∈ S, b e * b l * rescaledConductorGram (c N) N e l) =
      c N ^ (7 : ℝ) * ∑ e ∈ S, ∑ l ∈ S, b e * b l * conductorEntry (c N) N e l := by
    simp only [rescaledConductorGram, mul_sum]
    exact sum_congr rfl fun e _ => sum_congr rfl fun l _ => by ring
  rw [heq] at hN
  exact pos_of_mul_pos_right hN hc7.le

/-- Each fixed conductor block is eventually positive definite, uniformly in its coefficients. -/
theorem eventually_posDef_critical_conductor_block {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N)
    {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) (Q : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      Matrix.PosDef (fun i j : Fin Q => rescaledConductorGram (c N) N (i.val + 1) (j.val + 1)) := by
  let w : Fin Q → ℝ := fun i => jordanCoefficient (i.val + 1) +
    (if i.val + 1 = 1 then criticalGenusCoefficient R else 0)
  have hw : (Matrix.diagonal w).PosDef := Matrix.posDef_diagonal_iff.mpr fun i => by
    apply add_pos_of_pos_of_nonneg (jordanCoefficient_pos (Nat.succ_pos _))
    split_ifs
    · exact criticalGenusCoefficient_nonneg hR.le
    · exact le_rfl
  have hHerm : ∀ N : ℕ,
      Matrix.IsHermitian (fun i j : Fin Q => rescaledConductorGram (c N) N (i.val + 1) (j.val + 1)) := by
    intro N
    apply Matrix.IsHermitian.ext
    intro i j
    change rescaledConductorGram (c N) N (j.val + 1) (i.val + 1) =
      rescaledConductorGram (c N) N (i.val + 1) (j.val + 1)
    have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (completeWeilMatrix_isHermitian tiltedUnitSpline (c N) N))
        (normalizedRamanujanHorizonVector (j.val + 1) N)
        (normalizedRamanujanHorizonVector (i.val + 1) N)
    dsimp only [rescaledConductorGram, conductorEntry]
    rw [hsym, real_inner_comm]
  apply HTGeometry.posDef_eventually_of_tendsto hw (Eventually.of_forall hHerm)
  intro i j
  have h := tendsto_critical_rescaledConductorGram hc hR hcrit
    (Nat.succ_pos i.val) (Nat.succ_pos j.val)
  have hval : ((if i.val + 1 = j.val + 1 then jordanCoefficient (i.val + 1) else 0) +
      (if i.val + 1 = 1 ∧ j.val + 1 = 1 then criticalGenusCoefficient R else 0)) =
      Matrix.diagonal w i j := by
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, if_true, and_self, w]
    · have hnat : i.val + 1 ≠ j.val + 1 := by
        intro hnat
        apply hij
        apply Fin.ext
        omega
      have hpolar : ¬(i.val + 1 = 1 ∧ j.val + 1 = 1) :=
        fun h => hnat (h.1.trans h.2.symm)
      simp only [if_neg hnat, if_neg hpolar, zero_add]
      change 0 = if i = j then w i else 0
      rw [if_neg hij]
  rwa [hval] at h

end GaloisForLFunctions.ArithmeticDegenerationTheory

#print axioms GaloisForLFunctions.ArithmeticDegenerationTheory.tendsto_critical_rescaledConductorGram
#print axioms GaloisForLFunctions.ArithmeticDegenerationTheory.tendsto_critical_rescaled_packet
#print axioms GaloisForLFunctions.ArithmeticDegenerationTheory.eventually_pos_critical_packet
#print axioms GaloisForLFunctions.ArithmeticDegenerationTheory.eventually_posDef_critical_conductor_block
