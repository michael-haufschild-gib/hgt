import GaloisForLFunctions.ArithmeticCriticalityTheory.ReflectedPrimeMassAsymptotics
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateFoldExcessThresholdAndOddProfileDomination

/-!
# The weight criterion fails for every large shift

On even profiles `u ≥ 0` nonincreasing on `[0, ∞)`, fold domination gives
`Q(m_a u) ≥ 4 sinh(a/2) ∫ u² dμ_a − 2 ∫_{x>0} u² m_a W_a`, with the fold excess weight
`W_a(x) = ∫_{t>2x} dm(t) (m_a(t − x) − m_a(x + t))⁺`, so the **weight criterion**
`W_a(x) ≤ 2 sinh(a/2) sinh(x/2)` for all `x > 0` would give positivity on the whole monotone cone
(`markovEnergy_phiDoob_shiftedGroundState_nonneg_of_antitone_of_weight_le`).

**Theorem** (`exists_foldExcessWeight_gt_criterion`). For every `x` with `0 < 2x < log 2` there is
`A` such that `W_a(x) > 2 sinh(a/2) sinh(x/2)` for all `a ≥ A`. Hence the criterion fails for every
large shift (`exists_not_weightCriterion`).

Proof. The fold excess of the shifted ground state at `x` is a shift difference read at `a`:
`m_a(t − x) − m_a(t + x) = m_x(t − a) − m_x(t + a)`. All prime atoms have `log n > 2x`, so dropping the
positive parts and the arguments `log n ≤ a`,

    W_a(x) ≥ Σ_{log n > a} Λ(n) n^{−1/2} m_x(log n − a) − (bounded),

the reflected prime mass of the profile `m_x` at `a`. By the prime number theorem
(`tendsto_exp_neg_half_mul_reflectedPrimeMass`) it is `e^{a/2}(κ_x + o(1))`, with
`κ_x = ∫_0^∞ e^{r/2} m_x = sinh(x/2) + ∫_0^∞ e^{−r/2} m_x`, while the criterion is
`e^{a/2}(sinh(x/2) + o(1))`. The criterion fails by exactly the moment at the other pole,
`∫_0^∞ e^{−r/2} m_x(r) dr > 0`, the same excess as in the collar ratio `R(a)`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- `m_a(t − x) − m_a(x + t) = m_x(t − a) − m_x(t + a)`. -/
theorem shiftDifference_sub_shiftDifference_eq (a x t : ℝ) :
    shiftDifference a (t - x) - shiftDifference a (x + t) =
      shiftDifference x (t - a) - shiftDifference x (t + a) := by
  unfold shiftDifference
  rw [show t - x - a = t - a - x by ring, show t - x + a = t + a - x by ring,
    show x + t - a = t - a + x by ring, show x + t + a = t + a + x by ring]
  ring

/-- `κ_x = ∫_0^∞ e^{r/2} m_x = sinh(x/2) + ∫_0^∞ e^{−r/2} m_x`. -/
theorem integral_Ioi_exp_half_mul_shiftDifference_eq (x : ℝ) :
    (∫ r in Ioi (0 : ℝ), Real.exp (r / 2) * shiftDifference x r) =
      Real.sinh (x / 2) + ∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference x r := by
  have hmi : IntegrableOn (fun r => shiftDifference x r * Real.sinh (r / 2)) (Ioi 0) :=
    (integrable_shiftDifference_mul_sinh_half x).integrableOn
  have hm : Integrable (shiftDifference x) :=
    (integrable_riemannKernelReal.comp_sub_right x).sub (integrable_riemannKernelReal.comp_add_right x)
  have hei : IntegrableOn (fun r => Real.exp (-r / 2) * shiftDifference x r) (Ioi 0) := by
    refine (hm.norm.integrableOn).mono' ((Real.continuous_exp.comp (continuous_neg.div_const 2)).mul
      (continuous_shiftDifference x)).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    have : Real.exp (-r / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [mem_Ioi.mp hr])
    nlinarith [abs_nonneg (shiftDifference x r)]
  have e : (fun r => Real.exp (r / 2) * shiftDifference x r) =
      fun r => 2 * (shiftDifference x r * Real.sinh (r / 2)) +
        Real.exp (-r / 2) * shiftDifference x r := funext fun r => by
    rw [Real.sinh_eq, neg_div]; ring
  rw [e, integral_add (hmi.const_mul 2) hei, integral_const_mul,
    integral_Ioi_shiftDifference_mul_sinh_half]
  ring

/-- **Prime lower bound for the fold excess weight.** For `0 < 2x < log 2`:
`W_a(x) ≥ Σ_{log n > a} Λ(n)n^{−1/2} m_x(log n − a) − Σ_{log n > a} Λ(n)n^{−1/2} m_x(log n + a)`. -/
theorem foldExcessWeight_ge {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) (hx2 : 2 * x < Real.log 2) :
    (∑' n : ℕ, vonMangoldtAtom n *
        (if a < Real.log n then shiftDifference x (Real.log n - a) else 0)) -
      (∑' n : ℕ, vonMangoldtAtom n *
        (if a < Real.log n then shiftDifference x (Real.log n + a) else 0)) ≤
      foldExcessWeight a x := by
  have h1 : Summable fun n : ℕ => vonMangoldtAtom n *
      (if a < Real.log n then shiftDifference x (Real.log n - a) else 0) := by
    refine (summable_primeShift_left (a + x)).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · refine mul_nonneg (vonMangoldtAtom_nonneg n) ?_
      split_ifs with h
      · exact shiftDifference_nonneg_of_nonneg hx.le (by linarith)
      · exact le_rfl
    · refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
      split_ifs with h
      · have := shiftDifference_le_kernel x (Real.log n - a)
        rw [show Real.log n - a - x = -(a + x - Real.log n) by ring, riemannKernelReal_neg'] at this
        exact this
      · exact (riemannKernelReal_pos _).le
  have h2 : Summable fun n : ℕ => vonMangoldtAtom n *
      (if a < Real.log n then shiftDifference x (Real.log n + a) else 0) := by
    refine (summable_primeShift_right (a - x)).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    · refine mul_nonneg (vonMangoldtAtom_nonneg n) ?_
      split_ifs with h
      · exact shiftDifference_nonneg_of_nonneg hx.le (by linarith [Real.log_natCast_nonneg n])
      · exact le_rfl
    · refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
      split_ifs with h
      · have := shiftDifference_le_kernel x (Real.log n + a)
        rw [show Real.log n + a - x = a - x + Real.log n by ring] at this
        exact this
      · exact (riemannKernelReal_pos _).le
  have hterm : ∀ n : ℕ, vonMangoldtAtom n *
      (if a < Real.log n then shiftDifference x (Real.log n - a) else 0) -
      vonMangoldtAtom n * (if a < Real.log n then shiftDifference x (Real.log n + a) else 0) ≤
      vonMangoldtAtom n * foldExcessDensity a (Real.log n) x := fun n => by
    by_cases hn : 2 ≤ n
    · have hlog2 : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      rw [foldExcessDensity_of_lt (by linarith), ← mul_sub]
      refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
      split_ifs with h
      · rw [← shiftDifference_sub_shiftDifference_eq]
        exact le_max_left _ _
      · rw [sub_zero]
        exact le_max_right _ _
    · rw [vonMangoldtAtom_eq_zero_of_lt_two (by omega)]
      simp
  have hprime : (∑' n : ℕ, vonMangoldtAtom n *
      (if a < Real.log n then shiftDifference x (Real.log n - a) else 0)) -
      (∑' n : ℕ, vonMangoldtAtom n *
        (if a < Real.log n then shiftDifference x (Real.log n + a) else 0)) ≤
      ∑' n : ℕ, vonMangoldtAtom n * foldExcessDensity a (Real.log n) x := by
    rw [← h1.tsum_sub h2]
    exact Summable.tsum_le_tsum hterm (h1.sub h2) (summable_atom_mul_foldExcessDensity ha hx.le)
  have harch : 0 ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessDensity a t x :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (archLevyDensity_pos (mem_Ioi.mp ht)).le (foldExcessDensity_nonneg a t x)
  unfold foldExcessWeight
  linarith

/-- **The weight criterion fails for every large shift**, at every fixed `x` with `0 < 2x < log 2`:
eventually in `a`, `W_a(x) > 2 sinh(a/2) sinh(x/2)`. -/
theorem exists_foldExcessWeight_gt_criterion {x : ℝ} (hx : 0 < x) (hx2 : 2 * x < Real.log 2) :
    ∃ A : ℝ, ∀ a, A ≤ a → 2 * Real.sinh (a / 2) * Real.sinh (x / 2) < foldExcessWeight a x := by
  obtain ⟨C, hC0, hdec, hdec'⟩ := exists_shiftDifference_decay hx.le
  have hT := tendsto_exp_neg_half_mul_reflectedPrimeMass (contDiff_shiftDifference x)
    (shiftDifference_zero x) hC0 hdec hdec'
  rw [integral_Ioi_exp_half_mul_shiftDifference_eq] at hT
  set E := ∫ r in Ioi (0 : ℝ), Real.exp (-r / 2) * shiftDifference x r with hE_def
  have hE : 0 < E := integral_exp_neg_half_mul_shiftDifference_pos hx
  have hcrit : Tendsto (fun a : ℝ => Real.exp (-a / 2) * (2 * Real.sinh (a / 2) * Real.sinh (x / 2)))
      atTop (𝓝 (Real.sinh (x / 2))) := by
    have h1 : Tendsto (fun a : ℝ => (1 - Real.exp (-a)) * Real.sinh (x / 2)) atTop
        (𝓝 ((1 - 0) * Real.sinh (x / 2))) :=
      (tendsto_const_nhds.sub Real.tendsto_exp_neg_atTop_nhds_zero).mul_const _
    rw [sub_zero, one_mul] at h1
    refine h1.congr fun a => ?_
    rw [Real.sinh_eq (a / 2)]
    have e1 : Real.exp (-a / 2) * Real.exp (a / 2) = 1 := by rw [← Real.exp_add]; ring_nf; simp
    have e2 : Real.exp (-a / 2) * Real.exp (-(a / 2)) = Real.exp (-a) := by
      rw [← Real.exp_add]; ring_nf
    linear_combination (-(Real.sinh (x / 2))) * e1 + Real.sinh (x / 2) * e2
  have hbd : Tendsto (fun a : ℝ => Real.exp (-a / 2) * rightPrimeShift 0) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2))).mul_const (rightPrimeShift 0)
    simpa [Function.comp_def, neg_div] using this
  have hg := (hT.sub hbd).sub hcrit
  rw [sub_zero, add_sub_cancel_left] at hg
  obtain ⟨A, hA⟩ := eventually_atTop.mp (hg.eventually (lt_mem_nhds hE))
  refine ⟨max A x, fun a ha => ?_⟩
  have haA : A ≤ a := le_trans (le_max_left _ _) ha
  have hax : x ≤ a := le_trans (le_max_right _ _) ha
  have ha0 : 0 ≤ a := le_trans hx.le hax
  have hW := foldExcessWeight_ge ha0 hx hx2
  have hT2 : (∑' n : ℕ, vonMangoldtAtom n *
      (if a < Real.log n then shiftDifference x (Real.log n + a) else 0)) ≤ rightPrimeShift 0 := by
    refine le_trans ?_ (rightPrimeShift_le_zero_point (show 0 ≤ a - x by linarith))
    unfold rightPrimeShift
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ (summable_primeShift_right (a - x))
    · refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
      split_ifs with h
      · have := shiftDifference_le_kernel x (Real.log n + a)
        rw [show Real.log n + a - x = a - x + Real.log n by ring] at this
        exact this
      · exact (riemannKernelReal_pos _).le
    · refine (summable_primeShift_right (a - x)).of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      · refine mul_nonneg (vonMangoldtAtom_nonneg n) ?_
        split_ifs with h
        · exact shiftDifference_nonneg_of_nonneg hx.le (by linarith [Real.log_natCast_nonneg n])
        · exact le_rfl
      · refine mul_le_mul_of_nonneg_left ?_ (vonMangoldtAtom_nonneg n)
        split_ifs with h
        · have := shiftDifference_le_kernel x (Real.log n + a)
          rw [show Real.log n + a - x = a - x + Real.log n by ring] at this
          exact this
        · exact (riemannKernelReal_pos _).le
  have hpos := hA a haA
  have hexp := Real.exp_pos (-a / 2)
  by_contra hle
  replace hle := not_lt.mp hle
  have : Real.exp (-a / 2) * (∑' n : ℕ, vonMangoldtAtom n *
      (if a < Real.log n then shiftDifference x (Real.log n - a) else 0)) -
      Real.exp (-a / 2) * rightPrimeShift 0 -
      Real.exp (-a / 2) * (2 * Real.sinh (a / 2) * Real.sinh (x / 2)) ≤ 0 := by
    have h3 := mul_le_mul_of_nonneg_left (hW.trans hle) hexp.le
    have h4 := mul_le_mul_of_nonneg_left hT2 hexp.le
    nlinarith
  linarith

/-- **The weight criterion of fold domination is false for every large shift.** -/
theorem exists_not_weightCriterion :
    ∃ A : ℝ, ∀ a, A ≤ a →
      ¬ ∀ x, 0 < x → foldExcessWeight a x ≤ 2 * Real.sinh (a / 2) * Real.sinh (x / 2) := by
  have hlog : 2 * (1 / 4 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  obtain ⟨A, hA⟩ := exists_foldExcessWeight_gt_criterion (x := 1 / 4) (by norm_num) hlog
  exact ⟨A, fun a ha hcrit => absurd (hcrit (1 / 4) (by norm_num)) (not_le.mpr (hA a ha))⟩

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
