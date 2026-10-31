import GaloisForLFunctions.ArithmeticIndexDescent.TheSharpEulerHeadCouplesDetailsToFarWindows
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.ThePoleHyperplaneIsTheHarmonicHyperplane

/-!
# Full prime windows cancel the growing-head pole

For a fixed Haar detail and a far coarse window, the literal sum over all
prime powers has the same leading square-root term as the mixed pole.
Window PNT gives the limit; exact support identifies the entire Euler tail.
Cancellation is uniform over bounded coefficients in a fixed finite family.
-/

namespace GaloisForLFunctions.ArithmeticIndexDescent
noncomputable section
open MeasureTheory Finset Filter Topology
open GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells


/-- Both window truncations are inactive on the support of every positive-index detail. -/
private theorem full_window_limit (b : ℕ) {u : ℝ} (hu : Real.log 2 ≤ u) :
    Real.sqrt ((b : ℝ) + 1) * windowLimit b (u + Real.log ((b : ℝ) + 1)) =
      4 * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) * Real.exp (-u / 2) := by
  have hr : 0 < (b : ℝ) + 1 := by positivity
  have he : Real.exp (-u) ≤ 1 / 2 := by
    have h := Real.exp_le_exp.mpr (neg_le_neg hu)
    simpa only [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div] using h
  have hexp : Real.exp (-(u + Real.log ((b : ℝ) + 1))) =
      Real.exp (-u) / ((b : ℝ) + 1) := by
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log ((b : ℝ) + 1)),
      Real.exp_log hr, div_eq_mul_inv]
  have hmul := mul_le_mul_of_nonneg_left he hr.le
  have h1 : (2 * (b : ℝ) + 2) * Real.exp (-u) / ((b : ℝ) + 1) ≤ 1 := by
    rw [div_le_iff₀ hr]
    linarith only [hmul]
  have h0 : 2 * (b : ℝ) * Real.exp (-u) / ((b : ℝ) + 1) ≤ 1 := by
    apply le_trans (div_le_div_of_nonneg_right ?_ hr.le) h1
    nlinarith only [(Real.exp_pos (-u)).le]
  rw [windowLimit, hexp, ← mul_div_assoc, ← mul_div_assoc,
    min_eq_left h1, min_eq_left h0,
    Real.sqrt_div (by positivity), Real.sqrt_div (by positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), ← Real.exp_half]
  field_simp [(Real.sqrt_pos.mpr hr).ne']

/-- The prime trace through the last integer that can meet a detail supported above `log 2`. -/
def fullPrimeWindowTrace (Y b : ℕ) (u : ℝ) : ℝ :=
  headTrace ((b + 1) * Y) b (u + Real.log ((b : ℝ) + 1))

theorem fullPrimeWindowTrace_eq {Y : ℕ} (hY : 1 ≤ Y) (b : ℕ) (u : ℝ) :
    fullPrimeWindowTrace Y b u =
      ∑ m ∈ Icc 1 ((b + 1) * Y),
        2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m *
          coarseProfile b (u + (Real.log m - Real.log Y)) := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  unfold fullPrimeWindowTrace headTrace
  refine sum_congr rfl fun m _ => ?_
  congr 2
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Real.log_mul (by positivity) hY0.ne']
  ring

theorem tendsto_fullPrimeWindowTrace {b : ℕ} (hb : 1 ≤ b) {u : ℝ}
    (hu : Real.log 2 ≤ u) :
    Tendsto (fun Y : ℕ => fullPrimeWindowTrace Y b u / Real.sqrt Y) atTop
      (𝓝 (4 * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) * Real.exp (-u / 2))) := by
  have hr : 0 < (b : ℝ) + 1 := by positivity
  have hm : Tendsto (fun Y : ℕ => (b + 1) * Y) atTop atTop :=
    tendsto_atTop_mono (fun Y => by
      change Y ≤ (b + 1) * Y
      nlinarith only [Nat.zero_le (b * Y)]) tendsto_id
  have h := ((tendsto_headTrace hb (u + Real.log ((b : ℝ) + 1))).comp hm).const_mul
    (Real.sqrt ((b : ℝ) + 1))
  rw [full_window_limit b hu] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with Y hY
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  dsimp only [Function.comp_apply]
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.sqrt_mul hr.le]
  unfold fullPrimeWindowTrace
  field_simp [(Real.sqrt_pos.mpr hr).ne', (Real.sqrt_pos.mpr hY0).ne']

/-- Full prime-window coupling with a logarithmic profile. -/
def fullPrimeWindowCoupling (f : ℝ → ℝ) (Y b : ℕ) : ℝ :=
  ∫ u, f u * fullPrimeWindowTrace Y b u

private theorem fullPrimeWindowTrace_nonneg_le {Y b : ℕ} (hY : 1 ≤ Y) (hb : 1 ≤ b)
    (u : ℝ) :
    0 ≤ fullPrimeWindowTrace Y b u ∧
      fullPrimeWindowTrace Y b u ≤
        (4 * RHTower.FreeLagTrace.chebyshevConst * Real.sqrt ((b : ℝ) + 1)) * Real.sqrt Y := by
  have hRY : 1 ≤ (b + 1) * Y := by nlinarith only [hY, Nat.zero_le (b * Y)]
  have h := headTrace_nonneg_le hRY hb (u + Real.log ((b : ℝ) + 1))
  rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Real.sqrt_mul (by positivity)] at h
  exact ⟨h.1, h.2.trans_eq (by ring)⟩

/-- Window PNT and an integrable Chebyshev majorant identify the full mixed limit. -/
theorem tendsto_fullPrimeWindowCoupling {f : ℝ → ℝ} (hf : Integrable f)
    (hsupp : ∀ u, u < Real.log 2 → f u = 0) {b : ℕ} (hb : 1 ≤ b) :
    Tendsto (fun Y : ℕ => fullPrimeWindowCoupling f Y b / Real.sqrt Y) atTop
      (𝓝 (4 * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) *
        ∫ u, f u * Real.exp (-u / 2))) := by
  let C := 4 * RHTower.FreeLagTrace.chebyshevConst * Real.sqrt ((b : ℝ) + 1)
  let k := 4 * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b))
  have h : Tendsto
      (fun Y : ℕ => ∫ u, f u * (fullPrimeWindowTrace Y b u / Real.sqrt Y)) atTop
      (𝓝 (∫ u, f u * (k * Real.exp (-u / 2)))) := by
    refine tendsto_integral_of_dominated_convergence (fun u => |f u| * |C|)
      (fun Y => hf.aestronglyMeasurable.mul
        (((measurable_headTrace ((b + 1) * Y) b).comp
          (measurable_add_const _)).div_const _).aestronglyMeasurable)
      (hf.abs.mul_const _) (fun Y => Eventually.of_forall fun u => ?_)
      (Eventually.of_forall fun u => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rcases Nat.eq_zero_or_pos Y with rfl | hY
      · simp only [fullPrimeWindowTrace, mul_zero, headTrace, Nat.cast_zero,
          Real.sqrt_zero, div_zero, abs_zero]
        exact abs_nonneg _
      · obtain ⟨h0, h1⟩ := fullPrimeWindowTrace_nonneg_le hY hb u
        have hY0 : 0 < Real.sqrt (Y : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hY)
        rw [abs_of_nonneg (div_nonneg h0 hY0.le), div_le_iff₀ hY0]
        exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hY0.le)
    · by_cases hu : Real.log 2 ≤ u
      · exact (tendsto_fullPrimeWindowTrace hb hu).const_mul (f u)
      · simp only [hsupp u (lt_of_not_ge hu), zero_mul]
        exact tendsto_const_nhds
  have heq : (∫ u, f u * (k * Real.exp (-u / 2))) = k * ∫ u, f u * Real.exp (-u / 2) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  rw [heq] at h
  refine h.congr fun Y => ?_
  rw [fullPrimeWindowCoupling, ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with u
  ring

#print axioms tendsto_fullPrimeWindowCoupling

theorem fullPrimeWindowCoupling_haar_eq {Y a b : ℕ} (hY : 1 ≤ Y) (hb : 1 ≤ b) :
    fullPrimeWindowCoupling (haarProfile a) Y b =
      ∑ m ∈ Icc 1 ((b + 1) * Y), headTerm Y a b m := by
  have heq : (fun u => haarProfile a u * fullPrimeWindowTrace Y b u) =
      (fun u => ∑ m ∈ Icc 1 ((b + 1) * Y),
        (2 * ArithmeticFunction.vonMangoldt m / Real.sqrt m) *
          (haarProfile a u * coarseProfile b (u + (Real.log m - Real.log Y)))) := by
    funext u
    rw [fullPrimeWindowTrace_eq hY, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [fullPrimeWindowCoupling, heq, integral_finsetSum _ (fun m _ =>
    (integrable_haarProfile_mul_coarseProfile a hb _).const_mul _)]
  apply Finset.sum_congr rfl
  intro m _
  rw [integral_const_mul]
  rfl

theorem tendsto_fullPrimeWindowCoupling_haar {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Tendsto (fun Y : ℕ => fullPrimeWindowCoupling (haarProfile a) Y b / Real.sqrt Y) atTop
      (𝓝 (4 * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) *
        ∫ u, haarProfile a u * Real.exp (-u / 2))) := by
  apply tendsto_fullPrimeWindowCoupling (integrable_haarProfile a) _ hb
  intro u hu
  apply haarProfile_zero_outside_pair ha
  intro hm
  have hlog : Real.log (2 : ℝ) ≤ Real.log ((2 * a : ℕ) : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ 2 * a by omega))
  exact (not_le_of_gt (hu.trans_le hlog)) hm.1

#print axioms tendsto_fullPrimeWindowCoupling_haar

/-- The support geometry removes every integer beyond the full window exactly. -/
theorem headTerm_eq_zero_beyond_fullWindow {Y a b : ℕ}
    (hY : 1 ≤ Y) (ha : 1 ≤ a) (hb : 1 ≤ b) {m : ℕ}
    (hm : (b + 1) * Y < m) : headTerm Y a b m = 0 := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  rw [headTerm, headCouplingKernel_eq_zero hb, mul_zero]
  have hlog : Real.log Y + Real.log ((b : ℝ) + 1) ≤ Real.log m := by
    rw [← Real.log_mul hY0.ne' (by positivity)]
    apply Real.log_le_log (by positivity)
    have hM : (((b + 1) * Y : ℕ) : ℝ) ≤ m := by exact_mod_cast hm.le
    push_cast at hM
    nlinarith only [hM]
  have ha0 : 0 ≤ Real.log (a : ℝ) := Real.log_nonneg (by exact_mod_cast ha)
  have h2b : Real.log ((2 * b + 2 : ℕ) : ℝ) =
      Real.log 2 + Real.log ((b : ℝ) + 1) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    push_cast
    ring_nf
  have h2a : Real.log ((2 * a : ℕ) : ℝ) = Real.log 2 + Real.log (a : ℝ) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    push_cast
    ring_nf
  rw [h2b, h2a]
  linarith only [hlog, ha0]

theorem fullPrimeWindowCoupling_haar_eq_euler {Y a b : ℕ}
    (hY : 1 ≤ Y) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    fullPrimeWindowCoupling (haarProfile a) Y b =
      ∑ p ∈ eulerHead ((b + 1) * Y), ∑' k : ℕ, headTerm Y a b ((p : ℕ) ^ (k + 1)) := by
  classical
  let M := (b + 1) * Y
  let F := headTerm Y a b
  have hF0 : ∀ m, M < m → F m = 0 :=
    fun m hm => headTerm_eq_zero_beyond_fullWindow hY ha hb hm
  have hΛ : ∀ m, ArithmeticFunction.vonMangoldt m = 0 → F m = 0 := by
    intro m hm
    simp only [F, headTerm, hm, mul_zero, zero_div, zero_mul]
  have hbij : (∑ p ∈ eulerHead M, ∑' k : ℕ, F ((p : ℕ) ^ (k + 1))) =
      ∑ p ∈ Nat.primesLE M, ∑' k : ℕ, F (p ^ (k + 1)) :=
    Finset.sum_bij (fun (p : Nat.Primes) _ => (p : ℕ))
      (fun p hp => Nat.mem_primesLE.mpr ⟨mem_eulerHead.mp hp, p.property⟩)
      (fun p _ q _ h => Subtype.ext h)
      (fun n hn => ⟨⟨n, (Nat.mem_primesLE.mp hn).2⟩,
        mem_eulerHead.mpr (Nat.mem_primesLE.mp hn).1, rfl⟩) (fun _ _ => rfl)
  rw [fullPrimeWindowCoupling_haar_eq hY hb]
  change (∑ m ∈ Icc 1 M, F m) = _
  rw [hbij]
  have htrunc : (∑ p ∈ Nat.primesLE M, ∑' k : ℕ, F (p ^ (k + 1))) =
      ∑ p ∈ Nat.primesLE M, ∑ e ∈ Icc 1 (p.log M), F (p ^ e) :=
    Finset.sum_congr rfl fun p hp => tsum_primePow_eq_sum hF0 p (Nat.mem_primesLE.mp hp).2
  rw [htrunc, ← RHTower.sum_primePow_Icc_eq_sum_primesLE, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs with hm
  · rfl
  · exact hΛ m (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hm)

/-- Every prime omitted by the sharp head but still visible to the full mixed source. -/
def fullPrimeWindowTail (Y a b : ℕ) : ℝ :=
  ∑ p ∈ eulerHead ((b + 1) * Y) \ eulerHead Y,
    ∑' k : ℕ, headTerm Y a b ((p : ℕ) ^ (k + 1))

theorem fullPrimeWindowCoupling_eq_head_add_tail {Y a b : ℕ}
    (hY : 1 ≤ Y) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    fullPrimeWindowCoupling (haarProfile a) Y b =
      headCoupling Y a b + fullPrimeWindowTail Y a b := by
  classical
  rw [fullPrimeWindowCoupling_haar_eq_euler hY ha hb]
  have hsub : eulerHead Y ⊆ eulerHead ((b + 1) * Y) := by
    intro p hp
    apply mem_eulerHead.mpr
    exact (mem_eulerHead.mp hp).trans (by nlinarith only [Nat.zero_le (b * Y)])
  simpa only [headCoupling, fullPrimeWindowTail, add_comm] using
    (Finset.sum_sdiff hsub (f := fun p : Nat.Primes =>
      ∑' k : ℕ, headTerm Y a b ((p : ℕ) ^ (k + 1)))).symm

#print axioms fullPrimeWindowCoupling_eq_head_add_tail

theorem integral_coarseProfile_mul_exp_half {b : ℕ} (hb : 1 ≤ b) :
    (∫ u, coarseProfile b u * Real.exp (u / 2)) =
      2 * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) := by
  let l := Real.log ((2 * b : ℕ) : ℝ)
  let r := Real.log ((2 * b + 2 : ℕ) : ℝ)
  have hlr : l ≤ r := Real.log_le_log (by positivity)
    (by exact_mod_cast (show 2 * b ≤ 2 * b + 2 by omega))
  have heq : (fun u => coarseProfile b u * Real.exp (u / 2)) =
      (Set.Ico l r).indicator (fun u => Real.exp (u / 2)) := by
    funext u
    rw [coarseProfile_eq_indicator hb]
    by_cases hu : u ∈ Set.Ico l r
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, one_mul]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, zero_mul]
  rw [heq, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hlr]
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => 2 * Real.exp (v / 2))
      (Real.exp (u / 2)) u := by
    have h : HasDerivAt (fun v : ℝ => 2 * Real.exp (v / 2))
        (2 * (Real.exp (u / 2) * (1 / 2))) u :=
      (((hasDerivAt_id u).div_const 2).exp.const_mul 2)
    convert h using 1
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((Real.continuous_exp.comp (continuous_id.div_const 2)).intervalIntegrable _ _)]
  dsimp only [l, r]
  rw [exp_half_log_eq_sqrt (by omega), exp_half_log_eq_sqrt (by omega)]
  push_cast
  ring

theorem integral_farCoarse_exp_half {Y : ℕ} (hY : 1 ≤ Y) (b : ℕ) :
    (∫ u, coarseProfile b (u - Real.log Y) * Real.exp (u / 2)) =
      Real.sqrt Y * ∫ u, coarseProfile b u * Real.exp (u / 2) := by
  have h := integral_shift_mul_exp (coarseProfile b) (Real.log Y) (1 / 2)
  simp only [show ∀ u : ℝ, (1 / 2) * u = u / 2 from fun u => by ring] at h
  rwa [exp_half_log_eq_sqrt hY] at h

theorem integral_farCoarse_exp_neg_half {Y : ℕ} (hY : 1 ≤ Y) (b : ℕ) :
    (∫ u, coarseProfile b (u - Real.log Y) * Real.exp (-u / 2)) =
      (1 / Real.sqrt Y) * ∫ u, coarseProfile b u * Real.exp (-u / 2) := by
  have h := integral_shift_mul_exp (coarseProfile b) (Real.log Y) (-(1 / 2))
  simp only [show ∀ u : ℝ, -(1 / 2) * u = -u / 2 from fun u => by ring] at h
  rw [show -(Real.log (Y : ℝ)) / 2 = -(Real.log Y / 2) by ring,
    exp_neg_half_log_eq hY] at h
  exact h

#print axioms integral_coarseProfile_mul_exp_half

/-- Both cross terms of the actual quadratic pole pairing. -/
def fullPrimeWindowMixedPole (Y a b : ℕ) : ℝ :=
  2 * (∫ u, haarProfile a u * Real.exp (-u / 2)) *
      (∫ u, coarseProfile b (u - Real.log Y) * Real.exp (u / 2)) +
    2 * (∫ u, haarProfile a u * Real.exp (u / 2)) *
      (∫ u, coarseProfile b (u - Real.log Y) * Real.exp (-u / 2))

theorem fullPrimeWindowMixedPole_div_sqrt {Y a b : ℕ} (hY : 1 ≤ Y) (hb : 1 ≤ b) :
    fullPrimeWindowMixedPole Y a b / Real.sqrt Y =
      4 * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) *
        (∫ u, haarProfile a u * Real.exp (-u / 2)) +
      (2 * (∫ u, haarProfile a u * Real.exp (u / 2)) *
        (∫ u, coarseProfile b u * Real.exp (-u / 2))) / (Y : ℝ) := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hs0 : Real.sqrt (Y : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hY0).ne'
  rw [fullPrimeWindowMixedPole, integral_farCoarse_exp_half hY,
    integral_farCoarse_exp_neg_half hY, integral_coarseProfile_mul_exp_half hb]
  have hs : (Y : ℝ) = Real.sqrt (Y : ℝ) * Real.sqrt Y :=
    (Real.mul_self_sqrt hY0.le).symm
  conv_rhs => rw [hs]
  field_simp [hs0]
  ring

theorem tendsto_fullPrimeWindowMixedPole {a b : ℕ} (hb : 1 ≤ b) :
    Tendsto (fun Y : ℕ => fullPrimeWindowMixedPole Y a b / Real.sqrt Y) atTop
      (𝓝 (4 * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) *
        ∫ u, haarProfile a u * Real.exp (-u / 2))) := by
  let L := 4 * (Real.sqrt (2 * b + 2) - Real.sqrt (2 * b)) *
    ∫ u, haarProfile a u * Real.exp (-u / 2)
  let C := 2 * (∫ u, haarProfile a u * Real.exp (u / 2)) *
    ∫ u, coarseProfile b u * Real.exp (-u / 2)
  have hsmall : Tendsto (fun Y : ℕ => C / (Y : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h : Tendsto (fun Y : ℕ => L + C / (Y : ℝ)) atTop (𝓝 L) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hsmall :
      Tendsto (fun Y : ℕ => L + C / (Y : ℝ)) atTop (𝓝 (L + 0)))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with Y hY
  exact (fullPrimeWindowMixedPole_div_sqrt hY hb).symm

/-- Including the full Euler tail cancels the head--pole square-root discrepancy. -/
theorem tendsto_head_add_tail_sub_mixedPole_div_sqrt {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Tendsto (fun Y : ℕ =>
      (headCoupling Y a b + fullPrimeWindowTail Y a b - fullPrimeWindowMixedPole Y a b) /
        Real.sqrt Y) atTop (𝓝 0) := by
  have h := (tendsto_fullPrimeWindowCoupling_haar ha hb).sub
    (tendsto_fullPrimeWindowMixedPole (a := a) hb)
  simp only [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with Y hY
  rw [fullPrimeWindowCoupling_eq_head_add_tail hY ha hb, sub_div]

#print axioms tendsto_head_add_tail_sub_mixedPole_div_sqrt

theorem fullPrimeWindowCoupling_eq_finiteEulerMixedSource {Y a b X : ℕ}
    (hY : 1 ≤ Y) (ha : 1 ≤ a) (hb : 1 ≤ b) (haX : a ≤ X)
    (hX : Y * (b + 1) ≤ X + 1) :
    fullPrimeWindowCoupling (haarProfile a) Y b =
      finiteEulerMixedSource (eulerHead ((b + 1) * Y))
        (detailUnit a) (coarseWindow Y b) X := by
  rw [fullPrimeWindowCoupling_haar_eq_euler hY ha hb]
  unfold finiteEulerMixedSource primeEulerMixedSource
  apply Finset.sum_congr rfl
  intro p _
  apply tsum_congr
  intro k
  rw [integerMixedSource_detailUnit_coarseWindow ha haX hY hb hX]
  rfl

theorem tendsto_fullEulerMixedSource_sub_pole_div_sqrt {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Tendsto (fun Y : ℕ =>
      (finiteEulerMixedSource (eulerHead ((b + 1) * Y))
        (detailUnit a) (coarseWindow Y b) (a + (b + 1) * Y) -
          fullPrimeWindowMixedPole Y a b) / Real.sqrt Y) atTop (𝓝 0) := by
  have h := (tendsto_fullPrimeWindowCoupling_haar ha hb).sub
    (tendsto_fullPrimeWindowMixedPole (a := a) hb)
  simp only [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with Y hY
  rw [fullPrimeWindowCoupling_eq_finiteEulerMixedSource (X := a + (b + 1) * Y) hY ha hb (by omega)
    (by nlinarith only [Nat.zero_le a]), sub_div]

#print axioms tendsto_fullEulerMixedSource_sub_pole_div_sqrt

theorem primeEulerMixedSource_eq_zero_beyond_fullWindow {Y a b X : ℕ}
    (hY : 1 ≤ Y) (ha : 1 ≤ a) (hb : 1 ≤ b) (haX : a ≤ X)
    (hX : Y * (b + 1) ≤ X + 1) (p : Nat.Primes)
    (hp : (b + 1) * Y < (p : ℕ)) :
    primeEulerMixedSource p (detailUnit a) (coarseWindow Y b) X = 0 := by
  calc
    _ = ∑' _ : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro k
      rw [integerMixedSource_detailUnit_coarseWindow ha haX hY hb hX]
      change headTerm Y a b ((p : ℕ) ^ (k + 1)) = 0
      apply headTerm_eq_zero_beyond_fullWindow hY ha hb
      apply hp.trans_le
      calc
        (p : ℕ) = (p : ℕ) ^ 1 := by rw [pow_one]
        _ ≤ (p : ℕ) ^ (k + 1) := Nat.pow_le_pow_right p.property.pos (by omega)
    _ = 0 := tsum_zero

theorem fullPrimeWindowCoupling_eq_tsum_euler {Y a b X : ℕ}
    (hY : 1 ≤ Y) (ha : 1 ≤ a) (hb : 1 ≤ b) (haX : a ≤ X)
    (hX : Y * (b + 1) ≤ X + 1) :
    fullPrimeWindowCoupling (haarProfile a) Y b =
      ∑' p : Nat.Primes, primeEulerMixedSource p (detailUnit a) (coarseWindow Y b) X := by
  rw [fullPrimeWindowCoupling_eq_finiteEulerMixedSource hY ha hb haX hX]
  symm
  apply tsum_eq_sum
  intro p hp
  apply primeEulerMixedSource_eq_zero_beyond_fullWindow hY ha hb haX hX
  exact lt_of_not_ge (fun h => hp (mem_eulerHead.mpr h))

/-- The literal all-prime mixed source and both pole terms cancel at square-root scale. -/
theorem tendsto_allPrimesMixedSource_sub_pole_div_sqrt {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Tendsto (fun Y : ℕ =>
      ((∑' p : Nat.Primes, primeEulerMixedSource p
        (detailUnit a) (coarseWindow Y b) (a + (b + 1) * Y)) -
          fullPrimeWindowMixedPole Y a b) / Real.sqrt Y) atTop (𝓝 0) := by
  have h := (tendsto_fullPrimeWindowCoupling_haar ha hb).sub
    (tendsto_fullPrimeWindowMixedPole (a := a) hb)
  simp only [sub_self] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with Y hY
  rw [fullPrimeWindowCoupling_eq_tsum_euler (X := a + (b + 1) * Y) hY ha hb (by omega)
    (by nlinarith only [Nat.zero_le a]), sub_div]

#print axioms tendsto_allPrimesMixedSource_sub_pole_div_sqrt

/-- The normalized full prime--pole remainder of one detail--window pair. -/
def fullPrimeWindowRemainder (Y a b : ℕ) : ℝ :=
  ((∑' p : Nat.Primes, primeEulerMixedSource p
    (detailUnit a) (coarseWindow Y b) (a + (b + 1) * Y)) -
      fullPrimeWindowMixedPole Y a b) / Real.sqrt Y

/-- The cancellation is uniform over bounded coefficients on every fixed finite family. -/
theorem fullPrimeWindowRemainder_uniform_finite_family (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, 1 ≤ p.1 ∧ 1 ≤ p.2) {B : ℝ}
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Y : ℕ in atTop, ∀ c : ℕ × ℕ → ℝ, (∀ p ∈ S, |c p| ≤ B) →
      |∑ p ∈ S, c p * fullPrimeWindowRemainder Y p.1 p.2| < ε := by
  have hsum : Tendsto (fun Y : ℕ => ∑ p ∈ S, |fullPrimeWindowRemainder Y p.1 p.2|)
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum S (fun p hp =>
      (tendsto_allPrimesMixedSource_sub_pole_div_sqrt (hS p hp).1 (hS p hp).2).abs)
    simpa only [abs_zero, Finset.sum_const_zero, fullPrimeWindowRemainder] using h
  have hlim : Tendsto (fun Y : ℕ =>
      (B + 1) * ∑ p ∈ S, |fullPrimeWindowRemainder Y p.1 p.2|) atTop (𝓝 0) := by
    simpa only [mul_zero] using hsum.const_mul (B + 1)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with Y hY
  intro c hc
  calc
    _ ≤ ∑ p ∈ S, |c p * fullPrimeWindowRemainder Y p.1 p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ S, B * |fullPrimeWindowRemainder Y p.1 p.2| := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hc p hp) (abs_nonneg _)
    _ = B * ∑ p ∈ S, |fullPrimeWindowRemainder Y p.1 p.2| := (Finset.mul_sum _ _ _).symm
    _ ≤ (B + 1) * ∑ p ∈ S, |fullPrimeWindowRemainder Y p.1 p.2| :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    _ < ε := hY

#print axioms fullPrimeWindowRemainder_uniform_finite_family

end
end GaloisForLFunctions.ArithmeticIndexDescent
