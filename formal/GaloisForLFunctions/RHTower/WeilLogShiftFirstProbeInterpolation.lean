import GaloisForLFunctions.RHTower.WeilTailPanelSharpPrefix
import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticDomain

/-!
# Arbitrary integer-cutoff first-probe histories

One new coefficient at each window interpolates the real first-probe value
exactly without disturbing earlier windows. The stabilized coefficients retain
every coordinate outside the lift indices. Thus arbitrary probe histories can
coexist with a nonsummable potential. In particular the integer-cutoff probe
can vanish identically while both local excess and deficit moments diverge.
No boundedness claim is made for intervening real cutoffs.
-/

open Filter Topology Zeta23 Real

noncomputable section

namespace RHTower

open WeilExcess

/-- The real m=2 probe at positive integer cutoff k+1. -/
def weilLogShiftFirstProbe (lam : ℕ → ℝ) (k : ℕ) : ℝ :=
  (weilFullFunctional lam (EF.weilTest
    (logShiftRiemannDifference ((k + 1 : ℕ) : ℝ) (log 2))
    (logShiftRiemannDifference ((k + 1 : ℕ) : ℝ) (log 2)))).re

private theorem liftIndex_gap (k : ℕ) :
    weilLogShiftLiftIndex k + 1 < weilLogShiftLiftIndex (k + 1) := by
  have hN := weilLogShiftLiftIndex_bounds k
  have hNext := (weilLogShiftLiftIndex_bounds (k + 1)).2.1
  have hthree : (3 : ℝ) < exp 2 := by
    have h := add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
    linarith only [h]
  have hE : 1 < exp (2 * ((k + 1 : ℕ) : ℝ)) := one_lt_exp_iff.mpr (by positivity)
  have hstep : exp (2 * ((k + 1 + 1 : ℕ) : ℝ)) =
      exp (2 * ((k + 1 : ℕ) : ℝ)) * exp 2 := by
    rw [← exp_add]
    congr 1
    push_cast
    ring
  rw [hstep] at hNext
  have hgap : (weilLogShiftLiftIndex k : ℝ) + 1 < weilLogShiftLiftIndex (k + 1) := by
    nlinarith only [hN.2.2.1, hNext, hthree, hE]
  exact_mod_cast hgap

private theorem liftIndex_strictMono : StrictMono weilLogShiftLiftIndex := by
  apply strictMono_nat_of_lt_succ
  intro k
  have h := liftIndex_gap k
  omega

private theorem liftIndex_succ_ne (j k : ℕ) :
    weilLogShiftLiftIndex j + 1 ≠ weilLogShiftLiftIndex k := by
  by_cases hk : k ≤ j
  · have h := liftIndex_strictMono.monotone hk
    omega
  · have h := liftIndex_strictMono.monotone (show j + 1 ≤ k by omega)
    have hg := liftIndex_gap j
    omega

private theorem index_le_exp_window (base i : ℕ) :
    (i : ℝ) ≤ exp (2 * ((base + i + 1 : ℕ) : ℝ)) := by
  have hi : (i : ℝ) ≤ ((base + i + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show i ≤ base + i + 1 by omega)
  have hx : 0 < 2 * ((base + i + 1 : ℕ) : ℝ) := by positivity
  have he := add_one_lt_exp hx.ne'
  linarith only [hi, hx, he]

private theorem sharpIndex_lt_next_window (base : ℕ) :
    (weilLogShiftSharpLiftIndex base : ℝ) < exp (2 * ((base + 2 : ℕ) : ℝ)) := by
  have he : (2 : ℝ) < exp 2 := by
    have h := add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
    linarith only [h]
  have h := mul_lt_mul_of_pos_right he (exp_pos (2 * ((base + 1 : ℕ) : ℝ)))
  apply (weilLogShiftSharpLiftIndex_bounds base).2.1.trans
  calc _ < exp 2 * exp (2 * ((base + 1 : ℕ) : ℝ)) := h
    _ = exp (2 * ((base + 2 : ℕ) : ℝ)) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring

/-- A single signed spike solves the first-probe value equation exactly. -/
theorem exists_weilLogShiftFirstProbe_exact_completion
    (k : ℕ) (lam : ℕ → ℝ) (target : ℝ) :
    ∃ a : ℝ, weilLogShiftFirstProbe
      (fun n => lam n + if n = weilLogShiftLiftIndex k then a else 0) k = target := by
  have hE : 2 < exp (2 * ((k + 1 : ℕ) : ℝ)) := by
    have hk : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ k + 1 by omega)
    have hx : 0 < 2 * ((k + 1 : ℕ) : ℝ) := by positivity
    have h := add_one_lt_exp hx.ne'
    linarith only [hk, h]
  let m : Finset.Icc 2 ⌊exp (2 * ((k + 1 : ℕ) : ℝ))⌋₊ :=
    ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_floor hE.le⟩⟩
  let slope := 2 * truncatedRiemannAutocorr ((k + 1 : ℕ) : ℝ)
    (log (weilLogShiftLiftIndex k) - log 2) / sqrt (weilLogShiftLiftIndex k)
  have hnpos : (0 : ℝ) < weilLogShiftLiftIndex k := by
    exact_mod_cast (show 0 < weilLogShiftLiftIndex k from
      lt_of_lt_of_le (by norm_num) (weilLogShiftLiftIndex_bounds k).1)
  have hslope : 0 < slope := div_pos
    (mul_pos (by norm_num) (weilLogShiftLiftIndex_kernel k m).1) (sqrt_pos.mpr hnpos)
  let a := (target - weilLogShiftFirstProbe lam k) / slope
  refine ⟨a, ?_⟩
  have hid := congrArg Complex.re (weilLogShiftWindowPanel_singleSpike k lam a m)
  simp only [Complex.add_re, Complex.ofReal_re] at hid
  change weilLogShiftFirstProbe
    (fun n => lam n + if n = weilLogShiftLiftIndex k then a else 0) k =
      weilLogShiftFirstProbe lam k + a * slope at hid
  have hcancel : a * slope = target - weilLogShiftFirstProbe lam k := by
    dsimp only [a]
    field_simp [hslope.ne']
  rw [hid, hcancel]
  ring

private def exactStep (k : ℕ) (lam : ℕ → ℝ) (target : ℝ) : ℕ → ℝ :=
  fun n => lam n + if n = weilLogShiftLiftIndex k then
    Classical.choose (exists_weilLogShiftFirstProbe_exact_completion k lam target) else 0

private theorem exactStep_off (k : ℕ) (lam : ℕ → ℝ) (target : ℝ) (n : ℕ)
    (hn : n ≠ weilLogShiftLiftIndex k) : exactStep k lam target n = lam n := by
  simp only [exactStep, if_neg hn, add_zero]

private theorem exactStep_head (k : ℕ) (lam : ℕ → ℝ) (target : ℝ) (n : ℕ)
    (hn : (n : ℝ) ≤ exp (2 * ((k + 1 : ℕ) : ℝ))) : exactStep k lam target n = lam n := by
  apply exactStep_off
  intro heq
  rw [heq] at hn
  exact (not_le_of_gt (weilLogShiftLiftIndex_bounds k).2.1) hn

private theorem exactStep_value (k : ℕ) (lam : ℕ → ℝ) (target : ℝ) :
    weilLogShiftFirstProbe (exactStep k lam target) k = target :=
  Classical.choose_spec (exists_weilLogShiftFirstProbe_exact_completion k lam target)

private def interpolationStages (base : ℕ) (lam height : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => lam
  | i + 1 => exactStep (base + i) (interpolationStages base lam height i) (height i)

private theorem interpolationStages_head_eq (base : ℕ) (lam height : ℕ → ℝ)
    (i j n : ℕ) (hij : i ≤ j)
    (hn : (n : ℝ) ≤ exp (2 * ((base + i + 1 : ℕ) : ℝ))) :
    interpolationStages base lam height j n = interpolationStages base lam height i n := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    have hb : exp (2 * ((base + i + 1 : ℕ) : ℝ)) ≤
        exp (2 * ((base + j + 1 : ℕ) : ℝ)) := by
      apply exp_le_exp.mpr
      exact_mod_cast (show 2 * (base + i + 1) ≤ 2 * (base + j + 1) by omega)
    exact (exactStep_head (base + j) (interpolationStages base lam height j)
      (height j) n (hn.trans hb)).trans ih

private def interpolationDiagonal (base : ℕ) (lam height : ℕ → ℝ) (n : ℕ) : ℝ :=
  interpolationStages base lam height n n

private theorem interpolationDiagonal_head_eq (base : ℕ) (lam height : ℕ → ℝ)
    (i n : ℕ) (hn : (n : ℝ) ≤ exp (2 * ((base + i + 1 : ℕ) : ℝ))) :
    interpolationDiagonal base lam height n = interpolationStages base lam height i n := by
  change interpolationStages base lam height n n = interpolationStages base lam height i n
  by_cases hi : i ≤ n
  · exact interpolationStages_head_eq base lam height i n n hi hn
  · exact (interpolationStages_head_eq base lam height n i n (by omega)
      (index_le_exp_window base n)).symm

/-- Arbitrary real first-probe histories admit exact arithmetic interpolation,
preserving the initial head and every coordinate outside the sparse lift set. -/
theorem exists_weilLogShiftFirstProbe_interpolation (base : ℕ) (lam height : ℕ → ℝ) :
    ∃ mu : ℕ → ℝ,
      (∀ n : ℕ, (n : ℝ) ≤ exp (2 * ((base + 1 : ℕ) : ℝ)) → mu n = lam n) ∧
      (∀ n : ℕ, (∀ j : ℕ, n ≠ weilLogShiftLiftIndex (base + j)) → mu n = lam n) ∧
      ∀ j : ℕ, weilLogShiftFirstProbe mu (base + j) = height j := by
  refine ⟨interpolationDiagonal base lam height, ?_, ?_, ?_⟩
  · intro n hn
    exact interpolationDiagonal_head_eq base lam height 0 n
      (by simpa only [Nat.add_zero] using hn)
  · intro n hn
    have hstage : ∀ i : ℕ, interpolationStages base lam height i n = lam n := by
      intro i
      induction i with
      | zero => rfl
      | succ i ih =>
        exact (exactStep_off (base + i) (interpolationStages base lam height i)
          (height i) n (hn i)).trans ih
    exact hstage n
  · intro j
    have hhead (n : ℕ) (hn : n ≤ weilLogShiftSharpLiftIndex (base + j)) :
        interpolationDiagonal base lam height n = interpolationStages base lam height (j + 1) n := by
      apply interpolationDiagonal_head_eq
      have hcast : (n : ℝ) ≤ weilLogShiftSharpLiftIndex (base + j) := by exact_mod_cast hn
      have hnext := sharpIndex_lt_next_window (base + j)
      have hle := hcast.trans hnext.le
      simpa only [Nat.add_assoc] using hle
    have hid := congrArg Complex.re (weilLogShift_firstProbe_tail_invariant (base + j)
      (interpolationDiagonal base lam height) (interpolationStages base lam height (j + 1)) hhead)
    change weilLogShiftFirstProbe (interpolationDiagonal base lam height) (base + j) =
      weilLogShiftFirstProbe (interpolationStages base lam height (j + 1)) (base + j) at hid
    rw [hid]
    exact exactStep_value (base + j) (interpolationStages base lam height j) (height j)

/-- The complete integer-cutoff history of the first probe can be arbitrary. -/
theorem weilLogShiftFirstProbe_surjective : Function.Surjective weilLogShiftFirstProbe := by
  intro height
  obtain ⟨mu, _, _, hmu⟩ := exists_weilLogShiftFirstProbe_interpolation 0 (fun _ => 0) height
  exact ⟨mu, funext fun j => by simpa only [Nat.zero_add] using hmu j⟩

/-- Even a divergent signed potential places no restriction on the first
probe's integer-cutoff history: untouched coefficients force divergent excess. -/
theorem exists_weilLogShiftFirstProbe_history_nonsummable (height : ℕ → ℝ) :
    ∃ lam : ℕ → ℝ,
      (∀ k : ℕ, weilLogShiftFirstProbe lam k = height k) ∧
      (¬ Summable fun n => deviationExcess lam n * pairedLogKernel (log 2) n) ∧
      (¬ Summable fun n => weilDeviation lam n * pairedLogKernel (log 2) n) := by
  let v (n : ℕ) := (pairedLogKernel (log 2) n)⁻¹
  obtain ⟨lam, _, hoff, hvalue⟩ :=
    exists_weilLogShiftFirstProbe_interpolation 0 (weilCoefficientLift v) height
  have hterm (j : ℕ) : deviationExcess lam (weilLogShiftLiftIndex j + 1) *
      pairedLogKernel (log 2) (weilLogShiftLiftIndex j + 1) = 1 := by
    let n := weilLogShiftLiftIndex j + 1
    have hn2 : 2 ≤ n := by have h := (weilLogShiftLiftIndex_bounds j).1; dsimp only [n]; omega
    have hcoef : lam n = weilCoefficientLift v n :=
      hoff n (fun k => by simpa only [Nat.zero_add] using liftIndex_succ_ne j k)
    have hdev : weilDeviation lam n = v n := by
      have h := weilDeviation_coefficientLift v n
      simpa only [weilDeviation, if_pos hn2, hcoef] using h
    change deviationExcess lam n * pairedLogKernel (log 2) n = 1
    rw [deviationExcess, hdev]
    have hv : 0 ≤ v n := inv_nonneg.mpr (pairedLogKernel_pos _ _).le
    rw [max_eq_left hv]
    exact inv_mul_cancel₀ (pairedLogKernel_pos _ _).ne'
  have hexc : ¬ Summable fun n => deviationExcess lam n * pairedLogKernel (log 2) n := by
    intro hs
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      ((tendsto_order.mp hs.tendsto_atTop_zero).2 1 (by norm_num))
    have hMcast : (M : ℝ) < weilLogShiftLiftIndex M := by
      have h := index_le_exp_window 0 M
      simp only [Nat.zero_add] at h
      exact h.trans_lt (weilLogShiftLiftIndex_bounds M).2.1
    have hMn : M ≤ weilLogShiftLiftIndex M + 1 := by
      have h : M < weilLogShiftLiftIndex M := by exact_mod_cast hMcast
      omega
    have hsmall := hM (weilLogShiftLiftIndex M + 1) hMn
    rw [hterm M] at hsmall
    exact (lt_irrefl (1 : ℝ)) hsmall
  refine ⟨lam, fun k => by simpa only [Nat.zero_add] using hvalue k, hexc, ?_⟩
  intro hs
  exact hexc (summable_excess_potential_of_summable_potential hs)

/-- A first probe can be exactly zero at every positive integer cutoff while
both its excess and deficit potential moments are nonsummable. Thus a bounded
integer probe alone controls neither moment in the mixed-sign case. -/
theorem exists_zero_firstProbe_with_divergent_excess_and_deficit :
    ∃ lam : ℕ → ℝ,
      (∀ k : ℕ, weilLogShiftFirstProbe lam k = 0) ∧
      (¬ Summable fun n => deviationExcess lam n * pairedLogKernel (log 2) n) ∧
      (¬ Summable fun n => deviationDeficit lam n * pairedLogKernel (log 2) n) ∧
      (¬ Summable fun n => weilDeviation lam n * pairedLogKernel (log 2) n) := by
  obtain ⟨lam, hzero, hexc, hbad⟩ :=
    exists_weilLogShiftFirstProbe_history_nonsummable (fun _ => 0)
  refine ⟨lam, hzero, hexc, ?_, hbad⟩
  intro hdef
  apply hbad
  apply (summable_potential_iff_local_deficit_and_probe_upper_bound (m := 2) (by omega)).mpr
  refine ⟨hdef, 0, 1, ?_⟩
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 1 := ⟨k - 1, by omega⟩
  exact (hzero j).le

end RHTower
