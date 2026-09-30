import GaloisForLFunctions.RHTower.SteinhausEulerTiltPositiveTail
import GaloisForLFunctions.HTGeometry.FiniteModificationZeroOne
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Vanishing barrier survival under the exact Euler Poisson product law

For every cofinal sequence of prime cutoffs, the actual centered tilted sums
cannot stay below `A + 2 * log (1 + variance)` for any finite offset `A`.
Finite coordinate changes shift all sums by a bounded amount, so the union over
offsets satisfies the product zero-one law. The previously proved positive tail
at the standard-deviation scale excludes probability one. Continuity from above
then gives vanishing finite-horizon survival probabilities.

This closes the tilted survival input of the BAG critical-mass argument. Spatial
maximum estimates, change of measure for finite events, and deterministic
recurrence transfer are separate obligations; none is assumed here.
-/

open Filter MeasureTheory
open scoped Topology BigOperators

noncomputable section
namespace RHTower
open SteinhausModel

/-- Variance of the actual centered tilted prime sum. -/
def steinhausEulerTiltVariance (N : ℕ) : ℝ :=
  ∫ ω, steinhausEulerTiltPrimeSum (Finset.range N) ω ^ 2 ∂steinhausEulerTiltProductMeasure

/-- The literal logarithmic-variance barrier at the selected cutoffs. -/
def steinhausEulerTiltBarrier (u : ℕ → ℕ) (A : ℝ) : Set Omega :=
  {ω | ∀ j, steinhausEulerTiltPrimeSum (Finset.range (u j)) ω ≤
    A + 2 * Real.log (1 + steinhausEulerTiltVariance (u j))}

/-- Existence of any finite upper offset for this barrier. -/
def steinhausEulerTiltBoundedBarrier (u : ℕ → ℕ) : Set Omega :=
  ⋃ A : ℕ, steinhausEulerTiltBarrier u A

/-- Survival through the first `J` selected cutoffs. -/
def steinhausEulerTiltFiniteBarrier (u : ℕ → ℕ) (A : ℝ) (J : ℕ) : Set Omega :=
  {ω | ∀ j < J, steinhausEulerTiltPrimeSum (Finset.range (u j)) ω ≤
    A + 2 * Real.log (1 + steinhausEulerTiltVariance (u j))}

theorem measurableSet_steinhausEulerTiltBarrier (u : ℕ → ℕ) (A : ℝ) :
    MeasurableSet (steinhausEulerTiltBarrier u A) := by
  simp only [steinhausEulerTiltBarrier, Set.setOf_forall]
  exact MeasurableSet.iInter fun j => measurableSet_le
    (measurable_steinhausEulerTiltPrimeSum _) measurable_const

theorem measurableSet_steinhausEulerTiltBoundedBarrier (u : ℕ → ℕ) :
    MeasurableSet (steinhausEulerTiltBoundedBarrier u) :=
  MeasurableSet.iUnion fun A => measurableSet_steinhausEulerTiltBarrier u A

theorem measurableSet_steinhausEulerTiltFiniteBarrier (u : ℕ → ℕ) (A : ℝ) (J : ℕ) :
    MeasurableSet (steinhausEulerTiltFiniteBarrier u A J) := by
  simp only [steinhausEulerTiltFiniteBarrier, Set.setOf_forall]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le (measurable_steinhausEulerTiltPrimeSum _) measurable_const

/-- A finite phase change shifts every cutoff sum by a uniformly bounded amount. -/
theorem norm_steinhausEulerTiltPrimeSum_sub_le (P D : Finset ℕ) (x y : Omega)
    (hxy : ∀ n, n ∉ D → x n = y n) :
    ‖steinhausEulerTiltPrimeSum P x - steinhausEulerTiltPrimeSum P y‖ ≤ 9 * D.card := by
  classical
  let f := fun n => steinhausEulerTiltPrimeVariable n x - steinhausEulerTiltPrimeVariable n y
  have hf : ∀ n, ‖f n‖ ≤ 9 := by
    intro n
    have hx := norm_steinhausEulerTiltPrimeTerm_le n (x n)
    have hy := norm_steinhausEulerTiltPrimeTerm_le n (y n)
    have hr := steinhausCriticalPrimeRadius_le n
    have hn := norm_sub_le (steinhausEulerTiltPrimeTerm n (x n))
      (steinhausEulerTiltPrimeTerm n (y n))
    change ‖steinhausEulerTiltPrimeTerm n (x n) - steinhausEulerTiltPrimeTerm n (y n)‖ ≤ 9
    linarith
  have hs : ∑ n ∈ P ∩ D, f n = ∑ n ∈ P, f n := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro n hn hnD
    have h : n ∉ D := fun hd => hnD (Finset.mem_inter.mpr ⟨hn, hd⟩)
    simp [f, steinhausEulerTiltPrimeVariable, hxy n h]
  unfold steinhausEulerTiltPrimeSum
  rw [← Finset.sum_sub_distrib, ← hs]
  calc
    ‖∑ n ∈ P ∩ D, f n‖ ≤ ∑ n ∈ P ∩ D, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ P ∩ D, (9 : ℝ) := Finset.sum_le_sum fun n _ => hf n
    _ ≤ ∑ n ∈ D, (9 : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg
      Finset.inter_subset_right (by intros; positivity)
    _ = 9 * D.card := by simp [mul_comm]

/-- The union over barrier offsets is invariant under finite coordinate changes. -/
theorem steinhausEulerTiltBoundedBarrier_invariant (u : ℕ → ℕ) (x y : Omega)
    (hxy : {n | x n ≠ y n}.Finite) :
    x ∈ steinhausEulerTiltBoundedBarrier u ↔ y ∈ steinhausEulerTiltBoundedBarrier u := by
  classical
  let D := hxy.toFinset
  have hagree : ∀ n, n ∉ D → x n = y n := by
    intro n hn
    by_contra h
    exact hn (hxy.mem_toFinset.mpr h)
  have hb : ∀ P, ‖steinhausEulerTiltPrimeSum P x - steinhausEulerTiltPrimeSum P y‖ ≤
      9 * D.card := fun P => norm_steinhausEulerTiltPrimeSum_sub_le P D x y hagree
  simp only [steinhausEulerTiltBoundedBarrier, Set.mem_iUnion]
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A + 9 * D.card, ?_⟩
    intro j
    have h := hb (Finset.range (u j))
    have h' := neg_le_abs (steinhausEulerTiltPrimeSum (Finset.range (u j)) x -
      steinhausEulerTiltPrimeSum (Finset.range (u j)) y)
    have ha := hA j
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.norm_eq_abs] at h
    linarith
  · rintro ⟨A, hA⟩
    refine ⟨A + 9 * D.card, ?_⟩
    intro j
    have h := hb (Finset.range (u j))
    have h' := le_abs_self (steinhausEulerTiltPrimeSum (Finset.range (u j)) x -
      steinhausEulerTiltPrimeSum (Finset.range (u j)) y)
    have ha := hA j
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.norm_eq_abs] at h
    linarith

private theorem eventually_log_barrier_lt_sqrt (A c : ℝ) (hc : 0 < c) :
    ∀ᶠ v : ℝ in atTop, A + 2 * Real.log (1 + v) < c * Real.sqrt v := by
  have hlo := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by positivity : 0 < c / 4)
  have hs : Tendsto (fun v : ℝ => Real.sqrt v) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2))
  have hlarge := hs.eventually (eventually_gt_atTop ((A + 2 * Real.log 2) / (c / 2)))
  filter_upwards [hlo, hlarge, eventually_ge_atTop (1 : ℝ)] with v hv hbig hv1
  have hv0 : 0 < v := lt_of_lt_of_le (by norm_num) hv1
  have hlog : Real.log (1 + v) ≤ Real.log 2 + Real.log v := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hv0)]
    exact Real.log_le_log (by positivity) (by linarith)
  have hvlog : 0 ≤ Real.log v := Real.log_nonneg hv1
  rw [Real.norm_eq_abs, abs_of_nonneg hvlog, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hv0.le _), ← Real.sqrt_eq_rpow] at hv
  have hbig' : A + 2 * Real.log 2 < c / 2 * Real.sqrt v := by
    have := (div_lt_iff₀ (by positivity : 0 < c / 2)).mp hbig
    nlinarith
  nlinarith

/-- Every fixed barrier level misses a uniform positive amount of tilted mass. -/
theorem exists_measure_steinhausEulerTiltBarrier_le (u : ℕ → ℕ)
    (hu : Tendsto u atTop atTop) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : ℝ,
      (steinhausEulerTiltProductMeasure (steinhausEulerTiltBarrier u A)).toReal ≤ 1 - δ := by
  obtain ⟨c, δ, hc, hδ, htail⟩ := exists_steinhausEulerTiltPrimeSum_positive_tail
  refine ⟨δ, hδ, fun A => ?_⟩
  have hv : Tendsto (fun j => steinhausEulerTiltVariance (u j)) atTop atTop :=
    tendsto_integral_sq_steinhausEulerTiltPrimeSum_atTop.comp hu
  obtain ⟨j, hj3, hj⟩ := ((hu.eventually (eventually_ge_atTop 3)).and
    (hv.eventually (eventually_log_barrier_lt_sqrt A c hc))).exists
  let T : Set Omega := {ω | c * Real.sqrt (steinhausEulerTiltVariance (u j)) <
    steinhausEulerTiltPrimeSum (Finset.range (u j)) ω}
  have hT : MeasurableSet T := measurableSet_lt measurable_const
    (measurable_steinhausEulerTiltPrimeSum _)
  have hsub : steinhausEulerTiltBarrier u A ⊆ Tᶜ := by
    intro ω hω hωT
    have h := hω j
    exact (not_lt_of_ge h) (hj.trans hωT)
  have hm := measureReal_mono (μ := steinhausEulerTiltProductMeasure) hsub
  rw [measureReal_compl hT, probReal_univ] at hm
  have ht := htail (u j) hj3
  change δ ≤ steinhausEulerTiltProductMeasure.real T at ht
  change steinhausEulerTiltProductMeasure.real (steinhausEulerTiltBarrier u A) ≤ 1 - δ
  linarith

/-- Under the actual tilted product law, no finite offset preserves the selected-cutoff
logarithmic barrier. The only cutoff assumption is cofinality. -/
theorem measure_steinhausEulerTiltBoundedBarrier_eq_zero (u : ℕ → ℕ)
    (hu : Tendsto u atTop atTop) :
    steinhausEulerTiltProductMeasure (steinhausEulerTiltBoundedBarrier u) = 0 := by
  obtain ⟨δ, hδ, hgap⟩ := exists_measure_steinhausEulerTiltBarrier_le u hu
  have hnonneg : 0 ≤ 1 - δ :=
    (ENNReal.toReal_nonneg).trans (hgap 0)
  have hmono : Monotone (fun A : ℕ => steinhausEulerTiltBarrier u A) := by
    intro A B hAB ω hω j
    exact (hω j).trans (by gcongr)
  have hbound : steinhausEulerTiltProductMeasure (steinhausEulerTiltBoundedBarrier u) ≤
      ENNReal.ofReal (1 - δ) := by
    rw [steinhausEulerTiltBoundedBarrier, hmono.measure_iUnion]
    refine iSup_le fun A => ?_
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal hnonneg]
    exact hgap A
  have hzeroone := GaloisForLFunctions.HTGeometry.measure_infinitePi_eq_zero_or_one_of_invariant
    steinhausEulerTiltPrimeMeasure (fun _ => 0)
    (measurableSet_steinhausEulerTiltBoundedBarrier u)
    (steinhausEulerTiltBoundedBarrier_invariant u)
  change steinhausEulerTiltProductMeasure (steinhausEulerTiltBoundedBarrier u) = 0 ∨
    steinhausEulerTiltProductMeasure (steinhausEulerTiltBoundedBarrier u) = 1 at hzeroone
  rcases hzeroone with hzero | hone
  · exact hzero
  · rw [hone] at hbound
    exact False.elim ((not_lt_of_ge hbound) (ENNReal.ofReal_lt_one.mpr (by linarith)))

/-- Every real-valued offset gives a null infinite barrier event. -/
theorem measure_steinhausEulerTiltBarrier_eq_zero (u : ℕ → ℕ)
    (hu : Tendsto u atTop atTop) (A : ℝ) :
    steinhausEulerTiltProductMeasure (steinhausEulerTiltBarrier u A) = 0 := by
  obtain ⟨B, hB⟩ := exists_nat_ge A
  have hsub : steinhausEulerTiltBarrier u A ⊆ steinhausEulerTiltBoundedBarrier u := by
    intro ω hω
    apply Set.mem_iUnion.mpr
    refine ⟨B, fun j => (hω j).trans ?_⟩
    linarith
  exact le_antisymm ((measure_mono hsub).trans_eq
    (measure_steinhausEulerTiltBoundedBarrier_eq_zero u hu)) bot_le

/-- The literal finite-horizon barrier survival probabilities vanish. -/
theorem tendsto_measure_steinhausEulerTiltFiniteBarrier (u : ℕ → ℕ)
    (hu : Tendsto u atTop atTop) (A : ℝ) :
    Tendsto (fun J => steinhausEulerTiltProductMeasure (steinhausEulerTiltFiniteBarrier u A J))
      atTop (𝓝 0) := by
  have hanti : Antitone (steinhausEulerTiltFiniteBarrier u A) := by
    intro I J hIJ ω hω j hj
    exact hω j (lt_of_lt_of_le hj hIJ)
  have hi : (⋂ J, steinhausEulerTiltFiniteBarrier u A J) = steinhausEulerTiltBarrier u A := by
    ext ω
    simp only [Set.mem_iInter]
    constructor
    · intro h j
      exact h (j + 1) j (Nat.lt_succ_self j)
    · intro h J j _
      exact h j
  have ht := tendsto_measure_iInter_atTop (μ := steinhausEulerTiltProductMeasure)
    (fun J => (measurableSet_steinhausEulerTiltFiniteBarrier u A J).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  simpa only [Function.comp_def, hi, measure_steinhausEulerTiltBarrier_eq_zero u hu A] using ht

end RHTower
