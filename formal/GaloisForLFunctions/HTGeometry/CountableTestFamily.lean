import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-!
# A countable family of test functions determining empirical limits

On a proper second-countable normed space the continuous functions form a separable space for the
topology of uniform convergence on compact sets.  Truncating a countable dense family and adding
the radial cut-off bumps produces a countable family of bounded continuous functions with the
property that convergence of the averages `N⁻¹ ∑_{j<N} ψ (y j)` to `∫ ψ dμ` along the family forces
the same convergence for **every** bounded continuous function.

The cut-off bumps supply the uniform tightness that upgrades approximation on a ball to
approximation everywhere.
-/

open MeasureTheory Filter Metric Set
open scoped Topology Uniformity

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E]

/-- A continuous function truncated to a symmetric band. -/
def clampFun (m : ℕ) (ψ : C(E, ℝ)) : E → ℝ := fun x => max (-(m : ℝ)) (min (m : ℝ) (ψ x))

theorem continuous_clampFun (m : ℕ) (ψ : C(E, ℝ)) : Continuous (clampFun m ψ) :=
  continuous_const.max (continuous_const.min ψ.continuous)

theorem abs_clampFun_le (m : ℕ) (ψ : C(E, ℝ)) (x : E) : |clampFun m ψ x| ≤ (m : ℝ) := by
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  simp only [clampFun, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- The radial cut-off which vanishes on the ball of radius `R` and equals one outside the ball of
radius `R + 1`. -/
def bumpFun (R : ℕ) : E → ℝ := fun x => min 1 (max 0 (‖x‖ - R))

theorem continuous_bumpFun (R : ℕ) : Continuous (bumpFun (E := E) R) :=
  continuous_const.min (continuous_const.max (continuous_norm.sub continuous_const))

theorem bumpFun_nonneg (R : ℕ) (x : E) : 0 ≤ bumpFun R x :=
  le_min zero_le_one (le_max_left _ _)

theorem bumpFun_le_one (R : ℕ) (x : E) : bumpFun R x ≤ 1 := min_le_left _ _

theorem abs_bumpFun_le (R : ℕ) (x : E) : |bumpFun R x| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_trans (by norm_num) (bumpFun_nonneg R x), bumpFun_le_one R x⟩

theorem bumpFun_eq_one_of_lt {R : ℕ} {x : E} (hx : (R : ℝ) + 1 < ‖x‖) : bumpFun R x = 1 := by
  have h1 : (1 : ℝ) ≤ ‖x‖ - R := by linarith
  rw [bumpFun, max_eq_right (by linarith), min_eq_left h1]

variable [ProperSpace E] [SecondCountableTopology E]

/-- A countable dense family of continuous functions for uniform convergence on compact sets. -/
def testDense (E : Type*) [NormedAddCommGroup E] [ProperSpace E] [SecondCountableTopology E] :
    Set C(E, ℝ) :=
  (TopologicalSpace.exists_countable_dense C(E, ℝ)).choose

theorem countable_testDense : (testDense E).Countable :=
  (TopologicalSpace.exists_countable_dense C(E, ℝ)).choose_spec.1

theorem dense_testDense : Dense (testDense E) :=
  (TopologicalSpace.exists_countable_dense C(E, ℝ)).choose_spec.2

/-- The countable family of test functions. -/
def testFamily (E : Type*) [NormedAddCommGroup E] [ProperSpace E] [SecondCountableTopology E] :
    Set (E → ℝ) :=
  (⋃ m : ℕ, ⋃ ψ ∈ testDense E, {clampFun m ψ}) ∪ (⋃ R : ℕ, {bumpFun R})

theorem countable_testFamily : (testFamily E).Countable := by
  refine Set.Countable.union ?_ (Set.countable_iUnion fun R => Set.countable_singleton _)
  refine Set.countable_iUnion fun m => ?_
  exact Set.Countable.biUnion countable_testDense fun ψ _ => Set.countable_singleton _

theorem clampFun_mem_testFamily {m : ℕ} {ψ : C(E, ℝ)} (hψ : ψ ∈ testDense E) :
    clampFun m ψ ∈ testFamily E := by
  refine Or.inl ?_
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  exact ⟨m, ψ, hψ, rfl⟩

theorem bumpFun_mem_testFamily (R : ℕ) : bumpFun (E := E) R ∈ testFamily E := by
  refine Or.inr ?_
  simp only [Set.mem_iUnion, Set.mem_singleton_iff]
  exact ⟨R, rfl⟩

/-! ### Approximation on a ball -/

theorem exists_mem_testDense_close (Φ : C(E, ℝ)) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ ∈ testDense E, ∀ x ∈ closedBall (0 : E) R, dist (Φ x) (ψ x) < ε := by
  classical
  set K : Set E := closedBall (0 : E) R with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  set V : Set (C(E, ℝ) × C(E, ℝ)) :=
    {fg | ∀ x ∈ K, dist (fg.1 x) (fg.2 x) < ε} with hV
  have hVu : V ∈ 𝓤 C(E, ℝ) := by
    rw [ContinuousMap.mem_compactConvergence_entourage_iff]
    exact ⟨K, {p : ℝ × ℝ | dist p.1 p.2 < ε}, hKc, Metric.dist_mem_uniformity hε,
      fun _fg hfg => hfg⟩
  have hball : UniformSpace.ball Φ V ∈ 𝓝 Φ := UniformSpace.ball_mem_nhds Φ hVu
  have hmem := (mem_closure_iff_nhds.1 (dense_testDense (E := E) Φ)) _ hball
  obtain ⟨ψ, hψ1, hψ2⟩ := hmem
  exact ⟨ψ, hψ2, fun x hx => hψ1 x hx⟩

theorem exists_mem_testFamily_approx (Φ : E → ℝ) (hΦc : Continuous Φ) {M : ℝ}
    (hΦb : ∀ x, |Φ x| ≤ M) (m : ℕ) (hm : M ≤ (m : ℝ)) (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ ∈ testFamily E, (∀ x, |ψ x| ≤ (m : ℝ)) ∧
      ∀ x, ‖x‖ ≤ R → |Φ x - ψ x| ≤ ε := by
  classical
  obtain ⟨ψ₀, hψ₀mem, hψ₀⟩ :=
    exists_mem_testDense_close (E := E) ⟨Φ, hΦc⟩ R hε
  refine ⟨clampFun m ψ₀, clampFun_mem_testFamily hψ₀mem, abs_clampFun_le m ψ₀, ?_⟩
  intro x hx
  have hxK : x ∈ closedBall (0 : E) R := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hx
  have hclose : dist (Φ x) (ψ₀ x) < ε := hψ₀ x hxK
  have habs : |Φ x - ψ₀ x| < ε := by
    rwa [Real.dist_eq] at hclose
  have hMx : |Φ x| ≤ (m : ℝ) := le_trans (hΦb x) hm
  have hMx' : -(m : ℝ) ≤ Φ x ∧ Φ x ≤ (m : ℝ) := abs_le.1 hMx
  rcases le_total (ψ₀ x) (-(m : ℝ)) with h | h
  · have hval : clampFun m ψ₀ x = -(m : ℝ) := by
      have hmin : min (m : ℝ) (ψ₀ x) = ψ₀ x :=
        min_eq_right (le_trans h (by linarith [hMx'.1, hMx'.2]))
      rw [clampFun, hmin, max_eq_left h]
    rw [hval]
    have : |Φ x - -(m : ℝ)| ≤ |Φ x - ψ₀ x| := by
      rw [abs_le]
      constructor
      · have := abs_nonneg (Φ x - ψ₀ x)
        linarith [hMx'.1]
      · have h1 : Φ x - ψ₀ x ≤ |Φ x - ψ₀ x| := le_abs_self _
        linarith
    linarith [this, habs]
  · rcases le_total (ψ₀ x) (m : ℝ) with h' | h'
    · have hval : clampFun m ψ₀ x = ψ₀ x := by
        rw [clampFun, min_eq_right h', max_eq_right h]
      rw [hval]
      linarith [habs]
    · have hval : clampFun m ψ₀ x = (m : ℝ) := by
        rw [clampFun, min_eq_left h', max_eq_right (by linarith [Nat.cast_nonneg (α := ℝ) m])]
      rw [hval]
      have : |Φ x - (m : ℝ)| ≤ |Φ x - ψ₀ x| := by
        rw [abs_le]
        constructor
        · have h1 : -(|Φ x - ψ₀ x|) ≤ Φ x - ψ₀ x := neg_abs_le _
          linarith
        · have := abs_nonneg (Φ x - ψ₀ x)
          linarith [hMx'.2]
      linarith [this, habs]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Metric Set
open scoped Topology Uniformity

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]

theorem integrable_of_continuous_bounded {μ : Measure E} [IsFiniteMeasure μ] {ψ : E → ℝ}
    (hc : Continuous ψ) {M : ℝ} (hb : ∀ x, |ψ x| ≤ M) : Integrable ψ μ :=
  Integrable.mono' (integrable_const M) hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb x)

theorem tendsto_integral_bumpFun (μ : Measure E) [IsProbabilityMeasure μ] :
    Tendsto (fun R : ℕ => ∫ x, bumpFun R x ∂μ) atTop (𝓝 0) := by
  have hzero : ∫ _x : E, (0 : ℝ) ∂μ = 0 := integral_zero E ℝ
  rw [← hzero]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    (fun R => (continuous_bumpFun R).aestronglyMeasurable) (integrable_const 1)
    (fun R => Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using abs_bumpFun_le R x)
    (Filter.Eventually.of_forall fun x => ?_)
  have heq : ∀ R : ℕ, ⌈‖x‖⌉₊ ≤ R → bumpFun R x = 0 := by
    intro R hR
    have hx : ‖x‖ ≤ (R : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hR)
    rw [bumpFun, max_eq_left (by linarith), min_eq_right zero_le_one]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop ⌈‖x‖⌉₊] with R hR
  exact (heq R hR).symm

omit [MeasurableSpace E] [BorelSpace E] in
theorem abs_average_sub_le {y : ℕ → E} {F G : E → ℝ} {R : ℕ} {c ε : ℝ}
    (hFG : ∀ x, |F x - G x| ≤ ε + c * bumpFun R x) {N : ℕ} (hN : 1 ≤ N) :
    |(N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, F (y j)
        - (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, G (y j)|
      ≤ ε + c * ((N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, bumpFun R (y j)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hsub : (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, F (y j)
      - (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, G (y j)
      = (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, (F (y j) - G (y j)) := by
    rw [← mul_sub, Finset.sum_sub_distrib]
  rw [hsub, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.2 hNpos))]
  have h1 : |∑ j ∈ Finset.range N, (F (y j) - G (y j))|
      ≤ ∑ j ∈ Finset.range N, |F (y j) - G (y j)| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ j ∈ Finset.range N, |F (y j) - G (y j)|
      ≤ ∑ j ∈ Finset.range N, (ε + c * bumpFun R (y j)) :=
    Finset.sum_le_sum fun j _ => hFG (y j)
  have h3 : ∑ j ∈ Finset.range N, (ε + c * bumpFun R (y j))
      = (N : ℝ) * ε + c * ∑ j ∈ Finset.range N, bumpFun R (y j) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      ← Finset.mul_sum]
  have h4 : (N : ℝ)⁻¹ * ((N : ℝ) * ε + c * ∑ j ∈ Finset.range N, bumpFun R (y j))
      = ε + c * ((N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, bumpFun R (y j)) := by
    field_simp
  calc (N : ℝ)⁻¹ * |∑ j ∈ Finset.range N, (F (y j) - G (y j))|
      ≤ (N : ℝ)⁻¹ * ((N : ℝ) * ε + c * ∑ j ∈ Finset.range N, bumpFun R (y j)) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (inv_pos.2 hNpos))
        rw [← h3]
        exact le_trans h1 h2
    _ = ε + c * ((N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, bumpFun R (y j)) := h4

theorem abs_integral_sub_le {μ : Measure E} [IsProbabilityMeasure μ] {F G : E → ℝ} {R : ℕ}
    {c ε : ℝ} (hF : Integrable F μ) (hG : Integrable G μ)
    (hFG : ∀ x, |F x - G x| ≤ ε + c * bumpFun R x) :
    |(∫ x, F x ∂μ) - ∫ x, G x ∂μ| ≤ ε + c * ∫ x, bumpFun R x ∂μ := by
  have hbump : Integrable (fun x => bumpFun R x) μ :=
    integrable_of_continuous_bounded (continuous_bumpFun R) (abs_bumpFun_le R)
  have hdiff : Integrable (fun x => F x - G x) μ := hF.sub hG
  have hbound : Integrable (fun x => ε + c * bumpFun R x) μ :=
    (integrable_const ε).add (hbump.const_mul c)
  have h1 : |(∫ x, F x ∂μ) - ∫ x, G x ∂μ| = |∫ x, (F x - G x) ∂μ| := by
    rw [integral_sub hF hG]
  rw [h1]
  refine le_trans (abs_integral_le_integral_abs) ?_
  have h2 : ∫ x, |F x - G x| ∂μ ≤ ∫ x, (ε + c * bumpFun R x) ∂μ :=
    integral_mono hdiff.abs hbound hFG
  have h3 : ∫ x, (ε + c * bumpFun R x) ∂μ = ε + c * ∫ x, bumpFun R x ∂μ := by
    rw [integral_add (integrable_const ε) (hbump.const_mul c), integral_const,
      integral_const_mul, probReal_univ, smul_eq_mul, one_mul]
  linarith [h2, h3.le, h3.ge]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Metric Set
open scoped Topology Uniformity

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E] [SecondCountableTopology E]
  [MeasurableSpace E] [BorelSpace E]

set_option linter.unusedSectionVars false in
/-- **Convergence along the countable test family forces convergence for every bounded continuous
function.** -/
theorem tendsto_average_of_testFamily {μ : Measure E} [IsProbabilityMeasure μ] {y : ℕ → E}
    (h : ∀ ψ ∈ testFamily E, Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ψ (y j))
      atTop (𝓝 (∫ x, ψ x ∂μ)))
    {Φ : E → ℝ} (hΦc : Continuous Φ) {M : ℝ} (hΦb : ∀ x, |Φ x| ≤ M) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, Φ (y j)) atTop
      (𝓝 (∫ x, Φ x ∂μ)) := by
  classical
  have hM0 : 0 ≤ M := le_trans (abs_nonneg (Φ 0)) (hΦb 0)
  set m : ℕ := ⌈M⌉₊ with hm
  have hMm : M ≤ (m : ℝ) := Nat.le_ceil M
  set c : ℝ := M + (m : ℝ) with hc
  have hc0 : 0 ≤ c := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simp only [hc]; linarith
  have hΦint : Integrable Φ μ := integrable_of_continuous_bounded hΦc hΦb
  rw [Metric.tendsto_atTop]
  intro ε₀ hε₀
  set ε : ℝ := ε₀ / (3 + 3 * c) with hεdef
  have hden : (0 : ℝ) < 3 + 3 * c := by linarith
  have hε : 0 < ε := div_pos hε₀ hden
  -- a cut-off radius with small tail mass
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ∫ x, bumpFun R x ∂μ < ε := by
    have hlim := tendsto_integral_bumpFun (E := E) μ
    rw [Metric.tendsto_atTop] at hlim
    obtain ⟨R₀, hR₀⟩ := hlim ε hε
    refine ⟨R₀, ?_⟩
    have := hR₀ R₀ (le_refl _)
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_le_of_lt (le_abs_self _) this
  have hbumpint : Integrable (fun x => bumpFun (E := E) R x) μ :=
    integrable_of_continuous_bounded (continuous_bumpFun R) (abs_bumpFun_le R)
  have hbumpnn : 0 ≤ ∫ x, bumpFun (E := E) R x ∂μ :=
    integral_nonneg fun x => bumpFun_nonneg R x
  -- an approximant from the test family
  obtain ⟨ψ, hψmem, hψb, hψa⟩ :=
    exists_mem_testFamily_approx (E := E) Φ hΦc hΦb m hMm ((R : ℝ) + 1) hε
  have hψc : Continuous ψ := by
    rcases hψmem with hcl | hbm
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hcl
      obtain ⟨m', ψ', _, rfl⟩ := hcl
      exact continuous_clampFun m' ψ'
    · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hbm
      obtain ⟨R', rfl⟩ := hbm
      exact continuous_bumpFun R'
  have hψint : Integrable ψ μ := integrable_of_continuous_bounded hψc hψb
  -- the pointwise comparison
  have hcomp : ∀ x, |Φ x - ψ x| ≤ ε + c * bumpFun R x := by
    intro x
    rcases le_or_gt ‖x‖ ((R : ℝ) + 1) with hx | hx
    · have := hψa x hx
      have hb : 0 ≤ c * bumpFun R x := mul_nonneg hc0 (bumpFun_nonneg R x)
      linarith
    · have hone : bumpFun (E := E) R x = 1 := bumpFun_eq_one_of_lt hx
      have h1 : |Φ x - ψ x| ≤ |Φ x| + |ψ x| := abs_sub _ _
      have h2 : |Φ x| + |ψ x| ≤ M + (m : ℝ) := add_le_add (hΦb x) (hψb x)
      rw [hone, mul_one]
      simp only [hc]
      linarith [h1, h2, hε.le]
  -- the two convergent averages
  have hlimψ := h ψ hψmem
  have hlimb := h (bumpFun R) (bumpFun_mem_testFamily R)
  rw [Metric.tendsto_atTop] at hlimψ hlimb
  obtain ⟨N₁, hN₁⟩ := hlimψ ε hε
  obtain ⟨N₂, hN₂⟩ := hlimb ε hε
  refine ⟨max (max N₁ N₂) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ 1) hN
  have hbψ := hN₁ N (le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 1)) hN)
  have hbb := hN₂ N (le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 1)) hN)
  rw [Real.dist_eq] at hbψ hbb ⊢
  have havg := abs_average_sub_le (E := E) (y := y) (F := Φ) (G := ψ) (R := R) hcomp hN1
  have hint := abs_integral_sub_le (μ := μ) (F := Φ) (G := ψ) (R := R) hΦint hψint hcomp
  set A : ℝ := (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, Φ (y j) with hA
  set B : ℝ := (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, ψ (y j) with hB
  set D : ℝ := (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, bumpFun (E := E) R (y j) with hD
  set I : ℝ := ∫ x, Φ x ∂μ with hI
  set J : ℝ := ∫ x, ψ x ∂μ with hJ
  set K : ℝ := ∫ x, bumpFun (E := E) R x ∂μ with hK
  have hDle : D ≤ K + ε := by
    have := le_abs_self (D - K)
    linarith [hbb]
  have h1 : |A - B| ≤ ε + c * D := havg
  have h2 : |I - J| ≤ ε + c * K := hint
  have h3 : |B - J| < ε := hbψ
  have hDnn : 0 ≤ D := by
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN1
    refine mul_nonneg (le_of_lt (inv_pos.2 hNpos)) ?_
    exact Finset.sum_nonneg fun j _ => bumpFun_nonneg R (y j)
  have hchain : |A - I| ≤ |A - B| + |B - J| + |J - I| := by
    have : A - I = (A - B) + (B - J) + (J - I) := by ring
    rw [this]
    have hab := abs_add_le (A - B + (B - J)) (J - I)
    have hbc := abs_add_le (A - B) (B - J)
    linarith
  have hJI : |J - I| = |I - J| := abs_sub_comm _ _
  have hcD : c * D ≤ c * (K + ε) := mul_le_mul_of_nonneg_left hDle hc0
  have hcK : c * K ≤ c * ε := mul_le_mul_of_nonneg_left hR.le hc0
  have hfinal : |A - I| < ε * (3 + 3 * c) := by
    have hcKe : c * (K + ε) ≤ c * ε + c * ε := by
      rw [mul_add]
      linarith [hcK]
    nlinarith [hchain, h1, h2, h3, hJI, hcD, hcKe]
  have : ε * (3 + 3 * c) = ε₀ := by
    rw [hεdef]
    field_simp
  linarith [hfinal, this.le, this.ge]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Metric Set
open scoped Topology Uniformity

variable {E : Type*} [NormedAddCommGroup E] [ProperSpace E] [SecondCountableTopology E]

theorem continuous_of_mem_testFamily {ψ : E → ℝ} (hψ : ψ ∈ testFamily E) : Continuous ψ := by
  rcases hψ with hcl | hbm
  · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hcl
    obtain ⟨m, ψ', _, rfl⟩ := hcl
    exact continuous_clampFun m ψ'
  · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hbm
    obtain ⟨R, rfl⟩ := hbm
    exact continuous_bumpFun R

theorem exists_bound_of_mem_testFamily {ψ : E → ℝ} (hψ : ψ ∈ testFamily E) :
    ∃ M : ℝ, ∀ x, |ψ x| ≤ M := by
  rcases hψ with hcl | hbm
  · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hcl
    obtain ⟨m, ψ', _, rfl⟩ := hcl
    exact ⟨(m : ℝ), abs_clampFun_le m ψ'⟩
  · simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hbm
    obtain ⟨R, rfl⟩ := hbm
    exact ⟨1, abs_bumpFun_le R⟩

end GaloisForLFunctions.HTGeometry
