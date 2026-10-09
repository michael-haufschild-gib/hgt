import GaloisForLFunctions.HTGeometry.QKrawtchoukMaximalAtomUniqueness
import GaloisForLFunctions.HTGeometry.OrthoNoCommonRoot

/-!
# Finite quadratures selected by a moving atom

The measure-selection step of arXiv:2609.24149, Theorem 6.1, applies to an
explicit finite approximation of every inverse-q Hermite extremal measure.
At stage `n` choose one of degrees `n+1,n+2` where the orthogonal polynomial
does not vanish at the prescribed point. A terminal recurrence parameter
then puts that point among the quadrature nodes. The finite measure matches
increasingly many moments and carries at least the limiting Christoffel mass
there. Tightness, Portmanteau, and maximal-atom uniqueness identify its limit.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace HTGeometry

/-- A nearby admissible degree; consecutive orthogonal polynomials cannot
both vanish at the prescribed node. -/
def inverseQHermitePinnedLevel (t u x : ℝ) (n : ℕ) : ℕ :=
  if (monicOrtho (inverseQHermiteMoment t u) (n + 1)).eval x = 0
    then n + 2 else n + 1

private theorem pinnedLevel_bounds (t u x : ℝ) (n : ℕ) :
    n + 1 ≤ inverseQHermitePinnedLevel t u x n ∧
      inverseQHermitePinnedLevel t u x n ≤ n + 2 := by
  unfold inverseQHermitePinnedLevel
  split <;> omega

private theorem pinnedLevel_ne_zero (t u x : ℝ) (n : ℕ) :
    (monicOrtho (inverseQHermiteMoment t u)
      (inverseQHermitePinnedLevel t u x n)).eval x ≠ 0 := by
  unfold inverseQHermitePinnedLevel
  split
  · rename_i hx
    exact monicOrtho_succ_no_common_root (inverseQHermiteMoment_positive t u) (n + 1) hx
  · assumption

/-- The terminal parameter forcing the prescribed point to be a node. -/
def inverseQHermitePinnedParameter (t u x : ℝ) (n : ℕ) : ℝ :=
  -(monicOrtho (inverseQHermiteMoment t u)
      (inverseQHermitePinnedLevel t u x n + 1)).eval x /
    (monicOrtho (inverseQHermiteMoment t u)
      (inverseQHermitePinnedLevel t u x n)).eval x

private theorem pinned_mem_nodes (t u x : ℝ) (n : ℕ) :
    x ∈ quasiNodes (inverseQHermiteMoment t u) (inverseQHermitePinnedLevel t u x n)
      (inverseQHermitePinnedParameter t u x n) := by
  rw [mem_quasiNodes_iff, quasiOrtho_eval, inverseQHermitePinnedParameter]
  rw [div_mul_cancel₀ _ (pinnedLevel_ne_zero t u x n), add_neg_cancel]

/-- A finite probability quadrature with the prescribed node. -/
def inverseQHermitePinnedQuadrature (t u x : ℝ) (n : ℕ) : ProbabilityMeasure ℝ :=
  quasiProbMeasure (inverseQHermiteMoment_positive t u)
    (inverseQHermitePinnedLevel t u x n) (inverseQHermitePinnedParameter t u x n)

/-- Every stage carries at least the extremal mass at the pinned node. -/
theorem inverseQHermitePinnedQuadrature_atom (t u x : ℝ) (n : ℕ) :
    ENNReal.ofReal (christoffelLimit (inverseQHermiteMoment t u) x) ≤
      (inverseQHermitePinnedQuadrature t u x n : Measure ℝ) {x} :=
  quasiProb_ge_ofReal_christoffelLimit (inverseQHermiteMoment_positive t u)
    (inverseQHermiteMoment_zero t u) _ _ (measurableSet_singleton x)
    (pinned_mem_nodes t u x n) (Set.mem_singleton x)

/-- Each fixed moment is eventually reproduced exactly, even when the
prescribed atom moves arbitrarily between stages. -/
theorem inverseQHermitePinnedQuadrature_moments (t u : ℝ) (x : ℕ → ℝ) (k : ℕ) :
    ∀ᶠ n in atTop,
      Integrable (fun y : ℝ => y ^ k)
        (inverseQHermitePinnedQuadrature t u (x n) n : Measure ℝ) ∧
      (∫ y, y ^ k ∂(inverseQHermitePinnedQuadrature t u (x n) n : Measure ℝ)) =
        inverseQHermiteMoment t u k := by
  filter_upwards [eventually_ge_atTop k] with n hn
  refine ⟨integrable_quasiProb (inverseQHermiteMoment_positive t u) _ _ _, ?_⟩
  change (∫ y, y ^ k ∂(quasiProb (inverseQHermiteMoment t u) _ _)) = _
  rw [integral_pow_quasiProb (inverseQHermiteMoment_positive t u) _ _ k (by
    have := (pinnedLevel_bounds t u (x n) n).1
    omega), inverseQHermiteMoment_zero, inv_one, one_mul]

private theorem pinnedQuadrature_tendsto (t u : ℝ) (xs : ℕ → ℝ) (x : ℝ)
    (hx : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun n => inverseQHermitePinnedQuadrature t u (xs n) n) atTop
      (𝓝 (inverseQHermiteAtomMeasure t u x)) := by
  let h := inverseQHermiteMoment_positive t u
  let hb := inverseQHermiteMoment_boundedKernel t u 0
  let h0 := inverseQHermiteMoment_zero t u
  let lvl := fun n => inverseQHermitePinnedLevel t u (xs n) n
  let par := fun n => inverseQHermitePinnedParameter t u (xs n) n
  have hlvl : ∀ n, n + 1 ≤ lvl n := fun n => (pinnedLevel_bounds t u (xs n) n).1
  have hnode : ∃ η > (0 : ℝ), ∀ δ : ℝ, 0 < δ → δ < η →
      ∀ᶠ n in atTop, ∀ i : ℕ, n = lvl i →
        ∃ y ∈ quasiNodes (inverseQHermiteMoment t u) n (par i), |y - x| ≤ δ := by
    refine ⟨1, zero_lt_one, fun δ hδ _ => ?_⟩
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx δ hδ
    filter_upwards [eventually_ge_atTop (N + 2)] with n hn
    intro i hi
    have hiN : N ≤ i := by
      have := (pinnedLevel_bounds t u (xs i) i).2
      change lvl i ≤ i + 2 at this
      omega
    refine ⟨xs i, ?_, ?_⟩
    · rw [hi]
      exact pinned_mem_nodes t u (xs i) i
    · simpa only [Real.dist_eq] using (hN i hiN).le
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ρ, -, hρ⟩ := strictMono_subseq_of_tendsto_atTop hns
  have hgrow (n : ℕ) : n + 1 ≤ lvl (ns (ρ n)) := by
    have hfirst : n ≤ ns (ρ n) := hρ.le_apply
    have hsecond := hlvl (ns (ρ n))
    omega
  obtain ⟨μ, φ, hφ, hlim⟩ := exists_subseq_tendsto_quasiProbMeasure_of_level h
    (fun n => lvl (ns (ρ n))) hgrow (fun n => par (ns (ρ n)))
  have hψ : StrictMono (fun n => ns (ρ (φ n))) := hρ.comp hφ
  have hm : GaloisForLFunctions.HTGeometry.HasHamburgerMoments
      (inverseQHermiteMoment t u) (μ : Measure ℝ) := by
    intro k
    have hm := hasMoments_of_tendsto_quasi_of_level h lvl hlvl par hψ
      (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG) hlim k
    simpa only [h0, inv_one, one_mul] using hm
  have ha := ofReal_christoffelLimit_le_leaf_singleton_of_eventually_node
    h hb h0 hlvl hψ hlim hnode
  have hreal : christoffelLimit (inverseQHermiteMoment t u) x ≤
      (μ : Measure ℝ).real {x} := by
    have hr := ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _) |>.mpr ha
    simpa only [ENNReal.toReal_ofReal (christoffelLimit_nonneg h x), Measure.real] using hr
  have hmax : (μ : Measure ℝ).real {x} = christoffelLimit (inverseQHermiteMoment t u) x :=
    le_antisymm (measureReal_singleton_le_christoffelLimit_of_hasMoments h hm x) hreal
  have heq : μ = inverseQHermiteAtomMeasure t u x :=
    (inverseQHermite_maximal_atom_unique t u x).unique ⟨hm, hmax⟩
      ⟨inverseQHermiteAtomMeasure_moments t u x, inverseQHermiteAtomMeasure_atom_real t u x⟩
  refine ⟨fun n => ρ (φ n), ?_⟩
  rw [← heq]
  exact hlim

private theorem pinned_drift_tendsto (x r : ℝ) :
    Tendsto (fun n : ℕ => x + r / ((n : ℝ) + 1)) atTop (𝓝 x) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n : ℕ => show (n : ℝ) ≤ (n : ℝ) + 1 by linarith)
      tendsto_natCast_atTop_atTop
  have hz : Tendsto (fun n : ℕ => r / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  simpa only [add_zero] using tendsto_const_nhds.add hz

/-- A drifting pinned atom selects the extremal measure at its limiting
position. All finite measures and limiting moment data are constructed. -/
theorem inverseQHermitePinnedQuadrature_tendsto (t u x r : ℝ) :
    Tendsto (fun n : ℕ => inverseQHermitePinnedQuadrature t u
      (x + r / ((n : ℝ) + 1)) n) atTop (𝓝 (inverseQHermiteAtomMeasure t u x)) :=
  pinnedQuadrature_tendsto t u _ x (pinned_drift_tendsto x r)

/-- Selecting by atom position is weakly continuous, including points where
the finite Nevanlinna parameter passes through infinity. -/
theorem continuous_inverseQHermiteAtomMeasure (t u : ℝ) :
    Continuous (inverseQHermiteAtomMeasure t u) := by
  let F := inverseQHermiteNevanlinnaFamily t u
  have hc := F.matrix.toCarrierMatrix.continuous_projectiveLabel
    F.continuous_B F.continuous_D.neg
  have heq : F.matrix.toCarrierMatrix.projectiveLabel = F.matrix.projectiveLabel :=
    funext F.matrix.toCarrierMatrix_projectiveLabel
  rw [heq] at hc
  exact F.continuous_leaf.comp hc

private theorem moving_atom_limsup_le {μs : ℕ → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (hμ : Tendsto μs atTop (𝓝 μ))
    {xs : ℕ → ℝ} {x : ℝ} (hx : Tendsto xs atTop (𝓝 x)) :
    limsup (fun n => (μs n : Measure ℝ) {xs n}) atTop ≤ (μ : Measure ℝ) {x} := by
  apply le_measure_singleton_of_forall_Icc (μ : Measure ℝ) x zero_lt_one
  intro δ hδ _
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx δ hδ
  have hle : ∀ᶠ n in atTop, (μs n : Measure ℝ) {xs n} ≤
      (μs n : Measure ℝ) (Set.Icc (x - δ) (x + δ)) := by
    filter_upwards [eventually_ge_atTop N] with n hn
    apply measure_mono
    intro y hy
    have hy' : y = xs n := hy
    subst y
    have habs : |xs n - x| < δ := by simpa only [Real.dist_eq] using hN n hn
    have hb := abs_lt.mp habs
    exact ⟨by linarith [hb.1], by linarith [hb.2]⟩
  exact (limsup_le_limsup hle).trans
    (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ isClosed_Icc)

/-- The distinguished finite masses converge to the maximal permitted mass;
this verifies the saturation input of the paper's selection mechanism. -/
theorem inverseQHermitePinnedQuadrature_atom_tendsto (t u x r : ℝ) :
    Tendsto (fun n : ℕ => (inverseQHermitePinnedQuadrature t u
      (x + r / ((n : ℝ) + 1)) n : Measure ℝ) {x + r / ((n : ℝ) + 1)}) atTop
      (𝓝 (ENNReal.ofReal (christoffelLimit (inverseQHermiteMoment t u) x))) := by
  have hx := pinned_drift_tendsto x r
  have hweight := ENNReal.tendsto_ofReal
    (((continuous_christoffelLimit (inverseQHermiteMoment_positive t u)
      (inverseQHermiteMoment_boundedKernel t u 0)).tendsto x).comp hx)
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · rw [← hweight.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun n =>
      inverseQHermitePinnedQuadrature_atom t u _ n)
  · rw [← inverseQHermiteAtomMeasure_atom t u x]
    exact moving_atom_limsup_le (inverseQHermitePinnedQuadrature_tendsto t u x r) hx

end HTGeometry
