import GaloisForLFunctions.HTGeometry.PhaseGraphDetector

/-!
# Phase-graph blindness of every subcritical Sobolev hierarchy

A measurable phase map turns a probability space into a graph inside the completed phase space.
The graph law is singular in every phase direction, so the phase detector concentrated at the
sampled phase point has graph expectation one while its completed mean, mean square, and every
completed mean square of an iterated coordinate derivative of order at most the resolution decay
like the reciprocal resolution power of the phase dimension.

Consequently no estimate whose right-hand side vanishes with the completed mean, variance, and
phase Dirichlet energy can compare the graph law with completed phase Haar, and restriction to the
graph is unbounded on the completed phase Sobolev space of every integer order below half the phase
dimension.
-/

open MeasureTheory Complex UnitAddTorus Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]

section MultiIndex

/-- The coordinate list of a multi-index. -/
def multiIndexList (α : d → ℕ) : List d :=
  (Finset.univ : Finset d).toList.flatMap fun i => List.replicate (α i) i

theorem length_multiIndexList (α : d → ℕ) : (multiIndexList α).length = ∑ i, α i := by
  rw [multiIndexList, List.length_flatMap]
  simp

/-- The multi-indices of total order at most `k`. -/
def multiIndexSet (d : Type*) [Fintype d] [DecidableEq d] (k : ℕ) : Finset (d → ℕ) :=
  (Fintype.piFinset fun _ : d => Finset.range (k + 1)).filter fun α => ∑ i, α i ≤ k

theorem sum_le_of_mem_multiIndexSet {k : ℕ} {α : d → ℕ} (hα : α ∈ multiIndexSet d k) :
    ∑ i, α i ≤ k := (Finset.mem_filter.mp hα).2

end MultiIndex

section GraphExperiment

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The graph expectation of a phase observable along a phase map. -/
def graphExpectation (μ : Measure Ω) (Φ : Ω → (d → ℝ)) (F : Ω → (d → ℝ) → ℂ) : ℂ :=
  ∫ ω, F ω (Φ ω) ∂μ

/-- The completed expectation of a phase observable against conditional phase Haar. -/
def completedExpectation (μ : Measure Ω) (F : Ω → (d → ℝ) → ℂ) : ℂ :=
  ∫ ω, (∫ x in torusBox d, F ω x) ∂μ

/-- The completed mean square of a phase observable. -/
def completedSq (μ : Measure Ω) (F : Ω → (d → ℝ) → ℂ) : ℝ :=
  ∫ ω, (∫ x in torusBox d, ‖F ω x‖ ^ 2) ∂μ

/-- The completed variance of a phase observable. -/
def completedVar (μ : Measure Ω) (F : Ω → (d → ℝ) → ℂ) : ℝ :=
  completedSq μ F - ‖completedExpectation μ F‖ ^ 2

/-- The completed phase Dirichlet energy of a phase observable. -/
def completedDirichlet (μ : Measure Ω) (F : Ω → (d → ℝ) → ℂ) : ℝ :=
  ∑ i : d, ∫ ω, (∫ x in torusBox d, ‖pderiv i (F ω) x‖ ^ 2) ∂μ

/-- The completed phase Sobolev quantity of integer order `k`. -/
def phaseSobolevSq (μ : Measure Ω) (F : Ω → (d → ℝ) → ℂ) (k : ℕ) : ℝ :=
  ∑ α ∈ multiIndexSet d k,
    ∫ ω, (∫ x in torusBox d, ‖pderivList (multiIndexList α) (F ω) x‖ ^ 2) ∂μ

/-- The detector family adapted to a phase map. -/
def graphDetector (N : ℕ) (Φ : Ω → (d → ℝ)) : Ω → (d → ℝ) → ℂ :=
  fun ω => phaseDetector N (Φ ω)

theorem graphDetector_nonneg (N : ℕ) (Φ : Ω → (d → ℝ)) (ω : Ω) (x : d → ℝ) :
    0 ≤ (graphDetector N Φ ω x).re := phaseDetector_nonneg N (Φ ω) x

theorem graphDetector_le_one (N : ℕ) (Φ : Ω → (d → ℝ)) (ω : Ω) (x : d → ℝ) :
    (graphDetector N Φ ω x).re ≤ 1 := phaseDetector_le_one N (Φ ω) x

theorem graphDetector_im (N : ℕ) (Φ : Ω → (d → ℝ)) (ω : Ω) (x : d → ℝ) :
    (graphDetector N Φ ω x).im = 0 := phaseDetector_im N (Φ ω) x

variable (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- **Graph expectation one.**  The detector adapted to the phase map is one on every sample. -/
theorem graphExpectation_graphDetector (N : ℕ) (Φ : Ω → (d → ℝ)) :
    graphExpectation μ Φ (graphDetector N Φ) = 1 := by
  rw [graphExpectation]
  have hpt : ∀ ω : Ω, graphDetector N Φ ω (Φ ω) = 1 := fun ω => phaseDetector_self N (Φ ω)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  simp

/-- **Completed expectation.**  The completed mean of the detector is the reciprocal resolution
power of the phase dimension. -/
theorem completedExpectation_graphDetector (N : ℕ) (Φ : Ω → (d → ℝ)) :
    completedExpectation μ (graphDetector N Φ) =
      (((((N : ℝ) + 1) ^ Fintype.card d)⁻¹ : ℝ) : ℂ) := by
  rw [completedExpectation]
  have hpt : ∀ ω : Ω, (∫ x in torusBox d, graphDetector N Φ ω x) =
      (((((N : ℝ) + 1) ^ Fintype.card d)⁻¹ : ℝ) : ℂ) := fun ω =>
    integral_box_phaseDetector N (Φ ω)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  simp

/-- The completed mean square of a derivative of the detector does not depend on the sample. -/
theorem integral_graphDetector_pderivList (N : ℕ) (Φ : Ω → (d → ℝ)) (l : List d) :
    (∫ ω, (∫ x in torusBox d, ‖pderivList l (graphDetector N Φ ω) x‖ ^ 2) ∂μ) =
      ∫ x in torusBox d, ‖pderivList l (phaseDetector N (0 : d → ℝ)) x‖ ^ 2 := by
  have hpt : ∀ ω : Ω, (∫ x in torusBox d, ‖pderivList l (graphDetector N Φ ω) x‖ ^ 2) =
      ∫ x in torusBox d, ‖pderivList l (phaseDetector N (0 : d → ℝ)) x‖ ^ 2 := fun ω =>
    integral_box_normSq_pderivList_phaseDetector_eq N (Φ ω) l
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  simp

theorem integral_graphDetector_pderivList_le (N : ℕ) (Φ : Ω → (d → ℝ)) (l : List d) :
    (∫ ω, (∫ x in torusBox d, ‖pderivList l (graphDetector N Φ ω) x‖ ^ 2) ∂μ) ≤
      ((2 * Real.pi * (N : ℝ)) ^ l.length) ^ 2 / ((N : ℝ) + 1) ^ Fintype.card d := by
  rw [integral_graphDetector_pderivList μ N Φ l]
  exact integral_box_normSq_pderivList_phaseDetector_le N (0 : d → ℝ) l

/-- **Completed mean square.**  The detector has completed mean square at most the reciprocal
resolution power of the phase dimension. -/
theorem completedSq_graphDetector_le (N : ℕ) (Φ : Ω → (d → ℝ)) :
    completedSq μ (graphDetector N Φ) ≤ (((N : ℝ) + 1) ^ Fintype.card d)⁻¹ := by
  have h := integral_graphDetector_pderivList_le μ N Φ ([] : List d)
  rw [List.length_nil, pow_zero, one_pow] at h
  rw [completedSq, inv_eq_one_div]
  exact h

theorem completedVar_graphDetector_le (N : ℕ) (Φ : Ω → (d → ℝ)) :
    completedVar μ (graphDetector N Φ) ≤ (((N : ℝ) + 1) ^ Fintype.card d)⁻¹ := by
  rw [completedVar]
  have h := completedSq_graphDetector_le μ N Φ
  nlinarith [sq_nonneg ‖completedExpectation μ (graphDetector N Φ)‖]

/-- **Completed Dirichlet energy.**  The detector has completed phase Dirichlet energy at most the
squared resolution frequency over the resolution power of the phase dimension. -/
theorem completedDirichlet_graphDetector_le (N : ℕ) (Φ : Ω → (d → ℝ)) :
    completedDirichlet μ (graphDetector N Φ) ≤
      (Fintype.card d : ℝ) * ((2 * Real.pi * (N : ℝ)) ^ 2 /
        ((N : ℝ) + 1) ^ Fintype.card d) := by
  rw [completedDirichlet]
  have hterm : ∀ i : d, (∫ ω, (∫ x in torusBox d, ‖pderiv i (graphDetector N Φ ω) x‖ ^ 2) ∂μ) ≤
      (2 * Real.pi * (N : ℝ)) ^ 2 / ((N : ℝ) + 1) ^ Fintype.card d := by
    intro i
    have h := integral_graphDetector_pderivList_le μ N Φ [i]
    rw [List.length_cons, List.length_nil, zero_add, pow_one] at h
    exact h
  calc ∑ i : d, ∫ ω, (∫ x in torusBox d, ‖pderiv i (graphDetector N Φ ω) x‖ ^ 2) ∂μ
      ≤ ∑ _i : d, (2 * Real.pi * (N : ℝ)) ^ 2 / ((N : ℝ) + 1) ^ Fintype.card d :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (Fintype.card d : ℝ) * ((2 * Real.pi * (N : ℝ)) ^ 2 /
          ((N : ℝ) + 1) ^ Fintype.card d) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **Sobolev decay.**  Every completed phase Sobolev quantity of the detector decays at the
subcritical rate. -/
theorem phaseSobolevSq_graphDetector_le (N k : ℕ) (Φ : Ω → (d → ℝ)) :
    phaseSobolevSq μ (graphDetector N Φ) k ≤
      ((multiIndexSet d k).card : ℝ) *
        ((1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) / ((N : ℝ) + 1) ^ Fintype.card d) := by
  rw [phaseSobolevSq]
  have hterm : ∀ α ∈ multiIndexSet d k,
      (∫ ω, (∫ x in torusBox d, ‖pderivList (multiIndexList α) (graphDetector N Φ ω) x‖ ^ 2) ∂μ) ≤
        (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) / ((N : ℝ) + 1) ^ Fintype.card d := by
    intro α hα
    refine le_trans (integral_graphDetector_pderivList_le μ N Φ (multiIndexList α)) ?_
    have hlen : (multiIndexList α).length ≤ k := by
      rw [length_multiIndexList]
      exact sum_le_of_mem_multiIndexSet hα
    have hb : (0 : ℝ) ≤ 2 * Real.pi * (N : ℝ) := by positivity
    have h1 : ((2 * Real.pi * (N : ℝ)) ^ (multiIndexList α).length) ^ 2
        ≤ (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) := by
      rw [← pow_mul, mul_comm ((multiIndexList α).length) 2]
      calc (2 * Real.pi * (N : ℝ)) ^ (2 * (multiIndexList α).length)
          ≤ (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * (multiIndexList α).length) :=
            pow_le_pow_left₀ hb (by linarith) _
        _ ≤ (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) :=
            pow_le_pow_right₀ (by linarith) (by omega)
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  calc ∑ α ∈ multiIndexSet d k,
        ∫ ω, (∫ x in torusBox d, ‖pderivList (multiIndexList α) (graphDetector N Φ ω) x‖ ^ 2) ∂μ
      ≤ ∑ _α ∈ multiIndexSet d k,
          (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) / ((N : ℝ) + 1) ^ Fintype.card d :=
        Finset.sum_le_sum hterm
    _ = ((multiIndexSet d k).card : ℝ) *
          ((1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) / ((N : ℝ) + 1) ^ Fintype.card d) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end GraphExperiment

section Limits

theorem tendsto_inv_pow_succ {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ => (((N : ℝ) + 1) ^ m)⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ m) atTop atTop := by
    refine Filter.Tendsto.comp (tendsto_pow_atTop (by omega)) ?_
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact h1.inv_tendsto_atTop

/-- The subcritical decay rate. -/
theorem tendsto_freq_pow_div_pow {k m : ℕ} (hkm : 2 * k < m) :
    Tendsto (fun N : ℕ => (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) / ((N : ℝ) + 1) ^ m)
      atTop (𝓝 0) := by
  have hkey : ∀ N : ℕ, (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) / ((N : ℝ) + 1) ^ m ≤
      (1 + 2 * Real.pi) ^ (2 * k) * ((((N : ℝ) + 1) ^ (m - 2 * k))⁻¹) := by
    intro N
    have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have h1 : (1 + 2 * Real.pi * (N : ℝ)) ≤ (1 + 2 * Real.pi) * ((N : ℝ) + 1) := by
      nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) N]
    have h2 : (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) ≤
        (1 + 2 * Real.pi) ^ (2 * k) * ((N : ℝ) + 1) ^ (2 * k) := by
      have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1 + 2 * Real.pi * (N : ℝ)) h1 (2 * k)
      rwa [mul_pow] at this
    have hsplit : ((N : ℝ) + 1) ^ m = ((N : ℝ) + 1) ^ (2 * k) * ((N : ℝ) + 1) ^ (m - 2 * k) := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((N : ℝ) + 1) ^ m), hsplit]
    have hid : (1 + 2 * Real.pi) ^ (2 * k) * (((N : ℝ) + 1) ^ (m - 2 * k))⁻¹ *
        (((N : ℝ) + 1) ^ (2 * k) * ((N : ℝ) + 1) ^ (m - 2 * k)) =
        (1 + 2 * Real.pi) ^ (2 * k) * ((N : ℝ) + 1) ^ (2 * k) := by
      field_simp
    rw [hid]
    exact h2
  have hlim : Tendsto
      (fun N : ℕ => (1 + 2 * Real.pi) ^ (2 * k) * ((((N : ℝ) + 1) ^ (m - 2 * k))⁻¹))
      atTop (𝓝 0) := by
    have := (tendsto_inv_pow_succ (m := m - 2 * k) (by omega)).const_mul
      ((1 + 2 * Real.pi) ^ (2 * k))
    simpa using this
  exact squeeze_zero (fun N => by positivity) hkey hlim

end Limits

section Blindness

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem phaseSobolevSq_nonneg (N k : ℕ) (Φ : Ω → (d → ℝ)) :
    0 ≤ phaseSobolevSq μ (graphDetector N Φ) k := by
  rw [phaseSobolevSq]
  refine Finset.sum_nonneg fun α _ => ?_
  rw [integral_graphDetector_pderivList]
  exact integral_nonneg fun x => sq_nonneg _

theorem completedSq_nonneg (N : ℕ) (Φ : Ω → (d → ℝ)) :
    0 ≤ completedSq μ (graphDetector N Φ) := by
  have h : completedSq μ (graphDetector N Φ) =
      ∫ ω, (∫ x in torusBox d, ‖pderivList ([] : List d) (graphDetector N Φ ω) x‖ ^ 2) ∂μ := rfl
  rw [h, integral_graphDetector_pderivList]
  exact integral_nonneg fun x => sq_nonneg _

theorem completedDirichlet_nonneg (N : ℕ) (Φ : Ω → (d → ℝ)) :
    0 ≤ completedDirichlet μ (graphDetector N Φ) := by
  rw [completedDirichlet]
  refine Finset.sum_nonneg fun i _ => ?_
  have h : (∫ ω, (∫ x in torusBox d, ‖pderiv i (graphDetector N Φ ω) x‖ ^ 2) ∂μ) =
      ∫ ω, (∫ x in torusBox d, ‖pderivList [i] (graphDetector N Φ ω) x‖ ^ 2) ∂μ := rfl
  rw [h, integral_graphDetector_pderivList]
  exact integral_nonneg fun x => sq_nonneg _

/-- **The graph-completed gap tends to one.** -/
theorem tendsto_graph_completed_gap (hd : 1 ≤ Fintype.card d) (Φ : Ω → (d → ℝ)) :
    Tendsto (fun N : ℕ => ‖graphExpectation μ Φ (graphDetector N Φ) -
        completedExpectation μ (graphDetector N Φ)‖) atTop (𝓝 1) := by
  have hpt : ∀ N : ℕ, ‖graphExpectation μ Φ (graphDetector N Φ) -
      completedExpectation μ (graphDetector N Φ)‖ =
      |1 - (((N : ℝ) + 1) ^ Fintype.card d)⁻¹| := by
    intro N
    rw [graphExpectation_graphDetector, completedExpectation_graphDetector]
    rw [show (1 : ℂ) - ((((((N : ℝ) + 1) ^ Fintype.card d)⁻¹ : ℝ)) : ℂ)
        = (((1 - (((N : ℝ) + 1) ^ Fintype.card d)⁻¹ : ℝ)) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  simp_rw [hpt]
  have h0 := tendsto_inv_pow_succ (m := Fintype.card d) hd
  have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub h0
  simpa using this.abs

/-- **The completed control tends to zero.** -/
theorem tendsto_completed_control (hd : 3 ≤ Fintype.card d) (Φ : Ω → (d → ℝ)) :
    Tendsto (fun N : ℕ => completedVar μ (graphDetector N Φ) +
      completedDirichlet μ (graphDetector N Φ)) atTop (𝓝 0) := by
  have hsq : Tendsto (fun N : ℕ => completedSq μ (graphDetector N Φ)) atTop (𝓝 0) :=
    squeeze_zero (fun N => completedSq_nonneg μ N Φ)
      (fun N => completedSq_graphDetector_le μ N Φ)
      (tendsto_inv_pow_succ (m := Fintype.card d) (by omega))
  have hE : Tendsto (fun N : ℕ => ‖completedExpectation μ (graphDetector N Φ)‖ ^ 2)
      atTop (𝓝 0) := by
    have hpt : ∀ N : ℕ, ‖completedExpectation μ (graphDetector N Φ)‖ ^ 2 =
        ((((N : ℝ) + 1) ^ Fintype.card d)⁻¹) ^ 2 := by
      intro N
      rw [completedExpectation_graphDetector, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
    simp_rw [hpt]
    have := (tendsto_inv_pow_succ (m := Fintype.card d) (by omega)).pow 2
    simpa using this
  have hdir : Tendsto (fun N : ℕ => completedDirichlet μ (graphDetector N Φ)) atTop (𝓝 0) := by
    refine squeeze_zero (fun N => completedDirichlet_nonneg μ N Φ)
      (fun N => completedDirichlet_graphDetector_le μ N Φ) ?_
    have hbase : Tendsto
        (fun N : ℕ => (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * 1) / ((N : ℝ) + 1) ^ Fintype.card d)
        atTop (𝓝 0) := tendsto_freq_pow_div_pow (by omega)
    have hcomp : ∀ N : ℕ, (Fintype.card d : ℝ) *
        ((2 * Real.pi * (N : ℝ)) ^ 2 / ((N : ℝ) + 1) ^ Fintype.card d) ≤
        (Fintype.card d : ℝ) *
          ((1 + 2 * Real.pi * (N : ℝ)) ^ (2 * 1) / ((N : ℝ) + 1) ^ Fintype.card d) := by
      intro N
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [div_eq_mul_inv, div_eq_mul_inv]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      simp only [pow_mul, pow_one]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos]) 2
    refine squeeze_zero (fun N => by positivity) hcomp ?_
    have := hbase.const_mul (Fintype.card d : ℝ)
    simpa using this
  have hvar : Tendsto (fun N : ℕ => completedVar μ (graphDetector N Φ)) atTop (𝓝 0) := by
    have := hsq.sub hE
    simpa [completedVar] using this
  have := hvar.add hdir
  simpa using this

/-- **No uniform Dirichlet-dual comparison.**  For every constant there is a resolution at which
the detector violates the proposed bound. -/
theorem exists_resolution_violating_dirichlet_bound (hd : 3 ≤ Fintype.card d)
    (Φ : Ω → (d → ℝ)) (C : ℝ) :
    ∃ N : ℕ, C * Real.sqrt (completedVar μ (graphDetector N Φ) +
        completedDirichlet μ (graphDetector N Φ)) <
      ‖graphExpectation μ Φ (graphDetector N Φ) -
        completedExpectation μ (graphDetector N Φ)‖ := by
  have hleft : Tendsto (fun N : ℕ => C * Real.sqrt (completedVar μ (graphDetector N Φ) +
      completedDirichlet μ (graphDetector N Φ))) atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp (tendsto_completed_control μ hd Φ)
    simp only [Function.comp_def, Real.sqrt_zero] at hs
    have := hs.const_mul C
    simpa using this
  have hright := tendsto_graph_completed_gap μ (by omega) Φ
  have h1 : ∀ᶠ N : ℕ in atTop, C * Real.sqrt (completedVar μ (graphDetector N Φ) +
      completedDirichlet μ (graphDetector N Φ)) < 1 / 2 :=
    (tendsto_order.1 hleft).2 (1 / 2) (by norm_num)
  have h2 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) / 2 < ‖graphExpectation μ Φ (graphDetector N Φ) -
      completedExpectation μ (graphDetector N Φ)‖ :=
    (tendsto_order.1 hright).1 (1 / 2) (by norm_num)
  obtain ⟨N, hN1, hN2⟩ := (h1.and h2).exists
  exact ⟨N, lt_trans hN1 hN2⟩

/-- **Subcritical Sobolev blindness.**  Below half the phase dimension the completed Sobolev
quantity of the detector tends to zero. -/
theorem tendsto_phaseSobolevSq_graphDetector (k : ℕ) (hk : 2 * k < Fintype.card d)
    (Φ : Ω → (d → ℝ)) :
    Tendsto (fun N : ℕ => phaseSobolevSq μ (graphDetector N Φ) k) atTop (𝓝 0) := by
  refine squeeze_zero (fun N => phaseSobolevSq_nonneg μ N k Φ)
    (fun N => phaseSobolevSq_graphDetector_le μ N k Φ) ?_
  have hbase := tendsto_freq_pow_div_pow (k := k) (m := Fintype.card d) hk
  have := hbase.const_mul ((multiIndexSet d k).card : ℝ)
  simpa using this

/-- **Graph restriction is unbounded on every subcritical Sobolev space.** -/
theorem exists_resolution_violating_sobolev_bound (k : ℕ) (hk : 2 * k < Fintype.card d)
    (Φ : Ω → (d → ℝ)) (C : ℝ) :
    ∃ N : ℕ, C * Real.sqrt (phaseSobolevSq μ (graphDetector N Φ) k) <
      ‖graphExpectation μ Φ (graphDetector N Φ)‖ := by
  have hleft : Tendsto (fun N : ℕ => C * Real.sqrt (phaseSobolevSq μ (graphDetector N Φ) k))
      atTop (𝓝 0) := by
    have hs := (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_phaseSobolevSq_graphDetector μ k hk Φ)
    simp only [Function.comp_def, Real.sqrt_zero] at hs
    have := hs.const_mul C
    simpa using this
  have h1 : ∀ᶠ N : ℕ in atTop, C * Real.sqrt (phaseSobolevSq μ (graphDetector N Φ) k) < 1 :=
    (tendsto_order.1 hleft).2 1 (by norm_num)
  obtain ⟨N, hN⟩ := h1.exists
  refine ⟨N, ?_⟩
  rw [graphExpectation_graphDetector, norm_one]
  exact hN

/-- **Projective form.**  For a `D`-dimensional state space the projective phase torus has `D - 1`
coordinates, so graph restriction is unbounded for every integer order below `(D - 1)/2`. -/
theorem exists_resolution_violating_sobolev_bound_projective (D k : ℕ)
    (hD : Fintype.card d + 1 = D) (hk : 2 * k + 1 < D) (Φ : Ω → (d → ℝ)) (C : ℝ) :
    ∃ N : ℕ, C * Real.sqrt (phaseSobolevSq μ (graphDetector N Φ) k) <
      ‖graphExpectation μ Φ (graphDetector N Φ)‖ :=
  exists_resolution_violating_sobolev_bound μ k (by omega) Φ C

end Blindness

section ManyBody

/-- **Many-body derivative-order barrier.**  For a qubit state space every polynomially growing
derivative order is eventually subcritical. -/
theorem eventually_polynomial_order_subcritical (j : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, k ≤ n ^ j → 2 * k + 1 < 2 ^ n := by
  have hlim : Tendsto (fun n : ℕ => (n : ℝ) ^ j / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt j (by norm_num)
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ j / (2 : ℝ) ^ n < 1 / 4 :=
    (tendsto_order.1 hlim).2 (1 / 4) (by norm_num)
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  intro k hk
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hkr : (k : ℝ) ≤ (n : ℝ) ^ j := by exact_mod_cast hk
  have hbound : 4 * (n : ℝ) ^ j < (2 : ℝ) ^ n := by
    rw [div_lt_iff₀ h2] at hn
    linarith
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ j := by
    refine one_le_pow₀ ?_
    exact_mod_cast hn1
  have : (2 * (k : ℝ) + 1) < (2 : ℝ) ^ n := by linarith
  exact_mod_cast this

end ManyBody

section ResolutionScale

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The resolution scale of the detector family. -/
def phaseScale (N : ℕ) : ℝ := ((N : ℝ) + 1)⁻¹

theorem phaseScale_pos (N : ℕ) : 0 < phaseScale N := by
  rw [phaseScale]
  positivity

theorem phaseScale_pow (N m : ℕ) : phaseScale N ^ m = (((N : ℝ) + 1) ^ m)⁻¹ := by
  rw [phaseScale, inv_pow]

/-- **Completed mean at scale.**  The detector has completed mean exactly the resolution scale to
the phase dimension. -/
theorem completedExpectation_graphDetector_scale (N : ℕ) (Φ : Ω → (d → ℝ)) :
    completedExpectation μ (graphDetector N Φ) =
      ((phaseScale N ^ Fintype.card d : ℝ) : ℂ) := by
  rw [completedExpectation_graphDetector, phaseScale_pow]

/-- **Completed variance at scale.** -/
theorem completedVar_graphDetector_le_scale (N : ℕ) (Φ : Ω → (d → ℝ)) :
    completedVar μ (graphDetector N Φ) ≤ phaseScale N ^ Fintype.card d := by
  rw [phaseScale_pow]
  exact completedVar_graphDetector_le μ N Φ

/-- **Completed Dirichlet energy at scale.**  The phase Dirichlet energy of the detector is at most
a dimensional constant times the resolution scale to the phase codimension of a gradient. -/
theorem completedDirichlet_graphDetector_le_scale (hd : 2 ≤ Fintype.card d) (N : ℕ)
    (Φ : Ω → (d → ℝ)) :
    completedDirichlet μ (graphDetector N Φ) ≤
      4 * Real.pi ^ 2 * (Fintype.card d : ℝ) * phaseScale N ^ (Fintype.card d - 2) := by
  refine le_trans (completedDirichlet_graphDetector_le μ N Φ) ?_
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsplit : ((N : ℝ) + 1) ^ Fintype.card d =
      ((N : ℝ) + 1) ^ 2 * ((N : ℝ) + 1) ^ (Fintype.card d - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hnum : (2 * Real.pi * (N : ℝ)) ^ 2 ≤ 4 * Real.pi ^ 2 * ((N : ℝ) + 1) ^ 2 := by
    have h1 : (2 * Real.pi * (N : ℝ)) ^ 2 = 4 * Real.pi ^ 2 * (N : ℝ) ^ 2 := by ring
    rw [h1]
    have h2 : ((N : ℝ)) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg N) (by linarith) 2
    nlinarith [Real.pi_pos, sq_nonneg Real.pi]
  rw [phaseScale_pow, hsplit]
  have hrw : (2 * Real.pi * (N : ℝ)) ^ 2 /
      (((N : ℝ) + 1) ^ 2 * ((N : ℝ) + 1) ^ (Fintype.card d - 2)) =
      ((2 * Real.pi * (N : ℝ)) ^ 2 / ((N : ℝ) + 1) ^ 2) *
        (((N : ℝ) + 1) ^ (Fintype.card d - 2))⁻¹ := by
    field_simp
  rw [hrw]
  have hfrac : (2 * Real.pi * (N : ℝ)) ^ 2 / ((N : ℝ) + 1) ^ 2 ≤ 4 * Real.pi ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    exact hnum
  calc (Fintype.card d : ℝ) * (((2 * Real.pi * (N : ℝ)) ^ 2 / ((N : ℝ) + 1) ^ 2) *
        (((N : ℝ) + 1) ^ (Fintype.card d - 2))⁻¹)
      ≤ (Fintype.card d : ℝ) * (4 * Real.pi ^ 2 *
          (((N : ℝ) + 1) ^ (Fintype.card d - 2))⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = 4 * Real.pi ^ 2 * (Fintype.card d : ℝ) *
          (((N : ℝ) + 1) ^ (Fintype.card d - 2))⁻¹ := by ring

/-- **Sobolev quantity at scale.**  Below half the phase dimension the detector's Sobolev quantity
is at most a dimensional constant times the resolution scale to the reduced phase dimension. -/
theorem phaseSobolevSq_graphDetector_le_scale {k : ℕ} (hk : 2 * k ≤ Fintype.card d) (N : ℕ)
    (Φ : Ω → (d → ℝ)) :
    phaseSobolevSq μ (graphDetector N Φ) k ≤
      ((multiIndexSet d k).card : ℝ) * (1 + 2 * Real.pi) ^ (2 * k) *
        phaseScale N ^ (Fintype.card d - 2 * k) := by
  refine le_trans (phaseSobolevSq_graphDetector_le μ N k Φ) ?_
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hsplit : ((N : ℝ) + 1) ^ Fintype.card d =
      ((N : ℝ) + 1) ^ (2 * k) * ((N : ℝ) + 1) ^ (Fintype.card d - 2 * k) := by
    rw [← pow_add]
    congr 1
    omega
  have hnum : (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) ≤
      (1 + 2 * Real.pi) ^ (2 * k) * ((N : ℝ) + 1) ^ (2 * k) := by
    have h1 : (1 + 2 * Real.pi * (N : ℝ)) ≤ (1 + 2 * Real.pi) * ((N : ℝ) + 1) := by
      nlinarith [Real.pi_pos, Nat.cast_nonneg (α := ℝ) N]
    have := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1 + 2 * Real.pi * (N : ℝ)) h1 (2 * k)
    rwa [mul_pow] at this
  rw [phaseScale_pow, hsplit]
  have hrw : (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) /
      (((N : ℝ) + 1) ^ (2 * k) * ((N : ℝ) + 1) ^ (Fintype.card d - 2 * k)) =
      ((1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) / ((N : ℝ) + 1) ^ (2 * k)) *
        (((N : ℝ) + 1) ^ (Fintype.card d - 2 * k))⁻¹ := by
    field_simp
  rw [hrw]
  have hfrac : (1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) / ((N : ℝ) + 1) ^ (2 * k) ≤
      (1 + 2 * Real.pi) ^ (2 * k) := by
    rw [div_le_iff₀ (by positivity)]
    exact hnum
  calc ((multiIndexSet d k).card : ℝ) *
        (((1 + 2 * Real.pi * (N : ℝ)) ^ (2 * k) / ((N : ℝ) + 1) ^ (2 * k)) *
          (((N : ℝ) + 1) ^ (Fintype.card d - 2 * k))⁻¹)
      ≤ ((multiIndexSet d k).card : ℝ) * ((1 + 2 * Real.pi) ^ (2 * k) *
          (((N : ℝ) + 1) ^ (Fintype.card d - 2 * k))⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        exact mul_le_mul_of_nonneg_right hfrac (by positivity)
    _ = ((multiIndexSet d k).card : ℝ) * (1 + 2 * Real.pi) ^ (2 * k) *
          (((N : ℝ) + 1) ^ (Fintype.card d - 2 * k))⁻¹ := by ring

end ResolutionScale

end GaloisForLFunctions.HTGeometry
