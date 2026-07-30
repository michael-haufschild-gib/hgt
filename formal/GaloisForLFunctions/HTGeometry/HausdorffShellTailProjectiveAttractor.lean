import GaloisForLFunctions.HTGeometry.AtomlessProbabilityLaws
import GaloisForLFunctions.HTGeometry.CountableWeightedDirac
import GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel

/-!
# The zero-shell projective attractor of a positive Hausdorff shell family

Let `ν = ∑_j w_j δ_{y_j}` be the Hausdorff coupling measure of a paired CDD divisor: the weights
`w_j` are strictly positive and summable, and the source points `y_j` form an antitone sequence in
`[0,1]` shrinking to zero.  Deleting the first `N` shells leaves the tail `ν_{≥N}` of mass
`M_N = ∑_{j ≥ N} w_j > 0`, and `ν̂_N = M_N⁻¹ ν_{≥N}` is a probability law.

This module proves, for **every** such family:

* **A.**  `ν̂_N → δ_0` weak-*, equivalently `∫ f dν̂_N → f(0)` for every continuous `f`;
* **B.**  the moments satisfy `b_0 = 1` and `0 ≤ b_m ≤ y_N^m → 0` for `m ≥ 1`, hence every
  normalized odd higher-spin coupling `8(-1)^m b_m/(2m+1)` collapses except the spin-one coupling,
  which is fixed at `8`;
* **C.**  the normalized phase obeys `|Σ̂_N(θ) − 8 sinh θ| ≤ (8/3) y_N cosh 3θ`, so it converges to
  the flat direction `8 sinh θ` uniformly on every bounded rapidity window, while the unnormalized
  tail phase and its exponential become trivial.

Nothing here refers to a particular shell law: only positivity, summability and the shrinking
nested supports are used.  The geometric family `y_j = r_j²`, `w_j = r_j` is one instance.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {w y : ℕ → ℝ}

/-- A positive Hausdorff shell family: strictly positive summable couplings carried by an antitone
sequence of source points in `[0,1]` shrinking to the zero shell. -/
structure PositiveShellFamily (w y : ℕ → ℝ) : Prop where
  /-- Every shell carries strictly positive coupling. -/
  weight_pos : ∀ j, 0 < w j
  /-- The total coupling is finite. -/
  weight_summable : Summable w
  /-- The source points are nonnegative. -/
  radius_nonneg : ∀ j, 0 ≤ y j
  /-- The source points lie in the Hausdorff interval. -/
  radius_le_one : ∀ j, y j ≤ 1
  /-- Deeper shells sit closer to the zero shell. -/
  radius_antitone : Antitone y
  /-- The shells accumulate only at the zero shell. -/
  radius_tendsto : Tendsto y atTop (𝓝 0)

namespace PositiveShellFamily

theorem summable_shift (hf : PositiveShellFamily w y) (N : ℕ) :
    Summable fun j : ℕ => w (N + j) := by
  refine ((summable_nat_add_iff N).2 hf.weight_summable).congr fun j => ?_
  rw [Nat.add_comm]

theorem atom_le (hf : PositiveShellFamily w y) (N j : ℕ) : y (N + j) ≤ y N :=
  hf.radius_antitone (Nat.le_add_right N j)

theorem atom_mem_Icc (hf : PositiveShellFamily w y) (N j : ℕ) :
    y (N + j) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hf.radius_nonneg _, hf.radius_le_one _⟩

end PositiveShellFamily

/-! ## The tail coupling mass -/

/-- The total coupling mass carried by the shells beyond level `N`. -/
def shellTailMass (w : ℕ → ℝ) (N : ℕ) : ℝ := ∑' j : ℕ, w (N + j)

theorem shellTailMass_pos (hf : PositiveShellFamily w y) (N : ℕ) : 0 < shellTailMass w N := by
  have h0 : w (N + 0) ≤ shellTailMass w N :=
    (hf.summable_shift N).le_tsum 0 fun j _ => (hf.weight_pos _).le
  have := hf.weight_pos (N + 0)
  linarith

/-- The deleted tail becomes weightless. -/
theorem tendsto_shellTailMass (v : ℕ → ℝ) :
    Tendsto (shellTailMass v) atTop (𝓝 0) := by
  refine (tendsto_sum_nat_add v).congr fun i => ?_
  exact tsum_congr fun k => by rw [Nat.add_comm]

/-- The normalized weight of the `j`-th surviving shell beyond level `N`. -/
def shellTailWeight (w : ℕ → ℝ) (N j : ℕ) : ℝ := w (N + j) / shellTailMass w N

theorem shellTailWeight_nonneg (hf : PositiveShellFamily w y) (N j : ℕ) :
    0 ≤ shellTailWeight w N j :=
  div_nonneg (hf.weight_pos _).le (shellTailMass_pos hf N).le

theorem summable_shellTailWeight (hf : PositiveShellFamily w y) (N : ℕ) :
    Summable fun j : ℕ => shellTailWeight w N j := by
  simpa [shellTailWeight, div_eq_inv_mul] using
    (hf.summable_shift N).mul_left (shellTailMass w N)⁻¹

theorem tsum_shellTailWeight (hf : PositiveShellFamily w y) (N : ℕ) :
    ∑' j : ℕ, shellTailWeight w N j = 1 := by
  have hM := (shellTailMass_pos hf N).ne'
  have hrw : ∑' j : ℕ, shellTailWeight w N j
      = (shellTailMass w N)⁻¹ * ∑' j : ℕ, w (N + j) := by
    simp only [shellTailWeight, div_eq_inv_mul]
    exact (hf.summable_shift N).tsum_mul_left _
  rw [hrw, ← shellTailMass, inv_mul_cancel₀ hM]

/-! ## The tail measures -/

/-- The unnormalized coupling measure of the shells beyond level `N`. -/
def shellTailMeasure (w y : ℕ → ℝ) (N : ℕ) : Measure ℝ :=
  _root_.HTGeometry.countableWeightedDirac (fun j => w (N + j)) (fun j => y (N + j))

/-- The normalized tail measure `ν̂_N = M_N⁻¹ ν_{≥N}`. -/
def shellNormalizedTailMeasure (w y : ℕ → ℝ) (N : ℕ) : Measure ℝ :=
  _root_.HTGeometry.countableWeightedDirac (shellTailWeight w N) (fun j => y (N + j))

theorem shellNormalizedTailMeasure_eq_smul (hf : PositiveShellFamily w y) (N : ℕ) :
    shellNormalizedTailMeasure w y N
      = ENNReal.ofReal (shellTailMass w N)⁻¹ • shellTailMeasure w y N := by
  have hinv : (0 : ℝ) ≤ (shellTailMass w N)⁻¹ := inv_nonneg.mpr (shellTailMass_pos hf N).le
  rw [shellTailMeasure, ← _root_.HTGeometry.countableWeightedDirac_const_mul hinv,
    shellNormalizedTailMeasure]
  congr 1
  funext j
  simp [shellTailWeight, div_eq_inv_mul]

theorem shellTailMeasure_univ (hf : PositiveShellFamily w y) (N : ℕ) :
    shellTailMeasure w y N Set.univ = ENNReal.ofReal (shellTailMass w N) :=
  _root_.HTGeometry.countableWeightedDirac_univ_ofReal
    (fun _ => (hf.weight_pos _).le) (hf.summable_shift N) _

theorem shellNormalizedTailMeasure_univ (hf : PositiveShellFamily w y) (N : ℕ) :
    shellNormalizedTailMeasure w y N Set.univ = 1 := by
  rw [shellNormalizedTailMeasure,
    _root_.HTGeometry.countableWeightedDirac_univ_ofReal
      (fun j => shellTailWeight_nonneg hf N j) (summable_shellTailWeight hf N),
    tsum_shellTailWeight hf N, ENNReal.ofReal_one]

theorem isProbabilityMeasure_shellNormalizedTailMeasure
    (hf : PositiveShellFamily w y) (N : ℕ) :
    IsProbabilityMeasure (shellNormalizedTailMeasure w y N) :=
  ⟨shellNormalizedTailMeasure_univ hf N⟩

/-- The normalized tail measure as a bundled probability law. -/
def shellTailProbability (hf : PositiveShellFamily w y) (N : ℕ) : ProbabilityMeasure ℝ :=
  ⟨shellNormalizedTailMeasure w y N, isProbabilityMeasure_shellNormalizedTailMeasure hf N⟩

@[simp]
theorem shellTailProbability_toMeasure (hf : PositiveShellFamily w y) (N : ℕ) :
    (shellTailProbability hf N : Measure ℝ) = shellNormalizedTailMeasure w y N := rfl

/-! ## Theorem A: the normalized tail collapses to the zero shell -/

/-- Outside any ball strictly larger than `y_N` the normalized tail carries no mass. -/
theorem shellNormalizedTailMeasure_compl_ball (hf : PositiveShellFamily w y) (N : ℕ) {ε : ℝ}
    (hε : y N < ε) :
    shellNormalizedTailMeasure w y N (Metric.ball (0 : ℝ) ε)ᶜ = 0 := by
  rw [shellNormalizedTailMeasure,
    _root_.HTGeometry.countableWeightedDirac_apply _ _
      (measurableSet_ball (x := (0 : ℝ)) (ε := ε)).compl]
  refine ENNReal.tsum_eq_zero.mpr fun j => ?_
  have hmem : y (N + j) ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (hf.radius_nonneg _)]
    exact lt_of_le_of_lt (hf.atom_le N j) hε
  rw [Set.indicator_of_notMem (by simpa using hmem), mul_zero]

/-- The normalized tail measure is carried by `[0, y_N]`. -/
theorem shellNormalizedTailMeasure_compl_Icc (hf : PositiveShellFamily w y) (N : ℕ) :
    shellNormalizedTailMeasure w y N (Set.Icc 0 (y N))ᶜ = 0 := by
  rw [shellNormalizedTailMeasure,
    _root_.HTGeometry.countableWeightedDirac_apply _ _ measurableSet_Icc.compl]
  refine ENNReal.tsum_eq_zero.mpr fun j => ?_
  have hmem : y (N + j) ∈ Set.Icc (0 : ℝ) (y N) := ⟨hf.radius_nonneg _, hf.atom_le N j⟩
  rw [Set.indicator_of_notMem (by simpa using hmem), mul_zero]

/-- **Theorem A.**  The normalized tail laws converge weak-* to the Dirac law at the zero shell. -/
theorem tendsto_shellTailProbability_diracProba (hf : PositiveShellFamily w y) :
    Tendsto (fun N => shellTailProbability hf N) atTop (𝓝 (diracProba (0 : ℝ))) := by
  refine GaloisForLFunctions.HTGeometry.tendsto_diracProba_of_eventually_measure_nhds_eq_one
    _ _ ?_
  intro U hU
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hU
  filter_upwards [hf.radius_tendsto.eventually (eventually_lt_nhds hε)] with N hN
  haveI := isProbabilityMeasure_shellNormalizedTailMeasure hf N
  have hzero := shellNormalizedTailMeasure_compl_ball hf N hN
  have hball : shellNormalizedTailMeasure w y N (Metric.ball (0 : ℝ) ε) = 1 := by
    have hadd := measure_add_measure_compl
      (μ := shellNormalizedTailMeasure w y N)
      (measurableSet_ball (x := (0 : ℝ)) (ε := ε))
    rw [hzero, add_zero, measure_univ] at hadd
    exact hadd
  have hle : (1 : ENNReal) ≤ shellNormalizedTailMeasure w y N U := by
    rw [← hball]
    exact measure_mono hsub
  exact le_antisymm prob_le_one hle

/-! ## Integration against the normalized tail -/

theorem summable_shellTailWeight_mul_abs (hf : PositiveShellFamily w y) (N : ℕ)
    {f : ℝ → ℝ} (hcont : Continuous f) :
    Summable fun j : ℕ => shellTailWeight w N j * |f (y (N + j))| := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine Summable.of_nonneg_of_le
    (fun j => mul_nonneg (shellTailWeight_nonneg hf N j) (abs_nonneg _))
    (fun j => ?_) ((summable_shellTailWeight hf N).mul_right K)
  have hb := hK _ (hf.atom_mem_Icc N j)
  rw [Real.norm_eq_abs] at hb
  nlinarith [shellTailWeight_nonneg hf N j]

theorem summable_shellTailWeight_mul (hf : PositiveShellFamily w y) (N : ℕ)
    {f : ℝ → ℝ} (hcont : Continuous f) :
    Summable fun j : ℕ => shellTailWeight w N j * f (y (N + j)) := by
  refine Summable.of_norm_bounded (summable_shellTailWeight_mul_abs hf N hcont) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (shellTailWeight_nonneg hf N j)]

theorem integrable_shellNormalizedTailMeasure (hf : PositiveShellFamily w y) (N : ℕ)
    {f : ℝ → ℝ} (hcont : Continuous f) :
    Integrable f (shellNormalizedTailMeasure w y N) :=
  _root_.HTGeometry.integrable_countableWeightedDirac
    (fun j => shellTailWeight_nonneg hf N j) hcont.aestronglyMeasurable
    (summable_shellTailWeight_mul_abs hf N hcont)

theorem integral_shellNormalizedTailMeasure (hf : PositiveShellFamily w y) (N : ℕ)
    {f : ℝ → ℝ} (hcont : Continuous f) :
    ∫ t, f t ∂(shellNormalizedTailMeasure w y N)
      = ∑' j : ℕ, shellTailWeight w N j * f (y (N + j)) :=
  _root_.HTGeometry.integral_countableWeightedDirac
    (fun j => shellTailWeight_nonneg hf N j)
    (integrable_shellNormalizedTailMeasure hf N hcont)

/-- **Theorem A, test-function form.**  The normalized tail integrates every continuous function to
its zero-shell value. -/
theorem tendsto_integral_shellNormalizedTailMeasure (hf : PositiveShellFamily w y)
    {f : ℝ → ℝ} (hcont : Continuous f) :
    Tendsto (fun N => ∫ t, f t ∂(shellNormalizedTailMeasure w y N)) atTop (𝓝 (f 0)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ := Metric.continuousAt_iff.mp hcont.continuousAt (ε / 2) (by linarith)
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hf.radius_tendsto) δ hδ
  refine ⟨N₀, fun N hN => ?_⟩
  have hrad : y N < δ := by
    have hd := hN₀ N hN
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hf.radius_nonneg N)] at hd
  have hdistj : ∀ j : ℕ, |f (y (N + j)) - f 0| ≤ ε / 2 := by
    intro j
    have hlt : dist (y (N + j)) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf.radius_nonneg _)]
      exact lt_of_le_of_lt (hf.atom_le N j) hrad
    have hc := hclose hlt
    rw [Real.dist_eq] at hc
    linarith
  have hsumf := summable_shellTailWeight_mul hf N hcont
  have hkey : (∑' j : ℕ, shellTailWeight w N j * (f (y (N + j)) - f 0))
      = (∫ t, f t ∂(shellNormalizedTailMeasure w y N)) - f 0 := by
    have hsplit : (fun j : ℕ => shellTailWeight w N j * (f (y (N + j)) - f 0))
        = fun j : ℕ => shellTailWeight w N j * f (y (N + j))
          - shellTailWeight w N j * f 0 := by
      funext j; ring
    rw [hsplit, Summable.tsum_sub hsumf ((summable_shellTailWeight hf N).mul_right (f 0)),
      (summable_shellTailWeight hf N).tsum_mul_right, tsum_shellTailWeight hf N,
      one_mul, integral_shellNormalizedTailMeasure hf N hcont]
  have hnorm : Summable fun j : ℕ => ‖shellTailWeight w N j * (f (y (N + j)) - f 0)‖ := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((summable_shellTailWeight hf N).mul_right (ε / 2))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (shellTailWeight_nonneg hf N j)]
    nlinarith [shellTailWeight_nonneg hf N j, hdistj j, abs_nonneg (f (y (N + j)) - f 0)]
  have hbnd : (∑' j : ℕ, ‖shellTailWeight w N j * (f (y (N + j)) - f 0)‖)
      ≤ ∑' j : ℕ, shellTailWeight w N j * (ε / 2) := by
    refine Summable.tsum_le_tsum (fun j => ?_) hnorm
      ((summable_shellTailWeight hf N).mul_right (ε / 2))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (shellTailWeight_nonneg hf N j)]
    nlinarith [shellTailWeight_nonneg hf N j, hdistj j, abs_nonneg (f (y (N + j)) - f 0)]
  have hhalf : (∑' j : ℕ, shellTailWeight w N j * (ε / 2)) = ε / 2 := by
    rw [(summable_shellTailWeight hf N).tsum_mul_right, tsum_shellTailWeight hf N, one_mul]
  have htri := norm_tsum_le_tsum_norm hnorm
  rw [Real.norm_eq_abs, hkey] at htri
  rw [Real.dist_eq]
  have hfin : |(∫ t, f t ∂(shellNormalizedTailMeasure w y N)) - f 0| ≤ ε / 2 := by
    refine htri.trans ?_
    rw [← hhalf]
    exact hbnd
  linarith

/-! ## Theorem B: all normalized higher-spin directions except spin one vanish -/

/-- The `m`-th moment of the normalized tail measure. -/
def shellTailMoment (w y : ℕ → ℝ) (N m : ℕ) : ℝ :=
  ∑' j : ℕ, shellTailWeight w N j * y (N + j) ^ m

theorem summable_shellTailMomentTerm (hf : PositiveShellFamily w y) (N m : ℕ) :
    Summable fun j : ℕ => shellTailWeight w N j * y (N + j) ^ m := by
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) (summable_shellTailWeight hf N)
  · exact mul_nonneg (shellTailWeight_nonneg hf N j) (pow_nonneg (hf.radius_nonneg _) m)
  · have hle : y (N + j) ^ m ≤ 1 := pow_le_one₀ (hf.radius_nonneg _) (hf.radius_le_one _)
    nlinarith [shellTailWeight_nonneg hf N j, pow_nonneg (hf.radius_nonneg (N + j)) m]

@[simp]
theorem shellTailMoment_zero (hf : PositiveShellFamily w y) (N : ℕ) :
    shellTailMoment w y N 0 = 1 := by
  simpa [shellTailMoment] using tsum_shellTailWeight hf N

theorem shellTailMoment_nonneg (hf : PositiveShellFamily w y) (N m : ℕ) :
    0 ≤ shellTailMoment w y N m :=
  tsum_nonneg fun j =>
    mul_nonneg (shellTailWeight_nonneg hf N j) (pow_nonneg (hf.radius_nonneg _) m)

/-- **Theorem B, bound.**  The `m`-th normalized tail moment is at most `y_N^m`. -/
theorem shellTailMoment_le (hf : PositiveShellFamily w y) (N m : ℕ) :
    shellTailMoment w y N m ≤ y N ^ m := by
  have hcmp : shellTailMoment w y N m ≤ ∑' j : ℕ, shellTailWeight w N j * y N ^ m := by
    refine Summable.tsum_le_tsum (fun j => ?_) (summable_shellTailMomentTerm hf N m)
      ((summable_shellTailWeight hf N).mul_right _)
    have hstep := pow_le_pow_left₀ (hf.radius_nonneg (N + j)) (hf.atom_le N j) m
    nlinarith [shellTailWeight_nonneg hf N j]
  have hval : (∑' j : ℕ, shellTailWeight w N j * y N ^ m) = y N ^ m := by
    rw [(summable_shellTailWeight hf N).tsum_mul_right, tsum_shellTailWeight hf N, one_mul]
  linarith [hcmp, hval.le, hval.ge]

/-- **Theorem B, collapse.**  Every moment of positive order tends to zero along the shell tail. -/
theorem tendsto_shellTailMoment (hf : PositiveShellFamily w y) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N => shellTailMoment w y N m) atTop (𝓝 0) := by
  have hb : Tendsto (fun N : ℕ => y N ^ m) atTop (𝓝 0) := by
    have hpow := hf.radius_tendsto.pow m
    rwa [zero_pow (by omega : m ≠ 0)] at hpow
  exact squeeze_zero (fun N => shellTailMoment_nonneg hf N m)
    (fun N => shellTailMoment_le hf N m) hb

/-- The moments are the integrals of the monomials. -/
theorem integral_pow_shellNormalizedTailMeasure (hf : PositiveShellFamily w y) (N m : ℕ) :
    ∫ t, t ^ m ∂(shellNormalizedTailMeasure w y N) = shellTailMoment w y N m :=
  integral_shellNormalizedTailMeasure hf N (continuous_pow m)

/-- The normalized odd higher-spin coupling `α̂_{2m+1} = 8(-1)^m b_m/(2m+1)`. -/
def shellNormalizedSpinCoupling (w y : ℕ → ℝ) (N m : ℕ) : ℝ :=
  8 * (-1) ^ m * shellTailMoment w y N m / (2 * m + 1)

/-- The spin-one coupling is the fixed value `8` at every truncation level. -/
@[simp]
theorem shellNormalizedSpinCoupling_zero (hf : PositiveShellFamily w y) (N : ℕ) :
    shellNormalizedSpinCoupling w y N 0 = 8 := by
  simp [shellNormalizedSpinCoupling, shellTailMoment_zero hf N]

/-- **Theorem B, projective direction.**  Every higher-spin coupling collapses; only the spin-one
current–current direction survives. -/
theorem tendsto_shellNormalizedSpinCoupling (hf : PositiveShellFamily w y) {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N => shellNormalizedSpinCoupling w y N m) atTop (𝓝 0) := by
  have h := (tendsto_shellTailMoment hf hm).const_mul (8 * (-1) ^ m)
  have h2 := h.div_const ((2 : ℝ) * m + 1)
  simpa [shellNormalizedSpinCoupling] using h2

/-! ## Theorem C: the normalized phase converges to the flat direction -/

/-- The unnormalized tail phase `Σ_{≥N}(θ) = ∫ K dν_{≥N}`. -/
def shellTailPhase (w y : ℕ → ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  ∑' j : ℕ, w (N + j) * cddPhaseKernel (y (N + j)) θ

/-- The normalized tail phase `Σ̂_N(θ) = ∫ K dν̂_N`. -/
def shellNormalizedTailPhase (w y : ℕ → ℝ) (N : ℕ) (θ : ℝ) : ℝ :=
  ∑' j : ℕ, shellTailWeight w N j * cddPhaseKernel (y (N + j)) θ

theorem summable_shellNormalizedTailPhase (hf : PositiveShellFamily w y) (N : ℕ) (θ : ℝ) :
    Summable fun j : ℕ => shellTailWeight w N j * cddPhaseKernel (y (N + j)) θ :=
  summable_shellTailWeight_mul hf N (continuous_cddPhaseKernel θ)

/-- Termwise kernel defect bound along the tail. -/
theorem abs_cddPhaseKernel_atom_sub_flat_le (hf : PositiveShellFamily w y) (N j : ℕ) (θ : ℝ) :
    |cddPhaseKernel (y (N + j)) θ - 8 * Real.sinh θ|
      ≤ 8 / 3 * y N * Real.cosh (3 * θ) := by
  have hker := abs_cddPhaseKernel_sub_flat_le (y (N + j)) θ
  rw [abs_of_nonneg (hf.radius_nonneg (N + j))] at hker
  have hcosh := (Real.cosh_pos (3 * θ)).le
  have hatom := hf.atom_le N j
  nlinarith

/-- **Theorem C, sharp estimate.**  The normalized tail phase differs from the flat direction
`8 sinh θ` by at most `(8/3) y_N cosh 3θ`. -/
theorem abs_shellNormalizedTailPhase_sub_flat_le
    (hf : PositiveShellFamily w y) (N : ℕ) (θ : ℝ) :
    |shellNormalizedTailPhase w y N θ - 8 * Real.sinh θ|
      ≤ 8 / 3 * y N * Real.cosh (3 * θ) := by
  have hflat : (∑' j : ℕ, shellTailWeight w N j * (8 * Real.sinh θ)) = 8 * Real.sinh θ := by
    rw [(summable_shellTailWeight hf N).tsum_mul_right, tsum_shellTailWeight hf N, one_mul]
  have hdiff : (∑' j : ℕ, shellTailWeight w N j *
        (cddPhaseKernel (y (N + j)) θ - 8 * Real.sinh θ))
      = shellNormalizedTailPhase w y N θ - 8 * Real.sinh θ := by
    have hsplit : (fun j : ℕ => shellTailWeight w N j *
          (cddPhaseKernel (y (N + j)) θ - 8 * Real.sinh θ))
        = fun j : ℕ => shellTailWeight w N j * cddPhaseKernel (y (N + j)) θ
          - shellTailWeight w N j * (8 * Real.sinh θ) := by
      funext j; ring
    rw [hsplit, Summable.tsum_sub (summable_shellNormalizedTailPhase hf N θ)
      ((summable_shellTailWeight hf N).mul_right (8 * Real.sinh θ)), hflat,
      shellNormalizedTailPhase]
  rw [← hdiff]
  have hnormsum : Summable fun j : ℕ =>
      ‖shellTailWeight w N j * (cddPhaseKernel (y (N + j)) θ - 8 * Real.sinh θ)‖ := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((summable_shellTailWeight hf N).mul_right (8 / 3 * y N * Real.cosh (3 * θ)))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (shellTailWeight_nonneg hf N j)]
    nlinarith [shellTailWeight_nonneg hf N j, abs_cddPhaseKernel_atom_sub_flat_le hf N j θ,
      abs_nonneg (cddPhaseKernel (y (N + j)) θ - 8 * Real.sinh θ)]
  have hle := norm_tsum_le_tsum_norm hnormsum
  rw [Real.norm_eq_abs] at hle
  refine hle.trans ?_
  have hbnd : (∑' j : ℕ,
      ‖shellTailWeight w N j * (cddPhaseKernel (y (N + j)) θ - 8 * Real.sinh θ)‖)
      ≤ ∑' j : ℕ, shellTailWeight w N j * (8 / 3 * y N * Real.cosh (3 * θ)) := by
    refine Summable.tsum_le_tsum (fun j => ?_) hnormsum
      ((summable_shellTailWeight hf N).mul_right _)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (shellTailWeight_nonneg hf N j)]
    nlinarith [shellTailWeight_nonneg hf N j, abs_cddPhaseKernel_atom_sub_flat_le hf N j θ,
      abs_nonneg (cddPhaseKernel (y (N + j)) θ - 8 * Real.sinh θ)]
  refine hbnd.trans (le_of_eq ?_)
  rw [(summable_shellTailWeight hf N).tsum_mul_right, tsum_shellTailWeight hf N, one_mul]

/-- Pointwise convergence of the normalized tail phase to the flat direction. -/
theorem tendsto_shellNormalizedTailPhase (hf : PositiveShellFamily w y) (θ : ℝ) :
    Tendsto (fun N => shellNormalizedTailPhase w y N θ) atTop (𝓝 (8 * Real.sinh θ)) := by
  have hb : Tendsto (fun N : ℕ => 8 / 3 * y N * Real.cosh (3 * θ)) atTop (𝓝 0) := by
    simpa using (hf.radius_tendsto.const_mul (8 / 3 : ℝ)).mul_const (Real.cosh (3 * θ))
  have hlim : Tendsto (fun N => shellNormalizedTailPhase w y N θ - 8 * Real.sinh θ)
      atTop (𝓝 0) :=
    squeeze_zero_norm (fun N => abs_shellNormalizedTailPhase_sub_flat_le hf N θ) hb
  have hshift := hlim.add_const (8 * Real.sinh θ)
  simpa using hshift

/-- **Theorem C, locally uniform convergence.**  On every bounded rapidity window the normalized
tail phase converges uniformly to the flat direction `8 sinh θ`. -/
theorem tendstoUniformlyOn_shellNormalizedTailPhase (hf : PositiveShellFamily w y) (T : ℝ) :
    TendstoUniformlyOn (fun N θ => shellNormalizedTailPhase w y N θ)
      (fun θ => 8 * Real.sinh θ) atTop (Set.Icc (-T) T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hb : Tendsto (fun N : ℕ => 8 / 3 * y N * Real.exp (3 * T)) atTop (𝓝 0) := by
    simpa using (hf.radius_tendsto.const_mul (8 / 3 : ℝ)).mul_const (Real.exp (3 * T))
  filter_upwards [hb.eventually (eventually_lt_nhds hε)] with N hN θ hθ
  have hbound := abs_shellNormalizedTailPhase_sub_flat_le hf N θ
  have habs : |3 * θ| ≤ 3 * T := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
    have := abs_le.mpr ⟨hθ.1, hθ.2⟩
    linarith
  have hcosh : Real.cosh (3 * θ) ≤ Real.exp (3 * T) :=
    (cosh_le_exp_abs (3 * θ)).trans (Real.exp_le_exp.mpr habs)
  have hstep : 8 / 3 * y N * Real.cosh (3 * θ) ≤ 8 / 3 * y N * Real.exp (3 * T) := by
    have := hf.radius_nonneg N
    nlinarith
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-- **Theorem C, exponentiated form.**  The normalized tail scattering factor converges to the
universal flat dressing `exp(8 i sinh θ)`. -/
theorem tendsto_exp_shellNormalizedTailPhase (hf : PositiveShellFamily w y) (θ : ℝ) :
    Tendsto (fun N => Complex.exp (Complex.I * (shellNormalizedTailPhase w y N θ : ℂ))) atTop
      (𝓝 (Complex.exp (Complex.I * ((8 * Real.sinh θ : ℝ) : ℂ)))) := by
  have hfun : Continuous fun z : ℂ => Complex.exp (Complex.I * z) :=
    Complex.continuous_exp.comp (continuous_const.mul continuous_id)
  have hcast : Tendsto (fun N => ((shellNormalizedTailPhase w y N θ : ℝ) : ℂ)) atTop
      (𝓝 ((8 * Real.sinh θ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_shellNormalizedTailPhase hf θ)
  exact (hfun.continuousAt.tendsto).comp hcast

/-- The normalized phase is the kernel integral against the normalized tail. -/
theorem integral_cddPhaseKernel_shellNormalizedTailMeasure
    (hf : PositiveShellFamily w y) (N : ℕ) (θ : ℝ) :
    ∫ t, cddPhaseKernel t θ ∂(shellNormalizedTailMeasure w y N)
      = shellNormalizedTailPhase w y N θ :=
  integral_shellNormalizedTailMeasure hf N (continuous_cddPhaseKernel θ)

/-! ### The unnormalized tail is asymptotically trivial -/

theorem summable_shellTailPhaseTerm (hf : PositiveShellFamily w y) (N : ℕ) (θ : ℝ)
    {K : ℝ} (hK : ∀ t ∈ Set.Icc (0 : ℝ) 1, |cddPhaseKernel t θ| ≤ K) :
    Summable fun j : ℕ => w (N + j) * cddPhaseKernel (y (N + j)) θ := by
  refine Summable.of_norm_bounded ((hf.summable_shift N).mul_right K) (fun j => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.weight_pos _).le]
  have hb := hK _ (hf.atom_mem_Icc N j)
  nlinarith [(hf.weight_pos (N + j)).le, abs_nonneg (cddPhaseKernel (y (N + j)) θ)]

/-- The unnormalized tail phase is bounded by the tail mass times the kernel size. -/
theorem abs_shellTailPhase_le (hf : PositiveShellFamily w y) (N : ℕ) (θ : ℝ)
    {K : ℝ} (hK : ∀ t ∈ Set.Icc (0 : ℝ) 1, |cddPhaseKernel t θ| ≤ K) :
    |shellTailPhase w y N θ| ≤ shellTailMass w N * K := by
  have hnorm : Summable fun j : ℕ => ‖w (N + j) * cddPhaseKernel (y (N + j)) θ‖ := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((hf.summable_shift N).mul_right K)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.weight_pos _).le]
    have hb := hK _ (hf.atom_mem_Icc N j)
    nlinarith [(hf.weight_pos (N + j)).le, abs_nonneg (cddPhaseKernel (y (N + j)) θ)]
  have hle := norm_tsum_le_tsum_norm hnorm
  rw [Real.norm_eq_abs] at hle
  refine hle.trans ?_
  have hcmp : (∑' j : ℕ, ‖w (N + j) * cddPhaseKernel (y (N + j)) θ‖)
      ≤ ∑' j : ℕ, w (N + j) * K := by
    refine Summable.tsum_le_tsum (fun j => ?_) hnorm ((hf.summable_shift N).mul_right K)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hf.weight_pos _).le]
    have hb := hK _ (hf.atom_mem_Icc N j)
    nlinarith [(hf.weight_pos (N + j)).le, abs_nonneg (cddPhaseKernel (y (N + j)) θ)]
  refine hcmp.trans (le_of_eq ?_)
  rw [(hf.summable_shift N).tsum_mul_right, ← shellTailMass]

/-- The unnormalized tail phase vanishes in the deep-shell limit. -/
theorem tendsto_shellTailPhase (hf : PositiveShellFamily w y) (θ : ℝ) :
    Tendsto (fun N => shellTailPhase w y N θ) atTop (𝓝 0) := by
  obtain ⟨K, hK⟩ := exists_bound_cddPhaseKernel θ
  have hKnn : 0 ≤ K := le_trans (abs_nonneg _) (hK 0 ⟨le_refl 0, zero_le_one⟩)
  have hb : Tendsto (fun N : ℕ => shellTailMass w N * K) atTop (𝓝 0) := by
    simpa using (tendsto_shellTailMass w).mul_const K
  exact squeeze_zero_norm (fun N => abs_shellTailPhase_le hf N θ hK) hb

/-- The unnormalized tail scattering factor becomes trivial. -/
theorem tendsto_exp_shellTailPhase (hf : PositiveShellFamily w y) (θ : ℝ) :
    Tendsto (fun N => Complex.exp (Complex.I * (shellTailPhase w y N θ : ℂ))) atTop (𝓝 1) := by
  have hfun : Continuous fun z : ℂ => Complex.exp (Complex.I * z) :=
    Complex.continuous_exp.comp (continuous_const.mul continuous_id)
  have hcast : Tendsto (fun N => ((shellTailPhase w y N θ : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
    simpa using! Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_shellTailPhase hf θ)
  have hlim := (hfun.continuousAt.tendsto).comp hcast
  simpa using! hlim

end

end GaloisForLFunctions.HTGeometry
