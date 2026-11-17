import GaloisForLFunctions.HilbertMetric.Bergman.DiskAreaSurjectivity

/-!
# Sharp central Bergman and Carathéodory jet norms

The normalized area model has value extremal one and first-jet extremal
sqrt(2) at the origin. The latter is attained by the normalized linear
monomial. Schwarz's lemma gives the actual Carathéodory extremal one,
so the scalar Bergman/Carathéodory ratio is exactly sqrt(2), realizing
the p = 2 disk case of the extremal normalization in arXiv:2611.08616.
-/

open Complex Metric Set
namespace GaloisForLFunctions.HilbertMetric.Bergman
open HTGeometry
noncomputable section

@[simp] theorem diskFun_zero (a : Disk) : diskFun a 0 = a 0 := by
  simpa [diskCoeff, coefficient] using diskCoeff_diskFun a 0

/-- The first derivative is the first normalized Bergman coordinate. -/
theorem deriv_diskFun_zero (a : Disk) : deriv (diskFun a) 0 = (Real.sqrt 2 : ℂ) * a 1 := by
  have h := diskCoeff_diskFun a 1
  norm_num [diskCoeff, coefficient] at h
  exact h

private theorem central_derivative_bound (a : Disk) :
    ‖deriv (diskFun a) 0‖ ≤ Real.sqrt 2 * ‖a‖ := by
  rw [deriv_diskFun_zero, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (hardyDisk_norm_coord_le a 1) (Real.sqrt_nonneg _)

/-- Exactly one is the largest central value on the normalized Bergman unit ball. -/
theorem central_value_isGreatest :
    IsGreatest {r : ℝ | ∃ a : Disk, ‖a‖ ≤ 1 ∧ ‖diskFun a 0‖ = r} 1 := by
  constructor
  · refine ⟨lp.single 2 0 (1 : ℂ), ?_, ?_⟩
    · rw [lp.norm_single (by norm_num), norm_one]
    · simp [diskFun_zero, lp.single_apply]
  · rintro r ⟨a, ha, rfl⟩
    rw [diskFun_zero]
    exact (hardyDisk_norm_coord_le a 0).trans ha

/-- Exactly sqrt(2) is the largest zero-preserving central first derivative. -/
theorem central_jet_isGreatest :
    IsGreatest {r : ℝ | ∃ a : Disk,
      ‖a‖ ≤ 1 ∧ diskFun a 0 = 0 ∧ ‖deriv (diskFun a) 0‖ = r} (Real.sqrt 2) := by
  constructor
  · refine ⟨lp.single 2 1 (1 : ℂ), ?_, ?_, ?_⟩
    · rw [lp.norm_single (by norm_num), norm_one]
    · simp [diskFun_zero, lp.single_apply]
    · simp [deriv_diskFun_zero, lp.single_apply, Real.sqrt_nonneg]
  · rintro r ⟨a, ha, _, rfl⟩
    exact (central_derivative_bound a).trans
      (by simpa only [mul_one] using mul_le_mul_of_nonneg_left ha (Real.sqrt_nonneg 2))

private theorem schwarz_derivative_bound {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 1)) (hz : f 0 = 0)
    (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1) : ‖deriv f 0‖ ≤ 1 := by
  have hm : MapsTo f (ball (0 : ℂ) 1) (closedBall (f 0) 1) := by
    intro z hzin
    rw [mem_closedBall, hz, dist_zero_right]
    exact hb z hzin
  have h := (fderiv ℂ f 0).le_opNorm (1 : ℂ)
  simp only [norm_one, mul_one] at h
  exact h.trans (Complex.norm_fderiv_le_one_of_mapsTo_ball hf hm zero_lt_one)

/-- The genuine holomorphic Carathéodory central jet extremal is one. -/
theorem central_caratheodory_isGreatest :
    IsGreatest {r : ℝ | ∃ f : ℂ → ℂ,
      DifferentiableOn ℂ f (ball 0 1) ∧ f 0 = 0 ∧
      (∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1) ∧ ‖deriv f 0‖ = r} 1 := by
  constructor
  · refine ⟨id, differentiableOn_id, rfl, ?_, ?_⟩
    · intro z hz
      exact (show ‖z‖ < 1 by simpa only [mem_ball, dist_zero_right] using hz).le
    · simp
  · rintro r ⟨f, hf, hz, hb, rfl⟩
    exact schwarz_derivative_bound hf hz hb

def centralValueExtremal : ℝ :=
  sSup {r : ℝ | ∃ a : Disk, ‖a‖ ≤ 1 ∧ ‖diskFun a 0‖ = r}

def centralJetExtremal : ℝ :=
  sSup {r : ℝ | ∃ a : Disk,
    ‖a‖ ≤ 1 ∧ diskFun a 0 = 0 ∧ ‖deriv (diskFun a) 0‖ = r}

def centralCaratheodory : ℝ :=
  sSup {r : ℝ | ∃ f : ℂ → ℂ,
    DifferentiableOn ℂ f (ball 0 1) ∧ f 0 = 0 ∧
    (∀ z ∈ ball (0 : ℂ) 1, ‖f z‖ ≤ 1) ∧ ‖deriv f 0‖ = r}

/-- Exact comparison using the value/jet extremal definitions, with all suprema attained. -/
theorem central_bergman_caratheodory_ratio :
    (centralJetExtremal / centralValueExtremal) / centralCaratheodory = Real.sqrt 2 := by
  rw [centralValueExtremal, central_value_isGreatest.csSup_eq,
    centralJetExtremal, central_jet_isGreatest.csSup_eq,
    centralCaratheodory, central_caratheodory_isGreatest.csSup_eq, div_one, div_one]

#print axioms central_value_isGreatest
#print axioms central_jet_isGreatest
#print axioms central_caratheodory_isGreatest
#print axioms central_bergman_caratheodory_ratio
end
end GaloisForLFunctions.HilbertMetric.Bergman
