import GaloisForLFunctions.RHTower.SuzukiCompactifiedPhaseProfile
import GaloisForLFunctions.HTGeometry.ComplexWeakConvergenceBridge

/-!
# The Donoghue kernel is continuous and uniformly bounded above the real axis

The endpoint residual of a cofinal Suzuki limit is read off by testing the compactified spectral
probabilities against the Donoghue kernel

`K_z (t) = z + (z² + 1) / (t - z)`.

Two analytic facts make that test legitimate.  For each spectral parameter above the real axis the
kernel is continuous in the spectral variable, because the denominator never vanishes there; and
its size is controlled by the imaginary height alone, so it is uniformly bounded when the spectral
parameter ranges over a set of bounded modulus and bounded-below height.

Together with the two projective endpoint limits, already formalized, these give exactly the
hypotheses under which weak convergence of the compactified probabilities transfers to the
Herglotz transforms, and under which the pointwise transfer upgrades to a locally uniform one.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology

/-- Above the real axis the Donoghue denominator never vanishes. -/
theorem suzukiDonoghueDenom_ne_zero {z : ℂ} (hz : 0 < z.im) (t : ℝ) : ((t : ℂ) - z) ≠ 0 := by
  intro h
  have him : ((t : ℂ) - z).im = -z.im := by simp
  rw [h] at him
  simp at him
  linarith

/-- The denominator is at least the imaginary height. -/
theorem le_norm_suzukiDonoghueDenom {z : ℂ} (t : ℝ) : z.im ≤ ‖(t : ℂ) - z‖ := by
  refine le_trans (le_abs_self _) ?_
  have habs : |((t : ℂ) - z).im| ≤ ‖(t : ℂ) - z‖ := Complex.abs_im_le_norm _
  have hval : ((t : ℂ) - z).im = -z.im := by simp
  rw [hval, abs_neg] at habs
  exact habs

/-- **Continuity in the spectral variable.** -/
theorem continuous_suzukiDonoghueKernel {z : ℂ} (hz : 0 < z.im) :
    Continuous (fun t : ℝ => suzukiDonoghueKernel t z) := by
  unfold suzukiDonoghueKernel
  refine continuous_const.add (Continuous.div continuous_const ?_ ?_)
  · fun_prop
  · exact fun t => suzukiDonoghueDenom_ne_zero hz t

/-- **Size control by the imaginary height alone.** -/
theorem norm_suzukiDonoghueKernel_le {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    ‖suzukiDonoghueKernel t z‖ ≤ ‖z‖ + (‖z‖ ^ (2 : ℕ) + 1) / z.im := by
  have hden : z.im ≤ ‖(t : ℂ) - z‖ := le_norm_suzukiDonoghueDenom t
  have hdenpos : 0 < ‖(t : ℂ) - z‖ := lt_of_lt_of_le hz hden
  have hnum : ‖z ^ (2 : ℕ) + 1‖ ≤ ‖z‖ ^ (2 : ℕ) + 1 := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_pow, norm_one]
  have hfrac : ‖(z ^ (2 : ℕ) + 1) / ((t : ℂ) - z)‖ ≤ (‖z‖ ^ (2 : ℕ) + 1) / z.im := by
    rw [norm_div, div_le_div_iff₀ hdenpos hz]
    nlinarith [norm_nonneg (z ^ (2 : ℕ) + 1), norm_nonneg z, hz.le, hdenpos.le]
  refine le_trans (norm_add_le _ _) ?_
  linarith

/-- **Uniform bound on a compact spectral window.**  When the parameter has modulus at most `R` and
imaginary height at least `η`, the kernel is bounded by one constant independent of the spectral
variable. -/
theorem norm_suzukiDonoghueKernel_le_of_window {z : ℂ} {eta R : ℝ} (heta : 0 < eta)
    (him : eta ≤ z.im) (hR : ‖z‖ ≤ R) (t : ℝ) :
    ‖suzukiDonoghueKernel t z‖ ≤ R + (R ^ (2 : ℕ) + 1) / eta := by
  have hz : 0 < z.im := lt_of_lt_of_le heta him
  refine le_trans (norm_suzukiDonoghueKernel_le hz t) ?_
  have hnn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have h1 : ‖z‖ ^ (2 : ℕ) + 1 ≤ R ^ (2 : ℕ) + 1 := by nlinarith
  have h2 : (‖z‖ ^ (2 : ℕ) + 1) / z.im ≤ (R ^ (2 : ℕ) + 1) / eta := by
    rw [div_le_div_iff₀ hz heta]
    nlinarith [hnn, heta.le, hz.le]
  linarith

/-! ## The kernel in the compactified coordinate -/

/-- The Donoghue kernel read in the compactified projective coordinate, where the physical point of
a compactified phase `t` is `tan t`. -/
noncomputable def projectiveDonoghueKernel (t : ℝ) (z : ℂ) : ℂ :=
  suzukiDonoghueKernel (Real.tan t) z

/-- **Continuity at the right projective endpoint.**  Approaching `π/2` the physical point escapes
to `+∞` and the kernel tends to its linear Nevanlinna value. -/
theorem tendsto_projectiveDonoghueKernel_right (z : ℂ) :
    Filter.Tendsto (fun t : ℝ => projectiveDonoghueKernel t z)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds z) :=
  (tendsto_suzukiDonoghueKernel_atTop z).comp Real.tendsto_tan_pi_div_two

/-- **Continuity at the left projective endpoint.**  Approaching `-π/2` the physical point escapes
to `-∞` and the kernel tends to the same linear Nevanlinna value. -/
theorem tendsto_projectiveDonoghueKernel_left (z : ℂ) :
    Filter.Tendsto (fun t : ℝ => projectiveDonoghueKernel t z)
      (nhdsWithin (-(Real.pi / 2)) (Set.Ioi (-(Real.pi / 2)))) (nhds z) :=
  (tendsto_suzukiDonoghueKernel_atBot z).comp Real.tendsto_tan_neg_pi_div_two

/-- **Continuity in the projective interior.** -/
theorem continuousOn_projectiveDonoghueKernel {z : ℂ} (hz : 0 < z.im) :
    ContinuousOn (fun t : ℝ => projectiveDonoghueKernel t z)
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  have htan : ContinuousOn Real.tan (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    refine Real.continuousOn_tan.mono ?_
    intro t ht
    have hcos := Real.cos_pos_of_mem_Ioo ht
    simpa using hcos.ne'
  exact (continuous_suzukiDonoghueKernel hz).comp_continuousOn htan

/-- The compactified kernel is bounded by the same window constant, uniformly in the compactified
coordinate. -/
theorem norm_projectiveDonoghueKernel_le_of_window {z : ℂ} {eta R : ℝ} (heta : 0 < eta)
    (him : eta ≤ z.im) (hR : ‖z‖ ≤ R) (t : ℝ) :
    ‖projectiveDonoghueKernel t z‖ ≤ R + (R ^ (2 : ℕ) + 1) / eta :=
  norm_suzukiDonoghueKernel_le_of_window heta him hR _

/-! ## The continuous extension to the closed projective interval -/

open Set

/-- The compact projective interval of compactified phases. -/
def projectiveInterval : Set ℝ := Set.Icc (-(Real.pi / 2)) (Real.pi / 2)

/-- The Donoghue kernel extended to the closed projective interval by its common endpoint value. -/
noncomputable def extendedProjectiveKernel (t : ℝ) (z : ℂ) : ℂ :=
  if t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) then projectiveDonoghueKernel t z else z

theorem extendedProjectiveKernel_of_mem_Ioo {t : ℝ}
    (ht : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (z : ℂ) :
    extendedProjectiveKernel t z = projectiveDonoghueKernel t z := if_pos ht

theorem extendedProjectiveKernel_right (z : ℂ) :
    extendedProjectiveKernel (Real.pi / 2) z = z := by
  refine if_neg ?_
  intro h
  exact absurd h.2 (lt_irrefl _)

theorem extendedProjectiveKernel_left (z : ℂ) :
    extendedProjectiveKernel (-(Real.pi / 2)) z = z := by
  refine if_neg ?_
  intro h
  exact absurd h.1 (lt_irrefl _)

/-- **The extended kernel is continuous on the closed projective interval.**  On the interior it is
the kernel in the compactified coordinate; at each endpoint the physical point escapes to projective
infinity and the kernel tends to the common linear Nevanlinna value, which is the assigned value
there. -/
theorem continuousOn_extendedProjectiveKernel {z : ℂ} (hz : 0 < z.im) :
    ContinuousOn (fun t : ℝ => extendedProjectiveKernel t z) projectiveInterval := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hleft | hleft
  · -- left endpoint
    have hteq : t = -(Real.pi / 2) := hleft.symm
    subst hteq
    rw [ContinuousWithinAt, extendedProjectiveKernel_left z]
    have hsub : projectiveInterval ⊆ Set.Ioi (-(Real.pi / 2)) ∪ {-(Real.pi / 2)} := by
      intro s hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    refine Filter.Tendsto.mono_left ?_ (nhdsWithin_mono _ hsub)
    rw [nhdsWithin_union]
    refine Filter.Tendsto.sup ?_ ?_
    · refine (tendsto_projectiveDonoghueKernel_left z).congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (show -(Real.pi / 2) ∈ Set.Iio (Real.pi / 2) by
          simp only [Set.mem_Iio]; linarith))] with s hs hs2
      exact (extendedProjectiveKernel_of_mem_Ioo ⟨hs, hs2⟩ z).symm
    · rw [nhdsWithin_singleton]
      simpa [extendedProjectiveKernel_left z] using
        tendsto_pure_nhds (fun t : ℝ => extendedProjectiveKernel t z) (-(Real.pi / 2))
  · rcases eq_or_lt_of_le ht.2 with hright | hright
    · -- right endpoint
      subst hright
      rw [ContinuousWithinAt, extendedProjectiveKernel_right z]
      have hsub : projectiveInterval ⊆ Set.Iio (Real.pi / 2) ∪ {Real.pi / 2} := by
        intro s hs
        rcases eq_or_lt_of_le hs.2 with h | h
        · exact Or.inr h
        · exact Or.inl h
      refine Filter.Tendsto.mono_left ?_ (nhdsWithin_mono _ hsub)
      rw [nhdsWithin_union]
      refine Filter.Tendsto.sup ?_ ?_
      · refine (tendsto_projectiveDonoghueKernel_right z).congr' ?_
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds
            (show Real.pi / 2 ∈ Set.Ioi (-(Real.pi / 2)) by
              simp only [Set.mem_Ioi]; linarith))] with s hs hs2
        exact (extendedProjectiveKernel_of_mem_Ioo ⟨hs2, hs⟩ z).symm
      · rw [nhdsWithin_singleton]
        simpa [extendedProjectiveKernel_right z] using
          tendsto_pure_nhds (fun t : ℝ => extendedProjectiveKernel t z) (Real.pi / 2)
    · -- interior
      have hmem : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨hleft, hright⟩
      have hat : ContinuousAt (fun s : ℝ => projectiveDonoghueKernel s z) t :=
        (continuousOn_projectiveDonoghueKernel hz).continuousAt (isOpen_Ioo.mem_nhds hmem)
      refine (hat.congr ?_).continuousWithinAt
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
      exact (extendedProjectiveKernel_of_mem_Ioo hs z).symm

/-! ## The Herglotz transform of a compactified spectral probability -/

instance : CompactSpace ↥projectiveInterval := by
  rw [projectiveInterval]
  infer_instance

/-- The Donoghue kernel as a continuous function on the compact projective interval. -/
noncomputable def projectiveKernelMap {z : ℂ} (hz : 0 < z.im) :
    C(↥projectiveInterval, ℂ) :=
  ⟨fun t => extendedProjectiveKernel (t : ℝ) z,
    (continuousOn_extendedProjectiveKernel hz).restrict⟩

/-- **`(17)`.**  Weak convergence of the compactified spectral probabilities transfers to their
Herglotz transforms.  The kernel is continuous on the compact projective interval, so the
compact-space weak-convergence test applies to it directly. -/
theorem tendsto_integral_extendedProjectiveKernel
    {ι : Type*} {l : Filter ι} {nu : ι → MeasureTheory.ProbabilityMeasure ↥projectiveInterval}
    {nu0 : MeasureTheory.ProbabilityMeasure ↥projectiveInterval}
    (h : Filter.Tendsto nu l (nhds nu0)) {z : ℂ} (hz : 0 < z.im) :
    Filter.Tendsto
      (fun i => ∫ t, extendedProjectiveKernel (t : ℝ) z
        ∂(nu i : MeasureTheory.Measure ↥projectiveInterval)) l
      (nhds (∫ t, extendedProjectiveKernel (t : ℝ) z
        ∂(nu0 : MeasureTheory.Measure ↥projectiveInterval))) :=
  GaloisForLFunctions.HTGeometry.tendsto_integral_complex_of_compact h (projectiveKernelMap hz)

end GaloisForLFunctions.RHTower
