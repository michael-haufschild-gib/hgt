import GaloisForLFunctions.RHTower.SuzukiAnchoredEulerWronskian
import GaloisForLFunctions.RHTower.SuzukiDonoghueKernelUniformBound

/-!
# Projective Euler-defect convergence for Suzuki Donoghue measures

The compactified Donoghue transform has a nonzero common endpoint value,
which is exactly the linear Nevanlinna escape mode.  The Euler defect replaces
its kernel by

`((t : ℂ) * (z^(2 : ℕ) - 1) + 2z) / ((t : ℂ) - z)^(2 : ℕ)`.

This kernel vanishes at both projective endpoints.  It therefore extends by
zero to the compact projective interval and weak convergence of compactified
spectral probabilities transfers directly to the Euler-defect transforms.

This is a convergence theorem only: it does not identify the limiting
Euler-defect transform with the exterior Carleman quotient.  That
source-identification remains the RH-bearing Suzuki weld.
-/

namespace GaloisForLFunctions.RHTower

open Filter Topology Set

noncomputable section

/-- Euler-defect kernel in the arctangent compactification coordinate. -/
def projectiveDonoghueEulerKernel (t : ℝ) (z : ℂ) : ℂ :=
  suzukiDonoghueEulerKernel (Real.tan t) z

/-- Endpoint-zero extension of the Euler-defect kernel to the projective compactification. -/
def extendedProjectiveEulerKernel (t : ℝ) (z : ℂ) : ℂ :=
  if t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) then
    projectiveDonoghueEulerKernel t z
  else 0

/-- The Euler-defect kernel tends to zero at the right projective endpoint. -/
theorem tendsto_projectiveDonoghueEulerKernel_right (z : ℂ) (hz : z.im ≠ 0) :
    Tendsto (fun t : ℝ => projectiveDonoghueEulerKernel t z)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
  (tendsto_suzukiDonoghueEulerKernel_atTop z hz).comp Real.tendsto_tan_pi_div_two

/-- The Euler-defect kernel tends to zero at the left projective endpoint. -/
theorem tendsto_projectiveDonoghueEulerKernel_left (z : ℂ) (hz : z.im ≠ 0) :
    Tendsto (fun t : ℝ => projectiveDonoghueEulerKernel t z)
      (nhdsWithin (-(Real.pi / 2)) (Set.Ioi (-(Real.pi / 2)))) (nhds 0) :=
  (tendsto_suzukiDonoghueEulerKernel_atBot z hz).comp Real.tendsto_tan_neg_pi_div_two

/-- The physical Euler-defect kernel is continuous away from the real spectral axis. -/
theorem continuous_suzukiDonoghueEulerKernel {z : ℂ} (hz : z.im ≠ 0) :
    Continuous (fun t : ℝ => suzukiDonoghueEulerKernel t z) := by
  unfold suzukiDonoghueEulerKernel
  refine Continuous.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro t hzero
    have hbase : ((t : ℂ) - z) ≠ 0 := by
      intro h
      have him := congrArg Complex.im h
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub] at him
      exact hz (neg_eq_zero.mp him)
    exact (pow_ne_zero 2 hbase) hzero

/-- The Euler-defect kernel is continuous in the projective interior. -/
theorem continuousOn_projectiveDonoghueEulerKernel {z : ℂ} (hz : 0 < z.im) :
    ContinuousOn (fun t : ℝ => projectiveDonoghueEulerKernel t z)
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  have htan : ContinuousOn Real.tan (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    refine Real.continuousOn_tan.mono ?_
    intro t ht
    have hcos := Real.cos_pos_of_mem_Ioo ht
    simpa using hcos.ne'
  exact (continuous_suzukiDonoghueEulerKernel (ne_of_gt hz)).comp_continuousOn htan

theorem extendedProjectiveEulerKernel_of_mem_Ioo {t : ℝ}
    (ht : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) (z : ℂ) :
    extendedProjectiveEulerKernel t z = projectiveDonoghueEulerKernel t z :=
  if_pos ht

theorem extendedProjectiveEulerKernel_right (z : ℂ) :
    extendedProjectiveEulerKernel (Real.pi / 2) z = 0 := by
  refine if_neg ?_
  intro h
  exact absurd h.2 (lt_irrefl _)

theorem extendedProjectiveEulerKernel_left (z : ℂ) :
    extendedProjectiveEulerKernel (-(Real.pi / 2)) z = 0 := by
  refine if_neg ?_
  intro h
  exact absurd h.1 (lt_irrefl _)

/-- The endpoint-zero Euler-defect kernel extends continuously to the compact projective interval. -/
theorem continuousOn_extendedProjectiveEulerKernel {z : ℂ} (hz : 0 < z.im) :
    ContinuousOn (fun t : ℝ => extendedProjectiveEulerKernel t z) projectiveInterval := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hleft | hleft
  · have hteq : t = -(Real.pi / 2) := hleft.symm
    subst hteq
    rw [ContinuousWithinAt, extendedProjectiveEulerKernel_left z]
    have hsub : projectiveInterval ⊆ Set.Ioi (-(Real.pi / 2)) ∪ {-(Real.pi / 2)} := by
      intro s hs
      rcases eq_or_lt_of_le hs.1 with h | h
      · exact Or.inr h.symm
      · exact Or.inl h
    refine Filter.Tendsto.mono_left ?_ (nhdsWithin_mono _ hsub)
    rw [nhdsWithin_union]
    refine Filter.Tendsto.sup ?_ ?_
    · refine (tendsto_projectiveDonoghueEulerKernel_left z (ne_of_gt hz)).congr' ?_
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (show -(Real.pi / 2) ∈ Set.Iio (Real.pi / 2) by
          simp only [Set.mem_Iio]; linarith))] with s hs hs2
      exact (extendedProjectiveEulerKernel_of_mem_Ioo ⟨hs, hs2⟩ z).symm
    · rw [nhdsWithin_singleton]
      simpa [extendedProjectiveEulerKernel_left z] using
        tendsto_pure_nhds (fun t : ℝ => extendedProjectiveEulerKernel t z) (-(Real.pi / 2))
  · rcases eq_or_lt_of_le ht.2 with hright | hright
    · subst hright
      rw [ContinuousWithinAt, extendedProjectiveEulerKernel_right z]
      have hsub : projectiveInterval ⊆ Set.Iio (Real.pi / 2) ∪ {Real.pi / 2} := by
        intro s hs
        rcases eq_or_lt_of_le hs.2 with h | h
        · exact Or.inr h
        · exact Or.inl h
      refine Filter.Tendsto.mono_left ?_ (nhdsWithin_mono _ hsub)
      rw [nhdsWithin_union]
      refine Filter.Tendsto.sup ?_ ?_
      · refine (tendsto_projectiveDonoghueEulerKernel_right z (ne_of_gt hz)).congr' ?_
        filter_upwards [self_mem_nhdsWithin,
          nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds
            (show Real.pi / 2 ∈ Set.Ioi (-(Real.pi / 2)) by
              simp only [Set.mem_Ioi]; linarith))] with s hs hs2
        exact (extendedProjectiveEulerKernel_of_mem_Ioo ⟨hs2, hs⟩ z).symm
      · rw [nhdsWithin_singleton]
        simpa [extendedProjectiveEulerKernel_right z] using
          tendsto_pure_nhds (fun t : ℝ => extendedProjectiveEulerKernel t z) (Real.pi / 2)
    · have hmem : t ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨hleft, hright⟩
      have hat : ContinuousAt (fun s : ℝ => projectiveDonoghueEulerKernel s z) t :=
        (continuousOn_projectiveDonoghueEulerKernel hz).continuousAt (isOpen_Ioo.mem_nhds hmem)
      refine (hat.congr ?_).continuousWithinAt
      filter_upwards [isOpen_Ioo.mem_nhds hmem] with s hs
      exact (extendedProjectiveEulerKernel_of_mem_Ioo hs z).symm

/-- The extended Euler-defect kernel as a continuous compact test function. -/
noncomputable def projectiveEulerKernelMap {z : ℂ} (hz : 0 < z.im) :
    C(↥projectiveInterval, ℂ) :=
  ⟨fun t => extendedProjectiveEulerKernel (t : ℝ) z,
    (continuousOn_extendedProjectiveEulerKernel hz).restrict⟩

/-- Weak convergence of compactified Donoghue probabilities transports their Euler-defect
transforms, with no endpoint linear-mass correction. -/
theorem tendsto_integral_extendedProjectiveEulerKernel
    {ι : Type*} {l : Filter ι} {nu : ι → MeasureTheory.ProbabilityMeasure ↥projectiveInterval}
    {nu0 : MeasureTheory.ProbabilityMeasure ↥projectiveInterval}
    (h : Filter.Tendsto nu l (nhds nu0)) {z : ℂ} (hz : 0 < z.im) :
    Filter.Tendsto
      (fun i => ∫ t, extendedProjectiveEulerKernel (t : ℝ) z
        ∂(nu i : MeasureTheory.Measure ↥projectiveInterval)) l
      (nhds (∫ t, extendedProjectiveEulerKernel (t : ℝ) z
        ∂(nu0 : MeasureTheory.Measure ↥projectiveInterval))) :=
  GaloisForLFunctions.HTGeometry.tendsto_integral_complex_of_compact h
    (projectiveEulerKernelMap hz)

end
end GaloisForLFunctions.RHTower
