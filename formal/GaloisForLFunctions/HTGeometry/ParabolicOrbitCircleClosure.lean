import GaloisForLFunctions.HTGeometry.ParabolicOrbitRigidity
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Compactification.OnePoint.Sphere

/-!
# The completed parabolic orbit is a one-point compactification

In the compact-open topology of holomorphic functions on the disc the parabolic orbit of the outer
carrier is a continuous injective image of the real line whose only extra limit point is the
constant `exp (-N)`.  Adding that point to the parameter line gives a continuous injection of the
one-point compactification, hence a closed embedding, so the orbit closure is exactly the orbit
together with the constant, homeomorphic to `OnePoint ℝ`.

Continuity in the parameter comes from analyticity of the Cauchy transform off the real axis;
continuity at the added point is the locally uniform collapse; injectivity is the rigidity theorem,
and the constant is not an orbit point because the orbit modulus stays strictly above `exp (-N)`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Filter Set

open scoped Topology

noncomputable section

/-- The open unit disc. -/
def openDisc : Set ℂ := Metric.ball (0 : ℂ) 1

theorem mem_openDisc_iff {w : ℂ} : w ∈ openDisc ↔ ‖w‖ < 1 := by
  rw [openDisc, Metric.mem_ball, dist_zero_right]

theorem isOpen_openDisc : IsOpen openDisc := Metric.isOpen_ball

instance instLocallyCompactOpenDisc : LocallyCompactSpace ↥openDisc :=
  isOpen_openDisc.locallyCompactSpace

theorem isOpen_upperHalf : IsOpen {z : ℂ | 0 < z.im} :=
  isOpen_lt continuous_const Complex.continuous_im

/-- The Cauchy transform is continuous above the real axis. -/
theorem continuousOn_cauchyTransform_upper (ν : Measure ℝ) [IsFiniteMeasure ν] :
    ContinuousOn (cauchyTransform ν) {z : ℂ | 0 < z.im} :=
  (analyticOnNhd_cauchyTransform ν isOpen_upperHalf fun _ hz => ne_of_gt hz).continuousOn

/-- The Cauchy transform of a finite positive measure has nonnegative imaginary part above the
real axis. -/
theorem im_cauchyTransform_nonneg (ν : Measure ℝ) [IsFiniteMeasure ν] {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (cauchyTransform ν z).im := by
  rcases eq_or_ne ν 0 with rfl | hν
  · rw [cauchyTransform, integral_zero_measure]
    simp
  · exact (im_cauchyTransform_pos_of_ne_zero ν hν hz).le

theorem continuousOn_cayleyToDisc : ContinuousOn cayleyToDisc {z : ℂ | z + Complex.I ≠ 0} := by
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => hz

/-- The orbit is jointly continuous in the translation and the disc point. -/
theorem continuous_uncurry_parabolicOuterOrbit (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) :
    Continuous fun p : ℝ × ↥openDisc => parabolicOuterOrbit ν N p.1 p.2.1 := by
  have hcayley : Continuous fun p : ℝ × ↥openDisc => cayleyToUpper p.2.1 := by
    refine continuousOn_cayleyToUpper.comp_continuous (by fun_prop) fun p => ?_
    exact mem_openDisc_iff.mp p.2.2
  have hup : Continuous fun p : ℝ × ↥openDisc => cayleyToUpper p.2.1 + (p.1 : ℂ) :=
    hcayley.add (Complex.continuous_ofReal.comp continuous_fst)
  have hupim : ∀ p : ℝ × ↥openDisc,
      (cayleyToUpper p.2.1 + (p.1 : ℂ)) ∈ {z : ℂ | 0 < z.im} := by
    intro p
    exact im_cayleyToUpper_add_pos (mem_openDisc_iff.mp p.2.2)
  have hm : Continuous fun p : ℝ × ↥openDisc =>
      cauchyTransform ν (cayleyToUpper p.2.1 + (p.1 : ℂ)) :=
    (continuousOn_cauchyTransform_upper ν).comp_continuous hup hupim
  have hmne : ∀ p : ℝ × ↥openDisc,
      cauchyTransform ν (cayleyToUpper p.2.1 + (p.1 : ℂ)) ∈ {z : ℂ | z + Complex.I ≠ 0} := by
    intro p
    have hnn : 0 ≤ (cauchyTransform ν (cayleyToUpper p.2.1 + (p.1 : ℂ))).im :=
      im_cauchyTransform_nonneg ν (hupim p)
    intro hzero
    have him : (cauchyTransform ν (cayleyToUpper p.2.1 + (p.1 : ℂ)) + Complex.I).im
        = (cauchyTransform ν (cayleyToUpper p.2.1 + (p.1 : ℂ))).im + 1 := by simp
    rw [hzero] at him
    simp only [Complex.zero_im] at him
    linarith
  have hquot : Continuous fun p : ℝ × ↥openDisc =>
      cayleyToDisc (cauchyTransform ν (cayleyToUpper p.2.1 + (p.1 : ℂ))) :=
    continuousOn_cayleyToDisc.comp_continuous hm hmne
  have hfinal : Continuous fun p : ℝ × ↥openDisc =>
      Complex.exp ((N : ℂ) * cayleyToDisc
        (cauchyTransform ν (cayleyToUpper p.2.1 + (p.1 : ℂ)))) :=
    Complex.continuous_exp.comp (continuous_const.mul hquot)
  exact hfinal

theorem continuous_parabolicOuterOrbit_disc (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) (t : ℝ) :
    Continuous fun w : ↥openDisc => parabolicOuterOrbit ν N t w.1 := by
  have hpair : Continuous fun w : ↥openDisc => ((t, w) : ℝ × ↥openDisc) :=
    continuous_const.prodMk continuous_id
  have h := (continuous_uncurry_parabolicOuterOrbit ν N).comp hpair
  simpa [Function.comp_def] using h

/-- The orbit point as a continuous function on the disc. -/
def discOrbit (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) (t : ℝ) : C(↥openDisc, ℂ) :=
  ⟨fun w => parabolicOuterOrbit ν N t w.1, continuous_parabolicOuterOrbit_disc ν N t⟩

@[simp]
theorem discOrbit_apply (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) (t : ℝ) (w : ↥openDisc) :
    discOrbit ν N t w = parabolicOuterOrbit ν N t w.1 := rfl

theorem continuous_discOrbit (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) :
    Continuous (discOrbit ν N) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_uncurry_parabolicOuterOrbit ν N)

/-- **Compact-open convergence of the orbit.**  The orbit converges to the constant `exp (-N)` in
the compact-open topology as the translation escapes. -/
theorem tendsto_discOrbit (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) :
    Tendsto (discOrbit ν N) (cocompact ℝ)
      (𝓝 (ContinuousMap.const ↥openDisc (Complex.exp (-(N : ℂ))))) := by
  refine ContinuousMap.tendsto_of_tendstoLocallyUniformly ?_
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  have himage : IsCompact (Subtype.val '' K) := hK.image continuous_subtype_val
  have hdisc : ∀ w ∈ Subtype.val '' K, ‖w‖ < 1 := by
    rintro _ ⟨u, -, rfl⟩
    exact mem_openDisc_iff.mp u.2
  have huniform := tendstoUniformlyOn_parabolicOuterOrbit ν N himage hdisc
  have hcomp := huniform.comp (Subtype.val : ↥openDisc → ℂ)
  refine hcomp.mono ?_
  intro u hu
  exact ⟨u, hu, rfl⟩

/-- The extended orbit map on the one-point compactification of the parameter line. -/
def orbitOnePoint (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) :
    OnePoint ℝ → C(↥openDisc, ℂ) :=
  fun x => x.elim (ContinuousMap.const ↥openDisc (Complex.exp (-(N : ℂ)))) (discOrbit ν N)

@[simp]
theorem orbitOnePoint_coe (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) (t : ℝ) :
    orbitOnePoint ν N (t : OnePoint ℝ) = discOrbit ν N t := rfl

@[simp]
theorem orbitOnePoint_infty (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) :
    orbitOnePoint ν N (OnePoint.infty) =
      ContinuousMap.const ↥openDisc (Complex.exp (-(N : ℂ))) := rfl

theorem continuous_orbitOnePoint (ν : Measure ℝ) [IsFiniteMeasure ν] (N : ℕ) :
    Continuous (orbitOnePoint ν N) := by
  rw [continuous_iff_continuousAt]
  intro x
  induction x using OnePoint.rec with
  | infty =>
      rw [OnePoint.continuousAt_infty']
      rw [orbitOnePoint_infty, coclosedCompact_eq_cocompact]
      exact tendsto_discOrbit ν N
  | coe t =>
      rw [OnePoint.continuousAt_coe]
      exact (continuous_discOrbit ν N).continuousAt

/-- The limiting constant is never an orbit point: the orbit modulus stays strictly above it. -/
theorem discOrbit_ne_const (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) {N : ℕ} (hN : 0 < N)
    (t : ℝ) : discOrbit ν N t ≠ ContinuousMap.const ↥openDisc (Complex.exp (-(N : ℂ))) := by
  intro hcon
  have hzero : (0 : ℂ) ∈ openDisc := by
    rw [mem_openDisc_iff]
    simp
  have hval := congrArg (fun f => f ⟨(0 : ℂ), hzero⟩) hcon
  simp only [discOrbit_apply, ContinuousMap.const_apply] at hval
  have hbounds := norm_parabolicOuterOrbit_bounds ν hν N t (mem_openDisc_iff.mp hzero) hN
  rw [hval] at hbounds
  have hnorm : ‖Complex.exp (-(N : ℂ))‖ = Real.exp (-(N : ℝ)) := by
    rw [Complex.norm_exp]
    simp
  rw [hnorm] at hbounds
  exact absurd hbounds.1 (lt_irrefl _)

theorem injective_orbitOnePoint (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) {N : ℕ}
    (hN : 0 < N) : Function.Injective (orbitOnePoint ν N) := by
  intro x y hxy
  induction x using OnePoint.rec with
  | infty =>
      induction y using OnePoint.rec with
      | infty => rfl
      | coe t =>
          exact absurd hxy.symm (discOrbit_ne_const ν hν hN t)
  | coe s =>
      induction y using OnePoint.rec with
      | infty => exact absurd hxy (discOrbit_ne_const ν hν hN s)
      | coe t =>
          have heq : ∀ w : ℂ, ‖w‖ < 1 →
              parabolicOuterOrbit ν N s w = parabolicOuterOrbit ν N t w := by
            intro w hw
            have := congrArg (fun f => f ⟨w, mem_openDisc_iff.mpr hw⟩) hxy
            simpa using this
          rw [parabolicOuterOrbit_injective ν hν hN heq]

/-- **The completed orbit is a one-point compactification.**  The extended orbit map is a closed
embedding of `OnePoint ℝ`. -/
theorem isClosedEmbedding_orbitOnePoint (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) {N : ℕ}
    (hN : 0 < N) : Topology.IsClosedEmbedding (orbitOnePoint ν N) :=
  (continuous_orbitOnePoint ν N).isClosedEmbedding (injective_orbitOnePoint ν hν hN)

/-- **The orbit closure adds exactly one point.** -/
theorem closure_range_discOrbit (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0) {N : ℕ}
    (hN : 0 < N) :
    closure (Set.range (discOrbit ν N))
      = Set.range (discOrbit ν N) ∪ {ContinuousMap.const ↥openDisc (Complex.exp (-(N : ℂ)))} := by
  have hrange : Set.range (orbitOnePoint ν N)
      = Set.range (discOrbit ν N) ∪ {ContinuousMap.const ↥openDisc (Complex.exp (-(N : ℂ)))} := by
    ext f
    constructor
    · rintro ⟨x, rfl⟩
      induction x using OnePoint.rec with
      | infty => exact Or.inr rfl
      | coe t => exact Or.inl ⟨t, rfl⟩
    · rintro (⟨t, rfl⟩ | hf)
      · exact ⟨(t : OnePoint ℝ), rfl⟩
      · rw [mem_singleton_iff] at hf
        exact ⟨OnePoint.infty, hf.symm⟩
  have hclosed : IsClosed (Set.range (orbitOnePoint ν N)) :=
    (isClosedEmbedding_orbitOnePoint ν hν hN).isClosed_range
  refine Subset.antisymm ?_ ?_
  · rw [← hrange]
    refine closure_minimal ?_ hclosed
    rintro _ ⟨t, rfl⟩
    exact ⟨(t : OnePoint ℝ), rfl⟩
  · refine union_subset subset_closure ?_
    intro f hf
    rw [mem_singleton_iff] at hf
    rw [hf]
    refine mem_closure_of_tendsto (tendsto_discOrbit ν N) ?_
    exact Filter.Eventually.of_forall fun t => ⟨t, rfl⟩

/-- **The completed orbit is homeomorphic to the one-point compactification of the line.** -/
theorem exists_homeomorph_closure_range_discOrbit (ν : Measure ℝ) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    {N : ℕ} (hN : 0 < N) :
    ∃ e : OnePoint ℝ ≃ₜ ↥(closure (Set.range (discOrbit ν N))),
      ∀ t : ℝ, (e (t : OnePoint ℝ) : C(↥openDisc, ℂ)) = discOrbit ν N t := by
  have hemb := isClosedEmbedding_orbitOnePoint ν hν hN
  have hrange : Set.range (orbitOnePoint ν N) = closure (Set.range (discOrbit ν N)) := by
    rw [closure_range_discOrbit ν hν hN]
    ext f
    constructor
    · rintro ⟨x, rfl⟩
      induction x using OnePoint.rec with
      | infty => exact Or.inr rfl
      | coe t => exact Or.inl ⟨t, rfl⟩
    · rintro (⟨t, rfl⟩ | hf)
      · exact ⟨(t : OnePoint ℝ), rfl⟩
      · rw [mem_singleton_iff] at hf
        exact ⟨OnePoint.infty, hf.symm⟩
  refine ⟨(hemb.isEmbedding.toHomeomorph).trans (Homeomorph.setCongr hrange), fun t => ?_⟩
  rfl

/-- **The completed orbit is a topological circle.**  Combining the one-point description with the
standard homeomorphism between the one-point compactification of the line and the circle. -/
theorem exists_homeomorph_sphere_closure_range_discOrbit (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ν ≠ 0) {N : ℕ} (hN : 0 < N) :
    Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1
      ≃ₜ ↥(closure (Set.range (discOrbit ν N)))) := by
  obtain ⟨e, -⟩ := exists_homeomorph_closure_range_discOrbit ν hν hN
  have hcircle : OnePoint ℝ ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 :=
    onePointEquivSphereOfFinrankEq (V := ℝ) (ι := Fin 2) (by simp)
  exact ⟨hcircle.symm.trans e⟩

end

end GaloisForLFunctions.HTGeometry
