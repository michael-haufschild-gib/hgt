import GaloisForLFunctions.HTGeometry.FiniteRegularityCurveBounds
import GaloisForLFunctions.HTGeometry.KleinGordonSpacetimeProbe
import GaloisForLFunctions.HTGeometry.KleinGordonRegularProbes

/-!
# Clock probes for a spacetime potential of finite regularity

The construction of clock probes by Fourier synthesis consumes the potential only through a weighted
decay bound on its spatial Fourier density, and that bound needs finitely many derivatives. Cutting
a `C^{2j+1}` potential off in space and time around an event produces a curve of compactly supported
`C^{2j+1}` functions whose decay functional of order `j` is bounded uniformly in time and Lipschitz
in time, hence an admissible family whose potential is the given one near the event.

So the smoothness hypothesis of the earlier theorem is replaced by an explicit finite order: in
dimension `1 + d` a potential of class `C^{2d+5}` already carries clock probes at every event.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Metric

open scoped FourierTransform ContDiff

section Cut

variable {d : ℕ} {P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ} {t₀ : ℝ}
  {x₀ : EuclideanSpace ℝ (Fin d)}

theorem contDiff_kgSpacetimeCut_finite {k : ℕ}
    (hP : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) P) :
    ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) (kgSpacetimeCut P t₀ x₀) := by
  have htime : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞)
      fun p : ℝ × EuclideanSpace ℝ (Fin d) => (kgTimeCutoff t₀) p.1 :=
    ((kgTimeCutoff t₀).contDiff.of_le (by exact_mod_cast le_top)).comp contDiff_fst
  have hspace : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞)
      fun p : ℝ × EuclideanSpace ℝ (Fin d) => (kgCutoff x₀) p.2 :=
    ((kgCutoff x₀).contDiff.of_le (by exact_mod_cast le_top)).comp contDiff_snd
  refine Complex.ofRealCLM.contDiff.of_le (by exact_mod_cast le_top) |>.comp ?_
  exact htime.mul (hspace.mul (hP.add contDiff_const))

theorem hasCompactSupport_kgSpacetimeCut :
    HasCompactSupport (kgSpacetimeCut P t₀ x₀) := by
  refine HasCompactSupport.intro
    ((isCompact_closedBall t₀ 2).prod (isCompact_closedBall x₀ 2)) fun p hp => ?_
  exact kgSpacetimeCut_zero_of_notMem hp

/-- Near the event the cut-off is invisible. -/
theorem kgSpacetimeCut_re {t : ℝ} {x : EuclideanSpace ℝ (Fin d)} (ht : t ∈ ball t₀ 1)
    (hx : x ∈ ball x₀ 1) : (kgSpacetimeCut P t₀ x₀ (t, x)).re - 1 = P (t, x) := by
  have htime : kgTimeCutoff t₀ t = 1 :=
    (kgTimeCutoff t₀).one_of_mem_closedBall (ball_subset_closedBall ht)
  have hspace : kgCutoff x₀ x = 1 :=
    (kgCutoff x₀).one_of_mem_closedBall (ball_subset_closedBall hx)
  rw [kgSpacetimeCut_apply, htime, hspace, Complex.ofReal_re]
  ring

theorem kgSpacetimeCut_conj (p : ℝ × EuclideanSpace ℝ (Fin d)) :
    (starRingEnd ℂ) (kgSpacetimeCut P t₀ x₀ p) = kgSpacetimeCut P t₀ x₀ p := by
  rw [kgSpacetimeCut_apply, Complex.conj_ofReal]

end Cut

/-! ## The realization -/

section Realization

variable {d N j m : ℕ}

/-- **Every spacetime potential of class `C^{2j+1}` is locally the potential of an admissible
family.** No smoothness is used: the cut-off potential is a curve of compactly supported functions
of finite regularity, and its decay functional of order `j` is what the family constructor asks
for. -/
theorem exists_locally_kgChartPotential_of_contDiff_spacetime
    (hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < m) (hj : N + m ≤ 2 * j)
    {P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hP : ContDiff ℝ ((2 * j + 1 : ℕ) : WithTop ℕ∞) P) :
    ∀ y₀ : Fin (d + 1) → ℝ, ∃ (B : WienerFamily (EuclideanSpace ℝ (Fin d)) N)
      (W : Set (Fin (d + 1) → ℝ)), IsRealFamily B ∧ IsOpen W ∧ y₀ ∈ W ∧
        Set.EqOn (fun y : Fin (d + 1) → ℝ => P (y 0, kgSpatial d y)) (kgChartPotential B) W := by
  intro y₀
  set t₀ : ℝ := y₀ 0 with ht₀
  set x₀ : EuclideanSpace ℝ (Fin d) := kgSpatial d y₀ with hx₀
  set H : ℝ × EuclideanSpace ℝ (Fin d) → ℂ := kgSpacetimeCut P t₀ x₀ with hH
  set K : Set (EuclideanSpace ℝ (Fin d)) := closedBall x₀ 2 with hK
  have hHcd : ContDiff ℝ ((2 * j + 1 : ℕ) : WithTop ℕ∞) H := contDiff_kgSpacetimeCut_finite hP
  have hHsupp : HasCompactSupport H := hasCompactSupport_kgSpacetimeCut
  have hKcompact : IsCompact K := isCompact_closedBall x₀ 2
  have hKmeas : MeasurableSet K := measurableSet_closedBall
  have hzero : ∀ (t : ℝ) (x : EuclideanSpace ℝ (Fin d)), x ∉ K → H (t, x) = 0 :=
    fun t x hx => kgSpacetimeCut_zero_of_space (p := (t, x)) hx
  obtain ⟨M, L, hL0, hM, hL⟩ :=
    exists_contDiffDecay_bounds (j := j) hHcd hHsupp hKcompact hKmeas hzero
  have hle : ((2 * j : ℕ) : WithTop ℕ∞) ≤ ((2 * j + 1 : ℕ) : WithTop ℕ∞) := by
    exact_mod_cast Nat.le_succ _
  have hcd : ∀ t : ℝ, ContDiff ℝ ((2 * j : ℕ) : WithTop ℕ∞) fun x : EuclideanSpace ℝ (Fin d) =>
      H (t, x) := by
    intro t
    have hmap : ContDiff ℝ ((2 * j : ℕ) : WithTop ℕ∞)
        fun x : EuclideanSpace ℝ (Fin d) => ((t, x) : ℝ × EuclideanSpace ℝ (Fin d)) := by fun_prop
    exact (hHcd.of_le hle).comp hmap
  have hsupp : ∀ t : ℝ, HasCompactSupport fun x : EuclideanSpace ℝ (Fin d) => H (t, x) :=
    fun t => HasCompactSupport.intro hKcompact fun x hx => hzero t x hx
  have hmj : m ≤ 2 * j := le_trans (Nat.le_add_left m N) hj
  refine ⟨WienerFamily.ofContDiffCurve (N := N) hdim hj hcd hsupp hM hL0 hL,
    {y : Fin (d + 1) → ℝ | y 0 ∈ ball t₀ 1} ∩ (kgSpatial d) ⁻¹' (ball x₀ 1), ?_,
    (isOpen_ball.preimage (continuous_apply 0)).inter
      (isOpen_ball.preimage (continuous_kgSpatial d)), ⟨mem_ball_self one_pos,
        mem_ball_self one_pos⟩, ?_⟩
  · intro t η
    show 𝓕 (fun x : EuclideanSpace ℝ (Fin d) => H (t, x)) (-η)
      = (starRingEnd ℂ) (𝓕 (fun x : EuclideanSpace ℝ (Fin d) => H (t, x)) η)
    exact fourier_neg_eq_conj (fun x => kgSpacetimeCut_conj (p := (t, x))) η
  · intro z hz
    have htime : z 0 ∈ ball t₀ 1 := hz.1
    have hspace : kgSpatial d z ∈ ball x₀ 1 := hz.2
    show P (z 0, kgSpatial d z) = kgChartPotential _ z
    have hpot : kgPotential (WienerFamily.ofContDiffCurve (N := N) hdim hj hcd hsupp hM hL0
        hL |>.density (z 0)) (kgSpatial d z) = H (z 0, kgSpatial d z) :=
      kgPotential_fourier_of_contDiff hdim hmj (hcd (z 0)) (hsupp (z 0)) (hM (z 0))
        (fun η => rfl) (kgSpatial d z)
    rw [kgChartPotential, hpot]
    exact (kgSpacetimeCut_re htime hspace).symm

/-- **Clock probes for every spacetime potential of class `C^{2j+1}`**, in every dimension, with no
decay, smallness or time-independence hypothesis. -/
theorem regularOpenProbes_of_contDiff_spacetime
    (hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < N)
    (hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < m) (hj : N + m ≤ 2 * j)
    {P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hP : ContDiff ℝ ((2 * j + 1 : ℕ) : WithTop ℕ∞) P) :
    RegularOpenProbes (kgWaveOp d) (fun y : Fin (d + 1) → ℝ => P (y 0, kgSpatial d y)) :=
  regularOpenProbes_of_locally_kgChartPotential (N := N) hN
    (exists_locally_kgChartPotential_of_contDiff_spacetime hdim hj hP)

/-- **The explicit finite order.** In dimension `1 + d` a potential of class `C^{2d+5}` carries
regular clock probes at every event. -/
theorem regularOpenProbes_of_contDiff_spacetime_explicit
    {P : ℝ × EuclideanSpace ℝ (Fin d) → ℝ}
    (hP : ContDiff ℝ ((2 * d + 5 : ℕ) : WithTop ℕ∞) P) :
    RegularOpenProbes (kgWaveOp d) (fun y : Fin (d + 1) → ℝ => P (y 0, kgSpatial d y)) := by
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d := finrank_euclideanSpace_fin
  have hN : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) + 2 < (d + 3 : ℕ) := by
    rw [hrank]
    push_cast
    linarith
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) : ℝ) < (d + 1 : ℕ) := by
    rw [hrank]
    push_cast
    linarith
  have hj : (d + 3) + (d + 1) ≤ 2 * (d + 2) := by omega
  have hord : 2 * (d + 2) + 1 = 2 * d + 5 := by omega
  refine regularOpenProbes_of_contDiff_spacetime (N := d + 3) (m := d + 1) (j := d + 2)
    hN hdim hj ?_
  rw [hord]
  exact hP

end Realization

end GaloisForLFunctions.HTGeometry
