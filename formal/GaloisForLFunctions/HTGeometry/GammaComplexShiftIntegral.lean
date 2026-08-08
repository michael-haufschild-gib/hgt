import GaloisForLFunctions.HTGeometry.GammaShiftExpIntegral

/-!
# Shifting Gamma by a complex amount

The real-shift law `Γ(z+λ) = Γ(z)·exp(∫₀^λ ψ(z+u) du)` is the differential equation `Γ′ = Γ·ψ`
integrated along a horizontal segment.  Nothing in that argument uses the direction of the segment:
integrating along the parametrised segment `u ↦ z + u·w`, `u ∈ [0,1]`, gives

`Γ(z+w) = Γ(z)·exp(∫₀¹ w·ψ(z+u w) du)`

whenever the whole segment stays in the right half plane.  Because the real part is affine in `u`,
the segment condition is just positivity at the two endpoints.

This is the form an oblique asymptotic needs: the base point runs along a ray of complex direction
and the shift is a complex multiple of that same direction.
-/

open Filter Set Topology Function intervalIntegral

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The real part along a parametrised segment is affine in the parameter. -/
theorem re_segment (z w : ℂ) (u : ℝ) : (z + (u : ℂ) * w).re = z.re + u * w.re := by
  simp

/-- The parameters keeping a segment in the right half plane form an open set. -/
theorem isOpen_segmentSet (z w : ℂ) : IsOpen {u : ℝ | 0 < (z + (u : ℂ) * w).re} := by
  have hcont : Continuous fun u : ℝ => (z + (u : ℂ) * w).re := by
    simp only [re_segment]
    fun_prop
  exact isOpen_lt continuous_const hcont

/-- Positivity at the two endpoints keeps the whole segment in the right half plane. -/
theorem segment_re_pos {z w : ℂ} (h0 : 0 < z.re) (h1 : 0 < (z + w).re) {u : ℝ}
    (hu : u ∈ Set.Icc (0 : ℝ) 1) : 0 < (z + (u : ℂ) * w).re := by
  rw [re_segment]
  have h1' : 0 < z.re + w.re := by simpa using h1
  rcases le_or_gt w.re 0 with hw | hw
  · nlinarith [hu.1, hu.2]
  · nlinarith [hu.1, hu.2]

/-- Along a complex shift that stays in the right half plane, the digamma is continuous. -/
theorem continuousOn_digamma_segment (z w : ℂ) :
    ContinuousOn (fun u : ℝ => w * Complex.digamma (z + (u : ℂ) * w))
      {u : ℝ | 0 < (z + (u : ℂ) * w).re} := by
  intro u hu
  have hre : 0 < (z + (u : ℂ) * w).re := hu
  have hmap : ContinuousAt (fun u : ℝ => z + (u : ℂ) * w) u := by fun_prop
  have hout : ContinuousAt Complex.digamma (z + (u : ℂ) * w) :=
    continuousOn_digamma_rePos.continuousAt (isOpen_rePos.mem_nhds hre)
  have hcomp : ContinuousAt (fun u : ℝ => Complex.digamma (z + (u : ℂ) * w)) u :=
    ContinuousAt.comp (g := Complex.digamma) (f := fun u : ℝ => z + (u : ℂ) * w) (x := u) hout hmap
  exact (hcomp.const_mul w).continuousWithinAt

/-- **Gamma shifts by the exponential of the integrated digamma, in any direction.** -/
theorem gamma_shift_exp_integral_complex {z w : ℂ} (h0 : 0 < z.re) (h1 : 0 < (z + w).re) :
    Complex.Gamma (z + w)
      = Complex.Gamma z
        * Complex.exp (∫ u in (0 : ℝ)..1, w * Complex.digamma (z + (u : ℂ) * w)) := by
  classical
  set S : Set ℝ := {u : ℝ | 0 < (z + (u : ℂ) * w).re} with hS
  have hSopen : IsOpen S := isOpen_segmentSet z w
  have hcontS : ContinuousOn (fun u : ℝ => w * Complex.digamma (z + (u : ℂ) * w)) S :=
    continuousOn_digamma_segment z w
  have hsub : Set.uIcc (0 : ℝ) 1 ⊆ S := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hu
    exact segment_re_pos h0 h1 hu
  have hcontI : ContinuousOn (fun u : ℝ => w * Complex.digamma (z + (u : ℂ) * w))
      (Set.uIcc 0 1) := hcontS.mono hsub
  have hint : IntervalIntegrable (fun u : ℝ => w * Complex.digamma (z + (u : ℂ) * w))
      MeasureTheory.volume 0 1 := hcontI.intervalIntegrable
  set Ψ : ℝ → ℂ := fun y => ∫ u in (0 : ℝ)..y, w * Complex.digamma (z + (u : ℂ) * w) with hΨ
  have hderivΨ : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt Ψ (w * Complex.digamma (z + (y : ℂ) * w)) y := by
    intro y hy
    have hyS : y ∈ S := hsub hy
    have hsuby : Set.uIcc (0 : ℝ) y ⊆ Set.uIcc (0 : ℝ) 1 := by
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      rw [Set.uIcc_of_le (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy; exact hy.1)]
      rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hy
      exact Set.Icc_subset_Icc le_rfl hy.2
    refine intervalIntegral.integral_hasDerivAt_right (hint.mono_set hsuby) ?_ ?_
    · exact hcontS.stronglyMeasurableAtFilter hSopen y hyS
    · exact hcontS.continuousAt (hSopen.mem_nhds hyS)
  have hzero : ∀ y ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun v : ℝ => Complex.Gamma (z + (v : ℂ) * w) * Complex.exp (-Ψ v)) 0 y := by
    intro y hy
    have hyS : y ∈ S := hsub hy
    have hre : 0 < (z + (y : ℂ) * w).re := hyS
    have hinner : HasDerivAt (fun v : ℂ => z + v * w) w ((y : ℝ) : ℂ) := by
      have := ((hasDerivAt_id ((y : ℝ) : ℂ)).mul_const w).const_add z
      simpa using this
    have houter : HasDerivAt Complex.Gamma (deriv Complex.Gamma (z + (y : ℂ) * w))
        (z + (y : ℂ) * w) := (differentiableAt_gamma_of_re_pos hre).hasDerivAt
    have hcomp : HasDerivAt (fun v : ℂ => Complex.Gamma (z + v * w))
        (deriv Complex.Gamma (z + (y : ℂ) * w) * w) ((y : ℝ) : ℂ) :=
      houter.comp ((y : ℝ) : ℂ) hinner
    have hΓ : HasDerivAt (fun v : ℝ => Complex.Gamma (z + (v : ℂ) * w))
        (Complex.Gamma (z + (y : ℂ) * w) * Complex.digamma (z + (y : ℂ) * w) * w) y := by
      have h := hcomp.comp_ofReal
      rw [deriv_gamma_eq hre] at h
      exact h
    have hexp : HasDerivAt (fun v : ℝ => Complex.exp (-Ψ v))
        (Complex.exp (-Ψ y) * -(w * Complex.digamma (z + (y : ℂ) * w))) y :=
      ((hderivΨ y hy).neg).cexp
    have hprod := hΓ.mul hexp
    have hval : Complex.Gamma (z + (y : ℂ) * w) * Complex.digamma (z + (y : ℂ) * w) * w
          * Complex.exp (-Ψ y)
        + Complex.Gamma (z + (y : ℂ) * w)
          * (Complex.exp (-Ψ y) * -(w * Complex.digamma (z + (y : ℂ) * w))) = 0 := by
      ring
    rw [hval] at hprod
    exact hprod
  have hΨ0 : Ψ 0 = 0 := by
    rw [hΨ]
    simp
  have heq : Complex.Gamma (z + ((1 : ℝ) : ℂ) * w) * Complex.exp (-Ψ 1) = Complex.Gamma z := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hzero
      (intervalIntegrable_const (c := (0 : ℂ)))
    rw [intervalIntegral.integral_zero] at h
    have hstep := sub_eq_zero.mp h.symm
    have h0' : Complex.Gamma (z + (((0 : ℝ) : ℂ)) * w) * Complex.exp (-Ψ 0) = Complex.Gamma z := by
      rw [hΨ0, neg_zero, Complex.exp_zero, mul_one]
      norm_num
    rw [h0'] at hstep
    exact hstep
  have hone : z + ((1 : ℝ) : ℂ) * w = z + w := by push_cast; ring
  rw [hone] at heq
  rw [← heq, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

end

end GaloisForLFunctions.HTGeometry
