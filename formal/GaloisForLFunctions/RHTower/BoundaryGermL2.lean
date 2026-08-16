import GaloisForLFunctions.RHTower.JonquiereExpansion

/-!
# The boundary germ of the polylogarithm is square integrable on the phase window

For `1/2 < Re s < 1` the boundary germ `θ ↦ Li_s(e^{iθ})` is continuous away from the origin and
grows like `|θ|^{σ-1}` there, so it lies in `L²` of the window `(-π, π]`.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- The boundary germ as a function of the phase. -/
noncomputable def phaseGerm (s : ℂ) (θ : ℝ) : ℂ :=
  expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) s

theorem phaseGerm_neg (s : ℂ) (θ : ℝ) :
    phaseGerm s (-θ) = expZeta ((-(θ / (2 * Real.pi)) : ℝ) : UnitAddCircle) s := by
  rw [phaseGerm]
  congr 2
  ring

/-- Continuity of the germ on the positive half of the window. -/
theorem continuousOn_phaseGerm_pos {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ContinuousOn (phaseGerm s) (Ioc (0 : ℝ) Real.pi) :=
  continuousOn_expZeta_phase h0 h1

/-- Continuity of the germ on the negative half of the window. -/
theorem continuousOn_phaseGerm_neg {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ContinuousOn (phaseGerm s) (Ico (-Real.pi) 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hw : 0 < (1 - s).re := by simp; linarith
  have hmaps : Set.MapsTo (fun θ : ℝ => -θ) (Ico (-Real.pi) 0) (Ioc (0 : ℝ) Real.pi) := by
    intro θ hθ
    exact ⟨by simpa using hθ.2, by linarith [hθ.1]⟩
  have hmaps2 : Set.MapsTo (fun u : ℝ => u / (2 * Real.pi)) (Ioc (0 : ℝ) Real.pi)
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hpos : (0 : ℝ) < u / (2 * Real.pi) := by positivity
    refine ⟨by linarith, ?_⟩
    rw [div_le_iff₀ (by positivity)]
    linarith [hu.2]
  have hmaps3 : Set.MapsTo (fun u : ℝ => -(u / (2 * Real.pi))) (Ioc (0 : ℝ) Real.pi)
      (Set.Icc (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro u hu
    obtain ⟨ha, hb⟩ := hmaps2 hu
    exact ⟨by linarith, by linarith⟩
  have hdiv : ContinuousOn (fun u : ℝ => u / (2 * Real.pi)) (Ioc (0 : ℝ) Real.pi) := by fun_prop
  have hdivneg : ContinuousOn (fun u : ℝ => -(u / (2 * Real.pi))) (Ioc (0 : ℝ) Real.pi) := by
    fun_prop
  have hrem : ContinuousOn (fun u : ℝ => jonquiereRemainderNeg s u) (Ioc (0 : ℝ) Real.pi) := by
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.add ?_ ?_)
    · exact continuousOn_const.mul ((continuousOn_shiftDiffSeries hw).comp hdivneg hmaps3)
    · exact continuousOn_const.mul ((continuousOn_shiftDiffSeries hw).comp hdiv hmaps2)
  have hpow : ContinuousOn (fun u : ℝ => ((u : ℝ) : ℂ) ^ (s - 1)) (Ioc (0 : ℝ) Real.pi) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hslit : ((u : ℝ) : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by simpa using hu0)
    have h1' : ContinuousAt (fun t : ℝ => ((t : ℝ) : ℂ)) u := by fun_prop
    exact (ContinuousAt.comp (g := fun z : ℂ => z ^ (s - 1))
      (f := fun t : ℝ => ((t : ℝ) : ℂ)) (x := u)
      (continuousAt_cpow_const hslit) h1').continuousWithinAt
  have hg : ContinuousOn (fun u : ℝ => jonquiereLeadNeg s * ((u : ℝ) : ℂ) ^ (s - 1)
      + riemannZeta s + jonquiereRemainderNeg s u) (Ioc (0 : ℝ) Real.pi) :=
    ((continuousOn_const.mul hpow).add continuousOn_const).add hrem
  have hcomp := hg.comp (continuousOn_neg.mono (Set.subset_univ _)) hmaps
  refine hcomp.congr fun θ hθ => ?_
  have hu : (0 : ℝ) < -θ := by simpa using hθ.2
  have hu2 : -θ ≤ Real.pi := by linarith [hθ.1]
  have hval := expZeta_neg_eq_jonquiere h0 h1 hu hu2
  have hgerm : phaseGerm s θ = expZeta ((-((-θ) / (2 * Real.pi)) : ℝ) : UnitAddCircle) s := by
    rw [phaseGerm]
    congr 2
    ring
  simp only [Function.comp_apply]
  rw [hgerm, hval]

/-- Powers of the absolute value are integrable on the symmetric window. -/
theorem integrableOn_abs_rpow_window {r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun θ : ℝ => |θ| ^ r) (Ioc (-Real.pi) Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : IntegrableOn (fun θ : ℝ => |θ| ^ r) (Ioc (0 : ℝ) Real.pi) := by
    have hbase : IntegrableOn (fun θ : ℝ => θ ^ r) (Ioc (0 : ℝ) Real.pi) := by
      have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := Real.pi) hr
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le] at h
    refine hbase.congr_fun (fun θ hθ => ?_) measurableSet_Ioc
    have hθ0 : (0 : ℝ) < θ := hθ.1
    rw [abs_of_pos hθ0]
  have hneg : IntegrableOn (fun θ : ℝ => |θ| ^ r) (Ioc (-Real.pi) 0) := by
    have hcomp := hpos.comp_neg
    have hset : (-(Ioc (0 : ℝ) Real.pi)) = Ico (-Real.pi) 0 := by
      ext y
      simp
    rw [hset] at hcomp
    have hfun : (fun θ : ℝ => |(-θ)| ^ r) = fun θ : ℝ => |θ| ^ r := by
      funext θ
      rw [abs_neg]
    rw [hfun] at hcomp
    exact hcomp.congr_set_ae (MeasureTheory.Ico_ae_eq_Ioc).symm
  have hsplit : Ioc (-Real.pi) Real.pi = Ioc (-Real.pi) 0 ∪ Ioc (0 : ℝ) Real.pi := by
    rw [Set.Ioc_union_Ioc_eq_Ioc (by linarith) hpi.le]
  rw [hsplit]
  exact hneg.union hpos

/-- **The boundary germ is bounded by the Jonquière profile on the window.** -/
theorem norm_phaseGerm_le {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    ∀ θ ∈ Ioc (-Real.pi) Real.pi, θ ≠ 0 →
      ‖phaseGerm s θ‖
        ≤ (‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖
            + jonquiereConst s * Real.pi) * (|θ| ^ (s.re - 1) + 1) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set C : ℝ := ‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖
    + jonquiereConst s * Real.pi with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have := jonquiereConst_nonneg s
    positivity
  intro θ hθ hθ0
  rcases lt_or_gt_of_ne hθ0 with hneg | hpos
  · -- negative phase
    have hu : (0 : ℝ) < -θ := by linarith
    have hu2 : -θ ≤ Real.pi := by linarith [hθ.1]
    have hgerm : phaseGerm s θ = expZeta ((-((-θ) / (2 * Real.pi)) : ℝ) : UnitAddCircle) s := by
      rw [phaseGerm]; congr 2; ring
    have hb := norm_expZeta_neg_sub_jonquiere_le h0 h1 hu hu2
    set B : ℂ := jonquiereLeadNeg s * (((-θ : ℝ)) : ℂ) ^ (s - 1) + riemannZeta s with hB
    have hsplit : ‖phaseGerm s θ‖ ≤ ‖B‖ + jonquiereConst s * (-θ) := by
      rw [hgerm]
      have hid : expZeta ((-((-θ) / (2 * Real.pi)) : ℝ) : UnitAddCircle) s
          = B + (expZeta ((-((-θ) / (2 * Real.pi)) : ℝ) : UnitAddCircle) s - B) := by ring
      rw [hid]
      refine (norm_add_le _ _).trans ?_
      linarith [hb]
    have hpow : ‖(((-θ : ℝ)) : ℂ) ^ (s - 1)‖ = (-θ) ^ (s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, Complex.sub_re, Complex.one_re]
    have habs : |θ| = -θ := abs_of_neg hneg
    refine hsplit.trans ?_
    have h1' : ‖B‖ ≤ ‖jonquiereLeadNeg s‖ * (-θ) ^ (s.re - 1) + ‖riemannZeta s‖ := by
      rw [hB]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, hpow]
    have h2' : jonquiereConst s * (-θ) ≤ jonquiereConst s * Real.pi :=
      mul_le_mul_of_nonneg_left hu2 (jonquiereConst_nonneg s)
    have hnn : (0 : ℝ) ≤ (-θ) ^ (s.re - 1) := Real.rpow_nonneg hu.le _
    rw [habs, hC]
    nlinarith [mul_nonneg (norm_nonneg (jonquiereLead s)) hnn,
      mul_nonneg (norm_nonneg (jonquiereLeadNeg s)) hnn,
      mul_nonneg (norm_nonneg (riemannZeta s)) hnn,
      mul_nonneg (mul_nonneg (jonquiereConst_nonneg s) hpi.le) hnn,
      norm_nonneg (jonquiereLead s), norm_nonneg (jonquiereLeadNeg s),
      norm_nonneg (riemannZeta s), mul_nonneg (jonquiereConst_nonneg s) hpi.le]
  · -- positive phase
    have hu2 : θ ≤ Real.pi := hθ.2
    have hb := norm_expZeta_sub_jonquiere_le h0 h1 hpos hu2
    set B : ℂ := jonquiereLead s * ((θ : ℝ) : ℂ) ^ (s - 1) + riemannZeta s with hB
    have hsplit : ‖phaseGerm s θ‖ ≤ ‖B‖ + jonquiereConst s * θ := by
      rw [phaseGerm]
      have hid : expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) s
          = B + (expZeta (((θ / (2 * Real.pi) : ℝ)) : UnitAddCircle) s - B) := by ring
      rw [hid]
      refine (norm_add_le _ _).trans ?_
      linarith [hb]
    have hpow : ‖((θ : ℝ) : ℂ) ^ (s - 1)‖ = θ ^ (s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hpos, Complex.sub_re, Complex.one_re]
    have habs : |θ| = θ := abs_of_pos hpos
    refine hsplit.trans ?_
    have h1' : ‖B‖ ≤ ‖jonquiereLead s‖ * θ ^ (s.re - 1) + ‖riemannZeta s‖ := by
      rw [hB]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, hpow]
    have h2' : jonquiereConst s * θ ≤ jonquiereConst s * Real.pi :=
      mul_le_mul_of_nonneg_left hu2 (jonquiereConst_nonneg s)
    have hnn : (0 : ℝ) ≤ θ ^ (s.re - 1) := Real.rpow_nonneg hpos.le _
    rw [habs, hC]
    nlinarith [mul_nonneg (norm_nonneg (jonquiereLead s)) hnn,
      mul_nonneg (norm_nonneg (jonquiereLeadNeg s)) hnn,
      mul_nonneg (norm_nonneg (riemannZeta s)) hnn,
      mul_nonneg (mul_nonneg (jonquiereConst_nonneg s) hpi.le) hnn,
      norm_nonneg (jonquiereLead s), norm_nonneg (jonquiereLeadNeg s),
      norm_nonneg (riemannZeta s), mul_nonneg (jonquiereConst_nonneg s) hpi.le]

/-- The germ is measurable on the window. -/
theorem aestronglyMeasurable_phaseGerm {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    AEStronglyMeasurable (phaseGerm s) (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hunion : Ioo (-Real.pi) 0 ∪ Ioc (0 : ℝ) Real.pi = Ioc (-Real.pi) Real.pi \ {(0 : ℝ)} := by
    ext y
    simp only [mem_union, mem_Ioo, mem_Ioc, Set.mem_sdiff, mem_singleton_iff]
    constructor
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · exact ⟨⟨ha, by linarith⟩, by linarith⟩
      · exact ⟨⟨by linarith, hb⟩, by linarith⟩
    · rintro ⟨⟨ha, hb⟩, hc⟩
      rcases lt_or_gt_of_ne hc with h | h
      · exact Or.inl ⟨ha, h⟩
      · exact Or.inr ⟨h, hb⟩
  have hae : Ioc (-Real.pi) Real.pi
      =ᵐ[volume] ((Ioo (-Real.pi) 0 ∪ Ioc (0 : ℝ) Real.pi : Set ℝ)) := by
    have hnull : (volume : Measure ℝ) {(0 : ℝ)} = 0 := measure_singleton (0 : ℝ)
    have h : ((Ioc (-Real.pi) Real.pi \ {(0 : ℝ)} : Set ℝ)) =ᵐ[volume]
        (Ioc (-Real.pi) Real.pi : Set ℝ) :=
      MeasureTheory.sdiff_null_ae_eq_self hnull
    rw [← hunion] at h
    exact h.symm
  rw [MeasureTheory.Measure.restrict_congr_set hae, aestronglyMeasurable_union_iff]
  refine ⟨?_, ?_⟩
  · exact ((continuousOn_phaseGerm_neg h0 h1).mono
      Set.Ioo_subset_Ico_self).aestronglyMeasurable measurableSet_Ioo
  · exact (continuousOn_phaseGerm_pos h0 h1).aestronglyMeasurable measurableSet_Ioc

/-- The Jonquière profile is square integrable on the window. -/
theorem memLp_jonquiereProfile {sig C : ℝ} (hsig : 1 / 2 < sig) (hsig1 : sig < 1) :
    MemLp (fun θ : ℝ => C * (|θ| ^ (sig - 1) + 1)) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmeas : AEStronglyMeasurable (fun θ : ℝ => C * (|θ| ^ (sig - 1) + 1))
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    refine (Measurable.aestronglyMeasurable ?_)
    fun_prop
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hsq : ∀ θ : ℝ, ‖C * (|θ| ^ (sig - 1) + 1)‖ ^ 2
      = C ^ 2 * (|θ| ^ (2 * sig - 2) + 2 * |θ| ^ (sig - 1) + 1) := by
    intro θ
    rcases eq_or_ne θ 0 with h | h
    · subst h
      have h1 : |(0 : ℝ)| ^ (sig - 1) = 0 := by
        rw [abs_zero, Real.zero_rpow (by linarith)]
      have h2 : |(0 : ℝ)| ^ (2 * sig - 2) = 0 := by
        rw [abs_zero, Real.zero_rpow (by linarith)]
      rw [h1, h2]
      simp [Real.norm_eq_abs, sq_abs]
    · have hpos : (0 : ℝ) < |θ| := abs_pos.mpr h
      have hd : (|θ| ^ (sig - 1)) ^ 2 = |θ| ^ (2 * sig - 2) := by
        rw [← Real.rpow_natCast (|θ| ^ (sig - 1)) 2, ← Real.rpow_mul (abs_nonneg θ)]
        congr 1
        push_cast
        ring
      rw [Real.norm_eq_abs, sq_abs, mul_pow]
      have hexp : (|θ| ^ (sig - 1) + 1) ^ 2
          = (|θ| ^ (sig - 1)) ^ 2 + 2 * |θ| ^ (sig - 1) + 1 := by ring
      rw [hexp, hd]
  have hcongr : (fun θ : ℝ => ‖C * (|θ| ^ (sig - 1) + 1)‖ ^ 2)
      = fun θ : ℝ => C ^ 2 * (|θ| ^ (2 * sig - 2) + 2 * |θ| ^ (sig - 1) + 1) := funext hsq
  rw [hcongr]
  refine Integrable.const_mul ?_ _
  refine Integrable.add (Integrable.add ?_ ?_) ?_
  · exact integrableOn_abs_rpow_window (by linarith)
  · exact (integrableOn_abs_rpow_window (by linarith)).const_mul 2
  · refine integrableOn_const (C := (1 : ℝ)) ?_
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top

/-- **The boundary germ is square integrable on the phase window.** -/
theorem memLp_phaseGerm {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) :
    MemLp (phaseGerm s) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  have h0' : (0 : ℝ) < s.re := by linarith
  set C : ℝ := ‖jonquiereLead s‖ + ‖jonquiereLeadNeg s‖ + ‖riemannZeta s‖
    + jonquiereConst s * Real.pi with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have := jonquiereConst_nonneg s
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  refine MemLp.of_le (memLp_jonquiereProfile (C := C) h0 h1)
    (aestronglyMeasurable_phaseGerm h0' h1) ?_
  have hne0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
    MeasureTheory.ae_restrict_of_ae hne0] with θ hθ hne
  have hb := norm_phaseGerm_le h0' h1 θ hθ hne
  have hnn : (0 : ℝ) ≤ C * (|θ| ^ (s.re - 1) + 1) := by
    have : (0 : ℝ) ≤ |θ| ^ (s.re - 1) := Real.rpow_nonneg (abs_nonneg θ) _
    positivity
  rw [Real.norm_of_nonneg hnn]
  exact hb

end RHTower
