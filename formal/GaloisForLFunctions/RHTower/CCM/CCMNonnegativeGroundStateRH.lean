import GaloisForLFunctions.RHTower.CCM.CCMRiemannKernelBartaFarTail
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilCrossApertureFormTransport
import GaloisForLFunctions.RHTower.CCM.CCMFullGroundGaussianGrowthRH
import GaloisForLFunctions.RHTower.CCM.CCMEigenvectorLowFrequencyMassBound

/-!
# Nonnegative ground states force RH

Let `x ≥ 0` be an eigenvector of the restricted Weil form at aperture `b`,
`Q_b(x, s) = μ ⟨x, s⟩` for every smooth interior source `s`. Test it against the truncated Riemann
kernel `s = Φ χ_{b−w,w}`, `w = e^{−2b}`:

* nesting into aperture `b + 3` and splitting `Φ χ_{b−w,w} = Φ χ_{b+2,1} − T_b` gives
  `|Q_b(x, s)| ≤ (C_far + C_edge (1 + b)) Φ(b − 2w) ∫|x|` (`exists_bartaFar_bound`,
  `exists_bartaEdge_bound_formDomain`);
* `s ≥ Φ(b − 2w)` on `|t| ≤ b − 2w`, so `Re ⟨x, s⟩ ≥ Φ(b − 2w) (∫|x| − ∫_{|t| > b−2w} |x|)`.

Without any sign condition this gives `|μ| |⟨x, s⟩| ≤ C (1 + b) Φ(b − 2w) ∫|x|`
(`exists_abs_eigenvalue_mul_overlap_le`), so ground states whose overlap with Riemann's kernel is
not smaller than `e^{−εb} Φ(b − 2w) ∫|x|` force RH (`riemannHypothesis_of_fullGrounds_overlap`).
If the edge mass `∫_{|t| > b−2w} |x|` is at most half of `∫|x|`, then `|μ| ≤ C (1 + b)`
(`exists_abs_eigenvalue_le_of_nonneg`). The edge has total length `4e^{−2b}`, so this holds as
soon as `‖x‖₂ ≤ e^{b} ‖x‖₁ / 6` (`bartaEdgeMass_le_half_of_norm_le`).

Applied to full ground states this bounds the ground energy below polynomially in the aperture,
and the subexponential criterion gives RH (`riemannHypothesis_of_nonneg_fullGrounds`,
`riemannHypothesis_of_nonneg_fullGrounds_of_norm_le`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

namespace RHTower

open RHTower.CCMRealRootedGround RHTower.CCMFullGroundEigen RHTower.CCMFullRealRootedGround

noncomputable section

/-! ## Linear structure of smooth form vectors -/

theorem ccmRestrictedWeilForm_sub_right (a : SuzukiPositiveAperture)
    (x v₁ v₂ : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a x (v₁ - v₂) =
      ccmRestrictedWeilForm a x v₁ - ccmRestrictedWeilForm a x v₂ := by
  unfold ccmRestrictedWeilForm
  rw [inner_sub_right, map_sub, inner_sub_right]
  ring

/-- Smooth interior sources with the same profile have the same form vector, at any apertures. -/
theorem toCCMFormVector_val_eq_of_coe_eq {a a' : SuzukiPositiveAperture}
    (s : CCMComplexSmoothInteriorSource a) (s' : CCMComplexSmoothInteriorSource a')
    (h : ∀ t, s' t = s t) : s'.toCCMFormVector.1 = s.toCCMFormVector.1 := by
  apply ccmArchimedeanFourierToTime_injective
  change (ccmArchimedeanFormToAperture a' s'.toCCMFormVector : SoninL2) =
    (ccmArchimedeanFormToAperture a s.toCCMFormVector : SoninL2)
  apply Lp.ext
  filter_upwards [s'.toCCMFormVector_physical_coeFn, s.toCCMFormVector_physical_coeFn]
    with t h1 h2
  rw [h1, h2]
  exact h t

/-- A smooth interior source whose profile is a difference has the difference form vector. -/
theorem toCCMFormVector_eq_sub_of_coe_eq {a : SuzukiPositiveAperture}
    (s s₁ s₂ : CCMComplexSmoothInteriorSource a) (h : ∀ t, s t = s₁ t - s₂ t) :
    s.toCCMFormVector = s₁.toCCMFormVector - s₂.toCCMFormVector := by
  apply ccmArchimedeanFormToAperture_injective a
  rw [map_sub]
  apply Subtype.ext
  rw [Submodule.coe_sub]
  apply Lp.ext
  filter_upwards [s.toCCMFormVector_physical_coeFn, s₁.toCCMFormVector_physical_coeFn,
    s₂.toCCMFormVector_physical_coeFn,
    Lp.coeFn_sub (ccmArchimedeanFormToAperture a s₁.toCCMFormVector : SoninL2)
      (ccmArchimedeanFormToAperture a s₂.toCCMFormVector : SoninL2)] with t h0 h1 h2 h3
  rw [h0, h3, Pi.sub_apply, h1, h2]
  exact h t

/-- Extending a vector to a larger aperture does not change its time function. -/
theorem timeRep_ae_eq_of_val_eq {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b} (hvu : v.1 = u.1) :
    timeRep b v =ᵐ[volume] timeRep a u := by
  have hsub : centralInterval a.1 ⊆ centralInterval b.1 := by
    unfold centralInterval; exact Icc_subset_Icc (by linarith) hab
  have e : timeRep b v = (centralInterval b.1).indicator
      (((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) : ℝ → ℂ) := by
    unfold timeRep; rw [ccmArchimedeanFormToAperture_coe_eq_of_val_eq hvu]
  have h2 : (centralInterval b.1).indicator (timeRep a u) = timeRep a u := by
    unfold timeRep; rw [Set.indicator_indicator, Set.inter_eq_right.mpr hsub]
  rw [e]
  calc (centralInterval b.1).indicator
        (((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) : ℝ → ℂ)
      =ᵐ[volume] (centralInterval b.1).indicator (timeRep a u) :=
        (coeFn_eq_timeRep a u).indicator
    _ = timeRep a u := h2

/-! ## The edge set and the overlap -/

/-- The edge `|t| > b − 2w` of the truncated kernel. -/
def bartaEdgeSet (b : ℝ) : Set ℝ := {t : ℝ | bartaInner b < |t|}

theorem measurableSet_bartaEdgeSet (b : ℝ) : MeasurableSet (bartaEdgeSet b) :=
  measurableSet_lt measurable_const continuous_abs.measurable

/-- The edge mass of a time function. -/
def bartaEdgeMass (b : ℝ) (f : ℝ → ℂ) : ℝ := ∫ t, (bartaEdgeSet b).indicator (fun t => ‖f t‖) t

/-- The inner truncated kernel `Φ χ_{b−w,w}` at aperture `A`, `A.1 = b`. -/
def bartaInnerAt (A : SuzukiPositiveAperture) : CCMComplexSmoothInteriorSource A :=
  bartaSource A (A.1 - bartaWidth A.1) (bartaWidth A.1) (bartaWidth_pos A.1)
    (by linarith [bartaWidth_pos A.1])

theorem bartaInnerAt_toFun (A : SuzukiPositiveAperture) (t : ℝ) :
    (bartaInnerAt A).toFun t =
      ((bartaProfile (A.1 - bartaWidth A.1) (bartaWidth A.1) t : ℝ) : ℂ) := rfl

/-- **Overlap.** For a nonnegative time function, `Re ⟨x, Φχ⟩ ≥ Φ(b − 2w) (∫|x| − edge mass)`. -/
theorem bartaEdge_mul_le_re_overlap {A : SuzukiPositiveAperture}
    (hmin : ∀ t : ℝ, |t| ≤ bartaInner A.1 → bartaEdge A.1 ≤ riemannKernelReal t)
    (x : CCMArchimedeanFormDomain A)
    (hpos : ∀ t, (timeRep A x t).im = 0 ∧ 0 ≤ (timeRep A x t).re) :
    bartaEdge A.1 * ((∫ t, ‖timeRep A x t‖) - bartaEdgeMass A.1 (timeRep A x)) ≤
      (∫ t, (starRingEnd ℂ) (timeRep A x t) * bartaInnerAt A t).re := by
  have hw0 : 0 < bartaWidth A.1 := bartaWidth_pos A.1
  have hfint : Integrable (timeRep A x) := integrable_timeRep A x
  have hnorm : ∀ t, ‖timeRep A x t‖ = (timeRep A x t).re := by
    intro t
    have hft : timeRep A x t = ((timeRep A x t).re : ℂ) :=
      Complex.ext (by simp) (by simp [(hpos t).1])
    rw [hft, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos t).2, Complex.ofReal_re]
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support
    (bartaInnerAt A).smooth.continuous (bartaInnerAt A).hasCompactSupport
  have hprodint : Integrable fun t => (starRingEnd ℂ) (timeRep A x t) * bartaInnerAt A t := by
    refine (hfint.norm.mul_const M).mono'
      ((hfint.aestronglyMeasurable.star).mul
        (bartaInnerAt A).smooth.continuous.aestronglyMeasurable) (ae_of_all _ fun t => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (hM t) (norm_nonneg _)
  have hpt : ∀ t, RCLike.re ((starRingEnd ℂ) (timeRep A x t) * bartaInnerAt A t) =
      (timeRep A x t).re * bartaProfile (A.1 - bartaWidth A.1) (bartaWidth A.1) t := by
    intro t
    show ((starRingEnd ℂ) (timeRep A x t) * (bartaInnerAt A).toFun t).re = _
    rw [bartaInnerAt_toFun]
    simp [Complex.mul_re]
  have hre : (∫ t, (starRingEnd ℂ) (timeRep A x t) * bartaInnerAt A t).re =
      ∫ t, (timeRep A x t).re * bartaProfile (A.1 - bartaWidth A.1) (bartaWidth A.1) t := by
    refine (integral_re hprodint).symm.trans ?_
    exact integral_congr_ae (ae_of_all _ hpt)
  rw [hre]
  have hind : Integrable ((bartaEdgeSet A.1).indicator fun t => ‖timeRep A x t‖) :=
    (integrable_indicator_iff (measurableSet_bartaEdgeSet A.1)).mpr hfint.norm.integrableOn
  have hint2 : Integrable fun t =>
      (timeRep A x t).re * bartaProfile (A.1 - bartaWidth A.1) (bartaWidth A.1) t :=
    hprodint.re.congr (ae_of_all _ hpt)
  unfold bartaEdgeMass
  rw [← integral_sub hfint.norm hind, ← integral_const_mul]
  refine integral_mono ((hfint.norm.sub hind).const_mul _) hint2 fun t => ?_
  simp only
  have hg0 := (hpos t).2
  rw [hnorm t]
  by_cases ht : t ∈ bartaEdgeSet A.1
  · rw [indicator_of_mem ht, hnorm t, sub_self, mul_zero]
    exact mul_nonneg hg0 (bartaProfile_nonneg _ _ _)
  · rw [indicator_of_notMem ht, sub_zero]
    have hts : |t| ≤ bartaInner A.1 := not_lt.mp ht
    have hP : bartaProfile (A.1 - bartaWidth A.1) (bartaWidth A.1) t = riemannKernelReal t := by
      apply bartaProfile_eq hw0
      have : bartaInner A.1 = A.1 - bartaWidth A.1 - bartaWidth A.1 := by rw [bartaInner]; ring
      linarith
    rw [hP, mul_comm]
    exact mul_le_mul_of_nonneg_left (hmin t hts) hg0

/-! ## The edge mass from the `L²` norm -/

theorem setIntegral_Icc_norm_le_sqrt {p q : ℝ} (hpq : p ≤ q) (f : SoninL2) :
    (∫ t in Icc p q, ‖(f : ℝ → ℂ) t‖) ≤ Real.sqrt (q - p) * ‖f‖ := by
  haveI : IsFiniteMeasure (volume.restrict (Icc p q)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact measure_Icc_lt_top
  have hmem : MemLp ((f : ℝ → ℂ)) 2 (volume.restrict (Icc p q)) := (Lp.memLp f).restrict _
  have hsq : (∫ t in Icc p q, ‖(f : ℝ → ℂ) t‖ ^ 2) ≤ ‖f‖ ^ 2 :=
    integral_norm_sq_le_norm_sq f (Icc p q)
  have hone : Integrable (fun _ : ℝ => ((1 : ℝ)) ^ 2) (volume.restrict (Icc p q)) := by simp
  have hcs : (∫ t in Icc p q, (1 : ℝ) * ‖(f : ℝ → ℂ) t‖) ^ 2
      ≤ (∫ _t in Icc p q, ((1 : ℝ)) ^ 2) * ∫ t in Icc p q, ‖(f : ℝ → ℂ) t‖ ^ 2 :=
    GaloisForLFunctions.HTGeometry.sq_integral_mul_le aestronglyMeasurable_const hmem.1.norm hone
      ((memLp_two_iff_integrable_sq_norm hmem.1).1 hmem)
  have hmeas : (∫ _t in Icc p q, ((1 : ℝ)) ^ 2) = q - p := by
    simp only [one_pow]
    rw [setIntegral_const, Real.volume_real_Icc, max_eq_left (by linarith : (0:ℝ) ≤ q - p)]
    simp
  have hone_mul : (∫ t in Icc p q, (1 : ℝ) * ‖(f : ℝ → ℂ) t‖) =
      ∫ t in Icc p q, ‖(f : ℝ → ℂ) t‖ := by
    refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    ring
  rw [hone_mul, hmeas] at hcs
  have hnn : (0 : ℝ) ≤ ∫ t in Icc p q, ‖(f : ℝ → ℂ) t‖ :=
    setIntegral_nonneg measurableSet_Icc fun t _ => norm_nonneg _
  have hqp : 0 ≤ q - p := by linarith
  have hrhs : (Real.sqrt (q - p) * ‖f‖) ^ 2 = (q - p) * ‖f‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hqp]
  have hX2 : (∫ t in Icc p q, ‖(f : ℝ → ℂ) t‖) ^ 2 ≤ (Real.sqrt (q - p) * ‖f‖) ^ 2 := by
    rw [hrhs]
    exact hcs.trans (mul_le_mul_of_nonneg_left hsq hqp)
  have hR0 : (0 : ℝ) ≤ Real.sqrt (q - p) * ‖f‖ := by positivity
  nlinarith [hX2, hnn, hR0]

/-- **The `L²` edge condition.** If `‖x‖₂ ≤ e^{b} ‖x‖₁ / 6`, the edge mass is at most half of the
mass: the edge `b − 2w < |t| ≤ b` has total length `4e^{−2b}`. -/
theorem bartaEdgeMass_le_half_of_norm_le {A : SuzukiPositiveAperture} (hb : 1 ≤ A.1)
    (x : CCMArchimedeanFormDomain A)
    (h : ‖ccmArchimedeanFormToAperture A x‖ ≤ Real.exp A.1 / 6 * ∫ t, ‖timeRep A x t‖) :
    bartaEdgeMass A.1 (timeRep A x) ≤ 1 / 2 * ∫ t, ‖timeRep A x t‖ := by
  set F : SoninL2 := (ccmArchimedeanFormToAperture A x : SoninL2) with hF
  set s := bartaInner A.1 with hs
  set N : ℝ := ∫ t, ‖timeRep A x t‖ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  have hw0 := bartaWidth_pos A.1
  have hsb : A.1 - s = 2 * bartaWidth A.1 := by rw [hs, bartaInner]; ring
  have hs0 : 0 ≤ s := (bartaInner_pos hb).le
  have hg : Integrable (fun t => ‖(F : ℝ → ℂ) t‖) (volume.restrict (Icc s A.1)) := by
    haveI : IsFiniteMeasure (volume.restrict (Icc s A.1)) := by
      refine ⟨?_⟩; rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top
    exact (((Lp.memLp F).restrict _).integrable (by norm_num)).norm
  have hg' : Integrable (fun t => ‖(F : ℝ → ℂ) t‖) (volume.restrict (Icc (-A.1) (-s))) := by
    haveI : IsFiniteMeasure (volume.restrict (Icc (-A.1) (-s))) := by
      refine ⟨?_⟩; rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top
    exact (((Lp.memLp F).restrict _).integrable (by norm_num)).norm
  have hi1 : Integrable ((Icc s A.1).indicator fun t => ‖(F : ℝ → ℂ) t‖) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hg
  have hi2 : Integrable ((Icc (-A.1) (-s)).indicator fun t => ‖(F : ℝ → ℂ) t‖) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hg'
  have hfint : Integrable (timeRep A x) := integrable_timeRep A x
  have hE : Integrable ((bartaEdgeSet A.1).indicator fun t => ‖timeRep A x t‖) :=
    (integrable_indicator_iff (measurableSet_bartaEdgeSet A.1)).mpr hfint.norm.integrableOn
  have hpt : ∀ t, (bartaEdgeSet A.1).indicator (fun t => ‖timeRep A x t‖) t ≤
      (Icc s A.1).indicator (fun t => ‖(F : ℝ → ℂ) t‖) t +
        (Icc (-A.1) (-s)).indicator (fun t => ‖(F : ℝ → ℂ) t‖) t := by
    intro t
    have h0 : 0 ≤ (Icc s A.1).indicator (fun t => ‖(F : ℝ → ℂ) t‖) t :=
      indicator_nonneg (fun _ _ => norm_nonneg _) t
    have h0' : 0 ≤ (Icc (-A.1) (-s)).indicator (fun t => ‖(F : ℝ → ℂ) t‖) t :=
      indicator_nonneg (fun _ _ => norm_nonneg _) t
    by_cases hE : t ∈ bartaEdgeSet A.1
    · rw [indicator_of_mem hE]
      have hts : s < |t| := hE
      by_cases hc : t ∈ centralInterval A.1
      · have htr : timeRep A x t = (F : ℝ → ℂ) t := by
          rw [timeRep, indicator_of_mem hc]
        rw [htr]
        have hc' := hc
        rw [centralInterval, mem_Icc] at hc'
        rcases le_total 0 t with h0t | h0t
        · rw [abs_of_nonneg h0t] at hts
          rw [indicator_of_mem (show t ∈ Icc s A.1 from ⟨hts.le, hc'.2⟩)]
          linarith
        · rw [abs_of_nonpos h0t] at hts
          rw [indicator_of_mem (show t ∈ Icc (-A.1) (-s) from ⟨hc'.1, by linarith⟩)]
          linarith
      · rw [timeRep, indicator_of_notMem hc, norm_zero]
        linarith
    · rw [indicator_of_notMem hE]
      linarith
  have hmass : bartaEdgeMass A.1 (timeRep A x) ≤
      (∫ t in Icc s A.1, ‖(F : ℝ → ℂ) t‖) + ∫ t in Icc (-A.1) (-s), ‖(F : ℝ → ℂ) t‖ := by
    unfold bartaEdgeMass
    rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc,
      ← integral_add hi1 hi2]
    exact integral_mono hE (hi1.add hi2) hpt
  have h1 := setIntegral_Icc_norm_le_sqrt (show s ≤ A.1 by linarith) F
  have h2 := setIntegral_Icc_norm_le_sqrt (show -A.1 ≤ -s by linarith) F
  have hFnorm : ‖F‖ = ‖ccmArchimedeanFormToAperture A x‖ := rfl
  have hlen : -s - -A.1 = A.1 - s := by ring
  rw [hlen] at h2
  have hsqrt : Real.sqrt (A.1 - s) = Real.sqrt 2 * Real.exp (-A.1) := by
    rw [hsb, bartaWidth, Real.sqrt_mul (by norm_num),
      show Real.exp (-2 * A.1) = Real.exp (-A.1) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf,
      Real.sqrt_sq (Real.exp_pos _).le]
  have hs2 : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hexp : Real.exp (-A.1) * Real.exp A.1 = 1 := by rw [← Real.exp_add]; simp
  have hFle : ‖F‖ ≤ Real.exp A.1 / 6 * N := by rw [hFnorm]; exact h
  have hF0 : 0 ≤ ‖F‖ := norm_nonneg _
  have hsq0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hem := Real.exp_pos (-A.1)
  calc bartaEdgeMass A.1 (timeRep A x)
      ≤ 2 * (Real.sqrt 2 * Real.exp (-A.1) * ‖F‖) := by
        rw [hsqrt] at h1 h2; linarith
    _ ≤ 2 * (Real.sqrt 2 * Real.exp (-A.1) * (Real.exp A.1 / 6 * N)) := by gcongr
    _ = Real.sqrt 2 / 3 * N * (Real.exp (-A.1) * Real.exp A.1) := by ring
    _ = Real.sqrt 2 / 3 * N := by rw [hexp, mul_one]
    _ ≤ 1 / 2 * N := by nlinarith

/-! ## The eigenvalue bound -/

/-- **Overlap bound.** There is `C` such that every eigenvector `x` at an aperture `b ≥ 1`
satisfies `|μ| |⟨x, Φχ_{b−w,w}⟩| ≤ C (1 + b) Φ(b − 2w) ∫|x|`. No sign condition is needed. -/
theorem exists_abs_eigenvalue_mul_overlap_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ A : SuzukiPositiveAperture, 1 ≤ A.1 → ∀ (x : CCMArchimedeanFormDomain A) (μ : ℝ),
      (∀ s : CCMComplexSmoothInteriorSource A, ccmRestrictedWeilForm A x s.toCCMFormVector =
        (μ : ℂ) * ∫ t, (starRingEnd ℂ) (timeRep A x t) * s t) →
      |μ| * ‖∫ t, (starRingEnd ℂ) (timeRep A x t) * bartaInnerAt A t‖ ≤
        C * (1 + A.1) * (bartaEdge A.1 * ∫ t, ‖timeRep A x t‖) := by
  obtain ⟨CE, hCE, hE⟩ := exists_bartaEdge_bound_formDomain
  obtain ⟨CF, hCF, hF⟩ := exists_bartaFar_bound
  refine ⟨CF + CE, by positivity, fun A hb x μ heig => ?_⟩
  have hw0 := bartaWidth_pos A.1
  have hab : A.1 ≤ (bartaAperture A.1 hb).1 := by show A.1 ≤ A.1 + 3; linarith
  obtain ⟨x', hx'⟩ := exists_ccmArchimedeanFormDomain_extension hab x
  have hval : (bartaSource (bartaAperture A.1 hb) (A.1 - bartaWidth A.1) (bartaWidth A.1) hw0
      (by show A.1 - bartaWidth A.1 < A.1 + 3; linarith)).toCCMFormVector.1 =
      (bartaInnerAt A).toCCMFormVector.1 :=
    toCCMFormVector_val_eq_of_coe_eq _ _ fun t => rfl
  have hnest := (ccmRestrictedWeilForm_eq_of_val_eq hab hx' hval).symm
  have hdecomp : (bartaSource (bartaAperture A.1 hb) (A.1 - bartaWidth A.1) (bartaWidth A.1) hw0
      (by show A.1 - bartaWidth A.1 < A.1 + 3; linarith)).toCCMFormVector =
      (bartaFarAt A.1 hb).toCCMFormVector - (bartaLayerAt A.1 hb).toCCMFormVector := by
    apply toCCMFormVector_eq_sub_of_coe_eq
    intro t
    rw [bartaSource_apply, bartaLayerAt_apply, bartaFarAt, bartaSource_apply, bartaLayerFn]
    push_cast
    ring
  have hmass : ∫ t, ‖timeRep (bartaAperture A.1 hb) x' t‖ = ∫ t, ‖timeRep A x t‖ :=
    integral_congr_ae ((timeRep_ae_eq_of_val_eq hab hx').mono fun t ht => by simp only [ht])
  have hQ : ‖ccmRestrictedWeilForm A x (bartaInnerAt A).toCCMFormVector‖ ≤
      (∫ t, ‖timeRep A x t‖) * (bartaEdge A.1 * (CF + CE * (1 + A.1))) := by
    rw [hnest, hdecomp, ccmRestrictedWeilForm_sub_right]
    have h1 := hF A.1 hb x'
    have h2 := hE A.1 hb x'
    rw [hmass] at h1 h2
    refine (norm_sub_le _ _).trans ((add_le_add h1 h2).trans (le_of_eq ?_))
    ring
  rw [heig (bartaInnerAt A), norm_mul, Complex.norm_real, Real.norm_eq_abs] at hQ
  refine hQ.trans ?_
  have hN0 : 0 ≤ ∫ t, ‖timeRep A x t‖ := integral_nonneg fun _ => norm_nonneg _
  have hΦ0 := (bartaEdge_pos A.1).le
  have hb0 : 0 ≤ A.1 := by linarith
  have h1 : CF + CE * (1 + A.1) ≤ (CF + CE) * (1 + A.1) := by nlinarith
  calc (∫ t, ‖timeRep A x t‖) * (bartaEdge A.1 * (CF + CE * (1 + A.1)))
      ≤ (∫ t, ‖timeRep A x t‖) * (bartaEdge A.1 * ((CF + CE) * (1 + A.1))) := by gcongr
    _ = (CF + CE) * (1 + A.1) * (bartaEdge A.1 * ∫ t, ‖timeRep A x t‖) := by ring

/-- **Eigenvalue bound for nonnegative eigenvectors.** There are `C` and `b₁` such that every
nonnegative eigenvector at an aperture `b ≥ b₁` whose edge mass is at most half its mass has
`|μ| ≤ C (1 + b)`. -/
theorem exists_abs_eigenvalue_le_of_nonneg : ∃ C b₁ : ℝ, 0 ≤ C ∧ 1 ≤ b₁ ∧
    ∀ A : SuzukiPositiveAperture, b₁ ≤ A.1 → ∀ (x : CCMArchimedeanFormDomain A) (μ : ℝ),
      (∀ s : CCMComplexSmoothInteriorSource A, ccmRestrictedWeilForm A x s.toCCMFormVector =
        (μ : ℂ) * ∫ t, (starRingEnd ℂ) (timeRep A x t) * s t) →
      (∀ t, (timeRep A x t).im = 0 ∧ 0 ≤ (timeRep A x t).re) →
      bartaEdgeMass A.1 (timeRep A x) ≤ (1 / 2) * ∫ t, ‖timeRep A x t‖ →
      ccmArchimedeanFormToAperture A x ≠ 0 →
      |μ| ≤ C * (1 + A.1) := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_eigenvalue_mul_overlap_le
  obtain ⟨b₀, hb₀, hmin⟩ := exists_riemannKernelReal_edge_min
  refine ⟨2 * C, max 1 (b₀ + 1), by positivity, le_max_left _ _,
    fun A hA x μ heig hpos hedge hne => ?_⟩
  have hb : 1 ≤ A.1 := le_trans (le_max_left _ _) hA
  have hb₀s : b₀ ≤ bartaInner A.1 := by
    have := bartaInner_ge hb
    have := le_trans (le_max_right _ _) hA
    linarith
  set N : ℝ := ∫ t, ‖timeRep A x t‖ with hN
  have hNpos : 0 < N := integral_norm_timeRep_pos hne
  set Φ₀ := bartaEdge A.1 with hΦ₀
  have hΦ₀pos : 0 < Φ₀ := bartaEdge_pos A.1
  have hov := bartaEdge_mul_le_re_overlap
    (fun t ht => hmin (bartaInner A.1) hb₀s t ht) x hpos
  have hov' : Φ₀ * (N / 2) ≤
      ‖∫ t, (starRingEnd ℂ) (timeRep A x t) * bartaInnerAt A t‖ := by
    refine le_trans ?_ ((Complex.re_le_norm _).trans le_rfl)
    refine le_trans ?_ hov
    apply mul_le_mul_of_nonneg_left _ hΦ₀pos.le
    linarith
  have hkey : |μ| * (Φ₀ * (N / 2)) ≤ C * (1 + A.1) * (Φ₀ * N) :=
    (mul_le_mul_of_nonneg_left hov' (abs_nonneg μ)).trans (hbound A hb x μ heig)
  have hpos' : 0 < Φ₀ * N := mul_pos hΦ₀pos hNpos
  by_contra hcon
  push Not at hcon
  have : 2 * C * (1 + A.1) * (Φ₀ * N) < |μ| * (Φ₀ * N) := mul_lt_mul_of_pos_right hcon hpos'
  nlinarith

/-! ## The capstone -/

/-- **Nonnegative ground states force RH.** If for all large apertures some full ground state is
nonnegative with edge mass at most half of its mass, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_nonneg_fullGrounds {B₀ : ℝ}
    (h : ∀ A : SuzukiPositiveAperture, B₀ ≤ A.1 → ∃ x : CCMArchimedeanFormDomain A,
      IsFullGround A x ∧ ccmArchimedeanFormToAperture A x ≠ 0 ∧
      (∀ t, (timeRep A x t).im = 0 ∧ 0 ≤ (timeRep A x t).re) ∧
      bartaEdgeMass A.1 (timeRep A x) ≤ (1 / 2) * ∫ t, ‖timeRep A x t‖) :
    RiemannHypothesis := by
  obtain ⟨C, b₁, hC, hb₁, hbound⟩ := exists_abs_eigenvalue_le_of_nonneg
  set B₁ := max B₀ b₁ with hB₁
  have hB₁1 : 1 ≤ B₁ := le_trans hb₁ (le_max_right _ _)
  have hlow : ∀ A : SuzukiPositiveAperture, B₁ ≤ A.1 →
      -(C * (1 + A.1)) ≤ ccmRestrictedWeilGroundEnergy A := by
    intro A hA
    obtain ⟨x, hground, hne, hpos, hedge⟩ := h A (le_trans (le_max_left _ _) hA)
    have hμ := hbound A (le_trans (le_max_right _ _) hA) x (ccmRestrictedWeilGroundEnergy A)
      (fun s => formEigen_of_isFullGround A hground s) hpos hedge hne
    linarith [neg_abs_le (ccmRestrictedWeilGroundEnergy A)]
  apply riemannHypothesis_of_polarGroundEnergy_subexponential
  intro ε hε
  have hε' : 0 < 1 + 1 / ε := by positivity
  refine ⟨C * (1 + B₁) * (1 + 1 / ε), by positivity, fun B => ?_⟩
  have hB0 : 0 < B.1 := B.2
  have hexp1 : 1 ≤ Real.exp (ε * B.1) := Real.one_le_exp (by positivity)
  have hexp2 : 1 + ε * B.1 ≤ Real.exp (ε * B.1) := by
    have := Real.add_one_le_exp (ε * B.1); linarith
  refine le_trans ?_ (ccmRestrictedWeilGroundEnergy_le_polar B)
  rcases le_total B₁ B.1 with hB | hB
  · -- large apertures: the polynomial bound
    have h1 := hlow B hB
    have hpoly : 1 + B.1 ≤ (1 + 1 / ε) * Real.exp (ε * B.1) := by
      have hεB : (1 + 1 / ε) * (1 + ε * B.1) = 1 + B.1 + (1 / ε + ε * B.1) := by
        field_simp; ring
      have : 0 ≤ 1 / ε + ε * B.1 := by positivity
      nlinarith
    have hC1 : C * (1 + B.1) ≤ C * (1 + B₁) * (1 + 1 / ε) * Real.exp (ε * B.1) := by
      calc C * (1 + B.1) ≤ C * ((1 + 1 / ε) * Real.exp (ε * B.1)) :=
            mul_le_mul_of_nonneg_left hpoly hC
        _ = C * 1 * ((1 + 1 / ε) * Real.exp (ε * B.1)) := by ring
        _ ≤ C * (1 + B₁) * ((1 + 1 / ε) * Real.exp (ε * B.1)) := by
            gcongr; linarith
        _ = _ := by ring
    linarith
  · -- small apertures: antitonicity
    set A₁ : SuzukiPositiveAperture := ⟨B₁, by linarith⟩ with hA₁
    have h1 := hlow A₁ le_rfl
    have h2 := ccmRestrictedWeilGroundEnergy_antitone (a := B) (b := A₁) hB
    have hC1 : C * (1 + B₁) ≤ C * (1 + B₁) * (1 + 1 / ε) * Real.exp (ε * B.1) := by
      have h0 : 0 ≤ C * (1 + B₁) := by positivity
      have h3 : 1 ≤ (1 + 1 / ε) * Real.exp (ε * B.1) := by
        have : 1 ≤ 1 + 1 / ε := by have := one_div_pos.mpr hε; linarith
        nlinarith
      calc C * (1 + B₁) = C * (1 + B₁) * 1 := (mul_one _).symm
        _ ≤ C * (1 + B₁) * ((1 + 1 / ε) * Real.exp (ε * B.1)) :=
            mul_le_mul_of_nonneg_left h3 h0
        _ = _ := by ring
    have : -(C * (1 + A₁.1)) = -(C * (1 + B₁)) := rfl
    linarith

/-- **Ground states not almost orthogonal to Riemann's kernel force RH.** If for every `ε > 0` and
all large apertures `b` some full ground state `x` has `|⟨x, Φχ_{b−w,w}⟩| ≥ e^{−εb} Φ(b − 2w) ∫|x|`,
then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_fullGrounds_overlap
    (h : ∀ ε : ℝ, 0 < ε → ∃ B₀ : ℝ, ∀ A : SuzukiPositiveAperture, B₀ ≤ A.1 →
      ∃ x : CCMArchimedeanFormDomain A, IsFullGround A x ∧
        ccmArchimedeanFormToAperture A x ≠ 0 ∧
        Real.exp (-(ε * A.1)) * (bartaEdge A.1 * ∫ t, ‖timeRep A x t‖) ≤
          ‖∫ t, (starRingEnd ℂ) (timeRep A x t) * bartaInnerAt A t‖) :
    RiemannHypothesis := by
  obtain ⟨C, hC, hbound⟩ := exists_abs_eigenvalue_mul_overlap_le
  apply riemannHypothesis_of_polarGroundEnergy_subexponential
  intro ε hε
  obtain ⟨B₀, hB₀⟩ := h (ε / 2) (by positivity)
  set B₁ := max B₀ 1 with hB₁
  have hB₁1 : 1 ≤ B₁ := le_max_right _ _
  have hlow : ∀ A : SuzukiPositiveAperture, B₁ ≤ A.1 →
      -(C * (1 + A.1) * Real.exp (ε / 2 * A.1)) ≤ ccmRestrictedWeilGroundEnergy A := by
    intro A hA
    have hb : 1 ≤ A.1 := le_trans hB₁1 hA
    obtain ⟨x, hground, hne, hov⟩ := hB₀ A (le_trans (le_max_left _ _) hA)
    have hk := hbound A hb x _ fun s => formEigen_of_isFullGround A hground s
    have hNpos : 0 < ∫ t, ‖timeRep A x t‖ := integral_norm_timeRep_pos hne
    have hP : 0 < bartaEdge A.1 * ∫ t, ‖timeRep A x t‖ := mul_pos (bartaEdge_pos A.1) hNpos
    have hE := Real.exp_pos (-(ε / 2 * A.1))
    have hchain : |ccmRestrictedWeilGroundEnergy A| *
        (Real.exp (-(ε / 2 * A.1)) * (bartaEdge A.1 * ∫ t, ‖timeRep A x t‖)) ≤
        C * (1 + A.1) * (bartaEdge A.1 * ∫ t, ‖timeRep A x t‖) :=
      (mul_le_mul_of_nonneg_left hov (abs_nonneg _)).trans hk
    have hμ : |ccmRestrictedWeilGroundEnergy A| * Real.exp (-(ε / 2 * A.1)) ≤ C * (1 + A.1) := by
      have h2 : (|ccmRestrictedWeilGroundEnergy A| * Real.exp (-(ε / 2 * A.1))) *
          (bartaEdge A.1 * ∫ t, ‖timeRep A x t‖) ≤
          (C * (1 + A.1)) * (bartaEdge A.1 * ∫ t, ‖timeRep A x t‖) := by
        calc (|ccmRestrictedWeilGroundEnergy A| * Real.exp (-(ε / 2 * A.1))) *
              (bartaEdge A.1 * ∫ t, ‖timeRep A x t‖)
            = |ccmRestrictedWeilGroundEnergy A| *
              (Real.exp (-(ε / 2 * A.1)) * (bartaEdge A.1 * ∫ t, ‖timeRep A x t‖)) := by ring
          _ ≤ _ := hchain
      exact le_of_mul_le_mul_right h2 hP
    have hexp : Real.exp (-(ε / 2 * A.1)) * Real.exp (ε / 2 * A.1) = 1 := by
      rw [← Real.exp_add]; simp
    have hμ' : |ccmRestrictedWeilGroundEnergy A| ≤ C * (1 + A.1) * Real.exp (ε / 2 * A.1) := by
      have := mul_le_mul_of_nonneg_right hμ (Real.exp_pos (ε / 2 * A.1)).le
      calc |ccmRestrictedWeilGroundEnergy A|
          = |ccmRestrictedWeilGroundEnergy A| *
            (Real.exp (-(ε / 2 * A.1)) * Real.exp (ε / 2 * A.1)) := by rw [hexp, mul_one]
        _ = |ccmRestrictedWeilGroundEnergy A| * Real.exp (-(ε / 2 * A.1)) *
            Real.exp (ε / 2 * A.1) := by ring
        _ ≤ _ := this
    linarith [neg_abs_le (ccmRestrictedWeilGroundEnergy A)]
  set K : ℝ := C * (1 + B₁) * Real.exp (ε / 2 * B₁) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨C * (1 + 2 / ε) + K, by positivity, fun B => ?_⟩
  have hB0 : 0 < B.1 := B.2
  have hexp1 : 1 ≤ Real.exp (ε * B.1) := Real.one_le_exp (by positivity)
  refine le_trans ?_ (ccmRestrictedWeilGroundEnergy_le_polar B)
  rcases le_total B₁ B.1 with hB | hB
  · have h1 := hlow B hB
    have hhalf : 1 + ε / 2 * B.1 ≤ Real.exp (ε / 2 * B.1) := by
      have := Real.add_one_le_exp (ε / 2 * B.1); linarith
    have hpoly : 1 + B.1 ≤ (1 + 2 / ε) * Real.exp (ε / 2 * B.1) := by
      have heq : (1 + 2 / ε) * (1 + ε / 2 * B.1) = 1 + B.1 + (2 / ε + ε / 2 * B.1) := by
        field_simp; ring
      have : 0 ≤ 2 / ε + ε / 2 * B.1 := by positivity
      have hm := mul_le_mul_of_nonneg_left hhalf (show 0 ≤ 1 + 2 / ε by positivity)
      linarith
    have hsplit : Real.exp (ε / 2 * B.1) * Real.exp (ε / 2 * B.1) = Real.exp (ε * B.1) := by
      rw [← Real.exp_add]; ring_nf
    have hC1 : C * (1 + B.1) * Real.exp (ε / 2 * B.1) ≤
        (C * (1 + 2 / ε) + K) * Real.exp (ε * B.1) := by
      calc C * (1 + B.1) * Real.exp (ε / 2 * B.1)
          ≤ C * ((1 + 2 / ε) * Real.exp (ε / 2 * B.1)) * Real.exp (ε / 2 * B.1) := by gcongr
        _ = C * (1 + 2 / ε) * Real.exp (ε * B.1) := by rw [← hsplit]; ring
        _ ≤ (C * (1 + 2 / ε) + K) * Real.exp (ε * B.1) := by gcongr; linarith
    linarith
  · set A₁ : SuzukiPositiveAperture := ⟨B₁, by linarith⟩ with hA₁
    have h1 := hlow A₁ le_rfl
    have h2 := ccmRestrictedWeilGroundEnergy_antitone (a := B) (b := A₁) hB
    have hC1 : K ≤ (C * (1 + 2 / ε) + K) * Real.exp (ε * B.1) := by
      have h0 : 0 ≤ C * (1 + 2 / ε) := by positivity
      nlinarith
    have : -(C * (1 + A₁.1) * Real.exp (ε / 2 * A₁.1)) = -K := rfl
    linarith

/-- **Nonnegative ground states force RH, `L²` form.** If for all large apertures `b` some full
ground state `x` is nonnegative with `‖x‖₂ ≤ e^{b} ‖x‖₁ / 6`, then the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_nonneg_fullGrounds_of_norm_le {B₀ : ℝ}
    (h : ∀ A : SuzukiPositiveAperture, B₀ ≤ A.1 → ∃ x : CCMArchimedeanFormDomain A,
      IsFullGround A x ∧ ccmArchimedeanFormToAperture A x ≠ 0 ∧
      (∀ t, (timeRep A x t).im = 0 ∧ 0 ≤ (timeRep A x t).re) ∧
      ‖ccmArchimedeanFormToAperture A x‖ ≤ Real.exp A.1 / 6 * ∫ t, ‖timeRep A x t‖) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_nonneg_fullGrounds (B₀ := max B₀ 1) fun A hA => ?_
  obtain ⟨x, hground, hne, hpos, hnorm⟩ := h A (le_trans (le_max_left _ _) hA)
  exact ⟨x, hground, hne, hpos,
    bartaEdgeMass_le_half_of_norm_le (le_trans (le_max_right _ _) hA) x hnorm⟩

end

end RHTower
