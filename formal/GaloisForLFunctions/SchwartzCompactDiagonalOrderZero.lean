import GaloisForLFunctions.SchwartzPositiveCompactDiagonal

/-!
# Local order-zero bound for the compact diagonal functional

Positivity on compact smooth tests gives the classical order-zero estimate directly.  A real
canonical cutoff supplies the two nonnegative envelopes `M * chi ± h`, where `M` is the zeroth
Schwartz seminorm of `h`.  Their positivity bounds the stabilized local diagonal functional by
the sup norm on every fixed compact packet.
-/

open Complex Function Filter Set
open scoped SchwartzMap FourierTransform Topology Polynomial ContDiff

noncomputable section

namespace SchwartzMap

/-- Real-valued canonical interval cutoff. -/
def realCompactIntervalCutoff (R : ℝ) : SchwartzMap ℝ ℝ := by
  let b : ContDiffBump (0 : ℝ) :=
    ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  exact b.hasCompactSupport.toSchwartzMap b.contDiff

@[simp] theorem realCompactIntervalCutoff_apply_of_abs_le_add_one
    (R : ℝ) {t : ℝ} (ht : |t| ≤ |R| + 1) :
    realCompactIntervalCutoff R t = 1 := by
  rw [realCompactIntervalCutoff]
  let b : ContDiffBump (0 : ℝ) :=
    ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  change b t = 1
  apply b.one_of_mem_closedBall
  rw [Metric.mem_closedBall]
  simpa only [Real.dist_0_eq_abs] using ht

@[simp] theorem realCompactIntervalCutoff_nonnegative (R : ℝ) (t : ℝ) :
    0 ≤ realCompactIntervalCutoff R t := by
  rw [realCompactIntervalCutoff]
  let b : ContDiffBump (0 : ℝ) :=
    ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  exact b.nonneg

@[simp] theorem realToComplexSchwartz_realCompactIntervalCutoff (R : ℝ) :
    realToComplexSchwartz (realCompactIntervalCutoff R) = compactIntervalCutoff R := by
  ext t
  rfl

@[simp] theorem realCompactIntervalCutoff_tsupport (R : ℝ) :
    tsupport (realCompactIntervalCutoff R) = {t : ℝ | |t| ≤ |R| + 2} := by
  have hcomplex := congrArg (fun f : SchwartzMap ℝ ℂ => tsupport f)
    (realToComplexSchwartz_realCompactIntervalCutoff R)
  change tsupport (realToComplexSchwartz (realCompactIntervalCutoff R)) =
    tsupport (compactIntervalCutoff R) at hcomplex
  rw [compactIntervalCutoff_tsupport] at hcomplex
  have heq : tsupport (realToComplexSchwartz (realCompactIntervalCutoff R)) =
      tsupport (realCompactIntervalCutoff R) := by
    rw [tsupport, tsupport]
    congr 1
    ext t
    simp only [Function.mem_support, realToComplexSchwartz_apply, ne_eq]
    norm_cast
  rwa [heq] at hcomplex

/-- The two real cutoff envelopes `M*chi ± h` are nonnegative when `M` is the zeroth Schwartz
seminorm of a packet supported in the cutoff core. -/
theorem cutoff_envelopes_nonnegative
    (h : SchwartzMap ℝ ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hh : tsupport h ⊆ {t : ℝ | |t| ≤ R}) (t : ℝ) :
    0 ≤ (SchwartzMap.seminorm ℝ 0 0 h) * realCompactIntervalCutoff R t + h t ∧
      0 ≤ (SchwartzMap.seminorm ℝ 0 0 h) * realCompactIntervalCutoff R t - h t := by
  let M : ℝ := SchwartzMap.seminorm ℝ 0 0 h
  have hM : 0 ≤ M := by positivity
  by_cases ht : t ∈ tsupport h
  · have hχ : realCompactIntervalCutoff R t = 1 := by
      apply realCompactIntervalCutoff_apply_of_abs_le_add_one
      have habs : |t| ≤ R := hh ht
      rw [abs_of_nonneg hR]
      linarith
    have hnorm := SchwartzMap.norm_le_seminorm ℝ h t
    rw [Real.norm_eq_abs] at hnorm
    change 0 ≤ M * realCompactIntervalCutoff R t + h t ∧
      0 ≤ M * realCompactIntervalCutoff R t - h t
    rw [hχ, mul_one]
    exact ⟨by linarith [neg_abs_le (h t)], by linarith [le_abs_self (h t)]⟩
  · have hzero : h t = 0 := image_eq_zero_of_notMem_tsupport ht
    rw [hzero, add_zero, sub_zero]
    exact ⟨mul_nonneg hM (realCompactIntervalCutoff_nonnegative R t),
      mul_nonneg hM (realCompactIntervalCutoff_nonnegative R t)⟩

/-- Both cutoff envelopes remain inside the cutoff support. -/
theorem cutoff_envelopes_tsupport_subset
    (h : SchwartzMap ℝ ℝ) {R : ℝ} (hR : 0 ≤ R)
    (hh : tsupport h ⊆ {t : ℝ | |t| ≤ R}) :
    tsupport ((SchwartzMap.seminorm ℝ 0 0 h) • realCompactIntervalCutoff R + h) ⊆
        {t : ℝ | |t| ≤ R + 2} ∧
      tsupport ((SchwartzMap.seminorm ℝ 0 0 h) • realCompactIntervalCutoff R - h) ⊆
        {t : ℝ | |t| ≤ R + 2} := by
  have hχ : tsupport (realCompactIntervalCutoff R) ⊆ {t : ℝ | |t| ≤ R + 2} := by
    rw [realCompactIntervalCutoff_tsupport]
    rw [abs_of_nonneg hR]
  have hh' : tsupport h ⊆ {t : ℝ | |t| ≤ R + 2} := by
    intro t ht
    have hle : |t| ≤ R := hh ht
    change |t| ≤ R + 2
    linarith
  let M : ℝ := SchwartzMap.seminorm ℝ 0 0 h
  have hsmul : tsupport (M • realCompactIntervalCutoff R) ⊆
      {t : ℝ | |t| ≤ R + 2} := by
    have hs := tsupport_smul_subset_right (fun _t : ℝ => M)
      (realCompactIntervalCutoff R)
    have hs' : tsupport (M • realCompactIntervalCutoff R) ⊆
        tsupport (realCompactIntervalCutoff R) := by
      simpa only [Pi.smul_apply, smul_eq_mul] using hs
    exact hs'.trans hχ
  constructor
  · exact (tsupport_add (M • realCompactIntervalCutoff R) h).trans
      (union_subset hsmul hh')
  · exact (tsupport_sub (M • realCompactIntervalCutoff R) h).trans
      (union_subset hsmul hh')

/-- **Local order-zero estimate.** On every fixed compact packet the stabilized diagonal
functional is bounded by the zeroth Schwartz seminorm, with an explicit positive cutoff mass. -/
theorem ContinuousSchwartzSesquilinearForm.compactIntervalDiagonalFunctional_norm_le_seminorm_zero
    (Q : ContinuousSchwartzSesquilinearForm) (hQ : Q.MomentumSymmetric)
    (hQnonneg : Q.IsNonnegative) (h : SchwartzMap ℝ ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hh : tsupport h ⊆ {t : ℝ | |t| ≤ R}) :
    ‖Q.compactIntervalDiagonalFunctional (R + 4) (realToComplexSchwartz h)‖ ≤
      SchwartzMap.seminorm ℝ 0 0 h *
        (Q.compactIntervalDiagonalFunctional (R + 4)
          (realToComplexSchwartz (realCompactIntervalCutoff R))).re := by
  let M : ℝ := SchwartzMap.seminorm ℝ 0 0 h
  let χ : SchwartzMap ℝ ℝ := realCompactIntervalCutoff R
  let hpkt : SchwartzMap ℝ ℝ := M • χ + h
  let mpkt : SchwartzMap ℝ ℝ := M • χ - h
  let L := Q.compactIntervalDiagonalFunctional (R + 4)
  let a : ℂ := L (realToComplexSchwartz h)
  let c : ℂ := L (realToComplexSchwartz χ)
  have hsupp := cutoff_envelopes_tsupport_subset h hR hh
  have hpnonneg : ∀ t, 0 ≤ hpkt t := by
    intro t
    exact (cutoff_envelopes_nonnegative h hR hh t).1
  have hmnonneg : ∀ t, 0 ≤ mpkt t := by
    intro t
    exact (cutoff_envelopes_nonnegative h hR hh t).2
  have hp := Q.compactIntervalDiagonalFunctional_nonnegative_real hQ hQnonneg
    hpkt hpnonneg (show 0 ≤ R + 2 by linarith) hsupp.1
  have hm := Q.compactIntervalDiagonalFunctional_nonnegative_real hQ hQnonneg
    mpkt hmnonneg (show 0 ≤ R + 2 by linarith) hsupp.2
  have hpc : realToComplexSchwartz hpkt = (M : ℂ) • realToComplexSchwartz χ +
      realToComplexSchwartz h := by
    ext t
    change ((M * χ t + h t : ℝ) : ℂ) =
      (M : ℂ) * (χ t : ℂ) + (h t : ℂ)
    push_cast
    rfl
  have hmc : realToComplexSchwartz mpkt = (M : ℂ) • realToComplexSchwartz χ -
      realToComplexSchwartz h := by
    ext t
    change ((M * χ t - h t : ℝ) : ℂ) =
      (M : ℂ) * (χ t : ℂ) - (h t : ℂ)
    push_cast
    rfl
  have hrad : R + 2 + 2 = R + 4 := by ring
  rw [hrad] at hp hm
  change 0 ≤ (L (realToComplexSchwartz hpkt)).re ∧
      (L (realToComplexSchwartz hpkt)).im = 0 at hp
  change 0 ≤ (L (realToComplexSchwartz mpkt)).re ∧
      (L (realToComplexSchwartz mpkt)).im = 0 at hm
  rw [hpc, map_add, map_smul] at hp
  rw [hmc, map_sub, map_smul] at hm
  change 0 ≤ ((M : ℂ) * c + a).re ∧ ((M : ℂ) * c + a).im = 0 at hp
  change 0 ≤ ((M : ℂ) * c - a).re ∧ ((M : ℂ) * c - a).im = 0 at hm
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, ofReal_re, ofReal_im, zero_mul, sub_zero] at hp hm
  have haim : a.im = 0 := by linarith [hp.2, hm.2]
  have halower : -(M * c.re) ≤ a.re := by linarith [hp.1]
  have haupper : a.re ≤ M * c.re := by linarith [hm.1]
  have hanorm : ‖a‖ = |a.re| := by
    have ha : a = (a.re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [haim]
    rw [ha]
    exact norm_real _
  change ‖a‖ ≤ M * c.re
  rw [hanorm]
  exact abs_le.mpr ⟨halower, haupper⟩

end SchwartzMap

