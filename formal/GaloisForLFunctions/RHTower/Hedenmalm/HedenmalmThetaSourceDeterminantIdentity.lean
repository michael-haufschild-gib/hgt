import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaRealResolventTrace
import GaloisForLFunctions.HTGeometry.CompactFourierEntire

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

open GaloisForLFunctions.HTGeometry
open HedenmalmQuantile HedenmalmHilbertSchmidt ContinuousLinearMap

local instance hedenmalmThetaSourceDeterminantIdentityLocalInst1 : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩

/-- Evenness forces the centered completed Xi derivative to vanish at the origin. -/
theorem deriv_XiC_at_zero : deriv XiC 0 = 0 := by
  have hneg : HasDerivAt (fun z : ℂ => -z) (-1) 0 :=
    (hasDerivAt_id (0 : ℂ)).neg
  have hcomp := XiC_differentiable.differentiableAt.hasDerivAt.comp 0 hneg
  have hfun : XiC ∘ (fun z : ℂ => -z) = XiC := by
    funext z
    exact XiC_even z
  rw [hfun] at hcomp
  have hder := hcomp.deriv
  simp only [neg_zero] at hder
  linear_combination (1 / 2 : ℂ) * hder

/-- On a nondegenerate real neighborhood of the origin, the entire source determinant is the
normalized completed Xi function. -/
theorem exists_thetaSourceEntireDet2_eq_XiC_normalized_ofReal :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, |t| < ρ →
      thetaSourceEntireDet2 (t : ℂ) = XiC (t : ℂ) / XiC 0 := by
  let K := -thetaKernelMatrix
  obtain ⟨_, rD, hrD, hrDK, hD⟩ :=
    (isRegularizedDet_entireDet2 isHS_neg_thetaKernelMatrix)
  have hXiCont : ContinuousAt (fun t : ℝ => XiC (t : ℂ)) 0 := by
    exact XiC_differentiable.continuous.continuousAt.comp
      Complex.ofRealCLM.continuous.continuousAt
  obtain ⟨rXi, hrXi, hXi⟩ := Metric.eventually_nhds_iff.mp
    (hXiCont.eventually_ne XiC_zero_ne)
  let rB : ℝ := 1 / (‖thetaKernelOperator‖ + 1)
  have hrB : 0 < rB := by
    dsimp [rB]
    positivity
  have hrBB : rB * ‖thetaKernelOperator‖ < 1 := by
    dsimp [rB]
    rw [one_div, inv_mul_eq_div]
    exact (div_lt_one (by positivity)).mpr (by linarith [norm_nonneg thetaKernelOperator])
  let ρ : ℝ := min rXi (min rD rB)
  have hρ : 0 < ρ := lt_min hrXi (lt_min hrD hrB)
  have hρXi : ρ ≤ rXi := min_le_left _ _
  have hρD : ρ ≤ rD := (min_le_right _ _).trans (min_le_left _ _)
  have hρB : ρ ≤ rB := (min_le_right _ _).trans (min_le_right _ _)
  let q : ℝ → ℂ :=
    (fun t : ℝ => HilbertSchmidt.fredholmDet K (t : ℂ)) /
      (fun t : ℝ => XiC (t : ℂ))
  have hdata (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) ρ) :
      |t| * ‖thetaKernelOperator‖ < 1 ∧
      ‖(t : ℂ)‖ * HilbertSchmidt.hsNorm K < 1 ∧
      XiC (t : ℂ) ≠ 0 ∧
      (t : ℂ) ∈ Metric.ball (0 : ℂ) rD := by
    have htρ : |t| < ρ := by
      simpa [Metric.mem_ball, Real.dist_eq] using ht
    have htB : |t| < rB := htρ.trans_le hρB
    have htD : |t| < rD := htρ.trans_le hρD
    have htXi : dist t 0 < rXi := by
      simpa [Real.dist_eq, abs_sub_comm] using htρ.trans_le hρXi
    refine ⟨?_, ?_, hXi htXi, ?_⟩
    · exact (mul_le_mul_of_nonneg_right htB.le
        (norm_nonneg thetaKernelOperator)).trans_lt hrBB
    · rw [Complex.norm_real]
      exact (mul_le_mul_of_nonneg_right htD.le
        (HilbertSchmidt.hsNorm_nonneg K)).trans_lt hrDK
    · simpa [Metric.mem_ball, Complex.dist_eq, Complex.norm_real] using htD
  have hqderiv (t : ℝ) (ht : t ∈ Metric.ball (0 : ℝ) ρ) :
      HasDerivAt q 0 t := by
    obtain ⟨htB, htK, htXi, htD⟩ := hdata t ht
    have hroot : rootA thetaSource (t : ℂ) 1 ≠ 0 := by
      intro hzero
      have hsource : xiC thetaSource (t : ℂ) = 0 :=
        (rootA_one_eq_zero_iff (S := thetaSource) (t : ℂ)).mp hzero
      rw [xiC_thetaSource_all] at hsource
      exact htXi hsource
    have htrace : HilbertSchmidt.resolventTrace K (t : ℂ) =
        -(deriv XiC (t : ℂ) / XiC (t : ℂ)) := by
      by_cases ht0 : t = 0
      · subst t
        simp [K, HilbertSchmidt.resolventTrace, deriv_XiC_at_zero]
      · rw [show K = -thetaKernelMatrix by rfl,
          resolventTrace_neg_thetaKernelMatrix_ofReal_eq_thetaRealRegularizedTrace
            htB htK,
          thetaRealRegularizedTrace_eq_neg_logDeriv_XiC ht0 htB hroot]
    have hFredC := HilbertSchmidt.hasDerivAt_fredholmDet
      isHS_neg_thetaKernelMatrix rD hrDK (t : ℂ) htD
    change HasDerivAt (fun z : ℂ => HilbertSchmidt.fredholmDet K z)
      (HilbertSchmidt.fredholmDet K (t : ℂ) *
        (-HilbertSchmidt.resolventTrace K (t : ℂ))) (t : ℂ) at hFredC
    have hFred := hFredC.comp_ofReal
    have hXiDeriv :=
      XiC_differentiable.differentiableAt.hasDerivAt.comp_ofReal (z := t)
    have hFred' : HasDerivAt
        (fun s : ℝ => HilbertSchmidt.fredholmDet K (s : ℂ))
        (HilbertSchmidt.fredholmDet K (t : ℂ) *
          (deriv XiC (t : ℂ) / XiC (t : ℂ))) t := by
      convert hFred using 1
      rw [htrace]
      ring
    have hquot := hFred'.div hXiDeriv htXi
    have hcoeff :
        (HilbertSchmidt.fredholmDet K (t : ℂ) *
            (deriv XiC (t : ℂ) / XiC (t : ℂ)) * XiC (t : ℂ) -
          HilbertSchmidt.fredholmDet K (t : ℂ) * deriv XiC (t : ℂ)) /
            XiC (t : ℂ) ^ 2 = 0 := by
      field_simp [htXi]
      ring
    simpa only [q, Pi.div_apply] using hquot.congr_deriv hcoeff
  have hqdiff : DifferentiableOn ℝ q (Metric.ball (0 : ℝ) ρ) :=
    fun t ht => (hqderiv t ht).differentiableAt.differentiableWithinAt
  have hqzero : Set.EqOn (deriv q) 0 (Metric.ball (0 : ℝ) ρ) := by
    intro t ht
    simpa using (hqderiv t ht).deriv
  obtain ⟨c, hc⟩ := Metric.isOpen_ball.exists_is_const_of_deriv_eq_zero
    (convex_ball (0 : ℝ) ρ).isPreconnected hqdiff hqzero
  refine ⟨ρ, hρ, fun t ht => ?_⟩
  have htBall : t ∈ Metric.ball (0 : ℝ) ρ := by
    simpa [Metric.mem_ball, Real.dist_eq] using ht
  have hzeroBall : (0 : ℝ) ∈ Metric.ball (0 : ℝ) ρ := by
    simpa using hρ
  have hqt : q t = q 0 := (hc t htBall).trans (hc 0 hzeroBall).symm
  obtain ⟨_, _, htXi, htD⟩ := hdata t htBall
  have hlocal := hD (t : ℂ) htD
  change thetaSourceEntireDet2 (t : ℂ) = _
  rw [thetaSourceEntireDet2, show -thetaKernelMatrix = K by rfl, hlocal]
  change HilbertSchmidt.fredholmDet K (t : ℂ) = _
  change HilbertSchmidt.fredholmDet K (t : ℂ) / XiC (t : ℂ) =
    HilbertSchmidt.fredholmDet K 0 / XiC 0 at hqt
  have hFred0 : HilbertSchmidt.fredholmDet K 0 = 1 := by
    simp [HilbertSchmidt.fredholmDet, HilbertSchmidt.fredholmExp]
  rw [hFred0] at hqt
  field_simp [htXi, XiC_zero_ne] at hqt ⊢
  exact hqt

/-- **Exact determinant identity.**  The fixed source inverse has Hilbert--Carleman determinant
`XiC(z) / XiC(0)` on the whole complex plane. -/
theorem thetaSourceEntireDet2_eq_XiC_normalized (z : ℂ) :
    thetaSourceEntireDet2 z = XiC z / XiC 0 := by
  obtain ⟨ρ, hρ, hlocal⟩ :=
    exists_thetaSourceEntireDet2_eq_XiC_normalized_ofReal
  let G : ℂ → ℂ := fun w => thetaSourceEntireDet2 w - XiC w / XiC 0
  have hG : Differentiable ℂ G :=
    differentiable_thetaSourceEntireDet2.sub (XiC_differentiable.div_const _)
  have hzero : ∀ t : ℝ, |t - 0| < ρ → G (t : ℂ) = 0 := by
    intro t ht
    dsimp [G]
    rw [hlocal t (by simpa using ht)]
    ring
  have := GaloisForLFunctions.HTGeometry.entire_eq_zero_of_vanishing_on_real_interval
    hG hρ hzero z
  dsimp [G] at this
  exact sub_eq_zero.mp this

end

end RHTower.HedenmalmThetaSource

