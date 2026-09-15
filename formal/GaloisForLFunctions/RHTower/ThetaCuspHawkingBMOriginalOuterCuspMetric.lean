import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalOuterCuspBoundary
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalOuterCuspForcing

/-! Full original moving metric restoration through the outer endpoint. -/
open Set Filter Topology MeasureTheory
namespace RHTower.D4BMOriginalOuterCuspMetric
open D4BMModularCore D4BMOriginalFullMetricCollar D4BMOriginalFullMetricDifference
open D4BMOriginalSourceRadialRestoration D4BMOriginalCompleteTransfer
open D4BMOriginalOuterCuspSource D4BMOriginalOuterCuspBoundary D4BMOriginalOuterCuspForcing
noncomputable section
set_option autoImplicit false

/-- The complete original finite-cusp metric discrepancy is separately admitted
on the full finite outer interval. Its actual moving time boundary is retained,
and its integral tends uniformly to zero with cusp removal. -/
theorem full_outer_static_metric_restoration (q : XiZeroCopy) (br : Bool) (amp : ℂ) :
    ∃ G : ℝ,0≤G ∧ ∀ w : ℂ,w.im≠0 → G+1≤w.re → ∀ A : ℝ,0<A →
      ∃ eta : ℝ→ℝ,(∀ k,0≤eta k) ∧ Tendsto eta atTop (𝓝 0) ∧
        ∀ a T k : ℝ,0<a → 0≤k → 4≤Real.exp k →
          IntervalIntegrable (fun L => metricDifference q br amp w a (max a (T-L/2)) L k) volume 0 A ∧
          ‖∫ L in (0:ℝ)..A,metricDifference q br amp w a (max a (T-L/2)) L k/2‖≤eta k := by
  obtain ⟨G1,hG1,h1⟩ := outer_static_source_restoration q br amp 1
  obtain ⟨G2,hG2,h2⟩ := outer_static_boundary_restoration q br amp 1
  refine ⟨max G1 G2,le_max_of_le_left hG1,?_⟩
  intro w hwi hw A hA
  have hw1 : G1+1≤w.re := by linarith [le_max_left G1 G2]
  have hw2 : G2+1≤w.re := by linarith [le_max_right G1 G2]
  obtain ⟨Cs,hCs,hs⟩ := h1 w hw1 A hA
  obtain ⟨Cb,hCb,hb⟩ := h2 w hwi hw2 A hA
  obtain ⟨ef,hef,htf,hf⟩ := outer_static_forcing_restoration q br amp w (by linarith) A hA
  refine ⟨fun k => (Cs+Cb)*Real.exp (-k)+ef k,
    fun k => add_nonneg (mul_nonneg (add_nonneg hCs hCb) (Real.exp_nonneg _)) (hef k),?_,?_⟩
  · simpa only [Function.comp_def,mul_zero,zero_add] using!
      ((Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot).const_mul (Cs+Cb)).add htf
  · intro a T k ha hk hk4
    obtain ⟨hSi,hSn⟩ := hs a T k ha hk hk4
    obtain ⟨hBi,hBn⟩ := hb a T k ha hk
    obtain ⟨hFi,hFn⟩ := hf a T k ha
    let S := fun L => sourceFunctional q br amp w a (max a (T-L/2)) L k
    let F := fun L => forcingMoment q br amp w a (max a (T-L/2)) L k
    let B := fun L => radialBoundary q br amp w a (max a (T-L/2)) L k
    let D := fun L => metricDifference q br amp w a (max a (T-L/2)) L k
    have he (L : ℝ) (hL : L∈Ioc (0:ℝ) A) : D L=S L+F L+B L :=
      original_full_metric_difference q br amp w hwi a (max a (T-L/2)) L k ha (le_max_left _ _) hL.1 hk4
    have hsum : IntervalIntegrable (fun L => S L+F L+B L) volume 0 A := (hSi.add hFi).add hBi
    have hDi : IntervalIntegrable D volume 0 A := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le).mpr
      apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le hA.le).mp hsum).congr
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with L hL
      exact (he L hL).symm
    have hi : (∫ L in (0:ℝ)..A,D L/2)=
        (∫ L in (0:ℝ)..A,S L/2)+(∫ L in (0:ℝ)..A,F L/2)+(∫ L in (0:ℝ)..A,B L/2) := by
      have hi' : (∫ L in (0:ℝ)..A,D L)=(∫ L in (0:ℝ)..A,S L+F L+B L) := by
        simp only [intervalIntegral.integral_of_le hA.le]
        exact setIntegral_congr_fun measurableSet_Ioc he
      rw [intervalIntegral.integral_div,hi',intervalIntegral.integral_add (hSi.add hFi) hBi,
        intervalIntegral.integral_add hSi hFi]
      simp only [intervalIntegral.integral_div]
      ring
    refine ⟨hDi,?_⟩
    change ‖∫ L in (0:ℝ)..A,D L/2‖≤_
    rw [hi]
    calc
      _ ≤ (‖∫ L in (0:ℝ)..A,S L/2‖+‖∫ L in (0:ℝ)..A,F L/2‖)+‖∫ L in (0:ℝ)..A,B L/2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (Cs*Real.exp (-k)+ef k)+Cb*Real.exp (-k) := by
        exact add_le_add (add_le_add (by simpa only [Nat.cast_one,neg_mul,one_mul] using hSn) hFn)
          (by simpa only [Nat.cast_one,neg_mul,one_mul] using hBn)
      _ = _ := by ring

end
end RHTower.D4BMOriginalOuterCuspMetric
