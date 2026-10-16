import GaloisForLFunctions.HTGeometry.CompactMonicRootCovering
import Mathlib.Analysis.Meromorphic.Order

/-!
# Analytic root germs along real analytic coefficient paths

A simple complex root varies analytically with the complex coefficients.
Restricting scalars and pulling back along a real analytic path gives a real
analytic root germ. Local pointwise uniqueness also controls competing root
germs defined only on the punctured real parameter interval.
-/

open Filter Topology Polynomial
open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry
noncomputable section

theorem analytic_monic_root_germ {N : ℕ} {c : ℝ → Fin N → ℂ} {a : ℝ} {z : ℂ}
    (hc : AnalyticAt ℝ c a)
    (hz : (monicCoeffPolynomial N (c a)).eval z = 0)
    (hd : (derivative (monicCoeffPolynomial N (c a))).eval z ≠ 0) :
    ∃ r : ℝ → ℂ, AnalyticAt ℝ r a ∧ r a = z ∧
      (∀ᶠ t in 𝓝 a, (monicCoeffPolynomial N (c t)).eval (r t) = 0) ∧
      ∀ s : ℝ → ℂ, ContinuousAt s a → s a = z →
        (∀ᶠ t in 𝓝[≠] a, (monicCoeffPolynomial N (c t)).eval (s t) = 0) →
        r =ᶠ[𝓝[≠] a] s := by
  let F := monicCoeffRelation N
  have hF : AnalyticAt ℂ F (c a, z) := analyticAt_monicCoeffRelation N _
  have hF0 : F (c a, z) = 0 := by simpa only [F, monicCoeffRelation_eq_eval] using hz
  have cdf : ContDiffAt ℂ ω F (c a, z) := hF.contDiffAt
  have hi : (fderiv ℂ F (c a, z) ∘L (.inr ℂ (Fin N → ℂ) ℂ)).IsInvertible :=
    HolomorphicIFT.clm_invertible_of_apply_one_ne (by
      simpa only [F, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
        monicCoeffRelation_partial_snd] using hd)
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by decide
  let b : (Fin N → ℂ) → ℂ := cdf.implicitFunction hω hi
  have hb : AnalyticAt ℂ b (c a) := (cdf.contDiffAt_implicitFunction hω hi).analyticAt
  have hbR : AnalyticAt ℝ b (c a) := hb.restrictScalars
  refine ⟨fun t => b (c t), hbR.comp hc, cdf.implicitFunction_apply_self hω hi, ?_, ?_⟩
  · have he := hc.continuousAt.eventually (cdf.eventually_apply_implicitFunction hω hi)
    filter_upwards [he] with t ht
    simpa only [F, monicCoeffRelation_eq_eval] using ht.trans hF0
  · intro s hs hsa hseq
    have hpair : Tendsto (fun t => (c t, s t)) (𝓝 a) (𝓝 (c a, z)) := by
      have hp := hc.continuousAt.prodMk hs
      change Tendsto (fun t => (c t, s t)) (𝓝 a) (𝓝 (c a, s a)) at hp
      simpa only [hsa] using hp
    have he := (hpair.eventually
      (cdf.eventually_apply_eq_iff_implicitFunction hω hi)).filter_mono nhdsWithin_le_nhds
    filter_upwards [he, hseq] with t ht hst
    exact ht.mp (by simpa only [F, monicCoeffRelation_eq_eval, hz] using hst)

/-- A nonzero analytic residue produces a genuine simple pole. -/
theorem analytic_residue_simple_pole {r : ℝ → ℂ} {a : ℝ}
    (hr : AnalyticAt ℝ r a) (hra : r a ≠ 0) :
    MeromorphicAt (fun t => r t / ((t - a : ℝ) : ℂ)) a ∧
      meromorphicOrderAt (fun t => r t / ((t - a : ℝ) : ℂ)) a = (-1 : WithTop ℤ) := by
  have hs : AnalyticAt ℝ (fun t : ℝ => ((t - a : ℝ) : ℂ)) a :=
    (Complex.ofRealCLM.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have hm := hr.meromorphicAt.div hs.meromorphicAt
  refine ⟨hm, (meromorphicOrderAt_eq_int_iff hm).mpr ⟨r, hr, hra, ?_⟩⟩
  filter_upwards [] with t
  simp [Complex.real_smul, div_eq_mul_inv, mul_comm]

end
end GaloisForLFunctions.HTGeometry
