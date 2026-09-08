import GaloisForLFunctions.HTGeometry.L2FamilyCongruence
import GaloisForLFunctions.RHTower.L2SeparatedProductDensity
import Mathlib.Analysis.Meromorphic.Basic

/-! The actual L² family respects finite source sums and continuous separated-product lifts. -/
open MeasureTheory Filter
namespace GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Continuous linear maps preserve actual Banach-valued meromorphic germs. -/
theorem meromorphicAt_continuousLinearMap {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (L : E →L[ℂ] F) (f : ℂ → E) (w : ℂ)
    (hf : MeromorphicAt f w) : MeromorphicAt (fun u => L (f u)) w := by
  obtain ⟨n,hn⟩ := hf
  refine ⟨n,?_⟩
  simpa only [Function.comp_def,map_smul] using (L.analyticAt _).comp hn

/-- The complete pointwise product of admitted radial and angular representatives is admitted. -/
theorem l2SeparatedRepresentative_memLp (μ : Measure A) (ν : Measure B) [SigmaFinite μ] [SigmaFinite ν]
    (f : A → ℂ) (g : B → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun p : A × B => f p.1*g p.2) 2 (μ.prod ν) := by
  apply (l2SeparatedFun_memLp (hf.toLp f) (hg.toLp g)).ae_eq
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae_eq_comp hf.coeFn_toLp,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hg.coeFn_toLp] with p hp hq
  exact congrArg₂ (· * ·) hp hq

/-- Taking the actual product-space L² class agrees with the existing continuous bilinear lift. -/
theorem l2Family_separated (μ : Measure A) (ν : Measure B) [SigmaFinite μ] [SigmaFinite ν]
    (F : ℂ → A → ℂ) (g : B → ℂ) (w : ℂ) (hF : MemLp (F w) 2 μ) (hg : MemLp g 2 ν) :
    l2Family (μ.prod ν) (fun u p => F u p.1*g p.2) w =
      l2SeparatedProductContinuousBilinear (l2Family μ F w) (hg.toLp g) := by
  have hp := l2SeparatedRepresentative_memLp μ ν (F w) g hF hg
  rw [l2Family_eq_toLp _ _ _ hp,l2Family_eq_toLp _ _ _ hF,l2SeparatedProductContinuousBilinear_apply]
  apply Lp.ext
  filter_upwards [hp.coeFn_toLp,l2SeparatedProduct_ae (hF.toLp (F w)) (hg.toLp g),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp hF.coeFn_toLp,
    Measure.quasiMeasurePreserving_snd.ae_eq_comp hg.coeFn_toLp] with p h₀ h₁ h₂ h₃
  rw [h₀,h₁]
  exact (congrArg₂ (· * ·) h₂ h₃).symm

/-- Addition commutes with taking the actual L² class of complete admitted representatives. -/
theorem l2Family_add (μ : Measure A) (F G : ℂ → A → ℂ) (w : ℂ)
    (hF : MemLp (F w) 2 μ) (hG : MemLp (G w) 2 μ) :
    l2Family μ (fun u a => F u a+G u a) w = l2Family μ F w+l2Family μ G w := by
  rw [l2Family_eq_toLp _ _ _ (hF.add hG),l2Family_eq_toLp _ _ _ hF,l2Family_eq_toLp _ _ _ hG]
  exact hF.toLp_add hG

/-- A finite sum of admitted representatives gives exactly the finite sum of their L² classes. -/
theorem l2Family_sum (μ : Measure A) {I : Type*} [Fintype I] (F : I → ℂ → A → ℂ) (w : ℂ)
    (hF : ∀ i, MemLp (F i w) 2 μ) :
    l2Family μ (fun u a => ∑ i, F i u a) w = ∑ i, l2Family μ (F i) w := by
  have hs := memLp_finsetSum Finset.univ (fun i _ => hF i)
  rw [l2Family_eq_toLp _ _ _ hs]
  simp_rw [l2Family_eq_toLp _ _ _ (hF _)]
  apply Lp.ext
  have he : ∀ᵐ a ∂μ, ∀ i, (hF i).toLp (F i w) a = F i w a :=
    ae_all_iff.mpr (fun i => (hF i).coeFn_toLp)
  filter_upwards [hs.coeFn_toLp,Lp.coeFn_fun_finsetSum Finset.univ (fun i => (hF i).toLp (F i w)),he]
    with a h₀ h₁ h₂
  rw [h₀,h₁]
  exact Finset.sum_congr rfl (fun i _ => (h₂ i).symm)

end
end GaloisForLFunctions.HTGeometry
