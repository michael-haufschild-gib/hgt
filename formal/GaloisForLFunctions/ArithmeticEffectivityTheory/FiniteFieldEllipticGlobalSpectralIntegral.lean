import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticRadialKernel
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticSpectralProduct

/-!
# The actual adelic spectral integral

Finite cylinders exhaust the restricted product. Their norm integrals
converge to a finite real part of the zeta ratio; directed monotone
convergence proves global integrability. Complex exhaustion then gives
the exact integral without assuming an infinite local-product measure.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open MeasureTheory Filter Set
open HTGeometry.LoopEisenstein
open scoped ENNReal Topology
noncomputable section

private theorem integrable_of_directed_exhaustion {A ι : Type*} [MeasurableSpace A] [Countable ι] [Nonempty ι]
    [SemilatticeSup ι] (μ : Measure A) (C : ι → Set A)
    (hC : ∀ i, MeasurableSet (C i)) (hmono : Monotone C)
    (hcover : ∀ a, ∃ i, a ∈ C i) (f : A → ℂ) (hf : Measurable f)
    (hi : ∀ i, IntegrableOn f (C i) μ) (M : ℝ)
    (hlim : Tendsto (fun i => ∫ a in C i, ‖f a‖ ∂μ) atTop (𝓝 M)) :
    Integrable f μ := by
  classical
  let F : ι → A → ℝ≥0∞ := fun i => (C i).indicator (fun a => ‖f a‖ₑ)
  have hF : ∀ i, Measurable (F i) := fun i => hf.enorm.indicator (hC i)
  have hFm : Monotone F := by
    intro i j hij a
    by_cases ha : a ∈ C i
    · simp only [F, indicator_of_mem ha, indicator_of_mem (hmono hij ha), le_refl]
    · simp only [F, indicator_of_notMem ha]
      exact zero_le
  have hdir : Directed (· ≤ ·) F := fun i j =>
    ⟨i ⊔ j, hFm le_sup_left, hFm le_sup_right⟩
  have hsup (a : A) : (⨆ i, F i a) = ‖f a‖ₑ := by
    apply le_antisymm
    · apply iSup_le
      intro i
      by_cases ha : a ∈ C i
      · simp only [F, indicator_of_mem ha, le_refl]
      · simp only [F, indicator_of_notMem ha]
        exact zero_le
    · obtain ⟨i, hi⟩ := hcover a
      calc
        ‖f a‖ₑ = F i a := by
          change ‖f a‖ₑ = (C i).indicator (fun b => ‖f b‖ₑ) a
          rw [indicator_of_mem hi]
        _ ≤ ⨆ j, F j a := le_iSup (fun j => F j a) i
  have hval (i : ι) : (∫⁻ a, F i a ∂μ) =
      ENNReal.ofReal (∫ a in C i, ‖f a‖ ∂μ) := by
    change (∫⁻ a, (C i).indicator (fun b => ‖f b‖ₑ) a ∂μ) = _
    rw [lintegral_indicator (hC i)]
    exact (ofReal_integral_norm_eq_lintegral_enorm (hi i)).symm
  have hL : Monotone (fun i => ∫⁻ a, F i a ∂μ) :=
    fun i j hij => lintegral_mono (hFm hij)
  have hlim' : Tendsto (fun i => ∫⁻ a, F i a ∂μ) atTop (𝓝 (ENNReal.ofReal M)) := by
    simp only [hval]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim
  have he : (∫⁻ a, ‖f a‖ₑ ∂μ) = ENNReal.ofReal M := by
    calc
      _ = ∫⁻ a, ⨆ i, F i a ∂μ := lintegral_congr fun a => (hsup a).symm
      _ = ⨆ i, ∫⁻ a, F i a ∂μ := lintegral_iSup_directed (fun i => (hF i).aemeasurable) hdir
      _ = _ := iSup_eq_of_tendsto hL hlim'
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  change (∫⁻ a, ‖f a‖ₑ ∂μ) < ⊤
  rw [he]
  exact ENNReal.ofReal_lt_top

/-- Enlarging the exceptional finite-place set enlarges the actual cylinder. -/
theorem ellipticAdeleCylinder_monotone : Monotone ellipticAdeleCylinder := by
  intro S T h a ha
  exact finiteAdeleCylinder_mono h ha

/-- Every cylinder is an open measurable subset of the actual adelic group. -/
theorem ellipticAdeleCylinder_isOpen (S : Finset FinitePlace) :
    IsOpen (ellipticAdeleCylinder S) :=
  (finiteAdeleCylinder_isOpen S).preimage continuous_fst

/-- Finite cylinders exhaust the actual restricted adelic product. -/
theorem iUnion_ellipticAdeleCylinder :
    (⋃ S : Finset FinitePlace, ellipticAdeleCylinder S) = univ := by
  ext a
  simp only [mem_iUnion, mem_univ, iff_true]
  exact exists_mem_finiteAdeleCylinder a.1

private theorem kernel_real (r : ℝ) (a : Adeles) :
    ellipticAdeleSpectralKernel (r : ℂ) a =
      (Real.exp (-(r+1)*adelicLogHeight a) : ℂ) := by
  simp only [ellipticAdeleSpectralKernel, Complex.ofReal_exp, Complex.ofReal_mul,
    Complex.ofReal_neg, Complex.ofReal_add, Complex.ofReal_one]

private theorem norm_kernel_eq_re (s : ℂ) (a : Adeles) :
    ‖ellipticAdeleSpectralKernel s a‖ = (ellipticAdeleSpectralKernel (s.re : ℂ) a).re := by
  rw [norm_ellipticAdeleSpectralKernel, kernel_real, Complex.ofReal_re]

/-- The actual cylinder integral is the finite normalized local spectral product. -/
theorem integral_ellipticAdeleSpectralKernel_cylinder (S : Finset FinitePlace)
    (s : ℂ) (hs : 0 < s.re) :
    (∫ a in ellipticAdeleCylinder S, ellipticAdeleSpectralKernel s a ∂adeleHaar) =
      (∏ v ∈ S, ellipticFiniteSpectralFactor s v) * ellipticInfinitySpectralFactor s := by
  rw [← integral_ellipticCylinderAssembly]
  have he : (fun x => ellipticAdeleSpectralKernel s (ellipticCylinderAssembly S x)) =
      ellipticCylinderSpectralKernel S s := funext (ellipticAdeleSpectralKernel_cylinder S s)
  rw [he]
  have h := integral_ellipticCylinderSpectralKernel S s hs
  change (∫ x, ellipticCylinderSpectralKernel S s x ∂ellipticCylinderProductHaar S) =
    (∏ v : S, ellipticFiniteSpectralFactor s v.1) * ellipticInfinitySpectralFactor s at h
  rw [Finset.prod_coe_sort S (ellipticFiniteSpectralFactor s)] at h
  exact h

private theorem tendsto_cylinder_integral (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun S : Finset FinitePlace =>
      ∫ a in ellipticAdeleCylinder S, ellipticAdeleSpectralKernel s a ∂adeleHaar)
      atTop (𝓝 (ellipticSpectralZetaRatio s)) := by
  simp only [integral_ellipticAdeleSpectralKernel_cylinder _ s (zero_lt_one.trans hs)]
  exact tendsto_ellipticSpectralCylinderProduct s hs

private theorem tendsto_cylinder_norm_integral (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun S : Finset FinitePlace =>
      ∫ a in ellipticAdeleCylinder S, ‖ellipticAdeleSpectralKernel s a‖ ∂adeleHaar)
      atTop (𝓝 (ellipticSpectralZetaRatio (s.re : ℂ)).re) := by
  have he (S : Finset FinitePlace) :
      (∫ a in ellipticAdeleCylinder S, ‖ellipticAdeleSpectralKernel s a‖ ∂adeleHaar) =
        (∫ a in ellipticAdeleCylinder S,
          ellipticAdeleSpectralKernel (s.re : ℂ) a ∂adeleHaar).re := by
    simp only [norm_kernel_eq_re]
    exact integral_re (ellipticAdeleSpectralKernel_integrableOn_cylinder S (s.re : ℂ)
      (zero_lt_one.trans hs))
  simp only [he]
  exact Complex.continuous_re.continuousAt.tendsto.comp
    (tendsto_cylinder_integral (s.re : ℂ) hs)


/-- The actual adelic radial kernel is absolutely integrable throughout `Re(s)>1`. -/
theorem ellipticAdeleSpectralKernel_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (ellipticAdeleSpectralKernel s) adeleHaar := by
  classical
  apply integrable_of_directed_exhaustion (A := Adeles) (ι := Finset FinitePlace)
    (μ := adeleHaar) (C := ellipticAdeleCylinder) (f := ellipticAdeleSpectralKernel s)
    (M := (ellipticSpectralZetaRatio (s.re : ℂ)).re)
  · exact fun S => (ellipticAdeleCylinder_isOpen S).measurableSet
  · exact ellipticAdeleCylinder_monotone
  · exact fun a => exists_mem_finiteAdeleCylinder a.1
  · exact (continuous_ellipticAdeleSpectralKernel s).measurable
  · exact fun S => ellipticAdeleSpectralKernel_integrableOn_cylinder S s (zero_lt_one.trans hs)
  · exact tendsto_cylinder_norm_integral s hs

/-- The independently defined actual adelic integral is the complete elliptic zeta ratio. -/
theorem integral_ellipticAdeleSpectralKernel (s : ℂ) (hs : 1 < s.re) :
    (∫ a, ellipticAdeleSpectralKernel s a ∂adeleHaar) = ellipticSpectralZetaRatio s := by
  have hi : IntegrableOn (ellipticAdeleSpectralKernel s)
      (⋃ S : Finset FinitePlace, ellipticAdeleCylinder S) adeleHaar := by
    rw [iUnion_ellipticAdeleCylinder, integrableOn_univ]
    exact ellipticAdeleSpectralKernel_integrable s hs
  have h := tendsto_setIntegral_of_monotone
    (fun S => (ellipticAdeleCylinder_isOpen S).measurableSet)
    ellipticAdeleCylinder_monotone hi
  simp only [iUnion_ellipticAdeleCylinder, Measure.restrict_univ] at h
  exact tendsto_nhds_unique h (tendsto_cylinder_integral s hs)

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticAdeleSpectralKernel_integrable
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.integral_ellipticAdeleSpectralKernel
