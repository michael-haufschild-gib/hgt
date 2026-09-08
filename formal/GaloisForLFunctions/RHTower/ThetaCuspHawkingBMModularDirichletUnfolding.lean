import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMModularDirichletCovariance

/-!
The complete differentiated periodization unfolds the actual Dirichlet integral.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

/-- Real chart smoothness is retained by each actual projective modular pullback. -/
theorem ChartSmooth.modular_pullback {f : UpperHalfPlane → ℂ} (hf : ChartSmooth f) (γ : PSL2Z) :
    ChartSmooth (fun z => f (γ • z)) := by
  induction γ using QuotientGroup.induction_on with
  | H A =>
    simp only [PSL2Z_mk_smul]
    intro z
    have hG : ContDiffAt ℝ ∞ (fun w : ℂ => ((A • ofComplex w : UpperHalfPlane):ℂ)) (z:ℂ) :=
      ((UpperHalfPlane.analyticAt_smul (g := (A : GL (Fin 2) ℝ)) (by change 0 < (A : GL (Fin 2) ℝ).det.val; simp) z).contDiffAt).restrict_scalars ℝ
    have hF : ContDiffAt ℝ ∞ (f ∘ ofComplex) ((A • ofComplex (z:ℂ):UpperHalfPlane):ℂ) := by
      simpa only [ofComplex_apply] using hf (A • z)
    simpa only [Function.comp_def,ofComplex_apply] using hF.comp (z:ℂ) hG

private theorem weightedDeriv_zero_of_eventually (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane)
    (he : f =ᶠ[𝓝 z] (fun _ => 0)) (v : ℂ) : weightedDeriv v f z = 0 := by
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have hh : f ∘ ofComplex =ᶠ[𝓝 (z:ℂ)] (fun _ => 0) := by
    change ∀ᶠ w in 𝓝 (z:ℂ), f (ofComplex w) = 0
    apply hc.eventually (p := fun w : UpperHalfPlane => f w = (0:ℂ))
    rw [ofComplex_apply]
    filter_upwards [he] with w hw
    exact hw
  unfold weightedDeriv
  rw [hh.fderiv_eq]
  simp

/-- Every original derivative vanishes off the support of a compact chart test. -/
theorem weightedDeriv_zero_off_support (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane)
    (hz : z ∉ tsupport f) (v : ℂ) : weightedDeriv v f z = 0 := by
  apply weightedDeriv_zero_of_eventually f z _ v
  filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hz] with w hw
  exact image_eq_zero_of_notMem_tsupport hw

private theorem compact_test_locally_finite_translates (f : UpperHalfPlane → ℂ)
    (hf : HasCompactSupport f) (z : UpperHalfPlane) :
    ∃ s : Finset PSL2Z, ∀ᶠ w in 𝓝 z, ∀ γ ∉ s, f (γ • w) = 0 := by
  classical
  obtain ⟨K,hK,hKz⟩ := exists_compact_mem_nhds z
  have hfin := ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ := PSL2Z) hK hf
  refine ⟨hfin.toFinset,?_⟩
  filter_upwards [hKz] with w hw γ hγ
  by_contra hn
  apply hγ
  simp only [Set.Finite.mem_toFinset]
  exact ⟨γ • w,⟨w,hw,rfl⟩,subset_tsupport f hn⟩

private theorem frameEnergy_projective_pullback (γ : PSL2Z) (f h : UpperHalfPlane → ℂ)
    (hf : ChartSmooth f) (hh : ChartSmooth h) (z : UpperHalfPlane) :
    frameEnergy (fun w => f (γ • w)) (fun w => h (γ • w)) z = frameEnergy f h (γ • z) := by
  induction γ using QuotientGroup.induction_on with
  | H A => simpa only [PSL2Z_mk_smul] using frameEnergy_modular_pullback A f h hf hh z

/-- The complete Dirichlet density commutes with actual modular periodization
against an invariant smooth field, with the full local finite sum differentiated. -/
theorem frameEnergy_periodize (g : CompactChartTest) (h : UpperHalfPlane → ℂ)
    (hh : ChartSmooth h) (hinv : ∀ γ : PSL2Z, ∀ z, h (γ • z) = h z) (z : UpperHalfPlane) :
    frameEnergy (periodize g.field) h z = periodize (frameEnergy g.field h) z := by
  classical
  obtain ⟨s,hs⟩ := compact_test_locally_finite_translates g.field g.compact z
  have he : periodize g.field =ᶠ[𝓝 z] (fun w => ∑ γ ∈ s, g.field (γ • w)) := by
    filter_upwards [hs] with w hw
    exact tsum_eq_sum (fun γ hγ => hw γ hγ)
  have hc := (UpperHalfPlane.contMDiffAt_ofComplex (n := 0) z.im_pos).continuousAt
  have he' : (periodize g.field) ∘ ofComplex =ᶠ[𝓝 (z:ℂ)]
      (fun w => ∑ γ ∈ s, g.field (γ • ofComplex w)) := by
    change ∀ᶠ w in 𝓝 (z:ℂ), periodize g.field (ofComplex w) = ∑ γ ∈ s, g.field (γ • ofComplex w)
    apply hc.eventually (p := fun w : UpperHalfPlane => periodize g.field w = ∑ γ ∈ s, g.field (γ • w))
    rw [ofComplex_apply]
    filter_upwards [he] with w hw
    exact hw
  have hd (v : ℂ) : weightedDeriv v (periodize g.field) z =
      ∑ γ ∈ s, weightedDeriv v (fun w => g.field (γ • w)) z := by
    unfold weightedDeriv
    rw [he'.fderiv_eq]
    rw [fderiv_fun_sum (u := s) (A := fun γ (w : ℂ) => g.field (γ • ofComplex w))
      (fun γ _ => ((g.smooth.modular_pullback γ) z).differentiableAt (by simp))]
    simp only [sum_apply,Finset.mul_sum,Function.comp_def]
  have heγ (γ : PSL2Z) : frameEnergy (fun w => g.field (γ • w)) h z =
      frameEnergy g.field h (γ • z) := by
    have hhγ : (fun w => h (γ • w)) = h := funext (hinv γ)
    simpa only [hhγ] using frameEnergy_projective_pullback γ g.field h g.smooth hh z
  have hzero (γ : PSL2Z) (hγ : γ ∉ s) : frameEnergy g.field h (γ • z) = 0 := by
    rw [← heγ]
    have hz (v : ℂ) : weightedDeriv v (fun w => g.field (γ • w)) z = 0 :=
      weightedDeriv_zero_of_eventually _ z (hs.mono (fun _ hw => hw γ hγ)) v
    simp [frameEnergy,hz]
  rw [periodize,tsum_eq_sum hzero]
  change (∑ i : Fin 2, conj (weightedDeriv (direction i) (periodize g.field) z)*
    weightedDeriv (direction i) h z) = _
  simp only [hd,map_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ hγ
  exact heγ γ

/-- The full hyperbolic Dirichlet density of smooth fields is continuous. -/
theorem frameEnergy_continuous (f h : UpperHalfPlane → ℂ) (hf : ChartSmooth f) (hh : ChartSmooth h) :
    Continuous (frameEnergy f h) := by
  apply continuous_finsetSum
  intro i _
  exact ((Complex.conjCLE.continuous.comp (weightedDeriv_continuous _ f hf)).mul
    (weightedDeriv_continuous _ h hh))

/-- Compact support of the first field suffices for compact support of the entire
Dirichlet density, including all its original derivative terms. -/
theorem frameEnergy_hasCompactSupport (f h : UpperHalfPlane → ℂ) (hf : HasCompactSupport f) :
    HasCompactSupport (frameEnergy f h) := by
  apply hf.of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closure
  intro z hz
  by_contra hn
  have hd (v : ℂ) := weightedDeriv_zero_off_support f z hn v
  apply hz
  simp [frameEnergy,hd]

/-- Actual gradient energy of an admitted seam-crossing test unfolds to the full
upper-half-plane energy. No smooth representative of the weak response is assumed. -/
theorem frameEnergy_periodize_integral (g : CompactChartTest) (h : UpperHalfPlane → ℂ)
    (hh : ChartSmooth h) (hinv : ∀ γ : PSL2Z, ∀ z, h (γ • z) = h z) :
    (∫ z : UpperHalfPlane, frameEnergy (periodize g.field) h z ∂measure) =
      ∫ z : UpperHalfPlane, frameEnergy g.field h z := by
  have hk := frameEnergy_hasCompactSupport g.field h g.compact
  have hi : Integrable (frameEnergy g.field h) (volume : Measure UpperHalfPlane) :=
    (frameEnergy_continuous g.field h g.smooth hh).integrable_of_hasCompactSupport hk
  have he := compact_test_periodize_integral _ hk hi
  simpa only [← frameEnergy_periodize g h hh hinv] using he

end
end RHTower.D4BMModularCore
