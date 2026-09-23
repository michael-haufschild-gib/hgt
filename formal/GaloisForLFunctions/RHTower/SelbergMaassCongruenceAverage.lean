import GaloisForLFunctions.RHTower.SelbergMaassSourceCurrents
import GaloisForLFunctions.HTGeometry.FiniteRegularReynolds

/-!
# Averaging the complete original Maass congruence family

The finite regular representation acts on the literal original component
values by integral pullback. Its average is a full-modular scalar Maass
source, possibly zero; its complete complement retains the original level,
eigenvalue, and every integral cusp condition. The exact Reynolds loss is
the original source variance, and the full trace splits into the retained
mean mass and complement mass. No spectral quarter bound is asserted.
-/

open Complex Set Filter Topology UpperHalfPlane ModularGroup
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassCongruenceAverage
open SelbergMaassCongruenceTrace SelbergMaassCuspTransport SelbergMaassTraceEnergy
open SelbergMaassSourceCurrents GaloisForLFunctions.HTGeometry
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

def sourceVector (z : ℍ) : EuclideanSpace ℂ (Deck N) :=
  WithLp.toLp 2 (fun q : Deck N => (quotientForm N f q).1.1 z)

def sourceMean (z : ℍ) : ℂ :=
  (Fintype.card (Deck N):ℂ)⁻¹ * ∑ q : Deck N, (quotientForm N f q).1.1 z

def centeredComponent (q : Deck N) (z : ℍ) : ℂ :=
  (quotientForm N f q).1.1 z-sourceMean N f z

theorem sourceVector_pullback (A : SL2Z) (z : ℍ) :
    sourceVector N f (A • z)=finiteRegularUnitary (QuotientGroup.mk A : Deck N) (sourceVector N f z) := by
  ext q
  change (quotientForm N f q).1.1 (A • z)=(quotientForm N f (q*QuotientGroup.mk A)).1.1 z
  rw [quotientForm_mul,translate_apply]

theorem sourceMean_modular (A : SL2Z) (z : ℍ) : sourceMean N f (A • z)=sourceMean N f z := by
  unfold sourceMean
  simp_rw [← translate_apply (N+1) A,← quotientForm_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk A : Deck N))
    (fun q : Deck N => (quotientForm N f q).1.1 z)

theorem centeredComponent_pullback (q : Deck N) (A : SL2Z) (z : ℍ) :
    centeredComponent N f q (A • z)=centeredComponent N f (q*QuotientGroup.mk A) z := by
  rw [centeredComponent,centeredComponent,sourceMean_modular,quotientForm_mul,translate_apply]

theorem average_sourceVector_apply (z : ℍ) (q : Deck N) :
    finiteRegularAverage (sourceVector N f z) q=sourceMean N f z := by
  rw [finiteRegularAverage_apply]
  rfl

theorem sourceVector_norm_sq (z : ℍ) : ‖sourceVector N f z‖^(2 : ℕ)=density N f z := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm]
  rfl

theorem average_sourceVector_norm_sq (z : ℍ) :
    ‖finiteRegularAverage (sourceVector N f z)‖^(2 : ℕ)=
      (Fintype.card (Deck N):ℝ)*normSq (sourceMean N f z) := by
  simp only [EuclideanSpace.norm_sq_eq,average_sourceVector_apply,Complex.sq_norm,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul]

theorem complement_sourceVector_norm_sq (z : ℍ) :
    ‖sourceVector N f z-finiteRegularAverage (sourceVector N f z)‖^(2 : ℕ)=
      ∑ q : Deck N, normSq (centeredComponent N f q z) := by
  rw [EuclideanSpace.norm_sq_eq]
  apply Finset.sum_congr rfl
  intro q _
  rw [Complex.sq_norm]
  congr 1
  change (sourceVector N f z) q-(finiteRegularAverage (sourceVector N f z)) q= _
  rw [average_sourceVector_apply]
  rfl

/-- The original full congruence trace is exactly its invariant mean mass plus
the complete mean-zero component mass. -/
theorem density_mean_variance (z : ℍ) :
    density N f z=(Fintype.card (Deck N):ℝ)*normSq (sourceMean N f z)+
      ∑ q : Deck N, normSq (centeredComponent N f q z) := by
  have h := finiteRegularAverage_norm_decomposition (sourceVector N f z)
  rw [sourceVector_norm_sq,average_sourceVector_norm_sq,complement_sourceVector_norm_sq] at h
  exact h.symm

/-- The finite regular mixing loss is the actual source variance, with every
congruence component retained. -/
theorem source_mixing_energy (z : ℍ) :
    (2*(Fintype.card (Deck N):ℝ))⁻¹ *
      ∑ g : Deck N, ‖finiteRegularUnitary g (sourceVector N f z)-sourceVector N f z‖^(2 : ℕ)=
        ∑ q : Deck N, normSq (centeredComponent N f q z) := by
  rw [finiteRegularAverage_energy,sourceVector_norm_sq,average_sourceVector_norm_sq,density_mean_variance]
  ring

theorem sum_centeredComponent (z : ℍ) : ∑ q : Deck N, centeredComponent N f q z=0 := by
  simp only [centeredComponent,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,sourceMean]
  rw [← mul_assoc,mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card (Deck N):ℂ)≠0),one_mul,sub_self]

private theorem dir_const_smul {F : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ F z) (c v : ℂ) :
    dir v (fun w => c • F w) z=c • dir v F z := by
  rw [dir,fderiv_fun_const_smul hf,smul_apply]
  rfl

private theorem second_dir_const_smul {F : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 F z) (c v : ℂ) :
    dir v (dir v (fun w => c • F w)) z=c • dir v (dir v F) z := by
  have he : dir v (fun w => c • F w) =ᶠ[𝓝 z] (fun w => c • dir v F w) := by
    filter_upwards [hf.eventually (by norm_num)] with w hw
    exact dir_const_smul (hw.differentiableAt (by norm_num)) c v
  change fderiv ℝ (dir v (fun w => c • F w)) z v= _
  rw [he.fderiv_eq]
  exact dir_const_smul ((dir_contDiffAt hf v).differentiableAt (by norm_num)) c v

theorem sourceMean_smooth : IsRealSmoothUpperHalfPlane (sourceMean N f) := by
  have hs : ContDiffOn ℝ 2
      (fun z => ∑ q : Deck N, field N f q z) {z : ℂ | 0 < z.im} :=
    ContDiffOn.sum (fun q _ => (quotientForm N f q).2.2.1.1)
  exact hs.const_smul ((Fintype.card (Deck N):ℂ)⁻¹)

/-- Finite averaging preserves the original Maass eigen-equation, including
when the entire average vanishes. -/
theorem sourceMean_eigenfunction : IsMaassEigenfunction lam (sourceMean N f) := by
  refine ⟨sourceMean_smooth N f,fun z => ?_⟩
  have hs : ContDiffAt ℝ 2 (fun w => ∑ q : Deck N, field N f q w) (z:ℂ) :=
    ContDiffAt.sum (fun q _ => field_smooth N f q z)
  change -(z.im:ℂ)^(2 : ℕ)*(dir 1 (dir 1 (fun w => (Fintype.card (Deck N):ℂ)⁻¹ •
      ∑ q : Deck N, field N f q w)) (z:ℂ)+
    dir Complex.I (dir Complex.I (fun w => (Fintype.card (Deck N):ℂ)⁻¹ •
      ∑ q : Deck N, field N f q w)) (z:ℂ))=(lam:ℂ)*sourceMean N f z
  rw [second_dir_const_smul hs,second_dir_const_smul hs,
    second_dir_sum Finset.univ (fun q _ => field_smooth N f q z),
    second_dir_sum Finset.univ (fun q _ => field_smooth N f q z),← smul_add,← Finset.sum_add_distrib]
  simp_rw [field_laplacian]
  rw [← Finset.mul_sum]
  have hz : (z.im:ℂ)≠0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  have hv : (∑ q : Deck N, field N f q (z:ℂ))=∑ q : Deck N, (quotientForm N f q).1.1 z := by
    simp only [field,Function.comp_apply,ofComplex_apply]
  rw [hv]
  unfold sourceMean
  simp only [smul_eq_mul]
  push_cast
  field_simp

/-- The complete average keeps every original integral cusp decay condition. -/
theorem sourceMean_cuspidal : IsCuspidalAtIntegralCusps (sourceMean N f) := by
  intro A
  have h := tendsto_finsetSum Finset.univ
    (fun q _ => (quotientForm N f q).2.2.2 A)
  have hh := h.const_smul ((Fintype.card (Deck N):ℂ)⁻¹)
  simpa only [IsZeroAtImInfty,ZeroAtFilter,sourceMean,Finset.sum_const_zero,
    smul_eq_mul,mul_zero] using hh

/-- The actual source average descends to the full integral modular subgroup. -/
def meanInvariant : upperHalfPlaneInvariantFunctions (realImage (⊤ : Subgroup SL2Z)) :=
  ⟨sourceMean N f,by
    intro γ z
    obtain ⟨g,_,he⟩ := γ.2
    rw [← he,integral_action]
    exact sourceMean_modular N f g z⟩

/-- Averaging either vanishes or gives an actual full-modular Maass cusp
eigenform with the unchanged original eigenvalue. The zero case is retained. -/
theorem sourceMean_zero_or_full_modular_eigenform :
    sourceMean N f=0 ∨ ∃ g : MaassCuspEigenform (realImage (⊤ : Subgroup SL2Z)) lam,
      g.1.1=sourceMean N f := by
  classical
  by_cases hm : sourceMean N f=0
  · exact Or.inl hm
  · refine Or.inr ⟨⟨meanInvariant N f,?_,sourceMean_eigenfunction N f,sourceMean_cuspidal N f⟩,rfl⟩
    intro h
    exact hm (congrArg Subtype.val h)

private theorem dir_sub {F G : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ F z) (hg : DifferentiableAt ℝ G z) (v : ℂ) :
    dir v (fun w => F w-G w) z=dir v F z-dir v G z := by
  rw [dir,fderiv_fun_sub hf hg,sub_apply]
  rfl

private theorem second_dir_sub {F G : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℝ 2 F z) (hg : ContDiffAt ℝ 2 G z) (v : ℂ) :
    dir v (dir v (fun w => F w-G w)) z=dir v (dir v F) z-dir v (dir v G) z := by
  have he : dir v (fun w => F w-G w) =ᶠ[𝓝 z] (fun w => dir v F w-dir v G w) := by
    filter_upwards [hf.eventually (by norm_num),hg.eventually (by norm_num)] with w hfw hgw
    exact dir_sub (hfw.differentiableAt (by norm_num)) (hgw.differentiableAt (by norm_num)) v
  change fderiv ℝ (dir v (fun w => F w-G w)) z v= _
  rw [he.fderiv_eq]
  exact dir_sub ((dir_contDiffAt hf v).differentiableAt (by norm_num))
    ((dir_contDiffAt hg v).differentiableAt (by norm_num)) v

/-- The complete mean-zero remainder preserves the original Maass equation;
no individual remainder component is presumed nonzero. -/
theorem centeredComponent_eigenfunction (q : Deck N) :
    IsMaassEigenfunction lam (centeredComponent N f q) := by
  have hm := sourceMean_eigenfunction N f
  have hq := (quotientForm N f q).2.2.1
  refine ⟨hq.1.sub hm.1,fun z => ?_⟩
  have hfz := field_smooth N f q z
  have hmz : ContDiffAt ℝ 2 (sourceMean N f ∘ ofComplex) (z:ℂ) :=
    hm.1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  have he : positiveHyperbolicLaplacian (centeredComponent N f q) z=
      positiveHyperbolicLaplacian (quotientForm N f q).1.1 z-
        positiveHyperbolicLaplacian (sourceMean N f) z := by
    change -(z.im:ℂ)^(2 : ℕ)*(dir 1 (dir 1 (fun w => field N f q w-(sourceMean N f ∘ ofComplex) w)) (z:ℂ)+
      dir Complex.I (dir Complex.I (fun w => field N f q w-(sourceMean N f ∘ ofComplex) w)) (z:ℂ))= _
    rw [second_dir_sub hfz hmz,second_dir_sub hfz hmz]
    change _= -(z.im:ℂ)^(2 : ℕ)*(dir 1 (dir 1 (field N f q)) (z:ℂ)+dir Complex.I (dir Complex.I (field N f q)) (z:ℂ))-
      (-(z.im:ℂ)^(2 : ℕ)*(dir 1 (dir 1 (sourceMean N f ∘ ofComplex)) (z:ℂ)+
        dir Complex.I (dir Complex.I (sourceMean N f ∘ ofComplex)) (z:ℂ)))
    ring
  rw [he,hq.2,hm.2]
  exact (mul_sub _ _ _).symm

theorem centeredComponent_cuspidal (q : Deck N) :
    IsCuspidalAtIntegralCusps (centeredComponent N f q) := by
  intro A
  simpa only [IsZeroAtImInfty,ZeroAtFilter,centeredComponent,sub_zero] using
    ((quotientForm N f q).2.2.2 A).sub (sourceMean_cuspidal N f A)

/-- Every mean-zero source component is still invariant under the original
principal congruence subgroup. -/
def centeredInvariant (q : Deck N) :
    upperHalfPlaneInvariantFunctions (realImage (CongruenceSubgroup.Gamma (N+1))) :=
  ⟨centeredComponent N f q,by
    intro γ z
    have hq := (quotientForm N f q).1.2 γ z
    obtain ⟨g,_,he⟩ := γ.2
    change (quotientForm N f q).1.1 ((γ:SL2R) • z)-sourceMean N f ((γ:SL2R) • z)= _
    rw [hq,← he,integral_action,sourceMean_modular]
    rfl⟩

end
end GaloisForLFunctions.RHTower.SelbergMaassCongruenceAverage
