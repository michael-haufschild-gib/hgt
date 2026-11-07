/-
Smooth cusp exhaustion adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicBarrierPotential

/-!
# Compact exhaustion with uniformly bounded hyperbolic gradient

The invariant barrier is proper on the cubic quotient. Smooth dilations of
its height give compact cutoffs, eventually one near every point. A single
active cusp profile and the logarithmic eikonal identity bound their
hyperbolic gradients uniformly in the cutoff radius.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma kernelBarrier_sublevel_isCompact (T : ℝ) :
    IsCompact {q : KernelQuotient | kernelQuotientBarrier 2 3 q≤T} := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS (max 3 T)
  apply hcompact.of_isClosed_subset
    (isClosed_le (kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)) continuous_const)
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S (max 3 T) ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r (max 3 T) := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    have hh : 3<p.1.2 := (le_max_left 3 T).trans_lt hp.2.2
    change kernelQuotientBarrier 2 3 (fordOrbitChart globalKubotaKernel r p)≤T at hq
    rw [kernelQuotientBarrier_fordCusp 2 3 (by norm_num) (by norm_num) r p hh] at hq
    exact (not_lt_of_ge hq) ((le_max_right 3 T).trans_lt hp.2.2)

def kernelExhaustionProfile (n : ℕ) (v : ℝ) : ℝ :=
  1-cuspTransition 1 2 (v/((n:ℝ)+1))

def kernelExhaustionCutoff (n : ℕ) (q : KernelQuotient) : ℝ :=
  kernelExhaustionProfile n (kernelQuotientBarrier 2 3 q)

lemma kernelExhaustionProfile_smooth (n : ℕ) :
    ContDiff ℝ ∞ (kernelExhaustionProfile n) := by
  unfold kernelExhaustionProfile cuspTransition
  fun_prop

lemma kernelExhaustionCutoff_smooth (n : ℕ) :
    ContMDiff 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,ℝ) ∞ (kernelExhaustionCutoff n) :=
  (kernelExhaustionProfile_smooth n).contMDiff.comp
    (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num))

lemma kernelExhaustionProfile_bounds (n : ℕ) (v : ℝ) :
    0≤kernelExhaustionProfile n v ∧ kernelExhaustionProfile n v≤1 := by
  have h0 := Real.smoothTransition.nonneg ((v/((n:ℝ)+1)-1)/(2-1))
  have h1 := Real.smoothTransition.le_one ((v/((n:ℝ)+1)-1)/(2-1))
  change 0≤1-Real.smoothTransition _ ∧ 1-Real.smoothTransition _≤1
  constructor <;> linarith

lemma kernelExhaustionProfile_one (n : ℕ) (v : ℝ) (hv : v≤(n:ℝ)+1) :
    kernelExhaustionProfile n v=1 := by
  rw [kernelExhaustionProfile,cuspTransition_zero 1 2 _ (by norm_num)
    ((div_le_one (by positivity)).mpr hv),sub_zero]

lemma kernelExhaustionProfile_zero (n : ℕ) (v : ℝ) (hv : 2*((n:ℝ)+1)≤v) :
    kernelExhaustionProfile n v=0 := by
  rw [kernelExhaustionProfile,cuspTransition_one 1 2 _ (by norm_num)
    ((le_div_iff₀ (by positivity)).mpr hv),sub_self]

lemma kernelExhaustionCutoff_hasCompactSupport (n : ℕ) :
    HasCompactSupport (kernelExhaustionCutoff n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (kernelBarrier_sublevel_isCompact (2*((n:ℝ)+1)))
  intro q hq
  change kernelQuotientBarrier 2 3 q≤2*((n:ℝ)+1)
  by_contra h
  exact hq (kernelExhaustionProfile_zero n _ (le_of_not_ge h))

lemma kernelExhaustionCutoff_bounds (n : ℕ) (q : KernelQuotient) :
    0≤kernelExhaustionCutoff n q ∧ kernelExhaustionCutoff n q≤1 :=
  kernelExhaustionProfile_bounds n _

lemma kernelExhaustionCutoff_eventually_one (q : KernelQuotient) :
    ∀ᶠn : ℕ in atTop,kernelExhaustionCutoff n q=1 := by
  obtain ⟨N,hN⟩ := exists_nat_gt (kernelQuotientBarrier 2 3 q)
  filter_upwards [eventually_ge_atTop N] with n hn
  apply kernelExhaustionProfile_one
  have hh : (N:ℝ)≤n := by exact_mod_cast hn
  linarith

lemma kernelExhaustionCutoff_eventually_one_near (q : KernelQuotient) :
    ∀ᶠn : ℕ in atTop,kernelExhaustionCutoff n =ᶠ[𝓝 q] (fun _ => 1) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (kernelQuotientBarrier 2 3 q)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hh : kernelQuotientBarrier 2 3 q<(n:ℝ)+1 := by
    have hcast : (N:ℝ)≤n := by exact_mod_cast hn
    linarith
  filter_upwards [(kernelQuotientBarrier_continuous 2 3 (by norm_num) (by norm_num)).continuousAt.eventually_lt_const hh]
    with p hp
  exact kernelExhaustionProfile_one n _ hp.le


lemma cuspTransition_euler_bounded (a b : ℝ) (hab : a<b) :
    ∃C : ℝ,0≤C ∧ ∀v,|v*deriv (cuspTransition a b) v|≤C := by
  have hc : HasCompactSupport (fun v => v*deriv (cuspTransition a b) v) := by
    apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    intro v hv
    by_contra hnot
    have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hnot
    exact hv (by change v*deriv (cuspTransition a b) v=0; rw [(cuspTransition_derivatives a b v hab hout).1,mul_zero])
  have hcont : Continuous (fun v => v*deriv (cuspTransition a b) v) :=
    continuous_id.mul ((contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2.continuous)
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous hcont
  exact ⟨max C 0,le_max_right _ _,fun v => (hC v).trans (le_max_left _ _)⟩

lemma rowLogD_hyperbolic_bound (u : Fin 2→ℂ) (hu : u≠0)
    (p : SpatialCoordinates) (hp : 0<p 2) (j : Fin 3) : |p 2*rowLogD u p j|≤1 := by
  have he := rowLog_eikonal u hu p hp
  have hsq : (p 2*rowLogD u p j)^2≤1 := by
    fin_cases j
    · change (p 2*rowLogD u p 0)^2≤1
      nlinarith only [he,sq_nonneg (p 2*rowLogD u p 1),sq_nonneg (p 2*rowLogD u p 2)]
    · change (p 2*rowLogD u p 1)^2≤1
      nlinarith only [he,sq_nonneg (p 2*rowLogD u p 0),sq_nonneg (p 2*rowLogD u p 2)]
    · change (p 2*rowLogD u p 2)^2≤1
      nlinarith only [he,sq_nonneg (p 2*rowLogD u p 0),sq_nonneg (p 2*rowLogD u p 1)]
  exact (abs_le).mpr ⟨by nlinarith only [hsq],by nlinarith only [hsq]⟩

lemma axisSlice_eventuallyEq_of_positive (f g : SpatialCoordinates → ℂ)
    (heq : ∀ q, 0<q 2 → f q=g q) (p : SpatialCoordinates) (hv : 0<p 2) (j : Fin 3) :
    axisSlice f p j =ᶠ[𝓝 (p j)] axisSlice g p j := by
  have hnear : ∀ᶠ t in 𝓝 (p j), 0<(Function.update p j t) 2 := by
    apply ((continuous_apply 2).comp (continuous_axis_update p j)).continuousAt.eventually_const_lt
    change 0<(Function.update p j (p j)) 2
    simpa only [Function.update_eq_self] using hv
  filter_upwards [hnear] with t ht
  exact heq _ ht

lemma cuspBarrierField_local_model (p : SpatialCoordinates) (hp : 0<p 2) :
    (cuspBarrierField 2 3 =ᶠ[𝓝 p] (fun _ => 1)) ∨
    ∃x : FullCuspClasses,1<rowHeight (fullCuspRow x) p ∧
      cuspBarrierField 2 3 =ᶠ[𝓝 p] (fun q => 1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q)) := by
  by_cases hx : ∃x : FullCuspClasses,1<rowHeight (fullCuspRow x) p
  · obtain ⟨x,hx⟩ := hx
    refine Or.inr ⟨x,hx,?_⟩
    have hc := (rowHeight_contDiffAt _ (fullCuspRow_ne_zero x) p hp).continuousAt
    filter_upwards [hc.eventually_const_lt hx,(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq hpos
    change 1+fullCuspProfileField (cuspBarrierProfile 2 3) q=_
    rw [fullCuspProfileField_eq _ q hpos,fullCuspProfileSum_eq_single _
      (fun v hv => cuspBarrierProfile_zero 2 3 (by norm_num) v (by linarith)) _ x
        (by rwa [←fullCuspRow_height x q hpos]),←fullCuspRow_height x q hpos]
  · left
    obtain ⟨T,hT⟩ := fullCuspRows_locally_finite p hp
    have hsmall : ∀ᶠq in 𝓝 p,∀x∈T,rowHeight (fullCuspRow x) q<2 := by
      rw [eventually_all_finset]
      intro x hxT
      apply (rowHeight_contDiffAt _ (fullCuspRow_ne_zero x) p hp).continuousAt.eventually_lt_const
      have hn : rowHeight (fullCuspRow x) p≤1 := not_lt.mp (fun h => hx ⟨x,h⟩)
      linarith
    filter_upwards [hT,hsmall] with q hq hqT
    change 1+fullCuspProfileField (cuspBarrierProfile 2 3) q=1
    have hz : ∀x : FullCuspClasses,cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q)=0 := by
      intro x
      apply cuspBarrierProfile_zero 2 3 (by norm_num)
      by_cases hmem : x∈T
      · exact (hqT x hmem).le
      · exact (hq x hmem).le.trans (by norm_num)
    simp only [fullCuspProfileField,hz,tsum_zero,add_zero]

lemma cuspBarrierProfile_log_derivative_bound :
    ∃D : ℝ,0≤D ∧ ∀v : ℝ,1<v→
      |v*deriv (cuspBarrierProfile 2 3) v|≤D*(1+cuspBarrierProfile 2 3 v) := by
  have hd := (contDiff_infty_iff_deriv.mp (cuspBarrierProfile_smooth 2 3)).2.continuous
  obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Set.Icc (1:ℝ) 3)).image hd.abs).bddAbove
  let D := max 1 (3*max C 0)
  have hD : 0≤D := le_trans (by norm_num) (le_max_left _ _)
  refine ⟨D,hD,fun v hv => ?_⟩
  by_cases hhigh : 3<v
  · have he : cuspBarrierProfile 2 3 =ᶠ[𝓝 v] (fun x => x-1) := by
      filter_upwards [Ioi_mem_nhds hhigh] with x hx
      rw [cuspBarrierProfile,cuspTransition_one 2 3 x (by norm_num) hx.le,one_mul]
    have hder : deriv (cuspBarrierProfile 2 3) v=1 := by rw [he.deriv_eq]; simp
    rw [hder,mul_one,abs_of_pos (by linarith),he.self_of_nhds]
    have h := mul_le_mul_of_nonneg_right (le_max_left 1 (3*max C 0)) (show 0≤v by linarith)
    dsimp only [D]
    nlinarith only [h]
  · have hCv : |deriv (cuspBarrierProfile 2 3) v|≤ max C 0 :=
      (hC (Set.mem_image_of_mem _ (show v∈Set.Icc (1:ℝ) 3 from ⟨hv.le,not_lt.mp hhigh⟩))).trans (le_max_left _ _)
    have h1 : |v*deriv (cuspBarrierProfile 2 3) v|≤3*max C 0 := by
      rw [abs_mul,abs_of_pos (by linarith)]
      exact mul_le_mul (not_lt.mp hhigh) hCv (abs_nonneg _) (by positivity)
    have hphi := cuspBarrierProfile_nonneg 2 3 (by norm_num) (by norm_num) v
    exact (h1.trans (le_max_right _ _)).trans (by nlinarith only [mul_nonneg hD hphi])

lemma cuspBarrierField_scaled_deriv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : SpatialCoordinates,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*deriv (axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j) (p j)‖≤
        D*cuspBarrierField 2 3 p := by
  obtain ⟨D,hD,hbound⟩ := cuspBarrierProfile_log_derivative_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  have ht : Tendsto (fun t => Function.update p j t) (𝓝 (p j)) (𝓝 p) := by
    simpa only [Function.update_eq_self] using ((continuous_axis_update p j).continuousAt (x := p j)).tendsto
  rcases cuspBarrierField_local_model p hp with hz | ⟨x,hx,he⟩
  · have hzCast : (fun q => (cuspBarrierField 2 3 q:ℂ)) =ᶠ[𝓝 p] (fun _ => (1:ℂ)) :=
      hz.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
    have hzC := hzCast.comp_tendsto ht
    change axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j =ᶠ[𝓝 (p j)] (fun _ => (1:ℂ)) at hzC
    rw [hzC.deriv_eq,deriv_const,mul_zero,norm_zero,hz.self_of_nhds,mul_one]
    exact hD
  · have heCast : (fun q => (cuspBarrierField 2 3 q:ℂ)) =ᶠ[𝓝 p]
        (fun q => ((1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q):ℝ):ℂ)) :=
      he.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
    have heC := heCast.comp_tendsto ht
    change axisSlice (fun q => (cuspBarrierField 2 3 q:ℂ)) p j =ᶠ[𝓝 (p j)]
      (fun t => ((1+cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) (Function.update p j t)):ℝ):ℂ)) at heC
    rw [heC.deriv_eq]
    simp only [Complex.ofReal_add,Complex.ofReal_one]
    rw [deriv_const_add]
    have hpF := (rowProfile_axis_derivatives (fun v => (cuspBarrierProfile 2 3 v:ℂ))
      (fun v hv => Complex.ofRealCLM.contDiff.contDiffAt.comp v (cuspBarrierProfile_smooth 2 3).contDiffAt)
      (fullCuspRow x) (fullCuspRow_ne_zero x) p hp j).1
    change ‖(p 2:ℂ)*deriv (axisSlice (fun q => (cuspBarrierProfile 2 3 (rowHeight (fullCuspRow x) q):ℂ)) p j) (p j)‖≤_
    rw [hpF.deriv,cast_profile_deriv _ ((cuspBarrierProfile_smooth 2 3).differentiable (by simp))]
    have hid : (p 2:ℂ)*(((deriv (cuspBarrierProfile 2 3) (rowHeight (fullCuspRow x) p):ℝ):ℂ)*
        (rowHeight (fullCuspRow x) p:ℂ)*(rowLogD (fullCuspRow x) p j:ℂ))=
        ((p 2*rowLogD (fullCuspRow x) p j:ℝ):ℂ)*
        ((rowHeight (fullCuspRow x) p*deriv (cuspBarrierProfile 2 3) (rowHeight (fullCuspRow x) p):ℝ):ℂ) := by
      push_cast
      ring
    rw [hid,norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
    apply (mul_le_of_le_one_left (abs_nonneg _) (rowLogD_hyperbolic_bound _ (fullCuspRow_ne_zero x) p hp j)).trans
    rw [he.self_of_nhds]
    exact hbound _ hx

lemma kernelBarrier_scaled_fderiv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤D*kernelQuotientBarrier 2 3 (kernelEuclideanProjection p) := by
  obtain ⟨D,hD,hbound⟩ := cuspBarrierField_scaled_deriv_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  let f : EuclideanSpatial→ℂ := fun q => (kernelQuotientBarrier 2 3 (kernelEuclideanProjection q):ℂ)
  have hf : ∀q,0<q 2→ContDiffAt ℝ ∞ f q := fun q hq =>
    Complex.ofRealCLM.contDiff.contDiffAt.comp q
      (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) q hq)
  have he : ∀q : SpatialCoordinates,0<q 2→ f (WithLp.toLp 2 q)=(cuspBarrierField 2 3 q:ℂ) := by
    intro q hq
    exact congrArg Complex.ofReal (cuspBarrier_euclidean_eq 2 3 (WithLp.toLp 2 q) hq)
  have ha := axisSlice_eventuallyEq_of_positive _ _ he p.ofLp hp j
  change ‖(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector j)‖≤_
  rw [←(euclideanAxisSlice_derivatives f hf p hp j).1,ha.deriv_eq]
  change _≤D*cuspBarrier 2 3 (euclideanToHyperbolic p)
  rw [cuspBarrier_euclidean_eq 2 3 p hp]
  exact hbound p.ofLp hp j

lemma kernelBarrier_scaled_real_fderiv_bound :
    ∃D : ℝ,0≤D ∧ ∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      |p 2*fderiv ℝ (fun q => kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)) p
        (euclideanCoordinateVector j)|≤D*kernelQuotientBarrier 2 3 (kernelEuclideanProjection p) := by
  obtain ⟨D,hD,hbound⟩ := kernelBarrier_scaled_fderiv_bound
  refine ⟨D,hD,fun p hp j => ?_⟩
  have hphi := (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) p hp).differentiableAt (by simp)
  have he := (Complex.ofRealCLM.hasFDerivAt.comp p hphi.hasFDerivAt).fderiv
  have hh := hbound p hp j
  change ‖(p 2:ℂ)*fderiv ℝ (Complex.ofRealCLM ∘ (fun q => cuspBarrier 2 3 (euclideanToHyperbolic q))) p
      (euclideanCoordinateVector j)‖≤_ at hh
  rw [he] at hh
  simpa only [ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,←Complex.ofReal_mul,
    Complex.norm_real,Real.norm_eq_abs] using! hh

lemma kernelExhaustionProfile_euler_bounded :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀v : ℝ,|v*deriv (kernelExhaustionProfile n) v|≤C := by
  obtain ⟨C,hC,hbound⟩ := cuspTransition_euler_bounded 1 2 (by norm_num)
  refine ⟨C,hC,fun n v => ?_⟩
  let c : ℝ := (n:ℝ)+1
  have hc : c≠0 := by dsimp [c]; positivity
  have hd := (hasDerivAt_const v (1:ℝ)).sub
    (((cuspTransition_contDiff 1 2).differentiable (by simp) (v/c)).hasDerivAt.comp v
      ((hasDerivAt_id v).div_const c))
  change HasDerivAt (kernelExhaustionProfile n) (0-deriv (cuspTransition 1 2) (v/c)*(1/c)) v at hd
  rw [hd.deriv]
  have he : v*(0-deriv (cuspTransition 1 2) (v/c)*(1/c))= -(v/c*deriv (cuspTransition 1 2) (v/c)) := by ring
  rw [he,abs_neg]
  exact hbound (v/c)

lemma kernelExhaustionCutoff_scaled_fderiv_bound :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→∀j : Fin 3,
      ‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖≤C := by
  obtain ⟨D,hD,hgrad⟩ := kernelBarrier_scaled_real_fderiv_bound
  obtain ⟨B,hB,hprofile⟩ := kernelExhaustionProfile_euler_bounded
  refine ⟨D*B,mul_nonneg hD hB,fun n p hp j => ?_⟩
  let phi : EuclideanSpatial→ℝ := fun q => kernelQuotientBarrier 2 3 (kernelEuclideanProjection q)
  have hphi : DifferentiableAt ℝ phi p :=
    (cuspBarrier_euclidean_contDiffAt 2 3 (by norm_num) (by norm_num) p hp).differentiableAt (by simp)
  have hP := ((kernelExhaustionProfile_smooth n).differentiable (by simp) (phi p)).hasDerivAt
  have hd := (hP.ofReal_comp.hasFDerivAt.comp p hphi.hasFDerivAt).fderiv
  change ‖(p 2:ℂ)*fderiv ℝ ((fun v => (kernelExhaustionProfile n v:ℂ)) ∘ phi) p
    (euclideanCoordinateVector j)‖≤D*B
  rw [hd]
  change ‖(p 2:ℂ)*((fderiv ℝ phi p (euclideanCoordinateVector j):ℝ) •
    ((deriv (kernelExhaustionProfile n) (phi p):ℝ):ℂ))‖≤D*B
  rw [Complex.real_smul,←Complex.ofReal_mul,←Complex.ofReal_mul,Complex.norm_real,Real.norm_eq_abs]
  calc
    |p 2*(fderiv ℝ phi p (euclideanCoordinateVector j)*deriv (kernelExhaustionProfile n) (phi p))|
      = |p 2*fderiv ℝ phi p (euclideanCoordinateVector j)| *|deriv (kernelExhaustionProfile n) (phi p)| := by rw [←abs_mul]; congr 1; ring
    _ ≤ (D*phi p)*|deriv (kernelExhaustionProfile n) (phi p)| :=
      mul_le_mul_of_nonneg_right (hgrad p hp j) (abs_nonneg _)
    _ = D*|phi p*deriv (kernelExhaustionProfile n) (phi p)| := by
      rw [abs_mul,abs_of_nonneg (le_trans zero_le_one (kernelQuotientBarrier_one_le 2 3 (by norm_num) (by norm_num) _))]
      ring
    _ ≤ D*B := mul_le_mul_of_nonneg_left (hprofile n (phi p)) hD

lemma kernelExhaustionCutoff_fderiv_eventually_zero (p : EuclideanSpatial) (hp : 0<p 2) :
    ∀ᶠn : ℕ in atTop,
      fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p=0 := by
  have hc : ContinuousAt kernelEuclideanProjection p :=
    (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt p hp).continuousAt
  filter_upwards [kernelExhaustionCutoff_eventually_one_near (kernelEuclideanProjection p)] with n hn
  have he := hn.comp_tendsto hc
  have heC : (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) =ᶠ[𝓝 p]
      (fun _ => (1:ℂ)) := he.mono (fun q hq => congrArg (fun v : ℝ => (v:ℂ)) hq)
  rw [heC.fderiv_eq]
  simp

lemma kernelExhaustionCutoff_energy_density_bound :
    ∃C : ℝ,0≤C ∧ ∀n : ℕ,∀p : EuclideanSpatial,0<p 2→
      (∑j : Fin 3,‖(p 2:ℂ)*fderiv ℝ (fun q => (kernelExhaustionCutoff n (kernelEuclideanProjection q):ℂ)) p
        (euclideanCoordinateVector j)‖^2)≤C := by
  obtain ⟨D,hD,hbound⟩ := kernelExhaustionCutoff_scaled_fderiv_bound
  refine ⟨3*D^2,by positivity,fun n p hp => ?_⟩
  calc
    _ ≤ ∑j : Fin 3,D^2 := Finset.sum_le_sum (fun j hj =>
      (sq_le_sq₀ (norm_nonneg _) hD).mpr (hbound n p hp j))
    _ = 3*D^2 := by simp


#print axioms kernelBarrier_sublevel_isCompact
#print axioms kernelExhaustionCutoff_scaled_fderiv_bound
#print axioms kernelExhaustionCutoff_fderiv_eventually_zero
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
