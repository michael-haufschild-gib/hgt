/-
Uniform polynomial kernels adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.GaussSums.FreeReflectionPools

/-!
# Uniform polynomial kernels

Uniformly twisted Schwartz sources and the uniform polynomial kernel condition
`HasUniformPolynomialKernel`. Fixed logarithmic localization transfers derivative bounds to
Fourier decay; coefficient moment bounds.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap

namespace CompletedHeight
open SchwartzPlanePoisson MeasureTheory Filter Set
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff Topology

open CompletedGauss

/-- The compactly supported square-root weighted source is a Schwartz function. -/
def vstarSchwartz (W : ℝ → ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) : SchwartzMap ℝ ℂ :=
  (HasCompactSupport.of_support_subset_isCompact isCompact_Icc (Vstar_support W a b hs)).toSchwartzMap
    (Vstar_contDiff W a b ha hs hW)

def HasPolynomialKernel (P : ℝ→ ℝ→ ℂ) : Prop :=
  (∀t,ContDiffOn ℝ ∞ (paperKernel (Vstar (P t))) (Set.Ioi 0)) ∧
  ∀ A K : ℕ,∃n : ℕ,∃C : ℝ,0<C ∧ ∀t : ℝ,∀i≤ K,∀x : ℝ,0<x → 
    (1+x)^A*‖LocalLogFourier.eulerDeriv (paperKernel (Vstar (P t))) i x‖≤ 
      C*(1+‖t‖)^n

theorem normTwistedSource_polynomial_kernel (W : ℝ→ ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    HasPolynomialKernel (normTwistedSource W) := by
  let S := vstarSchwartz W a b ha hsupp hW
  have hS : Function.support (S : ℝ→ ℂ) ⊆ Set.Icc a b := Vstar_support W a b hsupp
  obtain ⟨G,hG,hbound⟩ := normTwistedSource_schwartz S a b ha hS
  have hlink (t : ℝ) : (G t : ℝ→ ℂ)=Vstar (normTwistedSource W t) := by
    funext x
    rw [hG t x]
    change kernelLogPhase t (Real.log x)*((Real.sqrt x:ℂ)*W x)=
      (Real.sqrt x:ℂ)*(kernelLogPhase t (Real.log x)*W x)
    ring
  have hGs (t : ℝ) : Function.support (G t : ℝ→ ℂ)⊆Set.Icc a b := by
    intro x hx
    change G t x≠0 at hx
    rw [hG t x] at hx
    exact hS (normTwistedSource_support S t hx)
  constructor
  · intro t
    rw [←hlink t]
    exact paperKernel_compact_source_smooth (G t) a b ha (hGs t) ((G t).smooth ⊤)
  · intro A K
    obtain ⟨s,D,hD,hkernel⟩ := paperKernel_euler_source_uniform_weighted_bound a b ha A K
    obtain ⟨n,C,hC,hsource⟩ := hbound s
    refine ⟨n,D*C,mul_pos hD hC,?_⟩
    intro t i hi x hx
    rw [←hlink t]
    exact (hkernel (G t) (hGs t) i hi x hx).trans
      ((mul_le_mul_of_nonneg_left (hsource t) hD.le).trans_eq (by ring))


end CompletedHeight

namespace CompletedHeight

section

open MeasureTheory Filter Set
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff Topology
open SchwartzPlanePoisson JointLogSeparation

def fixedLogReturnCLM (a b : ℝ) (ha : 0 < a) : 𝓢(ℝ,ℂ) →L[ℝ] 𝓢(ℝ,ℂ) :=
  (SchwartzMap.smulLeftCLM ℂ (positiveCutoff a b ha)).comp
    (SchwartzMap.compCLM ℝ
      (patchedLog_temperate (a/2) (max a b+a/2) (by linarith))
      (patchedLog_proper (a/2) (max a b+a/2) (by linarith)))

lemma fixedLogReturnCLM_apply (a b : ℝ) (ha : 0 < a) (g : 𝓢(ℝ,ℂ)) (x : ℝ) :
    fixedLogReturnCLM a b ha g x = positiveCutoff a b ha x •
      g (patchedLog (a/2) (max a b+a/2) (by linarith) x) := by
  rw [fixedLogReturnCLM,ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply
      ((positiveCutoff a b ha).hasCompactSupport.hasTemperateGrowth (positiveCutoff a b ha).contDiff)]
  rfl

lemma positiveCutoff_support_bounds (a b : ℝ) (ha : 0 < a) (x : ℝ)
    (hx : positiveCutoff a b ha x ≠ 0) : x ∈ Icc (a/2) (max a b+a/2) := by
  have hm : x ∈ Function.support (positiveCutoff a b ha) := hx
  rw [(positiveCutoff a b ha).support_eq] at hm
  change dist x ((a+max a b)/2) < (max a b-a)/2+a/2 at hm
  rw [Real.dist_eq,abs_lt] at hm
  constructor <;> linarith [hm.1,hm.2]

theorem frequencyTwist_finite_uniform_degree (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ, ∀g : 𝓢(ℝ,ℂ), ∃C : ℝ, 0 < C ∧ ∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (frequencyTwist g t) ≤ C*(1+‖t‖)^n := by
  let n := S.sup Prod.snd
  refine ⟨n,?_⟩
  intro g
  let c : ℕ×ℕ → ℝ := fun z => (2:ℝ)^z.2*(1+2*Real.pi)^z.2*derivativeSeminormSum g z.1 z.2
  let C := 1+∑z∈S,c z
  have hc : ∀z,0≤c z := fun z => by dsimp [c]; exact mul_nonneg (by positivity) (derivativeSeminormSum_nonneg _ _ _)
  have hC : 0<C := by dsimp [C]; have := Finset.sum_nonneg (fun z (_ : z∈S) => hc z); linarith
  refine ⟨C,hC,?_⟩
  intro t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzC : c z≤C := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S) => hc z) hz
    dsimp [C]
    linarith
  have hzn : z.2≤n := Finset.le_sup hz
  exact (frequencyTwist_seminorm_polynomial g t z.1 z.2).trans
    (mul_le_mul hzC (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hzn) (by positivity) hC.le)

def uniformTwistedSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  fixedLogReturnCLM a b ha (frequencyTwist (kernelLogSource W a b ha hs hW) t)

lemma uniformTwistedSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    uniformTwistedSchwartz W a b ha hs hW t x = normTwistedSource W t x := by
  rw [uniformTwistedSchwartz,fixedLogReturnCLM_apply,frequencyTwist_apply,
    kernelLogSource_apply]
  by_cases hc : positiveCutoff a b ha x=0
  · have hx : W x=0 := by
      by_contra hx
      have := positiveCutoff_one a b ha x (hs hx)
      exact zero_ne_one (hc.symm.trans this)
    simp only [hc,zero_smul,normTwistedSource,hx,mul_zero]
  · have hb := positiveCutoff_support_bounds a b ha x hc
    have hx : 0 < x := by linarith [hb.1]
    rw [patchedLog_eq_log _ _ _ x hb,Real.exp_log hx]
    by_cases hw : W x=0
    · simp only [hw,mul_zero,smul_zero,normTwistedSource]
    · rw [positiveCutoff_one a b ha x (hs hw),one_smul]
      rfl

theorem normTwistedSource_uniform_degree (a b : ℝ) (ha : 0 < a) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∀W : ℝ→ℂ,∀hs : Function.support W ⊆ Icc a b,∀hW : ContDiff ℝ ∞ W,
    ∃C : ℝ,0<C ∧ ∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (uniformTwistedSchwartz W a b ha hs hW t) ≤
        C*(1+‖t‖)^n := by
  obtain ⟨s,C,hC,hcontrol⟩ := SchwartzPlanePoisson.schwartzCLM_finite_seminorm_control
    (fixedLogReturnCLM a b ha) S
  obtain ⟨n,hn⟩ := frequencyTwist_finite_uniform_degree s
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hbound⟩ := hn (kernelLogSource W a b ha hs hW)
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro t
  exact (hcontrol _).trans ((mul_le_mul_of_nonneg_left (hbound t) hC.le).trans_eq (by ring))

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open CompletedGauss

def HasUniformPolynomialKernel {κ : Type*} (P : κ→ℝ→ℝ→ℂ) : Prop :=
  (∀w t,ContDiffOn ℝ ∞ (paperKernel (Vstar (P w t))) (Set.Ioi 0)) ∧
  ∀ A K : ℕ,∃n : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀t : ℝ,∀i≤K,∀x : ℝ,0<x →
    (1+x)^A*‖LocalLogFourier.eulerDeriv (paperKernel (Vstar (P w t))) i x‖≤
      C*(1+‖t‖)^n

abbrev SupportedSmoothSource (a b : ℝ) :=
  {W : ℝ→ℂ // Function.support W⊆Set.Icc a b ∧ ContDiff ℝ ∞ W}

theorem normTwistedSource_uniform_polynomial_kernel (a b : ℝ) (ha : 0<a) :
    HasUniformPolynomialKernel (fun W : SupportedSmoothSource a b => normTwistedSource W.val) := by
  constructor
  · intro W t
    exact (normTwistedSource_polynomial_kernel W.val a b ha W.property.1 W.property.2).1 t
  · intro A K
    obtain ⟨s,D,hD,hkernel⟩ := paperKernel_euler_source_uniform_weighted_bound a b ha A K
    obtain ⟨n,hn⟩ := normTwistedSource_uniform_degree a b ha s
    refine ⟨n,?_⟩
    intro W
    let S := vstarSchwartz W.val a b ha W.property.1 W.property.2
    have hS : Function.support (S : ℝ→ℂ)⊆Set.Icc a b := Vstar_support W.val a b W.property.1
    let G := uniformTwistedSchwartz S a b ha hS (S.smooth ⊤)
    obtain ⟨C,hC,hsource⟩ := hn S hS (S.smooth ⊤)
    have hlink (t : ℝ) : (G t : ℝ→ℂ)=Vstar (normTwistedSource W.val t) := by
      funext x
      rw [show G t x=uniformTwistedSchwartz S a b ha hS (S.smooth ⊤) t x from rfl,
        uniformTwistedSchwartz_apply]
      change kernelLogPhase t (Real.log x)*((Real.sqrt x:ℂ)*W.val x)=
        (Real.sqrt x:ℂ)*(kernelLogPhase t (Real.log x)*W.val x)
      ring
    have hGs (t : ℝ) : Function.support (G t : ℝ→ℂ)⊆Set.Icc a b := by
      intro x hx
      change G t x≠0 at hx
      rw [show G t x=uniformTwistedSchwartz S a b ha hS (S.smooth ⊤) t x from rfl,
        uniformTwistedSchwartz_apply] at hx
      exact hS (normTwistedSource_support S t hx)
    refine ⟨D*C,mul_pos hD hC,?_⟩
    intro t i hi x hx
    rw [←hlink t]
    exact (hkernel (G t) (hGs t) i hi x hx).trans
      ((mul_le_mul_of_nonneg_left (hsource t) hD.le).trans_eq (by ring))


end CompletedHeight

namespace CompletedHeight
open SchwartzPlanePoisson CompletedGauss MeasureTheory Filter Set
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff Topology

/-- Fixed logarithmic localization transfers derivative bounds linearly to Fourier decay. -/
theorem localized_fourier_linear_bound
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (M : ℝ)
    (hχs : Function.support χ ⊆ Set.Icc (-M) M) (N j : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ F : ℝ → ℝ → ℂ,
      (∀ R, 0 < R → ContDiff ℝ ∞ (F R)) → ∀ C : ℝ, 0 ≤ C →
      (∀ i ≤ j, ∀ R, 0 < R → ∀ u, |u| ≤ M →
        (1+R)^N * ‖iteratedDeriv i (F R) u‖ ≤ C) →
      ∀ R, 0 < R → ∀ t,
        (1+R)^N * (1+|t|)^j * ‖𝓕 (fun u => χ u * F R u) t‖ ≤ D*C := by
  obtain ⟨D₀,hD₀,h₀⟩ := localized_derivative_linear_bound χ hχ M hχs N 0
  obtain ⟨Dj,hDj,hj⟩ := localized_derivative_linear_bound χ hχ M hχs N j
  let V := volume.real (Set.Icc (-M) M)+1
  let C₀ := D₀*V
  let Cj := Dj*V/(2*Real.pi)^j
  have hV : 0<V := by dsimp only [V]; positivity
  have hC₀ : 0<C₀ := mul_pos hD₀ hV
  have hCj : 0<Cj := by dsimp only [Cj]; positivity
  refine ⟨2^j*(C₀+Cj),by positivity,?_⟩
  intro F hF C hC hb R hR t
  let G := fun u => χ u*F R u
  have hG : ContDiff ℝ ∞ G := hχ.mul (hF R hR)
  have hGs : Function.support G ⊆ Set.Icc (-M) M := by
    intro u hu
    exact hχs (mul_ne_zero_iff.mp hu).1
  have hb₀ := compact_fourier_power_linear_bound G hG (Set.Icc (-M) M) isCompact_Icc hGs
    ((1+R)^N) (D₀*C) (by positivity) (mul_nonneg hD₀.le hC) 0
    (h₀ F hF C hC (fun i hi => hb i (hi.trans (Nat.zero_le j))) R hR) t
  have hbj := compact_fourier_power_linear_bound G hG (Set.Icc (-M) M) isCompact_Icc hGs
    ((1+R)^N) (Dj*C) (by positivity) (mul_nonneg hDj.le hC) j
    (hj F hF C hC hb R hR) t
  have hzero : (1+R)^N*‖𝓕 G t‖ ≤ C₀*C := by
    simpa only [pow_zero,one_mul,div_one,C₀,V,mul_assoc,mul_left_comm,mul_comm] using hb₀
  have hpower : (1+R)^N*(|t|^j*‖𝓕 G t‖) ≤ Cj*C := by
    convert hbj using 1 <;> dsimp only [Cj,V] <;> ring
  change (1+R)^N*(1+|t|)^j*‖𝓕 G t‖ ≤ _
  by_cases ht : |t|≤1
  · have hp : (1+|t|)^j ≤ (2:ℝ)^j := by gcongr; linarith
    calc
      _ ≤ (1+R)^N*2^j*‖𝓕 G t‖ := by gcongr
      _ = 2^j*((1+R)^N*‖𝓕 G t‖) := by ring
      _ ≤ 2^j*(C₀*C) := mul_le_mul_of_nonneg_left hzero (by positivity)
      _ ≤ _ := by
        have hh:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (show C₀≤C₀+Cj from le_add_of_nonneg_right hCj.le) hC) (by positivity : 0≤(2:ℝ)^j)
        simpa only [mul_assoc] using hh
  · have hp : (1+|t|)^j ≤ (2*|t|)^j := by gcongr; linarith
    calc
      _ ≤ (1+R)^N*(2*|t|)^j*‖𝓕 G t‖ := by gcongr
      _ = 2^j*((1+R)^N*(|t|^j*‖𝓕 G t‖)) := by rw [mul_pow]; ring
      _ ≤ 2^j*(Cj*C) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ _ := by
        have hh:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (show Cj≤C₀+Cj from le_add_of_nonneg_left hC₀.le) hC) (by positivity : 0≤(2:ℝ)^j)
        simpa only [mul_assoc] using hh

/-- Euler bounds control logarithmic derivatives uniformly in the source parameter. -/
theorem uniform_polynomial_localized_fourier {κ : Type*}
    (P : κ → ℝ → ℝ → ℂ) (hP : HasUniformPolynomialKernel P)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (M : ℝ) (hM : 0≤M)
    (hχs : Function.support χ ⊆ Set.Icc (-M) M) (A J : ℕ) :
    ∃ n : ℕ, ∀ w : κ, ∃ C : ℝ, 0<C ∧ ∀ θ R : ℝ, 0<R → ∀ t : ℝ,
      (1+R)^A*(1+|t|)^J*
        ‖𝓕 (fun u => χ u*paperKernel (Vstar (P w θ)) (R*Real.exp u)) t‖ ≤ C*(1+‖θ‖)^n := by
  obtain ⟨n,hn⟩ := hP.2 A J
  obtain ⟨D,hD,hFourier⟩ := localized_fourier_linear_bound χ hχ M hχs A J
  refine ⟨n,?_⟩
  intro w
  obtain ⟨C,hC,hkernel⟩ := hn w
  refine ⟨D*(Real.exp M)^A*C,by positivity,?_⟩
  intro θ R hR t
  let F := fun R u => paperKernel (Vstar (P w θ)) (R*Real.exp u)
  have hF (R : ℝ) (hR : 0<R) : ContDiff ℝ ∞ (F R) := by
    rw [contDiff_iff_contDiffAt]
    intro u
    exact ((hP.1 w θ).contDiffAt (isOpen_Ioi.mem_nhds (mul_pos hR (Real.exp_pos u)))).comp (g:=paperKernel (Vstar (P w θ)))
      (f:=fun v : ℝ=>R*Real.exp v) u (contDiff_const.mul Real.contDiff_exp).contDiffAt
  have hb (i : ℕ) (hi : i≤J) (R : ℝ) (hR : 0<R) (u : ℝ) (hu : |u|≤M) :
      (1+R)^A*‖iteratedDeriv i (F R) u‖ ≤ (Real.exp M)^A*(C*(1+‖θ‖)^n) := by
    have hE : 1≤Real.exp M := by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hM
    have hEu : 1≤Real.exp M*Real.exp u := by
      rw [←Real.exp_add]
      exact Real.one_le_exp (by linarith [(abs_le.mp hu).1])
    have hbase : 1+R≤Real.exp M*(1+R*Real.exp u) := by
      have hr:=mul_le_mul_of_nonneg_left hEu hR.le
      nlinarith only [hE,hr]
    have hp : (1+R)^A≤(Real.exp M)^A*(1+R*Real.exp u)^A := by
      rw [←mul_pow]
      exact pow_le_pow_left₀ (by positivity) hbase A
    dsimp only [F]
    rw [LocalLogFourier.iteratedDeriv_log_eq_euler]
    calc
      _ ≤ ((Real.exp M)^A*(1+R*Real.exp u)^A)*
          ‖LocalLogFourier.eulerDeriv (paperKernel (Vstar (P w θ))) i (R*Real.exp u)‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ (Real.exp M)^A*(C*(1+‖θ‖)^n) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (hkernel θ i hi _ (mul_pos hR (Real.exp_pos u))) (by positivity)
  have hh:=hFourier F hF ((Real.exp M)^A*(C*(1+‖θ‖)^n)) (by positivity) hb R hR t
  exact hh.trans_eq (by ring)

end CompletedHeight

namespace CompletedHeight
open SchwartzPlanePoisson CompletedGauss MeasureTheory Filter Set
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff Topology

/-- Two extra Fourier powers give an integrable envelope with the same uniform height degree. -/
theorem uniform_polynomial_localized_envelope {κ : Type*}
    (P : κ → ℝ → ℝ → ℂ) (hP : HasUniformPolynomialKernel P)
    (χ : ℝ → ℂ) (hχ : ContDiff ℝ ∞ χ) (M : ℝ) (hM : 0≤M)
    (hχs : Function.support χ ⊆ Set.Icc (-M) M) (A J : ℕ) :
    ∃n : ℕ, ∀w : κ, ∃C : ℝ, 0<C ∧ ∀θ R : ℝ, 0<R → ∃B : SchwartzMap ℝ ℂ,
      (∀u,χ u*paperKernel (Vstar (P w θ)) (R*Real.exp u)=𝓕⁻ (B : ℝ → ℂ) u) ∧
      Integrable (fun t : ℝ => (1+|t|)^J*‖B t‖) ∧
      (1+R)^A*(∫t : ℝ,(1+|t|)^J*‖B t‖)≤C*(1+‖θ‖)^n ∧
      ∀t : ℝ,(1+R)^A*(1+|t|)^J*‖B t‖≤C*(1+‖θ‖)^n := by
  obtain ⟨n,hn⟩ := uniform_polynomial_localized_fourier P hP χ hχ M hM hχs A (J+2)
  let I : ℝ := ∫t : ℝ,((1+|t|)^(2:ℕ))⁻¹
  have hI : 0≤I := integral_nonneg (fun _ => by positivity)
  refine ⟨n,?_⟩
  intro w
  obtain ⟨C,hC,hb⟩ := hn w
  refine ⟨C*(I+1),by positivity,?_⟩
  intro θ R hR
  let F := fun u => χ u*paperKernel (Vstar (P w θ)) (R*Real.exp u)
  have hFs : Function.support F ⊆ Set.Icc (-M) M := by
    intro u hu
    exact hχs (mul_ne_zero_iff.mp hu).1
  have hFc : HasCompactSupport F := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hFs
  have hFlow : ContDiff ℝ ∞ (fun u => paperKernel (Vstar (P w θ)) (R*Real.exp u)) := by
    rw [contDiff_iff_contDiffAt]
    intro u
    exact ((hP.1 w θ).contDiffAt (isOpen_Ioi.mem_nhds (mul_pos hR (Real.exp_pos u)))).comp (g:=paperKernel (Vstar (P w θ)))
      (f:=fun v : ℝ=>R*Real.exp v) u (contDiff_const.mul Real.contDiff_exp).contDiffAt
  let S : SchwartzMap ℝ ℂ := hFc.toSchwartzMap (hχ.mul hFlow)
  have he (u : ℝ) : F u=𝓕⁻ (𝓕 (S : ℝ → ℂ)) u :=
    (S.integrable.fourierInv_fourier_eq (𝓕 S).integrable S.continuous.continuousAt).symm
  have hbound := weighted_fourier_L1_bound (𝓕 (S : ℝ → ℂ)) (𝓕 S).continuous
    ((1+R)^A) (C*(1+‖θ‖)^n) (by positivity) (by positivity) J (hb θ R hR)
  refine ⟨𝓕 S,he,hbound.1,?_,?_⟩
  · apply hbound.2.trans
    change (C*(1+‖θ‖)^n)*I ≤ (C*(I+1))*(1+‖θ‖)^n
    nlinarith only [show 0≤C*(1+‖θ‖)^n by positivity]
  · intro t
    have hp : (1+|t|)^J≤(1+|t|)^(J+2) :=
      pow_le_pow_right₀ (by linarith [abs_nonneg t]) (by omega)
    calc
      _≤(1+R)^A*(1+|t|)^(J+2)*‖(𝓕 S) t‖ := by gcongr
      _≤C*(1+‖θ‖)^n := hb θ R hR t
      _≤(C*(I+1))*(1+‖θ‖)^n := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact le_mul_of_one_le_right hC.le (by linarith)

end CompletedHeight

namespace CompletedHeight
open Eisenstein SchwartzPlanePoisson CompletedGauss CanonicalRowCompletion MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap ContDiff Topology

/-- Fixed logarithmic windows separate uniformly over the compactly supported source family. -/
theorem uniform_polynomial_kernel_log_separation {κ ι : Type*} [Fintype ι]
    (P : κ → ℝ → ℝ → ℂ) (hP : HasUniformPolynomialKernel P)
    (W : ι → ℝ → ℂ) (slope M : ι → ℝ)
    (hM : ∀i,0≤M i) (hW : ∀i u,W i u≠0 → |u|≤M i) (N J : ℕ) :
    ∃n : ℕ,∀w : κ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : SchwartzMap ℝ ℂ,
      (∀y : ι → ℝ,(∏i,W i (y i))*paperKernel (Vstar (P w θ))
        (R*Real.exp (∑i,slope i*y i))=
        ∫t : ℝ,(∏i,W i (y i)*kernelLogPhase t (slope i*y i))*B t) ∧
      Integrable (fun t : ℝ => (1+‖t‖)^J*‖B t‖) ∧
      (1+R)^N*(∫t : ℝ,(1+‖t‖)^J*‖B t‖)≤C*(1+‖θ‖)^n ∧
      ∀t : ℝ,(1+R)^N*(1+‖t‖)^J*‖B t‖≤C*(1+‖θ‖)^n := by
  classical
  let L : ℝ := ∑ i, |slope i| * M i
  have hL : 0 ≤ L := Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hM i))
  let χ₀ : ContDiffBump (0 : ℝ) :=
    ⟨L + 1, L + 2, by linarith, by linarith⟩
  let χ : ℝ → ℂ := fun u => (χ₀ u : ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp χ₀.contDiff
  have hχs : Function.support χ ⊆ Set.Icc (-(L + 2)) (L + 2) := by
    intro u hu
    have hu₀ : u ∈ Function.support χ₀ := by
      change χ₀ u ≠ 0
      intro hz
      exact hu (by simp only [χ, hz, Complex.ofReal_zero])
    rw [χ₀.support_eq] at hu₀
    have habs : |u| < L + 2 := by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hu₀
    exact abs_le.mp habs.le
  have hχone (u : ℝ) (hu : |u| ≤ L) : χ u = 1 := by
    have hu₀ : u ∈ Metric.closedBall (0 : ℝ) χ₀.rIn := by
      change dist u 0 ≤ L + 1
      rw [Real.dist_eq, sub_zero]
      linarith
    simp only [χ, χ₀.one_of_mem_closedBall hu₀, Complex.ofReal_one]
  obtain ⟨n, hn⟩ := uniform_polynomial_localized_envelope P hP
    χ hχ (L + 2) (by linarith) hχs N J
  refine ⟨n,?_⟩
  intro w
  obtain ⟨C,hC,hb⟩ := hn w
  refine ⟨C,hC.le,?_⟩
  intro θ R hR
  obtain ⟨B, hsep, hi, hI, hpt⟩ := hb θ R hR
  refine ⟨B, ?_, ?_⟩
  swap
  · simpa only [Real.norm_eq_abs] using And.intro hi (And.intro hI hpt)
  intro y
  have hprod (t : ℝ) : (∏ i, W i (y i) * kernelLogPhase t (slope i * y i)) =
      (∏ i, W i (y i)) * kernelLogPhase t (∑ i, slope i * y i) := by
    rw [Finset.prod_mul_distrib, kernelLogPhase_sum]
  simp_rw [hprod, mul_assoc]
  rw [integral_const_mul]
  by_cases hz : (∏ i, W i (y i)) = 0
  · simp only [hz, zero_mul]
  · congr 1
    have hwy (i : ι) : W i (y i) ≠ 0 := by
      exact (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
    have hys : |∑ i, slope i * y i| ≤ L := by
      calc
        _ ≤ ∑ i, |slope i * y i| := by
          simpa only [Real.norm_eq_abs] using norm_sum_le (s := Finset.univ) (f := fun i => slope i * y i)
        _ ≤ L := Finset.sum_le_sum (fun i _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hW i (y i) (hwy i)) (abs_nonneg _))
    have he := hsep (∑ i, slope i * y i)
    rw [hχone _ hys, one_mul, Real.fourierInv_eq'] at he
    simp only [smul_eq_mul] at he
    convert he using 1
    apply integral_congr_ae
    filter_upwards [] with t
    congr 1
    unfold kernelLogPhase
    congr 1
    simp only [RCLike.inner_apply, conj_trivial]
    push_cast
    ring


theorem uniform_polynomial_kernel_three_window {κ : Type*}
    (P : κ→ℝ→ℝ→ℂ) (hP : HasUniformPolynomialKernel P)
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂) (A : ℕ) :
    ∃n : ℕ,∀w : κ,∃C : ℝ,0≤C ∧ ∀θ R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀r u v : ℝ,V₀ r*V₁ u*V₂ v*paperKernel (Vstar (P w θ))
        (R*Real.exp (-2*r+u+3*v))=
        ∫t : ℝ,(V₀ r*kernelLogPhase t (-2*r))*
          (V₁ u*kernelLogPhase t u)*(V₂ v*kernelLogPhase t (3*v))*B t) ∧
      (1+R)^A*(∫t : ℝ,‖B t‖)≤C*(1+‖θ‖)^n := by
  let V : Fin 3→ℝ→ℂ := ![V₀,V₁,V₂]
  let slope : Fin 3→ℝ := ![-2,1,3]
  let M : Fin 3→ℝ := ![M₀,M₁,M₂]
  have hm : ∀i,0≤M i := by intro i; fin_cases i <;> assumption
  have hv : ∀i y,V i y≠0 → |y|≤M i := by intro i; fin_cases i <;> assumption
  obtain ⟨n,hn⟩ := uniform_polynomial_kernel_log_separation P hP V slope M hm hv A 0
  refine ⟨n,?_⟩
  intro w
  obtain ⟨C,hC,h⟩ := hn w
  refine ⟨C,hC,?_⟩
  intro θ R hR
  obtain ⟨B,hB,hi,hbound,hpoint⟩ := h θ R hR
  refine ⟨B,?_,by simpa only [pow_zero,one_mul] using hbound⟩
  intro r u v
  simpa [V,slope,Fin.prod_univ_succ,Fin.sum_univ_succ,mul_assoc,add_assoc] using hB ![r,u,v]

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform

namespace CompletedHeight
open CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion
open CanonicalQuadraticSieve
theorem uniform_polynomial_smooth_quadratic {κ : Type*}
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (P : κ→ℝ→ℝ→ℂ) (hP : HasUniformPolynomialKernel P)
    (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K U B lengthScale R : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale → 0<R →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,(∀n∈S,∀v∈T,‖β n v‖≤lengthScale) →
    ∀yr : idealRange K→ℝ,∀yn yb : Ideal O→ℝ,
    (∑k : idealRange K,‖∑n∈S,∑v∈T,
      canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*β n v*
      (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*paperKernel (Vstar (P w θ))
        (R*Real.exp (-2*yr k+yn n+3*yb v)))‖^2)≤
      (C*(1+‖θ‖)^heightDegree)*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2/(1+R)^(2*A) := by
  obtain ⟨Cq,hCq,hq⟩ := integrated_product_quadratic ε hε
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_kernel_three_window P hP V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ A
  refine ⟨2*heightDegree,?_⟩
  intro w
  obtain ⟨Ck₀,hCk₀,hkernel⟩ := hheight w
  refine ⟨Cq*(Ck₀^2+1),by positivity,?_⟩
  intro θ K U B lengthScale R hK hU hB hL hR S T hS hT β hβ yr yn yb
  let Ck := Ck₀*(1+‖θ‖)^heightDegree
  have hCk : 0≤Ck := by dsimp [Ck]; positivity
  have hCoeff : Cq*(Ck^2+1)≤(Cq*(Ck₀^2+1))*(1+‖θ‖)^(2*heightDegree) := by
    have hh : 1≤(1+‖θ‖)^(2*heightDegree) := one_le_pow₀ (by linarith [norm_nonneg θ])
    have he : Ck^2=Ck₀^2*(1+‖θ‖)^(2*heightDegree) := by
      dsimp [Ck]
      rw [mul_pow,←pow_mul]
      congr 2
      omega
    rw [he]
    nlinarith [sq_nonneg Ck₀]
  obtain ⟨g,hsep,hg⟩ := hkernel θ R hR
  change (1+R)^A*(∫t : ℝ,‖g t‖)≤Ck at hg
  let rowPhase : idealRange K→ℝ→ℂ := fun k t => V₀ (yr k)*kernelLogPhase t (-2*yr k)
  let βt : ℝ→Ideal O→Ideal O→ℂ := fun t n v =>
    β n v*(V₁ (yn n)*kernelLogPhase t (yn n))*(V₂ (yb v)*kernelLogPhase t (3*yb v))
  have hphase (t x : ℝ) : ‖kernelLogPhase t x‖=1 := kernelLogPhase_norm t x
  have hrowPhase (k : idealRange K) (t : ℝ) : ‖rowPhase k t‖≤1 := by
    simp only [rowPhase,norm_mul,hphase,mul_one]
    exact hV₀n _
  have hβt (t : ℝ) (n : Ideal O) (hn : n∈S) (v : Ideal O) (hv : v∈T) : ‖βt t n v‖≤lengthScale := by
    simp only [βt,norm_mul,hphase,mul_one]
    exact (mul_le_of_le_one_right (by positivity)
      (hV₂n _)).trans ((mul_le_of_le_one_right (norm_nonneg _) (hV₁n _)).trans (hβ n hn v hv))
  have hrowPhasec (k : idealRange K) : Continuous (rowPhase k) :=
    continuous_const.mul (kernelLogPhase_continuous_left _)
  have hβtc (n v : Ideal O) : Continuous (fun t => βt t n v) :=
    (continuous_const.mul (continuous_const.mul (kernelLogPhase_continuous_left _))).mul
      (continuous_const.mul (kernelLogPhase_continuous_left _))
  have hi := hq K U B lengthScale hK hU hB hL S T hS hT βt hβtc hβt rowPhase hrowPhasec hrowPhase g
  have he (k : idealRange K) :
      (∑n∈S,∑v∈T,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*β n v*
        (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*paperKernel (Vstar (P w θ))
          (R*Real.exp (-2*yr k+yn n+3*yb v)))) =
      ∫t : ℝ,g t*(rowPhase k t*∑n∈S,∑v∈T,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*βt t n v) := by
    have hint (n v : Ideal O) : Integrable (fun t : ℝ =>
        g t*(rowPhase k t*(canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*βt t n v))) := by
      apply g.integrable.mul_bdd (c := ‖canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*β n v‖)
      · exact ((hrowPhasec k).mul (continuous_const.mul (hβtc n v))).aestronglyMeasurable
      · filter_upwards [] with t
        simp only [rowPhase,βt,norm_mul,hphase,mul_one]
        have hv01 : ‖V₀ (yr k)‖*‖V₁ (yn n)‖≤1 := by
          simpa only [one_mul] using mul_le_mul (hV₀n (yr k)) (hV₁n (yn n)) (norm_nonneg _) zero_le_one
        have hv012 : (‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖≤1 := by
          simpa only [one_mul] using mul_le_mul hv01 (hV₂n (yb v)) (norm_nonneg _) zero_le_one
        calc
          _ = (‖canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))‖*‖β n v‖)*
            ((‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖) := by ring
          _ ≤ (‖canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))‖*‖β n v‖)*1 :=
            mul_le_mul_of_nonneg_left hv012 (by positivity)
          _ = _ := by ring
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ (fun n hn => integrable_finsetSum _ (fun v hv => hint n v))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_finsetSum _ (fun v hv => hint n v)]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hsep (yr k) (yn n) (yb v),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [rowPhase,βt]
    ring
  simp_rw [he]
  apply hi.trans
  have hpow : 0<(1+R)^A := by positivity
  have hmass : (∫t : ℝ,‖g t‖)≤Ck/(1+R)^A := (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hg)
  have hmass2 := pow_le_pow_left₀ (integral_nonneg (fun t => norm_nonneg _)) hmass 2
  have hbase : 0≤Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2 := by positivity
  calc
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*(Ck/(1+R)^A)^2 :=
      mul_le_mul_of_nonneg_left hmass2 hbase
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*((Ck^2+1)/(1+R)^(2*A)) := by
      apply mul_le_mul_of_nonneg_left _ hbase
      rw [div_pow,←pow_mul]
      have hp : A*2=2*A := Nat.mul_comm _ _
      rw [hp]
      exact div_le_div_of_nonneg_right (by nlinarith : Ck^2≤Ck^2+1) (by positivity)
    _ = (Cq*(Ck^2+1))*((K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)/(1+R)^(2*A) := by ring
    _ ≤ _ := by
      have hb := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCoeff (by positivity : 0≤(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2))
        (by positivity : 0≤(1+R)^(2*A))
      simpa only [div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hb

end CompletedHeight

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CompletedHeight
open CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion CompletedDyadic
open CanonicalQuadraticSieve
theorem uniform_polynomial_smooth_series_rowPhase {κ : Type*}
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (P : κ→ℝ→ℝ→ℂ) (hP : HasUniformPolynomialKernel P)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K Y H : ℝ,1≤K → 0<Y → 0<H →
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀I∈S i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀β : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖β i n v‖≤
        1/(Real.sqrt ((2:ℝ)^i.2.2)*(2:ℝ)^i.2.1*ramifiedScale ρ q i.1*Real.sqrt H)) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,
        σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*Y)^(2*deltaLoss)*(K+Y)/H := by
  obtain ⟨A,hA⟩ := exists_nat_gt (deltaLoss+1/2)
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_smooth_quadratic V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ hV₀n hV₁n hV₂n P hP A (2*deltaLoss) (by positivity)
  obtain ⟨Cs,hCs,hsum⟩ := normMajorant_sum_bound deltaLoss A ρ q hδ hA hρ hq
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hquadbase⟩ := hheight w
  refine ⟨2*Cbase*Cs^2,by positivity,?_⟩
  intro θ K Y H hK hY hH S T hS hT β hβ σ hσ
  let Cq := Cbase*(1+‖θ‖)^heightDegree
  have hCq : 0<Cq := by dsimp [Cq]; positivity
  have hquad := hquadbase θ
  have hKp : 0<K := by linarith
  have hqp : 0<q := by linarith
  let g : (ℕ×ℕ×ℕ)→ℝ := fun i => Real.sqrt Cq *
    normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
  have hg0 (i : ℕ×ℕ×ℕ) : 0≤g i := by
    dsimp [g]
    exact mul_nonneg (Real.sqrt_nonneg _) (normMajorant_nonneg _ _ _ _ _ _ _ _
      hKp (by positivity) (ramifiedScale_pos ρ q hρ hqp _) hH (by positivity) (by positivity))
  have henergy (i : ℕ×ℕ×ℕ) :
      (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖^2)
        ≤(g i)^2 := by
    let U : ℝ := (2:ℝ)^i.2.2
    let B : ℝ := (2:ℝ)^i.2.1
    let r : ℝ := ramifiedScale ρ q i.1
    let R : ℝ := Y⁻¹*r^3*B^3*U
    have hU : 1≤U := one_le_pow₀ (by norm_num)
    have hB : 1≤B := one_le_pow₀ (by norm_num)
    have hUp : 0<U := by positivity
    have hBp : 0<B := by positivity
    have hr : 0<r := ramifiedScale_pos ρ q hρ hqp _
    have hR : 0<R := by dsimp [R]; positivity
    have h := hquad K U B (1/(Real.sqrt U*B*r*Real.sqrt H)) R
      hK hU hB (by positivity) hR (S i) (T i) (hS i) (hT i) (β i) (hβ i)
      (fun k => Real.log ((Ideal.absNorm k.val:ℝ)/K))
      (fun n => Real.log ((Ideal.absNorm n:ℝ)/U))
      (fun v => Real.log ((Ideal.absNorm v:ℝ)/B))
    change (∑k,‖completedSmoothDyadicBlock V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖^2)≤_ at h
    have hphase : (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖^2)≤
        ∑k : idealRange K,‖completedSmoothDyadicBlock V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hσ i k)
    apply (hphase.trans h).trans
    have he : Cq*(K*(U*B))^(2*deltaLoss)*(K+U*B)*(U*B)*
        (1/(Real.sqrt U*B*r*Real.sqrt H))^2/(1+R)^(2*A)=
        Cq*((K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+R)^(2*(A:ℝ))) := by
      rw [show 2*(A:ℝ)=((2*A:ℕ):ℝ) by norm_num,Real.rpow_natCast]
      simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt hUp.le,Real.sq_sqrt hH.le]
      field_simp

    rw [he]
    have hm := smooth_energy_le_normMajorant_sq deltaLoss A K Y⁻¹ r H U B
      hKp (by positivity) hr hH hUp hBp
    calc
      _ ≤ Cq*(normMajorant deltaLoss A K Y⁻¹ r H U B)^2 := mul_le_mul_of_nonneg_left hm hCq.le
      _ = (g i)^2 := by dsimp [g,U,B,r]; rw [mul_pow,Real.sq_sqrt hCq.le]
  obtain ⟨hs,hb⟩ := hsum K Y H hKp hY hH
  have hm := finite_tsum_energy_bound
    (fun i k => σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ (P w θ) K Y ρ q S T β i k) g hg0
    (hs.mul_left (Real.sqrt Cq)) henergy
  refine ⟨hm.1,hm.2.trans ?_⟩
  have hb' : (∑'i,g i)≤Real.sqrt Cq*(Cs*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H) := by
    rw [show g=(fun i => Real.sqrt Cq*normMajorant deltaLoss A K Y⁻¹
      (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) from rfl,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ (tsum_nonneg hg0) hb' 2
  apply hsq.trans
  have hroot : (Real.sqrt K+Real.sqrt Y)^2≤2*(K+Y) := by
    nlinarith [Real.sq_sqrt hKp.le,Real.sq_sqrt hY.le,
      sq_nonneg (Real.sqrt K-Real.sqrt Y)]
  simp only [mul_pow,div_pow,Real.sq_sqrt hCq.le,Real.sq_sqrt hH.le]
  have hp : ((K*Y)^deltaLoss)^2=(K*Y)^(2*deltaLoss) := by
    rw [←Real.rpow_mul_natCast (mul_pos hKp hY).le]
    congr 1
    ring
  rw [hp]
  calc
    _ ≤ Cq*(Cs^2*(K*Y)^(2*deltaLoss)*(2*(K+Y))/H) := by
      apply mul_le_mul_of_nonneg_left _ hCq.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity)) hH.le
    _ = _ := by dsimp [Cq]; ring

end CompletedHeight

namespace CompletedHeight
open Eisenstein SchwartzPlanePoisson CompletedGauss CompletedDyadic CanonicalRowCompletion MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
theorem uniform_polynomial_reflected_branch_series {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel Wfamily)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K Y : ℝ,1≤K → 0<Y →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3),
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀I∈S i,I≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖reflectedBranchBlock P hg j e (Wfamily w θ) K Y ρ q S T η σ i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock P hg j e (Wfamily w θ) K Y ρ q S T η σ i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*Y)^(2*deltaLoss)*(K+Y)/
          ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
            (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_smooth_series_rowPhase
    completedShellWindow completedShellWindow completedShellWindow (Real.log 2) (Real.log 2) (Real.log 2)
    hl hl hl completedShellWindow_support completedShellWindow_support completedShellWindow_support
    completedShellWindow_norm completedShellWindow_norm completedShellWindow_norm
    Wfamily hWfamily deltaLoss ρ q hδ hρ hq
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨C,hC,h⟩ := hheight w
  refine ⟨C,hC,?_⟩
  intro θ K Y hK hY ι _ P _ hg j e S T hS hT η hη σ hσ
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
      reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
        (Ideal.absNorm_eq_zero_iff.mp hz))
  exact h θ K Y _ hK hY (mul_pos (hn 0) (hn 2)) S T
    (fun i I hI => ⟨(hS i I hI).1,(hS i I hI).2.2⟩)
    (fun i I hI => ⟨(hT i I hI).1,(hT i I hI).2.2⟩)
    (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1))
    (fun i n hn v hv => reflectedDyadicCoefficient_norm P hg j e (η i)
      (ramifiedScale ρ q i.1) _ _ (ramifiedScale_pos ρ q hρ (by linarith) _) (by positivity) (by positivity)
      n v (hS i n hn).1 (hT i v hv).1 (hη i n hn v hv) (hS i n hn).2.1 (hT i v hv).2.1)
    σ hσ

theorem uniform_polynomial_reflected_fiber_fixed_scale {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel Wfamily)
    (deltaLoss ρ q B : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hB : 1≤B) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K X c : ℝ,1≤K → 1≤X → 0<c → c≤B →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        reflectedBranchBlock P hg (fun i => completedLocalExponent I F (P i)) e (Wfamily w θ)
          (completedResidualScale K I Q) (completedBranchScale K (X/c) I F Q P e) ρ q S T η σ i k‖^2)
        ≤(C*(1+‖θ‖)^heightDegree)*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_reflected_branch_series Wfamily hWfamily deltaLoss ρ q hδ hρ hq
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Cbase*B^(2*deltaLoss+1),by positivity,?_⟩
  intro θ K X c hK hX hc hcB I F Q hI hQ hIK hk ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  let C := Cbase*(1+‖θ‖)^heightDegree
  have hC : 0<C := by dsimp [C]; positivity
  have h := hbase θ
  have hn (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hk0 : 0<completedResidualScale K I Q := by linarith
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hX0 : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  rw [completedBranchScale_div]
  have hb := (h (completedResidualScale K I Q) (c*completedBranchScale K X I F Q P e)
    hk (mul_pos hc hy) P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hs := completed_scaled_shape (2*deltaLoss) (completedResidualScale K I Q)
    (completedBranchScale K X I F Q P e) _ c B (by positivity) hk0 hy
    (mul_pos (hj 0) (hj 2)) hc hcB hB
  have hcst := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hh := hs.trans (mul_le_mul_of_nonneg_left hcst (by positivity : 0≤B^(2*deltaLoss+1)))
  apply hb.trans
  have hfinal := mul_le_mul_of_nonneg_left hh hC.le
  convert hfinal using 1 <;> (try dsimp [completedResidualScale,completedBranchScale,C]) <;> ring

theorem uniform_polynomial_branch_energy {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel Wfamily)
    (deltaLoss ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀θ K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedBranchData levelBound K I F Q,
      (∑k,‖d.value (Wfamily w θ) X ρ q k‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_reflected_fiber_fixed_scale Wfamily hWfamily deltaLoss ρ q levelBound hδ hρ hq hlevel
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨C,hC,h⟩ := hheight w
  refine ⟨C,hC,?_⟩
  intro θ K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact h θ K X d.levelScale hK hX d.levelScale_pos d.levelScale_le I F Q hI hQ hIK hk _ d.good d.coprime d.divides d.nonresidual
    d.label d.nColumns d.bColumns d.nBounds d.bBounds d.amplitude d.amplitude_bound
    d.rowPhase d.rowPhase_bound

theorem uniform_polynomial_fiber_energy {κ : Type*}
    (Wfamily : κ→ℝ→ℝ→ℂ) (hWfamily : HasUniformPolynomialKernel Wfamily)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃heightDegree : ℕ,∀w : κ,∃C : ℝ,0<C ∧ ∀(θ : ℝ) (rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedFiberData rays levelBound K I F Q,
      (∑k,‖d.value (Wfamily w θ) X ρ q k‖^2)≤
        (C*(1+‖θ‖)^heightDegree)*(rays:ℝ)^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨heightDegree,hheight⟩ := uniform_polynomial_branch_energy Wfamily hWfamily deltaLoss ρ q levelBound hδ hρ hq hlevel
  obtain ⟨Cp,hCp,hp⟩ := completed_branch_count_small_power ε hε
  refine ⟨heightDegree,?_⟩
  intro w
  obtain ⟨Cbase,hCbase,hbase⟩ := hheight w
  refine ⟨Cbase*Cp,by positivity,?_⟩
  intro θ rays K X hK hX I F Q hI hQ hIK hk d
  let Cb := Cbase*(1+‖θ‖)^heightDegree
  have hCb : 0<Cb := by dsimp [Cb]; positivity
  have hb := hbase θ
  let : ∀p : d.pool,p.val.IsMaximal := d.maximal
  have hcount := hp (I*Q) (mul_ne_zero hI hQ) (fun p : d.pool => p.val)
    Subtype.val_injective d.divides
  have hnorm : (Ideal.absNorm (I*Q):ℝ)≤K*(Ideal.absNorm Q:ℝ) := by
    simp only [map_mul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _)
  have hcount' : (6:ℝ)^(2*d.pool.card)≤Cp*(K*(Ideal.absNorm Q:ℝ))^ε := by
    have hc : (6:ℝ)^(2*d.pool.card)≤Cp*(Ideal.absNorm (I*Q):ℝ)^ε := by
      simpa only [Fintype.card_coe] using hcount
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hε.le) hCp.le)
  have he := ReflectedFiberData.finite_energy_bound
    (fun b => (d.branch b).value (Wfamily w θ) X ρ q) d.weight d.weight_bound _
    (fun b => hb K X hK hX I F Q hI hQ hIK hk (d.branch b))
  change (∑k,‖d.value (Wfamily w θ) X ρ q k‖^2)≤_ at he
  apply he.trans
  have hc : (Fintype.card (Fin rays×(d.pool→Fin 6)):ℝ)^2=(rays:ℝ)^2*(6:ℝ)^(2*d.pool.card) := by
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_mul,Nat.cast_pow]
    rw [mul_pow,←pow_mul,Nat.mul_comm d.pool.card 2]
    norm_num
  rw [hc]
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hKQ : 0<K*(Ideal.absNorm Q:ℝ) := mul_pos (by linarith) hnQ
  calc
    _ ≤ ((rays:ℝ)^2*(Cp*(K*(Ideal.absNorm Q:ℝ))^ε))*
      (Cb*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcount' (sq_nonneg _)
    _ = _ := by rw [Real.rpow_add hKQ]; dsimp [Cb]; ring


end CompletedHeight

namespace CompletedHeight
open Eisenstein SchwartzPlanePoisson CompletedGauss CanonicalRowCompletion
open SecondPassArithmetic (normPhase normHeightTwist)
open scoped BigOperators Classical

lemma logPhase_triple (t x : ℝ) : kernelLogPhase t (3*x)=(kernelLogPhase t x)^3 := by
  rw [show 3*x=x+x+x by ring,kernelLogPhase_add,kernelLogPhase_add]
  ring

lemma columnWeight_normHeight (Ψ : O→*ℂ) (t : ℝ) (I : Ideal O) :
    columnWeight (normHeightTwist Ψ t) I =
      kernelLogPhase t (Real.log (Ideal.absNorm I:ℝ))*columnWeight Ψ I := by
  by_cases hI : primaryIdealGenerator I=0
  · have hz : squarefreeGaussCoefficient I=0 := by simp [squarefreeGaussCoefficient,hI,angularFactor]
    simp only [columnWeight,hz,zero_mul,mul_zero]
  · have hn := SecondPassArithmetic.normPhase_of_ne_zero t (primaryIdealGenerator I) hI
    rw [primaryIdealGenerator_norm_sq I hI] at hn
    simp only [columnWeight,normHeightTwist,MonoidHom.mul_apply,hn]
    ring

lemma cubeWeight_normHeight (Ψ : O→*ℂ) (t : ℝ) (I : Ideal O) :
    cubeWeight (normHeightTwist Ψ t) I =
      kernelLogPhase t (3*Real.log (Ideal.absNorm I:ℝ))*cubeWeight Ψ I := by
  by_cases hI : primaryIdealGenerator I=0
  · simp [cubeWeight,hI,angularFactor]
  · have hn := SecondPassArithmetic.normPhase_of_ne_zero t (primaryIdealGenerator I) hI
    rw [primaryIdealGenerator_norm_sq I hI] at hn
    change star (angularFactor (primaryIdealGenerator I))^3*
        (Ψ (primaryIdealGenerator I)*normPhase t (primaryIdealGenerator I))^3/(Ideal.absNorm I:ℂ)=_
    rw [hn,logPhase_triple]
    change _ = (kernelLogPhase t (Real.log (Ideal.absNorm I:ℝ)))^3*
      (star (angularFactor (primaryIdealGenerator I))^3*
        Ψ (primaryIdealGenerator I)^3/(Ideal.absNorm I:ℂ))
    ring

lemma summand_normHeight (Ψ : O→*ℂ) (W : ℝ→ℂ) (t X : ℝ) (hX : 0<X)
    (I J : Ideal O) :
    CompletedGauss.summand (normHeightTwist Ψ t) W X I J =
      kernelLogPhase t (Real.log X)*CompletedGauss.summand Ψ (normTwistedSource W t) X I J := by
  by_cases hI : I=0
  · simp only [hI,CompletedGauss.summand_zero_left,mul_zero]
  by_cases hJ : J=0
  · simp only [hJ,CompletedGauss.summand_zero_right,mul_zero]
  have hni : 0<(Ideal.absNorm I:ℝ) := nonzeroDualIdeal_norm_pos ⟨I,hI⟩
  have hnj : 0<(Ideal.absNorm J:ℝ) := nonzeroDualIdeal_norm_pos ⟨J,hJ⟩
  have hl : Real.log X+Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X)=
      Real.log (Ideal.absNorm I:ℝ)+3*Real.log (Ideal.absNorm J:ℝ) := by
    rw [Real.log_div (mul_pos hni (pow_pos hnj 3)).ne' hX.ne',
      Real.log_mul hni.ne' (pow_pos hnj 3).ne',Real.log_pow]
    push_cast
    ring
  have hphase : kernelLogPhase t (Real.log X)*
      kernelLogPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X)) =
      kernelLogPhase t (Real.log (Ideal.absNorm I:ℝ))*kernelLogPhase t (3*Real.log (Ideal.absNorm J:ℝ)) := by
    rw [←kernelLogPhase_add,hl,kernelLogPhase_add]
  simp only [CompletedGauss.summand,columnWeight_normHeight,cubeWeight_normHeight,Vstar,normTwistedSource]
  linear_combination -(columnWeight Ψ I / (Real.sqrt (Ideal.absNorm I:ℝ):ℂ) * cubeWeight Ψ J *
    (Real.sqrt ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X):ℂ)*
      W ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/X))*hphase

theorem completedIdealT_normHeight (Ψ : O→*ℂ) (W : ℝ→ℂ) (t X : ℝ) (hX : 0<X) :
    completedIdealT (normHeightTwist Ψ t) W X =
      kernelLogPhase t (Real.log X)*completedIdealT Ψ (normTwistedSource W t) X := by
  simp only [completedIdealT,summand_normHeight Ψ W t X hX,tsum_mul_left]

@[simp] theorem completedIdealT_normHeight_norm (Ψ : O→*ℂ) (W : ℝ→ℂ)
    (t X : ℝ) (hX : 0<X) :
    ‖completedIdealT (normHeightTwist Ψ t) W X‖=‖completedIdealT Ψ (normTwistedSource W t) X‖ := by
  rw [completedIdealT_normHeight Ψ W t X hX,norm_mul,kernelLogPhase_norm,one_mul]

theorem shortCompletedSum_normHeight (Ψ : O→*ℂ) (W : ℝ→ℂ) (t X H₀ : ℝ) (hX : 0<X) :
    shortCompletedSum (normHeightTwist Ψ t) W X H₀ =
      kernelLogPhase t (Real.log X)*shortCompletedSum Ψ (normTwistedSource W t) X H₀ := by
  rw [shortCompletedSum_eq,shortCompletedSum_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro H hH
  have hn : 0<(Ideal.absNorm H:ℝ) := nonzeroDualIdeal_norm_pos ⟨H,((mem_shortCubeRange H₀ H).mp hH).1⟩
  rw [cubeWeight_normHeight,completedIdealT_normHeight Ψ W t _ (div_pos hX (pow_pos hn 3))]
  have hl : 3*Real.log (Ideal.absNorm H:ℝ)+Real.log (X/(Ideal.absNorm H:ℝ)^3)=Real.log X := by
    rw [Real.log_div hX.ne' (pow_pos hn 3).ne',Real.log_pow]
    push_cast
    ring
  have hphase : kernelLogPhase t (3*Real.log (Ideal.absNorm H:ℝ))*
      kernelLogPhase t (Real.log (X/(Ideal.absNorm H:ℝ)^3))=kernelLogPhase t (Real.log X) := by
    rw [←kernelLogPhase_add,hl]
  linear_combination (UniqueFactorizationMonoid.moebius H : ℂ)*cubeWeight Ψ H*
    completedIdealT Ψ (normTwistedSource W t) (X/(Ideal.absNorm H:ℝ)^3)*hphase

@[simp] theorem shortCompletedSum_normHeight_norm (Ψ : O→*ℂ) (W : ℝ→ℂ)
    (t X H₀ : ℝ) (hX : 0<X) :
    ‖shortCompletedSum (normHeightTwist Ψ t) W X H₀‖=
      ‖shortCompletedSum Ψ (normTwistedSource W t) X H₀‖ := by
  rw [shortCompletedSum_normHeight Ψ W t X H₀ hX,norm_mul,kernelLogPhase_norm,one_mul]

end CompletedHeight

namespace JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

/-- Weighted Fourier moments are controlled by finitely many source seminorms. -/
theorem fourier_coefficient_moment (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖ ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
        (SchwartzMap.seminorm ℝ (J + (volume : Measure ℝ).integrablePower) 0) (𝓕 g)) := by
  simpa using SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume (𝓕 g) J 0

theorem uniform_fourier_coefficient_moment
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C) := by
  let p := (volume : Measure ℝ).integrablePower
  let V : ℝ := 2 ^ p * ∫ t : ℝ, (1 + ‖t‖) ^ (-(p : ℝ))
  let K := J + p
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hfourier_zero := uniform_fourier_seminorm_transfer g 0 S C hS hC
    (by intro i hi; exact hsource i (by omega))
  have hfourier_K := uniform_fourier_seminorm_transfer g K S C hS hC
    (by intro i hi; exact hsource i (by simpa [K, p] using hi))
  have hmoment := fourier_coefficient_moment g J
  calc
    S * (∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖) ≤
        S * (V * ((SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
          (SchwartzMap.seminorm ℝ K 0) (𝓕 g))) :=
      mul_le_mul_of_nonneg_left (by simpa [V, K, p] using hmoment) hS
    _ = V * (S * (SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
        S * (SchwartzMap.seminorm ℝ K 0) (𝓕 g)) := by ring
    _ ≤ V * ((2 : ℝ) ^ 0 * (0 + 1) * V * C +
        (2 : ℝ) ^ K * (K + 1) * V * C) := by
      apply mul_le_mul_of_nonneg_left _ hV
      exact add_le_add (by simpa [V] using hfourier_zero)
        (by simpa [K, V] using hfourier_K)
    _ = _ := by simp [V, K, p, Nat.cast_add]

noncomputable def coefficientMomentBound (J : ℕ) (C : ℝ) : ℝ :=
  let p := (volume : Measure ℝ).integrablePower
  let V : ℝ := 2 ^ p * ∫ t : ℝ, (1 + ‖t‖) ^ (-(p : ℝ))
  V * (V * C + (2 : ℝ) ^ (J + p) * (J + p + 1) * V * C)

theorem coefficientMomentBound_nonneg (J : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ coefficientMomentBound J C := by
  unfold coefficientMomentBound
  positivity

theorem uniform_fourier_one_plus_moment
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) (S C : ℝ)
    (hS : 0 ≤ S) (hC : 0 ≤ C)
    (hsource : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      S * ((SchwartzMap.seminorm ℝ 0 i) g +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) g) ≤ C) :
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) ≤
      (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa using b.integrable_pow_mul volume 0
  have hIJ : Integrable (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hIrhs : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hpow := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hintegral :
      (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
    calc
      _ ≤ ∫ t : ℝ, (2 : ℝ) ^ J *
          (‖b t‖ + ‖t‖ ^ J * ‖b t‖) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall (by intro t; positivity))
          hIrhs (Filter.Eventually.of_forall hpoint)
      _ = (2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by
        rw [integral_const_mul, integral_add hI0 hIJ]
  have hbound0 := uniform_fourier_coefficient_moment g 0 S C hS hC
    (by intro i hi; exact hsource i (by omega))
  have hboundJ := uniform_fourier_coefficient_moment g J S C hS hC hsource
  calc
    S * (∫ t : ℝ, (1 + ‖t‖) ^ J * ‖b t‖) ≤
        S * ((2 : ℝ) ^ J *
          ((∫ t : ℝ, ‖b t‖) +
            (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖))) :=
      mul_le_mul_of_nonneg_left hintegral hS
    _ = (2 : ℝ) ^ J *
        (S * (∫ t : ℝ, ‖b t‖) +
          S * (∫ t : ℝ, ‖t‖ ^ J * ‖b t‖)) := by ring
    _ ≤ (2 : ℝ) ^ J *
        (coefficientMomentBound 0 C + coefficientMomentBound J C) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add
      · simpa [coefficientMomentBound, b] using hbound0
      · simpa [coefficientMomentBound, b] using hboundJ

theorem frequencyTwist_fourier_moment (J : ℕ) (g : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ θ : ℝ,
      (∫ t : ℝ, (1 + ‖t‖)^J * ‖(𝓕 (frequencyTwist g θ)) t‖) ≤
        C * (1 + ‖θ‖)^(J + (volume : Measure ℝ).integrablePower) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let D := twistSourceBound g K
  have hD : 0 ≤ D := twistSourceBound_nonneg g K
  let C := (2 : ℝ)^J * (coefficientMomentBound 0 D + coefficientMomentBound J D)
  have hC : 0 ≤ C := mul_nonneg (by positivity) (add_nonneg
    (coefficientMomentBound_nonneg 0 D hD) (coefficientMomentBound_nonneg J D hD))
  refine ⟨C, hC, ?_⟩
  intro θ
  let H := (1 + ‖θ‖)^K
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hs : ∀ i ≤ K,
      (SchwartzMap.seminorm ℝ 0 i) (frequencyTwist g θ) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower i) (frequencyTwist g θ) ≤ D * H := by
    intro i hi
    exact (source_le_profileSourceBound (frequencyTwist g θ) K i hi).trans
      (profileSourceBound_frequencyTwist g θ K)
  have hh := uniform_fourier_one_plus_moment (frequencyTwist g θ) J 1 (D * H)
    (by norm_num) (mul_nonneg hD hH) (fun i hi => by simpa only [one_mul] using hs i hi)
  have hlin (j : ℕ) : coefficientMomentBound j (D * H) = coefficientMomentBound j D * H := by
    unfold coefficientMomentBound
    ring
  simpa only [one_mul, hlin, add_mul, C, H, K, mul_assoc, mul_add] using hh


end JointLogSeparation

noncomputable section
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection JointLogSeparation MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
namespace JointLogSeparation
theorem coupled_cutoff_active
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (V : ℝ → ℂ) (a y M : ι → ℝ)
    (hwindow : ∀ j z, W j z ≠ 0 → |z| ≤ M j)
    (hVone : ∀ s,
      |s| ≤ ∑ j : ι, |a j| * M j → V s = 1)
    (hprod : (∏ j : ι, W j (y j)) ≠ 0) :
    V (∑ j : ι, a j * y j) = 1 := by
  classical
  apply hVone
  calc
    |∑ j : ι, a j * y j| ≤ ∑ j : ι, |a j * y j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : ι, |a j| * M j := by
      apply Finset.sum_le_sum
      intro j hj
      have hnonzero : W j (y j) ≠ 0 :=
        (Finset.prod_ne_zero_iff.mp hprod) j (Finset.mem_univ j)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hwindow j (y j) hnonzero) (abs_nonneg _)

theorem exists_complex_smooth_cutoff_with_derivative_bounds
    (T : ℝ) (K : ℕ) (hT : 0 ≤ T) :
    ∃ (V : ℝ → ℂ) (CW : ℝ),
      HasCompactSupport V ∧ ContDiff ℝ ∞ V ∧
      (∀ s, |s| ≤ T → V s = 1) ∧
      0 ≤ CW ∧
      (∀ i ≤ K, ∀ y, ‖iteratedFDeriv ℝ i V y‖ ≤ CW) ∧
      (∀ y,
        (∃ i ≤ K, ‖iteratedFDeriv ℝ i V y‖ ≠ 0) →
          Real.exp (-(T + 1)) ≤ Real.exp y ∧
          Real.exp y ≤ Real.exp (T + 1) ∧ |y| ≤ T + 1) := by
  obtain ⟨V, hVc, hVs, hVone, hVsupport, _⟩ :=
    exists_complex_smooth_cutoff T hT
  let g : SchwartzMap ℝ ℂ := hVc.toSchwartzMap hVs
  let CW : ℝ := ∑ j ∈ Finset.range (K + 1), SchwartzMap.seminorm ℝ 0 j g
  have hCW : 0 ≤ CW := by dsimp [CW]; positivity
  have hVderiv (i : ℕ) (hi : i ≤ K) (y : ℝ) :
      ‖iteratedFDeriv ℝ i V y‖ ≤ CW := by
    apply (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ g i y).trans
    exact Finset.single_le_sum
      (s := Finset.range (K + 1)) (f := fun j => SchwartzMap.seminorm ℝ 0 j g)
      (fun j _ => by positivity) (Finset.mem_range.mpr (by omega))
  refine ⟨V, CW, hVc, hVs, hVone, hCW, hVderiv, ?_⟩
  intro y hy
  obtain ⟨i, hi, hnonzero⟩ := hy
  have hyderiv : y ∈ Function.support (iteratedFDeriv ℝ i V) := by
    simpa [Function.mem_support] using hnonzero
  have hysupport : y ∈ tsupport V :=
    (support_iteratedFDeriv_subset i) hyderiv
  have hyinterval := hVsupport hysupport
  have hylower : -(T + 1) ≤ y := hyinterval.1
  have hyupper : y ≤ T + 1 := hyinterval.2
  constructor
  · exact Real.exp_le_exp.mpr hylower
  constructor
  · exact Real.exp_le_exp.mpr hyupper
  · exact abs_le.mpr ⟨hylower, hyupper⟩

theorem schwartz_fourier_one_plus_integrable
    (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    Integrable (fun t : ℝ =>
      (1 + ‖t‖) ^ J * ‖(𝓕 g) t‖) volume := by
  let b := 𝓕 g
  have hI0 : Integrable (fun t : ℝ => ‖b t‖) volume := by
    simpa [b] using b.integrable_pow_mul volume 0
  have hIJ : Integrable
      (fun t : ℝ => ‖t‖ ^ J * ‖b t‖) volume :=
    b.integrable_pow_mul volume J
  have hR : Integrable
      (fun t : ℝ => (2 : ℝ) ^ J *
        (‖b t‖ + ‖t‖ ^ J * ‖b t‖)) volume :=
    (hI0.add hIJ).const_mul _
  have hpoint (t : ℝ) :
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
        (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
    have hp := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num)
      (norm_nonneg t) J
    have htwo : (2 : ℝ) ^ (J - 1) ≤ (2 : ℝ) ^ J :=
      pow_le_pow_right₀ (by norm_num) (Nat.sub_le J 1)
    calc
      (1 + ‖t‖) ^ J * ‖b t‖ ≤
          (2 : ℝ) ^ (J - 1) * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ J * (1 ^ J + ‖t‖ ^ J) * ‖b t‖ := by
        gcongr
      _ = (2 : ℝ) ^ J * (‖b t‖ + ‖t‖ ^ J * ‖b t‖) := by
        simp; ring
  have hcont : Continuous
      (fun t : ℝ => (1 + ‖t‖) ^ J * ‖b t‖) := by
    fun_prop
  exact hR.mono_nonneg hcont.aestronglyMeasurable
    (Filter.Eventually.of_forall (by intro t; positivity))
    (Filter.Eventually.of_forall hpoint)

end JointLogSeparation

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open scoped BigOperators SchwartzMap ContDiff
namespace JointLogSeparation
/-- Exponential rescaling preserves derivative bounds after absorbing the scale into decay. -/
theorem exp_argument_derivative_bound
    (R a y H : ℝ) (i : ℕ)
    (hR : 0 ≤ R) (hH : 1 ≤ H)
    (ha : |a| ≤ H) (hexp : Real.exp (a * y) ≤ H)
    (hi : 1 ≤ i) :
    ‖iteratedFDeriv ℝ i (fun z : ℝ => R * Real.exp (a * z)) y‖ ≤
      (H ^ 2 * (1 + R)) ^ i := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  simp only [iteratedDeriv_const_mul_field, iteratedDeriv_exp_const_mul]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hR,
    abs_of_pos (Real.exp_pos _), abs_pow]
  have hpowH : H ≤ H ^ i := by
    calc H = H ^ 1 := by ring
         _ ≤ H ^ i := pow_le_pow_right₀ hH hi
  have hpowR : R ≤ (1 + R) ^ i := by
    calc R ≤ 1 + R := by linarith
         _ = (1 + R) ^ 1 := by ring
         _ ≤ (1 + R) ^ i := pow_le_pow_right₀ (by linarith) hi
  calc
    R * (|a| ^ i * Real.exp (a * y)) ≤ R * (H ^ i * H) := by gcongr
    _ ≤ (1 + R) ^ i * (H ^ i * H ^ i) := by gcongr
    _ = (H ^ 2 * (1 + R)) ^ i := by simp only [mul_pow, pow_two]; ring

theorem coupled_factor_derivative_bound
    (F : ℝ → ℂ) (R a y H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hH : 1 ≤ H)
    (ha : |a| ≤ H) (hexp : Real.exp (a * y) ≤ H)
    (hj : j ≤ n)
    (_hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
      j.factorial * (CF / (1 + R * Real.exp (a * y)) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j := by
  have harg : ContDiff ℝ ∞ (fun z : ℝ => R * Real.exp (a * z)) := by fun_prop
  have hu : 0 ≤ R * Real.exp (a * y) := by positivity
  have hden : 0 < (1 + R * Real.exp (a * y)) ^ (A + n) := by positivity
  apply norm_iteratedFDeriv_comp_le hF harg
    (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤)) y
  · intro i hi
    apply (le_div_iff₀ hden).mpr
    simpa [mul_comm] using hFdecay i (hi.trans hj) _ hu
  · intro i hi₁ hi₂
    exact exp_argument_derivative_bound R a y H i hR hH ha hexp hi₁

theorem derivative_scale_absorption
    (R u m H CF : ℝ) (A n j : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m)
    (_hH : 0 ≤ H) (hCF : 0 ≤ CF)
    (hu : 0 ≤ u) (hlower : m * (1 + R) ≤ 1 + u)
    (hj : j ≤ n) :
    m ^ (A + n) * (1 + R) ^ A *
      ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
        (H ^ 2 * (1 + R)) ^ j) ≤
      (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hRp : 1 ≤ 1 + R := by linarith
  have hden : 0 < (1 + u) ^ (A + n) := by positivity
  have hpowR : (1 + R) ^ (A + j) ≤ (1 + R) ^ (A + n) :=
    pow_le_pow_right₀ hRp (Nat.add_le_add_left hj A)
  have hscale : m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j ≤
      (1 + u) ^ (A + n) := by
    calc
      m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j =
          m ^ (A + n) * (1 + R) ^ (A + j) := by rw [pow_add]; ring
      _ ≤ m ^ (A + n) * (1 + R) ^ (A + n) :=
        mul_le_mul_of_nonneg_left hpowR (by positivity)
      _ = (m * (1 + R)) ^ (A + n) := by rw [mul_pow]
      _ ≤ (1 + u) ^ (A + n) := by gcongr
  let Q : ℝ := (j.factorial : ℝ) * CF * (H ^ 2) ^ j
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hQscale : Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) ≤
      Q * (1 + u) ^ (A + n) := mul_le_mul_of_nonneg_left hscale hQ
  calc
    m ^ (A + n) * (1 + R) ^ A *
        ((j.factorial : ℝ) * (CF / (1 + u) ^ (A + n)) *
          (H ^ 2 * (1 + R)) ^ j) =
      Q * (m ^ (A + n) * (1 + R) ^ A * (1 + R) ^ j) /
        (1 + u) ^ (A + n) := by dsimp [Q]; rw [mul_pow]; ring
    _ ≤ Q := (div_le_iff₀ hden).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hQscale)
    _ = (j.factorial : ℝ) * CF * (H ^ 2) ^ j := rfl

theorem coupled_factor_uniform_derivative
    (F : ℝ → ℂ) (R a y m H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hexpLower : m ≤ Real.exp (a * y))
    (hexpUpper : Real.exp (a * y) ≤ H)
    (hj : j ≤ n) (hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    m ^ (A + n) * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
        (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hcomp := coupled_factor_derivative_bound F R a y H CF A n j hF hR hH
    ha hexpUpper hj hCF hFdecay
  have hscale : 0 ≤ m ^ (A + n) * (1 + R) ^ A := by positivity
  have hlower : m * (1 + R) ≤ 1 + R * Real.exp (a * y) := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hexpLower)]
  exact (mul_le_mul_of_nonneg_left hcomp hscale).trans
    (derivative_scale_absorption R (R * Real.exp (a * y)) m H CF A n j
      hR hm (by linarith) hCF (by positivity) hlower hj)

noncomputable def schwartzDerivativeDecayConstant
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) : ℝ :=
  (2 : ℝ) ^ M *
    ∑ i ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 i) F +
        (SchwartzMap.seminorm ℝ M i) F)

theorem schwartzDerivativeDecayConstant_nonneg
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) :
    0 ≤ schwartzDerivativeDecayConstant F M K := by
  unfold schwartzDerivativeDecayConstant
  positivity

theorem schwartz_derivative_decay_finite
    (F : 𝓢(ℝ, ℂ)) (A K j i : ℕ) (u : ℝ)
    (hj : j ≤ K) (hi : i ≤ j) (hu : 0 ≤ u) :
    (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤
      schwartzDerivativeDecayConstant F (A + K) K := by
  let M := A + K
  let T : ℝ := (SchwartzMap.seminorm ℝ 0 i) F +
    (SchwartzMap.seminorm ℝ M i) F
  let N : ℝ := ‖iteratedFDeriv ℝ i F u‖
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hpow : (1 + u) ^ (A + j) ≤ (1 + u) ^ M :=
    pow_le_pow_right₀ (by linarith) (by dsimp [M]; omega)
  have hadd := add_pow_le (show (0 : ℝ) ≤ 1 by norm_num) hu M
  have htwo : (2 : ℝ) ^ (M - 1) ≤ (2 : ℝ) ^ M :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le M 1)
  have hsum : (1 + u) ^ M * N ≤ (2 : ℝ) ^ M *
      (N + u ^ M * N) := by
    calc
      (1 + u) ^ M * N ≤
          (2 : ℝ) ^ (M - 1) * (1 ^ M + u ^ M) * N :=
        mul_le_mul_of_nonneg_right hadd hN
      _ ≤ (2 : ℝ) ^ M * (1 ^ M + u ^ M) * N := by
        gcongr
      _ = (2 : ℝ) ^ M * (N + u ^ M * N) := by
        simp; ring
  have h0 : N ≤ (SchwartzMap.seminorm ℝ 0 i) F := by
    simpa [N] using SchwartzMap.le_seminorm ℝ 0 i F u
  have hM : u ^ M * N ≤ (SchwartzMap.seminorm ℝ M i) F := by
    simpa [N, Real.norm_eq_abs, abs_of_nonneg hu] using
      SchwartzMap.le_seminorm ℝ M i F u
  have hT : N + u ^ M * N ≤ T := add_le_add h0 hM
  have hTnonneg : 0 ≤ T := by dsimp [T]; positivity
  have hTsum : T ≤ ∑ k ∈ Finset.range (K + 1),
      ((SchwartzMap.seminorm ℝ 0 k) F +
        (SchwartzMap.seminorm ℝ M k) F) := by
    apply Finset.single_le_sum
      (f := fun k : ℕ =>
        (SchwartzMap.seminorm ℝ 0 k) F +
          (SchwartzMap.seminorm ℝ M k) F)
      (a := i)
    · intro k hk
      positivity
    · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hi.trans hj))
  calc
    (1 + u) ^ (A + j) * N ≤ (1 + u) ^ M * N :=
      mul_le_mul_of_nonneg_right hpow hN
    _ ≤ (2 : ℝ) ^ M * (N + u ^ M * N) := hsum
    _ ≤ (2 : ℝ) ^ M * T :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    _ ≤ (2 : ℝ) ^ M *
        (∑ k ∈ Finset.range (K + 1),
          ((SchwartzMap.seminorm ℝ 0 k) F +
            (SchwartzMap.seminorm ℝ M k) F)) :=
      mul_le_mul_of_nonneg_left hTsum (by positivity)
    _ = schwartzDerivativeDecayConstant F (A + K) K := rfl


end JointLogSeparation

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
