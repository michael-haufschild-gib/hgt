import GaloisForLFunctions.RHTower.ThetaCusp.SourceActions.SpectralEisensteinForcing
import GaloisForLFunctions.RHTower.ThetaCusp.SourceActions.ModularWeakResponseRegularity
import GaloisForLFunctions.RHTower.ThetaCusp.SourceActions.NativeTwoResponseActionOnSourceData

/-!
# The PW-B source data as a zero-independent arithmetic family

For every `s` in the nonreal open strip this module constructs the complete PW-B
native-action source data: the finite-energy weak response to the squared completed
Eisenstein forcing, its globally smooth modular representative, the full angular field, the
direct-minus-image circular kernels, the native Eisenstein kernels and the time-reduced source
legs. Nothing in the construction refers to Xi or its zeros.

At every Xi zero copy `q` the zero-indexed theta source data are definitionally the member of
this family at the location of `q`, so its responses, actions, admission, cutoff contact and
exhaustion limit are those of the family.
-/

open Complex Set Filter Topology MeasureTheory UpperHalfPlane
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

namespace RHTower.PWBSpectralSource
open D4BMModularCore (energyDomain embedding Space energyOperator energyOperator_selfAdjoint
  embedding_injective embedding_dense ModularWeakSolution
  modularWeak_global_planar_smooth globalLift ChartSmooth angularCoordinates)
open D4BMGlobalAngularResponse (scalar)
open D4BMNativeCircle (average logCircle)
open D4BMCausalKernel (invariant)
open D4BMJointSource (timeReducedCoefficient)
open D4BMPWSourceAction

noncomputable section
set_option autoImplicit false

/-! ## Finite-energy weak response -/

private theorem shift_im_ne_zero (s : SpectralSite) (b : Bool) :
    (1-parameter s b).im ≠ 0 := by
  simpa using neg_ne_zero.mpr (parameter_im_ne_zero s b)

/-- The modular resolvent is invertible at both physical parameters of every site. -/
theorem resolvent_bijective (s : SpectralSite) (b : Bool) :
    Function.Bijective (shiftedMap energyOperator (1-parameter s b)) :=
  bijective_shiftedMap energyOperator_selfAdjoint (shift_im_ne_zero s b)

/-- The variational form of the cusp-subtracted forced angular equation at `s`. -/
def WeakSolution (s : SpectralSite) (b : Bool) (h : energyDomain) : Prop :=
  ∀ v : energyDomain, inner ℂ v h - (1-parameter s b)*inner ℂ (embedding v) (embedding h) =
    -inner ℂ (embedding v) (forcingVector s b)

/-- Every spectral site has a finite-energy weak response on both branches. -/
theorem exists_weak_response (s : SpectralSite) (b : Bool) :
    ∃ h : energyDomain, WeakSolution s b h := by
  obtain ⟨x, hx⟩ := (resolvent_bijective s b).2 (-forcingVector s b)
  have hrange : (x : Space) ∈ (formEmbeddingCovariance embedding).range := by
    simpa only [energyOperator, friedrichsFormOperator, closedDenseInverse_domain] using
      x.property
  obtain ⟨y, hy⟩ := hrange
  have hAy : energyOperator x = y := by
    have happ := friedrichsFormOperator_apply_covariance embedding embedding_injective
      embedding_dense y
    have he : x = ⟨formEmbeddingCovariance embedding y, happ.1⟩ := Subtype.ext hy.symm
    exact (congrArg energyOperator he).trans happ.2
  let h : energyDomain := embedding.adjoint y
  have hJ : embedding h = (x : Space) := hy
  have hforce : y - (1-parameter s b) • embedding h = -forcingVector s b := by
    change energyOperator x - (1-parameter s b) • (x : Space) = _ at hx
    rw [hAy, ← hJ] at hx
    exact hx
  refine ⟨h, ?_⟩
  intro v
  have he := congrArg (fun w : Space => inner ℂ (embedding v) w) hforce
  rw [inner_sub_right, inner_smul_right, inner_neg_right] at he
  change inner ℂ v (embedding.adjoint y) - _ = _
  rw [embedding.adjoint_inner_right]
  exact he

/-- The nonreal shifted parameter makes the weak response unique. -/
theorem weak_response_unique (s : SpectralSite) (b : Bool) (h k : energyDomain)
    (hh : WeakSolution s b h) (hk : WeakSolution s b k) : h = k := by
  let w : energyDomain := h-k
  have he : inner ℂ w w -(1-parameter s b)*inner ℂ (embedding w) (embedding w) = 0 := by
    calc
      _ = (inner ℂ w h -(1-parameter s b)*inner ℂ (embedding w) (embedding h)) -
          (inner ℂ w k -(1-parameter s b)*inner ℂ (embedding w) (embedding k)) := by
        dsimp [w]
        rw [map_sub, inner_sub_right, inner_sub_right]
        ring
      _ = 0 := by rw [hh w, hk w, sub_self]
  have hi := congrArg Complex.im he
  have hwi : (inner ℂ w w).im = 0 := by
    simpa using! inner_self_im (𝕜 := ℂ) w
  have hji : (inner ℂ (embedding w) (embedding w)).im = 0 := by
    simpa using! inner_self_im (𝕜 := ℂ) (embedding w)
  have hjr : (inner ℂ (embedding w) (embedding w)).re = ‖embedding w‖^(2 : ℕ) := by
    simpa using! inner_self_eq_norm_sq (𝕜 := ℂ) (embedding w)
  have hp : (1-parameter s b).im*‖embedding w‖^(2 : ℕ) = 0 := by
    rw [Complex.sub_im, Complex.mul_im, hwi, hji, hjr, mul_zero, zero_add, Complex.zero_im,
      zero_sub] at hi
    exact neg_eq_zero.mp hi
  have hn : ‖embedding w‖^(2 : ℕ) = 0 :=
    (mul_eq_zero.mp hp).resolve_left (shift_im_ne_zero s b)
  have hj : embedding w = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  have hw : w = 0 := embedding_injective (by simpa only [map_zero] using hj)
  exact sub_eq_zero.mp hw

/-- The unique finite-energy weak response at `s`. -/
def weakResponse (s : SpectralSite) (b : Bool) : energyDomain :=
  (exists_weak_response s b).choose

theorem weakResponse_spec (s : SpectralSite) (b : Bool) :
    WeakSolution s b (weakResponse s b) :=
  (exists_weak_response s b).choose_spec

@[simp] theorem weakResponse_site (q : XiZeroCopy) (b : Bool) :
    weakResponse (site q) b = D4BMModularCore.weakResponse q b := rfl

/-! ## Global smooth response and full angular field -/

/-- The weak response has a smooth global representative at every spectral site. -/
theorem response_global_planar_smooth (s : SpectralSite) (b : Bool) :
    ∃ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im} ∧
      f =ᵐ[volume.restrict {z : ℂ | 0 < z.im}]
        (fun z => globalLift (embedding (weakResponse s b)) (ofComplex z)) :=
  modularWeak_global_planar_smooth (L := parameter s b) (F := forcingVector s b)
    (weakResponse_spec s b) (globalForcing_smooth s b) (globalForcing_ae_lift s b)

/-- The globally smooth representative of the weak response. -/
def globalResponse (s : SpectralSite) (b : Bool) (z : UpperHalfPlane) : ℂ :=
  (response_global_planar_smooth s b).choose (z : ℂ)

theorem globalResponse_smooth (s : SpectralSite) (b : Bool) :
    ChartSmooth (globalResponse s b) := by
  intro z
  have hs := (response_global_planar_smooth s b).choose_spec.1.contDiffAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)
  apply hs.congr_of_eventuallyEq
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds z.im_pos] with w hw
  simp only [Function.comp_apply, globalResponse, ofComplex_apply_of_im_pos hw]

@[simp] theorem globalResponse_site (q : XiZeroCopy) (b : Bool) :
    globalResponse (site q) b = D4BMModularCore.globalResponse q b := rfl

/-- Global cusp principal response plus the smooth forced correction. -/
def fullAngular (s : SpectralSite) (b : Bool) (z : UpperHalfPlane) : ℂ :=
  globalCuspCutoff s b z + globalResponse s b z

/-- The full angular response in angular metric coordinates. -/
def fullAngularField (s : SpectralSite) (b : Bool) (z : Fin 2 → ℝ) : ℂ :=
  fullAngular s b (ofComplex (angularCoordinates.symm z))

@[simp] theorem fullAngularField_site (q : XiZeroCopy) (b : Bool) :
    fullAngularField (site q) b = D4BMModularCore.fullAngularField q b := rfl

/-! ## Circular kernels -/

/-- The full angular field on a hyperbolic circle around `(x, e^k)`. -/
def angularSource (s : SpectralSite) (b : Bool) (d theta x k : ℝ) : ℂ :=
  fullAngularField s b (logCircle d theta x k)

/-- Circular average of the full angular field. -/
def angularMean (s : SpectralSite) (b : Bool) (d x k : ℝ) : ℂ :=
  average (fun theta => angularSource s b d theta x k)

/-- Direct-minus-image circular averages of the full angular field. -/
def angularDirichletKernel (s : SpectralSite) (b : Bool) (h x y X k : ℝ) : ℂ :=
  ((if |x-y| ≤ h then angularMean s b (Real.arcosh (invariant h x y)) X k else 0)-
    (if |x+y| ≤ h then angularMean s b (Real.arcosh (invariant h x (-y))) X k else 0))/2

/-- The half-square Eisenstein potential. -/
def fullSquarePotential (s : SpectralSite) (z : Fin 2 → ℝ) : ℂ :=
  (1/2 : ℂ)*(scalar (center s) z*scalar (center s) z)

/-- Circular average of the half-square Eisenstein potential. -/
def nativeMean (s : SpectralSite) (d x k : ℝ) : ℂ :=
  average (fun theta => fullSquarePotential s (logCircle d theta x k))

/-- Native Riemann kernel: the circular average at the causal invariant distance. -/
def nativeRiemannKernel (s : SpectralSite) (h x y X k : ℝ) : ℂ :=
  nativeMean s (Real.arcosh (invariant h x y)) X k

/-- Direct-minus-image native kernel with its causal supports. -/
def nativeDirichletCausalKernel (s : SpectralSite) (h x y X k : ℝ) : ℂ :=
  ((if |x-y| ≤ h then nativeRiemannKernel s h x y X k else 0)-
    (if |x+y| ≤ h then nativeRiemannKernel s h x (-y) X k else 0))/2

/-- Fundamental time rate of either branch, with its damping shift. -/
def physicalRate (s : SpectralSite) (b : Bool) : ℂ :=
  if b then s.1-2 else -s.1-1

@[simp] theorem angularDirichletKernel_site (q : XiZeroCopy) (b : Bool) :
    angularDirichletKernel (site q) b =
      D4BMFullAngularReconstruction.angularDirichletKernel q b := rfl

@[simp] theorem nativeDirichletCausalKernel_site (q : XiZeroCopy) :
    nativeDirichletCausalKernel (site q) = D4BMNativeCircle.nativeDirichletCausalKernel q := rfl

@[simp] theorem physicalRate_site (q : XiZeroCopy) (b : Bool) :
    physicalRate (site q) b = D4BMModularCore.physicalRate q b := rfl

/-! ## The source family and its identification at every zero -/

/-- **The PW-B arithmetic source family.** Native-action source data at a spectral site,
constructed from the completed Eisenstein series at `s` without reference to Xi. -/
def spectralSourceData (s : SpectralSite) (branch : Bool) (X k : ℝ) : NativeActionSourceData where
  parameter := parameter s branch
  contact := fullAngularField s branch ![X, Real.exp k]
  fullKernel r p := angularDirichletKernel s branch (r.1 - p.1) r.2 p.2 X k
  nativeKernel r p := nativeDirichletCausalKernel s (r.1 - p.1) r.2 p.2 X k
  source b a p := timeReducedCoefficient (physicalRate s b) a p.1 p.2

/-- At every Xi zero copy the theta source data are the family member at its location. -/
theorem thetaSourceData_eq_spectral (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    thetaSourceData q branch X k = spectralSourceData (site q) branch X k := rfl

/-- The family's responses at the location of every zero copy are the full retarded theta
responses. -/
theorem sourceResponse_spectral_site (q : XiZeroCopy) (branch b : Bool) (a : ℂ) (X k : ℝ)
    (p : D4BMPWRetardedWeakNative.Event) :
    sourceResponse (spectralSourceData (site q) branch X k) b a p =
      D4BMFullAngularCausalPeierls.fullRetardedResponse q branch b a p.1 p.2 X k := rfl

/-- The family's native action at every zero location is the literal theta action. -/
theorem nativeSourceAction_spectral_site (q : XiZeroCopy) (branch b c : Bool) (a d : ℂ)
    (X k : ℝ) (chi : D4BMPWRetardedWeakNative.Event → ℝ) :
    nativeSourceAction (spectralSourceData (site q) branch X k) chi b c a d =
      D4BMPWNativeTwoResponseAction.nativeTwoResponseAction chi q branch b c a d X k := rfl

/-- At every zero location the family action is exactly its cutoff source contact. -/
theorem spectralSourceData_action_eq_contact (q : XiZeroCopy) (branch b c : Bool)
    (a d : ℂ) (X k : ℝ) (n : ℕ) :
    let S := spectralSourceData (site q) branch X k
    nativeSourceAction S (D4BMPWTwoResponseAction.wedgeWindow n) b c a d =
      S.contact * ((∫ p, S.source b a p *
        sourceResponseTest S (D4BMPWTwoResponseAction.wedgeWindow n) c d p
          ∂D4BMFullAngularCausalPeierls.eventMeasure) -
        ∫ p, S.source c d p *
          sourceResponseTest S (D4BMPWTwoResponseAction.wedgeWindow n) b a p
            ∂D4BMFullAngularCausalPeierls.eventMeasure) :=
  thetaSourceData_action_eq_contact q branch b c a d X k n

/-- At every zero location the exhausted family action converges to its source contact. -/
theorem spectralSourceData_action_tendsto (q : XiZeroCopy) (branch : Bool) (a d : ℂ)
    (X k : ℝ) :
    Tendsto (fun n => nativeSourceAction (spectralSourceData (site q) branch X k)
      (D4BMPWTwoResponseAction.wedgeWindow n) true false a d) atTop
      (𝓝 (sourceContact (spectralSourceData (site q) branch X k) true false a d)) :=
  thetaSourceData_action_tendsto q branch a d X k

end
end RHTower.PWBSpectralSource

#print axioms RHTower.PWBSpectralSource.thetaSourceData_eq_spectral
#print axioms RHTower.PWBSpectralSource.spectralSourceData_action_tendsto
