import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspResponseMean

/-!
# Exact source and boundary Wronskian laws for the actual response.

The field is the original native energy response. Its identification with
continued retarded propagation and any extinction law remain separate.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMCuspResponse
open D4BMModularCore D4BMCuspProjection D4BMGlobalAngularResponse
noncomputable section

/-- The two actual homogeneous cusp exponents, without assigning a causal orientation. -/
def root (q : XiZeroCopy) (branch alternate : Bool) : ℂ :=
  if alternate then -physicalRate q branch-1 else physicalRate q branch+2

/-- The full boundary Wronskian flux of the actual response mean. -/
def responseFlux (q : XiZeroCopy) (branch alternate : Bool) (y : ℝ) : ℂ :=
  (y:ℂ)^(root q branch alternate)*deriv (responseMean q branch) y-
    root q branch alternate*(y:ℂ)^(root q branch alternate-1)*responseMean q branch y

/-- Source density paired with the literal homogeneous power, retaining the full global source. -/
def fluxSource (q : XiZeroCopy) (branch alternate : Bool) (y : ℝ) : ℂ :=
  (y:ℂ)^(root q branch alternate-2)*average (globalForcing q branch ∘ ofComplex) y

private theorem root_parameter (q : XiZeroCopy) (branch alternate : Bool) :
    root q branch alternate*(root q branch alternate-1)=parameter q branch := by
  rw [physicalRate_parameter]
  cases alternate <;> simp only [root,Bool.false_eq_true,if_false,if_true] <;> ring

private theorem power_step (a : ℂ) {y : ℝ} (hy : 0 < y) :
    (y:ℂ)^a = (y:ℂ)^(a-2)*(y:ℂ)^(2 : ℕ) := by
  have he : (y:ℂ)^(2:ℂ)=(y:ℂ)^(2 : ℕ) := by norm_cast
  rw [← he,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hy.ne')]
  congr 1
  ring

/-- The original response's Wronskian derivative is its exact source pairing,
with no boundary or radiation condition imposed. -/
theorem responseFlux_hasDerivAt (q : XiZeroCopy) (branch alternate : Bool)
    {y : ℝ} (hy : 0 < y) :
    HasDerivAt (responseFlux q branch alternate) (fluxSource q branch alternate y) y := by
  let a := root q branch alternate
  let m := responseMean q branch
  have hm : HasDerivAt m (deriv m y) y := by
    have h := average_hasDerivAt (responsePlanar q branch) (responsePlanar_smooth q branch) hy
    exact h.differentiableAt.hasDerivAt
  have hd : HasDerivAt (deriv m) (deriv (deriv m) y) y :=
    (average_second_hasDerivAt (responsePlanar q branch) (responsePlanar_smooth q branch) hy).differentiableAt.hasDerivAt
  have hp := GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := a) hy
  have hp1 := GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := a-1) hy
  have h := (hp.mul hd).sub ((hp1.const_mul a).mul hm)
  change HasDerivAt (responseFlux q branch alternate) _ y at h
  convert h using 1
  have he := responseMean_global_equation q branch hy
  change (y:ℂ)^(2 : ℕ)*deriv (deriv m) y-parameter q branch*m y=_ at he
  rw [fluxSource,← he,← root_parameter q branch alternate]
  change (y:ℂ)^(a-2)*((y:ℂ)^(2 : ℕ)*deriv (deriv m) y-a*(a-1)*m y)=_
  rw [show a-1-1=a-2 by ring,power_step a hy]
  ring

/-- The actual source flux density is continuous throughout positive height. -/
theorem fluxSource_continuousAt (q : XiZeroCopy) (branch alternate : Bool)
    {y : ℝ} (hy : 0 < y) : ContinuousAt (fluxSource q branch alternate) y := by
  exact (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal (w := root q branch alternate-2) hy).continuousAt.mul
    (average_hasDerivAt (globalForcing q branch ∘ ofComplex)
      (globalForcing_smooth q branch).planar_contDiffOn hy).continuousAt

/-- The exact finite-height source moment equals the difference of the two actual boundary fluxes. -/
theorem responseFlux_segment (q : XiZeroCopy) (branch alternate : Bool)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ y in a..b, fluxSource q branch alternate y) =
      responseFlux q branch alternate b-responseFlux q branch alternate a := by
  have hp : ∀ y ∈ uIcc a b, 0 < y := by
    intro y hy
    exact lt_of_lt_of_le (lt_min ha hb) hy.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => responseFlux_hasDerivAt q branch alternate (hp y hy))
  exact (show ContinuousOn (fluxSource q branch alternate) (uIcc a b) from
    fun y hy => (fluxSource_continuousAt q branch alternate (hp y hy)).continuousWithinAt).intervalIntegrable

/-- Above the cusp seam the complete explicit source, including cutoff derivatives,
is exactly the source density in the boundary flux law. -/
theorem fluxSource_explicit (q : XiZeroCopy) (branch alternate : Bool) {y : ℝ} (hy : 2 < y) :
    fluxSource q branch alternate y =
      (y:ℂ)^(root q branch alternate-2)*
        ((parameter q branch/2)*(principal (center q) ![0,y] ^(2 : ℕ)+
          8*∑' N, amplitude (center q) y N^(2 : ℕ))-
          ((y:ℂ)^(2 : ℕ)*deriv (deriv (cutoffHeight q branch)) y-
            parameter q branch*cutoffHeight q branch y)) := by
  rw [fluxSource,globalForcing_average q branch hy,mean_forcing q branch (by linarith)]

end
end RHTower.D4BMCuspResponse
