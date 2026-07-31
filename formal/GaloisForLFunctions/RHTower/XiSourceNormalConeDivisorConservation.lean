import GaloisForLFunctions.RHTower.XiArithmeticSourceMomentTorelli
import GaloisForLFunctions.RHTower.MFreeLadder
import GaloisForLFunctions.RHTower.SeamFluxCompletion
import GaloisForLFunctions.RHTower.CompletePositiveKolchinFreeRiemannResolution
import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization
import GaloisForLFunctions.HTGeometry.InverseGammaPoleCluster

/-!
# Source normal-cone divisor conservation

A dilation quotient has two different asymptotic faces. At fixed coordinate it may
converge to its bulk carrier, while at inverse-depth coordinate it converges to the
reciprocal exceptional section. Consecutive depths differentiate to the Euler
logarithmic current, whose centered residue retains the full affine displacement of
each divisor point.

The first part is carrier-independent. The second specializes the law to the
bounded-exponent Euler source and the completed Riemann `xi` carrier. The arithmetic
contour-moment Torelli certificate shows that no divisor point is selected as input.
-/

open Complex Filter Set
open scoped Topology BigOperators ArithmeticFunction.Omega Differential
  ArithmeticFunction.Moebius UpperEndDifferentialInstances
  UpperEndComplexTowerInstances LSeries.notation ArithmeticFunction.zeta
  ComplexOrder

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The lower endpoint chart of a reciprocal carrier. -/
def endpointNormalChart (f : ℂ → ℂ) (ε u : ℂ) : ℂ :=
  f (ε * u) / f u

/-- The upper endpoint chart of a reciprocal carrier. -/
def reflectedEndpointNormalChart (f : ℂ → ℂ) (ε u : ℂ) : ℂ :=
  f (1 - ε * u) / f u

/-- Exceptional section exposed when the endpoint scale tends to zero. -/
def exceptionalBoundarySection (f : ℂ → ℂ) (u : ℂ) : ℂ :=
  f 0 / f u

/-- Quotient between a carrier and its dilation by depth `t`. -/
def sourceDepthQuotient (f : ℂ → ℂ) (t s : ℂ) : ℂ :=
  f s / f (t * s)

/-- Transport between two infinitesimally adjacent normal depths. -/
def depthSuccessorTransport (f : ℂ → ℂ) (ε u : ℂ) : ℂ :=
  f u / f ((1 + ε) * u)

/-- Centered affine current carried by the exceptional divisor. -/
def exceptionalAffineDivisorCurrent
    (center : ℂ) (f : ℂ → ℂ) (u : ℂ) : ℂ :=
  -(u - center) * logDeriv f u

/-- A dilation quotient is a multiplicative cocycle for the dilation semigroup. -/
theorem sourceDepthQuotient_cocycle
    {f : ℂ → ℂ} {t v s : ℂ}
    (hmid : f (t * s) ≠ 0)
    (hend : f ((t * v) * s) ≠ 0) :
    sourceDepthQuotient f (t * v) s =
      sourceDepthQuotient f t s *
        sourceDepthQuotient f v (t * s) := by
  rw [sourceDepthQuotient, sourceDepthQuotient, sourceDepthQuotient]
  have harg : v * (t * s) = (t * v) * s := by ring
  rw [harg]
  field_simp

/-- Reciprocal symmetry glues the two endpoint charts exactly at every scale. -/
theorem endpointNormalChart_eq_reflected
    {f : ℂ → ℂ} (hsym : ∀ s, f (1 - s) = f s) (ε u : ℂ) :
    endpointNormalChart f ε u = reflectedEndpointNormalChart f ε u := by
  rw [endpointNormalChart, reflectedEndpointNormalChart, hsym]

/-- The zero-scale chart is the exceptional reciprocal section. -/
theorem endpointNormalChart_zero (f : ℂ → ℂ) (u : ℂ) :
    endpointNormalChart f 0 u = exceptionalBoundarySection f u := by
  simp [endpointNormalChart, exceptionalBoundarySection]

/-- Every carrier continuous at the endpoint has the same normal-cone law. -/
theorem tendsto_endpointNormalChart_zero
    {f : ℂ → ℂ} (hf : ContinuousAt f 0) (u : ℂ) :
    Tendsto (fun ε => endpointNormalChart f ε u)
      (𝓝 0) (𝓝 (exceptionalBoundarySection f u)) := by
  have harg : Tendsto (fun ε : ℂ => ε * u) (𝓝 0) (𝓝 0) := by
    convert (continuousAt_id.mul_const u).tendsto using 1 <;> simp
  have hnum : Tendsto (fun ε : ℂ => f (ε * u)) (𝓝 0) (𝓝 (f 0)) :=
    hf.tendsto.comp harg
  simpa [endpointNormalChart, exceptionalBoundarySection] using
    hnum.div_const (f u)

/-- A depth quotient at inverse depth is exactly its endpoint chart. -/
theorem sourceDepthQuotient_normal_coordinate
    {f : ℂ → ℂ} {t : ℂ} (ht : t ≠ 0) (u : ℂ) :
    sourceDepthQuotient f t (t⁻¹ * u) =
      endpointNormalChart f t⁻¹ u := by
  rw [sourceDepthQuotient, endpointNormalChart]
  congr 1
  field_simp

/-- Universal inverse-depth limit: every continuous carrier exposes its reciprocal
exceptional section. -/
theorem tendsto_sourceDepthQuotient_normalScale
    {f : ℂ → ℂ} (hf : ContinuousAt f 0) (u : ℂ) :
    Tendsto
      (fun M : ℕ =>
        sourceDepthQuotient f ((M + 1 : ℕ) : ℂ)
          ((((M + 1 : ℕ) : ℂ)⁻¹) * u))
      atTop (𝓝 (exceptionalBoundarySection f u)) := by
  have heps :
      Tendsto (fun M : ℕ => (((M + 1 : ℕ) : ℂ)⁻¹))
        atTop (𝓝 0) := by
    have h :=
      GaloisForLFunctions.tendsto_natCast_inv_complex.comp
        (tendsto_add_atTop_nat 1)
    exact h.congr' (Filter.Eventually.of_forall fun M => by rfl)
  have hcone := (tendsto_endpointNormalChart_zero hf u).comp heps
  refine hcone.congr' (Filter.Eventually.of_forall fun M => ?_)
  symm
  exact sourceDepthQuotient_normal_coordinate
    (by exact_mod_cast (show M + 1 ≠ 0 by omega)) u

/-- **Finite renormalized-depth selector.**  If the observation scale tends to
zero while depth times scale tends to `lam`, then the source quotient retains
exactly the reciprocal carrier at the rescaled coordinate `lam * u`. -/
theorem tendsto_sourceDepthQuotient_finiteRenormalizedDepth
    {f : ℂ → ℂ} {eps depth : ℕ → ℂ} {lam u : ℂ}
    (hf0 : ContinuousAt f 0)
    (hflam : ContinuousAt f (lam * u))
    (hflam0 : f (lam * u) ≠ 0)
    (heps : Tendsto eps atTop (𝓝 0))
    (hscale : Tendsto (fun n => depth n * eps n) atTop (𝓝 lam)) :
    Tendsto
      (fun n =>
        sourceDepthQuotient f (depth n) (eps n * u))
      atTop (𝓝 (f 0 / f (lam * u))) := by
  have harg0 : Tendsto (fun n => eps n * u) atTop (𝓝 0) := by
    convert heps.mul_const u using 1 ; simp
  have harglam :
      Tendsto (fun n => (depth n * eps n) * u)
        atTop (𝓝 (lam * u)) :=
    hscale.mul_const u
  have hnum :=
    hf0.tendsto.comp harg0
  have hden :=
    hflam.tendsto.comp harglam
  have hquot := hnum.div hden hflam0
  convert hquot using 1
  funext n
  simp only [sourceDepthQuotient, Function.comp_apply, Pi.div_apply]
  congr 1
  ring

/-- Ratio of consecutive depths before the normal rescaling. -/
theorem sourceDepthQuotient_successor_ratio
    {f : ℂ → ℂ} {t s : ℂ}
    (hfs : f s ≠ 0) (hft : f (t * s) ≠ 0)
    (hft1 : f ((t + 1) * s) ≠ 0) :
    sourceDepthQuotient f (t + 1) s /
        sourceDepthQuotient f t s =
      f (t * s) / f ((t + 1) * s) := by
  rw [sourceDepthQuotient, sourceDepthQuotient]
  field_simp

/-- On the inverse-depth chart, the consecutive quotient is the depth transport. -/
theorem sourceDepthQuotient_normal_successor_ratio
    {f : ℂ → ℂ} {t u : ℂ}
    (ht : t ≠ 0)
    (hfx : f (t⁻¹ * u) ≠ 0) (hfu : f u ≠ 0)
    (hfnext : f ((1 + t⁻¹) * u) ≠ 0) :
    sourceDepthQuotient f (t + 1) (t⁻¹ * u) /
        sourceDepthQuotient f t (t⁻¹ * u) =
      depthSuccessorTransport f t⁻¹ u := by
  rw [sourceDepthQuotient_successor_ratio hfx
    (by
      convert hfu using 1
      field_simp)
    (by
      convert hfnext using 1
      field_simp)]
  rw [depthSuccessorTransport]
  congr 1 <;> field_simp

/-- Infinitesimal depth transport is the Euler logarithmic current. -/
theorem hasDerivAt_depthSuccessorTransport_zero
    {f : ℂ → ℂ} {u : ℂ} (hf : DifferentiableAt ℂ f u)
    (hfu : f u ≠ 0) :
    HasDerivAt (fun ε => depthSuccessorTransport f ε u)
      (-u * logDeriv f u) 0 := by
  have harg : HasDerivAt (fun ε : ℂ => (1 + ε) * u) u 0 := by
    simpa using (((hasDerivAt_id (0 : ℂ)).const_add 1).mul_const u)
  have hden : HasDerivAt (fun ε : ℂ => f ((1 + ε) * u))
      (deriv f u * u) 0 := by
    have hf' : HasDerivAt f (deriv f u) ((1 + 0) * u) := by
      simpa using hf.hasDerivAt
    convert hf'.comp 0 harg using 1 <;> rfl
  have hquot := (hasDerivAt_const (x := (0 : ℂ)) (f u)).div hden
    (by simpa using hfu)
  change HasDerivAt (fun ε : ℂ => f u / f ((1 + ε) * u))
    ((0 * f ((1 + 0) * u) - f u * (deriv f u * u)) /
      f ((1 + 0) * u) ^ 2) 0 at hquot
  have heq :
      -u * logDeriv f u =
        (0 * f ((1 + 0) * u) - f u * (deriv f u * u)) /
          f ((1 + 0) * u) ^ 2 := by
    rw [logDeriv_apply]
    simp only [add_zero, one_mul, zero_mul, zero_sub]
    field_simp [hfu]
  rw [heq]
  exact hquot

/-- The exceptional section reverses the logarithmic connection. -/
theorem logDeriv_exceptionalBoundarySection
    {f : ℂ → ℂ} {u : ℂ}
    (hf0 : f 0 ≠ 0) (hfu : f u ≠ 0) (hf : DifferentiableAt ℂ f u) :
    logDeriv (exceptionalBoundarySection f) u = -logDeriv f u := by
  have h :=
    logDeriv_div (x := u) (f := fun _ : ℂ => f 0) (g := f)
      hf0 hfu (hasDerivAt_const u (f 0)).differentiableAt hf
  change logDeriv (fun z => f 0 / f z) u = -logDeriv f u
  simpa [logDeriv_apply] using h

/-- The exceptional section carries the negative of the original divisor. -/
theorem meromorphicOrderAt_exceptionalBoundarySection
    {f : ℂ → ℂ} {rho : ℂ} {n : ℤ}
    (hf0 : f 0 ≠ 0) (hf : MeromorphicAt f rho)
    (horder : meromorphicOrderAt f rho = n) :
    meromorphicOrderAt (exceptionalBoundarySection f) rho = -n := by
  change meromorphicOrderAt ((fun _ : ℂ => f 0) / f) rho = _
  rw [meromorphicOrderAt_div analyticAt_const.meromorphicAt hf,
    meromorphicOrderAt_const, if_neg hf0, horder]
  simp

/-- The affine divisor current is intrinsically the exceptional boundary connection. -/
theorem exceptionalAffineDivisorCurrent_eq_boundaryConnection
    {f : ℂ → ℂ} {center u : ℂ}
    (hf0 : f 0 ≠ 0) (hfu : f u ≠ 0) (hf : DifferentiableAt ℂ f u) :
    exceptionalAffineDivisorCurrent center f u =
      (u - center) * logDeriv (exceptionalBoundarySection f) u := by
  rw [logDeriv_exceptionalBoundarySection hf0 hfu hf]
  simp [exceptionalAffineDivisorCurrent]
  ring

/-- The centered affine current of a reciprocal carrier is reflection invariant. -/
theorem exceptionalAffineDivisorCurrent_reflection
    {f : ℂ → ℂ}
    (hlog : ∀ s, logDeriv f (1 - s) = -logDeriv f s)
    (u : ℂ) :
    exceptionalAffineDivisorCurrent (1 / 2) f (1 - u) =
      exceptionalAffineDivisorCurrent (1 / 2) f u := by
  rw [exceptionalAffineDivisorCurrent, exceptionalAffineDivisorCurrent, hlog]
  ring

/-- An affine weight is odd under reflection about `center` exactly when it is a
scalar multiple of the centered coordinate. -/
theorem affineWeight_reflectionOdd_iff
    (a b center : ℂ) :
    (∀ u : ℂ, a * (2 * center - u) + b = -(a * u + b)) ↔
      b = -a * center := by
  constructor
  · intro h
    have hc : a * center + b = -(a * center + b) := by
      calc
        a * center + b = a * (2 * center - center) + b := by ring
        _ = -(a * center + b) := h center
    have htwo : (2 : ℂ) * (a * center + b) = 0 := by
      calc
        (2 : ℂ) * (a * center + b) =
            (a * center + b) + (a * center + b) := by ring
        _ = -(a * center + b) + (a * center + b) :=
          congrArg (fun z : ℂ => z + (a * center + b)) hc
        _ = 0 := by ring
    have hzero : a * center + b = 0 :=
      (mul_eq_zero.mp htwo).resolve_left (by norm_num)
    simpa only [neg_mul] using eq_neg_of_add_eq_zero_right hzero
  · intro hb u
    rw [hb]
    ring

/-- The centered affine coordinate is therefore the unique affine polarization,
up to scale, compatible with reflection. -/
theorem affineWeight_eq_centered_of_reflectionOdd
    {a b center : ℂ}
    (hodd : ∀ u : ℂ, a * (2 * center - u) + b = -(a * u + b))
    (u : ℂ) :
    a * u + b = a * (u - center) := by
  rw [(affineWeight_reflectionOdd_iff a b center).mp hodd]
  ring

/-- Every reflection-even scalar observer identifies a point with its reflected
partner and hence cannot be globally injective. -/
theorem reflectionEvenObserver_not_injective
    {α : Type*} (center : ℂ) (obs : ℂ → α)
    (heven : ∀ u : ℂ, obs (2 * center - u) = obs u) :
    ¬Function.Injective obs := by
  intro hinj
  have hpair := hinj (heven (center + 1))
  have hone : (-1 : ℂ) = 1 := by
    calc
      (-1 : ℂ) = (2 * center - (center + 1)) - center := by ring
      _ = (center + 1) - center := congrArg (fun z : ℂ => z - center) hpair
      _ = 1 := by ring
  norm_num at hone

/-- Local conservation law: order becomes the full centered affine residue vector. -/
theorem exceptionalAffineDivisorCurrent_residue
    {f : ℂ → ℂ} {center rho : ℂ} {n : ℤ}
    (hf : MeromorphicAt f rho)
    (horder : meromorphicOrderAt f rho = n) :
    Tendsto
      (fun s => (s - rho) * exceptionalAffineDivisorCurrent center f s)
      (𝓝[≠] rho)
      (𝓝 (-((rho - center) * (n : ℂ)))) := by
  have hres :=
    logDeriv_residue_of_meromorphicOrder hf horder
  have hfactor :
      Tendsto (fun s : ℂ => -(s - center)) (𝓝[≠] rho)
        (𝓝 (-(rho - center))) := by
    exact ((continuous_id.sub continuous_const).neg.tendsto rho).mono_left
      nhdsWithin_le_nhds
  convert hfactor.mul hres using 1
  · funext s
    simp only [exceptionalAffineDivisorCurrent]
    ring
  · ring

end GaloisForLFunctions.HTGeometry

namespace RHTower

open ArithmeticFunction LSeries
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

/-- Euler source for integers whose prime exponents are bounded by `m - 1`. -/
def boundedExponentEulerSource (m : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s / riemannZeta ((m : ℂ) * s)

/-- Inverse-depth chart of the bounded-exponent source. -/
def boundedExponentNormalCone (ε u : ℂ) : ℂ :=
  riemannZeta (ε * u) / riemannZeta u

/-- Ordered positive-resolution prefix after reinserting the common zeta carrier. -/
def completeResolutionCarrierPrefix (K N : ℕ) (s : ℂ) : ℂ :=
  riemannZeta s *
    ∑ j ∈ Finset.range (N + 1), completeResolutionMultiplier K j s

/-- Every finite positive-resolution prefix is exactly one bounded-exponent
Euler source. This is the algebraic bridge between the hypertranscendental
channel resolution and the normal-cone family. -/
theorem completeResolutionCarrierPrefix_eq_boundedExponentEulerSource
    (K N : ℕ) (s : ℂ) :
    completeResolutionCarrierPrefix K N s =
      boundedExponentEulerSource (K + N) s := by
  rw [completeResolutionCarrierPrefix, sum_range_completeResolutionMultiplier]
  simp only [boundedExponentEulerSource, div_eq_mul_inv]

/-- The bounded-exponent Euler source is the exact `m`-free Dirichlet series. -/
theorem boundedExponentEulerSource_eq_LSeries
    {m : ℕ} (hm : m ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    boundedExponentEulerSource m s =
      LSeries (fun n => ((mFreeIndicator m n : ℤ) : ℂ)) s := by
  symm
  simpa [boundedExponentEulerSource] using
    LSeries_mFree_eq_riemannZeta_div hm hs

/-- Exact conversion from arithmetic depth to normal coordinate. -/
theorem boundedExponentEulerSource_normal_coordinate
    {m : ℕ} (hm : m ≠ 0) (u : ℂ) :
    boundedExponentEulerSource m (((m : ℂ)⁻¹) * u) =
      boundedExponentNormalCone ((m : ℂ)⁻¹) u := by
  rw [boundedExponentEulerSource, boundedExponentNormalCone]
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  congr 1
  field_simp

/-- Continuous normal-cone limit of the arithmetic source. -/
theorem tendsto_boundedExponentNormalCone_zero (u : ℂ) :
    Tendsto (fun ε => boundedExponentNormalCone ε u)
      (𝓝 0) (𝓝 ((-1 / 2 : ℂ) / riemannZeta u)) := by
  have hzeta : ContinuousAt riemannZeta 0 :=
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  have harg : Tendsto (fun ε : ℂ => ε * u) (𝓝 0) (𝓝 0) := by
    convert (continuousAt_id.mul_const u).tendsto using 1 <;> simp
  have hnum : Tendsto (fun ε : ℂ => riemannZeta (ε * u))
      (𝓝 0) (𝓝 (riemannZeta 0)) :=
    hzeta.tendsto.comp harg
  rw [riemannZeta_zero] at hnum
  simpa [boundedExponentNormalCone] using hnum.div_const (riemannZeta u)

/-- Zeta tends to one along every sequence escaping through the open right
half-plane. -/
theorem tendsto_riemannZeta_of_re_atTop
    {w : ℕ → ℂ}
    (hw : Tendsto (fun n => (w n).re) atTop atTop) :
    Tendsto (fun n => riemannZeta (w n)) atTop (𝓝 1) := by
  rw [Metric.tendsto_atTop]
  intro eps heps
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1
      (hw.eventually_gt_atTop (1 + 1 / eps))
  refine ⟨N, fun n hn => ?_⟩
  have hnlarge := hN n hn
  have hwin : 1 < (w n).re := by
    have : 0 < 1 / eps := one_div_pos.mpr heps
    linarith
  have hbound := norm_riemannZeta_sub_one_le hwin
  rw [dist_eq]
  refine hbound.trans_lt ?_
  have hden : 1 / eps < (w n).re - 1 := by
    linarith
  have hdenpos : 0 < (w n).re - 1 := by
    linarith
  exact (one_div_lt hdenpos heps).2 hden

/-- Zeta specialization of the finite renormalized-depth selector. -/
theorem tendsto_sourceDepthQuotient_zeta_finiteRenormalizedDepth
    {eps depth : ℕ → ℂ} {lam u : ℂ}
    (hpole : lam * u ≠ 1)
    (hzero : riemannZeta (lam * u) ≠ 0)
    (heps : Tendsto eps atTop (𝓝 0))
    (hscale :
      Tendsto (fun n => depth n * eps n) atTop (𝓝 lam)) :
    Tendsto
      (fun n =>
        sourceDepthQuotient riemannZeta (depth n) (eps n * u))
      atTop (𝓝 ((-1 / 2 : ℂ) / riemannZeta (lam * u))) := by
  have h :=
    tendsto_sourceDepthQuotient_finiteRenormalizedDepth
      ((differentiableAt_riemannZeta (by norm_num)).continuousAt)
      ((differentiableAt_riemannZeta hpole).continuousAt)
      hzero heps hscale
  rw [riemannZeta_zero] at h
  exact h

/-- **Right-escaping renormalized-depth selector.**  If the observation scale
tends to zero while the renormalized zeta argument escapes through the right
half-plane, every divisor is erased and only the endpoint constant remains. -/
theorem tendsto_sourceDepthQuotient_zeta_infiniteRenormalizedDepth
    {eps depth : ℕ → ℂ} {u : ℂ}
    (heps : Tendsto eps atTop (𝓝 0))
    (hright :
      Tendsto (fun n => ((depth n * eps n) * u).re)
        atTop atTop) :
    Tendsto
      (fun n =>
        sourceDepthQuotient riemannZeta (depth n) (eps n * u))
      atTop (𝓝 (-1 / 2 : ℂ)) := by
  have harg0 : Tendsto (fun n => eps n * u) atTop (𝓝 0) := by
    convert heps.mul_const u using 1 ; simp
  have hzeta0 : ContinuousAt riemannZeta 0 :=
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  have hnum := hzeta0.tendsto.comp harg0
  rw [riemannZeta_zero] at hnum
  have hden :=
    (tendsto_riemannZeta_of_re_atTop hright).inv₀ one_ne_zero
  have hprod := hnum.mul hden
  convert hprod using 1
  · funext n
    simp only [sourceDepthQuotient, Function.comp_apply]
    rw [div_eq_mul_inv]
    congr 2
    ring
  · ring

/-- At fixed scale the arithmetic source converges to the zeta bulk. -/
theorem tendsto_boundedExponentEulerSource_fixedScale
    {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => boundedExponentEulerSource (M + 1) s)
      atTop (𝓝 (riemannZeta s)) := by
  have hden :
      Tendsto
        (fun M : ℕ => (riemannZeta (((1 + M : ℕ) : ℂ) * s))⁻¹)
        atTop (𝓝 1) :=
    tendsto_inv_riemannZeta_nat_dilation_one (K := 1) hs
  have hconst :
      Tendsto (fun _ : ℕ => riemannZeta s) atTop (𝓝 (riemannZeta s)) :=
    tendsto_const_nhds
  have hprod := hconst.mul hden
  simpa [boundedExponentEulerSource, div_eq_mul_inv, Nat.add_comm] using hprod

/-- At inverse depth the same arithmetic source converges to reciprocal zeta. -/
theorem tendsto_boundedExponentEulerSource_normalScale (u : ℂ) :
    Tendsto
      (fun M : ℕ =>
        boundedExponentEulerSource (M + 1)
          ((((M + 1 : ℕ) : ℂ)⁻¹) * u))
      atTop (𝓝 ((-1 / 2 : ℂ) / riemannZeta u)) := by
  have heps :
      Tendsto (fun M : ℕ => (((M + 1 : ℕ) : ℂ)⁻¹))
        atTop (𝓝 0) := by
    have h :=
      GaloisForLFunctions.tendsto_natCast_inv_complex.comp
        (tendsto_add_atTop_nat 1)
    exact h.congr' (Filter.Eventually.of_forall fun M => by rfl)
  have hcone := (tendsto_boundedExponentNormalCone_zero u).comp heps
  refine hcone.congr' (Filter.Eventually.of_forall fun M => ?_)
  symm
  exact boundedExponentEulerSource_normal_coordinate (by omega) u

/-- A square-depth source observed at inverse linear scale has right-escaping
renormalized depth and collapses to the endpoint constant. -/
theorem tendsto_boundedExponentEulerSource_mesoscopicScale
    {u : ℂ} (hu : 0 < u.re) :
    Tendsto
      (fun M : ℕ =>
        boundedExponentEulerSource ((M + 1) ^ 2)
          ((((M + 1 : ℕ) : ℂ)⁻¹) * u))
      atTop (𝓝 (-1 / 2 : ℂ)) := by
  have hinv :
      Tendsto (fun M : ℕ => (((M + 1 : ℕ) : ℂ)⁻¹))
        atTop (𝓝 0) := by
    have h :=
      GaloisForLFunctions.tendsto_natCast_inv_complex.comp
        (tendsto_add_atTop_nat 1)
    exact h.congr' (Filter.Eventually.of_forall fun M => by rfl)
  have harg :
      Tendsto (fun M : ℕ => (((M + 1 : ℕ) : ℂ)⁻¹) * u)
        atTop (𝓝 0) := by
    convert hinv.mul_const u using 1 ; simp
  have hzeta0 : ContinuousAt riemannZeta 0 :=
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  have hnum :=
    hzeta0.tendsto.comp harg
  rw [riemannZeta_zero] at hnum
  have hden :=
    tendsto_inv_riemannZeta_nat_dilation_one (K := 1) hu
  have hprod := hnum.mul hden
  convert hprod using 1
  · funext M
    have hM : ((M + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (show M + 1 ≠ 0 by omega)
    simp only [boundedExponentEulerSource, div_eq_mul_inv,
      Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    congr 2
    field_simp [hM]
    ring
  · ring

/-- A linear-depth source observed faster than inverse depth has zero
renormalized depth and collapses to the identity. -/
theorem tendsto_boundedExponentEulerSource_microscopicScale
    (u : ℂ) :
    Tendsto
      (fun M : ℕ =>
        boundedExponentEulerSource (M + 1)
          (((((M + 1 : ℕ) : ℂ)⁻¹) ^ 2) * u))
      atTop (𝓝 1) := by
  have hinv :
      Tendsto (fun M : ℕ => (((M + 1 : ℕ) : ℂ)⁻¹))
        atTop (𝓝 0) := by
    have h :=
      GaloisForLFunctions.tendsto_natCast_inv_complex.comp
        (tendsto_add_atTop_nat 1)
    exact h.congr' (Filter.Eventually.of_forall fun M => by rfl)
  have hargNum :
      Tendsto
        (fun M : ℕ => ((((M + 1 : ℕ) : ℂ)⁻¹) ^ 2) * u)
        atTop (𝓝 0) := by
    convert (hinv.pow 2).mul_const u using 1 ; simp
  have hargDen :
      Tendsto
        (fun M : ℕ => (((M + 1 : ℕ) : ℂ)⁻¹) * u)
        atTop (𝓝 0) := by
    convert hinv.mul_const u using 1 ; simp
  have hzeta0 : ContinuousAt riemannZeta 0 :=
    (differentiableAt_riemannZeta (by norm_num)).continuousAt
  have hnum := hzeta0.tendsto.comp hargNum
  have hden := hzeta0.tendsto.comp hargDen
  rw [riemannZeta_zero] at hnum hden
  have hquot := hnum.div hden (by norm_num : (-1 / 2 : ℂ) ≠ 0)
  convert hquot using 1
  · funext M
    simp only [boundedExponentEulerSource, Function.comp_apply,
      Pi.div_apply, Nat.cast_add, Nat.cast_one]
    congr 1
    have hM : ((M + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast (show M + 1 ≠ 0 by omega)
    field_simp
  · norm_num

/-- At fixed scale the ordered positive hypertranscendental resolution fuses to
the zeta bulk. -/
theorem tendsto_completeResolutionCarrierPrefix_fixedScale
    (K : ℕ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun N : ℕ => completeResolutionCarrierPrefix K N s)
      atTop (𝓝 (riemannZeta s)) := by
  have hmultiplier :=
    tendsto_sum_range_completeResolutionMultiplier_one K hs
  simpa [completeResolutionCarrierPrefix] using
    (tendsto_const_nhds.mul hmultiplier)

/-- Exact conversion of a positive-resolution prefix to its inverse-depth chart. -/
theorem completeResolutionCarrierPrefix_normal_coordinate
    {K N : ℕ} (hdepth : K + N ≠ 0) (u : ℂ) :
    completeResolutionCarrierPrefix K N
        ((((K + N : ℕ) : ℂ)⁻¹) * u) =
      boundedExponentNormalCone (((K + N : ℕ) : ℂ)⁻¹) u := by
  rw [completeResolutionCarrierPrefix_eq_boundedExponentEulerSource,
    boundedExponentEulerSource_normal_coordinate hdepth]

/-- At inverse depth the same ordered positive hypertranscendental resolution
converges to the reciprocal zeta boundary. -/
theorem tendsto_completeResolutionCarrierPrefix_normalScale
    {K : ℕ} (hK : K ≠ 0) (u : ℂ) :
    Tendsto
      (fun N : ℕ =>
        completeResolutionCarrierPrefix K N
          ((((K + N : ℕ) : ℂ)⁻¹) * u))
      atTop (𝓝 ((-1 / 2 : ℂ) / riemannZeta u)) := by
  have heps :
      Tendsto (fun N : ℕ => (((K + N : ℕ) : ℂ)⁻¹))
        atTop (𝓝 0) := by
    have h :=
      GaloisForLFunctions.tendsto_natCast_inv_complex.comp
        (tendsto_add_atTop_nat K)
    exact h.congr' (Filter.Eventually.of_forall fun N => by
      simp [Function.comp_apply, Nat.add_comm])
  have hcone := (tendsto_boundedExponentNormalCone_zero u).comp heps
  refine hcone.congr' (Filter.Eventually.of_forall fun N => ?_)
  symm
  exact completeResolutionCarrierPrefix_normal_coordinate
    (by omega) u

/-- The bulk and exceptional zeta faces pair to the endpoint constant `ζ(0)`. -/
theorem riemannZeta_mul_exceptionalFace
    {u : ℂ} (hu : riemannZeta u ≠ 0) :
    riemannZeta u * ((-1 / 2 : ℂ) / riemannZeta u) = -1 / 2 := by
  field_simp

/-- Exact scale-selector package for bounded-exponent zeta sources. -/
structure ZetaSourceScaleTransitionCertificate : Prop where
  finiteRenormalizedDepth :
    ∀ (eps depth : ℕ → ℂ) (lam u : ℂ),
      lam * u ≠ 1 →
      riemannZeta (lam * u) ≠ 0 →
      Tendsto eps atTop (𝓝 0) →
      Tendsto (fun n => depth n * eps n) atTop (𝓝 lam) →
      Tendsto
        (fun n =>
          sourceDepthQuotient riemannZeta (depth n) (eps n * u))
        atTop (𝓝 ((-1 / 2 : ℂ) / riemannZeta (lam * u)))
  infiniteRenormalizedDepth :
    ∀ (eps depth : ℕ → ℂ) (u : ℂ),
      Tendsto eps atTop (𝓝 0) →
      Tendsto (fun n => ((depth n * eps n) * u).re) atTop atTop →
      Tendsto
        (fun n =>
          sourceDepthQuotient riemannZeta (depth n) (eps n * u))
        atTop (𝓝 (-1 / 2 : ℂ))
  fixedScale :
    ∀ {s : ℂ}, 0 < s.re →
      Tendsto (fun M : ℕ => boundedExponentEulerSource (M + 1) s)
        atTop (𝓝 (riemannZeta s))
  criticalScale :
    ∀ u : ℂ,
      Tendsto
        (fun M : ℕ =>
          boundedExponentEulerSource (M + 1)
            ((((M + 1 : ℕ) : ℂ)⁻¹) * u))
        atTop (𝓝 ((-1 / 2 : ℂ) / riemannZeta u))
  mesoscopicCollapse :
    ∀ {u : ℂ}, 0 < u.re →
      Tendsto
        (fun M : ℕ =>
          boundedExponentEulerSource ((M + 1) ^ 2)
            ((((M + 1 : ℕ) : ℂ)⁻¹) * u))
        atTop (𝓝 (-1 / 2 : ℂ))
  microscopicCollapse :
    ∀ u : ℂ,
      Tendsto
        (fun M : ℕ =>
          boundedExponentEulerSource (M + 1)
            (((((M + 1 : ℕ) : ℂ)⁻¹) ^ 2) * u))
        atTop (𝓝 1)

/-- **Zeta divisor scale-transition law.**  Renormalized depth selects whether
the bounded-exponent source retains a reciprocal divisor, collapses to the
identity, or erases the divisor to the endpoint constant. -/
theorem zetaSourceScaleTransition_law :
    ZetaSourceScaleTransitionCertificate where
  finiteRenormalizedDepth :=
    fun _ _ _ _ hpole hzero heps hscale =>
      tendsto_sourceDepthQuotient_zeta_finiteRenormalizedDepth
        hpole hzero heps hscale
  infiniteRenormalizedDepth :=
    fun _ _ _ heps hright =>
      tendsto_sourceDepthQuotient_zeta_infiniteRenormalizedDepth
        heps hright
  fixedScale := tendsto_boundedExponentEulerSource_fixedScale
  criticalScale := tendsto_boundedExponentEulerSource_normalScale
  mesoscopicCollapse :=
    tendsto_boundedExponentEulerSource_mesoscopicScale
  microscopicCollapse :=
    tendsto_boundedExponentEulerSource_microscopicScale

/-- Exact package joining positive coefficient resolution, maximal relative
differential rank, bulk fusion, and reciprocal exceptional boundary. -/
structure PositiveHTBulkBoundaryDualityCertificate (K : ℕ) : Prop where
  scaleTransition : ZetaSourceScaleTransitionCertificate
  relativeDifferentialFree :
    DifferentialIndependent zetaUpperEndDifferentialField
      (completeResolutionUpperEndMultiplier K)
  coefficientZeroOrOne :
    ∀ j n : ℕ, completeResolutionIndicator K j n = 0 ∨
      completeResolutionIndicator K j n = 1
  coefficientDisjoint :
    ∀ i j n : ℕ, i ≠ j →
      completeResolutionIndicator K i n ≠ 0 →
      completeResolutionIndicator K j n = 0
  coefficientFusion :
    ∀ n : ℕ, (∑' j : ℕ, completeResolutionIndicator K j n) =
      (ζ : ArithmeticFunction ℤ) n
  channelLSeries :
    ∀ j : ℕ, ∀ {s : ℂ}, 1 < s.re →
      LSeries ↗(completeResolutionIndicator K j) s =
        riemannZeta s * completeResolutionMultiplier K j s
  exactPrefix :
    ∀ N : ℕ, ∀ s : ℂ,
      completeResolutionCarrierPrefix K N s =
        boundedExponentEulerSource (K + N) s
  bulkFusion :
    ∀ {s : ℂ}, 0 < s.re →
      Tendsto (fun N : ℕ => completeResolutionCarrierPrefix K N s)
        atTop (𝓝 (riemannZeta s))
  exceptionalFusion :
    ∀ u : ℂ,
      Tendsto
        (fun N : ℕ =>
          completeResolutionCarrierPrefix K N
            ((((K + N : ℕ) : ℂ)⁻¹) * u))
        atTop (𝓝 ((-1 / 2 : ℂ) / riemannZeta u))
  channelDivisor :
    ∀ j : ℕ, ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      analyticOrderAt
          (fun z => riemannZeta z * completeResolutionMultiplier K j z) s =
        analyticOrderAt riemannZeta s
  bulkExceptionalPairing :
    ∀ {u : ℂ}, riemannZeta u ≠ 0 →
      riemannZeta u * ((-1 / 2 : ℂ) / riemannZeta u) = -1 / 2

/-- **Positive hypertranscendental bulk--boundary duality.**  For every
`K ≥ 12`, one explicit countable family is simultaneously a disjoint positive
resolution of zeta, maximally differentially free transverse to zeta, exactly
isodivisorial channel by channel, and a two-scale family whose fixed-scale
fusion is zeta while its inverse-depth fusion is reciprocal zeta. -/
theorem positiveHTBulkBoundaryDuality_law
    {K : ℕ} (hK : 12 ≤ K) :
    PositiveHTBulkBoundaryDualityCertificate K where
  scaleTransition := zetaSourceScaleTransition_law
  relativeDifferentialFree :=
    completeResolutionUpperEndMultiplier_relativeDifferentialIndependent K
      (by omega)
  coefficientZeroOrOne := completeResolutionIndicator_eq_zero_or_one
  coefficientDisjoint := fun _ _ _ hij hi =>
    completeResolutionIndicator_pairwiseDisjoint hij hi
  coefficientFusion := tsum_completeResolutionIndicator
  channelLSeries := fun j _ hs =>
    LSeries_completeResolutionIndicator (by omega) j hs
  exactPrefix := completeResolutionCarrierPrefix_eq_boundedExponentEulerSource K
  bulkFusion := tendsto_completeResolutionCarrierPrefix_fixedScale K
  exceptionalFusion :=
    tendsto_completeResolutionCarrierPrefix_normalScale (by omega)
  channelDivisor := fun j s hs hs1 =>
    analyticOrderAt_riemannZeta_completeResolutionChannel hK j hs hs1
  bulkExceptionalPairing := riemannZeta_mul_exceptionalFace

/-- Completed lower endpoint chart. -/
def xiEndpointNormalChart : ℂ → ℂ → ℂ :=
  endpointNormalChart xi

/-- Completed upper endpoint chart. -/
def xiReflectedEndpointNormalChart : ℂ → ℂ → ℂ :=
  reflectedEndpointNormalChart xi

/-- Completed exceptional reciprocal section. -/
def xiExceptionalBoundarySection : ℂ → ℂ :=
  exceptionalBoundarySection xi

/-- Completed consecutive-depth transport. -/
def xiDepthSuccessorTransport : ℂ → ℂ → ℂ :=
  depthSuccessorTransport xi

/-- Reflection-balanced affine Xi divisor current. -/
def xiExceptionalAffineDivisorCurrent : ℂ → ℂ :=
  exceptionalAffineDivisorCurrent (1 / 2) xi

/-- The completed endpoint charts glue exactly by the functional equation. -/
theorem xiEndpointNormalChart_eq_reflected (ε u : ℂ) :
    xiEndpointNormalChart ε u = xiReflectedEndpointNormalChart ε u :=
  endpointNormalChart_eq_reflected xi_one_sub ε u

/-- Both completed endpoint charts converge to the same exceptional reciprocal Xi section. -/
theorem tendsto_xiEndpointNormalChart_zero (u : ℂ) :
    Tendsto (fun ε => xiEndpointNormalChart ε u)
      (𝓝 0) (𝓝 ((1 / 2 : ℂ) / xi u)) := by
  have h :=
    tendsto_endpointNormalChart_zero
      (xi_differentiable 0).continuousAt u
  simpa [xiEndpointNormalChart, xiExceptionalBoundarySection,
    exceptionalBoundarySection, xi_zero] using h

/-- Infinitesimal completed depth is the Xi Euler current. -/
theorem hasDerivAt_xiDepthSuccessorTransport_zero
    {u : ℂ} (hu : xi u ≠ 0) :
    HasDerivAt (fun ε => xiDepthSuccessorTransport ε u)
      (-u * logDeriv xi u) 0 := by
  simpa [xiDepthSuccessorTransport] using
    hasDerivAt_depthSuccessorTransport_zero (xi_differentiable u) hu

/-- Difference-quotient form of the completed depth-current law. -/
theorem tendsto_xiDepthSuccessorTransport_differenceQuotient
    {u : ℂ} (hu : xi u ≠ 0) :
    Tendsto
      (fun ε : ℂ =>
        ε⁻¹ * (xiDepthSuccessorTransport ε u -
          xiDepthSuccessorTransport 0 u))
      (𝓝[≠] 0)
      (𝓝 (-u * logDeriv xi u)) := by
  simpa [smul_eq_mul] using
    (hasDerivAt_xiDepthSuccessorTransport_zero hu).tendsto_slope_zero

/-- The centered affine Xi current is reflection invariant. -/
theorem xiExceptionalAffineDivisorCurrent_reflection (u : ℂ) :
    xiExceptionalAffineDivisorCurrent (1 - u) =
      xiExceptionalAffineDivisorCurrent u := by
  simpa [xiExceptionalAffineDivisorCurrent] using
    exceptionalAffineDivisorCurrent_reflection logDeriv_xi_reciprocity u

/-- The centered current is the intrinsic connection of the exceptional boundary. -/
theorem xiExceptionalAffineDivisorCurrent_eq_boundaryConnection
    {u : ℂ} (hu : xi u ≠ 0) :
    xiExceptionalAffineDivisorCurrent u =
      (u - 1 / 2) * logDeriv xiExceptionalBoundarySection u := by
  exact exceptionalAffineDivisorCurrent_eq_boundaryConnection
    (by rw [xi_zero]; norm_num) hu (xi_differentiable u)

/-- At a Xi divisor point, the residue is multiplicity times its full centered
affine displacement. -/
theorem xiExceptionalAffineDivisorCurrent_residue
    {rho : ℂ} {n : ℤ}
    (horder : meromorphicOrderAt xi rho = n) :
    Tendsto
      (fun s => (s - rho) * xiExceptionalAffineDivisorCurrent s)
      (𝓝[≠] rho)
      (𝓝 (-((rho - 1 / 2) * (n : ℂ)))) := by
  have hxi : MeromorphicAt xi rho :=
    (xi_analyticOnNhd_univ rho (Set.mem_univ _)).meromorphicAt
  simpa [xiExceptionalAffineDivisorCurrent] using
    exceptionalAffineDivisorCurrent_residue hxi horder

/-- The exceptional Xi section carries the inverse Xi divisor with exact multiplicity. -/
theorem meromorphicOrderAt_xiExceptionalBoundarySection
    {rho : ℂ} {n : ℤ}
    (horder : meromorphicOrderAt xi rho = n) :
    meromorphicOrderAt xiExceptionalBoundarySection rho = -n := by
  exact meromorphicOrderAt_exceptionalBoundarySection
    (by rw [xi_zero]; norm_num)
    (xi_analyticOnNhd_univ rho (Set.mem_univ _)).meromorphicAt horder

/-- Exact theorem package for the Riemann source normal-cone conservation law. -/
structure XiSourceNormalConeDivisorConservationCertificate : Prop where
  arithmeticSource :
    ∀ {m : ℕ}, m ≠ 0 → ∀ {s : ℂ}, 1 < s.re →
      boundedExponentEulerSource m s =
        LSeries (fun n => ((mFreeIndicator m n : ℤ) : ℂ)) s
  bulkLimit :
    ∀ {s : ℂ}, 0 < s.re →
      Tendsto (fun M : ℕ => boundedExponentEulerSource (M + 1) s)
        atTop (𝓝 (riemannZeta s))
  exceptionalLimit :
    ∀ u : ℂ,
      Tendsto
        (fun M : ℕ =>
          boundedExponentEulerSource (M + 1)
            ((((M + 1 : ℕ) : ℂ)⁻¹) * u))
        atTop (𝓝 ((-1 / 2 : ℂ) / riemannZeta u))
  endpointGluing :
    ∀ ε u : ℂ,
      xiEndpointNormalChart ε u = xiReflectedEndpointNormalChart ε u
  completedExceptionalLimit :
    ∀ u : ℂ,
      Tendsto (fun ε => xiEndpointNormalChart ε u)
        (𝓝 0) (𝓝 ((1 / 2 : ℂ) / xi u))
  depthCurrent :
    ∀ {u : ℂ}, xi u ≠ 0 →
      HasDerivAt (fun ε => xiDepthSuccessorTransport ε u)
        (-u * logDeriv xi u) 0
  boundaryConnection :
    ∀ {u : ℂ}, xi u ≠ 0 →
      xiExceptionalAffineDivisorCurrent u =
        (u - 1 / 2) * logDeriv xiExceptionalBoundarySection u
  reflectionConservation :
    ∀ u : ℂ,
      xiExceptionalAffineDivisorCurrent (1 - u) =
        xiExceptionalAffineDivisorCurrent u
  affineResidue :
    ∀ {rho : ℂ} {n : ℤ}, meromorphicOrderAt xi rho = n →
      Tendsto
        (fun s => (s - rho) * xiExceptionalAffineDivisorCurrent s)
        (𝓝[≠] rho)
        (𝓝 (-((rho - 1 / 2) * (n : ℂ))))
  exceptionalDivisor :
    ∀ {rho : ℂ} {n : ℤ}, meromorphicOrderAt xi rho = n →
      meromorphicOrderAt xiExceptionalBoundarySection rho = -n
  arithmeticTomography : XiArithmeticSourceMomentTorelliCertificate

/-- Source-generated Xi divisor conservation: bulk, exceptional divisor, affine
current, and finite-divisor tomography in one unconditional certificate. -/
theorem xiSourceNormalConeDivisorConservation_law :
    XiSourceNormalConeDivisorConservationCertificate where
  arithmeticSource := fun hm _ hs =>
    boundedExponentEulerSource_eq_LSeries hm hs
  bulkLimit := fun hs => tendsto_boundedExponentEulerSource_fixedScale hs
  exceptionalLimit := tendsto_boundedExponentEulerSource_normalScale
  endpointGluing := xiEndpointNormalChart_eq_reflected
  completedExceptionalLimit := tendsto_xiEndpointNormalChart_zero
  depthCurrent := hasDerivAt_xiDepthSuccessorTransport_zero
  boundaryConnection := xiExceptionalAffineDivisorCurrent_eq_boundaryConnection
  reflectionConservation := xiExceptionalAffineDivisorCurrent_reflection
  affineResidue := xiExceptionalAffineDivisorCurrent_residue
  exceptionalDivisor := meromorphicOrderAt_xiExceptionalBoundarySection
  arithmeticTomography := xiArithmeticSourceMomentTorelli_law

/-- The signed arithmetic coefficient exposed by the exceptional boundary of
the positive bounded-exponent source. -/
def mobiusExceptionalCoefficient (n : ℕ) : ℝ :=
  -(((μ : ArithmeticFunction ℤ) n : ℤ) : ℝ) / 2

/-- The reciprocal-zeta exceptional boundary of the positive
bounded-exponent source. -/
def mobiusExceptionalBoundary (u : ℂ) : ℂ :=
  (-1 / 2 : ℂ) / riemannZeta u

@[simp] theorem mobiusExceptionalCoefficient_one :
    mobiusExceptionalCoefficient 1 = -1 / 2 := by
  simp [mobiusExceptionalCoefficient]

@[simp] theorem mobiusExceptionalCoefficient_two :
    mobiusExceptionalCoefficient 2 = 1 / 2 := by
  rw [mobiusExceptionalCoefficient,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  norm_num

/-- On the absolute-convergence half-plane, the exceptional boundary is
exactly the Dirichlet series with coefficients `-μ(n)/2`. -/
theorem LSeries_mobiusExceptionalCoefficient
    {u : ℂ} (hu : 1 < u.re) :
    LSeries (fun n => ((mobiusExceptionalCoefficient n : ℝ) : ℂ)) u =
      mobiusExceptionalBoundary u := by
  have hfun :
      (fun n => ((mobiusExceptionalCoefficient n : ℝ) : ℂ)) =
        (-1 / 2 : ℂ) • (↗μ : ℕ → ℂ) := by
    funext n
    simp [mobiusExceptionalCoefficient]
    ring
  rw [hfun, LSeries_smul, LSeries_moebius_eq_inv_riemannZeta hu]
  simp only [mobiusExceptionalBoundary, div_eq_mul_inv]

/-- A mixed-sign Möbius boundary cannot be obtained by coefficientwise
convergence of nonnegative coefficients on one fixed Dirichlet basis. -/
theorem no_nonnegative_coefficients_tendsto_mobiusExceptional :
    ¬ ∃ a : ℕ → ℕ → ℝ,
      (∀ k n, 0 ≤ a k n) ∧
      (∀ n, Tendsto (fun k => a k n) atTop
        (𝓝 (mobiusExceptionalCoefficient n))) := by
  rintro ⟨a, ha, hlim⟩
  have hnonneg : 0 ≤ mobiusExceptionalCoefficient 1 :=
    isClosed_Ici.mem_of_tendsto (hlim 1)
      (Filter.Eventually.of_forall fun k => ha k 1)
  rw [mobiusExceptionalCoefficient_one] at hnonneg
  norm_num at hnonneg

/-- Every native real value of a nontrivial bounded-exponent source is
strictly positive on its Dirichlet half-plane. -/
theorem boundedExponentEulerSource_pos_of_one_lt
    {m : ℕ} (hm : m ≠ 0) {x : ℝ} (hx : 1 < x) :
    0 < boundedExponentEulerSource m (x : ℂ) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm)
  have hmx : 1 < (m : ℝ) * x := by
    nlinarith
  have hnum : 0 < riemannZeta x :=
    riemannZeta_pos_of_one_lt hx
  have hden :=
    riemannZeta_pos_of_one_lt hmx
  have hden' :
      0 < riemannZeta ((m : ℂ) * (x : ℂ)) := by
    convert hden using 1
    all_goals norm_num
  rw [boundedExponentEulerSource]
  exact div_pos hnum hden'

/-- Every finite positive-resolution prefix is strictly positive at a native
real Dirichlet point. -/
theorem completeResolutionCarrierPrefix_pos_of_one_lt
    {K N : ℕ} (hKN : K + N ≠ 0) {x : ℝ} (hx : 1 < x) :
    0 < completeResolutionCarrierPrefix K N (x : ℂ) := by
  rw [completeResolutionCarrierPrefix_eq_boundedExponentEulerSource]
  exact boundedExponentEulerSource_pos_of_one_lt hKN hx

/-- The Möbius exceptional boundary is strictly negative on the real
Dirichlet half-line. -/
theorem mobiusExceptionalBoundary_neg_of_one_lt
    {x : ℝ} (hx : 1 < x) :
    mobiusExceptionalBoundary (x : ℂ) < 0 := by
  have hz : 0 < riemannZeta x :=
    riemannZeta_pos_of_one_lt hx
  rw [mobiusExceptionalBoundary]
  exact div_neg_of_neg_of_pos (by norm_num) hz

/-- At divisor-retaining inverse depth, the analytically continued positive
prefix is eventually strictly negative on every real ray `x > 1`. -/
theorem eventually_completeResolutionCarrierPrefix_critical_re_neg
    {K : ℕ} (hK : K ≠ 0) {x : ℝ} (hx : 1 < x) :
    ∀ᶠ N : ℕ in atTop,
      (completeResolutionCarrierPrefix K N
        ((((K + N : ℕ) : ℂ)⁻¹) * (x : ℂ))).re < 0 := by
  have hlim :=
    tendsto_completeResolutionCarrierPrefix_normalScale hK (x : ℂ)
  have hlimre :=
    Complex.continuous_re.continuousAt.tendsto.comp hlim
  have hneg :
      (mobiusExceptionalBoundary (x : ℂ)).re < 0 :=
    (Complex.neg_iff.mp
      (mobiusExceptionalBoundary_neg_of_one_lt hx)).1
  simpa only [Function.comp_apply, mobiusExceptionalBoundary] using
    (tendsto_order.1 hlimre).2 0 hneg

/-- Every inverse-depth observation point eventually leaves the common
Dirichlet half-plane of the nonnegative coefficient expansions. -/
theorem eventually_completeResolution_critical_outside_dirichletHalfPlane
    {K : ℕ} (x : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      ¬ 1 <
        (((((K + N : ℕ) : ℂ)⁻¹) * (x : ℂ))).re := by
  have heps :
      Tendsto (fun N : ℕ => (((K + N : ℕ) : ℂ)⁻¹))
        atTop (𝓝 0) := by
    have h :=
      GaloisForLFunctions.tendsto_natCast_inv_complex.comp
        (tendsto_add_atTop_nat K)
    exact h.congr' (Filter.Eventually.of_forall fun N => by
      simp [Function.comp_apply, Nat.add_comm])
  have harg :
      Tendsto
        (fun N : ℕ => (((K + N : ℕ) : ℂ)⁻¹) * (x : ℂ))
        atTop (𝓝 0) := by
    convert heps.mul_const (x : ℂ) using 1
    all_goals simp
  have hre :=
    Complex.continuous_re.continuousAt.tendsto.comp harg
  exact (hre.eventually_lt_const zero_lt_one).mono
    (fun _ hlt => not_lt_of_ge hlt.le)

/-- The exceptional Möbius boundary reverses every zeta divisor order. -/
theorem meromorphicOrderAt_mobiusExceptionalBoundary
    {rho : ℂ} {n : ℤ}
    (hf : MeromorphicAt riemannZeta rho)
    (horder : meromorphicOrderAt riemannZeta rho = n) :
    meromorphicOrderAt mobiusExceptionalBoundary rho = -n := by
  have hfun :
      mobiusExceptionalBoundary =
        exceptionalBoundarySection riemannZeta := by
    funext u
    simp [mobiusExceptionalBoundary, exceptionalBoundarySection,
      riemannZeta_zero]
  rw [hfun]
  exact
    meromorphicOrderAt_exceptionalBoundarySection
      (f := riemannZeta) (rho := rho) (n := n)
      (by rw [riemannZeta_zero]; norm_num) hf horder

/-- Exact certificate for the positive-occupancy to Möbius-boundary
transmutation and the minimal affine polarization of its completed divisor. -/
structure PositiveOccupancyMobiusBoundaryPolarityCertificate
    (K : ℕ) : Prop where
  bulkBoundary : PositiveHTBulkBoundaryDualityCertificate K
  nativePositive :
    ∀ N : ℕ, ∀ {x : ℝ}, 1 < x →
      0 < completeResolutionCarrierPrefix K N (x : ℂ)
  criticalLimit :
    ∀ x : ℝ,
      Tendsto
        (fun N : ℕ =>
          completeResolutionCarrierPrefix K N
            ((((K + N : ℕ) : ℂ)⁻¹) * (x : ℂ)))
        atTop (𝓝 (mobiusExceptionalBoundary (x : ℂ)))
  criticalEventuallyNegative :
    ∀ {x : ℝ}, 1 < x →
      ∀ᶠ N : ℕ in atTop,
        (completeResolutionCarrierPrefix K N
          ((((K + N : ℕ) : ℂ)⁻¹) * (x : ℂ))).re < 0
  criticalLeavesDirichletHalfPlane :
    ∀ x : ℝ,
      ∀ᶠ N : ℕ in atTop,
        ¬ 1 < (((((K + N : ℕ) : ℂ)⁻¹) * (x : ℂ))).re
  boundaryLSeries :
    ∀ {u : ℂ}, 1 < u.re →
      LSeries
          (fun n => ((mobiusExceptionalCoefficient n : ℝ) : ℂ)) u =
        mobiusExceptionalBoundary u
  boundaryMixedSign :
    mobiusExceptionalCoefficient 1 < 0 ∧
      0 < mobiusExceptionalCoefficient 2
  noCoefficientwisePositiveBoundary :
    ¬ ∃ a : ℕ → ℕ → ℝ,
      (∀ k n, 0 ≤ a k n) ∧
      (∀ n, Tendsto (fun k => a k n) atTop
        (𝓝 (mobiusExceptionalCoefficient n)))
  boundaryDivisorPolarity :
    ∀ {rho : ℂ} {n : ℤ},
      MeromorphicAt riemannZeta rho →
      meromorphicOrderAt riemannZeta rho = n →
      meromorphicOrderAt mobiusExceptionalBoundary rho = -n
  affinePolarization :
    ∀ {a b : ℂ},
      (∀ u : ℂ, a * (1 - u) + b = -(a * u + b)) →
      ∀ u : ℂ, a * u + b = a * (u - 1 / 2)
  xiAffineResidue :
    ∀ {rho : ℂ} {n : ℤ},
      meromorphicOrderAt xi rho = n →
      Tendsto
        (fun s => (s - rho) * xiExceptionalAffineDivisorCurrent s)
        (𝓝[≠] rho)
        (𝓝 (-((rho - 1 / 2) * (n : ℂ))))
  evenObserverLoss :
    ∀ {α : Type*} (obs : ℂ → α),
      (∀ u : ℂ, obs (1 - u) = obs u) →
      ¬Function.Injective obs

/-- **Positive occupancy--Möbius boundary-polarity law.**  For every
`K ≥ 12`, the complete positive hypertranscendental zeta resolution has a
forced singular boundary: its native branch is positive, its divisor-retaining
inverse-depth branch is eventually negative and equals signed Möbius inversion,
the boundary reverses divisor order, and reflection admits only the centered
affine polarization while every even observer loses injectivity. -/
theorem positiveOccupancyMobiusBoundaryPolarity_law
    {K : ℕ} (hK : 12 ≤ K) :
    PositiveOccupancyMobiusBoundaryPolarityCertificate K where
  bulkBoundary := positiveHTBulkBoundaryDuality_law hK
  nativePositive := fun N _ hx =>
    completeResolutionCarrierPrefix_pos_of_one_lt
      (by omega) hx
  criticalLimit := fun x => by
    simpa [mobiusExceptionalBoundary] using
      tendsto_completeResolutionCarrierPrefix_normalScale
        (K := K) (by omega) (x : ℂ)
  criticalEventuallyNegative := fun hx =>
    eventually_completeResolutionCarrierPrefix_critical_re_neg
      (K := K) (by omega) hx
  criticalLeavesDirichletHalfPlane := fun x =>
    eventually_completeResolution_critical_outside_dirichletHalfPlane
      (K := K) x
  boundaryLSeries :=
    LSeries_mobiusExceptionalCoefficient
  boundaryMixedSign := by
    rw [mobiusExceptionalCoefficient_one,
      mobiusExceptionalCoefficient_two]
    norm_num
  noCoefficientwisePositiveBoundary :=
    no_nonnegative_coefficients_tendsto_mobiusExceptional
  boundaryDivisorPolarity :=
    fun hf horder =>
      meromorphicOrderAt_mobiusExceptionalBoundary hf horder
  affinePolarization := fun hodd u =>
    affineWeight_eq_centered_of_reflectionOdd
      (center := (1 / 2 : ℂ)) (by simpa using hodd) u
  xiAffineResidue :=
    xiExceptionalAffineDivisorCurrent_residue
  evenObserverLoss := fun obs heven =>
    reflectionEvenObserver_not_injective
      (center := (1 / 2 : ℂ)) obs (by simpa using heven)

end RHTower
