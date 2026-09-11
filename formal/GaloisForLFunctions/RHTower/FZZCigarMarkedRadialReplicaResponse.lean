import GaloisForLFunctions.RHTower.FZZCigarCouplingInsertionGamma
import GaloisForLFunctions.HTGeometry.GammaShiftExpIntegral
import GaloisForLFunctions.HTGeometry.ExplicitDigammaHerglotzPalette
import GaloisForLFunctions.HTGeometry.FZZCigarReplicaBackreaction

/-!
# Integrated radial replica insertion and its surviving mixed response

Set `b=exp(v)`, `k=2+b^2`, `c=k/(k-2)`. The radial factor of the first-order marked
winding operator has weight `r(delta)=1-c*delta`. With the background exponential potential
and effective coupling fixed, its original radial integral is

`M_delta = integral b*exp(u+r(delta)*b*x-exp(u+b*x))*exp(i*p*x) dx`.

This module proves convergence near zero, the Gamma evaluation, and the exact normalized
replica derivative `c*(u-digamma(1+i*p/b))`. The Mellin differentiation theorem and two changes
of variables prove integrability of the marked logarithmic insertion and the identity between
the derivative of the original integral and the integral of that insertion.

Momentum reflection conjugates the integral. The normalized replica response of the paired
product is real at every momentum and equals `2*c*(u-Re digamma(1+i*p/b))`. Thus paired reality
cannot select vacuum, and fitting the effective coupling can make this first response vanish
at any momentum. Its real momentum derivative survives: it is
`(2*c/b)*Im trigamma(1+i*p/b)`, strictly negative at positive momentum and zero exactly at zero
momentum, independently of the effective coupling.

These are radial-sector identities and a precise mixed Ward receiver. No theorem asserts
that the complete CFT source has vanishing mixed response. Compact and nonzero modes, the
physical coupling transport, external momentum identification, and the source-fixed phase
frame remain to be derived. The paired construction is a mathematical diagnostic: the
Halder--Jafferis prescription explicitly excludes the reflected wave. Momentum reflection is
also distinct from the compact winding-charge sum. Only the first radial
jet is matched to its marked operator, not a complete finite-deficit off-shell CFT.
-/

open MeasureTheory Set Filter
open scoped Topology
namespace GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry
noncomputable section

def fzzMarkedRadialReplicaRate (v : ℝ) : ℝ :=
  (2 + Real.exp v ^ 2) / Real.exp v ^ 2

def fzzMarkedRadialReplicaIntegrand (u v p δ x : ℝ) : ℂ :=
  (Real.exp v * Real.exp (u + (1 - fzzMarkedRadialReplicaRate v * δ) *
    Real.exp v * x - Real.exp (u + Real.exp v * x)) : ℂ) *
      Complex.exp (((p * x : ℝ) : ℂ) * Complex.I)

def fzzMarkedRadialReplicaIntegral (u v p δ : ℝ) : ℂ :=
  ∫ x : ℝ, fzzMarkedRadialReplicaIntegrand u v p δ x

def fzzMarkedRadialReplicaResponse (u v p : ℝ) : ℂ :=
  deriv (fzzMarkedRadialReplicaIntegral u v p) 0 /
    fzzMarkedRadialReplicaIntegral u v p 0

theorem fzzMarkedRadialReplicaRate_pos (v : ℝ) :
    0 < fzzMarkedRadialReplicaRate v := by
  unfold fzzMarkedRadialReplicaRate
  positivity

theorem fzzMarkedRadialReplicaWeight_eq (v δ : ℝ) :
    FZZCigar.replicaRadialWeight (1 / (2 + Real.exp v ^ 2)) δ =
      1 - fzzMarkedRadialReplicaRate v * δ := by
  unfold FZZCigar.replicaRadialWeight fzzMarkedRadialReplicaRate
  have hb : Real.exp v ^ 2 ≠ 0 := pow_ne_zero _ (Real.exp_ne_zero v)
  have hk : 2 + Real.exp v ^ 2 ≠ 0 := by positivity
  have hd : 1 - 2 * (1 / (2 + Real.exp v ^ 2)) ≠ 0 := by
    have hn : 2 + Real.exp v ^ 2 - 2 = Real.exp v ^ 2 := by ring
    field_simp
    rw [hn]
    exact div_ne_zero hb hk
  field_simp
  ring

private theorem affine_substitution (u v : ℝ) (g : ℝ → ℂ) :
    (∫ y : ℝ, g y) = ∫ x : ℝ, Real.exp v • g (u + Real.exp v * x) := by
  have hderiv (x : ℝ) : HasDerivAt (fun x => u + Real.exp v * x) (Real.exp v) x := by
    simpa only [mul_one, id_eq] using
      ((hasDerivAt_id x).const_mul (Real.exp v)).const_add u
  have hinj : Function.Injective (fun x : ℝ => u + Real.exp v * x) := by
    intro x y h
    exact mul_left_cancel₀ (Real.exp_ne_zero v) (add_left_cancel h)
  have himg : (fun x : ℝ => u + Real.exp v * x) '' univ = univ := by
    apply Set.eq_univ_of_forall
    intro y
    refine ⟨(y-u)/Real.exp v, Set.mem_univ _, ?_⟩
    dsimp only
    rw [mul_div_cancel₀ _ (Real.exp_ne_zero v)]
    ring
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ) MeasurableSet.univ
    (fun x _ => (hderiv x).hasDerivWithinAt) hinj.injOn g
  simpa only [himg, setIntegral_univ, abs_of_pos (Real.exp_pos v)] using h


private theorem marked_integral_eq (u v p δ : ℝ)
    (hδ : 0 < 1 - fzzMarkedRadialReplicaRate v * δ) :
    fzzMarkedRadialReplicaIntegral u v p δ =
      Complex.exp (((fzzMarkedRadialReplicaRate v * δ * u : ℝ) : ℂ) -
        ((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) *
      Complex.Gamma (((1 - fzzMarkedRadialReplicaRate v * δ : ℝ) : ℂ) +
        ((p / Real.exp v : ℝ) : ℂ) * Complex.I) := by
  have h := GaloisForLFunctions.Gamma_vertical_eq_fourier hδ (p / Real.exp v)
  rw [affine_substitution u v] at h
  have hi : (∫ x : ℝ, Real.exp v •
      (Complex.exp (((p / Real.exp v * (u + Real.exp v * x) : ℝ) : ℂ) * Complex.I) *
        (Real.exp ((1 - fzzMarkedRadialReplicaRate v * δ) * (u + Real.exp v * x) -
          Real.exp (u + Real.exp v * x)) : ℂ))) =
      Complex.exp (-((fzzMarkedRadialReplicaRate v * δ * u : ℝ) : ℂ) +
        ((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) *
          fzzMarkedRadialReplicaIntegral u v p δ := by
    rw [fzzMarkedRadialReplicaIntegral, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    have he : p / Real.exp v * (u + Real.exp v * x) = p * u / Real.exp v + p * x := by
      field_simp
    have hr : (1 - fzzMarkedRadialReplicaRate v * δ) * (u + Real.exp v * x) -
        Real.exp (u + Real.exp v * x) =
        -(fzzMarkedRadialReplicaRate v * δ * u) +
          (u + (1 - fzzMarkedRadialReplicaRate v * δ) * Real.exp v * x -
            Real.exp (u + Real.exp v * x)) := by ring
    rw [he, hr, Real.exp_add, Complex.ofReal_add, add_mul, Complex.exp_add]
    simp only [fzzMarkedRadialReplicaIntegrand, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.exp_add]
    ring
  rw [hi] at h
  rw [h, ← mul_assoc, ← Complex.exp_add]
  have hz : (((fzzMarkedRadialReplicaRate v * δ * u : ℝ) : ℂ) -
        ((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) +
      (-((fzzMarkedRadialReplicaRate v * δ * u : ℝ) : ℂ) +
        ((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) = 0 := by ring
  rw [hz, Complex.exp_zero, one_mul]

theorem fzzMarkedRadialReplicaIntegral_eventually_eq (u v p : ℝ) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), fzzMarkedRadialReplicaIntegral u v p δ =
      Complex.exp (((fzzMarkedRadialReplicaRate v * δ * u : ℝ) : ℂ) -
        ((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) *
      Complex.Gamma (((1 - fzzMarkedRadialReplicaRate v * δ : ℝ) : ℂ) +
        ((p / Real.exp v : ℝ) : ℂ) * Complex.I) := by
  have hc : ContinuousAt (fun δ : ℝ => 1 - fzzMarkedRadialReplicaRate v * δ) 0 := by
    fun_prop
  have he := hc.eventually (eventually_gt_nhds (by simp :
    (0 : ℝ) < 1 - fzzMarkedRadialReplicaRate v * 0))
  filter_upwards [he] with δ hδ
  exact marked_integral_eq u v p δ hδ

theorem fzzMarkedRadialReplicaIntegral_zero (u v p : ℝ) :
    fzzMarkedRadialReplicaIntegral u v p 0 = fzzRadialCouplingCharacteristic u v p := by
  rw [marked_integral_eq u v p 0 (by simp), fzzRadialCouplingCharacteristic_eq_gamma]
  simp

theorem integrable_fzzMarkedRadialReplicaIntegrand_near_zero (u v p : ℝ) :
    ∀ᶠ δ in 𝓝 (0 : ℝ), Integrable (fzzMarkedRadialReplicaIntegrand u v p δ) := by
  have hc : ContinuousAt (fun δ : ℝ => 1 - fzzMarkedRadialReplicaRate v * δ) 0 := by
    fun_prop
  have he := hc.eventually (eventually_gt_nhds (by simp :
    (0 : ℝ) < 1 - fzzMarkedRadialReplicaRate v * 0))
  filter_upwards [he] with δ hδ
  by_contra hn
  have hz : fzzMarkedRadialReplicaIntegral u v p δ = 0 := integral_undef hn
  rw [marked_integral_eq u v p δ hδ] at hz
  exact (mul_ne_zero (Complex.exp_ne_zero _) (Complex.Gamma_ne_zero_of_re_pos (by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero] using hδ))) hz

theorem hasDerivAt_fzzMarkedRadialReplicaIntegral (u v p : ℝ) :
    HasDerivAt (fzzMarkedRadialReplicaIntegral u v p)
      ((fzzMarkedRadialReplicaRate v : ℂ) *
        ((u : ℂ) - Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)) *
          fzzMarkedRadialReplicaIntegral u v p 0) 0 := by
  let c := fzzMarkedRadialReplicaRate v
  let q := p / Real.exp v
  let z : ℂ := 1 + (q : ℂ) * Complex.I
  have hz : 0 < z.re := by simp [z]
  have hi : HasDerivAt (fun δ : ℝ => ((1 - c * δ : ℝ) : ℂ) + (q : ℂ) * Complex.I)
      (-(c : ℂ)) 0 := by
    simpa only [id_eq, mul_one, Complex.ofReal_neg] using!
      ((((hasDerivAt_id (0 : ℝ)).const_mul c).const_sub 1).ofReal_comp.add_const
        ((q : ℂ) * Complex.I))
  have hg := (differentiableAt_gamma_of_re_pos hz).hasDerivAt.scomp_of_eq 0 hi
    (by simp [z])
  rw [deriv_gamma_eq hz] at hg
  have he : HasDerivAt (fun δ : ℝ =>
      Complex.exp (((c * δ * u : ℝ) : ℂ) - ((p * u / Real.exp v : ℝ) : ℂ) * Complex.I))
      (Complex.exp (-((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) * (c * u : ℝ)) 0 := by
    have hd := (((((hasDerivAt_id (0 : ℝ)).const_mul c).mul_const u).ofReal_comp).sub_const
      (((p * u / Real.exp v : ℝ) : ℂ) * Complex.I)).cexp
    simpa only [id_eq, mul_one, mul_zero, zero_mul, Complex.ofReal_zero, zero_sub, neg_mul] using! hd
  have hp := he.mul hg
  have hm : fzzMarkedRadialReplicaIntegral u v p 0 =
      Complex.exp (-((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) * Complex.Gamma z := by
    rw [fzzMarkedRadialReplicaIntegral_zero, fzzRadialCouplingCharacteristic_eq_gamma]
    simp only [z, q, neg_mul]
  have hcoef :
      Complex.exp (-((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) * (c * u : ℝ) *
          (Complex.Gamma ∘ (fun δ : ℝ => ((1 - c * δ : ℝ) : ℂ) + (q : ℂ) * Complex.I)) 0 +
        Complex.exp (((c * 0 * u : ℝ) : ℂ) - ((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) *
          (-(c : ℂ) • (Complex.Gamma z * Complex.digamma z)) =
        (c : ℂ) * ((u : ℂ) - Complex.digamma z) *
          fzzMarkedRadialReplicaIntegral u v p 0 := by
    rw [hm]
    simp only [Function.comp_apply, mul_zero, zero_mul, sub_zero, Complex.ofReal_one,
      Complex.ofReal_zero, zero_sub, neg_mul, smul_eq_mul, Complex.ofReal_mul]
    dsimp [z]
    ring
  rw [hcoef] at hp
  exact hp.congr_of_eventuallyEq (fzzMarkedRadialReplicaIntegral_eventually_eq u v p)

theorem fzzMarkedRadialReplicaResponse_eq (u v p : ℝ) :
    fzzMarkedRadialReplicaResponse u v p = (fzzMarkedRadialReplicaRate v : ℂ) *
      ((u : ℂ) - Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)) := by
  have hn : fzzMarkedRadialReplicaIntegral u v p 0 ≠ 0 := by
    rw [fzzMarkedRadialReplicaIntegral_zero]
    exact fzzRadialCouplingCharacteristic_ne_zero u v p
  rw [fzzMarkedRadialReplicaResponse, (hasDerivAt_fzzMarkedRadialReplicaIntegral u v p).deriv,
    mul_div_cancel_right₀ _ hn]

/-- Momentum reflection is conjugation for the original integral, even away from its
convergence chamber (where the Bochner integral uses its totalized definition). -/
theorem fzzMarkedRadialReplicaIntegral_neg_momentum (u v p δ : ℝ) :
    fzzMarkedRadialReplicaIntegral u v (-p) δ =
      (starRingEnd ℂ) (fzzMarkedRadialReplicaIntegral u v p δ) := by
  rw [fzzMarkedRadialReplicaIntegral, fzzMarkedRadialReplicaIntegral, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [fzzMarkedRadialReplicaIntegrand, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj, Complex.conj_I, neg_mul, Complex.ofReal_neg, mul_neg]

theorem fzzMarkedRadialReplicaResponse_neg_momentum (u v p : ℝ) :
    fzzMarkedRadialReplicaResponse u v (-p) =
      (starRingEnd ℂ) (fzzMarkedRadialReplicaResponse u v p) := by
  simp only [fzzMarkedRadialReplicaResponse_eq, map_mul, map_sub, Complex.conj_ofReal]
  congr 2
  rw [← ReflectedDigammaAnomaly.digamma_conj]
  congr 1
  simp only [neg_div, Complex.ofReal_neg, map_add, map_one, map_mul,
    Complex.conj_ofReal, Complex.conj_I, neg_mul, mul_neg]

def fzzMarkedRadialReplicaPairedIntegral (u v p δ : ℝ) : ℂ :=
  fzzMarkedRadialReplicaIntegral u v p δ * fzzMarkedRadialReplicaIntegral u v (-p) δ

def fzzMarkedRadialReplicaPairedResponse (u v p : ℝ) : ℂ :=
  deriv (fzzMarkedRadialReplicaPairedIntegral u v p) 0 /
    fzzMarkedRadialReplicaPairedIntegral u v p 0

theorem fzzMarkedRadialReplicaPairedResponse_eq_sum (u v p : ℝ) :
    fzzMarkedRadialReplicaPairedResponse u v p =
      fzzMarkedRadialReplicaResponse u v p + fzzMarkedRadialReplicaResponse u v (-p) := by
  have hp := hasDerivAt_fzzMarkedRadialReplicaIntegral u v p
  have hn := hasDerivAt_fzzMarkedRadialReplicaIntegral u v (-p)
  have hz (p : ℝ) : fzzMarkedRadialReplicaIntegral u v p 0 ≠ 0 := by
    rw [fzzMarkedRadialReplicaIntegral_zero]
    exact fzzRadialCouplingCharacteristic_ne_zero u v p
  change deriv (fun δ => fzzMarkedRadialReplicaIntegral u v p δ *
    fzzMarkedRadialReplicaIntegral u v (-p) δ) 0 / _ = _
  have hd := (hp.mul hn).deriv
  change deriv (fun δ => fzzMarkedRadialReplicaIntegral u v p δ *
    fzzMarkedRadialReplicaIntegral u v (-p) δ) 0 = _ at hd
  rw [hd]
  simp only [fzzMarkedRadialReplicaResponse_eq, fzzMarkedRadialReplicaPairedIntegral]
  field_simp [hz p, hz (-p)]

theorem fzzMarkedRadialReplicaPairedResponse_eq (u v p : ℝ) :
    fzzMarkedRadialReplicaPairedResponse u v p =
      ((2 * fzzMarkedRadialReplicaRate v *
        (u - (Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)).re) : ℝ) : ℂ) := by
  rw [fzzMarkedRadialReplicaPairedResponse_eq_sum,
    fzzMarkedRadialReplicaResponse_neg_momentum, fzzMarkedRadialReplicaResponse_eq]
  apply Complex.ext <;> simp
  ring

theorem fzzMarkedRadialReplicaPairedResponse_im (u v p : ℝ) :
    (fzzMarkedRadialReplicaPairedResponse u v p).im = 0 := by
  rw [fzzMarkedRadialReplicaPairedResponse_eq]
  exact Complex.ofReal_im _

theorem fzzMarkedRadialReplicaPairedResponse_zero_iff (u v p : ℝ) :
    fzzMarkedRadialReplicaPairedResponse u v p = 0 ↔
      u = (Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)).re := by
  rw [fzzMarkedRadialReplicaPairedResponse_eq, Complex.ofReal_eq_zero]
  simp only [mul_eq_zero, (mul_pos (by norm_num : (0 : ℝ) < 2)
    (fzzMarkedRadialReplicaRate_pos v)).ne', false_or, sub_eq_zero]

theorem fzzMarkedRadialReplicaPairedResponse_fittedCoupling (v p : ℝ) :
    fzzMarkedRadialReplicaPairedResponse
      (Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)).re v p = 0 :=
  (fzzMarkedRadialReplicaPairedResponse_zero_iff _ v p).mpr rfl

/-- The momentum derivative of the normalized first replica response. -/
theorem hasDerivAt_fzzMarkedRadialReplicaResponse_momentum (u v p : ℝ) :
    HasDerivAt (fzzMarkedRadialReplicaResponse u v)
      (-((fzzMarkedRadialReplicaRate v / Real.exp v : ℝ) : ℂ) * Complex.I *
        deriv Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)) p := by
  have hi : HasDerivAt (fun t : ℝ => 1 + ((t / Real.exp v : ℝ) : ℂ) * Complex.I)
      (((1 / Real.exp v : ℝ) : ℂ) * Complex.I) p := by
    simpa only [id_eq] using!
      ((((hasDerivAt_id p).div_const (Real.exp v)).ofReal_comp).mul_const Complex.I).const_add 1
  have hz : 0 < (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I).re := by
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact zero_lt_one
  have hg := (_root_.RHTower.digamma_analyticOnNhd_re_pos _ hz).differentiableAt.hasDerivAt.scomp p hi
  have hd := (hg.const_sub (u : ℂ)).const_mul (fzzMarkedRadialReplicaRate v : ℂ)
  have hfun : fzzMarkedRadialReplicaResponse u v = fun t : ℝ =>
      (fzzMarkedRadialReplicaRate v : ℂ) *
        ((u : ℂ) - Complex.digamma (1 + ((t / Real.exp v : ℝ) : ℂ) * Complex.I)) := by
    funext t
    exact fzzMarkedRadialReplicaResponse_eq u v t
  rw [hfun]
  simpa only [Function.comp_apply, smul_eq_mul, Complex.ofReal_div, Complex.ofReal_one,
    div_eq_mul_inv, Complex.ofReal_mul, Complex.ofReal_inv, one_mul, mul_neg, neg_mul,
    mul_assoc, mul_comm, mul_left_comm] using! hd

theorem fzzMarkedRadialReplicaResponse_im_neg (u v w : ℝ) :
    (fzzMarkedRadialReplicaResponse u v (Real.exp w)).im < 0 := by
  have hp := verticalDigammaIm_pos 1 (Real.exp w / Real.exp v) (by positivity)
  change 0 < (Complex.digamma (1 + ((Real.exp w / Real.exp v : ℝ) : ℂ) * Complex.I)).im at hp
  rw [fzzMarkedRadialReplicaResponse_eq]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im,
    zero_sub, zero_mul, add_zero, mul_neg]
  exact neg_neg_of_pos (mul_pos (fzzMarkedRadialReplicaRate_pos v) hp)

private def gammaLogRay (q t : ℝ) : ℂ :=
  (t : ℂ) ^ ((1 + (q : ℂ) * Complex.I) - 1) *
    ((Real.log t * Real.exp (-t) : ℝ) : ℂ)

private def gammaLogLine (q y : ℝ) : ℂ :=
  (y : ℂ) * Complex.exp (((q * y : ℝ) : ℂ) * Complex.I) *
    (Real.exp (y - Real.exp y) : ℂ)

private theorem gamma_log_ray_integrable (q : ℝ) :
    IntegrableOn (gammaLogRay q) (Ioi 0) := by
  let z : ℂ := 1 + (q : ℂ) * Complex.I
  have hz : 0 < z.re := by simp [z]
  have hm := (mellin_hasDerivAt_of_isBigO_rpow (E := ℂ)
    (f := fun t : ℝ => (Real.exp (-t) : ℂ)) (s := z) (a := z.re + 1) (b := 0)
    (by
      refine (Continuous.continuousOn ?_).locallyIntegrableOn measurableSet_Ioi
      exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg))
    (by
      rw [← Asymptotics.isBigO_norm_left]
      simp_rw [Complex.norm_real, Asymptotics.isBigO_norm_left]
      simpa only [neg_one_mul] using
        (isLittleO_exp_neg_mul_rpow_atTop zero_lt_one (-(z.re + 1))).isBigO)
    (lt_add_one _) (by
      simp_rw [neg_zero, Real.rpow_zero]
      refine Asymptotics.isBigO_const_of_tendsto
        (?_ : Tendsto _ _ (𝓝 (1 : ℂ))) one_ne_zero
      rw [(by simp : (1 : ℂ) = Real.exp (-0))]
      exact (Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp continuous_neg)).continuousWithinAt) hz).1
  unfold gammaLogRay
  simpa only [MellinConvergent, z, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_mul] using! hm

private theorem gamma_log_ray_integral (q : ℝ) :
    (∫ t in Ioi 0, gammaLogRay q t) =
      Complex.Gamma (1 + (q : ℂ) * Complex.I) *
        Complex.digamma (1 + (q : ℂ) * Complex.I) := by
  have hz : 0 < (1 + (q : ℂ) * Complex.I).re := by simp
  have hd := Complex.hasDerivAt_GammaIntegral hz
  simp only [← Complex.ofReal_mul] at hd
  have hΓ : HasDerivAt Complex.Gamma (∫ t in Ioi 0, gammaLogRay q t)
      (1 + (q : ℂ) * Complex.I) := by
    refine hd.congr_of_eventuallyEq ?_
    have hopen : IsOpen {z : ℂ | 0 < z.re} :=
      Complex.continuous_re.isOpen_preimage _ isOpen_Ioi
    filter_upwards [hopen.mem_nhds hz] with z hz
    exact Complex.Gamma_eq_integral hz
  rw [← hΓ.deriv, deriv_gamma_eq hz]

private theorem gamma_log_line_change (q y : ℝ) :
    |Real.exp y| • gammaLogRay q (Real.exp y) = gammaLogLine q y := by
  unfold gammaLogRay gammaLogLine
  rw [GaloisForLFunctions.cpow_ofReal_exp y, abs_of_pos (Real.exp_pos y), Real.log_exp]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  have he : (y : ℂ) * (1 + (q : ℂ) * Complex.I - 1) =
      ((q * y : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [he]
  simp only [Complex.ofReal_exp]
  have hprod : Complex.exp (y : ℂ) * Complex.exp ((-Real.exp y : ℝ) : ℂ) =
      Complex.exp ((y - Real.exp y : ℝ) : ℂ) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    _ = (y : ℂ) * Complex.exp (((q * y : ℝ) : ℂ) * Complex.I) *
        (Complex.exp (y : ℂ) * Complex.exp ((-Real.exp y : ℝ) : ℂ)) := by ring
    _ = _ := by rw [hprod, Complex.ofReal_mul]

private theorem gamma_log_line_integrable (q : ℝ) : Integrable (gammaLogLine q) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := univ)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn (gammaLogRay q)
  rw [Set.image_univ, Real.range_exp] at h
  have hh := h.mp (gamma_log_ray_integrable q)
  simpa only [gamma_log_line_change, integrableOn_univ] using hh

private theorem gamma_log_line_integral (q : ℝ) :
    (∫ y : ℝ, gammaLogLine q y) =
      Complex.Gamma (1 + (q : ℂ) * Complex.I) *
        Complex.digamma (1 + (q : ℂ) * Complex.I) := by
  have h := integral_image_eq_integral_abs_deriv_smul (s := univ)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn (gammaLogRay q)
  rw [Set.image_univ, Real.range_exp, gamma_log_ray_integral] at h
  simpa only [gamma_log_line_change, setIntegral_univ] using h.symm

private def radialLogMoment (u v p x : ℝ) : ℂ :=
  ((u + Real.exp v * x : ℝ) : ℂ) * fzzMarkedRadialReplicaIntegrand u v p 0 x

private theorem gamma_log_affine (u v p x : ℝ) :
    (Real.exp v : ℂ) * gammaLogLine (p / Real.exp v) (u + Real.exp v * x) =
      Complex.exp (((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) * radialLogMoment u v p x := by
  have he : p / Real.exp v * (u + Real.exp v * x) = p * u / Real.exp v + p * x := by
    field_simp
  simp only [gammaLogLine, radialLogMoment, fzzMarkedRadialReplicaIntegrand,
    mul_zero, sub_zero, one_mul]
  rw [he]
  simp only [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.ofReal_mul]
  ring

private theorem radial_log_moment_integrable (u v p : ℝ) : Integrable (radialLogMoment u v p) := by
  have hi := (((gamma_log_line_integrable (p / Real.exp v)).comp_add_left u).comp_mul_left'
    (Real.exp_ne_zero v)).const_mul (Real.exp v : ℂ)
  have hh := hi.const_mul (Complex.exp (-(((p * u / Real.exp v : ℝ) : ℂ) * Complex.I)))
  apply hh.congr
  filter_upwards with x
  rw [gamma_log_affine, ← mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, one_mul]

private theorem radial_log_moment_integral (u v p : ℝ) :
    (∫ x : ℝ, radialLogMoment u v p x) =
      fzzMarkedRadialReplicaIntegral u v p 0 *
        Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I) := by
  have h := affine_substitution u v (gammaLogLine (p / Real.exp v))
  simp only [Complex.real_smul, gamma_log_affine] at h
  rw [gamma_log_line_integral, integral_const_mul] at h
  have hmul := congrArg (fun z : ℂ =>
      Complex.exp (-(((p * u / Real.exp v : ℝ) : ℂ) * Complex.I)) * z) h
  have hcancel : Complex.exp (-(((p * u / Real.exp v : ℝ) : ℂ) * Complex.I)) *
      Complex.exp (((p * u / Real.exp v : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  simp only [← mul_assoc, hcancel, one_mul] at hmul
  rw [fzzMarkedRadialReplicaIntegral_zero, fzzRadialCouplingCharacteristic_eq_gamma]
  simpa only [mul_assoc] using hmul.symm

/-- The first jet is exactly the logarithmic radial operator in the marked winding insertion. -/
theorem hasDerivAt_fzzMarkedRadialReplicaIntegrand (u v p x : ℝ) :
    HasDerivAt (fun δ => fzzMarkedRadialReplicaIntegrand u v p δ x)
      ((-(fzzMarkedRadialReplicaRate v * Real.exp v * x) : ℝ) *
        fzzMarkedRadialReplicaIntegrand u v p 0 x) 0 := by
  have h0 := ((hasDerivAt_id (0 : ℝ)).const_mul (fzzMarkedRadialReplicaRate v)).const_sub 1
  have hr := ((((h0.mul_const (Real.exp v)).mul_const x).const_add u).sub_const
    (Real.exp (u + Real.exp v * x)))
  have hd := (((hr.exp.const_mul (Real.exp v)).ofReal_comp).mul_const
    (Complex.exp (((p * x : ℝ) : ℂ) * Complex.I)))
  simpa only [fzzMarkedRadialReplicaIntegrand, id_eq, mul_one, mul_zero, zero_mul, sub_zero,
    one_mul, Complex.ofReal_mul, Complex.ofReal_neg, neg_mul, mul_neg, mul_assoc, mul_comm,
    mul_left_comm] using! hd

private theorem marked_jet_decomposition (u v p x : ℝ) :
    deriv (fun δ => fzzMarkedRadialReplicaIntegrand u v p δ x) 0 =
      -(fzzMarkedRadialReplicaRate v : ℂ) * radialLogMoment u v p x +
      ((fzzMarkedRadialReplicaRate v * u : ℝ) : ℂ) *
        fzzMarkedRadialReplicaIntegrand u v p 0 x := by
  rw [(hasDerivAt_fzzMarkedRadialReplicaIntegrand u v p x).deriv]
  simp only [radialLogMoment, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_add]
  ring

private theorem marked_zero_integrand_integrable (u v p : ℝ) :
    Integrable (fzzMarkedRadialReplicaIntegrand u v p 0) := by
  by_contra hn
  have hz : fzzMarkedRadialReplicaIntegral u v p 0 = 0 := integral_undef hn
  rw [fzzMarkedRadialReplicaIntegral_zero] at hz
  exact fzzRadialCouplingCharacteristic_ne_zero u v p hz

theorem integrable_fzzMarkedRadialReplicaInsertion (u v p : ℝ) :
    Integrable (fun x : ℝ => deriv (fun δ => fzzMarkedRadialReplicaIntegrand u v p δ x) 0) := by
  simp only [marked_jet_decomposition]
  exact ((radial_log_moment_integrable u v p).const_mul _).add
    ((marked_zero_integrand_integrable u v p).const_mul _)

/-- Differentiation of the original integral equals the integrated marked operator. Both
logarithmic terms are integrable; the Mellin derivative theorem supplies their exact integral. -/
theorem fzzMarkedRadialReplicaIntegral_deriv_eq_integral (u v p : ℝ) :
    deriv (fzzMarkedRadialReplicaIntegral u v p) 0 =
      ∫ x : ℝ, deriv (fun δ => fzzMarkedRadialReplicaIntegrand u v p δ x) 0 := by
  rw [(hasDerivAt_fzzMarkedRadialReplicaIntegral u v p).deriv]
  simp only [marked_jet_decomposition]
  rw [integral_add ((radial_log_moment_integrable u v p).const_mul _)
    ((marked_zero_integrand_integrable u v p).const_mul _), integral_const_mul,
    integral_const_mul, radial_log_moment_integral]
  change _ = _ * (_ * _) + _ * fzzMarkedRadialReplicaIntegral u v p 0
  push_cast
  ring

/-- Reflection cancels the imaginary replica response, but its real momentum derivative remains. -/
theorem hasDerivAt_fzzMarkedRadialReplicaPairedResponse_momentum (u v p : ℝ) :
    HasDerivAt (fzzMarkedRadialReplicaPairedResponse u v)
      ((2 * fzzMarkedRadialReplicaRate v / Real.exp v *
        (deriv Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)).im : ℝ) : ℂ) p := by
  have hr := Complex.reCLM.hasFDerivAt.comp_hasDerivAt p
    (hasDerivAt_fzzMarkedRadialReplicaResponse_momentum u v p)
  have hre : HasDerivAt (fun t => (fzzMarkedRadialReplicaResponse u v t).re)
      (fzzMarkedRadialReplicaRate v / Real.exp v *
        (deriv Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)).im) p := by
    change HasDerivAt (fun t => (fzzMarkedRadialReplicaResponse u v t).re)
      (-((fzzMarkedRadialReplicaRate v / Real.exp v : ℝ) : ℂ) * Complex.I *
        deriv Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)).re p at hr
    simpa only [Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, mul_one, sub_zero, zero_sub, add_zero, neg_zero, neg_neg,
      neg_mul] using! hr
  have hd := (hre.const_mul 2).ofReal_comp
  have hcoef : (2 : ℝ) * (fzzMarkedRadialReplicaRate v / Real.exp v *
      (deriv Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)).im) =
      2 * fzzMarkedRadialReplicaRate v / Real.exp v *
        (deriv Complex.digamma (1 + ((p / Real.exp v : ℝ) : ℂ) * Complex.I)).im := by ring
  rw [hcoef] at hd
  have hfun : fzzMarkedRadialReplicaPairedResponse u v = fun t : ℝ =>
      ((2 * (fzzMarkedRadialReplicaResponse u v t).re : ℝ) : ℂ) := by
    funext t
    rw [fzzMarkedRadialReplicaPairedResponse_eq, fzzMarkedRadialReplicaResponse_eq]
    congr 1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, zero_mul, sub_zero]
    ring
  rw [hfun]
  exact hd

theorem fzzMarkedRadialReplicaPairedMixedResponse_re_neg (u v w : ℝ) :
    (deriv (fzzMarkedRadialReplicaPairedResponse u v) (Real.exp w)).re < 0 := by
  rw [(hasDerivAt_fzzMarkedRadialReplicaPairedResponse_momentum u v (Real.exp w)).deriv,
    Complex.ofReal_re]
  apply mul_neg_of_pos_of_neg
  · exact div_pos (mul_pos (by norm_num) (fzzMarkedRadialReplicaRate_pos v)) (Real.exp_pos v)
  · exact _root_.RHTower.deriv_digamma_vertical_im_neg zero_lt_one (by positivity)

private theorem trigamma_conj (z : ℂ) :
    deriv Complex.digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (deriv Complex.digamma z) := by
  have hfun : ((starRingEnd ℂ) ∘ Complex.digamma ∘ (starRingEnd ℂ)) = Complex.digamma := by
    funext w
    simp only [Function.comp_apply, ReflectedDigammaAnomaly.digamma_conj,
      starRingEnd_self_apply]
  have hderiv := deriv_conj_conj (f := Complex.digamma)
  rw [hfun] at hderiv
  have h := congrFun hderiv ((starRingEnd ℂ) z)
  simpa only [Function.comp_apply, starRingEnd_self_apply] using h

private theorem trigamma_im_zero_iff (q : ℝ) :
    (deriv Complex.digamma (1 + (q : ℂ) * Complex.I)).im = 0 ↔ q = 0 := by
  have hzero : (deriv Complex.digamma 1).im = 0 := by
    have h := congrArg Complex.im (trigamma_conj 1)
    simp only [map_one, Complex.conj_im] at h
    linarith
  constructor
  · intro h
    rcases lt_trichotomy q 0 with hn | he | hp
    · have hh := _root_.RHTower.deriv_digamma_vertical_im_neg zero_lt_one (neg_pos.mpr hn)
      have ha : (1 : ℂ) + ((-q : ℝ) : ℂ) * Complex.I =
          (starRingEnd ℂ) (1 + (q : ℂ) * Complex.I) := by
        simp only [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_I,
          Complex.ofReal_neg, neg_mul, mul_neg]
      change (deriv Complex.digamma (1 + ((-q : ℝ) : ℂ) * Complex.I)).im < 0 at hh
      rw [ha, trigamma_conj, Complex.conj_im, h, neg_zero] at hh
      exact False.elim ((lt_irrefl 0) hh)
    · exact he
    · exact False.elim ((ne_of_lt
        (_root_.RHTower.deriv_digamma_vertical_im_neg zero_lt_one hp)) h)
  · intro h
    simpa only [h, Complex.ofReal_zero, zero_mul, add_zero] using hzero

/-- Exact radial mixed Ward receiver. Its vanishing is not assumed for the full CFT source. -/
theorem fzzMarkedRadialReplicaPairedMixedResponse_zero_iff (u v p : ℝ) :
    deriv (fzzMarkedRadialReplicaPairedResponse u v) p = 0 ↔ p = 0 := by
  rw [(hasDerivAt_fzzMarkedRadialReplicaPairedResponse_momentum u v p).deriv,
    Complex.ofReal_eq_zero, mul_eq_zero]
  have hc : 0 < 2 * fzzMarkedRadialReplicaRate v / Real.exp v :=
    div_pos (mul_pos (by norm_num) (fzzMarkedRadialReplicaRate_pos v)) (Real.exp_pos v)
  simp only [hc.ne', false_or, trigamma_im_zero_iff, div_eq_zero_iff,
    Real.exp_ne_zero, or_false]

end
end GaloisForLFunctions.RHTower
