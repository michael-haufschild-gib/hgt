import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGroundPolynomialStructure
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarConstrainedSmoothCore

/-!
# Ground multiplicity of the restricted Weil form and derivatives of ground states

At a positive aperture `a`, the polar ground level of the restricted Weil form is the polynomial
module `{P · f̂_G : deg P < d}` over a real-rooted generator `G` (`exists_groundGenerator`).

**Theorem** (`isPolarGround_of_mul`).  If `G` is a polar ground state and a polar form-domain
vector `v` has transform `t · f̂_G(t)` on the real line (the derivative of `G`'s time function,
up to `2πi`), then `v` is again a polar ground state.

**Corollary** (`two_le_finrank_iff`).  The ground level has multiplicity at least two iff the
time function of some nonzero polar ground state has a derivative in the polar form domain.

**Proof.**  The excess form `E(u, w) = ∫(S_a − μ_a) f̂_u conj(f̂_w)` vanishes on the ground state
against every polar vector (`excessForm_eq_zero_of_ground`).  For a smooth strict-interior polar
source `u`, its derivative `u'` is again such a source with `f̂_{u'} = 2πi t f̂_u`
(`unitaryLaplace_deriv`, integration by parts), and multiplication by the real variable `t`
moves across the form: `E(v, u) = E(G, u'/(2πi)) = 0`.  The polarization identity writes
`E(v, ·)` through the continuous quadratic `Q − μ_a‖J ·‖²`, and smooth polar sources are dense
in the polar form domain (`exists_polarConstrained_smooth_close`), so `E(v, ·) = 0` on polar
vectors and `E(v, v) = 0`.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped InnerProduct ComplexConjugate Real

namespace RHTower.CCMGroundDerivative

open GaloisForLFunctions.HTGeometry.FourierZeroFlip
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open RHTower.CCMRealRootedGround RHTower.CCMGroundQuadrature RHTower.CCMGroundStructure

variable (a : SuzukiPositiveAperture)

/-- The derivative of a strict-interior smooth source. -/
def derivSource (u : CCMComplexSmoothInteriorSource a) : CCMComplexSmoothInteriorSource a where
  toFun := deriv u
  smooth := (contDiff_infty_iff_deriv.mp u.smooth).2
  hasCompactSupport := u.hasCompactSupport.deriv
  tsupport_subset := tsupport_deriv_subset.trans u.tsupport_subset

theorem unitaryLaplace_timeRep_source (u : CCMComplexSmoothInteriorSource a) (w : ℂ) :
    unitaryLaplace (timeRep a u.toCCMFormVector) w = unitaryLaplace u w := by
  have h : timeRep a u.toCCMFormVector =ᵐ[volume] u :=
    (coeFn_eq_timeRep a u.toCCMFormVector).symm.trans u.toCCMFormVector_physical_coeFn
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-- Integration by parts: `∫ e^{−2πiwx} u'(x) dx = 2πiw ∫ e^{−2πiwx} u(x) dx`. -/
theorem unitaryLaplace_deriv (u : CCMComplexSmoothInteriorSource a) (w : ℂ) :
    unitaryLaplace (deriv u) w = 2 * π * I * w * unitaryLaplace u w := by
  set e : ℝ → ℂ := fun x => cexp (-(2 * π * I * w * x)) with he
  have hde : ∀ x : ℝ, HasDerivAt e (e x * (-(2 * π * I * w))) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => -(2 * π * I * w) * (y : ℂ)) (-(2 * π * I * w)) x := by
      simpa using (hasDerivAt_id (x : ℝ)).ofReal_comp.const_mul (-(2 * π * I * w))
    have h2 := h1.cexp
    have heq : (fun y : ℝ => cexp (-(2 * π * I * w) * (y : ℂ))) = e := by
      funext y; simp only [he]; ring_nf
    rw [heq] at h2
    convert h2 using 1
    simp only [he]; ring_nf
  have hdu : ∀ x : ℝ, HasDerivAt u (deriv u x) x := fun x =>
    ((u.smooth.differentiable (by simp)) x).hasDerivAt
  have hec : Continuous e := by simp only [he]; fun_prop
  have hdc : Continuous (deriv u) := (contDiff_infty_iff_deriv.mp u.smooth).2.continuous
  have hi1 : Integrable (e * deriv u) :=
    (hec.mul hdc).integrable_of_hasCompactSupport u.hasCompactSupport.deriv.mul_left
  have hi2 : Integrable ((fun x => e x * (-(2 * π * I * w))) * u.toFun) :=
    ((hec.mul continuous_const).mul u.continuous).integrable_of_hasCompactSupport
      u.hasCompactSupport.mul_left
  have hi3 : Integrable (e * u.toFun) :=
    (hec.mul u.continuous).integrable_of_hasCompactSupport u.hasCompactSupport.mul_left
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (fun x _ => hde x)
    (fun x _ => hdu x) hi1 hi2 hi3
  unfold unitaryLaplace
  change ∫ x, e x * deriv u x = 2 * π * I * w * ∫ x, e x * u x
  rw [hibp, ← integral_neg, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  ring

/-- The excess quadratic `Q(x) − μ_a‖Jx‖²`, through the continuous restricted Weil form. -/
def excessQuad (x : CCMArchimedeanFormDomain a) : ℂ :=
  (((ccmRestrictedWeilForm a x x).re -
    ccmRestrictedWeilPolarGroundEnergy a * ‖ccmArchimedeanFormToAperture a x‖ ^ 2 : ℝ) : ℂ)

theorem continuous_excessQuad : Continuous (excessQuad a) := by
  have hJ : Continuous (ccmArchimedeanFormToAperture a) :=
    (ccmArchimedeanFormToAperture a).continuous
  have hform : Continuous fun u : CCMArchimedeanFormDomain a => ccmRestrictedWeilForm a u u := by
    unfold ccmRestrictedWeilForm
    exact (continuous_id.inner continuous_id).add
      (((ccmRestrictedWeilBoundedRemainder a).continuous.comp hJ).inner hJ)
  unfold excessQuad
  exact Complex.continuous_ofReal.comp
    ((Complex.continuous_re.comp hform).sub (continuous_const.mul (hJ.norm.pow 2)))

theorem excessForm_self_eq_excessQuad {x : CCMArchimedeanFormDomain a}
    (hx : IsPolarConstrained a x) : excessForm a x x = excessQuad a x := by
  rw [excessForm_self a hx, excessQuad, ccmRestrictedWeilForm_self_re_eq_source]

theorem excessForm_polarization (v h : CCMArchimedeanFormDomain a) :
    excessForm a v h = (1 / 4 : ℂ) * (excessForm a (v + (1 : ℂ) • h) (v + (1 : ℂ) • h) -
      excessForm a (v + (-1 : ℂ) • h) (v + (-1 : ℂ) • h) +
      I * excessForm a (v + I • h) (v + I • h) -
      I * excessForm a (v + (-I) • h) (v + (-I) • h)) := by
  have key : ∀ c : ℂ, excessForm a (v + c • h) (v + c • h) = excessForm a v v +
      conj c * excessForm a v h + c * excessForm a h v + c * conj c * excessForm a h h := by
    intro c
    rw [excessForm_add_smul_left, excessForm_add_smul_right, excessForm_add_smul_right]
    ring
  rw [key, key, key, key]
  simp only [map_one, map_neg, Complex.conj_I, neg_neg]
  linear_combination (excessForm a v h - excessForm a h v) / 2 * Complex.I_sq

/-- **Frequency multiples of ground states are ground states.**  If `G` is a polar ground state
and a polar vector `v` has transform `t · f̂_G(t)` on the real line, then `v` is a polar ground
state.  For smooth polar `u`, `E(v, u) = E(G, k)` with `f̂_k = t f̂_u` (the derivative of `u`, which
is again polar), and `E(G, k) = 0`; density of smooth polar sources and continuity of the
polarized excess quadratic extend this to `E(v, ·) = 0` on polar vectors. -/
theorem isPolarGround_of_mul {G v : CCMArchimedeanFormDomain a} (hG : IsPolarGround a G)
    (hv : IsPolarConstrained a v)
    (hvG : ∀ t : ℝ, unitaryLaplace (timeRep a v) t =
      (t : ℂ) * unitaryLaplace (timeRep a G) t) :
    IsPolarGround a v := by
  have hπ : (2 * π * I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, I_ne_zero]
  have hsmooth : ∀ u : CCMComplexSmoothInteriorSource a,
      IsPolarConstrained a u.toCCMFormVector → excessForm a v u.toCCMFormVector = 0 := by
    intro u hu
    set k : CCMArchimedeanFormDomain a :=
      (1 / (2 * π * I) : ℂ) • (derivSource a u).toCCMFormVector with hkdef
    have hk : ∀ w : ℂ, unitaryLaplace (timeRep a k) w =
        w * unitaryLaplace (timeRep a u.toCCMFormVector) w := by
      intro w
      rw [hkdef, unitaryLaplace_timeRep_smul, unitaryLaplace_timeRep_source,
        unitaryLaplace_timeRep_source]
      change 1 / (2 * π * I) * unitaryLaplace (deriv u) w = _
      rw [unitaryLaplace_deriv]
      field_simp
    have hkpol : IsPolarConstrained a k := by
      rw [isPolarConstrained_iff] at hu ⊢
      rw [hk, hk, hu.1, hu.2, mul_zero, mul_zero]
      exact ⟨rfl, rfl⟩
    have hEL : excessForm a k G = 0 := excessForm_eq_zero_of_ground a hG hkpol
    have heq : excessForm a v u.toCCMFormVector = excessForm a G k := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp only
      rw [hvG t, hk t, map_mul, Complex.conj_ofReal]
      ring
    rw [heq, ← excessForm_conj, hEL, map_zero]
  set Φ : CCMArchimedeanFormDomain a → ℂ := fun h => (1 / 4 : ℂ) *
    (excessQuad a (v + (1 : ℂ) • h) - excessQuad a (v + (-1 : ℂ) • h) +
      I * excessQuad a (v + I • h) - I * excessQuad a (v + (-I) • h)) with hΦ
  have hΦc : Continuous Φ := by
    have hq := continuous_excessQuad a
    have hc : ∀ c : ℂ, Continuous fun h : CCMArchimedeanFormDomain a =>
        excessQuad a (v + c • h) :=
      fun c => hq.comp (continuous_const.add (continuous_id.const_smul c))
    exact continuous_const.mul ((((hc 1).sub (hc (-1))).add (continuous_const.mul (hc I))).sub
      (continuous_const.mul (hc (-I))))
  have hΦeq : ∀ h, IsPolarConstrained a h → excessForm a v h = Φ h := by
    intro h hh
    rw [excessForm_polarization a v h, hΦ]
    simp only
    rw [excessForm_self_eq_excessQuad a (isPolarConstrained_add_smul a hv hh 1),
      excessForm_self_eq_excessQuad a (isPolarConstrained_add_smul a hv hh (-1)),
      excessForm_self_eq_excessQuad a (isPolarConstrained_add_smul a hv hh I),
      excessForm_self_eq_excessQuad a (isPolarConstrained_add_smul a hv hh (-I))]
  have hall : ∀ h, IsPolarConstrained a h → excessForm a v h = 0 := by
    intro h hh
    have hclosed : IsClosed {x : CCMArchimedeanFormDomain a | Φ x = 0} :=
      isClosed_eq hΦc continuous_const
    have hmem : h ∈ closure {x : CCMArchimedeanFormDomain a | Φ x = 0} := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨u, hu, hu'⟩ := exists_polarConstrained_smooth_close a h hh hε
      refine ⟨u.toCCMFormVector, ?_, ?_⟩
      · show Φ u.toCCMFormVector = 0
        rw [← hΦeq _ hu]
        exact hsmooth u hu
      · rw [dist_eq_norm, norm_sub_rev]
        exact hu'
    rw [hclosed.closure_eq] at hmem
    rw [hΦeq h hh]
    exact hmem
  have h0 := hall v hv
  rw [excessForm_self a hv] at h0
  refine ⟨hv, ?_⟩
  have := Complex.ofReal_eq_zero.mp h0
  linarith

/-- **Multiplicity criterion.**  The polar ground level has multiplicity at least two iff some
nonzero polar ground state `G` has its frequency multiple `t f̂_G(t)` in the polar form domain,
i.e. iff the time function of some nonzero ground state has a form-domain derivative. -/
theorem two_le_finrank_iff :
    2 ≤ Module.finrank ℂ (groundSubmodule a) ↔ ∃ G v : CCMArchimedeanFormDomain a,
      IsPolarGround a G ∧ ccmArchimedeanFormToAperture a G ≠ 0 ∧ IsPolarConstrained a v ∧
        ∀ t : ℝ, unitaryLaplace (timeRep a v) t = (t : ℂ) * unitaryLaplace (timeRep a G) t := by
  classical
  haveI := finiteDimensional_groundSubmodule a
  constructor
  · intro hd
    obtain ⟨G, hG, hJG, -, -, hmul⟩ := exists_groundGenerator a
    obtain ⟨u, hu, P, hPm, hPd, hP⟩ := hmul 1 (by omega)
    refine ⟨G, u + (-(P.coeff 0)) • G, hG, hJG, isPolarConstrained_add_smul a hu.1 hG.1 _,
      fun t => ?_⟩
    have hPe : P.eval (t : ℂ) = t + P.coeff 0 := by
      conv_lhs => rw [Polynomial.Monic.eq_X_add_C hPm hPd]
      simp
    rw [unitaryLaplace_timeRep_add_smul, hP t, hPe]
    ring
  · rintro ⟨G, v, hG, hJG, hv, hvG⟩
    have hvg := isPolarGround_of_mul a hG hv hvG
    have hli : LinearIndependent ℂ ![(⟨G, hG⟩ : groundSubmodule a), ⟨v, hvg⟩] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have hval : ∀ τ : ℝ, (s + t * τ) * unitaryLaplace (timeRep a G) τ = 0 := by
        intro τ
        have h0 := congrArg (fun x : groundSubmodule a => evalAt a τ x.1) hst
        simp only [Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, smul_eq_mul,
          evalAt_apply, Submodule.coe_zero, map_zero] at h0
        rw [hvG τ] at h0
        linear_combination h0
      obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ := (infinite_real_ne_zero a hJG).nontrivial
      have e1 : s + t * t₁ = 0 := (mul_eq_zero.mp (hval t₁)).resolve_right ht₁
      have e2 : s + t * t₂ = 0 := (mul_eq_zero.mp (hval t₂)).resolve_right ht₂
      have ht0 : t = 0 := by
        have h3 : t * ((t₁ : ℂ) - t₂) = 0 := by linear_combination e1 - e2
        exact (mul_eq_zero.mp h3).resolve_right (sub_ne_zero.mpr (by exact_mod_cast hne))
      refine ⟨?_, ht0⟩
      rw [ht0, zero_mul, add_zero] at e1
      exact e1
    have := hli.fintype_card_le_finrank
    simpa using this

end RHTower.CCMGroundDerivative
