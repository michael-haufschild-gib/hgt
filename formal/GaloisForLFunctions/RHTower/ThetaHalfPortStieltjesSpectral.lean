import GaloisForLFunctions.HTGeometry.OnePortSpectralModel
import GaloisForLFunctions.RHTower.ThetaRenewalExitDensity
import GaloisForLFunctions.RHTower.ThetaHalfLinePortOrientation
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCenterMixedThreePoint
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAllShiftedTails
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedSourceOddStationary
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspAbelBoundaryPairing

/-!
# The theta half-port as a positive Stieltjes spectral measure

Let `k` be the completed theta source, `h(z) = ∫₀^∞ k(x) e^{izx} dx` the one-sided connection and
`ω = -k'`.  The density `σ(t) = (1/(π√t)) ∫₀^∞ ω(x)(1 - cos(√t x)) dx` is positive and smooth on
`(0, ∞)`, `O(√t)` at zero and `O(t^{-1/2})` at infinity.

* **(2), (2a).** `h(w) = ∫₀^∞ σ(t)/(t - w²) dt` for `Im w > 0`; the Stieltjes function
  `m(ζ) = h(w)` has positive imaginary part in the upper half-plane and `m(-r²) = h(ir) > 0`.  On
  `L²(σ(t) dt/(1 + t))` multiplication by `t` is self-adjoint, without eigenvalues, and
  `m(ζ) = m(-1) + (ζ + 1) ⟨1, (A - ζ)⁻¹ 1⟩`.
* **(3).** The boundary sheets are `m(u² ± i0) = h(±u)`, `σ(u²) = Im h(u)/π`, and
  `Ξ(u) = 2 PV ∫₀^∞ σ(t)/(t - u²) dt`.
* **(4), (4a)–(4c).** From the renewal seam `h(2r) = (a - ir) D(-ir) + icr` with
  `D(-ir) = c e^{-C(r) - iS(r)}`: `πσ(u²) = c[r - e^{-C(r)}(r cos S(r) + a sin S(r))] > 0`, `r = u/2`.
  From the Ward reduction: `πσ(u²) = u(c - 1)/2 - ((u² + 1/4)/4) Im M_u` and
  `Ξ(u) = 1/2 - ((u² + 1/4)/2) Re M_u`, whence `Im M_u < 2u(c - 1)/(u² + 1/4)` and the
  renewal–Mellin identity.
* **(7)–(11).** The right tails `h_s(z) = ∫₀^∞ k(s + x) e^{izx} dx` satisfy
  `∂_s h_s = -k(s) - iz h_s`, a forced rotation of `(Re, Im) h_s(u)`; each tail density
  `σ_s(t) = Im h_s(√t)/π` is positive, flows by `∂_s σ_s(t) = -(√t/π) PV ∫ σ_s(q)/(q - t) dq`, and
  at the seam `∂_s σ_s(u²)|₀ = -(u/(2π)) Ξ(u)`.
-/
open MeasureTheory Complex Set Filter Topology
open GaloisForLFunctions.HTGeometry (OnePortSource onePortConnection onePortDensity
  onePortStieltjes onePortSpectralMeasure onePortOperator isSelfAdjoint_onePortOperator upperRoot
  upperRootPath)
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

open HurwitzZeta

local notation "Θ" => evenKernel (0 : UnitAddCircle)

/-! ## The theta source as a one-port source -/

theorem strictAntiOn_thetaCuspFullSource : StrictAntiOn thetaCuspFullSource (Ici (0 : ℝ)) := by
  intro s hs t ht hst
  have h := strictAntiOn_thetaCuspFullSource_mul_reflect 0 hs ht hst
  simp only [zero_add, zero_sub, thetaCuspFullSource_neg] at h
  nlinarith [thetaCuspFullSource_pos_all s, thetaCuspFullSource_pos_all t]

theorem integrable_thetaCuspFullSource' : Integrable thetaCuspFullSource :=
  thetaCuspSchwartzReal.integrable (μ := (volume : Measure ℝ))

theorem integrable_abs_mul_thetaCuspFullSource :
    Integrable fun x : ℝ => |x| * thetaCuspFullSource x := by
  have h := HedenmalmThetaSource.integrable_abs_mul_exp_abs_mul_thetaCuspFullSource 0
  simpa using h

/-- Every right tail `x ↦ k(s + x)`, `s ≥ 0`, of the completed theta source is a one-port
source. -/
theorem onePortSource_thetaShift {s : ℝ} (hs : 0 ≤ s) :
    OnePortSource fun x => thetaCuspFullSource (s + x) where
  differentiable := differentiable_thetaCuspFullSource.comp (differentiable_id.const_add s)
  strictAntiOn := fun a ha b hb hab =>
    strictAntiOn_thetaCuspFullSource (mem_Ici.mpr (by linarith [mem_Ici.mp ha]))
      (mem_Ici.mpr (by linarith [mem_Ici.mp hb])) (by linarith)
  integrableOn := (integrable_thetaCuspFullSource'.comp_add_left s).integrableOn
  integrableOn_mul := by
    refine ((integrable_abs_mul_thetaCuspFullSource.comp_add_left s).integrableOn).mono'
      (by have := continuous_thetaCuspFullSource; fun_prop) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
    have hx : 0 < x := hx
    have hk := (thetaCuspFullSource_pos_all (s + x)).le
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx, abs_of_nonneg hk,
      abs_of_nonneg (by linarith : 0 ≤ s + x)]
    nlinarith
  tendsto_atTop := tendsto_thetaCuspFullSource_atTop_zero.comp (tendsto_atTop_add_const_left _ s
    tendsto_id)

theorem onePortSource_thetaCuspFullSource : OnePortSource thetaCuspFullSource := by
  simpa using onePortSource_thetaShift le_rfl

/-- The one-sided theta connection is the connection of the one-port source `k`. -/
theorem onePortConnection_thetaCuspFullSource :
    onePortConnection thetaCuspFullSource = thetaOneSidedConnection := rfl

theorem thetaOneSidedConnection_eq_thetaHalfLaplace (z : ℂ) :
    thetaOneSidedConnection z = thetaHalfLaplace (I * z) := by
  rw [thetaOneSidedConnection, thetaHalfLaplace, thetaHalfLaplaceTail]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  ring

/-- The one-sided connection is entire. -/
theorem differentiable_thetaOneSidedConnection : Differentiable ℂ thetaOneSidedConnection := by
  have h : thetaOneSidedConnection = fun z => thetaHalfLaplace (I * z) :=
    funext thetaOneSidedConnection_eq_thetaHalfLaplace
  rw [h]
  exact differentiable_thetaHalfLaplace.comp (differentiable_id.const_mul I)

/-- On the real axis `Ξ(u) = h(u) + h(-u) = 2 Re h(u)`. -/
theorem Xi_eq_two_mul_re_thetaOneSidedConnection (u : ℝ) :
    Xi u = 2 * (thetaOneSidedConnection u).re := by
  have h := XiC_eq_thetaOneSidedConnection_add (u : ℂ)
  rw [XiC_ofReal, show -(u : ℂ) = ((-u : ℝ) : ℂ) by push_cast; ring,
    ← onePortConnection_thetaCuspFullSource, GaloisForLFunctions.HTGeometry.onePortConnection_neg_ofReal] at h
  have := congrArg Complex.re h
  simp only [ofReal_re, add_re, conj_re] at this
  rw [onePortConnection_thetaCuspFullSource] at this
  linarith

/-! ## The spectral density of the theta port -/

/-- The theta spectral density
`σ(t) = (1/(π√t)) ∫₀^∞ ω(x) (1 - cos(√t x)) dx`, `ω = -k'`. -/
def thetaPortDensity : ℝ → ℝ := onePortDensity thetaCuspFullSource

/-- **(1).** `σ(t) > 0` for `t > 0`. -/
theorem thetaPortDensity_pos {t : ℝ} (ht : 0 < t) : 0 < thetaPortDensity t :=
  onePortSource_thetaCuspFullSource.onePortDensity_pos ht

/-- **(1), decay at infinity.** `σ(t) ≤ 2k(0)/(π√t)`. -/
theorem thetaPortDensity_le_inv_sqrt {t : ℝ} (ht : 0 < t) :
    thetaPortDensity t ≤ 2 * thetaCuspFullSource 0 / (Real.pi * √t) :=
  onePortSource_thetaCuspFullSource.onePortDensity_le_inv_sqrt ht

/-- **(1), behaviour at zero.** `σ(t) ≤ (√t/π) ∫₀^∞ x k(x) dx`. -/
theorem thetaPortDensity_le_sqrt {t : ℝ} (ht : 0 < t) :
    thetaPortDensity t ≤ √t / Real.pi * ∫ x in Ioi (0 : ℝ), x * thetaCuspFullSource x :=
  onePortSource_thetaCuspFullSource.onePortDensity_le_sqrt ht

/-- **(1).** `∫₀^∞ σ(t)/(1 + t) dt < ∞`. -/
theorem integrableOn_thetaPortDensity_div :
    IntegrableOn (fun t => thetaPortDensity t / (1 + t)) (Ioi 0) :=
  onePortSource_thetaCuspFullSource.integrableOn_onePortDensity_div

/-- **(3).** `σ(u²) = Im h(u) / π` for `u > 0`. -/
theorem thetaPortDensity_sq {u : ℝ} (hu : 0 < u) :
    thetaPortDensity (u ^ 2) = (thetaOneSidedConnection u).im / Real.pi :=
  onePortSource_thetaCuspFullSource.onePortDensity_sq hu

theorem thetaPortDensity_eq_im (t : ℝ) :
    thetaPortDensity t = (thetaOneSidedConnection (√t : ℝ)).im / Real.pi :=
  onePortSource_thetaCuspFullSource.onePortDensity_eq_im t

/-- **(1), local smoothness.** `σ` is smooth on `(0, ∞)`. -/
theorem contDiffOn_thetaPortDensity : ContDiffOn ℝ ⊤ thetaPortDensity (Ioi 0) := by
  have hh : ContDiff ℝ ⊤ thetaOneSidedConnection :=
    (differentiable_thetaOneSidedConnection.contDiff (n := ⊤)).restrict_scalars ℝ
  have hs : ContDiffOn ℝ ⊤ (fun t : ℝ => ((√t : ℝ) : ℂ)) (Ioi 0) :=
    ofRealCLM.contDiff.comp_contDiffOn
      (fun t ht => (Real.contDiffAt_sqrt (mem_Ioi.mp ht).ne').contDiffWithinAt)
  have h := (imCLM.contDiff.comp_contDiffOn (hh.comp_contDiffOn hs)).div_const Real.pi
  refine h.congr fun t _ => ?_
  rw [thetaPortDensity_eq_im]
  rfl

/-- **(5).** For `u > 0`,
`Im h(u) = ∫₀^∞ k(x) sin(ux) dx = (1/u) ∫₀^∞ ω(x)(1 - cos(ux)) dx > 0`. -/
theorem im_thetaOneSidedConnection_eq {u : ℝ} (hu : 0 < u) :
    (thetaOneSidedConnection u).im = ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.sin (u * x) ∧
      (thetaOneSidedConnection u).im =
        1 / u * ∫ x in Ioi (0 : ℝ), -deriv thetaCuspFullSource x * (1 - Real.cos (u * x)) ∧
      0 < (thetaOneSidedConnection u).im := by
  refine ⟨onePortSource_thetaCuspFullSource.im_onePortConnection_ofReal u,
    onePortSource_thetaCuspFullSource.im_onePortConnection_eq hu, ?_⟩
  have h := thetaPortDensity_sq hu
  have hσ := thetaPortDensity_pos (by positivity : 0 < u ^ 2)
  rw [h] at hσ
  exact (div_pos_iff_of_pos_right Real.pi_pos).mp hσ

/-- On the spectral cut the upper boundary value never vanishes: `m₊(u²) = h(u) ≠ 0`. -/
theorem thetaOneSidedConnection_ne_zero {u : ℝ} (hu : 0 < u) : thetaOneSidedConnection u ≠ 0 :=
  fun h => by
    have := (im_thetaOneSidedConnection_eq hu).2.2
    rw [h, zero_im] at this
    exact lt_irrefl 0 this

/-! ## The Stieltjes representation and the self-adjoint model -/

/-- **(2).** `h(w) = ∫₀^∞ σ(t)/(t - w²) dt` for `Im w > 0`. -/
theorem thetaOneSidedConnection_eq_stieltjes {w : ℂ} (hw : 0 < w.im) :
    thetaOneSidedConnection w =
      ∫ t in Ioi (0 : ℝ), (thetaPortDensity t : ℂ) / ((t : ℂ) - w ^ 2) :=
  onePortSource_thetaCuspFullSource.onePortConnection_eq_stieltjes hw

/-- **(2).** `m(ζ) = h(w) = ∫₀^∞ σ(t)/(t - ζ) dt` on `ℂ \ [0, ∞)`, with `w² = ζ`, `Im w > 0`. -/
theorem thetaStieltjes_eq {ζ : ℂ} (hζ : -ζ ∈ slitPlane) :
    onePortStieltjes thetaCuspFullSource ζ = thetaOneSidedConnection (upperRoot ζ) ∧
      upperRoot ζ ^ 2 = ζ ∧ 0 < (upperRoot ζ).im ∧
      onePortStieltjes thetaCuspFullSource ζ =
        ∫ t in Ioi (0 : ℝ), (thetaPortDensity t : ℂ) / ((t : ℂ) - ζ) :=
  ⟨rfl, GaloisForLFunctions.HTGeometry.upperRoot_sq ζ,
    GaloisForLFunctions.HTGeometry.upperRoot_im_pos hζ,
    onePortSource_thetaCuspFullSource.onePortStieltjes_eq hζ⟩

/-- **(2).** `Im m(ζ) > 0` for `Im ζ > 0`. -/
theorem im_thetaStieltjes_pos {ζ : ℂ} (hζ : 0 < ζ.im) :
    0 < (onePortStieltjes thetaCuspFullSource ζ).im :=
  onePortSource_thetaCuspFullSource.im_onePortStieltjes_pos hζ

/-- **(2).** `m(-r²) = h(ir) = ∫₀^∞ k(x)e^{-rx} dx > 0` for `r > 0`. -/
theorem thetaStieltjes_neg_sq {r : ℝ} (hr : 0 < r) :
    onePortStieltjes thetaCuspFullSource (-(r ^ 2 : ℝ)) = thetaOneSidedConnection (I * r) ∧
      onePortStieltjes thetaCuspFullSource (-(r ^ 2 : ℝ)) =
        ((∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (-(r * x)) : ℝ) : ℂ) ∧
      0 < ∫ x in Ioi (0 : ℝ), thetaCuspFullSource x * Real.exp (-(r * x)) :=
  onePortSource_thetaCuspFullSource.onePortStieltjes_neg_sq hr

/-- **(2a).** Multiplication by `t` on `L²(σ(t) dt/(1 + t))` is self-adjoint. -/
theorem isSelfAdjoint_thetaPortOperator : IsSelfAdjoint (onePortOperator thetaCuspFullSource) :=
  isSelfAdjoint_onePortOperator thetaCuspFullSource

/-- **(2a).** The exact resolvent formula
`m(ζ) = m(-1) + (ζ + 1) ⟨1, (A - ζ)⁻¹ 1⟩_{L²(μ)}` for `ζ ∉ [0, ∞)`, where the resolvent is a
bounded two-sided inverse of `A - ζ`. -/
theorem thetaStieltjes_eq_resolvent {ζ : ℂ} (hζ : -ζ ∈ slitPlane) :
    ∃ R : Lp ℂ 2 (onePortSpectralMeasure thetaCuspFullSource) →L[ℂ]
        Lp ℂ 2 (onePortSpectralMeasure thetaCuspFullSource),
      (∀ f, ∃ hf : R f ∈ (onePortOperator thetaCuspFullSource).domain,
        onePortOperator thetaCuspFullSource ⟨R f, hf⟩ - ζ • R f = f) ∧
      (∀ g : (onePortOperator thetaCuspFullSource).domain,
        R (onePortOperator thetaCuspFullSource g -
          ζ • (g : Lp ℂ 2 (onePortSpectralMeasure thetaCuspFullSource))) = g) ∧
      onePortStieltjes thetaCuspFullSource ζ = onePortStieltjes thetaCuspFullSource (-1) +
        (ζ + 1) * ⟪onePortSource_thetaCuspFullSource.onePortUnit,
          R onePortSource_thetaCuspFullSource.onePortUnit⟫_ℂ :=
  onePortSource_thetaCuspFullSource.onePortStieltjes_eq_resolvent hζ

/-- A real zero of the principal-value trace is not an eigenvalue of `A`: the operator has no
eigenvectors at all. -/
theorem thetaPortOperator_eigenvector_eq_zero (lam : ℂ)
    (f : (onePortOperator thetaCuspFullSource).domain)
    (hf : onePortOperator thetaCuspFullSource f =
      lam • (f : Lp ℂ 2 (onePortSpectralMeasure thetaCuspFullSource))) :
    (f : Lp ℂ 2 (onePortSpectralMeasure thetaCuspFullSource)) = 0 :=
  GaloisForLFunctions.HTGeometry.onePortOperator_eigenvector_eq_zero _ lam f hf

/-! ## The two boundary sheets and the principal-value trace (3) -/

/-- **(3), upper sheet.** `m(u² + iη) → h(u)`. -/
theorem tendsto_thetaStieltjes_upper {u : ℝ} (hu : 0 < u) :
    Tendsto (fun η : ℝ => ∫ t in Ioi (0 : ℝ), (thetaPortDensity t : ℂ) /
      ((t : ℂ) - ((u ^ 2 : ℝ) + η * I))) (𝓝[>] 0) (𝓝 (thetaOneSidedConnection u)) :=
  onePortSource_thetaCuspFullSource.tendsto_stieltjes_upper hu

/-- **(3), lower sheet.** `m(u² - iη) → h(-u) = conj h(u)`. -/
theorem tendsto_thetaStieltjes_lower {u : ℝ} (hu : 0 < u) :
    Tendsto (fun η : ℝ => ∫ t in Ioi (0 : ℝ), (thetaPortDensity t : ℂ) /
      ((t : ℂ) - ((u ^ 2 : ℝ) - η * I))) (𝓝[>] 0)
        (𝓝 (thetaOneSidedConnection (-u : ℝ))) ∧
      thetaOneSidedConnection (-u : ℝ) = conj (thetaOneSidedConnection u) :=
  ⟨onePortSource_thetaCuspFullSource.tendsto_stieltjes_lower hu,
    GaloisForLFunctions.HTGeometry.onePortConnection_neg_ofReal _ u⟩

/-- **(3).** `Ξ(u) = 2 PV ∫₀^∞ σ(t)/(t - u²) dt` for `u > 0`, the principal value being the limit
of the symmetric truncations. -/
theorem tendsto_thetaPrincipalValue_Xi {u : ℝ} (hu : 0 < u) :
    Tendsto (fun ε => 2 * ∫ t in Ioi (0 : ℝ) \ Icc (u ^ 2 - ε) (u ^ 2 + ε),
      thetaPortDensity t / (t - u ^ 2)) (𝓝[>] 0) (𝓝 (Xi u)) := by
  rw [Xi_eq_two_mul_re_thetaOneSidedConnection]
  exact (onePortSource_thetaCuspFullSource.tendsto_onePortPrincipalValue hu).const_mul 2

/-! ## The renewal form (4) -/

/-- `C(r) = ∫₀^∞ Q(s) cos(rs) ds`. -/
def thetaRenewalRealCos (r : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.cos (r * t)

/-- `S(r) = ∫₀^∞ Q(s) sin(rs) ds`. -/
def thetaRenewalRealSin (r : ℝ) : ℝ := ∫ t in Ioi (0 : ℝ), thetaRenewalLogKernel t * Real.sin (r * t)

theorem thetaRenewalCosTransform_I_mul (r : ℝ) :
    thetaRenewalCosTransform (I * r) = (thetaRenewalRealCos r : ℂ) := by
  rw [thetaRenewalCosTransform, thetaRenewalRealCos, ← integral_complex_ofReal]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show I * (r : ℂ) * t = ((r * t : ℝ) : ℂ) * I by push_cast; ring, Complex.cosh_mul_I]
  push_cast; ring

theorem thetaRenewalSinTransform_I_mul (r : ℝ) :
    thetaRenewalSinTransform (I * r) = (thetaRenewalRealSin r : ℂ) * I := by
  rw [thetaRenewalSinTransform, thetaRenewalRealSin, ← integral_complex_ofReal,
    ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show I * (r : ℂ) * t = ((r * t : ℝ) : ℂ) * I by push_cast; ring, Complex.sinh_mul_I]
  push_cast; ring

/-- `D(-ir) = c exp(-C(r) - iS(r))`. -/
theorem thetaRenewalDenominator_neg_I_mul (r : ℝ) :
    thetaRenewalDenominator (-(I * r)) =
      (Θ 1 : ℂ) * cexp (-((thetaRenewalRealCos r : ℂ) + (thetaRenewalRealSin r : ℂ) * I)) := by
  have hre : -(1 / 4 : ℝ) ≤ (-(I * (r : ℂ))).re := by simp
  have habs : |(-(I * (r : ℂ))).re| ≤ 1 / 4 := by simp
  rw [thetaRenewalDenominator_eq_exp hre, thetaRenewalLogKernelLaplace_eq_cos_sub_sin habs,
    thetaRenewalCosTransform_neg, thetaRenewalSinTransform_neg, thetaRenewalCosTransform_I_mul,
    thetaRenewalSinTransform_I_mul, sub_neg_eq_add]

theorem cexp_neg_add_mul_I (C S : ℝ) :
    cexp (-((C : ℂ) + (S : ℂ) * I)) =
      (Real.exp (-C) : ℂ) * ((Real.cos S : ℂ) - (Real.sin S : ℂ) * I) := by
  rw [neg_add, Complex.exp_add, ← ofReal_neg, ← ofReal_exp, show -((S : ℂ) * I) =
    ((-S : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_neg, Real.sin_neg]
  push_cast; ring

/-- **(4).** For `u > 0`, `r = u/2`, `a = 1/4`, `c = Θ(1)`:
`πσ(u²) = c [r - e^{-C(r)} (r cos S(r) + a sin S(r))] > 0`. -/
theorem pi_mul_thetaPortDensity_sq_eq_renewal {u : ℝ} (hu : 0 < u) :
    Real.pi * thetaPortDensity (u ^ 2) =
        Θ 1 * (u / 2 - Real.exp (-thetaRenewalRealCos (u / 2)) *
          (u / 2 * Real.cos (thetaRenewalRealSin (u / 2)) +
            1 / 4 * Real.sin (thetaRenewalRealSin (u / 2)))) ∧
      0 < Θ 1 * (u / 2 - Real.exp (-thetaRenewalRealCos (u / 2)) *
          (u / 2 * Real.cos (thetaRenewalRealSin (u / 2)) +
            1 / 4 * Real.sin (thetaRenewalRealSin (u / 2)))) := by
  have hσ : Real.pi * thetaPortDensity (u ^ 2) = (thetaOneSidedConnection u).im := by
    rw [thetaPortDensity_sq hu]; field_simp
  have h := thetaOneSidedConnection_two_mul_eq_denominator ((u / 2 : ℝ) : ℂ)
  rw [show 2 * ((u / 2 : ℝ) : ℂ) = (u : ℂ) by push_cast; ring,
    thetaRenewalDenominator_neg_I_mul, cexp_neg_add_mul_I] at h
  have heq : Real.pi * thetaPortDensity (u ^ 2) =
      Θ 1 * (u / 2 - Real.exp (-thetaRenewalRealCos (u / 2)) *
        (u / 2 * Real.cos (thetaRenewalRealSin (u / 2)) +
          1 / 4 * Real.sin (thetaRenewalRealSin (u / 2)))) := by
    rw [hσ, h]
    simp only [add_im, mul_im, sub_im, sub_re, mul_re, ofReal_re, ofReal_im, I_re, I_im,
      div_ofNat_re, div_ofNat_im, one_re, one_im]
    ring
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact mul_pos Real.pi_pos (thetaPortDensity_pos (by positivity))

/-! ## The Mellin form (4a)–(4c) -/

theorem jacobiThetaSum_one_eq : jacobiThetaSum 1 = (Θ 1 : ℂ) := by
  simpa using jacobiThetaSum_ofReal_eq_evenKernel 1

/-- **(4a).** `πσ(u²) = u(c-1)/2 - ((u² + 1/4)/4) Im M_u` for `u > 0`. -/
theorem pi_mul_thetaPortDensity_sq_eq_ward {u : ℝ} (hu : 0 < u) :
    Real.pi * thetaPortDensity (u ^ 2) =
      u * (Θ 1 - 1) / 2 - (u ^ 2 + 1 / 4) / 4 * (wardMellin u).im := by
  rw [thetaPortDensity_sq hu, mul_div_cancel₀ _ Real.pi_ne_zero, thetaOneSidedConnection_eq_ward,
    jacobiThetaSum_one_eq]
  simp only [add_im, sub_im, mul_im, div_ofNat_re, div_ofNat_im, mul_re, I_re, I_im, ofReal_re,
    ofReal_im, sub_re, one_re, one_im, add_re, pow_two]
  norm_num
  ring

/-- **(4a).** `Ξ(u) = 1/2 - ((u² + 1/4)/2) Re M_u`. -/
theorem Xi_eq_ward (u : ℝ) : Xi u = 1 / 2 - (u ^ 2 + 1 / 4) / 2 * (wardMellin u).re := by
  rw [Xi_eq_two_mul_re_thetaOneSidedConnection, thetaOneSidedConnection_eq_ward,
    jacobiThetaSum_one_eq]
  simp only [add_re, sub_re, mul_re, div_ofNat_re, div_ofNat_im, I_re, I_im, ofReal_re,
    ofReal_im, one_re, one_im, sub_im, mul_im, add_im, pow_two]
  norm_num
  ring

/-- **(4c).** The strict Abel inequality `Im M_u < 2u(c - 1)/(u² + 1/4)` for `u > 0`. -/
theorem im_wardMellin_lt {u : ℝ} (hu : 0 < u) :
    (wardMellin u).im < 2 * u * (Θ 1 - 1) / (u ^ 2 + 1 / 4) := by
  have h := pi_mul_thetaPortDensity_sq_eq_ward hu
  have hpos := mul_pos Real.pi_pos (thetaPortDensity_pos (by positivity : 0 < u ^ 2))
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- **(4c) through the square-phase potential.** The same strict inequality for the global
quadratic-phase representation of `M_u`. -/
theorem im_squarePhaseRepresentation_lt {u : ℝ} (hu : 0 < u) :
    (abelArcTerm (wardExponent u) +
      2 * cexp ((wardExponent u + 1) * ((Real.pi / 2 : ℝ) * I)) *
        (I * Real.pi / 12 + wardExponent u / (I * Real.pi) *
          ∫ r in Ioi (1 : ℝ), (r : ℂ) ^ (wardExponent u - 1) * squarePhasePotential r)).im <
      2 * u * (Θ 1 - 1) / (u ^ 2 + 1 / 4) := by
  rw [← wardMellin_eq_squarePhasePotential (u : ℂ) (by simp)]
  exact im_wardMellin_lt hu

/-- **(4b).** Renewal–Mellin compatibility:
`((u² + 1/4)/4) Im M_u = c e^{-C(u/2)} [(u/2) cos S(u/2) + a sin S(u/2)] - u/2`. -/
theorem wardMellin_im_eq_renewal {u : ℝ} (hu : 0 < u) :
    (u ^ 2 + 1 / 4) / 4 * (wardMellin u).im =
      Θ 1 * Real.exp (-thetaRenewalRealCos (u / 2)) *
        (u / 2 * Real.cos (thetaRenewalRealSin (u / 2)) +
          1 / 4 * Real.sin (thetaRenewalRealSin (u / 2))) - u / 2 := by
  have h1 := (pi_mul_thetaPortDensity_sq_eq_renewal hu).1
  have h2 := pi_mul_thetaPortDensity_sq_eq_ward hu
  linarith

/-! ## The flow of right-tail connections (7)–(11) -/

/-- The right-tail connection `h_s(z) = ∫₀^∞ k(s + x) e^{izx} dx`. -/
def thetaShiftConnection (s : ℝ) (z : ℂ) : ℂ :=
  onePortConnection (fun x => thetaCuspFullSource (s + x)) z

/-- The right-tail density `σ_s(t) = Im h_s(√t) / π`. -/
def thetaShiftDensity (s t : ℝ) : ℝ := (thetaShiftConnection s (√t : ℝ)).im / Real.pi

theorem thetaShiftConnection_zero : thetaShiftConnection 0 = thetaOneSidedConnection := by
  funext z
  simp only [thetaShiftConnection, zero_add]
  rfl

/-- For `s ≥ 0` the tail density is the one-port density of the tail source. -/
theorem thetaShiftDensity_eq {s : ℝ} (hs : 0 ≤ s) :
    thetaShiftDensity s = onePortDensity fun x => thetaCuspFullSource (s + x) :=
  funext fun t => ((onePortSource_thetaShift hs).onePortDensity_eq_im t).symm

/-- **(7).** `σ_s(t) > 0` for every tail `s ≥ 0` and `t > 0`. -/
theorem thetaShiftDensity_pos {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) : 0 < thetaShiftDensity s t := by
  rw [thetaShiftDensity_eq hs]
  exact (onePortSource_thetaShift hs).onePortDensity_pos ht

/-- **(7).** Each tail connection is the Stieltjes transform of its density. -/
theorem thetaShiftConnection_eq_stieltjes {s : ℝ} (hs : 0 ≤ s) {w : ℂ} (hw : 0 < w.im) :
    thetaShiftConnection s w =
      ∫ t in Ioi (0 : ℝ), (thetaShiftDensity s t : ℂ) / ((t : ℂ) - w ^ 2) := by
  rw [thetaShiftDensity_eq hs]
  exact (onePortSource_thetaShift hs).onePortConnection_eq_stieltjes hw

theorem integral_Ioi_comp_add (f : ℝ → ℂ) (s : ℝ) :
    ∫ x in Ioi (0 : ℝ), f (s + x) = ∫ y in Ioi s, f y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    ← integral_add_left_eq_self (μ := volume) ((Ioi s).indicator f) s]
  congr 1
  funext x
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx),
      indicator_of_mem (show s + x ∈ Ioi s by simp [hx])]
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
      indicator_of_notMem (show s + x ∉ Ioi s by simpa using hx)]

theorem thetaShiftConnection_eq_tail (s : ℝ) (z : ℂ) :
    thetaShiftConnection s z =
      cexp (-(I * z * s)) * ∫ y in Ioi s, cexp (I * z * y) * (thetaCuspFullSource y : ℂ) := by
  have h1 : ∫ x in Ioi (0 : ℝ), (thetaCuspFullSource (s + x) : ℂ) * cexp (I * z * x) =
      ∫ x in Ioi (0 : ℝ), (fun y : ℝ => (thetaCuspFullSource y : ℂ) *
        cexp (I * z * ((y : ℂ) - s))) (s + x) := by
    congr 1; funext x; push_cast; ring_nf
  rw [thetaShiftConnection, GaloisForLFunctions.HTGeometry.onePortConnection, h1,
    integral_Ioi_comp_add (fun y : ℝ => (thetaCuspFullSource y : ℂ) *
      cexp (I * z * ((y : ℂ) - s))) s, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [mul_sub, Complex.exp_sub]
  field_simp [Complex.exp_ne_zero]
  ring_nf
  rw [mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, mul_one]

theorem hasDerivAt_thetaTail (z : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ y in Ioi s, cexp (I * z * y) * (thetaCuspFullSource y : ℂ))
      (-(cexp (I * z * s) * (thetaCuspFullSource s : ℂ))) s := by
  set F : ℝ → ℂ := fun y => cexp (I * z * y) * (thetaCuspFullSource y : ℂ)
  have hFi : Integrable F := by
    have h := integrable_cexp_mul_thetaCuspFullSource (I * z)
    exact h.congr (Eventually.of_forall fun y => by simp only [F])
  have hFc : Continuous F := by
    have := continuous_thetaCuspFullSource; simp only [F]; fun_prop
  have hrep : (fun s : ℝ => ∫ y in Ioi s, F y) =
      fun s : ℝ => (∫ y in s..0, F y) + ∫ y in Ioi (0 : ℝ), F y :=
    funext fun s => (intervalIntegral.integral_interval_add_Ioi hFi.integrableOn
      hFi.integrableOn).symm
  change HasDerivAt (fun s : ℝ => ∫ y in Ioi s, F y) (-F s) s
  rw [hrep]
  exact (intervalIntegral.integral_hasDerivAt_left (hFi.intervalIntegrable)
    hFc.aestronglyMeasurable.stronglyMeasurableAtFilter hFc.continuousAt).add_const _

/-- **(8).** The causal source equation `∂_s h_s(z) = -k(s) - iz h_s(z)`. -/
theorem hasDerivAt_thetaShiftConnection (z : ℂ) (s : ℝ) :
    HasDerivAt (fun s => thetaShiftConnection s z)
      (-(thetaCuspFullSource s : ℂ) - I * z * thetaShiftConnection s z) s := by
  have he : HasDerivAt (fun s : ℝ => cexp (-(I * z * s))) (cexp (-(I * z * s)) * -(I * z)) s := by
    have h := (((hasDerivAt_id (s : ℂ)).const_mul (I * z)).neg).cexp.comp_ofReal
    simpa using h
  have h := he.mul (hasDerivAt_thetaTail z s)
  have hfun : (fun s => thetaShiftConnection s z) = fun s : ℝ => cexp (-(I * z * s)) *
      ∫ y in Ioi s, cexp (I * z * y) * (thetaCuspFullSource y : ℂ) :=
    funext fun s => thetaShiftConnection_eq_tail s z
  rw [hfun]
  refine h.congr_deriv ?_
  rw [thetaShiftConnection_eq_tail]
  have : cexp (-(I * z * s)) * cexp (I * z * s) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  linear_combination (-(thetaCuspFullSource s : ℂ)) * this

/-- **(9).** On the real axis the source equation is a forced rotation of `h_s(u) = P + iI`:
`∂_s P = -k(s) + u I`. -/
theorem hasDerivAt_re_thetaShiftConnection (u s : ℝ) :
    HasDerivAt (fun s => (thetaShiftConnection s u).re)
      (-thetaCuspFullSource s + u * (thetaShiftConnection s u).im) s := by
  have h := reCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_thetaShiftConnection u s)
  refine h.congr_deriv ?_
  simp only [reCLM_apply, sub_re, neg_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul,
    one_mul, sub_zero, mul_im, zero_sub]
  ring

/-- **(9).** `∂_s I = -u P`. -/
theorem hasDerivAt_im_thetaShiftConnection (u s : ℝ) :
    HasDerivAt (fun s => (thetaShiftConnection s u).im)
      (-(u * (thetaShiftConnection s u).re)) s := by
  have h := imCLM.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_thetaShiftConnection u s)
  refine h.congr_deriv ?_
  simp only [imCLM_apply, sub_im, neg_im, ofReal_im, mul_im, mul_re, I_re, I_im, ofReal_re,
    zero_mul, one_mul, sub_zero, zero_sub, neg_zero]
  ring

/-- **(10).** The spectral flow: `∂_s σ_s(t) = -(√t/π) P_s(√t)`, where for `s ≥ 0` the real
part `P_s(√t)` is the principal value `PV ∫₀^∞ σ_s(q)/(q - t) dq`. -/
theorem thetaShiftDensity_flow {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    Tendsto (fun ε => ∫ q in Ioi (0 : ℝ) \ Icc (t - ε) (t + ε), thetaShiftDensity s q / (q - t))
        (𝓝[>] 0) (𝓝 (thetaShiftConnection s (√t : ℝ)).re) ∧
      HasDerivAt (fun s => thetaShiftDensity s t)
        (-(√t / Real.pi) * (thetaShiftConnection s (√t : ℝ)).re) s := by
  constructor
  · have h := (onePortSource_thetaShift hs).tendsto_onePortPrincipalValue (Real.sqrt_pos.mpr ht)
    rw [Real.sq_sqrt ht.le, ← thetaShiftDensity_eq hs] at h
    exact h
  · have h := (hasDerivAt_im_thetaShiftConnection (√t) s).div_const Real.pi
    refine h.congr_deriv ?_
    ring

/-- **(11).** The seam velocity: `∂_s σ_s(u²)|_{s=0} = -(u/(2π)) Ξ(u)` for `u > 0`. -/
theorem hasDerivAt_thetaShiftDensity_seam {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun s => thetaShiftDensity s (u ^ 2)) (-(u / (2 * Real.pi)) * Xi u) 0 := by
  have h := (thetaShiftDensity_flow le_rfl (by positivity : 0 < u ^ 2)).2
  rw [Real.sqrt_sq hu.le, thetaShiftConnection_zero] at h
  refine h.congr_deriv ?_
  rw [Xi_eq_two_mul_re_thetaOneSidedConnection]
  field_simp

end

end RHTower
