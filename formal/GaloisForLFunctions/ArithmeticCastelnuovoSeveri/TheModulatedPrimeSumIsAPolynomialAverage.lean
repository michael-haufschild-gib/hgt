import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ZeroDensityFilteredWeilPositivityAndCoercivity
import GaloisForLFunctions.ArithmeticIncidencePositivity.OnePrimeDilationHasAnExplicitEnergyModulus
import GaloisForLFunctions.RHTower.RiemannKernelStripPlancherel
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointCoercivity

/-!
# The modulated Weil form as an archimedean logarithm minus a polynomial average

For a real test `F₀ ∈ C²_c([−A, A])` and a height `γ`, write
`Q_γ(F₀) = Q(F₀ cos γ·) + Q(F₀ sin γ·)` and `Φ = |F̂₀|²`.  With `e^{2A} ≤ N` and

`D_N(y) = Σ_{n ≤ N} Λ(n) n^{−1/2} cos(y log n)`

the prime part of `Q_γ` is the average of the Dirichlet polynomial against `Φ` (`primeSum_quadrature_eq`):

`primeSum(F₀ cos γ·) + primeSum(F₀ sin γ·) = (1/π) ∫ Φ(t) D_N(γ + t) dt`,

because the autocorrelation of the modulation is `c(x) cos(γx) = (1/2π) ∫ Φ(t) cos(x(t + γ)) dt`
(`autocorr_mul_cos_eq_integral`).

The archimedean part has no shape condition (`archForm_quadrature_ge`):
`archForm(F₀ cos γ·) + archForm(F₀ sin γ·) ≥ (½ log(2 + |γ|) − C) ∫ F₀²`, since `Φ` feeds both `Ω(t + γ)` and
`Ω(t − γ)`, and one of `|t ± γ|` is at least `|γ|`.

So `Q_γ(F₀) ≥ (½ log(2 + |γ|) − C) ∫ F₀² − (1/π) ∫ Φ |D_N(γ + ·)| − O(e^A N(F₀)²/γ⁴)`
(`fullZeroForm_quadrature_ge`), with no information on the zeros.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate Real
open Zeta23 RHTower
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.ArithmeticIncidencePositivity
open RHTower.ArchimedeanAnomaly

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

noncomputable section

/-! ### Fourier tools -/

theorem norm_exp_I_mul_mul (t u : ℝ) : ‖cexp (I * (t : ℂ) * (u : ℂ))‖ = 1 := by
  rw [show I * (t : ℂ) * (u : ℂ) = ((t * u : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- `|F̂₀(t)| ≤ ∫ |F₀|`. -/
theorem norm_paperFT_ofReal_le (F₀ : ℝ → ℝ) (t : ℝ) :
    ‖paperFT (fun u => (F₀ u : ℂ)) t‖ ≤ ∫ u, |F₀ u| := by
  unfold paperFT
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [norm_mul, norm_exp_I_mul_mul, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- `t² |F̂₀(t)| ≤ ∫ |F₀''|`. -/
theorem sq_mul_norm_paperFT_le {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀)
    (t : ℝ) :
    t ^ 2 * ‖paperFT (fun u => (F₀ u : ℂ)) t‖ ≤ ∫ u, |deriv (deriv F₀) u| := by
  set g : ℝ → ℂ := fun u => (F₀ u : ℂ) with hg
  have hgd : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.comp hF₀
  have hgc : HasCompactSupport g := hF₀c.comp_left Complex.ofReal_zero
  have h1 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) F₀ from hF₀)
  have h2 := contDiff_succ_iff_deriv.mp (show ContDiff ℝ (0 + 1) (deriv F₀) from h1.2.2)
  have hg'' : deriv (deriv g) = fun u => ((deriv (deriv F₀) u : ℝ) : ℂ) := by
    have hd1 : deriv g = fun u => ((deriv F₀ u : ℝ) : ℂ) := by
      funext u
      exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (h1.1 u).hasDerivAt).deriv
    rw [hd1]
    funext u
    exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u (h2.1 u).hasDerivAt).deriv
  have hbound := norm_paperFT_ofReal_le (deriv (deriv F₀)) t
  have hid := EvenSector.paperFT_deriv_deriv_of_compact hgd hgc (t : ℂ)
  rw [hg''] at hid
  rw [hid, norm_mul, norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hbound
  exact hbound

/-- The shape norm at scale `R`: `∫ |F₀| + R² ∫ |F₀''|`.  It is scale invariant after normalizing by
`√(R ∫ F₀²)`: for `F₀ = g(·/R)` it equals `R (∫ |g| + ∫ |g''|)`. -/
def shapeNorm (R : ℝ) (F₀ : ℝ → ℝ) : ℝ := (∫ u, |F₀ u|) + R ^ 2 * ∫ u, |deriv (deriv F₀) u|

theorem shapeNorm_nonneg (R : ℝ) (F₀ : ℝ → ℝ) : 0 ≤ shapeNorm R F₀ :=
  add_nonneg (integral_nonneg fun _ => abs_nonneg _)
    (mul_nonneg (sq_nonneg R) (integral_nonneg fun _ => abs_nonneg _))

/-- The envelope bound at scale `R`. -/
theorem one_add_mul_norm_paperFT_le {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) (R t : ℝ) :
    (1 + R ^ 2 * t ^ 2) * ‖paperFT (fun u => (F₀ u : ℂ)) t‖ ≤ shapeNorm R F₀ := by
  have h0 := norm_paperFT_ofReal_le F₀ t
  have h2 := mul_le_mul_of_nonneg_left (sq_mul_norm_paperFT_le hF₀ hF₀c t) (sq_nonneg R)
  unfold shapeNorm
  nlinarith

/-- Squared transforms of continuous compactly supported functions are integrable. -/
theorem integrable_norm_sq_paperFT {h : ℝ → ℂ} (hh : Continuous h) (hhc : HasCompactSupport h) :
    Integrable fun r : ℝ => ‖paperFT h (r : ℂ)‖ ^ 2 := by
  have hh1 : Integrable h := hh.integrable_of_hasCompactSupport hhc
  have hint : Integrable fun u : ℝ => ‖h u‖ ^ 2 :=
    (hh.norm.pow 2).integrable_of_hasCompactSupport
      ((hhc.norm).comp_left (zero_pow two_ne_zero))
  have hh2 : MemLp h 2 := (memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mpr hint
  have hfun : (fun x : ℝ => ‖paperFT h (x : ℂ)‖ ^ 2) =
      fun x => (fun ξ : ℝ => ‖FourierTransform.fourier h ξ‖ ^ 2) (x / (-(2 * Real.pi))) := by
    funext x
    rw [paperFT_ofReal_eq_fourier, neg_div, ← div_neg]
  rw [hfun]
  exact (GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hh1 hh2).comp_div
    (by linarith [Real.pi_pos])

theorem integral_norm_sq_paperFT_cc {h : ℝ → ℂ} (hh : Continuous h) (hhc : HasCompactSupport h) :
    ∫ r : ℝ, ‖paperFT h (r : ℂ)‖ ^ 2 = 2 * π * ∫ u, ‖h u‖ ^ 2 := by
  have hh1 : Integrable h := hh.integrable_of_hasCompactSupport hhc
  have hint : Integrable fun u : ℝ => ‖h u‖ ^ 2 :=
    (hh.norm.pow 2).integrable_of_hasCompactSupport
      ((hhc.norm).comp_left (zero_pow two_ne_zero))
  exact KernelStrip.integral_norm_sq_paperFT_of_memLp hh1
    ((memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mpr hint)

theorem paperFT_add_cc {a b : ℝ → ℂ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) (z : ℂ) :
    paperFT (fun u => a u + b u) z = paperFT a z + paperFT b z := by
  have hia : Integrable fun u : ℝ => a u * cexp (I * z * (u : ℂ)) :=
    (ha.mul (by fun_prop)).integrable_of_hasCompactSupport hac.mul_right
  have hib : Integrable fun u : ℝ => b u * cexp (I * z * (u : ℂ)) :=
    (hb.mul (by fun_prop)).integrable_of_hasCompactSupport hbc.mul_right
  unfold paperFT
  rw [← integral_add hia hib]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  ring

theorem paperFT_sub_cc {a b : ℝ → ℂ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) (z : ℂ) :
    paperFT (fun u => a u - b u) z = paperFT a z - paperFT b z := by
  have hia : Integrable fun u : ℝ => a u * cexp (I * z * (u : ℂ)) :=
    (ha.mul (by fun_prop)).integrable_of_hasCompactSupport hac.mul_right
  have hib : Integrable fun u : ℝ => b u * cexp (I * z * (u : ℂ)) :=
    (hb.mul (by fun_prop)).integrable_of_hasCompactSupport hbc.mul_right
  unfold paperFT
  rw [← integral_sub hia hib]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  ring

/-- **Parseval, real part.** -/
theorem integral_re_paperFT_mul_conj {a b : ℝ → ℂ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) :
    ∫ r : ℝ, (paperFT a (r : ℂ) * conj (paperFT b (r : ℂ))).re =
      2 * π * ∫ u, (a u * conj (b u)).re := by
  have hp : Continuous fun u => a u + b u := ha.add hb
  have hm : Continuous fun u => a u - b u := ha.sub hb
  have hpc : HasCompactSupport fun u => a u + b u := hac.add hbc
  have hmc : HasCompactSupport fun u => a u - b u := hac.sub hbc
  have hLp : Integrable fun u : ℝ => ‖a u + b u‖ ^ 2 :=
    (hp.norm.pow 2).integrable_of_hasCompactSupport
      ((hpc.norm).comp_left (zero_pow two_ne_zero))
  have hLm : Integrable fun u : ℝ => ‖a u - b u‖ ^ 2 :=
    (hm.norm.pow 2).integrable_of_hasCompactSupport
      ((hmc.norm).comp_left (zero_pow two_ne_zero))
  have hPp := integrable_norm_sq_paperFT hp hpc
  have hPm := integrable_norm_sq_paperFT hm hmc
  have hspec : ∫ r : ℝ, (paperFT a (r : ℂ) * conj (paperFT b (r : ℂ))).re
      = (∫ r : ℝ, ‖paperFT (fun u => a u + b u) (r : ℂ)‖ ^ 2) / 4
        - (∫ r : ℝ, ‖paperFT (fun u => a u - b u) (r : ℂ)‖ ^ 2) / 4 := by
    have hsub := integral_sub (hPp.div_const 4) (hPm.div_const 4)
    rw [integral_div, integral_div] at hsub
    rw [← hsub]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    change (paperFT a (r : ℂ) * conj (paperFT b (r : ℂ))).re = _
    rw [paperFT_add_cc ha hac hb hbc, paperFT_sub_cc ha hac hb hbc]
    exact re_mul_conj_polarization _ _
  have hphys : ∫ u, (a u * conj (b u)).re
      = (∫ u, ‖a u + b u‖ ^ 2) / 4 - (∫ u, ‖a u - b u‖ ^ 2) / 4 := by
    have hsub := integral_sub (hLp.div_const 4) (hLm.div_const 4)
    rw [integral_div, integral_div] at hsub
    rw [← hsub]
    exact integral_congr_ae (Eventually.of_forall fun u => re_mul_conj_polarization _ _)
  rw [hspec, hphys, integral_norm_sq_paperFT_cc hp hpc, integral_norm_sq_paperFT_cc hm hmc]
  ring

/-! ### The autocorrelation of a modulation -/

/-- `c(x) cos(γx) = (1/2π) ∫ Φ(t) cos(x(t + γ)) dt`. -/
theorem autocorr_mul_cos_eq_integral {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) (γ x : ℝ) :
    autocorr F₀ x * Real.cos (γ * x) =
      1 / (2 * π) * ∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * Real.cos (x * (t + γ)) := by
  set G : ℝ → ℂ := complexModulatedSource F₀ γ with hG
  have hGc : Continuous G := by
    rw [hG]
    unfold complexModulatedSource
    fun_prop
  have hGs : HasCompactSupport G := hasCompactSupport_complexModulatedSource hF₀c γ
  set b : ℝ → ℂ := fun u => G (u + x) with hb
  have hbc : Continuous b := hGc.comp (continuous_id.add continuous_const)
  have hbs : HasCompactSupport b := by
    have := hGs.comp_homeomorph (Homeomorph.addRight x)
    exact this
  have hParseval := integral_re_paperFT_mul_conj hGc hGs hbc hbs
  -- the physical side
  have hphys : ∫ u, (G u * conj (b u)).re = autocorr F₀ x * Real.cos (γ * x) := by
    unfold autocorr
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hb, hG, complexModulatedSource, map_mul, Complex.conj_ofReal]
    have hexp : cexp (-I * (γ : ℂ) * (u : ℂ)) * conj (cexp (-I * (γ : ℂ) * ((u + x : ℝ) : ℂ)))
        = cexp (((γ * x : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      ring
    have hgroup : (F₀ u : ℂ) * cexp (-I * (γ : ℂ) * (u : ℂ)) *
        (((F₀ (u + x) : ℝ) : ℂ) * conj (cexp (-I * (γ : ℂ) * ((u + x : ℝ) : ℂ))))
        = ((F₀ u * F₀ (u + x) : ℝ) : ℂ) * cexp (((γ * x : ℝ) : ℂ) * I) := by
      rw [← hexp]
      push_cast
      ring
    rw [hgroup, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  -- the transform of the shifted function
  have hshift : ∀ r : ℝ, paperFT b (r : ℂ) = cexp (-(I * (r : ℂ) * (x : ℂ))) * paperFT G (r : ℂ) := by
    intro r
    unfold paperFT
    rw [← integral_const_mul,
      ← integral_add_right_eq_self (fun v : ℝ =>
        cexp (-(I * (r : ℂ) * (x : ℂ))) * (G v * cexp (I * (r : ℂ) * (v : ℂ)))) x]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hb]
    rw [mul_left_comm, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  -- the spectral side
  have hspec : ∀ r : ℝ, (paperFT G (r : ℂ) * conj (paperFT b (r : ℂ))).re =
      ‖paperFT (fun u => (F₀ u : ℂ)) ((r - γ : ℝ) : ℂ)‖ ^ 2 * Real.cos (x * ((r - γ) + γ)) := by
    intro r
    have hG' : paperFT G (r : ℂ) = paperFT (fun u => (F₀ u : ℂ)) ((r - γ : ℝ) : ℂ) := by
      rw [hG, paperFT_complexModulatedSource]
      push_cast
      rfl
    rw [hshift r, hG']
    set z := paperFT (fun u => (F₀ u : ℂ)) ((r - γ : ℝ) : ℂ)
    have hmul : z * conj (cexp (-(I * (r : ℂ) * (x : ℂ))) * z)
        = ((‖z‖ ^ 2 : ℝ) : ℂ) * cexp (((x * r : ℝ) : ℂ) * I) := by
      rw [map_mul, ← Complex.exp_conj, mul_left_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq,
        mul_comm]
      congr 2
      simp only [map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast
      ring
    rw [hmul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, sub_add_cancel]
  have htrans : ∫ r : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) ((r - γ : ℝ) : ℂ)‖ ^ 2 *
        Real.cos (x * ((r - γ) + γ))
      = ∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * Real.cos (x * (t + γ)) :=
    integral_sub_right_eq_self
      (fun t : ℝ => ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * Real.cos (x * (t + γ))) γ
  rw [integral_congr_ae (Eventually.of_forall hspec), htrans, hphys] at hParseval
  rw [hParseval]
  field_simp

end

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
