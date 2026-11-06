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

theorem integrable_norm_sq_cc {h : ℝ → ℂ} (hh : Continuous h) (hhc : HasCompactSupport h) :
    Integrable fun u : ℝ => ‖h u‖ ^ 2 :=
  (hh.norm.pow 2).integrable_of_hasCompactSupport ((hhc.norm).comp_left (zero_pow two_ne_zero))

/-- Polarization under an integral. -/
theorem integral_re_mul_conj_eq {f g : ℝ → ℂ} (hP : Integrable fun x => ‖f x + g x‖ ^ 2)
    (hM : Integrable fun x => ‖f x - g x‖ ^ 2) :
    ∫ x, (f x * conj (g x)).re = (∫ x, ‖f x + g x‖ ^ 2) / 4 - (∫ x, ‖f x - g x‖ ^ 2) / 4 := by
  have hsub := integral_sub (hP.div_const 4) (hM.div_const 4)
  have e1 : ∫ x, ‖f x + g x‖ ^ 2 / 4 = (∫ x, ‖f x + g x‖ ^ 2) / 4 := integral_div _ _
  have e2 : ∫ x, ‖f x - g x‖ ^ 2 / 4 = (∫ x, ‖f x - g x‖ ^ 2) / 4 := integral_div _ _
  rw [← e1, ← e2, ← hsub]
  exact integral_congr_ae (Eventually.of_forall fun x => re_mul_conj_polarization _ _)

/-- **Parseval, real part.** -/
theorem integral_re_paperFT_mul_conj {a b : ℝ → ℂ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hb : Continuous b) (hbc : HasCompactSupport b) :
    ∫ r : ℝ, (paperFT a (r : ℂ) * conj (paperFT b (r : ℂ))).re =
      2 * π * ∫ u, (a u * conj (b u)).re := by
  have hp : Continuous fun u => a u + b u := ha.add hb
  have hm : Continuous fun u => a u - b u := ha.sub hb
  have hpc : HasCompactSupport fun u => a u + b u := hac.add hbc
  have hmc : HasCompactSupport fun u => a u - b u := hac.sub hbc
  have eP : ∀ r : ℝ, paperFT a (r : ℂ) + paperFT b (r : ℂ) = paperFT (fun u => a u + b u) (r : ℂ) :=
    fun r => (paperFT_add_cc ha hac hb hbc _).symm
  have eM : ∀ r : ℝ, paperFT a (r : ℂ) - paperFT b (r : ℂ) = paperFT (fun u => a u - b u) (r : ℂ) :=
    fun r => (paperFT_sub_cc ha hac hb hbc _).symm
  have hPp : Integrable fun r : ℝ => ‖paperFT a (r : ℂ) + paperFT b (r : ℂ)‖ ^ 2 := by
    simp only [eP]
    exact integrable_norm_sq_paperFT hp hpc
  have hPm : Integrable fun r : ℝ => ‖paperFT a (r : ℂ) - paperFT b (r : ℂ)‖ ^ 2 := by
    simp only [eM]
    exact integrable_norm_sq_paperFT hm hmc
  have hspec := integral_re_mul_conj_eq hPp hPm
  have hphys := integral_re_mul_conj_eq (integrable_norm_sq_cc hp hpc) (integrable_norm_sq_cc hm hmc)
  have ePl : ∫ r : ℝ, ‖paperFT a (r : ℂ) + paperFT b (r : ℂ)‖ ^ 2 = 2 * π * ∫ u, ‖a u + b u‖ ^ 2 := by
    simp only [eP]
    exact integral_norm_sq_paperFT_cc hp hpc
  have eMi : ∫ r : ℝ, ‖paperFT a (r : ℂ) - paperFT b (r : ℂ)‖ ^ 2 = 2 * π * ∫ u, ‖a u - b u‖ ^ 2 := by
    simp only [eM]
    exact integral_norm_sq_paperFT_cc hm hmc
  rw [hspec, hphys, ePl, eMi]
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

/-! ### The prime sum as a polynomial average -/

/-- The Dirichlet polynomial `D_N(y) = Σ_{k<N} Λ(k+1) (k+1)^{−1/2} cos(y log(k+1))`. -/
def primeCosine (N : ℕ) (y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, vonMangoldtAtom (k + 1) * Real.cos (y * Real.log ((k + 1 : ℕ) : ℝ))

theorem sum_Icc_one_eq_sum_range (f : ℕ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ k ∈ Finset.range N, f (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- A shifted product vanishes once the shift exceeds twice the aperture. -/
theorem integral_mul_shift_eq_zero {g : ℝ → ℝ} {A x : ℝ} (hsupp : ∀ u : ℝ, A < |u| → g u = 0)
    (hx : 2 * A < |x|) : ∫ t, g t * g (t + x) = 0 := by
  have hzero : (fun t => g t * g (t + x)) = fun _ => 0 := by
    funext t
    by_cases ht : A < |t|
    · rw [hsupp t ht, zero_mul]
    · have hgt : A < |t + x| := by
        have htri : |x| ≤ |t + x| + |t| := by
          have h := abs_sub (t + x) t
          rwa [add_sub_cancel_left] at h
        linarith only [not_lt.mp ht, htri, hx]
      rw [hsupp _ hgt, mul_zero]
  rw [hzero, integral_zero]

/-- `primeSum` of a test of aperture `A` is a finite sum as soon as `e^{2A} ≤ N`. -/
theorem primeSum_eq_sum_range {g : ℝ → ℝ} {A : ℝ} (hsupp : ∀ u : ℝ, A < |u| → g u = 0) {N : ℕ}
    (hN : Real.exp (2 * A) ≤ N) :
    primeSum g = ∑ k ∈ Finset.range N, vonMangoldtAtom (k + 1) *
      (autocorr g (-Real.log ((k + 1 : ℕ) : ℝ)) + autocorr g (Real.log ((k + 1 : ℕ) : ℝ))) := by
  rw [← sum_Icc_one_eq_sum_range (fun n => vonMangoldtAtom n *
      (autocorr g (-Real.log (n : ℝ)) + autocorr g (Real.log (n : ℝ)))) N]
  unfold primeSum
  rw [tsum_eq_sum (s := Finset.Icc 1 N)]
  · refine Finset.sum_congr rfl fun n _ => ?_
    congr 2
  · intro n hn
    rw [Finset.mem_Icc, not_and_or] at hn
    rcases n.eq_zero_or_pos with rfl | hpos
    · simp [vonMangoldtAtom]
    have hgt : N < n := by
      rcases hn with h | h <;> omega
    have hNpos : 0 < N := by
      by_contra h0
      have hN0 : N = 0 := by omega
      rw [hN0] at hN
      have := Real.exp_pos (2 * A)
      simp at hN
      linarith
    have hlog : 2 * A < Real.log n := by
      have hle : (2 * A) ≤ Real.log N := by
        rw [Real.le_log_iff_exp_le (by exact_mod_cast hNpos)]
        exact hN
      have hlt : Real.log N < Real.log n :=
        Real.log_lt_log (by exact_mod_cast hNpos) (by exact_mod_cast hgt)
      linarith
    have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
    have h1 : ∫ t, g t * g (t + Real.log n) = 0 :=
      integral_mul_shift_eq_zero hsupp (by rwa [abs_of_nonneg hlog0])
    have h2 : ∫ t, g t * g (t - Real.log n) = 0 := by
      have h := integral_mul_shift_eq_zero (x := -Real.log n) hsupp
        (by rwa [abs_neg, abs_of_nonneg hlog0])
      simpa only [sub_eq_add_neg] using h
    rw [h1, h2, add_zero, mul_zero]

/-- **The prime sum as an average.**  The quadrature prime sum is the average of `D_N` against `Φ`. -/
theorem primeSum_quadrature_eq {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀) (hF₀c : HasCompactSupport F₀)
    {A : ℝ} (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0) (γ : ℝ) {N : ℕ} (hN : Real.exp (2 * A) ≤ N) :
    primeSum (cosineSource F₀ γ) + primeSum (sineSource F₀ γ) =
      1 / π * ∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * primeCosine N (γ + t) := by
  have hsc : ∀ u : ℝ, A < |u| → cosineSource F₀ γ u = 0 := fun u hu => by
    simp [cosineSource, hsupp u hu]
  have hss : ∀ u : ℝ, A < |u| → sineSource F₀ γ u = 0 := fun u hu => by
    simp [sineSource, hsupp u hu]
  rw [primeSum_eq_sum_range hsc hN, primeSum_eq_sum_range hss hN, ← Finset.sum_add_distrib]
  have hΦ : Integrable fun t : ℝ => ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 :=
    integrable_norm_sq_paperFT (Complex.continuous_ofReal.comp hF₀)
      (hF₀c.comp_left Complex.ofReal_zero)
  have hterm : ∀ x : ℝ, Integrable fun t : ℝ =>
      ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * Real.cos (x * (t + γ)) := fun x =>
    hΦ.mul_bdd (c := 1) (by fun_prop)
      (Eventually.of_forall fun t => by simpa using Real.abs_cos_le_one _)
  have hsum : ∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * primeCosine N (γ + t)
      = ∑ k ∈ Finset.range N, vonMangoldtAtom (k + 1) *
          ∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 *
            Real.cos (Real.log ((k + 1 : ℕ) : ℝ) * (t + γ)) := by
    have hswap := integral_finsetSum (μ := volume) (Finset.range N)
      (f := fun k (t : ℝ) => vonMangoldtAtom (k + 1) *
        (‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 *
          Real.cos (Real.log ((k + 1 : ℕ) : ℝ) * (t + γ))))
      (fun k _ => (hterm _).const_mul _)
    have hconst : ∀ k, ∫ t : ℝ, vonMangoldtAtom (k + 1) *
        (‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 *
          Real.cos (Real.log ((k + 1 : ℕ) : ℝ) * (t + γ)))
        = vonMangoldtAtom (k + 1) * ∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 *
          Real.cos (Real.log ((k + 1 : ℕ) : ℝ) * (t + γ)) := fun k => integral_const_mul _ _
    simp only [hconst] at hswap
    rw [← hswap]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [primeCosine, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_comm (γ + t), add_comm γ t]
    ring
  rw [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  set x : ℝ := Real.log ((k + 1 : ℕ) : ℝ)
  have hplus := autocorr_cosineSource_add_sineSource hF₀ hF₀c γ x
  have hminus := autocorr_cosineSource_add_sineSource hF₀ hF₀c γ (-x)
  have hP := autocorr_mul_cos_eq_integral hF₀ hF₀c γ x
  have hM := autocorr_mul_cos_eq_integral hF₀ hF₀c γ (-x)
  have hMint : ∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * Real.cos (-x * (t + γ))
      = ∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * Real.cos (x * (t + γ)) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [neg_mul, Real.cos_neg]
  rw [hMint] at hM
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hval : autocorr (cosineSource F₀ γ) (-x) + autocorr (cosineSource F₀ γ) x +
      (autocorr (sineSource F₀ γ) (-x) + autocorr (sineSource F₀ γ) x)
      = 1 / π * ∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * Real.cos (x * (t + γ)) := by
    have e : (1 : ℝ) / π = 2 * (1 / (2 * π)) := by field_simp
    rw [e]
    linear_combination hplus + hminus + hP + hM
  rw [← mul_add, hval]
  ring

/-! ### The archimedean part -/

/-- `paperFT` two-shift law for the sine modulation. -/
theorem paperFT_sineSource {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀) (hF₀c : HasCompactSupport F₀)
    (γ : ℝ) (z : ℂ) :
    paperFT (fun u => (sineSource F₀ γ u : ℂ)) z =
      (paperFT (fun u => (F₀ u : ℂ)) (z + (γ : ℂ)) -
        paperFT (fun u => (F₀ u : ℂ)) (z - (γ : ℂ))) / (2 * I) := by
  have hi1 : Integrable fun u : ℝ =>
      (F₀ u : ℂ) * cexp (I * (z + (γ : ℂ)) * (u : ℂ)) :=
    ((Complex.continuous_ofReal.comp hF₀).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hF₀c.comp_left Complex.ofReal_zero).mul_right)
  have hi2 : Integrable fun u : ℝ =>
      (F₀ u : ℂ) * cexp (I * (z - (γ : ℂ)) * (u : ℂ)) :=
    ((Complex.continuous_ofReal.comp hF₀).mul (by fun_prop)).integrable_of_hasCompactSupport
      ((hF₀c.comp_left Complex.ofReal_zero).mul_right)
  unfold paperFT sineSource
  rw [← integral_sub hi1 hi2, ← integral_div]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  rw [Complex.ofReal_mul, Complex.ofReal_sin, Complex.sin]
  have h1 : I * z * (u : ℂ) + ((γ * u : ℝ) : ℂ) * I = I * (z + (γ : ℂ)) * (u : ℂ) := by
    push_cast
    ring
  have h2 : I * z * (u : ℂ) + (-((γ * u : ℝ) : ℂ) * I) = I * (z - (γ : ℂ)) * (u : ℂ) := by
    push_cast
    ring
  rw [← h1, ← h2, Complex.exp_add, Complex.exp_add]
  have hI : I * I = -1 := Complex.I_mul_I
  have h2I : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  generalize cexp (-((γ * u : ℝ) : ℂ) * I) = m
  generalize cexp (((γ * u : ℝ) : ℂ) * I) = p
  generalize cexp (I * z * (u : ℂ)) = E
  generalize (F₀ u : ℂ) = f
  rw [eq_div_iff h2I]
  linear_combination (f * (m - p) * E) * hI

/-- The quadrature spectral density is the average of the two shifted densities. -/
theorem norm_sq_paperFT_quadrature {F₀ : ℝ → ℝ} (hF₀ : Continuous F₀)
    (hF₀c : HasCompactSupport F₀) (γ r : ℝ) :
    ‖paperFT (fun u => (cosineSource F₀ γ u : ℂ)) (r : ℂ)‖ ^ 2 +
        ‖paperFT (fun u => (sineSource F₀ γ u : ℂ)) (r : ℂ)‖ ^ 2 =
      (‖paperFT (fun u => (F₀ u : ℂ)) ((r - γ : ℝ) : ℂ)‖ ^ 2 +
        ‖paperFT (fun u => (F₀ u : ℂ)) ((r + γ : ℝ) : ℂ)‖ ^ 2) / 2 := by
  rw [paperFT_cosineSource hF₀ hF₀c, paperFT_sineSource hF₀ hF₀c,
    show (r : ℂ) - (γ : ℂ) = ((r - γ : ℝ) : ℂ) by push_cast; rfl,
    show (r : ℂ) + (γ : ℂ) = ((r + γ : ℝ) : ℂ) by push_cast; rfl]
  set a := paperFT (fun u => (F₀ u : ℂ)) ((r - γ : ℝ) : ℂ)
  set b := paperFT (fun u => (F₀ u : ℂ)) ((r + γ : ℝ) : ℂ)
  have hnorm : ‖(2 : ℂ) * I‖ = 2 := by simp
  have hswap : ‖b - a‖ = ‖a - b‖ := norm_sub_rev b a
  have hpar := parallelogram_law_with_norm ℝ a b
  rw [norm_div, norm_div, hnorm, hswap, Complex.norm_ofNat]
  nlinarith

/-- **The archimedean lower bound, with no shape condition.** -/
theorem archForm_quadrature_ge {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀) (hF₀c : HasCompactSupport F₀)
    (γ : ℝ) :
    (Real.log (2 + |γ|) / 2 - (10 + Real.log 4)) * ∫ u, F₀ u ^ 2 ≤
      archForm (cosineSource F₀ γ) + archForm (sineSource F₀ γ) := by
  have hC := hF₀.continuous
  set Φ : ℝ → ℝ := fun t => ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 with hΦdef
  have hΦi : Integrable Φ :=
    integrable_norm_sq_paperFT (Complex.continuous_ofReal.comp hC)
      (hF₀c.comp_left Complex.ofReal_zero)
  have hΦ0 : ∀ t, 0 ≤ Φ t := fun t => by positivity
  have hΦcont : Continuous Φ := by
    have hf : Continuous fun t : ℝ => paperFT (fun u => (F₀ u : ℂ)) (t : ℂ) := by
      have hint : Integrable fun u : ℝ => ‖(F₀ u : ℂ)‖ :=
        ((Complex.continuous_ofReal.comp hC).norm).integrable_of_hasCompactSupport
          ((hF₀c.comp_left Complex.ofReal_zero).norm)
      rw [continuous_iff_continuousAt]
      intro x₀
      refine continuousAt_of_dominated (bound := fun u : ℝ => ‖(F₀ u : ℂ)‖)
        (Eventually.of_forall fun x =>
          ((Complex.continuous_ofReal.comp hC).mul (by fun_prop)).aestronglyMeasurable)
        (Eventually.of_forall fun x => Eventually.of_forall fun u => ?_)
        hint (Eventually.of_forall fun u => by fun_prop)
      rw [norm_mul, norm_exp_I_mul_mul, mul_one]
    exact hf.norm.pow 2
  have hPlancherel : ∫ t, Φ t = 2 * π * ∫ u, F₀ u ^ 2 := by
    have hG : Continuous fun u => (F₀ u : ℂ) := Complex.continuous_ofReal.comp hC
    have hGc : HasCompactSupport fun u => (F₀ u : ℂ) := hF₀c.comp_left Complex.ofReal_zero
    have h := integral_norm_sq_paperFT_cc hG hGc
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    exact h
  have hc2 : ContDiff ℝ 2 (cosineSource F₀ γ) := contDiff_cosineSource hF₀ γ
  have hs2 : ContDiff ℝ 2 (sineSource F₀ γ) := contDiff_sineSource hF₀ γ
  have hcc : HasCompactSupport (cosineSource F₀ γ) := hF₀c.mul_right
  have hsc : HasCompactSupport (sineSource F₀ γ) := hF₀c.mul_right
  have hic := RHTower.integrable_normSq_paperFT_mul_gammaBracket hc2 hcc
  have his := RHTower.integrable_normSq_paperFT_mul_gammaBracket hs2 hsc
  set Λ : ℝ := Real.log (2 + |γ|) with hΛ
  have hΛ0 : 0 ≤ Λ := Real.log_nonneg (by linarith only [abs_nonneg γ])
  set ℓ : ℝ → ℝ := fun r => min (Real.log (2 + |r|)) Λ with hℓ
  have hℓcont : Continuous ℓ := by
    refine Continuous.min ?_ continuous_const
    refine Continuous.log (by fun_prop) fun r => ?_
    have := abs_nonneg r
    positivity
  have hℓ0 : ∀ r, 0 ≤ ℓ r := fun r => le_min
    (Real.log_nonneg (by linarith only [abs_nonneg r])) hΛ0
  have hℓle : ∀ r, ℓ r ≤ Λ := fun r => min_le_right _ _
  have hΦℓ : ∀ s : ℝ, Integrable fun t => Φ t * ℓ (t + s) := fun s =>
    hΦi.mul_bdd (c := Λ) (hℓcont.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun t => by
        rw [Real.norm_of_nonneg (hℓ0 _)]
        exact hℓle _)
  -- the two translated densities
  have hshift : ∀ s : ℝ, ∫ r, Φ (r - s) * ℓ r = ∫ t, Φ t * ℓ (t + s) := fun s => by
    have h := integral_sub_right_eq_self (μ := volume) (fun t => Φ t * ℓ (t + s)) s
    simp only [sub_add_cancel] at h
    exact h
  -- pointwise lower bound for the symbol
  have hsym : ∀ r : ℝ,
      (Φ (r - γ) + Φ (r + γ)) / 2 * (ℓ r - (10 + Real.log 4)) ≤
        (‖paperFT (fun u => (cosineSource F₀ γ u : ℂ)) (r : ℂ)‖ ^ 2 * EF.gammaBracket r +
          ‖paperFT (fun u => (sineSource F₀ γ u : ℂ)) (r : ℂ)‖ ^ 2 * EF.gammaBracket r) := by
    intro r
    have hq := norm_sq_paperFT_quadrature hC hF₀c γ r
    have hb := WeilWorkPBAP.joint_gamma_lower_log r
    have hmin : ℓ r ≤ Real.log (2 + |r|) := min_le_left _ _
    have hE : 0 ≤ (Φ (r - γ) + Φ (r + γ)) / 2 := by
      have h1 := hΦ0 (r - γ)
      have h2 := hΦ0 (r + γ)
      positivity
    rw [← add_mul, hq]
    exact mul_le_mul_of_nonneg_left (by linarith only [hb, hmin]) hE
  have hLint : Integrable fun r : ℝ =>
      (Φ (r - γ) + Φ (r + γ)) / 2 * (ℓ r - (10 + Real.log 4)) := by
    have hsh1 : Integrable fun r : ℝ => Φ (r - γ) := hΦi.comp_sub_right γ
    have hsh2 : Integrable fun r : ℝ => Φ (r + γ) := hΦi.comp_add_right γ
    exact ((hsh1.add hsh2).div_const 2).mul_bdd (c := Λ + (10 + Real.log 4))
      (hℓcont.sub continuous_const).aestronglyMeasurable
      (Eventually.of_forall fun r => by
        have h0 := hℓ0 r
        have h1 := hℓle r
        have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> linarith only [h0, h1, hl4, hΛ0])
  have hmono : ∫ r : ℝ, (Φ (r - γ) + Φ (r + γ)) / 2 * (ℓ r - (10 + Real.log 4)) ≤
      ∫ r : ℝ, (‖paperFT (fun u => (cosineSource F₀ γ u : ℂ)) (r : ℂ)‖ ^ 2 * EF.gammaBracket r +
        ‖paperFT (fun u => (sineSource F₀ γ u : ℂ)) (r : ℂ)‖ ^ 2 * EF.gammaBracket r) :=
    integral_mono hLint (hic.add his) hsym
  -- evaluate the lower integral
  have hval : ∫ r : ℝ, (Φ (r - γ) + Φ (r + γ)) / 2 * (ℓ r - (10 + Real.log 4))
      ≥ (Λ / 2 - (10 + Real.log 4)) * ∫ t, Φ t := by
    have hsh1 : Integrable fun r : ℝ => Φ (r - γ) := hΦi.comp_sub_right γ
    have hsh2 : Integrable fun r : ℝ => Φ (r + γ) := hΦi.comp_add_right γ
    have hmeanE : ∫ r : ℝ, (Φ (r - γ) + Φ (r + γ)) / 2 = ∫ t, Φ t := by
      have h1 : ∫ r, Φ (r - γ) = ∫ t, Φ t := integral_sub_right_eq_self Φ γ
      have h2 : ∫ r, Φ (r + γ) = ∫ t, Φ t := integral_add_right_eq_self Φ γ
      have h3 : ∫ r : ℝ, (Φ (r - γ) + Φ (r + γ)) / 2
          = (∫ r, (Φ (r - γ) + Φ (r + γ))) / 2 := integral_div _ _
      rw [h3, integral_add hsh1 hsh2, h1, h2]
      ring
    have hgeo : ∫ r : ℝ, (Φ (r - γ) + Φ (r + γ)) / 2 * ℓ r
        = ((∫ t, Φ t * ℓ (t + γ)) + ∫ t, Φ t * ℓ (t + -γ)) / 2 := by
      have h1 : Integrable fun r : ℝ => Φ (r - γ) * ℓ r := by
        have := (hΦℓ γ).comp_sub_right γ
        simpa only [sub_add_cancel] using this
      have h2 : Integrable fun r : ℝ => Φ (r + γ) * ℓ r := by
        have := (hΦℓ (-γ)).comp_add_right γ
        simpa only [add_neg_cancel_right] using this
      have e : (fun r : ℝ => (Φ (r - γ) + Φ (r + γ)) / 2 * ℓ r)
          = fun r : ℝ => (Φ (r - γ) * ℓ r + Φ (r + γ) * ℓ r) / 2 := by
        funext r
        ring
      have e3 : ∫ r : ℝ, (Φ (r - γ) * ℓ r + Φ (r + γ) * ℓ r) / 2
          = (∫ r, (Φ (r - γ) * ℓ r + Φ (r + γ) * ℓ r)) / 2 := integral_div _ _
      rw [e, e3, integral_add h1 h2, hshift γ]
      have hs2' : ∫ r, Φ (r + γ) * ℓ r = ∫ t, Φ t * ℓ (t + -γ) := by
        have h := hshift (-γ)
        simpa only [sub_neg_eq_add] using h
      rw [hs2']
    have hlogLower : Λ * ∫ t, Φ t ≤ (∫ t, Φ t * ℓ (t + γ)) + ∫ t, Φ t * ℓ (t + -γ) := by
      rw [← integral_add (hΦℓ γ) (hΦℓ (-γ)), ← integral_const_mul]
      refine integral_mono (hΦi.const_mul _) ((hΦℓ γ).add (hΦℓ (-γ))) fun t => ?_
      have hsumge : Λ ≤ ℓ (t + γ) + ℓ (t + -γ) := by
        have hmax : |γ| ≤ |t + γ| ∨ |γ| ≤ |t + -γ| := by
          by_contra hcon
          push Not at hcon
          have htri : 2 * |γ| ≤ |t + γ| + |t + -γ| := by
            have h := abs_sub (t + γ) (t + -γ)
            have e : t + γ - (t + -γ) = 2 * γ := by ring
            rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
            exact h
          linarith only [hcon.1, hcon.2, htri]
        have hfull : ∀ y : ℝ, |γ| ≤ |y| → ℓ y = Λ := fun y hy =>
          min_eq_right (Real.log_le_log (by positivity) (by linarith only [hy]))
        rcases hmax with h | h
        · rw [hfull _ h]
          linarith only [hℓ0 (t + -γ)]
        · rw [hfull _ h]
          linarith only [hℓ0 (t + γ)]
      have hprod := mul_le_mul_of_nonneg_right hsumge (hΦ0 t)
      linarith only [hprod]
    have hsplit : ∫ r : ℝ, (Φ (r - γ) + Φ (r + γ)) / 2 * (ℓ r - (10 + Real.log 4))
        = (∫ r : ℝ, (Φ (r - γ) + Φ (r + γ)) / 2 * ℓ r)
          - (10 + Real.log 4) * ∫ r : ℝ, (Φ (r - γ) + Φ (r + γ)) / 2 := by
      have hA : Integrable fun r : ℝ => (Φ (r - γ) + Φ (r + γ)) / 2 * ℓ r := by
        refine ((hsh1.add hsh2).div_const 2).mul_bdd (c := Λ) hℓcont.aestronglyMeasurable
          (Eventually.of_forall fun r => ?_)
        rw [Real.norm_of_nonneg (hℓ0 _)]
        exact hℓle _
      have hB : Integrable fun r : ℝ => (10 + Real.log 4) * ((Φ (r - γ) + Φ (r + γ)) / 2) :=
        ((hsh1.add hsh2).div_const 2).const_mul _
      rw [← integral_const_mul, ← integral_sub hA hB]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      ring
    rw [hsplit, hmeanE, hgeo]
    nlinarith only [hlogLower]
  -- conclude
  have hsumArch : archForm (cosineSource F₀ γ) + archForm (sineSource F₀ γ) =
      1 / (2 * π) * ∫ r : ℝ,
        (‖paperFT (fun u => (cosineSource F₀ γ u : ℂ)) (r : ℂ)‖ ^ 2 * EF.gammaBracket r +
          ‖paperFT (fun u => (sineSource F₀ γ u : ℂ)) (r : ℂ)‖ ^ 2 * EF.gammaBracket r) := by
    unfold archForm
    rw [← mul_add, integral_add hic his]
  have hπ : 0 < π := Real.pi_pos
  have h2π : 0 < 1 / (2 * π) := by positivity
  rw [hsumArch]
  have hfinal := mul_le_mul_of_nonneg_left (hval.le.trans hmono) h2π.le
  have hcancel : 1 / (2 * π) * ((Λ / 2 - (10 + Real.log 4)) * ∫ t, Φ t)
      = (Λ / 2 - (10 + Real.log 4)) * ∫ u, F₀ u ^ 2 := by
    rw [hPlancherel]
    field_simp
  linarith only [hfinal, hcancel]

/-! ### The pole part -/

theorem expHalfMoment_eq_paperFT (f : ℝ → ℝ) :
    ((expHalfMoment f : ℝ) : ℂ) = paperFT (fun u => (f u : ℂ)) (-(I / 2)) := by
  unfold expHalfMoment paperFT
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  push_cast
  congr 2
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination ((u : ℂ) / 2) * hI

theorem expNegHalfMoment_eq_paperFT (f : ℝ → ℝ) :
    ((expNegHalfMoment f : ℝ) : ℂ) = paperFT (fun u => (f u : ℂ)) (I / 2) := by
  unfold expNegHalfMoment paperFT
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only
  push_cast
  congr 2
  have hI : I * I = -1 := Complex.I_mul_I
  linear_combination (-(u : ℂ) / 2) * hI

/-- The transform of a test at `±γ ± i/2`. -/
theorem norm_paperFT_half_shift_le {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    {z : ℂ} (hz : |z.im| = 1 / 2) {γ : ℝ} (hre : |z.re| = |γ|) :
    ‖paperFT (fun u => (F₀ u : ℂ)) z‖ ≤
      Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + γ ^ 2) := by
  have h := norm_paperFT_symm_le hF₀ hF₀c hA hsupp z
  rw [hz, show A * (1 / 2) = A / 2 by ring, ← sq_abs z.re, hre, sq_abs] at h
  exact h

/-- **The quadrature pole form is negligible at large height.** -/
theorem abs_realPoleForm_quadrature_le {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    (γ : ℝ) :
    |realPoleForm (cosineSource F₀ γ) + realPoleForm (sineSource F₀ γ)| ≤
      4 * (Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + γ ^ 2)) ^ 2 := by
  set B : ℝ := Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + γ ^ 2) with hB
  have hB0 : 0 ≤ B := by
    rw [hB]
    have := envelopeWindowNorm_nonneg F₀
    positivity
  have hC := hF₀.continuous
  have hshift : ∀ (w : ℂ), |w.im| = 1 / 2 → w.re = 0 → ∀ σ : ℝ, |σ| = |γ| →
      ‖paperFT (fun u => (F₀ u : ℂ)) (w + (σ : ℂ))‖ ≤ B := by
    intro w hw hw0 σ hσ
    refine norm_paperFT_half_shift_le hF₀ hF₀c hA hsupp ?_ ?_
    · simpa using hw
    · simpa [hw0] using hσ
  have hcos : ∀ (w : ℂ), |w.im| = 1 / 2 → w.re = 0 →
      ‖paperFT (fun u => (cosineSource F₀ γ u : ℂ)) w‖ ≤ B := by
    intro w hw hw0
    rw [paperFT_cosineSource hC hF₀c, sub_eq_add_neg w (γ : ℂ), ← Complex.ofReal_neg, norm_div,
      Complex.norm_ofNat]
    have h1 := hshift w hw hw0 (-γ) (abs_neg γ)
    have h2 := hshift w hw hw0 γ rfl
    have := norm_add_le (paperFT (fun u => (F₀ u : ℂ)) (w + ((-γ : ℝ) : ℂ)))
      (paperFT (fun u => (F₀ u : ℂ)) (w + (γ : ℂ)))
    linarith only [this, h1, h2]
  have hsin : ∀ (w : ℂ), |w.im| = 1 / 2 → w.re = 0 →
      ‖paperFT (fun u => (sineSource F₀ γ u : ℂ)) w‖ ≤ B := by
    intro w hw hw0
    rw [paperFT_sineSource hC hF₀c, sub_eq_add_neg w (γ : ℂ), ← Complex.ofReal_neg, norm_div]
    have hn : ‖(2 : ℂ) * I‖ = 2 := by simp
    rw [hn]
    have h1 := hshift w hw hw0 (-γ) (abs_neg γ)
    have h2 := hshift w hw hw0 γ rfl
    have := norm_sub_le (paperFT (fun u => (F₀ u : ℂ)) (w + (γ : ℂ)))
      (paperFT (fun u => (F₀ u : ℂ)) (w + ((-γ : ℝ) : ℂ)))
    linarith only [this, h1, h2]
  have him1 : |(I / 2 : ℂ).im| = 1 / 2 := by
    simp [abs_of_pos]
  have hre1 : (I / 2 : ℂ).re = 0 := by simp
  have him2 : |(-(I / 2) : ℂ).im| = 1 / 2 := by
    simp [abs_of_pos]
  have hre2 : (-(I / 2) : ℂ).re = 0 := by simp
  have hbound : ∀ f : ℝ → ℝ, (∀ w : ℂ, |w.im| = 1 / 2 → w.re = 0 →
      ‖paperFT (fun u => (f u : ℂ)) w‖ ≤ B) → |realPoleForm f| ≤ 2 * B ^ 2 := by
    intro f hf
    rw [realPoleForm_eq_expMoments, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h1 : |expHalfMoment f| ≤ B := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real, expHalfMoment_eq_paperFT]
      exact hf _ him2 hre2
    have h2 : |expNegHalfMoment f| ≤ B := by
      rw [← Real.norm_eq_abs, ← Complex.norm_real, expNegHalfMoment_eq_paperFT]
      exact hf _ him1 hre1
    have := mul_le_mul h1 h2 (abs_nonneg _) hB0
    nlinarith only [this]
  have h1 := hbound _ hcos
  have h2 := hbound _ hsin
  calc _ ≤ |realPoleForm (cosineSource F₀ γ)| + |realPoleForm (sineSource F₀ γ)| := abs_add_le _ _
    _ ≤ 4 * B ^ 2 := by linarith only [h1, h2]

/-- **The modulated Weil form against its prime average.**  No information on the zeros is used. -/
theorem fullZeroForm_quadrature_ge {F₀ : ℝ → ℝ} (hF₀ : ContDiff ℝ 2 F₀)
    (hF₀c : HasCompactSupport F₀) {A : ℝ} (hA : 0 ≤ A) (hsupp : ∀ u : ℝ, A < |u| → F₀ u = 0)
    (γ : ℝ) {N : ℕ} (hN : Real.exp (2 * A) ≤ N) :
    (Real.log (2 + |γ|) / 2 - (10 + Real.log 4)) * (∫ u, F₀ u ^ 2)
        - 1 / π * |∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * primeCosine N (γ + t)|
        - 4 * (Real.exp (A / 2) * envelopeWindowNorm F₀ / (1 + γ ^ 2)) ^ 2 ≤
      fullZeroForm (cosineSource F₀ γ) + fullZeroForm (sineSource F₀ γ) := by
  have hc2 : ContDiff ℝ 2 (cosineSource F₀ γ) := contDiff_cosineSource hF₀ γ
  have hs2 : ContDiff ℝ 2 (sineSource F₀ γ) := contDiff_sineSource hF₀ γ
  have hcc : HasCompactSupport (cosineSource F₀ γ) := hF₀c.mul_right
  have hsc : HasCompactSupport (sineSource F₀ γ) := hF₀c.mul_right
  rw [fullZeroForm_eq_arch_prime_pole hc2 hcc, fullZeroForm_eq_arch_prime_pole hs2 hsc]
  have harch := archForm_quadrature_ge hF₀ hF₀c γ
  have hprime := primeSum_quadrature_eq hF₀.continuous hF₀c hsupp γ hN
  have hpole := abs_realPoleForm_quadrature_le hF₀ hF₀c hA hsupp γ
  have hπ : 0 < 1 / π := by positivity [Real.pi_pos]
  have hP := mul_le_mul_of_nonneg_left
    (le_abs_self (∫ t : ℝ, ‖paperFT (fun u => (F₀ u : ℂ)) (t : ℂ)‖ ^ 2 * primeCosine N (γ + t))) hπ.le
  have hneg := (abs_le.mp hpole).1
  linarith only [harch, hprime, hneg, hP]

end

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
