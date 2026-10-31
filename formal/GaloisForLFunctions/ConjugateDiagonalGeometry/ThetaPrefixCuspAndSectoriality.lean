import GaloisForLFunctions.ConjugateDiagonalGeometry.IntegerThetaCollisionFredholmIndex
import GaloisForLFunctions.RHTower.ThetaFiniteShellFourierBoundary
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeWeightedTail
import GaloisForLFunctions.RHTower.PrimeArchThetaWardLaplaceHalfDensity

/-!
# Complex seam-cusp asymptotics, height-freezing, and low-window sectoriality of integer theta prefixes

This module establishes the global zero-locus geometry, seam-cusp asymptotics, operator
height-freezing, and low-window sectorial positivity of `finiteThetaAmplitude N` and its continuous
Haglund–Jacobi shell-addition pencil `finiteThetaShellPencil N θ`:

1. **Haglund–Jacobi shell-addition pencil & quartet symmetries**:
   `finiteThetaShellPencil N θ z = (1 - θ) A_N(z) + θ A_{N+1}(z)` interpolates continuously between
   consecutive integer theta prefixes by adjoining `θ · Φ_{N+2}(|x|)` to the reflected source,
   preserving functional symmetry `z ↔ 1 - z`, Schwarz reflection, strict real-axis positivity for
   `θ ∈ [0, 1]`, finite analytic order, and ballwise zero finiteness.
2. **Complex seam-cusp asymptotic law, global strip zero finiteness, critical-line root, and
   exact operator height-freezing**:
   Three half-line integrations by parts against `thetaFiniteShellJet (N + 1)` expose the uncancelled
   seam cusp `J_{N+1,1}(0) > 0`:
   `(z - 1 / 2)² A_N(z) → 2 J_{N+1,1}(0) > 0` uniformly in vertical strips, with explicit horizon
   `thetaPrefixCuspHorizon N R`. Consequently:
   - every fixed prefix `A_N` has only finitely many zeros in `{|Re z - 1 / 2| ≤ R}`;
   - on the critical line `A_N(1 / 2 + i t) < 0` above `thetaPrefixCuspHorizon N 0`, forcing an
     unconditional critical-line zero `t_*(N) > 3` for every `N : ℕ`;
   - for all `R : ℝ` and all `T₁, T₂ > thetaPrefixCuspHorizon N R`, the height-window zero sets of
     `A_N` in `{|Re z - 1 / 2| ≤ R}` are identical (`finiteThetaAmplitude_strip_zeros_eq_of_gt_cuspHorizon`),
     and whenever `A_N` avoids the finite base side segments up to `thetaPrefixCuspHorizon N 3 + 2`,
     `integerThetaCollisionOperator T₁ n N = integerThetaCollisionOperator T₂ n N` identically.
3. **Direct all-`N`, all-stage sectorial certificate on low windows `T ≤ 3`**:
   Combining the exact Ward–Laplace half-density identity `∫_{x > 0} e^{-x / 2} Φ₁(x) dx =
   (2 π - 1) e^{-π}` with geometric higher-atom domination yields
   `Re A_{N,θ}(z) ≥ (5026 / 16875) e^{-π} > 0` for all `N : ℕ`, `θ ∈ [0, 1]`,
   `|Re z - 1 / 2| ≤ 9 / 8`, and `|Im z| ≤ 61 / 20`, certifying `integerThetaCollisionOperator T n N`
   to have trivial loop `1` and Fredholm index `0` for all `T ≤ 3`, `n : ℕ`, and `N : ℕ`.
-/

set_option autoImplicit false

open Complex MeasureTheory Filter Set Metric intervalIntegral Polynomial
open scoped BigOperators Topology Classical Real

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry

/-! ## §1 Haglund–Jacobi shell-addition pencil, quartet symmetries, and ball zero finiteness -/

/-- Bilateral integral folding onto `(0, ∞)` for any integrable Banach-valued function on `ℝ`. -/
private lemma integral_eq_integral_Ioi_add_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : ℝ → E} (hg : Integrable g) :
    (∫ x : ℝ, g x) = ∫ x in Ioi (0 : ℝ), (g x + g (-x)) := by
  have hsplit := MeasureTheory.integral_add_compl (measurableSet_Ioi (a := (0 : ℝ))) hg
  rw [compl_Ioi] at hsplit
  have hrefl : (∫ x in Iic (0 : ℝ), g x) = ∫ x in Ioi (0 : ℝ), g (-x) := by
    have h := integral_comp_neg_Iic (0 : ℝ) (fun u => g (-u))
    simp only [neg_zero, neg_neg] at h
    exact h
  have hg_pos : IntegrableOn g (Ioi (0 : ℝ)) := hg.integrableOn
  have hg_neg : IntegrableOn (fun x => g (-x)) (Ioi (0 : ℝ)) := (hg.comp_neg).integrableOn
  rw [← hsplit, hrefl, ← MeasureTheory.integral_add hg_pos hg_neg]

/-- Real part of a Bochner integral over any measure. -/
private lemma bochner_integral_re {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := by
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hf]
  rfl

/-- Imaginary part of a Bochner integral over any measure. -/
private lemma bochner_integral_im {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : Integrable f μ) : (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ := by
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hf]
  rfl

/-- Continuous Haglund–Jacobi shell-addition pencil interpolating `finiteThetaAmplitude N` (`θ = 0`)
and `finiteThetaAmplitude (N + 1)` (`θ = 1`). -/
def finiteThetaShellPencil (N : ℕ) (θ : ℝ) (z : ℂ) : ℂ :=
  ((1 - θ : ℝ) : ℂ) * _root_.RHTower.finiteThetaAmplitude N z +
    (θ : ℂ) * _root_.RHTower.finiteThetaAmplitude (N + 1) z

/-- Associated first-moment pencil satisfying `deriv (finiteThetaShellPencil N θ) = -M_{N,θ}`. -/
def finiteThetaPencilFirstMoment (N : ℕ) (θ : ℝ) (z : ℂ) : ℂ :=
  ((1 - θ : ℝ) : ℂ) * _root_.RHTower.finiteThetaFirstMoment N z +
    (θ : ℂ) * _root_.RHTower.finiteThetaFirstMoment (N + 1) z

/-- Reflected source kernel `∑_{m=1}^{N+1} Φ_m(|x|) + θ Φ_{N+2}(|x|)` of the `(N, θ)` shell pencil. -/
def reflectedFiniteThetaShellPencil (N : ℕ) (θ : ℝ) (x : ℝ) : ℝ :=
  _root_.RHTower.reflectedFiniteThetaSource (N + 1) x +
    θ * _root_.RHTower.thetaCuspSourceTerm |x| (N + 2)

theorem reflectedFiniteThetaShellPencil_eq_affine (N : ℕ) (θ x : ℝ) :
    reflectedFiniteThetaShellPencil N θ x =
      (1 - θ) * _root_.RHTower.reflectedFiniteThetaSource (N + 1) x +
        θ * _root_.RHTower.reflectedFiniteThetaSource (N + 2) x := by
  unfold reflectedFiniteThetaShellPencil _root_.RHTower.reflectedFiniteThetaSource
    _root_.RHTower.thetaCuspFiniteShellPrefix
  rw [Finset.sum_range_succ _ (N + 2)]
  ring

/-- Integral representation of `finiteThetaShellPencil` against `reflectedFiniteThetaShellPencil`. -/
theorem finiteThetaShellPencil_eq_integral (N : ℕ) (θ : ℝ) (z : ℂ) :
    finiteThetaShellPencil N θ z =
      ∫ x : ℝ, (reflectedFiniteThetaShellPencil N θ x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)) := by
  have hN : Integrable (fun x : ℝ => (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
      Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    simpa only [_root_.RHTower.finiteThetaTiltSource] using
      _root_.RHTower.integrable_bilateralLaplace
        (_root_.RHTower.finiteThetaTiltSource N) ((1 / 2 : ℂ) - z)
  have hN1 : Integrable (fun x : ℝ => (_root_.RHTower.reflectedFiniteThetaSource (N + 2) x : ℂ) *
      Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    simpa only [_root_.RHTower.finiteThetaTiltSource] using
      _root_.RHTower.integrable_bilateralLaplace
        (_root_.RHTower.finiteThetaTiltSource (N + 1)) ((1 / 2 : ℂ) - z)
  have hrew : (fun x : ℝ => (reflectedFiniteThetaShellPencil N θ x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) =
      fun x : ℝ =>
        ((1 - θ : ℝ) : ℂ) * ((_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) +
        (θ : ℂ) * ((_root_.RHTower.reflectedFiniteThetaSource (N + 2) x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    funext x
    rw [reflectedFiniteThetaShellPencil_eq_affine]
    push_cast
    ring
  rw [hrew, MeasureTheory.integral_add (hN.const_mul _) (hN1.const_mul _),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rfl

@[simp]
theorem finiteThetaShellPencil_zero (N : ℕ) (z : ℂ) :
    finiteThetaShellPencil N 0 z = _root_.RHTower.finiteThetaAmplitude N z := by
  simp [finiteThetaShellPencil]

@[simp]
theorem finiteThetaShellPencil_one (N : ℕ) (z : ℂ) :
    finiteThetaShellPencil N 1 z = _root_.RHTower.finiteThetaAmplitude (N + 1) z := by
  simp [finiteThetaShellPencil]

@[simp]
theorem finiteThetaPencilFirstMoment_zero (N : ℕ) (z : ℂ) :
    finiteThetaPencilFirstMoment N 0 z = _root_.RHTower.finiteThetaFirstMoment N z := by
  simp [finiteThetaPencilFirstMoment]

@[simp]
theorem finiteThetaPencilFirstMoment_one (N : ℕ) (z : ℂ) :
    finiteThetaPencilFirstMoment N 1 z = _root_.RHTower.finiteThetaFirstMoment (N + 1) z := by
  simp [finiteThetaPencilFirstMoment]

theorem hasDerivAt_finiteThetaShellPencil (N : ℕ) (θ : ℝ) (z : ℂ) :
    HasDerivAt (finiteThetaShellPencil N θ) (-finiteThetaPencilFirstMoment N θ z) z := by
  have h1 := (_root_.RHTower.hasDerivAt_finiteThetaAmplitude N z).const_mul ((1 - θ : ℝ) : ℂ)
  have h2 := (_root_.RHTower.hasDerivAt_finiteThetaAmplitude (N + 1) z).const_mul (θ : ℂ)
  refine (h1.add h2).congr_deriv ?_
  unfold finiteThetaPencilFirstMoment
  ring

theorem differentiable_finiteThetaShellPencil (N : ℕ) (θ : ℝ) :
    Differentiable ℂ (finiteThetaShellPencil N θ) :=
  fun z => (hasDerivAt_finiteThetaShellPencil N θ z).differentiableAt

theorem deriv_finiteThetaShellPencil (N : ℕ) (θ : ℝ) (z : ℂ) :
    deriv (finiteThetaShellPencil N θ) z = -finiteThetaPencilFirstMoment N θ z :=
  (hasDerivAt_finiteThetaShellPencil N θ z).deriv

theorem analyticOnNhd_finiteThetaAmplitude (N : ℕ) :
    AnalyticOnNhd ℂ (_root_.RHTower.finiteThetaAmplitude N) Set.univ :=
  (_root_.RHTower.differentiable_finiteThetaAmplitude N).differentiableOn.analyticOnNhd isOpen_univ

theorem analyticOnNhd_finiteThetaShellPencil (N : ℕ) (θ : ℝ) :
    AnalyticOnNhd ℂ (finiteThetaShellPencil N θ) Set.univ :=
  (differentiable_finiteThetaShellPencil N θ).differentiableOn.analyticOnNhd isOpen_univ

theorem continuous_finiteThetaShellPencil_uncurry (N : ℕ) :
    Continuous (fun p : ℝ × ℂ => finiteThetaShellPencil N p.1 p.2) := by
  unfold finiteThetaShellPencil
  exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)).mul
    ((_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous.comp continuous_snd)).add
    ((Complex.continuous_ofReal.comp continuous_fst).mul
      ((_root_.RHTower.differentiable_finiteThetaAmplitude (N + 1)).continuous.comp continuous_snd))

theorem continuous_neg_finiteThetaPencilFirstMoment_uncurry (N : ℕ) :
    Continuous (fun p : ℝ × ℂ => -finiteThetaPencilFirstMoment N p.1 p.2) := by
  have hc : ∀ k : ℕ, Continuous (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment k z) := by
    intro k
    have heq : (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment k z) =
        deriv (_root_.RHTower.finiteThetaAmplitude k) :=
      funext fun z => (_root_.RHTower.deriv_finiteThetaAmplitude k z).symm
    rw [heq]
    exact continuousOn_univ.mp
      (((_root_.RHTower.differentiable_finiteThetaAmplitude k).differentiableOn.deriv
        isOpen_univ).continuousOn)
  have hrew : (fun p : ℝ × ℂ => -finiteThetaPencilFirstMoment N p.1 p.2) =
      fun p : ℝ × ℂ =>
        ((1 - p.1 : ℝ) : ℂ) * (-_root_.RHTower.finiteThetaFirstMoment N p.2) +
          (p.1 : ℂ) * (-_root_.RHTower.finiteThetaFirstMoment (N + 1) p.2) := by
    funext p
    unfold finiteThetaPencilFirstMoment
    ring
  rw [hrew]
  exact ((Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)).mul
    ((hc N).comp continuous_snd)).add
    ((Complex.continuous_ofReal.comp continuous_fst).mul
      ((hc (N + 1)).comp continuous_snd))

/-- Functional symmetry `A_N(1 - z) = A_N(z)`. -/
theorem finiteThetaAmplitude_one_sub (N : ℕ) (z : ℂ) :
    _root_.RHTower.finiteThetaAmplitude N (1 - z) = _root_.RHTower.finiteThetaAmplitude N z := by
  rw [_root_.RHTower.finiteThetaAmplitude_eq_bilateral,
    _root_.RHTower.finiteThetaAmplitude_eq_bilateral]
  have hw : (1 / 2 : ℂ) - (1 - z) = -((1 / 2 : ℂ) - z) := by ring
  rw [hw, _root_.RHTower.bilateralLaplace_neg]

/-- Schwarz reflection `conj (A_N (conj z)) = A_N z`. -/
theorem finiteThetaAmplitude_conj (N : ℕ) (z : ℂ) :
    star (_root_.RHTower.finiteThetaAmplitude N (star z)) =
      _root_.RHTower.finiteThetaAmplitude N z := by
  rw [_root_.RHTower.finiteThetaAmplitude_eq_bilateral,
    _root_.RHTower.finiteThetaAmplitude_eq_bilateral]
  change (starRingEnd ℂ) (_root_.RHTower.bilateralLaplace (_root_.RHTower.finiteThetaTiltSource N)
    ((1 / 2 : ℂ) - (starRingEnd ℂ) z)) = _
  have hw : (1 / 2 : ℂ) - (starRingEnd ℂ) z = (starRingEnd ℂ) ((1 / 2 : ℂ) - z) := by
    simp [map_sub, map_ofNat]
  rw [hw, _root_.RHTower.bilateralLaplace_conj, RingHomCompTriple.comp_apply, RingHom.id_apply]

theorem finiteThetaShellPencil_one_sub (N : ℕ) (θ : ℝ) (z : ℂ) :
    finiteThetaShellPencil N θ (1 - z) = finiteThetaShellPencil N θ z := by
  simp only [finiteThetaShellPencil, finiteThetaAmplitude_one_sub]

theorem finiteThetaShellPencil_conj (N : ℕ) (θ : ℝ) (z : ℂ) :
    star (finiteThetaShellPencil N θ (star z)) = finiteThetaShellPencil N θ z := by
  have h0 : (starRingEnd ℂ) (_root_.RHTower.finiteThetaAmplitude N ((starRingEnd ℂ) z)) =
      _root_.RHTower.finiteThetaAmplitude N z := finiteThetaAmplitude_conj N z
  have h1 : (starRingEnd ℂ) (_root_.RHTower.finiteThetaAmplitude (N + 1) ((starRingEnd ℂ) z)) =
      _root_.RHTower.finiteThetaAmplitude (N + 1) z := finiteThetaAmplitude_conj (N + 1) z
  change (starRingEnd ℂ) (finiteThetaShellPencil N θ ((starRingEnd ℂ) z)) = _
  unfold finiteThetaShellPencil
  simp only [map_add, map_mul, Complex.conj_ofReal]
  rw [h0, h1]

/-- Every `finiteThetaShellPencil N θ` is real-valued on the critical line `Re z = 1 / 2`. -/
theorem finiteThetaShellPencil_criticalLine_im_eq_zero (N : ℕ) (θ t : ℝ) :
    (finiteThetaShellPencil N θ ((1 / 2 : ℂ) + (t : ℂ) * I)).im = 0 := by
  set z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have h1z : 1 - star z = z := by
    simp [z, Complex.ext_iff]
    norm_num
  have hsym : star (finiteThetaShellPencil N θ z) = finiteThetaShellPencil N θ z := by
    calc star (finiteThetaShellPencil N θ z)
        = star (finiteThetaShellPencil N θ (1 - star z)) := by rw [h1z]
      _ = star (finiteThetaShellPencil N θ (star z)) := by rw [finiteThetaShellPencil_one_sub]
      _ = finiteThetaShellPencil N θ z := finiteThetaShellPencil_conj N θ z
  have him := congrArg Complex.im hsym
  simp only [Complex.star_def, Complex.conj_im] at him
  linarith

theorem finiteThetaAmplitude_criticalLine_im_eq_zero (N : ℕ) (t : ℝ) :
    (_root_.RHTower.finiteThetaAmplitude N ((1 / 2 : ℂ) + (t : ℂ) * I)).im = 0 := by
  simpa using finiteThetaShellPencil_criticalLine_im_eq_zero N 0 t

/-- Strict positivity on the entire real axis for every `N : ℕ`. -/
theorem finiteThetaAmplitude_real_re_pos (N : ℕ) (σ : ℝ) :
    0 < (_root_.RHTower.finiteThetaAmplitude N (σ : ℂ)).re := by
  have hint := _root_.RHTower.integrable_bilateralLaplace
    (_root_.RHTower.finiteThetaTiltSource N) ((1 / 2 : ℂ) - (σ : ℂ))
  rw [_root_.RHTower.finiteThetaAmplitude_eq_bilateral, _root_.RHTower.bilateralLaplace,
    bochner_integral_re hint]
  have hrew : (fun x : ℝ => (((_root_.RHTower.finiteThetaTiltSource N).k x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - (σ : ℂ)) * (x : ℂ))).re) =
      fun x : ℝ => _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
        Real.exp ((1 / 2 - σ) * x) := by
    funext x
    have hexp : ((1 / 2 : ℂ) - (σ : ℂ)) * (x : ℂ) = (((1 / 2 - σ) * x : ℝ) : ℂ) := by
      push_cast; ring
    rw [hexp, ← Complex.ofReal_exp, ← Complex.ofReal_mul, Complex.ofReal_re]
    rfl
  rw [hrew]
  have hint_re : Integrable (fun x : ℝ => _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
      Real.exp ((1 / 2 - σ) * x)) := by
    have h1 := Complex.reCLM.integrable_comp hint
    exact h1.congr (Eventually.of_forall fun x => by
      dsimp only [Function.comp_apply, Complex.reCLM_apply]
      exact congrFun hrew x)
  have hcont : Continuous (fun x : ℝ => _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
      Real.exp ((1 / 2 - σ) * x)) :=
    (_root_.RHTower.continuous_reflectedFiniteThetaSource (N + 1)).mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  exact (MeasureTheory.integral_pos_iff_support_of_nonneg
    (fun x => mul_nonneg (_root_.RHTower.reflectedFiniteThetaSource_nonneg (N + 1) x)
      (Real.exp_pos _).le) hint_re).mpr (by
      have hsupp : Function.support (fun x : ℝ =>
          _root_.RHTower.reflectedFiniteThetaSource (N + 1) x *
            Real.exp ((1 / 2 - σ) * x)) = Set.univ := by
        ext x
        simp only [Function.mem_support, Set.mem_univ, iff_true]
        exact mul_ne_zero
          (_root_.RHTower.reflectedFiniteThetaSource_pos (by omega) x).ne'
          (Real.exp_pos _).ne'
      rw [hsupp]
      simp)

theorem finiteThetaShellPencil_real_re_pos (N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (σ : ℝ) :
    0 < (finiteThetaShellPencil N θ (σ : ℂ)).re := by
  unfold finiteThetaShellPencil
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have h0 := finiteThetaAmplitude_real_re_pos N σ
  have h1 := finiteThetaAmplitude_real_re_pos (N + 1) σ
  rcases eq_or_lt_of_le hθ.1 with rfl | hpos
  · linarith
  · nlinarith [hθ.2]

theorem finiteThetaShellPencil_half_ne_zero (N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    finiteThetaShellPencil N θ (1 / 2 : ℂ) ≠ 0 := by
  intro h0
  have hpos := finiteThetaShellPencil_real_re_pos N hθ (1 / 2)
  have hcast : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hcast, h0, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- Every `finiteThetaShellPencil N θ` (`θ ∈ [0, 1]`) has finite analytic order at every `z : ℂ`. -/
theorem finiteThetaShellPencil_orderAt_ne_top (N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (z : ℂ) :
    analyticOrderAt (finiteThetaShellPencil N θ) z ≠ ⊤ := by
  refine (analyticOnNhd_finiteThetaShellPencil N θ).analyticOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (Set.mem_univ (1 / 2 : ℂ)) (Set.mem_univ z) ?_
  rw [((analyticOnNhd_finiteThetaShellPencil N θ) (1 / 2 : ℂ)
    (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr (finiteThetaShellPencil_half_ne_zero N hθ)]
  exact ENat.zero_ne_top

theorem finiteThetaAmplitude_orderAt_ne_top (N : ℕ) (z : ℂ) :
    analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z ≠ ⊤ := by
  have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
    funext fun w => (finiteThetaShellPencil_zero N w).symm
  rw [hfun]
  exact finiteThetaShellPencil_orderAt_ne_top N ⟨le_rfl, zero_le_one⟩ z

/-- Every `finiteThetaShellPencil N θ` (`θ ∈ [0, 1]`) has finitely many zeros in any closed ball. -/
theorem finiteThetaShellPencil_zeros_closedBall_finite (N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (c : ℂ) (R : ℝ) :
    {z ∈ Metric.closedBall c R | finiteThetaShellPencil N θ z = 0}.Finite := by
  have hcod : (finiteThetaShellPencil N θ ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    (analyticOnNhd_finiteThetaShellPencil N θ).preimage_zero_mem_codiscreteWithin
      (x := (1 / 2 : ℂ)) (finiteThetaShellPencil_half_ne_zero N hθ)
      (Set.mem_univ _) isConnected_univ
  have hcodK : (finiteThetaShellPencil N θ ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Metric.closedBall c R) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  refine ((isCompact_closedBall c R).finite_sdiff_of_mem_codiscreteWithin hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

theorem finiteThetaAmplitude_zeros_closedBall_finite (N : ℕ) (c : ℂ) (R : ℝ) :
    {z ∈ Metric.closedBall c R | _root_.RHTower.finiteThetaAmplitude N z = 0}.Finite := by
  simpa using finiteThetaShellPencil_zeros_closedBall_finite N ⟨le_rfl, zero_le_one⟩ c R

/-! ## §2 Complex seam-cusp 3rd-order IBP, strip zero finiteness, and operator height-freezing -/

/-- Half-line jet integral representation of `finiteThetaAmplitude N`. -/
theorem finiteThetaAmplitude_eq_integral_Ioi (N : ℕ) (z : ℂ) :
    _root_.RHTower.finiteThetaAmplitude N z =
      ∫ x in Ioi (0 : ℝ), (_root_.RHTower.thetaFiniteShellJet (N + 1) 0 x : ℂ) *
        (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) +
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
  have hint : Integrable (fun x : ℝ => (_root_.RHTower.reflectedFiniteThetaSource (N + 1) x : ℂ) *
      Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    simpa only [_root_.RHTower.finiteThetaTiltSource] using
      _root_.RHTower.integrable_bilateralLaplace
        (_root_.RHTower.finiteThetaTiltSource N) ((1 / 2 : ℂ) - z)
  rw [_root_.RHTower.finiteThetaAmplitude, integral_eq_integral_Ioi_add_neg hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hpos : _root_.RHTower.reflectedFiniteThetaSource (N + 1) x =
      _root_.RHTower.thetaFiniteShellJet (N + 1) 0 x := by
    rw [_root_.RHTower.thetaFiniteShellJet_zero_eq]
    simp [_root_.RHTower.reflectedFiniteThetaSource, abs_of_pos (mem_Ioi.mp hx)]
  have heven := _root_.RHTower.reflectedFiniteThetaSource_even (N + 1) x
  rw [heven, hpos]
  have hexp_neg : ((1 / 2 : ℂ) - z) * ((-x : ℝ) : ℂ) = (z - (1 / 2 : ℂ)) * (x : ℂ) := by
    push_cast; ring
  rw [hexp_neg]
  ring

/-- Exponentially weighted half-line decay of every jet `thetaFiniteShellJet (N + 1) k`. -/
theorem exp_mul_abs_thetaFiniteShellJet_le (N k q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    Real.exp ((q : ℝ) * x) * |_root_.RHTower.thetaFiniteShellJet (N + 1) k x| ≤
      ((N + 1 : ℕ) : ℝ) *
        _root_.RHTower.thetaCuspGaussianConstant
          (_root_.RHTower.thetaCuspWeightedPolynomial
            (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (q + 1)) *
        Real.exp (-x) := by
  let C_g := _root_.RHTower.thetaCuspGaussianConstant
    (_root_.RHTower.thetaCuspWeightedPolynomial
      (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (q + 1))
  have hCg_nn : 0 ≤ C_g := _root_.RHTower.thetaCuspGaussianConstant_nonneg _
  have hjet_le : |_root_.RHTower.thetaFiniteShellJet (N + 1) k x| ≤
      ∑ m ∈ Finset.range (N + 1),
        |_root_.RHTower.thetaCuspPolynomialAtom
          (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (m + 1) x| := by
    unfold _root_.RHTower.thetaFiniteShellJet
    exact Finset.abs_sum_le_sum_abs _ _
  have hterm : ∀ m ∈ Finset.range (N + 1),
      Real.exp ((q : ℝ) * x) *
          |_root_.RHTower.thetaCuspPolynomialAtom
            (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (m + 1) x| ≤
        C_g * Real.exp (-x) := by
    intro m _
    have hatom := _root_.RHTower.exp_natSucc_mul_abs_thetaCuspPolynomialAtom_le
      (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (q + 1) hx (Nat.succ_pos m)
    have hgauss_le : Real.exp (-(Real.pi / 2) * ((m + 1 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg ((m + 1 : ℕ) : ℝ)])
    have hatom' : Real.exp (((q + 2 : ℕ) : ℝ) * x) *
        |_root_.RHTower.thetaCuspPolynomialAtom
          (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (m + 1) x| ≤ C_g :=
      hatom.trans (mul_le_of_le_one_right hCg_nn hgauss_le)
    have hexp_split : Real.exp ((q : ℝ) * x) =
        Real.exp (-2 * x) * Real.exp (((q + 2 : ℕ) : ℝ) * x) := by
      rw [← Real.exp_add]
      congr 1
      push_cast; ring
    have hexp_le : Real.exp (-2 * x) ≤ Real.exp (-x) :=
      Real.exp_le_exp.mpr (by linarith)
    calc Real.exp ((q : ℝ) * x) *
            |_root_.RHTower.thetaCuspPolynomialAtom
              (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (m + 1) x|
        = Real.exp (-2 * x) * (Real.exp (((q + 2 : ℕ) : ℝ) * x) *
            |_root_.RHTower.thetaCuspPolynomialAtom
              (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (m + 1) x|) := by
          rw [hexp_split]; ring
      _ ≤ Real.exp (-2 * x) * C_g := mul_le_mul_of_nonneg_left hatom' (Real.exp_pos _).le
      _ ≤ Real.exp (-x) * C_g := mul_le_mul_of_nonneg_right hexp_le hCg_nn
      _ = C_g * Real.exp (-x) := mul_comm _ _
  calc Real.exp ((q : ℝ) * x) * |_root_.RHTower.thetaFiniteShellJet (N + 1) k x|
      ≤ Real.exp ((q : ℝ) * x) * ∑ m ∈ Finset.range (N + 1),
          |_root_.RHTower.thetaCuspPolynomialAtom
            (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (m + 1) x| :=
        mul_le_mul_of_nonneg_left hjet_le (Real.exp_pos _).le
    _ = ∑ m ∈ Finset.range (N + 1), Real.exp ((q : ℝ) * x) *
          |_root_.RHTower.thetaCuspPolynomialAtom
            (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (m + 1) x| :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ _m ∈ Finset.range (N + 1), C_g * Real.exp (-x) := Finset.sum_le_sum hterm
    _ = ((N + 1 : ℕ) : ℝ) * C_g * Real.exp (-x) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_assoc]

/-- Complex-kernel times real-jet integration by parts on `(0, ∞)`. -/
private lemma integral_Ioi_complex_mul_realDeriv
    {u u' : ℝ → ℂ} {v v' : ℝ → ℝ} {c₀ : ℂ}
    (hu : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt v (v' x) x)
    (huv' : IntegrableOn (fun x => u x * (v' x : ℂ)) (Ioi (0 : ℝ)))
    (hu'v : IntegrableOn (fun x => u' x * (v x : ℂ)) (Ioi (0 : ℝ)))
    (hzero : Tendsto (fun x => u x * (v x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 c₀))
    (hinf : Tendsto (fun x => u x * (v x : ℂ)) atTop (𝓝 0)) :
    (∫ x in Ioi (0 : ℝ), u x * (v' x : ℂ)) =
      -c₀ - ∫ x in Ioi (0 : ℝ), u' x * (v x : ℂ) := by
  have hre_eq : ∀ f : ℝ → ℂ, ∀ g : ℝ → ℝ, ∀ x : ℝ, (f x * (g x : ℂ)).re = (f x).re * g x := by
    intro f g x; simp [Complex.mul_re]
  have him_eq : ∀ f : ℝ → ℂ, ∀ g : ℝ → ℝ, ∀ x : ℝ, (f x * (g x : ℂ)).im = (f x).im * g x := by
    intro f g x; simp [Complex.mul_im]
  have hu_re : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y => (u y).re) ((u' x).re) x :=
    fun x hx => Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hu x hx)
  have hu_im : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun y => (u y).im) ((u' x).im) x :=
    fun x hx => Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hu x hx)
  have huv'_re : IntegrableOn (fun x => (u x).re * v' x) (Ioi (0 : ℝ)) := by
    have h := Complex.reCLM.integrable_comp (φ := fun x => u x * (v' x : ℂ)) huv'
    exact h.congr (Eventually.of_forall fun x => by
      dsimp only [Function.comp_apply, Complex.reCLM_apply]
      exact hre_eq u v' x)
  have hu'v_re : IntegrableOn (fun x => (u' x).re * v x) (Ioi (0 : ℝ)) := by
    have h := Complex.reCLM.integrable_comp (φ := fun x => u' x * (v x : ℂ)) hu'v
    exact h.congr (Eventually.of_forall fun x => by
      dsimp only [Function.comp_apply, Complex.reCLM_apply]
      exact hre_eq u' v x)
  have huv'_im : IntegrableOn (fun x => (u x).im * v' x) (Ioi (0 : ℝ)) := by
    have h := Complex.imCLM.integrable_comp (φ := fun x => u x * (v' x : ℂ)) huv'
    exact h.congr (Eventually.of_forall fun x => by
      dsimp only [Function.comp_apply, Complex.imCLM_apply]
      exact him_eq u v' x)
  have hu'v_im : IntegrableOn (fun x => (u' x).im * v x) (Ioi (0 : ℝ)) := by
    have h := Complex.imCLM.integrable_comp (φ := fun x => u' x * (v x : ℂ)) hu'v
    exact h.congr (Eventually.of_forall fun x => by
      dsimp only [Function.comp_apply, Complex.imCLM_apply]
      exact him_eq u' v x)
  have hzero_re : Tendsto (fun x => (u x).re * v x) (𝓝[>] (0 : ℝ)) (𝓝 c₀.re) := by
    simpa only [Function.comp_def, hre_eq] using
      (Complex.continuous_re.continuousAt.tendsto).comp hzero
  have hinf_re : Tendsto (fun x => (u x).re * v x) atTop (𝓝 0) := by
    simpa only [Function.comp_def, hre_eq, Complex.zero_re] using
      (Complex.continuous_re.continuousAt.tendsto).comp hinf
  have hzero_im : Tendsto (fun x => (u x).im * v x) (𝓝[>] (0 : ℝ)) (𝓝 c₀.im) := by
    simpa only [Function.comp_def, him_eq] using
      (Complex.continuous_im.continuousAt.tendsto).comp hzero
  have hinf_im : Tendsto (fun x => (u x).im * v x) atTop (𝓝 0) := by
    simpa only [Function.comp_def, him_eq, Complex.zero_im] using
      (Complex.continuous_im.continuousAt.tendsto).comp hinf
  have hibp_re := integral_Ioi_mul_deriv_eq_deriv_mul hu_re hv huv'_re hu'v_re hzero_re hinf_re
  have hibp_im := integral_Ioi_mul_deriv_eq_deriv_mul hu_im hv huv'_im hu'v_im hzero_im hinf_im
  apply Complex.ext
  · rw [bochner_integral_re huv', Complex.sub_re, Complex.neg_re, bochner_integral_re hu'v]
    simp only [hre_eq]
    linarith [hibp_re]
  · rw [bochner_integral_im huv', Complex.sub_im, Complex.neg_im, bochner_integral_im hu'v]
    simp only [him_eq]
    linarith [hibp_im]

private lemma integrableOn_cexp_pm_mul_jet (N k : ℕ) (w : ℂ) (s : ℂ) :
    IntegrableOn
      (fun x : ℝ => (Complex.exp (w * (x : ℂ)) + s * Complex.exp (-w * (x : ℂ))) *
        (_root_.RHTower.thetaFiniteShellJet (N + 1) k x : ℂ))
      (Ioi (0 : ℝ)) := by
  set q := Nat.ceil |w.re|
  let B := ((N + 1 : ℕ) : ℝ) *
    _root_.RHTower.thetaCuspGaussianConstant
      (_root_.RHTower.thetaCuspWeightedPolynomial
        (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (q + 1))
  have hdom : IntegrableOn (fun x : ℝ => ((1 + ‖s‖) * B) * Real.exp (-x)) (Ioi (0 : ℝ)) := by
    have h1 := integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
    exact (h1.congr_fun (fun x _ => by ring_nf) measurableSet_Ioi).const_mul _
  have hcont_jet : Continuous (_root_.RHTower.thetaFiniteShellJet (N + 1) k) :=
    continuous_iff_continuousAt.mpr fun x =>
      (_root_.RHTower.hasDerivAt_thetaFiniteShellJet (N + 1) k x).continuousAt
  have hcont : Continuous (fun x : ℝ =>
      (Complex.exp (w * (x : ℂ)) + s * Complex.exp (-w * (x : ℂ))) *
        (_root_.RHTower.thetaFiniteShellJet (N + 1) k x : ℂ)) :=
    ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).add
      (continuous_const.mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)))).mul
      (Complex.continuous_ofReal.comp hcont_jet)
  refine Integrable.mono' hdom hcont.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 ≤ x := hx.le
  have hq : |w.re| ≤ (q : ℝ) := Nat.le_ceil |w.re|
  have hexp1 : ‖Complex.exp (w * (x : ℂ))‖ ≤ Real.exp ((q : ℝ) * x) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (w * (x : ℂ)).re = w.re * x := by simp
    rw [hre]
    exact (le_abs_self _).trans (by rw [abs_mul, abs_of_nonneg hx0]; exact mul_le_mul_of_nonneg_right hq hx0)
  have hexp2 : ‖Complex.exp (-w * (x : ℂ))‖ ≤ Real.exp ((q : ℝ) * x) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (-w * (x : ℂ)).re = -w.re * x := by simp
    rw [hre]
    exact (le_abs_self _).trans (by
      rw [abs_mul, abs_neg, abs_of_nonneg hx0]
      exact mul_le_mul_of_nonneg_right hq hx0)
  have hsum : ‖Complex.exp (w * (x : ℂ)) + s * Complex.exp (-w * (x : ℂ))‖ ≤
      (1 + ‖s‖) * Real.exp ((q : ℝ) * x) := by
    calc ‖Complex.exp (w * (x : ℂ)) + s * Complex.exp (-w * (x : ℂ))‖
        ≤ ‖Complex.exp (w * (x : ℂ))‖ + ‖s‖ * ‖Complex.exp (-w * (x : ℂ))‖ := by
          simpa only [norm_mul] using
            norm_add_le (Complex.exp (w * (x : ℂ))) (s * Complex.exp (-w * (x : ℂ)))
      _ ≤ Real.exp ((q : ℝ) * x) + ‖s‖ * Real.exp ((q : ℝ) * x) :=
          add_le_add hexp1 (mul_le_mul_of_nonneg_left hexp2 (norm_nonneg s))
      _ = (1 + ‖s‖) * Real.exp ((q : ℝ) * x) := by ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖Complex.exp (w * (x : ℂ)) + s * Complex.exp (-w * (x : ℂ))‖ *
          |_root_.RHTower.thetaFiniteShellJet (N + 1) k x|
      ≤ ((1 + ‖s‖) * Real.exp ((q : ℝ) * x)) *
          |_root_.RHTower.thetaFiniteShellJet (N + 1) k x| :=
        mul_le_mul_of_nonneg_right hsum (abs_nonneg _)
    _ = (1 + ‖s‖) * (Real.exp ((q : ℝ) * x) *
          |_root_.RHTower.thetaFiniteShellJet (N + 1) k x|) := by ring
    _ ≤ (1 + ‖s‖) * (B * Real.exp (-x)) :=
        mul_le_mul_of_nonneg_left (exp_mul_abs_thetaFiniteShellJet_le N k q hx0) (by positivity)
    _ = ((1 + ‖s‖) * B) * Real.exp (-x) := by ring

private lemma tendsto_cexp_pm_mul_jet_atTop (N k : ℕ) (w : ℂ) (s : ℂ) :
    Tendsto
      (fun x : ℝ => (Complex.exp (w * (x : ℂ)) + s * Complex.exp (-w * (x : ℂ))) *
        (_root_.RHTower.thetaFiniteShellJet (N + 1) k x : ℂ))
      atTop (𝓝 0) := by
  set q := Nat.ceil |w.re|
  let B := ((N + 1 : ℕ) : ℝ) *
    _root_.RHTower.thetaCuspGaussianConstant
      (_root_.RHTower.thetaCuspWeightedPolynomial
        (_root_.RHTower.thetaCuspLogDerivativePolynomial k) (q + 1))
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun x : ℝ => ((1 + ‖s‖) * B) * Real.exp (-x)) atTop (𝓝 0) := by
    simpa only [mul_zero] using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul ((1 + ‖s‖) * B)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ ht
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx0
  have hq : |w.re| ≤ (q : ℝ) := Nat.le_ceil |w.re|
  have hexp1 : ‖Complex.exp (w * (x : ℂ))‖ ≤ Real.exp ((q : ℝ) * x) := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
    have hre : (w * (x : ℂ)).re = w.re * x := by simp
    rw [hre]
    exact (le_abs_self _).trans (by rw [abs_mul, abs_of_nonneg hx0]; exact mul_le_mul_of_nonneg_right hq hx0)
  have hexp2 : ‖Complex.exp (-w * (x : ℂ))‖ ≤ Real.exp ((q : ℝ) * x) := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
    have hre : (-w * (x : ℂ)).re = -w.re * x := by simp
    rw [hre]
    exact (le_abs_self _).trans (by
      rw [abs_mul, abs_neg, abs_of_nonneg hx0]
      exact mul_le_mul_of_nonneg_right hq hx0)
  have hsum : ‖Complex.exp (w * (x : ℂ)) + s * Complex.exp (-w * (x : ℂ))‖ ≤
      (1 + ‖s‖) * Real.exp ((q : ℝ) * x) := by
    calc ‖Complex.exp (w * (x : ℂ)) + s * Complex.exp (-w * (x : ℂ))‖
        ≤ ‖Complex.exp (w * (x : ℂ))‖ + ‖s‖ * ‖Complex.exp (-w * (x : ℂ))‖ := by
          simpa only [norm_mul] using
            norm_add_le (Complex.exp (w * (x : ℂ))) (s * Complex.exp (-w * (x : ℂ)))
      _ ≤ (1 + ‖s‖) * Real.exp ((q : ℝ) * x) := by nlinarith [norm_nonneg s]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc ‖Complex.exp (w * (x : ℂ)) + s * Complex.exp (-w * (x : ℂ))‖ *
          |_root_.RHTower.thetaFiniteShellJet (N + 1) k x|
      ≤ (1 + ‖s‖) * (Real.exp ((q : ℝ) * x) *
          |_root_.RHTower.thetaFiniteShellJet (N + 1) k x|) := by
        nlinarith [abs_nonneg (_root_.RHTower.thetaFiniteShellJet (N + 1) k x)]
    _ ≤ ((1 + ‖s‖) * B) * Real.exp (-x) := by
        have := exp_mul_abs_thetaFiniteShellJet_le N k q hx0
        nlinarith [norm_nonneg s]

private lemma hasDerivAt_cexp_cosh (w : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (w * (y : ℂ)) + Complex.exp (-w * (y : ℂ)))
      (w * (Complex.exp (w * (x : ℂ)) - Complex.exp (-w * (x : ℂ)))) x := by
  have hlin1 : HasDerivAt (fun y : ℝ => w * (y : ℂ)) w x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul w
  have hlin2 : HasDerivAt (fun y : ℝ => -w * (y : ℂ)) (-w) x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-w)
  have h1 : HasDerivAt (fun y : ℝ => Complex.exp (w * (y : ℂ)))
      (Complex.exp (w * (x : ℂ)) * w) x :=
    (Complex.hasDerivAt_exp (w * (x : ℂ))).comp x hlin1
  have h2 : HasDerivAt (fun y : ℝ => Complex.exp (-w * (y : ℂ)))
      (Complex.exp (-w * (x : ℂ)) * (-w)) x :=
    (Complex.hasDerivAt_exp (-w * (x : ℂ))).comp x hlin2
  exact (h1.add h2).congr_deriv (by ring)

private lemma hasDerivAt_cexp_sinh (w : ℂ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.exp (w * (y : ℂ)) - Complex.exp (-w * (y : ℂ)))
      (w * (Complex.exp (w * (x : ℂ)) + Complex.exp (-w * (x : ℂ)))) x := by
  have hlin1 : HasDerivAt (fun y : ℝ => w * (y : ℂ)) w x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul w
  have hlin2 : HasDerivAt (fun y : ℝ => -w * (y : ℂ)) (-w) x := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using
      (Complex.ofRealCLM.hasDerivAt (x := x)).const_mul (-w)
  have h1 : HasDerivAt (fun y : ℝ => Complex.exp (w * (y : ℂ)))
      (Complex.exp (w * (x : ℂ)) * w) x :=
    (Complex.hasDerivAt_exp (w * (x : ℂ))).comp x hlin1
  have h2 : HasDerivAt (fun y : ℝ => Complex.exp (-w * (y : ℂ)))
      (Complex.exp (-w * (x : ℂ)) * (-w)) x :=
    (Complex.hasDerivAt_exp (-w * (x : ℂ))).comp x hlin2
  exact (h1.sub h2).congr_deriv (by ring)

/-- **Second-order complex seam-cusp identity.**
`(z - 1 / 2)² A_N(z) = 2 J_{N+1,1}(0) + ∫_{x > 0} J_{N+1,2}(x) (e^{(z - 1/2)x} + e^{(1/2 - z)x})`. -/
theorem finiteThetaAmplitude_mul_sq_sub_half_ibp2 (N : ℕ) (z : ℂ) :
    (z - (1 / 2 : ℂ)) ^ 2 * _root_.RHTower.finiteThetaAmplitude N z =
      2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ) +
        ∫ x in Ioi (0 : ℝ), (_root_.RHTower.thetaFiniteShellJet (N + 1) 2 x : ℂ) *
          (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) +
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
  set w : ℂ := z - (1 / 2 : ℂ)
  have hw_neg : (1 / 2 : ℂ) - z = -w := by dsimp [w]; ring
  let C : ℝ → ℂ := fun x => Complex.exp (w * (x : ℂ)) + Complex.exp (-w * (x : ℂ))
  let S : ℝ → ℂ := fun x => Complex.exp (w * (x : ℂ)) - Complex.exp (-w * (x : ℂ))
  let J := _root_.RHTower.thetaFiniteShellJet (N + 1)
  have hC_int : ∀ k, IntegrableOn (fun x => C x * (J k x : ℂ)) (Ioi (0 : ℝ)) := fun k => by
    simpa [C] using integrableOn_cexp_pm_mul_jet N k w 1
  have hS_int : ∀ k, IntegrableOn (fun x => S x * (J k x : ℂ)) (Ioi (0 : ℝ)) := fun k => by
    simpa [S, sub_eq_add_neg] using integrableOn_cexp_pm_mul_jet N k w (-1)
  have hC_inf : ∀ k, Tendsto (fun x => C x * (J k x : ℂ)) atTop (𝓝 0) := fun k => by
    simpa [C] using tendsto_cexp_pm_mul_jet_atTop N k w 1
  have hS_inf : ∀ k, Tendsto (fun x => S x * (J k x : ℂ)) atTop (𝓝 0) := fun k => by
    simpa [S, sub_eq_add_neg] using tendsto_cexp_pm_mul_jet_atTop N k w (-1)
  have hJ_cont : ∀ k, Continuous (J k) := fun k =>
    continuous_iff_continuousAt.mpr fun x =>
      (_root_.RHTower.hasDerivAt_thetaFiniteShellJet (N + 1) k x).continuousAt
  have hC_cont : Continuous C :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).add
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hS_cont : Continuous S :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).sub
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hzero1 : Tendsto (fun x => S x * (J 0 x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : S 0 * (J 0 0 : ℂ) = 0 := by simp [S]
    rw [← h0]
    exact ((hS_cont.mul (Complex.continuous_ofReal.comp (hJ_cont 0))).continuousAt.tendsto).mono_left
      inf_le_left
  have hzero2 : Tendsto (fun x => C x * (J 1 x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (2 * (J 1 0 : ℂ))) := by
    have h0 : C 0 * (J 1 0 : ℂ) = 2 * (J 1 0 : ℂ) := by simp [C]; norm_num
    rw [← h0]
    exact ((hC_cont.mul (Complex.continuous_ofReal.comp (hJ_cont 1))).continuousAt.tendsto).mono_left
      inf_le_left
  have hwC0 : IntegrableOn (fun x => (w * C x) * (J 0 x : ℂ)) (Ioi (0 : ℝ)) :=
    ((hC_int 0).const_mul w).congr (Eventually.of_forall fun _ => by dsimp only; ring)
  have hwS1 : IntegrableOn (fun x => (w * S x) * (J 1 x : ℂ)) (Ioi (0 : ℝ)) :=
    ((hS_int 1).const_mul w).congr (Eventually.of_forall fun _ => by dsimp only; ring)
  have hibp1 := integral_Ioi_complex_mul_realDeriv
    (u := S) (u' := fun x => w * C x) (v := J 0) (v' := J 1) (c₀ := 0)
    (fun x _ => hasDerivAt_cexp_sinh w x)
    (fun x _ => _root_.RHTower.hasDerivAt_thetaFiniteShellJet (N + 1) 0 x)
    (hS_int 1) hwC0 hzero1 (hS_inf 0)
  have hibp2 := integral_Ioi_complex_mul_realDeriv
    (u := C) (u' := fun x => w * S x) (v := J 1) (v' := J 2) (c₀ := 2 * (J 1 0 : ℂ))
    (fun x _ => hasDerivAt_cexp_cosh w x)
    (fun x _ => _root_.RHTower.hasDerivAt_thetaFiniteShellJet (N + 1) 1 x)
    (hC_int 2) hwS1 hzero2 (hC_inf 1)
  have hpull1 : (∫ x in Ioi (0 : ℝ), (w * C x) * (J 0 x : ℂ)) =
      w * ∫ x in Ioi (0 : ℝ), C x * (J 0 x : ℂ) := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun _ _ => by ring
  have hpull2 : (∫ x in Ioi (0 : ℝ), (w * S x) * (J 1 x : ℂ)) =
      w * ∫ x in Ioi (0 : ℝ), S x * (J 1 x : ℂ) := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun _ _ => by ring
  rw [hpull1, neg_zero, zero_sub] at hibp1
  rw [hpull2, hibp1] at hibp2
  have hamp : _root_.RHTower.finiteThetaAmplitude N z = ∫ x in Ioi (0 : ℝ), C x * (J 0 x : ℂ) := by
    rw [finiteThetaAmplitude_eq_integral_Ioi]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    dsimp [C, J]; rw [hw_neg]; ring
  have hint2_comm : (∫ x in Ioi (0 : ℝ), (J 2 x : ℂ) *
        (Complex.exp (w * (x : ℂ)) + Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))) =
      ∫ x in Ioi (0 : ℝ), C x * (J 2 x : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    dsimp [C]; rw [hw_neg]; ring
  rw [hamp, hint2_comm]
  linear_combination -hibp2

/-- **Third-order complex seam-cusp remainder identity.** -/
theorem finiteThetaAmplitude_mul_sq_sub_half_ibp3 (N : ℕ) (z : ℂ) :
    (z - (1 / 2 : ℂ)) *
        ((z - (1 / 2 : ℂ)) ^ 2 * _root_.RHTower.finiteThetaAmplitude N z -
          2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ)) =
      -∫ x in Ioi (0 : ℝ), (_root_.RHTower.thetaFiniteShellJet (N + 1) 3 x : ℂ) *
        (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
  set w : ℂ := z - (1 / 2 : ℂ)
  have hw_neg : (1 / 2 : ℂ) - z = -w := by dsimp [w]; ring
  let C : ℝ → ℂ := fun x => Complex.exp (w * (x : ℂ)) + Complex.exp (-w * (x : ℂ))
  let S : ℝ → ℂ := fun x => Complex.exp (w * (x : ℂ)) - Complex.exp (-w * (x : ℂ))
  let J := _root_.RHTower.thetaFiniteShellJet (N + 1)
  have hC_int : IntegrableOn (fun x => C x * (J 2 x : ℂ)) (Ioi (0 : ℝ)) := by
    simpa [C] using integrableOn_cexp_pm_mul_jet N 2 w 1
  have hS_int : IntegrableOn (fun x => S x * (J 3 x : ℂ)) (Ioi (0 : ℝ)) := by
    simpa [S, sub_eq_add_neg] using integrableOn_cexp_pm_mul_jet N 3 w (-1)
  have hS_inf : Tendsto (fun x => S x * (J 2 x : ℂ)) atTop (𝓝 0) := by
    simpa [S, sub_eq_add_neg] using tendsto_cexp_pm_mul_jet_atTop N 2 w (-1)
  have hJ2_cont : Continuous (J 2) :=
    continuous_iff_continuousAt.mpr fun x =>
      (_root_.RHTower.hasDerivAt_thetaFiniteShellJet (N + 1) 2 x).continuousAt
  have hS_cont : Continuous S :=
    (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).sub
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hzero3 : Tendsto (fun x => S x * (J 2 x : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : S 0 * (J 2 0 : ℂ) = 0 := by simp [S]
    rw [← h0]
    exact ((hS_cont.mul (Complex.continuous_ofReal.comp hJ2_cont)).continuousAt.tendsto).mono_left
      inf_le_left
  have hwC2 : IntegrableOn (fun x => (w * C x) * (J 2 x : ℂ)) (Ioi (0 : ℝ)) :=
    (hC_int.const_mul w).congr (Eventually.of_forall fun _ => by dsimp only; ring)
  have hibp3 := integral_Ioi_complex_mul_realDeriv
    (u := S) (u' := fun x => w * C x) (v := J 2) (v' := J 3) (c₀ := 0)
    (fun x _ => hasDerivAt_cexp_sinh w x)
    (fun x _ => _root_.RHTower.hasDerivAt_thetaFiniteShellJet (N + 1) 2 x)
    hS_int hwC2 hzero3 hS_inf
  have hpull3 : (∫ x in Ioi (0 : ℝ), (w * C x) * (J 2 x : ℂ)) =
      w * ∫ x in Ioi (0 : ℝ), C x * (J 2 x : ℂ) := by
    rw [← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi fun _ _ => by ring
  rw [hpull3, neg_zero, zero_sub] at hibp3
  have hibp2 := finiteThetaAmplitude_mul_sq_sub_half_ibp2 N z
  have hint2_comm : (∫ x in Ioi (0 : ℝ), (J 2 x : ℂ) *
        (Complex.exp (w * (x : ℂ)) + Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))) =
      ∫ x in Ioi (0 : ℝ), C x * (J 2 x : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    dsimp [C]; rw [hw_neg]; ring
  have hint3_comm : (∫ x in Ioi (0 : ℝ), (J 3 x : ℂ) *
        (Complex.exp (w * (x : ℂ)) - Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))) =
      ∫ x in Ioi (0 : ℝ), S x * (J 3 x : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    dsimp [S]; rw [hw_neg]; ring
  rw [hint2_comm] at hibp2
  rw [hint3_comm]
  linear_combination w * hibp2 + hibp3

/-- Explicit vertical-strip third-jet remainder constant for `finiteThetaAmplitude N` on
`{|Re z - 1 / 2| ≤ |R|}`. -/
def thetaJetStripThirdBound (N : ℕ) (R : ℝ) : ℝ :=
  2 * (((N + 1 : ℕ) : ℝ) *
    _root_.RHTower.thetaCuspGaussianConstant
      (_root_.RHTower.thetaCuspWeightedPolynomial
        (_root_.RHTower.thetaCuspLogDerivativePolynomial 3) (Nat.ceil |R| + 1)))

/-- Explicit vertical-strip seam-cusp horizon `thetaPrefixCuspHorizon N R` above which
`(z - 1 / 2)² A_N(z)` is strictly right-half-plane sectorial around `2 J_{N+1,1}(0) > 0`. -/
def thetaPrefixCuspHorizon (N : ℕ) (R : ℝ) : ℝ :=
  thetaJetStripThirdBound N R / _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0

theorem thetaJetStripThirdBound_nonneg (N : ℕ) (R : ℝ) :
    0 ≤ thetaJetStripThirdBound N R := by
  unfold thetaJetStripThirdBound
  have h := _root_.RHTower.thetaCuspGaussianConstant_nonneg
    (_root_.RHTower.thetaCuspWeightedPolynomial
      (_root_.RHTower.thetaCuspLogDerivativePolynomial 3) (Nat.ceil |R| + 1))
  positivity

theorem thetaPrefixCuspHorizon_nonneg (N : ℕ) (R : ℝ) :
    0 ≤ thetaPrefixCuspHorizon N R :=
  div_nonneg (thetaJetStripThirdBound_nonneg N R)
    (_root_.RHTower.thetaFiniteShellJet_one_zero_pos N).le

/-- Uniform strip remainder bound `‖(z - 1/2) ((z - 1/2)² A_N(z) - 2 J_1(0))‖ ≤ B_3(N, R)`. -/
theorem norm_finiteThetaAmplitude_cusp_remainder_le (N : ℕ) (R : ℝ) {z : ℂ}
    (hz : |z.re - 1 / 2| ≤ |R|) :
    ‖(z - (1 / 2 : ℂ)) *
        ((z - (1 / 2 : ℂ)) ^ 2 * _root_.RHTower.finiteThetaAmplitude N z -
          2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ))‖ ≤
      thetaJetStripThirdBound N R := by
  rw [finiteThetaAmplitude_mul_sq_sub_half_ibp3, norm_neg]
  set q := Nat.ceil |R|
  let B := ((N + 1 : ℕ) : ℝ) *
    _root_.RHTower.thetaCuspGaussianConstant
      (_root_.RHTower.thetaCuspWeightedPolynomial
        (_root_.RHTower.thetaCuspLogDerivativePolynomial 3) (q + 1))
  have hdom_int : IntegrableOn (fun x : ℝ => (2 * B) * Real.exp (-x)) (Ioi (0 : ℝ)) := by
    have h1 := integrableOn_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
    exact (h1.congr_fun (fun x _ => by ring_nf) measurableSet_Ioi).const_mul _
  have hint : IntegrableOn
      (fun x : ℝ => (_root_.RHTower.thetaFiniteShellJet (N + 1) 3 x : ℂ) *
        (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))))
      (Ioi (0 : ℝ)) := by
    have h := integrableOn_cexp_pm_mul_jet N 3 (z - (1 / 2 : ℂ)) (-1)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    have hw : (1 / 2 : ℂ) - z = -(z - (1 / 2 : ℂ)) := by ring
    rw [hw]; ring
  have hexp_int : (∫ x in Ioi (0 : ℝ), Real.exp (-x)) = 1 := by
    have h := integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) 0
    have hcongr : (∫ x in Ioi (0 : ℝ), Real.exp (-x)) =
        ∫ x in Ioi (0 : ℝ), Real.exp (-1 * x) :=
      setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring_nf
    rw [hcongr, h]
    norm_num
  calc ‖∫ x in Ioi (0 : ℝ), (_root_.RHTower.thetaFiniteShellJet (N + 1) 3 x : ℂ) *
          (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))‖
      ≤ ∫ x in Ioi (0 : ℝ), ‖(_root_.RHTower.thetaFiniteShellJet (N + 1) 3 x : ℂ) *
          (Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ)))‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ x in Ioi (0 : ℝ), (2 * B) * Real.exp (-x) := by
        refine integral_mono_ae hint.norm hdom_int ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        have hx0 : 0 ≤ x := hx.le
        have hq : |z.re - 1 / 2| ≤ (q : ℝ) := hz.trans (Nat.le_ceil |R|)
        have hexp1 : ‖Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ))‖ ≤ Real.exp ((q : ℝ) * x) := by
          rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
          have hre : ((z - (1 / 2 : ℂ)) * (x : ℂ)).re = (z.re - 1 / 2) * x := by simp
          rw [hre]
          exact (le_abs_self _).trans
            (by rw [abs_mul, abs_of_nonneg hx0]; exact mul_le_mul_of_nonneg_right hq hx0)
        have hexp2 : ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤ Real.exp ((q : ℝ) * x) := by
          rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
          have hre : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = -(z.re - 1 / 2) * x := by
            have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
            have h12i : (1 / 2 : ℂ).im = 0 := by norm_num
            simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
              Complex.ofReal_im, h12, h12i, mul_zero, sub_zero]
            ring
          rw [hre]
          exact (le_abs_self _).trans (by
            rw [abs_mul, abs_neg, abs_of_nonneg hx0]
            exact mul_le_mul_of_nonneg_right hq hx0)
        have hdiff : ‖Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
            Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤ 2 * Real.exp ((q : ℝ) * x) :=
          (norm_sub_le _ _).trans (by linarith)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc |_root_.RHTower.thetaFiniteShellJet (N + 1) 3 x| *
                ‖Complex.exp ((z - (1 / 2 : ℂ)) * (x : ℂ)) -
                  Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖
            ≤ |_root_.RHTower.thetaFiniteShellJet (N + 1) 3 x| * (2 * Real.exp ((q : ℝ) * x)) :=
              mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
          _ = 2 * (Real.exp ((q : ℝ) * x) * |_root_.RHTower.thetaFiniteShellJet (N + 1) 3 x|) := by
              ring
          _ ≤ 2 * (B * Real.exp (-x)) :=
              mul_le_mul_of_nonneg_left (exp_mul_abs_thetaFiniteShellJet_le N 3 q hx0) (by norm_num)
          _ = (2 * B) * Real.exp (-x) := by ring
    _ = thetaJetStripThirdBound N R := by
        rw [MeasureTheory.integral_const_mul, hexp_int, mul_one]
        rfl

/-- **High-ordinate seam-cusp sectoriality and nonvanishing theorem.**
Above `thetaPrefixCuspHorizon N R` in the strip `{|Re z - 1 / 2| ≤ |R|}`,
`(z - 1 / 2)² A_N(z)` lies in the open disc of radius `J_{N+1,1}(0)` around `2 J_{N+1,1}(0) > 0`,
hence has strictly positive real part `> J_{N+1,1}(0)` and `A_N(z) ≠ 0`. -/
theorem finiteThetaAmplitude_cusp_sectorial_above_horizon (N : ℕ) (R : ℝ) {z : ℂ}
    (hz_re : |z.re - 1 / 2| ≤ |R|) (hz_norm : thetaPrefixCuspHorizon N R < ‖z - (1 / 2 : ℂ)‖) :
    _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 <
        ((z - (1 / 2 : ℂ)) ^ 2 * _root_.RHTower.finiteThetaAmplitude N z).re ∧
      _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
  have hJ_pos := _root_.RHTower.thetaFiniteShellJet_one_zero_pos N
  have hw_pos : 0 < ‖z - (1 / 2 : ℂ)‖ :=
    (thetaPrefixCuspHorizon_nonneg N R).trans_lt hz_norm
  have hrem := norm_finiteThetaAmplitude_cusp_remainder_le N R hz_re
  rw [norm_mul] at hrem
  have hlt_mul : thetaJetStripThirdBound N R <
      ‖z - (1 / 2 : ℂ)‖ * _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by
    rw [thetaPrefixCuspHorizon, div_lt_iff₀ hJ_pos] at hz_norm
    linarith
  have hball : ‖(z - (1 / 2 : ℂ)) ^ 2 * _root_.RHTower.finiteThetaAmplitude N z -
      2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ)‖ <
      _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by
    exact lt_of_mul_lt_mul_left (hrem.trans_lt hlt_mul) hw_pos.le
  have hre_sub : |((z - (1 / 2 : ℂ)) ^ 2 * _root_.RHTower.finiteThetaAmplitude N z -
      2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ)).re| <
      _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 :=
    (Complex.abs_re_le_norm _).trans_lt hball
  have hre_two : (2 * (_root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 : ℂ)).re =
      2 * _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 := by simp
  rw [Complex.sub_re, hre_two] at hre_sub
  have hre_gt : _root_.RHTower.thetaFiniteShellJet (N + 1) 1 0 <
      ((z - (1 / 2 : ℂ)) ^ 2 * _root_.RHTower.finiteThetaAmplitude N z).re :=
    by linarith [(abs_lt.mp hre_sub).1]
  refine ⟨hre_gt, ?_⟩
  intro hzero
  rw [hzero, mul_zero, Complex.zero_re] at hre_gt
  exact lt_irrefl 0 (hJ_pos.trans hre_gt)

/-- **Global vertical-strip zero finiteness of `finiteThetaAmplitude N`.**
Unlike `xi` (which has infinitely many zeros in `{0 < Re z < 1}`), every finite integer theta
prefix has only *finitely* many zeros in the entire infinite vertical strip `{|Re z - 1/2| ≤ R}`. -/
theorem finiteThetaAmplitude_strip_zeros_finite (N : ℕ) (R : ℝ) :
    {z : ℂ | |z.re - 1 / 2| ≤ R ∧ _root_.RHTower.finiteThetaAmplitude N z = 0}.Finite := by
  refine (finiteThetaAmplitude_zeros_closedBall_finite N (1 / 2 : ℂ)
    (thetaPrefixCuspHorizon N R + 1)).subset ?_
  rintro z ⟨hz_re, hz0⟩
  rw [Set.mem_sep_iff, Metric.mem_closedBall, dist_eq_norm]
  refine ⟨?_, hz0⟩
  by_contra hgt
  have hlt : thetaPrefixCuspHorizon N R < ‖z - (1 / 2 : ℂ)‖ := by linarith [not_le.mp hgt]
  exact (finiteThetaAmplitude_cusp_sectorial_above_horizon N R
    (hz_re.trans (le_abs_self R)) hlt).2 hz0

/-- Above `thetaPrefixCuspHorizon N 0`, `finiteThetaAmplitude N (1 / 2 + t * I)` is strictly
negative on the critical line. -/
theorem finiteThetaAmplitude_criticalLine_neg_above_horizon (N : ℕ) {t : ℝ}
    (ht : thetaPrefixCuspHorizon N 0 < |t|) :
    (_root_.RHTower.finiteThetaAmplitude N ((1 / 2 : ℂ) + (t : ℂ) * I)).re < 0 := by
  set z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I
  have hz_sub : z - (1 / 2 : ℂ) = (t : ℂ) * I := by dsimp [z]; ring
  have hz_re : |z.re - 1 / 2| ≤ |(0 : ℝ)| := by
    have : z.re = 1 / 2 := by simp [z]
    rw [this]; simp
  have hz_norm : thetaPrefixCuspHorizon N 0 < ‖z - (1 / 2 : ℂ)‖ := by
    rw [hz_sub, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    exact ht
  have hsec := (finiteThetaAmplitude_cusp_sectorial_above_horizon N 0 hz_re hz_norm).1
  have hsq : (z - (1 / 2 : ℂ)) ^ 2 = (-(t ^ 2) : ℝ) := by
    rw [hz_sub, mul_pow, Complex.I_sq]
    push_cast; ring
  rw [hsq] at hsec
  have hre : (((-(t ^ 2) : ℝ) : ℂ) * _root_.RHTower.finiteThetaAmplitude N z).re =
      -(t ^ 2) * (_root_.RHTower.finiteThetaAmplitude N z).re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre] at hsec
  have hJ_pos := _root_.RHTower.thetaFiniteShellJet_one_zero_pos N
  have ht2_pos : 0 < t ^ 2 := by
    have ht0 : 0 < |t| := (thetaPrefixCuspHorizon_nonneg N 0).trans_lt ht
    nlinarith [sq_abs t]
  nlinarith

/-- Vertical rectangle splitting identity: subtracting the lower rectangle integral from the tall
rectangle integral leaves the upper stacked rectangle integral. -/
private lemma rectIntegral_vertical_split (g : ℂ → ℂ) (x₁ x₂ y₁ y₂ y₃ : ℝ)
    (hr1 : IntervalIntegrable (fun y : ℝ => g ((x₂ : ℂ) + y * I)) volume y₁ y₂)
    (hr2 : IntervalIntegrable (fun y : ℝ => g ((x₂ : ℂ) + y * I)) volume y₂ y₃)
    (hl1 : IntervalIntegrable (fun y : ℝ => g ((x₁ : ℂ) + y * I)) volume y₁ y₂)
    (hl2 : IntervalIntegrable (fun y : ℝ => g ((x₁ : ℂ) + y * I)) volume y₂ y₃) :
    _root_.RHTower.rectIntegral g ((x₁ : ℂ) + (y₁ : ℂ) * I) ((x₂ : ℂ) + (y₃ : ℂ) * I) -
        _root_.RHTower.rectIntegral g ((x₁ : ℂ) + (y₁ : ℂ) * I) ((x₂ : ℂ) + (y₂ : ℂ) * I) =
      _root_.RHTower.rectIntegral g ((x₁ : ℂ) + (y₂ : ℂ) * I) ((x₂ : ℂ) + (y₃ : ℂ) * I) := by
  have hre : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * I).re = a := fun a b => by simp
  have him : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * I).im = b := fun a b => by simp
  unfold _root_.RHTower.rectIntegral
  simp only [hre, him, smul_eq_mul]
  rw [← intervalIntegral.integral_add_adjacent_intervals hr1 hr2,
    ← intervalIntegral.integral_add_adjacent_intervals hl1 hl2]
  ring

/-- **Unconditional strip zero-set height-freezing.**
For every `N : ℕ`, `R : ℝ`, and `T₁, T₂ > thetaPrefixCuspHorizon N R`, the height-window zero sets
of `finiteThetaAmplitude N` in `{|Re z - 1 / 2| ≤ R}` are identical. -/
theorem finiteThetaAmplitude_strip_zeros_eq_of_gt_cuspHorizon (N : ℕ) (R : ℝ) {T₁ T₂ : ℝ}
    (hT₁ : thetaPrefixCuspHorizon N R < T₁) (hT₂ : thetaPrefixCuspHorizon N R < T₂) :
    {z : ℂ | |z.re - 1 / 2| ≤ R ∧ 0 ≤ z.im ∧ z.im < T₁ ∧
        _root_.RHTower.finiteThetaAmplitude N z = 0} =
      {z : ℂ | |z.re - 1 / 2| ≤ R ∧ 0 ≤ z.im ∧ z.im < T₂ ∧
        _root_.RHTower.finiteThetaAmplitude N z = 0} := by
  ext z
  have him_le : |z.re - 1 / 2| ≤ R → _root_.RHTower.finiteThetaAmplitude N z = 0 →
      z.im ≤ thetaPrefixCuspHorizon N R := by
    intro hre hz0
    by_contra hgt
    have hlt : thetaPrefixCuspHorizon N R < z.im := not_le.mp hgt
    have hnorm : thetaPrefixCuspHorizon N R < ‖z - (1 / 2 : ℂ)‖ := by
      have him : z.im ≤ ‖z - (1 / 2 : ℂ)‖ := by
        have : (z - (1 / 2 : ℂ)).im = z.im := by simp
        rw [← this]
        exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
      exact hlt.trans_le him
    exact (finiteThetaAmplitude_cusp_sectorial_above_horizon N R
      (hre.trans (le_abs_self R)) hnorm).2 hz0
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hre, h0, _, hz0⟩
    exact ⟨hre, h0, (him_le hre hz0).trans_lt hT₂, hz0⟩
  · rintro ⟨hre, h0, _, hz0⟩
    exact ⟨hre, h0, (him_le hre hz0).trans_lt hT₁, hz0⟩

/-- **Exact contour and Wiener–Hopf operator height-freezing theorem.**
Whenever `finiteThetaAmplitude N` avoids the side edges `{Re z ∈ {-1/2, 3/2}}` up to the base
cusp height `thetaPrefixCuspHorizon N 3 + 2` (in particular whenever `finiteThetaAmplitude N` is
boundary-regular at `T₀ = thetaPrefixCuspHorizon N 3 + 2`), advancing `T₁ → T₂` above
`thetaPrefixCuspHorizon N 3 + 2` leaves `integerThetaWindowPowerSum`, `integerThetaWindowDegree`,
`integerThetaDifferencePoly`, `integerThetaLaurentLoop`, and `integerThetaCollisionOperator`
identically unchanged. -/
theorem integerThetaWindowPowerSum_eq_of_ge_cuspHorizon (n N r : ℕ) {T₁ T₂ : ℝ}
    (hT₁ : thetaPrefixCuspHorizon N 3 + 2 ≤ T₁)
    (hT₂ : thetaPrefixCuspHorizon N 3 + 2 ≤ T₂)
    (hside : ∀ y ∈ Icc (-(1 / (2 * (zhukovskyStage n : ℝ))))
        (thetaPrefixCuspHorizon N 3 + 2 - 1 / (2 * (zhukovskyStage n : ℝ))),
      _root_.RHTower.finiteThetaAmplitude N ((-1 / 2 : ℂ) + (y : ℂ) * I) ≠ 0 ∧
        _root_.RHTower.finiteThetaAmplitude N ((3 / 2 : ℂ) + (y : ℂ) * I) ≠ 0) :
    integerThetaWindowPowerSum T₁ n N r = integerThetaWindowPowerSum T₂ n N r := by
  set T₀ : ℝ := thetaPrefixCuspHorizon N 3 + 2
  suffices hbase : ∀ {B : ℝ}, T₀ ≤ B →
      integerThetaWindowPowerSum T₀ n N r = integerThetaWindowPowerSum B n N r by
    rw [← hbase hT₁, ← hbase hT₂]
  intro B hB
  have hH_nn := thetaPrefixCuspHorizon_nonneg N 3
  have hT₀_nn : 0 ≤ T₀ := by dsimp [T₀]; linarith
  have hB_nn : 0 ≤ B := hT₀_nn.trans hB
  set s := (zhukovskyStage n : ℝ)
  have hs6 : (6 : ℝ) ≤ s := six_le_zhukovskyStage_real n
  have hhalf_le : 1 / (2 * s) ≤ 1 / 12 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  set y₁ : ℝ := -(1 / (2 * s))
  set y₂ : ℝ := T₀ - 1 / (2 * s)
  set y₃ : ℝ := B - 1 / (2 * s)
  let U : Set ℂ := {z : ℂ | -2 < z.re ∧ z.re < 3 ∧ y₂ - 1 / 2 < z.im ∧ z.im < y₃ + 1 / 2}
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        ((isOpen_lt continuous_const Complex.continuous_im).inter
          (isOpen_lt Complex.continuous_im continuous_const)))
  have hU_nz : ∀ z ∈ U, _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
    intro z hz
    have hz_re : |z.re - 1 / 2| ≤ |(3 : ℝ)| := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_le]
      exact ⟨by linarith [hz.1], by linarith [hz.2.1]⟩
    have hz_im : thetaPrefixCuspHorizon N 3 < z.im := by
      linarith [hz.2.2.1, hhalf_le]
    have hz_norm : thetaPrefixCuspHorizon N 3 < ‖z - (1 / 2 : ℂ)‖ := by
      have him : z.im ≤ ‖z - (1 / 2 : ℂ)‖ := by
        have : (z - (1 / 2 : ℂ)).im = z.im := by simp
        rw [← this]
        exact (le_abs_self _).trans (Complex.abs_im_le_norm _)
      exact hz_im.trans_le him
    exact (finiteThetaAmplitude_cusp_sectorial_above_horizon N 3 hz_re hz_norm).2
  let g : ℂ → ℂ := fun z => z ^ r *
    (-_root_.RHTower.finiteThetaFirstMoment N z / _root_.RHTower.finiteThetaAmplitude N z)
  have hg_an : AnalyticOnNhd ℂ g U := by
    intro z hz
    have hnum : AnalyticAt ℂ (fun w => -_root_.RHTower.finiteThetaFirstMoment N w) z := by
      have heq : (fun w => -_root_.RHTower.finiteThetaFirstMoment N w) =
          deriv (_root_.RHTower.finiteThetaAmplitude N) :=
        funext fun w => (_root_.RHTower.deriv_finiteThetaAmplitude N w).symm
      rw [heq]
      exact ((analyticOnNhd_finiteThetaAmplitude N).deriv) z (Set.mem_univ z)
    exact (analyticAt_id.pow r).mul
      (hnum.div (analyticOnNhd_finiteThetaAmplitude N z (Set.mem_univ z)) (hU_nz z hz))
  have hsub_U : (uIcc (-1 / 2 : ℝ) (3 / 2 : ℝ) ×ℂ uIcc y₂ y₃) ⊆ U := by
    intro z hz
    rw [uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 3 / 2),
      uIcc_of_le (by dsimp [y₂, y₃]; linarith), Complex.mem_reProdIm] at hz
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2],
      by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hnum_cont : Continuous (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment N z) := by
    have heq : (fun z : ℂ => -_root_.RHTower.finiteThetaFirstMoment N z) =
        deriv (_root_.RHTower.finiteThetaAmplitude N) :=
      funext fun z => (_root_.RHTower.deriv_finiteThetaAmplitude N z).symm
    rw [heq]
    exact continuousOn_univ.mp
      (((_root_.RHTower.differentiable_finiteThetaAmplitude N).differentiableOn.deriv
        isOpen_univ).continuousOn)
  have hg_contOn : ∀ {x₀ a b : ℝ}, a ≤ b →
      (∀ y ∈ Icc a b, _root_.RHTower.finiteThetaAmplitude N ((x₀ : ℂ) + (y : ℂ) * I) ≠ 0) →
      IntervalIntegrable (fun y : ℝ => g ((x₀ : ℂ) + (y : ℂ) * I)) volume a b := by
    intro x₀ a b hab hnz
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    have hpt : Continuous (fun y : ℝ => (x₀ : ℂ) + (y : ℂ) * I) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    exact (hpt.pow r).continuousOn.mul
      ((hnum_cont.comp hpt).continuousOn.div
        (((_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous.comp hpt).continuousOn)
        hnz)
  have hy12 : y₁ ≤ y₂ := by dsimp [y₁, y₂]; linarith
  have hy23 : y₂ ≤ y₃ := by dsimp [y₂, y₃]; linarith
  have hr1 : IntervalIntegrable (fun y : ℝ => g (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) volume y₁ y₂ :=
    hg_contOn hy12 fun y hy => by simpa [y₁, y₂, T₀] using (hside y hy).2
  have hl1 : IntervalIntegrable (fun y : ℝ => g (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) volume y₁ y₂ :=
    hg_contOn hy12 fun y hy => by simpa [y₁, y₂, T₀] using (hside y hy).1
  have hr2 : IntervalIntegrable (fun y : ℝ => g (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) volume y₂ y₃ :=
    hg_contOn hy23 fun y hy => hU_nz _ (hsub_U (Complex.mem_reProdIm.mpr
      ⟨uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 3 / 2) ▸ ⟨by simp; norm_num, by simp⟩,
       uIcc_of_le hy23 ▸ (by simpa using hy)⟩))
  have hl2 : IntervalIntegrable (fun y : ℝ => g (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) volume y₂ y₃ :=
    hg_contOn hy23 fun y hy => hU_nz _ (hsub_U (Complex.mem_reProdIm.mpr
      ⟨uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 3 / 2) ▸ ⟨by simp, by simp; norm_num⟩,
       uIcc_of_le hy23 ▸ (by simpa using hy)⟩))
  have hsplit := rectIntegral_vertical_split g (-1 / 2) (3 / 2) y₁ y₂ y₃ hr1 hr2 hl1 hl2
  have htop_zero : _root_.RHTower.rectIntegral g
      (((-1 / 2 : ℝ) : ℂ) + (y₂ : ℂ) * I) (((3 / 2 : ℝ) : ℂ) + (y₃ : ℂ) * I) = 0 := by
    apply _root_.RHTower.rectIntegral_eq_zero_of_analyticOnNhd _ hg_an
    simpa using hsub_U
  rw [htop_zero] at hsplit
  have hcorner_low : ((-1 / 2 : ℝ) : ℂ) + (y₁ : ℂ) * I = thetaWindowLowerLeft n := by
    unfold thetaWindowLowerLeft
    dsimp [y₁, s]
    push_cast; ring
  have hcorner_T₀ : ((3 / 2 : ℝ) : ℂ) + (y₂ : ℂ) * I = thetaWindowUpperRight T₀ n := by
    unfold thetaWindowUpperRight
    rw [max_eq_right hT₀_nn]
    dsimp [y₂, s]
    push_cast; ring
  have hcorner_B : ((3 / 2 : ℝ) : ℂ) + (y₃ : ℂ) * I = thetaWindowUpperRight B n := by
    unfold thetaWindowUpperRight
    rw [max_eq_right hB_nn]
    dsimp [y₃, s]
    push_cast; ring
  rw [hcorner_low, hcorner_T₀, hcorner_B] at hsplit
  unfold integerThetaWindowPowerSum
  rw [sub_eq_zero.mp hsplit]

/-- Operator-level corollary of `integerThetaWindowPowerSum_eq_of_ge_cuspHorizon`. -/
theorem integerThetaCollisionOperator_eq_of_ge_cuspHorizon (n N : ℕ) {T₁ T₂ : ℝ}
    (hT₁ : thetaPrefixCuspHorizon N 3 + 2 ≤ T₁)
    (hT₂ : thetaPrefixCuspHorizon N 3 + 2 ≤ T₂)
    (hside : ∀ y ∈ Icc (-(1 / (2 * (zhukovskyStage n : ℝ))))
        (thetaPrefixCuspHorizon N 3 + 2 - 1 / (2 * (zhukovskyStage n : ℝ))),
      _root_.RHTower.finiteThetaAmplitude N ((-1 / 2 : ℂ) + (y : ℂ) * I) ≠ 0 ∧
        _root_.RHTower.finiteThetaAmplitude N ((3 / 2 : ℂ) + (y : ℂ) * I) ≠ 0) :
    integerThetaWindowDegree T₁ n N = integerThetaWindowDegree T₂ n N ∧
    integerThetaDifferencePoly T₁ n N = integerThetaDifferencePoly T₂ n N ∧
    integerThetaLaurentLoop T₁ n N = integerThetaLaurentLoop T₂ n N ∧
    integerThetaCollisionOperator T₁ n N = integerThetaCollisionOperator T₂ n N := by
  have hps : integerThetaWindowPowerSum T₁ n N = integerThetaWindowPowerSum T₂ n N :=
    funext fun r => integerThetaWindowPowerSum_eq_of_ge_cuspHorizon n N r hT₁ hT₂ hside
  have hdeg : integerThetaWindowDegree T₁ n N = integerThetaWindowDegree T₂ n N := by
    unfold integerThetaWindowDegree; rw [hps]
  have hpoly : integerThetaDifferencePoly T₁ n N = integerThetaDifferencePoly T₂ n N := by
    unfold integerThetaDifferencePoly; rw [hdeg, hps]
  have hbase : integerThetaBaseLoop T₁ n N = integerThetaBaseLoop T₂ n N := by
    ext u
    change (integerThetaDifferencePoly T₁ n N).eval (zhukovskyLoop n u) =
      (integerThetaDifferencePoly T₂ n N).eval (zhukovskyLoop n u)
    rw [hpoly]
  have hloop : integerThetaLaurentLoop T₁ n N = integerThetaLaurentLoop T₂ n N := by
    unfold integerThetaLaurentLoop; rw [hbase]
  refine ⟨hdeg, hpoly, hloop, ?_⟩
  unfold integerThetaCollisionOperator integerThetaCollisionSymbol
  rw [hloop]

/-! ## §3 Direct all-`N`, all-stage sectorial certificate on low windows `T ≤ 3` -/

private lemma one_sub_cos_le_half_sq (u : ℝ) : 1 - Real.cos u ≤ u ^ 2 / 2 := by
  have h2 : u = 2 * (u / 2) := by ring
  have hc : Real.cos u = 1 - 2 * Real.sin (u / 2) ^ 2 := by
    rw [h2, Real.cos_two_mul, Real.cos_sq']
    ring
  have hs : Real.sin (u / 2) ^ 2 ≤ (u / 2) ^ 2 := by
    rw [← sq_abs, ← sq_abs (u / 2)]
    exact pow_le_pow_left₀ (abs_nonneg _) Real.abs_sin_le_abs 2
  linarith

private lemma exp_eight_fifths_lt_five : Real.exp (8 / 5) < 5 := by
  have he1 : Real.exp 1 < 2719 / 1000 := by
    have h := Real.exp_one_lt_d9
    norm_num at h ⊢
    linarith
  have hp8 : Real.exp 8 < (5 : ℝ) ^ 5 := by
    calc Real.exp 8 = Real.exp ((8 : ℕ) * (1 : ℝ)) := by norm_num
      _ = Real.exp 1 ^ 8 := Real.exp_nat_mul 1 8
      _ < (2719 / 1000 : ℝ) ^ 8 := pow_lt_pow_left₀ he1 (Real.exp_pos 1).le (by norm_num)
      _ < (5 : ℝ) ^ 5 := by norm_num
  have hp5 : Real.exp (8 / 5) ^ 5 = Real.exp 8 := by
    rw [← Real.exp_nat_mul]
    norm_num
  by_contra hge
  have hle : (5 : ℝ) ≤ Real.exp (8 / 5) := not_lt.mp hge
  have hpow : (5 : ℝ) ^ 5 ≤ Real.exp (8 / 5) ^ 5 := pow_le_pow_left₀ (by norm_num) hle 5
  linarith

private lemma two_cosh_mul_thetaCuspSourceTerm_one_le {σ x : ℝ} (hσ : |σ| ≤ 9 / 8) (hx : 0 ≤ x) :
    (Real.exp (σ * x) + Real.exp (-σ * x)) * _root_.RHTower.thetaCuspSourceTerm x 1 ≤
      400 * Real.exp (-Real.pi) * Real.exp (-(15 / 2) * x) := by
  have hσ1 : σ * x ≤ (9 / 8) * x := by
    have h := (abs_le.mp hσ).2
    exact mul_le_mul_of_nonneg_right h hx
  have hσ2 : -σ * x ≤ (9 / 8) * x := by
    have h : -σ ≤ 9 / 8 := by linarith [(abs_le.mp hσ).1]
    exact mul_le_mul_of_nonneg_right h hx
  have hcosh : Real.exp (σ * x) + Real.exp (-σ * x) ≤ 2 * Real.exp ((9 / 8) * x) := by
    linarith [Real.exp_le_exp.mpr hσ1, Real.exp_le_exp.mpr hσ2]
  have hpi_gt : (314 / 100 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d2; norm_num at h ⊢; linarith
  have hpi_lt : Real.pi < (315 / 100 : ℝ) := by
    have h := Real.pi_lt_d2; norm_num at h ⊢; linarith
  have hterm1 : _root_.RHTower.thetaCuspSourceTerm x 1 ≤
      40 * Real.exp ((9 / 2) * x - Real.pi * Real.exp (2 * x)) := by
    unfold _root_.RHTower.thetaCuspSourceTerm _root_.RHTower.thetaCuspSeed
    simp only [Nat.cast_one, one_mul]
    have hexp4 : Real.exp x ^ (4 : ℕ) = Real.exp (4 * x) := by
      rw [← Real.exp_nat_mul]; norm_num
    have hexp2 : Real.exp x ^ (2 : ℕ) = Real.exp (2 * x) := by
      rw [← Real.exp_nat_mul]; norm_num
    have hpi_sq : 4 * Real.pi ^ 2 ≤ 40 := by nlinarith [Real.pi_pos]
    have hpoly : 2 * Real.pi * (2 * Real.pi * Real.exp x ^ (4 : ℕ) - 3 * Real.exp x ^ (2 : ℕ)) ≤
        40 * Real.exp (4 * x) := by
      rw [hexp4, hexp2]
      have he4_pos : 0 < Real.exp (4 * x) := Real.exp_pos _
      have he2_nn : 0 ≤ Real.exp (2 * x) := (Real.exp_pos _).le
      nlinarith [Real.pi_pos]
    calc Real.exp (x / 2) *
            (2 * Real.pi * (2 * Real.pi * Real.exp x ^ (4 : ℕ) - 3 * Real.exp x ^ (2 : ℕ)) *
              Real.exp (-Real.pi * Real.exp x ^ (2 : ℕ)))
        ≤ Real.exp (x / 2) * (40 * Real.exp (4 * x) * Real.exp (-Real.pi * Real.exp x ^ (2 : ℕ))) := by
          gcongr
      _ = 40 * (Real.exp (x / 2) * Real.exp (4 * x) *
            Real.exp (-Real.pi * Real.exp (2 * x))) := by rw [hexp2]; ring
      _ = 40 * Real.exp ((9 / 2) * x - Real.pi * Real.exp (2 * x)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 2; ring
  have htaylor0 := Real.sum_le_exp_of_nonneg (show 0 ≤ 2 * x by positivity) 4
  have htaylor : 1 + 2 * x + 2 * x ^ 2 + (4 / 3) * x ^ 3 ≤ Real.exp (2 * x) := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at htaylor0
    linarith
  have hsos : 1 + (106 / 25) * x - 184 / 375 ≤ 1 + 2 * x + 2 * x ^ 2 + (4 / 3) * x ^ 3 := by
    have hdiff : (1 + 2 * x + 2 * x ^ 2 + (4 / 3) * x ^ 3) - (1 + (106 / 25) * x - 184 / 375) =
        (x - 2 / 5) ^ 2 * ((4 / 3) * x + 46 / 15) := by ring
    have hnn : 0 ≤ (x - 2 / 5) ^ 2 * ((4 / 3) * x + 46 / 15) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    linarith
  have hexp2_ge : 1 + (106 / 25) * x - 184 / 375 ≤ Real.exp (2 * x) := hsos.trans htaylor
  have hexponent : (9 / 8) * x + ((9 / 2) * x - Real.pi * Real.exp (2 * x)) ≤
      -Real.pi + 8 / 5 + -(15 / 2) * x := by
    have h1 : Real.pi * (1 + (106 / 25) * x - 184 / 375) ≤ Real.pi * Real.exp (2 * x) :=
      mul_le_mul_of_nonneg_left hexp2_ge Real.pi_pos.le
    have h2 : (314 / 100) * ((106 / 25) * x) ≤ Real.pi * ((106 / 25) * x) :=
      mul_le_mul_of_nonneg_right hpi_gt.le (by positivity)
    linarith
  have hexp_comb : Real.exp ((9 / 8) * x) * Real.exp ((9 / 2) * x - Real.pi * Real.exp (2 * x)) ≤
      5 * Real.exp (-Real.pi) * Real.exp (-(15 / 2) * x) := by
    rw [← Real.exp_add]
    calc Real.exp ((9 / 8) * x + ((9 / 2) * x - Real.pi * Real.exp (2 * x)))
        ≤ Real.exp (-Real.pi + 8 / 5 + -(15 / 2) * x) := Real.exp_le_exp.mpr hexponent
      _ = Real.exp (-Real.pi) * Real.exp (8 / 5) * Real.exp (-(15 / 2) * x) := by
          rw [Real.exp_add, Real.exp_add]
      _ ≤ Real.exp (-Real.pi) * 5 * Real.exp (-(15 / 2) * x) := by
          gcongr; exact exp_eight_fifths_lt_five.le
      _ = 5 * Real.exp (-Real.pi) * Real.exp (-(15 / 2) * x) := by ring
  have hsrc_nn : 0 ≤ _root_.RHTower.thetaCuspSourceTerm x 1 :=
    _root_.RHTower.thetaCuspSourceTerm_nonneg_on_halfLine hx 1
  calc (Real.exp (σ * x) + Real.exp (-σ * x)) * _root_.RHTower.thetaCuspSourceTerm x 1
      ≤ (2 * Real.exp ((9 / 8) * x)) *
          (40 * Real.exp ((9 / 2) * x - Real.pi * Real.exp (2 * x))) :=
        mul_le_mul hcosh hterm1 hsrc_nn (by positivity)
    _ = 80 * (Real.exp ((9 / 8) * x) *
          Real.exp ((9 / 2) * x - Real.pi * Real.exp (2 * x))) := by ring
    _ ≤ 80 * (5 * Real.exp (-Real.pi) * Real.exp (-(15 / 2) * x)) :=
        mul_le_mul_of_nonneg_left hexp_comb (by norm_num)
    _ = 400 * Real.exp (-Real.pi) * Real.exp (-(15 / 2) * x) := by ring

private lemma integral_Ioi_sq_mul_exp_neg_fifteen_halves :
    (∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-(15 / 2) * x)) = 16 / 3375 := by
  have hbil := _root_.HTGeometry.integral_abs_evenPow_mul_exp_neg_abs 1
    (by norm_num : (0 : ℝ) < 15 / 2)
  have hint := _root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 2
    (by norm_num : (0 : ℝ) < 15 / 2)
  rw [show 2 * 1 = 2 by rfl] at hbil
  rw [integral_eq_integral_Ioi_add_neg hint] at hbil
  have hcongr : (∫ x in Ioi (0 : ℝ),
      |x| ^ 2 * Real.exp (-(15 / 2) * |x|) + |-x| ^ 2 * Real.exp (-(15 / 2) * |-x|)) =
      2 * ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-(15 / 2) * x) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    rw [abs_neg, abs_of_pos hx]
    ring
  have hval : (2 : ℝ) * (Nat.factorial 2 : ℝ) / (15 / 2 : ℝ) ^ (2 + 1) = 32 / 3375 := by
    norm_num [Nat.factorial]
  rw [hcongr, hval] at hbil
  linarith

/-- **Direct all-`N` right-half-plane sectorial certificate on low windows.**
For every `N : ℕ` and every `z : ℂ` with `|z.re - 1 / 2| ≤ 9 / 8` and `|z.im| ≤ 61 / 20`,
`Re (finiteThetaAmplitude N z) ≥ (5026 / 16875) * exp (-π) > 0`. -/
theorem finiteThetaAmplitude_re_ge_lowWindow (N : ℕ) {z : ℂ}
    (hz_re : |z.re - 1 / 2| ≤ 9 / 8) (hz_im : |z.im| ≤ 61 / 20) :
    (5026 / 16875) * Real.exp (-Real.pi) ≤ (_root_.RHTower.finiteThetaAmplitude N z).re := by
  set σ : ℝ := 1 / 2 - z.re
  set b : ℝ := -z.im
  have hσ : |σ| ≤ 9 / 8 := by dsimp [σ]; rwa [abs_sub_comm]
  have hb : |b| ≤ 61 / 20 := by dsimp [b]; rwa [abs_neg]
  let P := _root_.RHTower.reflectedFiniteThetaSource (N + 1)
  have hint_c := _root_.RHTower.integrable_bilateralLaplace
    (_root_.RHTower.finiteThetaTiltSource N) ((1 / 2 : ℂ) - z)
  have hpt_eq : ∀ x : ℝ, (((_root_.RHTower.finiteThetaTiltSource N).k x : ℂ) *
      Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))).re =
      P x * Real.exp (σ * x) * Real.cos (b * x) := by
    intro x
    have hw : ((1 / 2 : ℂ) - z) * (x : ℂ) = ((σ * x : ℝ) : ℂ) + ((b * x : ℝ) : ℂ) * I := by
      dsimp [σ, b]
      apply Complex.ext <;> simp
    rw [hw, Complex.exp_add, ← Complex.ofReal_exp, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
    change ((P x : ℂ) * ((Real.exp (σ * x) : ℂ) *
      ((Real.cos (b * x) : ℂ) + (Real.sin (b * x) : ℂ) * I))).re = _
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, add_zero, sub_zero, mul_one]
    ring
  have hre_int : (_root_.RHTower.finiteThetaAmplitude N z).re =
      ∫ x : ℝ, P x * Real.exp (σ * x) * Real.cos (b * x) := by
    rw [_root_.RHTower.finiteThetaAmplitude_eq_bilateral, _root_.RHTower.bilateralLaplace,
      bochner_integral_re hint_c]
    exact MeasureTheory.integral_congr_ae (Eventually.of_forall hpt_eq)
  have hint_real : Integrable (fun x : ℝ => P x * Real.exp (σ * x) * Real.cos (b * x)) :=
    (Complex.reCLM.integrable_comp hint_c).congr (Eventually.of_forall fun x => by
      dsimp only [Function.comp_apply, Complex.reCLM_apply]
      exact hpt_eq x)
  rw [hre_int, integral_eq_integral_Ioi_add_neg hint_real]
  have hfold : (∫ x in Ioi (0 : ℝ),
        P x * Real.exp (σ * x) * Real.cos (b * x) +
          P (-x) * Real.exp (σ * -x) * Real.cos (b * -x)) =
      ∫ x in Ioi (0 : ℝ), P x * (Real.exp (σ * x) + Real.exp (-σ * x)) * Real.cos (b * x) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    have hev : P (-x) = P x := _root_.RHTower.reflectedFiniteThetaSource_even (N + 1) x
    rw [hev, show b * -x = -(b * x) by ring, Real.cos_neg, show σ * -x = -σ * x by ring]
    ring
  rw [hfold]
  -- Integrability of `P x * (exp(σ x) + exp(-σ x))` on `Ioi 0` (`b = 0` specialization).
  have hint_cosh : IntegrableOn (fun x : ℝ => P x * (Real.exp (σ * x) + Real.exp (-σ * x)))
      (Ioi (0 : ℝ)) := by
    have hpos : IntegrableOn
        (fun x : ℝ => (((_root_.RHTower.finiteThetaTiltSource N).k x : ℂ) *
          Complex.exp ((σ : ℂ) * (x : ℂ))).re) (Ioi (0 : ℝ)) :=
      (Complex.reCLM.integrable_comp (_root_.RHTower.integrable_bilateralLaplace
        (_root_.RHTower.finiteThetaTiltSource N) (σ : ℂ))).integrableOn
    have hneg : IntegrableOn
        (fun x : ℝ => (((_root_.RHTower.finiteThetaTiltSource N).k x : ℂ) *
          Complex.exp (((-σ : ℝ) : ℂ) * (x : ℂ))).re) (Ioi (0 : ℝ)) :=
      (Complex.reCLM.integrable_comp (_root_.RHTower.integrable_bilateralLaplace
        (_root_.RHTower.finiteThetaTiltSource N) ((-σ : ℝ) : ℂ))).integrableOn
    refine (hpos.add hneg).congr_fun (fun x _ => ?_) measurableSet_Ioi
    have h1 : (((_root_.RHTower.finiteThetaTiltSource N).k x : ℂ) *
        Complex.exp ((σ : ℂ) * (x : ℂ))).re = P x * Real.exp (σ * x) := by
      rw [show (σ : ℂ) * (x : ℂ) = ((σ * x : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp]
      change ((P x : ℂ) * (Real.exp (σ * x) : ℂ)).re = _
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    have h2 : (((_root_.RHTower.finiteThetaTiltSource N).k x : ℂ) *
        Complex.exp (((-σ : ℝ) : ℂ) * (x : ℂ))).re = P x * Real.exp (-σ * x) := by
      rw [show ((-σ : ℝ) : ℂ) * (x : ℂ) = ((-σ * x : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp]
      change ((P x : ℂ) * (Real.exp (-σ * x) : ℂ)).re = _
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    dsimp only [Pi.add_apply]
    rw [h1, h2]; ring
  have hint_cos : IntegrableOn
      (fun x : ℝ => P x * (Real.exp (σ * x) + Real.exp (-σ * x)) * Real.cos (b * x))
      (Ioi (0 : ℝ)) := by
    have hmul := Integrable.bdd_mul hint_cosh
      (Real.continuous_cos.comp ((continuous_const : Continuous fun _ : ℝ => b).mul
        continuous_id)).aestronglyMeasurable.restrict
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one (b * x))
    exact hmul.congr (Eventually.of_forall fun x => mul_comm _ _)
  have hint_def : IntegrableOn
      (fun x : ℝ => P x * (Real.exp (σ * x) + Real.exp (-σ * x)) * (1 - Real.cos (b * x)))
      (Ioi (0 : ℝ)) := by
    refine (hint_cosh.sub hint_cos).congr_fun (fun x _ => ?_) measurableSet_Ioi
    dsimp only [Pi.sub_apply]; ring
  have hsplit_cos : (∫ x in Ioi (0 : ℝ),
        P x * (Real.exp (σ * x) + Real.exp (-σ * x)) * Real.cos (b * x)) =
      (∫ x in Ioi (0 : ℝ), P x * (Real.exp (σ * x) + Real.exp (-σ * x))) -
        ∫ x in Ioi (0 : ℝ),
          P x * (Real.exp (σ * x) + Real.exp (-σ * x)) * (1 - Real.cos (b * x)) := by
    rw [← MeasureTheory.integral_sub hint_cosh hint_def]
    exact setIntegral_congr_fun measurableSet_Ioi fun _ _ => by ring
  rw [hsplit_cos]
  -- 1. Lower bound on the main positive integral via Ward half-density at `-1 / 2`.
  have hmain_ge : 10 * Real.exp (-Real.pi) ≤
      ∫ x in Ioi (0 : ℝ), P x * (Real.exp (σ * x) + Real.exp (-σ * x)) := by
    have hward_int := (_root_.RHTower.integrableOn_exp_mul_thetaCuspSourceTerm_of_lt_one
      (n := 1) (by omega) (z := -1 / 2) (by norm_num)).const_mul 2
    have hward_val := _root_.RHTower.thetaCuspSourceExponentialTilt_neg_half (n := 1) (by omega)
    simp only [Nat.cast_one, one_pow, mul_one] at hward_val
    have hmono : (∫ x in Ioi (0 : ℝ),
          2 * (Real.exp ((-1 / 2) * x) * _root_.RHTower.thetaCuspSourceTerm x 1)) ≤
        ∫ x in Ioi (0 : ℝ), P x * (Real.exp (σ * x) + Real.exp (-σ * x)) := by
      refine integral_mono_ae hward_int hint_cosh ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have hP_ge : _root_.RHTower.thetaCuspSourceTerm x 1 ≤ P x := by
        dsimp [P]
        unfold _root_.RHTower.reflectedFiniteThetaSource _root_.RHTower.thetaCuspFiniteShellPrefix
        rw [abs_of_nonneg hx0]
        exact Finset.single_le_sum
          (fun m _ => _root_.RHTower.thetaCuspSourceTerm_nonneg_on_halfLine hx0 m)
          (Finset.mem_range.mpr (by omega))
      have h2_le : 2 ≤ Real.exp (σ * x) + Real.exp (-σ * x) := by
        have hprod : Real.exp (σ * x) * Real.exp (-σ * x) = 1 := by
          rw [← Real.exp_add]; simp
        have hsq : 0 ≤ (Real.exp (σ * x) - 1) ^ 2 * Real.exp (-σ * x) :=
          mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
        nlinarith
      have hexp_le1 : Real.exp ((-1 / 2) * x) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by linarith)
      have hsrc_nn := _root_.RHTower.thetaCuspSourceTerm_nonneg_on_halfLine hx0 1
      calc 2 * (Real.exp ((-1 / 2) * x) * _root_.RHTower.thetaCuspSourceTerm x 1)
          ≤ 2 * (1 * _root_.RHTower.thetaCuspSourceTerm x 1) := by gcongr
        _ = _root_.RHTower.thetaCuspSourceTerm x 1 * 2 := by ring
        _ ≤ P x * (Real.exp (σ * x) + Real.exp (-σ * x)) :=
            mul_le_mul hP_ge h2_le (by norm_num) (hsrc_nn.trans hP_ge)
    rw [MeasureTheory.integral_const_mul] at hmono
    change 2 * _root_.RHTower.thetaCuspSourceExponentialTilt (-1 / 2) 1 ≤ _ at hmono
    rw [hward_val] at hmono
    have hpi3 : 3 < Real.pi := Real.pi_gt_three
    have he_pos : 0 < Real.exp (-Real.pi) := Real.exp_pos _
    nlinarith
  -- 2. Upper bound on the oscillatory defect integral.
  have hdef_le : (∫ x in Ioi (0 : ℝ),
        P x * (Real.exp (σ * x) + Real.exp (-σ * x)) * (1 - Real.cos (b * x))) ≤
      (163724 / 16875) * Real.exp (-Real.pi) := by
    let C_top : ℝ := ((61 / 20 : ℝ) ^ 2 / 2) * (11 / 10) * 400 * Real.exp (-Real.pi)
    have hmom_int : IntegrableOn (fun x : ℝ => C_top * (x ^ 2 * Real.exp (-(15 / 2) * x)))
        (Ioi (0 : ℝ)) := by
      have h : IntegrableOn (fun x : ℝ => |x| ^ 2 * Real.exp (-(15 / 2) * |x|)) (Ioi (0 : ℝ)) :=
        (_root_.HTGeometry.integrable_abs_pow_mul_exp_neg_abs 2
          (by norm_num : (0 : ℝ) < 15 / 2)).integrableOn
      exact (h.const_mul C_top).congr
        ((ae_restrict_mem measurableSet_Ioi).mono fun x hx => by
          dsimp only
          rw [abs_of_pos (mem_Ioi.mp hx)])
    have hmono : (∫ x in Ioi (0 : ℝ),
          P x * (Real.exp (σ * x) + Real.exp (-σ * x)) * (1 - Real.cos (b * x))) ≤
        ∫ x in Ioi (0 : ℝ), C_top * (x ^ 2 * Real.exp (-(15 / 2) * x)) := by
      refine integral_mono_ae hint_def hmom_int ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 ≤ x := hx.le
      have hP_full : P x ≤ _root_.RHTower.thetaCuspFullSource x :=
        _root_.RHTower.reflectedFiniteThetaSource_le_full (N + 1) x
      have hsrc1_nn := _root_.RHTower.thetaCuspSourceTerm_nonneg_on_halfLine hx0 1
      have hfull_1 : _root_.RHTower.thetaCuspFullSource x ≤
          (11 / 10) * _root_.RHTower.thetaCuspSourceTerm x 1 := by
        have hsub := _root_.RHTower.thetaCuspFullSource_sub_first_le hx0
        have hw := _root_.RHTower.thetaCuspHigherAtomDominationWeight_le_geometric_rational
        nlinarith
      have hP_le : P x ≤ (11 / 10) * _root_.RHTower.thetaCuspSourceTerm x 1 :=
        hP_full.trans hfull_1
      have hcos_def : 1 - Real.cos (b * x) ≤ ((61 / 20 : ℝ) ^ 2 / 2) * x ^ 2 := by
        have h1 := one_sub_cos_le_half_sq (b * x)
        have h2 : b ^ 2 ≤ (61 / 20 : ℝ) ^ 2 := by
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg b) hb 2
        have h3 : (b * x) ^ 2 / 2 ≤ ((61 / 20 : ℝ) ^ 2 / 2) * x ^ 2 := by
          have : (b * x) ^ 2 = b ^ 2 * x ^ 2 := by ring
          nlinarith [sq_nonneg x]
        exact h1.trans h3
      have hcosh_src := two_cosh_mul_thetaCuspSourceTerm_one_le hσ hx0
      have hcos_nn : 0 ≤ 1 - Real.cos (b * x) := by linarith [Real.cos_le_one (b * x)]
      have hcosh_pos : 0 ≤ Real.exp (σ * x) + Real.exp (-σ * x) := by positivity
      calc P x * (Real.exp (σ * x) + Real.exp (-σ * x)) * (1 - Real.cos (b * x))
          ≤ ((11 / 10) * _root_.RHTower.thetaCuspSourceTerm x 1) *
              (Real.exp (σ * x) + Real.exp (-σ * x)) *
              (((61 / 20 : ℝ) ^ 2 / 2) * x ^ 2) := by
            refine mul_le_mul ?_ hcos_def hcos_nn
              (mul_nonneg (mul_nonneg (by norm_num) hsrc1_nn) hcosh_pos)
            exact mul_le_mul_of_nonneg_right hP_le hcosh_pos
        _ = (((61 / 20 : ℝ) ^ 2 / 2) * (11 / 10) * x ^ 2) *
              ((Real.exp (σ * x) + Real.exp (-σ * x)) *
                _root_.RHTower.thetaCuspSourceTerm x 1) := by ring
        _ ≤ (((61 / 20 : ℝ) ^ 2 / 2) * (11 / 10) * x ^ 2) *
              (400 * Real.exp (-Real.pi) * Real.exp (-(15 / 2) * x)) :=
            mul_le_mul_of_nonneg_left hcosh_src (by positivity)
        _ = C_top * (x ^ 2 * Real.exp (-(15 / 2) * x)) := by dsimp [C_top]; ring
    rw [MeasureTheory.integral_const_mul, integral_Ioi_sq_mul_exp_neg_fifteen_halves] at hmono
    refine hmono.trans_eq ?_
    dsimp [C_top]
    ring
  linarith

/-- Convex-pencil extension: `Re A_{N,θ}(z) ≥ (5026 / 16875) e^{-π} > 0` for all `θ ∈ [0, 1]`. -/
theorem finiteThetaShellPencil_re_ge_lowWindow (N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz_re : |z.re - 1 / 2| ≤ 9 / 8) (hz_im : |z.im| ≤ 61 / 20) :
    (5026 / 16875) * Real.exp (-Real.pi) ≤ (finiteThetaShellPencil N θ z).re := by
  unfold finiteThetaShellPencil
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  have h0 := finiteThetaAmplitude_re_ge_lowWindow N hz_re hz_im
  have h1 := finiteThetaAmplitude_re_ge_lowWindow (N + 1) hz_re hz_im
  nlinarith [hθ.1, hθ.2]

theorem finiteThetaShellPencil_re_pos_lowWindow (N : ℕ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz_re : |z.re - 1 / 2| ≤ 9 / 8) (hz_im : |z.im| ≤ 61 / 20) :
    0 < (finiteThetaShellPencil N θ z).re :=
  lt_of_lt_of_le (by positivity) (finiteThetaShellPencil_re_ge_lowWindow N hθ hz_re hz_im)

/-- Passing `N → ∞` yields the identical sectorial lower bound for `xi` on low windows. -/
theorem xi_re_ge_lowWindow {z : ℂ}
    (hz_re : |z.re - 1 / 2| ≤ 9 / 8) (hz_im : |z.im| ≤ 61 / 20) :
    (5026 / 16875) * Real.exp (-Real.pi) ≤ (_root_.RHTower.xi z).re := by
  have hz2 : |z.re| ≤ 2 := by
    rw [abs_le] at hz_re ⊢
    exact ⟨by linarith [hz_re.1], by linarith [hz_re.2]⟩
  have htend : Tendsto (fun N : ℕ => (_root_.RHTower.finiteThetaAmplitude N z).re)
      atTop (𝓝 (_root_.RHTower.xi z).re) := by
    apply (Complex.continuous_re.continuousAt.tendsto).comp
    rw [Metric.tendsto_nhds]
    intro ε hε
    let C_env := _root_.RHTower.thetaCuspIntegerTailConstant *
      _root_.RHTower.thetaAmplitudeEnvelope 2
    have hsq : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ) ^ 2) atTop atTop :=
      (Filter.tendsto_pow_atTop (by norm_num : 2 ≠ 0)).comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    have hexp : Tendsto (fun N : ℕ => C_env * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
      simpa only [Function.comp_def, pow_zero, one_mul, mul_zero] using
        ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp hsq).const_mul C_env
    filter_upwards [hexp.eventually (gt_mem_nhds hε)] with N hN
    rw [dist_eq_norm]
    exact (norm_finiteThetaAmplitude_sub_xi_le_strip N (by norm_num : (0 : ℝ) ≤ 2) hz2).trans_lt
      (by simpa only [C_env, mul_right_comm] using hN)
  exact ge_of_tendsto htend
    (Eventually.of_forall fun N => finiteThetaAmplitude_re_ge_lowWindow N hz_re hz_im)

/-- **Unconditional critical-line root existence for every integer theta prefix.**
Combining `A_N(1 / 2 + 3 i) > 0` (§3) with `A_N(1 / 2 + t i) < 0` above `thetaPrefixCuspHorizon N 0`
(§2) proves that every finite prefix `A_N` has a genuine critical-line zero `t_*(N) > 3`, ruling out
global right-half-plane sectoriality on the critical strip at large heights. -/
theorem exists_criticalLine_zero_finiteThetaAmplitude (N : ℕ) :
    ∃ t : ℝ, 3 < t ∧ _root_.RHTower.finiteThetaAmplitude N ((1 / 2 : ℂ) + (t : ℂ) * I) = 0 := by
  let f : ℝ → ℝ := fun t =>
    (_root_.RHTower.finiteThetaAmplitude N ((1 / 2 : ℂ) + (t : ℂ) * I)).re
  have hf_cont : Continuous f :=
    Complex.continuous_re.comp
      ((_root_.RHTower.differentiable_finiteThetaAmplitude N).continuous.comp
        (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)))
  set B : ℝ := max 4 (thetaPrefixCuspHorizon N 0 + 1)
  have h3B : (3 : ℝ) ≤ B := le_trans (by norm_num) (le_max_left 4 _)
  have hf3_pos : 0 < f 3 := by
    have hre : |((1 / 2 : ℂ) + ((3 : ℝ) : ℂ) * I).re - 1 / 2| ≤ 9 / 8 := by simp; norm_num
    have him : |((1 / 2 : ℂ) + ((3 : ℝ) : ℂ) * I).im| ≤ 61 / 20 := by simp; norm_num
    exact lt_of_lt_of_le (by positivity) (finiteThetaAmplitude_re_ge_lowWindow N hre him)
  have hfB_neg : f B < 0 := by
    have hB_gt : thetaPrefixCuspHorizon N 0 < |B| := by
      have hB_pos : 0 < B := lt_of_lt_of_le (by norm_num) (le_max_left 4 _)
      rw [abs_of_pos hB_pos]
      linarith [le_max_right 4 (thetaPrefixCuspHorizon N 0 + 1)]
    exact finiteThetaAmplitude_criticalLine_neg_above_horizon N hB_gt
  obtain ⟨t₀, ht₀_mem, ht₀_eq⟩ := intermediate_value_Icc' h3B hf_cont.continuousOn
    ⟨hfB_neg.le, hf3_pos.le⟩
  have ht₀_gt : 3 < t₀ := lt_of_le_of_ne ht₀_mem.1 fun h => by
    rw [← h] at ht₀_eq; exact hf3_pos.ne' ht₀_eq
  refine ⟨t₀, ht₀_gt, Complex.ext ?_ ?_⟩
  · simpa [f] using ht₀_eq
  · simpa using finiteThetaAmplitude_criticalLine_im_eq_zero N t₀

/-- **Direct all-`N`, all-stage low-window triviality of `integerThetaCollisionOperator` (`T ≤ 3`).**
For every height `T ≤ 3` (including natural windows `m ∈ {0, 1, 2, 3}`), every Zhukovsky stage
`n : ℕ`, and every prefix length `N : ℕ` (already at the single-shell prefix `N = 0`!), the
entire window contour lies strictly inside the sectorial box `Re A_N > 0`, so every contour power
sum vanishes, the Laurent loop is identically `1`, the Fredholm index is `0`, and `O(T) = 0`. -/
theorem integerThetaCollisionOperator_trivial_of_le_three {T : ℝ} (hT : T ≤ 3) (n N : ℕ) :
    (∀ r : ℕ, integerThetaWindowPowerSum T n N r = 0) ∧
    integerThetaWindowDegree T n N = 0 ∧
    integerThetaDifferencePoly T n N = 1 ∧
    integerThetaLaurentLoop T n N = 1 ∧
    HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) = 0 ∧
    _root_.RHTower.xiHorizontalCollisionCharge T = 0 := by
  let U : Set ℂ := {z : ℂ | |z.re - 1 / 2| < 9 / 8 ∧ |z.im| < 61 / 20}
  have hU_open : IsOpen U :=
    (isOpen_lt (continuous_abs.comp (Complex.continuous_re.sub continuous_const)) continuous_const).inter
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  have hsub_U : (uIcc (thetaWindowLowerLeft n).re (thetaWindowUpperRight T n).re ×ℂ
      uIcc (thetaWindowLowerLeft n).im (thetaWindowUpperRight T n).im) ⊆ U := by
    intro z hz
    rw [uIcc_of_le (thetaWindow_re_le T n), uIcc_of_le (thetaWindow_im_le T n),
      Complex.mem_reProdIm, thetaWindowLowerLeft_re, thetaWindowUpperRight_re,
      thetaWindowLowerLeft_im, thetaWindowUpperRight_im] at hz
    have hs6 : (6 : ℝ) ≤ (zhukovskyStage n : ℝ) := six_le_zhukovskyStage_real n
    have hhalf_pos : 0 < 1 / (2 * (zhukovskyStage n : ℝ)) := by positivity
    have hhalf_le : 1 / (2 * (zhukovskyStage n : ℝ)) ≤ 1 / 12 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    have hmax3 : max 0 T ≤ 3 := max_le (by norm_num) hT
    refine ⟨?_, ?_⟩
    · rw [abs_lt]; exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    · rw [abs_lt]; exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hU_nz : ∀ z ∈ U, _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
    intro z hz h0
    have hpos := lt_of_lt_of_le (by positivity)
      (finiteThetaAmplitude_re_ge_lowWindow N hz.1.le hz.2.le)
    rw [h0, Complex.zero_re] at hpos
    exact lt_irrefl 0 hpos
  have hps0 : ∀ r : ℕ, integerThetaWindowPowerSum T n N r = 0 := by
    intro r
    unfold integerThetaWindowPowerSum
    have hg_an : AnalyticOnNhd ℂ
        (fun z => z ^ r *
          (-_root_.RHTower.finiteThetaFirstMoment N z /
            _root_.RHTower.finiteThetaAmplitude N z)) U := by
      intro z hz
      have hnum : AnalyticAt ℂ (fun w => -_root_.RHTower.finiteThetaFirstMoment N w) z := by
        have heq : (fun w => -_root_.RHTower.finiteThetaFirstMoment N w) =
            deriv (_root_.RHTower.finiteThetaAmplitude N) :=
          funext fun w => (_root_.RHTower.deriv_finiteThetaAmplitude N w).symm
        rw [heq]
        exact ((analyticOnNhd_finiteThetaAmplitude N).deriv) z (Set.mem_univ z)
      exact (analyticAt_id.pow r).mul
        (hnum.div (analyticOnNhd_finiteThetaAmplitude N z (Set.mem_univ z)) (hU_nz z hz))
    rw [_root_.RHTower.rectIntegral_eq_zero_of_analyticOnNhd hsub_U hg_an, mul_zero]
  have hdeg0 : integerThetaWindowDegree T n N = 0 := by
    unfold integerThetaWindowDegree
    rw [hps0 0, Complex.zero_re, zero_add]
    exact (Nat.floor_eq_iff (by norm_num)).mpr ⟨by norm_num, by norm_num⟩
  have hpoly1 : integerThetaDifferencePoly T n N = 1 := by
    unfold integerThetaDifferencePoly pairDiffPoly newtonPoly
    rw [hdeg0]
    simp [newtonElem]
  have hbase1 : integerThetaBaseLoop T n N = 1 := by
    ext u
    change (integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u) = 1
    rw [hpoly1, Polynomial.eval_one]
  have hloop1 : integerThetaLaurentLoop T n N = 1 := by
    unfold integerThetaLaurentLoop; rw [hbase1, one_pow]
  have hsym1 : integerThetaCollisionSymbol T n N = 1 := by
    ext u
    have hnz : ∀ v : HTGeometry.UnitCircle, integerThetaLaurentLoop T n N v ≠ 0 := by
      intro v; rw [hloop1]; exact one_ne_zero
    rw [integerThetaCollisionSymbol, unitNormalizeSymbol_apply_of_ne_zero hnz, hloop1]
    simp
  have hind0 : HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) = 0 := by
    rw [fredholmIndex_integerThetaCollisionOperator_eq_circleWinding, hsym1]
    change _root_.RHTower.windingNumber (fun _ => (1 : ℂ)) 0 (2 * Real.pi) = 0
    exact _root_.RHTower.windingNumber_const one_ne_zero 0 (2 * Real.pi)
  have hcharge0 : _root_.RHTower.xiHorizontalCollisionCharge T = 0 := by
    have hno_zeros : (_root_.RHTower.stripZeros_finite T).toFinset = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun w hw => ?_
      have hw_mem := (_root_.RHTower.stripZeros_finite T).mem_toFinset.mp hw
      have hw_re : |w.re - 1 / 2| ≤ 9 / 8 := by
        rw [abs_le]; exact ⟨by linarith [hw_mem.1.1], by linarith [hw_mem.1.2.1]⟩
      have hw_im : |w.im| ≤ 61 / 20 := by
        rw [abs_le]; exact ⟨by linarith [hw_mem.1.2.2.1], by linarith [hw_mem.1.2.2.2, hT]⟩
      have hre_pos : 0 < (_root_.RHTower.xi w).re :=
        lt_of_lt_of_le (by positivity) (xi_re_ge_lowWindow hw_re hw_im)
      rw [hw_mem.2, Complex.zero_re] at hre_pos
      exact lt_irrefl 0 hre_pos
    rw [_root_.RHTower.xiHorizontalCollisionCharge_eq_sum_pairs,
      _root_.RHTower.xiHorizontalCollisionPairs, hno_zeros]
    simp
  exact ⟨hps0, hdeg0, hpoly1, hloop1, hind0, hcharge0⟩

end GaloisForLFunctions.ConjugateDiagonalGeometry

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.finiteThetaAmplitude_cusp_sectorial_above_horizon
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.finiteThetaAmplitude_strip_zeros_finite
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.finiteThetaAmplitude_strip_zeros_eq_of_gt_cuspHorizon
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.integerThetaCollisionOperator_eq_of_ge_cuspHorizon
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.finiteThetaShellPencil_re_ge_lowWindow
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.exists_criticalLine_zero_finiteThetaAmplitude
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.integerThetaCollisionOperator_trivial_of_le_three
