import GaloisForLFunctions.HTGeometry.CaratheodoryKernelPositive
import GaloisForLFunctions.HTGeometry.PSDKernelDensity
import GaloisForLFunctions.RHTower.XiEulerSafePairedRationalCriterion
import GaloisForLFunctions.RHTower.XiShiftLoewnerCriticalGenerator
import GaloisForLFunctions.RHTower.ThetaCuspCenterMixedPublishedGrowthPriorArt
import GaloisForLFunctions.RHTower.XiProjectiveReflectionSourceTemperatureSpectrum
import GaloisForLFunctions.RHTower.WeightedLaplaceShift

/-!
# The critical logarithmic-derivative kernel is an Euler-safe Carathéodory kernel minus its
Cauchy loss

In the centred coordinate `X(W) = ξ(1/2 + W)` and `L = X'/X`, fix a safe offset `a > 1/2` and put

```
K_a (W, V) = (L W + conj (L V)) / (W + conj V - 2 a),
C_a (W, V) = 2 a / (W + conj V),
K_0 (W, V) = (L W + conj (L V)) / (W + conj V).
```

On the Euler-safe half plane `Re W > a` the logarithmic derivative has strictly positive real part,
so `K_a` is an unconditional positive Carathéodory kernel; `C_a` is the positive Cauchy kernel of
the same half plane, realized as a Laplace Gram, with unit-bounded diagonal `a / Re W < 1`.  The
exact factorization `K_a (1 - C_a) = K_0` turns positivity of the RH-deciding kernel `K_0` into the
Schur domination `K_a ∘ C_a ≤ K_a`, and both sides of that domination are separately positive
without any hypothesis on the zeros.

The domination is genuinely multi-node: for the positive-real function `w ↦ 1/(w - a)` the same
subtraction produces a two-node matrix of strictly negative determinant.
-/

noncomputable section

open Complex Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate ComplexOrder

namespace RHTower

/-! ### The centred logarithmic derivative has positive real part -/

theorem xiCent_eq_XiC (W : ℂ) : xiCent W = XiC (-Complex.I * W) := by
  rw [xiCent, XiC]
  congr 1
  have h := Complex.I_mul_I
  linear_combination W * h

theorem logDeriv_xiCent_eq (W : ℂ) :
    logDeriv xiCent W = -Complex.I * logDeriv XiC (-Complex.I * W) := by
  have hlin : HasDerivAt (fun z : ℂ => -Complex.I * z) (-Complex.I) W := by
    simpa using (hasDerivAt_id W).const_mul (-Complex.I)
  have hcomp : HasDerivAt xiCent (deriv XiC (-Complex.I * W) * (-Complex.I)) W := by
    have h := (XiC_differentiable (-Complex.I * W)).hasDerivAt.comp W hlin
    have hfun : (XiC ∘ fun z : ℂ => -Complex.I * z) = xiCent := by
      funext z
      exact (xiCent_eq_XiC z).symm
    rwa [hfun] at h
  rw [logDeriv_apply, logDeriv_apply, hcomp.deriv, xiCent_eq_XiC W]
  ring

/-- **Unconditional Euler-safe positivity.**  Beyond the critical half-width the centred
logarithmic derivative maps into the open right half plane. -/
theorem re_logDeriv_xiCent_pos {W : ℂ} (hW : 1 / 2 < W.re) :
    0 < (logDeriv xiCent W).re := by
  set z : ℂ := -Complex.I * W with hz
  have hzim : z.im = -W.re := by
    rw [hz]
    simp [Complex.mul_im]
  have hzIm : z.im < -(1 / 2 : ℝ) := by
    rw [hzim]
    linarith
  have hXi : XiC z ≠ 0 := by
    rw [hz, ← xiCent_eq_XiC]
    exact xiCent_ne_zero_of_half_lt_re hW
  have htrace := xiRelativeResolventTrace_im_pos_of_halfPlaneBound
    (by norm_num : (0 : ℝ) ≤ 1 / 2) xiZeroHalfPlaneBound_half z hzIm
  rw [logDeriv_xiCent_eq W, ← hz, logDeriv_XiC_eq_relativeResolventTrace hXi]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im,
    neg_zero, zero_mul, zero_sub]
  linarith

theorem differentiableAt_logDeriv_xiCent {W : ℂ} (hW : 1 / 2 < W.re) :
    DifferentiableAt ℂ (logDeriv xiCent) W := by
  have hne := xiCent_ne_zero_of_half_lt_re hW
  have hana := xiCent_analytic W (Set.mem_univ W)
  have hfun : logDeriv xiCent = fun z : ℂ => deriv xiCent z / xiCent z := by
    funext z
    exact logDeriv_apply _ _
  rw [hfun]
  exact DifferentiableAt.div hana.deriv.differentiableAt hana.differentiableAt hne

/-! ### The three kernels -/

/-- The Euler-safe Carathéodory kernel `K_a`. -/
def safeCaratheodoryKernel (a : ℝ) (W V : ℂ) : ℂ :=
  (logDeriv xiCent W + conj (logDeriv xiCent V)) / (W + conj V - 2 * (a : ℂ))

/-- The Cauchy loss factor `C_a`. -/
def cauchyLossKernel (a : ℝ) (W V : ℂ) : ℂ := 2 * (a : ℂ) / (W + conj V)

/-- The RH-deciding critical kernel `K_0`. -/
def criticalLogDerivKernel (W V : ℂ) : ℂ :=
  (logDeriv xiCent W + conj (logDeriv xiCent V)) / (W + conj V)

theorem re_add_conj (W V : ℂ) : (W + conj V).re = W.re + V.re := by
  simp [Complex.add_re, Complex.conj_re]

theorem add_conj_ne_zero {W V : ℂ} (hW : 0 < W.re) (hV : 0 < V.re) : W + conj V ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [re_add_conj] at this
  simp only [Complex.zero_re] at this
  linarith

theorem add_conj_sub_ne_zero {a : ℝ} {W V : ℂ} (hW : a < W.re) (hV : a < V.re) :
    W + conj V - 2 * (a : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.zero_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, re_add_conj] at this
  norm_num at this
  linarith

/-! ### Equation (4): the strictly subunit diagonal -/

theorem cauchyLossKernel_diag {a : ℝ} {W : ℂ} (hW : 0 < W.re) :
    cauchyLossKernel a W W = ((a / W.re : ℝ) : ℂ) := by
  have hsum : W + conj W = ((2 * W.re : ℝ) : ℂ) := Complex.add_conj W
  have hWne : ((W.re : ℝ) : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt hW
  rw [cauchyLossKernel, hsum]
  push_cast
  field_simp

theorem cauchyLossKernel_diag_lt_one {a : ℝ} {W : ℂ} (ha : 0 < a) (hW : a < W.re) :
    (a / W.re : ℝ) < 1 := by
  have hWpos : 0 < W.re := lt_trans ha hW
  rw [div_lt_one hWpos]
  exact hW

/-! ### Equation (6): the Laplace Gram realization of the Cauchy factor -/

theorem cauchyLossKernel_eq_laplace {a : ℝ} {W V : ℂ} (hW : 0 < W.re) (hV : 0 < V.re) :
    cauchyLossKernel a W V
      = ∫ x in Ioi (0 : ℝ), 2 * (a : ℂ) *
          (Complex.exp (-(W * (x : ℂ))) * Complex.exp (-(conj V * (x : ℂ)))) := by
  have hre : 0 < (W + conj V).re := by
    rw [re_add_conj]
    linarith
  have hcongr : ∀ x : ℝ, 2 * (a : ℂ) *
      (Complex.exp (-(W * (x : ℂ))) * Complex.exp (-(conj V * (x : ℂ))))
      = 2 * (a : ℂ) * Complex.exp (-((W + conj V) * (x : ℂ))) := by
    intro x
    rw [← Complex.exp_add]
    congr 1
    ring_nf
  have hlap := GaloisForLFunctions.RHTower.integral_cexp_neg_mul_Ioi_zero hre
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x _ => hcongr x),
    MeasureTheory.integral_const_mul, hlap, cauchyLossKernel]
  have hne : W + conj V ≠ 0 := add_conj_ne_zero hW hV
  field_simp

/-! ### Unconditional positivity of the two safe kernels -/

/-- The Euler-safe Carathéodory kernel is unconditionally positive semidefinite. -/
theorem isPSDKernel_safeCaratheodoryKernel {a : ℝ} (ha : 1 / 2 < a) :
    IsPSDKernel (fun x y : {W : ℂ // a < W.re} =>
      safeCaratheodoryKernel a (x : ℂ) (y : ℂ)) :=
  isPSDKernel_shiftedCaratheodory a
    (fun u hu => differentiableAt_logDeriv_xiCent (by linarith))
    (fun u hu => (re_logDeriv_xiCent_pos (by linarith)).le)

theorem isPSDKernel_cauchyLossKernel_halfPlane {a : ℝ} (ha : 0 ≤ a) :
    IsPSDKernel (fun x y : {W : ℂ // 0 < W.re} => cauchyLossKernel a (x : ℂ) (y : ℂ)) := by
  have hone := isPSDKernel_halfPlaneCaratheodory (F := fun _ : ℂ => (1 : ℂ))
    (fun u _ => differentiableAt_const _) (fun u _ => by norm_num)
  refine (hone.const_mul ha).congr fun x y => ?_
  rw [cauchyLossKernel]
  simp only [map_one]
  rw [mul_div_assoc']
  ring_nf

/-- The Cauchy loss factor is unconditionally positive semidefinite on the safe half plane. -/
theorem isPSDKernel_cauchyLossKernel {a : ℝ} (ha : 0 < a) :
    IsPSDKernel (fun x y : {W : ℂ // a < W.re} => cauchyLossKernel a (x : ℂ) (y : ℂ)) :=
  ((isPSDKernel_cauchyLossKernel_halfPlane ha.le).comp
    (fun x : {W : ℂ // a < W.re} => (⟨(x : ℂ), lt_trans ha x.2⟩ : {W : ℂ // 0 < W.re}))).congr
    fun _ _ => rfl

/-- **Equation (10).**  The Schur loss is unconditionally positive semidefinite. -/
theorem isPSDKernel_schurLoss {a : ℝ} (ha : 1 / 2 < a) :
    IsPSDKernel (fun x y : {W : ℂ // a < W.re} =>
      safeCaratheodoryKernel a (x : ℂ) (y : ℂ) * cauchyLossKernel a (x : ℂ) (y : ℂ)) :=
  (isPSDKernel_safeCaratheodoryKernel ha).mul (isPSDKernel_cauchyLossKernel (by linarith))

/-! ### Equations (7) and (9): the exact Cauchy-loss identity -/

theorem safeCaratheodoryKernel_mul_one_sub_cauchyLossKernel {a : ℝ} (ha : 0 < a) {W V : ℂ}
    (hW : a < W.re) (hV : a < V.re) :
    safeCaratheodoryKernel a W V * (1 - cauchyLossKernel a W V)
      = criticalLogDerivKernel W V := by
  have h0 : W + conj V ≠ 0 := add_conj_ne_zero (lt_trans ha hW) (lt_trans ha hV)
  have h1 : W + conj V - 2 * (a : ℂ) ≠ 0 := add_conj_sub_ne_zero hW hV
  rw [safeCaratheodoryKernel, cauchyLossKernel, criticalLogDerivKernel]
  field_simp

/-- **Equation (7).**  The RH-deciding kernel is the safe Carathéodory kernel minus its Schur
Cauchy loss. -/
theorem criticalLogDerivKernel_eq_sub {a : ℝ} (ha : 0 < a) {W V : ℂ}
    (hW : a < W.re) (hV : a < V.re) :
    criticalLogDerivKernel W V
      = safeCaratheodoryKernel a W V
        - safeCaratheodoryKernel a W V * cauchyLossKernel a W V := by
  rw [← safeCaratheodoryKernel_mul_one_sub_cauchyLossKernel ha hW hV]
  ring

/-! ### Equation (8): the critical kernel decides RH on every safe half plane -/

theorem riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel {a : ℝ} (ha : 1 / 2 ≤ a) :
    RiemannHypothesis ↔
      IsPSDKernel (fun x y : {W : ℂ // a < W.re} =>
        criticalLogDerivKernel (x : ℂ) (y : ℂ)) := by
  constructor
  · intro hRH
    have hgen := riemannHypothesis_iff_isPSDKernel_criticalGenerator.mp hRH
    have hcar : IsPSDKernel (fun x y : {W : ℂ // 1 / 2 < W.re} =>
        criticalLogDerivKernel (x : ℂ) (y : ℂ)) := by
      refine (hgen.const_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)).congr fun x y => ?_
      rw [xiShiftGenKernel_zero_eq, criticalLogDerivKernel]
      push_cast
      ring
    exact (hcar.comp (fun x : {W : ℂ // a < W.re} =>
      (⟨(x : ℂ), lt_of_le_of_lt ha x.2⟩ : {W : ℂ // 1 / 2 < W.re}))).congr fun x y => rfl
  · intro hPSD
    have hno := ne_zero_of_isPSDKernel_caratheodory (by linarith : (0 : ℝ) ≤ a)
      xiCent_analytic (fun W hW => xiCent_ne_zero_of_half_lt_re (lt_of_le_of_lt ha hW))
      (hPSD.congr fun x y => rfl)
    refine rh_iff_xi_ne_zero_right.mpr (fun s hs => ?_)
    have hre : 0 < (s - 1 / 2).re := by
      have hmem := mem_rightHalf.mp hs
      simp only [Complex.sub_re, Complex.div_re, Complex.one_re, Complex.one_im]
      norm_num
      linarith
    have hval := hno (s - 1 / 2) hre
    rwa [xiCent, show (1 : ℂ) / 2 + (s - 1 / 2) = s by ring] at hval

/-- **Equation (15).**  The Riemann hypothesis is exactly the Schur domination of the safe
Carathéodory kernel over its Cauchy loss. -/
theorem riemannHypothesis_iff_kernelDominates {a : ℝ} (ha : 1 / 2 < a) :
    RiemannHypothesis ↔
      IsPSDKernel (fun x y : {W : ℂ // a < W.re} =>
        safeCaratheodoryKernel a (x : ℂ) (y : ℂ)
          - safeCaratheodoryKernel a (x : ℂ) (y : ℂ) * cauchyLossKernel a (x : ℂ) (y : ℂ)) := by
  rw [riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel ha.le]
  constructor
  · exact fun h => h.congr fun x y => criticalLogDerivKernel_eq_sub (by linarith) x.2 y.2
  · exact fun h => h.congr fun x y => (criticalLogDerivKernel_eq_sub (by linarith) x.2 y.2).symm

/-- **Equations (13)–(14).**  The diagonal Fock map is a contraction exactly when the Riemann
hypothesis holds: the Schur-loss energy of every finite node/coefficient system is dominated by the
safe energy. -/
theorem riemannHypothesis_iff_energy_le {a : ℝ} (ha : 1 / 2 < a) :
    RiemannHypothesis ↔
      ∀ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → {W : ℂ // a < W.re}),
        (kernelEnergy (fun x y : {W : ℂ // a < W.re} =>
            safeCaratheodoryKernel a (x : ℂ) (y : ℂ)
              * cauchyLossKernel a (x : ℂ) (y : ℂ)) c w).re
          ≤ (kernelEnergy (fun x y : {W : ℂ // a < W.re} =>
            safeCaratheodoryKernel a (x : ℂ) (y : ℂ)) c w).re := by
  rw [riemannHypothesis_iff_kernelDominates ha]
  exact isPSDKernel_sub_iff_forall_energy_le (isPSDKernel_safeCaratheodoryKernel ha)
    (isPSDKernel_schurLoss ha)

/-! ### The domination is not generic positivity -/

/-- The Carathéodory kernel of the model positive-real function `w ↦ 1 / (w - a)`. -/
def modelCaratheodoryKernel (a : ℝ) (W V : ℂ) : ℂ :=
  1 / ((W - (a : ℂ)) * (conj V - (a : ℂ)))

theorem sub_ofReal_ne_zero {a : ℝ} {W : ℂ} (hW : a < W.re) : W - (a : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.zero_re] at hre
  linarith

theorem conj_sub_ofReal_ne_zero {a : ℝ} {V : ℂ} (hV : a < V.re) : conj V - (a : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp only [Complex.sub_re, Complex.conj_re, Complex.ofReal_re, Complex.zero_re] at hre
  linarith

/-- **Equation (23).**  The model function is positive real on the safe half plane and its
Carathéodory kernel is the rank-one resolvent kernel. -/
theorem modelCaratheodoryKernel_eq {a : ℝ} {W V : ℂ} (hW : a < W.re) (hV : a < V.re) :
    (1 / (W - (a : ℂ)) + conj (1 / (V - (a : ℂ)))) / (W + conj V - 2 * (a : ℂ))
      = modelCaratheodoryKernel a W V := by
  have hWa : W - (a : ℂ) ≠ 0 := sub_ofReal_ne_zero hW
  have hVa : conj V - (a : ℂ) ≠ 0 := conj_sub_ofReal_ne_zero hV
  have hs : W + conj V - 2 * (a : ℂ) ≠ 0 := add_conj_sub_ne_zero hW hV
  have hnum : (1 / (W - (a : ℂ)) + conj (1 / (V - (a : ℂ))))
      = (W + conj V - 2 * (a : ℂ)) / ((W - (a : ℂ)) * (conj V - (a : ℂ))) := by
    rw [map_div₀, map_one, map_sub, Complex.conj_ofReal]
    field_simp
    ring
  rw [hnum, modelCaratheodoryKernel, div_div,
    mul_comm ((W - (a : ℂ)) * (conj V - (a : ℂ))) (W + conj V - 2 * (a : ℂ)), ← div_div,
    div_self hs]

/-- The two-node symbol `S_a` of the subtracted model kernel. -/
def modelLossSymbol (a x y : ℝ) : ℝ := 1 - 2 * a / (x + y)

/-- **Equation (25).**  The two-node determinant of the model symbol. -/
theorem det_modelLossSymbol {a x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    modelLossSymbol a x x * modelLossSymbol a y y
        - modelLossSymbol a x y * modelLossSymbol a y x
      = -(a * (x + y - a) * (x - y) ^ (2 : ℕ)) / (x * y * (x + y) ^ (2 : ℕ)) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hxy : x + y ≠ 0 := ne_of_gt (by linarith)
  rw [modelLossSymbol, modelLossSymbol, modelLossSymbol, modelLossSymbol]
  field_simp
  ring

theorem det_modelLossSymbol_neg {a x y : ℝ} (ha : 0 < a) (hx : a < x) (hy : a < y)
    (hne : x ≠ y) :
    modelLossSymbol a x x * modelLossSymbol a y y
      - modelLossSymbol a x y * modelLossSymbol a y x < 0 := by
  have hx0 : 0 < x := lt_trans ha hx
  have hy0 : 0 < y := lt_trans ha hy
  rw [det_modelLossSymbol hx0 hy0]
  have hd : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hnum : 0 < a * (x + y - a) * (x - y) ^ (2 : ℕ) := by
    have h1 : 0 < x + y - a := by linarith
    positivity
  have hden : 0 < x * y * (x + y) ^ (2 : ℕ) := by positivity
  exact div_neg_of_neg_of_pos (by linarith) hden

/-- **The generic positive-real shortcut fails.**  The Carathéodory kernel of `w ↦ 1 / (w - a)` is
unconditionally positive and its Cauchy factor is strictly subunit on the diagonal, yet the
subtracted kernel is not positive semidefinite. -/
theorem not_isPSDKernel_modelLoss {a : ℝ} (ha : 0 < a) :
    ¬ IsPSDKernel (fun x y : {W : ℂ // a < W.re} =>
        modelCaratheodoryKernel a (x : ℂ) (y : ℂ)
          - modelCaratheodoryKernel a (x : ℂ) (y : ℂ) * cauchyLossKernel a (x : ℂ) (y : ℂ)) := by
  intro hPSD
  have hane : (a : ℂ) ≠ 0 := by
    simp only [Ne, Complex.ofReal_eq_zero]
    exact ne_of_gt ha
  have h2 : a < (((2 * a : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith
  have h3 : a < (((3 * a : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith
  set w : Fin 2 → {W : ℂ // a < W.re} :=
    ![⟨((2 * a : ℝ) : ℂ), h2⟩, ⟨((3 * a : ℝ) : ℂ), h3⟩] with hw
  set c : Fin 2 → ℂ := ![((3 : ℝ) : ℂ), ((-5 : ℝ) : ℂ)] with hc
  have hnn := (hPSD.posSemidef w).dotProduct_mulVec_nonneg c
  have hrw := dotProduct_mulVec_kernelMatrix
    (fun x y : {W : ℂ // a < W.re} => modelCaratheodoryKernel a (x : ℂ) (y : ℂ)
      - modelCaratheodoryKernel a (x : ℂ) (y : ℂ) * cauchyLossKernel a (x : ℂ) (y : ℂ)) c w
  rw [hrw, kernelEnergy] at hnn
  have hval : ∀ u v : ℝ, a < u → a < v →
      modelCaratheodoryKernel a ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
        - modelCaratheodoryKernel a ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
          * cauchyLossKernel a ((u : ℝ) : ℂ) ((v : ℝ) : ℂ)
      = ((1 - 2 * a / (u + v)) / ((u - a) * (v - a)) : ℝ) := by
    intro u v hu hv
    have hu0 : (u : ℂ) - (a : ℂ) ≠ 0 := by
      simp only [Ne, sub_eq_zero, Complex.ofReal_inj]
      exact ne_of_gt hu
    have hv0 : (v : ℂ) - (a : ℂ) ≠ 0 := by
      simp only [Ne, sub_eq_zero, Complex.ofReal_inj]
      exact ne_of_gt hv
    have huv : (u : ℂ) + (v : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_add]
      simp only [Ne, Complex.ofReal_eq_zero]
      exact ne_of_gt (by linarith)
    rw [modelCaratheodoryKernel, cauchyLossKernel, Complex.conj_ofReal]
    push_cast
    field_simp
  simp only [hw, hc, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Complex.conj_ofReal] at hnn
  rw [hval (2 * a) (2 * a) (by linarith) (by linarith),
    hval (2 * a) (3 * a) (by linarith) (by linarith),
    hval (3 * a) (2 * a) (by linarith) (by linarith),
    hval (3 * a) (3 * a) (by linarith) (by linarith)] at hnn
  rw [show ((3 : ℝ) : ℂ) * ((3 : ℝ) : ℂ) *
        (((1 - 2 * a / (2 * a + 2 * a)) / ((2 * a - a) * (2 * a - a)) : ℝ) : ℂ)
      + ((3 : ℝ) : ℂ) * ((-5 : ℝ) : ℂ) *
        (((1 - 2 * a / (2 * a + 3 * a)) / ((2 * a - a) * (3 * a - a)) : ℝ) : ℂ)
      + (((-5 : ℝ) : ℂ) * ((3 : ℝ) : ℂ) *
        (((1 - 2 * a / (3 * a + 2 * a)) / ((3 * a - a) * (2 * a - a)) : ℝ) : ℂ)
      + ((-5 : ℝ) : ℂ) * ((-5 : ℝ) : ℂ) *
        (((1 - 2 * a / (3 * a + 3 * a)) / ((3 * a - a) * (3 * a - a)) : ℝ) : ℂ))
      = ((-(1 / (3 * a ^ (2 : ℕ))) : ℝ) : ℂ) by push_cast; field_simp; ring] at hnn
  rw [Complex.zero_le_real] at hnn
  have hpos : 0 < 1 / (3 * a ^ (2 : ℕ)) := by positivity
  linarith

/-! ### Countable rational test family -/

theorem countable_gaussianRationalSet : gaussianRationalSet.Countable := by
  have hrange : gaussianRationalSet
      = Set.range fun q : ℚ × ℚ => ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I) := by
    ext z
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨(u, v), rfl⟩
    · rintro ⟨⟨u, v⟩, rfl⟩
      exact ⟨u, v, rfl⟩
  rw [hrange]
  exact Set.countable_range _

/-- The Gaussian-rational points of a safe half plane are dense in it. -/
theorem dense_safeGaussianRational {a : ℝ} :
    Dense {x : {W : ℂ // a < W.re} | (x : ℂ) ∈ gaussianRationalSet} := by
  rw [Metric.dense_iff]
  intro x r hr
  have hxa : a < (x : ℂ).re := x.2
  have hdpos : 0 < min r ((x : ℂ).re - a) := lt_min hr (by linarith)
  obtain ⟨z, hz1, hz2⟩ :=
    Metric.dense_iff.mp dense_gaussianRationalSet (x : ℂ) (min r ((x : ℂ).re - a)) hdpos
  have hzd : dist z (x : ℂ) < min r ((x : ℂ).re - a) := Metric.mem_ball.mp hz1
  have hzre : a < z.re := by
    have hle : |z.re - (x : ℂ).re| ≤ dist z (x : ℂ) := by
      rw [Complex.dist_eq]
      have hb := Complex.abs_re_le_norm (z - (x : ℂ))
      simpa [Complex.sub_re] using hb
    have h2 : dist z (x : ℂ) < (x : ℂ).re - a := lt_of_lt_of_le hzd (min_le_right _ _)
    have h4 := abs_lt.mp (lt_of_le_of_lt hle h2)
    linarith [h4.1]
  refine ⟨⟨z, hzre⟩, ?_, hz2⟩
  rw [Metric.mem_ball, Subtype.dist_eq]
  exact lt_of_lt_of_le hzd (min_le_left _ _)

/-! ### Continuity of the two safe kernels -/

theorem continuous_logDeriv_xiCent_subtype {a : ℝ} (ha : 1 / 2 < a) :
    Continuous fun x : {W : ℂ // a < W.re} => logDeriv xiCent (x : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact ContinuousAt.comp (x := x)
    ((differentiableAt_logDeriv_xiCent (lt_trans ha x.2)).continuousAt)
    continuous_subtype_val.continuousAt

theorem continuous_safeCaratheodoryKernel {a : ℝ} (ha : 1 / 2 < a) :
    Continuous fun p : {W : ℂ // a < W.re} × {W : ℂ // a < W.re} =>
      safeCaratheodoryKernel a (p.1 : ℂ) (p.2 : ℂ) := by
  have hL := continuous_logDeriv_xiCent_subtype ha
  have hnum : Continuous fun p : {W : ℂ // a < W.re} × {W : ℂ // a < W.re} =>
      logDeriv xiCent (p.1 : ℂ) + conj (logDeriv xiCent (p.2 : ℂ)) :=
    (hL.comp continuous_fst).add (Complex.continuous_conj.comp (hL.comp continuous_snd))
  have hden : Continuous fun p : {W : ℂ // a < W.re} × {W : ℂ // a < W.re} =>
      (p.1 : ℂ) + conj (p.2 : ℂ) - 2 * (a : ℂ) :=
    ((continuous_subtype_val.comp continuous_fst).add
      (Complex.continuous_conj.comp (continuous_subtype_val.comp continuous_snd))).sub
      continuous_const
  exact hnum.div hden (fun p => add_conj_sub_ne_zero p.1.2 p.2.2)

theorem continuous_cauchyLossKernel {a : ℝ} (ha : 0 < a) :
    Continuous fun p : {W : ℂ // a < W.re} × {W : ℂ // a < W.re} =>
      cauchyLossKernel a (p.1 : ℂ) (p.2 : ℂ) := by
  have hden : Continuous fun p : {W : ℂ // a < W.re} × {W : ℂ // a < W.re} =>
      (p.1 : ℂ) + conj (p.2 : ℂ) :=
    (continuous_subtype_val.comp continuous_fst).add
      (Complex.continuous_conj.comp (continuous_subtype_val.comp continuous_snd))
  exact continuous_const.div hden
    (fun p => add_conj_ne_zero (lt_trans ha p.1.2) (lt_trans ha p.2.2))

/-- **Equation (21).**  It is enough to test the Schur domination on Gaussian-rational nodes and
coefficients, a countable family of finite absolute-Euler value inequalities. -/
theorem riemannHypothesis_iff_rational_energy_le {a : ℝ} (ha : 1 / 2 < a) :
    RiemannHypothesis ↔
      ∀ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → {W : ℂ // a < W.re}),
        (∀ j, c j ∈ gaussianRationalSet) → (∀ j, ((w j : ℂ)) ∈ gaussianRationalSet) →
        (kernelEnergy (fun x y : {W : ℂ // a < W.re} =>
            safeCaratheodoryKernel a (x : ℂ) (y : ℂ)
              * cauchyLossKernel a (x : ℂ) (y : ℂ)) c w).re
          ≤ (kernelEnergy (fun x y : {W : ℂ // a < W.re} =>
            safeCaratheodoryKernel a (x : ℂ) (y : ℂ)) c w).re := by
  constructor
  · intro hRH n c w _ _
    exact (riemannHypothesis_iff_energy_le ha).mp hRH n c w
  · intro hrat
    refine (riemannHypothesis_iff_kernelDominates ha).mpr ?_
    refine isPSDKernel_of_dense_energy (fun x y => ?_) ?_ dense_gaussianRationalSet
      dense_safeGaussianRational (fun n c w hc hw => ?_)
    · have h₁ := (isPSDKernel_safeCaratheodoryKernel ha).conj_symm x y
      have h₂ := (isPSDKernel_schurLoss ha).conj_symm x y
      rw [map_sub, h₁, h₂]
    · exact (continuous_safeCaratheodoryKernel ha).sub
        ((continuous_safeCaratheodoryKernel ha).mul (continuous_cauchyLossKernel (by linarith)))
    · have hsplit := kernelEnergy_sub
        (fun x y : {W : ℂ // a < W.re} => safeCaratheodoryKernel a (x : ℂ) (y : ℂ))
        (fun x y : {W : ℂ // a < W.re} => safeCaratheodoryKernel a (x : ℂ) (y : ℂ)
          * cauchyLossKernel a (x : ℂ) (y : ℂ)) c w
      rw [hsplit, Complex.sub_re]
      have hle := hrat n c w hc hw
      linarith

end RHTower
