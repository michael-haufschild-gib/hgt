import GaloisForLFunctions.RHTower.XiBoundaryCauchyRepresentation
import GaloisForLFunctions.HTGeometry.FrullaniIntegral

/-!
# The Euler-safe observability deficit is the critical logarithmic-derivative energy

Fix a safe offset `a > 1/2` and nodes `w_j` with `Re w_j > a`.  The Euler-safe Cauchy-loss deficit

```
O_a(c, w) = ∫ h_a(t) |∑_j c_j / (w_j - a - i t)|² dt
            - 2a ∫ h_a(t) ∫_0^∞ |∑_j c_j e^{-w_j x} / (w_j - a - i t)|² dx dt
```

is exactly `π` times the energy of the critical logarithmic-derivative kernel
`K_0(w, v) = (L w + conj (L v)) / (w + conj v)`, and therefore does not depend on `a` at all.
The mechanism is the boundary Cauchy representation of the safe Carathéodory kernel together with
the half-line Laplace evaluation `∫_0^∞ e^{-(w_j + conj w_k)x} dx = (w_j + conj w_k)⁻¹`, which
converts the subtraction into the exact factor `(w_j + conj w_k - 2a)/(w_j + conj w_k)` cancelling
the safe denominator.
-/

noncomputable section

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

namespace RHTower

/-! ### The boundary density is continuous and positive -/

theorem continuous_eulerSafeDensity {a : ℝ} (ha : 1 / 2 < a) :
    Continuous fun t : ℝ => eulerSafeDensity a t := by
  have hline : Continuous fun t : ℝ => ((a : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
  refine Complex.continuous_re.comp (continuous_iff_continuousAt.mpr fun t => ?_)
  have hre : ((a : ℂ) + (t : ℂ) * Complex.I).re = a := by simp
  exact ContinuousAt.comp
    ((differentiableAt_logDeriv_xiCent (by rw [hre]; exact ha)).continuousAt) hline.continuousAt

theorem eulerSafeDensity_pos {a : ℝ} (ha : 1 / 2 < a) (t : ℝ) : 0 < eulerSafeDensity a t := by
  have hre : ((a : ℂ) + (t : ℂ) * Complex.I).re = a := by simp
  exact re_logDeriv_xiCent_pos (by rw [hre]; exact ha)

/-! ### Integrability of the density against the boundary Cauchy kernel -/

theorem summable_norm_boundaryTerm_cauchy {a : ℝ} (ha : 1 / 2 < a) (w v : ℂ) (t : ℝ) :
    Summable fun q : XiZeroCopy =>
      ‖((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t‖ := by
  refine ((summable_boundaryPoissonTerm ha t).mul_right
    ‖boundaryCauchyKernel a w v t‖).congr fun q => ?_
  have hT : 0 < boundaryPoissonTerm a t q := by
    obtain ⟨hpos, hneg⟩ := abs_im_spectral_lt ha q
    rw [boundaryPoissonTerm]
    exact add_pos (halfPlanePoisson_pos hpos _) (halfPlanePoisson_pos hneg _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]

theorem norm_density_mul_boundaryCauchy {a : ℝ} (ha : 1 / 2 < a) (w v : ℂ) (t : ℝ) :
    ‖((eulerSafeDensity a t : ℝ) : ℂ) * boundaryCauchyKernel a w v t‖
      = (Real.pi / 2) * ∑' q : XiZeroCopy,
          ‖((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t‖ := by
  have hcongr : ∀ q : XiZeroCopy,
      ‖((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t‖
        = boundaryPoissonTerm a t q * ‖boundaryCauchyKernel a w v t‖ := by
    intro q
    have hT : 0 < boundaryPoissonTerm a t q := by
      obtain ⟨hpos, hneg⟩ := abs_im_spectral_lt ha q
      rw [boundaryPoissonTerm]
      exact add_pos (halfPlanePoisson_pos hpos _) (halfPlanePoisson_pos hneg _)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
  rw [tsum_congr hcongr, tsum_mul_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (eulerSafeDensity_pos ha t), eulerSafeDensity_eq_tsum_term ha t]
  ring

theorem continuous_density_mul_boundaryCauchy {a : ℝ} (ha : 1 / 2 < a) {w v : ℂ}
    (hw : a < w.re) (hv : a < v.re) :
    Continuous fun t : ℝ =>
      ((eulerSafeDensity a t : ℝ) : ℂ) * boundaryCauchyKernel a w v t := by
  refine (Complex.continuous_ofReal.comp (continuous_eulerSafeDensity ha)).mul ?_
  unfold boundaryCauchyKernel
  exact Continuous.inv₀ (by fun_prop) fun t =>
    mul_ne_zero (sub_I_ne_zero hw t) (add_I_ne_zero hv t)

theorem integrable_density_mul_boundaryCauchy {a : ℝ} (ha : 1 / 2 < a) {w v : ℂ}
    (hw : a < w.re) (hv : a < v.re) :
    Integrable fun t : ℝ =>
      ((eulerSafeDensity a t : ℝ) : ℂ) * boundaryCauchyKernel a w v t := by
  refine ⟨(continuous_density_mul_boundaryCauchy ha hw hv).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hEq : ∀ t : ℝ, ‖((eulerSafeDensity a t : ℝ) : ℂ) * boundaryCauchyKernel a w v t‖ₑ
      = ENNReal.ofReal (Real.pi / 2)
        * ∑' q : XiZeroCopy,
            ‖((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t‖ₑ := by
    intro t
    rw [← ofReal_norm, norm_density_mul_boundaryCauchy ha w v t,
      ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_tsum_of_nonneg (fun q => norm_nonneg _)
        (summable_norm_boundaryTerm_cauchy ha w v t)]
    exact congrArg _ (tsum_congr fun q => ofReal_norm _)
  rw [MeasureTheory.lintegral_congr hEq,
    MeasureTheory.lintegral_const_mul' _ _ (by simp),
    MeasureTheory.lintegral_tsum
      (fun q => ((integrable_boundaryTerm_cauchy ha hw hv q).1).enorm),
    tsum_congr (fun q =>
      (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm
        (integrable_boundaryTerm_cauchy ha hw hv q)).symm),
    ← ENNReal.ofReal_tsum_of_nonneg
      (fun q => MeasureTheory.integral_nonneg fun t => norm_nonneg _)
      (summable_integral_norm_boundaryTerm ha hw hv)]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- The boundary Cauchy transform of the density evaluates the safe Carathéodory kernel. -/
theorem integral_density_mul_boundaryCauchy {a : ℝ} (ha : 1 / 2 < a) {w v : ℂ}
    (hw : a < w.re) (hv : a < v.re) :
    (∫ t : ℝ, ((eulerSafeDensity a t : ℝ) : ℂ) * boundaryCauchyKernel a w v t)
      = (Real.pi : ℂ) * safeCaratheodoryKernel a w v := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  rw [safeCaratheodoryKernel_eq_boundary_integral ha hw hv (add_conj_sub_ne_zero hw hv)]
  field_simp

/-! ### The finite exponential/resolvent span -/

/-- The safe resolvent amplitude `∑_j c_j / (w_j - a - i t)`. -/
def eulerSafeAmplitude (a : ℝ) {n : ℕ} (c w : Fin n → ℂ) (t : ℝ) : ℂ :=
  ∑ j, c j / (w j - (a : ℂ) - Complex.I * (t : ℂ))

/-- The tail-Laplace amplitude `∑_j c_j e^{-w_j x} / (w_j - a - i t)`. -/
def eulerSafeTailAmplitude (a : ℝ) {n : ℕ} (c w : Fin n → ℂ) (x t : ℝ) : ℂ :=
  ∑ j, c j * Complex.exp (-(w j) * (x : ℂ)) / (w j - (a : ℂ) - Complex.I * (t : ℂ))

/-- **Equation (3).**  The Euler-safe Cauchy-loss deficit of a finite node/coefficient system. -/
def eulerSafeDeficit (a : ℝ) {n : ℕ} (c w : Fin n → ℂ) : ℂ :=
  (∫ t : ℝ, ((eulerSafeDensity a t : ℝ) : ℂ)
      * (eulerSafeAmplitude a c w t * conj (eulerSafeAmplitude a c w t)))
    - 2 * (a : ℂ) * ∫ t : ℝ, ((eulerSafeDensity a t : ℝ) : ℂ)
        * ∫ x in Set.Ioi (0 : ℝ),
            eulerSafeTailAmplitude a c w x t * conj (eulerSafeTailAmplitude a c w x t)

theorem conj_node_factor (a : ℝ) (v : ℂ) (t : ℝ) :
    conj (v - (a : ℂ) - Complex.I * (t : ℂ)) = conj v - (a : ℂ) + Complex.I * (t : ℂ) := by
  simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem amplitude_mul_conj (a : ℝ) {n : ℕ} (c w : Fin n → ℂ) (t : ℝ) :
    eulerSafeAmplitude a c w t * conj (eulerSafeAmplitude a c w t)
      = ∑ j, ∑ k, c j * conj (c k) * boundaryCauchyKernel a (w j) (w k) t := by
  rw [eulerSafeAmplitude, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [map_div₀, conj_node_factor, boundaryCauchyKernel, div_mul_div_comm, div_eq_mul_inv]

theorem tailAmplitude_mul_conj (a : ℝ) {n : ℕ} (c w : Fin n → ℂ) (x t : ℝ) :
    eulerSafeTailAmplitude a c w x t * conj (eulerSafeTailAmplitude a c w x t)
      = ∑ j, ∑ k, (c j * conj (c k) * boundaryCauchyKernel a (w j) (w k) t)
          * Complex.exp (-((w j + conj (w k)) * (x : ℂ))) := by
  rw [eulerSafeTailAmplitude, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have hexp : conj (Complex.exp (-(w k) * (x : ℂ))) = Complex.exp (-(conj (w k)) * (x : ℂ)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal]
  have hprod : Complex.exp (-(w j) * (x : ℂ)) * Complex.exp (-(conj (w k)) * (x : ℂ))
      = Complex.exp (-((w j + conj (w k)) * (x : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [map_div₀, map_mul, hexp, conj_node_factor, boundaryCauchyKernel, div_mul_div_comm,
    div_eq_mul_inv, ← hprod]
  ring

/-! ### The tail-Laplace integral removes exactly the safe denominator -/

theorem integral_tailAmplitude_mul_conj {a : ℝ} {n : ℕ} (c w : Fin n → ℂ)
    (hw : ∀ j, 0 < (w j).re) (t : ℝ) :
    (∫ x in Set.Ioi (0 : ℝ),
        eulerSafeTailAmplitude a c w x t * conj (eulerSafeTailAmplitude a c w x t))
      = ∑ j, ∑ k, c j * conj (c k) * (w j + conj (w k))⁻¹
          * boundaryCauchyKernel a (w j) (w k) t := by
  have hS : ∀ j k : Fin n, 0 < (w j + conj (w k)).re := by
    intro j k
    rw [re_add_conj]
    have h1 := hw j
    have h2 := hw k
    linarith
  have hint : ∀ j k : Fin n, IntegrableOn
      (fun x : ℝ => (c j * conj (c k) * boundaryCauchyKernel a (w j) (w k) t)
        * Complex.exp (-((w j + conj (w k)) * (x : ℂ)))) (Set.Ioi (0 : ℝ)) :=
    fun j k => (integrableOn_cexp_neg_mul (hS j k)).const_mul _
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
      (fun x => tailAmplitude_mul_conj a c w x t)),
    MeasureTheory.integral_finsetSum _ (fun j _ =>
      MeasureTheory.integrable_finsetSum _ (fun k _ => hint j k))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun k _ => hint j k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MeasureTheory.integral_const_mul,
    GaloisForLFunctions.RHTower.integral_cexp_neg_mul_Ioi_zero (hS j k)]
  rw [one_div]
  ring

/-! ### The boundary transform of a finite pair sum -/

theorem integral_density_mul_pairSum {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (w : Fin n → ℂ)
    (hw : ∀ j, a < (w j).re) (d : Fin n → Fin n → ℂ) :
    (∫ t : ℝ, ((eulerSafeDensity a t : ℝ) : ℂ)
        * ∑ j, ∑ k, d j k * boundaryCauchyKernel a (w j) (w k) t)
      = ∑ j, ∑ k, d j k * ((Real.pi : ℂ) * safeCaratheodoryKernel a (w j) (w k)) := by
  have hint : ∀ j k : Fin n, Integrable fun t : ℝ =>
      d j k * (((eulerSafeDensity a t : ℝ) : ℂ) * boundaryCauchyKernel a (w j) (w k) t) :=
    fun j k => (integrable_density_mul_boundaryCauchy ha (hw j) (hw k)).const_mul _
  have hcongr : ∀ t : ℝ, ((eulerSafeDensity a t : ℝ) : ℂ)
        * ∑ j, ∑ k, d j k * boundaryCauchyKernel a (w j) (w k) t
      = ∑ j, ∑ k, d j k * (((eulerSafeDensity a t : ℝ) : ℂ)
          * boundaryCauchyKernel a (w j) (w k) t) := by
    intro t
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_finsetSum _ (fun j _ =>
      MeasureTheory.integrable_finsetSum _ (fun k _ => hint j k))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun k _ => hint j k)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [MeasureTheory.integral_const_mul, integral_density_mul_boundaryCauchy ha (hw j) (hw k)]

/-! ### Equation (4): the deficit is the critical energy -/

/-- **Equation (4).**  The Euler-safe Cauchy-loss deficit of a finite safe node/coefficient system
is `π` times the energy of the critical logarithmic-derivative kernel.  In particular it carries no
trace of the offset `a`. -/
theorem eulerSafeDeficit_eq {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (c w : Fin n → ℂ)
    (hw : ∀ j, a < (w j).re) :
    eulerSafeDeficit a c w
      = (Real.pi : ℂ) * ∑ j, ∑ k, c j * conj (c k) * criticalLogDerivKernel (w j) (w k) := by
  have hwpos : ∀ j, 0 < (w j).re := fun j => lt_trans (by linarith) (hw j)
  have hI1 : (∫ t : ℝ, ((eulerSafeDensity a t : ℝ) : ℂ)
        * (eulerSafeAmplitude a c w t * conj (eulerSafeAmplitude a c w t)))
      = ∑ j, ∑ k, (c j * conj (c k))
          * ((Real.pi : ℂ) * safeCaratheodoryKernel a (w j) (w k)) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
        (fun t => congrArg (fun z : ℂ => ((eulerSafeDensity a t : ℝ) : ℂ) * z)
          (amplitude_mul_conj a c w t))),
      integral_density_mul_pairSum ha w hw (fun j k => c j * conj (c k))]
  have hI2 : (∫ t : ℝ, ((eulerSafeDensity a t : ℝ) : ℂ)
        * ∫ x in Set.Ioi (0 : ℝ),
            eulerSafeTailAmplitude a c w x t * conj (eulerSafeTailAmplitude a c w x t))
      = ∑ j, ∑ k, (c j * conj (c k) * (w j + conj (w k))⁻¹)
          * ((Real.pi : ℂ) * safeCaratheodoryKernel a (w j) (w k)) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall
        (fun t => congrArg (fun z : ℂ => ((eulerSafeDensity a t : ℝ) : ℂ) * z)
          (integral_tailAmplitude_mul_conj c w hwpos t))),
      integral_density_mul_pairSum ha w hw
        (fun j k => c j * conj (c k) * (w j + conj (w k))⁻¹)]
  have hpair : ∀ j k : Fin n,
      (c j * conj (c k)) * ((Real.pi : ℂ) * safeCaratheodoryKernel a (w j) (w k))
        - 2 * (a : ℂ) * ((c j * conj (c k) * (w j + conj (w k))⁻¹)
            * ((Real.pi : ℂ) * safeCaratheodoryKernel a (w j) (w k)))
      = (Real.pi : ℂ) * (c j * conj (c k) * criticalLogDerivKernel (w j) (w k)) := by
    intro j k
    have hsplit := criticalLogDerivKernel_eq_sub (by linarith : (0 : ℝ) < a) (hw j) (hw k)
    rw [hsplit, cauchyLossKernel, div_eq_mul_inv]
    ring
  rw [eulerSafeDeficit, hI1, hI2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k _ => hpair j k

/-! ### Equations (15)–(16): the offset-free stationary form -/

/-- **Equation (16).**  The stationary critical form `W_Xi = O_a / (2π)` on the finite
exponential/resolvent span. -/
def xiStationaryForm {n : ℕ} (c w : Fin n → ℂ) : ℂ :=
  (1 / 2) * ∑ j, ∑ k, c j * conj (c k) * criticalLogDerivKernel (w j) (w k)

theorem xiStationaryForm_eq_deficit_div {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (c w : Fin n → ℂ)
    (hw : ∀ j, a < (w j).re) :
    xiStationaryForm c w = eulerSafeDeficit a c w / (2 * (Real.pi : ℂ)) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  rw [eulerSafeDeficit_eq ha c w hw, xiStationaryForm]
  field_simp

/-- **Equation (15).**  All safe offsets give the same deficit: the Poisson orbit `h_a` and the
Cauchy-loss subtraction cancel exactly. -/
theorem eulerSafeDeficit_offset_independent {a b : ℝ} (ha : 1 / 2 < a) (hb : 1 / 2 < b)
    {n : ℕ} (c w : Fin n → ℂ) (hwa : ∀ j, a < (w j).re) (hwb : ∀ j, b < (w j).re) :
    eulerSafeDeficit a c w = eulerSafeDeficit b c w := by
  rw [eulerSafeDeficit_eq ha c w hwa, eulerSafeDeficit_eq hb c w hwb]

/-! ### Equation (21): the exact RH chain -/

theorem eulerSafeDeficit_re_eq_kernelEnergy {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (c w : Fin n → ℂ)
    (hw : ∀ j, a < (w j).re) :
    (eulerSafeDeficit a c w).re
      = Real.pi * (kernelEnergy (fun x y : {W : ℂ // a < W.re} =>
          criticalLogDerivKernel (x : ℂ) (y : ℂ)) (fun j => conj (c j))
          (fun j => (⟨w j, hw j⟩ : {W : ℂ // a < W.re}))).re := by
  have hsum : (∑ j, ∑ k, c j * conj (c k) * criticalLogDerivKernel (w j) (w k))
      = kernelEnergy (fun x y : {W : ℂ // a < W.re} =>
          criticalLogDerivKernel (x : ℂ) (y : ℂ)) (fun j => conj (c j))
          (fun j => (⟨w j, hw j⟩ : {W : ℂ // a < W.re})) := by
    rw [kernelEnergy]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by
      rw [Complex.conj_conj]
  rw [eulerSafeDeficit_eq ha c w hw, hsum, Complex.re_ofReal_mul]

/-- **Equation (21).**  For one and hence every safe offset `a > 1/2`, the Riemann hypothesis is
equivalent to nonnegativity of the Euler-safe Cauchy-loss deficit on every finite safe
node/coefficient system. -/
theorem riemannHypothesis_iff_eulerSafeDeficit_nonneg {a : ℝ} (ha : 1 / 2 < a) :
    RiemannHypothesis ↔
      ∀ (n : ℕ) (c w : Fin n → ℂ), (∀ j, a < (w j).re) →
        0 ≤ (eulerSafeDeficit a c w).re := by
  rw [riemannHypothesis_iff_isPSDKernel_criticalLogDerivKernel ha.le,
    isPSDKernel_iff_forall_energy_nonneg (fun x y => criticalLogDerivKernel_conj_symm _ _)]
  constructor
  · intro h n c w hw
    rw [eulerSafeDeficit_re_eq_kernelEnergy ha c w hw]
    exact mul_nonneg Real.pi_pos.le (h n _ _)
  · intro h n c w
    have hnodes : ∀ j, a < ((w j : ℂ)).re := fun j => (w j).2
    have hval := h n (fun j => conj (c j)) (fun j => (w j : ℂ)) hnodes
    rw [eulerSafeDeficit_re_eq_kernelEnergy ha _ _ hnodes] at hval
    have hc : (fun j => conj (conj (c j))) = c := by
      funext j
      rw [Complex.conj_conj]
    have hw : (fun j => (⟨(w j : ℂ), hnodes j⟩ : {W : ℂ // a < W.re})) = w := by
      funext j
      exact Subtype.ext rfl
    rw [hc, hw] at hval
    exact nonneg_of_mul_nonneg_right hval Real.pi_pos

/-! ### The deficit in its real form -/

/-- **Equation (3)** as a real quantity. -/
def eulerSafeDeficitReal (a : ℝ) {n : ℕ} (c w : Fin n → ℂ) : ℝ :=
  (∫ t : ℝ, eulerSafeDensity a t * ‖eulerSafeAmplitude a c w t‖ ^ 2)
    - 2 * a * ∫ t : ℝ, eulerSafeDensity a t
        * ∫ x in Set.Ioi (0 : ℝ), ‖eulerSafeTailAmplitude a c w x t‖ ^ 2

theorem eulerSafeDeficit_eq_ofReal (a : ℝ) {n : ℕ} (c w : Fin n → ℂ) :
    eulerSafeDeficit a c w = ((eulerSafeDeficitReal a c w : ℝ) : ℂ) := by
  have h1 : ∀ t : ℝ, ((eulerSafeDensity a t : ℝ) : ℂ)
      * (eulerSafeAmplitude a c w t * conj (eulerSafeAmplitude a c w t))
      = ((eulerSafeDensity a t * ‖eulerSafeAmplitude a c w t‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [Complex.mul_conj']
    push_cast
    ring
  have h2 : ∀ t : ℝ, (∫ x in Set.Ioi (0 : ℝ),
        eulerSafeTailAmplitude a c w x t * conj (eulerSafeTailAmplitude a c w x t))
      = ((∫ x in Set.Ioi (0 : ℝ), ‖eulerSafeTailAmplitude a c w x t‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [← integral_complex_ofReal]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    dsimp only
    rw [Complex.mul_conj']
    push_cast
    ring
  have h3 : ∀ t : ℝ, ((eulerSafeDensity a t : ℝ) : ℂ)
      * ∫ x in Set.Ioi (0 : ℝ),
          eulerSafeTailAmplitude a c w x t * conj (eulerSafeTailAmplitude a c w x t)
      = ((eulerSafeDensity a t
          * ∫ x in Set.Ioi (0 : ℝ), ‖eulerSafeTailAmplitude a c w x t‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    rw [h2 t]
    push_cast
    ring
  rw [eulerSafeDeficit, eulerSafeDeficitReal,
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h1),
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h3),
    integral_complex_ofReal, integral_complex_ofReal]
  push_cast
  ring

theorem eulerSafeDeficitReal_eq_re (a : ℝ) {n : ℕ} (c w : Fin n → ℂ) :
    eulerSafeDeficitReal a c w = (eulerSafeDeficit a c w).re := by
  rw [eulerSafeDeficit_eq_ofReal, Complex.ofReal_re]

/-- **Equations (3)–(4)** in real form: the observability deficit is `π` times the real part of the
critical logarithmic-derivative energy. -/
theorem eulerSafeDeficitReal_eq {a : ℝ} (ha : 1 / 2 < a) {n : ℕ} (c w : Fin n → ℂ)
    (hw : ∀ j, a < (w j).re) :
    eulerSafeDeficitReal a c w
      = Real.pi * (∑ j, ∑ k, c j * conj (c k) * criticalLogDerivKernel (w j) (w k)).re := by
  rw [eulerSafeDeficitReal_eq_re, eulerSafeDeficit_eq ha c w hw, Complex.re_ofReal_mul]

/-- **Equation (21)** in real form. -/
theorem riemannHypothesis_iff_eulerSafeDeficitReal_nonneg {a : ℝ} (ha : 1 / 2 < a) :
    RiemannHypothesis ↔
      ∀ (n : ℕ) (c w : Fin n → ℂ), (∀ j, a < (w j).re) →
        0 ≤ eulerSafeDeficitReal a c w := by
  rw [riemannHypothesis_iff_eulerSafeDeficit_nonneg ha]
  constructor
  · exact fun h n c w hw => by rw [eulerSafeDeficitReal_eq_re]; exact h n c w hw
  · exact fun h n c w hw => by rw [← eulerSafeDeficitReal_eq_re]; exact h n c w hw

end RHTower
