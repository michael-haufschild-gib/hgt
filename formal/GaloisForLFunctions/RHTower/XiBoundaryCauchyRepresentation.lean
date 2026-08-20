import GaloisForLFunctions.HTGeometry.PoissonCauchyIntegral
import GaloisForLFunctions.RHTower.XiBoundaryPoissonDensity

/-!
# The boundary Cauchy representation of the Euler-safe Carathéodory kernel

On the absolute-Euler line `Re w = a > 1/2` the Carathéodory kernel of the completed logarithmic
derivative is the boundary Cauchy transform of its own density:

`K_a (w, v) = (1/pi) integral h_a(t) / ((w - a - i t)(conj v - a + i t)) dt`.

The proof is the divisor expansion of `h_a` into Poisson kernels, the constant-sum split
`((A - it)(B + it))⁻¹ = S⁻¹ [(A - it)⁻¹ + (B + it)⁻¹]` with `S = A + B` free of `t`, and the
Poisson--Cauchy evaluation `∫ P_c (u) (A - i u)⁻¹ du = (A + c)⁻¹` applied term by term.  The
interchange is legitimate because the arithmetic-geometric bound
`‖(A-it)⁻¹ (B+it)⁻¹‖ ≤ (1/2)[‖(A-it)⁻¹‖² + ‖(B+it)⁻¹‖²]` turns each dominating integral back into a
boundary Poisson term at the raised heights `a + Re A` and `a + Re B`.
-/

noncomputable section

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

namespace RHTower

/-! ### The shifted Poisson--Cauchy evaluation -/

theorem re_sub_I_ofReal (A : ℂ) (r : ℝ) : (A - Complex.I * (r : ℂ)).re = A.re := by
  simp

theorem integral_poisson_cauchy_shift {c : ℝ} (hc : 0 < c) {A : ℂ} (hA : 0 < A.re) (r : ℝ) :
    (∫ t : ℝ, ((halfPlanePoisson c (t - r) : ℝ) : ℂ) * (A - Complex.I * (t : ℂ))⁻¹)
      = (A - Complex.I * (r : ℂ) + (c : ℂ))⁻¹ := by
  have hshift : (∫ u : ℝ, ((halfPlanePoisson c ((u + r) - r) : ℝ) : ℂ)
        * (A - Complex.I * (((u + r : ℝ)) : ℂ))⁻¹)
      = ∫ t : ℝ, ((halfPlanePoisson c (t - r) : ℝ) : ℂ) * (A - Complex.I * (t : ℂ))⁻¹ :=
    MeasureTheory.integral_add_right_eq_self
      (fun t : ℝ => ((halfPlanePoisson c (t - r) : ℝ) : ℂ) * (A - Complex.I * (t : ℂ))⁻¹) r
  rw [← hshift]
  have hcongr : ∀ u : ℝ, ((halfPlanePoisson c ((u + r) - r) : ℝ) : ℂ)
      * (A - Complex.I * (((u + r : ℝ)) : ℂ))⁻¹
      = ((halfPlanePoisson c u : ℝ) : ℂ)
        * ((A - Complex.I * (r : ℂ)) - Complex.I * (u : ℂ))⁻¹ := by
    intro u
    have h1 : (u + r) - r = u := by ring
    have h2 : (A - Complex.I * (((u + r : ℝ)) : ℂ))
        = (A - Complex.I * (r : ℂ)) - Complex.I * (u : ℂ) := by
      push_cast
      ring
    rw [h1, h2]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr)]
  exact integral_poisson_cauchy hc (by rwa [re_sub_I_ofReal])

theorem integral_poisson_cauchy_shift_conj {c : ℝ} (hc : 0 < c) {B : ℂ} (hB : 0 < B.re) (r : ℝ) :
    (∫ t : ℝ, ((halfPlanePoisson c (t - r) : ℝ) : ℂ) * (B + Complex.I * (t : ℂ))⁻¹)
      = (B + Complex.I * (r : ℂ) + (c : ℂ))⁻¹ := by
  have hconjB : 0 < (conj B).re := by
    rwa [Complex.conj_re]
  have hbase := integral_poisson_cauchy_shift hc hconjB r
  have hcongr : ∀ t : ℝ, conj (((halfPlanePoisson c (t - r) : ℝ) : ℂ)
      * (conj B - Complex.I * (t : ℂ))⁻¹)
      = ((halfPlanePoisson c (t - r) : ℝ) : ℂ) * (B + Complex.I * (t : ℂ))⁻¹ := by
    intro t
    rw [map_mul, Complex.conj_ofReal, map_inv₀, map_sub, map_mul, Complex.conj_I,
      Complex.conj_conj, Complex.conj_ofReal]
    ring_nf
  rw [← MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    integral_conj, hbase, map_inv₀]
  congr 1
  simp only [map_add, map_sub, map_mul, Complex.conj_I, Complex.conj_conj, Complex.conj_ofReal]
  ring

/-! ### The product kernel and its constant-sum split -/

/-- The Cauchy product kernel of the boundary observability integral. -/
def boundaryCauchyKernel (a : ℝ) (w v : ℂ) (t : ℝ) : ℂ :=
  ((w - (a : ℂ) - Complex.I * (t : ℂ)) * (conj v - (a : ℂ) + Complex.I * (t : ℂ)))⁻¹

theorem re_node_offset {a : ℝ} {w : ℂ} (hw : a < w.re) : 0 < (w - (a : ℂ)).re := by
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

theorem re_conj_node_offset {a : ℝ} {v : ℂ} (hv : a < v.re) : 0 < (conj v - (a : ℂ)).re := by
  simp only [Complex.sub_re, Complex.conj_re, Complex.ofReal_re]
  linarith

theorem sub_I_ne_zero {a : ℝ} {w : ℂ} (hw : a < w.re) (t : ℝ) :
    w - (a : ℂ) - Complex.I * (t : ℂ) ≠ 0 := by
  intro h
  have := re_node_offset hw
  have hre : (w - (a : ℂ) - Complex.I * (t : ℂ)).re = (w - (a : ℂ)).re := re_sub_I_ofReal _ t
  rw [h, Complex.zero_re] at hre
  linarith [hre ▸ this]

theorem add_I_ne_zero {a : ℝ} {v : ℂ} (hv : a < v.re) (t : ℝ) :
    conj v - (a : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
  intro h
  have hpos := re_conj_node_offset hv
  have hre : (conj v - (a : ℂ) + Complex.I * (t : ℂ)).re = (conj v - (a : ℂ)).re := by
    simp
  rw [h, Complex.zero_re] at hre
  linarith [hre ▸ hpos]

theorem boundaryCauchyKernel_split {a : ℝ} {w v : ℂ} (hw : a < w.re) (hv : a < v.re)
    (hS : w + conj v - 2 * (a : ℂ) ≠ 0) (t : ℝ) :
    boundaryCauchyKernel a w v t
      = (w + conj v - 2 * (a : ℂ))⁻¹
        * ((w - (a : ℂ) - Complex.I * (t : ℂ))⁻¹
          + (conj v - (a : ℂ) + Complex.I * (t : ℂ))⁻¹) := by
  have h1 := sub_I_ne_zero hw t
  have h2 := add_I_ne_zero hv t
  have hSform : w + conj v - 2 * (a : ℂ)
      = (w - (a : ℂ) - Complex.I * (t : ℂ)) + (conj v - (a : ℂ) + Complex.I * (t : ℂ)) := by
    ring
  have hSne : (w - (a : ℂ) - Complex.I * (t : ℂ))
      + (conj v - (a : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    rw [← hSform]
    exact hS
  rw [boundaryCauchyKernel, hSform]
  field_simp
  ring

/-! ### The dominating bound -/

theorem norm_inv_sub_I_sq (A : ℂ) (t : ℝ) :
    ‖(A - Complex.I * (t : ℂ))⁻¹‖ ^ 2 = (A.re ^ 2 + (t - A.im) ^ 2)⁻¹ := by
  rw [norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq, normSq_sub_I_mul_real]

theorem normSq_add_I_mul_real (B : ℂ) (t : ℝ) :
    Complex.normSq (B + Complex.I * (t : ℂ)) = B.re ^ 2 + (t + B.im) ^ 2 := by
  have hre : (B + Complex.I * (t : ℂ)).re = B.re := by simp
  have him : (B + Complex.I * (t : ℂ)).im = B.im + t := by simp
  rw [Complex.normSq_apply, hre, him]
  ring

theorem norm_inv_add_I_sq (B : ℂ) (t : ℝ) :
    ‖(B + Complex.I * (t : ℂ))⁻¹‖ ^ 2 = (B.re ^ 2 + (t + B.im) ^ 2)⁻¹ := by
  rw [norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq, normSq_add_I_mul_real]

theorem norm_boundaryCauchyKernel_le {a : ℝ} (w v : ℂ) (t : ℝ) :
    ‖boundaryCauchyKernel a w v t‖
      ≤ (1 / 2) * (((w.re - a) ^ 2 + (t - w.im) ^ 2)⁻¹
        + ((v.re - a) ^ 2 + (t - v.im) ^ 2)⁻¹) := by
  have hAeq : w - (a : ℂ) - Complex.I * (t : ℂ) = (w - (a : ℂ)) - Complex.I * (t : ℂ) := by ring
  have hBeq : conj v - (a : ℂ) + Complex.I * (t : ℂ)
      = (conj v - (a : ℂ)) + Complex.I * (t : ℂ) := by ring
  have h1 := norm_inv_sub_I_sq (w - (a : ℂ)) t
  have h2 := norm_inv_add_I_sq (conj v - (a : ℂ)) t
  have hre1 : (w - (a : ℂ)).re = w.re - a := by simp
  have him1 : (w - (a : ℂ)).im = w.im := by simp
  have hre2 : (conj v - (a : ℂ)).re = v.re - a := by simp
  have him2 : (conj v - (a : ℂ)).im = -v.im := by simp
  rw [hre1, him1] at h1
  rw [hre2, him2] at h2
  have hshift : t + -v.im = t - v.im := by ring
  rw [hshift] at h2
  rw [boundaryCauchyKernel, hAeq, hBeq, mul_inv, norm_mul]
  nlinarith [norm_nonneg ((w - (a : ℂ)) - Complex.I * (t : ℂ))⁻¹,
    norm_nonneg ((conj v - (a : ℂ)) + Complex.I * (t : ℂ))⁻¹,
    sq_nonneg (‖((w - (a : ℂ)) - Complex.I * (t : ℂ))⁻¹‖
      - ‖((conj v - (a : ℂ)) + Complex.I * (t : ℂ))⁻¹‖)]

theorem inv_sq_add_sq_eq_poisson {p : ℝ} (hp : 0 < p) (x : ℝ) :
    (p ^ 2 + x ^ 2)⁻¹ = (Real.pi / p) * halfPlanePoisson p x := by
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hden : (0 : ℝ) < p ^ 2 + x ^ 2 := by positivity
  rw [halfPlanePoisson]
  field_simp

/-! ### The divisor-term integrals -/

theorem halfPlanePoisson_even (d x : ℝ) : halfPlanePoisson d (-x) = halfPlanePoisson d x := by
  rw [halfPlanePoisson, halfPlanePoisson]
  congr 2
  ring

theorem integral_poisson_product_pair {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (r m : ℝ) :
    (∫ t : ℝ, halfPlanePoisson c (t - r) * halfPlanePoisson p (t - m))
      = halfPlanePoisson (c + p) (r - m) := by
  have hcongr : ∀ t : ℝ, halfPlanePoisson c (t - r) * halfPlanePoisson p (t - m)
      = halfPlanePoisson c (r - t) * halfPlanePoisson p (t - m) := by
    intro t
    congr 1
    rw [← halfPlanePoisson_even c (t - r)]
    congr 1
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    integral_poisson_shift_product hc hp r m]

theorem integrable_poisson_product_pair {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (r m : ℝ) :
    Integrable fun t : ℝ => halfPlanePoisson c (t - r) * halfPlanePoisson p (t - m) := by
  refine (integrable_poisson_shift_product hc hp r m).congr
    (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  congr 1
  rw [← halfPlanePoisson_even c (r - t)]
  congr 1
  ring

theorem integral_boundaryPoissonTerm_mul_poisson {a p : ℝ} (ha : 1 / 2 < a) (hp : 0 < p)
    (m : ℝ) (q : XiZeroCopy) :
    (∫ t : ℝ, boundaryPoissonTerm a t q * halfPlanePoisson p (t - m))
      = boundaryPoissonTerm (a + p) m q := by
  obtain ⟨hpos, hneg⟩ := abs_im_spectral_lt ha q
  have hcongr : ∀ t : ℝ, boundaryPoissonTerm a t q * halfPlanePoisson p (t - m)
      = halfPlanePoisson (a + (xiSpectralPoint q).im) (t - (xiSpectralPoint q).re)
          * halfPlanePoisson p (t - m)
        + halfPlanePoisson (a - (xiSpectralPoint q).im) (t - (-(xiSpectralPoint q).re))
          * halfPlanePoisson p (t - m) := by
    intro t
    rw [boundaryPoissonTerm]
    have h : t - (-(xiSpectralPoint q).re) = t + (xiSpectralPoint q).re := by ring
    rw [h]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hcongr),
    MeasureTheory.integral_add (integrable_poisson_product_pair hpos hp _ m)
      (integrable_poisson_product_pair hneg hp _ m),
    integral_poisson_product_pair hpos hp _ m, integral_poisson_product_pair hneg hp _ m,
    boundaryPoissonTerm]
  have e1 : a + (xiSpectralPoint q).im + p = a + p + (xiSpectralPoint q).im := by ring
  have e2 : a - (xiSpectralPoint q).im + p = a + p - (xiSpectralPoint q).im := by ring
  rw [e1, e2]
  congr 1
  · rw [← halfPlanePoisson_even (a + p + (xiSpectralPoint q).im) (m - (xiSpectralPoint q).re)]
    congr 1
    ring
  · rw [← halfPlanePoisson_even (a + p - (xiSpectralPoint q).im) (m + (xiSpectralPoint q).re)]
    congr 1
    ring

/-! ### Integrability of the divisor terms against the Cauchy kernel -/

theorem norm_inv_add_I_mul_real_le {B : ℂ} (hB : 0 < B.re) (t : ℝ) :
    ‖(B + Complex.I * (t : ℂ))⁻¹‖ ≤ 1 / B.re := by
  have hre : (B + Complex.I * (t : ℂ)).re = B.re := by simp
  have hge : B.re ≤ ‖B + Complex.I * (t : ℂ)‖ := by
    have := Complex.re_le_norm (B + Complex.I * (t : ℂ))
    rwa [hre] at this
  rw [norm_inv, inv_eq_one_div]
  exact one_div_le_one_div_of_le hB hge

theorem integrable_poisson_cauchy_shiftL {c : ℝ} (hc : 0 < c) {A : ℂ} (hA : 0 < A.re) (r : ℝ) :
    Integrable fun t : ℝ =>
      ((halfPlanePoisson c (t - r) : ℝ) : ℂ) * (A - Complex.I * (t : ℂ))⁻¹ := by
  have hne : ∀ t : ℝ, A - Complex.I * (t : ℂ) ≠ 0 := by
    intro t h
    have hre : (A - Complex.I * (t : ℂ)).re = A.re := re_sub_I_ofReal A t
    rw [h, Complex.zero_re] at hre
    linarith [hre ▸ hA]
  have hcont : Continuous fun t : ℝ =>
      ((halfPlanePoisson c (t - r) : ℝ) : ℂ) * (A - Complex.I * (t : ℂ))⁻¹ :=
    (Complex.continuous_ofReal.comp ((continuous_halfPlanePoisson hc).comp (by fun_prop))).mul
      (Continuous.inv₀ (by fun_prop) hne)
  refine ((((integrable_halfPlanePoisson hc).comp_sub_right r)).const_mul (1 / A.re)).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hp := halfPlanePoisson_pos hc (t - r)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, mul_comm (1 / A.re)]
  exact mul_le_mul_of_nonneg_left (norm_inv_sub_I_mul_real_le hA t) (le_of_lt hp)

theorem integrable_poisson_cauchy_shiftR {c : ℝ} (hc : 0 < c) {B : ℂ} (hB : 0 < B.re) (r : ℝ) :
    Integrable fun t : ℝ =>
      ((halfPlanePoisson c (t - r) : ℝ) : ℂ) * (B + Complex.I * (t : ℂ))⁻¹ := by
  have hne : ∀ t : ℝ, B + Complex.I * (t : ℂ) ≠ 0 := by
    intro t h
    have hre : (B + Complex.I * (t : ℂ)).re = B.re := by simp
    rw [h, Complex.zero_re] at hre
    linarith [hre ▸ hB]
  have hcont : Continuous fun t : ℝ =>
      ((halfPlanePoisson c (t - r) : ℝ) : ℂ) * (B + Complex.I * (t : ℂ))⁻¹ :=
    (Complex.continuous_ofReal.comp ((continuous_halfPlanePoisson hc).comp (by fun_prop))).mul
      (Continuous.inv₀ (by fun_prop) hne)
  refine ((((integrable_halfPlanePoisson hc).comp_sub_right r)).const_mul (1 / B.re)).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hp := halfPlanePoisson_pos hc (t - r)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp, mul_comm (1 / B.re)]
  exact mul_le_mul_of_nonneg_left (norm_inv_add_I_mul_real_le hB t) (le_of_lt hp)

theorem norm_boundaryCauchyKernel_le_const {a : ℝ} {w v : ℂ} (hw : a < w.re) (hv : a < v.re)
    (t : ℝ) :
    ‖boundaryCauchyKernel a w v t‖ ≤ (1 / (w - (a : ℂ)).re) * (1 / (conj v - (a : ℂ)).re) := by
  have hAeq : w - (a : ℂ) - Complex.I * (t : ℂ) = (w - (a : ℂ)) - Complex.I * (t : ℂ) := by ring
  have hBeq : conj v - (a : ℂ) + Complex.I * (t : ℂ)
      = (conj v - (a : ℂ)) + Complex.I * (t : ℂ) := by ring
  rw [boundaryCauchyKernel, hAeq, hBeq, mul_inv, norm_mul]
  exact mul_le_mul (norm_inv_sub_I_mul_real_le (re_node_offset hw) t)
    (norm_inv_add_I_mul_real_le (re_conj_node_offset hv) t) (norm_nonneg _)
    (le_of_lt (one_div_pos.mpr (re_node_offset hw)))

theorem integrable_boundaryPoissonTerm {a : ℝ} (ha : 1 / 2 < a) (q : XiZeroCopy) :
    Integrable fun t : ℝ => boundaryPoissonTerm a t q := by
  obtain ⟨hpos, hneg⟩ := abs_im_spectral_lt ha q
  have h1 : Integrable fun t : ℝ =>
      halfPlanePoisson (a + (xiSpectralPoint q).im) (t - (xiSpectralPoint q).re) :=
    (integrable_halfPlanePoisson hpos).comp_sub_right _
  have h2 : Integrable fun t : ℝ =>
      halfPlanePoisson (a - (xiSpectralPoint q).im) (t - (-(xiSpectralPoint q).re)) :=
    (integrable_halfPlanePoisson hneg).comp_sub_right _
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, boundaryPoissonTerm]
  have h : t - -(xiSpectralPoint q).re = t + (xiSpectralPoint q).re := by ring
  rw [h]

theorem integrable_boundaryTerm_cauchy {a : ℝ} (ha : 1 / 2 < a) {w v : ℂ} (hw : a < w.re)
    (hv : a < v.re) (q : XiZeroCopy) :
    Integrable fun t : ℝ =>
      ((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t := by
  obtain ⟨hpos, hneg⟩ := abs_im_spectral_lt ha q
  have hcont : Continuous fun t : ℝ =>
      ((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t := by
    refine Continuous.mul (Complex.continuous_ofReal.comp ?_) ?_
    · unfold boundaryPoissonTerm
      exact ((continuous_halfPlanePoisson hpos).comp (by fun_prop)).add
        ((continuous_halfPlanePoisson hneg).comp (by fun_prop))
    · unfold boundaryCauchyKernel
      refine Continuous.inv₀ (by fun_prop) fun t => ?_
      exact mul_ne_zero (sub_I_ne_zero hw t) (add_I_ne_zero hv t)
  have hApos := re_node_offset hw
  have hBpos := re_conj_node_offset hv
  refine ((integrable_boundaryPoissonTerm ha q).const_mul
    ((1 / (w - (a : ℂ)).re) * (1 / (conj v - (a : ℂ)).re))).mono'
    hcont.aestronglyMeasurable ?_
  filter_upwards with t
  have hT : 0 < boundaryPoissonTerm a t q := by
    rw [boundaryPoissonTerm]
    exact add_pos (halfPlanePoisson_pos hpos _) (halfPlanePoisson_pos hneg _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT,
    mul_comm ((1 / (w - (a : ℂ)).re) * (1 / (conj v - (a : ℂ)).re))]
  exact mul_le_mul_of_nonneg_left (norm_boundaryCauchyKernel_le_const hw hv t) (le_of_lt hT)

/-! ### The per-term Cauchy integral -/

theorem integral_boundaryTerm_cauchy {a : ℝ} (ha : 1 / 2 < a) {w v : ℂ} (hw : a < w.re)
    (hv : a < v.re) (hS : w + conj v - 2 * (a : ℂ) ≠ 0) (q : XiZeroCopy) :
    (∫ t : ℝ, ((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t)
      = (w + conj v - 2 * (a : ℂ))⁻¹
        * (2 * (weilChannelA w (xiSpectralPoint q)
          + conj (weilChannelA v (xiSpectralPoint q)))) := by
  obtain ⟨hpos, hneg⟩ := abs_im_spectral_lt ha q
  have hA := re_node_offset hw
  have hB := re_conj_node_offset hv
  have hwhalf : 1 / 2 < w.re := lt_trans ha hw
  have hvhalf : 1 / 2 < v.re := lt_trans ha hv
  set r : ℝ := (xiSpectralPoint q).re with hrdef
  set n : ℝ := (xiSpectralPoint q).im with hndef
  have hsplit : ∀ t : ℝ, ((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t
      = (w + conj v - 2 * (a : ℂ))⁻¹
        * ((((halfPlanePoisson (a + n) (t - r) : ℝ) : ℂ)
              * (w - (a : ℂ) - Complex.I * (t : ℂ))⁻¹
            + ((halfPlanePoisson (a - n) (t - (-r)) : ℝ) : ℂ)
              * (w - (a : ℂ) - Complex.I * (t : ℂ))⁻¹)
          + (((halfPlanePoisson (a + n) (t - r) : ℝ) : ℂ)
              * (conj v - (a : ℂ) + Complex.I * (t : ℂ))⁻¹
            + ((halfPlanePoisson (a - n) (t - (-r)) : ℝ) : ℂ)
              * (conj v - (a : ℂ) + Complex.I * (t : ℂ))⁻¹)) := by
    intro t
    rw [boundaryCauchyKernel_split hw hv hS t, boundaryPoissonTerm]
    have h : t - -r = t + r := by ring
    rw [h, ← hrdef, ← hndef]
    push_cast
    ring
  have hi1 : Integrable fun t : ℝ => ((halfPlanePoisson (a + n) (t - r) : ℝ) : ℂ)
      * (w - (a : ℂ) - Complex.I * (t : ℂ))⁻¹ :=
    integrable_poisson_cauchy_shiftL (A := w - (a : ℂ)) hpos hA r
  have hi2 : Integrable fun t : ℝ => ((halfPlanePoisson (a - n) (t - (-r)) : ℝ) : ℂ)
      * (w - (a : ℂ) - Complex.I * (t : ℂ))⁻¹ :=
    integrable_poisson_cauchy_shiftL (A := w - (a : ℂ)) hneg hA (-r)
  have hi3 : Integrable fun t : ℝ => ((halfPlanePoisson (a + n) (t - r) : ℝ) : ℂ)
      * (conj v - (a : ℂ) + Complex.I * (t : ℂ))⁻¹ :=
    integrable_poisson_cauchy_shiftR (B := conj v - (a : ℂ)) hpos hB r
  have hi4 : Integrable fun t : ℝ => ((halfPlanePoisson (a - n) (t - (-r)) : ℝ) : ℂ)
      * (conj v - (a : ℂ) + Complex.I * (t : ℂ))⁻¹ :=
    integrable_poisson_cauchy_shiftR (B := conj v - (a : ℂ)) hneg hB (-r)
  have hi12 : Integrable fun t : ℝ =>
      ((halfPlanePoisson (a + n) (t - r) : ℝ) : ℂ) * (w - (a : ℂ) - Complex.I * (t : ℂ))⁻¹
        + ((halfPlanePoisson (a - n) (t - (-r)) : ℝ) : ℂ)
          * (w - (a : ℂ) - Complex.I * (t : ℂ))⁻¹ := by
    exact hi1.add hi2
  have hi34 : Integrable fun t : ℝ =>
      ((halfPlanePoisson (a + n) (t - r) : ℝ) : ℂ) * (conj v - (a : ℂ) + Complex.I * (t : ℂ))⁻¹
        + ((halfPlanePoisson (a - n) (t - (-r)) : ℝ) : ℂ)
          * (conj v - (a : ℂ) + Complex.I * (t : ℂ))⁻¹ := by
    exact hi3.add hi4
  have hv1 : (∫ t : ℝ, ((halfPlanePoisson (a + n) (t - r) : ℝ) : ℂ)
      * (w - (a : ℂ) - Complex.I * (t : ℂ))⁻¹)
      = (w - (a : ℂ) - Complex.I * ((r : ℝ) : ℂ) + ((a + n : ℝ) : ℂ))⁻¹ :=
    integral_poisson_cauchy_shift (A := w - (a : ℂ)) hpos hA r
  have hv2 : (∫ t : ℝ, ((halfPlanePoisson (a - n) (t - (-r)) : ℝ) : ℂ)
      * (w - (a : ℂ) - Complex.I * (t : ℂ))⁻¹)
      = (w - (a : ℂ) - Complex.I * ((-r : ℝ) : ℂ) + ((a - n : ℝ) : ℂ))⁻¹ :=
    integral_poisson_cauchy_shift (A := w - (a : ℂ)) hneg hA (-r)
  have hv3 : (∫ t : ℝ, ((halfPlanePoisson (a + n) (t - r) : ℝ) : ℂ)
      * (conj v - (a : ℂ) + Complex.I * (t : ℂ))⁻¹)
      = (conj v - (a : ℂ) + Complex.I * ((r : ℝ) : ℂ) + ((a + n : ℝ) : ℂ))⁻¹ :=
    integral_poisson_cauchy_shift_conj (B := conj v - (a : ℂ)) hpos hB r
  have hv4 : (∫ t : ℝ, ((halfPlanePoisson (a - n) (t - (-r)) : ℝ) : ℂ)
      * (conj v - (a : ℂ) + Complex.I * (t : ℂ))⁻¹)
      = (conj v - (a : ℂ) + Complex.I * ((-r : ℝ) : ℂ) + ((a - n : ℝ) : ℂ))⁻¹ :=
    integral_poisson_cauchy_shift_conj (B := conj v - (a : ℂ)) hneg hB (-r)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_add hi12 hi34,
    MeasureTheory.integral_add hi1 hi2, MeasureTheory.integral_add hi3 hi4,
    hv1, hv2, hv3, hv4]
  congr 1
  have halpha : xiSpectralPoint q = ((r : ℝ) : ℂ) + ((n : ℝ) : ℂ) * Complex.I := by
    rw [hrdef, hndef]
    exact (Complex.re_add_im _).symm
  have e1 : w - (a : ℂ) - Complex.I * ((r : ℝ) : ℂ) + ((a + n : ℝ) : ℂ)
      = w - Complex.I * xiSpectralPoint q := by
    rw [halpha]
    push_cast
    linear_combination ((n : ℝ) : ℂ) * Complex.I_mul_I
  have e2 : w - (a : ℂ) - Complex.I * ((-r : ℝ) : ℂ) + ((a - n : ℝ) : ℂ)
      = w + Complex.I * xiSpectralPoint q := by
    rw [halpha]
    push_cast
    linear_combination (-((n : ℝ) : ℂ)) * Complex.I_mul_I
  have e3 : conj v - (a : ℂ) + Complex.I * ((r : ℝ) : ℂ) + ((a + n : ℝ) : ℂ)
      = conj (v - Complex.I * xiSpectralPoint q) := by
    rw [halpha]
    simp only [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal, map_add]
    push_cast
    linear_combination ((n : ℝ) : ℂ) * Complex.I_mul_I
  have e4 : conj v - (a : ℂ) + Complex.I * ((-r : ℝ) : ℂ) + ((a - n : ℝ) : ℂ)
      = conj (v + Complex.I * xiSpectralPoint q) := by
    rw [halpha]
    simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    linear_combination (-((n : ℝ) : ℂ)) * Complex.I_mul_I
  rw [e1, e2, e3, e4, ← map_inv₀, ← map_inv₀]
  have hwsq := sq_add_spectral_sq_ne_zero hwhalf q
  have hvsq := sq_add_spectral_sq_ne_zero hvhalf q
  have hwA : weilChannelA w (xiSpectralPoint q)
      = ((w - Complex.I * xiSpectralPoint q)⁻¹
        + (w + Complex.I * xiSpectralPoint q)⁻¹) / 2 := by
    rw [weilChannelA_eq_resolvent hwsq, weilResolventPlus, weilResolventMinus, one_div, one_div]
  have hvA : conj (weilChannelA v (xiSpectralPoint q))
      = (conj ((v - Complex.I * xiSpectralPoint q)⁻¹)
        + conj ((v + Complex.I * xiSpectralPoint q)⁻¹)) / 2 := by
    rw [weilChannelA_eq_resolvent hvsq, weilResolventPlus, weilResolventMinus, one_div, one_div,
      map_div₀, map_add, map_ofNat]
  rw [hwA, hvA]
  ring

/-! ### The divisor sum of the boundary integrals -/

theorem integrable_boundaryPoissonTerm_mul_poisson {a p : ℝ} (ha : 1 / 2 < a) (hp : 0 < p)
    (m : ℝ) (q : XiZeroCopy) :
    Integrable fun t : ℝ => boundaryPoissonTerm a t q * halfPlanePoisson p (t - m) := by
  obtain ⟨hpos, hneg⟩ := abs_im_spectral_lt ha q
  have h1 := integrable_poisson_product_pair hpos hp (xiSpectralPoint q).re m
  have h2 := integrable_poisson_product_pair hneg hp (-(xiSpectralPoint q).re) m
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [Pi.add_apply, boundaryPoissonTerm]
  have h : t - -(xiSpectralPoint q).re = t + (xiSpectralPoint q).re := by ring
  rw [h]
  ring

theorem integrable_boundaryPoissonTerm_mul_invSq {a p : ℝ} (ha : 1 / 2 < a) (hp : 0 < p)
    (m : ℝ) (q : XiZeroCopy) :
    Integrable fun t : ℝ => boundaryPoissonTerm a t q * (p ^ 2 + (t - m) ^ 2)⁻¹ := by
  refine ((integrable_boundaryPoissonTerm_mul_poisson ha hp m q).const_mul
    (Real.pi / p)).congr (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [inv_sq_add_sq_eq_poisson hp]
  ring

theorem integral_boundaryPoissonTerm_mul_invSq {a p : ℝ} (ha : 1 / 2 < a) (hp : 0 < p)
    (m : ℝ) (q : XiZeroCopy) :
    (∫ t : ℝ, boundaryPoissonTerm a t q * (p ^ 2 + (t - m) ^ 2)⁻¹)
      = (Real.pi / p) * boundaryPoissonTerm (a + p) m q := by
  have hc : ∀ t : ℝ, boundaryPoissonTerm a t q * (p ^ 2 + (t - m) ^ 2)⁻¹
      = (Real.pi / p) * (boundaryPoissonTerm a t q * halfPlanePoisson p (t - m)) := by
    intro t
    rw [inv_sq_add_sq_eq_poisson hp]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hc),
    MeasureTheory.integral_const_mul, integral_boundaryPoissonTerm_mul_poisson ha hp m q]

theorem integral_norm_boundaryTerm_cauchy_le {a : ℝ} (ha : 1 / 2 < a) {w v : ℂ} (hw : a < w.re)
    (hv : a < v.re) (q : XiZeroCopy) :
    (∫ t : ℝ, ‖((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t‖)
      ≤ (1 / 2) * ((Real.pi / (w.re - a)) * boundaryPoissonTerm w.re w.im q
        + (Real.pi / (v.re - a)) * boundaryPoissonTerm v.re v.im q) := by
  obtain ⟨hpos, hneg⟩ := abs_im_spectral_lt ha q
  have hwa : (0 : ℝ) < w.re - a := by linarith
  have hva : (0 : ℝ) < v.re - a := by linarith
  have hmaj : Integrable fun t : ℝ => (1 / 2) *
      (boundaryPoissonTerm a t q * ((w.re - a) ^ 2 + (t - w.im) ^ 2)⁻¹
        + boundaryPoissonTerm a t q * ((v.re - a) ^ 2 + (t - v.im) ^ 2)⁻¹) := by
    refine (((integrable_boundaryPoissonTerm_mul_invSq ha hwa w.im q).add
      (integrable_boundaryPoissonTerm_mul_invSq ha hva v.im q)).const_mul (1 / 2)).congr
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]
  have hle : ∀ t : ℝ, ‖((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t‖
      ≤ (1 / 2) * (boundaryPoissonTerm a t q * ((w.re - a) ^ 2 + (t - w.im) ^ 2)⁻¹
        + boundaryPoissonTerm a t q * ((v.re - a) ^ 2 + (t - v.im) ^ 2)⁻¹) := by
    intro t
    have hT : 0 < boundaryPoissonTerm a t q := by
      rw [boundaryPoissonTerm]
      exact add_pos (halfPlanePoisson_pos hpos _) (halfPlanePoisson_pos hneg _)
    have hb := norm_boundaryCauchyKernel_le (a := a) w v t
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT]
    nlinarith [hb, hT]
  refine le_trans (MeasureTheory.integral_mono
    (integrable_boundaryTerm_cauchy ha hw hv q).norm hmaj hle) ?_
  have hcalc : (∫ t : ℝ, (1 / 2) *
      (boundaryPoissonTerm a t q * ((w.re - a) ^ 2 + (t - w.im) ^ 2)⁻¹
        + boundaryPoissonTerm a t q * ((v.re - a) ^ 2 + (t - v.im) ^ 2)⁻¹))
      = (1 / 2) * ((Real.pi / (w.re - a)) * boundaryPoissonTerm (a + (w.re - a)) w.im q
        + (Real.pi / (v.re - a)) * boundaryPoissonTerm (a + (v.re - a)) v.im q) := by
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (integrable_boundaryPoissonTerm_mul_invSq ha hwa w.im q)
        (integrable_boundaryPoissonTerm_mul_invSq ha hva v.im q),
      integral_boundaryPoissonTerm_mul_invSq ha hwa w.im q,
      integral_boundaryPoissonTerm_mul_invSq ha hva v.im q]
  rw [hcalc]
  have e1 : a + (w.re - a) = w.re := by ring
  have e2 : a + (v.re - a) = v.re := by ring
  rw [e1, e2]

theorem summable_integral_norm_boundaryTerm {a : ℝ} (ha : 1 / 2 < a) {w v : ℂ} (hw : a < w.re)
    (hv : a < v.re) :
    Summable fun q : XiZeroCopy =>
      ∫ t : ℝ, ‖((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t‖ := by
  have hwh : 1 / 2 < w.re := lt_trans ha hw
  have hvh : 1 / 2 < v.re := lt_trans ha hv
  refine Summable.of_nonneg_of_le
    (fun q => MeasureTheory.integral_nonneg fun t => norm_nonneg _)
    (fun q => integral_norm_boundaryTerm_cauchy_le ha hw hv q) ?_
  exact (((summable_boundaryPoissonTerm hwh w.im).mul_left _).add
    ((summable_boundaryPoissonTerm hvh v.im).mul_left _)).mul_left _

/-! ### The boundary Cauchy representation of the safe Carathéodory kernel -/

/-- **The safe Carathéodory kernel is the Cauchy transform of its boundary density.**  Averaging
`h_a(t) = Re (ξ'/ξ)(a + it)` against the two-node Cauchy kernel
`((w - a - it)(conj v - a + it))⁻¹` reproduces
`(L(w) + conj L(v)) / (w + conj v - 2a)`. -/
theorem safeCaratheodoryKernel_eq_boundary_integral {a : ℝ} (ha : 1 / 2 < a) {w v : ℂ}
    (hw : a < w.re) (hv : a < v.re) (hS : w + conj v - 2 * (a : ℂ) ≠ 0) :
    safeCaratheodoryKernel a w v
      = (1 / (Real.pi : ℂ))
        * ∫ t : ℝ, ((eulerSafeDensity a t : ℝ) : ℂ) * boundaryCauchyKernel a w v t := by
  have hwh : 1 / 2 < w.re := lt_trans ha hw
  have hvh : 1 / 2 < v.re := lt_trans ha hv
  have hcvh : 1 / 2 < (conj v).re := by rwa [Complex.conj_re]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  have hpt : ∀ t : ℝ, ((eulerSafeDensity a t : ℝ) : ℂ) * boundaryCauchyKernel a w v t
      = ((Real.pi : ℂ) / 2)
        * ∑' q : XiZeroCopy,
            ((boundaryPoissonTerm a t q : ℝ) : ℂ) * boundaryCauchyKernel a w v t := by
    intro t
    rw [eulerSafeDensity_eq_tsum_term ha t, Complex.ofReal_mul, Complex.ofReal_tsum, mul_assoc,
      tsum_mul_right]
    push_cast
    ring
  have hsA : Summable fun q : XiZeroCopy => weilChannelA w (xiSpectralPoint q) :=
    summable_channelA hwh
  have hsB : Summable fun q : XiZeroCopy => conj (weilChannelA v (xiSpectralPoint q)) := by
    refine (summable_channelA hvh).map (starRingEnd ℂ) ?_
    exact Complex.continuous_conj
  have hsum : (∑' q : XiZeroCopy, (w + conj v - 2 * (a : ℂ))⁻¹
        * (2 * (weilChannelA w (xiSpectralPoint q)
          + conj (weilChannelA v (xiSpectralPoint q)))))
      = (w + conj v - 2 * (a : ℂ))⁻¹
        * (2 * (logDeriv xiCent w + conj (logDeriv xiCent v))) := by
    rw [tsum_mul_left, tsum_mul_left, Summable.tsum_add hsA hsB,
      ← logDeriv_xiCent_eq_tsum_channelA hwh, ← Complex.conj_tsum,
      ← logDeriv_xiCent_eq_tsum_channelA hvh]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun q => integrable_boundaryTerm_cauchy ha hw hv q)
      (summable_integral_norm_boundaryTerm ha hw hv),
    tsum_congr (integral_boundaryTerm_cauchy ha hw hv hS), hsum, safeCaratheodoryKernel]
  field_simp

end RHTower
