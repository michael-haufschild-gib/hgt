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

theorem norm_boundaryCauchyKernel_le {a : ℝ} {w v : ℂ} (t : ℝ) :
    ‖boundaryCauchyKernel a w v t‖
      ≤ (1 / 2) * (((w - (a : ℂ)).re ^ 2 + (t - (w - (a : ℂ)).im) ^ 2)⁻¹
        + ((conj v - (a : ℂ)).re ^ 2 + (t + (conj v - (a : ℂ)).im) ^ 2)⁻¹) := by
  have hAeq : w - (a : ℂ) - Complex.I * (t : ℂ) = (w - (a : ℂ)) - Complex.I * (t : ℂ) := by ring
  have hBeq : conj v - (a : ℂ) + Complex.I * (t : ℂ)
      = (conj v - (a : ℂ)) + Complex.I * (t : ℂ) := by ring
  rw [boundaryCauchyKernel, hAeq, hBeq, mul_inv, norm_mul]
  have h1 := norm_inv_sub_I_sq (w - (a : ℂ)) t
  have h2 := norm_inv_add_I_sq (conj v - (a : ℂ)) t
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

end RHTower
