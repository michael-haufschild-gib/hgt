import GaloisForLFunctions.SurfaceOfSpecZ.HyperbolicQuotientsJetCarriersAndCoupledDamping

/-!
# The images of the degree geodesic

The archimedean fibre of the hyperbolic Arakelov surface of `Spec ℤ` is upper half-space `ℍ³` with
the degree geodesic `ℓ = {z_t = (0, t)}`; the archimedean intersection of the Frobenius graphs
`Γ_m, Γ_n` is `2π√(mn) G_{1/2}(d(z_m, z_n))`. A hyperbolic carrier replaces `z_n` by its images
`γ z_n` under isometries `γ ∈ SL₂(ℂ)`, so every carrier is governed by the distances `d(z_t, γ z_u)`.

**Image distances** (`h3Cosh_degPoint_h3Act`, `imageCosh_eq`). For `γ = (a b; c d)` and `t, u > 0`,

  `cosh d(z_t, γ z_u) = ½ (‖a‖² r + ‖d‖² r⁻¹ + ‖b‖² P⁻¹ + ‖c‖² P)`,   `r = u/t`, `P = tu`.

The four squared norms are the **Arakelov coordinates** of `γ` relative to `ℓ`. The ratio `r` is the
dilation-invariant coordinate of the pair; the product `P` moves under the dilation `z ↦ λz`, which
scales it by `λ²`. The identity is the Lagrange identity
`‖b d̄ + a c̄ u²‖² + u² ‖ad − bc‖² = (‖a‖²u² + ‖b‖²)(‖c‖²u² + ‖d‖²)` with `ad − bc = 1`.

**The two ends of a carrier** (`half_mul_le_imageCosh`, `imageCosh_of_c_eq_zero`). If `c ≠ 0` the
image distance grows with the product, `cosh d ≥ ½ ‖c‖² P`: such an image recedes as the degrees go
to the end `∞` of `ℓ`. If `c = 0`, `γ` fixes that end, `‖d‖ = ‖a‖⁻¹`, and

  `cosh d(z_t, γ z_u) = ½ (x + x⁻¹) + ‖b‖²/(2P)`,   `x = ‖a‖² r`,

which tends to `cosh |log x|` as `P → ∞`: the stabilizer of the end acts on the ratio alone.
-/

open Complex ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HyperbolicArakelovTheory

open SurfaceOfSpecZ

/-- `cosh` of the distance from `z_t` to `γ z_u`, in the Arakelov coordinates of `γ`. -/
def imageCosh (g : SL2C) (t u : ℝ) : ℝ :=
  (‖g.1 0 0‖ ^ 2 * u ^ 2 + ‖g.1 0 1‖ ^ 2 + ‖g.1 1 0‖ ^ 2 * t ^ 2 * u ^ 2 +
      ‖g.1 1 1‖ ^ 2 * t ^ 2) / (2 * t * u)

/-- The Lagrange identity behind the image distances. -/
theorem normSq_lagrange (a b c d : ℂ) (u : ℝ) :
    normSq (b * conj d + a * conj c * (u : ℂ) ^ 2) + u ^ 2 * normSq (a * d - b * c) =
      (normSq a * u ^ 2 + normSq b) * (normSq c * u ^ 2 + normSq d) := by
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, sub_re, sub_im, conj_re, conj_im,
    sq, ofReal_re, ofReal_im]
  ring

/-- **Image distances on the degree geodesic.** -/
theorem h3Cosh_degPoint_h3Act (g : SL2C) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    h3Cosh (degPoint t ht) (h3Act g (degPoint u hu)) = imageCosh g t u := by
  set a := g.1 0 0
  set b := g.1 0 1
  set c := g.1 1 0
  set d := g.1 1 1
  have hdet : a * d - b * c = 1 := by
    have := g.prop
    rwa [Matrix.det_fin_two] at this
  set D := h3Denom g (degPoint u hu) with hD
  have hDpos : 0 < D := h3Denom_pos g _
  have hDe : D = normSq c * u ^ 2 + normSq d := by
    simp only [hD, h3Denom, degPoint, mul_zero, zero_add, ← normSq_eq_norm_sq]
    ring
  set num := b * conj d + a * conj c * (u : ℂ) ^ 2 with hnum
  have hz : (h3Act g (degPoint u hu)).z = num / (D : ℂ) := by
    rw [h3Act_z]
    simp only [degPoint, mul_zero, zero_add]
    rfl
  have ht' : (h3Act g (degPoint u hu)).t = u / D := by
    rw [h3Act_t]; rfl
  have hN : normSq num = (normSq a * u ^ 2 + normSq b) * D - u ^ 2 := by
    have h := normSq_lagrange a b c d u
    rw [hdet, map_one, mul_one] at h
    rw [hDe]; linarith
  have hnorm : ‖(degPoint t ht).z - (h3Act g (degPoint u hu)).z‖ ^ 2 = normSq num / D ^ 2 := by
    rw [hz, show (degPoint t ht).z = 0 from rfl, zero_sub, norm_neg, norm_div,
      Complex.norm_real, Real.norm_of_nonneg hDpos.le, div_pow, ← normSq_eq_norm_sq]
  unfold h3Cosh imageCosh
  rw [hnorm, ht', hN, show (degPoint t ht).t = t from rfl]
  simp only [← normSq_eq_norm_sq]
  have hD0 : D ≠ 0 := hDpos.ne'
  field_simp
  rw [hDe]
  ring

/-- The distance from `z_t` to `γ z_u`. -/
theorem h3Dist_degPoint_h3Act (g : SL2C) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    h3Dist (degPoint t ht) (h3Act g (degPoint u hu)) = Real.arcosh (imageCosh g t u) := by
  rw [h3Dist, h3Cosh_degPoint_h3Act]

theorem one_le_imageCosh (g : SL2C) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    1 ≤ imageCosh g t u := by
  rw [← h3Cosh_degPoint_h3Act g ht hu]; exact one_le_h3Cosh _ _

/-- **Ratio and product.** `cosh d(z_t, γz_u) = ½(‖a‖²r + ‖d‖²r⁻¹ + ‖b‖²P⁻¹ + ‖c‖²P)`. -/
theorem imageCosh_eq (g : SL2C) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    imageCosh g t u = (‖g.1 0 0‖ ^ 2 * (u / t) + ‖g.1 1 1‖ ^ 2 * (u / t)⁻¹ +
      ‖g.1 0 1‖ ^ 2 * (t * u)⁻¹ + ‖g.1 1 0‖ ^ 2 * (t * u)) / 2 := by
  unfold imageCosh
  field_simp
  ring

/-- An image with `c ≠ 0` recedes with the product: `cosh d ≥ ½‖c‖²·tu`. -/
theorem half_mul_le_imageCosh (g : SL2C) {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    ‖g.1 1 0‖ ^ 2 * (t * u) / 2 ≤ imageCosh g t u := by
  rw [imageCosh_eq g ht hu]
  have h1 : 0 ≤ ‖g.1 0 0‖ ^ 2 * (u / t) := by positivity
  have h2 : 0 ≤ ‖g.1 1 1‖ ^ 2 * (u / t)⁻¹ := by positivity
  have h3 : 0 ≤ ‖g.1 0 1‖ ^ 2 * (t * u)⁻¹ := by positivity
  linarith

/-- In the stabilizer of the end `∞` the multipliers are inverse: `‖d‖ = ‖a‖⁻¹`. -/
theorem norm_d_of_c_eq_zero {g : SL2C} (hc : g.1 1 0 = 0) :
    g.1 0 0 ≠ 0 ∧ ‖g.1 1 1‖ = ‖g.1 0 0‖⁻¹ := by
  have hdet : g.1 0 0 * g.1 1 1 = 1 := by
    have := g.prop
    rwa [Matrix.det_fin_two, hc, mul_zero, sub_zero] at this
  have ha : g.1 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  refine ⟨ha, ?_⟩
  have := congrArg norm hdet
  rw [norm_mul, norm_one] at this
  exact eq_inv_of_mul_eq_one_right this

/-- **The stabilizer of the end acts on the ratio.** For `c = 0`,
`cosh d(z_t, γz_u) = ½(x + x⁻¹) + ‖b‖²/(2tu)` with `x = ‖a‖²·u/t`. -/
theorem imageCosh_of_c_eq_zero {g : SL2C} (hc : g.1 1 0 = 0) {t u : ℝ} (ht : 0 < t)
    (hu : 0 < u) :
    imageCosh g t u = (‖g.1 0 0‖ ^ 2 * (u / t) + (‖g.1 0 0‖ ^ 2 * (u / t))⁻¹) / 2 +
      ‖g.1 0 1‖ ^ 2 * (t * u)⁻¹ / 2 := by
  obtain ⟨ha, hd⟩ := norm_d_of_c_eq_zero hc
  rw [imageCosh_eq g ht hu, hd, hc, norm_zero]
  rw [mul_inv, inv_pow]
  ring

/-- `½(x + x⁻¹) = cosh |log x|` for `x > 0`. -/
theorem half_add_inv_eq_cosh {x : ℝ} (hx : 0 < x) :
    (x + x⁻¹) / 2 = Real.cosh |Real.log x| := by
  rw [Real.cosh_abs, Real.cosh_eq, Real.exp_log hx, Real.exp_neg, Real.exp_log hx]

end GaloisForLFunctions.HyperbolicArakelovTheory
