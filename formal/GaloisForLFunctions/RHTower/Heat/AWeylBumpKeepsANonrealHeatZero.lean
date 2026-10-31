import GaloisForLFunctions.RHTower.XiCosineShiftDefectPersistence
import GaloisForLFunctions.RHTower.GaussianPoleFilter

/-!
# A Weyl bump keeps a nonreal zero of the de Bruijn flow below the horizon `4θ`

The de Bruijn flow `H_t(z) = ∫ Φ(u) e^{tu²} cos(zu) du` of `Ξ` has only real zeros above the height
`2π e^{(2/3+ε)/t}` (`KiKimLeeTwoThirdsHorizon`): in units `κ = t log X`, the reality horizon is
`κ = 2/3 = 4μ(½)`.  This file shows that no argument from size bounds and a positive kernel alone
can go lower.

Let `L > 0`, `A > 0` and

  `F(z) = cos(Lz/2) + A e^{−z²/L²} = ∫ cos(zu) dμ(u)`,

`μ = ½(δ_{L/2} + δ_{−L/2}) + A (L/(2√π)) e^{−L²u²/4} du ≥ 0`: real zeros spaced `2π/L` (the zero
density of `Ξ` at height `X` when `L = log X`) and a centre bump of height `A`.  Its deformation
`∫ e^{tu²} cos(zu) dμ(u)` is (`cosBumpHeat`, `cosBumpHeat_eq_integral`)

  `H_t(z) = e^{tL²/4} cos(Lz/2) + A (1 − 4t/L²)^{−1/2} e^{−z²/(L² − 4t)}`.

* **Size** (`norm_cosBumpModel_le`): `‖F(x + iy)‖ ≤ cosh(Ly/2) + A e^{y²/L²}`.  At `y = 0` the bump
  is `A` against a cosine of size `1`; with `A = e^{θL}`, `θ = μ(½) = 1/6` is the centre size that
  Weyl's bound allows for `Ξ` at height `X = e^L`.
* **A nonreal zero** (`exists_nonreal_zero_cosBumpHeat`).  For `0 < θ ≤ ½` and `0 ≤ κ < 4θ`, for all
  large `L`, `H_{κ/L}` with `A = e^{θL}` has a zero with positive imaginary part.

Proof.  With `E = e^{tL²/4}`, `B = A(1 − 4t/L²)^{−1/2}` and `cosh a = B/E`, the approximant
`G(z) = E cos(Lz/2) + B` vanishes at `z* = (2/L)(π + ia)`.  On the circle `|z − z*| = 1/L`,
`G = −2E sin((ζ + ζ*)/2) sin((ζ − ζ*)/2)` (`ζ = Lz/2`) has `‖G‖ ≥ E sinh(a − ¼)/π`
(`‖sin w‖² = sin² Re w + sinh² Im w`), while `‖H_t − G‖ = B‖e^{−z²/(L²−4t)} − 1‖ ≤ 4B‖z‖²/L²`.  For
`2 ≤ a ≤ L` and `L ≥ 22` the second is smaller, so by Rouché `H_t` vanishes in the disc, which lies in
`Im z > 0`.  `a ≥ 2` needs `(θ − κ/4)L ≥ 2`.

So with Weyl's centre size the model keeps a nonreal zero at height-scale `e^L` up to heat
`(2/3 − ε)/L`, exactly the horizon of the corpus, and the constant `2/3` in the heat-count bound
`N(t) ≤ C R log R`, `R = 2π e^{(2/3+ε)/t}` (`exists_nonrealZeroCount_and_collisionMass_le_twoThirds`)
cannot be lowered from size bounds and kernel positivity alone.
-/

open Complex Metric

namespace RHTower.DeBruijn

noncomputable section

/-- The model `F(z) = cos(Lz/2) + A e^{−z²/L²}`. -/
def cosBumpModel (L A : ℝ) (z : ℂ) : ℂ :=
  Complex.cos (L * z / 2) + A * Complex.exp (-(z ^ 2) / L ^ 2)

/-- The de Bruijn flow of the model at time `t`:
`e^{tL²/4} cos(Lz/2) + A (1 − 4t/L²)^{−1/2} e^{−z²/(L² − 4t)}`. -/
def cosBumpHeat (L A t : ℝ) (z : ℂ) : ℂ :=
  Real.exp (t * L ^ 2 / 4) * Complex.cos (L * z / 2)
    + (A / Real.sqrt (1 - 4 * t / L ^ 2) : ℝ) * Complex.exp (-(z ^ 2) / (L ^ 2 - 4 * t))

theorem cosBumpHeat_zero {L : ℝ} (A : ℝ) (z : ℂ) : cosBumpHeat L A 0 z = cosBumpModel L A z := by
  simp [cosBumpHeat, cosBumpModel]

/-! ### The model as a positive kernel -/

/-- The heated Gaussian part of the kernel: `(L/(2√π)) e^{−L²u²/4} e^{tu²}` is `L/√(L² − 4t)` times
the normal density of variance `2/(L² − 4t)`. -/
theorem gaussKernel_heat_eq {L t : ℝ} (hL : 0 < L) (ht : 4 * t < L ^ 2) (u : ℝ) :
    L / (2 * Real.sqrt Real.pi) * Real.exp (-(L ^ 2 / 4 * u ^ 2)) * Real.exp (t * u ^ 2)
      = L / Real.sqrt (L ^ 2 - 4 * t) * filterGauss (1 / (L ^ 2 - 4 * t)) u := by
  have hd : 0 < L ^ 2 - 4 * t := by linarith
  have hπ := Real.pi_pos
  unfold filterGauss
  have hsq4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hrpow : (4 * Real.pi * (1 / (L ^ 2 - 4 * t))) ^ (-(1 / 2 : ℝ))
      = Real.sqrt (L ^ 2 - 4 * t) / (2 * Real.sqrt Real.pi) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by norm_num), hsq4, one_div, Real.sqrt_inv]
    have : 0 < Real.sqrt (L ^ 2 - 4 * t) := Real.sqrt_pos.mpr hd
    have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hπ
    field_simp
  rw [hrpow, mul_assoc (L / (2 * Real.sqrt Real.pi)), ← Real.exp_add]
  have hexp : -(L ^ 2 / 4 * u ^ 2) + t * u ^ 2 = -(u ^ 2 / (4 * (1 / (L ^ 2 - 4 * t)))) := by
    field_simp; ring
  rw [hexp]
  have : 0 < Real.sqrt (L ^ 2 - 4 * t) := Real.sqrt_pos.mpr hd
  field_simp

/-- **The heated Gaussian kernel against `cos(zu)`**:
`∫ (L/(2√π)) e^{−L²u²/4} e^{tu²} cos(zu) du = (1 − 4t/L²)^{−1/2} e^{−z²/(L² − 4t)}`. -/
theorem integral_gaussKernel_heat_mul_cos {L t : ℝ} (hL : 0 < L) (ht : 4 * t < L ^ 2) (z : ℂ) :
    ∫ u : ℝ, ((L / (2 * Real.sqrt Real.pi) * Real.exp (-(L ^ 2 / 4 * u ^ 2))
        * Real.exp (t * u ^ 2) : ℝ) : ℂ) * Complex.cos (z * u)
      = ((1 / Real.sqrt (1 - 4 * t / L ^ 2) : ℝ) : ℂ) * Complex.exp (-(z ^ 2) / (L ^ 2 - 4 * t)) := by
  have hd : 0 < L ^ 2 - 4 * t := by linarith
  have ht' : 0 < 1 / (L ^ 2 - 4 * t) := by positivity
  set c : ℝ := L / Real.sqrt (L ^ 2 - 4 * t) with hc
  have hpt : ∀ u : ℝ, ((L / (2 * Real.sqrt Real.pi) * Real.exp (-(L ^ 2 / 4 * u ^ 2))
      * Real.exp (t * u ^ 2) : ℝ) : ℂ) * Complex.cos (z * u)
      = (c / 2 : ℂ) * ((filterGauss (1 / (L ^ 2 - 4 * t)) u : ℂ) * Complex.exp (u * (z * I))
        + (filterGauss (1 / (L ^ 2 - 4 * t)) u : ℂ) * Complex.exp (u * (-(z * I)))) := by
    intro u
    rw [gaussKernel_heat_eq hL ht u,
      show Complex.cos (z * u) = (Complex.exp (z * u * I) + Complex.exp (-(z * u) * I)) / 2 from rfl]
    rw [show z * u * I = u * (z * I) by ring, show -(z * u) * I = u * (-(z * I)) by ring, hc]
    push_cast; ring
  rw [show (fun u : ℝ => ((L / (2 * Real.sqrt Real.pi) * Real.exp (-(L ^ 2 / 4 * u ^ 2))
      * Real.exp (t * u ^ 2) : ℝ) : ℂ) * Complex.cos (z * u)) = fun u =>
      (c / 2 : ℂ) * ((filterGauss (1 / (L ^ 2 - 4 * t)) u : ℂ) * Complex.exp (u * (z * I))
        + (filterGauss (1 / (L ^ 2 - 4 * t)) u : ℂ) * Complex.exp (u * (-(z * I)))) from funext hpt,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_add (integrable_filterGauss_mul_exp ht' _)
      (integrable_filterGauss_mul_exp ht' _), integral_filterGauss_mul_exp ht',
    integral_filterGauss_mul_exp ht']
  have hs : Real.sqrt (1 - 4 * t / L ^ 2) = Real.sqrt (L ^ 2 - 4 * t) / L := by
    rw [show 1 - 4 * t / L ^ 2 = (L ^ 2 - 4 * t) / L ^ 2 by field_simp, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq hL.le]
  have hsd : 0 < Real.sqrt (L ^ 2 - 4 * t) := Real.sqrt_pos.mpr hd
  have hexp : ((1 / (L ^ 2 - 4 * t) : ℝ) : ℂ) * (z * I) ^ 2 = -(z ^ 2) / (L ^ 2 - 4 * t) := by
    push_cast; rw [mul_pow, Complex.I_sq]; field_simp
  have hexp' : ((1 / (L ^ 2 - 4 * t) : ℝ) : ℂ) * (-(z * I)) ^ 2 = -(z ^ 2) / (L ^ 2 - 4 * t) := by
    rw [neg_sq]; exact hexp
  rw [hexp, hexp', hs, hc]
  push_cast
  field_simp
  ring

/-- **The model's de Bruijn deformation.**  With `F(z) = ∫ cos(zu) dμ(u)`,
`μ = ½(δ_{L/2} + δ_{−L/2}) + A (L/(2√π)) e^{−L²u²/4} du`, the deformation `∫ e^{tu²} cos(zu) dμ(u)` is
`cosBumpHeat L A t z` for `4t < L²`. -/
theorem cosBumpHeat_eq_integral {L A t : ℝ} (hL : 0 < L) (ht : 4 * t < L ^ 2) (z : ℂ) :
    cosBumpHeat L A t z = (Real.exp (t * (L / 2) ^ 2) : ℂ) * ((Complex.cos (z * (L / 2 : ℝ))
        + Complex.cos (z * (-(L / 2) : ℝ))) / 2)
      + A * ∫ u : ℝ, ((L / (2 * Real.sqrt Real.pi) * Real.exp (-(L ^ 2 / 4 * u ^ 2))
        * Real.exp (t * u ^ 2) : ℝ) : ℂ) * Complex.cos (z * u) := by
  rw [integral_gaussKernel_heat_mul_cos hL ht z]
  unfold cosBumpHeat
  rw [show z * ((-(L / 2) : ℝ) : ℂ) = -(z * ((L / 2 : ℝ) : ℂ)) by push_cast; ring, Complex.cos_neg]
  push_cast
  ring_nf

/-- `‖sin w‖² = sin²(Re w) + sinh²(Im w)`. -/
theorem norm_sin_sq (w : ℂ) :
    ‖Complex.sin w‖ ^ 2 = Real.sin w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have e : Complex.sin w = ((Real.sin w.re * Real.cosh w.im : ℝ) : ℂ)
      + ((Real.cos w.re * Real.sinh w.im : ℝ) : ℂ) * I := by
    rw [Complex.sin_eq]; push_cast; ring
  rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
  have h1 := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  nlinarith [h1, h2]

/-- `‖cos w‖² = cos²(Re w) + sinh²(Im w)`. -/
theorem norm_cos_sq (w : ℂ) :
    ‖Complex.cos w‖ ^ 2 = Real.cos w.re ^ 2 + Real.sinh w.im ^ 2 := by
  have e : Complex.cos w = ((Real.cos w.re * Real.cosh w.im : ℝ) : ℂ)
      + ((-(Real.sin w.re * Real.sinh w.im) : ℝ) : ℂ) * I := by
    rw [Complex.cos_eq]; push_cast; ring
  rw [e, Complex.sq_norm, Complex.normSq_add_mul_I]
  have h1 := Real.cosh_sq w.im
  have h2 := Real.sin_sq_add_cos_sq w.re
  nlinarith [h1, h2]

/-- `‖cos w‖ ≤ cosh(Im w)`. -/
theorem norm_cos_le_cosh_im (w : ℂ) : ‖Complex.cos w‖ ≤ Real.cosh w.im := by
  have h := norm_cos_sq w
  have hc := Real.cos_sq_le_one w.re
  have hch := Real.cosh_sq w.im
  have : ‖Complex.cos w‖ ^ 2 ≤ Real.cosh w.im ^ 2 := by nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (Real.cosh_pos _).le this

/-- `‖sin u‖ ≥ sinh(Im u)`. -/
theorem sinh_im_le_norm_sin (u : ℂ) : Real.sinh u.im ≤ ‖Complex.sin u‖ := by
  have h := norm_sin_sq u
  have : Real.sinh u.im ^ 2 ≤ ‖Complex.sin u‖ ^ 2 := by nlinarith [sq_nonneg (Real.sin u.re)]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) this

/-- `‖sin w‖ ≥ (2/π)‖w‖` for `|Re w| ≤ π/2`. -/
theorem two_div_pi_mul_norm_le_norm_sin {w : ℂ} (hw : |w.re| ≤ Real.pi / 2) :
    2 / Real.pi * ‖w‖ ≤ ‖Complex.sin w‖ := by
  have hπ := Real.pi_pos
  have hc : 0 ≤ 2 / Real.pi := by positivity
  have hc1 : 2 / Real.pi ≤ 1 := by
    rw [div_le_one hπ]; linarith [Real.pi_gt_three]
  -- `(2/π)|x| ≤ |sin x|` on `|x| ≤ π/2` (Jordan)
  have hsin1 : 2 / Real.pi * |w.re| ≤ |Real.sin w.re| := by
    rcases le_total 0 w.re with h0 | h0
    · rw [abs_of_nonneg h0]
      exact (Real.mul_le_sin h0 (by rwa [abs_of_nonneg h0] at hw)).trans (le_abs_self _)
    · have h := Real.mul_le_sin (neg_nonneg.mpr h0) (by rwa [abs_of_nonpos h0] at hw)
      rw [Real.sin_neg] at h
      rw [abs_of_nonpos h0]
      exact h.trans (neg_le_abs _)
  have hsin : (2 / Real.pi * |w.re|) ^ 2 ≤ Real.sin w.re ^ 2 := by
    calc (2 / Real.pi * |w.re|) ^ 2 ≤ |Real.sin w.re| ^ 2 := pow_le_pow_left₀ (by positivity) hsin1 2
      _ = Real.sin w.re ^ 2 := sq_abs _
  -- `|y| ≤ |sinh y|`
  have hsinh : (2 / Real.pi * |w.im|) ^ 2 ≤ Real.sinh w.im ^ 2 := by
    have h1 : |w.im| ≤ |Real.sinh w.im| := by
      rcases le_total 0 w.im with h0 | h0
      · rw [abs_of_nonneg h0, abs_of_nonneg (Real.sinh_nonneg_iff.mpr h0)]
        exact Real.self_le_sinh_iff.mpr h0
      · rw [abs_of_nonpos h0, abs_of_nonpos (Real.sinh_nonpos_iff.mpr h0)]
        have := Real.self_le_sinh_iff.mpr (neg_nonneg.mpr h0)
        rw [Real.sinh_neg] at this; linarith
    have h2 : 2 / Real.pi * |w.im| ≤ |Real.sinh w.im| :=
      le_trans (mul_le_of_le_one_left (abs_nonneg _) hc1) h1
    calc (2 / Real.pi * |w.im|) ^ 2 ≤ |Real.sinh w.im| ^ 2 :=
          pow_le_pow_left₀ (by positivity) h2 2
      _ = Real.sinh w.im ^ 2 := sq_abs _
  have hsq : (2 / Real.pi * ‖w‖) ^ 2 ≤ ‖Complex.sin w‖ ^ 2 := by
    rw [norm_sin_sq, mul_pow]
    have hn : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hn]
    have e1 : (2 / Real.pi * |w.re|) ^ 2 = (2 / Real.pi) ^ 2 * w.re ^ 2 := by rw [mul_pow, sq_abs]
    have e2 : (2 / Real.pi * |w.im|) ^ 2 = (2 / Real.pi) ^ 2 * w.im ^ 2 := by rw [mul_pow, sq_abs]
    nlinarith [hsin, hsinh, e1, e2]
  exact le_of_pow_le_pow_left₀ two_ne_zero (norm_nonneg _) hsq

/-- **Size of the model on horizontal lines**: `‖F(x + iy)‖ ≤ cosh(Ly/2) + A e^{y²/L²}`. -/
theorem norm_cosBumpModel_le {L A : ℝ} (hA : 0 ≤ A) (x y : ℝ) :
    ‖cosBumpModel L A (x + y * I)‖ ≤ Real.cosh (L * y / 2) + A * Real.exp (y ^ 2 / L ^ 2) := by
  unfold cosBumpModel
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have h := norm_cos_le_cosh_im ((L : ℂ) * (x + y * I) / 2)
    have him : ((L : ℂ) * (x + y * I) / 2).im = L * y / 2 := by simp
    rwa [him] at h
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hA
    have hre : (-((x : ℂ) + y * I) ^ 2 / (L : ℂ) ^ 2).re = (y ^ 2 - x ^ 2) / L ^ 2 := by
      rw [show (L : ℂ) ^ 2 = ((L ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.div_ofReal_re]
      simp [sq]
    rw [hre]
    rcases eq_or_ne L 0 with hL | hL
    · simp [hL]
    · exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg x]) (by positivity)

/-! ### The nonreal zero -/

theorem differentiable_cosBumpHeat (L A t : ℝ) : Differentiable ℂ (cosBumpHeat L A t) := by
  unfold cosBumpHeat; fun_prop

/-- **A nonreal zero from `cosh a = B/E`.**  For `L ≥ 22`, `8t ≤ L²` and `2 ≤ a ≤ L` with
`E cosh a = B`, `E = e^{tL²/4}`, `B = A(1 − 4t/L²)^{−1/2}`, the flow `H_t` has a zero with positive
imaginary part within `1/L` of `(2/L)(π + ia)`. -/
theorem exists_nonreal_zero_cosBumpHeat_of_cosh {L A t a : ℝ} (hL : 22 ≤ L)
    (htL : 8 * t ≤ L ^ 2) (ha2 : 2 ≤ a) (haL : a ≤ L)
    (hcosh : Real.exp (t * L ^ 2 / 4) * Real.cosh a = A / Real.sqrt (1 - 4 * t / L ^ 2)) :
    ∃ z : ℂ, cosBumpHeat L A t z = 0 ∧ 0 < z.im := by
  have hL0 : 0 < L := by linarith
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (t * L ^ 2 / 4) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = A / Real.sqrt (1 - 4 * t / L ^ 2) := ⟨_, rfl⟩
  rw [← hE, ← hB] at hcosh
  have hE0 : 0 < E := by rw [hE]; exact Real.exp_pos _
  have hB0 : 0 ≤ B := by rw [← hcosh]; exact mul_nonneg hE0.le (Real.cosh_pos _).le
  obtain ⟨zs, hzs⟩ : ∃ zs : ℂ, zs = ((2 * Real.pi / L : ℝ) : ℂ) + ((2 * a / L : ℝ) : ℂ) * I :=
    ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℂ → ℂ, G = fun z => (E : ℂ) * Complex.cos (L * z / 2) + (B : ℂ) :=
    ⟨_, rfl⟩
  have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL0.ne'
  have hζs : (L : ℂ) * zs / 2 = (a : ℂ) * I + Real.pi := by
    rw [hzs]; push_cast; field_simp; ring
  have hcs : Complex.cos ((L : ℂ) * zs / 2) = -(Real.cosh a : ℂ) := by
    rw [hζs, Complex.cos_add_pi, Complex.cos_mul_I, ← Complex.ofReal_cosh]
  have hBE : (B : ℂ) = (E : ℂ) * (Real.cosh a : ℂ) := by rw [← hcosh]; push_cast; ring
  have hGs : G zs = 0 := by
    rw [hG]; simp only
    rw [hcs, hBE]; ring
  have hGd : Differentiable ℂ G := by rw [hG]; fun_prop
  have hr : (0 : ℝ) < 1 / L := by positivity
  have hHG : ∀ z : ℂ, cosBumpHeat L A t z - G z
      = (B : ℂ) * (Complex.exp (-(z ^ 2) / ((L : ℂ) ^ 2 - 4 * t)) - 1) := by
    intro z
    rw [hG]; simp only [cosBumpHeat]
    rw [← hE, ← hB]; ring
  -- the two sides on the circle `|z − z*| = 1/L`
  have hbd : ∀ z ∈ sphere zs (1 / L), ‖cosBumpHeat L A t z - G z‖ < ‖G z‖ := by
    intro z hz
    have hzr : ‖z - zs‖ = 1 / L := by simpa [dist_eq_norm] using hz
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w = ((L : ℂ) * z / 2 - (L : ℂ) * zs / 2) / 2 := ⟨_, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u : ℂ, u = ((L : ℂ) * z / 2 + (L : ℂ) * zs / 2) / 2 := ⟨_, rfl⟩
    have hGz : G z = (E : ℂ) * (-2 * Complex.sin u * Complex.sin w) := by
      rw [hG]; simp only
      rw [hBE, hu, hw, ← Complex.cos_sub_cos, hcs]; ring
    have hwn : ‖w‖ = 1 / 4 := by
      have : w = (L : ℂ) * (z - zs) / 4 := by rw [hw]; ring
      rw [this, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL0, hzr]
      norm_num; field_simp
    have hwre : |w.re| ≤ Real.pi / 2 := by
      have := Complex.abs_re_le_norm w
      linarith [Real.pi_gt_three]
    have hsw : 2 / Real.pi * (1 / 4) ≤ ‖Complex.sin w‖ := by
      have := two_div_pi_mul_norm_le_norm_sin hwre; rwa [hwn] at this
    have huim : a - 1 / 4 ≤ u.im := by
      have hue : u = (a : ℂ) * I + Real.pi + w := by rw [hu, hw, hζs]; ring
      have him := Complex.abs_im_le_norm w
      rw [hwn] at him
      have : u.im = a + w.im := by rw [hue]; simp
      rw [this]; linarith [(abs_le.mp him).1]
    have hsu : Real.sinh (a - 1 / 4) ≤ ‖Complex.sin u‖ :=
      (Real.sinh_le_sinh.mpr huim).trans (sinh_im_le_norm_sin u)
    -- `sinh(a − ¼) ≥ e^a/4`
    have hsinh : Real.exp a / 4 ≤ Real.sinh (a - 1 / 4) := by
      rw [Real.sinh_eq]
      have h1 : 3 / 4 * Real.exp a ≤ Real.exp (a - 1 / 4) := by
        rw [Real.exp_sub]
        have h2 : Real.exp (1 / 4) ≤ 4 / 3 := by
          have := Real.exp_bound' (x := 1 / 4) (by norm_num) (by norm_num) (n := 2) (by norm_num)
          norm_num [Finset.sum_range_succ, Nat.factorial] at this
          linarith
        rw [le_div_iff₀ (Real.exp_pos _)]
        nlinarith [Real.exp_pos a]
      have h3 : Real.exp (-(a - 1 / 4)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have h4 : 7 ≤ Real.exp a := by
        have h5 : Real.exp 2 ≤ Real.exp a := Real.exp_le_exp.mpr ha2
        have h6 : 7 ≤ Real.exp 2 := by
          have := Real.exp_one_gt_d9
          have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
          nlinarith
        linarith
      linarith
    have hGlow : Real.exp a * E / (4 * Real.pi) ≤ ‖G z‖ := by
      rw [hGz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hE0, norm_mul, norm_mul,
        norm_neg, Complex.norm_two]
      have hπ := Real.pi_pos
      have h1 : Real.exp a / 4 * (2 / Real.pi * (1 / 4)) ≤ ‖Complex.sin u‖ * ‖Complex.sin w‖ :=
        mul_le_mul (hsinh.trans hsu) hsw (by positivity) (norm_nonneg _)
      have e : Real.exp a * E / (4 * Real.pi)
          = E * (2 * (Real.exp a / 4 * (2 / Real.pi * (1 / 4)))) := by
        field_simp; ring
      rw [e]
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by norm_num : (0:ℝ) ≤ 2))
        hE0.le
      linarith
    have hzs_norm : ‖zs‖ ≤ (2 * Real.pi + 2 * a) / L := by
      refine (Complex.norm_le_abs_re_add_abs_im zs).trans ?_
      have hre : zs.re = 2 * Real.pi / L := by rw [hzs]; simp
      have him : zs.im = 2 * a / L := by rw [hzs]; simp
      rw [hre, him, abs_of_pos (by positivity), abs_of_pos (by positivity), ← add_div]
    have hz_norm : ‖z‖ ≤ 3 := by
      have h1 : ‖z‖ ≤ ‖zs‖ + 1 / L := by
        calc ‖z‖ = ‖zs + (z - zs)‖ := by ring_nf
          _ ≤ ‖zs‖ + ‖z - zs‖ := norm_add_le _ _
          _ = ‖zs‖ + 1 / L := by rw [hzr]
      have h2 : (2 * Real.pi + 2 * a) / L + 1 / L ≤ 3 := by
        rw [← add_div, div_le_iff₀ hL0]
        linarith [Real.pi_lt_d2]
      linarith
    have hden0 : 0 < L ^ 2 - 4 * t := by nlinarith
    have hv : ‖-(z ^ 2) / ((L : ℂ) ^ 2 - 4 * t)‖ ≤ 18 / L ^ 2 := by
      rw [show (L : ℂ) ^ 2 - 4 * t = ((L ^ 2 - 4 * t : ℝ) : ℂ) by push_cast; ring, norm_div,
        norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden0,
        div_le_div_iff₀ hden0 (by positivity)]
      have : ‖z‖ ^ 2 ≤ 9 := by nlinarith [norm_nonneg z]
      nlinarith
    have hv1 : 18 / L ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    have hexp := (Complex.norm_exp_sub_one_le (hv.trans hv1)).trans
      (mul_le_mul_of_nonneg_left hv (by norm_num : (0 : ℝ) ≤ 2))
    have hHGn : ‖cosBumpHeat L A t z - G z‖ ≤ B * (2 * (18 / L ^ 2)) := by
      rw [hHG, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB0]
      exact mul_le_mul_of_nonneg_left hexp hB0
    have hBle : B ≤ E * Real.exp a := by
      rw [← hcosh]
      refine mul_le_mul_of_nonneg_left ?_ hE0.le
      rw [Real.cosh_eq]
      have : Real.exp (-a) ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hk : 2 * (18 / L ^ 2) < 1 / (4 * Real.pi) := by
      rw [show 2 * (18 / L ^ 2) = 36 / L ^ 2 by ring, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [Real.pi_lt_d2]
    have hpos : 0 < E * Real.exp a := by positivity
    calc ‖cosBumpHeat L A t z - G z‖ ≤ B * (2 * (18 / L ^ 2)) := hHGn
      _ ≤ E * Real.exp a * (2 * (18 / L ^ 2)) := mul_le_mul_of_nonneg_right hBle (by positivity)
      _ < E * Real.exp a * (1 / (4 * Real.pi)) := mul_lt_mul_of_pos_left hk hpos
      _ = Real.exp a * E / (4 * Real.pi) := by ring
      _ ≤ ‖G z‖ := hGlow
  obtain ⟨z, hz, hz0⟩ := exists_zero_mem_ball_of_norm_sub_lt hGd (differentiable_cosBumpHeat L A t)
    hr hbd (mem_ball_self hr) hGs
  refine ⟨z, hz0, ?_⟩
  have h1 := Complex.abs_im_le_norm (z - zs)
  rw [mem_ball, dist_eq_norm] at hz
  have him : zs.im = 2 * a / L := by rw [hzs]; simp
  rw [Complex.sub_im, him] at h1
  have h2 : 1 / L < 2 * a / L := by
    rw [div_lt_div_iff_of_pos_right hL0]; linarith
  have h3 : |z.im - 2 * a / L| < 1 / L := lt_of_le_of_lt h1 hz
  linarith [(abs_lt.mp h3).1]

/-- **A Weyl bump keeps a nonreal zero below the horizon `4θ`.**  For `0 < θ ≤ ½` and
`0 ≤ κ < 4θ` there is `L₀` such that for every `L ≥ L₀` the de Bruijn flow at time `κ/L` of
`cos(Lz/2) + e^{θL} e^{−z²/L²}` has a zero with positive imaginary part. -/
theorem exists_nonreal_zero_cosBumpHeat {θ κ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 2) (hκ : 0 ≤ κ)
    (hκθ : κ < 4 * θ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
      ∃ z : ℂ, cosBumpHeat L (Real.exp (θ * L)) (κ / L) z = 0 ∧ 0 < z.im := by
  set ε := θ - κ / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  refine ⟨max 22 (2 / ε), by positivity, fun L hL => ?_⟩
  have hL22 : 22 ≤ L := (le_max_left _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hεL : 2 ≤ ε * L := by
    have := (le_max_right _ _).trans hL
    rw [div_le_iff₀ hε] at this; linarith
  set t := κ / L with htdef
  have ht : 0 ≤ t := by positivity
  have hκ2 : κ ≤ 2 := by linarith
  have htL : 8 * t ≤ L ^ 2 := by
    rw [htdef, mul_div_assoc', div_le_iff₀ hL0]; nlinarith
  have htL2 : t * L ^ 2 / 4 = κ * L / 4 := by rw [htdef]; field_simp
  set s := Real.sqrt (1 - 4 * t / L ^ 2) with hs
  have h4t : 4 * t / L ^ 2 ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have h4t0 : 0 ≤ 4 * t / L ^ 2 := by positivity
  have hs1 : s ≤ 1 := by rw [hs, Real.sqrt_le_one]; linarith
  have hs2 : 1 / 2 ≤ s := by
    rw [hs, show (1 / 2 : ℝ) = Real.sqrt (1 / 4) by rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs0 : 0 < s := by linarith
  set q := Real.exp (θ * L) / s / Real.exp (t * L ^ 2 / 4) with hq
  -- `q ≥ e^{εL} ≥ e² ≥ cosh 2` and `q ≤ 2 e^{θL}`
  have hqe : Real.exp (ε * L) ≤ q := by
    rw [hq, htL2, div_div, le_div_iff₀ (by positivity)]
    have e1 : Real.exp (ε * L) * (s * Real.exp (κ * L / 4)) = s * Real.exp (θ * L) := by
      rw [mul_comm s, ← mul_assoc, ← Real.exp_add, hεdef]; ring_nf
    rw [e1]
    exact mul_le_of_le_one_left (Real.exp_pos _).le hs1
  have hcosh2 : Real.cosh 2 ≤ q := by
    have h1 : Real.cosh 2 ≤ Real.exp 2 := by
      rw [Real.cosh_eq]; have := Real.exp_le_exp.mpr (show (-2 : ℝ) ≤ 2 by norm_num); linarith
    exact h1.trans ((Real.exp_le_exp.mpr hεL).trans hqe)
  have hq2 : q ≤ 2 * Real.exp (θ * L) := by
    rw [hq, div_le_iff₀ (Real.exp_pos _), div_le_iff₀ hs0]
    have h1 : 1 ≤ Real.exp (t * L ^ 2 / 4) := Real.one_le_exp (by positivity)
    have h2 : 1 ≤ 2 * Real.exp (t * L ^ 2 / 4) * s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (θ * L)).le]
  -- `cosh a = q` with `2 ≤ a ≤ L`
  have h1q : Real.cosh 0 ≤ q := by
    rw [Real.cosh_zero]; exact (Real.one_le_cosh 2).trans hcosh2
  have hqq : q ≤ Real.cosh q := by
    rw [Real.cosh_eq]
    have h1 := Real.add_one_le_exp (q / 2)
    have e : Real.exp q = Real.exp (q / 2) ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
    have h0 : 0 ≤ 1 + q / 2 := by linarith [(Real.one_le_cosh 2).trans hcosh2]
    have h3 : (1 + q / 2) ^ 2 ≤ Real.exp q := by
      rw [e]; exact pow_le_pow_left₀ h0 (by linarith) 2
    have h2 := Real.exp_pos (-q)
    nlinarith [sq_nonneg (1 - q / 2)]
  have hq0 : 0 ≤ q := le_trans (by norm_num) h1q
  obtain ⟨a, ⟨ha0, -⟩, hca⟩ := intermediate_value_Icc hq0 Real.continuous_cosh.continuousOn ⟨h1q, hqq⟩
  have ha2 : 2 ≤ a := by
    have : Real.cosh 2 ≤ Real.cosh a := hca ▸ hcosh2
    rw [Real.cosh_le_cosh, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_nonneg ha0] at this
    exact this
  have haL : a ≤ L := by
    have h1 : Real.exp a / 2 ≤ Real.cosh a := by
      rw [Real.cosh_eq]; have := Real.exp_pos (-a); linarith
    have h2 : Real.exp a ≤ 4 * Real.exp (θ * L) := by rw [hca] at h1; linarith
    have h3 : a ≤ Real.log 4 + θ * L := by
      have := Real.log_le_log (Real.exp_pos a) h2
      rwa [Real.log_exp, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
    have h4 : Real.log 4 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have e : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    nlinarith
  refine exists_nonreal_zero_cosBumpHeat_of_cosh hL22 htL ha2 haL ?_
  have hsq0 : Real.sqrt (1 - 4 * t / L ^ 2) ≠ 0 := by rw [← hs]; exact hs0.ne'
  rw [hca, hq, hs]
  field_simp

end

end RHTower.DeBruijn
