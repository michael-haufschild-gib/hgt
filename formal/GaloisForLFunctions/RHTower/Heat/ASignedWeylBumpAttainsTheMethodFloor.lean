import GaloisForLFunctions.RHTower.Heat.AWeylBumpBreaksSizeOnlyRepair

/-!
# A signed Weyl bump attains the size-only method floor `27/40`

The low-order step of size-only repair (`exists_xiSliceHeatTransfer_pos_low_order_interior`) needs,
for the first size profile `t^{−(p + s(½ − |a|))}` (`p = s = 1/9`), the gap
`κ/2 − (½ + 2η) + (p + s/2) − s²κ/2 > 0`, i.e. `κ(1 − s²) > 2θ` with `θ = ½ + 2η − p − s/2`.  At
`η → 0` this is `κ > (2/3)/(80/81) = 27/40`.  This file shows that the condition is exact for these
inputs.

Let `0 ≤ s ≤ 1`, `A = e^{θL}` and

  `g(x) = cosh(Lx) − A cosh(sLx)`        (`signedBumpModel`).

* **Size** (`norm_signedBumpModelC_le_profiles`): with `η ≥ 0`, `θ ≤ ½ + 2η − p − s/2`, `c₂ ≤ 1`,
  `|a| ≤ ½ + η` and `4A e^{sL(½+2η)} ≤ e^{L(½+2η)}`, the entire extension satisfies
  `‖g(a + ic)‖ ≤ 4 g(½ + 2η)(e^{−L(p + s(½ − |a|))} + e^{−L(η + c₂(½ + η − |a|))})`.
* **Euler points** (`signedBumpModel_mul_pow_le_iteratedDeriv`): `g^{(n)}(x₀) ≥ g(x₀) Lⁿ/4` for every
  `n` once `L ≥ 1`, `Lx₀ ≥ 1` and `4A e^{sLx₀} ≤ e^{Lx₀}`.
* **Heat** (`signedBumpHeat_eq`, `hasSum_signedBumpHeatCoeff`): the Gaussian average of variance `λ`
  is `e^{λL²/2} cosh(Lx) − A e^{λs²L²/2} cosh(sLx)`, with `x^{2m}` coefficient
  `(e^{λL²/2} L^{2m} − A e^{λs²L²/2} (sL)^{2m})/(2m)!`.
* **Exact threshold** (`signedBumpHeatCoeff_nonneg`, `signedBumpHeatCoeff_two_neg`): at heat `κ/L`
  every coefficient is `≥ 0` when `κ(1 − s²) ≥ 2θ` (`L ≥ 1`), and the `x²` coefficient is negative
  for all large `L` when `0 < κ` and `κ(1 − s²) < 2θ`.

With `p = s = 1/9` and `θ = 1/3` the threshold is `27/40`: the size inputs alone do not prove repair
at any lower rate.  The model is negative near `0` (`signedBumpModel_zero_lt_zero`).  The positive
Weyl bump (`AWeylBumpBreaksSizeOnlyRepair`) meets the same inputs and is `≥ 1` on the real axis, with
threshold `2θ`.  So below `27/40` an argument must use the positivity of the slice on the real axis,
and with it the floor is at least `2/3`.
-/

open MeasureTheory Filter Topology

namespace RHTower.DeBruijn

noncomputable section

/-- The signed Weyl bump `g(x) = cosh(Lx) − A cosh(sLx)`. -/
def signedBumpModel (L s A x : ℝ) : ℝ := Real.cosh (L * x) - A * Real.cosh (s * L * x)

theorem signedBumpModel_zero_lt_zero {L s A : ℝ} (hA : 1 < A) : signedBumpModel L s A 0 < 0 := by
  simp [signedBumpModel, hA]

/-! ### Size on the critical band -/

/-- The entire extension `cosh(Lz) − A cosh(sLz)`. -/
def signedBumpModelC (L s A : ℝ) (z : ℂ) : ℂ :=
  (Complex.exp (L * z) + Complex.exp (-(L * z))) / 2 -
    A * ((Complex.exp (s * L * z) + Complex.exp (-(s * L * z))) / 2)

theorem norm_cosh_combination_le (μ a c : ℝ) :
    ‖(Complex.exp (μ * (a + c * Complex.I)) + Complex.exp (-(μ * (a + c * Complex.I)))) / 2‖ ≤
      Real.cosh (μ * a) := by
  have e1 : ‖Complex.exp (μ * (a + c * Complex.I))‖ = Real.exp (μ * a) := by
    rw [Complex.norm_exp]; simp
  have e2 : ‖Complex.exp (-(μ * (a + c * Complex.I)))‖ = Real.exp (-(μ * a)) := by
    rw [Complex.norm_exp]; simp
  rw [norm_div, Complex.norm_two, Real.cosh_eq]
  have := norm_add_le (Complex.exp (μ * (a + c * Complex.I)))
    (Complex.exp (-(μ * (a + c * Complex.I))))
  rw [e1, e2] at this
  linarith

/-- `‖g(a + ic)‖ ≤ cosh(La) + A cosh(sLa)`. -/
theorem norm_signedBumpModelC_le {A : ℝ} (hA : 0 ≤ A) (L s a c : ℝ) :
    ‖signedBumpModelC L s A (a + c * Complex.I)‖ ≤ Real.cosh (L * a) + A * Real.cosh (s * L * a) := by
  unfold signedBumpModelC
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
  have h1 := norm_cosh_combination_le L a c
  have h2 := norm_cosh_combination_le (s * L) a c
  push_cast at h2
  have := mul_le_mul_of_nonneg_left h2 hA
  linarith

/-- **The signed bump satisfies the two-profile size bound.**  For `L ≥ 0`, `0 ≤ s`, `0 ≤ η`,
`θ ≤ ½ + 2η − p − s/2`, `c₂ ≤ 1`, `|a| ≤ ½ + η`, and `4A e^{sL(½+2η)} ≤ e^{L(½+2η)}`, `A = e^{θL}`:
`‖g(a + ic)‖ ≤ 4 g(½ + 2η)(e^{−L(p + s(½ − |a|))} + e^{−L(η + c₂(½ + η − |a|))})`. -/
theorem norm_signedBumpModelC_le_profiles {L s θ η p c₂ a c : ℝ} (hL : 0 ≤ L) (hs : 0 ≤ s)
    (hη : 0 ≤ η) (hθ : θ ≤ 1 / 2 + 2 * η - p - s / 2) (hc₂1 : c₂ ≤ 1) (ha : |a| ≤ 1 / 2 + η)
    (hA4 : 4 * Real.exp (θ * L) * Real.exp (s * L * (1 / 2 + 2 * η)) ≤
      Real.exp (L * (1 / 2 + 2 * η))) :
    ‖signedBumpModelC L s (Real.exp (θ * L)) (a + c * Complex.I)‖ ≤
      4 * signedBumpModel L s (Real.exp (θ * L)) (1 / 2 + 2 * η) *
        (Real.exp (-(L * (p + s * (1 / 2 - |a|)))) +
          Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|))))) := by
  set A := Real.exp (θ * L) with hAdef
  set G := signedBumpModel L s A (1 / 2 + 2 * η) with hG
  set E := Real.exp (L * (1 / 2 + 2 * η)) with hE
  have hA0 : 0 < A := Real.exp_pos _
  have hN := norm_signedBumpModelC_le hA0.le L s a c
  -- `G ≥ e^{L(½ + 2η)}/4`
  have hGE : E / 4 ≤ G := by
    have h1 : E / 2 ≤ Real.cosh (L * (1 / 2 + 2 * η)) := by
      rw [Real.cosh_eq]; have := Real.exp_pos (-(L * (1 / 2 + 2 * η))); linarith
    have h2 : Real.cosh (s * L * (1 / 2 + 2 * η)) ≤ Real.exp (s * L * (1 / 2 + 2 * η)) := by
      have := cosh_le_exp_abs (s * L * (1 / 2 + 2 * η))
      have hpos : 0 ≤ s * L * (1 / 2 + 2 * η) := by
        have : 0 ≤ 1 / 2 + 2 * η := by linarith
        positivity
      rwa [abs_of_nonneg hpos] at this
    have h3 := mul_le_mul_of_nonneg_left h2 hA0.le
    rw [hG]; unfold signedBumpModel; linarith
  have hG0 : 0 ≤ G := by linarith [Real.exp_pos (L * (1 / 2 + 2 * η))]
  -- the background
  have hbg : Real.cosh (L * a) ≤ 4 * G * Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|)))) := by
    have h1 : Real.cosh (L * a) ≤ Real.exp (L * |a|) := by
      have := cosh_le_exp_abs (L * a)
      rwa [abs_mul, abs_of_nonneg hL] at this
    have h2 : L * |a| ≤ L * (1 / 2 + 2 * η) + -(L * (η + c₂ * (1 / 2 + η - |a|))) := by
      have : (1 - c₂) * (1 / 2 + η - |a|) ≥ 0 := mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonneg hL this]
    have h3 : Real.exp (L * |a|) ≤ E * Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|)))) := by
      rw [hE, ← Real.exp_add]; exact Real.exp_le_exp.mpr h2
    have h4 : E * Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|))))
        ≤ 4 * G * Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|)))) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    linarith
  -- the bump
  have hbump : A * Real.cosh (s * L * a) ≤ 4 * G * Real.exp (-(L * (p + s * (1 / 2 - |a|)))) := by
    have h1 : Real.cosh (s * L * a) ≤ Real.exp (s * L * |a|) := by
      have := cosh_le_exp_abs (s * L * a)
      rwa [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg hL] at this
    have h2 : θ * L + s * L * |a| ≤ L * (1 / 2 + 2 * η) + -(L * (p + s * (1 / 2 - |a|))) := by
      nlinarith [mul_le_mul_of_nonneg_left hθ hL]
    have h3 : A * Real.exp (s * L * |a|) ≤ E * Real.exp (-(L * (p + s * (1 / 2 - |a|)))) := by
      rw [hAdef, hE, ← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr h2
    have h4 : E * Real.exp (-(L * (p + s * (1 / 2 - |a|))))
        ≤ 4 * G * Real.exp (-(L * (p + s * (1 / 2 - |a|)))) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left h1 hA0.le
    linarith
  calc ‖signedBumpModelC L s A (a + c * Complex.I)‖
      ≤ Real.cosh (L * a) + A * Real.cosh (s * L * a) := hN
    _ ≤ 4 * G * Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|)))) +
        4 * G * Real.exp (-(L * (p + s * (1 / 2 - |a|)))) := add_le_add hbg hbump
    _ = _ := by ring

/-! ### Euler points -/

theorem iteratedDeriv_signedBumpModel (L s A : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (signedBumpModel L s A) x =
      (L ^ n * Real.exp (L * x) + (-L) ^ n * Real.exp (-L * x)) / 2 -
        A * (((s * L) ^ n * Real.exp (s * L * x) + (-(s * L)) ^ n * Real.exp (-(s * L) * x)) / 2) := by
  have hfun : signedBumpModel L s A =
      (fun y => Real.cosh (L * y)) - fun y => A * Real.cosh ((s * L) * y) := rfl
  have hc1 : ContDiffAt ℝ n (fun y => Real.cosh (L * y)) x :=
    (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hc2 : ContDiffAt ℝ n (fun y => Real.cosh ((s * L) * y)) x :=
    (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).contDiffAt
  rw [hfun, iteratedDeriv_sub hc1 (contDiffAt_const.mul hc2), iteratedDeriv_cosh_mul,
    iteratedDeriv_const_mul _ hc2, iteratedDeriv_cosh_mul]

/-- **The signed bump satisfies the Euler-point bound.**  For every `n`, `L ≥ 1`, `0 ≤ s ≤ 1`,
`A ≥ 0`, `Lx₀ ≥ 1`, `0 ≤ x₀` and `4A e^{sLx₀} ≤ e^{Lx₀}`: `g(x₀) Lⁿ/4 ≤ g^{(n)}(x₀)`. -/
theorem signedBumpModel_mul_pow_le_iteratedDeriv {L s A x₀ : ℝ} {n : ℕ} (hL : 1 ≤ L)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hA : 0 ≤ A) (hx₀ : 0 ≤ x₀) (hLx : 1 ≤ L * x₀)
    (hAx : 4 * A * Real.exp (s * L * x₀) ≤ Real.exp (L * x₀)) :
    signedBumpModel L s A x₀ * L ^ n / 4 ≤ iteratedDeriv n (signedBumpModel L s A) x₀ := by
  rw [iteratedDeriv_signedBumpModel]
  set E := Real.exp (L * x₀) with hE
  set F := Real.exp (-L * x₀) with hF
  set e := Real.exp (s * L * x₀) with he
  set f := Real.exp (-(s * L) * x₀) with hf
  set P := L ^ n with hP
  have hEF : E * F = 1 := by rw [hE, hF, ← Real.exp_add]; simp
  have hE1 : Real.exp 1 ≤ E := Real.exp_le_exp.mpr hLx
  have he27 : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hF0 : 0 < F := Real.exp_pos _
  have hFE : 7 * F ≤ E := by nlinarith
  have hP1 : 1 ≤ P := one_le_pow₀ hL
  have hsign : -P ≤ (-L) ^ n := by
    rcases Nat.even_or_odd n with h | h
    · rw [h.neg_pow]; linarith
    · rw [h.neg_pow]
  -- the subtracted part is at most `A (sL)ⁿ e^{sLx₀} ≤ A P e`
  have hsL : (s * L) ^ n ≤ P := by
    rw [hP]; exact pow_le_pow_left₀ (by positivity) (by nlinarith) n
  have hsL0 : 0 ≤ (s * L) ^ n := by positivity
  have hfe : f ≤ e := Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (mul_nonneg hs0 (by linarith : (0:ℝ) ≤ L)) hx₀])
  have hsub : ((s * L) ^ n * e + (-(s * L)) ^ n * f) / 2 ≤ P * e := by
    have h1 : (-(s * L)) ^ n * f ≤ (s * L) ^ n * f := by
      rcases Nat.even_or_odd n with h | h
      · rw [h.neg_pow]
      · rw [h.neg_pow]; nlinarith [Real.exp_pos (-(s * L) * x₀)]
    have h2 : (s * L) ^ n * f ≤ (s * L) ^ n * e := mul_le_mul_of_nonneg_left hfe hsL0
    have h3 : (s * L) ^ n * e ≤ P * e := mul_le_mul_of_nonneg_right hsL (Real.exp_pos _).le
    linarith
  have hg : signedBumpModel L s A x₀ ≤ (E + F) / 2 := by
    unfold signedBumpModel
    rw [Real.cosh_eq, ← hE, show -(L * x₀) = -L * x₀ by ring, ← hF]
    have := mul_nonneg hA (Real.cosh_pos (s * L * x₀)).le
    linarith
  have h1 : (-L) ^ n * F ≥ -P * F := mul_le_mul_of_nonneg_right hsign hF0.le
  have h3 : P * F ≤ P * E / 7 := by nlinarith
  have h4 : A * (P * e) ≤ P * E / 4 := by
    have := mul_le_mul_of_nonneg_left hAx (by linarith : (0 : ℝ) ≤ P)
    nlinarith
  have h5 : A * (((s * L) ^ n * e + (-(s * L)) ^ n * f) / 2) ≤ A * (P * e) :=
    mul_le_mul_of_nonneg_left hsub hA
  have h6 : signedBumpModel L s A x₀ * P ≤ (E + F) / 2 * P :=
    mul_le_mul_of_nonneg_right hg (by linarith)
  nlinarith

/-! ### Heat -/

/-- The heated signed bump: the Gaussian average of variance `λ`. -/
def signedBumpHeat (L s A lam x : ℝ) : ℝ :=
  ∫ u : ℝ, DeBruijn.gaussDensity (lam / 2) u * signedBumpModel L s A (x + u)

/-- **Closed form.** `H(x) = e^{λL²/2} cosh(Lx) − A e^{λs²L²/2} cosh(sLx)`. -/
theorem signedBumpHeat_eq {lam : ℝ} (hlam : 0 < lam) (L s A x : ℝ) :
    signedBumpHeat L s A lam x = Real.exp (lam * L ^ 2 / 2) * Real.cosh (L * x) -
      A * (Real.exp (lam * (s * L) ^ 2 / 2) * Real.cosh (s * L * x)) := by
  set t := lam / 2 with htdef
  have ht : 0 < t := by positivity
  have hi1 := integrable_filterGauss_mul_rexp ht L
  have hi2 := integrable_filterGauss_mul_rexp ht (-L)
  have hi3 := integrable_filterGauss_mul_rexp ht (s * L)
  have hi4 := integrable_filterGauss_mul_rexp ht (-(s * L))
  have j1 : Integrable fun u => Real.exp (L * x) / 2 * (filterGauss t u * Real.exp (u * L)) :=
    hi1.const_mul _
  have j2 : Integrable fun u =>
      Real.exp (-(L * x)) / 2 * (filterGauss t u * Real.exp (u * -L)) := hi2.const_mul _
  have j3 : Integrable fun u =>
      A * Real.exp (s * L * x) / 2 * (filterGauss t u * Real.exp (u * (s * L))) := hi3.const_mul _
  have j4 : Integrable fun u =>
      A * Real.exp (-(s * L * x)) / 2 * (filterGauss t u * Real.exp (u * -(s * L))) :=
    hi4.const_mul _
  have j12 : Integrable fun u => Real.exp (L * x) / 2 * (filterGauss t u * Real.exp (u * L)) +
      Real.exp (-(L * x)) / 2 * (filterGauss t u * Real.exp (u * -L)) := j1.add j2
  have j123 : Integrable fun u => Real.exp (L * x) / 2 * (filterGauss t u * Real.exp (u * L)) +
      Real.exp (-(L * x)) / 2 * (filterGauss t u * Real.exp (u * -L)) -
      A * Real.exp (s * L * x) / 2 * (filterGauss t u * Real.exp (u * (s * L))) := j12.sub j3
  have hpt : ∀ u : ℝ, DeBruijn.gaussDensity t u * signedBumpModel L s A (x + u) =
      Real.exp (L * x) / 2 * (filterGauss t u * Real.exp (u * L)) +
        Real.exp (-(L * x)) / 2 * (filterGauss t u * Real.exp (u * -L)) -
        A * Real.exp (s * L * x) / 2 * (filterGauss t u * Real.exp (u * (s * L))) -
        A * Real.exp (-(s * L * x)) / 2 * (filterGauss t u * Real.exp (u * -(s * L))) := by
    intro u
    rw [gaussDensity_eq_filterGauss]
    unfold signedBumpModel
    have e1 : Real.exp (L * (x + u)) = Real.exp (L * x) * Real.exp (u * L) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(L * (x + u))) = Real.exp (-(L * x)) * Real.exp (u * -L) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp (s * L * (x + u)) = Real.exp (s * L * x) * Real.exp (u * (s * L)) := by
      rw [← Real.exp_add]; ring_nf
    have e4 : Real.exp (-(s * L * (x + u))) =
        Real.exp (-(s * L * x)) * Real.exp (u * -(s * L)) := by
      rw [← Real.exp_add]; ring_nf
    rw [Real.cosh_eq, Real.cosh_eq, e1, e2, e3, e4]
    ring
  unfold signedBumpHeat
  rw [show (fun u : ℝ => DeBruijn.gaussDensity t u * signedBumpModel L s A (x + u)) = fun u =>
      Real.exp (L * x) / 2 * (filterGauss t u * Real.exp (u * L)) +
        Real.exp (-(L * x)) / 2 * (filterGauss t u * Real.exp (u * -L)) -
        A * Real.exp (s * L * x) / 2 * (filterGauss t u * Real.exp (u * (s * L))) -
        A * Real.exp (-(s * L * x)) / 2 * (filterGauss t u * Real.exp (u * -(s * L)))
      from funext hpt]
  rw [integral_sub j123 j4, integral_sub j12 j3, integral_add j1 j2, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_filterGauss_mul_rexp ht,
    integral_filterGauss_mul_rexp ht, integral_filterGauss_mul_rexp ht,
    integral_filterGauss_mul_rexp ht, Real.cosh_eq, Real.cosh_eq]
  have e5 : t * (-L) ^ 2 = lam * L ^ 2 / 2 := by rw [htdef]; ring
  have e6 : t * L ^ 2 = lam * L ^ 2 / 2 := by rw [htdef]; ring
  have e7 : t * (s * L) ^ 2 = lam * (s * L) ^ 2 / 2 := by rw [htdef]; ring
  have e8 : t * (-(s * L)) ^ 2 = lam * (s * L) ^ 2 / 2 := by rw [htdef]; ring
  rw [e5, e6, e7, e8]
  ring

/-- The Taylor coefficients at `0` of the heated signed bump. -/
def signedBumpHeatCoeff (L s A lam : ℝ) (n : ℕ) : ℝ :=
  if Even n then
    (Real.exp (lam * L ^ 2 / 2) * L ^ n - A * Real.exp (lam * (s * L) ^ 2 / 2) * (s * L) ^ n) /
      n.factorial
  else 0

/-- The heated signed bump is the sum of its power series at `0`. -/
theorem hasSum_signedBumpHeatCoeff {lam : ℝ} (hlam : 0 < lam) (L s A x : ℝ) :
    HasSum (fun n : ℕ => signedBumpHeatCoeff L s A lam n * x ^ n) (signedBumpHeat L s A lam x) := by
  rw [signedBumpHeat_eq hlam]
  have h1 := (Real.hasSum_cosh (L * x)).mul_left (Real.exp (lam * L ^ 2 / 2))
  have h2 := ((Real.hasSum_cosh (s * L * x)).mul_left
    (Real.exp (lam * (s * L) ^ 2 / 2))).mul_left A
  have h := h1.sub h2
  have hinj : Function.Injective (fun m : ℕ => 2 * m) := fun a b hab => by
    simp only at hab; omega
  have hzero : ∀ n ∉ Set.range (fun m : ℕ => 2 * m),
      signedBumpHeatCoeff L s A lam n * x ^ n = 0 := by
    intro n hn
    have hne : ¬ Even n := fun he => hn ⟨n / 2, by obtain ⟨r, hr⟩ := he; simp only; omega⟩
    simp [signedBumpHeatCoeff, hne]
  rw [← hinj.hasSum_iff hzero]
  have hfun : ((fun n => signedBumpHeatCoeff L s A lam n * x ^ n) ∘ fun m : ℕ => 2 * m) = fun b =>
      Real.exp (lam * L ^ 2 / 2) * ((L * x) ^ (2 * b) / ((2 * b).factorial : ℝ)) -
        A * (Real.exp (lam * (s * L) ^ 2 / 2) * ((s * L * x) ^ (2 * b) / ((2 * b).factorial : ℝ))) := by
    funext m
    simp only [Function.comp, signedBumpHeatCoeff, if_pos (even_two_mul m)]
    rw [mul_pow, mul_pow (s * L)]
    ring
  rw [hfun]
  exact h

/-! ### The exact threshold `2θ/(1 − s²)` -/

/-- **Positivity from rate `2θ/(1 − s²)`.**  For `L ≥ 1`, `0 ≤ s ≤ 1` and `κ(1 − s²) ≥ 2θ`, every
Taylor coefficient of the heated signed bump at heat `κ/L`, `A = e^{θL}`, is nonnegative. -/
theorem signedBumpHeatCoeff_nonneg {L s θ κ : ℝ} (hL : 1 ≤ L) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hθκ : 2 * θ ≤ κ * (1 - s ^ 2)) (n : ℕ) :
    0 ≤ signedBumpHeatCoeff L s (Real.exp (θ * L)) (κ / L) n := by
  unfold signedBumpHeatCoeff
  split_ifs with he
  · have hL0 : 0 < L := by linarith
    have hexp : Real.exp (θ * L) * Real.exp (κ / L * (s * L) ^ 2 / 2) ≤
        Real.exp (κ / L * L ^ 2 / 2) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have e1 : κ / L * (s * L) ^ 2 / 2 = κ * s ^ 2 * L / 2 := by field_simp
      have e2 : κ / L * L ^ 2 / 2 = κ * L / 2 := by field_simp
      rw [e1, e2]
      nlinarith
    have hpow : (s * L) ^ n ≤ L ^ n := pow_le_pow_left₀ (by positivity) (by nlinarith) n
    have hnum : Real.exp (θ * L) * Real.exp (κ / L * (s * L) ^ 2 / 2) * (s * L) ^ n ≤
        Real.exp (κ / L * L ^ 2 / 2) * L ^ n :=
      mul_le_mul hexp hpow (by positivity) (Real.exp_pos _).le
    exact div_nonneg (by linarith) (Nat.cast_nonneg _)
  · exact le_rfl

/-- **Failure below rate `2θ/(1 − s²)`.**  For `0 < s ≤ 1`, `0 < κ` and `κ(1 − s²) < 2θ`, there is
`L₀` such that for `L ≥ L₀` the `x²` coefficient of the heated signed bump at heat `κ/L`,
`A = e^{θL}`, is negative. -/
theorem signedBumpHeatCoeff_two_neg {s θ κ : ℝ} (hs0 : 0 < s) (hκ : 0 < κ)
    (hθκ : κ * (1 - s ^ 2) < 2 * θ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀, signedBumpHeatCoeff L s (Real.exp (θ * L)) (κ / L) 2 < 0 := by
  set ε := θ - κ * (1 - s ^ 2) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  -- `e^{εL} > 1/s²` for `L > 1/(ε s²)`
  refine ⟨1 / (ε * s ^ 2) + 1, by positivity, fun L hL => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  unfold signedBumpHeatCoeff
  rw [if_pos (by decide : Even 2)]
  have hfac : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [hfac]
  refine div_neg_of_neg_of_pos ?_ (by norm_num)
  have e1 : κ / L * (s * L) ^ 2 / 2 = κ * s ^ 2 * L / 2 := by field_simp
  have e2 : κ / L * L ^ 2 / 2 = κ * L / 2 := by field_simp
  rw [e1, e2]
  -- `e^{θL} e^{κs²L/2} s² = e^{κL/2} e^{εL} s² > e^{κL/2}`
  have hsplit : Real.exp (θ * L) * Real.exp (κ * s ^ 2 * L / 2) =
      Real.exp (κ * L / 2) * Real.exp (ε * L) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; rw [hεdef]; ring
  have hεL : 1 < Real.exp (ε * L) * s ^ 2 := by
    have h1 := Real.add_one_le_exp (ε * L)
    have h2 : 1 / s ^ 2 < ε * L := by
      have hL' : 1 / (ε * s ^ 2) < L := by linarith
      rw [div_lt_iff₀ (by positivity)] at hL'
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    have h3 : 1 / s ^ 2 < Real.exp (ε * L) := by linarith
    rw [div_lt_iff₀ (by positivity)] at h3
    linarith
  have hE0 := Real.exp_pos (κ * L / 2)
  have hL2 : 0 < L ^ 2 := by positivity
  have : Real.exp (κ * L / 2) * L ^ 2 <
      Real.exp (θ * L) * Real.exp (κ * s ^ 2 * L / 2) * (s * L) ^ 2 := by
    rw [hsplit, mul_pow]
    have := mul_lt_mul_of_pos_left hεL (mul_pos hE0 hL2)
    nlinarith
  linarith

end

end RHTower.DeBruijn
