import GaloisForLFunctions.RHTower.DeBruijnHeatGaussianAverage
import GaloisForLFunctions.RHTower.GaussianPoleFilter

/-!
# A Weyl bump breaks size-only repair below `2θ`

Size-only repair of the heated slice (`exists_xiSliceHeatTransfer_pos_heat_interior`, rate `17/25`)
uses two inputs about `S(t, ·)`, `L = log t`:

* the two-profile bound (`exists_norm_xiSliceProduct_le_two_profiles`): on `|a| < ½ + η`, `|c| ≤ R`,
  `‖S(t, a + ic)‖ ≤ C S(t, ½ + 2η) (t^{−(1/9 + (1/9)(½ − |a|))} + t^{−(η + c₂(½ + η − |a|))})`;
  at `a = 0` its first profile is Weyl's `t^{−1/6}`;
* the Euler-point bound (`exists_iteratedDeriv_xiSliceProduct_ge_euler_from`): for `x₀ ≥ ½ + 2η`,
  `S^{(n)}(t, x₀)/n! ≥ S(t, x₀) L′ⁿ/n! · 1/(40π√(2L))`, `L′ ≤ L`.

This file gives an even, positive, entire function that satisfies both inputs and still has a
negative heated Taylor coefficient at `0`, at every heat rate below `2θ`:

  `g(x) = cosh(Lx) + A(1 + cos x)`,   `A = e^{θL}`        (`weylBumpModel`),

a cosh background of zero density `L/2π` plus a bump of height `2A` at the centre.

* **Size** (`norm_weylBumpModelC_le_two_profiles`): for `θ ≤ 1/3 + 2η` and `c₂ ≤ 1` the entire
  extension satisfies the two-profile bound with `C = 2(1 + cosh R)`.
* **Euler points** (`weylBumpModel_mul_pow_le_iteratedDeriv`): `g^{(n)}(x₀) ≥ g(x₀) Lⁿ/4` for
  `n ≥ 1` once `L ≥ 1`, `Lx₀ ≥ 1` and `12A ≤ e^{Lx₀}`.
* **Sign on the real axis** (`one_le_weylBumpModel`, `weylBumpModel_neg`): `g ≥ 1` and `g` is even.
* **Heat** (`weylBumpHeat_eq`, `hasSum_weylBumpHeatCoeff`): the Gaussian average of variance `λ` is
  `e^{λL²/2} cosh(Lx) + A(1 + e^{−λ/2} cos x)`; its coefficient of `x^{2m}`, `m ≥ 1`, is
  `(e^{λL²/2} L^{2m} + (−1)^m A e^{−λ/2})/(2m)!`.
* **Exact threshold** (`weylBumpHeatCoeff_nonneg`, `not_exists_nonneg_hasSum_weylBumpHeat`): at heat
  `κ/L`, every coefficient is `≥ 0` when `0 ≤ κ`, `2θ ≤ κ` and `L ≥ 1`; when `0 < κ < 2θ`, for all
  large `L` the heated model has no power series at `0` with nonnegative coefficients.

With `θ = 1/3` the model satisfies both inputs for every `η > 0` and all large `L`, together with
positivity and evenness on the real axis, and its threshold is `2/3`. So no argument from these
inputs proves repair below the rate `2/3`. The bump is a centre-concave defect: its heated `x²`
coefficient is `(e^{κL/2} L² − e^{θL − κ/(2L)})/2`.
-/

open MeasureTheory Filter Topology

namespace RHTower.DeBruijn

noncomputable section

/-- The Weyl bump model `g(x) = cosh(Lx) + A(1 + cos x)`. -/
def weylBumpModel (L A x : ℝ) : ℝ := Real.cosh (L * x) + A * (1 + Real.cos x)

theorem weylBumpModel_neg (L A x : ℝ) : weylBumpModel L A (-x) = weylBumpModel L A x := by
  unfold weylBumpModel
  rw [mul_neg, Real.cosh_neg, Real.cos_neg]

theorem one_le_weylBumpModel {A : ℝ} (hA : 0 ≤ A) (L x : ℝ) : 1 ≤ weylBumpModel L A x := by
  have h1 := Real.one_le_cosh (L * x)
  have h2 : 0 ≤ 1 + Real.cos x := by linarith [Real.neg_one_le_cos x]
  unfold weylBumpModel
  nlinarith [mul_nonneg hA h2]

/-! ### Size on the critical band -/

/-- The entire extension `cosh(Lz) + A(1 + cos z)`. -/
def weylBumpModelC (L A : ℝ) (z : ℂ) : ℂ :=
  (Complex.exp (L * z) + Complex.exp (-(L * z))) / 2 +
    A * (1 + (Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2)

theorem weylBumpModelC_ofReal (L A x : ℝ) :
    weylBumpModelC L A x = (weylBumpModel L A x : ℂ) := by
  unfold weylBumpModelC weylBumpModel
  rw [show (Complex.exp ((x : ℂ) * Complex.I) + Complex.exp (-(x : ℂ) * Complex.I)) / 2 =
    Complex.cos x from rfl, Real.cosh_eq]
  push_cast
  ring

/-- `‖cosh(L(a + ic)) + A(1 + cos(a + ic))‖ ≤ cosh(La) + A(1 + cosh c)`. -/
theorem norm_weylBumpModelC_le {A : ℝ} (hA : 0 ≤ A) (L a c : ℝ) :
    ‖weylBumpModelC L A (a + c * Complex.I)‖ ≤ Real.cosh (L * a) + A * (1 + Real.cosh c) := by
  unfold weylBumpModelC
  have e1 : ‖Complex.exp (L * (a + c * Complex.I))‖ = Real.exp (L * a) := by
    rw [Complex.norm_exp]; simp
  have e2 : ‖Complex.exp (-(L * (a + c * Complex.I)))‖ = Real.exp (-(L * a)) := by
    rw [Complex.norm_exp]; simp
  have e3 : ‖Complex.exp ((a + c * Complex.I) * Complex.I)‖ = Real.exp (-c) := by
    rw [Complex.norm_exp]; simp
  have e4 : ‖Complex.exp (-(a + c * Complex.I) * Complex.I)‖ = Real.exp c := by
    rw [Complex.norm_exp]; simp
  have hb1 : ‖(Complex.exp (L * (a + c * Complex.I)) + Complex.exp (-(L * (a + c * Complex.I)))) / 2‖
      ≤ Real.cosh (L * a) := by
    rw [norm_div, Complex.norm_two, Real.cosh_eq]
    have := norm_add_le (Complex.exp (L * (a + c * Complex.I)))
      (Complex.exp (-(L * (a + c * Complex.I))))
    rw [e1, e2] at this
    linarith
  have hb2 : ‖(1 : ℂ) + (Complex.exp ((a + c * Complex.I) * Complex.I) +
      Complex.exp (-(a + c * Complex.I) * Complex.I)) / 2‖ ≤ 1 + Real.cosh c := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_div, Complex.norm_two, Real.cosh_eq]
    have := norm_add_le (Complex.exp ((a + c * Complex.I) * Complex.I))
      (Complex.exp (-(a + c * Complex.I) * Complex.I))
    rw [e3, e4] at this
    linarith
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA]
  have := mul_le_mul_of_nonneg_left hb2 hA
  linarith

theorem cosh_le_exp_abs (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [Real.cosh_eq]
  have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
  have h2 : Real.exp (-x) ≤ Real.exp |x| := Real.exp_le_exp.mpr (neg_le_abs x)
  linarith

/-- **The Weyl bump satisfies the two-profile size bound.** For `L ≥ 0`, `θ ≤ 1/3 + 2η`,
`c₂ ≤ 1`, `|a| ≤ ½ + η` and `|c| ≤ R`, with `A = e^{θL}`,
`‖g(a + ic)‖ ≤ 2(1 + cosh R) g(½ + 2η) (e^{−L(1/9 + (1/9)(½ − |a|))} + e^{−L(η + c₂(½ + η − |a|))})`. -/
theorem norm_weylBumpModelC_le_two_profiles {L θ η c₂ R a c : ℝ} (hL : 0 ≤ L)
    (hθ : θ ≤ 1 / 3 + 2 * η) (hc₂1 : c₂ ≤ 1) (ha : |a| ≤ 1 / 2 + η)
    (hc : |c| ≤ R) :
    ‖weylBumpModelC L (Real.exp (θ * L)) (a + c * Complex.I)‖ ≤
      2 * (1 + Real.cosh R) * weylBumpModel L (Real.exp (θ * L)) (1 / 2 + 2 * η) *
        (Real.exp (-(L * (1 / 9 + 1 / 9 * (1 / 2 - |a|)))) +
          Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|))))) := by
  set A := Real.exp (θ * L) with hAdef
  set G := weylBumpModel L A (1 / 2 + 2 * η) with hG
  set E := Real.exp (L * (1 / 2 + 2 * η)) with hE
  have hA0 : 0 < A := Real.exp_pos _
  have hN := norm_weylBumpModelC_le hA0.le L a c
  -- `G ≥ e^{L(½ + 2η)}/2`
  have hGE : E / 2 ≤ G := by
    have h1 : E / 2 ≤ Real.cosh (L * (1 / 2 + 2 * η)) := by
      rw [Real.cosh_eq]; have := Real.exp_pos (-(L * (1 / 2 + 2 * η))); linarith
    have h2 : 0 ≤ A * (1 + Real.cos (1 / 2 + 2 * η)) :=
      mul_nonneg hA0.le (by linarith [Real.neg_one_le_cos (1 / 2 + 2 * η)])
    rw [hG]; unfold weylBumpModel; linarith
  -- the background: `cosh(La) ≤ 2G e^{−L(η + c₂(½ + η − |a|))}`
  have hbg : Real.cosh (L * a) ≤ 2 * G * Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|)))) := by
    have h1 : Real.cosh (L * a) ≤ Real.exp (L * |a|) := by
      have := cosh_le_exp_abs (L * a)
      rwa [abs_mul, abs_of_nonneg hL] at this
    have h2 : L * |a| ≤ L * (1 / 2 + 2 * η) + -(L * (η + c₂ * (1 / 2 + η - |a|))) := by
      have : (1 - c₂) * (1 / 2 + η - |a|) ≥ 0 := mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonneg hL this]
    have h3 : Real.exp (L * |a|) ≤ E * Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|)))) := by
      rw [hE, ← Real.exp_add]; exact Real.exp_le_exp.mpr h2
    have h4 : E * Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|))))
        ≤ 2 * G * Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|)))) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    linarith
  -- the bump: `A ≤ 2G e^{−L(1/9 + (1/9)(½ − |a|))}`
  have hbump : A ≤ 2 * G * Real.exp (-(L * (1 / 9 + 1 / 9 * (1 / 2 - |a|)))) := by
    have h2 : θ * L ≤ L * (1 / 2 + 2 * η) + -(L * (1 / 9 + 1 / 9 * (1 / 2 - |a|))) := by
      have : 1 / 9 + 1 / 9 * (1 / 2 - |a|) ≤ 1 / 6 := by nlinarith [abs_nonneg a]
      nlinarith [mul_le_mul_of_nonneg_left this hL, mul_le_mul_of_nonneg_left hθ hL]
    have h3 : A ≤ E * Real.exp (-(L * (1 / 9 + 1 / 9 * (1 / 2 - |a|)))) := by
      rw [hAdef, hE, ← Real.exp_add]; exact Real.exp_le_exp.mpr h2
    have h4 : E * Real.exp (-(L * (1 / 9 + 1 / 9 * (1 / 2 - |a|))))
        ≤ 2 * G * Real.exp (-(L * (1 / 9 + 1 / 9 * (1 / 2 - |a|)))) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    linarith
  have hcR : 1 + Real.cosh c ≤ 1 + Real.cosh R := by
    have := Real.cosh_le_cosh.mpr (hc.trans (le_abs_self R))
    linarith
  have hcR0 : 1 ≤ 1 + Real.cosh R := by linarith [Real.one_le_cosh R]
  have hG0 : 0 ≤ G := by linarith [Real.exp_pos (L * (1 / 2 + 2 * η))]
  set P₁ := Real.exp (-(L * (1 / 9 + 1 / 9 * (1 / 2 - |a|))))
  set P₂ := Real.exp (-(L * (η + c₂ * (1 / 2 + η - |a|))))
  have hP₁ : 0 ≤ P₁ := (Real.exp_pos _).le
  have hP₂ : 0 ≤ P₂ := (Real.exp_pos _).le
  have hAc : A * (1 + Real.cosh c) ≤ (1 + Real.cosh R) * (2 * G * P₁) :=
    mul_le_mul hbump hcR (by linarith [Real.one_le_cosh c]) (by positivity) |>.trans_eq (by ring)
  have hGP : 2 * G * P₂ ≤ (1 + Real.cosh R) * (2 * G * P₂) := by
    have : 0 ≤ 2 * G * P₂ := by positivity
    nlinarith
  calc ‖weylBumpModelC L A (a + c * Complex.I)‖ ≤ Real.cosh (L * a) + A * (1 + Real.cosh c) := hN
    _ ≤ 2 * G * P₂ + (1 + Real.cosh R) * (2 * G * P₁) := add_le_add hbg hAc
    _ ≤ (1 + Real.cosh R) * (2 * G * P₂) + (1 + Real.cosh R) * (2 * G * P₁) := by linarith
    _ = 2 * (1 + Real.cosh R) * G * (P₁ + P₂) := by ring

/-! ### Euler points -/

theorem iteratedDeriv_cosh_mul (L : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => Real.cosh (L * y)) x =
      (L ^ n * Real.exp (L * x) + (-L) ^ n * Real.exp (-L * x)) / 2 := by
  have hfun : (fun y => Real.cosh (L * y)) =
      fun y => (1 / 2 : ℝ) * (Real.exp (L * y) + Real.exp (-L * y)) := by
    funext y; rw [Real.cosh_eq, neg_mul]; ring
  have hc1 : ContDiffAt ℝ n (fun y => Real.exp (L * y)) x :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hc2 : ContDiffAt ℝ n (fun y => Real.exp (-L * y)) x :=
    (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffAt
  rw [hfun, iteratedDeriv_const_mul _ (hc1.add hc2),
    show (fun y => Real.exp (L * y) + Real.exp (-L * y)) =
      (fun y => Real.exp (L * y)) + (fun y => Real.exp (-L * y)) from rfl,
    iteratedDeriv_add hc1 hc2, iteratedDeriv_exp_const_mul, iteratedDeriv_exp_const_mul]
  ring

theorem abs_iteratedDeriv_cos_sin_le (n : ℕ) :
    ∀ x : ℝ, |iteratedDeriv n Real.cos x| ≤ 1 ∧ |iteratedDeriv n Real.sin x| ≤ 1 := by
  induction n with
  | zero => intro x; simp [Real.abs_cos_le_one, Real.abs_sin_le_one]
  | succ n ih =>
    intro x
    rw [iteratedDeriv_succ', iteratedDeriv_succ', Real.deriv_cos', Real.deriv_sin]
    refine ⟨?_, (ih x).1⟩
    rw [show (fun y => -Real.sin y) = -Real.sin from rfl, iteratedDeriv_neg, abs_neg]
    exact (ih x).2

theorem iteratedDeriv_weylBumpModel {n : ℕ} (hn : 1 ≤ n) (L A x : ℝ) :
    iteratedDeriv n (weylBumpModel L A) x =
      (L ^ n * Real.exp (L * x) + (-L) ^ n * Real.exp (-L * x)) / 2 +
        A * iteratedDeriv n Real.cos x := by
  have hfun : weylBumpModel L A =
      (fun y => Real.cosh (L * y)) + fun y => A * (1 + Real.cos y) := rfl
  have hc1 : ContDiffAt ℝ n (fun y => Real.cosh (L * y)) x :=
    (Real.contDiff_cosh.comp (contDiff_const.mul contDiff_id)).contDiffAt
  have hc2 : ContDiffAt ℝ n (fun y => 1 + Real.cos y) x :=
    (contDiff_const.add Real.contDiff_cos).contDiffAt
  rw [hfun, iteratedDeriv_add hc1 (contDiffAt_const.mul hc2), iteratedDeriv_cosh_mul,
    iteratedDeriv_const_mul _ hc2, iteratedDeriv_const_add (by omega)]

/-- **The Weyl bump satisfies the Euler-point bound.** For `n ≥ 1`, `L ≥ 1`, `A ≥ 0`, `Lx₀ ≥ 1` and
`12A ≤ e^{Lx₀}`: `g(x₀) Lⁿ/4 ≤ g^{(n)}(x₀)`. -/
theorem weylBumpModel_mul_pow_le_iteratedDeriv {L A x₀ : ℝ} {n : ℕ} (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hA : 0 ≤ A) (hLx : 1 ≤ L * x₀) (hAx : 12 * A ≤ Real.exp (L * x₀)) :
    weylBumpModel L A x₀ * L ^ n / 4 ≤ iteratedDeriv n (weylBumpModel L A) x₀ := by
  rw [iteratedDeriv_weylBumpModel hn]
  set E := Real.exp (L * x₀) with hE
  set F := Real.exp (-L * x₀) with hF
  set P := L ^ n with hP
  set D := iteratedDeriv n Real.cos x₀ with hD
  have hEF : E * F = 1 := by rw [hE, hF, ← Real.exp_add]; simp
  have hE1 : Real.exp 1 ≤ E := Real.exp_le_exp.mpr hLx
  have he : (2.7 : ℝ) ≤ Real.exp 1 := by have := Real.exp_one_gt_d9; linarith
  have hF0 : 0 < F := Real.exp_pos _
  have hFE : 7 * F ≤ E := by nlinarith
  have hP1 : 1 ≤ P := one_le_pow₀ hL
  have hD1 : -1 ≤ D := (abs_le.mp (abs_iteratedDeriv_cos_sin_le n x₀).1).1
  have hsign : -P ≤ (-L) ^ n := by
    rcases Nat.even_or_odd n with h | h
    · rw [h.neg_pow]; linarith
    · rw [h.neg_pow]
  have hcos : 1 + Real.cos x₀ ≤ 2 := by linarith [Real.cos_le_one x₀]
  have hg : weylBumpModel L A x₀ ≤ (E + F) / 2 + 2 * A := by
    unfold weylBumpModel
    rw [Real.cosh_eq, ← hE, show -(L * x₀) = -L * x₀ by ring, ← hF]
    nlinarith [mul_le_mul_of_nonneg_left hcos hA]
  have h1 : (-L) ^ n * F ≥ -P * F := mul_le_mul_of_nonneg_right hsign hF0.le
  have h2 : A * D ≥ -A := by nlinarith
  have h3 : P * F ≤ P * E / 7 := by nlinarith
  have h4 : A * P ≤ E * P / 12 := by nlinarith
  have hg0 : 0 ≤ weylBumpModel L A x₀ := by linarith [one_le_weylBumpModel hA L x₀]
  have h5 : weylBumpModel L A x₀ * P ≤ ((E + F) / 2 + 2 * A) * P :=
    mul_le_mul_of_nonneg_right hg (by linarith)
  nlinarith

/-! ### Heat -/

/-- The heated Weyl bump: the Gaussian average of variance `λ`. -/
def weylBumpHeat (L A lam x : ℝ) : ℝ :=
  ∫ u : ℝ, DeBruijn.gaussDensity (lam / 2) u * weylBumpModel L A (x + u)

theorem gaussDensity_eq_filterGauss (t u : ℝ) : DeBruijn.gaussDensity t u = filterGauss t u := rfl

/-- The Gaussian average of an odd bounded multiple of the density vanishes. -/
theorem integral_filterGauss_mul_sin {t : ℝ} : ∫ u : ℝ, filterGauss t u * Real.sin u = 0 := by
  have h := integral_neg_eq_self (fun u : ℝ => filterGauss t u * Real.sin u) volume
  simp only [filterGauss_neg, Real.sin_neg, mul_neg, integral_neg] at h
  linarith

/-- **Closed form of the heated model.** `H(x) = e^{λL²/2} cosh(Lx) + A(1 + e^{−λ/2} cos x)`. -/
theorem weylBumpHeat_eq {lam : ℝ} (hlam : 0 < lam) (L A x : ℝ) :
    weylBumpHeat L A lam x =
      Real.exp (lam * L ^ 2 / 2) * Real.cosh (L * x) + A * (1 + Real.exp (-(lam / 2)) * Real.cos x) := by
  set t := lam / 2 with htdef
  have ht : 0 < t := by positivity
  have hi1 := integrable_filterGauss_mul_rexp ht L
  have hi2 := integrable_filterGauss_mul_rexp ht (-L)
  have hi0 := integrable_filterGauss ht
  have hbdd : ∀ f : ℝ → ℝ, Continuous f → (∀ u, |f u| ≤ 1) →
      Integrable fun u => filterGauss t u * f u := by
    intro f hf hb
    have := hi0.bdd_mul (c := 1) hf.aestronglyMeasurable
      (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hb u)
    exact this.congr (Eventually.of_forall fun u => by ring)
  have hic := hbdd (fun u => Real.cos (1 * u)) (Real.continuous_cos.comp (continuous_const.mul
    continuous_id)) fun u => Real.abs_cos_le_one _
  have his := hbdd Real.sin Real.continuous_sin Real.abs_sin_le_one
  have hpt : ∀ u : ℝ, DeBruijn.gaussDensity t u * weylBumpModel L A (x + u) =
      Real.exp (L * x) / 2 * (filterGauss t u * Real.exp (u * L)) +
        Real.exp (-(L * x)) / 2 * (filterGauss t u * Real.exp (u * -L)) +
        A * filterGauss t u + A * Real.cos x * (filterGauss t u * Real.cos (1 * u)) -
        A * Real.sin x * (filterGauss t u * Real.sin u) := by
    intro u
    rw [gaussDensity_eq_filterGauss]
    unfold weylBumpModel
    have e1 : Real.exp (L * (x + u)) = Real.exp (L * x) * Real.exp (u * L) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(L * (x + u))) = Real.exp (-(L * x)) * Real.exp (u * -L) := by
      rw [← Real.exp_add]; ring_nf
    rw [Real.cosh_eq, e1, e2, Real.cos_add, one_mul]
    ring
  have j1 : Integrable fun u => Real.exp (L * x) / 2 * (filterGauss t u * Real.exp (u * L)) :=
    hi1.const_mul _
  have j2 : Integrable fun u =>
      Real.exp (-(L * x)) / 2 * (filterGauss t u * Real.exp (u * -L)) := hi2.const_mul _
  have j3 : Integrable fun u => A * filterGauss t u := hi0.const_mul _
  have j4 : Integrable fun u => A * Real.cos x * (filterGauss t u * Real.cos (1 * u)) :=
    hic.const_mul _
  have j5 : Integrable fun u => A * Real.sin x * (filterGauss t u * Real.sin u) := his.const_mul _
  have j12 : Integrable fun u => Real.exp (L * x) / 2 * (filterGauss t u * Real.exp (u * L)) +
      Real.exp (-(L * x)) / 2 * (filterGauss t u * Real.exp (u * -L)) := j1.add j2
  have j123 : Integrable fun u => Real.exp (L * x) / 2 * (filterGauss t u * Real.exp (u * L)) +
      Real.exp (-(L * x)) / 2 * (filterGauss t u * Real.exp (u * -L)) + A * filterGauss t u :=
    j12.add j3
  have j1234 : Integrable fun u => Real.exp (L * x) / 2 * (filterGauss t u * Real.exp (u * L)) +
      Real.exp (-(L * x)) / 2 * (filterGauss t u * Real.exp (u * -L)) + A * filterGauss t u +
      A * Real.cos x * (filterGauss t u * Real.cos (1 * u)) := j123.add j4
  unfold weylBumpHeat
  rw [show (fun u : ℝ => DeBruijn.gaussDensity t u * weylBumpModel L A (x + u)) = fun u =>
      Real.exp (L * x) / 2 * (filterGauss t u * Real.exp (u * L)) +
        Real.exp (-(L * x)) / 2 * (filterGauss t u * Real.exp (u * -L)) +
        A * filterGauss t u + A * Real.cos x * (filterGauss t u * Real.cos (1 * u)) -
        A * Real.sin x * (filterGauss t u * Real.sin u) from funext hpt]
  rw [integral_sub j1234 j5, integral_add j123 j4, integral_add j12 j3, integral_add j1 j2,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_filterGauss_mul_rexp ht, integral_filterGauss_mul_rexp ht,
    integral_filterGauss_eq_one ht, integral_filterGauss_mul_cos ht, integral_filterGauss_mul_sin,
    Real.cosh_eq]
  have e3 : Real.exp (t * (-L) ^ 2) = Real.exp (lam * L ^ 2 / 2) := by
    rw [htdef]; ring_nf
  have e4 : Real.exp (t * L ^ 2) = Real.exp (lam * L ^ 2 / 2) := by
    rw [htdef]; ring_nf
  have e5 : Real.exp (-(t * 1 ^ 2)) = Real.exp (-(lam / 2)) := by
    rw [htdef]; ring_nf
  rw [e3, e4, e5]
  ring

/-- The Taylor coefficients at `0` of the heated model. -/
def weylBumpHeatCoeff (L A lam : ℝ) (n : ℕ) : ℝ :=
  if Even n then
    (Real.exp (lam * L ^ 2 / 2) * L ^ n + A * Real.exp (-(lam / 2)) * (-1) ^ (n / 2)) /
        n.factorial + (if n = 0 then A else 0)
  else 0

/-- The heated model is the sum of its power series at `0`. -/
theorem hasSum_weylBumpHeatCoeff {lam : ℝ} (hlam : 0 < lam) (L A x : ℝ) :
    HasSum (fun n : ℕ => weylBumpHeatCoeff L A lam n * x ^ n) (weylBumpHeat L A lam x) := by
  rw [weylBumpHeat_eq hlam]
  have h1 := (Real.hasSum_cosh (L * x)).mul_left (Real.exp (lam * L ^ 2 / 2))
  have h2 := (Real.hasSum_cos x).mul_left (A * Real.exp (-(lam / 2)))
  have h := (h1.add h2).add (hasSum_ite_eq 0 A)
  have hinj : Function.Injective (fun m : ℕ => 2 * m) := fun a b hab => by
    simp only at hab; omega
  have hzero : ∀ n ∉ Set.range (fun m : ℕ => 2 * m),
      weylBumpHeatCoeff L A lam n * x ^ n = 0 := by
    intro n hn
    have hne : ¬ Even n := fun he => hn ⟨n / 2, by obtain ⟨r, hr⟩ := he; simp only; omega⟩
    simp [weylBumpHeatCoeff, hne]
  rw [← hinj.hasSum_iff hzero]
  have hfun : ((fun n => weylBumpHeatCoeff L A lam n * x ^ n) ∘ fun m : ℕ => 2 * m) = fun b =>
      Real.exp (lam * L ^ 2 / 2) * ((L * x) ^ (2 * b) / ((2 * b).factorial : ℝ)) +
        A * Real.exp (-(lam / 2)) * ((-1) ^ b * x ^ (2 * b) / ((2 * b).factorial : ℝ)) +
        (if b = 0 then A else 0) := by
    funext m
    simp only [Function.comp, weylBumpHeatCoeff, if_pos (even_two_mul m),
      Nat.mul_div_cancel_left m two_pos]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [if_neg (by omega : 2 * m ≠ 0), if_neg hm.ne', mul_pow]
      ring
  rw [hfun, show Real.exp (lam * L ^ 2 / 2) * Real.cosh (L * x) +
      A * (1 + Real.exp (-(lam / 2)) * Real.cos x) = Real.exp (lam * L ^ 2 / 2) * Real.cosh (L * x) +
        A * Real.exp (-(lam / 2)) * Real.cos x + A by ring]
  exact h

/-! ### The exact threshold `2θ` -/

/-- **Positivity from rate `2θ`.** For `L ≥ 1`, `0 ≤ κ` and `2θ ≤ κ`, every Taylor coefficient of the
heated model at heat `κ/L`, `A = e^{θL}`, is nonnegative. -/
theorem weylBumpHeatCoeff_nonneg {L θ κ : ℝ} (hL : 1 ≤ L) (hκ : 0 ≤ κ) (hθκ : 2 * θ ≤ κ)
    (n : ℕ) : 0 ≤ weylBumpHeatCoeff L (Real.exp (θ * L)) (κ / L) n := by
  unfold weylBumpHeatCoeff
  split_ifs with he h0
  · subst h0; positivity
  · have hL0 : 0 < L := by linarith
    set A := Real.exp (θ * L)
    set e' := Real.exp (-(κ / L / 2))
    have he'1 : e' ≤ 1 := Real.exp_le_one_iff.mpr (by
      have : 0 ≤ κ / L / 2 := by positivity
      linarith)
    have he'0 : 0 < e' := Real.exp_pos _
    have hsign : -1 ≤ (-1 : ℝ) ^ (n / 2) := by
      rcases Nat.even_or_odd (n / 2) with h | h
      · rw [h.neg_one_pow]; norm_num
      · rw [h.neg_one_pow]
    have hpow : 1 ≤ L ^ n := one_le_pow₀ hL
    have hAE : A ≤ Real.exp (κ / L * L ^ 2 / 2) := by
      refine Real.exp_le_exp.mpr ?_
      rw [show κ / L * L ^ 2 / 2 = κ * L / 2 by field_simp]
      nlinarith
    have hA0 : 0 < A := Real.exp_pos _
    have h1 : -(A * e') ≤ A * e' * (-1) ^ (n / 2) := by nlinarith [mul_pos hA0 he'0]
    have h2 : A * e' ≤ A := by nlinarith
    have h3 : Real.exp (κ / L * L ^ 2 / 2) ≤ Real.exp (κ / L * L ^ 2 / 2) * L ^ n := by
      nlinarith [Real.exp_pos (κ / L * L ^ 2 / 2)]
    have hnum : 0 ≤ Real.exp (κ / L * L ^ 2 / 2) * L ^ n + A * e' * (-1) ^ (n / 2) := by
      linarith
    have : 0 ≤ (Real.exp (κ / L * L ^ 2 / 2) * L ^ n + A * e' * (-1) ^ (n / 2)) /
        (n.factorial : ℝ) := div_nonneg hnum (Nat.cast_nonneg _)
    linarith
  · exact le_rfl

/-- A function with a nonnegative power series at `0` satisfies `2H(0) ≤ H(y) + H(−y)`. -/
theorem two_mul_le_add_of_hasSum_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {H : ℝ → ℝ}
    (hH : ∀ x, HasSum (fun n => a n * x ^ n) (H x)) (y : ℝ) : 2 * H 0 ≤ H y + H (-y) := by
  have h0 : H 0 = a 0 := by
    have h := hH 0
    have hf : (fun n => a n * (0 : ℝ) ^ n) = fun n => if n = 0 then a 0 else 0 := by
      funext n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · simp [hn.ne', zero_pow hn.ne']
    rw [hf] at h
    exact h.unique (hasSum_ite_eq 0 (a 0))
  have hle : ∀ n, (if n = 0 then 2 * a 0 else 0) ≤ a n * y ^ n + a n * (-y) ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp; ring_nf; exact le_rfl
    · rw [if_neg hn.ne']
      rcases Nat.even_or_odd n with he | ho
      · rw [he.neg_pow]
        have := he.pow_nonneg y
        nlinarith [ha n]
      · rw [ho.neg_pow]; ring_nf; exact le_rfl
  have := hasSum_le hle (hasSum_ite_eq 0 (2 * a 0)) ((hH y).add (hH (-y)))
  rw [h0]; linarith

/-- `cos y ≤ 1 − y²/4` for `|y| ≤ 1`. -/
theorem cos_le_one_sub_sq_div_four {y : ℝ} (hy : |y| ≤ 1) : Real.cos y ≤ 1 - y ^ 2 / 4 := by
  have h := Real.cos_bound hy
  have hy2 : y ^ 2 ≤ 1 := by
    have := abs_le.mp hy; nlinarith
  have h4 : |y| ^ 4 = (y ^ 2) ^ 2 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
  rw [h4] at h
  have := (abs_le.mp h).2
  nlinarith [sq_nonneg y]

/-- **No positivity below rate `2θ`.** For `0 < κ < 2θ` there is `L₀` such that for all `L ≥ L₀`
the heated model at heat `κ/L`, `A = e^{θL}`, has no power series at `0` with nonnegative
coefficients. -/
theorem not_exists_nonneg_hasSum_weylBumpHeat {θ κ : ℝ} (hκ : 0 < κ) (hκθ : κ < 2 * θ) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L ≥ L₀, ¬ ∃ a : ℕ → ℝ, (∀ n, 0 ≤ a n) ∧
      ∀ x : ℝ, HasSum (fun n : ℕ => a n * x ^ n) (weylBumpHeat L (Real.exp (θ * L)) (κ / L) x) := by
  set ε := θ - κ / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  refine ⟨max 1 (24 * Real.exp (κ / 2) / ε ^ 3 + 1), by positivity, fun L hL ⟨a, ha, hH⟩ => ?_⟩
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hL
  have hLbig : 24 * Real.exp (κ / 2) / ε ^ 3 < L :=
    lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hL)
  have hL0 : 0 < L := by linarith
  have hlam : 0 < κ / L := by positivity
  have key := two_mul_le_add_of_hasSum_nonneg ha hH (1 / L)
  rw [weylBumpHeat_eq hlam, weylBumpHeat_eq hlam, weylBumpHeat_eq hlam] at key
  -- evaluate at `y = 1/L`
  set Eh := Real.exp (κ / L * L ^ 2 / 2) with hEh
  set A := Real.exp (θ * L) with hA
  set e' := Real.exp (-(κ / L / 2)) with he'
  have hy : L * (1 / L) = 1 := by field_simp
  have hy' : L * -(1 / L) = -1 := by field_simp
  rw [mul_zero, Real.cosh_zero, Real.cos_zero, hy, hy', Real.cosh_neg, Real.cos_neg] at key
  have hcosh1 : Real.cosh 1 ≤ 2 := by
    rw [Real.cosh_eq]
    have := Real.exp_one_lt_d9
    have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    linarith
  have habs : |1 / L| ≤ 1 := by
    rw [abs_of_pos (by positivity), div_le_one hL0]; exact hL1
  have hcos := cos_le_one_sub_sq_div_four habs
  -- `key`: `2(Eh + A(1 + e')) ≤ 2(Eh cosh 1 + A(1 + e' cos(1/L)))`, so `A e'/(4L²) ≤ Eh`
  have hA0 : 0 < A := Real.exp_pos _
  have he'0 : 0 < e' := Real.exp_pos _
  have hEh0 : 0 < Eh := Real.exp_pos _
  have hineq : A * e' * (1 / L) ^ 2 / 4 ≤ Eh := by nlinarith [mul_pos hA0 he'0]
  -- but `A e' ≥ e^{εL} Eh e^{−κ/2}` and `e^{εL} > 4L² e^{κ/2}`
  have hAe : A * e' = Real.exp (ε * L) * Eh * Real.exp (-(κ / L / 2)) := by
    rw [hA, hEh, he', ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hεdef]; field_simp; ring
  have he'κ : Real.exp (-(κ / 2)) ≤ Real.exp (-(κ / L / 2)) := by
    refine Real.exp_le_exp.mpr ?_
    have : κ / L ≤ κ := div_le_self hκ.le hL1
    linarith
  have hexpε : 4 * L ^ 2 * Real.exp (κ / 2) < Real.exp (ε * L) := by
    have h3 := Real.pow_div_factorial_le_exp (ε * L) (by positivity) 3
    have hfac : ((3 : ℕ).factorial : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [hfac] at h3
    have hcube : 24 * Real.exp (κ / 2) < ε ^ 3 * L := by
      rw [div_lt_iff₀ (by positivity)] at hLbig; linarith
    have : 4 * L ^ 2 * Real.exp (κ / 2) < (ε * L) ^ 3 / 6 := by
      have hL2 : 0 < L ^ 2 := by positivity
      nlinarith [mul_lt_mul_of_pos_left hcube hL2]
    linarith
  have hinv : (1 / L) ^ 2 * L ^ 2 = 1 := by field_simp
  have hκ2 : Real.exp (κ / 2) * Real.exp (-(κ / 2)) = 1 := by
    rw [← Real.exp_add]; simp
  -- combine: `Eh ≥ A e'/(4L²) ≥ e^{εL} Eh e^{−κ/2}/(4L²) > Eh`
  have hlow : Real.exp (ε * L) * Eh * Real.exp (-(κ / 2)) * (1 / L) ^ 2 / 4 ≤ Eh := by
    have : Real.exp (ε * L) * Eh * Real.exp (-(κ / 2)) ≤ A * e' := by
      rw [hAe]
      exact mul_le_mul_of_nonneg_left he'κ (by positivity)
    have h2 : Real.exp (ε * L) * Eh * Real.exp (-(κ / 2)) * (1 / L) ^ 2 / 4
        ≤ A * e' * (1 / L) ^ 2 / 4 := by
      have := mul_le_mul_of_nonneg_right this (sq_nonneg (1 / L))
      linarith
    linarith
  have hfinal : Eh < Real.exp (ε * L) * Eh * Real.exp (-(κ / 2)) * (1 / L) ^ 2 / 4 := by
    have h1 : 4 * L ^ 2 * Real.exp (κ / 2) * (Eh * Real.exp (-(κ / 2)) * (1 / L) ^ 2 / 4) <
        Real.exp (ε * L) * (Eh * Real.exp (-(κ / 2)) * (1 / L) ^ 2 / 4) :=
      mul_lt_mul_of_pos_right hexpε (by positivity)
    have h2 : 4 * L ^ 2 * Real.exp (κ / 2) * (Eh * Real.exp (-(κ / 2)) * (1 / L) ^ 2 / 4) = Eh := by
      have : 4 * L ^ 2 * Real.exp (κ / 2) * (Eh * Real.exp (-(κ / 2)) * (1 / L) ^ 2 / 4)
          = Eh * (Real.exp (κ / 2) * Real.exp (-(κ / 2))) * ((1 / L) ^ 2 * L ^ 2) := by ring
      rw [this, hκ2, hinv]; ring
    rw [h2] at h1
    linarith
  linarith

end

end RHTower.DeBruijn
