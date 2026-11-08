import GaloisForLFunctions.SurfaceOfSpecZ.NoMetricOnTheProjectiveLineCarriesTheJets
import GaloisForLFunctions.RHTower.ArchimedeanWeilKernelSign

/-!
# The archimedean Frobenius of `Spec ℤ` is a Green function of hyperbolic three-space

On coprime orders the Frobenius intersection of `Spec ℤ` is the archimedean kernel
`min(m,n)/(1 − (min/max)²)` (`archKernel`): the `𝔽₁`-cusp `min(m,n)` and the jets of the trivial
zeros. Normalized by `√(mn)` it depends only on `d = |log(n/m)|`, and

  `archKernel m n / √(mn) = Σ_{k≥0} e^{−(2k+½)d} = e^{d/2}/(2 sinh d) = 2π·G_{1/2}(d)`

(`archKernel_eq`, `hasSum_archProfile`, `archProfile_eq_hyperbolicGreen`), where
`G_s(d) = e^{−(s−1)d}/(4π sinh d)` is the Green function of `Δ − s(2 − s)` on hyperbolic
three-space `ℍ³` at geodesic distance `d`. The term `k = 0` is the cusp, the terms `k ≥ 1` are the
jets.

**The carrier.** Put `z_n = (0, 0, n)` in the upper half-space model of `ℍ³`. Then
`cosh d(z_m, z_n) = 1 + (n − m)²/(2mn)`, so `d(z_m, z_n) = |log(n/m)|` (`cosh_log_sub_log`): the
dilation `x ↦ nx` of `ℝ` extends to the hyperbolic translation along the vertical geodesic, and the
archimedean Frobenius intersection of the points `z_m, z_n` is `2π√(mn)` times the Green function at
spectral parameter `s = ½`. `G_s` solves the radial equation `G″ + 2 coth(d) G′ = −s(2 − s)G` off the
pole (`hyperbolicGreen_radial`), and `4πd·G_s(d) → 1` (`tendsto_mul_hyperbolicGreen`): the diagonal
of the archimedean Frobenius is the Newtonian self-energy of a point of `ℍ³`
(`tendsto_mul_archProfile`), which is the divergence any presentation of the diagonal must
renormalize. In the language of Euclidean `AdS₃ = ℍ³`, `G_{1/2}` is the bulk-to-bulk propagator of
a scalar of mass `m² = −¾` in the quantization `Δ = ½`; the quantization `Δ = 3/2` differs from it
by the complementary-series spherical function: `2πG_{1/2} = 2πG_{3/2} + 1/(2 cosh(d/2))`
(`archProfile_eq_standard_add_spherical`).

**Damping.** The archimedean Frobenius is a counterterm-free damping limit off the diagonal:
`A_r(m,n) = √(mn)·e^{−d/2}/(1 − r²e^{−2d})`, `0 ≤ r < 1`, is a positive semidefinite kernel on
every finite set of atoms (`dampedFrobenius_posSemidef`, from the Ornstein–Uhlenbeck positivity of
`e^{−a|u−v|}`, `sum_mul_exp_neg_abs_nonneg`), `A_r(m,n) → archKernel m n` for `m ≠ n`
(`tendsto_dampedFrobenius`), and `A_r(n,n) = n/(1 − r²) → ∞` (`tendsto_dampedFrobenius_diag`).

**Weil's archimedean weight.** The archimedean-plus-pole weight of Weil's functional in the
autocorrelation variable is `4π·G_{1/2}(u) − 4 cosh(u/2)` (`weilKernel_eq_hyperbolicGreen`): the
Green function of `ℍ³` at `s = ½` against the pole.
-/

open Real Set MeasureTheory Filter Topology Finset

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

/-- The normalized archimedean Frobenius profile `e^{−d/2}/(1 − e^{−2d}) = Σ_k e^{−(2k+½)d}`. -/
def archProfile (d : ℝ) : ℝ := Real.exp (-d / 2) / (1 - Real.exp (-2 * d))

/-- The Green function of `Δ − s(2 − s)` on hyperbolic three-space at geodesic distance `d`. -/
def hyperbolicGreen (s d : ℝ) : ℝ := Real.exp (-(s - 1) * d) / (4 * π * Real.sinh d)

/-- The radial mode `e^{−αd}/sinh d` of hyperbolic three-space. -/
def radialMode (α d : ℝ) : ℝ := Real.exp (-α * d) / Real.sinh d

/-- The damped archimedean profile `e^{−|d|/2}/(1 − r²e^{−2|d|})`. -/
def archDamped (r d : ℝ) : ℝ := Real.exp (-|d| / 2) / (1 - r ^ 2 * Real.exp (-2 * |d|))

/-- The damped archimedean Frobenius kernel of two atoms. -/
def dampedFrobenius (r : ℝ) (m n : ℕ) : ℝ :=
  Real.sqrt ((m : ℝ) * n) * archDamped r (Real.log m - Real.log n)

/-! ## Elementary identities -/

theorem one_sub_exp_neg_two_mul_ne_zero {d : ℝ} (hd : d ≠ 0) : 1 - Real.exp (-2 * d) ≠ 0 := by
  intro h
  have : Real.exp (-2 * d) = 1 := by linarith
  rw [Real.exp_eq_one_iff] at this
  exact hd (by linarith)

theorem archProfile_eq_exp_div_sinh {d : ℝ} (hd : d ≠ 0) :
    archProfile d = Real.exp (d / 2) / (2 * Real.sinh d) := by
  have hs : Real.sinh d ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
  have h1 := one_sub_exp_neg_two_mul_ne_zero hd
  unfold archProfile
  rw [div_eq_div_iff h1 (mul_ne_zero two_ne_zero hs), Real.sinh_eq]
  have e1 : Real.exp (-d / 2) * Real.exp d = Real.exp (d / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-d / 2) * Real.exp (-d) = Real.exp (d / 2) * Real.exp (-2 * d) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  linear_combination e1 - e2

/-- **The trivial-zero series.** `e^{−d/2}/(1 − e^{−2d}) = Σ_{k≥0} e^{−(2k+½)d}` for `d > 0`. -/
theorem hasSum_archProfile {d : ℝ} (hd : 0 < d) :
    HasSum (fun k : ℕ => Real.exp (-(2 * k + 1 / 2) * d)) (archProfile d) := by
  have hq0 : 0 ≤ Real.exp (-2 * d) := (Real.exp_pos _).le
  have hq1 : Real.exp (-2 * d) < 1 := by
    rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by linarith)
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (-d / 2))
  have hf : (fun k : ℕ => Real.exp (-(2 * k + 1 / 2) * d)) =
      fun k : ℕ => Real.exp (-d / 2) * Real.exp (-2 * d) ^ k := by
    funext k
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  rw [hf, show archProfile d = Real.exp (-d / 2) * (1 - Real.exp (-2 * d))⁻¹ from
    div_eq_mul_inv _ _]
  exact h

/-- On the vertical geodesic of the upper half-space model, `cosh d(z_m, z_n) = 1 + (n−m)²/(2mn)`. -/
theorem cosh_log_sub_log {m n : ℝ} (hm : 0 < m) (hn : 0 < n) :
    Real.cosh (Real.log n - Real.log m) = 1 + (n - m) ^ 2 / (2 * m * n) := by
  rw [Real.cosh_eq, Real.exp_sub, neg_sub, Real.exp_sub, Real.exp_log hm, Real.exp_log hn]
  field_simp
  ring

theorem sqrt_eq_exp_half_log {a : ℝ} (ha : 0 < a) : Real.sqrt a = Real.exp (Real.log a / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ha]; congr 1; ring

/-- The real form of the identity: for `0 < a < b`,
`a/(1 − (a/b)²) = √(ab)·e^{−d/2}/(1 − e^{−2d})` with `d = log b − log a`. -/
theorem div_one_sub_sq_eq {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    a / (1 - (a / b) ^ 2) = Real.sqrt (a * b) * archProfile (Real.log b - Real.log a) := by
  have hb : 0 < b := ha.trans hab
  set p := Real.exp (Real.log a / 2) with hp
  set q := Real.exp (Real.log b / 2) with hq
  have hp0 : 0 < p := Real.exp_pos _
  have hq0 : 0 < q := Real.exp_pos _
  have hpa : p ^ 2 = a := by
    rw [hp, ← Real.exp_nat_mul]; push_cast; rw [show 2 * (Real.log a / 2) = Real.log a by ring,
      Real.exp_log ha]
  have hqb : q ^ 2 = b := by
    rw [hq, ← Real.exp_nat_mul]; push_cast; rw [show 2 * (Real.log b / 2) = Real.log b by ring,
      Real.exp_log hb]
  have hsq : Real.sqrt (a * b) = p * q := by
    rw [Real.sqrt_mul ha.le, sqrt_eq_exp_half_log ha, sqrt_eq_exp_half_log hb]
  have hpq : p < q := by
    rw [hp, hq, Real.exp_lt_exp]; linarith [Real.log_lt_log ha hab]
  have e1 : Real.exp (-(Real.log b - Real.log a) / 2) = p / q := by
    rw [hp, hq, ← Real.exp_sub]; congr 1; ring
  have e2 : Real.exp (-2 * (Real.log b - Real.log a)) = (p / q) ^ 4 := by
    rw [← e1, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [archProfile, e1, e2, hsq, ← hpa, ← hqb]
  have hq4 : q ^ 4 - p ^ 4 ≠ 0 := by
    have : p ^ 4 < q ^ 4 := by gcongr
    linarith
  have hq4' : q ^ 4 ≠ p ^ 4 := fun h => hq4 (by rw [h]; ring)
  field_simp

theorem archKernel_eq_real {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    min a b / (1 - (min a b / max a b) ^ 2) =
      Real.sqrt (a * b) * archProfile |Real.log b - Real.log a| := by
  rcases lt_or_gt_of_ne hab with h | h
  · rw [min_eq_left h.le, max_eq_right h.le,
      abs_of_pos (sub_pos.mpr (Real.log_lt_log ha h))]
    exact div_one_sub_sq_eq ha h
  · rw [min_eq_right h.le, max_eq_left h.le, abs_sub_comm,
      abs_of_pos (sub_pos.mpr (Real.log_lt_log hb h)), mul_comm a b]
    exact div_one_sub_sq_eq hb h

/-- **The archimedean Frobenius as a profile of the hyperbolic distance.** -/
theorem archKernel_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    archKernel m n = Real.sqrt ((m : ℝ) * n) * archProfile |Real.log n - Real.log m| :=
  archKernel_eq_real (by exact_mod_cast hm) (by exact_mod_cast hn) (by exact_mod_cast hmn)

/-- **The archimedean Frobenius is a Green function of `ℍ³`.** The normalized profile is `2π` times
the Green function of `Δ − ¾` at the spectral parameter `s = ½`. -/
theorem archProfile_eq_hyperbolicGreen {d : ℝ} (hd : d ≠ 0) :
    archProfile d = 2 * π * hyperbolicGreen (1 / 2) d := by
  have hs : Real.sinh d ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
  rw [archProfile_eq_exp_div_sinh hd, hyperbolicGreen,
    show -((1 : ℝ) / 2 - 1) * d = d / 2 by ring]
  field_simp
  ring

theorem archKernel_eq_hyperbolicGreen {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    archKernel m n =
      2 * π * Real.sqrt ((m : ℝ) * n) * hyperbolicGreen (1 / 2) |Real.log n - Real.log m| := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hne : |Real.log n - Real.log m| ≠ 0 := by
    rw [abs_ne_zero, sub_ne_zero]
    intro h
    have := Real.log_injOn_pos hn' hm' h
    exact hmn (by exact_mod_cast this.symm)
  rw [archKernel_eq hm hn hmn, archProfile_eq_hyperbolicGreen hne]
  ring

/-- **Standard quantization plus the complementary series.** `2πG_{1/2} = 2πG_{3/2} + 1/(2cosh(d/2))`. -/
theorem archProfile_eq_standard_add_spherical {d : ℝ} (hd : d ≠ 0) :
    archProfile d = 2 * π * hyperbolicGreen (3 / 2) d + 1 / (2 * Real.cosh (d / 2)) := by
  have hs : Real.sinh d ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
  have hc : Real.cosh (d / 2) ≠ 0 := (Real.cosh_pos _).ne'
  rw [archProfile_eq_exp_div_sinh hd, hyperbolicGreen,
    show -((3 : ℝ) / 2 - 1) * d = -(d / 2) by ring]
  have h2 : Real.sinh d = 2 * Real.sinh (d / 2) * Real.cosh (d / 2) := by
    rw [← Real.sinh_two_mul]; congr 1; ring
  have hsh : Real.exp (d / 2) - Real.exp (-(d / 2)) = 2 * Real.sinh (d / 2) := by
    rw [Real.sinh_eq]; ring
  have hs2 : Real.sinh (d / 2) ≠ 0 := by
    rw [ne_eq, Real.sinh_eq_zero]; intro h; exact hd (by linarith)
  have hE : Real.exp (d / 2) = Real.exp (-(d / 2)) + 2 * Real.sinh (d / 2) := by linarith [hsh]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [hE, h2]
  field_simp
  ring

/-! ## The radial equation of `ℍ³` -/

/-- First derivative of the radial mode. -/
def radialMode' (α d : ℝ) : ℝ :=
  -Real.exp (-α * d) * (α * Real.sinh d + Real.cosh d) / Real.sinh d ^ 2

/-- Second derivative of the radial mode. -/
def radialMode'' (α d : ℝ) : ℝ :=
  Real.exp (-α * d) * ((α ^ 2 - 1) * Real.sinh d ^ 2 +
    2 * Real.cosh d * (α * Real.sinh d + Real.cosh d)) / Real.sinh d ^ 3

theorem hasDerivAt_exp_neg_mul (α d : ℝ) :
    HasDerivAt (fun x => Real.exp (-α * x)) (-α * Real.exp (-α * d)) d := by
  have h := ((hasDerivAt_id d).const_mul (-α)).exp
  simp only [id, mul_one] at h
  exact h.congr_deriv (by ring)

theorem hasDerivAt_radialMode (α : ℝ) {d : ℝ} (hd : Real.sinh d ≠ 0) :
    HasDerivAt (radialMode α) (radialMode' α d) d := by
  have h : HasDerivAt (radialMode α) _ d :=
    (hasDerivAt_exp_neg_mul α d).div (Real.hasDerivAt_sinh d) hd
  refine h.congr_deriv ?_
  unfold radialMode'
  field_simp
  ring

theorem hasDerivAt_radialMode' (α : ℝ) {d : ℝ} (hd : Real.sinh d ≠ 0) :
    HasDerivAt (radialMode' α) (radialMode'' α d) d := by
  have hN : HasDerivAt (fun x => -Real.exp (-α * x) * (α * Real.sinh x + Real.cosh x))
      (α * Real.exp (-α * d) * (α * Real.sinh d + Real.cosh d) -
        Real.exp (-α * d) * (α * Real.cosh d + Real.sinh d)) d := by
    have h1 : HasDerivAt (fun x => -Real.exp (-α * x) * (α * Real.sinh x + Real.cosh x)) _ d :=
      (hasDerivAt_exp_neg_mul α d).neg.mul
        (((Real.hasDerivAt_sinh d).const_mul α).add (Real.hasDerivAt_cosh d))
    exact h1.congr_deriv (by simp only [Pi.neg_apply, neg_mul]; ring)
  have hD : HasDerivAt (fun x => Real.sinh x ^ 2) (2 * Real.sinh d * Real.cosh d) d :=
    ((Real.hasDerivAt_sinh d).pow 2).congr_deriv (by norm_num)
  have h : HasDerivAt (radialMode' α) _ d := hN.div hD (pow_ne_zero 2 hd)
  refine h.congr_deriv ?_
  unfold radialMode''
  field_simp
  ring

theorem deriv_radialMode_eventually (α : ℝ) {d : ℝ} (hd : d ≠ 0) :
    deriv (radialMode α) =ᶠ[𝓝 d] radialMode' α := by
  have hne : ∀ᶠ x in 𝓝 d, x ≠ 0 := isOpen_ne.mem_nhds hd
  filter_upwards [hne] with x hx
  exact (hasDerivAt_radialMode α (by rwa [ne_eq, Real.sinh_eq_zero])).deriv

/-- **The radial equation.** `F″ + 2 coth(d) F′ = (α² − 1)F` for `F = e^{−αd}/sinh d`, `d ≠ 0`. -/
theorem radialMode_radial (α : ℝ) {d : ℝ} (hd : d ≠ 0) :
    deriv (deriv (radialMode α)) d + 2 * (Real.cosh d / Real.sinh d) * deriv (radialMode α) d =
      (α ^ 2 - 1) * radialMode α d := by
  have hs : Real.sinh d ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
  rw [(deriv_radialMode_eventually α hd).deriv_eq, (hasDerivAt_radialMode' α hs).deriv,
    (hasDerivAt_radialMode α hs).deriv]
  unfold radialMode'' radialMode' radialMode
  field_simp
  ring

theorem hyperbolicGreen_eq_radialMode (s : ℝ) :
    hyperbolicGreen s = fun d => radialMode (s - 1) d / (4 * π) := by
  funext d
  rw [hyperbolicGreen, radialMode, div_div, mul_comm (Real.sinh d)]

/-- **`G_s` is the Green function of `Δ − s(2 − s)` off its pole.** With the radial Laplacian
`Δ = −(∂² + 2 coth(d) ∂)` of `ℍ³`, `ΔG_s = s(2 − s)G_s` for `d ≠ 0`. -/
theorem hyperbolicGreen_radial (s : ℝ) {d : ℝ} (hd : d ≠ 0) :
    deriv (deriv (hyperbolicGreen s)) d +
        2 * (Real.cosh d / Real.sinh d) * deriv (hyperbolicGreen s) d =
      -(s * (2 - s)) * hyperbolicGreen s d := by
  have h := radialMode_radial (s - 1) hd
  have hfun : (fun x => radialMode (s - 1) x / (4 * π)) =
      fun x => (4 * π)⁻¹ * radialMode (s - 1) x := by
    funext x; rw [div_eq_inv_mul]
  rw [hyperbolicGreen_eq_radialMode, hfun, deriv_const_mul_field' ((4 * π)⁻¹),
    deriv_const_mul_field' ((4 * π)⁻¹)]
  beta_reduce
  rw [show (s - 1) ^ 2 - 1 = -(s * (2 - s)) by ring] at h
  linear_combination (4 * π)⁻¹ * h

/-- **The Newtonian pole.** `4πd·G_s(d) → 1` as `d → 0`. -/
theorem tendsto_mul_hyperbolicGreen (s : ℝ) :
    Tendsto (fun d => 4 * π * d * hyperbolicGreen s d) (𝓝[≠] 0) (𝓝 1) := by
  have hslope : Tendsto (fun d => Real.sinh d / d) (𝓝[≠] 0) (𝓝 1) := by
    have := (hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_sinh 0))
    rw [Real.cosh_zero] at this
    refine this.congr fun d => ?_
    rw [slope_def_field, Real.sinh_zero, sub_zero, sub_zero]
  have hexp : Tendsto (fun d => Real.exp (-(s - 1) * d)) (𝓝[≠] 0) (𝓝 1) := by
    have : Continuous fun d : ℝ => Real.exp (-(s - 1) * d) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have := hexp.mul (hslope.inv₀ one_ne_zero)
  rw [inv_one, mul_one] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  have hs : Real.sinh d ≠ 0 := by rwa [ne_eq, Real.sinh_eq_zero]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [hyperbolicGreen]
  field_simp

/-- **The diagonal of the archimedean Frobenius is a Coulomb self-energy.** `d·archProfile d → ½`. -/
theorem tendsto_mul_archProfile :
    Tendsto (fun d => d * archProfile d) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have h := (tendsto_mul_hyperbolicGreen (1 / 2)).const_mul (1 / 2)
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with d hd
  rw [archProfile_eq_hyperbolicGreen hd]
  ring

/-! ## Positivity of the damped Frobenius -/

/-- **Ornstein–Uhlenbeck positivity.** `e^{−a|u−v|}` is positive semidefinite: it is `2a` times the
`L²` pairing of the one-sided exponentials `w ↦ e^{a(w−u)}·1_{w≤u}`. -/
theorem sum_mul_exp_neg_abs_nonneg {ι : Type*} (s : Finset ι) {a : ℝ} (ha : 0 < a)
    (u c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.exp (-a * |u i - u j|) := by
  set φ : ι → ℝ → ℝ := fun i => (Iic (u i)).indicator fun w => Real.exp (a * (w - u i))
  have hprod : ∀ i j, (fun w => φ i w * φ j w) = (Iic (min (u i) (u j))).indicator
      (fun w => Real.exp (-a * (u i + u j)) * Real.exp ((2 * a) * w)) := by
    intro i j
    funext w
    simp only [φ]
    rw [← inter_indicator_mul, Iic_inter_Iic]
    congr 1
    funext x
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hint : ∀ i j, Integrable (fun w => φ i w * φ j w) := by
    intro i j
    rw [hprod]
    have hon : IntegrableOn (fun w => Real.exp (-a * (u i + u j)) * Real.exp ((2 * a) * w))
        (Iic (min (u i) (u j))) :=
      (integrableOn_exp_mul_Iic (a := 2 * a) (by positivity) (min (u i) (u j))).const_mul _
    exact hon.integrable_indicator measurableSet_Iic
  have hpair : ∀ i j, ∫ w, φ i w * φ j w = Real.exp (-a * |u i - u j|) / (2 * a) := by
    intro i j
    rw [hprod, integral_indicator measurableSet_Iic, integral_const_mul,
      integral_exp_mul_Iic (by positivity), mul_div_assoc', ← Real.exp_add]
    congr 2
    rcases le_total (u i) (u j) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  have hsq : ∀ w, (∑ i ∈ s, c i * φ i w) ^ 2 =
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * (φ i w * φ j w) := by
    intro w
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hform : ∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.exp (-a * |u i - u j|) =
      2 * a * ∫ w, (∑ i ∈ s, c i * φ i w) ^ 2 := by
    simp_rw [hsq]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hint i j).const_mul _]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hpair]
    field_simp
  rw [hform]
  exact mul_nonneg (by positivity) (integral_nonneg fun w => sq_nonneg _)

theorem hasSum_archDamped {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (d : ℝ) :
    HasSum (fun k : ℕ => r ^ (2 * k) * Real.exp (-(2 * k + 1 / 2) * |d|)) (archDamped r d) := by
  have hq0 : 0 ≤ r ^ 2 * Real.exp (-2 * |d|) := by positivity
  have hq1 : r ^ 2 * Real.exp (-2 * |d|) < 1 := by
    have h1 : r ^ 2 < 1 := by nlinarith
    have h2 : Real.exp (-2 * |d|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [abs_nonneg d])
    nlinarith [Real.exp_pos (-2 * |d|), sq_nonneg r]
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Real.exp (-|d| / 2))
  have hf : (fun k : ℕ => r ^ (2 * k) * Real.exp (-(2 * k + 1 / 2) * |d|)) =
      fun k : ℕ => Real.exp (-|d| / 2) * (r ^ 2 * Real.exp (-2 * |d|)) ^ k := by
    funext k
    rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul,
      show Real.exp (-|d| / 2) * (r ^ (2 * k) * Real.exp (k * (-2 * |d|))) =
        r ^ (2 * k) * (Real.exp (-|d| / 2) * Real.exp (k * (-2 * |d|))) by ring, ← Real.exp_add]
    congr 2; ring
  rw [hf, show archDamped r d = Real.exp (-|d| / 2) * (1 - r ^ 2 * Real.exp (-2 * |d|))⁻¹ from
    div_eq_mul_inv _ _]
  exact h

/-- **The damped archimedean profile is a positive definite function of `log`-distance.** -/
theorem sum_mul_archDamped_nonneg {ι : Type*} (s : Finset ι) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (u c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * archDamped r (u i - u j) := by
  set f : ℕ → ι → ι → ℝ := fun k i j =>
    c i * c j * (r ^ (2 * k) * Real.exp (-(2 * k + 1 / 2) * |u i - u j|))
  have hsum : ∀ i j, Summable fun k => f k i j := fun i j =>
    ((hasSum_archDamped hr0 hr1 (u i - u j)).summable).mul_left _
  have hrow : ∀ i j, c i * c j * archDamped r (u i - u j) = ∑' k, f k i j := fun i j => by
    rw [← (hasSum_archDamped hr0 hr1 (u i - u j)).tsum_eq, ← tsum_mul_left]
  simp_rw [hrow]
  rw [Finset.sum_congr rfl fun i _ => (Summable.tsum_finsetSum fun j _ => hsum i j).symm,
    ← Summable.tsum_finsetSum fun i _ => summable_sum fun j _ => hsum i j]
  refine tsum_nonneg fun k => ?_
  have hform : ∑ i ∈ s, ∑ j ∈ s, f k i j = r ^ (2 * k) *
      ∑ i ∈ s, ∑ j ∈ s, c i * c j * Real.exp (-(2 * k + 1 / 2) * |u i - u j|) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [f]; ring
  rw [hform]
  exact mul_nonneg (by positivity) (sum_mul_exp_neg_abs_nonneg s (by positivity) u c)

/-- **Damped positivity on atoms.** For `0 ≤ r < 1` the damped archimedean Frobenius kernel is
positive semidefinite on every finite family of positive integers. -/
theorem dampedFrobenius_posSemidef {ι : Type*} (s : Finset ι) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (n : ι → ℕ) (c : ι → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * dampedFrobenius r (n i) (n j) := by
  have h := sum_mul_archDamped_nonneg s hr0 hr1 (fun i => Real.log (n i))
    (fun i => c i * Real.sqrt (n i))
  convert h using 3 with i _ j _
  rw [dampedFrobenius, Real.sqrt_mul (Nat.cast_nonneg _)]
  ring

/-- **Off the diagonal the damping is lossless.** `A_r(m,n) → archKernel m n` as `r → 1`. -/
theorem tendsto_dampedFrobenius {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    Tendsto (fun r => dampedFrobenius r m n) (𝓝 1) (𝓝 (archKernel m n)) := by
  set d := Real.log m - Real.log n
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : d ≠ 0 := by
    simp only [d, sub_ne_zero]
    intro h
    have := Real.log_injOn_pos hm' hn' h
    exact hmn (by exact_mod_cast this)
  have hden : 1 - (1 : ℝ) ^ 2 * Real.exp (-2 * |d|) ≠ 0 := by
    rw [one_pow, one_mul]; exact one_sub_exp_neg_two_mul_ne_zero (abs_ne_zero.mpr hd)
  have hcont : ContinuousAt (fun r : ℝ => dampedFrobenius r m n) 1 := by
    unfold dampedFrobenius archDamped
    refine continuousAt_const.mul (continuousAt_const.div ?_ hden)
    fun_prop
  have hval : dampedFrobenius 1 m n = archKernel m n := by
    rw [archKernel_eq hm hn hmn, dampedFrobenius, archDamped, one_pow, one_mul, abs_sub_comm]
    rfl
  rw [← hval]
  exact hcont.tendsto

/-- **On the diagonal the damped Frobenius diverges:** `A_r(n,n) = n/(1 − r²) → ∞`. -/
theorem tendsto_dampedFrobenius_diag {n : ℕ} (hn : 0 < n) :
    Tendsto (fun r => dampedFrobenius r n n) (𝓝[<] 1) atTop := by
  have hval : ∀ r, dampedFrobenius r n n = (n : ℝ) * (1 - r ^ 2)⁻¹ := fun r => by
    rw [dampedFrobenius, archDamped, sub_self, abs_zero, mul_zero, neg_zero, zero_div,
      Real.exp_zero, mul_one, Real.sqrt_mul_self (Nat.cast_nonneg _), one_div]
  simp_rw [hval]
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  refine Tendsto.const_mul_atTop hpos (tendsto_inv_nhdsGT_zero.comp ?_)
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have : Continuous fun r : ℝ => 1 - r ^ 2 := by fun_prop
    simpa using (this.tendsto 1).mono_left nhdsWithin_le_nhds
  · have h0 : ∀ᶠ r in 𝓝[<] (1 : ℝ), 0 < r :=
      nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [h0, self_mem_nhdsWithin] with r hr0 hr1
    have : r ^ 2 < 1 := by nlinarith [mem_Iio.mp hr1]
    exact mem_Ioi.mpr (by linarith)

/-! ## Weil's archimedean weight -/

/-- **Weil's archimedean-plus-pole weight is the `ℍ³` Green function against the pole.** -/
theorem weilKernel_eq_hyperbolicGreen {u : ℝ} (hu : u ≠ 0) :
    RHTower.ArchimedeanKernel.weilKernel u =
      4 * π * hyperbolicGreen (1 / 2) u - 4 * Real.cosh (u / 2) := by
  have h : RHTower.ArchimedeanKernel.weilKernel u = 2 * archProfile u - 4 * Real.cosh (u / 2) := by
    rw [RHTower.ArchimedeanKernel.weilKernel, archProfile, mul_div_assoc]
  rw [h, archProfile_eq_hyperbolicGreen hu]
  ring

end GaloisForLFunctions.SurfaceOfSpecZ
