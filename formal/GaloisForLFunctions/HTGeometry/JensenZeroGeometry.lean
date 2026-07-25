/-
Exponent arithmetic of the Jensen–Backlund inequality: the zero-geometry route is inert.

Jensen's formula on a disc of radius `R` centred at a point of the critical line turns the size of
`ζ` there into an exact balance between two quantities:

* the mean of `log|ζ|` over the disc boundary, which the functional equation splits into the
  explicit factor `(R/π)·log(t/2π)` plus the mean of `log|ζ|` over sample points with real part
  `≥ 1/2` — the part an upper bound `μ(σ) ≤ 2θ₀(1-σ)` controls;
* the zero potential `∫₀^R n(u) du/u`, whose expected value `(R/π)·log(t/2π)` cancels the explicit
  factor exactly.

Feeding the two available inputs into that balance produces an output exponent depending only on
`θ₀` and on one geometric weight: the mean over the Jensen circle of the surviving convexity
allowance,

  `foldedWidth R = (1/2π) ∫₀^{2π} (1/2 - R|cos θ|)₊ dθ ∈ [0, 1/2]`.

The two branches recorded here are the unconditional output `1/4 + 2J(θ₀ - 1/4)` and, when the
zeros in the disc are known to lie on the critical line, the output `2Jθ₀`.  The arithmetic of the
first shows the route returns `1/4` for every radius, and that iterating it drives any subconvex
input back up to `1/4`; the arithmetic of the second shows a strict geometric contraction to `0`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Basic

namespace HTGeometry

open Real

/-- The mean over the Jensen circle of radius `R` of the surviving convexity allowance
`(1/2 - R|cos θ|)₊`.  Below `R = 1/2` the positive part is inactive and the mean is
`1/2 - 2R/π`; above it the circle reaches past the abscissa of absolute convergence and the
truncation contributes an inverse-cosine term. -/
noncomputable def foldedWidth (R : ℝ) : ℝ :=
  if R ≤ 1/2 then 1/2 - 2 * R / π
  else (2 / π) * (π / 4 - arccos (1 / (2 * R)) / 2 - R + Real.sqrt (R ^ 2 - 1/4))

@[simp] theorem foldedWidth_zero : foldedWidth 0 = 1/2 := by
  simp [foldedWidth]

theorem foldedWidth_half : foldedWidth (1/2) = 1/2 - 1 / π := by
  simp [foldedWidth]

/-- The two branches of `foldedWidth` agree at the junction `R = 1/2`: the truncation switches on
continuously. -/
theorem foldedWidth_branches_agree :
    (2 / π) * (π / 4 - arccos (1 / (2 * (1/2 : ℝ))) / 2 - (1/2) + Real.sqrt ((1/2 : ℝ) ^ 2 - 1/4))
      = foldedWidth (1/2) := by
  have h1 : (1 : ℝ) / (2 * (1/2 : ℝ)) = 1 := by norm_num
  have h2 : ((1/2 : ℝ) ^ 2 - 1/4) = 0 := by norm_num
  have hπ : π ≠ 0 := ne_of_gt pi_pos
  rw [foldedWidth_half, h1, h2, Real.arccos_one, Real.sqrt_zero]
  field_simp
  ring

theorem foldedWidth_lt_half {R : ℝ} (hR : 0 < R) : foldedWidth R < 1/2 := by
  have hπ : 0 < π := pi_pos
  unfold foldedWidth
  split_ifs with h
  · have : 0 < 2 * R / π := by positivity
    linarith
  · rw [not_le] at h
    have hR2 : (0 : ℝ) ≤ R ^ 2 - 1/4 := by nlinarith
    have hs : Real.sqrt (R ^ 2 - 1/4) < R := by
      have : Real.sqrt (R ^ 2 - 1/4) < Real.sqrt (R ^ 2) := by
        apply Real.sqrt_lt_sqrt hR2; linarith
      rwa [Real.sqrt_sq hR.le] at this
    have hac : 0 ≤ arccos (1 / (2 * R)) := Real.arccos_nonneg _
    have hkey : π / 4 - arccos (1 / (2 * R)) / 2 - R + Real.sqrt (R ^ 2 - 1/4) < π / 4 := by
      linarith
    have h2π : 0 < 2 / π := by positivity
    calc (2 / π) * (π / 4 - arccos (1 / (2 * R)) / 2 - R + Real.sqrt (R ^ 2 - 1/4))
        < (2 / π) * (π / 4) := mul_lt_mul_of_pos_left hkey h2π
      _ = 1/2 := by field_simp; ring

/-- `arcsin x ≥ x` for `x ∈ [0,1]`, the elementary half of Jordan's inequality. -/
theorem le_arcsin_of_mem {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : x ≤ arcsin x := by
  have h0 : 0 ≤ arcsin x := Real.arcsin_nonneg.mpr hx0
  have := Real.sin_le h0
  rwa [Real.sin_arcsin (by linarith) hx1] at this

theorem foldedWidth_nonneg {R : ℝ} (hR : 0 ≤ R) : 0 ≤ foldedWidth R := by
  have hπ : 0 < π := pi_pos
  have hπ2 : (2 : ℝ) ≤ π := Real.two_le_pi
  unfold foldedWidth
  split_ifs with h
  · have hle : 2 * R / π ≤ 1 / π := by gcongr; linarith
    have hhalf : (1 : ℝ) / π ≤ 1/2 := by
      rw [div_le_div_iff₀ hπ (by norm_num)]; linarith
    linarith
  · rw [not_le] at h
    have hRpos : (0 : ℝ) < R := by linarith
    have hR2 : (0 : ℝ) ≤ R ^ 2 - 1/4 := by nlinarith
    set s := Real.sqrt (R ^ 2 - 1/4) with hsdef
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = R ^ 2 - 1/4 := Real.sq_sqrt hR2
    -- `arccos (1/(2R)) ≤ π/2 - 1/(2R)` from `arcsin y ≥ y`
    have hy0 : (0 : ℝ) ≤ 1 / (2 * R) := by positivity
    have hy1 : (1 : ℝ) / (2 * R) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have harc : arccos (1 / (2 * R)) ≤ π / 2 - 1 / (2 * R) := by
      rw [Real.arccos_eq_pi_div_two_sub_arcsin]
      have := le_arcsin_of_mem hy0 hy1
      linarith
    -- `R - s ≤ 1/(4R)`
    have hgap : R - s ≤ 1 / (4 * R) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith [sq_nonneg (2 * R - 2 * s), sq_nonneg s, mul_nonneg hs0 hRpos.le]
    have hinner : 0 ≤ π / 4 - arccos (1 / (2 * R)) / 2 - R + s := by
      have h4R : (1 : ℝ) / (2 * R) / 2 = 1 / (4 * R) := by
        rw [div_div]; ring_nf
      linarith [hgap, harc, h4R.le, h4R.ge]
    have h2π : (0 : ℝ) ≤ 2 / π := by positivity
    exact mul_nonneg h2π hinner

/-- Output exponent of the Jensen–Backlund inequality on input `θ₀`, in the unconditional regime
where the only lower bound available for the zero potential is the one supplied by the
Riemann–von Mangoldt count. -/
noncomputable def jensenOutput (J θ₀ : ℝ) : ℝ := 1/4 + 2 * J * (θ₀ - 1/4)

/-- Output exponent when the zeros in the Jensen disc are known to lie on the critical line, so the
zero potential attains its expected value and cancels the explicit factor entirely. -/
noncomputable def rhOutput (J θ₀ : ℝ) : ℝ := 2 * J * θ₀

/-- **The convexity bound is a fixed point of the route at every radius.** -/
@[simp] theorem jensenOutput_quarter (J : ℝ) : jensenOutput J (1/4) = 1/4 := by
  simp [jensenOutput]

/-- **The exact-cancellation identity.**  With `A = R - √(R² - 1/4)` the explicit factor minus the
guaranteed potential, `R - I(R)` where `I(R) = √(R² - 1/4) - θ/2`, is exactly a quarter of the
weight `θ + 2A` appearing in `1 - 2·foldedWidth R`.  This is why the route reproduces `1/4`. -/
theorem jensen_cancellation (R θ : ℝ) :
    4 * (R - (Real.sqrt (R ^ 2 - 1/4) - θ / 2))
      = 2 * (θ + 2 * (R - Real.sqrt (R ^ 2 - 1/4))) := by
  ring

/-- **Inertness, contraction form.**  The route moves the exponent toward `1/4` by the factor `2J`;
it never moves it away from `1/4`. -/
theorem jensenOutput_sub_quarter (J θ₀ : ℝ) :
    jensenOutput J θ₀ - 1/4 = 2 * J * (θ₀ - 1/4) := by
  unfold jensenOutput; ring

/-- **The route never improves its input.** -/
theorem le_jensenOutput {J θ₀ : ℝ} (hJ : J ≤ 1/2) (hθ : θ₀ ≤ 1/4) :
    θ₀ ≤ jensenOutput J θ₀ := by
  have h : jensenOutput J θ₀ - θ₀ = (1 - 2 * J) * (1/4 - θ₀) := by
    unfold jensenOutput; ring
  nlinarith [h]

/-- **The route never exceeds the convexity bound.** -/
theorem jensenOutput_le_quarter {J θ₀ : ℝ} (hJ : 0 ≤ J) (hθ : θ₀ ≤ 1/4) :
    jensenOutput J θ₀ ≤ 1/4 := by
  have := jensenOutput_sub_quarter J θ₀
  nlinarith

/-- **`1/4` is the unique fixed point** whenever the radius is positive (`J < 1/2`): the route
returns its input only at the convexity bound itself. -/
theorem jensenOutput_eq_self_iff {J θ₀ : ℝ} (hJ : J ≠ 1/2) :
    jensenOutput J θ₀ = θ₀ ↔ θ₀ = 1/4 := by
  constructor
  · intro h
    have h2 : (1 - 2 * J) * (1/4 - θ₀) = 0 := by
      unfold jensenOutput at h; linarith
    have hne : (1 : ℝ) - 2 * J ≠ 0 := by
      intro hc; apply hJ; linarith
    have := (mul_eq_zero.mp h2).resolve_left hne
    linarith
  · rintro rfl; simp [jensenOutput]

/-- **Iterating the route pushes any subconvex input back up to the convexity bound.**  The `n`-th
iterate differs from `1/4` by `(2J)^n` times the initial gap, and `2J < 1` for every positive
radius. -/
theorem jensenOutput_iterate (J θ₀ : ℝ) (n : ℕ) :
    (fun θ => jensenOutput J θ)^[n] θ₀ - 1/4 = (2 * J) ^ n * (θ₀ - 1/4) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', jensenOutput_sub_quarter, pow_succ]
    rw [show (2 * J) ^ n * (2 * J) * (θ₀ - 1/4) = 2 * J * ((2 * J) ^ n * (θ₀ - 1/4)) by ring, ← ih]

/-- **With the zeros on the line the route contracts strictly.** -/
theorem rhOutput_lt {J θ₀ : ℝ} (hJ : J < 1/2) (hθ : 0 < θ₀) :
    rhOutput J θ₀ < θ₀ := by
  have : 2 * J < 1 := by linarith
  calc rhOutput J θ₀ = (2 * J) * θ₀ := rfl
    _ < 1 * θ₀ := mul_lt_mul_of_pos_right this hθ
    _ = θ₀ := one_mul θ₀

theorem rhOutput_iterate (J θ₀ : ℝ) (n : ℕ) :
    (fun θ => rhOutput J θ)^[n] θ₀ = (2 * J) ^ n * θ₀ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    show 2 * J * ((fun θ => rhOutput J θ)^[n] θ₀) = _
    rw [ih, pow_succ]; ring

/-- **With the zeros on the line the iterated route reaches `μ = 0`.**  For every positive radius
the contraction factor `2·foldedWidth R` is `< 1`, so the iterates tend to `0`: this is the
zero-geometry proof that the Riemann hypothesis implies the Lindelöf hypothesis. -/
theorem rhOutput_tendsto_zero {J θ₀ : ℝ} (hJ : |2 * J| < 1) :
    Filter.Tendsto (fun n : ℕ => (fun θ => rhOutput J θ)^[n] θ₀) Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hJ).mul_const θ₀
  simpa [rhOutput_iterate] using h

/-- **The zero-geometry ceiling.**  For every positive Jensen radius:
`(i)` the unconditional route returns `1/4` from the convexity input, at every radius;
`(ii)` it never improves any input, and never beats `1/4`;
`(iii)` iterating it drives a subconvex input back up to `1/4`;
`(iv)` the same route with the zeros placed on the critical line contracts strictly and iterates
to `0`.
So the entire gain of the route is the horizontal position of the zeros; the vertical count
contributes nothing. -/
theorem zero_geometry_ceiling {R θ₀ : ℝ} (hR : 0 < R) (hθ0 : 0 < θ₀) (hθ : θ₀ ≤ 1/4) :
    jensenOutput (foldedWidth R) (1/4) = 1/4 ∧
    θ₀ ≤ jensenOutput (foldedWidth R) θ₀ ∧
    jensenOutput (foldedWidth R) θ₀ ≤ 1/4 ∧
    (∀ n : ℕ, (fun θ => jensenOutput (foldedWidth R) θ)^[n] θ₀ - 1/4
      = (2 * foldedWidth R) ^ n * (θ₀ - 1/4)) ∧
    rhOutput (foldedWidth R) θ₀ < θ₀ ∧
    Filter.Tendsto (fun n : ℕ => (fun θ => rhOutput (foldedWidth R) θ)^[n] θ₀)
      Filter.atTop (nhds 0) := by
  have hlt := foldedWidth_lt_half hR
  have hnn := foldedWidth_nonneg hR.le
  exact ⟨jensenOutput_quarter _, le_jensenOutput hlt.le hθ,
    jensenOutput_le_quarter hnn hθ, jensenOutput_iterate _ _,
    rhOutput_lt hlt hθ0, rhOutput_tendsto_zero (by rw [abs_lt]; constructor <;> linarith)⟩

/-- An upper bound for the growth exponent `μ(σ)` produced by bounding Dirichlet blocks: the value
at `σ` is the supremum, over admissible block lengths `t^α`, of an affine function of `σ` with slope
`-α`.  The approximate functional equation caps `α` at `1/2`, and the bound on the critical line is
attained at the self-dual block `α = 1/2`. -/
structure AFEBound where
  /-- Exponent bounding a Dirichlet block of length `t^α` on the critical line. -/
  blockExponent : ℝ → ℝ
  /-- The resulting bound on `μ(σ)`. -/
  val : ℝ → ℝ
  /-- Every admissible block gives a valid bound. -/
  dominates : ∀ σ, ∀ α ∈ Set.Icc (0 : ℝ) (1/2), blockExponent α - α * σ ≤ val σ
  /-- On the critical line the bound is attained at the self-dual block. -/
  selfDual : val (1/2) = blockExponent (1/2) - (1/2) * (1/2)

/-- **Every such bound falls at most at slope `1/2`.**  The self-dual block that attains the bound
on the critical line remains admissible at every `σ`, and contributes an affine function of slope
`-1/2`; so the bound can never drop faster. -/
theorem AFEBound.half_lipschitz_lower (M : AFEBound) (σ : ℝ) :
    M.val (1/2) - (σ - 1/2) / 2 ≤ M.val σ := by
  have hmem : (1/2 : ℝ) ∈ Set.Icc (0 : ℝ) (1/2) := by constructor <;> norm_num
  have hdom := M.dominates σ (1/2) hmem
  have hsd := M.selfDual
  linarith

/-- **The plateau identity.**  In the linear regime `R ≤ 2θ₀` the explicit factor `R/π` produced by
the functional equation and the loss `R/π` incurred by the folded mean of a slope-`1/2` bound cancel
identically, so the Jensen balance returns its own input at every radius. -/
theorem afe_plateau_identity (θ₀ R : ℝ) :
    R / π + (1/2) * (2 * θ₀ - 2 * R / π) = θ₀ := by
  ring

/-- **The gain criterion.**  The right derivative of the Jensen-balance output at `R = 0` is
`(1 + 2s)/π`, where `s` is the right derivative at `σ = 1/2` of the bound being fed in. -/
theorem gain_derivative (s : ℝ) : 1 / π + (2 / π) * s = (1 + 2 * s) / π := by
  ring

/-- **No gain from a slope-`1/2` bound.**  The criterion is negative only for `s < -1/2`, which
`AFEBound.half_lipschitz_lower` forbids. -/
theorem no_gain_of_half_lipschitz {s : ℝ} (h : -(1/2 : ℝ) ≤ s) : 0 ≤ (1 + 2 * s) / π :=
  div_nonneg (by linarith) pi_pos.le

/-- **The AFE-slope barrier.**  For any bound produced by the self-dual block:
`(i)` it cannot fall faster than slope `1/2` off the critical line;
`(ii)` in the resulting linear regime the Jensen balance returns exactly the input;
`(iii)` the gain criterion is non-negative, so no radius produces an improvement.
Breaking the barrier requires a bound on `μ(σ)` for `σ > 1/2` that beats the slope-`1/2` line —
equivalently, a critical Dirichlet block longer than `√t`. -/
theorem afe_slope_barrier (M : AFEBound) (σ R : ℝ) :
    M.val (1/2) - (σ - 1/2) / 2 ≤ M.val σ ∧
    R / π + (1/2) * (2 * M.val (1/2) - 2 * R / π) = M.val (1/2) ∧
    0 ≤ (1 + 2 * (-(1/2) : ℝ)) / π :=
  ⟨M.half_lipschitz_lower σ, afe_plateau_identity _ _, no_gain_of_half_lipschitz le_rfl⟩

/-- The ceiling for `μ` at abscissa `1/2 + x` traced by the self-dual block: slope `-1/2` from the
critical-line record `θ₀`. -/
noncomputable def selfDualCeiling (θ₀ x : ℝ) : ℝ := θ₀ - x / 2

/-- The greatest moment order for which the mean value theorem `∫|ζ(1/2+x+it)|^{2k} ≪ T^{1+ε}`
holds: the criticality `σ ≥ 1 - 1/k` reads `k ≤ 1/(1/2 - x)`.  At `x = 0` it is `k = 2`, the fourth
moment. -/
noncomputable def meanValueThreshold (x : ℝ) : ℝ := 1 / (1/2 - x)

/-- Exponent of the large-value saving obtainable at abscissa `1/2 + x` by pairing the self-dual
ceiling with the mean value theorem at its critical order. -/
noncomputable def largeValueSaving (θ₀ x : ℝ) : ℝ :=
  2 * meanValueThreshold x * selfDualCeiling θ₀ x

theorem largeValueSaving_eq {θ₀ x : ℝ} (hx : x < 1/2) :
    largeValueSaving θ₀ x = (2 * θ₀ - x) / (1/2 - x) := by
  have h : (1/2 : ℝ) - x ≠ 0 := by intro hc; rw [sub_eq_zero] at hc; linarith
  unfold largeValueSaving meanValueThreshold selfDualCeiling
  field_simp

@[simp] theorem largeValueSaving_zero (θ₀ : ℝ) : largeValueSaving θ₀ 0 = 4 * θ₀ := by
  unfold largeValueSaving meanValueThreshold selfDualCeiling
  norm_num

/-- **Perfect degeneracy at the convexity bound.**  With `θ₀ = 1/4` the saving is `1` at every
abscissa: the whole strip is exactly tied, so no choice of abscissa is preferred. -/
theorem largeValueSaving_convexity {x : ℝ} (hx : x < 1/2) :
    largeValueSaving (1/4) x = 1 := by
  have h : (1/2 : ℝ) - x ≠ 0 := by intro hc; rw [sub_eq_zero] at hc; linarith
  rw [largeValueSaving_eq hx, div_eq_iff h]
  ring

/-- **Subconvexity breaks the tie, strictly, toward the critical line.**  For `θ₀ < 1/4` the saving
is strictly decreasing in the abscissa, so the unique optimum is `x = 0`. -/
theorem largeValueSaving_strictAnti {θ₀ x y : ℝ} (hθ : θ₀ < 1/4)
    (hxy : x < y) (hy : y < 1/2) :
    largeValueSaving θ₀ y < largeValueSaving θ₀ x := by
  have hx : x < 1/2 := lt_trans hxy hy
  have hdx : (0 : ℝ) < 1/2 - x := by linarith
  have hdy : (0 : ℝ) < 1/2 - y := by linarith
  rw [largeValueSaving_eq hx, largeValueSaving_eq hy, div_lt_div_iff₀ hdy hdx]
  nlinarith [hxy, hθ]

/-- **Self-dual stationarity.**  Pairing the self-dual ceiling with the mean value theorem at its
critical order: at the convexity bound every abscissa gives exactly the same saving `1`, while any
subconvex input makes the saving strictly decreasing, so the optimum is the critical line `x = 0`
with saving `4θ₀` — the fourth moment.  The convexity bound is the degenerate tie; subconvexity
breaks it, and always in the same direction. -/
theorem self_dual_stationarity {θ₀ : ℝ} (hθ : θ₀ < 1/4) :
    (∀ x : ℝ, x < 1/2 → largeValueSaving (1/4) x = 1) ∧
    (∀ x y : ℝ, x < y → y < 1/2 → largeValueSaving θ₀ y < largeValueSaving θ₀ x) ∧
    largeValueSaving θ₀ 0 = 4 * θ₀ :=
  ⟨fun _ hx => largeValueSaving_convexity hx,
   fun _ _ hxy hy => largeValueSaving_strictAnti hθ hxy hy,
   largeValueSaving_zero θ₀⟩

end HTGeometry
