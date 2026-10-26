import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurface
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.BezoutEffectivityAndTheBeurlingObstruction

/-!
# The effectivity calculus

Weil's use of Riemann–Roch on `C × C`, with `h⁰` replaced by an arbitrary real function.

On a polar surface with ample class `A = H + V`, fix a canonical class `κ` and a constant `χ₀`, and
let `χ(x) = ½ x·(x − κ) + χ₀` be the quadratic **Euler characteristic**; it is Serre symmetric,
`χ(κ − x) = χ(x)` (`eulerChar_serre`). A real function `h` on classes satisfies the **Riemann
inequality** if `χ(x) ≤ h(x) + h(κ − x)`: Riemann–Roch with `h¹ ≥ 0` dropped and
`h²(x) = h⁰(κ − x)`.

* **Weil's argument** (`ampleHodgeIndex_of_riemannInequality`). The Riemann inequality together with
  subquadratic growth in degree zero — for every `x` with `x·A = 0` and every `c > 0`,
  `h(nx) + h(κ − nx) < c n²` for arbitrarily large `n` — forces the Hodge index. Values bounded on
  each degree level suffice (`degreeZeroSubquadratic_of_degreeBounded`).
* **Converse** (`exists_effectivity_of_hodgeIndex`). Under the Hodge index, with `κ` in the pole
  plane, `max(0, χ)` satisfies the Riemann inequality and is bounded on degree levels. Hence the
  Hodge index is the existence of an effectivity function (`hodgeIndex_tfae`).
* **Abundance** (`abundant_iff`). A class of degree zero is *abundant* — every function with the
  Riemann inequality grows quadratically along it — iff its self-intersection is positive, and then
  the rate is every `c < ½ x²` (`eventually_le_of_riemannInequality`). The Hodge index is the
  absence of abundant classes.
* **The abundance rate** (`pair_self_le_two_mul_rate`, `eventually_optimalEffectivity_le`). Along
  any class the least growth rate of `h(nx) + h(κ − nx)` over functions with the Riemann inequality
  is exactly `max(0, ½ x²)`, attained by `½ max(0, χ)`. On a primitive class the self-intersection
  is minus the defect, so on the scaling surface the negative part of Weil's form is twice the
  least abundance rate of sections.
* **Calibration.** On the scaling surface of `ℤ` an effectivity function exists iff RH
  (`riemannHypothesis_iff_exists_effectivity`), and an off-line zero is an abundant class
  (`riemannHypothesis_iff_no_abundant_class`). On the Frobenius windows of a curve datum it exists
  iff the datum is unitary; the golden datum has an abundant class (`goldenDatum_exists_abundant`).

The calculus fixes what an `h⁰` must do: grow quadratically along positive classes and
subquadratically in degree zero. It does not supply one.
-/

noncomputable section

open Filter

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

open ArithmeticCastelnuovoSeveri

section Calculus

variable {E : Type*} [AddCommGroup E] [Module ℝ E] (S : PolarSurface E)

/-- The quadratic **Euler characteristic** `χ(x) = ½ x·(x − κ) + χ₀`. -/
def eulerChar (κ : E) (χ₀ : ℝ) (x : E) : ℝ := S.pair x (x - κ) / 2 + χ₀

/-- **Serre symmetry** of the Euler characteristic. -/
theorem eulerChar_serre (κ : E) (χ₀ : ℝ) (x : E) :
    eulerChar S κ χ₀ (κ - x) = eulerChar S κ χ₀ x := by
  rw [eulerChar, eulerChar, show κ - x - κ = -x by abel]
  simp only [map_sub, map_neg, LinearMap.sub_apply]
  rw [S.pair_comm κ x]
  ring

theorem eulerChar_smul (κ : E) (χ₀ t : ℝ) (x : E) :
    eulerChar S κ χ₀ (t • x) = (t ^ 2 * S.pair x x - t * S.pair x κ) / 2 + χ₀ := by
  simp only [eulerChar, map_sub, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The **Riemann inequality** `χ(x) ≤ h(x) + h(κ − x)`. -/
def RiemannInequality (κ : E) (χ₀ : ℝ) (h : E → ℝ) : Prop :=
  ∀ x, eulerChar S κ χ₀ x ≤ h x + h (κ - x)

/-- Values bounded above on every degree level `{x · A = t}`. -/
def DegreeBounded (h : E → ℝ) : Prop :=
  ∀ t : ℝ, ∃ M, ∀ x, S.pair x S.ample = t → h x ≤ M

/-- **Subquadratic growth in degree zero**: along every class of degree zero,
`h(nx) + h(κ − nx) < c n²` for arbitrarily large `n`, for every `c > 0`. -/
def DegreeZeroSubquadratic (κ : E) (h : E → ℝ) : Prop :=
  ∀ x, S.pair x S.ample = 0 → ∀ c : ℝ, 0 < c →
    ∃ᶠ n : ℕ in atTop, h ((n : ℝ) • x) + h (κ - (n : ℝ) • x) < c * (n : ℝ) ^ 2

/-- A class of degree zero is **abundant** if every function with the Riemann inequality grows
quadratically along it. -/
def Abundant (κ : E) (χ₀ : ℝ) (x : E) : Prop :=
  S.pair x S.ample = 0 ∧ ∀ h : E → ℝ, RiemannInequality S κ χ₀ h →
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ h ((n : ℝ) • x) + h (κ - (n : ℝ) • x)

/-- A positive quadratic eventually dominates every affine function on `ℕ`. -/
theorem eventually_affine_lt_quadratic {δ : ℝ} (hδ : 0 < δ) (α β : ℝ) :
    ∀ᶠ n : ℕ in atTop, α * n + β < δ * (n : ℝ) ^ 2 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((|α| + |β| + 1) / δ)
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_max_right N 1).trans hn
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast (le_max_left N 1).trans hn
  have hδn : |α| + |β| + 1 ≤ δ * n := by
    rw [div_le_iff₀ hδ] at hN
    nlinarith
  have hsq : (|α| + |β| + 1) * n ≤ δ * (n : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hδn (by linarith : (0 : ℝ) ≤ n)
    nlinarith
  nlinarith [le_abs_self α, le_abs_self β, abs_nonneg α, abs_nonneg β]

theorem pair_smul_ample (t : ℝ) (x : E) : S.pair (t • x) S.ample = t * S.pair x S.ample := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]

/-- **Abundance.** If `x² > 0`, every function with the Riemann inequality eventually satisfies
`h(nx) + h(κ − nx) ≥ c n²` for each `c < ½ x²`. -/
theorem eventually_le_of_riemannInequality {κ : E} {χ₀ : ℝ} {h : E → ℝ}
    (hRI : RiemannInequality S κ χ₀ h) {x : E} {c : ℝ} (hc : c < S.pair x x / 2) :
    ∀ᶠ n : ℕ in atTop, c * (n : ℝ) ^ 2 ≤ h ((n : ℝ) • x) + h (κ - (n : ℝ) • x) := by
  filter_upwards [eventually_affine_lt_quadratic (sub_pos.mpr hc) (S.pair x κ / 2) (-χ₀)]
    with n hn
  refine le_trans ?_ (hRI _)
  rw [eulerChar_smul]
  nlinarith

/-- **Weil's argument.** The Riemann inequality and subquadratic growth in degree zero force the
Hodge index for the ample class. -/
theorem ampleHodgeIndex_of_riemannInequality {κ : E} {χ₀ : ℝ} {h : E → ℝ}
    (hRI : RiemannInequality S κ χ₀ h) (hsub : DegreeZeroSubquadratic S κ h) :
    S.AmpleHodgeIndex := by
  intro x hx
  by_contra hpos
  have hpos := not_le.mp hpos
  have hc : S.pair x x / 4 < S.pair x x / 2 := by linarith
  obtain ⟨n, hn1, hn2⟩ := ((hsub x hx (S.pair x x / 8) (by linarith)).and_eventually
    (eventually_le_of_riemannInequality S hRI hc)).exists
  nlinarith [sq_nonneg (n : ℝ)]

theorem hodgeIndex_of_riemannInequality {κ : E} {χ₀ : ℝ} {h : E → ℝ}
    (hRI : RiemannInequality S κ χ₀ h) (hsub : DegreeZeroSubquadratic S κ h) :
    S.HodgeIndex :=
  S.hodgeIndex_iff_castelnuovoSeveri.mpr
    (S.ampleHodgeIndex_iff_castelnuovoSeveri.mp (ampleHodgeIndex_of_riemannInequality S hRI hsub))

/-- Values bounded on degree levels give subquadratic growth in degree zero: along `x` of degree
zero, `nx` has degree `0` and `κ − nx` has the degree of `κ`. -/
theorem degreeZeroSubquadratic_of_degreeBounded {κ : E} {h : E → ℝ} (hb : DegreeBounded S h) :
    DegreeZeroSubquadratic S κ h := by
  intro x hx c hc
  obtain ⟨M₀, hM₀⟩ := hb 0
  obtain ⟨M₁, hM₁⟩ := hb (S.pair κ S.ample)
  refine Eventually.frequently ?_
  filter_upwards [eventually_affine_lt_quadratic hc 0 (M₀ + M₁)] with n hn
  have h0 : h ((n : ℝ) • x) ≤ M₀ := hM₀ _ (by rw [pair_smul_ample, hx, mul_zero])
  have h1 : h (κ - (n : ℝ) • x) ≤ M₁ := hM₁ _ (by
    rw [map_sub, LinearMap.sub_apply, pair_smul_ample, hx, mul_zero, sub_zero])
  linarith

/-- The **level bound** of the Euler characteristic: the maximum of `χ` on the degree level
`x · A = t` under the Hodge index, for `κ = aH + bV`. -/
def levelBound (a b χ₀ t : ℝ) : ℝ := (t - (a - b) / 2) ^ 2 / 4 - b * t / 2 + χ₀

/-- Under the Hodge index the Euler characteristic is bounded on each degree level by the level
bound: `x² ≤ 2(x·H)(x·V)` and `(x·H) + (x·V) = t` leave a concave quadratic in `x·H`. -/
theorem eulerChar_le_levelBound (hH : S.HodgeIndex) (a b χ₀ : ℝ) {x : E} {t : ℝ}
    (hx : S.pair x S.ample = t) : eulerChar S (a • S.H + b • S.V) χ₀ x ≤ levelBound a b χ₀ t := by
  have hCS := (S.hodgeIndex_iff_castelnuovoSeveri.mp hH) x
  have hdeg : S.pair x S.H + S.pair x S.V = t := by rw [← S.pair_ample, hx]
  have hκx : S.pair x (a • S.H + b • S.V) = a * S.pair x S.H + b * S.pair x S.V := by
    simp only [map_add, map_smul, smul_eq_mul]
  simp only [eulerChar, levelBound, map_sub]
  rw [hκx]
  have hv : S.pair x S.V = t - S.pair x S.H := by linarith
  rw [hv] at hCS ⊢
  nlinarith [sq_nonneg (S.pair x S.H - (t - (a - b) / 2) / 2)]

/-- **The converse.** Under the Hodge index, with `κ = aH + bV` in the pole plane, `max(0, χ)` is a
nonnegative function with the Riemann inequality, bounded on every degree level. -/
theorem exists_effectivity_of_hodgeIndex (hH : S.HodgeIndex) (a b χ₀ : ℝ) :
    ∃ h : E → ℝ, (∀ x, 0 ≤ h x) ∧ RiemannInequality S (a • S.H + b • S.V) χ₀ h ∧
      DegreeBounded S h := by
  refine ⟨fun x => max 0 (eulerChar S (a • S.H + b • S.V) χ₀ x), fun x => le_max_left _ _,
    fun x => ?_, fun t => ⟨max 0 (levelBound a b χ₀ t), fun x hx =>
      max_le_max le_rfl (eulerChar_le_levelBound S hH a b χ₀ hx)⟩⟩
  exact (le_max_right _ _).trans (le_add_of_nonneg_right (le_max_left _ _))

/-- **Abundance is positivity.** A class is abundant iff it has degree zero and positive
self-intersection. The witness against abundance for `x² ≤ 0` is `max(0, χ)`, which grows at most
linearly along `x`. -/
theorem abundant_iff (κ : E) (χ₀ : ℝ) (x : E) :
    Abundant S κ χ₀ x ↔ S.pair x S.ample = 0 ∧ 0 < S.pair x x := by
  constructor
  · rintro ⟨hx, hab⟩
    refine ⟨hx, ?_⟩
    by_contra hneg
    have hneg := not_lt.mp hneg
    obtain ⟨c, hc, hev⟩ := hab (fun y => max 0 (eulerChar S κ χ₀ y))
      (fun y => (le_max_right _ _).trans (le_add_of_nonneg_right (le_max_left _ _)))
    obtain ⟨n, hn1, hn2⟩ := (hev.and (eventually_affine_lt_quadratic hc
      |S.pair x κ| (2 * |χ₀|))).exists
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hbound : max 0 (eulerChar S κ χ₀ ((n : ℝ) • x)) ≤ n * |S.pair x κ| / 2 + |χ₀| := by
      refine max_le (by positivity) ?_
      rw [eulerChar_smul]
      nlinarith [neg_abs_le (S.pair x κ), le_abs_self χ₀, mul_nonneg (sq_nonneg (n : ℝ))
        (neg_nonneg.mpr hneg), mul_le_mul_of_nonneg_left (neg_abs_le (S.pair x κ)) hn0]
    simp only [eulerChar_serre] at hn1
    linarith
  · rintro ⟨hx, hpos⟩
    exact ⟨hx, fun h hRI => ⟨S.pair x x / 4, by linarith,
      eventually_le_of_riemannInequality S hRI (by linarith)⟩⟩

/-- **The abundance rate bounds the form.** If a function with the Riemann inequality grows along
`x` at rate at most `r` for arbitrarily large `n`, then `x² ≤ 2r`. -/
theorem pair_self_le_two_mul_rate {κ : E} {χ₀ : ℝ} {h : E → ℝ} (hRI : RiemannInequality S κ χ₀ h)
    {x : E} {r : ℝ} (hr : ∃ᶠ n : ℕ in atTop, h ((n : ℝ) • x) + h (κ - (n : ℝ) • x) ≤ r * (n : ℝ) ^ 2) :
    S.pair x x ≤ 2 * r := by
  by_contra hlt
  have hlt := not_le.mp hlt
  have hc : (r + S.pair x x / 2) / 2 < S.pair x x / 2 := by linarith
  obtain ⟨n, hn1, hn2⟩ := ((hr.and_eventually (eventually_le_of_riemannInequality S hRI hc)).and_eventually
    (eventually_gt_atTop 0)).exists
  have hn : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn2) 2
  nlinarith [hn1.1, hn1.2]

/-- The **optimal effectivity function** `½ max(0, χ)`: by Serre symmetry
`h(x) + h(κ − x) = max(0, χ(x))`. -/
def optimalEffectivity (κ : E) (χ₀ : ℝ) (x : E) : ℝ := max 0 (eulerChar S κ χ₀ x) / 2

theorem optimalEffectivity_add (κ : E) (χ₀ : ℝ) (x : E) :
    optimalEffectivity S κ χ₀ x + optimalEffectivity S κ χ₀ (κ - x) = max 0 (eulerChar S κ χ₀ x) := by
  rw [optimalEffectivity, optimalEffectivity, eulerChar_serre]; ring

theorem riemannInequality_optimalEffectivity (κ : E) (χ₀ : ℝ) :
    RiemannInequality S κ χ₀ (optimalEffectivity S κ χ₀) := fun x => by
  rw [optimalEffectivity_add]; exact le_max_right _ _

/-- **The abundance rate is attained**: along every class the optimal effectivity function grows at
rate at most `max(0, x²/2) + ε`. Together with `pair_self_le_two_mul_rate`, the least growth rate
of sections along `x` is exactly the positive part of `½ x²`. -/
theorem eventually_optimalEffectivity_le (κ : E) (χ₀ : ℝ) (x : E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, optimalEffectivity S κ χ₀ ((n : ℝ) • x) +
      optimalEffectivity S κ χ₀ (κ - (n : ℝ) • x) ≤ (max 0 (S.pair x x / 2) + ε) * (n : ℝ) ^ 2 := by
  filter_upwards [eventually_affine_lt_quadratic hε (|S.pair x κ| / 2) |χ₀|] with n hn
  rw [optimalEffectivity_add]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hbound : eulerChar S κ χ₀ ((n : ℝ) • x) ≤ (max 0 (S.pair x x / 2) + ε) * (n : ℝ) ^ 2 := by
    rw [eulerChar_smul]
    have h1 : (n : ℝ) ^ 2 * S.pair x x / 2 ≤ max 0 (S.pair x x / 2) * (n : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left (le_max_right 0 (S.pair x x / 2)) (sq_nonneg (n : ℝ))
      linarith
    nlinarith [neg_abs_le (S.pair x κ), le_abs_self χ₀,
      mul_le_mul_of_nonneg_left (neg_abs_le (S.pair x κ)) hn0]
  exact max_le (mul_nonneg (by linarith [le_max_left 0 (S.pair x x / 2)]) (sq_nonneg _)) hbound

/-- The ample Hodge index is the absence of abundant classes. -/
theorem ampleHodgeIndex_iff_not_abundant (κ : E) (χ₀ : ℝ) :
    S.AmpleHodgeIndex ↔ ∀ x, ¬ Abundant S κ χ₀ x := by
  simp only [abundant_iff, not_and, not_lt]
  exact Iff.rfl

/-- **The effectivity calculus.** With `κ` in the pole plane, four statements are equivalent: the
Hodge index; an effectivity function bounded on degree levels; an effectivity function with
subquadratic growth in degree zero; no abundant class. -/
theorem hodgeIndex_tfae (a b χ₀ : ℝ) :
    List.TFAE [S.HodgeIndex,
      ∃ h : E → ℝ, RiemannInequality S (a • S.H + b • S.V) χ₀ h ∧ DegreeBounded S h,
      ∃ h : E → ℝ, RiemannInequality S (a • S.H + b • S.V) χ₀ h ∧
        DegreeZeroSubquadratic S (a • S.H + b • S.V) h,
      ∀ x, ¬ Abundant S (a • S.H + b • S.V) χ₀ x] := by
  tfae_have 1 → 2 := fun hH => by
    obtain ⟨h, -, hRI, hb⟩ := exists_effectivity_of_hodgeIndex S hH a b χ₀
    exact ⟨h, hRI, hb⟩
  tfae_have 2 → 3 := fun ⟨h, hRI, hb⟩ => ⟨h, hRI, degreeZeroSubquadratic_of_degreeBounded S hb⟩
  tfae_have 3 → 1 := fun ⟨h, hRI, hsub⟩ => hodgeIndex_of_riemannInequality S hRI hsub
  tfae_have 1 ↔ 4 := by
    rw [S.hodgeIndex_iff_castelnuovoSeveri, ← S.ampleHodgeIndex_iff_castelnuovoSeveri]
    exact ampleHodgeIndex_iff_not_abundant S _ χ₀
  tfae_finish

end Calculus

/-! ### Calibration -/

/-- **The scaling surface.** An effectivity function on the scaling surface of `ℤ`, bounded on degree
levels, exists iff RH. -/
theorem riemannHypothesis_iff_exists_effectivity (a b χ₀ : ℝ) :
    RiemannHypothesis ↔ ∃ h : ScalingCycle → ℝ,
      RiemannInequality scalingSurface (a • scalingSurface.H + b • scalingSurface.V) χ₀ h ∧
        DegreeBounded scalingSurface h := by
  rw [← scalingSurface_hodgeIndex_iff]
  exact (hodgeIndex_tfae scalingSurface a b χ₀).out 0 1

/-- **An off-line zero is an abundant class.** RH holds iff the scaling surface has no class of
degree zero along which every function with the Riemann inequality grows quadratically. -/
theorem riemannHypothesis_iff_no_abundant_class (κ : ScalingCycle) (χ₀ : ℝ) :
    RiemannHypothesis ↔ ∀ x, ¬ Abundant scalingSurface κ χ₀ x := by
  rw [← scalingSurface_hodgeIndex_iff, scalingSurface.hodgeIndex_iff_castelnuovoSeveri,
    ← scalingSurface.ampleHodgeIndex_iff_castelnuovoSeveri]
  exact ampleHodgeIndex_iff_not_abundant scalingSurface κ χ₀

/-- **Curves.** A curve datum is unitary iff every Frobenius window carries an effectivity
function bounded on degree levels. -/
theorem CurveDatum.unitary_iff_forall_window_exists_effectivity {ι : Type*} [Fintype ι]
    (D : CurveDatum ι) (a b χ₀ : ℝ) :
    (∀ i, ‖D.β i‖ = 1) ↔ ∀ W : Finset ℕ, ∃ h : SpanCycle → ℝ,
      RiemannInequality (D.windowSurface W)
        (a • (D.windowSurface W).H + b • (D.windowSurface W).V) χ₀ h ∧
        DegreeBounded (D.windowSurface W) h := by
  rw [← D.windowSurface_hodgeIndex_iff_unitary]
  exact forall_congr' fun W => (hodgeIndex_tfae (D.windowSurface W) a b χ₀).out 0 1

/-- **The golden datum** `1 − 5X + 5X²` has a Frobenius window with an abundant class: integral
point counts and a functional equation do not keep degree-zero sections bounded. -/
theorem goldenDatum_exists_abundant (κ : SpanCycle) (χ₀ : ℝ) :
    ∃ W : Finset ℕ, ∃ x, Abundant (goldenDatum.windowSurface W) κ χ₀ x := by
  by_contra h
  simp only [not_exists] at h
  apply goldenDatum_not_unitary
  rw [← goldenDatum.windowSurface_hodgeIndex_iff_unitary]
  intro W
  rw [(goldenDatum.windowSurface W).hodgeIndex_iff_castelnuovoSeveri,
    ← (goldenDatum.windowSurface W).ampleHodgeIndex_iff_castelnuovoSeveri]
  exact (ampleHodgeIndex_iff_not_abundant _ κ χ₀).mpr (h W)

end GaloisForLFunctions.ArithmeticEffectivityTheory
