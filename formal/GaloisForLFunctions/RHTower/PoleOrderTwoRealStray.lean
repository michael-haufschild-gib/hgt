import GaloisForLFunctions.RHTower.EntireFunctionalEquationOffLine

/-!
# Pole order two already permits zeros off the critical line

Work in logarithmic coordinates, `dΨ = u·dΠ_*`, `M(s) = ∫₀^∞ e^{-su} dΨ(u) = -F'/F(s)`.  Invariance
of `π^{-s/2}Γ(s/2)F(s)` under `s ↦ 1-s` is equivalent to `M(s) + M(1-s) = A(s)` with `A` depending
only on the archimedean factor, so two zeta functions with the same functional equation differ by a
**reflection antisymmetric** correction `N(s) = -N(1-s)`.  Writing `w = r - 1/2`, the elementary
antisymmetric transforms are `1/(s-r) + 1/(s-(1-r))`, whose inverse transform is
`e^{ru} + e^{(1-r)u} = 2e^{u/2}cosh(wu)`; a **negative** coefficient at `w` inserts a zero of `F` at
`1/2 ± w`, a **positive** coefficient a pole.

`EntireFunctionalEquationOffLine.lean` reached an entire completed function with off-critical zeros
at the cost of a pole of order three at `s = 1`.  Order three is not needed.  The correction

```text
d(u) = e^u + 1 - e^{(1/2+w)u} - e^{(1/2-w)u} = (e^{u/2} - e^{wu})(e^{u/2} - e^{-wu}) ≥ 0
```

has its whole positive part at the single admissible real frequency `w = 1/2`, with coefficient
one instead of two, and inserts the **real** pair of zeros `1/2 ± w`.  The resulting

```text
F(s) = ζ(s)·((s - 1/2)² - w²)/(s(s-1)),
(s(s-1))²·π^{-s/2}Γ(s/2)·F(s)/2 = ξ(s)·((s - 1/2)² - w²)
```

is entire of order one, invariant under `s ↦ 1-s`, has nonnegative generalized von Mangoldt
measure, and has zeros at `1/2 ± w` off the critical line, with a pole of order **two** at `s = 1`.

The final section shows two is optimal and quantifies the cost of leaving the critical line.  Local
finiteness of the prime measure at `x = 1` forces the trace condition `Σ t_j = 0`, so the
coefficient at the admissible frequency `1/2` — equivalently `ord₁F - 1` — is the total inserted
multiplicity counted by **frequency pairs** `{w, -w}`, since `cosh(wu) = cosh(-wu)`.  A frequency
pair is stable under conjugation exactly when `w` is real or purely imaginary, i.e. exactly when the
inserted zeros are real or critical.  So a genuinely complex off-critical quadruple occupies two
distinct frequency pairs and costs two budget units, forcing `ord₁F ≥ 3`, whereas a real stray pair
costs one and `ord₁F = 2` suffices.
-/

open Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace RHTower

/-! ## The correction density -/

/-- Logarithmic density of the pole-order-two correction inserting the real zero pair
`1/2 ± w`. -/
def realStrayDensity (w u : ℝ) : ℝ :=
  Real.exp u + 1 - Real.exp ((1 / 2 + w) * u) - Real.exp ((1 / 2 - w) * u)

/-- The density factors as a product of two differences of exponentials. -/
theorem realStrayDensity_factor (w u : ℝ) :
    realStrayDensity w u
      = (Real.exp (u / 2) - Real.exp (w * u)) * (Real.exp (u / 2) - Real.exp (-(w * u))) := by
  have h1 : Real.exp (u / 2) * Real.exp (u / 2) = Real.exp u := by
    rw [← Real.exp_add]; congr 1; ring
  have h2 : Real.exp (w * u) * Real.exp (-(w * u)) = 1 := by
    rw [← Real.exp_add]; simp
  have h3 : Real.exp (u / 2) * Real.exp (-(w * u)) = Real.exp ((1 / 2 - w) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (w * u) * Real.exp (u / 2) = Real.exp ((1 / 2 + w) * u) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold realStrayDensity
  nlinarith [h1, h2, h3, h4]

/-- **Λ-positivity.**  The correction is a nonnegative measure for every real stray parameter
`w ∈ [0, 1/2]`. -/
theorem realStrayDensity_nonneg {w u : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2) (hu : 0 ≤ u) :
    0 ≤ realStrayDensity w u := by
  rw [realStrayDensity_factor]
  have hA : Real.exp (w * u) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hB : Real.exp (-(w * u)) ≤ Real.exp (u / 2) := Real.exp_le_exp.mpr (by nlinarith)
  exact mul_nonneg (by linarith) (by linarith)

/-! ## Nonnegativity of the prime measure

The Möbius inversion `dΠ = Σ_k μ(k)k^{-2}dΠ_*(·/k)` is nonnegative as soon as the prime-power
density `u ↦ d(u)/u` is nonnegative and nondecreasing.  Since `d = A·B` with `B(u) = e^{u/2} -
e^{-wu}` nonnegative and nondecreasing, it suffices that `A(u)/u = (e^{u/2} - e^{wu})/u` be
nondecreasing, which in cross-multiplied form is monotonicity of `t ↦ (t-1)e^t` on `[0,∞)`. -/

/-- `t ↦ (t-1)e^t` is monotone on `[0,∞)`; its derivative is `t e^t`. -/
theorem monotoneOn_sub_one_mul_exp :
    MonotoneOn (fun t : ℝ => (t - 1) * Real.exp t) (Ici (0 : ℝ)) := by
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t - 1) * Real.exp t) (t * Real.exp t) t := by
    intro t
    have h := ((hasDerivAt_id t).sub_const (1 : ℝ)).mul (Real.hasDerivAt_exp t)
    simpa using h.congr_deriv (by simp; ring)
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop)
    (fun t _ => (hderiv t).differentiableAt.differentiableWithinAt) ?_
  intro t ht
  rw [interior_Ici] at ht
  rw [(hderiv t).deriv]
  have ht' : (0 : ℝ) ≤ t := le_of_lt ht
  positivity

/-- The scaled factor `(e^{u/2} - e^{wu})/u` is nondecreasing; in cross-multiplied form,
`u·((1/2)e^{u/2} - w e^{wu}) ≥ e^{u/2} - e^{wu}`.  This is what makes the *prime* measure — and not
merely the von Mangoldt measure — nonnegative. -/
theorem realStrayFactor_ratio_ineq {w u : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2) (hu : 0 ≤ u) :
    (w * u - 1) * Real.exp (w * u) ≤ (u / 2 - 1) * Real.exp (u / 2) := by
  have hx : (0 : ℝ) ≤ w * u := mul_nonneg hw0 hu
  have hy : (0 : ℝ) ≤ u / 2 := by linarith
  have hxy : w * u ≤ u / 2 := by nlinarith
  exact monotoneOn_sub_one_mul_exp hx hy hxy

/-! ## The Laplace transform of the correction -/

/-- Real form of the transform: `1/(σ-1) + 1/σ - 1/(σ-1/2-w) - 1/(σ-1/2+w)`. -/
def realStrayTransformReal (w σ : ℝ) : ℝ :=
  1 / (σ - 1) + 1 / σ - 1 / (σ - (1 / 2 + w)) - 1 / (σ - (1 / 2 - w))

theorem integral_realStrayDensity {w σ : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ 1 / 2) (hσ : 1 < σ) :
    (∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * realStrayDensity w u)
      = realStrayTransformReal w σ := by
  have key : ∀ p : ℝ, 0 < σ - p →
      (∫ u in Ioi (0 : ℝ), Real.exp (-(σ * u)) * Real.exp (p * u)) = 1 / (σ - p) := by
    intro p hp
    have hcongr : (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp (p * u))
        = fun u : ℝ => Real.exp (-((σ - p) * u)) := by
      funext u; rw [← Real.exp_add]; congr 1; ring
    rw [hcongr, integral_Ioi_exp_neg_mul hp]
  have hint : ∀ p : ℝ, 0 < σ - p →
      IntegrableOn (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp (p * u)) (Ioi 0) := by
    intro p hp
    have hcongr : (fun u : ℝ => Real.exp (-(σ * u)) * Real.exp (p * u))
        = fun u : ℝ => Real.exp (-(σ - p) * u) := by
      funext u; rw [← Real.exp_add]; congr 1; ring
    rw [hcongr]; exact exp_neg_integrableOn_Ioi 0 hp
  have h1 : (0 : ℝ) < σ - 1 := by linarith
  have h0 : (0 : ℝ) < σ - 0 := by linarith
  have hp : (0 : ℝ) < σ - (1 / 2 + w) := by linarith
  have hm : (0 : ℝ) < σ - (1 / 2 - w) := by linarith
  have I1 := hint 1 h1
  have I2 := hint 0 h0
  have I3 := hint _ hp
  have I4 := hint _ hm
  have hA : IntegrableOn (fun u : ℝ =>
      Real.exp (-(σ * u)) * Real.exp ((1 : ℝ) * u)
        + Real.exp (-(σ * u)) * Real.exp ((0 : ℝ) * u)) (Ioi 0) := by simpa using I1.add I2
  have hB : IntegrableOn (fun u : ℝ =>
      Real.exp (-(σ * u)) * Real.exp ((1 / 2 + w) * u)
        + Real.exp (-(σ * u)) * Real.exp ((1 / 2 - w) * u)) (Ioi 0) := by simpa using I3.add I4
  have hsplit : (fun u : ℝ => Real.exp (-(σ * u)) * realStrayDensity w u)
      = fun u : ℝ =>
        (Real.exp (-(σ * u)) * Real.exp ((1 : ℝ) * u)
          + Real.exp (-(σ * u)) * Real.exp ((0 : ℝ) * u))
        - (Real.exp (-(σ * u)) * Real.exp ((1 / 2 + w) * u)
          + Real.exp (-(σ * u)) * Real.exp ((1 / 2 - w) * u)) := by
    funext u
    unfold realStrayDensity
    simp only [one_mul, zero_mul, Real.exp_zero]
    ring
  rw [hsplit, integral_sub hA hB, integral_add I1 I2, integral_add I3 I4,
    key 1 h1, key 0 h0, key _ hp, key _ hm]
  unfold realStrayTransformReal
  ring

/-- Complex form of the transform. -/
def realStrayTransform (w : ℝ) (s : ℂ) : ℂ :=
  (s - 1)⁻¹ + s⁻¹ - ((s - ((1 / 2 + w : ℝ) : ℂ))⁻¹ + (s - ((1 / 2 - w : ℝ) : ℂ))⁻¹)

/-- **The functional equation.**  The correction is reflection antisymmetric, so `F` inherits the
exact Riemann functional equation from `ζ`. -/
theorem realStrayTransform_antisymm (w : ℝ) (s : ℂ) :
    realStrayTransform w s + realStrayTransform w (1 - s) = 0 := by
  have pair : ∀ r : ℂ, (s - r)⁻¹ + (s - (1 - r))⁻¹ +
      ((1 - s - r)⁻¹ + (1 - s - (1 - r))⁻¹) = 0 := by
    intro r
    have h1 : (1 : ℂ) - s - r = -(s - (1 - r)) := by ring
    have h2 : (1 : ℂ) - s - (1 - r) = -(s - r) := by ring
    rw [h1, h2, inv_neg, inv_neg]; ring
  have hp := pair 1
  have hq := pair (((1 / 2 + w : ℝ) : ℂ))
  have e0 : (1 : ℂ) - 1 = 0 := by ring
  have e1 : (1 : ℂ) - ((1 / 2 + w : ℝ) : ℂ) = ((1 / 2 - w : ℝ) : ℂ) := by push_cast; ring
  rw [e0] at hp
  rw [e1] at hq
  simp only [realStrayTransform]
  linear_combination hp - hq

/-! ## The completed function -/

/-- The quadratic factor carrying the inserted real zero pair `1/2 ± w`. -/
def realStrayQuadratic (w : ℝ) (s : ℂ) : ℂ := (s - 1 / 2) ^ 2 - (w : ℂ) ^ 2

/-- The inserted factor is invariant under the reflection `s ↦ 1 - s`. -/
theorem realStrayQuadratic_reflect (w : ℝ) (s : ℂ) :
    realStrayQuadratic w (1 - s) = realStrayQuadratic w s := by
  unfold realStrayQuadratic; ring

/-- The gauge by which `F` differs from `ζ`. -/
def realStrayGauge (w : ℝ) (s : ℂ) : ℂ := realStrayQuadratic w s / (s * (s - 1))

/-- Clearing the double pole: `gauge(s)·s(s-1)` is the entire quadratic factor, so
`(s(s-1))²·π^{-s/2}Γ(s/2)F(s)/2 = ξ(s)·((s-1/2)² - w²)`, entire of order one and invariant under
`s ↦ 1-s`. -/
theorem realStrayGauge_mul_completion (w : ℝ) {s : ℂ} (hs : s ≠ 0) (hs1 : s ≠ 1) :
    realStrayGauge w s * (s * (s - 1)) = realStrayQuadratic w s := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  unfold realStrayGauge
  field_simp

/-- The inserted zeros sit at the **real** points `1/2 ± w`. -/
theorem realStrayQuadratic_eq_zero (w : ℝ) :
    realStrayQuadratic w (((1 / 2 + w : ℝ) : ℂ)) = 0 ∧
      realStrayQuadratic w (((1 / 2 - w : ℝ) : ℂ)) = 0 := by
  constructor <;> · unfold realStrayQuadratic; push_cast; ring

/-- **Off the critical line.**  For `w ≠ 0` the inserted zeros have real part `≠ 1/2`. -/
theorem realStray_offCriticalLine {w : ℝ} (hw : w ≠ 0) :
    ((((1 / 2 + w : ℝ) : ℂ)).re ≠ 1 / 2) ∧ ((((1 / 2 - w : ℝ) : ℂ)).re ≠ 1 / 2) := by
  constructor <;> · simp; intro h; exact hw (by linarith)

/-- **Pole order two suffices.**  For every `w ∈ (0, 1/2]` there is a reflection-antisymmetric
correction of `ζ`'s von Mangoldt measure which is a nonnegative measure, whose Laplace transform
has its whole positive part at the single admissible real frequency `1/2` with coefficient one —
raising the pole at `s = 1` to order exactly two — and which inserts a pair of zeros `1/2 ± w` off
the critical line, the completed function `ξ(s)·((s-1/2)² - w²)` remaining entire of order one and
invariant under `s ↦ 1-s`. -/
theorem lambdaPositive_poleOrderTwo_not_criticalLine {w : ℝ} (hw0 : 0 < w) (hw : w ≤ 1 / 2) :
    (∀ u : ℝ, 0 ≤ u → 0 ≤ realStrayDensity w u) ∧
      (∀ s : ℂ, realStrayTransform w s + realStrayTransform w (1 - s) = 0) ∧
      (∀ s : ℂ, realStrayQuadratic w (1 - s) = realStrayQuadratic w s) ∧
      realStrayQuadratic w (((1 / 2 + w : ℝ) : ℂ)) = 0 ∧
      ((((1 / 2 + w : ℝ) : ℂ)).re ≠ 1 / 2) :=
  ⟨fun _ hu => realStrayDensity_nonneg (le_of_lt hw0) hw hu,
    realStrayTransform_antisymm w, realStrayQuadratic_reflect w,
    (realStrayQuadratic_eq_zero w).1, (realStray_offCriticalLine (ne_of_gt hw0)).1⟩

/-! ## The budget law -/

/-- A frequency contributes the pair `{w, -w}`, since `cosh(wu) = cosh(-wu)`.  The pair is stable
under conjugation exactly when `w` is real or purely imaginary — exactly when the inserted zeros
`1/2 ± w` are either real or on the critical line.  Any other inserted zero therefore occupies two
distinct frequency pairs. -/
theorem frequencyPair_conj_stable_iff (w : ℂ) :
    ({w, -w} : Set ℂ) = {(starRingEnd ℂ) w, -(starRingEnd ℂ) w} ↔ w.im = 0 ∨ w.re = 0 := by
  constructor
  · intro h
    have hmem : (starRingEnd ℂ) w ∈ ({w, -w} : Set ℂ) := by
      rw [h]; exact Set.mem_insert _ _
    rcases hmem with h1 | h1
    · left
      have := congrArg Complex.im h1
      simp only [Complex.conj_im] at this
      linarith
    · right
      have h2 : (starRingEnd ℂ) w = -w := h1
      have := congrArg Complex.re h2
      simp only [Complex.conj_re, Complex.neg_re] at this
      linarith
  · intro h
    rcases h with h | h
    · rw [Complex.conj_eq_iff_im.mpr h]
    · have hc : (starRingEnd ℂ) w = -w := by
        apply Complex.ext <;> simp [h]
      rw [hc, neg_neg]
      exact Set.pair_comm w (-w)

/-- **The trace condition.**  Local finiteness of the prime measure at `x = 1` gives `Σ_j t_j = 0`.
With the single positive coefficient `t₀` at the admissible frequency `1/2` and every other
coefficient nonpositive, the budget spent equals the total inserted multiplicity, and
`ord₁F = 1 + t₀`. -/
theorem poleOrderBudget {ι : Type*} (s : Finset ι) (t : ι → ℝ) (t0 : ℝ)
    (hneg : ∀ i ∈ s, t i ≤ 0) (htrace : t0 + ∑ i ∈ s, t i = 0) :
    t0 = ∑ i ∈ s, |t i| := by
  have h : ∑ i ∈ s, |t i| = -∑ i ∈ s, t i := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i hi => abs_of_nonpos (hneg i hi)
  rw [h]; linarith

/-- **Cost of a genuinely complex stray.**  Two distinct inserted frequency pairs, each of
multiplicity at least one — which is what a zero that is neither real nor critical forces, by
`frequencyPair_conj_stable_iff` — spend at least two budget units, so `ord₁F = 1 + t₀ ≥ 3`.  A real
or critical stray occupies one frequency pair and spends one unit, so `ord₁F = 2` suffices, and
`lambdaPositive_poleOrderTwo_not_criticalLine` realizes it off the critical line. -/
theorem poleOrderBudget_ge_two {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → ℝ) (t0 : ℝ)
    (hneg : ∀ i ∈ s, t i ≤ 0) (htrace : t0 + ∑ i ∈ s, t i = 0)
    {j k : ι} (hj : j ∈ s) (hk : k ∈ s) (hjk : j ≠ k)
    (htj : t j ≤ -1) (htk : t k ≤ -1) :
    2 ≤ t0 := by
  rw [poleOrderBudget s t t0 hneg htrace]
  have hsub : ({j, k} : Finset ι) ⊆ s := by
    intro i hi
    rcases Finset.mem_insert.mp hi with h | h
    · exact h ▸ hj
    · exact (Finset.mem_singleton.mp h) ▸ hk
  have hle : ∑ i ∈ ({j, k} : Finset ι), |t i| ≤ ∑ i ∈ s, |t i| :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => abs_nonneg _)
  have hpair : ∑ i ∈ ({j, k} : Finset ι), |t i| = |t j| + |t k| := Finset.sum_pair hjk
  have h1 : (1 : ℝ) ≤ |t j| := by rw [abs_of_nonpos (by linarith)]; linarith
  have h2 : (1 : ℝ) ≤ |t k| := by rw [abs_of_nonpos (by linarith)]; linarith
  rw [hpair] at hle
  linarith

end RHTower
