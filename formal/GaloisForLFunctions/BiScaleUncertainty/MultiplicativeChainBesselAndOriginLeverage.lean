import GaloisForLFunctions.BiScaleUncertainty.KreinIncrementAndChordCascade

/-!
# Pillar II: Multiplicative-Chain Bessel & Origin-Singularity Leverage Theory

This module develops the second pillar of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`): the multi-node Hilbert-space geometry of translates on
difference-closed and logarithmic divisibility grids, and its coupling to the continuum `1/y`
singularity at the origin.

## Core Mathematical Insights

1. **Orthogonal-Frame Bessel Sphere Law (`autocorr_finset_bessel_sq_le`):**
   If a finite family of shifts `{t_i}_{i ∈ s}` is pairwise orthogonal under `h = autocorr f`
   (`h(t_i - t_j) = 0` for `i ≠ j`), then the translated functions `{f(· + t_i)}_{i ∈ s}` form an
   orthogonal frame in `L²(ℝ)` of norm `√(h(0))`. By Bessel's inequality applied to `f(· + y)`,
   for **every** `y ∈ ℝ`,
   `∑ i ∈ s, h(y - t_i)^2 ≤ h(0)^2`.
2. **Origin-Anchored Euclidean Sphere Law (`autocorr_origin_chain_sphere_sub_le`,
   `autocorr_origin_chain_sphere_add_le`, `autocorr_reflected_collar_sum_sub_ge`):**
   If `h(t_i) = 0` for all `i ∈ s` and `h(t_i - t_j) = 0` for all `i ≠ j ∈ s`, adjoining the origin
   node `t₀ = 0` yields the derivative-free Euclidean Sphere Laws
   `h(y)^2 + ∑ i ∈ s, h(t_i - y)^2 ≤ h(0)^2` and `h(y)^2 + ∑ i ∈ s, h(t_i + y)^2 ≤ h(0)^2`
   for **every** `y ∈ ℝ`. In particular, for a single node `t₁` with `h(t₁) = 0`,
   `(2 - √2) h(0) ≤ (h(0) - h(y)) + (h(0) - h(t₁ - y))` for all `y ∈ ℝ`.
3. **Origin-Singularity Leverage Theorem (`origin_singularity_leverage_sphere_bound`,
   `origin_singularity_leverage_rational_bound`, `autocorr_origin_singularity_leverage_sub`):**
   For any origin weight `W₀ > 0` and collar weights `w_i ≥ 0`, the Euclidean sphere constraint
   `h(y)^2 + ∑ i ∈ s, h(t_i ± y)^2 ≤ h(0)^2` forces
   `W₀ (h(0) - h(y)) + ∑ i ∈ s, w_i (h(0) - h(t_i ± y))`
   `≥ (W₀ + ∑ i ∈ s, w_i - √(W₀^2 + ∑ i ∈ s, w_i^2)) h(0)`
   `≥ (∑ i ∈ s, w_i - (∑ i ∈ s, w_i^2) / (2 W₀)) h(0)`.
   As `y → 0⁺`, the singular origin weight `W₀(y) = e^{y/2}/sinh y ~ 1/y → +∞` drives the defect
   `(∑ w_i^2) / (2 W₀(y))` to `0`, transferring the full collar weight `∑ w_i` into a
   derivative-free lower bound on the increment energy.
4. **Logarithmic Divisibility & Dyadic-Coset Chains (`autocorr_log_divisibility_pair_orth`,
   `autocorr_dyadic_coset_sphere_sub_le`):**
   On the logarithmic grid `Λ_N = {log n : 2 ≤ n ≤ N}`, any divisibility relation `a ∣ b` with
   `1 ≤ a < b ≤ N` satisfies `log b - log a = log (b / a) ∈ Λ_N`. In particular, every dyadic-odd
   coset `𝒞_m = {m · 2^k : 2 ≤ m · 2^k ≤ N}` forms an exact mutually orthogonal translation chain!
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace GaloisForLFunctions.BiScaleUncertainty

open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

noncomputable section

variable {f : ℝ → ℝ} {ι : Type*}

/-! ### 1. Shifted Cross-Correlation and Orthogonal-Frame Projection Identities -/

/-- Shifted cross-correlation identity:
`∫ u, f (u + x) * f (u + y) = h(y - x) = h(x - y)`. -/
theorem integral_shift_mul_shift (f : ℝ → ℝ) (x y : ℝ) :
    (∫ u, f (u + x) * f (u + y)) = autocorr f (y - x) := by
  have htrans := integral_add_right_eq_self (μ := volume)
    (fun u => f u * f (u + (y - x))) x
  have hcongr : (fun u => f (u + x) * f (u + y)) =
      fun u => f (u + x) * f (u + x + (y - x)) := by
    funext u
    rw [show u + x + (y - x) = u + y by ring]
  rw [hcongr, htrans]
  rfl

/-- Integrability of a shifted product `u ↦ f (u + x) * f (u + y)`. -/
theorem integrable_shift_mul_shift (hf : Continuous f) (hfc : HasCompactSupport f) (x y : ℝ) :
    Integrable fun u => f (u + x) * f (u + y) :=
  ((hf.comp (continuous_add_const x)).mul
    (hf.comp (continuous_add_const y))).integrable_of_hasCompactSupport
    ((hasCompactSupport_comp_add hfc x).mul_right)

/-- Given coefficients `c : ι → ℝ` and shifts `t : ι → ℝ` on `s : Finset ι`, the linear combination
`P(u) = ∑ i ∈ s, c i * f (u + t i)` is continuous and compactly supported, and its pairing against
`f(· + z)` equals `∑ i ∈ s, c i * h(t i - z)`. -/
theorem integral_shift_mul_finset_sum (hf : Continuous f) (hfc : HasCompactSupport f)
    (s : Finset ι) (c t : ι → ℝ) (z : ℝ) :
    (∫ u, f (u + z) * (∑ i ∈ s, c i * f (u + t i))) =
      ∑ i ∈ s, c i * autocorr f (t i - z) := by
  have hrew : (fun u => f (u + z) * (∑ i ∈ s, c i * f (u + t i))) =
      fun u => ∑ i ∈ s, c i * (f (u + z) * f (u + t i)) := by
    funext u
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hrew, integral_finsetSum s (fun i _ => (integrable_shift_mul_shift hf hfc z (t i)).const_mul (c i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_shift_mul_shift]

/-- For a pairwise `h`-orthogonal family of shifts `t : ι → ℝ` on `s : Finset ι`
(`h(t i - t j) = 0` for `i ≠ j`), the `L²` norm square of `P(u) = ∑ i ∈ s, c i * f (u + t i)`
equals `h(0) * ∑ i ∈ s, c i ^ 2`. -/
theorem integral_finset_sum_shift_sq_of_orthogonal [DecidableEq ι]
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (s : Finset ι) (c t : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0) :
    (∫ u, (∑ i ∈ s, c i * f (u + t i)) ^ 2) = autocorr f 0 * ∑ i ∈ s, c i ^ 2 := by
  set P : ℝ → ℝ := fun u => ∑ i ∈ s, c i * f (u + t i)
  have hPc : Continuous P :=
    continuous_finsetSum s fun i _ => continuous_const.mul (hf.comp (continuous_add_const (t i)))
  have hrew : (fun u => P u ^ 2) =
      fun u => ∑ i ∈ s, c i * (f (u + t i) * P u) := by
    funext u
    simp only [P, sq]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hint_term (i : ι) : Integrable fun u => c i * (f (u + t i) * P u) := by
    refine ((continuous_const.mul ((hf.comp (continuous_add_const (t i))).mul hPc)).integrable_of_hasCompactSupport ?_)
    exact ((hasCompactSupport_comp_add hfc (t i)).mul_right).mul_left
  rw [hrew, integral_finsetSum s (fun i _ => hint_term i)]
  have hinner (i : ι) (hi : i ∈ s) :
      (∫ u, c i * (f (u + t i) * P u)) = autocorr f 0 * c i ^ 2 := by
    rw [integral_const_mul, integral_shift_mul_finset_sum hf hfc s c t (t i)]
    have hsingle : (∑ j ∈ s, c j * autocorr f (t j - t i)) = c i * autocorr f 0 := by
      rw [Finset.sum_eq_single i]
      · rw [sub_self]
      · intro j hj hji
        rw [horth j hj i hi hji, mul_zero]
      · intro hi'
        exact absurd hi hi'
    rw [hsingle]
    ring
  rw [Finset.sum_congr rfl hinner, ← Finset.mul_sum]

/-! ### 2. The Multi-Node Orthogonal-Frame Bessel Sphere Law -/

/-- **Multi-Node Orthogonal-Frame Bessel Sphere Law:**
If `t : ι → ℝ` is pairwise orthogonal on `s : Finset ι` (`h(t i - t j) = 0` for `i ≠ j`), then for
every `y ∈ ℝ`,
`∑ i ∈ s, h(y - t i)^2 ≤ h(0)^2`. -/
theorem autocorr_finset_bessel_sq_le [DecidableEq ι]
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0) (y : ℝ) :
    (∑ i ∈ s, autocorr f (y - t i) ^ 2) ≤ autocorr f 0 ^ 2 := by
  rcases eq_or_lt_of_le (autocorr_zero_nonneg f) with h0_eq | h0_pos
  · have hzero : (∑ i ∈ s, autocorr f (y - t i) ^ 2) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [autocorr_eq_zero_of_zero_eq_zero hfc hf h0_eq.symm (y - t i), sq, zero_mul]
    rw [hzero, ← h0_eq]
    positivity
  · set c : ι → ℝ := fun i => autocorr f (y - t i)
    set P : ℝ → ℝ := fun u => ∑ i ∈ s, c i * f (u + t i)
    have hPc : Continuous P :=
      continuous_finsetSum s fun i _ => continuous_const.mul (hf.comp (continuous_add_const (t i)))
    have hfy_c : Continuous (fun u => f (u + y)) := hf.comp (continuous_add_const y)
    have hfy_cs : HasCompactSupport (fun u => f (u + y)) := hasCompactSupport_comp_add hfc y
    have hi_fyP : Integrable (fun u => f (u + y) * P u) :=
      (hfy_c.mul hPc).integrable_of_hasCompactSupport hfy_cs.mul_right
    have hi_P2 : Integrable (fun u => P u ^ 2) := by
      have hrew : (fun u => P u ^ 2) =
          fun u => ∑ i ∈ s, c i * (f (u + t i) * P u) := by
        funext u; simp only [P, sq]; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring
      rw [hrew]
      refine integrable_finsetSum s fun i _ => ?_
      exact ((continuous_const.mul ((hf.comp (continuous_add_const (t i))).mul hPc)).integrable_of_hasCompactSupport
        (((hasCompactSupport_comp_add hfc (t i)).mul_right).mul_left))
    have hnonneg : 0 ≤ ∫ u, (autocorr f 0 * f (u + y) - P u) ^ 2 :=
      integral_nonneg fun u => sq_nonneg _
    have hexp : (fun u => (autocorr f 0 * f (u + y) - P u) ^ 2) =
        fun u => (autocorr f 0 ^ 2 * f (u + y) ^ 2 - 2 * autocorr f 0 * (f (u + y) * P u)) + P u ^ 2 := by
      funext u; ring
    have e1 : (∫ u, ((autocorr f 0 ^ 2 * f (u + y) ^ 2 - 2 * autocorr f 0 * (f (u + y) * P u)) + P u ^ 2)) =
        (∫ u, (autocorr f 0 ^ 2 * f (u + y) ^ 2 - 2 * autocorr f 0 * (f (u + y) * P u))) + ∫ u, P u ^ 2 :=
      integral_add (((integrable_sq hfy_c hfy_cs).const_mul _).sub (hi_fyP.const_mul _)) hi_P2
    have e2 : (∫ u, (autocorr f 0 ^ 2 * f (u + y) ^ 2 - 2 * autocorr f 0 * (f (u + y) * P u))) =
        (∫ u, autocorr f 0 ^ 2 * f (u + y) ^ 2) - ∫ u, 2 * autocorr f 0 * (f (u + y) * P u) :=
      integral_sub ((integrable_sq hfy_c hfy_cs).const_mul _) (hi_fyP.const_mul _)
    rw [hexp, e1, e2, integral_const_mul, integral_const_mul,
      integral_add_right_eq_self (fun u => f u ^ 2) y, integral_sq_eq_autocorr_zero,
      integral_shift_mul_finset_sum hf hfc s c t y,
      integral_finset_sum_shift_sq_of_orthogonal hf hfc s c t horth] at hnonneg
    have hsum_eq : (∑ i ∈ s, c i * autocorr f (t i - y)) = ∑ i ∈ s, c i ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show t i - y = -(y - t i) by ring, autocorr_neg]
      simp only [c, sq]
    rw [hsum_eq] at hnonneg
    have hprod : 0 ≤ autocorr f 0 * (autocorr f 0 ^ 2 - ∑ i ∈ s, c i ^ 2) := by linarith
    have hpos_iff := nonneg_of_mul_nonneg_right hprod h0_pos
    linarith

/-! ### 3. Origin-Anchored Euclidean Sphere Laws (Left & Right Collars) -/

/-- **Origin-Anchored Left-Collar Euclidean Sphere Law:**
If `t : ι → ℝ` is a family of zero nodes on `s : Finset ι` (`h(t i) = 0`) that are pairwise
difference-orthogonal (`h(t i - t j) = 0` for `i ≠ j`), then adjoining the origin node `0` yields,
for **every** `y ∈ ℝ`:
`h(y)^2 + ∑ i ∈ s, h(t i - y)^2 ≤ h(0)^2`. -/
theorem autocorr_origin_chain_sphere_sub_le [DecidableEq ι]
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (hzero : ∀ i ∈ s, autocorr f (t i) = 0)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0) (y : ℝ) :
    autocorr f y ^ 2 + (∑ i ∈ s, autocorr f (t i - y) ^ 2) ≤ autocorr f 0 ^ 2 := by
  set s' : Finset (Option ι) := insert none (s.map ⟨some, Option.some_injective ι⟩)
  set t' : Option ι → ℝ := fun o => Option.elim o 0 t
  have horth' : ∀ a ∈ s', ∀ b ∈ s', a ≠ b → autocorr f (t' a - t' b) = 0 := by
    intro a ha b hb hab
    rcases a with _ | i <;> rcases b with _ | j
    · exact absurd rfl hab
    · simp only [s', Finset.mem_insert, reduceCtorEq, Finset.mem_map,
        Function.Embedding.coeFn_mk, Option.some.injEq, exists_eq_right, false_or] at hb
      simp only [t', Option.elim_none, Option.elim_some, zero_sub, autocorr_neg]
      exact hzero j hb
    · simp only [s', Finset.mem_insert, reduceCtorEq, Finset.mem_map,
        Function.Embedding.coeFn_mk, Option.some.injEq, exists_eq_right, false_or] at ha
      simp only [t', Option.elim_some, Option.elim_none, sub_zero]
      exact hzero i ha
    · simp only [s', Finset.mem_insert, reduceCtorEq, Finset.mem_map,
        Function.Embedding.coeFn_mk, Option.some.injEq, exists_eq_right, false_or] at ha hb
      have hij : i ≠ j := fun h => hab (congrArg some h)
      exact horth i ha j hb hij
  have hbessel := autocorr_finset_bessel_sq_le hfc hf s' t' horth' y
  have hmem : none ∉ s.map ⟨some, Option.some_injective ι⟩ := by
    simp
  rw [Finset.sum_insert hmem, Finset.sum_map] at hbessel
  simp only [t', Option.elim_none, sub_zero, Function.Embedding.coeFn_mk, Option.elim_some] at hbessel
  have hcongr : (∑ x ∈ s, autocorr f (y - t x) ^ 2) = ∑ i ∈ s, autocorr f (t i - y) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show y - t i = -(t i - y) by ring, autocorr_neg]
  rwa [hcongr] at hbessel

/-- **Origin-Anchored Right-Collar Euclidean Sphere Law:**
Under the same hypotheses (`h(t i) = 0` and `h(t i - t j) = 0` for `i ≠ j`), for **every** `y ∈ ℝ`:
`h(y)^2 + ∑ i ∈ s, h(t i + y)^2 ≤ h(0)^2`. -/
theorem autocorr_origin_chain_sphere_add_le [DecidableEq ι]
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (hzero : ∀ i ∈ s, autocorr f (t i) = 0)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0) (y : ℝ) :
    autocorr f y ^ 2 + (∑ i ∈ s, autocorr f (t i + y) ^ 2) ≤ autocorr f 0 ^ 2 := by
  have h := autocorr_origin_chain_sphere_sub_le hfc hf s t hzero horth (-y)
  rw [autocorr_neg] at h
  have hcongr : (∑ i ∈ s, autocorr f (t i - -y) ^ 2) = ∑ i ∈ s, autocorr f (t i + y) ^ 2 := by
    refine Finset.sum_congr rfl fun i _ => by rw [sub_neg_eq_add]
  rwa [hcongr] at h

/-- **Single-Node Reflected-Collar Sphere Law:**
At any zero node `t₁ ∈ ℝ` where `h(t₁) = 0`, for every `y ∈ ℝ`,
`h(y)^2 + h(t₁ - y)^2 ≤ h(0)^2`. -/
theorem autocorr_reflected_collar_sphere_le (hfc : HasCompactSupport f) (hf : Continuous f)
    {t₁ : ℝ} (ht₁ : autocorr f t₁ = 0) (y : ℝ) :
    autocorr f y ^ 2 + autocorr f (t₁ - y) ^ 2 ≤ autocorr f 0 ^ 2 := by
  have h := autocorr_origin_chain_sphere_sub_le hfc hf ({0} : Finset ℕ) (fun _ => t₁)
    (fun _ _ => ht₁) (fun _ hi _ hj hij => by
      rw [Finset.mem_singleton] at hi hj
      exact absurd (hi.trans hj.symm) hij) y
  simpa using h

/-- **Reflected-Collar Defect Law:**
At any zero node `t₁ ∈ ℝ` where `h(t₁) = 0`, for every `y ∈ ℝ`,
`(2 - √2) * h(0) ≤ (h(0) - h(y)) + (h(0) - h(t₁ - y))`. -/
theorem autocorr_reflected_collar_sum_sub_ge (hfc : HasCompactSupport f) (hf : Continuous f)
    {t₁ : ℝ} (ht₁ : autocorr f t₁ = 0) (y : ℝ) :
    (2 - Real.sqrt 2) * autocorr f 0 ≤
      (autocorr f 0 - autocorr f y) + (autocorr f 0 - autocorr f (t₁ - y)) := by
  have hsph := autocorr_reflected_collar_sphere_le hfc hf ht₁ y
  have hcs : (autocorr f y + autocorr f (t₁ - y)) ^ 2 ≤
      2 * (autocorr f y ^ 2 + autocorr f (t₁ - y) ^ 2) := by
    have : 0 ≤ (autocorr f y - autocorr f (t₁ - y)) ^ 2 := sq_nonneg _
    linarith
  have hle : (autocorr f y + autocorr f (t₁ - y)) ^ 2 ≤ (Real.sqrt 2 * autocorr f 0) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt zero_le_two]
    linarith
  have hsqrt := Real.sqrt_le_sqrt hle
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg 2) (autocorr_zero_nonneg f))] at hsqrt
  have hsum : autocorr f y + autocorr f (t₁ - y) ≤ Real.sqrt 2 * autocorr f 0 :=
    (le_abs_self _).trans hsqrt
  linarith

/-! ### 4. The Origin-Singularity Leverage Theorem -/

/-- Cauchy–Schwarz on an `(s.card + 1)`-dimensional Euclidean sphere:
If `u₀^2 + ∑ i ∈ s, u i^2 ≤ R^2` with `R ≥ 0`, then for any weights `W₀ : ℝ` and `w : ι → ℝ`,
`W₀ * u₀ + ∑ i ∈ s, w i * u i ≤ √(W₀^2 + ∑ i ∈ s, w i^2) * R`. -/
theorem sphere_weighted_sum_le_sqrt_mul (s : Finset ι) (W₀ : ℝ) (w u : ι → ℝ) (u₀ R : ℝ)
    (hR : 0 ≤ R) (hsph : u₀ ^ 2 + (∑ i ∈ s, u i ^ 2) ≤ R ^ 2) :
    W₀ * u₀ + (∑ i ∈ s, w i * u i) ≤
      Real.sqrt (W₀ ^ 2 + ∑ i ∈ s, w i ^ 2) * R := by
  set A := W₀ ^ 2 + ∑ i ∈ s, w i ^ 2
  set B := u₀ ^ 2 + ∑ i ∈ s, u i ^ 2
  set C := W₀ * u₀ + ∑ i ∈ s, w i * u i
  have hA0 : 0 ≤ A := add_nonneg (sq_nonneg W₀) (Finset.sum_nonneg fun i _ => sq_nonneg (w i))
  have hdisc : 0 ≤ A * (A * B - C ^ 2) := by
    have hnonneg : 0 ≤ (A * u₀ - C * W₀) ^ 2 + ∑ i ∈ s, (A * u i - C * w i) ^ 2 :=
      add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hexp : (A * u₀ - C * W₀) ^ 2 + (∑ i ∈ s, (A * u i - C * w i) ^ 2) =
        A ^ 2 * B - 2 * A * C * C + C ^ 2 * A := by
      have hsum : (∑ i ∈ s, (A * u i - C * w i) ^ 2) =
          A ^ 2 * (∑ i ∈ s, u i ^ 2) - 2 * A * C * (∑ i ∈ s, w i * u i) +
            C ^ 2 * (∑ i ∈ s, w i ^ 2) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => by ring
      rw [hsum]
      simp only [A, B, C]
      ring
    linarith
  have hC2 : C ^ 2 ≤ A * R ^ 2 := by
    rcases eq_or_lt_of_le hA0 with hA_eq | hA_pos
    · have hW0 : W₀ = 0 := by
        have h1 : W₀ ^ 2 ≤ A := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => sq_nonneg _)
        nlinarith
      have hw0 : ∀ i ∈ s, w i = 0 := fun i hi => by
        have h1 : w i ^ 2 ≤ ∑ j ∈ s, w j ^ 2 :=
          Finset.single_le_sum (fun j _ => sq_nonneg (w j)) hi
        have h2 : (∑ j ∈ s, w j ^ 2) ≤ A := le_add_of_nonneg_left (sq_nonneg W₀)
        nlinarith
      have hC0 : C = 0 := by
        simp only [C, hW0, zero_mul, zero_add]
        refine Finset.sum_eq_zero fun i hi => by rw [hw0 i hi, zero_mul]
      rw [hC0, ← hA_eq]
      ring_nf
      exact le_rfl
    · have hAB : C ^ 2 ≤ A * B := by
        have := nonneg_of_mul_nonneg_right hdisc hA_pos
        linarith
      exact hAB.trans (mul_le_mul_of_nonneg_left hsph hA0)
  have hsqrt := Real.sqrt_le_sqrt hC2
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_mul hA0, Real.sqrt_sq hR] at hsqrt
  exact (le_abs_self C).trans hsqrt

/-- **The Origin-Singularity Leverage Theorem (Exact Sphere Form):**
For any origin weight `W₀ : ℝ`, collar weights `w : ι → ℝ`, radius `R ≥ 0`, and tuple `(u₀, u)`
satisfying `u₀^2 + ∑ i ∈ s, u i^2 ≤ R^2`,
`W₀ * (R - u₀) + ∑ i ∈ s, w i * (R - u i) ≥ (W₀ + ∑ i ∈ s, w i - √(W₀^2 + ∑ i ∈ s, w i^2)) * R`. -/
theorem origin_singularity_leverage_sphere_bound (s : Finset ι) (W₀ : ℝ) (w u : ι → ℝ) (u₀ R : ℝ)
    (hR : 0 ≤ R) (hsph : u₀ ^ 2 + (∑ i ∈ s, u i ^ 2) ≤ R ^ 2) :
    (W₀ + (∑ i ∈ s, w i) - Real.sqrt (W₀ ^ 2 + ∑ i ∈ s, w i ^ 2)) * R ≤
      W₀ * (R - u₀) + ∑ i ∈ s, w i * (R - u i) := by
  have hcs := sphere_weighted_sum_le_sqrt_mul s W₀ w u u₀ R hR hsph
  have hrew : W₀ * (R - u₀) + (∑ i ∈ s, w i * (R - u i)) =
      (W₀ + ∑ i ∈ s, w i) * R - (W₀ * u₀ + ∑ i ∈ s, w i * u i) := by
    have hsum : (∑ i ∈ s, w i * (R - u i)) =
        (∑ i ∈ s, w i) * R - ∑ i ∈ s, w i * u i := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hsum]
    ring
  linarith

/-- **The Origin-Singularity Leverage Theorem (Rationalized Anchor Form):**
When `W₀ > 0`, using `√(W₀^2 + S₂) ≤ W₀ + S₂ / (2 W₀)` shows that the large origin weight `W₀`
cancels out of the leading term and sits in the denominator of the collar defect:
`(∑ i ∈ s, w i - (∑ i ∈ s, w i^2) / (2 * W₀)) * R ≤ W₀ * (R - u₀) + ∑ i ∈ s, w i * (R - u i)`. -/
theorem origin_singularity_leverage_rational_bound (s : Finset ι) {W₀ : ℝ} (hW₀ : 0 < W₀)
    (w u : ι → ℝ) (u₀ R : ℝ) (hR : 0 ≤ R) (hsph : u₀ ^ 2 + (∑ i ∈ s, u i ^ 2) ≤ R ^ 2) :
    ((∑ i ∈ s, w i) - (∑ i ∈ s, w i ^ 2) / (2 * W₀)) * R ≤
      W₀ * (R - u₀) + ∑ i ∈ s, w i * (R - u i) := by
  set S₂ := ∑ i ∈ s, w i ^ 2
  have hS₂ : 0 ≤ S₂ := Finset.sum_nonneg fun i _ => sq_nonneg (w i)
  have hsqrt_le : Real.sqrt (W₀ ^ 2 + S₂) ≤ W₀ + S₂ / (2 * W₀) := by
    have hpos : 0 ≤ W₀ + S₂ / (2 * W₀) := by positivity
    rw [← Real.sqrt_sq hpos]
    apply Real.sqrt_le_sqrt
    have hsq : (W₀ + S₂ / (2 * W₀)) ^ 2 = W₀ ^ 2 + S₂ + (S₂ / (2 * W₀)) ^ 2 := by
      field_simp
      ring
    linarith [sq_nonneg (S₂ / (2 * W₀))]
  have h1 : ((∑ i ∈ s, w i) - S₂ / (2 * W₀)) * R ≤
      (W₀ + (∑ i ∈ s, w i) - Real.sqrt (W₀ ^ 2 + S₂)) * R :=
    mul_le_mul_of_nonneg_right (by linarith) hR
  exact h1.trans (origin_singularity_leverage_sphere_bound s W₀ w u u₀ R hR hsph)

/-- **Autocorrelation Origin-Singularity Leverage Inequality (Left Collars):**
For any difference-orthogonal zero chain `t : ι → ℝ` on `s : Finset ι`, any origin weight `W₀ > 0`,
any collar weights `w : ι → ℝ`, and any `y ∈ ℝ`,
`((∑ i ∈ s, w i) - (∑ i ∈ s, w i^2) / (2 * W₀)) * h(0)`
`≤ W₀ * (h(0) - h(y)) + ∑ i ∈ s, w i * (h(0) - h(t i - y))`. -/
theorem autocorr_origin_singularity_leverage_sub [DecidableEq ι]
    (hfc : HasCompactSupport f) (hf : Continuous f)
    (s : Finset ι) (t : ι → ℝ)
    (hzero : ∀ i ∈ s, autocorr f (t i) = 0)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → autocorr f (t i - t j) = 0)
    {W₀ : ℝ} (hW₀ : 0 < W₀) (w : ι → ℝ) (y : ℝ) :
    ((∑ i ∈ s, w i) - (∑ i ∈ s, w i ^ 2) / (2 * W₀)) * autocorr f 0 ≤
      W₀ * (autocorr f 0 - autocorr f y) +
        ∑ i ∈ s, w i * (autocorr f 0 - autocorr f (t i - y)) :=
  origin_singularity_leverage_rational_bound s hW₀ w
    (fun i => autocorr f (t i - y)) (autocorr f y) (autocorr f 0)
    (autocorr_zero_nonneg f)
    (autocorr_origin_chain_sphere_sub_le hfc hf s t hzero horth y)

/-! ### 5. Logarithmic Divisibility Chains & Dyadic-Coset Orthogonality on `Λ_N` -/

/-- If `1 ≤ a`, `a < b`, `b ≤ N`, and `a ∣ b`, then `b / a ∈ Finset.Icc 2 N` and
`log b - log a = log (b / a)`. -/
theorem log_sub_log_mem_Icc_of_dvd {a b N : ℕ} (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ N)
    (hdvd : a ∣ b) :
    b / a ∈ Finset.Icc 2 N ∧
      Real.log (b : ℝ) - Real.log (a : ℝ) = Real.log ((b / a : ℕ) : ℝ) := by
  obtain ⟨k, rfl⟩ := hdvd
  have ha_pos : 0 < a := ha
  have hk_gt1 : 1 < k := by
    by_contra hle
    have : a * k ≤ a * 1 := Nat.mul_le_mul_left a (by omega)
    omega
  have hk_div : a * k / a = k := Nat.mul_div_right k ha_pos
  rw [hk_div]
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
  · have : 1 * k ≤ a * k := Nat.mul_le_mul_right k ha
    omega
  · have haR : (0 : ℝ) < (a : ℝ) := Nat.cast_pos.mpr ha_pos
    have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr (by omega)
    rw [Nat.cast_mul, Real.log_mul haR.ne' hkR.ne']
    ring

/-- **Logarithmic Divisibility Pair Orthogonality:**
If `h(log n) = 0` for all `n ∈ [2, N]`, then any two distinct positive integers `a, b ≤ N` where
one divides the other satisfy `h(log a - log b) = 0`. -/
theorem autocorr_log_divisibility_pair_orth
    {N : ℕ} (hgrid : ∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0)
    {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (haN : a ≤ N) (hbN : b ≤ N)
    (hdvd : (a < b ∧ a ∣ b) ∨ (b < a ∧ b ∣ a)) :
    autocorr f (Real.log (a : ℝ) - Real.log (b : ℝ)) = 0 := by
  rcases hdvd with ⟨hab, hd⟩ | ⟨hba, hd⟩
  · obtain ⟨hmem, hlog⟩ := log_sub_log_mem_Icc_of_dvd ha hab hbN hd
    rw [show Real.log (a : ℝ) - Real.log (b : ℝ) = -(Real.log (b : ℝ) - Real.log (a : ℝ)) by ring,
      autocorr_neg, hlog]
    exact hgrid (b / a) hmem
  · obtain ⟨hmem, hlog⟩ := log_sub_log_mem_Icc_of_dvd hb hba haN hd
    rw [hlog]
    exact hgrid (a / b) hmem

/-- **Dyadic-Coset Chain Orthogonality & Euclidean Sphere Law on `Λ_N`:**
For any positive integer `m ≥ 1` and any finite set `s : Finset ℕ` of exponents `k` such that
`2 ≤ m * 2^k ≤ N` for all `k ∈ s`, if `h(log n) = 0` for all `n ∈ [2, N]`, then the dyadic-coset
logarithmic nodes `t k = log (m * 2^k)` satisfy the Euclidean Sphere Law
`h(y)^2 + ∑ k ∈ s, h(log(m * 2^k) - y)^2 ≤ h(0)^2` for every `y ∈ ℝ`. -/
theorem autocorr_dyadic_coset_sphere_sub_le (hfc : HasCompactSupport f) (hf : Continuous f)
    {N m : ℕ} (hm : 1 ≤ m)
    (hgrid : ∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0)
    (s : Finset ℕ) (hs : ∀ k ∈ s, 2 ≤ m * 2 ^ k ∧ m * 2 ^ k ≤ N) (y : ℝ) :
    autocorr f y ^ 2 +
      (∑ k ∈ s, autocorr f (Real.log ((m * 2 ^ k : ℕ) : ℝ) - y) ^ 2) ≤
      autocorr f 0 ^ 2 := by
  refine autocorr_origin_chain_sphere_sub_le hfc hf s
    (fun k => Real.log ((m * 2 ^ k : ℕ) : ℝ)) ?_ ?_ y
  · intro k hk
    exact hgrid (m * 2 ^ k) (Finset.mem_Icc.mpr (hs k hk))
  · intro i hi j hj hij
    have hi_b := hs i hi
    have hj_b := hs j hj
    apply autocorr_log_divisibility_pair_orth hgrid (by omega) (by omega) hi_b.2 hj_b.2
    rcases lt_or_gt_of_ne hij with hij_lt | hij_gt
    · left
      refine ⟨Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num) hij_lt) hm, ?_⟩
      exact ⟨2 ^ (j - i), by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hij_lt.le]⟩
    · right
      refine ⟨Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num) hij_gt) hm, ?_⟩
      exact ⟨2 ^ (i - j), by rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hij_gt.le]⟩

end

end GaloisForLFunctions.BiScaleUncertainty
