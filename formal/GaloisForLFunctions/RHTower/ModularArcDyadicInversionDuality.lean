import GaloisForLFunctions.RHTower.ModularArcDyadicHyperbolicTower

/-!
# Universal integer-scale dilation duality, scale-invariant `O(√c)` invariance, and the self-reciprocal dyadic modular arc tower

In `ModularArcUniversalSqrtMomentBound` and `ModularArcDyadicHyperbolicTower`, we showed that the
hyperbolic filter `hyperbolicFilterDeriv m` preserves the universal square-root frequency bound
`|∫ f'(t) sin(ω t) dt| ≤ K √ω` with constant `2 K` independent of `m`, and constructed the dyadic
(exponent-doubling) hyperbolic tower `arcLineDyadicTowerVector k r ν` (`r ∈ ℕ`), which is blind on
the doubly-exponential `k^{2^{r+1}}`-sublattice while satisfying the `k`-independent frequency bound
`2^r · (8 √(π/2) · ν.real univ) · √c`.

In this module we introduce the **universal unitary integer-scale dilation pair and self-reciprocal
symmetrizer** `(forwardScaleVec M, backwardScaleVec M, symScaleVec M)` for any integer `M ≥ 1` and
apply it at scale `M = k^{2^r}` (`M² = k^{2^{r+1}}`, `M⁴ = k^{2^{r+2}}`) to the dyadic tower:

## Main results

1. **Universal Mellin-inversion duality and exact decomposition of `hyperbolicFilter`
   (`forwardScaleVec_inv_eq_backward`, `symScaleVec_inv`, `hyperbolicFilterVec_eq_sub_symScaleVec`):**
   For any self-reciprocal `f`, `forwardScaleVec M f` and `backwardScaleVec M f` are exact
   Mellin-inversion duals, `symScaleVec M f` is strictly self-reciprocal (`S(1/x) = |x| S(x)`),
   and `hyperbolicFilterVec M f x = f x − (1 / cosh(log M)) · symScaleVec M f x`.
2. **Exact invariance of the `O(√c)` frequency norm under unitary dilations
   (`abs_integral_forwardScaleDeriv_mul_sin_le_sqrt`,
   `abs_integral_backwardScaleDeriv_mul_sin_le_sqrt`,
   `abs_integral_symScaleDeriv_mul_sin_le_sqrt`):**
   If `|∫ f'(t) sin(ω t) dt| ≤ K √ω` for all `ω > 0`, then for **every** integer `M ≥ 1` and
   every `c > 0`, both `forwardScaleDeriv M f'` and `backwardScaleDeriv M f'` satisfy the **exact
   same** bound `K √c` with zero loss and complete independence of `M` (since `M⁻¹ √(c M²) = √c`
   and `M √(c / M²) = √c`).
3. **Universal all-integer blindness, Forward-Backward Spectral Isolation, and `M⁴`-sublattice
   blindness (`integral_forwardScaleDeriv_mul_sin_eq_zero`,
   `integral_symScaleDeriv_mul_sin_eq_half_backward`,
   `abs_integral_symScaleDeriv_mul_sin_arcFreq_le`,
   `integral_symScaleDeriv_mul_sin_pow_four_eq_zero`):**
   If `f'` is blind on the `M²`-sublattice, then at every positive integer frequency `arcFreq n`:
   - `forwardScaleDeriv M f'` vanishes identically;
   - `symScaleDeriv M f'` isolates `½` of `backwardScaleDeriv M f'`, satisfying the `M`-independent
     bound `(K / 2) √(arcFreq n)` at all `n ∈ ℕ`;
   - Both `backwardScaleDeriv M f'` and `symScaleDeriv M f'` vanish identically on the
     `M⁴`-sublattice `arcFreq (M⁴(j+1) − 1)`.
4. **The Forward, Backward, and Symmetrized Dyadic Towers (`arcLineForwardDyadicTowerVector k r ν`,
   `arcLineBackwardDyadicTowerVector k r ν`, `arcLineSymDyadicTowerVector k r ν`):**
   Instantiating `M = k^{2^r}` gives all-integer blindness at arbitrary dyadic order `r + 1`,
   exact forward-backward isolation with `k`-independent bound
   `2^r · (4 √(π/2) · ν.real univ) · √(arcFreq n)` at all positive integers, doubly-exponential
   `k^{2^{r+2}}`-sublattice blindness, and `O((1/2 − l)^{r+1})` strip-edge vanishing
   (`exists_dyadic_inversionDual_isolation_arcWitness`).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry RHTower.BesselKZero

namespace RHTower

noncomputable section

/-! ### Universal unitary integer-scale dilation pair and self-reciprocal symmetrizer -/

/-- Forward unitary dilation by `M²` on line vectors: `(F_M f)(x) = M⁻¹ f(x / M²)`. -/
def forwardScaleVec (M : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (M : ℝ)⁻¹ * f (x * ((M : ℝ) ^ 2)⁻¹)

/-- Forward unitary dilation by `M²` on line derivatives: `(F_M' f')(x) = M⁻³ f'(x / M²)`. -/
def forwardScaleDeriv (M : ℕ) (f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  (((M : ℝ) ^ 3)⁻¹) * f' (x * ((M : ℝ) ^ 2)⁻¹)

/-- Forward shift by `2 log M` on log-scale profiles: `(F_M^{prof} P)(v) = P(v − 2 log M)`. -/
def forwardScaleProfile (M : ℕ) (P : ℝ → ℝ) (v : ℝ) : ℝ :=
  P (v - 2 * Real.log M)

/-- Backward unitary dilation by `M²` on line vectors: `(B_M f)(x) = M f(M² x)`. -/
def backwardScaleVec (M : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (M : ℝ) * f ((M : ℝ) ^ 2 * x)

/-- Backward unitary dilation by `M²` on line derivatives: `(B_M' f')(x) = M³ f'(M² x)`. -/
def backwardScaleDeriv (M : ℕ) (f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  (M : ℝ) ^ 3 * f' ((M : ℝ) ^ 2 * x)

/-- Backward shift by `2 log M` on log-scale profiles: `(B_M^{prof} P)(v) = P(v + 2 log M)`. -/
def backwardScaleProfile (M : ℕ) (P : ℝ → ℝ) (v : ℝ) : ℝ :=
  P (v + 2 * Real.log M)

/-- Self-reciprocal symmetrization at integer scale `M`: `S_M f = ½ (F_M f + B_M f)`. -/
def symScaleVec (M : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (forwardScaleVec M f x + backwardScaleVec M f x)

/-- Derivative of the self-reciprocal symmetrization: `S_M' f' = ½ (F_M' f' + B_M' f')`. -/
def symScaleDeriv (M : ℕ) (f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (forwardScaleDeriv M f' x + backwardScaleDeriv M f' x)

/-- Log-scale profile of the self-reciprocal symmetrization:
`S_M^{prof} P(v) = ½ (P(v − 2 log M) + P(v + 2 log M))`. -/
def symScaleProfile (M : ℕ) (P : ℝ → ℝ) (v : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (forwardScaleProfile M P v + backwardScaleProfile M P v)

/-- **Exact bridge between `hyperbolicFilterVec` and `symScaleVec`:**
`hyperbolicFilterVec M f x = f x − (1 / cosh(log M)) · symScaleVec M f x`. -/
theorem hyperbolicFilterVec_eq_sub_symScaleVec (M : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    hyperbolicFilterVec M f x =
      f x - (1 / Real.cosh (Real.log M)) * symScaleVec M f x := by
  unfold hyperbolicFilterVec symScaleVec forwardScaleVec backwardScaleVec
  ring

theorem hyperbolicFilterDeriv_eq_sub_symScaleDeriv (M : ℕ) (f' : ℝ → ℝ) (x : ℝ) :
    hyperbolicFilterDeriv M f' x =
      f' x - (1 / Real.cosh (Real.log M)) * symScaleDeriv M f' x := by
  unfold hyperbolicFilterDeriv symScaleDeriv forwardScaleDeriv backwardScaleDeriv
  ring

theorem hyperbolicFilterProfile_eq_sub_symScaleProfile (M : ℕ) (P : ℝ → ℝ) (v : ℝ) :
    hyperbolicFilterProfile M P v =
      P v - (1 / Real.cosh (Real.log M)) * symScaleProfile M P v := by
  unfold hyperbolicFilterProfile symScaleProfile forwardScaleProfile backwardScaleProfile
  ring

/-! ### Universal calculus, parity, Mellin inversion duality, and integrability -/

theorem hasDerivAt_forwardScaleVec (M : ℕ) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (forwardScaleVec M f) (forwardScaleDeriv M f' x) x := by
  have hc : HasDerivAt (fun x' : ℝ => x' * ((M : ℝ) ^ 2)⁻¹) (((M : ℝ) ^ 2)⁻¹) x := by
    simpa using (hasDerivAt_id x).mul_const (((M : ℝ) ^ 2)⁻¹)
  have h := ((hf (x * ((M : ℝ) ^ 2)⁻¹)).comp x hc).const_mul ((M : ℝ)⁻¹)
  refine h.congr_deriv ?_
  unfold forwardScaleDeriv
  ring

theorem hasDerivAt_backwardScaleVec (M : ℕ) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (backwardScaleVec M f) (backwardScaleDeriv M f' x) x := by
  have hc : HasDerivAt (fun x' : ℝ => (M : ℝ) ^ 2 * x') ((M : ℝ) ^ 2) x := by
    simpa using (hasDerivAt_id x).const_mul ((M : ℝ) ^ 2)
  have h := ((hf ((M : ℝ) ^ 2 * x)).comp x hc).const_mul (M : ℝ)
  refine h.congr_deriv ?_
  unfold backwardScaleDeriv
  ring

theorem hasDerivAt_symScaleVec (M : ℕ) {f f' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (symScaleVec M f) (symScaleDeriv M f' x) x :=
  ((hasDerivAt_forwardScaleVec M hf x).add
    (hasDerivAt_backwardScaleVec M hf x)).const_mul (1 / 2 : ℝ)

theorem forwardScaleVec_neg (M : ℕ) {f : ℝ → ℝ} (heven : ∀ x, f (-x) = f x) (x : ℝ) :
    forwardScaleVec M f (-x) = forwardScaleVec M f x := by
  unfold forwardScaleVec; rw [neg_mul, heven]

theorem backwardScaleVec_neg (M : ℕ) {f : ℝ → ℝ} (heven : ∀ x, f (-x) = f x) (x : ℝ) :
    backwardScaleVec M f (-x) = backwardScaleVec M f x := by
  unfold backwardScaleVec; rw [mul_neg, heven]

theorem symScaleVec_neg (M : ℕ) {f : ℝ → ℝ} (heven : ∀ x, f (-x) = f x) (x : ℝ) :
    symScaleVec M f (-x) = symScaleVec M f x := by
  unfold symScaleVec
  rw [forwardScaleVec_neg M heven, backwardScaleVec_neg M heven]

/-- **Universal forward-to-backward Mellin inversion duality:**
If `f(1/x) = |x| f(x)`, then `forwardScaleVec M f (1/x) = |x| · backwardScaleVec M f x`. -/
theorem forwardScaleVec_inv_eq_backward {M : ℕ} (hM : 1 ≤ M) {f : ℝ → ℝ}
    (hinv : ∀ x, x ≠ 0 → f (1 / x) = |x| * f x) {x : ℝ} (hx : x ≠ 0) :
    forwardScaleVec M f (1 / x) = |x| * backwardScaleVec M f x := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have hy : (M : ℝ) ^ 2 * x ≠ 0 := mul_ne_zero (pow_ne_zero 2 hMne) hx
  have e : 1 / x * ((M : ℝ) ^ 2)⁻¹ = 1 / ((M : ℝ) ^ 2 * x) := by field_simp
  unfold forwardScaleVec backwardScaleVec
  rw [e, hinv _ hy, abs_mul, abs_of_pos (pow_pos hMpos 2)]
  field_simp

/-- **Universal backward-to-forward Mellin inversion duality:**
If `f(1/x) = |x| f(x)`, then `backwardScaleVec M f (1/x) = |x| · forwardScaleVec M f x`. -/
theorem backwardScaleVec_inv_eq_forward {M : ℕ} (hM : 1 ≤ M) {f : ℝ → ℝ}
    (hinv : ∀ x, x ≠ 0 → f (1 / x) = |x| * f x) {x : ℝ} (hx : x ≠ 0) :
    backwardScaleVec M f (1 / x) = |x| * forwardScaleVec M f x := by
  have h := forwardScaleVec_inv_eq_backward hM hinv (one_div_ne_zero hx)
  rw [one_div_one_div, abs_one_div] at h
  have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
  calc backwardScaleVec M f (1 / x)
      = |x| * (|x|⁻¹ * backwardScaleVec M f (1 / x)) := by
        rw [← mul_assoc, mul_inv_cancel₀ habs, one_mul]
    _ = |x| * forwardScaleVec M f x := by
        rw [← one_div, ← h]

/-- **Universal `x ↦ 1/x` self-reciprocity of `symScaleVec M f`.** -/
theorem symScaleVec_inv {M : ℕ} (hM : 1 ≤ M) {f : ℝ → ℝ}
    (hinv : ∀ x, x ≠ 0 → f (1 / x) = |x| * f x) {x : ℝ} (hx : x ≠ 0) :
    symScaleVec M f (1 / x) = |x| * symScaleVec M f x := by
  unfold symScaleVec
  rw [forwardScaleVec_inv_eq_backward hM hinv hx,
    backwardScaleVec_inv_eq_forward hM hinv hx]
  ring

theorem exp_half_mul_forwardScaleVec {M : ℕ} (hM : 1 ≤ M) {f P : ℝ → ℝ}
    (hprof : ∀ v, Real.exp (v / 2) * f (Real.exp v) = P v) (v : ℝ) :
    Real.exp (v / 2) * forwardScaleVec M f (Real.exp v) =
      forwardScaleProfile M P v := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have he2_inv : ((M : ℝ) ^ 2)⁻¹ = Real.exp (-(2 * Real.log M)) := by
    rw [Real.exp_neg, show (2 : ℝ) * Real.log M = ((2 : ℕ) : ℝ) * Real.log M by norm_num,
      Real.exp_nat_mul, Real.exp_log hMpos]
  have e1 : Real.exp v * ((M : ℝ) ^ 2)⁻¹ = Real.exp (v - 2 * Real.log M) := by
    rw [he2_inv, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (v / 2) * (M : ℝ)⁻¹ = Real.exp ((v - 2 * Real.log M) / 2) := by
    rw [show (v - 2 * Real.log M) / 2 = v / 2 - Real.log M by ring,
      sub_eq_add_neg, Real.exp_add, Real.exp_neg, Real.exp_log hMpos]
  unfold forwardScaleVec forwardScaleProfile
  rw [← mul_assoc, e2, e1, hprof]

theorem exp_half_mul_backwardScaleVec {M : ℕ} (hM : 1 ≤ M) {f P : ℝ → ℝ}
    (hprof : ∀ v, Real.exp (v / 2) * f (Real.exp v) = P v) (v : ℝ) :
    Real.exp (v / 2) * backwardScaleVec M f (Real.exp v) =
      backwardScaleProfile M P v := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have he2 : (M : ℝ) ^ 2 = Real.exp (2 * Real.log M) := by
    rw [show (2 : ℝ) * Real.log M = ((2 : ℕ) : ℝ) * Real.log M by norm_num,
      Real.exp_nat_mul, Real.exp_log hMpos]
  have e1 : (M : ℝ) ^ 2 * Real.exp v = Real.exp (v + 2 * Real.log M) := by
    rw [he2, ← Real.exp_add]; ring_nf
  have e2 : Real.exp (v / 2) * (M : ℝ) = Real.exp ((v + 2 * Real.log M) / 2) := by
    rw [show (v + 2 * Real.log M) / 2 = v / 2 + Real.log M by ring,
      Real.exp_add, Real.exp_log hMpos]
  unfold backwardScaleVec backwardScaleProfile
  rw [← mul_assoc, e2, e1, hprof]

theorem exp_half_mul_symScaleVec {M : ℕ} (hM : 1 ≤ M) {f P : ℝ → ℝ}
    (hprof : ∀ v, Real.exp (v / 2) * f (Real.exp v) = P v) (v : ℝ) :
    Real.exp (v / 2) * symScaleVec M f (Real.exp v) =
      symScaleProfile M P v := by
  unfold symScaleVec symScaleProfile
  rw [← mul_left_comm, mul_add, exp_half_mul_forwardScaleVec hM hprof,
    exp_half_mul_backwardScaleVec hM hprof]

theorem integrable_forwardScaleVec {M : ℕ} (hM : 1 ≤ M) {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (forwardScaleVec M f) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  exact (hf.comp_mul_right' (inv_ne_zero (pow_ne_zero 2 hMpos.ne'))).const_mul ((M : ℝ)⁻¹)

theorem integrable_backwardScaleVec {M : ℕ} (hM : 1 ≤ M) {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (backwardScaleVec M f) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  exact (hf.comp_mul_left' (pow_ne_zero 2 hMpos.ne')).const_mul (M : ℝ)

theorem integrable_symScaleVec {M : ℕ} (hM : 1 ≤ M) {f : ℝ → ℝ} (hf : Integrable f) :
    Integrable (symScaleVec M f) :=
  ((integrable_forwardScaleVec hM hf).add (integrable_backwardScaleVec hM hf)).const_mul _

theorem integrable_forwardScaleDeriv {M : ℕ} (hM : 1 ≤ M) {f' : ℝ → ℝ} (hf' : Integrable f') :
    Integrable (forwardScaleDeriv M f') := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  exact (hf'.comp_mul_right' (inv_ne_zero (pow_ne_zero 2 hMpos.ne'))).const_mul (((M : ℝ) ^ 3)⁻¹)

theorem integrable_backwardScaleDeriv {M : ℕ} (hM : 1 ≤ M) {f' : ℝ → ℝ} (hf' : Integrable f') :
    Integrable (backwardScaleDeriv M f') := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  exact (hf'.comp_mul_left' (pow_ne_zero 2 hMpos.ne')).const_mul ((M : ℝ) ^ 3)

theorem integrable_symScaleDeriv {M : ℕ} (hM : 1 ≤ M) {f' : ℝ → ℝ} (hf' : Integrable f') :
    Integrable (symScaleDeriv M f') :=
  ((integrable_forwardScaleDeriv hM hf').add (integrable_backwardScaleDeriv hM hf')).const_mul _

theorem integral_forwardScaleVec_eq_zero {f : ℝ → ℝ} (h0 : ∫ x, f x = 0) (M : ℕ) :
    ∫ x, forwardScaleVec M f x = 0 := by
  unfold forwardScaleVec
  rw [integral_const_mul, Measure.integral_comp_mul_right f (((M : ℝ) ^ 2)⁻¹),
    h0, smul_zero, mul_zero]

theorem integral_backwardScaleVec_eq_zero {f : ℝ → ℝ} (h0 : ∫ x, f x = 0) (M : ℕ) :
    ∫ x, backwardScaleVec M f x = 0 := by
  unfold backwardScaleVec
  rw [integral_const_mul, Measure.integral_comp_mul_left f ((M : ℝ) ^ 2),
    h0, smul_zero, mul_zero]

theorem integral_symScaleVec_eq_zero {M : ℕ} (hM : 1 ≤ M) {f : ℝ → ℝ}
    (hf : Integrable f) (h0 : ∫ x, f x = 0) :
    ∫ x, symScaleVec M f x = 0 := by
  unfold symScaleVec
  rw [integral_const_mul, integral_add (integrable_forwardScaleVec hM hf)
    (integrable_backwardScaleVec hM hf),
    integral_forwardScaleVec_eq_zero h0 M,
    integral_backwardScaleVec_eq_zero h0 M, add_zero, mul_zero]

/-! ### Universal sine-moment rescaling, all-integer blindness, and `O(√c)` dilation invariance -/

theorem integral_forwardScaleDeriv_mul_sin {M : ℕ} (hM : 1 ≤ M) (f' : ℝ → ℝ) (c : ℝ) :
    ∫ x, forwardScaleDeriv M f' x * Real.sin (c * x) =
      (M : ℝ)⁻¹ * ∫ t, f' t * Real.sin ((c * (M : ℝ) ^ 2) * t) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have e : (fun x => forwardScaleDeriv M f' x * Real.sin (c * x)) = fun x =>
      ((M : ℝ) ^ 3)⁻¹ * (f' (x * ((M : ℝ) ^ 2)⁻¹) *
        Real.sin ((c * (M : ℝ) ^ 2) * (x * ((M : ℝ) ^ 2)⁻¹))) := by
    funext x
    unfold forwardScaleDeriv
    have hx : (c * (M : ℝ) ^ 2) * (x * ((M : ℝ) ^ 2)⁻¹) = c * x := by field_simp
    rw [hx]; ring
  rw [e, integral_const_mul, Measure.integral_comp_mul_right
    (fun t => f' t * Real.sin ((c * (M : ℝ) ^ 2) * t)) (((M : ℝ) ^ 2)⁻¹),
    smul_eq_mul, abs_of_pos (by positivity)]
  field_simp

theorem integral_backwardScaleDeriv_mul_sin {M : ℕ} (hM : 1 ≤ M) (f' : ℝ → ℝ) (c : ℝ) :
    ∫ x, backwardScaleDeriv M f' x * Real.sin (c * x) =
      (M : ℝ) * ∫ t, f' t * Real.sin ((c / (M : ℝ) ^ 2) * t) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have e : (fun x => backwardScaleDeriv M f' x * Real.sin (c * x)) = fun x =>
      (M : ℝ) ^ 3 * (f' ((M : ℝ) ^ 2 * x) *
        Real.sin ((c / (M : ℝ) ^ 2) * ((M : ℝ) ^ 2 * x))) := by
    funext x
    unfold backwardScaleDeriv
    have hx : (c / (M : ℝ) ^ 2) * ((M : ℝ) ^ 2 * x) = c * x := by field_simp
    rw [hx]; ring
  rw [e, integral_const_mul, Measure.integral_comp_mul_left
    (fun t => f' t * Real.sin ((c / (M : ℝ) ^ 2) * t)) ((M : ℝ) ^ 2),
    smul_eq_mul, abs_of_pos (inv_pos.mpr (pow_pos hMpos 2))]
  field_simp

/-- **Exact dilation invariance of the `O(√c)` frequency bound for `forwardScaleDeriv M`:**
If `|∫ f'(t) sin(ω t) dt| ≤ K √ω` for all `ω > 0`, then for every integer `M ≥ 1` and `c > 0`,
`|∫ forwardScaleDeriv M f' x · sin(c x) dx| ≤ K √c` (with zero loss and independent of `M`). -/
theorem abs_integral_forwardScaleDeriv_mul_sin_le_sqrt
    {M : ℕ} (hM : 1 ≤ M) {f' : ℝ → ℝ} {K : ℝ}
    (hbound : ∀ ω : ℝ, 0 < ω → |∫ t, f' t * Real.sin (ω * t)| ≤ K * Real.sqrt ω)
    {c : ℝ} (hc : 0 < c) :
    |∫ x, forwardScaleDeriv M f' x * Real.sin (c * x)| ≤ K * Real.sqrt c := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  rw [integral_forwardScaleDeriv_mul_sin hM f' c, abs_mul, abs_of_pos (inv_pos.mpr hMpos)]
  have hb := hbound (c * (M : ℝ) ^ 2) (by positivity)
  have hsqrt : Real.sqrt (c * (M : ℝ) ^ 2) = Real.sqrt c * (M : ℝ) := by
    rw [Real.sqrt_mul hc.le, Real.sqrt_sq hMpos.le]
  rw [hsqrt] at hb
  calc (M : ℝ)⁻¹ * |∫ t, f' t * Real.sin ((c * (M : ℝ) ^ 2) * t)|
      ≤ (M : ℝ)⁻¹ * (K * (Real.sqrt c * (M : ℝ))) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hMpos.le)
    _ = K * Real.sqrt c := by field_simp

/-- **Exact dilation invariance of the `O(√c)` frequency bound for `backwardScaleDeriv M`:**
If `|∫ f'(t) sin(ω t) dt| ≤ K √ω` for all `ω > 0`, then for every integer `M ≥ 1` and `c > 0`,
`|∫ backwardScaleDeriv M f' x · sin(c x) dx| ≤ K √c` (with zero loss and independent of `M`). -/
theorem abs_integral_backwardScaleDeriv_mul_sin_le_sqrt
    {M : ℕ} (hM : 1 ≤ M) {f' : ℝ → ℝ} {K : ℝ}
    (hbound : ∀ ω : ℝ, 0 < ω → |∫ t, f' t * Real.sin (ω * t)| ≤ K * Real.sqrt ω)
    {c : ℝ} (hc : 0 < c) :
    |∫ x, backwardScaleDeriv M f' x * Real.sin (c * x)| ≤ K * Real.sqrt c := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  rw [integral_backwardScaleDeriv_mul_sin hM f' c, abs_mul, abs_of_pos hMpos]
  have hb := hbound (c / (M : ℝ) ^ 2) (by positivity)
  have hsqrt : Real.sqrt (c / (M : ℝ) ^ 2) = Real.sqrt c / (M : ℝ) := by
    rw [Real.sqrt_div hc.le, Real.sqrt_sq hMpos.le]
  rw [hsqrt] at hb
  calc (M : ℝ) * |∫ t, f' t * Real.sin ((c / (M : ℝ) ^ 2) * t)|
      ≤ (M : ℝ) * (K * (Real.sqrt c / (M : ℝ))) :=
        mul_le_mul_of_nonneg_left hb hMpos.le
    _ = K * Real.sqrt c := by field_simp

/-- **Exact dilation invariance of the `O(√c)` frequency bound for `symScaleDeriv M`:**
If `|∫ f'(t) sin(ω t) dt| ≤ K √ω` for all `ω > 0`, then for every integer `M ≥ 1` and `c > 0`,
`|∫ symScaleDeriv M f' x · sin(c x) dx| ≤ K √c`. -/
theorem abs_integral_symScaleDeriv_mul_sin_le_sqrt
    {M : ℕ} (hM : 1 ≤ M) {f' : ℝ → ℝ} (hf' : Integrable f') {K : ℝ}
    (hbound : ∀ ω : ℝ, 0 < ω → |∫ t, f' t * Real.sin (ω * t)| ≤ K * Real.sqrt ω)
    {c : ℝ} (hc : 0 < c) :
    |∫ x, symScaleDeriv M f' x * Real.sin (c * x)| ≤ K * Real.sqrt c := by
  have hF : Integrable fun x => forwardScaleDeriv M f' x * Real.sin (c * x) :=
    (integrable_forwardScaleDeriv hM hf').mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hB : Integrable fun x => backwardScaleDeriv M f' x * Real.sin (c * x) :=
    (integrable_backwardScaleDeriv hM hf').mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have e : (fun x => symScaleDeriv M f' x * Real.sin (c * x)) = fun x =>
      (1 / 2 : ℝ) * (forwardScaleDeriv M f' x * Real.sin (c * x) +
        backwardScaleDeriv M f' x * Real.sin (c * x)) := by
    funext x; unfold symScaleDeriv; ring
  rw [e, integral_const_mul, integral_add hF hB, abs_mul, abs_of_pos (by positivity)]
  have h1 := abs_integral_forwardScaleDeriv_mul_sin_le_sqrt hM hbound hc
  have h2 := abs_integral_backwardScaleDeriv_mul_sin_le_sqrt hM hbound hc
  have habs := (abs_add_le _ _).trans (add_le_add h1 h2)
  linarith

/-- **Universal all-integer blindness of `forwardScaleDeriv M f'`:**
If `f'` is blind on the `M²`-sublattice `arcFreq (M²(n+1) − 1)`, then `forwardScaleDeriv M f'`
is identically blind at **every** positive integer frequency `arcFreq n = 2π(n+1)` (`n ∈ ℕ`). -/
theorem integral_forwardScaleDeriv_mul_sin_eq_zero {M : ℕ} (hM : 1 ≤ M) {f' : ℝ → ℝ}
    (hblind : ∀ n : ℕ, ∫ t, f' t * Real.sin (arcFreq (M ^ 2 * (n + 1) - 1) * t) = 0)
    (n : ℕ) :
    ∫ x, forwardScaleDeriv M f' x * Real.sin (arcFreq n * x) = 0 := by
  have hM2 : 1 ≤ M ^ 2 := Nat.one_le_pow 2 M hM
  rw [integral_forwardScaleDeriv_mul_sin hM f' (arcFreq n)]
  have hfreq : arcFreq n * (M : ℝ) ^ 2 = arcFreq (M ^ 2 * (n + 1) - 1) := by
    rw [show (M : ℝ) ^ 2 = ((M ^ 2 : ℕ) : ℝ) by push_cast; ring,
      arcFreq_mul_nat hM2 n, Nat.mul_comm]
  rw [hfreq, hblind n, mul_zero]

/-- **Universal Forward-Backward Spectral Isolation Law for `symScaleDeriv M f'`:**
If `f'` is blind on the `M²`-sublattice, then at every positive integer frequency `arcFreq n`
(`n ∈ ℕ`), the forward half of `symScaleDeriv M f'` vanishes identically, isolating `½` of the
backward half. -/
theorem integral_symScaleDeriv_mul_sin_eq_half_backward {M : ℕ} (hM : 1 ≤ M) {f' : ℝ → ℝ}
    (hf' : Integrable f')
    (hblind : ∀ n : ℕ, ∫ t, f' t * Real.sin (arcFreq (M ^ 2 * (n + 1) - 1) * t) = 0)
    (n : ℕ) :
    ∫ x, symScaleDeriv M f' x * Real.sin (arcFreq n * x) =
      (1 / 2 : ℝ) * ∫ x, backwardScaleDeriv M f' x * Real.sin (arcFreq n * x) := by
  have hF : Integrable fun x => forwardScaleDeriv M f' x * Real.sin (arcFreq n * x) :=
    (integrable_forwardScaleDeriv hM hf').mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hB : Integrable fun x => backwardScaleDeriv M f' x * Real.sin (arcFreq n * x) :=
    (integrable_backwardScaleDeriv hM hf').mul_bdd (by fun_prop)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have e : (fun x => symScaleDeriv M f' x * Real.sin (arcFreq n * x)) = fun x =>
      (1 / 2 : ℝ) * (forwardScaleDeriv M f' x * Real.sin (arcFreq n * x) +
        backwardScaleDeriv M f' x * Real.sin (arcFreq n * x)) := by
    funext x; unfold symScaleDeriv; ring
  rw [e, integral_const_mul, integral_add hF hB,
    integral_forwardScaleDeriv_mul_sin_eq_zero hM hblind n, zero_add]

/-- **Halved `M`-independent `O(√(arcFreq n))` bound at all integer frequencies for `symScaleDeriv M f'`:**
Because the forward half vanishes at every `arcFreq n` (`n ∈ ℕ`), the `½` factor in `symScaleDeriv`
survives, yielding `|∫ symScaleDeriv M f' x · sin(arcFreq n · x) dx| ≤ (K / 2) √(arcFreq n)`
completely independent of `M`. -/
theorem abs_integral_symScaleDeriv_mul_sin_arcFreq_le {M : ℕ} (hM : 1 ≤ M) {f' : ℝ → ℝ}
    (hf' : Integrable f')
    (hblind : ∀ n : ℕ, ∫ t, f' t * Real.sin (arcFreq (M ^ 2 * (n + 1) - 1) * t) = 0)
    {K : ℝ}
    (hbound : ∀ ω : ℝ, 0 < ω → |∫ t, f' t * Real.sin (ω * t)| ≤ K * Real.sqrt ω)
    (n : ℕ) :
    |∫ x, symScaleDeriv M f' x * Real.sin (arcFreq n * x)| ≤
      (K / 2) * Real.sqrt (arcFreq n) := by
  rw [integral_symScaleDeriv_mul_sin_eq_half_backward hM hf' hblind n,
    abs_mul, abs_of_pos (by positivity)]
  have hb := abs_integral_backwardScaleDeriv_mul_sin_le_sqrt hM hbound (arcFreq_pos n)
  linarith

/-- **Universal `M⁴`-sublattice blindness of `backwardScaleDeriv M f'` and `symScaleDeriv M f'`:**
If `f'` is blind on the `M²`-sublattice, then both `backwardScaleDeriv M f'` and
`symScaleDeriv M f'` are identically blind on the `M⁴`-sublattice `arcFreq (M⁴(j+1) − 1)`. -/
theorem integral_backwardScaleDeriv_mul_sin_pow_four_eq_zero {M : ℕ} (hM : 1 ≤ M) {f' : ℝ → ℝ}
    (hblind : ∀ n : ℕ, ∫ t, f' t * Real.sin (arcFreq (M ^ 2 * (n + 1) - 1) * t) = 0)
    (j : ℕ) :
    ∫ x, backwardScaleDeriv M f' x *
      Real.sin (arcFreq (M ^ 4 * (j + 1) - 1) * x) = 0 := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have hMne : (M : ℝ) ≠ 0 := hMpos.ne'
  have hM2 : 1 ≤ M ^ 2 := Nat.one_le_pow 2 M hM
  have h1 : 1 ≤ M ^ 2 * (j + 1) := Nat.mul_pos hM2 (Nat.succ_pos j)
  rw [integral_backwardScaleDeriv_mul_sin hM f']
  have hfreq : arcFreq (M ^ 4 * (j + 1) - 1) / (M : ℝ) ^ 2 =
      arcFreq (M ^ 2 * (j + 1) - 1) := by
    have heq : M ^ 4 * (j + 1) - 1 = (M ^ 2 * (j + 1) - 1 + 1) * M ^ 2 - 1 := by
      rw [Nat.sub_add_cancel h1]
      ring_nf
    rw [heq, ← arcFreq_mul_nat hM2 (M ^ 2 * (j + 1) - 1)]
    push_cast; field_simp
  rw [hfreq, hblind j, mul_zero]

theorem integral_symScaleDeriv_mul_sin_pow_four_eq_zero {M : ℕ} (hM : 1 ≤ M) {f' : ℝ → ℝ}
    (hf' : Integrable f')
    (hblind : ∀ n : ℕ, ∫ t, f' t * Real.sin (arcFreq (M ^ 2 * (n + 1) - 1) * t) = 0)
    (j : ℕ) :
    ∫ x, symScaleDeriv M f' x *
      Real.sin (arcFreq (M ^ 4 * (j + 1) - 1) * x) = 0 := by
  rw [integral_symScaleDeriv_mul_sin_eq_half_backward hM hf' hblind,
    integral_backwardScaleDeriv_mul_sin_pow_four_eq_zero hM hblind j, mul_zero]

/-! ### Universal strip Laplace/Mellin transform of `symScaleProfile M` -/

theorem integral_exp_mul_symScaleProfile (M : ℕ) {P : ℝ → ℝ} {l : ℝ}
    (hP : Integrable fun v => Real.exp (l * v) * P v) :
    ∫ v, Real.exp (l * v) * symScaleProfile M P v =
      Real.cosh (l * (2 * Real.log M)) * ∫ v, Real.exp (l * v) * P v := by
  have hshift : ∀ w, Integrable fun v => Real.exp (l * v) * P (v - w) := fun w => by
    have h := (hP.comp_sub_right w).const_mul (Real.exp (l * w))
    refine h.congr (Eventually.of_forall fun v => ?_)
    simp only
    rw [show l * v = l * w + l * (v - w) by ring, Real.exp_add]; ring
  have hishift : ∀ w, ∫ v, Real.exp (l * v) * P (v - w) =
      Real.exp (l * w) * ∫ v, Real.exp (l * v) * P v := fun w => by
    rw [← integral_add_right_eq_self (μ := volume)
      (fun v => Real.exp (l * v) * P (v - w)) w, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [add_sub_cancel_right, show l * (v + w) = l * w + l * v by ring, Real.exp_add]; ring
  have hF : Integrable fun v => Real.exp (l * v) * forwardScaleProfile M P v :=
    hshift (2 * Real.log M)
  have hB : Integrable fun v => Real.exp (l * v) * backwardScaleProfile M P v := by
    have e : (fun v => Real.exp (l * v) * backwardScaleProfile M P v) =
        fun v => Real.exp (l * v) * P (v - (-(2 * Real.log M))) := by
      funext v; unfold backwardScaleProfile; rw [sub_neg_eq_add]
    rw [e]; exact hshift (-(2 * Real.log M))
  have eB : ∫ v, Real.exp (l * v) * backwardScaleProfile M P v =
      Real.exp (-(l * (2 * Real.log M))) * ∫ v, Real.exp (l * v) * P v := by
    have e : (fun v => Real.exp (l * v) * backwardScaleProfile M P v) =
        fun v => Real.exp (l * v) * P (v - (-(2 * Real.log M))) := by
      funext v; unfold backwardScaleProfile; rw [sub_neg_eq_add]
    rw [e, hishift, mul_neg]
  have e : (fun v => Real.exp (l * v) * symScaleProfile M P v) = fun v =>
      (1 / 2 : ℝ) * (Real.exp (l * v) * forwardScaleProfile M P v +
        Real.exp (l * v) * backwardScaleProfile M P v) := by
    funext v; unfold symScaleProfile; ring
  rw [e, integral_const_mul, integral_add hF hB,
    show forwardScaleProfile M P = fun v => P (v - 2 * Real.log M) from rfl,
    hishift (2 * Real.log M), eB, Real.cosh_eq (l * (2 * Real.log M))]
  ring

theorem abs_integral_exp_mul_symScaleProfile_le {M : ℕ} (hM : 1 ≤ M) {P : ℝ → ℝ}
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l ≤ 1 / 2)
    (hP : Integrable fun v => Real.exp (l * v) * P v)
    {D : ℝ} {d : ℕ} (hbound : |∫ v, Real.exp (l * v) * P v| ≤ D * (1 / 2 - l) ^ d) :
    |∫ v, Real.exp (l * v) * symScaleProfile M P v| ≤
      ((M : ℝ) * D) * (1 / 2 - l) ^ d := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hM)
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog : 0 ≤ Real.log M := Real.log_nonneg hM1
  have hcosh_le : Real.cosh (l * (2 * Real.log M)) ≤ (M : ℝ) := by
    have hlw : l * (2 * Real.log M) ≤ Real.log M := by nlinarith
    have hlw0 : 0 ≤ l * (2 * Real.log M) := by positivity
    have h1 : Real.exp (l * (2 * Real.log M)) ≤ (M : ℝ) := by
      calc Real.exp (l * (2 * Real.log M))
          ≤ Real.exp (Real.log M) := Real.exp_le_exp.mpr hlw
        _ = (M : ℝ) := Real.exp_log hMpos
    have h2 : Real.exp (-(l * (2 * Real.log M))) ≤ (M : ℝ) := by
      calc Real.exp (-(l * (2 * Real.log M)))
          ≤ Real.exp (Real.log M) := Real.exp_le_exp.mpr (by linarith)
        _ = (M : ℝ) := Real.exp_log hMpos
    rw [Real.cosh_eq]; linarith
  rw [integral_exp_mul_symScaleProfile M hP, abs_mul, abs_of_pos (Real.cosh_pos _)]
  calc Real.cosh (l * (2 * Real.log M)) * |∫ v, Real.exp (l * v) * P v|
      ≤ (M : ℝ) * (D * (1 / 2 - l) ^ d) :=
        mul_le_mul hcosh_le hbound (abs_nonneg _) hMpos.le
    _ = ((M : ℝ) * D) * (1 / 2 - l) ^ d := by ring

/-! ### The Forward, Backward, and Symmetrized Dyadic Towers (`M = k^{2^r}`) -/

/-- Level `r` of the forward `k^{2^{r+1}}`-dilated dyadic modular arc tower. -/
def arcLineForwardDyadicTowerVector (k r : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  forwardScaleVec (k ^ (2 ^ r)) (arcLineDyadicTowerVector k r ν) x

/-- Derivative of the forward dyadic tower at level `r`. -/
def arcLineForwardDyadicTowerDeriv (k r : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  forwardScaleDeriv (k ^ (2 ^ r)) (arcLineDyadicTowerDeriv k r ν) x

/-- Log-scale profile of the forward dyadic tower at level `r`. -/
def arcLineForwardDyadicTowerProfile (k r : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  forwardScaleProfile (k ^ (2 ^ r)) (arcLineDyadicTowerProfile k r ν) v

/-- Level `r` of the backward `k^{2^{r+1}}`-dilated dyadic modular arc tower. -/
def arcLineBackwardDyadicTowerVector (k r : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  backwardScaleVec (k ^ (2 ^ r)) (arcLineDyadicTowerVector k r ν) x

/-- Derivative of the backward dyadic tower at level `r`. -/
def arcLineBackwardDyadicTowerDeriv (k r : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  backwardScaleDeriv (k ^ (2 ^ r)) (arcLineDyadicTowerDeriv k r ν) x

/-- Log-scale profile of the backward dyadic tower at level `r`. -/
def arcLineBackwardDyadicTowerProfile (k r : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  backwardScaleProfile (k ^ (2 ^ r)) (arcLineDyadicTowerProfile k r ν) v

/-- Level `r` of the self-reciprocal symmetrized dyadic modular arc tower. -/
def arcLineSymDyadicTowerVector (k r : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  symScaleVec (k ^ (2 ^ r)) (arcLineDyadicTowerVector k r ν) x

/-- Derivative of the self-reciprocal symmetrized dyadic tower at level `r`. -/
def arcLineSymDyadicTowerDeriv (k r : ℕ) (ν : Measure ArcParam) (x : ℝ) : ℝ :=
  symScaleDeriv (k ^ (2 ^ r)) (arcLineDyadicTowerDeriv k r ν) x

/-- Log-scale profile of the self-reciprocal symmetrized dyadic tower at level `r`. -/
def arcLineSymDyadicTowerProfile (k r : ℕ) (ν : Measure ArcParam) (v : ℝ) : ℝ :=
  symScaleProfile (k ^ (2 ^ r)) (arcLineDyadicTowerProfile k r ν) v

/-- **Exact step identity linking level `r + 1` of the dyadic tower to `arcLineSymDyadicTowerVector`:**
`arcLineDyadicTowerVector k (r + 1) ν x = arcLineDyadicTowerVector k r ν x − (1 / cosh(log(k^{2^r}))) · arcLineSymDyadicTowerVector k r ν x`. -/
theorem arcLineDyadicTowerVector_succ_eq_sub_sym (k r : ℕ) (ν : Measure ArcParam) (x : ℝ) :
    arcLineDyadicTowerVector k (r + 1) ν x =
      arcLineDyadicTowerVector k r ν x -
        (1 / Real.cosh (Real.log ((k ^ (2 ^ r) : ℕ)))) *
          arcLineSymDyadicTowerVector k r ν x :=
  hyperbolicFilterVec_eq_sub_symScaleVec (k ^ (2 ^ r)) (arcLineDyadicTowerVector k r ν) x

theorem arcLineSymDyadicTowerVector_neg_of_map_arcNeg (k r : ℕ) {ν : Measure ArcParam}
    (hν : ν.map arcNeg = ν) (x : ℝ) :
    arcLineSymDyadicTowerVector k r ν (-x) = arcLineSymDyadicTowerVector k r ν x :=
  symScaleVec_neg (k ^ (2 ^ r)) (arcLineDyadicTowerVector_neg_of_map_arcNeg k r hν) x

theorem arcLineSymDyadicTowerVector_inv {k : ℕ} (hk : 1 ≤ k) (r : ℕ) (ν : Measure ArcParam)
    {x : ℝ} (hx : x ≠ 0) :
    arcLineSymDyadicTowerVector k r ν (1 / x) = |x| * arcLineSymDyadicTowerVector k r ν x :=
  symScaleVec_inv (one_le_pow_two_pow hk r) (arcLineDyadicTowerVector_inv hk r ν) hx

theorem integral_arcLineSymDyadicTowerVector_eq_zero {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    ∫ x, arcLineSymDyadicTowerVector k r ν x = 0 :=
  integral_symScaleVec_eq_zero (one_le_pow_two_pow hk r)
    (integrable_arcLineDyadicTowerVector hk r hν)
    (integral_arcLineDyadicTowerVector_eq_zero hk r hν)

/-- **All-integer blindness of `arcLineForwardDyadicTowerDeriv k r ν` at every dyadic depth `r ∈ ℕ`.** -/
theorem integral_arcLineForwardDyadicTowerDeriv_mul_sin_eq_zero
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (r n : ℕ) :
    ∫ x, arcLineForwardDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x) = 0 :=
  integral_forwardScaleDeriv_mul_sin_eq_zero (one_le_pow_two_pow hk r)
    (fun j => by
      rw [pow_two_pow_sq]
      exact integral_arcLineDyadicTowerDeriv_mul_sin_sublattice_eq_zero hblind hk r j) n

/-- **Exact Forward-Backward Spectral Isolation Law for `arcLineSymDyadicTowerDeriv k r ν`.** -/
theorem integral_arcLineSymDyadicTowerDeriv_mul_sin_eq_half_backward
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (r n : ℕ) :
    ∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x) =
      (1 / 2 : ℝ) * ∫ x, arcLineBackwardDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x) :=
  integral_symScaleDeriv_mul_sin_eq_half_backward (one_le_pow_two_pow hk r)
    (integrable_arcLineDyadicTowerDeriv hk r ν)
    (fun j => by
      rw [pow_two_pow_sq]
      exact integral_arcLineDyadicTowerDeriv_mul_sin_sublattice_eq_zero hblind hk r j) n

/-- **Halved `k`-independent `O(√(arcFreq n))` bound at all integer frequencies for `arcLineSymDyadicTowerDeriv`.** -/
theorem abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_arcFreq_le
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (r n : ℕ) :
    |∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x)| ≤
      2 ^ r * (4 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt (arcFreq n) := by
  have h := abs_integral_symScaleDeriv_mul_sin_arcFreq_le (one_le_pow_two_pow hk r)
    (integrable_arcLineDyadicTowerDeriv hk r ν)
    (fun j => by
      rw [pow_two_pow_sq]
      exact integral_arcLineDyadicTowerDeriv_mul_sin_sublattice_eq_zero hblind hk r j)
    (fun _ hω => abs_integral_arcLineDyadicTowerDeriv_mul_sin_le_sqrt hk r ν hω) n
  refine h.trans_eq ?_
  ring

/-- **Doubly-exponential `k^{2^{r+2}}`-sublattice blindness of `arcLineSymDyadicTowerDeriv k r ν`.** -/
theorem integral_arcLineSymDyadicTowerDeriv_mul_sin_sublattice_eq_zero
    {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0)
    {k : ℕ} (hk : 1 ≤ k) (r j : ℕ) :
    ∫ x, arcLineSymDyadicTowerDeriv k r ν x *
      Real.sin (arcFreq (k ^ (2 ^ (r + 2)) * (j + 1) - 1) * x) = 0 := by
  have hpow4 : (k ^ (2 ^ r)) ^ 4 = k ^ (2 ^ (r + 2)) := by
    rw [← pow_mul, show 2 ^ r * 4 = 2 ^ r * 2 * 2 by ring, ← pow_succ, ← pow_succ]
  rw [← hpow4]
  exact integral_symScaleDeriv_mul_sin_pow_four_eq_zero (one_le_pow_two_pow hk r)
    (integrable_arcLineDyadicTowerDeriv hk r ν)
    (fun m => by
      rw [pow_two_pow_sq]
      exact integral_arcLineDyadicTowerDeriv_mul_sin_sublattice_eq_zero hblind hk r m) j

/-- **Order-`(r + 1)` strip-edge vanishing for `arcLineSymDyadicTowerProfile k r ν`.** -/
theorem abs_integral_exp_mul_arcLineSymDyadicTowerProfile_le
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν)
    {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    |∫ v, Real.exp (l * v) * arcLineSymDyadicTowerProfile k r ν v| ≤
      (((k ^ (2 ^ r) : ℕ) : ℝ) * (10 * ν.real univ * dyadicStripConst k r)) *
        (1 / 2 - l) ^ (r + 1) :=
  abs_integral_exp_mul_symScaleProfile_le (one_le_pow_two_pow hk r) hl0 hl.le
    (integrable_exp_mul_arcLineDyadicTowerProfile k r hν hl0 hl)
    (abs_integral_exp_mul_arcLineDyadicTowerProfile_le hk r hν hl0 hl)

/-- **Order-`r` divided-difference vanishing at `l → (1/2)⁻` for `arcLineSymDyadicTowerProfile k r ν`.** -/
theorem tendsto_div_pow_integral_exp_mul_arcLineSymDyadicTowerProfile_nhdsWithin
    {k : ℕ} (hk : 1 ≤ k) (r : ℕ)
    {ν : Measure ArcParam} [IsFiniteMeasure ν] (hν : ν.map arcNeg = ν) :
    Tendsto (fun l : ℝ =>
      (∫ v, Real.exp (l * v) * arcLineSymDyadicTowerProfile k r ν v) / (1 / 2 - l) ^ r)
      (𝓝[<] (1 / 2)) (𝓝 0) := by
  set D := ((k ^ (2 ^ r) : ℕ) : ℝ) * (10 * ν.real univ * dyadicStripConst k r)
  have hlin : Tendsto (fun l : ℝ => D * (1 / 2 - l)) (𝓝[<] (1 / 2)) (𝓝 0) := by
    have hcont : Continuous fun l : ℝ => D * (1 / 2 - l) := by fun_prop
    have h := (hcont.continuousAt (x := (1 / 2 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Iio (1 / 2 : ℝ)))
    rwa [sub_self, mul_zero] at h
  refine squeeze_zero_norm' ?_ hlin
  have hmem : Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[<] (1 / 2 : ℝ) :=
    Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hmem] with l hl
  have hκ : 0 < 1 / 2 - l := by linarith [hl.2]
  have hpow : 0 < (1 / 2 - l) ^ r := pow_pos hκ r
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow, div_le_iff₀ hpow]
  calc |∫ v, Real.exp (l * v) * arcLineSymDyadicTowerProfile k r ν v|
      ≤ D * (1 / 2 - l) ^ (r + 1) :=
        abs_integral_exp_mul_arcLineSymDyadicTowerProfile_le hk r hν hl.1.le hl.2
    _ = D * (1 / 2 - l) * (1 / 2 - l) ^ r := by rw [pow_succ']; ring

/-! ### Master unconditional dyadic Mellin-inversion duality & spectral isolation theorem -/

/-- **Master unconditional theorem for the forward, backward, and symmetrized dyadic modular arc towers.**
There exists a finite nonzero `arcNeg`-symmetric measure `ν` on the modular bottom arc such that
for every integer `k ≥ 2` and every dyadic depth `r ∈ ℕ`:
1. `arcLineForwardDyadicTowerDeriv k r ν` is identically blind at **every** positive integer
   frequency `arcFreq n = 2π(n+1)` (`n ∈ ℕ`);
2. `arcLineSymDyadicTowerVector k r ν` is even, strictly self-reciprocal (`S(1/x) = |x| S(x)`),
   and has zero mean;
3. At every positive integer frequency `arcFreq n`, `arcLineSymDyadicTowerDeriv k r ν` isolates
   `½` of the backward moment and satisfies the `k`-independent bound
   `2^r · (4 √(π/2) · ν.real univ) · √(arcFreq n)`;
4. Along the doubly-exponential `k^{2^{r+2}}`-sublattice `arcFreq (k^{2^{r+2}}(j+1) − 1)`,
   `arcLineSymDyadicTowerDeriv k r ν` vanishes identically;
5. Its strip Laplace/Mellin transform vanishes to order `O((1/2 − l)^{r+1})` as `l → (1/2)⁻`. -/
theorem exists_dyadic_inversionDual_isolation_arcWitness :
    ∃ ν : Measure ArcParam, IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν.map arcNeg = ν ∧
      ∀ k : ℕ, 2 ≤ k → ∀ r : ℕ,
        (∀ n : ℕ, ∫ x, arcLineForwardDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x) = 0) ∧
        (∀ x, arcLineSymDyadicTowerVector k r ν (-x) = arcLineSymDyadicTowerVector k r ν x) ∧
        (∀ x, x ≠ 0 → arcLineSymDyadicTowerVector k r ν (1 / x) =
          |x| * arcLineSymDyadicTowerVector k r ν x) ∧
        ∫ x, arcLineSymDyadicTowerVector k r ν x = 0 ∧
        (∀ n : ℕ, ∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x) =
          (1 / 2 : ℝ) * ∫ x, arcLineBackwardDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x)) ∧
        (∀ n : ℕ, |∫ x, arcLineSymDyadicTowerDeriv k r ν x * Real.sin (arcFreq n * x)| ≤
          2 ^ r * (4 * Real.sqrt (Real.pi / 2) * ν.real univ) * Real.sqrt (arcFreq n)) ∧
        (∀ j : ℕ, ∫ x, arcLineSymDyadicTowerDeriv k r ν x *
          Real.sin (arcFreq (k ^ (2 ^ (r + 2)) * (j + 1) - 1) * x) = 0) ∧
        Tendsto (fun l : ℝ =>
          (∫ v, Real.exp (l * v) * arcLineSymDyadicTowerProfile k r ν v) / (1 / 2 - l) ^ r)
          (𝓝[<] (1 / 2)) (𝓝 0) := by
  obtain ⟨ν, hfin, hne, hsym, hblind_whittaker, _⟩ := exists_arcWitness
  have hblind : ∀ n : ℕ, ∫ t, arcLineDeriv ν t * Real.sin (arcFreq n * t) = 0 := fun n => by
    rw [integral_arcLineDeriv_mul_sin, (hblind_whittaker n).1, mul_zero, neg_zero]
  refine ⟨ν, hfin, hne, hsym, fun k hk r => ?_⟩
  have hk1 : 1 ≤ k := by omega
  exact ⟨integral_arcLineForwardDyadicTowerDeriv_mul_sin_eq_zero hblind hk1 r,
    arcLineSymDyadicTowerVector_neg_of_map_arcNeg k r hsym,
    fun x hx => arcLineSymDyadicTowerVector_inv hk1 r ν hx,
    integral_arcLineSymDyadicTowerVector_eq_zero hk1 r hsym,
    integral_arcLineSymDyadicTowerDeriv_mul_sin_eq_half_backward hblind hk1 r,
    abs_integral_arcLineSymDyadicTowerDeriv_mul_sin_arcFreq_le hblind hk1 r,
    integral_arcLineSymDyadicTowerDeriv_mul_sin_sublattice_eq_zero hblind hk1 r,
    tendsto_div_pow_integral_exp_mul_arcLineSymDyadicTowerProfile_nhdsWithin hk1 r hsym⟩

end

end RHTower
