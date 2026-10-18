import GaloisForLFunctions.BiScaleUncertainty.DistantCopyPolarEnforcement

/-!
# Symmetric Three-Copy Even-Source Polar & Dual-Rate ($\pm 1/2$) Enforcement

This module closes the even-source polar enforcement problem (`quantitative-constant.md` §3).
Whereas the two-copy operation `subtractCopy f a T u = f u - a * f (u - T)` in
`DistantCopyPolarEnforcement` breaks source parity (`f(-u) = f(u)`) and cancels only the positive
exponential moment $\int g(u) e^{u/2}\,du$, the **symmetric three-copy operator**
$$\operatorname{symmetricCopy}(f, b, T)(u) := f(u) - b\bigl(f(u - T) + f(u + T)\bigr)$$
at the hyperbolic secant attenuation $b = \frac{1}{2\cosh(T/2)}$ simultaneously:
1. Preserves both **even source parity** (`f(-u) = f(u)`) and **odd source parity**
   (`f(-u) = -f(u)`).
2. Cancels **both** exponential moments $\int g(u) e^{+u/2}\,du = 0$ and
   $\int g(u) e^{-u/2}\,du = 0$ (and hence both $\int g(u)\cosh(u/2)\,du = 0$ and
   $\int g(u)\sinh(u/2)\,du = 0$) as well as $\int_{(0, \infty)} h_g(x)\cosh(x/2)\,dx = 0$.
3. Multiplies `autocorr f x` by the exact scalar $(1 + 2b^2)$ on every bounded window $|x| \le A$
   once $T > D + A$, preserving all normalized correlation values and finite logarithmic-grid zeros.
4. Perturbs the normalized Bi-Scale Lévy energy `normalizedArchEnergy` by $O(e^{-T})$, proving that
   the **even-source polar and nonpolar logarithmic-grid classes have identical infima** at every
   regularity order $r \ge 2$ (`even_polar_log_grid_lower_bound_iff`).
-/

open MeasureTheory Set Filter Topology
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

set_option autoImplicit false

/-! ## §1. The Symmetric Three-Copy Operator & Parity Preservation -/

/-- The symmetric three-copy source perturbation
$$\operatorname{symmetricCopy}(f, b, T)(u) := f(u) - b\bigl(f(u - T) + f(u + T)\bigr).$$ -/
def symmetricCopy (f : ℝ → ℝ) (b T u : ℝ) : ℝ :=
  f u - b * (f (u - T) + f (u + T))

/-- Decomposition of `symmetricCopy` into two successive `subtractCopy` steps plus a cross-term,
or directly as `subtractCopy f b T u - b * f (u + T)`. -/
theorem symmetricCopy_eq_subtractCopy_sub (f : ℝ → ℝ) (b T u : ℝ) :
    symmetricCopy f b T u = subtractCopy f b T u - b * f (u - (-T)) := by
  unfold symmetricCopy subtractCopy
  ring_nf

/-- The symmetric three-copy operator at attenuation $b = 1 / (2 \cosh(T/2))$, which simultaneously
cancels both $\pm 1/2$ exponential source moments while preserving parity. -/
def evenPolarCopy (f : ℝ → ℝ) (T : ℝ) : ℝ → ℝ :=
  symmetricCopy f (1 / (2 * Real.cosh (T / 2))) T

theorem continuous_symmetricCopy {f : ℝ → ℝ} (hf : Continuous f) (b T : ℝ) :
    Continuous (symmetricCopy f b T) := by
  unfold symmetricCopy
  exact hf.sub (continuous_const.mul
    ((hf.comp (continuous_id.sub continuous_const)).add
      (hf.comp (continuous_id.add continuous_const))))

theorem contDiff_symmetricCopy {f : ℝ → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) (b T : ℝ) :
    ContDiff ℝ n (symmetricCopy f b T) := by
  unfold symmetricCopy
  exact hf.sub (contDiff_const.mul
    ((hf.comp (contDiff_id.sub contDiff_const)).add
      (hf.comp (contDiff_id.add contDiff_const))))

theorem hasCompactSupport_symmetricCopy {f : ℝ → ℝ}
    (hfc : HasCompactSupport f) (b T : ℝ) :
    HasCompactSupport (symmetricCopy f b T) := by
  have hrew : symmetricCopy f b T =
      fun u => subtractCopy f b T u + (-b) * f (u - (-T)) := by
    funext u
    unfold symmetricCopy subtractCopy
    ring_nf
  rw [hrew]
  exact (hasCompactSupport_subtractCopy hfc b T).add
    ((hfc.comp_homeomorph (Homeomorph.subRight (-T))).mul_left)

/-- **Even-Source Parity Preservation:**
If `f` is even (`∀ u, f (-u) = f u`), then `symmetricCopy f b T` is even for all `b, T ∈ ℝ`. -/
theorem symmetricCopy_even_of_even {f : ℝ → ℝ}
    (heven : ∀ u : ℝ, f (-u) = f u) (b T u : ℝ) :
    symmetricCopy f b T (-u) = symmetricCopy f b T u := by
  unfold symmetricCopy
  have h1 : -u - T = -(u + T) := by ring
  have h2 : -u + T = -(u - T) := by ring
  rw [heven u, h1, h2, heven (u + T), heven (u - T), add_comm (f (u + T)) (f (u - T))]

/-- **Odd-Source Parity Preservation:**
If `f` is odd (`∀ u, f (-u) = -f u`), then `symmetricCopy f b T` is odd for all `b, T ∈ ℝ`. -/
theorem symmetricCopy_odd_of_odd {f : ℝ → ℝ}
    (hodd : ∀ u : ℝ, f (-u) = -f u) (b T u : ℝ) :
    symmetricCopy f b T (-u) = -symmetricCopy f b T u := by
  unfold symmetricCopy
  have h1 : -u - T = -(u + T) := by ring
  have h2 : -u + T = -(u - T) := by ring
  rw [hodd u, h1, h2, hodd (u + T), hodd (u - T)]
  ring

/-- `evenPolarCopy f T` preserves even source parity. -/
theorem evenPolarCopy_even_of_even {f : ℝ → ℝ}
    (heven : ∀ u : ℝ, f (-u) = f u) (T u : ℝ) :
    evenPolarCopy f T (-u) = evenPolarCopy f T u :=
  symmetricCopy_even_of_even heven _ T u

/-! ## §2. Simultaneous Dual-Rate ($\pm s$) Exponential Moment Cancellation -/

/-- **Exact Exponential Moment Multiplier of `symmetricCopy`:**
For every continuous compactly supported `f : ℝ → ℝ` and all `b, T, s ∈ ℝ`,
$$\int_{\mathbb{R}} \operatorname{symmetricCopy}(f, b, T)(u) \, e^{s u} \, du
  = \bigl(1 - 2 b \cosh(s T)\bigr) \int_{\mathbb{R}} f(u) \, e^{s u} \, du.$$ -/
theorem integral_symmetricCopy_mul_exp {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (b T s : ℝ) :
    (∫ u, symmetricCopy f b T u * Real.exp (s * u)) =
      (1 - 2 * b * Real.cosh (s * T)) * ∫ u, f u * Real.exp (s * u) := by
  have hi : Integrable (fun u => f u * Real.exp (s * u)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hit1 : Integrable (fun u => f (u - T) * Real.exp (s * u)) :=
    ((hf.comp (continuous_id.sub continuous_const)).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hfc.comp_homeomorph (Homeomorph.subRight T)).mul_right
  have hit2 : Integrable (fun u => f (u - (-T)) * Real.exp (s * u)) :=
    ((hf.comp (continuous_id.sub continuous_const)).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hfc.comp_homeomorph (Homeomorph.subRight (-T))).mul_right
  have hi12 : Integrable (fun u => f u * Real.exp (s * u) - b * (f (u - T) * Real.exp (s * u))) :=
    hi.sub (hit1.const_mul b)
  have hrew : (fun u => symmetricCopy f b T u * Real.exp (s * u)) =
      fun u => (f u * Real.exp (s * u) - b * (f (u - T) * Real.exp (s * u))) -
        b * (f (u - (-T)) * Real.exp (s * u)) := by
    funext u
    unfold symmetricCopy
    rw [sub_neg_eq_add]
    ring
  rw [hrew, integral_sub hi12 (hit2.const_mul b),
    integral_sub hi (hit1.const_mul b), integral_const_mul, integral_const_mul,
    integral_shift_mul_exp f s T, integral_shift_mul_exp f s (-T)]
  rw [Real.cosh_eq, show s * -T = -(s * T) by ring]
  ring

/-- `evenPolarCopy f T` has vanishing $+1/2$ exponential moment for every `T ∈ ℝ`. -/
theorem integral_evenPolarCopy_exp_pos_half {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (T : ℝ) :
    (∫ u, evenPolarCopy f T u * Real.exp (u / 2)) = 0 := by
  have h := integral_symmetricCopy_mul_exp hf hfc (1 / (2 * Real.cosh (T / 2))) T (1 / 2)
  have hcosh : Real.cosh (T / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hfactor : 1 - 2 * (1 / (2 * Real.cosh (T / 2))) * Real.cosh (1 / 2 * T) = 0 := by
    rw [show 1 / 2 * T = T / 2 by ring]
    field_simp [hcosh]
    ring
  rw [hfactor, zero_mul] at h
  simpa only [evenPolarCopy, one_div, div_eq_mul_inv, one_mul, mul_comm] using h

/-- `evenPolarCopy f T` simultaneously has vanishing $-1/2$ exponential moment for every `T ∈ ℝ`. -/
theorem integral_evenPolarCopy_exp_neg_half {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (T : ℝ) :
    (∫ u, evenPolarCopy f T u * Real.exp (-u / 2)) = 0 := by
  have h := integral_symmetricCopy_mul_exp hf hfc (1 / (2 * Real.cosh (T / 2))) T (-1 / 2)
  have hcosh : Real.cosh (T / 2) ≠ 0 := (Real.cosh_pos _).ne'
  have hfactor : 1 - 2 * (1 / (2 * Real.cosh (T / 2))) * Real.cosh (-1 / 2 * T) = 0 := by
    rw [show -1 / 2 * T = -(T / 2) by ring, Real.cosh_neg]
    field_simp [hcosh]
    ring
  rw [hfactor, zero_mul] at h
  have harg : ∀ u : ℝ, -1 / 2 * u = -u / 2 := fun u => by ring
  simpa only [evenPolarCopy, harg] using h

/-- `evenPolarCopy f T` is polar-neutral (`∫ x in Ioi 0, autocorr (evenPolarCopy f T) x * cosh(x/2) = 0`)
for every `T ∈ ℝ`. -/
theorem integral_evenPolarCopy_autocorr_cosh {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (T : ℝ) :
    (∫ x in Ioi 0, autocorr (evenPolarCopy f T) x * Real.cosh (x / 2)) = 0 := by
  have hwhole := integral_autocorr_mul_cosh
    (contDiff_symmetricCopy hf (1 / (2 * Real.cosh (T / 2))) T)
    (hasCompactSupport_symmetricCopy hfc (1 / (2 * Real.cosh (T / 2))) T)
  change (∫ x, autocorr (evenPolarCopy f T) x * Real.cosh (x / 2)) =
    (∫ u, evenPolarCopy f T u * Real.exp (u / 2)) *
      ∫ u, evenPolarCopy f T u * Real.exp (-u / 2) at hwhole
  rw [integral_evenPolarCopy_exp_pos_half hf.continuous hfc T, zero_mul] at hwhole
  have heven := integral_comp_abs (f := fun x => autocorr (evenPolarCopy f T) x * Real.cosh (x / 2))
  have hid : (fun x : ℝ => autocorr (evenPolarCopy f T) |x| * Real.cosh (|x| / 2)) =
      fun x => autocorr (evenPolarCopy f T) x * Real.cosh (x / 2) := by
    funext x
    rcases abs_choice x with hx | hx
    · rw [hx]
    · rw [hx, autocorr_neg, show -x / 2 = -(x / 2) by ring, Real.cosh_neg]
  rw [hid, hwhole] at heven
  linarith

/-! ## §3. Exact Nine-Term Autocorrelation Expansion & Local Window Preservation -/

/-- **Exact Five-Lag Autocorrelation Expansion of `symmetricCopy`:**
For any continuous compactly supported `f : ℝ → ℝ` and `b, T, x ∈ ℝ`,
$$\operatorname{autocorr}(\operatorname{symmetricCopy}(f, b, T), x)
  = (1 + 2 b^2) h_f(x)
    - 2 b \bigl(h_f(x - T) + h_f(x + T)\bigr)
    + b^2 \bigl(h_f(x - 2T) + h_f(x + 2T)\bigr).$$ -/
theorem autocorr_symmetricCopy {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (b T x : ℝ) :
    autocorr (symmetricCopy f b T) x =
      (1 + 2 * b ^ 2) * autocorr f x -
        2 * b * (autocorr f (x - T) + autocorr f (x + T)) +
        b ^ 2 * (autocorr f (x - 2 * T) + autocorr f (x + 2 * T)) := by
  have hi := integrable_shift_mul_shift hf hfc
  let term0 : ℝ → ℝ := fun u => f (u + 0) * f (u + x)
  let term1 : ℝ → ℝ := fun u => f (u + 0) * f (u + (x - T))
  let term2 : ℝ → ℝ := fun u => f (u + 0) * f (u + (x + T))
  let term3 : ℝ → ℝ := fun u => f (u + -T) * f (u + x)
  let term4 : ℝ → ℝ := fun u => f (u + -T) * f (u + (x - T))
  let term5 : ℝ → ℝ := fun u => f (u + -T) * f (u + (x + T))
  let term6 : ℝ → ℝ := fun u => f (u + T) * f (u + x)
  let term7 : ℝ → ℝ := fun u => f (u + T) * f (u + (x - T))
  let term8 : ℝ → ℝ := fun u => f (u + T) * f (u + (x + T))
  have h0 : Integrable term0 := hi 0 x
  have h1 : Integrable term1 := hi 0 (x - T)
  have h2 : Integrable term2 := hi 0 (x + T)
  have h3 : Integrable term3 := hi (-T) x
  have h4 : Integrable term4 := hi (-T) (x - T)
  have h5 : Integrable term5 := hi (-T) (x + T)
  have h6 : Integrable term6 := hi T x
  have h7 : Integrable term7 := hi T (x - T)
  have h8 : Integrable term8 := hi T (x + T)
  have hA0 : Integrable (fun u => term0 u + b ^ 2 * term4 u) :=
    h0.add (h4.const_mul (b ^ 2))
  have hA : Integrable (fun u => (term0 u + b ^ 2 * term4 u) + b ^ 2 * term8 u) :=
    hA0.add (h8.const_mul (b ^ 2))
  have hB0 : Integrable (fun u => b * term1 u + b * term2 u) :=
    (h1.const_mul b).add (h2.const_mul b)
  have hB1 : Integrable (fun u => (b * term1 u + b * term2 u) + b * term3 u) :=
    hB0.add (h3.const_mul b)
  have hB : Integrable (fun u => ((b * term1 u + b * term2 u) + b * term3 u) + b * term6 u) :=
    hB1.add (h6.const_mul b)
  have hAB : Integrable (fun u =>
      ((term0 u + b ^ 2 * term4 u) + b ^ 2 * term8 u) -
        (((b * term1 u + b * term2 u) + b * term3 u) + b * term6 u)) :=
    hA.sub hB
  have hC : Integrable (fun u => b ^ 2 * term5 u + b ^ 2 * term7 u) :=
    (h5.const_mul (b ^ 2)).add (h7.const_mul (b ^ 2))
  calc
    autocorr (symmetricCopy f b T) x =
        ∫ u, (((term0 u + b ^ 2 * term4 u) + b ^ 2 * term8 u) -
          (((b * term1 u + b * term2 u) + b * term3 u) + b * term6 u)) +
          (b ^ 2 * term5 u + b ^ 2 * term7 u) := by
      unfold autocorr symmetricCopy
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp [term0, term1, term2, term3, term4, term5, term6, term7, term8]
      simp only [add_zero, sub_eq_add_neg, add_assoc]
      ring
    _ = (1 + 2 * b ^ 2) * autocorr f x -
          2 * b * (autocorr f (x - T) + autocorr f (x + T)) +
          b ^ 2 * (autocorr f (x - 2 * T) + autocorr f (x + 2 * T)) := by
      rw [integral_add hAB hC, integral_sub hA hB,
        integral_add hA0 (h8.const_mul (b ^ 2)), integral_add h0 (h4.const_mul (b ^ 2)),
        integral_add hB1 (h6.const_mul b), integral_add hB0 (h3.const_mul b),
        integral_add (h1.const_mul b) (h2.const_mul b),
        integral_add (h5.const_mul (b ^ 2)) (h7.const_mul (b ^ 2))]
      dsimp [term0, term1, term2, term3, term4, term5, term6, term7, term8]
      simp only [integral_const_mul, integral_shift_mul_shift]
      have s0 : x - 0 = x := by ring
      have s1 : x - T - 0 = x - T := by ring
      have s2 : x + T - 0 = x + T := by ring
      have s3 : x - -T = x + T := by ring
      have s4 : x - T - -T = x := by ring
      have s5 : x + T - -T = x + 2 * T := by ring
      have s7 : x - T - T = x - 2 * T := by ring
      have s8 : x + T - T = x := by ring
      rw [s0, s1, s2, s3, s4, s5, s7, s8]
      ring

/-- On any bounded window `|x| ≤ A` (`0 ≤ A`, `0 ≤ D`), once `D + A < T`, `autocorr (symmetricCopy f b T) x`
is an exact scalar multiple `(1 + 2 * b ^ 2) * autocorr f x`. -/
theorem autocorr_symmetricCopy_local {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {D A T : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + A < T)
    {x : ℝ} (hx : |x| ≤ A) (b : ℝ) :
    autocorr (symmetricCopy f b T) x = (1 + 2 * b ^ 2) * autocorr f x := by
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  have h1 : D < |x - T| := lt_of_lt_of_le (by linarith : D < -(x - T)) (neg_le_abs _)
  have h2 : D < |x + T| := lt_of_lt_of_le (by linarith : D < x + T) (le_abs_self _)
  have h3 : D < |x - 2 * T| := lt_of_lt_of_le (by linarith : D < -(x - 2 * T)) (neg_le_abs _)
  have h4 : D < |x + 2 * T| := lt_of_lt_of_le (by linarith : D < x + 2 * T) (le_abs_self _)
  rw [autocorr_symmetricCopy hf hfc, hsupp _ h1, hsupp _ h2, hsupp _ h3, hsupp _ h4]
  ring

/-- Exact preservation of normalized local autocorrelation values on `|x| ≤ A`. -/
theorem normalized_autocorr_symmetricCopy_local {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {D A T : ℝ} (hD : 0 ≤ D) (hA : 0 ≤ A)
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + A < T)
    {x : ℝ} (hx : |x| ≤ A) (b : ℝ) :
    autocorr (symmetricCopy f b T) x / autocorr (symmetricCopy f b T) 0 =
      autocorr f x / autocorr f 0 := by
  rw [autocorr_symmetricCopy_local hf hfc hD hA hsupp hT hx,
    autocorr_symmetricCopy_local hf hfc hD hA hsupp hT (by simpa using hA : |(0 : ℝ)| ≤ A)]
  have hb : (1 + 2 * b ^ 2 : ℝ) ≠ 0 := by positivity
  exact mul_div_mul_left _ _ hb

/-! ## §4. Quantitative Archimedean Energy Error & Even-Source Infimum Equivalence -/

/-- Exact Bi-Scale Lévy energy decomposition of `symmetricCopy f b T` for `T ≥ D + 1` (`D ≥ 0`). -/
theorem biScaleLevyEnergy_symmetricCopy {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) {D T : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) (b : ℝ) :
    biScaleLevyEnergy (symmetricCopy f b T) =
      (1 + 2 * b ^ 2) * biScaleLevyEnergy f +
        2 * b * (∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x) -
        b ^ 2 * (∫ x in Ioi 0, autocorr f (x - 2 * T) * archLevySinhWeight x) := by
  have hm : autocorr (symmetricCopy f b T) 0 = (1 + 2 * b ^ 2) * autocorr f 0 :=
    autocorr_symmetricCopy_local hf.continuous hfc hD le_rfl hsupp (by linarith) (by simp) b
  have h2T : D + 1 ≤ 2 * T := by linarith
  have hfi := integrableOn_biScaleLevyIntegrand hf hfc
  have hti1 := integrableOn_shifted_autocorr_arch hf hfc hsupp hT
  have hti2 := integrableOn_shifted_autocorr_arch hf hfc hsupp h2T
  have hfi1 : IntegrableOn (fun x =>
      (1 + 2 * b ^ 2) * ((autocorr f 0 - autocorr f x) * archLevySinhWeight x) +
        2 * b * (autocorr f (x - T) * archLevySinhWeight x)) (Ioi 0) :=
    (hfi.const_mul (1 + 2 * b ^ 2)).add (hti1.const_mul (2 * b))
  unfold biScaleLevyEnergy
  calc
    _ = ∫ x in Ioi 0,
        ((1 + 2 * b ^ 2) * ((autocorr f 0 - autocorr f x) * archLevySinhWeight x) +
          2 * b * (autocorr f (x - T) * archLevySinhWeight x)) -
          b ^ 2 * (autocorr f (x - 2 * T) * archLevySinhWeight x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      have hp1 : autocorr f (x + T) = 0 := hsupp _
        (lt_of_lt_of_le (by linarith : D < x + T) (le_abs_self _))
      have hp2 : autocorr f (x + 2 * T) = 0 := hsupp _
        (lt_of_lt_of_le (by linarith : D < x + 2 * T) (le_abs_self _))
      rw [hm, autocorr_symmetricCopy hf.continuous hfc, hp1, hp2]
      ring
    _ = _ := by
      rw [integral_sub hfi1 (hti2.const_mul (b ^ 2)),
        integral_add (hfi.const_mul (1 + 2 * b ^ 2)) (hti1.const_mul (2 * b)),
        integral_const_mul, integral_const_mul, integral_const_mul]

/-- Normalized archimedean energy difference for `symmetricCopy f b T`. -/
theorem normalizedArchEnergy_symmetricCopy_sub {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) {D T : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) (b : ℝ) :
    normalizedArchEnergy (symmetricCopy f b T) - normalizedArchEnergy f =
      (2 * b * (∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x) -
        b ^ 2 * (∫ x in Ioi 0, autocorr f (x - 2 * T) * archLevySinhWeight x)) /
        ((1 + 2 * b ^ 2) * autocorr f 0) := by
  have hm : autocorr (symmetricCopy f b T) 0 = (1 + 2 * b ^ 2) * autocorr f 0 :=
    autocorr_symmetricCopy_local hf.continuous hfc hD le_rfl hsupp (by linarith) (by simp) b
  have hb : (1 + 2 * b ^ 2 : ℝ) ≠ 0 := by positivity
  rw [normalizedArchEnergy, normalizedArchEnergy,
    biScaleLevyEnergy_symmetricCopy hf hfc hD hsupp hT b, hm]
  field_simp [hR.ne', hb]
  ring

/-- For every `T ∈ ℝ`, `1 / (2 * cosh(T / 2)) ≤ exp(-T / 2)`. -/
theorem one_div_two_cosh_half_le_exp_neg_half (T : ℝ) :
    1 / (2 * Real.cosh (T / 2)) ≤ Real.exp (-T / 2) := by
  have hcosh : 0 < 2 * Real.cosh (T / 2) := mul_pos two_pos (Real.cosh_pos _)
  rw [div_le_iff₀ hcosh]
  have hsum : 2 * Real.cosh (T / 2) = Real.exp (T / 2) + Real.exp (-(T / 2)) := by
    rw [Real.cosh_eq]
    ring
  have hprod : Real.exp (-T / 2) * Real.exp (T / 2) = 1 := by
    rw [← Real.exp_add, show -T / 2 + T / 2 = 0 by ring, Real.exp_zero]
  have hpos : 0 ≤ Real.exp (-T / 2) * Real.exp (-(T / 2)) :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  nlinarith

/-- Exponentially small normalized archimedean energy error for `evenPolarCopy f T`:
$$|\operatorname{normalizedArchEnergy}(\operatorname{evenPolarCopy}(f, T))
  - \operatorname{normalizedArchEnergy}(f)|
  \le 3 \, \operatorname{polarEnergyErrorConstant}(f, D) \, e^{-T}.$$ -/
theorem normalizedArchEnergy_evenPolarCopy_error {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hR : 0 < autocorr f 0) {D T : ℝ} (hD : 0 ≤ D)
    (hsupp : ∀ x, D < |x| → autocorr f x = 0) (hT : D + 1 ≤ T) :
    |normalizedArchEnergy (evenPolarCopy f T) - normalizedArchEnergy f| ≤
      3 * polarEnergyErrorConstant f D * Real.exp (-T) := by
  let b := 1 / (2 * Real.cosh (T / 2))
  have hb_pos : 0 < b := div_pos one_pos (mul_pos two_pos (Real.cosh_pos _))
  have hb_le_exp : b ≤ Real.exp (-T / 2) := one_div_two_cosh_half_le_exp_neg_half T
  have hb_le_one : b ≤ 1 := by
    have h1 : (1 : ℝ) ≤ Real.cosh (T / 2) := Real.one_le_cosh _
    dsimp [b]
    rw [div_le_iff₀ (mul_pos two_pos (Real.cosh_pos _))]
    linarith
  have hb2_le : b ^ 2 ≤ b := by nlinarith
  have h2T : D + 1 ≤ 2 * T := by linarith
  have hM : 0 ≤ ∫ x, |autocorr f x| := integral_nonneg (fun _ => abs_nonneg _)
  have hI1 := abs_integral_shifted_autocorr_arch_le hf hfc hsupp hT
  have hI2 := abs_integral_shifted_autocorr_arch_le hf hfc hsupp h2T
  have htail2_le : copyTailFactor D (2 * T) ≤ copyTailFactor D T := by
    unfold copyTailFactor
    have hd : 0 ≤ 1 - Real.exp (-2) :=
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).le
    apply div_le_div_of_nonneg_right _ hd
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.exp_le_exp.mpr (by linarith)
  change |normalizedArchEnergy (symmetricCopy f b T) - normalizedArchEnergy f| ≤ _
  rw [normalizedArchEnergy_symmetricCopy_sub hf hfc hR hD hsupp hT b, abs_div,
    abs_of_pos (mul_pos (by positivity) hR)]
  have hnum :
      |2 * b * (∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x) -
        b ^ 2 * (∫ x in Ioi 0, autocorr f (x - 2 * T) * archLevySinhWeight x)| ≤
      3 * Real.exp (-T / 2) * (copyTailFactor D T * ∫ x, |autocorr f x|) := by
    have htri := abs_sub
      (2 * b * (∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x))
      (b ^ 2 * (∫ x in Ioi 0, autocorr f (x - 2 * T) * archLevySinhWeight x))
    rw [abs_mul, abs_of_pos (mul_pos two_pos hb_pos),
      abs_mul, abs_of_pos (sq_pos_of_pos hb_pos)] at htri
    have hterm1 :
        2 * b * |∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x| ≤
          2 * Real.exp (-T / 2) * (copyTailFactor D T * ∫ x, |autocorr f x|) := by
      calc
        2 * b * |∫ x in Ioi 0, autocorr f (x - T) * archLevySinhWeight x|
          ≤ 2 * b * (copyTailFactor D T * ∫ x, |autocorr f x|) :=
            mul_le_mul_of_nonneg_left hI1 (by positivity)
        _ ≤ 2 * Real.exp (-T / 2) * (copyTailFactor D T * ∫ x, |autocorr f x|) :=
            mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (copyTailFactor_nonneg D T) hM)
    have hterm2 :
        b ^ 2 * |∫ x in Ioi 0, autocorr f (x - 2 * T) * archLevySinhWeight x| ≤
          Real.exp (-T / 2) * (copyTailFactor D T * ∫ x, |autocorr f x|) := by
      calc
        b ^ 2 * |∫ x in Ioi 0, autocorr f (x - 2 * T) * archLevySinhWeight x|
          ≤ b ^ 2 * (copyTailFactor D (2 * T) * ∫ x, |autocorr f x|) :=
            mul_le_mul_of_nonneg_left hI2 (by positivity)
        _ ≤ b ^ 2 * (copyTailFactor D T * ∫ x, |autocorr f x|) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htail2_le hM) (by positivity)
        _ ≤ Real.exp (-T / 2) * (copyTailFactor D T * ∫ x, |autocorr f x|) :=
            mul_le_mul_of_nonneg_right (hb2_le.trans hb_le_exp)
              (mul_nonneg (copyTailFactor_nonneg D T) hM)
    linarith
  have hden : autocorr f 0 ≤ (1 + 2 * b ^ 2) * autocorr f 0 := by
    nlinarith [sq_nonneg b]
  calc
    _ ≤ (3 * Real.exp (-T / 2) * (copyTailFactor D T * ∫ x, |autocorr f x|)) / autocorr f 0 := by
      exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
        (div_le_div_of_nonneg_left
          (mul_nonneg (by positivity) (mul_nonneg (copyTailFactor_nonneg D T) hM)) hR hden)
    _ = 3 * polarEnergyErrorConstant f D * Real.exp (-T) := by
      have he : Real.exp (-T / 2) * Real.exp (-(T - D) / 2) =
          Real.exp (D / 2) * Real.exp (-T) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      have hd : 0 < 1 - Real.exp (-2) :=
        sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
      unfold copyTailFactor polarEnergyErrorConstant
      calc
        (3 * Real.exp (-T / 2) *
            (2 * Real.exp (-(T - D) / 2) / (1 - Real.exp (-2)) * ∫ x, |autocorr f x|)) /
            autocorr f 0 =
          3 * (2 * (Real.exp (-T / 2) * Real.exp (-(T - D) / 2)) * (∫ x, |autocorr f x|)) /
            (autocorr f 0 * (1 - Real.exp (-2))) := by
          field_simp [hR.ne', hd.ne']
        _ = 3 * (2 * Real.exp (D / 2) * (∫ x, |autocorr f x|) /
            (autocorr f 0 * (1 - Real.exp (-2)))) * Real.exp (-T) := by
          rw [he]
          ring

/-- Every nonzero even compactly supported $C^r$ source ($r \ge 2$) admits an **even**,
polar-neutral, dual-rate ($\pm 1/2$) neutral $C^r$ compact source with identical normalized
autocorrelation on `[-A, A]` and normalized Bi-Scale Lévy energy within `ε`. -/
theorem exists_even_polar_source_local_energy_close {f : ℝ → ℝ} {r : WithTop ℕ∞}
    (hr : 2 ≤ r) (hf : ContDiff ℝ r f) (hfc : HasCompactSupport f)
    (heven : ∀ u : ℝ, f (-u) = f u) (hR : 0 < autocorr f 0) (A : ℝ) (hA : 0 ≤ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ r g ∧ HasCompactSupport g ∧
      (∀ u : ℝ, g (-u) = g u) ∧ 0 < autocorr g 0 ∧
      (∫ u, g u * Real.exp (u / 2)) = 0 ∧
      (∫ u, g u * Real.exp (-u / 2)) = 0 ∧
      (∫ x in Ioi 0, autocorr g x * Real.cosh (x / 2)) = 0 ∧
      (∀ x, |x| ≤ A → autocorr g x / autocorr g 0 = autocorr f x / autocorr f 0) ∧
      |normalizedArchEnergy g - normalizedArchEnergy f| < ε := by
  obtain ⟨D, hDpos, hsupp⟩ := exists_pos_autocorr_support_radius hfc
  have hf2 : ContDiff ℝ 2 f := hf.of_le hr
  have htend :
      Tendsto (fun T : ℝ => 3 * polarEnergyErrorConstant f D * Real.exp (-T)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (3 * polarEnergyErrorConstant f D)
  have hevent := (tendsto_order.mp htend).2 ε hε
  obtain ⟨T, hlarge, hsmall⟩ := ((eventually_gt_atTop (D + max A 1)).and hevent).exists
  have hTA : D + A < T := lt_of_le_of_lt (by linarith [le_max_left A 1]) hlarge
  have hT1 : D + 1 ≤ T := le_of_lt (lt_of_le_of_lt (by linarith [le_max_right A 1]) hlarge)
  refine ⟨evenPolarCopy f T,
    contDiff_symmetricCopy hf _ _,
    hasCompactSupport_symmetricCopy hfc _ _,
    evenPolarCopy_even_of_even heven T,
    ?_,
    integral_evenPolarCopy_exp_pos_half hf.continuous hfc T,
    integral_evenPolarCopy_exp_neg_half hf.continuous hfc T,
    integral_evenPolarCopy_autocorr_cosh hf2 hfc T,
    ?_,
    (normalizedArchEnergy_evenPolarCopy_error hf2 hfc hR hDpos.le hsupp hT1).trans_lt hsmall⟩
  · change 0 < autocorr (symmetricCopy f (1 / (2 * Real.cosh (T / 2))) T) 0
    rw [autocorr_symmetricCopy_local hf.continuous hfc hDpos.le hA hsupp hTA
      (by simpa using hA : |(0 : ℝ)| ≤ A)]
    positivity
  · intro x hx
    exact normalized_autocorr_symmetricCopy_local hf.continuous hfc hDpos.le hA hsupp hTA hx _

/-- **Even-Source Polar Infimum Equivalence (`↔`):**
A lower bound `C` on `normalizedArchEnergy` holds for all **even** polar-neutral logarithmic-grid
sources if and only if it holds for all **even** logarithmic-grid sources without the polar
neutrality condition. -/
theorem even_polar_log_grid_lower_bound_iff (r : WithTop ℕ∞) (hr : 2 ≤ r) (N : ℕ) (C : ℝ) :
    (∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → (∀ u : ℝ, f (-u) = f u) →
      0 < autocorr f 0 →
      (∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0) →
      (∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2)) = 0 → C ≤ normalizedArchEnergy f) ↔
    (∀ (f : ℝ → ℝ), ContDiff ℝ r f → HasCompactSupport f → (∀ u : ℝ, f (-u) = f u) →
      0 < autocorr f 0 →
      (∀ n ∈ Finset.Icc 2 N, autocorr f (Real.log (n : ℝ)) = 0) → C ≤ normalizedArchEnergy f) := by
  constructor
  · intro hpolar f hf hfc heven hR hgrid
    by_contra hbad
    have hgap : 0 < (C - normalizedArchEnergy f) / 2 := by linarith
    let A := max (Real.log (N : ℝ)) 0
    obtain ⟨g, hg, hgc, hgeven, hRg, _, _, hpg, hlocal, herr⟩ :=
      exists_even_polar_source_local_energy_close hr hf hfc heven hR A (le_max_right _ _) hgap
    have hgridg : ∀ n ∈ Finset.Icc 2 N, autocorr g (Real.log (n : ℝ)) = 0 := by
      intro n hn
      have hnrange := Finset.mem_Icc.mp hn
      have hnp : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
      have hbound : |Real.log (n : ℝ)| ≤ A := by
        rw [abs_of_nonneg hln]
        exact (Real.log_le_log hnp (by exact_mod_cast hnrange.2)).trans (le_max_left _ _)
      have hval := hlocal (Real.log (n : ℝ)) hbound
      rw [hgrid n hn, zero_div] at hval
      exact (div_eq_zero_iff.mp hval).resolve_right hRg.ne'
    have hgC := hpolar g hg hgc hgeven hRg hgridg hpg
    have := (le_abs_self (normalizedArchEnergy g - normalizedArchEnergy f)).trans_lt herr
    linarith
  · intro hall f hf hfc heven hR hgrid _
    exact hall f hf hfc heven hR hgrid

end

end GaloisForLFunctions.BiScaleUncertainty
