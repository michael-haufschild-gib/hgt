import GaloisForLFunctions.FiniteFreeProbability.CauchyLimitLaw
import GaloisForLFunctions.FiniteFreeProbability.MultisetJensenInequality
import GaloisForLFunctions.FiniteFreeProbability.ZeroPieceRealization

/-!
# Almost all Jensen roots of `Ξ` are nearly real, unconditionally

Let `x` run over the roots of the reversed Jensen polynomial `R_d(ξ(σ + i·))`, and `ℓ_d = ½ log d`.

**Theorem.** For every `ε > 0`:

* for `σ ≥ 1/2`, the proportion of roots with `Im x ≥ ε ℓ_d` tends to `0`;
* at `σ = 1/2`, the proportion of roots of `R_d(Ξ)` with `|Im x| ≥ ε ℓ_d` tends to `0`.

No hypothesis on the zeros is used. If RH fails, finitely many outliers `x ≈ d/a_q` leave the real axis
linearly in `d`, but the bulk does not.

Mechanism. By the moment formula `R_d(w) = E (w + iV)^d`, in the upper half-plane
`|R_d(ℓz)| ≤ ℓ^d |z + i|^d e^{o(d)}`, uniformly on circles: `|ℓz + iv| ≤ ℓ(|z + i| − 1) + max(|v|, ℓ)`,
and the moments are controlled at the saddle. At `z = iθ` this is sharp, by the first-order law.
Since `log|z + i|` is harmonic in the upper half-plane, Jensen's inequality on a disc centred at `iθ`
bounds the number of rescaled roots in a smaller concentric disc by `o(d)`. Such discs exhaust the upper
half-plane as `θ → ∞`, and the same inequality bounds the far roots. At `σ = 1/2`, `R_d(−x) = (−1)^d R_d(x)`
gives the lower half-plane.
-/

open Polynomial Filter Topology Complex Metric MeasureTheory
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

/-! ## The moment formula in the complex plane -/

/-- `R_d(w) = ∫ Φ(v) e^{(σ−1/2)v} (w + iv)^d dv`. -/
theorem eval_xiJensen_eq_integral (σ : ℝ) (d : ℕ) (w : ℂ) :
    (xiJensen σ d).eval w = ∫ v : ℝ, ((riemannKernelReal v * Real.exp ((σ - 1 / 2) * v) : ℝ) : ℂ) *
      (w + I * v) ^ d := by
  have hterm : ∀ v : ℝ, ((riemannKernelReal v * Real.exp ((σ - 1 / 2) * v) : ℝ) : ℂ) *
      (w + I * v) ^ d = ∑ k ∈ Finset.range (d + 1), (d.choose k : ℂ) * w ^ (d - k) * I ^ k *
        ((riemannKernelReal v * v ^ k * Real.exp ((σ - 1 / 2) * v) : ℝ) : ℂ) := fun v => by
    rw [add_comm w, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]
    push_cast
    ring
  have hI : ∀ k, Integrable fun v : ℝ =>
      ((riemannKernelReal v * v ^ k * Real.exp ((σ - 1 / 2) * v) : ℝ) : ℂ) :=
    fun k => Complex.ofRealCLM.integrable_comp (integrable_kernel_pow_exp _ k)
  simp_rw [hterm]
  rw [integral_finsetSum _ fun k _ => (hI k).const_mul _, xiJensen, jensenRev_eq_sum,
    eval_finsetSum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
  rw [integral_const_mul, integral_complex_ofReal, eval_mul, eval_C, eval_pow, eval_X,
    PowerSeries.coeff_mk, xiShiftCoeff_eq_moment]
  have hdesc : (d.descFactorial k : ℂ) = (d.choose k : ℂ) * (k.factorial : ℂ) := by
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [hdesc, xiMoment]
  field_simp

theorem one_le_norm_add_I {z : ℂ} (hz : 0 ≤ z.im) : 1 ≤ ‖z + I‖ := by
  have h := Complex.abs_im_le_norm (z + I)
  simp only [add_im, I_im] at h
  have := le_abs_self (z.im + 1)
  linarith

/-- `|ℓz + iv| ≤ ℓ(|z + i| − 1) + max(|v|, ℓ)` for `Im z ≥ 0`. -/
theorem norm_mul_add_I_mul_le {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {z : ℂ} (hz : 0 ≤ z.im) (v : ℝ) :
    ‖(ℓ : ℂ) * z + I * v‖ ≤ ℓ * (‖z + I‖ - 1) + max |v| ℓ := by
  set u := max |v| ℓ
  have hu1 : |v| ≤ u := le_max_left _ _
  have hu2 : ℓ ≤ u := le_max_right _ _
  have hb : 0 ≤ ℓ * z.im := mul_nonneg hℓ hz
  have step1 : ‖(ℓ : ℂ) * z + I * v‖ ≤ ‖(ℓ : ℂ) * z + I * u‖ := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
    apply Real.sqrt_le_sqrt
    simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, zero_mul, one_mul,
      zero_add, sub_zero, add_zero]
    have h1 : |ℓ * z.im + v| ≤ ℓ * z.im + u :=
      abs_le.2 ⟨by linarith [(abs_le.1 hu1).1], by linarith [(abs_le.1 hu1).2]⟩
    have h2 : (ℓ * z.im + v) ^ 2 ≤ (ℓ * z.im + u) ^ 2 := sq_le_sq' (abs_le.1 h1).1 (abs_le.1 h1).2
    nlinarith
  have hsplit : (ℓ : ℂ) * z + I * u = (ℓ : ℂ) * (z + I) + I * ((u - ℓ : ℝ) : ℂ) := by
    push_cast
    ring
  have step2 : ‖(ℓ : ℂ) * z + I * u‖ ≤ ℓ * ‖z + I‖ + (u - ℓ) := by
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, one_mul,
      Real.norm_of_nonneg hℓ, Real.norm_of_nonneg (by linarith)]
  linarith

/-- `∫ Φ(v) e^{(σ−1/2)|v|} dv`. -/
def xiC0 (σ : ℝ) : ℝ := ∫ v : ℝ, riemannKernelReal v * Real.exp ((σ - 1 / 2) * |v|)

theorem xiC0_nonneg (σ : ℝ) : 0 ≤ xiC0 σ := integral_nonneg fun v =>
  mul_nonneg (riemannKernel_superExp.nonneg v) (Real.exp_pos _).le

/-- `∫ Φ(v) e^{y|v|} dv ≤ 2 ξ(1/2 + y)`-type bound, at `y = σ + r − 1/2`. -/
theorem integral_kernel_exp_abs_le (σ r : ℝ) :
    ∫ v : ℝ, riemannKernelReal v * Real.exp ((σ - 1 / 2 + r) * |v|) ≤ 2 * xiMoment (σ + r) 0 := by
  set y := σ - 1 / 2 + r
  have hmom : ∀ v : ℝ, riemannKernelReal v * v ^ 0 * Real.exp ((σ + r - 1 / 2) * v) =
      riemannKernelReal v * Real.exp (y * v) := fun v => by
    rw [pow_zero, mul_one, show σ + r - 1 / 2 = y by simp only [y]; ring]
  have hm : xiMoment (σ + r) 0 = ∫ v : ℝ, riemannKernelReal v * Real.exp (y * v) := by
    rw [xiMoment]
    exact integral_congr_ae (Eventually.of_forall hmom)
  have hi1 : Integrable fun v : ℝ => riemannKernelReal v * Real.exp (y * v) := by
    have := integrable_kernel_pow_exp y 0
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp
  have hi2 : Integrable fun v : ℝ => riemannKernelReal v * Real.exp (y * -v) := by
    have := hi1.comp_neg
    refine this.congr (Eventually.of_forall fun v => ?_)
    simp only [riemannKernel_superExp.even v]
  have hrefl := integral_kernel_reflect (fun v => Real.exp (y * v))
  have hle : ∫ v : ℝ, riemannKernelReal v * Real.exp (y * |v|) ≤
      ∫ v : ℝ, (riemannKernelReal v * Real.exp (y * v) + riemannKernelReal v * Real.exp (y * -v)) := by
    refine integral_mono (riemannKernel_superExp.integrable_mul_exp y) (hi1.add hi2) fun v => ?_
    have hΦ := riemannKernel_superExp.nonneg v
    have h1 := Real.exp_pos (y * v)
    have h2 := Real.exp_pos (y * -v)
    simp only
    rcases abs_cases v with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · nlinarith [mul_nonneg hΦ h2.le]
    · nlinarith [mul_nonneg hΦ h1.le]
  rw [integral_add hi1 hi2, hrefl, ← hm] at hle
  linarith

/-- **The upper half-plane bound.** With `t = ℓ(|z + i| − 1)` and any `r > 0`:
`|R_d(ℓz)| ≤ 2 d!/r^d e^{tr} ξ(σ + r) + (t + ℓ)^d C₀`. -/
theorem norm_eval_xiJensen_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) (d : ℕ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {z : ℂ}
    (hz : 0 ≤ z.im) {r : ℝ} (hr : 0 < r) :
    ‖(xiJensen σ d).eval ((ℓ : ℂ) * z)‖ ≤
      2 * ((d.factorial : ℝ) / r ^ d * (Real.exp (ℓ * (‖z + I‖ - 1) * r) * xiMoment (σ + r) 0)) +
        (ℓ * (‖z + I‖ - 1) + ℓ) ^ d * xiC0 σ := by
  set τ : ℝ := σ - 1 / 2
  have hτ : 0 ≤ τ := by simp only [τ]; linarith
  set t := ℓ * (‖z + I‖ - 1)
  have ht : 0 ≤ t := mul_nonneg hℓ (by linarith [one_le_norm_add_I hz])
  have hfact : (0 : ℝ) < (d.factorial : ℝ) := by positivity
  set K : ℝ := (d.factorial : ℝ) / r ^ d * Real.exp (t * r)
  have hK : 0 ≤ K := by positivity
  set Φ := riemannKernelReal
  have hΦ : ∀ v, 0 ≤ Φ v := riemannKernel_superExp.nonneg
  set G₁ : ℝ → ℝ := fun v => Φ v * Real.exp (τ * |v|) * (t + |v|) ^ d
  set G₂ : ℝ → ℝ := fun v => (t + ℓ) ^ d * (Φ v * Real.exp (τ * |v|))
  have hcontΦ : Continuous Φ := riemannKernel_superExp.continuous
  have hmaj : ∀ v, G₁ v ≤ K * (Φ v * Real.exp ((τ + r) * |v|)) := fun v => by
    have hb : 0 ≤ t + |v| := by positivity
    have h := Real.pow_div_factorial_le_exp ((t + |v|) * r) (by positivity) d
    rw [div_le_iff₀ hfact, mul_pow] at h
    have hpow : (t + |v|) ^ d ≤ K * Real.exp (r * |v|) := by
      simp only [K]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      rw [mul_assoc, ← Real.exp_add, show t * r + r * |v| = (t + |v|) * r by ring, mul_comm]
      linarith
    have hE : Real.exp ((τ + r) * |v|) = Real.exp (τ * |v|) * Real.exp (r * |v|) := by
      rw [← Real.exp_add]
      ring_nf
    simp only [G₁]
    rw [hE]
    have hnn : 0 ≤ Φ v * Real.exp (τ * |v|) := mul_nonneg (hΦ v) (Real.exp_pos _).le
    calc Φ v * Real.exp (τ * |v|) * (t + |v|) ^ d
        ≤ Φ v * Real.exp (τ * |v|) * (K * Real.exp (r * |v|)) :=
          mul_le_mul_of_nonneg_left hpow hnn
      _ = _ := by ring
  have hbase := riemannKernel_superExp.integrable_mul_exp (τ + r)
  have hG₁ : Integrable G₁ := by
    refine (hbase.const_mul K).mono' ?_ (Eventually.of_forall fun v => ?_)
    · exact ((hcontΦ.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by
        simp only [G₁]
        have := hΦ v
        positivity)]
      exact hmaj v
  have hG₂ : Integrable G₂ := (riemannKernel_superExp.integrable_mul_exp τ).const_mul _
  have hpt : ∀ v : ℝ, ‖((Φ v * Real.exp (τ * v) : ℝ) : ℂ) * ((ℓ : ℂ) * z + I * v) ^ d‖ ≤
      G₁ v + G₂ v := fun v => by
    have h1 := norm_mul_add_I_mul_le hℓ hz v
    have hnorm : ‖((ℓ : ℂ) * z + I * v)‖ ^ d ≤ (t + |v|) ^ d + (t + ℓ) ^ d := by
      have hmax : (t + max |v| ℓ) ^ d ≤ (t + |v|) ^ d + (t + ℓ) ^ d := by
        rcases max_choice |v| ℓ with h | h <;> rw [h]
        · have : 0 ≤ (t + ℓ) ^ d := pow_nonneg (by positivity) d
          linarith
        · have : 0 ≤ (t + |v|) ^ d := pow_nonneg (by positivity) d
          linarith
      exact (pow_le_pow_left₀ (norm_nonneg _) h1 d).trans hmax
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg
      (mul_nonneg (hΦ v) (Real.exp_pos _).le)]
    have hexp : Real.exp (τ * v) ≤ Real.exp (τ * |v|) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (le_abs_self v) hτ)
    have hnn : 0 ≤ ‖((ℓ : ℂ) * z + I * v)‖ ^ d := by positivity
    calc Φ v * Real.exp (τ * v) * ‖((ℓ : ℂ) * z + I * v)‖ ^ d
        ≤ Φ v * Real.exp (τ * |v|) * ‖((ℓ : ℂ) * z + I * v)‖ ^ d := by gcongr; exact hΦ v
      _ ≤ Φ v * Real.exp (τ * |v|) * ((t + |v|) ^ d + (t + ℓ) ^ d) :=
          mul_le_mul_of_nonneg_left hnorm (mul_nonneg (hΦ v) (Real.exp_pos _).le)
      _ = _ := by simp only [G₁, G₂]; ring
  have hbound := norm_integral_le_of_norm_le (hG₁.add hG₂) (Eventually.of_forall hpt)
  rw [integral_add' hG₁ hG₂] at hbound
  have hint1 : ∫ v, G₁ v ≤ K * (2 * xiMoment (σ + r) 0) := by
    calc ∫ v, G₁ v ≤ ∫ v, K * (Φ v * Real.exp ((τ + r) * |v|)) :=
          integral_mono hG₁ (hbase.const_mul K) hmaj
      _ = K * ∫ v, Φ v * Real.exp ((τ + r) * |v|) := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_kernel_exp_abs_le σ r) hK
  have hint2 : ∫ v, G₂ v = (t + ℓ) ^ d * xiC0 σ := integral_const_mul _ _
  rw [eval_xiJensen_eq_integral]
  refine hbound.trans ?_
  rw [hint2]
  have : K * (2 * xiMoment (σ + r) 0) =
      2 * ((d.factorial : ℝ) / r ^ d * (Real.exp (t * r) * xiMoment (σ + r) 0)) := by
    simp only [K]
    ring
  linarith

/-! ## The rescaled roots -/

/-- The rescaled roots `x/ℓ_d` of `R_d(ξ(σ + i·))`. -/
def scaledRoots (σ : ℝ) (d : ℕ) : Multiset ℂ :=
  (xiJensen σ d).roots.map fun x => x / (cauchyScale d : ℂ)

theorem xiShiftCoeff_zero (σ : ℝ) : xiShiftCoeff σ 0 = xi (σ : ℂ) := by
  simp [xiShiftCoeff]

theorem constantCoeff_mk_xiShiftCoeff (σ : ℝ) :
    PowerSeries.constantCoeff (PowerSeries.mk (xiShiftCoeff σ)) = xi (σ : ℂ) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, xiShiftCoeff_zero]

theorem natDegree_xiJensen (σ : ℝ) (d : ℕ) : (xiJensen σ d).natDegree = d :=
  natDegree_jensenRev (by rw [constantCoeff_mk_xiShiftCoeff]; exact xi_ne_zero_of_real σ)

theorem leadingCoeff_xiJensen (σ : ℝ) (d : ℕ) : (xiJensen σ d).leadingCoeff = xi (σ : ℂ) := by
  rw [leadingCoeff, natDegree_xiJensen, xiJensen, coeff_jensenRev_self,
    constantCoeff_mk_xiShiftCoeff]

theorem card_roots_xiJensen (σ : ℝ) (d : ℕ) : Multiset.card (xiJensen σ d).roots = d := by
  rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_xiJensen]

theorem card_scaledRoots (σ : ℝ) (d : ℕ) : Multiset.card (scaledRoots σ d) = d := by
  rw [scaledRoots, Multiset.card_map, card_roots_xiJensen]

theorem multiset_prod_mul_sub (M : Multiset ℂ) {ℓ : ℂ} (hℓ : ℓ ≠ 0) (z : ℂ) :
    (M.map fun x => ℓ * z - x).prod = ℓ ^ Multiset.card M * (M.map fun x => z - x / ℓ).prod := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons a M ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih, pow_succ]
    field_simp

/-- `R_d(ℓz) = ξ(σ) ℓ^d Π_y (z − y)`. -/
theorem eval_xiJensen_eq_prod (σ : ℝ) (d : ℕ) (hℓ : cauchyScale d ≠ 0) (z : ℂ) :
    (xiJensen σ d).eval ((cauchyScale d : ℂ) * z) =
      xi (σ : ℂ) * (cauchyScale d : ℂ) ^ d * ((scaledRoots σ d).map fun y => z - y).prod := by
  have hℓ' : (cauchyScale d : ℂ) ≠ 0 := ofReal_ne_zero.2 hℓ
  conv_lhs => rw [(IsAlgClosed.splits (xiJensen σ d)).eq_prod_roots]
  rw [leadingCoeff_xiJensen, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, scaledRoots,
    Multiset.map_map]
  have := multiset_prod_mul_sub (xiJensen σ d).roots hℓ' z
  rw [card_roots_xiJensen] at this
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  rw [this, mul_assoc]

/-! ## The bound on circles -/

/-- The error exponent `O(ℓ_d + d/ℓ_d)`. -/
def jensenError (σ : ℝ) (d : ℕ) : ℝ :=
  Real.log (xiMoment (1 / 2 + 1) 0) + (σ - 1 / 2) * 3 + (σ - 1 / 2) * cauchyScale d +
    3 * ((d : ℝ) / cauchyScale d) + 1 + cauchyScale d

theorem exp_nat_mul_log {x : ℝ} (hx : 0 < x) (d : ℕ) : Real.exp (d * Real.log x) = x ^ d := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

/-- On a circle in the upper half-plane centred on the imaginary axis,
`|Π_y (z − y)| ≤ (2e^{E_d} + C₀)/|ξ(σ)| · |z + i|^d`, uniformly, for large `d`. -/
theorem eventually_sphere_bound {σ : ℝ} (hσ : 1 / 2 ≤ σ) {θ₀ R : ℝ} (hR : 0 < R) (hRθ : R < θ₀) :
    ∀ᶠ d : ℕ in atTop, ∀ z ∈ sphere (I * (θ₀ : ℂ)) R,
      ‖((scaledRoots σ d).map fun y => z - y).prod‖ ≤
        (2 * Real.exp (jensenError σ d) + xiC0 σ) / ‖xi (σ : ℂ)‖ * ‖z + I‖ ^ d := by
  set τ : ℝ := σ - 1 / 2
  have hτ : 0 ≤ τ := by simp only [τ]; linarith
  set θ₁ := θ₀ - R
  have hθ₁ : 0 < θ₁ := by simp only [θ₁]; linarith
  have hθ₀ : 0 < θ₀ := by linarith
  have hξ : 0 < ‖xi (σ : ℂ)‖ := norm_pos_iff.2 (xi_ne_zero_of_real σ)
  have hA : (0 : ℝ) < 1 / (1 + θ₀ + R) := by positivity
  filter_upwards [tendsto_cauchyScale.eventually_ge_atTop 1,
    tendsto_cauchyScale_div.eventually (gt_mem_nhds hA),
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (τ * (1 + θ₁) / θ₁),
    eventually_ge_atTop 1] with d hℓ1 hℓd hdτ hd1 z hzs
  have hprod := eval_xiJensen_eq_prod σ d (show cauchyScale d ≠ 0 by linarith [hℓ1]) z
  have hdef : jensenError σ d = Real.log (xiMoment (1 / 2 + 1) 0) + τ * 3 + τ * cauchyScale d +
      3 * ((d : ℝ) / cauchyScale d) + 1 + cauchyScale d := rfl
  set ℓ := cauchyScale d
  have hℓ : 0 < ℓ := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hzn : ‖z - I * (θ₀ : ℂ)‖ = R := mem_sphere_iff_norm.1 hzs
  have hzim : θ₁ ≤ z.im := by
    have h := Complex.abs_im_le_norm (z - I * (θ₀ : ℂ))
    rw [hzn] at h
    have h2 := (abs_le.1 h).1
    simp only [sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add] at h2
    simp only [θ₁]
    linarith
  have hz0 : 0 ≤ z.im := by linarith
  set θ := ‖z + I‖ - 1
  have hnorm1 : 1 + θ = ‖z + I‖ := by
    simp only [θ]
    ring
  have hθlow : θ₁ ≤ θ := by
    have h := Complex.abs_im_le_norm (z + I)
    simp only [add_im, I_im] at h
    have := le_abs_self (z.im + 1)
    simp only [θ]
    linarith
  have hθup : θ ≤ θ₀ + R := by
    have hsum : z + I = (z - I * (θ₀ : ℂ)) + I * ((θ₀ + 1 : ℝ) : ℂ) := by
      push_cast
      ring
    have h : ‖z + I‖ ≤ R + (θ₀ + 1) := by
      rw [hsum]
      refine (norm_add_le _ _).trans ?_
      rw [hzn, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    simp only [θ]
    linarith
  have hθ0 : 0 ≤ θ := by linarith
  have h1θ : 0 < 1 + θ := by linarith
  have hdenom : 0 < (1 + θ) * ℓ := by positivity
  set r : ℝ := (d : ℝ) / ((1 + θ) * ℓ)
  have hr1 : 1 ≤ r := by
    rw [le_div_iff₀ hdenom]
    rw [div_lt_div_iff₀ hdR (by positivity)] at hℓd
    nlinarith
  have hrpos : 0 < r := by linarith
  have h1θ₁ : 0 < 1 + θ₁ := by linarith
  have hrle : r ≤ d / (1 + θ₁) :=
    div_le_div_of_nonneg_left hdR.le h1θ₁ (by nlinarith)
  have hτle : τ ≤ d * (θ₁ / (1 + θ₁)) := by
    rw [div_le_iff₀ hθ₁] at hdτ
    rw [mul_div_assoc', le_div_iff₀ h1θ₁]
    linarith
  have hsplit : d * (θ₁ / (1 + θ₁)) + d / (1 + θ₁) = (d : ℝ) := by
    field_simp
    ring
  have hwd : τ + r ≤ d := by linarith
  have hS : Real.log ((d.factorial : ℝ) / r ^ d * (Real.exp (θ * ℓ * r) * xiMoment (σ + r) 0)) ≤
      Real.log (xiMoment (1 / 2 + 1) 0) + τ * 3 + τ * ℓ + 3 * r + 1 + ℓ +
        d * Real.log (1 + θ) + d * Real.log ℓ :=
    log_saddle_le hτ hθ0 hd1 hℓ1 hr1 hwd
  have hc0 : 0 < xiMoment (σ + r) 0 := xiMoment_zero_pos _
  have hfact : (0 : ℝ) < (d.factorial : ℝ) := by positivity
  set S : ℝ := (d.factorial : ℝ) / r ^ d * (Real.exp (θ * ℓ * r) * xiMoment (σ + r) 0)
  have hSpos : 0 < S := by positivity
  have h3r : 3 * r ≤ 3 * ((d : ℝ) / ℓ) := by
    have : r ≤ (d : ℝ) / ℓ := div_le_div_of_nonneg_left hdR.le hℓ (by nlinarith)
    linarith
  set E := jensenError σ d
  have hE : Real.log S ≤ E + d * Real.log (1 + θ) + d * Real.log ℓ := by
    rw [hdef]
    linarith
  have hSle : S ≤ Real.exp E * (1 + θ) ^ d * ℓ ^ d := by
    calc S = Real.exp (Real.log S) := (Real.exp_log hSpos).symm
      _ ≤ Real.exp (E + d * Real.log (1 + θ) + d * Real.log ℓ) := Real.exp_le_exp.2 hE
      _ = _ := by rw [Real.exp_add, Real.exp_add, exp_nat_mul_log h1θ, exp_nat_mul_log hℓ]
  have hN := norm_eval_xiJensen_le hσ d hℓ.le hz0 hrpos
  have e1 : ℓ * (‖z + I‖ - 1) = θ * ℓ := mul_comm _ _
  have e2 : (θ * ℓ + ℓ) ^ d = (1 + θ) ^ d * ℓ ^ d := by
    rw [← mul_pow]
    congr 1
    ring
  rw [e1, e2] at hN
  have hnormeval : ‖(xiJensen σ d).eval ((ℓ : ℂ) * z)‖ =
      ‖xi (σ : ℂ)‖ * ℓ ^ d * ‖((scaledRoots σ d).map fun y => z - y).prod‖ := by
    rw [hprod, norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg hℓ.le]
  set P := ‖((scaledRoots σ d).map fun y => z - y).prod‖
  have hℓd' : 0 < ℓ ^ d := pow_pos hℓ d
  have hmain : ℓ ^ d * (‖xi (σ : ℂ)‖ * P) ≤
      ℓ ^ d * ((2 * Real.exp E + xiC0 σ) * ‖z + I‖ ^ d) := by
    rw [← hnorm1]
    have hbound : ‖xi (σ : ℂ)‖ * ℓ ^ d * P ≤ 2 * S + (1 + θ) ^ d * ℓ ^ d * xiC0 σ := by
      rw [← hnormeval]
      exact hN
    nlinarith [hSle, hbound]
  have hfin := le_of_mul_le_mul_left hmain hℓd'
  rw [div_mul_eq_mul_div, le_div_iff₀ hξ]
  linarith

/-- Jensen's inequality for the rescaled roots at the centre `iθ₀`. -/
theorem prod_max_le_center {σ : ℝ} {θ₀ R : ℝ} (hR : 0 < R) (hRθ : R < θ₀) {d : ℕ} {B : ℝ}
    (hB : ∀ z ∈ sphere (I * (θ₀ : ℂ)) R,
      ‖((scaledRoots σ d).map fun y => z - y).prod‖ ≤ B * ‖z + I‖ ^ d) :
    ((scaledRoots σ d).map fun y => max R ‖I * (θ₀ : ℂ) - y‖).prod ≤ B * (1 + θ₀) ^ d := by
  have hθ₀ : 0 < θ₀ := by linarith
  have hnorm : ‖I * (θ₀ : ℂ) - -I‖ = 1 + θ₀ := by
    rw [show I * (θ₀ : ℂ) - -I = I * ((1 + θ₀ : ℝ) : ℂ) by
      push_cast
      ring, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have ha : -I ∉ closedBall (I * (θ₀ : ℂ)) R := by
    rw [mem_closedBall, dist_comm, dist_eq_norm, hnorm]
    linarith
  have h := multiset_prod_max_le hR ha (scaledRoots σ d) (B := B) (fun z hz => by
    rw [card_scaledRoots, sub_neg_eq_add]
    exact hB z hz)
  rwa [card_scaledRoots, hnorm] at h

/-- At the centre `iθ₀`, `Π_y |iθ₀ − y| = m_d(θ₀ℓ_d)/(|ξ(σ)| ℓ_d^d)`. -/
theorem prod_norm_center {σ : ℝ} {θ₀ : ℝ} {d : ℕ} (hℓ : 0 < cauchyScale d)
    (hm : 0 ≤ jensenMass (xiMoment σ) d (θ₀ * cauchyScale d)) :
    ‖xi (σ : ℂ)‖ * cauchyScale d ^ d * ((scaledRoots σ d).map fun y => ‖I * (θ₀ : ℂ) - y‖).prod =
      jensenMass (xiMoment σ) d (θ₀ * cauchyScale d) := by
  have h := eval_xiJensen_eq_prod σ d hℓ.ne' (I * (θ₀ : ℂ))
  have harg : (cauchyScale d : ℂ) * (I * (θ₀ : ℂ)) = I * ((θ₀ * cauchyScale d : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, eval_xiJensen_I_mul] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hm, norm_mul, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_of_nonneg hℓ.le, norm_multiset_prod_map] at hn
  exact hn.symm

/-! ## Counting -/

theorem tendsto_jensenError_div (σ c : ℝ) :
    Tendsto (fun d : ℕ => (c + jensenError σ d) / d) atTop (𝓝 0) := by
  have h := ((((tendsto_const_div_atTop_nhds_zero_nat
    (c + Real.log (xiMoment (1 / 2 + 1) 0) + (σ - 1 / 2) * 3 + 1)).add
    (tendsto_cauchyScale_div.const_mul (σ - 1 / 2))).add
    (tendsto_one_div_cauchyScale.const_mul 3)).add tendsto_cauchyScale_div)
  have hlim : (0 : ℝ) + (σ - 1 / 2) * 0 + 3 * 0 + 0 = 0 := by ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0, tendsto_cauchyScale.eventually_gt_atTop 0] with d hd hℓ
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [jensenError]
  field_simp
  ring

/-- `2 e^E + C ≤ (2 + C) e^E` for `E ≥ 0`, `C ≥ 0`. -/
theorem two_mul_exp_add_le {E C : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C) :
    2 * Real.exp E + C ≤ (2 + C) * Real.exp E := by
  have := Real.one_le_exp hE
  nlinarith

theorem eventually_jensenError_nonneg (σ : ℝ) (hσ : 1 / 2 ≤ σ) :
    ∀ᶠ d : ℕ in atTop, 0 ≤ jensenError σ d := by
  have hK := tendsto_cauchyScale.eventually_ge_atTop (-Real.log (xiMoment (1 / 2 + 1) 0))
  filter_upwards [hK, tendsto_cauchyScale.eventually_gt_atTop 0] with d h1 h2
  simp only [jensenError]
  have h3 : 0 ≤ σ - 1 / 2 := by linarith
  have h4 : 0 ≤ (σ - 1 / 2) * cauchyScale d := mul_nonneg h3 h2.le
  have h5 : 0 ≤ 3 * ((d : ℝ) / cauchyScale d) := by positivity
  linarith

/-- **Few rescaled roots in a disc around `iθ₀`.** For `0 < r < R < θ₀`. -/
theorem tendsto_card_near_div {σ : ℝ} (hσ : 1 / 2 ≤ σ) {θ₀ r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hRθ : R < θ₀) :
    Tendsto (fun d : ℕ =>
      (Multiset.card ((scaledRoots σ d).filter fun y => ‖I * (θ₀ : ℂ) - y‖ ≤ r) : ℝ) / d)
      atTop (𝓝 0) := by
  have hR : 0 < R := by linarith
  have hθ₀ : 0 < θ₀ := by linarith
  have hC₀ := xiC0_nonneg σ
  have h2C : 0 < 2 + xiC0 σ := by linarith
  have hξ : 0 < ‖xi (σ : ℂ)‖ := norm_pos_iff.2 (xi_ne_zero_of_real σ)
  set L := Real.log (R / r)
  have hL : 0 < L := Real.log_pos ((one_lt_div hr).2 hrR)
  have hlaw := tendsto_log_jensenMass hσ hθ₀
  have hu : Tendsto (fun d : ℕ => ((Real.log (2 + xiC0 σ) + jensenError σ d) / d +
      (Real.log (1 + θ₀) - (Real.log (jensenMass (xiMoment σ) d (θ₀ * cauchyScale d)) / d -
        Real.log (cauchyScale d)))) / L) atTop (𝓝 0) := by
    have := ((tendsto_jensenError_div σ (Real.log (2 + xiC0 σ))).add
      (hlaw.const_sub (Real.log (1 + θ₀)))).div_const L
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun d => by positivity) ?_ hu
  filter_upwards [eventually_sphere_bound hσ hR hRθ, eventually_jensenError_nonneg σ hσ,
    tendsto_cauchyScale.eventually_ge_atTop (1 / θ₀), tendsto_cauchyScale.eventually_gt_atTop 0,
    eventually_gt_atTop 0] with d hB hE hℓθ hℓ hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : 1 ≤ θ₀ * cauchyScale d := by
    rw [div_le_iff₀ hθ₀] at hℓθ
    linarith
  have hm := jensenMass_pos hσ d ht
  have hcenter := prod_norm_center (σ := σ) (θ₀ := θ₀) hℓ hm.le
  have hA1 := prod_max_le_center hR hRθ hB
  have hA2 := pow_mul_prod_norm_le (scaledRoots σ d) (I * (θ₀ : ℂ)) hr hrR.le
  set N := Multiset.card ((scaledRoots σ d).filter fun y => ‖I * (θ₀ : ℂ) - y‖ ≤ r)
  set P₀ := ((scaledRoots σ d).map fun y => ‖I * (θ₀ : ℂ) - y‖).prod
  set m := jensenMass (xiMoment σ) d (θ₀ * cauchyScale d)
  set ℓ := cauchyScale d
  set E := jensenError σ d
  have hℓd : 0 < ℓ ^ d := pow_pos hℓ d
  have h1θ : 0 < 1 + θ₀ := by linarith
  have hkey : (R / r) ^ N * m ≤ (2 + xiC0 σ) * Real.exp E * (1 + θ₀) ^ d * ℓ ^ d := by
    have h1 : (R / r) ^ N * P₀ ≤ (2 * Real.exp E + xiC0 σ) / ‖xi (σ : ℂ)‖ * (1 + θ₀) ^ d :=
      hA2.trans hA1
    have h2 : (2 * Real.exp E + xiC0 σ) * (1 + θ₀) ^ d ≤
        (2 + xiC0 σ) * Real.exp E * (1 + θ₀) ^ d :=
      mul_le_mul_of_nonneg_right (two_mul_exp_add_le hE hC₀) (by positivity)
    rw [← hcenter]
    have h3 : (R / r) ^ N * P₀ * ‖xi (σ : ℂ)‖ ≤ (2 * Real.exp E + xiC0 σ) * (1 + θ₀) ^ d := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hξ] at h1
      exact h1
    calc (R / r) ^ N * (‖xi (σ : ℂ)‖ * ℓ ^ d * P₀)
        = (R / r) ^ N * P₀ * ‖xi (σ : ℂ)‖ * ℓ ^ d := by ring
      _ ≤ (2 * Real.exp E + xiC0 σ) * (1 + θ₀) ^ d * ℓ ^ d :=
          mul_le_mul_of_nonneg_right h3 hℓd.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hℓd.le
  have hRr : 0 < R / r := by positivity
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by positivity) hm.ne', Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_mul h2C.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_pow, Real.log_pow] at hlog
  rw [div_le_div_iff₀ hdR hL]
  have hexpand : ((Real.log (2 + xiC0 σ) + E) / d + (Real.log (1 + θ₀) -
      (Real.log m / d - Real.log ℓ))) * d = Real.log (2 + xiC0 σ) + E +
        d * Real.log (1 + θ₀) - Real.log m + d * Real.log ℓ := by
    field_simp
    ring
  rw [hexpand]
  linarith

/-- **Few far roots.** For `T > 1` and large `d`, at most `(log 3 + 1)/log T · d` rescaled roots lie at
distance `≥ T` from `2i`. -/
theorem eventually_card_far_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) {T : ℝ} (hT : 1 < T) :
    ∀ᶠ d : ℕ in atTop,
      (Multiset.card ((scaledRoots σ d).filter fun y => T ≤ ‖I * ((2 : ℝ) : ℂ) - y‖) : ℝ) ≤
        (Real.log 3 + 1) / Real.log T * d := by
  have hC₀ := xiC0_nonneg σ
  have h2C : 0 < 2 + xiC0 σ := by linarith
  have hξ : 0 < ‖xi (σ : ℂ)‖ := norm_pos_iff.2 (xi_ne_zero_of_real σ)
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have herr := tendsto_jensenError_div σ (Real.log (2 + xiC0 σ) - Real.log ‖xi (σ : ℂ)‖)
  filter_upwards [eventually_sphere_bound hσ (θ₀ := 2) (R := 1) one_pos (by norm_num),
    eventually_jensenError_nonneg σ hσ, herr.eventually (gt_mem_nhds one_pos),
    eventually_gt_atTop 0] with d hB hE herrd hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hA1 := prod_max_le_center one_pos (by norm_num : (1 : ℝ) < 2) hB
  have hA3 := pow_le_prod_max (scaledRoots σ d) (I * ((2 : ℝ) : ℂ)) le_rfl hT.le
  set N := Multiset.card ((scaledRoots σ d).filter fun y => T ≤ ‖I * ((2 : ℝ) : ℂ) - y‖)
  set E := jensenError σ d
  have hkey : T ^ N * ‖xi (σ : ℂ)‖ ≤ (2 + xiC0 σ) * Real.exp E * 3 ^ d := by
    have h1 := hA3.trans hA1
    rw [show (1 : ℝ) + 2 = 3 by norm_num, div_mul_eq_mul_div, le_div_iff₀ hξ] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (two_mul_exp_add_le hE hC₀) (by positivity))
  have hT0 : 0 < T := by linarith
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by positivity) hξ.ne', Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_mul h2C.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_pow] at hlog
  rw [div_lt_one hdR] at herrd
  rw [div_mul_eq_mul_div, le_div_iff₀ hlogT]
  nlinarith

/-! ## The theorem -/

/-- **The upper half-plane is almost empty, unconditionally.** For `σ ≥ 1/2` and `ε > 0`, the proportion
of roots of `R_d(ξ(σ + i·))` with `Im x ≥ ε ½ log d` tends to `0`. -/
theorem tendsto_card_im_ge_div {σ : ℝ} (hσ : 1 / 2 ≤ σ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun d : ℕ =>
      (Multiset.card ((xiJensen σ d).roots.filter fun x => ε * cauchyScale d ≤ x.im) : ℝ) / d)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have h3 : 0 < Real.log 3 + 1 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 3)
    linarith
  set T := Real.exp (4 * (Real.log 3 + 1) / η)
  have hlogT : Real.log T = 4 * (Real.log 3 + 1) / η := Real.log_exp _
  have hT : 1 < T := Real.one_lt_exp_iff.2 (by positivity)
  have hfar : (Real.log 3 + 1) / Real.log T = η / 4 := by
    rw [hlogT]
    field_simp
  set A := T + 2
  have hA : 0 < A := by simp only [A]; linarith
  set θ₀ := A ^ 2 / ε + ε + 1
  have hA2 : 0 ≤ A ^ 2 / ε := by positivity
  have hθε : ε < θ₀ := by simp only [θ₀]; linarith
  have hθ₀ : 0 < θ₀ := by linarith
  have hθA : A ^ 2 ≤ θ₀ * ε := by
    have e : θ₀ * ε = A ^ 2 + ε ^ 2 + ε := by
      simp only [θ₀]
      field_simp
    rw [e]
    nlinarith
  have hrad : 0 < θ₀ ^ 2 - ε * θ₀ := by nlinarith
  set r := Real.sqrt (θ₀ ^ 2 - ε * θ₀)
  have hr : 0 < r := Real.sqrt_pos.2 hrad
  have hrθ : r < θ₀ := (Real.sqrt_lt' hθ₀).2 (by nlinarith)
  set R := (r + θ₀) / 2
  have hrR : r < R := by simp only [R]; linarith
  have hRθ : R < θ₀ := by simp only [R]; linarith
  filter_upwards [(Metric.tendsto_nhds.1 (tendsto_card_near_div hσ hr hrR hRθ)) (η / 2) (half_pos hη),
    eventually_card_far_le hσ hT, tendsto_cauchyScale.eventually_gt_atTop 0,
    eventually_gt_atTop 0] with d h1 h2 hℓ hd0
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1 ⊢
  rw [hfar] at h2
  have hcount : Multiset.card ((xiJensen σ d).roots.filter fun x => ε * cauchyScale d ≤ x.im) ≤
      Multiset.card ((scaledRoots σ d).filter fun y => ‖I * (θ₀ : ℂ) - y‖ ≤ r) +
        Multiset.card ((scaledRoots σ d).filter fun y => T ≤ ‖I * ((2 : ℝ) : ℂ) - y‖) := by
    rw [scaledRoots, Multiset.filter_map, Multiset.card_map, Multiset.filter_map, Multiset.card_map]
    refine card_filter_le_add _ fun x _ hx => ?_
    simp only [Function.comp_apply]
    set y := x / (cauchyScale d : ℂ)
    by_cases hS : T ≤ ‖I * ((2 : ℝ) : ℂ) - y‖
    · exact Or.inr hS
    · left
      push Not at hS
      have hyim : ε ≤ y.im := by
        simp only [y]
        rw [Complex.div_ofReal_im, le_div_iff₀ hℓ]
        exact hx
      have hynorm : ‖y‖ ≤ A := by
        have h2n : ‖I * ((2 : ℝ) : ℂ)‖ = 2 := by
          rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
        have hle : ‖y‖ ≤ ‖I * ((2 : ℝ) : ℂ)‖ + ‖I * ((2 : ℝ) : ℂ) - y‖ := by
          calc ‖y‖ = ‖I * ((2 : ℝ) : ℂ) - (I * ((2 : ℝ) : ℂ) - y)‖ := by congr 1; ring
            _ ≤ _ := norm_sub_le _ _
        rw [h2n] at hle
        simp only [A]
        linarith
      have hsq1 : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      have hsq2 : ‖I * (θ₀ : ℂ) - y‖ ^ 2 = y.re ^ 2 + (θ₀ - y.im) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp only [sub_re, sub_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul,
          one_mul, zero_add, zero_sub, sub_zero, mul_zero]
        ring
      have hyA : ‖y‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hynorm 2
      have hle : ‖I * (θ₀ : ℂ) - y‖ ^ 2 ≤ θ₀ ^ 2 - ε * θ₀ := by
        rw [hsq2]
        nlinarith
      exact (le_abs_self _).trans (Real.abs_le_sqrt hle)
  have hcountR : (Multiset.card ((xiJensen σ d).roots.filter fun x => ε * cauchyScale d ≤ x.im) : ℝ) ≤
      (Multiset.card ((scaledRoots σ d).filter fun y => ‖I * (θ₀ : ℂ) - y‖ ≤ r) : ℝ) +
        (Multiset.card ((scaledRoots σ d).filter fun y => T ≤ ‖I * ((2 : ℝ) : ℂ) - y‖) : ℝ) := by
    exact_mod_cast hcount
  rw [div_lt_iff₀ hdR] at h1 ⊢
  nlinarith

/-! ## The critical line -/

/-- `R_d(−w) = (−1)^d R_d(w)` at `σ = 1/2`. -/
theorem eval_xiJensen_half_neg (d : ℕ) (w : ℂ) :
    (xiJensen (1 / 2) d).eval (-w) = (-1) ^ d * (xiJensen (1 / 2) d).eval w := by
  rw [eval_xiJensen_eq_integral, eval_xiJensen_eq_integral, ← integral_const_mul]
  have h := integral_neg_eq_self (fun v : ℝ =>
    (-1 : ℂ) ^ d * (((riemannKernelReal v * Real.exp ((1 / 2 - 1 / 2) * v) : ℝ) : ℂ) *
      (w + I * v) ^ d)) volume
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [riemannKernel_superExp.even v, sub_self, zero_mul, Real.exp_zero, mul_one]
  rw [show -w + I * (v : ℂ) = -1 * (w + I * ((-v : ℝ) : ℂ)) by push_cast; ring, mul_pow]
  ring

/-- The roots of `R_d(Ξ)` are symmetric under `x ↦ −x`. -/
theorem roots_xiJensen_half_map_neg (d : ℕ) :
    (xiJensen (1 / 2) d).roots.map (fun x => -x) = (xiJensen (1 / 2) d).roots := by
  set q := xiJensen (1 / 2) d
  have hq0 : q.leadingCoeff ≠ 0 := by
    rw [leadingCoeff_xiJensen]
    exact xi_ne_zero_of_real _
  have hcard : Multiset.card q.roots = d := card_roots_xiJensen _ d
  have hsplit := (IsAlgClosed.splits q).eq_prod_roots
  have hneg : q = C q.leadingCoeff * ((q.roots.map fun x => -x).map fun a => X - C a).prod := by
    refine Polynomial.funext fun w => ?_
    have hone : ((-1 : ℂ) ^ d) * ((-1 : ℂ) ^ d) = 1 := by
      rw [← mul_pow]
      simp
    have hw : q.eval w = (-1) ^ d * q.eval (-w) := by
      rw [show q.eval (-w) = (-1) ^ d * q.eval w from eval_xiJensen_half_neg d w]
      linear_combination (-q.eval w) * hone
    have heval : q.eval (-w) = q.leadingCoeff * (q.roots.map fun x => -w - x).prod := by
      conv_lhs => rw [hsplit]
      rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
      simp only [Function.comp_def, eval_sub, eval_X, eval_C]
    have hprod : ∀ M : Multiset ℂ, (M.map fun x => -w - x).prod =
        (-1) ^ Multiset.card M * (M.map fun x => w - -x).prod := fun M => by
      induction M using Multiset.induction_on with
      | empty => simp
      | cons a M ih =>
        simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, ih, pow_succ]
        ring
    rw [hw, heval, hprod, hcard, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map,
      Multiset.map_map]
    simp only [Function.comp_def, eval_sub, eval_X, eval_C]
    linear_combination (q.leadingCoeff * (q.roots.map fun x => w - -x).prod) * hone
  conv_rhs => rw [hneg]
  rw [roots_C_mul _ hq0, roots_multiset_prod_X_sub_C]

/-- **Almost all roots of `R_d(ξ(1/2 + i·))` are nearly real, unconditionally.** -/
theorem tendsto_card_abs_im_ge_div_half {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun d : ℕ =>
      (Multiset.card ((xiJensen (1 / 2) d).roots.filter fun x => ε * cauchyScale d ≤ |x.im|) : ℝ) / d)
      atTop (𝓝 0) := by
  have hup := tendsto_card_im_ge_div (σ := 1 / 2) le_rfl hε
  have hsum := hup.const_mul 2
  rw [mul_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun d => by positivity)
    (Eventually.of_forall fun d => ?_) hsum
  have hsym : Multiset.card ((xiJensen (1 / 2) d).roots.filter fun x => x.im ≤ -(ε * cauchyScale d)) =
      Multiset.card ((xiJensen (1 / 2) d).roots.filter fun x => ε * cauchyScale d ≤ x.im) := by
    conv_lhs => rw [← roots_xiJensen_half_map_neg d]
    rw [Multiset.filter_map, Multiset.card_map]
    congr 1
    refine Multiset.filter_congr fun x _ => ?_
    simp only [Function.comp_apply, neg_im]
    constructor <;> intro h <;> linarith
  have hle := card_filter_le_add (xiJensen (1 / 2) d).roots
    (p := fun x => ε * cauchyScale d ≤ |x.im|) (q := fun x => ε * cauchyScale d ≤ x.im)
    (s := fun x => x.im ≤ -(ε * cauchyScale d)) fun x _ hx => by
      rcases le_abs.1 hx with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
  rw [hsym] at hle
  have hleR : (Multiset.card ((xiJensen (1 / 2) d).roots.filter
      fun x => ε * cauchyScale d ≤ |x.im|) : ℝ) ≤
      2 * (Multiset.card ((xiJensen (1 / 2) d).roots.filter
        fun x => ε * cauchyScale d ≤ x.im) : ℝ) := by
    have : ((Multiset.card ((xiJensen (1 / 2) d).roots.filter
        fun x => ε * cauchyScale d ≤ |x.im|) : ℕ) : ℝ) ≤
        ((Multiset.card ((xiJensen (1 / 2) d).roots.filter fun x => ε * cauchyScale d ≤ x.im) +
          Multiset.card ((xiJensen (1 / 2) d).roots.filter
            fun x => ε * cauchyScale d ≤ x.im) : ℕ) : ℝ) := by
      exact_mod_cast hle
    push_cast at this
    linarith
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hleR (Nat.cast_nonneg d)

/-- **Bulk hyperbolicity of the Jensen polynomials of `Ξ`.** For every `ε > 0`, unconditionally, the
proportion of roots `x` of the reversed Jensen polynomial `R_d(Ξ)` with `|Im x| ≥ ε ½ log d` tends to
`0`. -/
theorem tendsto_card_abs_im_ge_div_xiSeries {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun d : ℕ =>
      (Multiset.card ((jensenRev d xiSeries).roots.filter
        fun x => ε * (Real.log d / 2) ≤ |x.im|) : ℝ) / d) atTop (𝓝 0) := by
  have hmk : PowerSeries.mk (xiShiftCoeff (1 / 2)) = xiSeries := by
    ext k
    rw [PowerSeries.coeff_mk]
    exact xiShiftCoeff_half k
  have h := tendsto_card_abs_im_ge_div_half hε
  simp only [xiJensen, hmk] at h
  exact h

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.tendsto_card_im_ge_div
#print axioms FiniteFreeProbability.tendsto_card_abs_im_ge_div_xiSeries
