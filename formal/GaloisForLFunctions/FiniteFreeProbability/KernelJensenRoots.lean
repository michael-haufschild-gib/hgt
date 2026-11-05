import GaloisForLFunctions.FiniteFreeProbability.BulkHyperbolicity
import GaloisForLFunctions.FiniteFreeProbability.HermiteBiehlerCounting

/-!
# Almost all Jensen roots of an even kernel below `Φ` are real and simple

Let `g` be continuous, even, `0 ≤ g ≤ Φ`, with a double-exponential lower bound `g(v) ≥ exp(−A e^{2v})` for large
`v`, and let `R_d(x) = ∫ g(v)(x + iv)^d dv` be the reversed Jensen polynomials of its transform.

**Theorem.** For every `η > 0` and all large `d`, `R_d` has at least `(1 − η) d` distinct real roots, and the
proportion of non-real roots with multiplicity tends to `0`.

Mechanism. Since `g` is even, on the real axis `R_d = E_d + conj E_d = 2 Re E_d`, with the one-sided transform

`E_d(w) = ∫₀^∞ g(v) (w + iv)^d dv`.

The polynomial `E_d` has only `o(d)` roots in `Im ≥ 0`. Indeed on `Im ζ ≥ −1/2`, with `ℓ = ½ log d`, the bound
`|E_d(ℓζ)| ≤ ℓ^d |ζ + i|^d e^{o(d)}` holds (the endpoint `v = 0` does not yet dominate: `|ζ| ≤ |ζ + i|`), using
only `g ≤ Φ` and the Gamma cap of `ξ'/ξ`; it is sharp at `ζ = iθ` by the lower bound on `g`, and `log|ζ + i|` is
harmonic there. So Jensen's inequality applies on discs around `iθ` of radius up to `θ + 1/2`, which cross the
real axis and exhaust `Im ζ ≥ 0` as `θ → ∞`. Hence `Z₋(E_d) − Z₊(E_d) ≥ (1 − o(1)) d`, and the winding count
(`HermiteBiehlerCounting`) produces that many distinct real zeros of `Re E_d`.

Nothing arithmetic enters beyond the size of `g`: the theorem covers `Φ` and all its backward heat flows.
-/

open Polynomial Filter Topology Complex Metric MeasureTheory
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace FiniteFreeProbability

noncomputable section

/-- An even kernel below `Φ` with a double-exponential lower bound. -/
structure HyperbolicKernel (g : ℝ → ℝ) : Prop where
  continuous : Continuous g
  even : ∀ v, g (-v) = g v
  nonneg : ∀ v, 0 ≤ g v
  le_kernel : ∀ v, g v ≤ riemannKernelReal v
  lower : ∃ A v₁ : ℝ, 0 < A ∧ ∀ v, v₁ ≤ v → Real.exp (-(A * Real.exp (2 * v))) ≤ g v

theorem hyperbolicKernel_riemann : HyperbolicKernel riemannKernelReal where
  continuous := riemannKernel_superExp.continuous
  even := riemannKernel_superExp.even
  nonneg := riemannKernel_superExp.nonneg
  le_kernel := fun _ => le_rfl
  lower := ⟨Real.pi, 1, Real.pi_pos, fun _ hv => riemannKernelReal_ge hv⟩

/-- The backward heat flows of `Φ` are hyperbolic kernels. -/
theorem hyperbolicKernel_heat {τ : ℝ} (hτ : 0 ≤ τ) :
    HyperbolicKernel (fun x => riemannKernelReal x * Real.exp (-τ * x ^ 2)) where
  continuous := riemannKernel_superExp.continuous.mul (by fun_prop)
  even := fun x => by simp only [even_two.neg_pow, riemannKernel_superExp.even]
  nonneg := fun x => mul_nonneg (riemannKernel_superExp.nonneg x) (Real.exp_pos _).le
  le_kernel := fun x => by
    have h1 : Real.exp (-τ * x ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
    exact mul_le_of_le_one_right (riemannKernel_superExp.nonneg x) h1
  lower := by
    refine ⟨Real.pi + τ, 1, by linarith [Real.pi_pos], fun v hv => ?_⟩
    have hsq : v ^ 2 ≤ Real.exp (2 * v) := by
      have h1 : v ≤ Real.exp v := by linarith [Real.add_one_le_exp v]
      have h2 : Real.exp (2 * v) = Real.exp v ^ 2 := by rw [two_mul, Real.exp_add, sq]
      rw [h2]
      exact pow_le_pow_left₀ (by linarith) h1 2
    have hsplit : Real.exp (-((Real.pi + τ) * Real.exp (2 * v))) =
        Real.exp (-(Real.pi * Real.exp (2 * v))) * Real.exp (-(τ * Real.exp (2 * v))) := by
      rw [← Real.exp_add]
      ring_nf
    rw [hsplit]
    refine mul_le_mul (riemannKernelReal_ge hv) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      (riemannKernel_superExp.nonneg v)
    nlinarith

variable {g : ℝ → ℝ}

theorem HyperbolicKernel.integrable_pow_exp (hg : HyperbolicKernel g) (r : ℝ) (k : ℕ) :
    Integrable fun v : ℝ => g v * v ^ k * Real.exp (r * v) := by
  refine (integrable_kernel_pow_exp r k).mono
    ((hg.continuous.mul (by fun_prop)).mul (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (hg.nonneg v), abs_of_nonneg (riemannKernel_superExp.nonneg v)]
  have := hg.le_kernel v
  gcongr

theorem HyperbolicKernel.integrable_pow (hg : HyperbolicKernel g) (k : ℕ) :
    Integrable fun v : ℝ => g v * v ^ k := by
  refine (hg.integrable_pow_exp 0 k).congr (Eventually.of_forall fun v => ?_)
  simp

theorem HyperbolicKernel.integrable_exp (hg : HyperbolicKernel g) (r : ℝ) :
    Integrable fun v : ℝ => g v * Real.exp (r * v) := by
  refine (hg.integrable_pow_exp r 0).congr (Eventually.of_forall fun v => ?_)
  simp

theorem kernel_mul_add_I_pow_expand (g : ℝ → ℝ) (d : ℕ) (w : ℂ) (v : ℝ) :
    (g v : ℂ) * (w + I * v) ^ d =
      ∑ k ∈ Finset.range (d + 1), (d.choose k : ℂ) * w ^ (d - k) * I ^ k *
        ((g v * v ^ k : ℝ) : ℂ) := by
  rw [add_comm w, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pow]
  push_cast
  ring

theorem HyperbolicKernel.integrable_ofReal_pow (hg : HyperbolicKernel g) (k : ℕ) :
    Integrable fun v : ℝ => ((g v * v ^ k : ℝ) : ℂ) :=
  Complex.ofRealCLM.integrable_comp (hg.integrable_pow k)

theorem HyperbolicKernel.integrable_mul_add_I_pow (hg : HyperbolicKernel g) (d : ℕ) (w : ℂ) :
    Integrable fun v : ℝ => (g v : ℂ) * (w + I * v) ^ d := by
  simp_rw [kernel_mul_add_I_pow_expand]
  exact integrable_finsetSum _ fun k _ => (hg.integrable_ofReal_pow k).const_mul _

/-! ## Polynomials from moments -/

/-- `Σ_k C(d,k) i^k μ_k X^{d−k}`: the polynomial `E (X + iV)^d` for a moment sequence `μ`. -/
def momentJensen (μ : ℕ → ℝ) (d : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (d + 1), C ((d.choose k : ℂ) * I ^ k * (μ k : ℂ)) * X ^ (d - k)

theorem coeff_momentJensen_self (μ : ℕ → ℝ) (d : ℕ) : (momentJensen μ d).coeff d = (μ 0 : ℂ) := by
  rw [momentJensen, finsetSum_coeff, Finset.sum_eq_single 0]
  · rw [coeff_C_mul_X_pow, if_pos (by simp)]
    simp
  · intro k hk hk0
    have := Finset.mem_range.1 hk
    rw [coeff_C_mul_X_pow, if_neg (by omega)]
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.succ_pos d)) h

theorem natDegree_momentJensen {μ : ℕ → ℝ} (hμ : μ 0 ≠ 0) (d : ℕ) :
    (momentJensen μ d).natDegree = d := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · refine natDegree_sum_le_of_forall_le _ _ fun k _ => (natDegree_C_mul_X_pow_le _ _).trans ?_
    omega
  · rw [coeff_momentJensen_self]
    exact ofReal_ne_zero.2 hμ

theorem leadingCoeff_momentJensen {μ : ℕ → ℝ} (hμ : μ 0 ≠ 0) (d : ℕ) :
    (momentJensen μ d).leadingCoeff = (μ 0 : ℂ) := by
  rw [leadingCoeff, natDegree_momentJensen hμ, coeff_momentJensen_self]

theorem card_roots_momentJensen {μ : ℕ → ℝ} (hμ : μ 0 ≠ 0) (d : ℕ) :
    Multiset.card (momentJensen μ d).roots = d := by
  rw [← (IsAlgClosed.splits _).natDegree_eq_card_roots, natDegree_momentJensen hμ]

/-- `μ_k = ∫ g(v) v^k dv`. -/
def kernelMoment (g : ℝ → ℝ) (k : ℕ) : ℝ := ∫ v : ℝ, g v * v ^ k

/-- `c⁺_k = ∫₀^∞ g(v) v^k dv`. -/
def halfMoment (g : ℝ → ℝ) (k : ℕ) : ℝ := ∫ v in Set.Ioi (0 : ℝ), g v * v ^ k

/-- `R_d(w) = ∫ g(v)(w + iv)^d dv`, as a polynomial in `w`. -/
abbrev kernelJensen (g : ℝ → ℝ) (d : ℕ) : ℂ[X] := momentJensen (kernelMoment g) d

/-- `E_d(w) = ∫₀^∞ g(v)(w + iv)^d dv`, as a polynomial in `w`. -/
abbrev halfJensen (g : ℝ → ℝ) (d : ℕ) : ℂ[X] := momentJensen (halfMoment g) d

theorem HyperbolicKernel.eval_kernelJensen (hg : HyperbolicKernel g) (d : ℕ) (w : ℂ) :
    (kernelJensen g d).eval w = ∫ v : ℝ, (g v : ℂ) * (w + I * v) ^ d := by
  simp_rw [kernel_mul_add_I_pow_expand]
  rw [integral_finsetSum _ fun k _ => (hg.integrable_ofReal_pow k).const_mul _, kernelJensen,
    momentJensen, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_complex_ofReal, eval_mul, eval_C, eval_pow, eval_X, kernelMoment]
  ring

theorem HyperbolicKernel.eval_halfJensen (hg : HyperbolicKernel g) (d : ℕ) (w : ℂ) :
    (halfJensen g d).eval w = ∫ v in Set.Ioi (0 : ℝ), (g v : ℂ) * (w + I * v) ^ d := by
  simp_rw [kernel_mul_add_I_pow_expand]
  rw [integral_finsetSum _ fun k _ => ((hg.integrable_ofReal_pow k).const_mul _).integrableOn,
    halfJensen, momentJensen, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_complex_ofReal, eval_mul, eval_C, eval_pow, eval_X, halfMoment]
  ring

/-- **The splitting on the real axis.** `R_d(x) = E_d(x) + conj E_d(x)` for real `x`. -/
theorem HyperbolicKernel.eval_kernelJensen_real (hg : HyperbolicKernel g) (d : ℕ) (x : ℝ) :
    (kernelJensen g d).eval (x : ℂ) =
      (halfJensen g d).eval (x : ℂ) + conj ((halfJensen g d).eval (x : ℂ)) := by
  set f : ℝ → ℂ := fun v => (g v : ℂ) * ((x : ℂ) + I * v) ^ d
  have hf : Integrable f := hg.integrable_mul_add_I_pow d x
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (f := f) (b := 0)
    hf.integrableOn hf.integrableOn
  have hneg : ∫ v in Set.Iic (0 : ℝ), f v = ∫ v in Set.Ioi (0 : ℝ), conj (f v) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) f
    rw [neg_zero] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [f, hg.even v, map_mul, map_pow, map_add, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hg.eval_kernelJensen, ← hsplit, hneg, integral_conj, hg.eval_halfJensen]
  exact add_comm _ _

/-! ## The one-sided mass -/

/-- The one-sided mass `M_d(t) = ∫₀^∞ g(v)(t + v)^d dv`. -/
def halfMass (g : ℝ → ℝ) (d : ℕ) (t : ℝ) : ℝ := ∫ x in Set.Ioi (0 : ℝ), g x * (t + x) ^ d

theorem HyperbolicKernel.integrable_mul_add_pow (hg : HyperbolicKernel g) (t : ℝ) (d : ℕ) :
    Integrable fun x : ℝ => g x * (t + x) ^ d := by
  have hexp : ∀ x : ℝ, g x * (t + x) ^ d = ∑ k ∈ Finset.range (d + 1),
      (d.choose k : ℝ) * t ^ (d - k) * (g x * x ^ k) := fun x => by
    rw [add_comm t x, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  simp_rw [hexp]
  exact integrable_finsetSum _ fun k _ => (hg.integrable_pow k).const_mul _

/-- `M_d(t) ≥ (t + v)^d exp(−A e^{2(v+1)})` for `t ≥ 0`, `v` large. -/
theorem HyperbolicKernel.exists_halfMass_ge (hg : HyperbolicKernel g) :
    ∃ A v₁ : ℝ, 0 < A ∧ 1 ≤ v₁ ∧ ∀ (d : ℕ) (t v : ℝ), 0 ≤ t → v₁ ≤ v →
      (t + v) ^ d * Real.exp (-(A * Real.exp (2 * (v + 1)))) ≤ halfMass g d t := by
  obtain ⟨A, v₀, hA, hlow⟩ := hg.lower
  refine ⟨A, max v₀ 1, hA, le_max_right _ _, fun d t v ht hv => ?_⟩
  have hv0 : v₀ ≤ v := (le_max_left _ _).trans hv
  have hv1 : 1 ≤ v := (le_max_right _ _).trans hv
  set c₀ := (t + v) ^ d * Real.exp (-(A * Real.exp (2 * (v + 1))))
  have hint := hg.integrable_mul_add_pow t d
  have hsub : Set.Icc v (v + 1) ⊆ Set.Ioi (0 : ℝ) := fun x hx => by
    have := hx.1
    simp only [Set.mem_Ioi]
    linarith
  have hgx : ∀ x ∈ Set.Icc v (v + 1), Real.exp (-(A * Real.exp (2 * (v + 1)))) ≤ g x := fun x hx => by
    refine le_trans (Real.exp_le_exp.2 ?_) (hlow x (hv0.trans hx.1))
    have : Real.exp (2 * x) ≤ Real.exp (2 * (v + 1)) := Real.exp_le_exp.2 (by linarith [hx.2])
    nlinarith
  have hlowF : ∀ x ∈ Set.Icc v (v + 1), c₀ ≤ g x * (t + x) ^ d := fun x hx => by
    have h2 : (t + v) ^ d ≤ (t + x) ^ d :=
      pow_le_pow_left₀ (by linarith) (by linarith [hx.1]) d
    simp only [c₀]
    rw [mul_comm]
    exact mul_le_mul (hgx x hx) h2 (pow_nonneg (by linarith) d) (hg.nonneg x)
  have hset : ∫ _x in Set.Icc v (v + 1), c₀ ≤ ∫ x in Set.Icc v (v + 1), g x * (t + x) ^ d :=
    setIntegral_mono_on continuousOn_const.integrableOn_Icc hint.integrableOn measurableSet_Icc hlowF
  have hconst : ∫ _x in Set.Icc v (v + 1), c₀ = c₀ := by simp
  have hmono : ∫ x in Set.Icc v (v + 1), g x * (t + x) ^ d ≤ halfMass g d t := by
    refine setIntegral_mono_set hint.integrableOn ?_ (Eventually.of_forall hsub)
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
    have hx' : (0 : ℝ) < x := hx
    exact mul_nonneg (hg.nonneg x) (pow_nonneg (by linarith) d)
  rw [hconst] at hset
  linarith

theorem HyperbolicKernel.halfMoment_zero_pos (hg : HyperbolicKernel g) : 0 < halfMoment g 0 := by
  obtain ⟨A, v₁, _, hv₁, hmass⟩ := hg.exists_halfMass_ge
  have h := hmass 0 0 v₁ le_rfl le_rfl
  have he : halfMass g 0 0 = halfMoment g 0 := by
    simp [halfMass, halfMoment]
  rw [he] at h
  refine lt_of_lt_of_le ?_ h
  positivity

theorem HyperbolicKernel.kernelMoment_zero_pos (hg : HyperbolicKernel g) :
    0 < kernelMoment g 0 := by
  refine lt_of_lt_of_le hg.halfMoment_zero_pos ?_
  exact setIntegral_le_integral (hg.integrable_pow 0) (Eventually.of_forall fun v => by
    simpa using hg.nonneg v)

/-- At `w = it`, `E_d(it) = i^d M_d(t)`. -/
theorem HyperbolicKernel.eval_halfJensen_I_mul (hg : HyperbolicKernel g) (d : ℕ) (t : ℝ) :
    (halfJensen g d).eval (I * t) = I ^ d * (halfMass g d t : ℂ) := by
  rw [hg.eval_halfJensen, halfMass, ← integral_complex_ofReal, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  beta_reduce
  rw [show I * (t : ℂ) + I * v = I * ((t + v : ℝ) : ℂ) by push_cast; ring, mul_pow]
  push_cast
  ring

/-! ## The bound below the real axis -/

/-- `|ℓζ + iv| ≤ ℓ|ζ + i| + max(v, ℓ) − ℓ` for `v ≥ 0`, `Im ζ ≥ −1/2`. -/
theorem norm_mul_add_I_mul_le_half {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {z : ℂ} (hz : -(1 / 2) ≤ z.im) {v : ℝ}
    (hv : 0 ≤ v) : ‖(ℓ : ℂ) * z + I * v‖ ≤ ℓ * ‖z + I‖ + (max v ℓ - ℓ) := by
  set u := max v ℓ
  have hu1 : v ≤ u := le_max_left _ _
  have hu2 : ℓ ≤ u := le_max_right _ _
  have hb : -(ℓ / 2) ≤ ℓ * z.im := by nlinarith
  have step1 : ‖(ℓ : ℂ) * z + I * v‖ ≤ ‖(ℓ : ℂ) * z + I * u‖ := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
    apply Real.sqrt_le_sqrt
    simp only [add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, I_re, I_im, zero_mul, one_mul,
      zero_add, sub_zero, add_zero]
    have h2 : (ℓ * z.im + v) ^ 2 ≤ (ℓ * z.im + u) ^ 2 :=
      sq_le_sq' (by linarith) (by linarith)
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

theorem HyperbolicKernel.integrable_mul_norm_pow (hg : HyperbolicKernel g) (d : ℕ) (w : ℂ) :
    Integrable fun v : ℝ => g v * ‖w + I * v‖ ^ d := by
  refine (hg.integrable_mul_add_I_pow d w).norm.congr (Eventually.of_forall fun v => ?_)
  simp only
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hg.nonneg v)]

/-- `∫₀^∞ g(v)|ℓζ + iv|^d dv ≤ d!/r^d e^{tr} ξ(1/2 + r) + (ℓ|ζ + i|)^d c⁺₀`, with `t = ℓ(|ζ + i| − 1)`, on
`Im ζ ≥ −1/2`. -/
theorem HyperbolicKernel.setIntegral_mul_norm_pow_le (hg : HyperbolicKernel g) (d : ℕ) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) {z : ℂ} (hz : -(1 / 2) ≤ z.im) {r : ℝ} (hr : 0 < r) :
    ∫ v in Set.Ioi (0 : ℝ), g v * ‖(ℓ : ℂ) * z + I * v‖ ^ d ≤
      (d.factorial : ℝ) / r ^ d * (Real.exp (ℓ * (‖z + I‖ - 1) * r) * xiMoment (1 / 2 + r) 0) +
        (ℓ * ‖z + I‖) ^ d * halfMoment g 0 := by
  set t := ℓ * (‖z + I‖ - 1)
  have hfact : (0 : ℝ) < (d.factorial : ℝ) := by positivity
  set K : ℝ := (d.factorial : ℝ) / r ^ d * Real.exp (t * r)
  have hK : 0 ≤ K := by positivity
  set B := ℓ * ‖z + I‖
  have hB : 0 ≤ B := by positivity
  have hpt : ∀ v ∈ Set.Ioi (0 : ℝ), g v * ‖(ℓ : ℂ) * z + I * v‖ ^ d ≤
      K * (g v * Real.exp (r * v)) + B ^ d * (g v * v ^ 0) := fun v hv => by
    have hv0 : (0 : ℝ) < v := hv
    have hΦ := hg.nonneg v
    have hn := norm_mul_add_I_mul_le_half hℓ hz hv0.le
    rw [pow_zero, mul_one]
    have hexp := Real.exp_pos (r * v)
    rcases le_total v ℓ with hvℓ | hvℓ
    · have hle : ‖(ℓ : ℂ) * z + I * v‖ ≤ B := by
        rw [max_eq_right hvℓ] at hn
        simp only [B]
        linarith
      have hp := pow_le_pow_left₀ (norm_nonneg _) hle d
      have h1 : 0 ≤ K * (g v * Real.exp (r * v)) := by positivity
      have h2 := mul_le_mul_of_nonneg_left hp hΦ
      nlinarith
    · have hle : ‖(ℓ : ℂ) * z + I * v‖ ≤ t + v := by
        rw [max_eq_left hvℓ] at hn
        simp only [t]
        linarith
      have htv : 0 ≤ t + v := (norm_nonneg _).trans hle
      have hp := pow_le_pow_left₀ (norm_nonneg _) hle d
      have hexpb := Real.pow_div_factorial_le_exp ((t + v) * r) (by positivity) d
      rw [div_le_iff₀ hfact, mul_pow] at hexpb
      have hpow : (t + v) ^ d ≤ K * Real.exp (r * v) := by
        simp only [K]
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity), mul_assoc,
          ← Real.exp_add, show t * r + r * v = (t + v) * r by ring, mul_comm]
        linarith
      have h1 : 0 ≤ B ^ d * g v := by positivity
      have h2 := mul_le_mul_of_nonneg_left (hp.trans hpow) hΦ
      nlinarith
  have hE := hg.integrable_exp r
  have hM := hg.integrable_pow 0
  have hmono := setIntegral_mono_on (hg.integrable_mul_norm_pow d _).integrableOn
    ((hE.const_mul K).add (hM.const_mul (B ^ d))).integrableOn measurableSet_Ioi hpt
  rw [integral_add' (hE.const_mul K).integrableOn (hM.const_mul (B ^ d)).integrableOn] at hmono
  simp only [integral_const_mul] at hmono
  have hup : ∫ v in Set.Ioi (0 : ℝ), g v * Real.exp (r * v) ≤ xiMoment (1 / 2 + r) 0 := by
    have hmom : xiMoment (1 / 2 + r) 0 = ∫ v, riemannKernelReal v * Real.exp (r * v) := by
      rw [xiMoment]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      simp
    have hΦE : Integrable fun v : ℝ => riemannKernelReal v * Real.exp (r * v) := by
      refine (integrable_kernel_pow_exp r 0).congr (Eventually.of_forall fun v => ?_)
      simp
    rw [hmom]
    refine (setIntegral_le_integral hE (Eventually.of_forall fun v =>
      mul_nonneg (hg.nonneg v) (Real.exp_pos _).le)).trans ?_
    exact integral_mono hE hΦE fun v =>
      mul_le_mul_of_nonneg_right (hg.le_kernel v) (Real.exp_pos _).le
  refine hmono.trans ?_
  have h1 := mul_le_mul_of_nonneg_left hup hK
  have hK' : K * xiMoment (1 / 2 + r) 0 =
      (d.factorial : ℝ) / r ^ d * (Real.exp (t * r) * xiMoment (1 / 2 + r) 0) := by
    simp only [K]
    ring
  rw [← hK', halfMoment]
  linarith

/-! ## The rescaled roots of the one-sided transform -/

/-- The rescaled roots `e/ℓ_d` of `E_d`. -/
def halfRoots (g : ℝ → ℝ) (d : ℕ) : Multiset ℂ :=
  (halfJensen g d).roots.map fun x => x / (cauchyScale d : ℂ)

theorem HyperbolicKernel.card_halfRoots (hg : HyperbolicKernel g) (d : ℕ) :
    Multiset.card (halfRoots g d) = d := by
  rw [halfRoots, Multiset.card_map, card_roots_momentJensen hg.halfMoment_zero_pos.ne']

theorem HyperbolicKernel.eval_halfJensen_eq_prod (hg : HyperbolicKernel g) (d : ℕ)
    (hℓ : cauchyScale d ≠ 0) (z : ℂ) :
    (halfJensen g d).eval ((cauchyScale d : ℂ) * z) =
      (halfMoment g 0 : ℂ) * (cauchyScale d : ℂ) ^ d *
        ((halfRoots g d).map fun y => z - y).prod := by
  have hℓ' : (cauchyScale d : ℂ) ≠ 0 := ofReal_ne_zero.2 hℓ
  have hμ := hg.halfMoment_zero_pos.ne'
  conv_lhs => rw [(IsAlgClosed.splits (halfJensen g d)).eq_prod_roots]
  rw [leadingCoeff_momentJensen hμ, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, halfRoots,
    Multiset.map_map]
  have := multiset_prod_mul_sub (halfJensen g d).roots hℓ' z
  rw [card_roots_momentJensen hμ] at this
  simp only [Function.comp_def, eval_sub, eval_X, eval_C]
  rw [this, mul_assoc]

/-- The error exponent of the one-sided bound. -/
def halfError (d : ℕ) : ℝ :=
  Real.log (xiMoment (1 / 2 + 1) 0) + 6 * ((d : ℝ) / cauchyScale d) + 1 + cauchyScale d

/-- On circles centred at `iθ₀` of radius `R < θ₀ + 1/2`, which may cross the real axis,
`∫₀^∞ g(v)|ℓz + iv|^d dv ≤ ℓ^d |z + i|^d (e^{E_d} + c⁺₀)`, uniformly, for large `d`. -/
theorem HyperbolicKernel.eventually_setIntegral_norm_le (hg : HyperbolicKernel g) {θ₀ R : ℝ}
    (hθ₀ : 0 < θ₀) (hR : 0 < R) (hRθ : R < θ₀ + 1 / 2) :
    ∀ᶠ d : ℕ in atTop, ∀ z ∈ sphere (I * (θ₀ : ℂ)) R,
      ∫ v in Set.Ioi (0 : ℝ), g v * ‖(cauchyScale d : ℂ) * z + I * v‖ ^ d ≤
        cauchyScale d ^ d * (‖z + I‖ ^ d * (Real.exp (halfError d) + halfMoment g 0)) := by
  have hA : (0 : ℝ) < 1 / (1 + θ₀ + R) := by positivity
  filter_upwards [tendsto_cauchyScale.eventually_ge_atTop 2,
    tendsto_cauchyScale_div.eventually (gt_mem_nhds hA), eventually_ge_atTop 1] with
    d hℓ2 hℓd hd1 z hzs
  have hℓ1 : 1 ≤ cauchyScale d := by linarith
  have hdef : halfError d = Real.log (xiMoment (1 / 2 + 1) 0) + 6 * ((d : ℝ) / cauchyScale d) + 1 +
      cauchyScale d := rfl
  set ℓ := cauchyScale d
  have hℓ : 0 < ℓ := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hzn : ‖z - I * (θ₀ : ℂ)‖ = R := mem_sphere_iff_norm.1 hzs
  have hzim : θ₀ - R ≤ z.im := by
    have h := Complex.abs_im_le_norm (z - I * (θ₀ : ℂ))
    rw [hzn] at h
    have h2 := (abs_le.1 h).1
    simp only [sub_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, zero_mul, one_mul, zero_add] at h2
    linarith
  have hz12 : -(1 / 2) ≤ z.im := by linarith
  set θ := ‖z + I‖ - 1
  have hnorm1 : 1 + θ = ‖z + I‖ := by
    simp only [θ]
    ring
  have hθlow : 1 / 2 ≤ 1 + θ := by
    have h := Complex.abs_im_le_norm (z + I)
    simp only [add_im, I_im] at h
    have := le_abs_self (z.im + 1)
    rw [hnorm1]
    linarith
  have hθup : 1 + θ ≤ 1 + θ₀ + R := by
    have hsum : z + I = (z - I * (θ₀ : ℂ)) + I * ((θ₀ + 1 : ℝ) : ℂ) := by
      push_cast
      ring
    have h : ‖z + I‖ ≤ R + (θ₀ + 1) := by
      rw [hsum]
      refine (norm_add_le _ _).trans ?_
      rw [hzn, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
        Real.norm_of_nonneg (by linarith)]
    rw [hnorm1]
    linarith
  have h1θ : 0 < 1 + θ := by linarith
  have hdenom : 0 < (1 + θ) * ℓ := by positivity
  set r : ℝ := (d : ℝ) / ((1 + θ) * ℓ)
  have hr1 : 1 ≤ r := by
    rw [le_div_iff₀ hdenom]
    rw [div_lt_div_iff₀ hdR (by positivity)] at hℓd
    nlinarith
  have hrpos : 0 < r := by linarith
  have hden1 : 1 ≤ (1 + θ) * ℓ := by nlinarith
  have hrled : r ≤ d := by
    simp only [r]
    exact div_le_self hdR.le hden1
  have hwd : (1 / 2 : ℝ) - 1 / 2 + r ≤ d := by linarith
  have hS : Real.log ((d.factorial : ℝ) / r ^ d * (Real.exp (θ * ℓ * r) * xiMoment (1 / 2 + r) 0)) ≤
      Real.log (xiMoment (1 / 2 + 1) 0) + (1 / 2 - 1 / 2) * 3 + (1 / 2 - 1 / 2) * ℓ + 3 * r + 1 + ℓ +
        d * Real.log (1 + θ) + d * Real.log ℓ :=
    log_saddle_le (by norm_num) (by linarith) hd1 hℓ1 hr1 hwd
  have hc0 : 0 < xiMoment (1 / 2 + r) 0 := xiMoment_zero_pos _
  have hfact : (0 : ℝ) < (d.factorial : ℝ) := by positivity
  set S : ℝ := (d.factorial : ℝ) / r ^ d * (Real.exp (θ * ℓ * r) * xiMoment (1 / 2 + r) 0)
  have hSpos : 0 < S := by positivity
  have h3r : 3 * r ≤ 6 * ((d : ℝ) / ℓ) := by
    have hr2 : r ≤ 2 * ((d : ℝ) / ℓ) := by
      simp only [r]
      rw [mul_div_assoc', div_le_div_iff₀ hdenom hℓ]
      nlinarith [mul_nonneg (mul_nonneg hdR.le hℓ.le) (by linarith : 0 ≤ 2 * (1 + θ) - 1)]
    linarith
  set E := halfError d
  have hE : Real.log S ≤ E + d * Real.log (1 + θ) + d * Real.log ℓ := by
    rw [hdef]
    linarith
  have hSle : S ≤ Real.exp E * (1 + θ) ^ d * ℓ ^ d := by
    calc S = Real.exp (Real.log S) := (Real.exp_log hSpos).symm
      _ ≤ Real.exp (E + d * Real.log (1 + θ) + d * Real.log ℓ) := Real.exp_le_exp.2 hE
      _ = _ := by rw [Real.exp_add, Real.exp_add, exp_nat_mul_log h1θ, exp_nat_mul_log hℓ]
  have hN := hg.setIntegral_mul_norm_pow_le d hℓ.le hz12 hrpos
  have e1 : ℓ * (‖z + I‖ - 1) = θ * ℓ := mul_comm _ _
  have e2 : (ℓ * ‖z + I‖) ^ d = (1 + θ) ^ d * ℓ ^ d := by
    rw [← hnorm1, ← mul_pow]
    congr 1
    ring
  rw [e1, e2] at hN
  rw [← hnorm1]
  refine hN.trans ?_
  linarith [hSle, show ℓ ^ d * ((1 + θ) ^ d * (Real.exp E + halfMoment g 0)) =
    Real.exp E * (1 + θ) ^ d * ℓ ^ d + (1 + θ) ^ d * ℓ ^ d * halfMoment g 0 by ring]

/-- On circles centred at `iθ₀` of radius `R < θ₀ + 1/2`, which may cross the real axis,
`|Π_y (z − y)| ≤ (e^{E_d} + c⁺₀)/c⁺₀ · |z + i|^d`, uniformly, for large `d`. -/
theorem HyperbolicKernel.eventually_half_sphere_bound (hg : HyperbolicKernel g) {θ₀ R : ℝ}
    (hθ₀ : 0 < θ₀) (hR : 0 < R) (hRθ : R < θ₀ + 1 / 2) :
    ∀ᶠ d : ℕ in atTop, ∀ z ∈ sphere (I * (θ₀ : ℂ)) R,
      ‖((halfRoots g d).map fun y => z - y).prod‖ ≤
        (Real.exp (halfError d) + halfMoment g 0) / halfMoment g 0 * ‖z + I‖ ^ d := by
  have hc₀ := hg.halfMoment_zero_pos
  filter_upwards [hg.eventually_setIntegral_norm_le hθ₀ hR hRθ,
    tendsto_cauchyScale.eventually_gt_atTop 0] with d hbound hℓ z hzs
  have hN := hbound z hzs
  have hprod := hg.eval_halfJensen_eq_prod d hℓ.ne' z
  have hnormeval : ‖(halfJensen g d).eval ((cauchyScale d : ℂ) * z)‖ =
      halfMoment g 0 * cauchyScale d ^ d * ‖((halfRoots g d).map fun y => z - y).prod‖ := by
    rw [hprod, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hℓ.le, Real.norm_of_nonneg hc₀.le]
  have hle : ‖(halfJensen g d).eval ((cauchyScale d : ℂ) * z)‖ ≤
      ∫ v in Set.Ioi (0 : ℝ), g v * ‖(cauchyScale d : ℂ) * z + I * v‖ ^ d := by
    rw [hg.eval_halfJensen]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (hg.nonneg v)]
  rw [hnormeval] at hle
  have hℓd' : 0 < cauchyScale d ^ d := pow_pos hℓ d
  have hmain : cauchyScale d ^ d * (halfMoment g 0 * ‖((halfRoots g d).map fun y => z - y).prod‖) ≤
      cauchyScale d ^ d * ((Real.exp (halfError d) + halfMoment g 0) * ‖z + I‖ ^ d) := by
    calc _ = halfMoment g 0 * cauchyScale d ^ d * ‖((halfRoots g d).map fun y => z - y).prod‖ := by
          ring
      _ ≤ _ := hle.trans hN
      _ = _ := by ring
  have hfin := le_of_mul_le_mul_left hmain hℓd'
  rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]
  linarith

theorem tendsto_halfError_div (c : ℝ) :
    Tendsto (fun d : ℕ => (c + halfError d) / d) atTop (𝓝 0) := by
  have h := ((tendsto_const_div_atTop_nhds_zero_nat
    (c + Real.log (xiMoment (1 / 2 + 1) 0) + 1)).add
    (tendsto_one_div_cauchyScale.const_mul 6)).add tendsto_cauchyScale_div
  have hlim : (0 : ℝ) + 6 * 0 + 0 = 0 := by ring
  rw [hlim] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0, tendsto_cauchyScale.eventually_gt_atTop 0] with d hd hℓ
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [halfError]
  field_simp
  ring

theorem eventually_halfError_nonneg : ∀ᶠ d : ℕ in atTop, 0 ≤ halfError d := by
  have hK := tendsto_cauchyScale.eventually_ge_atTop (-Real.log (xiMoment (1 / 2 + 1) 0))
  filter_upwards [hK, tendsto_cauchyScale.eventually_gt_atTop 0] with d h1 h2
  simp only [halfError]
  have h5 : 0 ≤ 6 * ((d : ℝ) / cauchyScale d) := by positivity
  linarith

theorem exp_add_le_of_nonneg {E C : ℝ} (hE : 0 ≤ E) (hC : 0 ≤ C) :
    Real.exp E + C ≤ (1 + C) * Real.exp E := by
  have := Real.one_le_exp hE
  nlinarith

/-- Jensen for the one-sided rescaled roots. -/
theorem HyperbolicKernel.prod_max_le_half_center (hg : HyperbolicKernel g) {θ₀ R : ℝ} (hθ₀ : 0 < θ₀)
    (hR : 0 < R) (hRθ : R < θ₀ + 1) {d : ℕ} {B : ℝ} (hB : ∀ z ∈ sphere (I * (θ₀ : ℂ)) R,
      ‖((halfRoots g d).map fun y => z - y).prod‖ ≤ B * ‖z + I‖ ^ d) :
    ((halfRoots g d).map fun y => max R ‖I * (θ₀ : ℂ) - y‖).prod ≤ B * (1 + θ₀) ^ d := by
  have hnorm : ‖I * (θ₀ : ℂ) - -I‖ = 1 + θ₀ := by
    rw [show I * (θ₀ : ℂ) - -I = I * ((1 + θ₀ : ℝ) : ℂ) by
      push_cast
      ring, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have ha : -I ∉ closedBall (I * (θ₀ : ℂ)) R := by
    rw [mem_closedBall, dist_comm, dist_eq_norm, hnorm]
    linarith
  have h := multiset_prod_max_le hR ha (halfRoots g d) (B := B) (fun z hz => by
    rw [hg.card_halfRoots, sub_neg_eq_add]
    exact hB z hz)
  rwa [hg.card_halfRoots, hnorm] at h

/-- At the centre, `c⁺₀ ℓ^d Π_y |iθ₀ − y| = M_d(θ₀ℓ)`. -/
theorem HyperbolicKernel.prod_norm_half_center (hg : HyperbolicKernel g) {θ₀ : ℝ} {d : ℕ}
    (hℓ : 0 < cauchyScale d) (hm : 0 ≤ halfMass g d (θ₀ * cauchyScale d)) :
    halfMoment g 0 * cauchyScale d ^ d * ((halfRoots g d).map fun y => ‖I * (θ₀ : ℂ) - y‖).prod =
      halfMass g d (θ₀ * cauchyScale d) := by
  have h := hg.eval_halfJensen_eq_prod d hℓ.ne' (I * (θ₀ : ℂ))
  have harg : (cauchyScale d : ℂ) * (I * (θ₀ : ℂ)) = I * ((θ₀ * cauchyScale d : ℝ) : ℂ) := by
    push_cast
    ring
  rw [harg, hg.eval_halfJensen_I_mul] at h
  have hn := congrArg norm h
  rw [norm_mul, norm_pow, Complex.norm_I, one_pow, one_mul, Complex.norm_real,
    Real.norm_of_nonneg hm, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg hℓ.le, Real.norm_of_nonneg hg.halfMoment_zero_pos.le,
    norm_multiset_prod_map] at hn
  exact hn.symm

/-! ## Counting the roots of the one-sided transform -/

/-- **Few roots of `E_d` in a disc around `iθ₀`**, for `0 < r < R < θ₀ + 1/2`. -/
theorem HyperbolicKernel.tendsto_card_half_near_div (hg : HyperbolicKernel g) {θ₀ r R : ℝ}
    (hθ₀ : 0 < θ₀) (hr : 0 < r) (hrR : r < R) (hRθ : R < θ₀ + 1 / 2) :
    Tendsto (fun d : ℕ =>
      (Multiset.card ((halfRoots g d).filter fun y => ‖I * (θ₀ : ℂ) - y‖ ≤ r) : ℝ) / d)
      atTop (𝓝 0) := by
  have hR : 0 < R := by linarith
  have hc₀ := hg.halfMoment_zero_pos
  have h1C : 0 < 1 + halfMoment g 0 := by linarith
  have h1θ : 0 < 1 + θ₀ := by linarith
  obtain ⟨A, v₁, hA, hv₁, hmass⟩ := hg.exists_halfMass_ge
  set L := Real.log (R / r)
  have hL : 0 < L := Real.log_pos ((one_lt_div hr).2 hrR)
  have hu : Tendsto (fun d : ℕ => 1 - Real.log (cauchyScale d) / cauchyScale d / (1 + θ₀)) atTop
      (𝓝 1) := by
    have := (tendsto_log_cauchyScale_div.div_const (1 + θ₀)).const_sub 1
    simpa using this
  have hlogu := (Real.continuousAt_log one_ne_zero).tendsto.comp hu
  rw [Real.log_one] at hlogu
  have hbound : Tendsto (fun d : ℕ => ((Real.log (1 + halfMoment g 0) + halfError d) / d -
      Real.log (1 - Real.log (cauchyScale d) / cauchyScale d / (1 + θ₀)) +
      A * Real.exp 2 * (1 / cauchyScale d) ^ 2) / L) atTop (𝓝 0) := by
    have := (((tendsto_halfError_div (Real.log (1 + halfMoment g 0))).sub hlogu).add
      ((tendsto_one_div_cauchyScale.pow 2).const_mul (A * Real.exp 2))).div_const L
    simpa [Function.comp_def] using this
  refine squeeze_zero' (Eventually.of_forall fun d => by positivity) ?_ hbound
  filter_upwards [hg.eventually_half_sphere_bound hθ₀ hR hRθ, eventually_halfError_nonneg,
    tendsto_cauchyScale.eventually_ge_atTop (2 * v₁), eventually_gt_atTop 0] with d hB hE hℓ2 hd
  have hℓ : 0 < cauchyScale d := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hlogℓ : Real.log (cauchyScale d) ≤ cauchyScale d / 2 := by
    have h := Real.log_le_sub_one_of_pos (x := cauchyScale d / 2) (by positivity)
    rw [Real.log_div hℓ.ne' two_ne_zero] at h
    have := Real.log_two_lt_d9
    linarith
  have hlogℓ0 : 0 ≤ Real.log (cauchyScale d) := Real.log_nonneg (by linarith)
  set v := cauchyScale d - Real.log (cauchyScale d)
  have hv1 : v₁ ≤ v := by simp only [v]; linarith
  have hv0 : 0 < v := by linarith
  have hge := hmass d (θ₀ * cauchyScale d) v (by positivity) hv1
  have hmpos : 0 < halfMass g d (θ₀ * cauchyScale d) := by
    refine lt_of_lt_of_le ?_ hge
    have : 0 < θ₀ * cauchyScale d + v := by positivity
    positivity
  have hcenter := hg.prod_norm_half_center (θ₀ := θ₀) hℓ hmpos.le
  have hA1 := hg.prod_max_le_half_center hθ₀ hR (by linarith) hB
  have hA2 := pow_mul_prod_norm_le (halfRoots g d) (I * (θ₀ : ℂ)) hr hrR.le
  set N := Multiset.card ((halfRoots g d).filter fun y => ‖I * (θ₀ : ℂ) - y‖ ≤ r)
  set P₀ := ((halfRoots g d).map fun y => ‖I * (θ₀ : ℂ) - y‖).prod
  set m := halfMass g d (θ₀ * cauchyScale d)
  set ℓ := cauchyScale d
  set E := halfError d
  have hℓd : 0 < ℓ ^ d := pow_pos hℓ d
  have hkey : (R / r) ^ N * m ≤ (1 + halfMoment g 0) * Real.exp E * (1 + θ₀) ^ d * ℓ ^ d := by
    have h1 : (R / r) ^ N * P₀ ≤ (Real.exp E + halfMoment g 0) / halfMoment g 0 * (1 + θ₀) ^ d :=
      hA2.trans hA1
    have h2 : (Real.exp E + halfMoment g 0) * (1 + θ₀) ^ d ≤
        (1 + halfMoment g 0) * Real.exp E * (1 + θ₀) ^ d :=
      mul_le_mul_of_nonneg_right (exp_add_le_of_nonneg hE hc₀.le) (by positivity)
    rw [← hcenter]
    have h3 : (R / r) ^ N * P₀ * halfMoment g 0 ≤ (Real.exp E + halfMoment g 0) * (1 + θ₀) ^ d := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc₀] at h1
      exact h1
    calc (R / r) ^ N * (halfMoment g 0 * ℓ ^ d * P₀)
        = (R / r) ^ N * P₀ * halfMoment g 0 * ℓ ^ d := by ring
      _ ≤ (Real.exp E + halfMoment g 0) * (1 + θ₀) ^ d * ℓ ^ d :=
          mul_le_mul_of_nonneg_right h3 hℓd.le
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hℓd.le
  have hRr : 0 < R / r := by positivity
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by positivity) hmpos.ne', Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul h1C.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_pow, Real.log_pow] at hlog
  -- the lower bound for `m`
  set X := θ₀ * ℓ + v
  have hX : 0 < X := by positivity
  have hexp : Real.exp (2 * (v + 1)) = Real.exp 2 * ((d : ℝ) * (1 / ℓ) ^ 2) := by
    have hd2 : Real.exp (2 * ℓ) = (d : ℝ) := by
      rw [show 2 * ℓ = Real.log d by simp only [ℓ, cauchyScale]; ring, Real.exp_log hdR]
    have hl : Real.exp (-(2 * Real.log ℓ)) = (1 / ℓ) ^ 2 := by
      rw [show -(2 * Real.log ℓ) = Real.log ((1 / ℓ) ^ 2) by
        rw [Real.log_pow, one_div, Real.log_inv]
        push_cast
        ring, Real.exp_log (by positivity)]
    rw [show 2 * (v + 1) = 2 + (2 * ℓ + -(2 * Real.log ℓ)) by simp only [v]; ring, Real.exp_add,
      Real.exp_add, hd2, hl]
  have hlogm := Real.log_le_log (by positivity) hge
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp, hexp] at hlogm
  have hXeq : X = (1 + θ₀) * ℓ * (1 - Real.log ℓ / ℓ / (1 + θ₀)) := by
    simp only [X, v]
    field_simp
    ring
  have hu0 : 0 < 1 - Real.log ℓ / ℓ / (1 + θ₀) := by
    have h := hX
    rw [hXeq] at h
    exact (pos_iff_pos_of_mul_pos h).1 (by positivity)
  have hlogX : Real.log X = Real.log (1 + θ₀) + Real.log ℓ +
      Real.log (1 - Real.log ℓ / ℓ / (1 + θ₀)) := by
    rw [hXeq, Real.log_mul (by positivity) hu0.ne', Real.log_mul h1θ.ne' hℓ.ne']
  rw [hlogX] at hlogm
  rw [div_le_div_iff₀ hdR hL]
  have hexpand : ((Real.log (1 + halfMoment g 0) + E) / d -
      Real.log (1 - Real.log ℓ / ℓ / (1 + θ₀)) + A * Real.exp 2 * (1 / ℓ) ^ 2) * d =
        Real.log (1 + halfMoment g 0) + E - d * Real.log (1 - Real.log ℓ / ℓ / (1 + θ₀)) +
          A * (Real.exp 2 * (d * (1 / ℓ) ^ 2)) := by
    field_simp
  rw [hexpand]
  nlinarith

/-- **Few far roots of `E_d`.** -/
theorem HyperbolicKernel.eventually_card_half_far_le (hg : HyperbolicKernel g) {T : ℝ} (hT : 1 < T) :
    ∀ᶠ d : ℕ in atTop,
      (Multiset.card ((halfRoots g d).filter fun y => T ≤ ‖I * ((2 : ℝ) : ℂ) - y‖) : ℝ) ≤
        (Real.log 3 + 1) / Real.log T * d := by
  have hc₀ := hg.halfMoment_zero_pos
  have h1C : 0 < 1 + halfMoment g 0 := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have herr := tendsto_halfError_div (Real.log (1 + halfMoment g 0) - Real.log (halfMoment g 0))
  filter_upwards [hg.eventually_half_sphere_bound (θ₀ := 2) (R := 1) two_pos one_pos (by norm_num),
    eventually_halfError_nonneg, herr.eventually (gt_mem_nhds one_pos),
    eventually_gt_atTop 0] with d hB hE herrd hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hA1 := hg.prod_max_le_half_center two_pos one_pos (by norm_num) hB
  have hA3 := pow_le_prod_max (halfRoots g d) (I * ((2 : ℝ) : ℂ)) le_rfl hT.le
  set N := Multiset.card ((halfRoots g d).filter fun y => T ≤ ‖I * ((2 : ℝ) : ℂ) - y‖)
  set E := halfError d
  have hkey : T ^ N * halfMoment g 0 ≤ (1 + halfMoment g 0) * Real.exp E * 3 ^ d := by
    have h1 := hA3.trans hA1
    rw [show (1 : ℝ) + 2 = 3 by norm_num, div_mul_eq_mul_div, le_div_iff₀ hc₀] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (exp_add_le_of_nonneg hE hc₀.le) (by positivity))
  have hT0 : 0 < T := by linarith
  have hlog := Real.log_le_log (by positivity) hkey
  rw [Real.log_mul (by positivity) hc₀.ne', Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_mul h1C.ne' (Real.exp_pos _).ne',
    Real.log_exp, Real.log_pow] at hlog
  rw [div_lt_one hdR] at herrd
  rw [div_mul_eq_mul_div, le_div_iff₀ hlogT]
  nlinarith

/-- **Almost no root of `E_d` lies in `Im ≥ 0`.** -/
theorem HyperbolicKernel.eventually_card_im_nonneg_halfJensen_le (hg : HyperbolicKernel g) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop,
      (Multiset.card ((halfJensen g d).roots.filter fun e => 0 ≤ e.im) : ℝ) ≤ η * d := by
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
  set θ₀ := 2 * A ^ 2 + 1
  have hθ₀ : 0 < θ₀ := by positivity
  filter_upwards [(Metric.tendsto_nhds.1 (hg.tendsto_card_half_near_div (θ₀ := θ₀) (r := θ₀ + 1 / 4)
      (R := θ₀ + 3 / 8) hθ₀ (by positivity) (by linarith) (by linarith))) (η / 2) (half_pos hη),
    hg.eventually_card_half_far_le hT, tendsto_cauchyScale.eventually_gt_atTop 0,
    eventually_gt_atTop 0] with d h1 h2 hℓ hd0
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h1
  rw [hfar] at h2
  have hcount : Multiset.card ((halfJensen g d).roots.filter fun e => 0 ≤ e.im) ≤
      Multiset.card ((halfRoots g d).filter fun y => ‖I * (θ₀ : ℂ) - y‖ ≤ θ₀ + 1 / 4) +
        Multiset.card ((halfRoots g d).filter fun y => T ≤ ‖I * ((2 : ℝ) : ℂ) - y‖) := by
    rw [halfRoots, Multiset.filter_map, Multiset.card_map, Multiset.filter_map, Multiset.card_map]
    refine card_filter_le_add _ fun x _ hx => ?_
    simp only [Function.comp_apply]
    set y := x / (cauchyScale d : ℂ)
    by_cases hS : T ≤ ‖I * ((2 : ℝ) : ℂ) - y‖
    · exact Or.inr hS
    · left
      push Not at hS
      have hyim : 0 ≤ y.im := by
        simp only [y]
        rw [Complex.div_ofReal_im]
        exact div_nonneg hx hℓ.le
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
      have hθA : A ^ 2 ≤ θ₀ / 2 := by
        simp only [θ₀]
        linarith
      have hle : ‖I * (θ₀ : ℂ) - y‖ ^ 2 ≤ (θ₀ + 1 / 4) ^ 2 := by
        rw [hsq2]
        nlinarith
      exact abs_le_of_sq_le_sq' hle (by positivity) |>.2
  have hcountR : (Multiset.card ((halfJensen g d).roots.filter fun e => 0 ≤ e.im) : ℝ) ≤
      (Multiset.card ((halfRoots g d).filter fun y => ‖I * (θ₀ : ℂ) - y‖ ≤ θ₀ + 1 / 4) : ℝ) +
        (Multiset.card ((halfRoots g d).filter fun y => T ≤ ‖I * ((2 : ℝ) : ℂ) - y‖) : ℝ) := by
    exact_mod_cast hcount
  rw [div_lt_iff₀ hdR] at h1
  nlinarith

/-! ## The theorem -/

/-- **Almost all Jensen roots of a hyperbolic kernel are real and simple.** -/
theorem HyperbolicKernel.eventually_exists_real_roots (hg : HyperbolicKernel g) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ d : ℕ in atTop, ∃ S : Finset ℝ, (1 - η) * d ≤ S.card ∧
      ∀ x ∈ S, (kernelJensen g d).IsRoot (x : ℂ) := by
  have hμ := hg.halfMoment_zero_pos.ne'
  filter_upwards [hg.eventually_card_im_nonneg_halfJensen_le (half_pos hη)] with d hd
  obtain ⟨S, hS, hroots⟩ := exists_finset_re_eval_eq_zero (halfJensen g d)
    (leadingCoeff_momentJensen hμ d)
  refine ⟨S, ?_, fun x hx => ?_⟩
  · set M := (halfJensen g d).roots
    have hsplit := card_filter_le_add M (p := fun _ => True) (q := fun e => e.im < 0)
      (s := fun e => 0 ≤ e.im) (fun e _ _ => lt_or_ge e.im 0)
    rw [Multiset.filter_true, card_roots_momentJensen hμ] at hsplit
    have hZp : Multiset.card (M.filter fun e => 0 < e.im) ≤
        Multiset.card (M.filter fun e => 0 ≤ e.im) :=
      Multiset.card_le_card (Multiset.monotone_filter_right M fun e he => le_of_lt he)
    have hsplitR : (d : ℝ) ≤ (Multiset.card (M.filter fun e => e.im < 0) : ℝ) +
        (Multiset.card (M.filter fun e => 0 ≤ e.im) : ℝ) := by exact_mod_cast hsplit
    have hSR : (Multiset.card (M.filter fun e => e.im < 0) : ℝ) ≤
        S.card + (Multiset.card (M.filter fun e => 0 < e.im) : ℝ) := by exact_mod_cast hS
    have hZpR : (Multiset.card (M.filter fun e => 0 < e.im) : ℝ) ≤
        (Multiset.card (M.filter fun e => 0 ≤ e.im) : ℝ) := by exact_mod_cast hZp
    linarith
  · rw [IsRoot, hg.eval_kernelJensen_real, Complex.add_conj, hroots x hx]
    simp

/-- The proportion of non-real roots of `kernelJensen g d`, with multiplicity, tends to `0`. -/
theorem HyperbolicKernel.tendsto_card_nonreal_roots_div (hg : HyperbolicKernel g) :
    Tendsto (fun d : ℕ =>
      (Multiset.card ((kernelJensen g d).roots.filter fun x => x.im ≠ 0) : ℝ) / d)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have hμ := hg.kernelMoment_zero_pos.ne'
  filter_upwards [hg.eventually_exists_real_roots (half_pos hη), eventually_gt_atTop 0] with d hd hd0
  obtain ⟨S, hS, hroots⟩ := hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  set q := kernelJensen g d
  have hq : q ≠ 0 := fun h => by
    have := natDegree_momentJensen hμ d
    rw [show momentJensen (kernelMoment g) d = q from rfl, h, natDegree_zero] at this
    omega
  have hcard : Multiset.card q.roots = d := card_roots_momentJensen hμ d
  have hsplit := Multiset.filter_add_not (fun x : ℂ => x.im ≠ 0) q.roots
  have hcardsplit := congrArg Multiset.card hsplit
  rw [Multiset.card_add, hcard] at hcardsplit
  have hreal : S.card ≤ Multiset.card (q.roots.filter fun x => ¬ x.im ≠ 0) := by
    have hinj : Function.Injective (fun x : ℝ => (x : ℂ)) := ofReal_injective
    have hsub : (S.map ⟨_, hinj⟩).val ≤ q.roots.filter fun x => ¬ x.im ≠ 0 := by
      refine (Multiset.le_iff_subset (Finset.nodup _)).2 fun z hz => ?_
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hz
      refine Multiset.mem_filter.2 ⟨(mem_roots hq).2 (hroots x hx), ?_⟩
      simp
    have := Multiset.card_le_card hsub
    simpa using this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hdR]
  have hrealR : (S.card : ℝ) ≤ (Multiset.card (q.roots.filter fun x => ¬ x.im ≠ 0) : ℝ) := by
    exact_mod_cast hreal
  have hsumR : (Multiset.card (q.roots.filter fun x => x.im ≠ 0) : ℝ) +
      (Multiset.card (q.roots.filter fun x => ¬ x.im ≠ 0) : ℝ) = d := by exact_mod_cast hcardsplit
  nlinarith

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.HyperbolicKernel.eventually_exists_real_roots
#print axioms FiniteFreeProbability.HyperbolicKernel.tendsto_card_nonreal_roots_div
