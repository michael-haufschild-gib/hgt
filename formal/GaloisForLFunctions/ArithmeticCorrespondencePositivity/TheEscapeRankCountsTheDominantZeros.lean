import GaloisForLFunctions.ArithmeticDefectRigidity.TwoDilationEigenrowsArePowerRows
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The escape rank counts the dominant zeros

An escape state is a limit of normalized cofactor Grams, and `TheCofactorGramIsATranslationGram`
reads a cofactor Gram as the translation Gram of the log profile. A translated zero
`ρ − ε = ½ + x + i y` contributes the exponential `e^{(x + i y) u}` to the profile. This file
classifies the escape states of a **dominant configuration**: a profile
`F(u) = Σ_k c_k e^{(x + i y_k) u}` with `x > 0` and distinct `y_k`, all exponents on one line.

* **The horizon law** (`exp_mul_hermGram_eq`). Exactly,
  `e^{−2xL} ∫_0^L F(u − a) F̄(u − b) du = K_{θ(L)}(a, b) − e^{−2xL} K_1(a, b)`, with the phases
  `θ_k(L) = e^{i y_k L}` and the **escape kernel**
  `K_θ(a, b) = Σ_{k,l} (c_k θ_k ψ_k(a)) conj(c_l θ_l ψ_l(b)) / (2x + i(y_k − y_l))`,
  `ψ_k(a) = e^{−(x + i y_k) a}`.
* **Every escape state is a phase kernel** (`exists_tendsto_escapeKernel`). Along every sequence of
  horizons `L_m → ∞` a subsequence of the normalized Grams converges, for all `a, b` at once, to a
  kernel `K_θ` with `|θ_k| = 1`. The escape states are the phase kernels over the closure of the
  orbit `L ↦ θ(L)` on the torus.
* **The Cauchy form is positive** (`cauchyForm_eq_integral`, `integral_cauchyDensity_pos`).
  `Σ_{k,l} v_k v̄_l / (2x + i(y_k − y_l)) = ∫_0^∞ e^{−2xt} |Σ_k v_k e^{−i y_k t}|² dt`, positive for
  `v ≠ 0`: the exponentials `e^{−i y_k t}` are independent on `t > 0` (Artin's lemma on the powers
  of one small step, `eq_zero_of_expSum_eq_zero`).
* **The null space of an escape state is the annihilator of the dominant characters**
  (`escapeForm_eq_cauchyForm`, `escapeForm_eq_zero_iff`). For weights `w_i` at points `a_i` the form
  `Σ w_i w̄_{i'} K_θ(a_i, a_{i'})` is the Cauchy form at `V_k = c_k θ_k Σ_i w_i ψ_k(a_i)`. It
  vanishes exactly when `Σ_i w_i ψ_k(a_i) = 0` for every `k`, whatever the phase.
* **The dominant characters are independent on the dilations** (`transChar_log`,
  `linearIndependent_powChar`). At `a = log j`, `ψ_k(log j) = j^{−(x + i y_k)}`, and distinct
  exponents give linearly independent characters of `(ℕ_{>0}, ·)` (`escapeForm_log_eq_zero_iff`).

So every escape state of a configuration of `r` dominant translated zeros is positive semidefinite
of rank exactly `r` on the dilations, with range the span of the power characters `j^{−(ρ_k − ε)}`
(after the prefactor `(jk)^{−1/2}` of the translation Gram), for every phase. The escape rank is an
integer that counts the intrinsic charge on the dominant line independently of the phase: an
oscillatory capacity for finite configurations. With `tendsto_normGram_sub_of_subdominant` the same
classification holds for every row whose profile is such a configuration plus a remainder of
subdominant energy.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

variable {r : ℕ}

/-! ### Profiles, Grams and kernels -/

/-- The translated character `ψ(a) = e^{−(x + i y) a}`. -/
def transChar (x y a : ℝ) : ℂ := Complex.exp (-(((x : ℂ) + y * I) * a))

/-- A dominant configuration `F(u) = Σ_k c_k e^{(x + i y_k) u}`. -/
def domProfile (x : ℝ) (y : Fin r → ℝ) (c : Fin r → ℂ) (u : ℝ) : ℂ :=
  ∑ k, c k * Complex.exp (((x : ℂ) + y k * I) * u)

/-- The Hermitian translation Gram `∫_0^L F(u − a) F̄(u − b) du`. -/
def hermGram (F : ℝ → ℂ) (L a b : ℝ) : ℂ := ∫ u in (0 : ℝ)..L, F (u - a) * conj (F (u - b))

/-- The escape kernel `K_θ(a, b)` at phases `θ`. -/
def escapeKernel (x : ℝ) (y : Fin r → ℝ) (c θ : Fin r → ℂ) (a b : ℝ) : ℂ :=
  ∑ k, ∑ l, c k * θ k * transChar x (y k) a * conj (c l * θ l * transChar x (y l) b) /
    (2 * (x : ℂ) + ((y k : ℂ) - y l) * I)

/-- The phases `θ_k(L) = e^{i y_k L}` at horizon `L`. -/
def phase (y : Fin r → ℝ) (L : ℝ) (k : Fin r) : ℂ := Complex.exp ((y k * L : ℝ) * I)

theorem norm_phase (y : Fin r → ℝ) (L : ℝ) (k : Fin r) : ‖phase y L k‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem den_ne_zero {x : ℝ} (hx : 0 < x) (p q : ℝ) : 2 * (x : ℂ) + ((p : ℂ) - q) * I ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

/-! ### The horizon law -/

theorem exp_mul_conj_exp (x p q u a b : ℝ) :
    Complex.exp (((x : ℂ) + p * I) * ((u - a : ℝ) : ℂ)) *
        conj (Complex.exp (((x : ℂ) + q * I) * ((u - b : ℝ) : ℂ))) =
      transChar x p a * conj (transChar x q b) *
        Complex.exp ((2 * (x : ℂ) + ((p : ℂ) - q) * I) * u) := by
  simp only [transChar, ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, map_add, map_neg, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The product of two translates expands into exponentials `e^{(2x + i(y_k − y_l)) u}`. -/
theorem domProfile_mul_conj (x : ℝ) (y : Fin r → ℝ) (c : Fin r → ℂ) (u a b : ℝ) :
    domProfile x y c (u - a) * conj (domProfile x y c (u - b)) =
      ∑ k, ∑ l, c k * transChar x (y k) a * conj (c l * transChar x (y l) b) *
        Complex.exp ((2 * (x : ℂ) + ((y k : ℂ) - y l) * I) * u) := by
  simp only [domProfile, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have h := exp_mul_conj_exp x (y k) (y l) u a b
  simp only [map_mul]
  linear_combination (c k * conj (c l)) * h

theorem continuous_gramTerm (C β : ℂ) : Continuous fun u : ℝ => C * Complex.exp (β * u) :=
  continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))

/-- **The horizon law**: the Gram at horizon `L`, scaled by `e^{−2xL}`, is the phase kernel at
`θ(L)` minus a term that decays like `e^{−2xL}`. -/
theorem exp_mul_hermGram_eq {x : ℝ} (hx : 0 < x) (y : Fin r → ℝ) (c : Fin r → ℂ) (L a b : ℝ) :
    (Real.exp (-(2 * x * L)) : ℂ) * hermGram (domProfile x y c) L a b =
      escapeKernel x y c (phase y L) a b -
        (Real.exp (-(2 * x * L)) : ℂ) * escapeKernel x y c 1 a b := by
  have hfun : (fun u : ℝ => domProfile x y c (u - a) * conj (domProfile x y c (u - b))) =
      fun u : ℝ => ∑ k, ∑ l, c k * transChar x (y k) a * conj (c l * transChar x (y l) b) *
        Complex.exp ((2 * (x : ℂ) + ((y k : ℂ) - y l) * I) * (u : ℂ)) :=
    funext fun u => domProfile_mul_conj x y c u a b
  rw [hermGram, hfun, intervalIntegral.integral_finsetSum fun k _ =>
    (continuous_finsetSum _ fun l _ => continuous_gramTerm
      (c k * transChar x (y k) a * conj (c l * transChar x (y l) b))
      (2 * (x : ℂ) + ((y k : ℂ) - y l) * I)).intervalIntegrable _ _]
  rw [Finset.mul_sum, escapeKernel, escapeKernel, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_finsetSum fun l _ => (continuous_gramTerm
      (c k * transChar x (y k) a * conj (c l * transChar x (y l) b))
      (2 * (x : ℂ) + ((y k : ℂ) - y l) * I)).intervalIntegrable _ _,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex (den_ne_zero hx (y k) (y l))]
  -- `e^{−2xL} e^{(2x + i(y_k − y_l)) L} = θ_k(L) conj θ_l(L)`
  have hE : (Real.exp (-(2 * x * L)) : ℂ) *
      Complex.exp ((2 * (x : ℂ) + ((y k : ℂ) - y l) * I) * L) =
        phase y L k * conj (phase y L l) := by
    simp only [phase, Complex.ofReal_exp, ← Complex.exp_conj, ← Complex.exp_add]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  simp only [Pi.one_apply, mul_one, map_mul, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero]
  linear_combination (c k * transChar x (y k) a * (conj (c l) * conj (transChar x (y l) b)) /
    (2 * (x : ℂ) + ((y k : ℂ) - y l) * I)) * hE

/-! ### Every escape state is a phase kernel -/

theorem tendsto_escapeKernel (x : ℝ) (y : Fin r → ℝ) (c : Fin r → ℂ) {θs : ℕ → Fin r → ℂ}
    {θ : Fin r → ℂ} (h : Tendsto θs atTop (𝓝 θ)) (a b : ℝ) :
    Tendsto (fun m => escapeKernel x y c (θs m) a b) atTop (𝓝 (escapeKernel x y c θ a b)) := by
  have hk : ∀ k, Tendsto (fun m => θs m k) atTop (𝓝 (θ k)) :=
    fun k => ((continuous_apply k).tendsto θ).comp h
  unfold escapeKernel
  refine tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ => ?_
  refine Filter.Tendsto.div_const ?_ _
  refine ((tendsto_const_nhds.mul (hk k)).mul tendsto_const_nhds).mul ?_
  exact (Complex.continuous_conj.tendsto _).comp
    ((tendsto_const_nhds.mul (hk l)).mul tendsto_const_nhds)

/-- **Every escape state is a phase kernel.** Along any horizons `L_m → ∞`, a subsequence of the
scaled Grams converges, for all `a, b` at once, to `K_θ` for some unimodular `θ`. -/
theorem exists_tendsto_escapeKernel {x : ℝ} (hx : 0 < x) (y : Fin r → ℝ) (c : Fin r → ℂ)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    ∃ θ : Fin r → ℂ, (∀ k, ‖θ k‖ = 1) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ a b : ℝ,
      Tendsto (fun m => (Real.exp (-(2 * x * L (φ m))) : ℂ) *
        hermGram (domProfile x y c) (L (φ m)) a b) atTop (𝓝 (escapeKernel x y c θ a b)) := by
  have hS : IsCompact (Set.pi Set.univ fun _ : Fin r => Metric.sphere (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_sphere 0 1
  have hmem : ∀ m, phase y (L m) ∈ Set.pi Set.univ fun _ : Fin r => Metric.sphere (0 : ℂ) 1 :=
    fun m k _ => by simp [norm_phase]
  obtain ⟨θ, hθ, φ, hφ, hlim⟩ := hS.tendsto_subseq hmem
  refine ⟨θ, fun k => by simpa using hθ k (Set.mem_univ k), φ, hφ, fun a b => ?_⟩
  have he : Tendsto (fun m => (Real.exp (-(2 * x * L (φ m))) : ℂ)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => -(2 * x * L (φ m))) atTop atBot :=
      tendsto_neg_atTop_atBot.comp ((hL.comp hφ.tendsto_atTop).const_mul_atTop (by linarith))
    have h2 := (Complex.continuous_ofReal.tendsto 0).comp (Real.tendsto_exp_atBot.comp h1)
    rw [Complex.ofReal_zero] at h2
    exact h2
  simp_rw [exp_mul_hermGram_eq hx]
  simpa using (tendsto_escapeKernel x y c hlim a b).sub (he.mul_const (escapeKernel x y c 1 a b))

/-! ### The Cauchy form -/

/-- The exponential sum `S(t) = Σ_k v_k e^{−i y_k t}`. -/
def expSum (y : Fin r → ℝ) (v : Fin r → ℂ) (t : ℝ) : ℂ :=
  ∑ k, v k * Complex.exp (-((y k * t : ℝ) * I))

/-- The density `e^{−2xt} |S(t)|²` of the Cauchy form. -/
def cauchyDensity (x : ℝ) (y : Fin r → ℝ) (v : Fin r → ℂ) (t : ℝ) : ℝ :=
  Real.exp (-(2 * x * t)) * ‖expSum y v t‖ ^ 2

theorem continuous_expSum (y : Fin r → ℝ) (v : Fin r → ℂ) : Continuous (expSum y v) := by
  unfold expSum
  fun_prop

theorem cauchyDensity_eq (x : ℝ) (y : Fin r → ℝ) (v : Fin r → ℂ) (t : ℝ) :
    (cauchyDensity x y v t : ℂ) = ∑ k, ∑ l, v k * conj (v l) *
      Complex.exp (-(2 * (x : ℂ) + ((y k : ℂ) - y l) * I) * t) := by
  rw [cauchyDensity, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', expSum, map_sum,
    Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h : (Real.exp (-(2 * x * t)) : ℂ) * (Complex.exp (-((y k * t : ℝ) * I)) *
      conj (Complex.exp (-((y l * t : ℝ) * I)))) =
        Complex.exp (-(2 * (x : ℂ) + ((y k : ℂ) - y l) * I) * t) := by
    rw [Complex.ofReal_exp, ← Complex.exp_conj, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [map_mul]
  linear_combination (v k * conj (v l)) * h

theorem re_neg_den_neg {x : ℝ} (hx : 0 < x) (p q : ℝ) :
    (-(2 * (x : ℂ) + ((p : ℂ) - q) * I)).re < 0 := by
  simp
  linarith

theorem integrable_cauchyDensity_complex {x : ℝ} (hx : 0 < x) (y : Fin r → ℝ) (v : Fin r → ℂ) :
    Integrable (fun t => (cauchyDensity x y v t : ℂ)) (volume.restrict (Ioi 0)) :=
  (integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (integrableOn_exp_mul_complex_Ioi (re_neg_den_neg hx (y k) (y l)) 0).const_mul
      (v k * conj (v l))).congr
      (Eventually.of_forall fun t => (cauchyDensity_eq x y v t).symm)

/-- **The Cauchy form as an integral.** -/
theorem cauchyForm_eq_integral {x : ℝ} (hx : 0 < x) (y : Fin r → ℝ) (v : Fin r → ℂ) :
    ∑ k, ∑ l, v k * conj (v l) / (2 * (x : ℂ) + ((y k : ℂ) - y l) * I) =
      ((∫ t in Ioi (0 : ℝ), cauchyDensity x y v t : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  simp_rw [cauchyDensity_eq]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (integrableOn_exp_mul_complex_Ioi (re_neg_den_neg hx (y k) (y l)) 0).const_mul
      (v k * conj (v l))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ =>
    (integrableOn_exp_mul_complex_Ioi (re_neg_den_neg hx (y k) (y l)) 0).const_mul
      (v k * conj (v l))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_exp_mul_complex_Ioi (re_neg_den_neg hx (y k) (y l)) 0,
    Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]
  ring

/-- **The exponentials `e^{−i y_k t}` are independent on `t > 0`.** With a step `t₀` so small that
the `y_k t₀` are distinct modulo `2π`, the values at `t₀, 2t₀, …` are the powers of distinct
numbers, and Artin's lemma on `Multiplicative ℕ` separates them. -/
theorem eq_zero_of_expSum_eq_zero {y : Fin r → ℝ} (hy : Function.Injective y) {v : Fin r → ℂ}
    (h : ∀ t : ℝ, 0 < t → expSum y v t = 0) : v = 0 := by
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∑ k, ∑ l, |y k - y l| := ⟨_, rfl⟩
  have hM : 0 ≤ M := by
    rw [hMdef]; exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg _
  obtain ⟨t₀, ht₀def⟩ : ∃ t : ℝ, t = 1 / (1 + M) := ⟨_, rfl⟩
  have ht₀ : 0 < t₀ := by rw [ht₀def]; exact div_pos one_pos (by linarith)
  -- the step is small: `|y_k − y_l| t₀ < 1`
  have hsmall : ∀ k l, |y k - y l| * t₀ < 1 := by
    intro k l
    have h1 : |y k - y l| ≤ ∑ l', |y k - y l'| :=
      Finset.single_le_sum (f := fun l' => |y k - y l'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ l)
    have h2 : ∑ l', |y k - y l'| ≤ M := by
      rw [hMdef]
      exact Finset.single_le_sum (f := fun k' => ∑ l', |y k' - y l'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    rw [ht₀def, mul_one_div, div_lt_one (by linarith)]
    linarith
  have hz : Function.Injective fun k => Complex.exp (-((y k * t₀ : ℝ) * I)) := by
    intro k l hkl
    -- `e^{i d} = 1` with `d = (y_l − y_k) t₀`, `|d| < 1`
    have h1 : Complex.exp (((y l - y k) * t₀ : ℝ) * I) = 1 := by
      have e : (((y l - y k) * t₀ : ℝ) : ℂ) * I =
          -((y k * t₀ : ℝ) * I) - -((y l * t₀ : ℝ) * I) := by push_cast; ring
      have hkl' : Complex.exp (-((y k * t₀ : ℝ) * I)) = Complex.exp (-((y l * t₀ : ℝ) * I)) :=
        hkl
      rw [e, Complex.exp_sub, hkl', div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    have h2 : ((((y l - y k) * t₀ - n * (2 * Real.pi)) : ℝ) : ℂ) * I = 0 := by
      push_cast at hn ⊢; linear_combination hn
    have h3 : (y l - y k) * t₀ - n * (2 * Real.pi) = 0 := by
      exact_mod_cast (mul_eq_zero.mp h2).resolve_right Complex.I_ne_zero
    have hn0 : n = 0 := by
      have hlt : |(n : ℝ)| * (2 * Real.pi) < 1 := by
        have : |(n : ℝ) * (2 * Real.pi)| = |y k - y l| * t₀ := by
          rw [← sub_eq_zero.mp h3, abs_mul, abs_of_pos ht₀, abs_sub_comm]
        rw [← abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), ← abs_mul, this]
        exact hsmall k l
      have : |(n : ℝ)| < 1 := by nlinarith [Real.pi_gt_three, abs_nonneg (n : ℝ)]
      exact Int.abs_lt_one_iff.mp (by exact_mod_cast this)
    rw [hn0, Int.cast_zero, zero_mul, sub_zero] at h3
    exact hy (by linarith [(mul_eq_zero.mp h3).resolve_right ht₀.ne'])
  have hli := (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp
    (fun k => powersHom ℂ (Complex.exp (-((y k * t₀ : ℝ) * I))))
    ((powersHom ℂ).injective.comp hz)
  rw [Fintype.linearIndependent_iff] at hli
  have hzero := hli (fun k => v k * Complex.exp (-((y k * t₀ : ℝ) * I))) (by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, powersHom_apply, smul_eq_mul,
      Pi.zero_apply]
    refine Eq.trans ?_ (h (((Multiplicative.toAdd n + 1 : ℕ) : ℝ) * t₀) (mul_pos (by positivity) ht₀))
    rw [expSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e : Complex.exp (-((y k * (((Multiplicative.toAdd n + 1 : ℕ) : ℝ) * t₀) : ℝ) * I)) =
        Complex.exp (-((y k * t₀ : ℝ) * I)) ^ (Multiplicative.toAdd n + 1) := by
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    rw [e, pow_succ]
    ring)
  funext k
  exact (mul_eq_zero.mp (hzero k)).resolve_right (Complex.exp_ne_zero _)

/-- **The Cauchy form is positive**: `∫_0^∞ e^{−2xt} |S(t)|² dt > 0` for `v ≠ 0`. -/
theorem integral_cauchyDensity_pos {x : ℝ} (hx : 0 < x) {y : Fin r → ℝ}
    (hy : Function.Injective y) {v : Fin r → ℂ} (hv : v ≠ 0) :
    0 < ∫ t in Ioi (0 : ℝ), cauchyDensity x y v t := by
  obtain ⟨t₀, ht₀, hS⟩ : ∃ t₀ : ℝ, 0 < t₀ ∧ expSum y v t₀ ≠ 0 := by
    by_contra hcon
    exact hv (eq_zero_of_expSum_eq_zero hy fun t ht => by_contra fun hne => hcon ⟨t, ht, hne⟩)
  have hcont : Continuous (cauchyDensity x y v) := by
    have := continuous_expSum y v
    unfold cauchyDensity
    fun_prop
  have hnn : 0 ≤ cauchyDensity x y v := fun t => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hint : Integrable (cauchyDensity x y v) (volume.restrict (Ioi 0)) :=
    (integrable_cauchyDensity_complex hx y v).re.congr
      (Eventually.of_forall fun t => by simp)
  rw [integral_pos_iff_support_of_nonneg hnn hint, Measure.restrict_apply' measurableSet_Ioi]
  refine IsOpen.measure_pos volume ((isOpen_ne_fun hcont continuous_const).inter isOpen_Ioi)
    ⟨t₀, ?_, ht₀⟩
  exact (mul_pos (Real.exp_pos _) (pow_pos (norm_pos_iff.mpr hS) 2)).ne'

theorem integral_cauchyDensity_zero (x : ℝ) (y : Fin r → ℝ) :
    ∫ t in Ioi (0 : ℝ), cauchyDensity x y 0 t = 0 := by
  simp [cauchyDensity, expSum]

/-! ### The null space of an escape state -/

/-- The coefficient vector `V_k = Σ_i w_i c_k θ_k ψ_k(a_i)` of a weighted escape form. -/
def escapeVec {ι : Type*} (s : Finset ι) (w : ι → ℂ) (p : ι → ℝ) (x : ℝ) (y : Fin r → ℝ)
    (c θ : Fin r → ℂ) (k : Fin r) : ℂ :=
  ∑ i ∈ s, w i * (c k * θ k * transChar x (y k) (p i))

/-- **The escape form is a Cauchy form.** -/
theorem escapeForm_eq_cauchyForm {ι : Type*} (s : Finset ι) (w : ι → ℂ) (p : ι → ℝ) (x : ℝ)
    (y : Fin r → ℝ) (c θ : Fin r → ℂ) :
    ∑ i ∈ s, ∑ i' ∈ s, w i * conj (w i') * escapeKernel x y c θ (p i) (p i') =
      ∑ k, ∑ l, escapeVec s w p x y c θ k * conj (escapeVec s w p x y c θ l) /
        (2 * (x : ℂ) + ((y k : ℂ) - y l) * I) := by
  have hR : ∀ k l, escapeVec s w p x y c θ k * conj (escapeVec s w p x y c θ l) /
      (2 * (x : ℂ) + ((y k : ℂ) - y l) * I) =
        ∑ i ∈ s, ∑ i' ∈ s, w i * conj (w i') *
          (c k * θ k * transChar x (y k) (p i) * conj (c l * θ l * transChar x (y l) (p i')) /
            (2 * (x : ℂ) + ((y k : ℂ) - y l) * I)) := by
    intro k l
    rw [escapeVec, escapeVec, map_sum, Finset.sum_mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i' _ => ?_
    simp only [map_mul]
    ring
  simp_rw [hR]
  simp only [escapeKernel, Finset.mul_sum]
  exact (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans (Finset.sum_comm.trans
    (Finset.sum_congr rfl fun k _ => (Finset.sum_congr rfl fun i _ => Finset.sum_comm).trans
      Finset.sum_comm))

/-- **The null space of every escape state is the annihilator of the dominant characters**,
whatever the phase. -/
theorem escapeForm_eq_zero_iff {x : ℝ} (hx : 0 < x) {y : Fin r → ℝ} (hy : Function.Injective y)
    {c θ : Fin r → ℂ} (hcθ : ∀ k, c k * θ k ≠ 0) {ι : Type*} (s : Finset ι) (w : ι → ℂ)
    (p : ι → ℝ) :
    ∑ i ∈ s, ∑ i' ∈ s, w i * conj (w i') * escapeKernel x y c θ (p i) (p i') = 0 ↔
      ∀ k, ∑ i ∈ s, w i * transChar x (y k) (p i) = 0 := by
  have hV : ∀ k, escapeVec s w p x y c θ k = c k * θ k * ∑ i ∈ s, w i * transChar x (y k) (p i) := by
    intro k
    rw [escapeVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [escapeForm_eq_cauchyForm, cauchyForm_eq_integral hx y (escapeVec s w p x y c θ),
    Complex.ofReal_eq_zero]
  constructor
  · intro h0 k
    by_cases hv : escapeVec s w p x y c θ = 0
    · have := congrFun hv k
      rw [hV, Pi.zero_apply] at this
      exact (mul_eq_zero.mp this).resolve_left (hcθ k)
    · exact absurd h0 (integral_cauchyDensity_pos hx hy hv).ne'
  · intro h
    have hv : escapeVec s w p x y c θ = 0 := funext fun k => by simp [hV, h k]
    rw [hv, integral_cauchyDensity_zero]

/-- The diagonal of an escape state is the Cauchy form of `c_k θ_k ψ_k(a)`; it is positive. -/
theorem escapeKernel_self_pos {x : ℝ} (hx : 0 < x) {y : Fin r → ℝ} (hy : Function.Injective y)
    {c θ : Fin r → ℂ} (hc : c ≠ 0) (hθ : ∀ k, θ k ≠ 0) (a : ℝ) :
    ∃ e : ℝ, 0 < e ∧ escapeKernel x y c θ a a = e := by
  refine ⟨_, integral_cauchyDensity_pos hx hy (v := fun k => c k * θ k * transChar x (y k) a) ?_,
    cauchyForm_eq_integral hx y (fun k => c k * θ k * transChar x (y k) a)⟩
  intro h0
  apply hc
  funext k
  have := congrFun h0 k
  simp only [Pi.zero_apply, mul_eq_zero, transChar, Complex.exp_ne_zero, or_false] at this
  exact this.resolve_right (hθ k)

/-! ### The dominant characters on the dilations -/

/-- At `a = log j` the translated character is the power character `j^{−(x + i y)}`. -/
theorem transChar_log (x y : ℝ) {j : ℕ} (hj : j ≠ 0) :
    transChar x y (Real.log j) = (j : ℂ) ^ (-((x : ℂ) + y * I)) := by
  rw [transChar, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hj : (j : ℂ) ≠ 0),
    Complex.ofReal_log (Nat.cast_nonneg j), Complex.ofReal_natCast]
  congr 1
  ring

/-- The power character `j ↦ j^{−s}` of the multiplicative monoid `ℕ_{>0}`. -/
def powChar (s : ℂ) : ℕ+ →* ℂ where
  toFun j := ((j : ℕ) : ℂ) ^ (-s)
  map_one' := by simp
  map_mul' j k := by
    simp only [PNat.mul_coe, Nat.cast_mul]
    exact Complex.natCast_mul_natCast_cpow _ _ _

theorem powChar_injective : Function.Injective powChar := by
  intro s s' h
  have h2 := DFunLike.congr_fun h 2
  have h3 := DFunLike.congr_fun h 3
  simp only [powChar, MonoidHom.coe_mk, OneHom.coe_mk, PNat.val_ofNat, Nat.cast_ofNat] at h2 h3
  exact neg_inj.mp (ArithmeticDefectRigidity.eq_of_two_three_cpow_eq h2.symm h3.symm).symm

/-- **Distinct exponents give independent characters of `ℕ_{>0}`** (Artin's lemma). -/
theorem linearIndependent_powChar {z : Fin r → ℂ} (hz : Function.Injective z) :
    LinearIndependent ℂ fun k => (powChar (z k) : ℕ+ → ℂ) :=
  (linearIndependent_monoidHom ℕ+ ℂ).comp _ (powChar_injective.comp hz)

/-- The dominant exponents `x + i y_k` are distinct when the `y_k` are. -/
theorem injective_exponent (x : ℝ) {y : Fin r → ℝ} (hy : Function.Injective y) :
    Function.Injective fun k => (x : ℂ) + y k * I := by
  intro k l h
  apply hy
  have := congrArg Complex.im h
  simpa using this

/-- **The escape rank on the dilations.** For weights `w_j` on finitely many dilations `j`, the
escape form at the points `log j` vanishes exactly when `Σ_j w_j j^{−(x + i y_k)} = 0` for every
`k`; these are `r` linearly independent functionals (`linearIndependent_powChar`). -/
theorem escapeForm_log_eq_zero_iff {x : ℝ} (hx : 0 < x) {y : Fin r → ℝ}
    (hy : Function.Injective y) {c θ : Fin r → ℂ} (hcθ : ∀ k, c k * θ k ≠ 0) (s : Finset ℕ+)
    (w : ℕ+ → ℂ) :
    ∑ j ∈ s, ∑ j' ∈ s, w j * conj (w j') *
        escapeKernel x y c θ (Real.log (j : ℕ)) (Real.log (j' : ℕ)) = 0 ↔
      ∀ k, ∑ j ∈ s, w j * powChar ((x : ℂ) + y k * I) j = 0 := by
  refine (escapeForm_eq_zero_iff hx hy hcθ s w fun j => Real.log (j : ℕ)).trans
    (forall_congr' fun k => ?_)
  have hsum : ∑ j ∈ s, w j * transChar x (y k) (Real.log (j : ℕ)) =
      ∑ j ∈ s, w j * powChar ((x : ℂ) + y k * I) j :=
    Finset.sum_congr rfl fun j _ => by
      show w j * transChar x (y k) (Real.log (j : ℕ)) =
        w j * ((j : ℕ) : ℂ) ^ (-((x : ℂ) + y k * I))
      rw [transChar_log x (y k) (PNat.ne_zero j)]
  exact Iff.of_eq (congrArg (· = 0) hsum)

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
