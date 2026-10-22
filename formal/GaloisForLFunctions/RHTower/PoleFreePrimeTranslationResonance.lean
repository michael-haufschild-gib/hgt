import GaloisForLFunctions.RHTower.ChebyshevPsiScaling
import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleFiniteCoherence

/-!
# The pole-free prime translation form grows like `e^A / A`

Let `Q_A(u, v) = Σ_{2 ≤ n ≤ e^{2A}} Λ(n) n^{-1/2} (⟨τ_{log n} u, v⟩ + ⟨τ_{-log n} u, v⟩)` be the prime
part of the level-`A` Weil form on functions supported in `[-A, A]`, and let `V₀` be the pole-free
subspace `∫ f(x) e^{x/2} dx = ∫ f(x) e^{-x/2} dx = 0`.  The main theorem
`poleFree_primeTranslation_resonance` says that for every large `A` there is `f ∈ V₀`, bounded and
supported in `[-A, A]`, with

```text
Re Q_A(f, f)  ≥  (e^A / (64 A)) ∫ |f|² .
```

So the compression `P_{V₀} (Σ Λ(n) n^{-1/2} τ_{±log n}) P_{V₀}` to `L²(-A, A)` has norm at least
`e^A/(64A)`: its exponential growth rate is exactly that of the uncompressed operator, with no
hypothesis on the zeros.  The pole constraint does not remove the exponential growth.

**Mechanism.**

* *Dirichlet resonance.*  For every finite set of logarithms there are arbitrarily large integers `τ`
  with `cos(τ log n) ≥ 1/2` for all `2 ≤ n ≤ e^{2A}` (`exists_resonant_frequency`).
* *The modulated flat vector.*  `g(x) = 1_{[-A,A]}(x) e^{iτx}` has autocorrelation
  `e^{±iτℓ}(2A - ℓ)`, so `Re Q_A(g, g) ≥ Σ Λ(n) n^{-1/2}(2A - log n)`, the hinge sum, which is
  `≥ e^A/4` by the prime number theorem (`exists_primeHinge_ge`).
* *Pole correction.*  The pole moments of `g` are `O(e^{A/2}/τ)`.  Subtracting a combination of
  `1_{[-A,A]} e^{±x/2}`, solved from the Gram matrix `[[2 sinh A, 2A], [2A, 2 sinh A]]`, gives a
  pole-free `f` with `‖f - g‖_∞ ≤ 8/τ`.
* *Stability.*  The form moves by at most `4Aε(2 + ε) Σ Λ(n) n^{-1/2}` under a perturbation of sup
  norm `ε`, and `τ` is taken large enough to make this `≤ e^A/8`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

namespace RHTower

noncomputable section

/-- The prime translation form of level `A`:
`Σ_{2 ≤ n ≤ e^{2A}} Λ(n) n^{-1/2} (∫ u(x + log n) conj v(x) + ∫ u(x - log n) conj v(x))`.
On functions supported in `[-A, A]` it is the quadratic form of the prime part
`Σ Λ(n) n^{-1/2}(τ_{log n} + τ_{-log n})` of the level-`A` Weil form compressed to `L²(-A, A)`. -/
def primeTranslationForm (A : ℝ) (u v : ℝ → ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A)⌋₊,
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      ((∫ x, u (x + Real.log n) * (starRingEnd ℂ) (v x)) +
        ∫ x, u (x - Real.log n) * (starRingEnd ℂ) (v x))

/-- The flat vector modulated at frequency `τ`. -/
def modulatedFlat (A τ : ℝ) : ℝ → ℂ := (Icc (-A) A).indicator fun x => cexp (I * τ * x)

theorem modulatedFlat_shift_mul (A τ ℓ x : ℝ) :
    modulatedFlat A τ (x + ℓ) * (starRingEnd ℂ) (modulatedFlat A τ x) =
      (Icc (-A - ℓ) (A - ℓ) ∩ Icc (-A) A).indicator (fun _ => cexp (I * τ * ℓ)) x := by
  unfold modulatedFlat
  simp only [indicator, mem_inter_iff, mem_Icc]
  by_cases h1 : -A ≤ x + ℓ ∧ x + ℓ ≤ A
  · by_cases h2 : -A ≤ x ∧ x ≤ A
    · have h1' : -A - ℓ ≤ x ∧ x ≤ A - ℓ := ⟨by linarith [h1.1], by linarith [h1.2]⟩
      rw [if_pos h1, if_pos h2, if_pos ⟨h1', h2⟩, ← Complex.exp_conj, ← Complex.exp_add]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      push_cast; ring
    · rw [if_neg h2]; simp [h2]
  · have h1' : ¬(-A - ℓ ≤ x ∧ x ≤ A - ℓ) := fun h => h1 ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [if_neg h1, zero_mul, if_neg (fun h => h1' h.1)]

theorem volume_real_Icc_inter_shift {A ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hℓA : ℓ ≤ 2 * A) :
    volume.real (Icc (-A - ℓ) (A - ℓ) ∩ Icc (-A) A) = 2 * A - ℓ := by
  rw [Icc_inter_Icc, measureReal_def, Real.volume_Icc]
  have h1 : max (-A - ℓ) (-A) = -A := max_eq_right (by linarith)
  have h2 : min (A - ℓ) A = A - ℓ := min_eq_left (by linarith)
  rw [h1, h2, ENNReal.toReal_ofReal (by linarith)]
  ring

theorem volume_real_Icc_inter_shift_neg {A ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hℓA : ℓ ≤ 2 * A) :
    volume.real (Icc (-A - -ℓ) (A - -ℓ) ∩ Icc (-A) A) = 2 * A - ℓ := by
  rw [Icc_inter_Icc, measureReal_def, Real.volume_Icc]
  have h1 : max (-A - -ℓ) (-A) = -A + ℓ := by rw [max_eq_left (by linarith)]; ring
  have h2 : min (A - -ℓ) A = A := min_eq_right (by linarith)
  rw [h1, h2, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- The autocorrelation of the modulated flat vector: `e^{iτℓ}(2A - ℓ)` for `0 ≤ ℓ ≤ 2A`. -/
theorem integral_modulatedFlat_shift {A τ ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hℓA : ℓ ≤ 2 * A) :
    (∫ x, modulatedFlat A τ (x + ℓ) * (starRingEnd ℂ) (modulatedFlat A τ x)) =
      cexp (I * τ * ℓ) * ((2 * A - ℓ : ℝ) : ℂ) := by
  simp_rw [modulatedFlat_shift_mul]
  rw [integral_indicator_const _ (measurableSet_Icc.inter measurableSet_Icc),
    volume_real_Icc_inter_shift hℓ hℓA, Complex.real_smul]
  ring

theorem integral_modulatedFlat_shift_neg {A τ ℓ : ℝ} (hℓ : 0 ≤ ℓ) (hℓA : ℓ ≤ 2 * A) :
    (∫ x, modulatedFlat A τ (x - ℓ) * (starRingEnd ℂ) (modulatedFlat A τ x)) =
      cexp (-(I * τ * ℓ)) * ((2 * A - ℓ : ℝ) : ℂ) := by
  have e : ∀ x, modulatedFlat A τ (x - ℓ) * (starRingEnd ℂ) (modulatedFlat A τ x) =
      (Icc (-A - -ℓ) (A - -ℓ) ∩ Icc (-A) A).indicator (fun _ => cexp (I * τ * (-ℓ))) x := by
    intro x
    rw [sub_eq_add_neg, modulatedFlat_shift_mul]
    push_cast; rfl
  simp_rw [e]
  rw [integral_indicator_const _ (measurableSet_Icc.inter measurableSet_Icc),
    volume_real_Icc_inter_shift_neg hℓ hℓA, Complex.real_smul]
  push_cast; ring_nf

/-! ## The prime side at a resonant frequency -/

/-- The hinge sum `S(A) = Σ_{2 ≤ n ≤ e^{2A}} Λ(n) n^{-1/2} (2A - log n)`. -/
def primeHinge (A : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A)⌋₊,
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * A - Real.log n)

theorem log_le_two_mul_of_mem {A : ℝ} {n : ℕ} (hn : n ∈ Finset.Icc 2 ⌊Real.exp (2 * A)⌋₊) :
    Real.log n ≤ 2 * A := by
  rw [Finset.mem_Icc] at hn
  have h1 : (n : ℝ) ≤ Real.exp (2 * A) :=
    (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (Real.exp_pos _).le)
  have h2 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  calc Real.log n ≤ Real.log (Real.exp (2 * A)) := Real.log_le_log h2 h1
    _ = 2 * A := Real.log_exp _

/-- **The hinge sum grows like `e^A`.** By the prime number theorem there is `A₀` with
`S(A) ≥ e^A/4` for `A ≥ A₀`. -/
theorem exists_primeHinge_ge : ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → Real.exp A / 4 ≤ primeHinge A := by
  have hpnt := tendsto_chebyshevPsiReal_div
  have hev : ∀ᶠ x : ℝ in Filter.atTop, 1 / 2 < chebyshevPsiReal x / x :=
    hpnt (Ioi_mem_nhds (by norm_num))
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hev
  set x₀ := max x₁ 1 with hx₀
  have hx₀1 : 1 ≤ x₀ := le_max_right _ _
  have hψ : ∀ X : ℝ, 1 ≤ X → X / 2 - x₀ ≤ Chebyshev.psi X := by
    intro X hX
    by_cases hXx : x₀ ≤ X
    · have h1 := hx₁ X (le_trans (le_max_left _ _) hXx)
      have hident : chebyshevPsiReal X = Chebyshev.psi X := by
        rw [chebyshevPsiReal_eq_sum_range, Chebyshev.psi_eq_sum_Icc]
        congr 1
        ext n
        simp
      rw [hident, lt_div_iff₀ (by linarith)] at h1
      linarith
    · have h0 := Chebyshev.psi_nonneg X
      have : X < x₀ := lt_of_not_ge hXx
      linarith
  refine ⟨Real.log (40 * x₀) + 1, fun A hA => ?_⟩
  have hA1 : 1 ≤ A := by
    have : 0 ≤ Real.log (40 * x₀) := Real.log_nonneg (by linarith)
    linarith
  -- keep only `n ≤ e^{2A-1}`, where `2A - log n ≥ 1` and `n^{-1/2} ≥ e^{-(A - 1/2)}`
  set X := Real.exp (2 * A - 1) with hX
  have hX1 : 1 ≤ X := Real.one_le_exp (by linarith)
  have hsub : Finset.Icc 1 ⌊X⌋₊ ⊆ Finset.Icc 1 ⌊Real.exp (2 * A)⌋₊ := by
    apply Finset.Icc_subset_Icc le_rfl
    exact Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊Real.exp (2 * A)⌋₊,
      0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * A - Real.log n) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : (n : ℝ) ≤ Real.exp (2 * A) :=
      (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (Real.exp_pos _).le)
    have h2 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h3 : Real.log n ≤ 2 * A := by
      calc Real.log n ≤ Real.log (Real.exp (2 * A)) := Real.log_le_log h2 h1
        _ = 2 * A := Real.log_exp _
    have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n := by positivity
    exact mul_nonneg this (by linarith)
  have hsplit : primeHinge A =
      ∑ n ∈ Finset.Icc 1 ⌊Real.exp (2 * A)⌋₊,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * A - Real.log n) := by
    unfold primeHinge
    apply Finset.sum_subset (Finset.Icc_subset_Icc (by norm_num) le_rfl)
    intro n hn hn2
    rw [Finset.mem_Icc] at hn hn2
    have : n = 1 := by omega
    subst this
    simp
  have hlow : ∀ n ∈ Finset.Icc 1 ⌊X⌋₊,
      ArithmeticFunction.vonMangoldt n * Real.exp (-(A - 1 / 2)) ≤
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * A - Real.log n) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have h1 : (n : ℝ) ≤ X := (Nat.cast_le.mpr hn.2).trans (Nat.floor_le (Real.exp_pos _).le)
    have h2 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have h3 : Real.log n ≤ 2 * A - 1 := by
      calc Real.log n ≤ Real.log X := Real.log_le_log h2 h1
        _ = 2 * A - 1 := Real.log_exp _
    have hsq : Real.sqrt n ≤ Real.exp (A - 1 / 2) := by
      rw [Real.sqrt_le_left (Real.exp_pos _).le, sq, ← Real.exp_add]
      calc (n : ℝ) ≤ X := h1
        _ = Real.exp (A - 1 / 2 + (A - 1 / 2)) := by rw [hX]; ring_nf
    have hsqpos : 0 < Real.sqrt n := Real.sqrt_pos.mpr h2
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hinv : Real.exp (-(A - 1 / 2)) ≤ 1 / Real.sqrt n := by
      rw [Real.exp_neg]
      calc (Real.exp (A - 1 / 2))⁻¹ ≤ (Real.sqrt n)⁻¹ := inv_anti₀ hsqpos hsq
        _ = 1 / Real.sqrt n := (one_div _).symm
    calc ArithmeticFunction.vonMangoldt n * Real.exp (-(A - 1 / 2))
        ≤ ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt n) * 1 := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hinv hΛ
      _ ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * A - Real.log n) := by
          rw [mul_one_div]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hψX : Chebyshev.psi X = ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.psi_eq_sum_Icc]
    symm
    apply Finset.sum_subset (Finset.Icc_subset_Icc (by norm_num) le_rfl)
    intro n hn hn1
    rw [Finset.mem_Icc] at hn hn1
    have : n = 0 := by omega
    subst this
    simp
  have hmain : Real.exp (-(A - 1 / 2)) * Chebyshev.psi X ≤ primeHinge A := by
    rw [hψX, Finset.mul_sum, hsplit]
    calc ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, Real.exp (-(A - 1 / 2)) * ArithmeticFunction.vonMangoldt n
        ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
            ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * A - Real.log n) :=
          Finset.sum_le_sum fun n hn => by rw [mul_comm]; exact hlow n hn
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => hterm n hn
  have hψ' := hψ X hX1
  -- `e^{-(A-1/2)} (e^{2A-1}/2 - x₀) ≥ e^A/4`
  have hE : Real.exp (-(A - 1 / 2)) * X = Real.exp (A - 1 / 2) := by
    rw [hX, ← Real.exp_add]; ring_nf
  have hEA : Real.exp (A - 1 / 2) = Real.exp A * Real.exp (-(1 / 2)) := by
    rw [← Real.exp_add]; ring_nf
  have he12 : 3 / 5 ≤ Real.exp (-(1 / 2)) := by
    have he := Real.exp_one_lt_d9
    have hsq : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [sq, ← Real.exp_add]; norm_num
    have hpos := Real.exp_pos (1 / 2)
    have h53 : Real.exp (1 / 2) ≤ 5 / 3 := by nlinarith
    rw [Real.exp_neg]
    rw [le_inv_comm₀ (by norm_num) hpos]
    linarith
  have hx0 : Real.exp (-(A - 1 / 2)) * x₀ ≤ Real.exp A / 40 := by
    have h1 : Real.log (40 * x₀) + 1 ≤ A := hA
    have h2 : 40 * x₀ ≤ Real.exp (A - 1) := by
      rw [← Real.exp_log (by linarith : (0 : ℝ) < 40 * x₀)]
      exact Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (-(A - 1 / 2)) * Real.exp (A - 1) = Real.exp (-(1 / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have h4 : Real.exp (-(1 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    have h5 : Real.exp (-(A - 1 / 2)) * (40 * x₀) ≤ Real.exp (-(A - 1 / 2)) * Real.exp (A - 1) :=
      mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
    have hAexp : 1 ≤ Real.exp A := Real.one_le_exp (by linarith)
    nlinarith
  have hkey : Real.exp A / 4 ≤ Real.exp (-(A - 1 / 2)) * Chebyshev.psi X := by
    have h1 : Real.exp (-(A - 1 / 2)) * (X / 2 - x₀) ≤ Real.exp (-(A - 1 / 2)) * Chebyshev.psi X :=
      mul_le_mul_of_nonneg_left hψ' (Real.exp_pos _).le
    have h2 : Real.exp (-(A - 1 / 2)) * (X / 2 - x₀) =
        Real.exp (-(A - 1 / 2)) * X / 2 - Real.exp (-(A - 1 / 2)) * x₀ := by ring
    rw [h2, hE, hEA] at h1
    have hAexp := Real.exp_pos A
    nlinarith
  linarith

/-- **Dirichlet resonance.** For every finite range `2 ≤ n ≤ e^{2A}` and every `B`, there is a
natural number `τ ≥ B` with `cos(τ log n) ≥ 1/2` for all `n` in the range. -/
theorem exists_resonant_frequency (A : ℝ) (B : ℕ) :
    ∃ τ : ℕ, B ≤ τ ∧ ∀ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A)⌋₊,
      1 / 2 ≤ Real.cos ((τ : ℝ) * Real.log n) := by
  classical
  set S := Finset.Icc 2 ⌊Real.exp (2 * A)⌋₊ with hS
  set e := S.equivFin
  obtain ⟨τ, hτB, -, r, hr⟩ :=
    exists_fin_simultaneous_two_pi_phase_approximation_delayed_quantitative (Q := 9) (L := B)
      (fun i : Fin S.card => Real.log ((e.symm i : S) : ℕ))
  refine ⟨τ, hτB, fun n hn => ?_⟩
  set i := e ⟨n, hn⟩
  have h := hr i
  have hi : ((e.symm i : S) : ℕ) = n := by simp [i]
  rw [hi] at h
  have hc : Real.cos ((τ : ℝ) * Real.log n) =
      Real.cos ((τ : ℝ) * Real.log n - 2 * Real.pi * r i) := by
    rw [show (τ : ℝ) * Real.log n - 2 * Real.pi * r i = (τ : ℝ) * Real.log n - (r i : ℤ) * (2 * Real.pi)
      by ring]
    rw [Real.cos_sub_int_mul_two_pi]
  rw [hc]
  set y := (τ : ℝ) * Real.log n - 2 * Real.pi * r i
  have hy : |y| ≤ 2 * Real.pi / 10 := by
    have h10 : 2 * Real.pi / ((9 : ℕ) + 1 : ℝ) = 2 * Real.pi / 10 := by norm_num
    calc |y| ≤ 2 * Real.pi / ((9 : ℕ) + 1 : ℝ) := h
      _ = 2 * Real.pi / 10 := h10
  have hcos := Real.one_sub_sq_div_two_le_cos (x := y)
  have hy2 : y ^ 2 ≤ (2 * Real.pi / 10) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have : (2 * Real.pi / 10) ^ 2 ≤ 1 := by nlinarith [Real.pi_pos]
  linarith


/-! ## Pole moments and the pole-free correction -/

/-- The pole moment `∫ f(x) e^{sx} dx`; at `s = ±1/2` it is the value of the Fourier transform
`∫ f(x) e^{izx} dx` at `z = ∓ i/2`, i.e. at the two poles of the Weil form. -/
def poleMoment (s : ℝ) (f : ℝ → ℂ) : ℂ := ∫ x, f x * (Real.exp (s * x) : ℂ)

/-- The truncated exponential `1_{[-A,A]}(x) e^{sx}`. -/
def poleExp (A s : ℝ) : ℝ → ℂ := (Icc (-A) A).indicator fun x => (Real.exp (s * x) : ℂ)

/-- The correction `α 1_{[-A,A]} e^{x/2} + β 1_{[-A,A]} e^{-x/2}`. -/
def poleCorrection (A : ℝ) (α β : ℂ) (x : ℝ) : ℂ :=
  α * poleExp A (1 / 2) x + β * poleExp A (-1 / 2) x

theorem norm_poleExp_le {A s : ℝ} (x : ℝ) : ‖poleExp A s x‖ ≤ Real.exp (|s| * A) := by
  unfold poleExp
  simp only [indicator]
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    have hA : 0 ≤ A := by linarith [h.1, h.2]
    have hx : |x| ≤ A := abs_le.mpr h
    calc s * x ≤ |s * x| := le_abs_self _
      _ = |s| * |x| := abs_mul _ _
      _ ≤ |s| * A := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
  · simp only [norm_zero]; positivity

theorem norm_poleCorrection_le {A : ℝ} (α β : ℂ) (x : ℝ) :
    ‖poleCorrection A α β x‖ ≤ (‖α‖ + ‖β‖) * Real.exp (A / 2) := by
  unfold poleCorrection
  have h1 := norm_poleExp_le (A := A) (s := 1 / 2) x
  have h2 := norm_poleExp_le (A := A) (s := -1 / 2) x
  have e1 : |(1 / 2 : ℝ)| * A = A / 2 := by rw [abs_of_pos (by norm_num)]; ring
  have e2 : |(-1 / 2 : ℝ)| * A = A / 2 := by
    rw [abs_of_neg (by norm_num)]; ring
  rw [e1] at h1; rw [e2] at h2
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul]
  have := norm_nonneg α; have := norm_nonneg β
  have := mul_le_mul_of_nonneg_left h1 (norm_nonneg α)
  have := mul_le_mul_of_nonneg_left h2 (norm_nonneg β)
  linarith

theorem norm_modulatedFlat_le (A τ x : ℝ) : ‖modulatedFlat A τ x‖ ≤ 1 := by
  unfold modulatedFlat
  simp only [indicator]
  split_ifs
  · rw [Complex.norm_exp]
    have : (I * τ * x).re = 0 := by simp
    rw [this, Real.exp_zero]
  · simp

theorem norm_modulatedFlat_of_mem {A τ x : ℝ} (hx : x ∈ Icc (-A) A) :
    ‖modulatedFlat A τ x‖ = 1 := by
  unfold modulatedFlat
  rw [indicator_of_mem hx, Complex.norm_exp]
  have : (I * τ * x).re = 0 := by simp
  rw [this, Real.exp_zero]

theorem modulatedFlat_eq_zero {A τ x : ℝ} (hx : x ∉ Icc (-A) A) : modulatedFlat A τ x = 0 := by
  unfold modulatedFlat; exact indicator_of_notMem hx _

theorem poleCorrection_eq_zero {A x : ℝ} (α β : ℂ) (hx : x ∉ Icc (-A) A) :
    poleCorrection A α β x = 0 := by
  unfold poleCorrection poleExp
  rw [indicator_of_notMem hx, indicator_of_notMem hx]; ring

theorem measurable_modulatedFlat (A τ : ℝ) : Measurable (modulatedFlat A τ) := by
  unfold modulatedFlat
  exact (by fun_prop : Measurable fun x : ℝ => cexp (I * τ * x)).indicator measurableSet_Icc

theorem measurable_poleExp (A s : ℝ) : Measurable (poleExp A s) := by
  unfold poleExp
  exact (by fun_prop : Measurable fun x : ℝ => (Real.exp (s * x) : ℂ)).indicator measurableSet_Icc

theorem measurable_poleCorrection (A : ℝ) (α β : ℂ) : Measurable (poleCorrection A α β) := by
  unfold poleCorrection
  exact (measurable_const.mul (measurable_poleExp A _)).add
    (measurable_const.mul (measurable_poleExp A _))

/-- A bounded measurable function supported in `[-A, A]` is integrable. -/
theorem integrable_of_bounded_supported {E : Type*} [NormedAddCommGroup E] {F : ℝ → E} {A M : ℝ}
    (hF : AEStronglyMeasurable F) (hM : ∀ x, ‖F x‖ ≤ M) (hs : ∀ x, x ∉ Icc (-A) A → F x = 0) :
    Integrable F := by
  have hint : Integrable ((Icc (-A) A).indicator fun _ : ℝ => M) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  refine hint.mono' hF (Eventually.of_forall fun x => ?_)
  simp only [indicator]
  split_ifs with h
  · exact hM x
  · rw [hs x h, norm_zero]

/-- A continuous function truncated to `[-A, A]`, times a continuous function, is integrable. -/
theorem integrable_indicator_mul {F G : ℝ → ℂ} (hF : Continuous F) (hG : Continuous G) (A : ℝ) :
    Integrable fun x => (Icc (-A) A).indicator F x * G x := by
  have e : (fun x => (Icc (-A) A).indicator F x * G x) =
      (Icc (-A) A).indicator (fun x => F x * G x) := by
    funext x; rw [indicator_mul_left]
  rw [e]
  exact ((hF.mul hG).integrableOn_Icc).integrable_indicator measurableSet_Icc

/-- The pole moment of the modulated flat vector:
`∫_{-A}^{A} e^{(iτ+s)x} dx = (e^{(iτ+s)A} - e^{-(iτ+s)A})/(iτ+s)`. -/
theorem poleMoment_modulatedFlat {A τ s : ℝ} (hA : 0 ≤ A) (hc : (I * τ + s : ℂ) ≠ 0) :
    poleMoment s (modulatedFlat A τ) =
      (cexp ((I * τ + s) * A) - cexp ((I * τ + s) * (-A : ℝ))) / (I * τ + s) := by
  unfold poleMoment modulatedFlat
  have e : (fun x : ℝ => (Icc (-A) A).indicator (fun x => cexp (I * τ * x)) x *
      (Real.exp (s * x) : ℂ)) = (Icc (-A) A).indicator (fun x : ℝ => cexp ((I * τ + s) * x)) := by
    funext x
    simp only [indicator]
    split_ifs
    · rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1; push_cast; ring
    · simp
  rw [e, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), integral_exp_mul_complex hc]

/-- The pole moment of the modulated flat vector is `O(e^{|s|A}/τ)`: the oscillation at
frequency `τ` beats the exponential weight. -/
theorem norm_poleMoment_modulatedFlat_le {A τ s : ℝ} (hA : 0 ≤ A) (hτ : 0 < τ) :
    ‖poleMoment s (modulatedFlat A τ)‖ ≤ 2 * Real.exp (|s| * A) / τ := by
  have hc : (I * τ + s : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  rw [poleMoment_modulatedFlat hA hc, norm_div]
  have hden : τ ≤ ‖(I * τ + s : ℂ)‖ := by
    have h1 := Complex.abs_im_le_norm (I * τ + s : ℂ)
    have h2 : (I * τ + s : ℂ).im = τ := by simp
    rw [h2, abs_of_pos hτ] at h1
    exact h1
  have hnum : ‖cexp ((I * τ + s) * A) - cexp ((I * τ + s) * (-A : ℝ))‖ ≤
      2 * Real.exp (|s| * A) := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_exp, Complex.norm_exp]
    have r1 : ((I * τ + s) * (A : ℂ)).re = s * A := by simp
    have r2 : ((I * τ + s) * ((-A : ℝ) : ℂ)).re = -(s * A) := by simp
    rw [r1, r2]
    have b1 : Real.exp (s * A) ≤ Real.exp (|s| * A) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self s) hA)
    have b2 : Real.exp (-(s * A)) ≤ Real.exp (|s| * A) :=
      Real.exp_le_exp.mpr (by
        have := mul_le_mul_of_nonneg_right (neg_le_abs s) hA
        linarith)
    linarith
  calc ‖cexp ((I * τ + s) * A) - cexp ((I * τ + s) * (-A : ℝ))‖ / ‖(I * τ + s : ℂ)‖
      ≤ 2 * Real.exp (|s| * A) / ‖(I * τ + s : ℂ)‖ :=
        div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ 2 * Real.exp (|s| * A) / τ :=
        div_le_div_of_nonneg_left (by positivity) hτ hden

/-- The Gram entries of the two truncated exponentials:
`∫ 1_{[-A,A]} e^{s₁x} e^{s₂x} dx = ∫_{-A}^{A} e^{(s₁+s₂)x} dx`. -/
theorem poleMoment_poleExp (A s₁ s₂ : ℝ) (hA : 0 ≤ A) :
    poleMoment s₂ (poleExp A s₁) = ((∫ x in (-A)..A, Real.exp ((s₁ + s₂) * x) : ℝ) : ℂ) := by
  unfold poleMoment poleExp
  have e : (fun x : ℝ => (Icc (-A) A).indicator (fun x => (Real.exp (s₁ * x) : ℂ)) x *
      (Real.exp (s₂ * x) : ℂ)) =
      fun x => (((Icc (-A) A).indicator (fun x => Real.exp ((s₁ + s₂) * x)) x : ℝ) : ℂ) := by
    funext x
    simp only [indicator]
    split_ifs
    · rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    · simp
  rw [e, integral_complex_ofReal, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith)]

theorem poleMoment_poleExp_same (A : ℝ) (hA : 0 ≤ A) :
    poleMoment (1 / 2) (poleExp A (1 / 2)) = ((Real.exp A - Real.exp (-A) : ℝ) : ℂ) := by
  rw [poleMoment_poleExp A _ _ hA]
  congr 1
  have : (fun x : ℝ => Real.exp ((1 / 2 + 1 / 2) * x)) = Real.exp := by
    funext x; congr 1; ring
  rw [this, integral_exp]

theorem poleMoment_poleExp_same_neg (A : ℝ) (hA : 0 ≤ A) :
    poleMoment (-1 / 2) (poleExp A (-1 / 2)) = ((Real.exp A - Real.exp (-A) : ℝ) : ℂ) := by
  rw [poleMoment_poleExp A _ _ hA]
  congr 1
  have : (fun x : ℝ => Real.exp ((-1 / 2 + -1 / 2) * x)) = fun x => Real.exp (-x) := by
    funext x; congr 1; ring
  rw [this, intervalIntegral.integral_comp_neg, integral_exp]
  ring_nf

theorem poleMoment_poleExp_cross (A : ℝ) (hA : 0 ≤ A) :
    poleMoment (-1 / 2) (poleExp A (1 / 2)) = ((2 * A : ℝ) : ℂ) := by
  rw [poleMoment_poleExp A _ _ hA]
  congr 1
  have : (fun x : ℝ => Real.exp ((1 / 2 + -1 / 2) * x)) = fun _ => 1 := by
    funext x; norm_num
  rw [this, intervalIntegral.integral_const, smul_eq_mul]; ring

theorem poleMoment_poleExp_cross' (A : ℝ) (hA : 0 ≤ A) :
    poleMoment (1 / 2) (poleExp A (-1 / 2)) = ((2 * A : ℝ) : ℂ) := by
  rw [poleMoment_poleExp A _ _ hA]
  congr 1
  have : (fun x : ℝ => Real.exp ((-1 / 2 + 1 / 2) * x)) = fun _ => 1 := by
    funext x; norm_num
  rw [this, intervalIntegral.integral_const, smul_eq_mul]; ring

/-- The pole moment is linear across the correction. -/
theorem poleMoment_sub_poleCorrection (A τ s : ℝ) (α β : ℂ) :
    poleMoment s (fun x => modulatedFlat A τ x - poleCorrection A α β x) =
      poleMoment s (modulatedFlat A τ) - α * poleMoment s (poleExp A (1 / 2)) -
        β * poleMoment s (poleExp A (-1 / 2)) := by
  unfold poleMoment poleCorrection
  have hc : Continuous fun x : ℝ => (Real.exp (s * x) : ℂ) := by fun_prop
  have i1 : Integrable fun x => modulatedFlat A τ x * (Real.exp (s * x) : ℂ) :=
    integrable_indicator_mul (by fun_prop) hc A
  have i2 : Integrable fun x => poleExp A (1 / 2) x * (Real.exp (s * x) : ℂ) :=
    integrable_indicator_mul (by fun_prop) hc A
  have i3 : Integrable fun x => poleExp A (-1 / 2) x * (Real.exp (s * x) : ℂ) :=
    integrable_indicator_mul (by fun_prop) hc A
  have e : (fun x => (modulatedFlat A τ x - (α * poleExp A (1 / 2) x +
      β * poleExp A (-1 / 2) x)) * (Real.exp (s * x) : ℂ)) =
      fun x => modulatedFlat A τ x * (Real.exp (s * x) : ℂ) -
        (α * (poleExp A (1 / 2) x * (Real.exp (s * x) : ℂ)) +
          β * (poleExp A (-1 / 2) x * (Real.exp (s * x) : ℂ))) := by
    funext x; ring
  have i23 : Integrable fun x => α * (poleExp A (1 / 2) x * (Real.exp (s * x) : ℂ)) +
      β * (poleExp A (-1 / 2) x * (Real.exp (s * x) : ℂ)) := (i2.const_mul α).add (i3.const_mul β)
  rw [e, integral_sub i1 i23, integral_add (i2.const_mul α) (i3.const_mul β), integral_const_mul,
    integral_const_mul]
  ring

/-- **Solving the 2×2 pole system.** With `S = e^A - e^{-A}` and Gram matrix `[[S, 2A],[2A, S]]`,
the coefficients `α = (S J₊ - 2A J₋)/(S² - 4A²)`, `β = (S J₋ - 2A J₊)/(S² - 4A²)` solve
`α S + β 2A = J₊`, `α 2A + β S = J₋`. -/
theorem pole_system_solve {S A : ℝ} (hD : S ^ 2 - 4 * A ^ 2 ≠ 0) (Jp Jm : ℂ) :
    Jp - (S * Jp - 2 * A * Jm) / (S ^ 2 - 4 * A ^ 2) * S -
        (S * Jm - 2 * A * Jp) / (S ^ 2 - 4 * A ^ 2) * (2 * A) = 0 ∧
      Jm - (S * Jp - 2 * A * Jm) / (S ^ 2 - 4 * A ^ 2) * (2 * A) -
        (S * Jm - 2 * A * Jp) / (S ^ 2 - 4 * A ^ 2) * S = 0 := by
  have hD' : ((S : ℂ) ^ 2 - 4 * (A : ℂ) ^ 2) ≠ 0 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_ofNat, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub]
    exact_mod_cast hD
  constructor <;>
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, sub_sub, ← add_div, sub_eq_zero, eq_div_iff hD']
    ring

/-- The coefficient bound: `‖(S Jp - 2A Jm)/(S² - 4A²)‖ ≤ K/m` when `‖J±‖ ≤ K` and
`S - 2A ≥ m > 0`. -/
theorem norm_pole_coefficient_le {S A K m : ℝ} (hA : 0 ≤ A) (hm : 0 < m) (hSm : m ≤ S - 2 * A)
    {J₁ J₂ : ℂ} (h₁ : ‖J₁‖ ≤ K) (h₂ : ‖J₂‖ ≤ K) :
    ‖((S : ℂ) * J₁ - 2 * A * J₂) / ((S : ℂ) ^ 2 - 4 * (A : ℂ) ^ 2)‖ ≤ K / m := by
  have hS : 0 < S := by linarith
  have hK : 0 ≤ K := (norm_nonneg _).trans h₁
  have hden : ((S : ℂ) ^ 2 - 4 * (A : ℂ) ^ 2) = (((S - 2 * A) * (S + 2 * A) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hden, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (mul_pos (by linarith) (by linarith))]
  have hnum : ‖(S : ℂ) * J₁ - 2 * A * J₂‖ ≤ (S + 2 * A) * K := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hS, abs_of_nonneg hA, Complex.norm_ofNat]
    have := mul_le_mul_of_nonneg_left h₁ hS.le
    have := mul_le_mul_of_nonneg_left h₂ (by linarith : (0 : ℝ) ≤ 2 * A)
    nlinarith
  rw [div_le_div_iff₀ (mul_pos (by linarith) (by linarith)) hm]
  calc ‖(S : ℂ) * J₁ - 2 * A * J₂‖ * m ≤ ((S + 2 * A) * K) * (S - 2 * A) :=
        mul_le_mul hnum hSm hm.le (by positivity)
    _ = K * ((S - 2 * A) * (S + 2 * A)) := by ring

/-- **Perturbation of the prime translation form.** If `‖u‖, ‖v‖ ≤ 1` and the perturbation `h`
has `‖h‖ ≤ ε`, all supported in `[-A, A]`, then the autocorrelation at a shift moves by at most
`2A ε (2 + ε)`. -/
theorem norm_autocorr_sub_le {A ℓ ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) {g h : ℝ → ℂ}
    (hg : Measurable g) (hh : Measurable h) (hg1 : ∀ x, ‖g x‖ ≤ 1) (hhε : ∀ x, ‖h x‖ ≤ ε)
    (hgs : ∀ x, x ∉ Icc (-A) A → g x = 0) (hhs : ∀ x, x ∉ Icc (-A) A → h x = 0) :
    ‖(∫ x, (g (x + ℓ) - h (x + ℓ)) * (starRingEnd ℂ) (g x - h x)) -
        ∫ x, g (x + ℓ) * (starRingEnd ℂ) (g x)‖ ≤ 2 * A * (ε * (2 + ε)) := by
  set F := fun x => (g (x + ℓ) - h (x + ℓ)) * (starRingEnd ℂ) (g x - h x) with hF
  set G := fun x => g (x + ℓ) * (starRingEnd ℂ) (g x) with hG
  have hsh : ∀ {k : ℝ → ℂ}, Measurable k → Measurable fun x => k (x + ℓ) :=
    fun hk => hk.comp (measurable_id.add_const ℓ)
  have hFm : Measurable F := by
    simp only [hF]
    exact ((hsh hg).sub (hsh hh)).mul (Complex.continuous_conj.measurable.comp (hg.sub hh))
  have hGm : Measurable G := by
    simp only [hG]; exact (hsh hg).mul (Complex.continuous_conj.measurable.comp hg)
  have hFb : ∀ x, ‖F x‖ ≤ (1 + ε) * (1 + ε) := by
    intro x
    simp only [hF]
    rw [norm_mul, RCLike.norm_conj]
    have h1 : ‖g (x + ℓ) - h (x + ℓ)‖ ≤ 1 + ε := (norm_sub_le _ _).trans (add_le_add (hg1 _) (hhε _))
    have h2 : ‖g x - h x‖ ≤ 1 + ε := (norm_sub_le _ _).trans (add_le_add (hg1 _) (hhε _))
    exact mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
  have hGb : ∀ x, ‖G x‖ ≤ 1 := by
    intro x
    simp only [hG]
    rw [norm_mul, RCLike.norm_conj]
    have := hg1 (x + ℓ); have := hg1 x
    nlinarith [norm_nonneg (g (x + ℓ)), norm_nonneg (g x)]
  have hFs : ∀ x, x ∉ Icc (-A) A → F x = 0 := fun x hx => by
    simp only [hF]; rw [hgs x hx, hhs x hx]; simp
  have hGs : ∀ x, x ∉ Icc (-A) A → G x = 0 := fun x hx => by
    simp only [hG]; rw [hgs x hx]; simp
  have hFi := integrable_of_bounded_supported hFm.aestronglyMeasurable hFb hFs
  have hGi := integrable_of_bounded_supported hGm.aestronglyMeasurable hGb hGs
  rw [← integral_sub hFi hGi]
  have hpt : ∀ x, ‖F x - G x‖ ≤ (Icc (-A) A).indicator (fun _ => ε * (2 + ε)) x := by
    intro x
    simp only [indicator]
    split_ifs with hx
    · simp only [hF, hG]
      have e : (g (x + ℓ) - h (x + ℓ)) * (starRingEnd ℂ) (g x - h x) -
          g (x + ℓ) * (starRingEnd ℂ) (g x) =
          -(h (x + ℓ) * (starRingEnd ℂ) (g x)) - g (x + ℓ) * (starRingEnd ℂ) (h x) +
            h (x + ℓ) * (starRingEnd ℂ) (h x) := by
        rw [map_sub]; ring
      rw [e]
      have a1 : ‖h (x + ℓ) * (starRingEnd ℂ) (g x)‖ ≤ ε * 1 := by
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (hhε _) (hg1 _) (norm_nonneg _) hε
      have a2 : ‖g (x + ℓ) * (starRingEnd ℂ) (h x)‖ ≤ 1 * ε := by
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (hg1 _) (hhε _) (norm_nonneg _) zero_le_one
      have a3 : ‖h (x + ℓ) * (starRingEnd ℂ) (h x)‖ ≤ ε * ε := by
        rw [norm_mul, RCLike.norm_conj]
        exact mul_le_mul (hhε _) (hhε _) (norm_nonneg _) hε
      calc ‖-(h (x + ℓ) * (starRingEnd ℂ) (g x)) - g (x + ℓ) * (starRingEnd ℂ) (h x) +
            h (x + ℓ) * (starRingEnd ℂ) (h x)‖
          ≤ ‖h (x + ℓ) * (starRingEnd ℂ) (g x)‖ + ‖g (x + ℓ) * (starRingEnd ℂ) (h x)‖ +
            ‖h (x + ℓ) * (starRingEnd ℂ) (h x)‖ := by
            have b1 := norm_add_le (-(h (x + ℓ) * (starRingEnd ℂ) (g x)) -
              g (x + ℓ) * (starRingEnd ℂ) (h x)) (h (x + ℓ) * (starRingEnd ℂ) (h x))
            have b2 := norm_sub_le (-(h (x + ℓ) * (starRingEnd ℂ) (g x)))
              (g (x + ℓ) * (starRingEnd ℂ) (h x))
            rw [norm_neg] at b2
            linarith
        _ ≤ ε * 1 + 1 * ε + ε * ε := by linarith
        _ = ε * (2 + ε) := by ring
    · rw [hFs x hx, hGs x hx, sub_zero, norm_zero]
  calc ‖∫ x, (F x - G x)‖ ≤ ∫ x, ‖F x - G x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, (Icc (-A) A).indicator (fun _ => ε * (2 + ε)) x := by
        apply integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
        · exact (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
        · exact Eventually.of_forall hpt
    _ = 2 * A * (ε * (2 + ε)) := by
        rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring


/-- The total prime weight `Σ_{2 ≤ n ≤ e^{2A}} Λ(n) n^{-1/2}`. -/
def vonMangoldtHalfWeightSum (A : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A)⌋₊, ArithmeticFunction.vonMangoldt n / Real.sqrt n

theorem vonMangoldtHalfWeightSum_nonneg (A : ℝ) : 0 ≤ vonMangoldtHalfWeightSum A :=
  Finset.sum_nonneg fun _ _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)

/-- **Stability of the prime translation form.** Perturbing a unit-bounded vector `g` by `h` with
`‖h‖ ≤ ε`, both supported in `[-A, A]`, moves the form by at most `4A ε (2 + ε)` times the total
prime weight. -/
theorem norm_primeTranslationForm_sub_le {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε) {g h : ℝ → ℂ}
    (hg : Measurable g) (hh : Measurable h) (hg1 : ∀ x, ‖g x‖ ≤ 1) (hhε : ∀ x, ‖h x‖ ≤ ε)
    (hgs : ∀ x, x ∉ Icc (-A) A → g x = 0) (hhs : ∀ x, x ∉ Icc (-A) A → h x = 0) :
    ‖primeTranslationForm A (fun x => g x - h x) (fun x => g x - h x) -
        primeTranslationForm A g g‖ ≤ vonMangoldtHalfWeightSum A * (4 * A * (ε * (2 + ε))) := by
  unfold primeTranslationForm vonMangoldtHalfWeightSum
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have hc : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have h1 := norm_autocorr_sub_le (ℓ := Real.log n) hA hε hg hh hg1 hhε hgs hhs
  have h2 := norm_autocorr_sub_le (ℓ := -Real.log n) hA hε hg hh hg1 hhε hgs hhs
  simp only [← sub_eq_add_neg] at h2
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  have e : ((∫ x, (g (x + Real.log n) - h (x + Real.log n)) *
        (starRingEnd ℂ) (g x - h x)) +
      ∫ x, (g (x - Real.log n) - h (x - Real.log n)) * (starRingEnd ℂ) (g x - h x)) -
      ((∫ x, g (x + Real.log n) * (starRingEnd ℂ) (g x)) +
        ∫ x, g (x - Real.log n) * (starRingEnd ℂ) (g x)) =
      ((∫ x, (g (x + Real.log n) - h (x + Real.log n)) * (starRingEnd ℂ) (g x - h x)) -
        ∫ x, g (x + Real.log n) * (starRingEnd ℂ) (g x)) +
      ((∫ x, (g (x - Real.log n) - h (x - Real.log n)) * (starRingEnd ℂ) (g x - h x)) -
        ∫ x, g (x - Real.log n) * (starRingEnd ℂ) (g x)) := by ring
  rw [e]
  have h3 := norm_add_le
    ((∫ x, (g (x + Real.log n) - h (x + Real.log n)) * (starRingEnd ℂ) (g x - h x)) -
        ∫ x, g (x + Real.log n) * (starRingEnd ℂ) (g x))
    ((∫ x, (g (x - Real.log n) - h (x - Real.log n)) * (starRingEnd ℂ) (g x - h x)) -
        ∫ x, g (x - Real.log n) * (starRingEnd ℂ) (g x))
  have h4 : ‖((∫ x, (g (x + Real.log n) - h (x + Real.log n)) * (starRingEnd ℂ) (g x - h x)) -
        ∫ x, g (x + Real.log n) * (starRingEnd ℂ) (g x)) +
      ((∫ x, (g (x - Real.log n) - h (x - Real.log n)) * (starRingEnd ℂ) (g x - h x)) -
        ∫ x, g (x - Real.log n) * (starRingEnd ℂ) (g x))‖ ≤ 4 * A * (ε * (2 + ε)) := by
    linarith
  exact mul_le_mul_of_nonneg_left h4 hc

/-- **The resonant flat vector sees the whole hinge sum.** If `cos(τ log n) ≥ 1/2` for every
`n ≤ e^{2A}`, the prime translation form of the modulated flat vector has real part at least
`Σ Λ(n) n^{-1/2}(2A - log n)`. -/
theorem primeHinge_le_re_resonant {A τ : ℝ}
    (hres : ∀ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A)⌋₊, 1 / 2 ≤ Real.cos (τ * Real.log n)) :
    primeHinge A ≤ (primeTranslationForm A (modulatedFlat A τ) (modulatedFlat A τ)).re := by
  unfold primeTranslationForm primeHinge
  rw [Complex.re_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
  have hℓ0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  have hℓA := log_le_two_mul_of_mem hn
  rw [integral_modulatedFlat_shift hℓ0 hℓA, integral_modulatedFlat_shift_neg hℓ0 hℓA]
  have hre : (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (cexp (I * τ * Real.log n) * ((2 * A - Real.log n : ℝ) : ℂ) +
        cexp (-(I * τ * Real.log n)) * ((2 * A - Real.log n : ℝ) : ℂ))).re =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n * (2 * A - Real.log n) *
        (2 * Real.cos (τ * Real.log n)) := by
    rw [Complex.re_ofReal_mul]
    simp only [Complex.add_re, Complex.exp_re, Complex.neg_re,
      Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, Real.cos_neg]
    simp only [zero_mul, one_mul, sub_zero, mul_zero, neg_zero, Real.exp_zero]
    ring_nf
  rw [hre]
  have hc : 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hcos := hres n hn
  have h2 : 0 ≤ 2 * A - Real.log n := by linarith
  have hp := mul_nonneg hc h2
  nlinarith


/-- The `L²` mass of a small perturbation of the flat vector: `A/2 ≤ ∫ |g - h|² ≤ 9A/2`
when `‖h‖ ≤ 1/2` and `h` is supported in `[-A, A]`. -/
theorem l2mass_modulatedFlat_sub {A τ ε : ℝ} (hA : 0 ≤ A) (hε : ε ≤ 1 / 2) {h : ℝ → ℂ}
    (hh : Measurable h) (hhε : ∀ x, ‖h x‖ ≤ ε) (hhs : ∀ x, x ∉ Icc (-A) A → h x = 0) :
    A / 2 ≤ ∫ x, ‖modulatedFlat A τ x - h x‖ ^ 2 ∧
      ∫ x, ‖modulatedFlat A τ x - h x‖ ^ 2 ≤ 9 * A / 2 := by
  have hfm : Measurable fun x => modulatedFlat A τ x - h x := (measurable_modulatedFlat A τ).sub hh
  have hfs : ∀ x, x ∉ Icc (-A) A → modulatedFlat A τ x - h x = 0 := fun x hx => by
    rw [modulatedFlat_eq_zero hx, hhs x hx, sub_zero]
  have hf1 : ∀ x, ‖modulatedFlat A τ x - h x‖ ≤ 3 / 2 := fun x =>
    (norm_sub_le _ _).trans (by linarith [norm_modulatedFlat_le A τ x, hhε x])
  have hf2 : ∀ x, ‖modulatedFlat A τ x - h x‖ ^ 2 ≤ 9 / 4 := fun x => by
    have := hf1 x
    have := norm_nonneg (modulatedFlat A τ x - h x)
    nlinarith
  have hfint : Integrable fun x => ‖modulatedFlat A τ x - h x‖ ^ 2 := by
    refine integrable_of_bounded_supported (A := A) (M := 9 / 4)
      ((hfm.norm.pow_const 2).aestronglyMeasurable) (fun x => ?_) (fun x hx => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hf2 x
    · rw [hfs x hx, norm_zero]; norm_num
  have hvol : ∀ c : ℝ, ∫ x, (Icc (-A) A).indicator (fun _ : ℝ => c) x = 2 * A * c := fun c => by
    rw [integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  have hind : ∀ c : ℝ, Integrable ((Icc (-A) A).indicator fun _ : ℝ => c) := fun c =>
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  constructor
  · have hmono := integral_mono (hind (1 / 4)) hfint fun x => by
      simp only [indicator]
      split_ifs with hx
      · have h1 : 1 / 2 ≤ ‖modulatedFlat A τ x - h x‖ := by
          have := norm_sub_norm_le (modulatedFlat A τ x) (h x)
          rw [norm_modulatedFlat_of_mem hx] at this
          linarith [hhε x]
        nlinarith
      · positivity
    rw [hvol] at hmono
    linarith
  · have hmono := integral_mono hfint (hind (9 / 4)) fun x => by
      simp only [indicator]
      split_ifs with hx
      · exact hf2 x
      · rw [hfs x hx, norm_zero]; norm_num
    rw [hvol] at hmono
    linarith

/-- The resonant lower bound survives a small perturbation:
`Re Q(g - h) ≥ Σ Λ(n) n^{-1/2}(2A - log n) - 4A ε(2 + ε) Σ Λ(n) n^{-1/2}`. -/
theorem re_primeTranslationForm_resonant_sub_ge {A τ ε : ℝ} (hA : 0 ≤ A) (hε : 0 ≤ ε)
    (hres : ∀ n ∈ Finset.Icc 2 ⌊Real.exp (2 * A)⌋₊, 1 / 2 ≤ Real.cos (τ * Real.log n))
    {h : ℝ → ℂ} (hh : Measurable h) (hhε : ∀ x, ‖h x‖ ≤ ε)
    (hhs : ∀ x, x ∉ Icc (-A) A → h x = 0) :
    primeHinge A - vonMangoldtHalfWeightSum A * (4 * A * (ε * (2 + ε))) ≤
      (primeTranslationForm A (fun x => modulatedFlat A τ x - h x)
        (fun x => modulatedFlat A τ x - h x)).re := by
  have hpert := norm_primeTranslationForm_sub_le hA hε (measurable_modulatedFlat A τ) hh
    (norm_modulatedFlat_le A τ) hhε (fun x hx => modulatedFlat_eq_zero hx) hhs
  have hres' := primeHinge_le_re_resonant (A := A) (τ := τ) hres
  have hre := Complex.abs_re_le_norm
    (primeTranslationForm A (fun x => modulatedFlat A τ x - h x)
        (fun x => modulatedFlat A τ x - h x) -
      primeTranslationForm A (modulatedFlat A τ) (modulatedFlat A τ))
  rw [Complex.sub_re] at hre
  have := (abs_le.mp hre).1
  linarith

/-- The pole correction built from the two pole moments of the modulated flat vector is
uniformly `≤ 8/τ` once `S - 2A ≥ e^A/2`. -/
theorem norm_poleCorrection_resonant_le {A τ S : ℝ} (hA : 0 ≤ A) (hτ : 0 < τ)
    (hSm : Real.exp A / 2 ≤ S - 2 * A) (x : ℝ) :
    ‖poleCorrection A
        (((S : ℂ) * poleMoment (1 / 2) (modulatedFlat A τ) -
            2 * A * poleMoment (-1 / 2) (modulatedFlat A τ)) / ((S : ℂ) ^ 2 - 4 * (A : ℂ) ^ 2))
        (((S : ℂ) * poleMoment (-1 / 2) (modulatedFlat A τ) -
            2 * A * poleMoment (1 / 2) (modulatedFlat A τ)) / ((S : ℂ) ^ 2 - 4 * (A : ℂ) ^ 2))
        x‖ ≤ 8 / τ := by
  have hJp : ‖poleMoment (1 / 2) (modulatedFlat A τ)‖ ≤ 2 * Real.exp (A / 2) / τ := by
    have := norm_poleMoment_modulatedFlat_le (s := 1 / 2) hA hτ
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at this
    convert this using 3; ring_nf
  have hJm : ‖poleMoment (-1 / 2) (modulatedFlat A τ)‖ ≤ 2 * Real.exp (A / 2) / τ := by
    have := norm_poleMoment_modulatedFlat_le (s := -1 / 2) hA hτ
    rw [abs_of_neg (by norm_num : (-1 / 2 : ℝ) < 0)] at this
    convert this using 3; ring_nf
  have hm : 0 < Real.exp A / 2 := by positivity
  have hα := norm_pole_coefficient_le hA hm hSm hJp hJm
  have hβ := norm_pole_coefficient_le hA hm hSm hJm hJp
  refine (norm_poleCorrection_le _ _ x).trans ?_
  have hKexp : 2 * Real.exp (A / 2) / τ / (Real.exp A / 2) * Real.exp (A / 2) = 4 / τ := by
    have e2 : Real.exp (A / 2) ^ 2 = Real.exp A := by
      rw [sq, ← Real.exp_add]; ring_nf
    field_simp
    rw [e2]; ring
  calc _ ≤ (2 * Real.exp (A / 2) / τ / (Real.exp A / 2) +
        2 * Real.exp (A / 2) / τ / (Real.exp A / 2)) * Real.exp (A / 2) :=
        mul_le_mul_of_nonneg_right (add_le_add hα hβ) (Real.exp_pos _).le
    _ = 8 / τ := by rw [add_mul, hKexp]; ring

theorem exp_half_sub_le_sinh_gap {A : ℝ} (hA : 8 ≤ A) :
    Real.exp A / 2 ≤ (Real.exp A - Real.exp (-A)) - 2 * A := by
  have h1 := Real.quadratic_le_exp_of_nonneg (by linarith : (0 : ℝ) ≤ A)
  have h2 : Real.exp (-A) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  nlinarith

/-- The arithmetic of the resonance: with `τ ≥ 768 C A e^{-A}`, `ε = 8/τ ≤ 1/2`, hinge `≥ e^A/4`
and `A/2 ≤ m ≤ 9A/2`, one has `(e^A/(64A)) m ≤ hinge - 4AC ε(2+ε)`. -/
theorem resonance_arith {A C τ H m : ℝ} (hA : 0 < A) (hC : 0 ≤ C) (hτ : 0 < τ)
    (hτC : 768 * C * A / Real.exp A ≤ τ) (hε : 8 / τ ≤ 1 / 2) (hH : Real.exp A / 4 ≤ H)
    (hm : m ≤ 9 * A / 2) :
    Real.exp A / (64 * A) * m ≤ H - C * (4 * A * (8 / τ * (2 + 8 / τ))) := by
  have heA : 0 < Real.exp A := Real.exp_pos _
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = 8 / τ := ⟨_, rfl⟩
  rw [← hεdef] at hε ⊢
  have hε0 : 0 ≤ ε := by rw [hεdef]; positivity
  have h1 : ε * (2 + ε) ≤ 3 * ε := by nlinarith
  have h2 : C * (4 * A * (ε * (2 + ε))) ≤ C * (4 * A * (3 * ε)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (by linarith)) hC
  have h3 : C * (4 * A * (3 * ε)) = 96 * C * A / τ := by rw [hεdef]; field_simp; ring
  have h4 : 96 * C * A / τ ≤ Real.exp A / 8 := by
    rw [div_le_iff₀ hτ]
    rw [div_le_iff₀ heA] at hτC
    nlinarith
  have h5 : Real.exp A / (64 * A) * m ≤ Real.exp A / (64 * A) * (9 * A / 2) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have h6 : Real.exp A / (64 * A) * (9 * A / 2) = 9 * Real.exp A / 128 := by
    field_simp; ring
  linarith

/-- **The pole-compressed prime translation form grows like `e^A/A`.** For every large level `A`
there is a vector `f` supported in `[-A, A]`, bounded by `2`, annihilated by both pole moments
`∫ f e^{±x/2} = 0`, with `∫ |f|² > 0` and
`Re Σ_{n ≤ e^{2A}} Λ(n) n^{-1/2} ⟨(τ_{log n} + τ_{-log n}) f, f⟩ ≥ (e^A/(64A)) ∫ |f|²`.

The vector is a flat vector modulated at an integer frequency `τ` resonant with every `log n`,
`n ≤ e^{2A}` (`cos(τ log n) ≥ 1/2`, Dirichlet), corrected by a combination of `e^{±x/2}` to kill the
pole moments.  The pole moments of the modulated flat vector are `O(e^{A/2}/τ)`, so for large `τ` the
correction is uniformly small and the form keeps the hinge sum `Σ Λ(n) n^{-1/2}(2A - log n) ≥ e^A/4`
(prime number theorem).  No hypothesis on the zeros enters. -/
theorem poleFree_primeTranslation_resonance :
    ∃ A₀ : ℝ, ∀ A : ℝ, A₀ ≤ A → ∃ f : ℝ → ℂ, Measurable f ∧ (∀ x, ‖f x‖ ≤ 2) ∧
      (∀ x, x ∉ Icc (-A) A → f x = 0) ∧ poleMoment (1 / 2) f = 0 ∧
      poleMoment (-1 / 2) f = 0 ∧ 0 < ∫ x, ‖f x‖ ^ 2 ∧
      Real.exp A / (64 * A) * ∫ x, ‖f x‖ ^ 2 ≤ (primeTranslationForm A f f).re := by
  obtain ⟨A₁, hA₁⟩ := exists_primeHinge_ge
  refine ⟨max A₁ 8, fun A hA => ?_⟩
  have hA8 : 8 ≤ A := le_of_max_le_right hA
  have hA0 : 0 ≤ A := by linarith
  have hhinge := hA₁ A (le_of_max_le_left hA)
  obtain ⟨C, hC⟩ : ∃ C, C = vonMangoldtHalfWeightSum A := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := hC ▸ vonMangoldtHalfWeightSum_nonneg A
  obtain ⟨τn, hBτ, hres⟩ := exists_resonant_frequency A (⌈768 * C * A / Real.exp A⌉₊ + 16)
  obtain ⟨τ, hτdef⟩ : ∃ τ : ℝ, τ = τn := ⟨_, rfl⟩
  have hBτ' : ((⌈768 * C * A / Real.exp A⌉₊ + 16 : ℕ) : ℝ) ≤ τ := by
    rw [hτdef]; exact_mod_cast hBτ
  push_cast at hBτ'
  have hceil := Nat.le_ceil (768 * C * A / Real.exp A)
  have hτ16 : 16 ≤ τ := by linarith [Nat.cast_nonneg (α := ℝ) ⌈768 * C * A / Real.exp A⌉₊]
  have hτpos : 0 < τ := by linarith
  have hτC : 768 * C * A / Real.exp A ≤ τ := by linarith
  have hεhalf : 8 / τ ≤ 1 / 2 := by rw [div_le_iff₀ hτpos]; linarith
  rw [← hτdef] at hres
  obtain ⟨S, hS⟩ : ∃ S, S = Real.exp A - Real.exp (-A) := ⟨_, rfl⟩
  have hSm : Real.exp A / 2 ≤ S - 2 * A := hS ▸ exp_half_sub_le_sinh_gap hA8
  have heA := Real.exp_pos A
  have hD : S ^ 2 - 4 * A ^ 2 ≠ 0 := by
    have : 0 < S - 2 * A := by linarith
    have : 0 < S + 2 * A := by linarith
    nlinarith
  obtain ⟨Jp, hJp⟩ : ∃ J, J = poleMoment (1 / 2) (modulatedFlat A τ) := ⟨_, rfl⟩
  obtain ⟨Jm, hJm⟩ : ∃ J, J = poleMoment (-1 / 2) (modulatedFlat A τ) := ⟨_, rfl⟩
  have hcorr := norm_poleCorrection_resonant_le hA0 hτpos hSm
  rw [← hJp, ← hJm] at hcorr
  have hcm := measurable_poleCorrection A
    (((S : ℂ) * Jp - 2 * A * Jm) / ((S : ℂ) ^ 2 - 4 * (A : ℂ) ^ 2))
    (((S : ℂ) * Jm - 2 * A * Jp) / ((S : ℂ) ^ 2 - 4 * (A : ℂ) ^ 2))
  have hcs := fun x (hx : x ∉ Icc (-A) A) => poleCorrection_eq_zero
    (((S : ℂ) * Jp - 2 * A * Jm) / ((S : ℂ) ^ 2 - 4 * (A : ℂ) ^ 2))
    (((S : ℂ) * Jm - 2 * A * Jp) / ((S : ℂ) ^ 2 - 4 * (A : ℂ) ^ 2)) hx
  have hmass := l2mass_modulatedFlat_sub (τ := τ) hA0 hεhalf hcm hcorr hcs
  have hform := re_primeTranslationForm_resonant_sub_ge hA0 (by positivity) hres hcm hcorr hcs
  rw [← hC] at hform
  refine ⟨fun x => modulatedFlat A τ x - poleCorrection A
      (((S : ℂ) * Jp - 2 * A * Jm) / ((S : ℂ) ^ 2 - 4 * (A : ℂ) ^ 2))
      (((S : ℂ) * Jm - 2 * A * Jp) / ((S : ℂ) ^ 2 - 4 * (A : ℂ) ^ 2)) x,
    (measurable_modulatedFlat A τ).sub hcm, fun x => ?_, fun x hx => ?_, ?_, ?_,
    by linarith [hmass.1], (resonance_arith (by linarith) hC0 hτpos hτC hεhalf hhinge
      hmass.2).trans hform⟩
  · refine (norm_sub_le _ _).trans ?_
    linarith [norm_modulatedFlat_le A τ x, hcorr x]
  · simp only
    rw [modulatedFlat_eq_zero hx, hcs x hx, sub_zero]
  · rw [poleMoment_sub_poleCorrection, poleMoment_poleExp_same A hA0,
      poleMoment_poleExp_cross' A hA0, ← hJp, ← hS]
    rw [← (pole_system_solve hD Jp Jm).1]
    push_cast; ring
  · rw [poleMoment_sub_poleCorrection, poleMoment_poleExp_same_neg A hA0,
      poleMoment_poleExp_cross A hA0, ← hJm, ← hS]
    rw [← (pole_system_solve hD Jp Jm).2]
    push_cast; ring

end

end RHTower
