import GaloisForLFunctions.RHTower.CoshPolynomialPeriodClassification
import GaloisForLFunctions.RHTower.CoshPolynomialExactOrderOne

/-!
# Finite products of displaced cosh quartet envelopes

A finite product

```text
B(w) = ∏_j cosh (w - A_j) · cosh (w + A_j)
```

is entire, real-even, Schwarz-real and `π i`-periodic, strictly positive real on the imaginary
axis when every displacement is nonzero, and its zero set is the union of the `2r` vertical
lattices `±A_j + i(2k+1)π/2`.  Multiplying by a nonconstant polynomial destroys every nonzero
period, and the resulting entire function is trapped between two-sided exponential bounds of type
`2r`, hence has exact order one.

These are the multi-quartet analogues of the single-envelope statements in
`CoshQuartetEnvelope`, `CoshPolynomialPeriodClassification` and `CoshPolynomialExactOrderOne`.
The period argument here is shorter than the single-envelope one: instead of quantising three
consecutive zeros, it observes that an infinite orbit of envelope zeros would inject the real
parts of that orbit into the finite set `{±A_j}`.
-/

namespace RHTower

open Complex Filter Topology
open scoped BigOperators

noncomputable section

variable {r : ℕ}

/-- A finite product of displaced cosh quartet envelopes. -/
def multiEnvelope (A : Fin r → ℝ) (w : ℂ) : ℂ := ∏ j, coshQuartetEnvelope (A j) w

theorem multiEnvelope_analyticAt (A : Fin r → ℝ) (w : ℂ) :
    AnalyticAt ℂ (multiEnvelope A) w := by
  unfold multiEnvelope
  exact Finset.analyticAt_fun_prod _ fun j _ => coshQuartetEnvelope_analyticAt (A j) w

theorem multiEnvelope_neg (A : Fin r → ℝ) (w : ℂ) :
    multiEnvelope A (-w) = multiEnvelope A w :=
  Finset.prod_congr rfl fun j _ => coshQuartetEnvelope_neg (A j) w

theorem multiEnvelope_conj (A : Fin r → ℝ) (w : ℂ) :
    multiEnvelope A ((starRingEnd ℂ) w) = (starRingEnd ℂ) (multiEnvelope A w) := by
  unfold multiEnvelope
  rw [map_prod]
  exact Finset.prod_congr rfl fun j _ => coshQuartetEnvelope_conj (A j) w

theorem multiEnvelope_add_pi_mul_I (A : Fin r → ℝ) (w : ℂ) :
    multiEnvelope A (w + (Real.pi : ℂ) * I) = multiEnvelope A w :=
  Finset.prod_congr rfl fun j _ => coshQuartetEnvelope_add_pi_mul_I (A j) w

theorem multiEnvelope_eq_zero_iff {A : Fin r → ℝ} {z : ℂ} :
    multiEnvelope A z = 0 ↔ ∃ j, coshQuartetEnvelope (A j) z = 0 := by
  unfold multiEnvelope
  rw [Finset.prod_eq_zero_iff]
  simp

theorem multiEnvelope_zero_re_sq {A : Fin r → ℝ} {z : ℂ} (hz : multiEnvelope A z = 0) :
    ∃ j, z.re ^ (2 : ℕ) = (A j) ^ (2 : ℕ) := by
  obtain ⟨j, hj⟩ := multiEnvelope_eq_zero_iff.mp hz
  exact ⟨j, coshQuartetEnvelope_zero_re_sq hj⟩

/-! ## Positivity -/

theorem exp_two_mul_div_four_le_norm_multiEnvelope_ofReal (A : Fin r → ℝ) (x : ℝ) :
    (Real.exp (2 * x) / 4) ^ r ≤ ‖multiEnvelope A (x : ℂ)‖ := by
  unfold multiEnvelope
  rw [norm_prod]
  calc (Real.exp (2 * x) / 4) ^ r
      = ∏ _j : Fin r, (Real.exp (2 * x) / 4) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ j : Fin r, ‖coshQuartetEnvelope (A j) (x : ℂ)‖ := by
        refine Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => ?_)
        exact exp_two_mul_div_four_le_norm_coshQuartetEnvelope_ofReal (A j) x

theorem multiEnvelope_ofReal_ne_zero (A : Fin r → ℝ) (x : ℝ) :
    multiEnvelope A (x : ℂ) ≠ 0 := by
  have hpos : (0 : ℝ) < (Real.exp (2 * x) / 4) ^ r := by positivity
  have hle := exp_two_mul_div_four_le_norm_multiEnvelope_ofReal A x
  intro hc
  rw [hc, norm_zero] at hle
  linarith

theorem multiEnvelope_mul_I_pos_real {A : Fin r → ℝ} (hA : ∀ j, A j ≠ 0) (y : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ multiEnvelope A ((y : ℂ) * I) = (ρ : ℂ) := by
  classical
  have hchoice : ∀ j : Fin r, ∃ ρ : ℝ, 0 < ρ ∧
      coshQuartetEnvelope (A j) ((y : ℂ) * I) = (ρ : ℂ) :=
    fun j => coshQuartetEnvelope_mul_I_pos_real (hA j)
  choose ρ hρpos hρval using hchoice
  refine ⟨∏ j, ρ j, Finset.prod_pos fun j _ => hρpos j, ?_⟩
  unfold multiEnvelope
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun j _ => hρval j

/-! ## Exponential type -/

theorem norm_multiEnvelope_le (A : Fin r → ℝ) (z : ℂ) :
    ‖multiEnvelope A z‖ ≤ Real.exp (2 * r * ‖z‖) * Real.exp (2 * ∑ j, |A j|) := by
  unfold multiEnvelope
  rw [norm_prod]
  calc ∏ j : Fin r, ‖coshQuartetEnvelope (A j) z‖
      ≤ ∏ j : Fin r, Real.exp (2 * (‖z‖ + |A j|)) :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _)
          (fun j _ => norm_coshQuartetEnvelope_le (A j) z)
    _ = Real.exp (∑ j : Fin r, 2 * (‖z‖ + |A j|)) := by rw [Real.exp_sum]
    _ = Real.exp (2 * r * ‖z‖) * Real.exp (2 * ∑ j, |A j|) := by
        rw [← Real.exp_add]
        congr 1
        simp only [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
        ring

/-- A nonzero polynomial is eventually bounded below on the positive real ray. -/
theorem eventually_norm_polynomial_eval_ofReal_ge {P : Polynomial ℂ} (hP : P ≠ 0) :
    ∃ R : ℝ, ∀ x : ℝ, R ≤ x → ‖P.leadingCoeff‖ / 8 ≤ ‖P.eval (x : ℂ)‖ := by
  obtain ⟨R, hR⟩ := eventually_le_norm_coshQuartetEnvelope_mul_polynomial_ofReal 0 hP
  refine ⟨max R 0, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := le_trans (le_max_right R 0) hx
  have hxR : R ≤ x := le_trans (le_max_left R 0) hx
  have hbase := hR x hxR
  rw [norm_mul] at hbase
  have henv : ‖coshQuartetEnvelope 0 (x : ℂ)‖ ≤ Real.exp (2 * x) := by
    have h := norm_coshQuartetEnvelope_le 0 (x : ℂ)
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0] using h
  have hepos : (0 : ℝ) < Real.exp (2 * x) := Real.exp_pos _
  nlinarith [norm_nonneg (P.eval (x : ℂ)), norm_nonneg (coshQuartetEnvelope 0 (x : ℂ)),
    Real.exp_pos (2 * x)]

/-- **Exact order-one certificate for a polynomially weighted product envelope.** -/
theorem multiEnvelope_mul_polynomial_order_one_bounds (A : Fin r → ℝ) {P : Polynomial ℂ}
    (hP : P ≠ 0) :
    ∃ Kupper Klower R : ℝ,
      0 < Kupper ∧ 0 < Klower ∧
      (∀ z : ℂ, ‖multiEnvelope A z * P.eval z‖ ≤
        Kupper * (1 + ‖z‖) ^ P.natDegree * Real.exp (2 * r * ‖z‖)) ∧
      ∀ x : ℝ, R ≤ x → Klower * Real.exp (2 * r * x) ≤
        ‖multiEnvelope A (x : ℂ) * P.eval (x : ℂ)‖ := by
  obtain ⟨R, hR⟩ := eventually_norm_polynomial_eval_ofReal_ge hP
  have hlc : 0 < ‖P.leadingCoeff‖ :=
    norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hP)
  refine ⟨polynomialCoeffNormSum P * Real.exp (2 * ∑ j, |A j|),
    (‖P.leadingCoeff‖ / 8) / 4 ^ r, R, ?_, ?_, fun z => ?_, fun x hx => ?_⟩
  · exact mul_pos (polynomialCoeffNormSum_pos hP) (Real.exp_pos _)
  · positivity
  · rw [norm_mul]
    have h1 := norm_multiEnvelope_le A z
    have h2 := norm_polynomial_eval_le P z
    have hnn : (0 : ℝ) ≤ (1 + ‖z‖) ^ P.natDegree := by positivity
    calc ‖multiEnvelope A z‖ * ‖P.eval z‖
        ≤ (Real.exp (2 * r * ‖z‖) * Real.exp (2 * ∑ j, |A j|)) *
            (polynomialCoeffNormSum P * (1 + ‖z‖) ^ P.natDegree) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = polynomialCoeffNormSum P * Real.exp (2 * ∑ j, |A j|) *
            (1 + ‖z‖) ^ P.natDegree * Real.exp (2 * r * ‖z‖) := by ring
  · rw [norm_mul]
    have h1 := exp_two_mul_div_four_le_norm_multiEnvelope_ofReal A x
    have h2 := hR x hx
    have hpow : (Real.exp (2 * x) / 4) ^ r = Real.exp (2 * r * x) / 4 ^ r := by
      rw [div_pow, ← Real.exp_nat_mul]
      congr 2
      ring
    rw [hpow] at h1
    have hnn1 : (0 : ℝ) ≤ Real.exp (2 * r * x) / 4 ^ r := by positivity
    calc (‖P.leadingCoeff‖ / 8) / 4 ^ r * Real.exp (2 * r * x)
        = (Real.exp (2 * r * x) / 4 ^ r) * (‖P.leadingCoeff‖ / 8) := by ring
      _ ≤ ‖multiEnvelope A (x : ℂ)‖ * ‖P.eval (x : ℂ)‖ :=
          mul_le_mul h1 h2 (by positivity) (norm_nonneg _)

/-! ## Period classification -/

theorem coshQuartetEnvelope_zero_form {a : ℝ} {z : ℂ} (hz : coshQuartetEnvelope a z = 0) :
    ∃ (b : ℝ) (k : ℤ), z = (b : ℂ) - ((2 * (k : ℂ) + 1) * Real.pi / 2) * I := by
  rcases coshQuartetEnvelope_eq_zero_iff.mp hz with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact ⟨a, k, hk⟩
  · refine ⟨-a, k, ?_⟩
    rw [hk]
    push_cast
    ring

theorem multiEnvelope_periodic_pi_mul_I (A : Fin r → ℝ) :
    Function.Periodic (multiEnvelope A) ((Real.pi : ℂ) * I) :=
  multiEnvelope_add_pi_mul_I A

/-- **The period group of a polynomially weighted product envelope is trivial.** -/
theorem multiEnvelope_mul_polynomial_periodic_eq_zero {A : Fin r → ℝ} (hr : 0 < r)
    (P : Polynomial ℂ) (hdeg : 0 < P.degree) {h : ℂ}
    (hper : Function.Periodic (fun z => multiEnvelope A z * P.eval z) h) : h = 0 := by
  classical
  by_contra hh
  obtain ⟨j0⟩ := Fin.pos_iff_nonempty.mp hr
  set z0 : ℂ := (A j0 : ℂ) - ((2 * (0 : ℂ) + 1) * Real.pi / 2) * I with hz0def
  have hz0 : multiEnvelope A z0 = 0 :=
    multiEnvelope_eq_zero_iff.mpr ⟨j0, coshQuartetEnvelope_eq_zero_iff.mpr
      (Or.inl ⟨0, by rw [hz0def]; push_cast; ring⟩)⟩
  set orbit : ℕ → ℂ := fun n => z0 + (n : ℂ) * h with horbitdef
  have horbitInj : Function.Injective orbit := by
    intro m n hmn
    apply Nat.cast_injective (R := ℂ)
    apply mul_right_cancel₀ hh
    simp only [horbitdef] at hmn
    exact add_left_cancel hmn
  have hFzero : ∀ n : ℕ, multiEnvelope A (orbit n) * P.eval (orbit n) = 0 := by
    intro n
    have hn := (hper.nsmul n) z0
    simpa [horbitdef, nsmul_eq_mul, hz0] using hn
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero] at hdeg
    simp at hdeg
  have hrootFinite : {w : ℂ | P.eval w = 0}.Finite := by
    by_contra hinf
    exact hPne (Polynomial.eq_of_infinite_eval_eq P 0 (by simpa using hinf))
  have hbad : {n : ℕ | P.eval (orbit n) = 0}.Finite :=
    hrootFinite.preimage horbitInj.injOn
  obtain ⟨B, hB⟩ := hbad.bddAbove
  have hgood : ∀ n : ℕ, B < n → multiEnvelope A (orbit n) = 0 := by
    intro n hn
    rcases mul_eq_zero.mp (hFzero n) with h1 | h2
    · exact h1
    · exact absurd (hB h2) (not_le.mpr hn)
  -- Step 1: the translation is purely imaginary.
  have hre : h.re = 0 := by
    by_contra hrene
    set S : Set ℝ := {x : ℝ | ∃ j, x ^ (2 : ℕ) = (A j) ^ (2 : ℕ)} with hSdef
    have hSfin : S.Finite := by
      refine Set.Finite.subset ((Set.finite_range A).union
        (Set.finite_range fun j => -(A j))) ?_
      rintro x ⟨j, hx⟩
      have hfac : (x - A j) * (x + A j) = 0 := by linear_combination hx
      rcases mul_eq_zero.mp hfac with hc | hc
      · exact Or.inl ⟨j, by linarith⟩
      · exact Or.inr ⟨j, by linarith⟩
    have hreval : ∀ n : ℕ, (orbit n).re = z0.re + n * h.re := by
      intro n
      simp [horbitdef, Complex.add_re, Complex.mul_re]
    have hinj : Set.InjOn (fun n : ℕ => (orbit n).re) (Set.Ioi B) := by
      intro m _ n _ hmn
      simp only [hreval] at hmn
      have : (m : ℝ) = (n : ℝ) := by
        have := add_left_cancel hmn
        exact mul_right_cancel₀ hrene this
      exact_mod_cast this
    have himg : (fun n : ℕ => (orbit n).re) '' (Set.Ioi B) ⊆ S := by
      rintro x ⟨n, hn, rfl⟩
      exact multiEnvelope_zero_re_sq (hgood n hn)
    exact (Set.Infinite.image hinj (Set.Ioi_infinite B)).not_finite (hSfin.subset himg)
  -- Step 2: the translation lies in the envelope period lattice.
  have hquant : ∃ k : ℤ, h = (k : ℂ) * ((Real.pi : ℂ) * I) := by
    obtain ⟨j1, hj1⟩ := multiEnvelope_eq_zero_iff.mp (hgood (B + 1) (by omega))
    obtain ⟨j2, hj2⟩ := multiEnvelope_eq_zero_iff.mp (hgood (B + 2) (by omega))
    obtain ⟨b1, k1, hb1⟩ := coshQuartetEnvelope_zero_form hj1
    obtain ⟨b2, k2, hb2⟩ := coshQuartetEnvelope_zero_form hj2
    have horb : orbit (B + 2) - orbit (B + 1) = h := by
      simp only [horbitdef]
      push_cast
      ring
    have hdiff : h = ((b2 - b1 : ℝ) : ℂ) + ((k1 - k2 : ℤ) : ℂ) * ((Real.pi : ℂ) * I) := by
      rw [← horb, hb1, hb2]
      push_cast
      ring
    have hb : b2 - b1 = 0 := by
      have hh1 := congrArg Complex.re hdiff
      rw [hre] at hh1
      simp [Complex.add_re, Complex.mul_re] at hh1
      linarith
    refine ⟨k1 - k2, ?_⟩
    rw [hdiff, hb]
    simp
  -- Step 3: transfer the period to the polynomial.
  obtain ⟨k, hk⟩ := hquant
  have hBper : Function.Periodic (multiEnvelope A) h := by
    have := (multiEnvelope_periodic_pi_mul_I A).zsmul k
    rwa [zsmul_eq_mul, ← hk] at this
  have hPeq : P.comp (Polynomial.X + Polynomial.C h) = P := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective Complex.ofReal_injective)
    rintro w ⟨x, rfl⟩
    have hFx := hper (x : ℂ)
    have hBx := hBper (x : ℂ)
    have hne := multiEnvelope_ofReal_ne_zero A x
    simp only at hFx
    rw [hBx] at hFx
    have := mul_left_cancel₀ hne hFx
    simpa [Polynomial.eval_comp] using this
  have hPper : Function.Periodic P.eval h := by
    intro z
    have := congrArg (fun q => Polynomial.eval z q) hPeq
    simpa [Polynomial.eval_comp] using this
  exact hh (polynomial_eval_periodic_eq_zero hdeg hPper)

/-- **Complete period classification for a polynomially weighted product envelope.** -/
theorem multiEnvelope_mul_polynomial_periodic_iff {A : Fin r → ℝ} (hr : 0 < r)
    (P : Polynomial ℂ) (hdeg : 0 < P.degree) (h : ℂ) :
    Function.Periodic (fun z => multiEnvelope A z * P.eval z) h ↔ h = 0 := by
  constructor
  · exact multiEnvelope_mul_polynomial_periodic_eq_zero hr P hdeg
  · rintro rfl z
    simp

end

end RHTower
