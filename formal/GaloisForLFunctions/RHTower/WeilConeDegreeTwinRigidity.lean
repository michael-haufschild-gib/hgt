import GaloisForLFunctions.RHTower.WeilPoleWeightBelowOneEmpty

/-!
# Degree-`d` Weil positivity forces `d Λ` and the Riemann hypothesis

For `d > 0` the degree-`d` Weil functional of `ζ`'s archimedean datum,

`W_d(lam; k) = d · (k̂(i/2) + k̂(−i/2) + (2π)⁻¹ ∫ k̂(r) Γ(r) dr) − Σ_{n≥2} lam(n) n^{−½} (k(log n) + k(−log n))`,

is the Weil explicit-formula functional of a Dirichlet series whose completed functional equation
is that of `ζ(s)^d` (gamma factor `Γ_ℝ(s)^d`, conductor `1`, pole of order `d` at `s = 1`), with
`lam` the coefficients of its negative logarithmic derivative.

**Theorem** (`weilPositiveDegree_iff`).  `W_d(lam; ·)` is nonnegative on every autocorrelation of a
compactly supported `C²` test if and only if the Riemann hypothesis holds and `lam(n) = d Λ(n)` for
every `n ≥ 2`.

Proof.  `W_d(lam; k) = d · W_1(lam/d; k)` (`weilDegreeFunctional_eq_mul`), so positivity in degree
`d` is positivity of `lam/d` in the full Weil cone of `ζ`, which is `{Λ}` if RH holds and empty
otherwise (`eq_vonMangoldt_of_weilPositiveFull`, `riemannHypothesis_iff_weilPositiveFull_vonMangoldt`).

Consequence (twin rigidity).  If a Dirichlet series `T` with real coefficients and `T(1) = 1`
leading coefficient shares the completed functional equation and polar data of `ζ^d` and all its
nontrivial zeros are critical, then Weil's explicit formula makes its weights `d`-Weil-positive,
so RH holds and `−T′/T = −d ζ′/ζ`, i.e. `T = ζ^d`.  In degree three the functional equation admits
an infinite-dimensional space of entire twins (`gammaRCube_functional_equation_abundance_vanishing_below`);
every twin `ζ³ + e` with `e ≠ 0` real therefore has a zero off the critical line, unconditionally.

**Pole order below the degree** (`not_forall_re_weilDegreePoleFunctional_nonneg`).  With `κ` copies
of the pole term instead of `d` (`weilDegreePoleFunctional`), the functional is
`d · W^{κ/d}(lam/d)` (`weilDegreePoleFunctional_eq_mul`), the Weil functional of pole weight
`κ/d`.  For `κ < d` and `lam/d − Λ` with linearly bounded partial sums it is negative on some real
autocorrelation (`WeilPoleWeight.not_forall_re_weilPoleWeightFunctional_nonneg`).  So a Dirichlet
series with gamma factor `Γ_ℝ(s)^d`, conductor `1` and a pole of order `κ < d` at `s = 1`
(including every entire one, `κ = 0`) never has all its zeros on the critical line: its weights obey
the linear bound by the prime number theorem for it, which follows from critical zeros.
-/

open Complex Zeta23

noncomputable section

namespace RHTower

/-- The degree-`d` Weil functional: `d` copies of `ζ`'s pole and archimedean datum minus the prime
pairing with weights `lam` on `n ≥ 2`. -/
def weilDegreeFunctional (d : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  (d : ℂ) * (paperFT k (I / 2) + paperFT k (-I / 2)
    + (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ))
  - ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))

/-- Degree-`d` Weil positivity on every autocorrelation of a compactly supported `C²` test. -/
def WeilPositiveDegree (d : ℝ) (lam : ℕ → ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
    0 ≤ (weilDegreeFunctional d lam (EF.weilTest f f)).re

/-- **Scaling.** The degree-`d` functional is `d` times the degree-one functional of `lam / d`. -/
theorem weilDegreeFunctional_eq_mul {d : ℝ} (hd : d ≠ 0) (lam : ℕ → ℝ) (k : ℝ → ℂ) :
    weilDegreeFunctional d lam k = (d : ℂ) * weilFullFunctional (fun n => lam n / d) k := by
  have hterm : ∀ n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (k (Real.log n) + k (-Real.log n)) =
      (d : ℂ) * (((if 2 ≤ n then lam n / d / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) := by
    intro n
    split_ifs
    · rw [← mul_assoc, ← ofReal_mul]
      congr 2
      field_simp
    · simp
  set P : ℂ := paperFT k (I / 2) + paperFT k (-I / 2) with hP
  set Ar : ℂ := (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ) with hAr
  set S : ℂ := ∑' n : ℕ, ((if 2 ≤ n then lam n / d / Real.sqrt n else 0 : ℝ) : ℂ) *
    (k (Real.log n) + k (-Real.log n)) with hS
  have h1 : weilFullFunctional (fun n => lam n / d) k = P - S + Ar := rfl
  have h2 : weilDegreeFunctional d lam k = (d : ℂ) * (P + Ar) - (d : ℂ) * S := by
    unfold weilDegreeFunctional
    rw [tsum_congr hterm, tsum_mul_left]
  rw [h1, h2]
  ring

/-- **Degree-`d` Weil positivity is RH together with `lam = d Λ`.** -/
theorem weilPositiveDegree_iff {d : ℝ} (hd : 0 < d) {lam : ℕ → ℝ} :
    WeilPositiveDegree d lam ↔
      RiemannHypothesis ∧ ∀ n, 2 ≤ n → lam n = d * (ArithmeticFunction.vonMangoldt n : ℝ) := by
  have hre : ∀ k : ℝ → ℂ, (weilDegreeFunctional d lam k).re =
      d * (weilFullFunctional (fun n => lam n / d) k).re := fun k => by
    rw [weilDegreeFunctional_eq_mul hd.ne', re_ofReal_mul]
  constructor
  · intro hW
    have hfull : WeilPositiveFull fun n => lam n / d := fun f hf hfc => by
      have h0 := hW f hf hfc
      rw [hre] at h0
      exact nonneg_of_mul_nonneg_right h0 hd
    have heq := WeilSpectral.eq_vonMangoldt_of_weilPositiveFull hfull
    refine ⟨riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_, fun n hn => ?_⟩
    · rw [weilFullFunctional_congr (fun m hm => (heq m hm).symm)]
      exact hfull f hf hfc
    · have h0 := heq n hn
      rw [div_eq_iff hd.ne'] at h0
      rw [h0, mul_comm]
  · rintro ⟨hRH, hlam⟩ f hf hfc
    rw [hre]
    have hcongr : weilFullFunctional (fun n => lam n / d) (EF.weilTest f f) =
        weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (EF.weilTest f f) :=
      weilFullFunctional_congr (fun n hn => by rw [hlam n hn, mul_div_cancel_left₀ _ hd.ne']) _
    rw [hcongr]
    exact mul_nonneg hd.le (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH f hf hfc)

/-- **The degree-`d` Weil cone is at most a point.** Any degree-`d` Weil-positive weight system is
`d Λ` on `n ≥ 2`, with no hypothesis on `ζ`. -/
theorem eq_smul_vonMangoldt_of_weilPositiveDegree {d : ℝ} (hd : 0 < d) {lam : ℕ → ℝ}
    (hW : WeilPositiveDegree d lam) :
    ∀ n, 2 ≤ n → lam n = d * (ArithmeticFunction.vonMangoldt n : ℝ) :=
  ((weilPositiveDegree_iff hd).mp hW).2

/-- The Weil functional of a degree-`d` datum with a pole of order `κ`: `d` copies of `ζ`'s
archimedean term and `κ` copies of its pole term. -/
def weilDegreePoleFunctional (d κ : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) : ℂ :=
  weilDegreeFunctional d lam k + ((κ - d : ℝ) : ℂ) * (paperFT k (I / 2) + paperFT k (-I / 2))

/-- **Scaling with a general pole order.** -/
theorem weilDegreePoleFunctional_eq_mul {d : ℝ} (hd : d ≠ 0) (κ : ℝ) (lam : ℕ → ℝ) (k : ℝ → ℂ) :
    weilDegreePoleFunctional d κ lam k =
      (d : ℂ) * WeilPoleWeight.weilPoleWeightFunctional (κ / d) (fun n => lam n / d) k := by
  have hdc : (d : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd
  unfold weilDegreePoleFunctional WeilPoleWeight.weilPoleWeightFunctional
  rw [weilDegreeFunctional_eq_mul hd]
  push_cast
  field_simp

/-- **A pole of order below the degree empties the cone.** -/
theorem not_forall_re_weilDegreePoleFunctional_nonneg {d κ : ℝ} (hd : 0 < d) (hκ : κ < d)
    {lam : ℕ → ℝ} {A : ℝ}
    (hA : ∀ N : ℕ, |WeilSpectral.primeWeightPartialSum
      (fun n => lam n / d - ArithmeticFunction.vonMangoldt n) N| ≤ A * (N + 1)) :
    ¬ ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
      0 ≤ (weilDegreePoleFunctional d κ lam
        (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re := by
  intro hpos
  refine WeilPoleWeight.not_forall_re_weilPoleWeightFunctional_nonneg
    (β := κ / d) (by rwa [div_lt_one hd]) (lam := fun n => lam n / d) hA fun F hF hFc => ?_
  have h0 := hpos F hF hFc
  rw [weilDegreePoleFunctional_eq_mul hd.ne', re_ofReal_mul] at h0
  exact nonneg_of_mul_nonneg_right h0 hd

/-- **Degree-`d` Weil positivity of any weight system implies the Riemann hypothesis.** -/
theorem riemannHypothesis_of_weilPositiveDegree {d : ℝ} (hd : 0 < d) {lam : ℕ → ℝ}
    (hW : WeilPositiveDegree d lam) : RiemannHypothesis :=
  ((weilPositiveDegree_iff hd).mp hW).1

end RHTower
