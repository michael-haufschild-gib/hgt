import GaloisForLFunctions.RHTower.EvenSectorPoleWeightWindow
import GaloisForLFunctions.RHTower.PrimitiveHyperplaneBlindPositivity

/-!
# No-go for multi-prime cosine periodization of the archimedean symbol without the polar zero

Avenue C of the EWU review asks whether subtracting a multi-prime cosine periodization
`Σ_{n≥2} lam(n) ℓ_n(f)` from the pure archimedean functional `poleWeightArchRe 0 f` can make the
resulting quadratic form nonnegative on even compactly supported `C²` tests without imposing the
off-axis complex polar condition `f̂(±i/2) = 0`, or equivalently whether `poleWeightArchRe 0` is
nonnegative on nonnegative combinations of even tests that are simultaneously blind at all integer
lags `±log n`, `n ≥ 2`.

This file proves the unconditional no-go and its positive structural separation:

1. **No multi-prime periodization succeeds without the polar constraint**
   (`not_weilPositiveEvenAt_of_lt_one`, `not_weilPositiveEvenAt_zero`):
   For every pole weight `β < 1` (and in particular at `β = 0`, where the pole term is dropped)
   and **every** real weight sequence `lam : ℕ → ℝ` (whether supported on `{2, 3}`, prime powers,
   or all integers `n ≥ 2`), `¬ WeilPositiveEvenAt β lam`.
2. **Simultaneously all-integer-blind even mixture with strictly negative pure archimedean energy**
   (`exists_even_blind_mixture_poleWeight_lt_one_neg`, `exists_even_blind_mixture_zeroPole_neg`):
   Unconditionally, there exists a finite nonnegative even mixture `c : EvenWeilTestFn →₀ ℝ` that
   vanishes at every integer lag `n ≥ 2` simultaneously (`∀ n ≥ 2, Σ_f c_f ℓ_n(f) = 0`) and has
   strictly negative `β = 0` archimedean energy (`Σ_f c_f · poleWeightArchRe 0 f < 0`), so for
   every weight sequence `lam : ℕ → ℝ`,
   `Σ_f c_f · Re W_0(lam)(k_f) = Σ_f c_f · poleWeightArchRe 0 f < 0`.
3. **Pole-vanishing invariance and non-polar support forcing**
   (`poleWeightArchRe_evenPolar_eq_weilArchRe`,
   `re_weilPoleWeightFunctional_evenPolar_eq_full`,
   `exists_nonpolar_support_of_poleWeightArchRe_ne`):
   On `WeilEvenPolarTestFn` (`f̂(i/2) = 0`), `poleWeightArchRe β` and `weilPoleWeightFunctional β`
   are completely independent of `β` and coincide with the canonical `β = 1` functionals.
   Consequently, any even mixture on which `poleWeightArchRe β` differs from `weilArchRe` must
   contain an active non-polar component with `f̂(i/2) ≠ 0`.
-/

open Complex MeasureTheory Filter Topology Set Finsupp Zeta23

noncomputable section

namespace RHTower.EvenSector

open WeilOneSided WeilSpectral WeilPoleWeight

/-! ## Pole-weight invariance on the even pole-free cone -/

/-- On an even pole-free test (`f̂(i/2) = 0`), the pole-weight-`β` archimedean functional
`poleWeightArchRe β` is independent of `β` and equals `weilArchRe`. -/
theorem poleWeightArchRe_evenPolar_eq_weilArchRe (β : ℝ) (f : WeilEvenPolarTestFn) :
    poleWeightArchRe β f.1 = weilArchRe (EF.weilTest f.1.1 f.1.1) := by
  unfold poleWeightArchRe
  rw [re_weilPoleTerm_eq_zero_of_evenPolar f, mul_zero, add_zero]

/-- On an even pole-free test (`f̂(i/2) = 0`), the real part of the `β`-weighted Weil functional
coincides with the full (`β = 1`) Weil functional for every weight sequence `lam`. -/
theorem re_weilPoleWeightFunctional_evenPolar_eq_full (β : ℝ) (lam : ℕ → ℝ)
    (f : WeilEvenPolarTestFn) :
    (weilPoleWeightFunctional β lam (EF.weilTest f.1.1 f.1.1)).re =
      (weilFullFunctional lam (EF.weilTest f.1.1 f.1.1)).re := by
  rw [re_weilPoleWeightFunctional_eq, re_weilFullFunctional_eq,
    poleWeightArchRe_evenPolar_eq_weilArchRe]

/-! ## Unconditional refutation of Avenue C (multi-prime periodization at `β < 1`) -/

/-- **No arithmetic weight sequence is Weil-positive on even tests at pole weight `β < 1`.** -/
theorem not_weilPositiveEvenAt_of_lt_one {β : ℝ} (hβ : β < 1) (lam : ℕ → ℝ) :
    ¬ WeilPositiveEvenAt β lam := fun h =>
  not_primeBlindPositiveEvenAt_of_lt_one hβ (primeBlindPositiveEvenAt_of_weilPositiveEvenAt h)

/-- **Unconditional no-go for pole-free multi-prime periodization (`β = 0`).**
No sequence of real weights `lam : ℕ → ℝ` (over `{2, 3}`, primes, prime powers, or all `n ≥ 2`)
makes the pure archimedean functional minus `Σ_{n≥2} lam(n) ℓ_n(f)` nonnegative on all even
compactly supported `C²` tests without the off-axis polar zero `f̂(±i/2) = 0`. -/
theorem not_weilPositiveEvenAt_zero (lam : ℕ → ℝ) :
    ¬ WeilPositiveEvenAt 0 lam :=
  not_weilPositiveEvenAt_of_lt_one (by norm_num) lam

/-- **Existence of an all-integer-blind even mixture with negative `β`-energy for any `β < 1`.** -/
theorem exists_even_blind_mixture_poleWeight_lt_one_neg {β : ℝ} (hβ : β < 1) :
    ∃ c : EvenWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1.1 n) = 0) ∧
      c.sum (fun f t => t * poleWeightArchRe β f.1) < 0 := by
  have h := not_primeBlindPositiveEvenAt_of_lt_one hβ
  unfold PrimeBlindPositiveEvenAt at h
  push Not at h
  exact h

/-- For any all-integer-blind even mixture `c`, the weighted sum of `Re W_β(lam)` is independent
of the arithmetic weight sequence `lam : ℕ → ℝ` and equals the pure `β`-archimedean sum. -/
theorem sum_re_weilPoleWeightFunctional_eq_of_even_blind (β : ℝ) (lam : ℕ → ℝ)
    {c : EvenWeilTestFn →₀ ℝ}
    (hnull : ∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1.1 n) = 0) :
    (c.sum fun f t =>
        t * (weilPoleWeightFunctional β lam (EF.weilTest f.1.1 f.1.1)).re) =
      c.sum fun f t => t * poleWeightArchRe β f.1 := by
  have hlin : (c.sum fun f t =>
      linearCombination ℝ (fun j : LogIndex => lam j) (t • logVector f.1)) = 0 := by
    rw [← map_finsuppSum, sum_logVector_eq_zero hnull, map_zero]
  have e : (c.sum fun f t =>
      t * (weilPoleWeightFunctional β lam (EF.weilTest f.1.1 f.1.1)).re) =
      (c.sum fun f t => t * poleWeightArchRe β f.1) -
        c.sum fun f t => linearCombination ℝ (fun j : LogIndex => lam j) (t • logVector f.1) := by
    rw [← Finsupp.sum_sub]
    refine Finsupp.sum_congr fun f _ => ?_
    rw [re_weilPoleWeightFunctional_eq, map_smul, smul_eq_mul]
    ring
  linarith

/-- **Unconditional refutation of Avenue C.**  There exists a finite nonnegative mixture of even
compactly supported `C²` tests that is simultaneously blind at every integer `n ≥ 2` and has
strictly negative pure archimedean energy (`β = 0`), hence strictly negative `β = 0` Weil energy
for **every** arithmetic weight sequence `lam : ℕ → ℝ`. -/
theorem exists_even_blind_mixture_zeroPole_neg :
    ∃ c : EvenWeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1.1 n) = 0) ∧
      c.sum (fun f t => t * poleWeightArchRe 0 f.1) < 0 ∧
      ∀ lam : ℕ → ℝ,
        c.sum (fun f t =>
          t * (weilPoleWeightFunctional 0 lam (EF.weilTest f.1.1 f.1.1)).re) < 0 := by
  obtain ⟨c, hc, hnull, hneg⟩ :=
    exists_even_blind_mixture_poleWeight_lt_one_neg (show (0 : ℝ) < 1 by norm_num)
  refine ⟨c, hc, hnull, hneg, fun lam => ?_⟩
  rw [sum_re_weilPoleWeightFunctional_eq_of_even_blind 0 lam hnull]
  exact hneg

/-- Any even mixture on which the `β`-weighted archimedean energy differs from the `β = 1`
archimedean energy must contain an active component with a nonvanishing polar transform
`f̂(i/2) ≠ 0`. -/
theorem exists_nonpolar_support_of_poleWeightArchRe_ne {β : ℝ} {c : EvenWeilTestFn →₀ ℝ}
    (hne : c.sum (fun f t => t * poleWeightArchRe β f.1) ≠
      c.sum (fun f t => t * weilArchRe (EF.weilTest f.1.1 f.1.1))) :
    ∃ f ∈ c.support, paperFT f.1.1 (I / 2) ≠ 0 := by
  by_contra hall
  push Not at hall
  apply hne
  refine Finsupp.sum_congr fun f hf => ?_
  have hp : WeilEvenPolarTestFn := ⟨f.1, f.2, hall f hf⟩
  rw [poleWeightArchRe_evenPolar_eq_weilArchRe β hp]

end RHTower.EvenSector

end
