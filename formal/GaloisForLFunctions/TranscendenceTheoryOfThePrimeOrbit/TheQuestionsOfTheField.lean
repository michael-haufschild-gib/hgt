import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheDepthLawOfReturns
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.SurvivalAtADeepReturn
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TheFunctionFieldCase
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.TuranOnThickSetsOfLevels
import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.AZeroFreeRegionBoundsTheHeavyReturns

/-!
# The questions of the field

The four questions of transcendence theory of the prime orbit, each answered by one statement.

1. How early can the primes `≤ y` return to precision `δ`, and how early can a heavy subset?
   (`question_one`)
2. How does the lower bound for linear forms in `k` logarithms depend on `k`, and can it be taken
   uniform for `k ≍ π(y)`? (`question_two`)
3. Which auxiliary integer polynomials on smooth numbers survive the passage from approximate to
   exact vanishing? (`question_three`)
4. How does Turán's power-sum method give ZAL on the finite-rank remainder of `ψ`?
   (`question_four`)
-/

open Real Finset Filter

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

open Zeta23
open RHTower.Matveev (primeLogForm coeffHeight totalLogSum)

/-- **Question 1.** *Depth:* every set of two or more primes `≤ y`, heavy subsets included, returns
to precision `δ ≤ 1/10` no earlier than `e^{−2}(2δ log y)^{−1/C(y)}/(2 log y)`, `C(y)` an explicit
power of `log y`; Dirichlet returns them by `⌈π/2δ⌉^{|P|}`. *Breadth:* bounded-height Diophantine
data cannot see past `2πK y^K` (the rounded system matches every form of height `≤ K` and returns
exactly). *Heavy subsets at constant precision:* unconditionally (Vinogradov–Korobov),
`√y ≤ K(y^{½ − w(2t)} log t + log(2 + t))` at every return beyond `T₁` of a `1/1000`-heavy subset at
precision `≤ 1/20`; under a strip of width `h`, `log t ≥ c y^{½−h}`. -/
theorem question_one :
    (∀ {y : ℕ} {S : Finset ℕ}, (∀ p ∈ S, p.Prime ∧ p ≤ y) → ∀ {p q : ℕ}, p ∈ S → q ∈ S → p ≠ q →
      ∀ {δ t : ℝ}, 0 < δ → δ ≤ 1 / 10 → 1 ≤ t →
        IsDeltaReturn S (fun n : ℕ => Real.log n) δ t →
          Real.exp (-2) * (2 * δ * Real.log y) ^
            (-(bakerExponent 1 ⌈(1 + 1 : ℝ) * Real.log y⌉₊)⁻¹) / (2 * Real.log y) ≤ t) ∧
    (∀ (s : Finset ℕ) {δ : ℝ}, 0 ≤ δ → ∀ {Q : ℕ}, 1 ≤ Q → π ≤ 2 * δ * Q →
      ∃ t, 1 ≤ t ∧ t ≤ (Q : ℝ) ^ s.card ∧ IsDeltaReturn s (fun n : ℕ => Real.log n) δ t) ∧
    (∀ {y : ℕ} {s : Finset ℕ}, (∀ p ∈ s, p.Prime ∧ p ≤ y) → ∀ (K : ℕ) {T : ℝ}, 0 < T →
      2 * π * K * (y : ℝ) ^ K ≤ T →
        MatchesToHeight s K (fun p => Real.log p) (roundedStep T fun p => Real.log p) ∧
          IsDeltaReturn s (roundedStep T fun p => Real.log p) 0 T) ∧
    (∃ K : ℝ, 0 < K ∧ ∃ T₁ : ℝ, ∀ᶠ y : ℕ in atTop, ∀ H : Finset ℕ, IsHeavy y (1 / 1000) H →
      ∀ δ t : ℝ, 0 ≤ δ → δ ≤ 1 / 20 → T₁ ≤ t →
        IsDeltaReturn H (fun p : ℕ => Real.log p) δ t →
          Real.sqrt y ≤ K * ((y : ℝ) ^ (1 / 2 - RHTower.vkHadamardWidth (2 * t)) * Real.log t +
            Real.log (2 + t))) ∧
    (∀ {h T₀ : ℝ}, 0 ≤ h →
      (∀ ρ ∈ zetaZeroConfig.carrier, T₀ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ h) →
      ∃ c : ℝ, 0 < c ∧ ∃ T₁ : ℝ, ∀ᶠ y : ℕ in atTop, ∀ H : Finset ℕ, IsHeavy y (1 / 1000) H →
        ∀ δ t : ℝ, 0 ≤ δ → δ ≤ 1 / 20 → T₁ ≤ t →
          IsDeltaReturn H (fun p : ℕ => Real.log p) δ t → c * (y : ℝ) ^ (1 / 2 - h) ≤ Real.log t) :=
  ⟨fun hS _ _ hp hq hpq _ _ hδ0 hδ ht hret =>
      le_of_isDeltaReturn_of_two_mem hS hp hq hpq hδ0 hδ ht hret,
    fun s _ hδ _ hQ hδQ => exists_isDeltaReturn_le_pow s _ hδ hQ hδQ,
    fun hs K _ hT0 hT => let h := exists_matching_system_with_exact_return hs K hT0 hT; ⟨h.1, h.2.1⟩,
    heavy_return_bound_vinogradovKorobov,
    fun hh hstrip => log_ge_of_heavy_return_of_strip hh hstrip⟩

/-- **Question 2.** For `m + 1` distinct primes with `Σ log p ≤ W`, explicitly
`|Λ_ν| ≥ exp(−U^{30(m+2)²}(log|ν|₁ + 2))`, `U = 10⁴(W+1)(m+2)²`: the exponent is `exp(O(k² log kW))`.
No exponent below `k − 1` is possible (Dirichlet). At `k ≍ π(y)` uniformity is irrelevant for
constant-precision returns: only forms of height `< 1/2δ` act, Liouville `y^{−|ν|₁}` holds for them,
and the rounded system defeats every statement about them past `2πKy^K` (`question_one`). -/
theorem question_two :
    (∀ {m : ℕ} (p : Fin (m + 1) → ℕ), Function.Injective p → (∀ i, (p i).Prime) →
      ∀ {Wb : ℕ}, totalLogSum p ≤ Wb → ∀ ν : Fin (m + 1) → ℤ, ν ≠ 0 →
        Real.exp (-(bakerExponent m Wb * (Real.log (coeffHeight ν) + 2))) ≤ |primeLogForm p ν|) ∧
    (∀ {d : ℕ}, 2 ≤ d → ∀ (p : Fin d → ℕ), (∀ i, 1 ≤ p i) → ∀ {c C : ℝ}, 0 < c →
      (∀ ν : Fin d → ℤ, ν ≠ 0 → c * (2 + (coeffHeight ν : ℝ)) ^ (-C) ≤ |primeLogForm p ν|) →
        (d : ℝ) - 1 ≤ C) ∧
    (∀ {y : ℕ} {s : Finset ℕ}, (∀ p ∈ s, p.Prime ∧ p ≤ y) → ∀ {ν : ℕ → ℤ}, (∃ p ∈ s, ν p ≠ 0) →
      ((y : ℝ) ^ formHeight s ν)⁻¹ ≤ |linForm s (fun p => Real.log p) ν|) :=
  ⟨fun p hp hprime _ hW ν hν => abs_primeLogForm_ge_explicit p hp hprime hW ν hν,
    fun hd p hp _ _ hc hbound => le_exponent_of_bakerBound hd p hp hc hbound,
    fun hs _ hν => inv_pow_le_abs_linForm_log hs hν⟩

/-- **Question 3.** At a `δ`-return the jets of an integer auxiliary equal its jets at `0` up to
`2πδM_j`, and at multiples `mt` up to `2πmδM_j`. Order `0` survives at constant precision
(`|A(it)| + 2πδM₀ < 1` forces `Σ c_n = 0`); order `1` survives below the explicit Baker threshold
(the first moments `μ_i = Σ c_n v_{p_i}(n)` vanish); order `2` at two primes is exact only in the
sense that an integer quadratic form in `log p, log q` vanishes only trivially; the orbit meets no
algebraic point of three prime coordinates away from `t = 0`. -/
theorem question_three :
    (∀ {d : ℕ} {p : Fin d → ℕ}, Function.Injective p → ∀ {N : Finset ℕ},
      (∀ n ∈ N, IsSmoothOver p n) → ∀ (c : ℕ → ℤ) (j : ℕ) {δ t : ℝ},
        IsDeltaReturn univ (fun i => Real.log (p i)) δ t → ∀ m : ℕ,
          ‖auxJet N c j (m * t) - auxJet N c j 0‖ ≤ 2 * π * (m * δ) * jetMass p N c j) ∧
    (∀ {d : ℕ} {p : Fin d → ℕ}, Function.Injective p → ∀ {N : Finset ℕ},
      (∀ n ∈ N, IsSmoothOver p n) → ∀ (c : ℕ → ℤ) {δ t : ℝ},
        IsDeltaReturn univ (fun i => Real.log (p i)) δ t →
          ‖auxJet N c 0 t‖ + 2 * π * δ * jetMass p N c 0 < 1 → ∑ n ∈ N, c n = 0) ∧
    (∀ {m : ℕ} (p : Fin (m + 1) → ℕ), Function.Injective p → (∀ i, (p i).Prime) →
      ∀ {Wb : ℕ}, totalLogSum p ≤ Wb → ∀ {N : Finset ℕ}, (∀ n ∈ N, IsSmoothOver p n) →
        ∀ (c : ℕ → ℤ) {δ t : ℝ}, IsDeltaReturn univ (fun i => Real.log (p i)) δ t →
          ‖auxJet N c 1 t‖ + 2 * π * δ * jetMass p N c 1 <
            Real.exp (-(bakerExponent m Wb * (Real.log (coeffHeight (firstMoment p N c)) + 2))) →
              firstMoment p N c = 0) ∧
    (∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q → ∀ {a b c : ℤ},
      (a : ℝ) * Real.log p ^ 2 + b * Real.log p * Real.log q + c * Real.log q ^ 2 = 0 →
        a = 0 ∧ b = 0 ∧ c = 0) ∧
    (∀ {t : ℝ}, t ≠ 0 → ∀ {p q r : ℕ}, p.Prime → q.Prime → r.Prime → p ≠ q → p ≠ r → q ≠ r →
      ¬ (IsAlgebraic ℚ ((p : ℂ) ^ (-(t : ℂ) * Complex.I)) ∧
        IsAlgebraic ℚ ((q : ℂ) ^ (-(t : ℂ) * Complex.I)) ∧
        IsAlgebraic ℚ ((r : ℂ) ^ (-(t : ℂ) * Complex.I)))) :=
  ⟨fun hp _ hN c j _ _ hret m => norm_auxJet_nsmul_sub_le hp hN c j hret m,
    fun hp _ hN c _ _ hret hsmall => sum_coeff_eq_zero_of_small hp hN c hret hsmall,
    fun p hp hprime _ hW _ hN c _ _ hret hsmall =>
      firstMoment_eq_zero_of_small p hp hprime hW hN c hret hsmall,
    fun hp hq hpq _ _ _ h => quadratic_log_form_eq_zero hp hq hpq h,
    fun ht _ _ _ hp hq hr hpq hpr hqr => not_isAlgebraic_orbit ht hp hq hr hpq hpr hqr⟩

/-- **Question 4.** Turán's second main theorem sees the finite top part of a tower on every thick
set of levels, with a loss polynomial in the position, so a thick crude count removes an isolated top;
it cannot produce ZAL, which is a statement about infinitely many modes. Nor can return bounds:
they are statements about the prime labels, and `ζ(s − h)` — an Euler product over the rational
primes — shares them while violating ZAL, so a route uniform over a class containing it refutes the
main conjecture. Through reciprocity a zero of depth `h` weighs only `y^h` on the orbit polynomial of
length `y`, while a return asks for `√y`. -/
theorem question_four :
    (∀ {ι : Type*} (s : Finset ι) (z b : ι → ℂ) {R : ℝ}, 0 < R → (∃ i ∈ s, R ≤ ‖z i‖) →
      ∀ {β : ℝ}, 0 < β →
        (∀ τ : ℝ, 1 / 2 ≤ τ → τ ≤ 1 → β ≤ ‖∑ i ∈ s.filter (fun i => τ * R ≤ ‖z i‖), b i‖) →
        ∀ (E : ℕ → ℂ) {B r : ℝ}, (∀ ν, ‖E ν‖ ≤ B * r ^ ν) → ∀ {G : Set ℕ},
          InfiniteRankWeilTheory.Thick G → ∀ M₀ : ℕ,
            ∃ ν ∈ G, M₀ < ν ∧ ∃ M : ℕ, M₀ ≤ M ∧
              β * R ^ ν / turanLoss M s.card - B * r ^ ν ≤ ‖∑ i ∈ s, b i * z i ^ ν + E ν‖) ∧
    (∀ {h : ℝ}, 0 < h → ¬ InfiniteRankWeilTheory.ZerosApproachLine
      (fun s : {s : ℂ // riemannZeta (s - h) = 0} => (s : ℂ))) ∧
    (∀ {h : ℝ}, 0 < h → ∀ (P : (ℂ → ℂ) → Prop), P (fun s => riemannZeta (s - h)) →
      (∀ F : ℂ → ℂ, P F → MainConjecture →
        InfiniteRankWeilTheory.ZerosApproachLine (fun s : {s : ℂ // F s = 0} => (s : ℂ))) →
      ¬ MainConjecture) ∧
    (∀ {φ : ℝ → ℂ} {a : ℝ}, ContDiff ℝ 2 φ → (∀ u, φ u ≠ 0 → |u| ≤ a) → ∀ (ρ : ℂ) (t : ℝ),
      ‖paperFT φ (gammaOf ρ - t)‖ ≤
        Real.exp (|ρ.re - 1 / 2| * a) * decayMass φ / (1 + |ρ.im - t|) ^ 2) :=
  ⟨fun s z b _ hR htop _ hβ0 hβ E _ _ hE _ hG M₀ =>
      exists_mem_thick_ge s z b hR htop hβ0 hβ E hE hG M₀,
    fun hh => not_zerosApproachLine_shift hh,
    fun hh P hP route => not_mainConjecture_of_uniform_route hh P hP route,
    fun hφ hsupp ρ t => norm_paperFT_gammaOf_sub_le hφ hsupp ρ t⟩

/-- **The tools.** T1 explicit linear forms in many logarithms; T2 extrapolation along the
approximate group of returns; T3 Turán on thick sets; T4 the reciprocity of returns
`P_φ(t) = π_φ(t) + Γ_φ(t) − Z_φ(t)`. Criterion C2: rank one gives an exact Frobenius. -/
theorem the_tools :
    (∀ {φ : ℝ → ℂ}, ContDiff ℝ 2 φ → HasCompactSupport φ → (∀ u ≤ 0, φ u = 0) → ∀ t : ℝ,
      orbitPoly φ t = poleTerm φ t + gammaTerm φ t - zeroSide φ t) ∧
    (∀ {ι : Type*} {s : Finset ι} {ℓ : ι → ℝ} {L : ℝ}, IsRankOne s ℓ L → L ≠ 0 →
      ∀ (V : Finset (ι → ℤ)) (c : (ι → ℤ) → ℂ) (j : ℕ) (t : ℝ),
        ∑ ν ∈ V, c ν * ((linForm s ℓ ν) ^ j : ℝ) *
            Complex.exp (-(((t + 2 * π / L) * linForm s ℓ ν : ℝ) : ℂ) * Complex.I) =
          ∑ ν ∈ V, c ν * ((linForm s ℓ ν) ^ j : ℝ) *
            Complex.exp (-((t * linForm s ℓ ν : ℝ) : ℂ) * Complex.I)) ∧
    (∀ {ι : Type*} {T : ℝ}, 0 < T → ∀ (s : Finset ι) (ℓ : ι → ℝ),
      IsRankOne s (roundedStep T ℓ) (2 * π / T)) ∧
    (∀ {p q : ℕ}, p.Prime → q.Prime → p ≠ q → ∀ {t : ℝ}, t ≠ 0 →
      ¬ IsDeltaReturn {p, q} (fun n : ℕ => Real.log n) 0 t) :=
  ⟨fun hφ hφc hφ0 t => orbit_reciprocity hφ hφc hφ0 t,
    fun h hL V c j t => frozenJet_add_period h hL V c j t,
    fun hT s ℓ => isRankOne_roundedStep hT s ℓ,
    fun hp hq hpq _ ht => not_isDeltaReturn_zero_pair hp hq hpq ht⟩

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
