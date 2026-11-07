import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.ThePrecisionLawOfTheFirstReturn
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.ProportionalSavingIsAHeavyFirstReturn
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheFadeOfAReturn
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheConditionalMomentsOfTheTail
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheHeadIsFrozenAtItsResolution
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheDepthAspect
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.EulerCoordinatesStopAtTheAbscissa
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheCombOfAReturn
import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheRecurrenceDichotomyOfTheTail

/-!
# The questions of the field

The six questions of tail arithmetic of the prime orbit, each with its answer as one statement.

1. What is the first return `R(y, δ)`? (`question_one`)
2. What does the tail look like conditionally on alignment below it, at resolution finer than `1/log y`?
   (`question_two`)
3. Why is `t log n` not a generic phase past Vinogradov's degree, given that binomial phases have no saving?
   (`question_three`)
4. What replaces `q`-factorization at the archimedean place? (`question_four`)
5. Is an atypical bounded return possible at a right zero, and what does its tail look like? (`question_five`)
6. Which certificates in non-returning coordinates survive past `Re s = 1`? (`question_six`)

The tools are collected in `the_tools`.
-/

open Real Finset Filter Topology Complex MeasureTheory Metric

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-- **Question 1.** The first return on the primes below `y` is at most `Q^{π(y)}` (Dirichlet). It exceeds
`exp(√(y/(48 log y)))` at precision `≍ y^{−9/2}` (the bound RH gives at constant precision), and `exp(y^{1/A})` at
precision `exp(−δ y^{1/A})`. At the weights `1/p` the harmonic defect is `log log N − log|ζ(1 + 1/log N + it)|` up to an
absolute constant, so the first weak return is the inverse of the extreme-value function of `ζ` next to the `1`-line;
and at every precision below `1` the first return tends to infinity with the length. -/
theorem question_one :
    (∀ (N Q : ℕ) (η : ℝ), 1 ≤ Q → 2 * π ^ 2 ≤ η * (Q : ℝ) ^ 2 →
      firstReturn N.primesBelow logStep η ≤ (Q : ℝ) ^ (N.primesBelow).card) ∧
    (∀ᶠ N : ℕ in atTop, ∀ η : ℝ, 0 < η → η * (12 * √(N : ℝ)) * (N : ℝ) ^ 4 < 4 / 10 ^ 10 * 48 ^ 4 →
      Real.exp (√((N : ℝ) / (48 * Real.log N))) < firstReturn N.primesBelow logStep η) ∧
    (∀ A δ : ℝ, 1 < A → 0 < δ → ∀ᶠ N : ℕ in atTop, ∀ η : ℝ, 0 < η →
      η * (12 * √(N : ℝ)) < Real.exp (-(δ * (N : ℝ) ^ (1 / A))) →
      Real.exp ((N : ℝ) ^ (1 / A)) < firstReturn N.primesBelow logStep η) ∧
    (∀ N : ℕ, 3 ≤ N → ∀ t : ℝ,
      |harmonicDefect N t - (RHTower.Sieve.logLog N - Real.log ‖riemannZeta (spikePoint N t)‖)| ≤
        harmonicConst) ∧
    (∀ η : ℝ, 0 < η → η < 1 → Tendsto (fun N : ℕ => firstReturn (Nat.primesLE N) logStep η) atTop atTop) :=
  ⟨fun _ _ _ hQ hηQ => firstReturn_le_pow _ _ hQ hηQ, eventually_exp_sqrt_lt_firstReturn,
    fun _ _ hA hδ => eventually_exp_rpow_lt_firstReturn hA hδ, fun _ hN t => abs_harmonicDefect_sub_le hN t,
    fun _ h0 h1 => tendsto_firstReturn_primes h0 h1⟩

/-- **Question 2.** Conditionally on a head weight `|R|²` on smooth integers, below the Kronecker scale the tail on rough
integers has its unconditional second moment, zero mean, and Gaussian moments `k! ‖b‖^{2k}` with Gaussian large
deviations. Finer than the resolution `1/log y` the head does not move: on `Re s ≥ 1`,
`|log|E_y(s + iv)| − log|E_y(s)|| ≤ 2|v|(log y + log 4)`, so every finer variation of `|ζ|` is the tail's. -/
theorem question_two :
    (∀ (y : ℕ) (A B : Finset ℕ), (∀ m ∈ A, m ∈ Nat.smoothNumbers y) → (∀ n ∈ B, IsRough y n) →
      ∀ (r b : ℕ → ℂ) (N : ℕ), (∀ m ∈ A, m ≤ N) → (∀ m ∈ A, ∀ n ∈ B, m * n ≤ N) → ∀ T : ℝ,
      |(∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2 * ‖headPoly B b t‖ ^ 2) -
          (∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2| ≤
        16 * N * (1 + Real.log N) * ((∑ m ∈ A, ‖r m‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2)) ∧
    (∀ (y : ℕ) (A B : Finset ℕ), (∀ m ∈ A, m ∈ Nat.smoothNumbers y) → (∀ n ∈ B, IsRough y n) →
      (∀ n ∈ B, 2 ≤ n) → ∀ (r b : ℕ → ℂ) (N : ℕ), 1 ≤ N → (∀ m ∈ A, m ≤ N) →
      (∀ m ∈ A, ∀ n ∈ B, m * n ≤ N) → ∀ T₁ T₂ : ℝ,
      ‖∫ t in T₁..T₂, ((‖headPoly A r t‖ ^ 2 : ℝ) : ℂ) * headPoly B b t‖ ≤
        2 * N * ((∑ m ∈ A, ‖r m‖) ^ 2 * ∑ n ∈ B, ‖b n‖)) ∧
    (∀ (y : ℕ) (A B : Finset ℕ), (∀ m ∈ A, m ∈ Nat.smoothNumbers y) → (∀ p ∈ B, p.Prime ∧ y ≤ p) →
      ∀ (r b : ℕ → ℂ) (k N Z : ℕ), (∀ p ∈ B, p ≤ Z) → (∀ m ∈ A, m * Z ^ k ≤ N) → ∀ T V : ℝ, 0 ≤ T → 0 < V →
      (∫ t in Set.Icc T (2 * T) ∩ {t | V ≤ ‖headPoly B b t‖}, ‖headPoly A r t‖ ^ 2) ≤
        (T + 8 * N * (1 + Real.log N)) * (∑ m ∈ A, ‖r m‖ ^ 2) *
          (k.factorial * ((∑ p ∈ B, ‖b p‖ ^ 2) / V ^ 2) ^ k)) ∧
    (∀ y : ℕ, 1 ≤ y → ∀ s : ℂ, 1 ≤ s.re → ∀ v : ℝ,
      |Real.log ‖RHTower.eulerHead y (s + v * I)‖ - Real.log ‖RHTower.eulerHead y s‖| ≤
        2 * |v| * (Real.log y + Real.log 4)) :=
  ⟨fun _ _ _ hA hB r b _ hAN hN T => abs_conditional_second_moment_sub_le hA hB r b hAN hN T,
    fun _ _ _ hA hB hB1 r b _ hN1 hAN hN T₁ T₂ => norm_integral_head_sq_mul_tail_le hA hB hB1 r b hN1 hAN hN T₁ T₂,
    fun _ _ _ hA hB r b k _ _ hZ hN _ _ hT hV => setIntegral_head_on_large_tail_le hA hB r b k hZ hN hT hV,
    fun _ hy _ hs v => abs_log_norm_eulerHead_sub_le_of_one_le hy hs v⟩

open Classical in
/-- **Question 3.** The jet of `t log` on a block depends only on `x/h`; its coefficients move at every step by at least
`(j+1)!/(x+j+2)^{j+2}`; so the blocks whose coefficient sits within `η` of a lattice `c + ℤ` are isolated. The ceiling
`2/(k+1)` of a binomial phase is a ceiling for one block, not for a moving family of blocks. -/
theorem question_three :
    (∀ (h x : ℝ), 0 < h → 0 < x → ∀ n : ℕ, 1 ≤ n →
      (fwdDiff h)^[n] Real.log x = (fwdDiff (1 : ℝ))^[n] Real.log (x / h)) ∧
    (∀ (j : ℕ) (x : ℝ), 0 < x → logDiffMass j x - logDiffMass j (x + 1) = logDiffMass (j + 1) x ∧
      (j.factorial : ℝ) / (x + j + 1) ^ (j + 1) ≤ logDiffMass j x) ∧
    (∀ (t : ℝ), 0 < t → ∀ (j X H : ℕ), 1 ≤ X → ∀ (c η : ℝ), 0 ≤ η →
      (((Icc X (X + H)).filter fun x : ℕ => ∃ m : ℤ, |t * logDiffMass j (x : ℝ) / (2 * π) - c - m| ≤ η).card : ℝ) ≤
        (t * j.factorial / (2 * π * (X : ℝ) ^ (j + 1)) + 2) *
          (2 * η * (2 * π * ((X : ℝ) + H + j + 2) ^ (j + 2) / (t * (j + 1).factorial)) + 1)) :=
  ⟨fun _ _ hh hx _ hn => fwdDiff_iter_log_dilate hh hx hn,
    fun j _ hx => ⟨logDiffMass_sub_succ j hx, le_logDiffMass j hx⟩,
    fun _ ht j _ _ hX c _ hη => card_exotic_le ht j hX c hη⟩

/-- **Question 4.** In the depth aspect `q = q₁q₂`, `q₂ ∣ q₁`, the map `u ↦ 1 + q₁u` is an exact homomorphism and
`q`-differencing is exact. At the archimedean place `h ↦ t log(1 + h/x)` is additive up to `|t| h h'/x²`: the real scale
`x/√|t|` replaces the factor `q₁ ≍ √q`, and the quadratic Taylor term is the defect that vanishes `p`-adically. -/
theorem question_four :
    (∀ (q₁ q₂ : ℕ), q₂ ∣ q₁ → ∀ (χ : MulChar (ZMod (q₁ * q₂)) ℂ) (u v : ZMod (q₁ * q₂)),
      χ (1 + q₁ * (u + v)) = χ (1 + q₁ * u) * χ (1 + q₁ * v)) ∧
    (∀ (q₁ q₂ : ℕ) (χ : MulChar (ZMod (q₁ * q₂)) ℂ) (n : (ZMod (q₁ * q₂))ˣ) (h : ZMod (q₁ * q₂)),
      χ (n + q₁ * h) = χ n * χ (1 + q₁ * (h * (n⁻¹ : (ZMod (q₁ * q₂))ˣ)))) ∧
    (∀ (t x h h' : ℝ), 0 < x → 0 ≤ h → 0 ≤ h' →
      |t * Real.log (1 + h / x) + t * Real.log (1 + h' / x) - t * Real.log (1 + (h + h') / x)| ≤
        |t| * (h * h') / x ^ 2) ∧
    (∀ (t x h : ℝ), 0 < x → 0 ≤ h → |t * Real.log (1 + h / x) - t * (h / x)| ≤ |t| * h ^ 2 / x ^ 2) :=
  ⟨fun _ _ hq χ u v => mulChar_one_add_mul_add hq χ u v, fun _ _ χ n h => mulChar_add_mul χ n h,
    fun t _ _ _ hx hh hh' => log_one_add_defect_le t hx hh hh', fun t _ _ hx hh => abs_log_one_add_sub_le t hx hh⟩

/-- **Question 5.** The zeros of `ζ` on `Re s > 0` are the zeros of the tail `ζ M_y` at every cut. At a right zero the
returns of `ζ` on an isolating disc are tail-bad at every cut, with a tolerance independent of the cut, and have density
zero. Along a bounded phase return the tail converges to `ζ M_y`, so the tail carries the zero and the head stays at
`E_y(ρ) ≠ 0`. On the universal disc about every point of the strip, nonvanishing targets are approached at positive
density, and targets with a zero only at heights tail-bad at every cut. Whether a bounded return at a right zero exists
is the exact input of the asymptotic abscissa law (AAD). -/
theorem question_five :
    (∀ (y : ℕ) (s : ℂ), 0 < s.re → (eulerTail y s = 0 ↔ riemannZeta s = 0)) ∧
    (∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 →
      ∃ r m : ℝ, 0 < r ∧ 0 < m ∧
        (∀ y : ℕ, RHTower.zetaReturnSet (closedBall ρ r) (m / 2) ⊆ RHTower.eulerDiscTailBadSet y ρ r (m / 4)) ∧
        ∀ δ : ℝ, 0 < δ → ∀ᶠ T : ℝ in atTop,
          volume (RHTower.zetaReturnSet (closedBall ρ r) (m / 2) ∩ Set.Icc 0 T) ≤ ENNReal.ofReal (δ * T)) ∧
    (∀ (τ : ℕ → ℝ), ArithmeticAuxiliaryDynamics.IsPhaseReturn τ → ∀ (y : ℕ) (s : ℂ),
      Tendsto (fun j => eulerMollifier y (s + τ j * I)) atTop (𝓝 (eulerMollifier y s))) ∧
    (∀ z₀ : ℂ, 1 / 2 < z₀.re → z₀.re < 1 → ∃ r > 0,
      (∀ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball z₀ (4 * r)) → (∀ z ∈ ball z₀ (4 * r), g z ≠ 0) →
        ∀ ε > 0, ∃ c > 0, ∀ᶠ T : ℝ in atTop,
          ENNReal.ofReal (c * T) ≤ volume (RHTower.zetaTargetReturnSet g (closedBall z₀ r) ε ∩ Set.Icc 0 T)) ∧
      (∀ g : ℂ → ℂ, (∃ w ∈ ball z₀ r, g w = 0) → ∀ m : ℝ, (∀ z ∈ sphere z₀ r, m ≤ ‖g z‖) →
        (∀ y : ℕ, RHTower.zetaTargetReturnSet g (closedBall z₀ r) (m / 2) ⊆
          RHTower.eulerDiscTailBadSet y z₀ r (m / 4)) ∧
        ∀ κ > 0, ∀ᶠ T : ℝ in atTop,
          volume (RHTower.zetaTargetReturnSet g (closedBall z₀ r) (m / 2) ∩ Set.Icc 0 T) ≤
            ENNReal.ofReal (κ * T))) :=
  ⟨fun y _ hs => eulerTail_eq_zero_iff y hs, fun _ hρ h1 h2 => exists_returns_tailBad_and_rare hρ h1 h2,
    fun _ h y s => tendsto_eulerMollifier_of_phaseReturn h y s, fun _ h1 h2 => tail_recurrence_dichotomy h1 h2⟩

/-- **Question 6.** On `Re s > ½`, `Σ_p |1 − E_p(s)| < ∞` exactly when `Re s > 1`, and no family within summable distance
of the Euler factors does better: prime-by-prime product certificates stop at the abscissa. What survives is the
head–tail certificate: any factorization is a decomposition with rank-one kernels, and the tail coordinate is Schur
exactly where `|S|` is at most the head. -/
theorem question_six :
    (∀ s : ℂ, 1 / 2 < s.re →
      (Summable (fun p : Nat.Primes => ‖1 - scatteringFactor p s‖) ↔ 1 < s.re)) ∧
    (∀ s : ℂ, 1 / 2 < s.re → s.re ≤ 1 → ∀ z : Nat.Primes → ℂ,
      Summable (fun p : Nat.Primes => ‖z p - scatteringFactor p s‖) →
      ¬ Summable (fun p : Nat.Primes => ‖1 - z p‖)) ∧
    (∀ {X : Type} (S : X → ℂ) (z : ℕ → X → ℂ) (n : ℕ) (x y : X),
      ∏ i ∈ range n, z i x ≠ 0 → ∏ i ∈ range n, z i y ≠ 0 →
      1 - S x * (starRingEnd ℂ) (S y) =
        ∑ i ∈ range (n + 1), (1 - headTailCoordinates S z n i x * (starRingEnd ℂ) (headTailCoordinates S z n i y)) *
          ((∏ m ∈ range i, headTailCoordinates S z n m x) *
            (starRingEnd ℂ) (∏ m ∈ range i, headTailCoordinates S z n m y))) ∧
    (∀ {X : Type} (S : X → ℂ) (z : ℕ → X → ℂ) (n : ℕ) (x : X), ∏ i ∈ range n, z i x ≠ 0 →
      (‖tailCoordinate S z n x‖ ≤ 1 ↔ ‖S x‖ ≤ ‖∏ i ∈ range n, z i x‖)) :=
  ⟨fun _ hs => summable_one_sub_scatteringFactor_iff hs, fun _ h1 h2 z hz => not_summable_of_summable_sub h1 h2 z hz,
    fun S z n _ _ hx hy => headTail_certificate S z n hx hy, fun S z n _ hne => norm_tailCoordinate_le_one_iff S z n hne⟩

/-- **The tools.** Proportional saving is the absence of heavy returns (both directions); a return lays the smooth
integers on a comb, which past the height is thin. -/
theorem the_tools :
    (∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (a ℓ : ι → ℝ), (∀ i ∈ s, 0 ≤ a i) → ∀ η c t : ℝ, 0 < η →
      (∀ H ⊆ s, IsReturn H ℓ η t → ∑ i ∈ H, a i ≤ (1 - c / η) * weightedSize s a) →
      c * weightedSize s a ≤ weightedDefect s a ℓ t) ∧
    (∀ {ι : Type} [DecidableEq ι] (s : Finset ι) (a ℓ : ι → ℝ), (∀ i ∈ s, 0 ≤ a i) → ∀ η κ c t : ℝ, 0 ≤ η →
      c * weightedSize s a ≤ weightedDefect s a ℓ t → η * weightedSize s a + 2 * κ < c * weightedSize s a →
      ∀ H : Finset ι, H ⊆ s → ∑ i ∈ s \ H, a i ≤ κ → ¬ IsReturn H ℓ η t) ∧
    (∀ (P : Finset ℕ) (η t : ℝ), 0 < t → IsReturn P logStep η t → ∀ X H k : ℕ, 1 ≤ X →
      (∀ n ∈ Icc X (X + H), (∀ p, p.Prime → p ∣ n → p ∈ P) ∧ ArithmeticFunction.cardFactors n ≤ k) →
      (H + 1 : ℝ) ≤ (t * (Real.log (X + H : ℕ) - Real.log X) / (2 * π) + 2) *
        (4 * π * (k * √(η / 8)) * (X + H + 1) / t + 1)) :=
  ⟨fun _ _ _ ha _ _ _ hη hno => saving_of_no_heavy_return ha hη hno,
    fun _ _ _ ha _ _ _ _ hη hsave hc _ hH hκ => no_heavy_return_of_saving ha hη hsave hc hH hκ,
    fun _ _ _ ht hret _ _ _ hX hsmooth => comb_inequality ht hret hX hsmooth⟩

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
