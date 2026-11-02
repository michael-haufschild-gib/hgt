import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheAliasingConstantOfTheTiltedSpline
import GaloisForLFunctions.RHTower.WeilMarkovPoleCapacity

/-!
# The primes of a horizon window

Weil's form is a Markov form plus the pole plane (RHTower):
`Q(g) = V_N ‖g‖² + J_arch(g) + Σ_{2 ≤ n ≤ N} Λ(n) n^{−1/2} ‖g − g(· + log n)‖² + ½⟨c, g⟩² − ½⟨s, g⟩²`
with the creation potential `V_N = Ω(0) − 2 Σ_{n ≤ N} Λ(n)/√n`, for every level `N` past the
support of `g`. This file reads the splitting on horizon windows.

* **Departing jumps pay their creation** (`primeJump_departing_eq`): a prime jump that leaves the
  support costs exactly `2Λ(n)/√n ‖g‖²`, the creation it adds; so the Markov form does not depend
  on the level past the support (`markovForm_eq_of_level`).
* **The primes a horizon window sees** (`weilQuad_halfWeight_eq_markovForm`): for `H = e^{y/2} h`,
  `h` on `[−A, 0]`, `Q(H) = M_N(H) + pole(H)` for every `N ≥ e^A`; only the prime powers `n ≤ e^A`
  act on `H` by a genuine jump, all larger ones pay their own creation potential.

With the exact second-order term `κ Q(H) + (7J(1)/K) ‖H‖²_{−8}`, whose correction is prime-free, the
prime atoms enter the degeneration at second order only through Weil's form of the window, and only
the primes up to the window length act on it.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole

variable {g h : ℝ → ℝ} {A : ℝ}

/-- `Q(g) = M_N(g) + ½⟨c, g⟩² − ½⟨s, g⟩²` past the support. -/
theorem weilQuad_eq_markovForm (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {N : ℕ}
    (hN : ∀ n : ℕ, N < n → ∀ u, g u * g (u + Real.log n) = 0) :
    weilQuad g = markovForm N g + coshPairing g ^ 2 / 2 - sinhPairing g ^ 2 / 2 :=
  weil_eq_markovForm_add_pole hg hgc hN

/-- **A departing jump pays its creation**: if `g` and its translate by `log n` are disjoint,
`Λ(n) n^{−1/2} ‖g − g(· + log n)‖² = 2 Λ(n) n^{−1/2} ‖g‖²`. -/
theorem primeJump_departing_eq (hg : Continuous g) (hgc : HasCompactSupport g) {n : ℕ}
    (hn : ∀ u, g u * g (u + Real.log n) = 0) :
    primeJumpWeight n * ∫ u, (g u - g (u + Real.log n)) ^ 2 =
      2 * primeJumpWeight n * ∫ u, g u ^ 2 := by
  have hsq := integrable_sq hg hgc
  have hsq' : Integrable fun u => g (u + Real.log n) ^ 2 :=
    integrable_sq (hg.comp (continuous_add_const _)) (hasCompactSupport_comp_add hgc _)
  have hexp : ∀ u, (g u - g (u + Real.log n)) ^ 2 =
      g u ^ 2 + g (u + Real.log n) ^ 2 - 2 * (g u * g (u + Real.log n)) := fun u => by ring
  have htr : ∫ u, g (u + Real.log n) ^ 2 = ∫ u, g u ^ 2 :=
    integral_add_right_eq_self (fun u => g u ^ 2) (Real.log n)
  simp_rw [hexp, hn, mul_zero, sub_zero]
  rw [integral_add hsq hsq', htr]
  ring

/-- **Level independence**: past the support the Markov form does not see further primes. -/
theorem markovForm_eq_of_level (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {N₀ N : ℕ}
    (hN₀ : ∀ n : ℕ, N₀ < n → ∀ u, g u * g (u + Real.log n) = 0) (hle : N₀ ≤ N) :
    markovForm N g = markovForm N₀ g := by
  have h1 := weilQuad_eq_markovForm hg hgc hN₀
  have h2 := weilQuad_eq_markovForm hg hgc (N := N) fun n hn => hN₀ n (lt_of_le_of_lt hle hn)
  linarith

/-- A horizon window does not overlap its translates by `log n` for `n > e^A`. -/
theorem halfWeight_mul_translate_eq_zero (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {n : ℕ}
    (hn : Real.exp A < n) (u : ℝ) : halfWeight h u * halfWeight h (u + Real.log n) = 0 := by
  have hn0 : (0 : ℝ) < n := lt_trans (Real.exp_pos A) hn
  have hlog : A < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hn
  by_cases hu : u ∈ Set.Icc (-A) 0
  · rw [halfWeight, halfWeight, hsupp (u + Real.log n) fun hm => by linarith [hm.2, hu.1]]
    ring
  · rw [halfWeight, hsupp u hu]; ring

/-- **The primes a horizon window sees.** For `H = e^{y/2} h`, `h` on `[−A, 0]`, and every level
`N ≥ e^A`: `Q(H) = M_N(H) + ½⟨c, H⟩² − ½⟨s, H⟩²`, and `M_N(H)` is the Markov form at level
`⌊e^A⌋`: the prime powers beyond the window length pay their own creation potential. -/
theorem weilQuad_halfWeight_eq_markovForm (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) {N : ℕ} (hN : ⌊Real.exp A⌋₊ ≤ N) :
    weilQuad (halfWeight h) = markovForm ⌊Real.exp A⌋₊ (halfWeight h) +
        coshPairing (halfWeight h) ^ 2 / 2 - sinhPairing (halfWeight h) ^ 2 / 2 ∧
      markovForm N (halfWeight h) = markovForm ⌊Real.exp A⌋₊ (halfWeight h) := by
  have hH : ContDiff ℝ 2 (halfWeight h) :=
    (Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul hh
  have hHc : HasCompactSupport (halfWeight h) :=
    HasCompactSupport.intro (isCompact_Icc (a := -A) (b := 0)) fun y hy => by
      simp [halfWeight, hsupp y hy]
  have hN₀ : ∀ n : ℕ, ⌊Real.exp A⌋₊ < n → ∀ u,
      halfWeight h u * halfWeight h (u + Real.log n) = 0 := fun n hn u =>
    halfWeight_mul_translate_eq_zero hsupp (Nat.floor_lt (Real.exp_pos A).le |>.mp hn) u
  exact ⟨weilQuad_eq_markovForm hH hHc hN₀, markovForm_eq_of_level hH hHc hN₀ hN⟩

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
