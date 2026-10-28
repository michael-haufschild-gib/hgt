import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHarmonicMeasureTensorizesOverPrimes
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheDeficitOfThePrimeFormIsADirichletEnergy

/-!
# The prime form has a spectral gap below its pole

The top of Weil's atomic prime form `P_N` is `log N − γ + o(1)`, attained near the pole `n^{−1/2}`
(`ThePoleIsTheTopOfThePrimeForm`). This file isolates it uniformly in `N`.

* **Poincaré inequality for the multiplicative walk** (`exists_poleDefect_ge`): there is `g > 0` such
  that every `x` orthogonal to the pole, `Σ_{n ≤ N} x_n/√n = 0`, has `D_N(x) ≥ g |x|²`, where
  `D_N(x) = Σ_{mt ≤ N} Λ(t)(x_{mt} − x_m/√t)²` is the pole defect.
* **The spectral gap** (`exists_atomicWeilForm_le_of_pole_orthogonal`): for every `ε > 0`, eventually
  in `N`, `P_N(x) ≤ (log N − γ − g + ε)|x|²` on the pole complement.

**Proof.** In the pole gauge `y_n = √n x_n` the defect is the Dirichlet form
`Σ Λ(t)/(mt) (y_{mt} − y_m)²` of the multiplicative walk under the harmonic measure `1/n`, and the
pole complement is the space of `1/n`-mean-zero `y`. On each `p`-ladder `{u p^i ≤ N}`, centring at the
base point bounds the ladder variance by the edges `u → u p^i`, which carry `log p ≥ log 2`
(`ladderVar_le_base_edges`); distinct ladders use distinct edges, so `D_N ≥ log 2 · Glauber`
(`log_two_mul_glauberForm_le_poleDefect`). The harmonic measure tensorizes over primes
(`TheHarmonicMeasureTensorizesOverPrimes`): `Var ≤ C · Glauber`. Hence `D_N ≥ (log 2/C)|x|²`, and the
ground-state identity with its top control (`eventually_atomicWeilForm_add_poleDefect_le`) turns the
Poincaré inequality into the gap.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open GaloisForLFunctions.ArithmeticElectrostatics ArithmeticFunction

local notation "γ" => Real.eulerMascheroniConstant

/-! ### 1. The pole gauge -/

/-- The pole gauge `y_n = √n x_n`. -/
def poleGauge (x : ℕ → ℝ) (n : ℕ) : ℝ := Real.sqrt n * x n

/-- In the pole gauge an edge of the defect is `(y_{mt} − y_m)²/(mt)`. -/
theorem sq_sub_div_sqrt_eq {m t : ℕ} (hm : 1 ≤ m) (ht : 1 ≤ t) (x : ℕ → ℝ) :
    (x (m * t) - x m / Real.sqrt t) ^ 2 =
      1 / ((m * t : ℕ) : ℝ) * (poleGauge x (m * t) - poleGauge x m) ^ 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have ht0 : (0 : ℝ) < t := by exact_mod_cast ht
  have hst0 : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have key : Real.sqrt m * Real.sqrt t * x (m * t) - Real.sqrt m * x m =
      Real.sqrt m * Real.sqrt t * (x (m * t) - x m / Real.sqrt t) := by
    field_simp
  rw [poleGauge, poleGauge, Nat.cast_mul, Real.sqrt_mul hm0.le, key, mul_pow, mul_pow,
    Real.sq_sqrt hm0.le, Real.sq_sqrt ht0.le]
  field_simp

/-- Pole orthogonality is mean zero in the pole gauge, and then the harmonic variance is `|x|²`. -/
theorem harmonicVar_poleGauge_eq {N : ℕ} {x : ℕ → ℝ} (hx : ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0) :
    harmonicVar 0 N (poleGauge x) = ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hterm : ∀ n ∈ Icc 1 N, 1 / (n : ℝ) * poleGauge x n = x n / Real.sqrt n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    have hs1 : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    rw [poleGauge, show (1 : ℝ) / n = 1 / (Real.sqrt n * Real.sqrt n) by
      rw [Real.mul_self_sqrt hn0.le]]
    field_simp
  have hmean : wMean (Icc 1 N) (fun n => 1 / (n : ℝ)) (poleGauge x) = 0 := by
    rw [wMean, sum_congr rfl hterm, hx, zero_div]
  rw [harmonicVar, roughInterval_zero, wVar, hmean]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
  rw [sub_zero, poleGauge, mul_pow, Real.sq_sqrt hn0.le]
  field_simp

/-! ### 2. The defect dominates the Glauber form -/

/-- **Ladder Poincaré**: centred at the base point, a ladder variance is at most the energy of the
edges `u → u p^i`. -/
theorem ladderVar_le_base_edges (p u N : ℕ) (y : ℕ → ℝ) :
    ladderVar p u N y ≤ ∑ i ∈ (ladder p u N).filter (fun i => 1 ≤ i),
      1 / ((u * p ^ i : ℕ) : ℝ) * (y (u * p ^ i) - y u) ^ 2 := by
  refine (wVar_le (fun i _ => ladderWeight_nonneg p u i) (y u)).trans (le_of_eq ?_)
  rw [← sum_filter_add_sum_filter_not (ladder p u N) (fun i => 1 ≤ i)]
  have h0 : ∑ i ∈ (ladder p u N).filter (fun i => ¬ 1 ≤ i),
      ladderWeight p u i * ((fun j => y (u * p ^ j)) i - y u) ^ 2 = 0 :=
    sum_eq_zero fun i hi => by
      have : i = 0 := by have := (mem_filter.mp hi).2; omega
      subst this
      simp
  rw [h0, add_zero]
  rfl

/-- Distinct prime powers: `(q, i) ↦ q^i` is injective on primes and `i ≥ 1`. -/
theorem prime_pow_inj {q₁ q₂ i₁ i₂ : ℕ} (h₁ : q₁.Prime) (h₂ : q₂.Prime) (hi₁ : 1 ≤ i₁)
    (h : q₁ ^ i₁ = q₂ ^ i₂) : q₁ = q₂ ∧ i₁ = i₂ := by
  have hq : q₁ = q₂ := by
    have : q₁ ∣ q₂ ^ i₂ := h ▸ dvd_pow_self q₁ (by omega)
    exact (Nat.prime_dvd_prime_iff_eq h₁ h₂).mp (h₁.dvd_of_dvd_pow this)
  subst hq
  exact ⟨rfl, Nat.pow_right_injective h₁.two_le h⟩

/-- **The defect dominates the Glauber form**: `log 2 · Glauber(y) ≤ D_N(x)` in the pole gauge. -/
theorem log_two_mul_glauberForm_le_poleDefect (N : ℕ) (x : ℕ → ℝ) :
    Real.log 2 * glauberForm 0 N (poleGauge x) ≤ poleDefect N x := by
  set y := poleGauge x
  set T : ℕ → ℕ → ℝ := fun u t => Λ t * (x (u * t) - x u / Real.sqrt t) ^ 2
  have hT : ∀ u t, 0 ≤ T u t := fun u t => mul_nonneg vonMangoldt_nonneg (sq_nonneg _)
  -- each prime `q` contributes `log q ≥ log 2` times its ladder variances
  have hqL : ∀ q ∈ (Icc 0 N).filter Nat.Prime, ∀ u ∈ (roughInterval 0 N).filter (fun u => ¬ q ∣ u),
      Real.log 2 * ladderVar q u N y ≤
        ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i), T u (q ^ i) := by
    intro q hq u hu
    have hqp := (mem_filter.mp hq).2
    have hu1 : 1 ≤ u := (mem_roughInterval.mp (mem_filter.mp hu).1).1
    have hl2 : Real.log 2 ≤ Real.log q :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hqp.two_le)
    calc Real.log 2 * ladderVar q u N y ≤ Real.log q * ladderVar q u N y :=
          mul_le_mul_of_nonneg_right hl2 (ladderVar_nonneg _ _ _ _)
      _ ≤ Real.log q * ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i),
          1 / ((u * q ^ i : ℕ) : ℝ) * (y (u * q ^ i) - y u) ^ 2 :=
          mul_le_mul_of_nonneg_left (ladderVar_le_base_edges q u N y)
            (Real.log_nonneg (by exact_mod_cast hqp.one_lt.le))
      _ = ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i), T u (q ^ i) := by
          rw [mul_sum]
          refine sum_congr rfl fun i hi => ?_
          have hi1 := (mem_filter.mp hi).2
          simp only [T]
          rw [vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hqp,
            sq_sub_div_sqrt_eq hu1 (Nat.one_le_pow _ _ hqp.pos) x]
  -- the prime powers below `N/u` are distinct edges of the defect
  have hu : ∀ u ∈ Icc 1 N, ∑ q ∈ (Icc 0 N).filter Nat.Prime,
      ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i), T u (q ^ i) ≤
        ∑ t ∈ Icc 1 (N / u), T u t := by
    intro u hu
    have hu1 := (mem_Icc.mp hu).1
    rw [sum_sigma']
    rw [← sum_image (s := ((Icc 0 N).filter Nat.Prime).sigma
        (fun q => (ladder q u N).filter (fun i => 1 ≤ i))) (g := fun z => z.1 ^ z.2)]
    · refine sum_le_sum_of_subset_of_nonneg (fun t ht => ?_) (fun t _ _ => hT u t)
      obtain ⟨⟨q, i⟩, hz, rfl⟩ := mem_image.mp ht
      obtain ⟨hq, hi⟩ := mem_sigma.mp hz
      have hqp := (mem_filter.mp hq).2
      have hiN := (mem_filter.mp (mem_filter.mp hi).1).2
      refine mem_Icc.mpr ⟨Nat.one_le_pow _ _ hqp.pos, ?_⟩
      rw [Nat.le_div_iff_mul_le (by omega), mul_comm]
      exact hiN
    · rintro ⟨q₁, i₁⟩ h₁ ⟨q₂, i₂⟩ h₂ heq
      obtain ⟨hq₁, hi₁⟩ := mem_sigma.mp h₁
      obtain ⟨hq₂, -⟩ := mem_sigma.mp h₂
      obtain ⟨rfl, rfl⟩ := prime_pow_inj (mem_filter.mp hq₁).2 (mem_filter.mp hq₂).2
        (mem_filter.mp hi₁).2 heq
      rfl
  -- assemble
  rw [glauberForm, mul_sum, roughInterval_zero]
  calc ∑ q ∈ (Icc 0 N).filter Nat.Prime, Real.log 2 *
        ∑ u ∈ (Icc 1 N).filter (fun u => ¬ q ∣ u), ladderVar q u N y
      ≤ ∑ q ∈ (Icc 0 N).filter Nat.Prime, ∑ u ∈ Icc 1 N,
          ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i), T u (q ^ i) := by
        refine sum_le_sum fun q hq => ?_
        rw [mul_sum]
        refine (sum_le_sum fun u hu => hqL q hq u (by rwa [roughInterval_zero])).trans ?_
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          fun u _ _ => sum_nonneg fun i _ => hT u _
    _ = ∑ u ∈ Icc 1 N, ∑ q ∈ (Icc 0 N).filter Nat.Prime,
          ∑ i ∈ (ladder q u N).filter (fun i => 1 ≤ i), T u (q ^ i) := sum_comm
    _ ≤ ∑ u ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / u), T u t := sum_le_sum hu
    _ = poleDefect N x := rfl

/-! ### 3. The Poincaré inequality and the gap -/

/-- **Poincaré inequality for the multiplicative walk.** There is `g > 0` such that for every `N`,
every `x` orthogonal to the pole has pole defect at least `g|x|²`. -/
theorem exists_poleDefect_ge : ∃ g : ℝ, 0 < g ∧ ∀ N : ℕ, ∀ x : ℕ → ℝ,
    ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 → g * ∑ n ∈ Icc 1 N, x n ^ 2 ≤ poleDefect N x := by
  obtain ⟨C, hC, hCg⟩ := exists_harmonicVar_le_glauberForm
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨Real.log 2 / C, by positivity, fun N x hx => ?_⟩
  have h1 := hCg N (poleGauge x)
  have h2 := log_two_mul_glauberForm_le_poleDefect N x
  rw [harmonicVar_poleGauge_eq hx] at h1
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  nlinarith

/-- **The prime form has a spectral gap below its pole.** There is `g > 0` such that for every
`ε > 0`, eventually in `N`, every `x` orthogonal to the pole satisfies
`P_N(x) ≤ (log N − γ − g + ε)|x|²`. -/
theorem exists_atomicWeilForm_le_of_pole_orthogonal : ∃ g : ℝ, 0 < g ∧ ∀ ε : ℝ, 0 < ε →
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 →
      atomicWeilForm N x ≤ (Real.log N - γ - g + ε) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  obtain ⟨g, hg, hD⟩ := exists_poleDefect_ge
  refine ⟨g, hg, fun ε hε => ?_⟩
  set ε₁ := min (1 / 2) (ε / (1 + g))
  have hε₁ : 0 < ε₁ := lt_min (by norm_num) (by positivity)
  have hε₁2 : ε₁ ≤ 1 / 2 := min_le_left _ _
  have hε₁g : ε₁ * (1 + g) ≤ ε := by
    have := min_le_right (1 / 2 : ℝ) (ε / (1 + g))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  obtain ⟨N₀, hN₀⟩ := eventually_atomicWeilForm_add_poleDefect_le hε₁
  refine ⟨N₀, fun N hN x hx => ?_⟩
  have h1 := hN₀ N hN x
  have h2 := hD N x hx
  have hS : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have h3 : (1 - ε₁) * (g * ∑ n ∈ Icc 1 N, x n ^ 2) ≤ (1 - ε₁) * poleDefect N x :=
    mul_le_mul_of_nonneg_left h2 (by linarith)
  nlinarith

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
