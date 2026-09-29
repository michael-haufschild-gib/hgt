import Mathlib

/-!
# Algebra of the discrete `ζ′`-moment method

These are the exact identities used to exclude finite-type second completions of the archimedean
Weil datum of `ζ`.

- **Derivative functional equation at zeros** (`deriv_riemannZeta_one_sub_eq_of_zero`). From
  `ζ(1 − s) = A(s) ζ(s)`, with `A(s) = 2(2π)^{-s} Γ(s) cos(πs/2)`, differentiation gives
  `ζ'(1 − ρ) = −A(ρ) ζ'(ρ)` at every zero `ρ` with `Re ρ > 0`.
- **The moment identity** (`deriv_mul_reflectionCombination_eq`):
  `ζ'(ρ)(E(1−ρ) + A(ρ)E(ρ)) = ζ'(ρ)E(1−ρ) − ζ'(1−ρ)E(ρ)`.
  This turns the realness constraint at critical zeros into a difference of two discrete moments of
  `ζ'`.
- **Nondegeneracy** (`eq_zero_of_sum_multiples_div_eq_const`). If a finitely supported `e`
  satisfies `Σ_q e(qm)/q = Σ_n e(n)/n` for every `m ≥ 1`, then `e = 0`. This is the statement that
  the main-term functional `B(E, ·)` of the moment asymptotic vanishes identically only for `E = 0`.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- The reflection factor `A(s) = 2 (2π)^{-s} Γ(s) cos(πs/2)` in `ζ(1 − s) = A(s) ζ(s)`. -/
def zetaReflectionFactor (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2)

theorem differentiableAt_zetaReflectionFactor {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ zetaReflectionFactor s := by
  have hΓ : DifferentiableAt ℂ Complex.Gamma s := by
    refine Complex.differentiableAt_Gamma s fun m h => ?_
    have := congrArg Complex.re h
    simp at this
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hbase : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero two_ne_zero this
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    (differentiableAt_id.neg).const_cpow (Or.inl hbase)
  unfold zetaReflectionFactor
  have hcos : DifferentiableAt ℂ (fun z : ℂ => Complex.cos (Real.pi * z / 2)) s := by fun_prop
  exact ((hpow.const_mul 2).mul hΓ).mul hcos

/-- **Derivative functional equation at a zero.**  If `ζ(ρ) = 0` with `Re ρ > 0` and `ρ ≠ 1`, then
`ζ'(1 − ρ) = −A(ρ) ζ'(ρ)`, where `ζ(1 − s) = A(s) ζ(s)`. -/
theorem deriv_riemannZeta_one_sub_eq_of_zero {ρ : ℂ} (hre : 0 < ρ.re) (h1 : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) :
    deriv riemannZeta (1 - ρ) = -(zetaReflectionFactor ρ * deriv riemannZeta ρ) := by
  have hev : (fun s => riemannZeta (1 - s)) =ᶠ[𝓝 ρ]
      fun s => zetaReflectionFactor s * riemannZeta s := by
    have h1' : ∀ᶠ s in 𝓝 ρ, 0 < s.re :=
      (Complex.continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hre
    have h2' : ∀ᶠ s in 𝓝 ρ, s ≠ 1 := eventually_ne_nhds h1
    filter_upwards [h1', h2'] with s hs hs1
    rw [zetaReflectionFactor]
    refine riemannZeta_one_sub (fun n h => ?_) hs1
    have := congrArg Complex.re h
    simp at this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h1ρ : (1 - ρ) ≠ 1 := by
    intro h
    have : ρ = 0 := by linear_combination -h
    rw [this] at hre; simp at hre
  have hL : HasDerivAt (fun s => riemannZeta (1 - s)) (-(deriv riemannZeta (1 - ρ))) ρ := by
    have hz' : HasDerivAt riemannZeta (deriv riemannZeta (1 - ρ)) (1 - ρ) :=
      (differentiableAt_riemannZeta h1ρ).hasDerivAt
    have hlin : HasDerivAt (fun s : ℂ => 1 - s) (-1) ρ := by
      simpa using (hasDerivAt_id ρ).const_sub 1
    have := hz'.comp ρ hlin
    simpa [Function.comp_def] using this
  have hR : HasDerivAt (fun s => zetaReflectionFactor s * riemannZeta s)
      (deriv zetaReflectionFactor ρ * riemannZeta ρ +
        zetaReflectionFactor ρ * deriv riemannZeta ρ) ρ :=
    (differentiableAt_zetaReflectionFactor hre).hasDerivAt.mul
      (differentiableAt_riemannZeta h1).hasDerivAt
  have hR' := hR.congr_of_eventuallyEq hev
  have huniq := hL.unique hR'
  rw [hz, mul_zero, zero_add] at huniq
  linear_combination -huniq

/-- **Recovery from sums over multiples.**  If `e` vanishes beyond `N` and
`Σ_{q ≤ N} e(qm)/q = 0` for every `m ≥ 1`, then `e(n) = 0` for every `n ≥ 1`: at the largest `n`
with `e(n) ≠ 0`, only the term `q = 1` survives. -/
theorem eq_zero_of_sum_multiples_div_eq_zero {e : ℕ → ℂ} {N : ℕ} (he : ∀ n, N < n → e n = 0)
    (h : ∀ m, 1 ≤ m → ∑ q ∈ Finset.Icc 1 N, e (q * m) / q = 0) : ∀ n, 1 ≤ n → e n = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨n₁, hn₁, hne₁⟩ := hcon
  set Sset := (Finset.Icc 1 N).filter (fun n => e n ≠ 0) with hS
  have hmem₁ : n₁ ∈ Sset := by
    rw [hS, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hn₁, ?_⟩, hne₁⟩
    by_contra hlt
    exact hne₁ (he n₁ (by omega))
  have hne : Sset.Nonempty := ⟨n₁, hmem₁⟩
  set n₀ := Sset.max' hne with hn₀
  have hn₀mem : n₀ ∈ Sset := Finset.max'_mem Sset hne
  rw [hS, Finset.mem_filter, Finset.mem_Icc] at hn₀mem
  obtain ⟨⟨hn₀1, hn₀N⟩, hn₀e⟩ := hn₀mem
  have hbig : ∀ n, n₀ < n → e n = 0 := by
    intro n hn
    by_contra hen
    by_cases hnN : n ≤ N
    · have hmem : n ∈ Sset := by
        rw [hS, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨by omega, hnN⟩, hen⟩
      have := Finset.le_max' Sset n hmem
      omega
    · exact hen (he n (by omega))
  have hsum := h n₀ hn₀1
  have hN1 : 1 ≤ N := le_trans hn₀1 hn₀N
  rw [Finset.sum_eq_single_of_mem 1 (by simp [hN1])] at hsum
  · simp at hsum
    exact hn₀e hsum
  · intro q hq hq1
    rw [Finset.mem_Icc] at hq
    have hq2 : 2 ≤ q := by omega
    have : n₀ < q * n₀ := by nlinarith
    rw [hbig _ this, zero_div]

/-- **Nondegeneracy of the discrete-moment functional.**  If `e` vanishes beyond `N` and, for every
`m ≥ 1`, `Σ_{q ≤ N} e(qm)/q` equals the constant `E(1) = Σ_{n ≤ N} e(n)/n`, then `e = 0` on
`n ≥ 1`. (For `m > N` the left side vanishes, so `E(1) = 0`.) -/
theorem eq_zero_of_sum_multiples_div_eq_const {e : ℕ → ℂ} {N : ℕ} (he : ∀ n, N < n → e n = 0)
    (h : ∀ m, 1 ≤ m → ∑ q ∈ Finset.Icc 1 N, e (q * m) / q =
      ∑ n ∈ Finset.Icc 1 N, e n / n) : ∀ n, 1 ≤ n → e n = 0 := by
  have hE : ∑ n ∈ Finset.Icc 1 N, e n / n = 0 := by
    rw [← h (N + 1) (by omega)]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.mem_Icc] at hq
    rw [he _ (by nlinarith), zero_div]
  exact eq_zero_of_sum_multiples_div_eq_zero he fun m hm => (h m hm).trans hE

/-- **The discrete-moment identity at a zero.**  With `G_E(ρ) = E(1−ρ) + A(ρ)E(ρ)` (where
`χ(1−ρ) = A(ρ)`), `ζ'(ρ) G_E(ρ) = ζ'(ρ)E(1−ρ) − ζ'(1−ρ)E(ρ)` at every zero with `Re ρ > 0`,
`ρ ≠ 1`, for arbitrary values `E(ρ)`, `E(1−ρ)`. -/
theorem deriv_mul_reflectionCombination_eq {ρ : ℂ} (hre : 0 < ρ.re) (h1 : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) (Eρ E1ρ : ℂ) :
    deriv riemannZeta ρ * (E1ρ + zetaReflectionFactor ρ * Eρ) =
      deriv riemannZeta ρ * E1ρ - deriv riemannZeta (1 - ρ) * Eρ := by
  rw [deriv_riemannZeta_one_sub_eq_of_zero hre h1 hz]
  ring

end RHTower
