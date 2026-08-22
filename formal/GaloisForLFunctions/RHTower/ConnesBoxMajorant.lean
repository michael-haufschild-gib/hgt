import GaloisForLFunctions.RHTower.ConnesBoxOverlap

/-!
# §VII (9): the rapid-decay box majorant

§VII (9) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `|f_i(x)| ≤ ∑_n λ_n k_n(x)`   for all `x ∈ A_S`,

with `(λ_n)` of rapid decay and `k_n` the characteristic function of the box
`K_n = {x : |x_v| ≤ n ∀ v ∈ S}`.

Connes states this as an immediate consequence of `f ∈ 𝒮(A_S)`.  The construction is a telescoping
one and needs nothing about `A_S`: if `|f(x)| ≤ μ(r(x))` for a nonincreasing profile `μ` vanishing
at infinity — for a Schwartz function on `A_S`, `r(x) = Sup_v |x_v|` and `μ` any of its decay
profiles — then

  `λ_n := μ(n) − μ(n+1)`

works, because the boxes are nested: at a given `x` the surviving terms are exactly those with
`n + 1 ≥ r(x)`, and they telescope to `μ(⌈r(x)⌉ − 1) ≥ μ(r(x))`.  The `λ_n` inherit the decay of
`μ` since `λ_n ≤ μ(n)`.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- A nonincreasing function vanishing at infinity is nonnegative. -/
theorem connes_nonneg_of_antitone_tendsto {μ : ℝ → ℝ} (hanti : Antitone μ)
    (hlim : Tendsto μ atTop (𝓝 0)) (t : ℝ) : 0 ≤ μ t := by
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop t] with s hs
  exact hanti hs

/-- **§VII (9).**  A function dominated by a nonincreasing profile vanishing at infinity is
dominated by a superposition of nested box indicators whose coefficients inherit the decay of the
profile. -/
theorem connes_box_majorant {X : Type*} {r : X → ℝ} (hr : ∀ x, 0 ≤ r x)
    {f : X → ℝ} {μ : ℝ → ℝ} (hanti : Antitone μ) (hlim : Tendsto μ atTop (𝓝 0))
    (hf : ∀ x, |f x| ≤ μ (r x)) :
    ∃ lam : ℕ → ℝ, (∀ n, 0 ≤ lam n) ∧ (∀ n, lam n ≤ μ n) ∧ Summable lam ∧
      ∀ x : X, |f x| ≤ ∑' n : ℕ, lam n * (if r x ≤ (n : ℝ) + 1 then 1 else 0) := by
  have hμnn : ∀ t : ℝ, 0 ≤ μ t := connes_nonneg_of_antitone_tendsto hanti hlim
  set lam : ℕ → ℝ := fun n => μ n - μ (n + 1) with hlamdef
  have hlamnn : ∀ n : ℕ, 0 ≤ lam n := by
    intro n
    have : μ ((n : ℝ) + 1) ≤ μ (n : ℝ) := hanti (by linarith)
    rw [hlamdef]
    push_cast
    linarith
  have hlamle : ∀ n : ℕ, lam n ≤ μ n := by
    intro n
    have := hμnn ((n : ℝ) + 1)
    rw [hlamdef]
    push_cast
    linarith
  have htel : ∀ K : ℕ, (∑ i ∈ Finset.range K, lam i) = μ 0 - μ K := by
    intro K
    have h := Finset.sum_range_sub' (fun i : ℕ => μ i) K
    simpa [hlamdef] using h
  have hsum : Summable lam := by
    refine summable_of_sum_range_le hlamnn (c := μ 0) fun K => ?_
    rw [htel K]
    have := hμnn ((K : ℝ))
    linarith
  refine ⟨lam, hlamnn, hlamle, hsum, fun x => ?_⟩
  set k : ℕ → ℝ := fun n => if r x ≤ (n : ℝ) + 1 then 1 else 0 with hkdef
  have hknn : ∀ n : ℕ, 0 ≤ lam n * k n := by
    intro n
    refine mul_nonneg (hlamnn n) ?_
    rw [hkdef]
    by_cases h : r x ≤ (n : ℝ) + 1 <;> simp [h]
  have hksum : Summable fun n : ℕ => lam n * k n := by
    refine hsum.of_nonneg_of_le hknn fun n => ?_
    rw [hkdef]
    by_cases h : r x ≤ (n : ℝ) + 1
    · simp [h]
    · simp [h, hlamnn n]
  set N : ℕ := ⌈r x⌉₊ with hN
  set M : ℕ := N - 1 with hM
  have hMle : (M : ℝ) ≤ r x := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · have hrx : r x ≤ 0 := by
        have := Nat.le_ceil (r x)
        rw [← hN, hN0] at this
        simpa using this
      have : r x = 0 := le_antisymm hrx (hr x)
      rw [hM, hN0]
      simp [this]
    · have hlt : (N : ℝ) < r x + 1 := by
        rw [hN]
        exact Nat.ceil_lt_add_one (hr x)
      have hMN : (M : ℝ) = (N : ℝ) - 1 := by
        rw [hM]
        have : (1 : ℕ) ≤ N := hNpos
        push_cast [Nat.cast_sub this]
        ring
      rw [hMN]
      linarith
  have hkone : ∀ n : ℕ, M ≤ n → k n = 1 := by
    intro n hn
    have hrN : r x ≤ (N : ℝ) := Nat.le_ceil (r x)
    have hstep : (N : ℝ) ≤ (n : ℝ) + 1 := by
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · rw [hN0]
        push_cast
        positivity
      · have hMN : M + 1 = N := by
          rw [hM]
          omega
        have : (M : ℝ) + 1 = (N : ℝ) := by
          rw [← hMN]
          push_cast
          ring
        have hnM : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
    rw [hkdef]
    simp only [if_pos (le_trans hrN hstep)]
  have hpartial : ∀ K : ℕ, M ≤ K → μ M - μ K ≤ ∑' n : ℕ, lam n * k n := by
    intro K hK
    have hsub : (∑ n ∈ Finset.Ico M K, lam n * k n) ≤ ∑' n : ℕ, lam n * k n :=
      Summable.sum_le_tsum (Finset.Ico M K) (fun n _ => hknn n) hksum
    have hval : (∑ n ∈ Finset.Ico M K, lam n * k n) = μ M - μ K := by
      have hcongr : (∑ n ∈ Finset.Ico M K, lam n * k n) = ∑ n ∈ Finset.Ico M K, lam n := by
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [hkone n (Finset.mem_Ico.mp hn).1, mul_one]
      rw [hcongr, Finset.sum_Ico_eq_sub _ hK, htel K, htel M]
      ring
    rw [hval] at hsub
    exact hsub
  have hlimK : Tendsto (fun K : ℕ => μ M - μ K) atTop (𝓝 (μ M)) := by
    have hcast : Tendsto (fun K : ℕ => ((K : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have := hlim.comp hcast
    simpa using tendsto_const_nhds.sub this
  have hMbound : μ M ≤ ∑' n : ℕ, lam n * k n := by
    refine le_of_tendsto hlimK ?_
    filter_upwards [eventually_ge_atTop M] with K hK
    exact hpartial K hK
  calc |f x| ≤ μ (r x) := hf x
    _ ≤ μ M := hanti hMle
    _ ≤ ∑' n : ℕ, lam n * k n := hMbound

end

end GaloisForLFunctions.RHTower
