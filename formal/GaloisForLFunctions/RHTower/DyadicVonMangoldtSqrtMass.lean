import GaloisForLFunctions.RHTower.ChebyshevPsiScaling

/-!
# The dyadic von Mangoldt mass weighted by the inverse square root

The prime mass of a dyadic block is `ψ(2X) − ψ(X)`, which the prime number theorem makes
asymptotic to `X`.  Weighting each prime power by `n^{-1/2}` costs at most the endpoint weight
`(2X)^{-1/2}`, so the weighted dyadic mass is eventually at least a fixed multiple of `√X`.

This is the arithmetic input of the mass-Bessel aperture: the coefficients of a dyadic aperture
are non-negative and their total mass grows like `√X`, so no cancellation can hide them.
-/

open Filter ArithmeticFunction
open scoped Topology BigOperators

namespace RHTower

/-- The dyadic von Mangoldt mass weighted by the inverse square root. -/
noncomputable def dyadicSqrtVonMangoldtMass (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, (vonMangoldt n : ℝ) / Real.sqrt n

theorem sum_range_succ_sub {a b : ℕ} (hab : a ≤ b) (f : ℕ → ℝ) :
    ∑ n ∈ Finset.range (b + 1), f n - ∑ n ∈ Finset.range (a + 1), f n
      = ∑ n ∈ Finset.Ioc a b, f n := by
  have hsplit : ∑ n ∈ Finset.Ico 0 (a + 1), f n + ∑ n ∈ Finset.Ico (a + 1) (b + 1), f n
      = ∑ n ∈ Finset.Ico 0 (b + 1), f n :=
    Finset.sum_Ico_consecutive f (Nat.zero_le _) (by omega)
  rw [← Finset.range_eq_Ico, ← Finset.range_eq_Ico] at hsplit
  have hset : Finset.Ico (a + 1) (b + 1) = Finset.Ioc a b := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [hset] at hsplit
  linarith

/-- The dyadic prime mass is a difference of Chebyshev functions. -/
theorem chebyshevPsiReal_dyadic_sub {X : ℝ} (hX : 0 ≤ X) :
    chebyshevPsiReal (2 * X) - chebyshevPsiReal X
      = ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, (vonMangoldt n : ℝ) := by
  rw [chebyshevPsiReal_eq_sum_range, chebyshevPsiReal_eq_sum_range]
  refine sum_range_succ_sub ?_ _
  exact Nat.floor_le_floor (by linarith)

/-- Weighting by the inverse square root costs at most the endpoint weight. -/
theorem dyadicSqrtVonMangoldtMass_ge {X : ℝ} (hX : 1 ≤ X) :
    (chebyshevPsiReal (2 * X) - chebyshevPsiReal X) / Real.sqrt (2 * X)
      ≤ dyadicSqrtVonMangoldtMass X := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have h2X : (0 : ℝ) < 2 * X := by linarith
  have hsqrt : (0 : ℝ) < Real.sqrt (2 * X) := Real.sqrt_pos.2 h2X
  rw [chebyshevPsiReal_dyadic_sub hX0.le, dyadicSqrtVonMangoldtMass, Finset.sum_div]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have hn1 : 1 ≤ n := by
    have : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
    omega
  have hnle : (n : ℝ) ≤ 2 * X := by
    have := Nat.floor_le h2X.le
    have hcast : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hn.2
    linarith
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hsq : Real.sqrt n ≤ Real.sqrt (2 * X) := Real.sqrt_le_sqrt hnle
  have hsqpos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hnpos
  exact div_le_div_of_nonneg_left vonMangoldt_nonneg hsqpos hsq

/-- The dyadic prime mass is asymptotic to `X`. -/
theorem tendsto_chebyshevPsiReal_dyadic_sub :
    Tendsto (fun X : ℝ => (chebyshevPsiReal (2 * X) - chebyshevPsiReal X) / X) atTop (𝓝 1) := by
  have h2 := tendsto_chebyshevPsiReal_scaled (c := 2) (by norm_num)
  have h1 := tendsto_chebyshevPsiReal_scaled (c := 1) (by norm_num)
  have hsub := h2.sub h1
  norm_num at hsub
  refine hsub.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  rw [sub_div]

/-- **The dyadic weighted prime mass grows like `√X`.** -/
theorem eventually_dyadicSqrtVonMangoldtMass_ge :
    ∀ᶠ X : ℝ in atTop, Real.sqrt X / 3 ≤ dyadicSqrtVonMangoldtMass X := by
  have hpsi := tendsto_chebyshevPsiReal_dyadic_sub
  have hev : ∀ᶠ X : ℝ in atTop,
      (1 : ℝ) / 2 < (chebyshevPsiReal (2 * X) - chebyshevPsiReal X) / X := by
    have := hpsi.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) / 2 < 1))
    exact this
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with X hX1 hX
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le zero_lt_one hX
  have hmass : X / 2 ≤ chebyshevPsiReal (2 * X) - chebyshevPsiReal X := by
    rw [lt_div_iff₀ hX0] at hX1
    linarith
  have hsqrtX : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 hX0
  have hsq2 : Real.sqrt (2 * X) = Real.sqrt 2 * Real.sqrt X := Real.sqrt_mul (by norm_num) X
  have hsqrt2 : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 : ℝ) / 2 = Real.sqrt ((3 / 2) ^ 2) from by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsqrtpos : (0 : ℝ) < Real.sqrt (2 * X) := by
    rw [hsq2]
    positivity
  refine le_trans ?_ (dyadicSqrtVonMangoldtMass_ge hX)
  rw [le_div_iff₀ hsqrtpos, hsq2]
  have hprod : Real.sqrt X / 3 * (Real.sqrt 2 * Real.sqrt X) ≤ X / 2 := by
    have hXsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
    nlinarith [hsqrt2, hsqrtX, hXsq]
  linarith

end RHTower
