import GaloisForLFunctions.RHTower.Sieve.ScheduleMonomialLimits
import GaloisForLFunctions.RHTower.Sieve.TwoRangeAggregates

/-!
# The groups of the two-range budget, at the schedule

Each group of `Sieve/MoebiusTwoRangeWindow.integral_Icc_normSq_logPoly_moebius_le_twoRange` has
been reduced to a closed form in the aggregates `L`, `θ` (or `ρ`), `W`, `Bmax`, `S`, `#P` by
`Sieve/LadderAggregates`, `Sieve/LargeLadderGroup`, `Sieve/LadderAffineBounds` and
`Sieve/MoebiusHeadBudget`.  Substituting the schedule turns each closed form into a finite sum of
monomials `(log x)^e·(log log x)^k·f`, and `Sieve/ScheduleMonomialLimits` kills every one of them.

The aggregates enter only through their schedule majorants, so the limits below are stated for
arbitrary functions obeying those majorants; the majorants themselves are the content of
`Sieve/TwoRangeScheduleFacts` and `Sieve/TwoRangeAggregates`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- A monomial vanishes against the length of the Dirichlet polynomial. -/
theorem tendsto_logMonomial_div_twoRangeLength {β : ℝ} (hβ : 0 < β) (e : ℝ) (k : ℕ) :
    Tendsto (fun x : ℝ =>
      (Real.log x) ^ e * (Real.log (Real.log x)) ^ k / ((twoRangeLength β x : ℕ) : ℝ))
      atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_logMonomial_div_sqrt e k)
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxe
    exact div_nonneg (logMonomial_nonneg k hxe) (Nat.cast_nonneg _)
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1), sqrt_le_twoRangeLength hβ,
      Filter.eventually_ge_atTop (16 : ℝ)] with x hxe hM hx16
    have hsq : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    exact div_le_div_of_nonneg_left (logMonomial_nonneg k hxe) hsq hM

/-- A monomial vanishes against the window length over the length of the Dirichlet polynomial. -/
theorem tendsto_logMonomial_mul_cardLength_div_twoRangeLength {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (e : ℝ) (k : ℕ) :
    Tendsto (fun x : ℝ =>
      (Real.log x) ^ e * (Real.log (Real.log x)) ^ k
        * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_logMonomial_mul_cardLength_div_sqrt hβ0 hβ1 e k)
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hxe
    exact mul_nonneg (logMonomial_nonneg k hxe)
      (div_nonneg (cardLength_pos β x).le (Nat.cast_nonneg _))
  · filter_upwards [Filter.eventually_ge_atTop (Real.exp 1), sqrt_le_twoRangeLength hβ0,
      Filter.eventually_ge_atTop (16 : ℝ)] with x hxe hM hx16
    have hsq : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
    refine mul_le_mul_of_nonneg_left ?_ (logMonomial_nonneg k hxe)
    exact div_le_div_of_nonneg_left (cardLength_pos β x).le hsq hM

/-- The Gallagher window in the length of the Dirichlet polynomial. -/
theorem twoRangeTop_eq (β x : ℝ) :
    twoRangeTop β x
      = ((twoRangeLength β x : ℕ) : ℝ) / cardLength β x * Real.log (Real.log x) := rfl

theorem lowTheta_sq {A x : ℝ} (hx : 1 ≤ x) : lowTheta A x ^ 2 = (Real.log x) ^ (-(2 * A)) := by
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  rw [lowTheta, ← Real.rpow_natCast ((Real.log x) ^ (-A)) 2, ← Real.rpow_mul hlog]
  congr 1
  push_cast
  ring

/-- **The small half's ladder group vanishes relative to `M²`.**  Every summand is a monomial of
the schedule; the binding constraint is `2A > β + c`, and the window enters only through
`W/M = log log x / h`. -/
theorem tendsto_smallLadderGroup_div_sq {β c A : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hc : 0 < c)
    (h2A : β + c < 2 * A)
    {Lf Bf Sf Pf : ℝ → ℝ}
    (hLf : ∀ᶠ x : ℝ in atTop, 0 ≤ Lf x ∧ Lf x ≤ 2 * (Real.log x) ^ (β + c))
    (hBf : ∀ᶠ x : ℝ in atTop, 0 ≤ Bf x ∧ Bf x ≤ cardLength β x * (Real.log x) ^ (-c) + 1)
    (hSf : ∀ᶠ x : ℝ in atTop, 0 ≤ Sf x
        ∧ Sf x ≤ 2 * ((twoRangeLength β x : ℕ) : ℝ) * Real.log (Real.log x))
    (hPf : ∀ᶠ x : ℝ in atTop, 0 ≤ Pf x ∧ Pf x ≤ cardLength β x) :
    Tendsto (fun x : ℝ =>
      (5 * Real.pi * Lf x * lowTheta A x ^ 2 * twoRangeTop β x * (Bf x * Sf x + Bf x * Pf x)
        + 5 * Real.exp 1 * Lf x * lowTheta A x ^ 2 * (Sf x ^ 2 + Bf x * Sf x))
      / ((twoRangeLength β x : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  have t1 : Tendsto (fun x : ℝ => 20 * Real.pi
      * ((Real.log x) ^ (β - 2 * A) * (Real.log (Real.log x)) ^ 2)) atTop (𝓝 0) := by
    simpa using (tendsto_logMonomial (e := β - 2 * A) (by linarith) 2).const_mul (20 * Real.pi)
  have t2 : Tendsto (fun x : ℝ => 20 * Real.pi
      * ((Real.log x) ^ (β + c - 2 * A) * (Real.log (Real.log x)) ^ 2 / cardLength β x))
      atTop (𝓝 0) := by
    simpa using (tendsto_logMonomial_div_cardLength (β := β) hβ0 (β + c - 2 * A) 2).const_mul
      (20 * Real.pi)
  have t3 : Tendsto (fun x : ℝ => 10 * Real.pi
      * ((Real.log x) ^ (β - 2 * A) * (Real.log (Real.log x)) ^ 1
        * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ)))) atTop (𝓝 0) := by
    simpa using (tendsto_logMonomial_mul_cardLength_div_twoRangeLength (β := β) hβ0 hβ1
      (β - 2 * A) 1).const_mul (10 * Real.pi)
  have t4 : Tendsto (fun x : ℝ => 10 * Real.pi
      * ((Real.log x) ^ (β + c - 2 * A) * (Real.log (Real.log x)) ^ 1
        / ((twoRangeLength β x : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_logMonomial_div_twoRangeLength (β := β) hβ0 (β + c - 2 * A) 1).const_mul
      (10 * Real.pi)
  have t5 : Tendsto (fun x : ℝ => 40 * Real.exp 1
      * ((Real.log x) ^ (β + c - 2 * A) * (Real.log (Real.log x)) ^ 2)) atTop (𝓝 0) := by
    simpa using (tendsto_logMonomial (e := β + c - 2 * A) (by linarith) 2).const_mul
      (40 * Real.exp 1)
  have t6 : Tendsto (fun x : ℝ => 20 * Real.exp 1
      * ((Real.log x) ^ (β - 2 * A) * (Real.log (Real.log x)) ^ 1
        * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ)))) atTop (𝓝 0) := by
    simpa using (tendsto_logMonomial_mul_cardLength_div_twoRangeLength (β := β) hβ0 hβ1
      (β - 2 * A) 1).const_mul (20 * Real.exp 1)
  have t7 : Tendsto (fun x : ℝ => 20 * Real.exp 1
      * ((Real.log x) ^ (β + c - 2 * A) * (Real.log (Real.log x)) ^ 1
        / ((twoRangeLength β x : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_logMonomial_div_twoRangeLength (β := β) hβ0 (β + c - 2 * A) 1).const_mul
      (20 * Real.exp 1)
  have hlim := ((((((t1.add t2).add t3).add t4).add t5).add t6).add t7)
  rw [show ((0 : ℝ) + 0 + 0 + 0 + 0 + 0 + 0) = 0 by ring] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hLf, hBf, hSf, hPf, Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ)] with x hL hB hS hP hx1 hlog1
    have hu0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
    have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
    have hM0 : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ) := Nat.cast_nonneg _
    have hW0 : (0 : ℝ) ≤ twoRangeTop β x := by
      rw [twoRangeTop_eq]
      positivity
    have hθ0 : (0 : ℝ) ≤ lowTheta A x ^ 2 := sq_nonneg _
    have hnum : (0 : ℝ) ≤ 5 * Real.pi * Lf x * lowTheta A x ^ 2 * twoRangeTop β x
          * (Bf x * Sf x + Bf x * Pf x)
        + 5 * Real.exp 1 * Lf x * lowTheta A x ^ 2 * (Sf x ^ 2 + Bf x * Sf x) := by
      have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
      have h1 : (0 : ℝ) ≤ Bf x * Sf x + Bf x * Pf x :=
        add_nonneg (mul_nonneg hB.1 hS.1) (mul_nonneg hB.1 hP.1)
      have h2 : (0 : ℝ) ≤ Sf x ^ 2 + Bf x * Sf x :=
        add_nonneg (sq_nonneg _) (mul_nonneg hB.1 hS.1)
      have hA : (0 : ℝ) ≤ 5 * Real.pi * Lf x * lowTheta A x ^ 2 * twoRangeTop β x
          * (Bf x * Sf x + Bf x * Pf x) := by
        have : (0 : ℝ) ≤ 5 * Real.pi * Lf x * lowTheta A x ^ 2 * twoRangeTop β x := by
          have := hL.1
          positivity
        exact mul_nonneg this h1
      have hBb : (0 : ℝ) ≤ 5 * Real.exp 1 * Lf x * lowTheta A x ^ 2 * (Sf x ^ 2 + Bf x * Sf x) := by
        have : (0 : ℝ) ≤ 5 * Real.exp 1 * Lf x * lowTheta A x ^ 2 := by
          have := hL.1
          positivity
        exact mul_nonneg this h2
      linarith
    positivity
  · filter_upwards [hLf, hBf, hSf, hPf, Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ), one_le_twoRangeLength hβ0]
      with x hL hB hS hP hx1 hlog1 hM1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hu0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
    have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
    have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
    have hcneg : (0 : ℝ) ≤ (Real.log x) ^ (-c) := Real.rpow_nonneg hlogx.le _
    have hAneg : (0 : ℝ) ≤ (Real.log x) ^ (-(2 * A)) := Real.rpow_nonneg hlogx.le _
    have hbc : (0 : ℝ) ≤ (Real.log x) ^ (β + c) := Real.rpow_nonneg hlogx.le _
    have e1 : (Real.log x) ^ (β + c - 2 * A)
        = (Real.log x) ^ (β + c) * (Real.log x) ^ (-(2 * A)) := by
      rw [show β + c - 2 * A = (β + c) + -(2 * A) by ring, Real.rpow_add hlogx]
    have e2 : (Real.log x) ^ (β - 2 * A)
        = (Real.log x) ^ (β + c) * (Real.log x) ^ (-(2 * A)) * (Real.log x) ^ (-c) := by
      rw [show β - 2 * A = (β + c) + -(2 * A) + -c by ring, Real.rpow_add hlogx,
        Real.rpow_add hlogx]
    have hbar : 5 * Real.pi * (2 * (Real.log x) ^ (β + c)) * (Real.log x) ^ (-(2 * A))
            * (((twoRangeLength β x : ℕ) : ℝ) / cardLength β x * Real.log (Real.log x))
            * ((cardLength β x * (Real.log x) ^ (-c) + 1)
                  * (2 * ((twoRangeLength β x : ℕ) : ℝ) * Real.log (Real.log x))
                + (cardLength β x * (Real.log x) ^ (-c) + 1) * cardLength β x)
          + 5 * Real.exp 1 * (2 * (Real.log x) ^ (β + c)) * (Real.log x) ^ (-(2 * A))
            * ((2 * ((twoRangeLength β x : ℕ) : ℝ) * Real.log (Real.log x)) ^ 2
                + (cardLength β x * (Real.log x) ^ (-c) + 1)
                  * (2 * ((twoRangeLength β x : ℕ) : ℝ) * Real.log (Real.log x)))
        = (20 * Real.pi * ((Real.log x) ^ (β - 2 * A) * (Real.log (Real.log x)) ^ 2)
            + 20 * Real.pi * ((Real.log x) ^ (β + c - 2 * A) * (Real.log (Real.log x)) ^ 2
                / cardLength β x)
            + 10 * Real.pi * ((Real.log x) ^ (β - 2 * A) * (Real.log (Real.log x)) ^ 1
                * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ)))
            + 10 * Real.pi * ((Real.log x) ^ (β + c - 2 * A) * (Real.log (Real.log x)) ^ 1
                / ((twoRangeLength β x : ℕ) : ℝ))
            + 40 * Real.exp 1 * ((Real.log x) ^ (β + c - 2 * A) * (Real.log (Real.log x)) ^ 2)
            + 20 * Real.exp 1 * ((Real.log x) ^ (β - 2 * A) * (Real.log (Real.log x)) ^ 1
                * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ)))
            + 20 * Real.exp 1 * ((Real.log x) ^ (β + c - 2 * A) * (Real.log (Real.log x)) ^ 1
                / ((twoRangeLength β x : ℕ) : ℝ)))
          * ((twoRangeLength β x : ℕ) : ℝ) ^ 2 := by
      rw [e1, e2]
      field_simp
      ring
    rw [div_le_iff₀ (by positivity), lowTheta_sq hx1.le, twoRangeTop_eq]
    refine le_trans ?_ (le_of_eq hbar)
    gcongr <;>
      first
        | exact hL.1 | exact hL.2 | exact hB.1 | exact hB.2 | exact hS.1 | exact hS.2
        | exact hP.1 | exact hP.2
        | positivity
        | (exact mul_nonneg hB.1 hS.1)
        | (exact add_nonneg (mul_nonneg hB.1 hS.1) (mul_nonneg hB.1 hP.1))
        | (exact add_nonneg (sq_nonneg _) (mul_nonneg hB.1 hS.1))

/-- The reciprocal of `log log` vanishes. -/
theorem tendsto_inv_logLog :
    Tendsto (fun x : ℝ => 1 / Real.log (Real.log x)) atTop (𝓝 0) := by
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  exact Filter.Tendsto.congr (fun x => (one_div _).symm) hll.inv_tendsto_atTop

/-- **A ladder's discrepancy group vanishes relative to `M²`.**  The same statement serves both
designated ranges: the range enters only through the exponent `ℓ` of its step count, the exponent
`c` of its step ratio, the exponent `K` of its bottom and the exponent `γ` of its top.  The binding
constraints are `1 + ℓ < 2c` (the ladder's own defect) and `1 + c < 2K` (its bottom). -/
theorem tendsto_defectGroup_div_sq {β γ ℓ c K : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hℓ : 1 + ℓ < 2 * c) (hK1 : 1 < K) (hK2 : 1 + c < 2 * K)
    {Cf Rf Lf Qf HRf : ℝ → ℝ}
    (hCf : ∀ᶠ x : ℝ in atTop, 0 ≤ Cf x ∧ Cf x ≤ 22 * ((twoRangeLength β x : ℕ) : ℝ))
    (hRf : ∀ᶠ x : ℝ in atTop, 0 ≤ Rf x ∧ Rf x ≤ Real.log x)
    (hLf : ∀ᶠ x : ℝ in atTop, 0 ≤ Lf x ∧ Lf x ≤ 2 * (Real.log x) ^ ℓ)
    (hQf : ∀ᶠ x : ℝ in atTop, (Real.log x) ^ K ≤ Qf x)
    (hHRf : ∀ᶠ x : ℝ in atTop, 0 ≤ HRf x ∧ HRf x ≤ 2 * cardLength γ x) :
    Tendsto (fun x : ℝ =>
      Cf x * (Rf x * (Lf x * ((1 + ((twoRangeLength β x : ℕ) : ℝ))
              * ((Real.log x) ^ (-c)) ^ 2 + 5)
          + 5 * HRf x
          + ((Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
              + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c))
            * (2 / (Qf x * (Real.log x) ^ (-c)))
          + ((twoRangeLength β x : ℕ) : ℝ) * (2 / (Qf x ^ 2 * (Real.log x) ^ (-c)))))
        / ((twoRangeLength β x : ℕ) : ℝ) ^ 2) atTop (𝓝 0) := by
  have t1 : Tendsto (fun x : ℝ => 88 * (Real.log x) ^ (1 + ℓ - 2 * c)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_log_of_neg (c := 1 + ℓ - 2 * c) (by linarith)).const_mul 88
  have t2 : Tendsto (fun x : ℝ =>
      220 * ((Real.log x) ^ (1 + ℓ) / ((twoRangeLength β x : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa using (tendsto_logMonomial_div_twoRangeLength (β := β) hβ0 (1 + ℓ) 0).const_mul 220
  have t3 : Tendsto (fun x : ℝ =>
      220 * ((Real.log x) ^ (1 : ℝ)
        * (cardLength γ x / ((twoRangeLength β x : ℕ) : ℝ)))) atTop (𝓝 0) := by
    have h := (tendsto_logMonomial_mul_cardLength_div_sqrt (β := γ) hγ0 hγ1 (1 : ℝ) 0)
    have hsq : Tendsto (fun x : ℝ =>
        220 * ((Real.log x) ^ (1 : ℝ) * (cardLength γ x / Real.sqrt x))) atTop (𝓝 0) := by
      simpa using h.const_mul 220
    refine squeeze_zero' ?_ ?_ hsq
    · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
      have h1 : (0 : ℝ) ≤ (Real.log x) ^ (1 : ℝ) := Real.rpow_nonneg hlogx.le _
      have h2 : (0 : ℝ) ≤ cardLength γ x / ((twoRangeLength β x : ℕ) : ℝ) :=
        div_nonneg (cardLength_pos γ x).le (Nat.cast_nonneg _)
      positivity
    · filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), sqrt_le_twoRangeLength hβ0,
        Filter.eventually_ge_atTop (16 : ℝ)] with x hx1 hM hx16
      have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
      have h1 : (0 : ℝ) ≤ (Real.log x) ^ (1 : ℝ) := Real.rpow_nonneg hlogx.le _
      have hs : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ h1) (by norm_num)
      exact div_le_div_of_nonneg_left (cardLength_pos γ x).le hs hM
  have t4 : Tendsto (fun x : ℝ => 132 * (Real.log x) ^ (1 - K)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_log_of_neg (c := 1 - K) (by linarith)).const_mul 132
  have t5 : Tendsto (fun x : ℝ => 44 * (Real.log x) ^ (1 + c - 2 * K)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_log_of_neg (c := 1 + c - 2 * K) (by linarith)).const_mul 44
  have hlim := ((((t1.add t2).add t3).add t4).add t5)
  rw [show ((0 : ℝ) + 0 + 0 + 0 + 0) = 0 by ring] at hlim
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [hCf, hRf, hLf, hQf, hHRf, Filter.eventually_gt_atTop (1 : ℝ),
      one_le_twoRangeLength hβ0] with x hC hR hL hQ hHR hx1 hM1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hη : (0 : ℝ) < (Real.log x) ^ (-c) := Real.rpow_pos_of_pos hlogx _
    have hQ0 : (0 : ℝ) < Qf x :=
      lt_of_lt_of_le (Real.rpow_pos_of_pos hlogx K) hQ
    have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
    have hin : (0 : ℝ) ≤ Lf x * ((1 + ((twoRangeLength β x : ℕ) : ℝ))
            * ((Real.log x) ^ (-c)) ^ 2 + 5)
        + 5 * HRf x
        + ((Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
            + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c))
          * (2 / (Qf x * (Real.log x) ^ (-c)))
        + ((twoRangeLength β x : ℕ) : ℝ) * (2 / (Qf x ^ 2 * (Real.log x) ^ (-c))) := by
      have h1 : (0 : ℝ) ≤ Lf x * ((1 + ((twoRangeLength β x : ℕ) : ℝ))
          * ((Real.log x) ^ (-c)) ^ 2 + 5) := by
        have := hL.1
        positivity
      have h2 : (0 : ℝ) ≤ 5 * HRf x := by linarith [hHR.1]
      have h3 : (0 : ℝ) ≤ ((Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
            + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c))
          * (2 / (Qf x * (Real.log x) ^ (-c))) := by positivity
      have h4 : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ)
          * (2 / (Qf x ^ 2 * (Real.log x) ^ (-c))) := by positivity
      linarith
    have hRin : (0 : ℝ) ≤ Rf x * _ := mul_nonneg hR.1 hin
    have : (0 : ℝ) ≤ Cf x * (Rf x * _) := mul_nonneg hC.1 hRin
    positivity
  · filter_upwards [hCf, hRf, hLf, hQf, hHRf, Filter.eventually_gt_atTop (1 : ℝ),
      one_le_twoRangeLength hβ0] with x hC hR hL hQ hHR hx1 hM1
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hη : (0 : ℝ) < (Real.log x) ^ (-c) := Real.rpow_pos_of_pos hlogx _
    have hQK : (0 : ℝ) < (Real.log x) ^ K := Real.rpow_pos_of_pos hlogx K
    have hQ0 : (0 : ℝ) < Qf x := lt_of_lt_of_le hQK hQ
    have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
    have hγ0' : (0 : ℝ) < cardLength γ x := cardLength_pos γ x
    -- the four inner terms
    have hsq : ((Real.log x) ^ (-c)) ^ 2 = (Real.log x) ^ (-(2 * c)) := by
      rw [← Real.rpow_natCast ((Real.log x) ^ (-c)) 2, ← Real.rpow_mul hlogx.le,
        show -c * ((2 : ℕ) : ℝ) = -(2 * c) by push_cast; ring]
    have hi1 : Lf x * ((1 + ((twoRangeLength β x : ℕ) : ℝ))
            * ((Real.log x) ^ (-c)) ^ 2 + 5)
        ≤ 4 * ((twoRangeLength β x : ℕ) : ℝ) * (Real.log x) ^ (ℓ - 2 * c)
          + 10 * (Real.log x) ^ ℓ := by
      have hlpow : (0 : ℝ) < (Real.log x) ^ ℓ := Real.rpow_pos_of_pos hlogx ℓ
      have hprod : (Real.log x) ^ ℓ * (Real.log x) ^ (-(2 * c)) = (Real.log x) ^ (ℓ - 2 * c) := by
        rw [show ℓ - 2 * c = ℓ + -(2 * c) by ring, Real.rpow_add hlogx]
      have hbase : (1 + ((twoRangeLength β x : ℕ) : ℝ)) * ((Real.log x) ^ (-c)) ^ 2 + 5
          ≤ 2 * ((twoRangeLength β x : ℕ) : ℝ) * (Real.log x) ^ (-(2 * c)) + 5 := by
        rw [hsq]
        have h2c : (0 : ℝ) < (Real.log x) ^ (-(2 * c)) := Real.rpow_pos_of_pos hlogx _
        nlinarith [hM1, h2c]
      have hb0 : (0 : ℝ) ≤ 2 * ((twoRangeLength β x : ℕ) : ℝ) * (Real.log x) ^ (-(2 * c)) + 5 := by
        have h2c : (0 : ℝ) < (Real.log x) ^ (-(2 * c)) := Real.rpow_pos_of_pos hlogx _
        positivity
      refine le_trans (mul_le_mul hL.2 hbase ?_ (by positivity)) (le_of_eq ?_)
      · rw [hsq]
        have h2c : (0 : ℝ) < (Real.log x) ^ (-(2 * c)) := Real.rpow_pos_of_pos hlogx _
        nlinarith [hM1, h2c]
      · rw [← hprod]
        ring
    have hi2 : 5 * HRf x ≤ 10 * cardLength γ x := by linarith [hHR.2]
    have hQη : (Real.log x) ^ (K - c) ≤ Qf x * (Real.log x) ^ (-c) := by
      have hid : (Real.log x) ^ (K - c) = (Real.log x) ^ K * (Real.log x) ^ (-c) := by
        rw [show K - c = K + -c by ring, Real.rpow_add hlogx]
      rw [hid]
      exact mul_le_mul_of_nonneg_right hQ hη.le
    have hdiv1 : 2 / (Qf x * (Real.log x) ^ (-c)) ≤ 2 * (Real.log x) ^ (c - K) := by
      have hpos : (0 : ℝ) < (Real.log x) ^ (K - c) := Real.rpow_pos_of_pos hlogx _
      have hstep : 2 / (Qf x * (Real.log x) ^ (-c)) ≤ 2 / (Real.log x) ^ (K - c) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hQη
      refine hstep.trans (le_of_eq ?_)
      rw [show c - K = -(K - c) by ring, Real.rpow_neg hlogx.le]
      field_simp
    have hQ2η : (Real.log x) ^ (2 * K - c) ≤ Qf x ^ 2 * (Real.log x) ^ (-c) := by
      have hid : (Real.log x) ^ (2 * K - c)
          = ((Real.log x) ^ K) ^ 2 * (Real.log x) ^ (-c) := by
        rw [← Real.rpow_natCast ((Real.log x) ^ K) 2, ← Real.rpow_mul hlogx.le,
          ← Real.rpow_add hlogx,
          show K * ((2 : ℕ) : ℝ) + -c = 2 * K - c by push_cast; ring]
      rw [hid]
      have hsq2 : ((Real.log x) ^ K) ^ 2 ≤ Qf x ^ 2 := by nlinarith [hQK, hQ]
      exact mul_le_mul_of_nonneg_right hsq2 hη.le
    have hdiv2 : 2 / (Qf x ^ 2 * (Real.log x) ^ (-c)) ≤ 2 * (Real.log x) ^ (c - 2 * K) := by
      have hpos : (0 : ℝ) < (Real.log x) ^ (2 * K - c) := Real.rpow_pos_of_pos hlogx _
      have hstep : 2 / (Qf x ^ 2 * (Real.log x) ^ (-c)) ≤ 2 / (Real.log x) ^ (2 * K - c) :=
        div_le_div_of_nonneg_left (by norm_num) hpos hQ2η
      refine hstep.trans (le_of_eq ?_)
      rw [show c - 2 * K = -(2 * K - c) by ring, Real.rpow_neg hlogx.le]
      field_simp
    have hi3 : ((Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
            + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c))
          * (2 / (Qf x * (Real.log x) ^ (-c)))
        ≤ 6 * ((twoRangeLength β x : ℕ) : ℝ) * (Real.log x) ^ (-K) := by
      have hfac : (Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
          + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c)
          ≤ 3 * ((twoRangeLength β x : ℕ) : ℝ) * (Real.log x) ^ (-c) := by
        nlinarith [hM1, hη]
      have hfac0 : (0 : ℝ) ≤ (Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
          + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c) := by positivity
      have hprod : (Real.log x) ^ (-c) * (Real.log x) ^ (c - K) = (Real.log x) ^ (-K) := by
        rw [← Real.rpow_add hlogx, show -c + (c - K) = -K by ring]
      refine le_trans (mul_le_mul hfac hdiv1 (by positivity) (by positivity)) (le_of_eq ?_)
      rw [← hprod]
      ring
    have hi4 : ((twoRangeLength β x : ℕ) : ℝ) * (2 / (Qf x ^ 2 * (Real.log x) ^ (-c)))
        ≤ 2 * ((twoRangeLength β x : ℕ) : ℝ) * (Real.log x) ^ (c - 2 * K) := by
      have := mul_le_mul_of_nonneg_left hdiv2 hM0.le
      linarith [this]
    -- assemble
    set Ibar : ℝ := 4 * ((twoRangeLength β x : ℕ) : ℝ) * (Real.log x) ^ (ℓ - 2 * c)
        + 10 * (Real.log x) ^ ℓ + 10 * cardLength γ x
        + 6 * ((twoRangeLength β x : ℕ) : ℝ) * (Real.log x) ^ (-K)
        + 2 * ((twoRangeLength β x : ℕ) : ℝ) * (Real.log x) ^ (c - 2 * K) with hIdef
    have hinner : Lf x * ((1 + ((twoRangeLength β x : ℕ) : ℝ))
            * ((Real.log x) ^ (-c)) ^ 2 + 5)
        + 5 * HRf x
        + ((Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
            + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c))
          * (2 / (Qf x * (Real.log x) ^ (-c)))
        + ((twoRangeLength β x : ℕ) : ℝ) * (2 / (Qf x ^ 2 * (Real.log x) ^ (-c)))
        ≤ Ibar := by
      rw [hIdef]
      linarith [hi1, hi2, hi3, hi4]
    have hinner0 : (0 : ℝ) ≤ Lf x * ((1 + ((twoRangeLength β x : ℕ) : ℝ))
            * ((Real.log x) ^ (-c)) ^ 2 + 5)
        + 5 * HRf x
        + ((Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
            + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c))
          * (2 / (Qf x * (Real.log x) ^ (-c)))
        + ((twoRangeLength β x : ℕ) : ℝ) * (2 / (Qf x ^ 2 * (Real.log x) ^ (-c))) := by
      have h1 : (0 : ℝ) ≤ Lf x * ((1 + ((twoRangeLength β x : ℕ) : ℝ))
          * ((Real.log x) ^ (-c)) ^ 2 + 5) := by
        have := hL.1
        positivity
      have h2 : (0 : ℝ) ≤ 5 * HRf x := by linarith [hHR.1]
      have h3 : (0 : ℝ) ≤ ((Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
            + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c))
          * (2 / (Qf x * (Real.log x) ^ (-c))) := by positivity
      have h4 : (0 : ℝ) ≤ ((twoRangeLength β x : ℕ) : ℝ)
          * (2 / (Qf x ^ 2 * (Real.log x) ^ (-c))) := by positivity
      linarith
    have hIbar0 : (0 : ℝ) ≤ Ibar := le_trans hinner0 hinner
    have hprod : Cf x * (Rf x * (Lf x * ((1 + ((twoRangeLength β x : ℕ) : ℝ))
              * ((Real.log x) ^ (-c)) ^ 2 + 5)
          + 5 * HRf x
          + ((Real.log x) ^ (-c) * ((twoRangeLength β x : ℕ) : ℝ)
              + (1 + ((twoRangeLength β x : ℕ) : ℝ)) * (Real.log x) ^ (-c))
            * (2 / (Qf x * (Real.log x) ^ (-c)))
          + ((twoRangeLength β x : ℕ) : ℝ) * (2 / (Qf x ^ 2 * (Real.log x) ^ (-c)))))
        ≤ 22 * ((twoRangeLength β x : ℕ) : ℝ) * (Real.log x * Ibar) := by
      have hb : Rf x * (_) ≤ Real.log x * Ibar :=
        mul_le_mul hR.2 hinner hinner0 hlogx.le
      have := mul_le_mul hC.2 hb (mul_nonneg hR.1 hinner0) (by positivity)
      linarith [this]
    have f1 : (Real.log x) ^ (1 + ℓ - 2 * c) = Real.log x * (Real.log x) ^ (ℓ - 2 * c) := by
      rw [show 1 + ℓ - 2 * c = 1 + (ℓ - 2 * c) by ring, Real.rpow_add hlogx, Real.rpow_one]
    have f2 : (Real.log x) ^ (1 + ℓ) = Real.log x * (Real.log x) ^ ℓ := by
      rw [show 1 + ℓ = 1 + ℓ by ring, Real.rpow_add hlogx, Real.rpow_one]
    have f3 : (Real.log x) ^ (1 - K) = Real.log x * (Real.log x) ^ (-K) := by
      rw [show 1 - K = 1 + -K by ring, Real.rpow_add hlogx, Real.rpow_one]
    have f4 : (Real.log x) ^ (1 + c - 2 * K) = Real.log x * (Real.log x) ^ (c - 2 * K) := by
      rw [show 1 + c - 2 * K = 1 + (c - 2 * K) by ring, Real.rpow_add hlogx, Real.rpow_one]
    have heq : 22 * ((twoRangeLength β x : ℕ) : ℝ) * (Real.log x * Ibar)
        = (88 * (Real.log x) ^ (1 + ℓ - 2 * c)
          + 220 * ((Real.log x) ^ (1 + ℓ) / ((twoRangeLength β x : ℕ) : ℝ))
          + 220 * ((Real.log x) ^ (1 : ℝ)
              * (cardLength γ x / ((twoRangeLength β x : ℕ) : ℝ)))
          + 132 * (Real.log x) ^ (1 - K)
          + 44 * (Real.log x) ^ (1 + c - 2 * K))
          * ((twoRangeLength β x : ℕ) : ℝ) ^ 2 := by
      rw [f1, f2, f3, f4, Real.rpow_one, hIdef]
      field_simp
      ring
    rw [div_le_iff₀ (by positivity)]
    exact hprod.trans (le_of_eq heq)

/-- **A rough group vanishes relative to `M²`, even against the Cauchy–Schwarz weight.**  The
weight `1 + 1/δ = 1 + (log log x)^{1/2}` is beaten by the harmonic mass `≍ log log x` in the
denominator: that is what forces `δ` to be a root of `log log`. -/
theorem tendsto_roughGroup_div_sq {β cA : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hcA : 0 < cA)
    {Af Pf : ℝ → ℝ}
    (hAf : ∀ᶠ x : ℝ in atTop, cA * Real.log (Real.log x) ≤ Af x)
    (hPf : ∀ᶠ x : ℝ in atTop, 0 ≤ Pf x ∧ Pf x ≤ cardLength β x) :
    Tendsto (fun x : ℝ =>
      (1 + 1 / twoRangeDelta x)
        * (10 * twoRangeTop β x / (Af x * ((twoRangeLength β x : ℕ) : ℝ))
          + 20 * twoRangeTop β x * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
          + 7 / Af x
          + 14 * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ)))) atTop (𝓝 0) := by
  have t1 : Tendsto (fun x : ℝ => (10 / cA) * (1 / cardLength β x)) atTop (𝓝 0) := by
    have h := tendsto_logMonomial_div_cardLength (β := β) hβ0 0 0
    have h' : Tendsto (fun x : ℝ => 1 / cardLength β x) atTop (𝓝 0) := by
      refine h.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
      simp [Real.rpow_zero]
    simpa using h'.const_mul (10 / cA)
  have t2 : Tendsto (fun x : ℝ =>
      (10 / cA) * (Real.log (Real.log x) / cardLength β x)) atTop (𝓝 0) := by
    have h := tendsto_logMonomial_div_cardLength (β := β) hβ0 0 1
    have h' : Tendsto (fun x : ℝ => Real.log (Real.log x) / cardLength β x) atTop (𝓝 0) := by
      refine h.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
      simp [Real.rpow_zero]
    simpa using h'.const_mul (10 / cA)
  have t3 : Tendsto (fun x : ℝ =>
      (20 / cA) * (1 / ((twoRangeLength β x : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_logMonomial_div_twoRangeLength (β := β) hβ0 0 0
    have h' : Tendsto (fun x : ℝ => 1 / ((twoRangeLength β x : ℕ) : ℝ)) atTop (𝓝 0) := by
      refine h.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
      simp [Real.rpow_zero]
    simpa using h'.const_mul (20 / cA)
  have t4 : Tendsto (fun x : ℝ =>
      (20 / cA) * (Real.log (Real.log x) / ((twoRangeLength β x : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_logMonomial_div_twoRangeLength (β := β) hβ0 0 1
    have h' : Tendsto (fun x : ℝ =>
        Real.log (Real.log x) / ((twoRangeLength β x : ℕ) : ℝ)) atTop (𝓝 0) := by
      refine h.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
      simp [Real.rpow_zero]
    simpa using h'.const_mul (20 / cA)
  have t5 : Tendsto (fun x : ℝ =>
      (7 / cA) * (1 / Real.log (Real.log x))) atTop (𝓝 0) := by
    simpa using tendsto_inv_logLog.const_mul (7 / cA)
  have t6 : Tendsto (fun x : ℝ => (7 / cA) * twoRangeDelta x) atTop (𝓝 0) := by
    simpa using tendsto_twoRangeDelta.const_mul (7 / cA)
  have t7 : Tendsto (fun x : ℝ =>
      (28 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h := tendsto_logMonomial_mul_cardLength_div_twoRangeLength (β := β) hβ0 hβ1 0 0
    have h' : Tendsto (fun x : ℝ =>
        cardLength β x / ((twoRangeLength β x : ℕ) : ℝ)) atTop (𝓝 0) := by
      refine h.congr' ?_
      filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx1
      simp [Real.rpow_zero]
    simpa using h'.const_mul (28 / cA)
  have hlim := ((((((t1.add t2).add t3).add t4).add t5).add t6).add t7)
  rw [show ((0 : ℝ) + 0 + 0 + 0 + 0 + 0 + 0) = 0 by ring] at hlim
  have hbase : ∀ᶠ x : ℝ in atTop,
      0 ≤ (1 + 1 / twoRangeDelta x)
        * (10 * twoRangeTop β x / (Af x * ((twoRangeLength β x : ℕ) : ℝ))
          + 20 * twoRangeTop β x * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
          + 7 / Af x
          + 14 * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ))) := by
    filter_upwards [hAf, hPf, Filter.eventually_gt_atTop (1 : ℝ),
      Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1), one_le_twoRangeLength hβ0]
      with x hA hP hx1 hlogbig hM1
    have hu1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
      have := Real.log_le_log (Real.exp_pos 1) hlogbig
      rwa [Real.log_exp] at this
    have hA0 : (0 : ℝ) < Af x := lt_of_lt_of_le (by positivity) hA
    have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
    have hd0 : (0 : ℝ) < twoRangeDelta x := by
      rw [twoRangeDelta]
      exact Real.rpow_pos_of_pos (by linarith) _
    have hW0 : (0 : ℝ) ≤ twoRangeTop β x := by
      rw [twoRangeTop_eq]
      have := cardLength_pos β x
      positivity
    have h1 : (0 : ℝ) ≤ 10 * twoRangeTop β x / (Af x * ((twoRangeLength β x : ℕ) : ℝ)) := by
      positivity
    have h2 : (0 : ℝ) ≤ 20 * twoRangeTop β x * Pf x
        / (Af x * ((twoRangeLength β x : ℕ) : ℝ) ^ 2) := by
      have := hP.1
      positivity
    have h3 : (0 : ℝ) ≤ 7 / Af x := by positivity
    have h4 : (0 : ℝ) ≤ 14 * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ)) := by
      have := hP.1
      positivity
    have h5 : (0 : ℝ) ≤ 1 + 1 / twoRangeDelta x := by positivity
    have : (0 : ℝ) ≤ 10 * twoRangeTop β x / (Af x * ((twoRangeLength β x : ℕ) : ℝ))
        + 20 * twoRangeTop β x * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
        + 7 / Af x
        + 14 * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ)) := by linarith
    exact mul_nonneg h5 this
  refine squeeze_zero' hbase ?_ hlim
  filter_upwards [hAf, hPf, Filter.eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1), one_le_twoRangeLength hβ0]
    with x hA hP hx1 hlogbig hM1
  have hu1 : (1 : ℝ) ≤ Real.log (Real.log x) := by
    have := Real.log_le_log (Real.exp_pos 1) hlogbig
    rwa [Real.log_exp] at this
  have hu0 : (0 : ℝ) < Real.log (Real.log x) := by linarith
  have hA0 : (0 : ℝ) < Af x := lt_of_lt_of_le (by positivity) hA
  have hM0 : (0 : ℝ) < ((twoRangeLength β x : ℕ) : ℝ) := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hune : Real.log (Real.log x) ≠ 0 := ne_of_gt hu0
  have hMne : ((twoRangeLength β x : ℕ) : ℝ) ≠ 0 := ne_of_gt hM0
  have hhne : cardLength β x ≠ 0 := ne_of_gt hh0
  have hcAne : cA ≠ 0 := ne_of_gt hcA
  have hAne : Af x ≠ 0 := ne_of_gt hA0
  -- the four normalized terms
  have hW : twoRangeTop β x
      = ((twoRangeLength β x : ℕ) : ℝ) / cardLength β x * Real.log (Real.log x) := twoRangeTop_eq β x
  have k1 : 10 * twoRangeTop β x / (Af x * ((twoRangeLength β x : ℕ) : ℝ))
      ≤ 10 / (cA * cardLength β x) := by
    have ha : 10 * twoRangeTop β x / (Af x * ((twoRangeLength β x : ℕ) : ℝ))
        = 10 * Real.log (Real.log x) / (cardLength β x * Af x) := by
      rw [hW]
      field_simp
    rw [ha]
    have hb : 10 * Real.log (Real.log x) / (cardLength β x * Af x)
        ≤ 10 * Real.log (Real.log x) / (cardLength β x * (cA * Real.log (Real.log x))) := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      exact mul_le_mul_of_nonneg_left hA hh0.le
    refine hb.trans (le_of_eq ?_)
    field_simp
  have k2 : 20 * twoRangeTop β x * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
      ≤ 20 / (cA * ((twoRangeLength β x : ℕ) : ℝ)) := by
    have ha : 20 * twoRangeTop β x * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
        = 20 * Real.log (Real.log x) * Pf x
          / (cardLength β x * Af x * ((twoRangeLength β x : ℕ) : ℝ)) := by
      rw [hW]
      field_simp
    rw [ha]
    have hb : 20 * Real.log (Real.log x) * Pf x
          / (cardLength β x * Af x * ((twoRangeLength β x : ℕ) : ℝ))
        ≤ 20 * Real.log (Real.log x) * cardLength β x
          / (cardLength β x * Af x * ((twoRangeLength β x : ℕ) : ℝ)) := by
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have := hP.2
      nlinarith [hu0]
    refine hb.trans ?_
    have hc : 20 * Real.log (Real.log x) * cardLength β x
          / (cardLength β x * Af x * ((twoRangeLength β x : ℕ) : ℝ))
        = 20 * Real.log (Real.log x) / (Af x * ((twoRangeLength β x : ℕ) : ℝ)) := by
      field_simp
    rw [hc]
    have hd2 : 20 * Real.log (Real.log x) / (Af x * ((twoRangeLength β x : ℕ) : ℝ))
        ≤ 20 * Real.log (Real.log x)
          / ((cA * Real.log (Real.log x)) * ((twoRangeLength β x : ℕ) : ℝ)) := by
      refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
      exact mul_le_mul_of_nonneg_right hA hM0.le
    refine hd2.trans (le_of_eq ?_)
    field_simp
  have k3 : 7 / Af x ≤ 7 / (cA * Real.log (Real.log x)) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hA
  have k4 : 14 * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ))
      ≤ 14 * cardLength β x / (cA * Real.log (Real.log x) * ((twoRangeLength β x : ℕ) : ℝ)) := by
    have hnum : 14 * Pf x ≤ 14 * cardLength β x := by linarith [hP.2]
    have hden : cA * Real.log (Real.log x) * ((twoRangeLength β x : ℕ) : ℝ)
        ≤ Af x * ((twoRangeLength β x : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hA hM0.le
    have hd0 : (0 : ℝ) < cA * Real.log (Real.log x) * ((twoRangeLength β x : ℕ) : ℝ) := by
      positivity
    refine div_le_div₀ (by positivity) hnum hd0 hden
  have hsum : 10 * twoRangeTop β x / (Af x * ((twoRangeLength β x : ℕ) : ℝ))
      + 20 * twoRangeTop β x * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ) ^ 2)
      + 7 / Af x
      + 14 * Pf x / (Af x * ((twoRangeLength β x : ℕ) : ℝ))
      ≤ 10 / (cA * cardLength β x) + 20 / (cA * ((twoRangeLength β x : ℕ) : ℝ))
        + 7 / (cA * Real.log (Real.log x))
        + 14 * cardLength β x
            / (cA * Real.log (Real.log x) * ((twoRangeLength β x : ℕ) : ℝ)) := by
    linarith [k1, k2, k3, k4]
  have hsum0 : (0 : ℝ) ≤ 10 / (cA * cardLength β x) + 20 / (cA * ((twoRangeLength β x : ℕ) : ℝ))
      + 7 / (cA * Real.log (Real.log x))
      + 14 * cardLength β x / (cA * Real.log (Real.log x) * ((twoRangeLength β x : ℕ) : ℝ)) := by
    positivity
  have hd1 : 1 / twoRangeDelta x = (Real.log (Real.log x)) ^ ((1 : ℝ) / 2) := by
    rw [twoRangeDelta, show (-(1 : ℝ) / 2) = -((1 : ℝ) / 2) by ring, Real.rpow_neg hu0.le,
      one_div, inv_inv]
  have hDle : 1 / twoRangeDelta x ≤ Real.log (Real.log x) := by
    rw [hd1]
    calc (Real.log (Real.log x)) ^ ((1 : ℝ) / 2)
        ≤ (Real.log (Real.log x)) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hu1 (by norm_num)
      _ = Real.log (Real.log x) := Real.rpow_one _
  have hD0 : (0 : ℝ) ≤ 1 / twoRangeDelta x := by
    rw [hd1]
    exact Real.rpow_nonneg hu0.le _
  have hδu : (1 / twoRangeDelta x) * (1 / Real.log (Real.log x)) = twoRangeDelta x := by
    rw [hd1, twoRangeDelta, show (-(1 : ℝ) / 2) = (1 : ℝ) / 2 + (-1) by ring,
      Real.rpow_add hu0, Real.rpow_neg_one]
    rw [one_div (Real.log (Real.log x))]
  have hδ1 : twoRangeDelta x ≤ 1 := by
    rw [twoRangeDelta]
    exact Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
  have hδ0 : (0 : ℝ) ≤ twoRangeDelta x := by
    rw [twoRangeDelta]
    exact Real.rpow_nonneg hu0.le _
  refine le_trans (mul_le_mul_of_nonneg_left hsum (by linarith : (0 : ℝ) ≤ 1 + 1 / twoRangeDelta x))
    ?_
  have hT1 : 10 / (cA * cardLength β x) = (10 / cA) * (1 / cardLength β x) := by
    field_simp
  have hT2 : 20 / (cA * ((twoRangeLength β x : ℕ) : ℝ))
      = (20 / cA) * (1 / ((twoRangeLength β x : ℕ) : ℝ)) := by
    field_simp
  have hT3 : 7 / (cA * Real.log (Real.log x))
      = (7 / cA) * (1 / Real.log (Real.log x)) := by
    field_simp
  have hT4 : 14 * cardLength β x
        / (cA * Real.log (Real.log x) * ((twoRangeLength β x : ℕ) : ℝ))
      = (14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))
        * (1 / Real.log (Real.log x)) := by
    field_simp
  have hDT1 : (1 / twoRangeDelta x) * ((10 / cA) * (1 / cardLength β x))
      ≤ (10 / cA) * (Real.log (Real.log x) / cardLength β x) := by
    have h := mul_le_mul_of_nonneg_right hDle
      (by positivity : (0 : ℝ) ≤ (10 / cA) * (1 / cardLength β x))
    refine h.trans (le_of_eq ?_)
    field_simp
  have hDT2 : (1 / twoRangeDelta x) * ((20 / cA) * (1 / ((twoRangeLength β x : ℕ) : ℝ)))
      ≤ (20 / cA) * (Real.log (Real.log x) / ((twoRangeLength β x : ℕ) : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hDle
      (by positivity : (0 : ℝ) ≤ (20 / cA) * (1 / ((twoRangeLength β x : ℕ) : ℝ)))
    refine h.trans (le_of_eq ?_)
    field_simp
  have hDT3 : (1 / twoRangeDelta x) * ((7 / cA) * (1 / Real.log (Real.log x)))
      = (7 / cA) * twoRangeDelta x := by
    have hre : (1 / twoRangeDelta x) * ((7 / cA) * (1 / Real.log (Real.log x)))
        = (7 / cA) * ((1 / twoRangeDelta x) * (1 / Real.log (Real.log x))) := by ring
    rw [hre, hδu]
  have hu1' : 1 / Real.log (Real.log x) ≤ 1 := by
    rw [div_le_one hu0]
    exact hu1
  have hhm0 : (0 : ℝ) ≤ (14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ)) := by
    positivity
  have hT4' : (14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))
        * (1 / Real.log (Real.log x))
      ≤ (14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ)) := by
    have := mul_le_mul_of_nonneg_left hu1' hhm0
    linarith [this]
  have hDT4 : (1 / twoRangeDelta x)
        * ((14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))
          * (1 / Real.log (Real.log x)))
      ≤ (14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ)) := by
    have hid : (1 / twoRangeDelta x)
          * ((14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))
            * (1 / Real.log (Real.log x)))
        = (14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ)) * twoRangeDelta x := by
      have hre : (1 / twoRangeDelta x)
            * ((14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))
              * (1 / Real.log (Real.log x)))
          = (14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))
            * ((1 / twoRangeDelta x) * (1 / Real.log (Real.log x))) := by ring
      rw [hre, hδu]
    rw [hid]
    have := mul_le_mul_of_nonneg_left hδ1 hhm0
    linarith [this]
  have hsplit : (1 + 1 / twoRangeDelta x)
        * (10 / (cA * cardLength β x) + 20 / (cA * ((twoRangeLength β x : ℕ) : ℝ))
          + 7 / (cA * Real.log (Real.log x))
          + 14 * cardLength β x
              / (cA * Real.log (Real.log x) * ((twoRangeLength β x : ℕ) : ℝ)))
      = ((10 / cA) * (1 / cardLength β x)
          + (20 / cA) * (1 / ((twoRangeLength β x : ℕ) : ℝ))
          + (7 / cA) * (1 / Real.log (Real.log x))
          + (14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))
            * (1 / Real.log (Real.log x)))
        + ((1 / twoRangeDelta x) * ((10 / cA) * (1 / cardLength β x))
          + (1 / twoRangeDelta x) * ((20 / cA) * (1 / ((twoRangeLength β x : ℕ) : ℝ)))
          + (1 / twoRangeDelta x) * ((7 / cA) * (1 / Real.log (Real.log x)))
          + (1 / twoRangeDelta x)
            * ((14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))
              * (1 / Real.log (Real.log x)))) := by
    rw [hT1, hT2, hT3, hT4]
    ring
  rw [hsplit]
  have hG7 : (14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))
      + (14 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ))
      = (28 / cA) * (cardLength β x / ((twoRangeLength β x : ℕ) : ℝ)) := by ring
  linarith [hDT1, hDT2, hDT3, hDT4, hT4', hG7]

/-- The Halász–Montgomery logarithm of the window is below the logarithm of the outer scale. -/
theorem log_window_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∀ᶠ x : ℝ in atTop,
      Real.log (2 + 2 * (2 * Real.pi * twoRangeTop β x)) ≤ Real.log x := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsq := tendsto_rpow_log_div_sqrt (1 : ℝ)
  filter_upwards [one_le_twoRangeCut hβ0 hβ1, Filter.eventually_gt_atTop (1 : ℝ),
    Filter.eventually_ge_atTop (16 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (1 : ℝ),
    (tendsto_cardLength hβ0).eventually_ge_atTop (1 : ℝ),
    Tendsto.eventually_le_const (show (0 : ℝ) < 1 / (32 * Real.pi) by positivity) hsq]
    with x hcut hx1 hx16 hlog1 hh1 hsmall
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hsqrt : (4 : ℝ) ≤ Real.sqrt x := by
    rw [show (4 : ℝ) = Real.sqrt 16 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx16
  have hsq0 : (0 : ℝ) < Real.sqrt x := by linarith
  have hxx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hkey : 32 * Real.pi * Real.log x ≤ Real.sqrt x := by
    rw [Real.rpow_one, div_le_iff₀ hsq0] at hsmall
    have hmul := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℝ) ≤ 32 * Real.pi)
    have hid : 32 * Real.pi * (1 / (32 * Real.pi) * Real.sqrt x) = Real.sqrt x := by
      field_simp
    rw [hid] at hmul
    linarith
  have hcutle : twoRangeCut β x ≤ Real.sqrt x + 1 := by
    have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
    have hfl : ((twoRangeLength β x : ℕ) : ℝ) ≤ Real.sqrt x + cardLength β x := by
      rw [twoRangeLength]
      refine Nat.floor_le ?_
      linarith [Real.sqrt_nonneg x, hh0]
    rw [twoRangeCut, div_le_iff₀ hh0]
    nlinarith [hfl, hh1, hsq0]
  have hll : Real.log (Real.log x) ≤ Real.log x := by
    have := Real.log_le_sub_one_of_pos hlogx
    linarith
  have hll0 : (0 : ℝ) ≤ Real.log (Real.log x) := Real.log_nonneg hlog1
  have hcut0 : (0 : ℝ) ≤ twoRangeCut β x := by linarith [hcut]
  have htop : twoRangeTop β x ≤ (Real.sqrt x + 1) * Real.log x := by
    rw [twoRangeTop]
    nlinarith [hcutle, hll, hll0, hcut0]
  have htop0 : (0 : ℝ) ≤ twoRangeTop β x := by
    rw [twoRangeTop]
    exact mul_nonneg hcut0 hll0
  have hle : 2 + 2 * (2 * Real.pi * twoRangeTop β x) ≤ x := by
    have h1 : 2 * (2 * Real.pi * twoRangeTop β x)
        ≤ 8 * Real.pi * (Real.sqrt x * Real.log x) := by
      nlinarith [htop, hpi, hsqrt, hlogx, htop0]
    have h2 : 8 * Real.pi * (Real.sqrt x * Real.log x) ≤ x / 4 := by
      nlinarith [hkey, hsq0, hxx, hpi, hlogx]
    have h3 : (2 : ℝ) ≤ x / 4 := by
      nlinarith [hsqrt, hxx, hsq0]
    linarith
  have hpos : (0 : ℝ) < 2 + 2 * (2 * Real.pi * twoRangeTop β x) := by
    nlinarith [htop0, hpi]
  exact Real.log_le_log hpos hle

end

end RHTower.Sieve
