import GaloisForLFunctions.RHTower.BeurlingDeletionSystemPrimes
import GaloisForLFunctions.RHTower.BeurlingDeletionEulerProduct

/-!
# The primes of the deletion system have exponent exactly `α` under RH

Let `S` be a set of deleted primes with the discrepancy bound (R) of `DeletionData α`,
`1/2 < α < 1`, `0 < β < α`.  For the deletion system `(ℙ ∖ S) ∪ ℙ^{1/β}`,

`ψ_B(X) − X = (ψ(X) − X) − ψ_S(X) + β^{−1} ψ(X^β)`.

Under RH, `|ψ(X) − X| ≪ √X log² X` (von Koch).  By (R) at `t = 0`,
`π_S(X) = Σ_{p ≤ X} p^{α−1} + O(X^{α/2} log X)`, and `Σ_{p ≤ X} p^{α−1}` lies between
`X^{α−1} π(X) ≫ X^α / log X` and `X^α/α`.  With `log 2 · π_S ≤ ψ_S ≤ π_S log X`:

* `ψ_B(X) − X = O(X^{α+ε})` for every `ε > 0` (`isBigO_chebyshevPsi_sub`);
* `ψ_B(X) − X ≠ O(X^{α−ε})` for every `ε > 0` (`not_isBigO_chebyshevPsi_sub`), since
  `X − ψ_B(X) ≫ X^{α−r}` for small `r > 0`.
-/

open Finset Real Filter Asymptotics

noncomputable section

namespace RHTower.BeurlingDeletion

/-- `c X^a ≤ X^b` eventually, for `a < b`. -/
theorem eventually_const_mul_rpow_le (c : ℝ) {a b : ℝ} (hab : a < b) :
    ∀ᶠ X : ℝ in atTop, c * X ^ a ≤ X ^ b := by
  filter_upwards [(tendsto_rpow_atTop (sub_pos.mpr hab)).eventually_ge_atTop c,
    eventually_gt_atTop 0] with X hX hX0
  calc c * X ^ a ≤ X ^ (b - a) * X ^ a := by
        gcongr
    _ = X ^ b := by rw [← Real.rpow_add hX0]; ring_nf

/-- `Σ_{p ≤ X} p^{α−1}`. -/
def primeWeightSum (α X : ℝ) : ℝ := ∑ p ∈ Nat.primesLE ⌊X⌋₊, (p : ℝ) ^ (α - 1)

theorem primesLE_eq_filter_Iic (n : ℕ) : Nat.primesLE n = (Finset.Iic n).filter Nat.Prime := by
  rw [Nat.primesLE_eq_filter_range, Nat.range_succ_eq_Iic]

theorem abs_deletedCount_sub_le {α : ℝ} (D : DeletionData α) {X : ℝ} (hX : 1 ≤ X) :
    |deletedCount D.S X - primeWeightSum α X| ≤
      D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2) := by
  classical
  have h := D.disc X hX 0
  simp only [Complex.ofReal_zero, zero_mul, neg_zero, Complex.cpow_zero, mul_one, abs_zero,
    zero_add] at h
  rw [← primesLE_eq_filter_Iic] at h
  have hsum : ∑ p ∈ Nat.primesLE ⌊X⌋₊,
      (D.S.indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) =
      ((deletedCount D.S X - primeWeightSum α X : ℝ) : ℂ) := by
    rw [Finset.sum_sub_distrib, deletedCount, primeWeightSum]
    push_cast
    congr 1
    rw [Finset.sum_indicator_eq_sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

theorem primeWeightSum_le {α : ℝ} (hα0 : 0 < α) (hα : α ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    primeWeightSum α X ≤ X ^ α / α := by
  have hsub : Nat.primesLE ⌊X⌋₊ ⊆ Finset.Icc 1 ⌊X⌋₊ := by
    intro p hp
    rw [Finset.mem_Icc]
    exact ⟨(Nat.prime_of_mem_primesLE hp).one_le, (Nat.mem_primesLE.mp hp).1⟩
  calc primeWeightSum α X ≤ ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (n : ℝ) ^ (α - 1) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ ≤ (⌊X⌋₊ : ℝ) ^ α / α := DeletionData.sum_rpow_le hα0 hα _
    _ ≤ X ^ α / α := by
        gcongr
        exact Nat.floor_le (by linarith)

theorem primeWeightSum_ge {α : ℝ} (hα : α ≤ 1) {X : ℝ} (hX : 1 ≤ X) :
    X ^ (α - 1) * (Nat.primesLE ⌊X⌋₊).card ≤ primeWeightSum α X := by
  rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le
  have hpX : (p : ℝ) ≤ X := (Nat.le_floor_iff (by linarith)).mp (Nat.mem_primesLE.mp hp).1
  exact Real.rpow_le_rpow_of_nonpos (by linarith) hpX (by linarith)

/-- The von Koch constant. -/
def vonKochConst : ℝ := 200 * (xiLineTwoLogDerivConstant + 2)

theorem vonKochConst_nonneg : 0 ≤ vonKochConst := by
  have := xiLineTwoLogDerivConstant_nonneg
  unfold vonKochConst; positivity

/-- The two-sided bounds for `ψ_B(X) − X` at a fixed `X ≥ 16`. -/
theorem chebyshevPsi_sub_bounds (hRH : RiemannHypothesis) {α : ℝ} (D : DeletionData α)
    {β : ℝ} (hβ0 : 0 < β) {X : ℝ} (hX : 16 ≤ X) :
    |(deletionSystem D.S β hβ0).chebyshevPsi X - X| ≤
        vonKochConst * Real.sqrt X * Real.log X ^ 2 +
          (primeWeightSum α X + D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2)) *
            Real.log X + β⁻¹ * ((Real.log 4 + 4) * X ^ β) ∧
      Real.log 2 * (primeWeightSum α X -
          D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2)) -
        vonKochConst * Real.sqrt X * Real.log X ^ 2 - β⁻¹ * ((Real.log 4 + 4) * X ^ β) ≤
        X - (deletionSystem D.S β hβ0).chebyshevPsi X := by
  have hX1 : 1 ≤ X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX1
  rw [chebyshevPsi_deletionSystem D.S hβ0 hX1]
  have hvK := abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH hX
  have hP := primePowerSum_bounds D.S hX1
  have hcount := abs_deletedCount_sub_le D hX1
  have hψβ0 := Chebyshev.psi_nonneg (X ^ β)
  have hψβ := Chebyshev.psi_le_const_mul_self (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ X) β)
  have hβinv : 0 ≤ β⁻¹ := inv_nonneg.mpr hβ0.le
  have hcnt_up : deletedCount D.S X ≤ primeWeightSum α X +
      D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2) := by
    linarith [(abs_le.mp hcount).2]
  have hcnt_low : primeWeightSum α X -
      D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2) ≤ deletedCount D.S X := by
    linarith [(abs_le.mp hcount).1]
  unfold vonKochConst
  constructor
  · have h1 : primePowerSum D.S X ≤ (primeWeightSum α X +
        D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2)) * Real.log X :=
      hP.2.trans (mul_le_mul_of_nonneg_right hcnt_up hlog)
    have h2 : 0 ≤ primePowerSum D.S X := by
      have : 0 ≤ deletedCount D.S X := by unfold deletedCount; positivity
      exact (mul_nonneg (Real.log_nonneg (by norm_num)) this).trans hP.1
    have h3 : β⁻¹ * Chebyshev.psi (X ^ β) ≤ β⁻¹ * ((Real.log 4 + 4) * X ^ β) :=
      mul_le_mul_of_nonneg_left hψβ hβinv
    have h4 : 0 ≤ β⁻¹ * Chebyshev.psi (X ^ β) := mul_nonneg hβinv hψβ0
    rw [abs_le]; constructor <;> linarith [(abs_le.mp hvK).1, (abs_le.mp hvK).2]
  · have h1 : Real.log 2 * (primeWeightSum α X -
        D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2)) ≤ primePowerSum D.S X :=
      (mul_le_mul_of_nonneg_left hcnt_low (Real.log_nonneg (by norm_num))).trans hP.1
    have h3 : β⁻¹ * Chebyshev.psi (X ^ β) ≤ β⁻¹ * ((Real.log 4 + 4) * X ^ β) :=
      mul_le_mul_of_nonneg_left hψβ hβinv
    linarith [(abs_le.mp hvK).1, (abs_le.mp hvK).2]

/-- `log X ≤ X^r / r` and `log X + 1 ≤ 2 X^r / r` for `X ≥ 1`, `0 < r ≤ 1`. -/
theorem log_bounds {r X : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hX : 1 ≤ X) :
    Real.log X ≤ X ^ r / r ∧ Real.log X + 1 ≤ 2 * (X ^ r / r) := by
  have h1 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ X) hr
  have hXr : 1 ≤ X ^ r := Real.one_le_rpow hX hr.le
  have h2 : 1 ≤ X ^ r / r := by rw [le_div_iff₀ hr]; nlinarith
  exact ⟨h1, by linarith⟩

theorem sqrt_eq_rpow_half {X : ℝ} : Real.sqrt X = X ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow X

/-- **Upper bound:** `ψ_B(X) − X = O(X^{α+ε})`. -/
theorem isBigO_chebyshevPsi_sub (hRH : RiemannHypothesis) {α : ℝ} (hα1 : 1 / 2 < α)
    (hα : α ≤ 1) (D : DeletionData α) {β : ℝ} (hβ0 : 0 < β) (hβα : β < α) {ε : ℝ} (hε : 0 < ε) :
    (fun X => (deletionSystem D.S β hβ0).chebyshevPsi X - X) =O[atTop]
      fun X => X ^ (α + ε) := by
  have hα0 : 0 < α := by linarith
  set r : ℝ := min ε 1 / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 := by have := min_le_right ε 1; linarith
  have hrε : 2 * r ≤ ε := by have := min_le_left ε 1; linarith
  set K : ℝ := vonKochConst / r ^ 2 + 1 / (α * r) + 2 * D.C * Real.sqrt (Real.log 2) / r ^ 2 +
    β⁻¹ * (Real.log 4 + 4) with hK
  refine IsBigO.of_bound K ?_
  filter_upwards [eventually_ge_atTop (16 : ℝ)] with X hX
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  obtain ⟨hl1, hl2⟩ := log_bounds hr0 hr1 hX1
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hXr : 0 < X ^ r := Real.rpow_pos_of_pos hX0 r
  have hmono : ∀ {a b : ℝ}, a ≤ b → X ^ a ≤ X ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hX1 h
  have hfin := (chebyshevPsi_sub_bounds hRH D hβ0 hX).1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hX0 _)]
  refine hfin.trans ?_
  have hF := primeWeightSum_le hα0 hα hX1
  have hvK0 := vonKochConst_nonneg
  have hC0 := D.C_nonneg
  -- term by term
  have t1 : vonKochConst * Real.sqrt X * Real.log X ^ 2 ≤ vonKochConst / r ^ 2 * X ^ (α + ε) := by
    calc vonKochConst * Real.sqrt X * Real.log X ^ 2
        ≤ vonKochConst * X ^ (1 / 2 : ℝ) * (X ^ r / r) ^ 2 := by
          rw [sqrt_eq_rpow_half]; gcongr
      _ = vonKochConst / r ^ 2 * X ^ (1 / 2 + 2 * r) := by
          rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le, Real.rpow_add hX0]
          push_cast; field_simp
      _ ≤ vonKochConst / r ^ 2 * X ^ (α + ε) :=
          mul_le_mul_of_nonneg_left (hmono (by linarith)) (div_nonneg hvK0 (by positivity))
  have t2 : primeWeightSum α X * Real.log X ≤ 1 / (α * r) * X ^ (α + ε) := by
    calc primeWeightSum α X * Real.log X ≤ X ^ α / α * (X ^ r / r) := by gcongr
      _ = 1 / (α * r) * X ^ (α + r) := by rw [Real.rpow_add hX0]; field_simp
      _ ≤ 1 / (α * r) * X ^ (α + ε) :=
          mul_le_mul_of_nonneg_left (hmono (by linarith)) (by positivity)
  have t3 : D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2) * Real.log X ≤
      2 * D.C * Real.sqrt (Real.log 2) / r ^ 2 * X ^ (α + ε) := by
    calc D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2) * Real.log X
        ≤ D.C * X ^ (α / 2) * (2 * (X ^ r / r)) * Real.sqrt (Real.log 2) * (X ^ r / r) := by
          gcongr
      _ = 2 * D.C * Real.sqrt (Real.log 2) / r ^ 2 * X ^ (α / 2 + 2 * r) := by
          rw [Real.rpow_add hX0, show 2 * r = r + r by ring, Real.rpow_add hX0]
          field_simp
      _ ≤ 2 * D.C * Real.sqrt (Real.log 2) / r ^ 2 * X ^ (α + ε) :=
          mul_le_mul_of_nonneg_left (hmono (by linarith)) (by positivity)
  have t4 : β⁻¹ * ((Real.log 4 + 4) * X ^ β) ≤ β⁻¹ * (Real.log 4 + 4) * X ^ (α + ε) := by
    rw [← mul_assoc]
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    exact mul_le_mul_of_nonneg_left (hmono (by linarith)) (by positivity)
  calc vonKochConst * Real.sqrt X * Real.log X ^ 2 +
        (primeWeightSum α X + D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2)) *
          Real.log X + β⁻¹ * ((Real.log 4 + 4) * X ^ β)
      = vonKochConst * Real.sqrt X * Real.log X ^ 2 + primeWeightSum α X * Real.log X +
          D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2) * Real.log X +
          β⁻¹ * ((Real.log 4 + 4) * X ^ β) := by ring
    _ ≤ vonKochConst / r ^ 2 * X ^ (α + ε) + 1 / (α * r) * X ^ (α + ε) +
          2 * D.C * Real.sqrt (Real.log 2) / r ^ 2 * X ^ (α + ε) +
          β⁻¹ * (Real.log 4 + 4) * X ^ (α + ε) := by linarith
    _ = K * X ^ (α + ε) := by rw [hK]; ring

/-- Under RH, `Σ_{p ≤ X} p^{α−1} ≥ (r/2) X^{α−r}` eventually, for `0 < r < 1/4`. -/
theorem eventually_primeWeightSum_ge (hRH : RiemannHypothesis) {α : ℝ} (hα : α ≤ 1) {r : ℝ}
    (hr0 : 0 < r) (hr : r < 1 / 4) :
    ∀ᶠ X : ℝ in atTop, r / 2 * X ^ (α - r) ≤ primeWeightSum α X := by
  filter_upwards [eventually_ge_atTop (16 : ℝ),
    eventually_const_mul_rpow_le (2 * (vonKochConst / r ^ 2 + 2 / r)) (a := 1 / 2 + 2 * r)
      (b := 1) (by linarith)] with X hX hcmp
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hr1 : r ≤ 1 := by linarith
  obtain ⟨hl1, -⟩ := log_bounds hr0 hr1 hX1
  have hlog0 : 0 < Real.log X := Real.log_pos (by linarith)
  have hvK0 := vonKochConst_nonneg
  have hmono : ∀ {a b : ℝ}, a ≤ b → X ^ a ≤ X ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hX1 h
  rw [Real.rpow_one] at hcmp
  -- `θ(X) ≥ X/2`
  have hvK := abs_chebyshevPsi_sub_le_of_riemannHypothesis hRH hX
  have hψθ := Chebyshev.psi_sub_theta_le hX1
  have hs1 : Real.sqrt X * Real.log X ^ 2 ≤ X ^ (1 / 2 + 2 * r) / r ^ 2 := by
    calc Real.sqrt X * Real.log X ^ 2 ≤ X ^ (1 / 2 : ℝ) * (X ^ r / r) ^ 2 := by
          rw [sqrt_eq_rpow_half]; gcongr
      _ = X ^ (1 / 2 + 2 * r) / r ^ 2 := by
          rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le, Real.rpow_add hX0]
          push_cast; field_simp
  have hs2 : Real.sqrt X * Real.log X ≤ X ^ (1 / 2 + 2 * r) / r := by
    calc Real.sqrt X * Real.log X ≤ X ^ (1 / 2 : ℝ) * (X ^ r / r) := by
          rw [sqrt_eq_rpow_half]; gcongr
      _ = X ^ (1 / 2 + r) / r := by rw [Real.rpow_add hX0]; ring
      _ ≤ X ^ (1 / 2 + 2 * r) / r := div_le_div_of_nonneg_right (hmono (by linarith)) hr0.le
  have hθ : X / 2 ≤ Chebyshev.theta X := by
    have h1 : X - vonKochConst * Real.sqrt X * Real.log X ^ 2 ≤ Chebyshev.psi X := by
      have := (abs_le.mp hvK).1; unfold vonKochConst; linarith
    have h2 : vonKochConst * (Real.sqrt X * Real.log X ^ 2) + 2 * (Real.sqrt X * Real.log X) ≤
        (vonKochConst / r ^ 2 + 2 / r) * X ^ (1 / 2 + 2 * r) := by
      calc vonKochConst * (Real.sqrt X * Real.log X ^ 2) + 2 * (Real.sqrt X * Real.log X)
          ≤ vonKochConst * (X ^ (1 / 2 + 2 * r) / r ^ 2) + 2 * (X ^ (1 / 2 + 2 * r) / r) := by
            gcongr
        _ = _ := by ring
    nlinarith
  -- `π(X) ≥ (r/2) X^{1−r}`
  have hπ := Chebyshev.theta_le_pi_mul_log' X
  rw [← Nat.primesLE_card_eq_primeCounting] at hπ
  have hπ0 : (0 : ℝ) ≤ (Nat.primesLE ⌊X⌋₊).card := Nat.cast_nonneg _
  have hXr : 0 < X ^ r := Real.rpow_pos_of_pos hX0 r
  have hπ' : r / 2 * X ^ (1 - r) ≤ (Nat.primesLE ⌊X⌋₊).card := by
    have h1 : X / 2 ≤ (Nat.primesLE ⌊X⌋₊).card * (X ^ r / r) :=
      (hθ.trans hπ).trans (mul_le_mul_of_nonneg_left hl1 hπ0)
    have h2 : X ^ (1 - r) * X ^ r = X := by
      rw [← Real.rpow_add hX0]; simp
    have h3 : r / 2 * X ^ (1 - r) * X ^ r ≤ (Nat.primesLE ⌊X⌋₊).card * X ^ r := by
      have := mul_le_mul_of_nonneg_left h1 hr0.le
      calc r / 2 * X ^ (1 - r) * X ^ r = r * (X / 2) := by rw [mul_assoc, h2]; ring
        _ ≤ r * ((Nat.primesLE ⌊X⌋₊).card * (X ^ r / r)) := this
        _ = (Nat.primesLE ⌊X⌋₊).card * X ^ r := by field_simp
    exact le_of_mul_le_mul_right h3 hXr
  have hF := primeWeightSum_ge hα hX1
  calc r / 2 * X ^ (α - r) = X ^ (α - 1) * (r / 2 * X ^ (1 - r)) := by
        rw [show α - r = (α - 1) + (1 - r) by ring, Real.rpow_add hX0]; ring
    _ ≤ X ^ (α - 1) * (Nat.primesLE ⌊X⌋₊).card := by gcongr
    _ ≤ primeWeightSum α X := hF

/-- **Lower bound:** `ψ_B(X) − X ≠ O(X^{α−ε})`. -/
theorem not_isBigO_chebyshevPsi_sub (hRH : RiemannHypothesis) {α : ℝ} (hα1 : 1 / 2 < α)
    (hα : α ≤ 1) (D : DeletionData α) {β : ℝ} (hβ0 : 0 < β) (hβα : β < α) {ε : ℝ}
    (hε : 0 < ε) :
    ¬ (fun X => (deletionSystem D.S β hβ0).chebyshevPsi X - X) =O[atTop]
      fun X => X ^ (α - ε) := by
  intro h
  obtain ⟨K, hK⟩ := h.bound
  set r : ℝ := min (min (ε / 2) ((α - 1 / 2) / 8)) (min (α / 8) ((α - β) / 4)) with hr
  have hr0 : 0 < r := by
    refine lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  have hrε : r ≤ ε / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hrα : r ≤ (α - 1 / 2) / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hrα' : r ≤ α / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have hrβ : r ≤ (α - β) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have hr4 : r < 1 / 4 := by linarith
  have hr1 : r ≤ 1 := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hvK0 := vonKochConst_nonneg
  have hC0 := D.C_nonneg
  set c'' : ℝ := Real.log 2 * (2 * D.C * Real.sqrt (Real.log 2) / r) + vonKochConst / r ^ 2 +
    β⁻¹ * (Real.log 4 + 4) with hc''
  set c₄ : ℝ := 2 * (c'' + |K| + 1) / (Real.log 2 * r) with hc₄
  obtain ⟨X, ⟨hX16, hXK⟩, hXF, hX4⟩ := (((eventually_ge_atTop (16 : ℝ)).and hK).and
    ((eventually_primeWeightSum_ge hRH hα hr0 hr4).and
      (eventually_const_mul_rpow_le c₄ (a := α - 2 * r) (b := α - r) (by linarith)))).exists
  have hX1 : 1 ≤ X := by linarith
  have hX0 : 0 < X := by linarith
  have hmono : ∀ {a b : ℝ}, a ≤ b → X ^ a ≤ X ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hX1 h
  obtain ⟨hl1, hl2⟩ := log_bounds hr0 hr1 hX1
  have hlow := (chebyshevPsi_sub_bounds hRH D hβ0 hX16).2
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hX0 _)] at hXK
  have hpos : 0 < X ^ (α - 2 * r) := Real.rpow_pos_of_pos hX0 _
  -- the error terms
  have e1 : D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2) ≤
      2 * D.C * Real.sqrt (Real.log 2) / r * X ^ (α - 2 * r) := by
    calc D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2)
        ≤ D.C * X ^ (α / 2) * (2 * (X ^ r / r)) * Real.sqrt (Real.log 2) := by gcongr
      _ = 2 * D.C * Real.sqrt (Real.log 2) / r * X ^ (α / 2 + r) := by
          rw [Real.rpow_add hX0]; ring
      _ ≤ 2 * D.C * Real.sqrt (Real.log 2) / r * X ^ (α - 2 * r) :=
          mul_le_mul_of_nonneg_left (hmono (by linarith)) (by positivity)
  have e2 : vonKochConst * Real.sqrt X * Real.log X ^ 2 ≤ vonKochConst / r ^ 2 * X ^ (α - 2 * r) := by
    have hlog0 : 0 ≤ Real.log X := Real.log_nonneg hX1
    calc vonKochConst * Real.sqrt X * Real.log X ^ 2
        ≤ vonKochConst * X ^ (1 / 2 : ℝ) * (X ^ r / r) ^ 2 := by
          rw [sqrt_eq_rpow_half]; gcongr
      _ = vonKochConst / r ^ 2 * X ^ (1 / 2 + 2 * r) := by
          rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le, Real.rpow_add hX0]
          push_cast; field_simp
      _ ≤ vonKochConst / r ^ 2 * X ^ (α - 2 * r) :=
          mul_le_mul_of_nonneg_left (hmono (by linarith)) (div_nonneg hvK0 (by positivity))
  have e3 : β⁻¹ * ((Real.log 4 + 4) * X ^ β) ≤ β⁻¹ * (Real.log 4 + 4) * X ^ (α - 2 * r) := by
    rw [← mul_assoc]
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    exact mul_le_mul_of_nonneg_left (hmono (by linarith)) (by positivity)
  have hKX : K * X ^ (α - ε) ≤ |K| * X ^ (α - 2 * r) := by
    calc K * X ^ (α - ε) ≤ |K| * X ^ (α - ε) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
      _ ≤ |K| * X ^ (α - 2 * r) := mul_le_mul_of_nonneg_left (hmono (by linarith)) (abs_nonneg K)
  have hupper : X - (deletionSystem D.S β hβ0).chebyshevPsi X ≤ K * X ^ (α - ε) := by
    have := neg_abs_le ((deletionSystem D.S β hβ0).chebyshevPsi X - X); linarith
  have hmain : Real.log 2 * (r / 2 * X ^ (α - r)) ≤ (c'' + |K|) * X ^ (α - 2 * r) := by
    have h1 : Real.log 2 * (r / 2 * X ^ (α - r)) ≤ Real.log 2 * primeWeightSum α X :=
      mul_le_mul_of_nonneg_left hXF hlog2.le
    have h2 : Real.log 2 * (D.C * X ^ (α / 2) * (Real.log X + 1) * Real.sqrt (Real.log 2)) ≤
        Real.log 2 * (2 * D.C * Real.sqrt (Real.log 2) / r * X ^ (α - 2 * r)) :=
      mul_le_mul_of_nonneg_left e1 hlog2.le
    rw [hc'']
    nlinarith
  have h4 : Real.log 2 * r / 2 * (c₄ * X ^ (α - 2 * r)) ≤ Real.log 2 * r / 2 * X ^ (α - r) :=
    mul_le_mul_of_nonneg_left hX4 (by positivity)
  have h5 : Real.log 2 * r / 2 * (c₄ * X ^ (α - 2 * r)) = (c'' + |K| + 1) * X ^ (α - 2 * r) := by
    rw [hc₄]; field_simp
  nlinarith

end RHTower.BeurlingDeletion
