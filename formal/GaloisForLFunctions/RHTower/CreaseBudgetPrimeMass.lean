import GaloisForLFunctions.RHTower.SqrtCarrierCertificate
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The line budget carries the Mertens mass

The Lipschitz variation budget that transfers a carrier floor from a certified line
`re = σ₂` to the critical line `σ₁ = 1/2` is not a free parameter: its square-only
support forces it to contain the prime reciprocal mass up to `√N`.  Three positive laws:

* `RHTower.primeMass_le_lineBudget_add` — the budget **must carry the Mertens mass**:
  `∑_{p ≤ √N} 1/p ≤ lineBudget σ₂ N + (1 + 1/(2σ₂-1))`, because each prime square `p²`
  contributes the full `p⁻¹ - p^(-2σ₂)` to the budget.
* `RHTower.tendsto_lineBudget_atTop` — the growth law: the line budget diverges with the
  cutoff, at least as fast as the prime mass.
* `RHTower.line_crossing_cutoff_primeMass_lt` — any Lipschitz line-crossing datum (a line
  floor at `re = σ₂` plus the budget condition to `1/2`) **forces the cutoff's prime mass
  under the explicit cap** `2(1 + 1/(2σ₂-1))`: budget technology reaches the line exactly
  for cutoffs of bounded Mertens mass, and the certified region beyond bounded mass
  belongs to the cofinal-density machinery of `FloorFailureCofinal`.

Supporting bricks, reusable: the partial zeta cap
`∑_{k≤M} k^(-c) ≤ 1 + 1/(c-1)` (`RHTower.sum_Icc_rpow_neg_le`), the uniform carrier sup
bound `‖dpoly2 sqrtMoebiusCoeff (Icc 1 N) z‖ ≤ 1 + 1/(2σ₂-1)` on `re z ≥ σ₂`
(`RHTower.norm_dpoly2_sqrtMoebius_le`, via the finite dilation identity), and the
divergence of prime reciprocal partial sums (`RHTower.tendsto_primeMass_atTop`, from
mathlib's `not_summable_one_div_on_primes`).
-/

noncomputable section

namespace RHTower

open Complex Filter

/-! ## The partial zeta cap and the carrier sup bound -/

/-- Real square-power dilation: `((k²:ℕ):ℝ)^y = (k:ℝ)^(2y)`. -/
theorem natCast_sq_rpow (k : ℕ) (y : ℝ) :
    ((k ^ 2 : ℕ) : ℝ) ^ y = ((k : ℕ) : ℝ) ^ (2 * y) := by
  push_cast
  rw [← Real.rpow_natCast ((k : ℕ) : ℝ) 2, ← Real.rpow_mul (Nat.cast_nonneg k)]
  norm_num

/-- Partial zeta cap: `∑_{k ∈ [1,M]} k^(-c) ≤ 1 + 1/(c-1)` for `c > 1`, uniformly in
`M`. -/
theorem sum_Icc_rpow_neg_le {c : ℝ} (hc : 1 < c) (M : ℕ) :
    ∑ k ∈ Finset.Icc 1 M, (k : ℝ) ^ (-c) ≤ 1 + 1 / (c - 1) := by
  have hpos : (0 : ℝ) < 1 / (c - 1) := by positivity
  rcases M with _ | n
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    linarith
  · have hIcc : Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 2) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range,
      show n + 2 - 1 = n + 1 from rfl, Finset.sum_range_succ']
    have h0 : ((1 + 0 : ℕ) : ℝ) ^ (-c) = 1 := by
      rw [show (1 + 0 : ℕ) = 1 from rfl, Nat.cast_one, Real.one_rpow]
    have hsum : ∑ i ∈ Finset.range n, ((1 + (i + 1) : ℕ) : ℝ) ^ (-c) ≤ 1 / (c - 1) := by
      have hb := sum_range_add_rpow_neg_le hc (M := 1) le_rfl n
      rw [Nat.cast_one, Real.one_rpow] at hb
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_)) hb
      congr 1
      push_cast
      ring
    rw [h0]
    linarith

/-- Uniform sup bound for the Möbius carrier: `‖dpoly2 moebiusCoeff (Icc 1 M) w‖ ≤
1 + 1/(c-1)` on `re w ≥ c > 1`, uniformly in the cutoff and the height. -/
theorem norm_dpoly2_moebiusCoeff_le {c : ℝ} (hc : 1 < c) {w : ℂ} (hw : c ≤ w.re) (M : ℕ) :
    ‖dpoly2 moebiusCoeff (Finset.Icc 1 M) w‖ ≤ 1 + 1 / (c - 1) := by
  rw [dpoly2]
  refine le_trans (le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n hn => ?_))
    (sum_Icc_rpow_neg_le hc M)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_natCast_cpow_of_pos (by omega), neg_re]
  calc |moebiusCoeff n| * (n : ℝ) ^ (-w.re)
      ≤ 1 * (n : ℝ) ^ (-w.re) :=
        mul_le_mul_of_nonneg_right (abs_moebiusCoeff_le_one n)
          (Real.rpow_nonneg (by positivity) _)
    _ = (n : ℝ) ^ (-w.re) := one_mul _
    _ ≤ (n : ℝ) ^ (-c) := Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)

/-- Uniform sup bound for the square-dilated carrier on `re z ≥ σ₂ > 1/2`:
`‖dpoly2 sqrtMoebiusCoeff (Icc 1 N) z‖ ≤ 1 + 1/(2σ₂-1)`, via the finite dilation
identity. -/
theorem norm_dpoly2_sqrtMoebius_le {σ₂ : ℝ} (hσ₂ : 1 / 2 < σ₂) {z : ℂ} (hz : σ₂ ≤ z.re)
    (N : ℕ) :
    ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) z‖ ≤ 1 + 1 / (2 * σ₂ - 1) := by
  rw [dpoly2_sqrtMoebiusCoeff_eq_moebius_sqrt]
  have h2re : (2 * z).re = 2 * z.re := by simp [Complex.mul_re]
  exact norm_dpoly2_moebiusCoeff_le (by linarith) (by rw [h2re]; linarith) _

/-! ## The line budget and its prime-mass content -/

/-- The Lipschitz variation budget from the critical line `σ₁ = 1/2` to the line
`re = σ₂`, for the square-dilated Möbius carrier at cutoff `N` — the `hbudget` quantity
of `sqrtCarrier_strip_floor` at `σ₁ = 1/2`, `σ₂ = 1/2 + ε`. -/
def lineBudget (σ₂ : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, |sqrtMoebiusCoeff n| * |(n : ℝ) ^ (-(1 / 2 : ℝ)) - (n : ℝ) ^ (-σ₂)|

/-- At a prime square the budget term is the full reciprocal defect
`p⁻¹ - p^(-2σ₂)`. -/
theorem lineBudget_term_sq_prime {σ₂ : ℝ} (hσ₂ : 1 / 2 < σ₂) {p : ℕ} (hp : p.Prime) :
    |sqrtMoebiusCoeff (p ^ 2)| *
        |((p ^ 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) - ((p ^ 2 : ℕ) : ℝ) ^ (-σ₂)|
      = (p : ℝ)⁻¹ - (p : ℝ) ^ (-(2 * σ₂)) := by
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hcoeff : |sqrtMoebiusCoeff (p ^ 2)| = 1 := by
    rw [sqrtMoebiusCoeff, sqrtPart_apply_sq, ArithmeticFunction.moebius_apply_prime hp]
    norm_num
  have hpow1 : ((p ^ 2 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) = (p : ℝ)⁻¹ := by
    rw [natCast_sq_rpow, show (2 : ℝ) * (-(1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  have hpow2 : ((p ^ 2 : ℕ) : ℝ) ^ (-σ₂) = (p : ℝ) ^ (-(2 * σ₂)) := by
    rw [natCast_sq_rpow]
    congr 1
    ring
  have hord : (p : ℝ) ^ (-(2 * σ₂)) ≤ (p : ℝ)⁻¹ := by
    have h := Real.rpow_le_rpow_of_exponent_le hp1 (show -(2 * σ₂) ≤ -1 by linarith)
    rwa [Real.rpow_neg_one] at h
  rw [hcoeff, one_mul, hpow1, hpow2, abs_of_nonneg (by linarith)]

/-- **The line budget must carry the Mertens mass.**  The prime reciprocal sum up to
`√N` is contained in the budget, up to the partial zeta cap:
`∑_{p ≤ √N} p⁻¹ ≤ lineBudget σ₂ N + (1 + 1/(2σ₂-1))`. -/
theorem primeMass_le_lineBudget_add {σ₂ : ℝ} (hσ₂ : 1 / 2 < σ₂) (N : ℕ) :
    ∑ p ∈ Nat.primesBelow (Nat.sqrt N + 1), (p : ℝ)⁻¹
      ≤ lineBudget σ₂ N + (1 + 1 / (2 * σ₂ - 1)) := by
  have hc2 : 1 < 2 * σ₂ := by linarith
  have himg : (Nat.primesBelow (Nat.sqrt N + 1)).image (fun p => p ^ 2)
      ⊆ Finset.Icc 1 N := by
    intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
    have hple : p ≤ Nat.sqrt N := by omega
    refine Finset.mem_Icc.mpr ⟨Nat.one_le_pow _ _ hpp.pos, ?_⟩
    rw [pow_two]
    exact Nat.le_sqrt.mp hple
  have hsub : ∑ n ∈ (Nat.primesBelow (Nat.sqrt N + 1)).image (fun p => p ^ 2),
      |sqrtMoebiusCoeff n| * |(n : ℝ) ^ (-(1 / 2 : ℝ)) - (n : ℝ) ^ (-σ₂)|
      ≤ lineBudget σ₂ N :=
    Finset.sum_le_sum_of_subset_of_nonneg himg fun i _ _ => by positivity
  rw [Finset.sum_image ((Nat.pow_left_injective two_ne_zero).injOn),
    Finset.sum_congr rfl (fun p hp =>
      lineBudget_term_sq_prime hσ₂ (Nat.mem_primesBelow.mp hp).2),
    Finset.sum_sub_distrib] at hsub
  have hzeta : ∑ p ∈ Nat.primesBelow (Nat.sqrt N + 1), (p : ℝ) ^ (-(2 * σ₂))
      ≤ 1 + 1 / (2 * σ₂ - 1) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun i _ _ => by positivity)
      (sum_Icc_rpow_neg_le hc2 (Nat.sqrt N + 1))
    intro p hp
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
    exact Finset.mem_Icc.mpr ⟨hpp.pos, by omega⟩
  linarith

/-! ## The growth law -/

/-- The prime reciprocal partial sums diverge (Euler–Mertens, from mathlib's
`not_summable_one_div_on_primes`). -/
theorem tendsto_primeMass_atTop :
    Tendsto (fun x : ℕ => ∑ p ∈ Nat.primesBelow x, (p : ℝ)⁻¹) atTop atTop := by
  have hpb : ∀ x : ℕ, x.primesBelow = (Finset.range x).filter Nat.Prime := by
    intro x
    ext p
    simp [Nat.mem_primesBelow, Finset.mem_filter, Finset.mem_range]
  have hkey : ∀ x : ℕ, ∑ p ∈ Nat.primesBelow x, (p : ℝ)⁻¹
      = ∑ i ∈ Finset.range x,
          Set.indicator {p : ℕ | Nat.Prime p} (fun n => 1 / (n : ℝ)) i := by
    intro x
    rw [hpb, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Set.indicator_apply]
    simp only [Set.mem_setOf_eq]
    split_ifs <;> simp [one_div]
  have hnn : ∀ i : ℕ, 0 ≤ Set.indicator {p : ℕ | Nat.Prime p} (fun n => 1 / (n : ℝ)) i :=
    fun i => Set.indicator_nonneg (fun j _ => by positivity) i
  have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).mp
    not_summable_one_div_on_primes
  exact Tendsto.congr (fun x => (hkey x).symm) hdiv

/-- **The growth law**: the line budget diverges with the cutoff, at least as fast as
the Mertens mass of the primes up to `√N`. -/
theorem tendsto_lineBudget_atTop {σ₂ : ℝ} (hσ₂ : 1 / 2 < σ₂) :
    Tendsto (fun N => lineBudget σ₂ N) atTop atTop := by
  have hsq : Tendsto (fun N : ℕ => Nat.sqrt N + 1) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    exact fun b => ⟨b * b, fun N hN => le_trans (Nat.le_sqrt.mpr hN) (Nat.le_succ _)⟩
  have hcomp := tendsto_primeMass_atTop.comp hsq
  have hshift := tendsto_atTop_add_const_right atTop (-(1 + 1 / (2 * σ₂ - 1))) hcomp
  refine tendsto_atTop_mono (fun N => ?_) hshift
  have hmass := primeMass_le_lineBudget_add hσ₂ N
  simp only [Function.comp_apply]
  linarith

/-! ## The forced constraint on line-crossing cutoffs -/

/-- **Line-crossing forces bounded prime mass.**  Any Lipschitz transfer datum reaching
the critical line — a line floor `t₀` at `re = σ₂` together with the budget condition
down to `σ₁ = 1/2` — forces the prime mass of the cutoff under the explicit cap:
`∑_{p ≤ √N} p⁻¹ < 2(1 + 1/(2σ₂-1))`.  Budget technology reaches the line exactly on
cutoffs of bounded Mertens mass; beyond them the line belongs to the cofinal-density
machinery. -/
theorem line_crossing_cutoff_primeMass_lt {σ₂ : ℝ} (hσ₂ : 1 / 2 < σ₂) {N : ℕ}
    {t₀ ε₁ τ : ℝ} (hε₁ : 0 < ε₁)
    (hline : t₀ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) ((σ₂ : ℂ) + (τ : ℂ) * I)‖)
    (hbudget : lineBudget σ₂ N ≤ t₀ - ε₁) :
    ∑ p ∈ Nat.primesBelow (Nat.sqrt N + 1), (p : ℝ)⁻¹ < 2 * (1 + 1 / (2 * σ₂ - 1)) := by
  have hcap := norm_dpoly2_sqrtMoebius_le hσ₂
    (z := (σ₂ : ℂ) + (τ : ℂ) * I) (by simp) N
  have hmass := primeMass_le_lineBudget_add hσ₂ N
  linarith

end RHTower
