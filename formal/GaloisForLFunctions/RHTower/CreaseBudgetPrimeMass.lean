import GaloisForLFunctions.RHTower.SqrtCarrierCertificate
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Primorial

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

/-! ## The effective Mertens lower bound -/

/-- The reciprocal monoid homomorphism `n ↦ (n:ℝ)⁻¹`. -/
def recipHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by norm_num
  map_mul' m n := by push_cast; rw [mul_inv]

/-- **Euler's finite product domination**: the harmonic sum up to `M` is bounded by the
Euler product over the primes up to `M`, via the geometric Euler product over the
`(M+1)`-smooth numbers. -/
theorem harmonic_le_prod_primesBelow (M : ℕ) :
    ∑ n ∈ Finset.Icc 1 M, 1 / (n : ℝ)
      ≤ ∏ p ∈ Nat.primesBelow (M + 1), (1 - (p : ℝ)⁻¹)⁻¹ := by
  have hlt : ∀ {p : ℕ}, p.Prime → ‖recipHom p‖ < 1 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    show ‖((p : ℝ))⁻¹‖ < 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
      _ < 1 := by norm_num
  have hhs := (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric
    (f := recipHom) hlt (M + 1)).2
  have htsum : ∑' m : (Nat.smoothNumbers (M + 1)), ((m : ℕ) : ℝ)⁻¹
      = ∏ p ∈ Nat.primesBelow (M + 1), (1 - (p : ℝ)⁻¹)⁻¹ := hhs.tsum_eq
  have hsummable : Summable (fun m : (Nat.smoothNumbers (M + 1)) => ((m : ℕ) : ℝ)⁻¹) :=
    hhs.summable
  calc ∑ n ∈ Finset.Icc 1 M, 1 / (n : ℝ)
      = ∑ n ∈ Finset.Icc 1 M,
          Set.indicator (Nat.smoothNumbers (M + 1)) (fun n => ((n : ℕ) : ℝ)⁻¹) n := by
        refine Finset.sum_congr rfl fun n hn => ?_
        obtain ⟨hn1, hnM⟩ := Finset.mem_Icc.mp hn
        rw [Set.indicator_of_mem (Nat.mem_smoothNumbers'.mpr fun p _ hpd =>
          lt_of_le_of_lt (Nat.le_of_dvd (by omega) hpd) (by omega)), one_div]
    _ ≤ ∑' n : ℕ, Set.indicator (Nat.smoothNumbers (M + 1)) (fun n => ((n : ℕ) : ℝ)⁻¹) n := by
        refine Summable.sum_le_tsum _
          (fun i _ => Set.indicator_nonneg (fun j _ => by positivity) i) ?_
        exact summable_subtype_iff_indicator.mp hsummable
    _ = ∑' m : (Nat.smoothNumbers (M + 1)), ((m : ℕ) : ℝ)⁻¹ := (tsum_subtype _ _).symm
    _ = ∏ p ∈ Nat.primesBelow (M + 1), (1 - (p : ℝ)⁻¹)⁻¹ := htsum

/-- `log((1-t)⁻¹) ≤ 2t` on `[0, 1/2]`. -/
theorem log_inv_one_sub_le {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1 / 2) :
    Real.log (1 - t)⁻¹ ≤ 2 * t := by
  have h1t : 0 < 1 - t := by linarith
  have hle := Real.log_le_sub_one_of_pos (inv_pos.mpr h1t)
  have heq : (1 - t)⁻¹ - 1 = t / (1 - t) := by
    field_simp
    ring
  have hfrac : t / (1 - t) ≤ 2 * t := by
    rw [div_le_iff₀ h1t]
    nlinarith
  linarith

/-- **The effective Mertens lower bound**: `log log(M+1) ≤ 2·∑_{p ≤ M} 1/p`.  Euler's
product domination, the banked harmonic lower bound, and the elementary logarithm
estimate — fully explicit constants. -/
theorem mertens_lower {M : ℕ} (hM : 1 ≤ M) :
    Real.log (Real.log ((M : ℝ) + 1)) ≤ 2 * ∑ p ∈ Nat.primesBelow (M + 1), (p : ℝ)⁻¹ := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hHpos : 0 < Real.log ((M : ℝ) + 1) := Real.log_pos (by linarith)
  have hH := harmonic_Icc_ge_log M
  have hprod := harmonic_le_prod_primesBelow M
  have hfacpos : ∀ p ∈ Nat.primesBelow (M + 1), (0 : ℝ) < (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      calc (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
        _ = 1 / 2 := by norm_num
    exact inv_pos.mpr (by linarith)
  calc Real.log (Real.log ((M : ℝ) + 1))
      ≤ Real.log (∑ n ∈ Finset.Icc 1 M, 1 / (n : ℝ)) := Real.log_le_log hHpos hH
    _ ≤ Real.log (∏ p ∈ Nat.primesBelow (M + 1), (1 - (p : ℝ)⁻¹)⁻¹) :=
        Real.log_le_log (by linarith) hprod
    _ = ∑ p ∈ Nat.primesBelow (M + 1), Real.log ((1 - (p : ℝ)⁻¹)⁻¹) :=
        Real.log_prod (fun p hp => (hfacpos p hp).ne')
    _ ≤ ∑ p ∈ Nat.primesBelow (M + 1), 2 * (p : ℝ)⁻¹ := by
        refine Finset.sum_le_sum fun p hp => ?_
        have hpp := (Nat.mem_primesBelow.mp hp).2
        have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
        refine log_inv_one_sub_le (by positivity) ?_
        calc (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
          _ = 1 / 2 := by norm_num
    _ = 2 * ∑ p ∈ Nat.primesBelow (M + 1), (p : ℝ)⁻¹ := by rw [Finset.mul_sum]

/-- **The closed-form cutoff constraint.**  Combining the forced prime mass with the
effective Mertens lower bound: any Lipschitz line-crossing datum forces the cutoff under
the double exponential `√N + 1 < exp exp(4(1 + 1/(2σ₂-1)))` — the explicit reach of
budget technology, in closed form. -/
theorem line_crossing_cutoff_lt_expexp {σ₂ : ℝ} (hσ₂ : 1 / 2 < σ₂) {N : ℕ}
    (hN : 1 ≤ Nat.sqrt N) {t₀ ε₁ τ : ℝ} (hε₁ : 0 < ε₁)
    (hline : t₀ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) ((σ₂ : ℂ) + (τ : ℂ) * I)‖)
    (hbudget : lineBudget σ₂ N ≤ t₀ - ε₁) :
    ((Nat.sqrt N : ℝ)) + 1 < Real.exp (Real.exp (4 * (1 + 1 / (2 * σ₂ - 1)))) := by
  have hmass := line_crossing_cutoff_primeMass_lt hσ₂ hε₁ hline hbudget
  have hmert := mertens_lower hN
  have hN1 : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hN
  have h1 : Real.log (Real.log ((Nat.sqrt N : ℝ) + 1)) < 4 * (1 + 1 / (2 * σ₂ - 1)) := by
    linarith
  have hpos1 : 0 < Real.log ((Nat.sqrt N : ℝ) + 1) := Real.log_pos (by linarith)
  have h2 : Real.log ((Nat.sqrt N : ℝ) + 1)
      < Real.exp (4 * (1 + 1 / (2 * σ₂ - 1))) := by
    have := Real.exp_lt_exp.mpr h1
    rwa [Real.exp_log hpos1] at this
  have h3 := Real.exp_lt_exp.mpr h2
  rwa [Real.exp_log (by positivity : (0 : ℝ) < (Nat.sqrt N : ℝ) + 1)] at h3

/-! ## The budget as a certified Mertens-mass meter -/

/-- Harmonic upper bound: `∑_{k ∈ [1,M]} 1/k ≤ 1 + log M`, by the integral test. -/
theorem sum_Icc_one_div_le {M : ℕ} (hM : 1 ≤ M) :
    ∑ k ∈ Finset.Icc 1 M, 1 / (k : ℝ) ≤ 1 + Real.log M := by
  rcases M with _ | n
  · omega
  · have hIcc : Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 2) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    rw [hIcc, Finset.sum_Ico_eq_sum_range, show n + 2 - 1 = n + 1 from rfl,
      Finset.sum_range_succ']
    have h0 : 1 / ((1 + 0 : ℕ) : ℝ) = 1 := by norm_num
    have hant : AntitoneOn (fun x : ℝ => 1 / x) (Set.Icc 1 (1 + (n : ℝ))) :=
      fun x hx _ _ hxy => one_div_le_one_div_of_le (lt_of_lt_of_le one_pos hx.1) hxy
    have heval : ∫ x in (1 : ℝ)..(1 + (n : ℝ)), 1 / x = Real.log ((n : ℝ) + 1) := by
      rw [integral_one_div (fun h => by
        rcases Set.mem_uIcc.mp h with ⟨h1, _⟩ | ⟨_, h2⟩ <;>
          nlinarith [Nat.cast_nonneg (α := ℝ) n]), div_one]
      ring_nf
    have hsum : ∑ i ∈ Finset.range n, 1 / ((1 + (i + 1) : ℕ) : ℝ)
        ≤ Real.log ((n : ℝ) + 1) := by
      rw [← heval]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
        hant.sum_le_integral
      congr 1
      push_cast
      ring
    rw [h0]
    have hlog : Real.log ((n : ℝ) + 1) = Real.log ((n + 1 : ℕ) : ℝ) := by push_cast; ring_nf
    linarith [hsum, hlog.ge, hlog.le]

/-- The line budget in square coordinates: it is exactly the Möbius-weighted reciprocal
defect sum over `[1, √N]`. -/
theorem lineBudget_eq_sum_sqrt (σ₂ : ℝ) (N : ℕ) :
    lineBudget σ₂ N = ∑ k ∈ Finset.Icc 1 (Nat.sqrt N),
      |((ArithmeticFunction.moebius k : ℤ) : ℝ)| *
        |(k : ℝ)⁻¹ - (k : ℝ) ^ (-(2 * σ₂))| := by
  rw [lineBudget,
    ← Finset.sum_filter_of_ne (p := fun n => n.sqrt * n.sqrt = n) (fun x _ hx => ?_)]
  · refine Finset.sum_nbij' (fun n => n.sqrt) (fun k => k * k) ?_ ?_ ?_ ?_ ?_
    · intro n hn
      obtain ⟨hn1, hnsq⟩ := Finset.mem_filter.mp hn
      obtain ⟨h1n, hnN⟩ := Finset.mem_Icc.mp hn1
      exact Finset.mem_Icc.mpr ⟨Nat.le_sqrt.mpr (by omega), Nat.sqrt_le_sqrt hnN⟩
    · intro k hk
      obtain ⟨h1k, hkN⟩ := Finset.mem_Icc.mp hk
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr (by positivity), Nat.le_sqrt.mp hkN⟩, ?_⟩
      show (k * k).sqrt * (k * k).sqrt = k * k
      rw [Nat.sqrt_eq]
    · intro n hn
      exact (Finset.mem_filter.mp hn).2
    · intro k _
      show (k * k).sqrt = k
      exact Nat.sqrt_eq k
    · intro n hn
      obtain ⟨-, hnsq⟩ := Finset.mem_filter.mp hn
      conv_lhs => rw [← hnsq]
      have hcoeff : sqrtMoebiusCoeff (n.sqrt * n.sqrt)
          = ((ArithmeticFunction.moebius n.sqrt : ℤ) : ℝ) := by
        rw [sqrtMoebiusCoeff, sqrtPart_apply_mul_self]
      have hpow1 : ((n.sqrt * n.sqrt : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
          = ((n.sqrt : ℕ) : ℝ)⁻¹ := by
        rw [show n.sqrt * n.sqrt = n.sqrt ^ 2 from (pow_two n.sqrt).symm, natCast_sq_rpow,
          show (2 : ℝ) * -(1 / 2) = -1 by norm_num, Real.rpow_neg_one]
      have hpow2 : ((n.sqrt * n.sqrt : ℕ) : ℝ) ^ (-σ₂)
          = ((n.sqrt : ℕ) : ℝ) ^ (-(2 * σ₂)) := by
        rw [show n.sqrt * n.sqrt = n.sqrt ^ 2 from (pow_two n.sqrt).symm, natCast_sq_rpow]
        congr 1
        ring
      rw [hcoeff, hpow1, hpow2]
  · by_contra hpx
    refine hx ?_
    have hzero : sqrtMoebiusCoeff x = 0 := by
      rw [sqrtMoebiusCoeff, sqrtPart_apply_of_not_isSquare]
      · norm_num
      · rintro ⟨r, hr⟩
        refine hpx ?_
        show x.sqrt * x.sqrt = x
        rw [hr, Nat.sqrt_eq]
    rw [hzero, abs_zero, zero_mul]

/-- **The log upper law**: the line budget is at most the squarefree harmonic mass,
`lineBudget σ₂ N ≤ 1 + log √N`. -/
theorem lineBudget_le_one_add_log {σ₂ : ℝ} (hσ₂ : 1 / 2 ≤ σ₂) {N : ℕ}
    (hN : 1 ≤ Nat.sqrt N) :
    lineBudget σ₂ N ≤ 1 + Real.log (Nat.sqrt N) := by
  rw [lineBudget_eq_sum_sqrt]
  refine le_trans (Finset.sum_le_sum fun k hk => ?_) (sum_Icc_one_div_le hN)
  obtain ⟨h1k, hkS⟩ := Finset.mem_Icc.mp hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1k
  have habs : |((ArithmeticFunction.moebius k : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have hord : (k : ℝ) ^ (-(2 * σ₂)) ≤ (k : ℝ)⁻¹ := by
    have h := Real.rpow_le_rpow_of_exponent_le hk1 (show -(2 * σ₂) ≤ -1 by linarith)
    rwa [Real.rpow_neg_one] at h
  have hnn : (0 : ℝ) ≤ (k : ℝ) ^ (-(2 * σ₂)) := Real.rpow_nonneg (by positivity) _
  calc |((ArithmeticFunction.moebius k : ℤ) : ℝ)| * |(k : ℝ)⁻¹ - (k : ℝ) ^ (-(2 * σ₂))|
      ≤ 1 * |(k : ℝ)⁻¹ - (k : ℝ) ^ (-(2 * σ₂))| :=
        mul_le_mul_of_nonneg_right habs (abs_nonneg _)
    _ = (k : ℝ)⁻¹ - (k : ℝ) ^ (-(2 * σ₂)) := by
        rw [one_mul, abs_of_nonneg (by linarith)]
    _ ≤ 1 / (k : ℝ) := by
        rw [one_div]
        linarith

/-- **The budget as a certified Mertens-mass meter**: the prime mass up to `√N` is pinned
between the explicit log-log law and the budget-plus-cap reading. -/
theorem lineBudget_measures_primeMass {σ₂ : ℝ} (hσ₂ : 1 / 2 < σ₂) {N : ℕ}
    (hN : 1 ≤ Nat.sqrt N) :
    (1 / 2) * Real.log (Real.log ((Nat.sqrt N : ℝ) + 1))
        ≤ ∑ p ∈ Nat.primesBelow (Nat.sqrt N + 1), (p : ℝ)⁻¹
      ∧ ∑ p ∈ Nat.primesBelow (Nat.sqrt N + 1), (p : ℝ)⁻¹
        ≤ lineBudget σ₂ N + (1 + 1 / (2 * σ₂ - 1)) :=
  ⟨by linarith [mertens_lower hN], primeMass_le_lineBudget_add hσ₂ N⟩

/-- **The two-sided budget bracket**: the line budget sits between the explicit log-log
lower law (its forced prime mass) and the explicit log upper law (its total squarefree
mass). -/
theorem lineBudget_bracket {σ₂ : ℝ} (hσ₂ : 1 / 2 < σ₂) {N : ℕ} (hN : 1 ≤ Nat.sqrt N) :
    (1 / 2) * Real.log (Real.log ((Nat.sqrt N : ℝ) + 1)) - (1 + 1 / (2 * σ₂ - 1))
        ≤ lineBudget σ₂ N
      ∧ lineBudget σ₂ N ≤ 1 + Real.log (Nat.sqrt N) := by
  obtain ⟨h1, h2⟩ := lineBudget_measures_primeMass hσ₂ hN
  exact ⟨by linarith, lineBudget_le_one_add_log hσ₂.le hN⟩

/-! ## The prime-mass upper law -/

/-- Chebyshev's bound in logarithmic form: `∑_{p ≤ n} log p ≤ n·log 4`, from the
primorial bound `primorial n ≤ 4^n`. -/
theorem sum_primesBelow_log_le (n : ℕ) :
    ∑ p ∈ Nat.primesBelow (n + 1), Real.log p ≤ n * Real.log 4 := by
  have hset : Nat.primesBelow (n + 1) = {p ∈ Finset.range (n + 1) | p.Prime} := by
    ext p
    simp [Nat.mem_primesBelow]
  have hprodeq : ∏ p ∈ Nat.primesBelow (n + 1), (p : ℝ) = ((primorial n : ℕ) : ℝ) := by
    rw [hset, primorial]
    push_cast
    rfl
  have hlogprod : ∑ p ∈ Nat.primesBelow (n + 1), Real.log p
      = Real.log (∏ p ∈ Nat.primesBelow (n + 1), (p : ℝ)) :=
    (Real.log_prod (fun p hp => by
      exact_mod_cast (Nat.mem_primesBelow.mp hp).2.pos.ne')).symm
  rw [hlogprod, hprodeq]
  calc Real.log ((primorial n : ℕ) : ℝ)
      ≤ Real.log ((4 : ℝ) ^ n) :=
        Real.log_le_log (by exact_mod_cast primorial_pos n)
          (by exact_mod_cast primorial_le_four_pow n)
    _ = n * Real.log 4 := by rw [Real.log_pow]

private theorem one_le_log_two_of_prime {p : ℕ} (hp : p.Prime) : 1 ≤ Nat.log 2 p := by
  rcases Nat.eq_zero_or_pos (Nat.log 2 p) with h0 | h1
  · rcases Nat.log_eq_zero_iff.mp h0 with h | h
    · have := hp.two_le
      omega
    · omega
  · exact h1

/-- **The prime-mass upper law**: `∑_{p ≤ x} 1/p ≤ 4·(1 + log(Nat.log 2 x))`.  Dyadic
blocks: the `j`-th block holds at most `2^(j+2)/j` primes by Chebyshev's primorial bound,
each of reciprocal at most `2^(-j)`, so each block carries mass at most `4/j`; the block
count is logarithmic, and the harmonic bound closes. -/
theorem primeMass_upper {x : ℕ} (hx : 2 ≤ x) :
    ∑ p ∈ Nat.primesBelow (x + 1), (p : ℝ)⁻¹ ≤ 4 * (1 + Real.log (Nat.log 2 x)) := by
  have hmaps : ∀ p ∈ Nat.primesBelow (x + 1),
      Nat.log 2 p ∈ Finset.Icc 1 (Nat.log 2 x) := by
    intro p hp
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
    exact Finset.mem_Icc.mpr ⟨one_le_log_two_of_prime hpp, Nat.log_mono_right (by omega)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ j ∈ Finset.Icc 1 (Nat.log 2 x),
      ∑ p ∈ (Nat.primesBelow (x + 1)).filter (fun p => Nat.log 2 p = j), (p : ℝ)⁻¹
        ≤ 4 / j := by
    intro j hj
    obtain ⟨hj1, hjx⟩ := Finset.mem_Icc.mp hj
    set B := (Nat.primesBelow (x + 1)).filter (fun p => Nat.log 2 p = j) with hB
    have hmem : ∀ p ∈ B, 2 ^ j ≤ p ∧ p < 2 ^ (j + 1) ∧ p.Prime := by
      intro p hp
      obtain ⟨hpmem, hlog⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, hpp⟩ := Nat.mem_primesBelow.mp hpmem
      refine ⟨?_, ?_, hpp⟩
      · rw [← hlog]
        exact Nat.pow_log_le_self 2 hpp.pos.ne'
      · rw [← hlog]
        exact Nat.lt_pow_succ_log_self one_lt_two p
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hjpos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have h1 : (B.card : ℝ) * ((j : ℝ) * Real.log 2) ≤ ∑ p ∈ B, Real.log p := by
      rw [show (B.card : ℝ) * ((j : ℝ) * Real.log 2)
          = B.card • ((j : ℝ) * Real.log 2) from by rw [nsmul_eq_mul]]
      refine Finset.card_nsmul_le_sum B _ _ fun p hp => ?_
      obtain ⟨hlow, -, -⟩ := hmem p hp
      calc (j : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ j) := by rw [Real.log_pow]
        _ ≤ Real.log p := Real.log_le_log (by positivity) (by exact_mod_cast hlow)
    have h2 : ∑ p ∈ B, Real.log p ≤ (2 : ℝ) ^ (j + 1) * Real.log 4 := by
      have hsub : B ⊆ Nat.primesBelow (2 ^ (j + 1) - 1 + 1) := by
        intro p hp
        obtain ⟨-, hup, hpp⟩ := hmem p hp
        exact Nat.mem_primesBelow.mpr ⟨by omega, hpp⟩
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ =>
        Real.log_nonneg (by exact_mod_cast (Nat.mem_primesBelow.mp hp).2.one_lt.le)) ?_
      refine le_trans (sum_primesBelow_log_le (2 ^ (j + 1) - 1)) ?_
      have hcast : ((2 ^ (j + 1) - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (j + 1) := by
        rw [Nat.cast_sub (Nat.one_le_two_pow)]
        push_cast
        linarith
      exact mul_le_mul_of_nonneg_right hcast (Real.log_nonneg (by norm_num))
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have hcard' : (B.card : ℝ) ≤ (2 : ℝ) ^ (j + 2) / j := by
      rw [le_div_iff₀ hjpos]
      have hstep : (B.card : ℝ) * (j : ℝ) * Real.log 2 ≤ (2 : ℝ) ^ (j + 2) * Real.log 2 := by
        have h2' : (2 : ℝ) ^ (j + 1) * Real.log 4 = (2 : ℝ) ^ (j + 2) * Real.log 2 := by
          rw [hlog4, show j + 2 = (j + 1) + 1 from rfl, pow_succ]
          ring
        calc (B.card : ℝ) * (j : ℝ) * Real.log 2
            = (B.card : ℝ) * ((j : ℝ) * Real.log 2) := by ring
          _ ≤ ∑ p ∈ B, Real.log p := h1
          _ ≤ (2 : ℝ) ^ (j + 1) * Real.log 4 := h2
          _ = (2 : ℝ) ^ (j + 2) * Real.log 2 := h2'
      exact le_of_mul_le_mul_right hstep hlog2pos
    have hmass : ∑ p ∈ B, (p : ℝ)⁻¹ ≤ (B.card : ℝ) * ((2 : ℝ) ^ j)⁻¹ := by
      rw [show (B.card : ℝ) * ((2 : ℝ) ^ j)⁻¹ = B.card • (((2 : ℝ) ^ j)⁻¹) from by
        rw [nsmul_eq_mul]]
      refine Finset.sum_le_card_nsmul B _ _ fun p hp => ?_
      obtain ⟨hlow, -, -⟩ := hmem p hp
      exact inv_anti₀ (by positivity) (by exact_mod_cast hlow)
    calc ∑ p ∈ B, (p : ℝ)⁻¹
        ≤ (B.card : ℝ) * ((2 : ℝ) ^ j)⁻¹ := hmass
      _ ≤ ((2 : ℝ) ^ (j + 2) / j) * ((2 : ℝ) ^ j)⁻¹ :=
          mul_le_mul_of_nonneg_right hcard' (by positivity)
      _ = 4 / j := by
          rw [show j + 2 = j + 2 from rfl, pow_add]
          field_simp
          ring
  have hL1 : 1 ≤ Nat.log 2 x := by
    have h2 : Nat.log 2 2 ≤ Nat.log 2 x := Nat.log_mono_right hx
    have : Nat.log 2 2 = 1 := by
      rw [Nat.log_eq_one_iff']
      omega
    omega
  calc ∑ j ∈ Finset.Icc 1 (Nat.log 2 x),
        ∑ p ∈ (Nat.primesBelow (x + 1)).filter (fun p => Nat.log 2 p = j), (p : ℝ)⁻¹
      ≤ ∑ j ∈ Finset.Icc 1 (Nat.log 2 x), 4 / (j : ℝ) := Finset.sum_le_sum hblock
    _ = 4 * ∑ j ∈ Finset.Icc 1 (Nat.log 2 x), 1 / (j : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 4 * (1 + Real.log (Nat.log 2 x)) :=
        mul_le_mul_of_nonneg_left (sum_Icc_one_div_le hL1) (by norm_num)

/-- The prime-mass upper law in log-log form: `∑_{p ≤ x} 1/p ≤ 4 + 4·log(2·log x)`.
Together with `mertens_lower` this pins the prime mass between two explicit log-log
laws. -/
theorem primeMass_upper_log_log {x : ℕ} (hx : 2 ≤ x) :
    ∑ p ∈ Nat.primesBelow (x + 1), (p : ℝ)⁻¹ ≤ 4 + 4 * Real.log (2 * Real.log x) := by
  refine le_trans (primeMass_upper hx) ?_
  have hL1 : 1 ≤ Nat.log 2 x := by
    have h2 : Nat.log 2 2 ≤ Nat.log 2 x := Nat.log_mono_right hx
    have : Nat.log 2 2 = 1 := by
      rw [Nat.log_eq_one_iff']
      omega
    omega
  have hexphalf : Real.exp (1 / 2) < 2 := by
    have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (1 / 2 : ℝ)]
  have hhalf : (1 / 2 : ℝ) < Real.log 2 := by
    calc (1 / 2 : ℝ) = Real.log (Real.exp (1 / 2)) := (Real.log_exp _).symm
      _ < Real.log 2 := Real.log_lt_log (Real.exp_pos _) hexphalf
  have hkey : ((Nat.log 2 x : ℕ) : ℝ) ≤ 2 * Real.log x := by
    have hpow := Nat.pow_log_le_self 2 (by omega : x ≠ 0)
    have hlogle : (Nat.log 2 x : ℝ) * Real.log 2 ≤ Real.log x := by
      rw [show (Nat.log 2 x : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ Nat.log 2 x) by
        rw [Real.log_pow]]
      exact Real.log_le_log (by positivity) (by exact_mod_cast hpow)
    nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.log 2 x)]
  have hmono : Real.log (Nat.log 2 x) ≤ Real.log (2 * Real.log x) :=
    Real.log_le_log (by exact_mod_cast hL1) hkey
  linarith

/-! ## The sharp Mertens lower bound: coefficient one -/

/-- The telescoping correction: `∑_{p ≤ x} 1/(p(p-1)) ≤ 1`. -/
theorem sum_primesBelow_inv_mul_sub_one_le (x : ℕ) :
    ∑ p ∈ Nat.primesBelow x, 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  have hsub : Nat.primesBelow x ⊆ Finset.Icc 2 x := by
    intro p hp
    obtain ⟨hplt, hpp⟩ := Nat.mem_primesBelow.mp hp
    exact Finset.mem_Icc.mpr ⟨hpp.two_le, by omega⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => ?_) ?_
  · have h2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have : (1 : ℝ) ≤ (k : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2
      linarith
    positivity
  · rcases Nat.lt_or_ge x 2 with hx | hx
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      norm_num
    · have hIcc : Finset.Icc 2 x = Finset.Ico 2 (x + 1) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      have hterm : ∀ i ∈ Finset.range (x + 1 - 2),
          1 / (((2 + i : ℕ) : ℝ) * (((2 + i : ℕ) : ℝ) - 1))
            = 1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2) := by
        intro i _
        have h1 : ((i : ℝ) + 1) ≠ 0 := by positivity
        have h2 : ((i : ℝ) + 2) ≠ 0 := by positivity
        push_cast
        rw [div_sub_div _ _ h1 h2]
        congr 1
        · ring
        · ring
      have htele : ∑ i ∈ Finset.range (x + 1 - 2), (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2))
          = 1 / ((0 : ℕ) + 1 : ℝ) - 1 / (((x + 1 - 2 : ℕ) : ℝ) + 1) := by
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_)
          (Finset.sum_range_sub' (f := fun j : ℕ => 1 / ((j : ℝ) + 1)) (n := x + 1 - 2))
        push_cast
        ring
      rw [Finset.sum_congr rfl hterm, htele]
      have hpos : (0 : ℝ) ≤ 1 / (((x + 1 - 2 : ℕ) : ℝ) + 1) := by positivity
      norm_num
      linarith

/-- The sharp per-prime logarithm estimate:
`log((1-p⁻¹)⁻¹) ≤ 1/p + 1/(p(p-1))`, exactly the reciprocal plus the telescoping
correction. -/
theorem log_inv_one_sub_inv_le {p : ℕ} (hp : 2 ≤ p) :
    Real.log (1 - (p : ℝ)⁻¹)⁻¹ ≤ (p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have ht : (0 : ℝ) < 1 - (p : ℝ)⁻¹ := by
    have : (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hp2
    have h2 : (2 : ℝ)⁻¹ < 1 := by norm_num
    linarith
  have hle := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  have heq : (1 - (p : ℝ)⁻¹)⁻¹ - 1 = (p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    have hpm1 : ((p : ℝ) - 1) ≠ 0 := by linarith
    field_simp
    ring
  linarith

/-- **The sharp effective Mertens lower bound**: `log log(M+1) ≤ ∑_{p ≤ M} 1/p + 1` —
coefficient one on the prime mass, the multiplicative constant of `mertens_lower`
replaced by a telescoped additive constant. -/
theorem mertens_lower_add_one {M : ℕ} (hM : 1 ≤ M) :
    Real.log (Real.log ((M : ℝ) + 1))
      ≤ (∑ p ∈ Nat.primesBelow (M + 1), (p : ℝ)⁻¹) + 1 := by
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hHpos : 0 < Real.log ((M : ℝ) + 1) := Real.log_pos (by linarith)
  have hH := harmonic_Icc_ge_log M
  have hprod := harmonic_le_prod_primesBelow M
  have hfacpos : ∀ p ∈ Nat.primesBelow (M + 1), (0 : ℝ) < (1 - (p : ℝ)⁻¹)⁻¹ := by
    intro p hp
    have hpp := (Nat.mem_primesBelow.mp hp).2
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hhalf : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      calc (p : ℝ)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h2
        _ = 1 / 2 := by norm_num
    exact inv_pos.mpr (by linarith)
  calc Real.log (Real.log ((M : ℝ) + 1))
      ≤ Real.log (∑ n ∈ Finset.Icc 1 M, 1 / (n : ℝ)) := Real.log_le_log hHpos hH
    _ ≤ Real.log (∏ p ∈ Nat.primesBelow (M + 1), (1 - (p : ℝ)⁻¹)⁻¹) :=
        Real.log_le_log (by linarith) hprod
    _ = ∑ p ∈ Nat.primesBelow (M + 1), Real.log ((1 - (p : ℝ)⁻¹)⁻¹) :=
        Real.log_prod (fun p hp => (hfacpos p hp).ne')
    _ ≤ ∑ p ∈ Nat.primesBelow (M + 1),
          ((p : ℝ)⁻¹ + 1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        Finset.sum_le_sum fun p hp =>
          log_inv_one_sub_inv_le (Nat.mem_primesBelow.mp hp).2.two_le
    _ = (∑ p ∈ Nat.primesBelow (M + 1), (p : ℝ)⁻¹)
          + ∑ p ∈ Nat.primesBelow (M + 1), 1 / ((p : ℝ) * ((p : ℝ) - 1)) :=
        Finset.sum_add_distrib
    _ ≤ (∑ p ∈ Nat.primesBelow (M + 1), (p : ℝ)⁻¹) + 1 := by
        linarith [sum_primesBelow_inv_mul_sub_one_le (M + 1)]

/-- **The sharp closed-form cutoff constraint**: with the coefficient-one Mertens bound,
any Lipschitz line-crossing datum forces `√N + 1 < exp exp(2(1 + 1/(2σ₂-1)) + 1)` — the
exponent of `line_crossing_cutoff_lt_expexp` halved up to the telescoped constant. -/
theorem line_crossing_cutoff_lt_expexp' {σ₂ : ℝ} (hσ₂ : 1 / 2 < σ₂) {N : ℕ}
    (hN : 1 ≤ Nat.sqrt N) {t₀ ε₁ τ : ℝ} (hε₁ : 0 < ε₁)
    (hline : t₀ < ‖dpoly2 sqrtMoebiusCoeff (Finset.Icc 1 N) ((σ₂ : ℂ) + (τ : ℂ) * I)‖)
    (hbudget : lineBudget σ₂ N ≤ t₀ - ε₁) :
    ((Nat.sqrt N : ℝ)) + 1 < Real.exp (Real.exp (2 * (1 + 1 / (2 * σ₂ - 1)) + 1)) := by
  have hmass := line_crossing_cutoff_primeMass_lt hσ₂ hε₁ hline hbudget
  have hmert := mertens_lower_add_one hN
  have hN1 : (1 : ℝ) ≤ (Nat.sqrt N : ℝ) := by exact_mod_cast hN
  have h1 : Real.log (Real.log ((Nat.sqrt N : ℝ) + 1))
      < 2 * (1 + 1 / (2 * σ₂ - 1)) + 1 := by linarith
  have hpos1 : 0 < Real.log ((Nat.sqrt N : ℝ) + 1) := Real.log_pos (by linarith)
  have h2 : Real.log ((Nat.sqrt N : ℝ) + 1)
      < Real.exp (2 * (1 + 1 / (2 * σ₂ - 1)) + 1) := by
    have := Real.exp_lt_exp.mpr h1
    rwa [Real.exp_log hpos1] at this
  have h3 := Real.exp_lt_exp.mpr h2
  rwa [Real.exp_log (by positivity : (0 : ℝ) < (Nat.sqrt N : ℝ) + 1)] at h3

end RHTower
