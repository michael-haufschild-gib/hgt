import GaloisForLFunctions.HTGeometry.LatticePolynomialWeight

/-!
# Exponential lattice weights survive a polynomial factor

A geometric weight in the `ℓ¹` length beats any fixed polynomial factor:

`Σ_{ν ∈ ℤ^d} (1 + |ν|₁)^N r^{|ν|₁} < ∞`   for `0 ≤ r < 1`.

Both factors split over the coordinates — exactly for the geometric one, and by
`1 + Σ aᵢ ≤ ∏ (1 + aᵢ)` for the polynomial one — so the whole weight is dominated by a product of
one-dimensional geometric-times-polynomial weights, and the product of summable nonnegative weights
over a finite index is summable by induction on the rank.

This is the summability that a finite recurrence type asks for: with `τ_ν ≤ R|ν|₁ + c` and
`2κ > 2σR`, the source weight `e^{-2κ|ν|₁} e^{2στ_ν}(1+τ_ν)^N` is of exactly this shape.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## One dimension -/

theorem summable_nat_polyGeom (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun n : ℕ => (1 + (n : ℝ)) ^ N * r ^ n := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have hgeom : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr
  have hpow : Summable fun n : ℕ => (n : ℝ) ^ N * r ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one N hnorm
  have hmaj : Summable fun n : ℕ => (2 : ℝ) ^ N * (r ^ n) + (2 : ℝ) ^ N * ((n : ℝ) ^ N * r ^ n) :=
    (hgeom.mul_left _).add (hpow.mul_left _)
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hr0n : (0 : ℝ) ≤ r ^ n := pow_nonneg hr0 n
  have hbase : (1 + (n : ℝ)) ^ N ≤ (2 : ℝ) ^ N * (1 + (n : ℝ) ^ N) := by
    rcases le_or_gt (n : ℝ) 1 with hle | hgt
    · have h1 : (1 + (n : ℝ)) ^ N ≤ (2 : ℝ) ^ N :=
        pow_le_pow_left₀ (by linarith) (by linarith) N
      nlinarith [pow_nonneg hn N, pow_pos (by norm_num : (0:ℝ) < 2) N]
    · have h1 : (1 + (n : ℝ)) ^ N ≤ (2 * (n : ℝ)) ^ N :=
        pow_le_pow_left₀ (by linarith) (by linarith) N
      have h2 : (2 * (n : ℝ)) ^ N = (2 : ℝ) ^ N * (n : ℝ) ^ N := by
        rw [mul_pow]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)) N]
  calc (1 + (n : ℝ)) ^ N * r ^ n
      ≤ ((2 : ℝ) ^ N * (1 + (n : ℝ) ^ N)) * r ^ n :=
        mul_le_mul_of_nonneg_right hbase hr0n
    _ = (2 : ℝ) ^ N * (r ^ n) + (2 : ℝ) ^ N * ((n : ℝ) ^ N * r ^ n) := by ring

theorem summable_int_polyGeom (N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun k : ℤ => (1 + ((k.natAbs : ℕ) : ℝ)) ^ N * r ^ k.natAbs := by
  refine Summable.of_nat_of_neg
    (f := fun k : ℤ => (1 + ((k.natAbs : ℕ) : ℝ)) ^ N * r ^ k.natAbs) ?_ ?_
  · refine (summable_nat_polyGeom N hr0 hr).congr fun n => ?_
    simp
  · refine (summable_nat_polyGeom N hr0 hr).congr fun n => ?_
    simp

/-! ## The product weight -/

set_option maxHeartbeats 1000000 in
theorem summable_prod_polyGeom (d N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun ν : Fin d → ℤ =>
      ∏ i, (1 + (((ν i).natAbs : ℕ) : ℝ)) ^ N * r ^ (ν i).natAbs := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
      have hprod : Summable
          (fun p : ℤ × (Fin d → ℤ) =>
            ((1 + (((p.1).natAbs : ℕ) : ℝ)) ^ N * r ^ (p.1).natAbs) *
              ∏ i, (1 + (((p.2 i).natAbs : ℕ) : ℝ)) ^ N * r ^ (p.2 i).natAbs) :=
        Summable.mul_of_nonneg (summable_int_polyGeom N hr0 hr) ih
          (fun _ => by positivity)
          (fun _ => Finset.prod_nonneg fun i _ => by positivity)
      refine (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ))).mp ?_
      refine hprod.congr fun p => ?_
      simp [Fin.consEquiv, Fin.prod_univ_succ]

/-! ## Splitting the polynomial factor -/

theorem one_add_sum_le_prod : ∀ {d : ℕ} (a : Fin d → ℝ), (∀ i, 0 ≤ a i) →
    1 + ∑ i, a i ≤ ∏ i, (1 + a i) := by
  intro d
  induction d with
  | zero => intro a _; simp
  | succ d ih =>
      intro a ha
      have hrest := ih (fun i : Fin d => a i.succ) (fun i => ha i.succ)
      have h0 : 0 ≤ a 0 := ha 0
      have hsum : (0 : ℝ) ≤ ∑ i : Fin d, a i.succ :=
        Finset.sum_nonneg fun i _ => ha i.succ
      rw [Fin.sum_univ_succ, Fin.prod_univ_succ]
      nlinarith [hrest, h0, hsum]

/-! ## The lattice weight -/

/-- **The exponential lattice weight absorbs any polynomial factor.** -/
theorem summable_latticeExpPoly (d N : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable fun ν : Fin d → ℤ =>
      (1 + latticeEll1 ν) ^ N * r ^ (∑ i, ((ν i).natAbs)) := by
  refine Summable.of_nonneg_of_le (fun ν => ?_) (fun ν => ?_)
    (summable_prod_polyGeom d N hr0 hr)
  · have h1 : (0 : ℝ) ≤ 1 + latticeEll1 ν := by linarith [latticeEll1_nonneg ν]
    exact mul_nonneg (pow_nonneg h1 N) (pow_nonneg hr0 _)
  have hsplitGeom : r ^ (∑ i, ((ν i).natAbs)) = ∏ i, r ^ (ν i).natAbs := by
    rw [Finset.prod_pow_eq_pow_sum]
  have hell : latticeEll1 ν = ∑ i, (((ν i).natAbs : ℕ) : ℝ) := by
    rw [latticeEll1]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hpoly : (1 + latticeEll1 ν) ^ N ≤ ∏ i, (1 + (((ν i).natAbs : ℕ) : ℝ)) ^ N := by
    have hstep : (1 + latticeEll1 ν) ≤ ∏ i, (1 + (((ν i).natAbs : ℕ) : ℝ)) := by
      rw [hell]
      exact one_add_sum_le_prod _ fun i => by positivity
    calc (1 + latticeEll1 ν) ^ N
        ≤ (∏ i, (1 + (((ν i).natAbs : ℕ) : ℝ))) ^ N :=
          pow_le_pow_left₀ (by linarith [latticeEll1_nonneg ν]) hstep N
      _ = ∏ i, (1 + (((ν i).natAbs : ℕ) : ℝ)) ^ N := (Finset.prod_pow _ _ _).symm
  calc (1 + latticeEll1 ν) ^ N * r ^ (∑ i, ((ν i).natAbs))
      ≤ (∏ i, (1 + (((ν i).natAbs : ℕ) : ℝ)) ^ N) * ∏ i, r ^ (ν i).natAbs := by
        rw [hsplitGeom]
        exact mul_le_mul_of_nonneg_right hpoly (Finset.prod_nonneg fun i _ => pow_nonneg hr0 _)
    _ = ∏ i, (1 + (((ν i).natAbs : ℕ) : ℝ)) ^ N * r ^ (ν i).natAbs := by
        rw [← Finset.prod_mul_distrib]


/-! ## The recurrence source weight -/

theorem latticeEll1_eq_sum_natAbs {d : ℕ} (ν : Fin d → ℤ) :
    latticeEll1 ν = ∑ i, (((ν i).natAbs : ℕ) : ℝ) := by
  rw [latticeEll1]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp

theorem exp_mul_latticeEll1 {d : ℕ} (a : ℝ) (ν : Fin d → ℤ) :
    Real.exp (a * latticeEll1 ν) = (Real.exp a) ^ (∑ i, ((ν i).natAbs)) := by
  rw [latticeEll1_eq_sum_natAbs, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **`(21)`: the finite-recurrence source weight is summable.**  A recurrence clock growing at most
linearly in the `ℓ¹` length is absorbed by an exponential weight of strictly larger slope, together
with any fixed polynomial factor in the clock. -/
theorem summable_recurrenceSourceWeight {d N : ℕ} {κ σ R c : ℝ}
    (hσ : 0 ≤ σ) (hR : 0 ≤ R) (hc : 0 ≤ c) (hgap : σ * R < κ)
    (τ : (Fin d → ℤ) → ℝ) (hτ0 : ∀ ν, 0 ≤ τ ν)
    (hτ : ∀ ν, τ ν ≤ R * latticeEll1 ν + c) :
    Summable fun ν : Fin d → ℤ =>
      Real.exp (-(2 * κ) * latticeEll1 ν) * Real.exp (2 * σ * τ ν) * (1 + τ ν) ^ N := by
  set r : ℝ := Real.exp (2 * σ * R - 2 * κ) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr : r < 1 := by
    rw [hrdef, Real.exp_lt_one_iff]
    nlinarith [hgap]
  set K : ℝ := Real.exp (2 * σ * c) * ((1 + c) ^ N * (1 + R) ^ N) with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine Summable.of_nonneg_of_le (fun ν => ?_) (fun ν => ?_)
    (((summable_latticeExpPoly d N hr0 hr).mul_left K))
  · have hb : (0 : ℝ) ≤ 1 + τ ν := by linarith [hτ0 ν]
    exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (pow_nonneg hb N)
  have hell0 : 0 ≤ latticeEll1 ν := latticeEll1_nonneg ν
  have hτν := hτ ν
  have hτ0ν := hτ0 ν
  -- the exponential factor
  have hexp : Real.exp (2 * σ * τ ν) ≤ Real.exp (2 * σ * (R * latticeEll1 ν + c)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hexpsplit : Real.exp (-(2 * κ) * latticeEll1 ν)
      * Real.exp (2 * σ * (R * latticeEll1 ν + c))
      = Real.exp (2 * σ * c) * r ^ (∑ i, ((ν i).natAbs)) := by
    rw [hrdef, ← exp_mul_latticeEll1, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  -- the polynomial factor
  have hpoly : (1 + τ ν) ^ N ≤ ((1 + c) ^ N * (1 + R) ^ N) * (1 + latticeEll1 ν) ^ N := by
    have hstep : 1 + τ ν ≤ (1 + c) * (1 + R) * (1 + latticeEll1 ν) := by
      nlinarith [hτν, hell0, hR, hc, mul_nonneg hc hR, mul_nonneg hc hell0,
        mul_nonneg (mul_nonneg hc hR) hell0, mul_nonneg hR hell0]
    calc (1 + τ ν) ^ N ≤ ((1 + c) * (1 + R) * (1 + latticeEll1 ν)) ^ N :=
          pow_le_pow_left₀ (by linarith) hstep N
      _ = ((1 + c) ^ N * (1 + R) ^ N) * (1 + latticeEll1 ν) ^ N := by
          rw [mul_pow, mul_pow]
  have hnn1 : (0 : ℝ) ≤ Real.exp (-(2 * κ) * latticeEll1 ν) := (Real.exp_pos _).le
  have hnn2 : (0 : ℝ) ≤ (1 + τ ν) ^ N := by positivity
  calc Real.exp (-(2 * κ) * latticeEll1 ν) * Real.exp (2 * σ * τ ν) * (1 + τ ν) ^ N
      ≤ Real.exp (-(2 * κ) * latticeEll1 ν) * Real.exp (2 * σ * (R * latticeEll1 ν + c))
          * (((1 + c) ^ N * (1 + R) ^ N) * (1 + latticeEll1 ν) ^ N) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hexp hnn1) hpoly hnn2 ?_
        exact mul_nonneg hnn1 (Real.exp_pos _).le
    _ = K * ((1 + latticeEll1 ν) ^ N * r ^ (∑ i, ((ν i).natAbs))) := by
        rw [hexpsplit, hKdef]
        ring

end GaloisForLFunctions.HTGeometry
