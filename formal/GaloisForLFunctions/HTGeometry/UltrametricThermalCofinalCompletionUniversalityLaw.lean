import GaloisForLFunctions.HTGeometry.UltrametricThermalMahler
import GaloisForLFunctions.HTGeometry.UltrametricThermalTruncation

/-!
# Ultrametric thermal cofinal-completion universality

Finite thermal shell truncations and the unique infinite Mahler signal were previously separate.
This module constructs the canonical polynomial prefix at every shell depth and proves an exact
prefix--tail decomposition of the infinite signal.  The tail is not an unspecified remainder: it
is one scaled substitution of the original branching signal.  Every solution of the affine
Mahler constraint has this same decomposition.
-/

open PowerSeries
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- First `N` terms of the geometrically weighted branching signal. -/
def branchingThermalPrefix (p N : ℕ) : ℂ⟦X⟧ :=
  ∑ k ∈ Finset.range N,
    PowerSeries.C ((p : ℂ) ^ k) * PowerSeries.X ^ (p ^ k)

/-- Exact cofinal tail after the first `N` branching shells. -/
def branchingThermalTail (p N : ℕ) : ℂ⟦X⟧ :=
  PowerSeries.C ((p : ℂ) ^ N) *
    PowerSeries.subst (PowerSeries.X ^ (p ^ N)) (branchingThermalSignal p)

/-- Peeling one tail shell leaves the next substituted tail exactly. -/
theorem branchingThermalTail_succ
    {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    branchingThermalTail p N =
      PowerSeries.C ((p : ℂ) ^ N) * PowerSeries.X ^ (p ^ N) +
        branchingThermalTail p (N + 1) := by
  rw [branchingThermalTail, branchingThermalTail]
  nth_rewrite 1 [branchingThermalSignal_constraint hp]
  have hpn : p ^ N ≠ 0 := pow_ne_zero _ (by omega : p ≠ 0)
  have hp0 : p ≠ 0 := by omega
  rw [PowerSeries.subst_add (PowerSeries.HasSubst.X_pow hpn)]
  rw [PowerSeries.subst_X (PowerSeries.HasSubst.X_pow hpn)]
  rw [PowerSeries.subst_mul (PowerSeries.HasSubst.X_pow hpn)]
  rw [PowerSeries.subst_C]
  rw [PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.X_pow hp0) (PowerSeries.HasSubst.X_pow hpn)]
  rw [PowerSeries.subst_pow (PowerSeries.HasSubst.X_pow hpn)]
  rw [PowerSeries.subst_X (PowerSeries.HasSubst.X_pow hpn)]
  rw [← pow_mul, ← pow_succ]
  rw [mul_add]
  change PowerSeries.C ((p : ℂ) ^ N) * PowerSeries.X ^ (p ^ N) +
      PowerSeries.C ((p : ℂ) ^ N) *
        (PowerSeries.C (p : ℂ) *
          PowerSeries.subst (PowerSeries.X ^ (p ^ (N + 1))) (branchingThermalSignal p)) =
    PowerSeries.C ((p : ℂ) ^ N) * PowerSeries.X ^ (p ^ N) +
      PowerSeries.C ((p : ℂ) ^ (N + 1)) *
        PowerSeries.subst (PowerSeries.X ^ (p ^ (N + 1))) (branchingThermalSignal p)
  rw [← mul_assoc, ← map_mul]
  rw [pow_succ]
  rw [pow_succ]

/-- Every cofinal cut of the branching signal has an exact prefix plus substituted-tail form. -/
theorem branchingThermalSignal_eq_prefix_add_tail
    {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    branchingThermalSignal p = branchingThermalPrefix p N + branchingThermalTail p N := by
  induction N with
  | zero => simp [branchingThermalPrefix, branchingThermalTail]
  | succ N ih =>
      rw [ih, branchingThermalTail_succ hp N]
      rw [branchingThermalPrefix, branchingThermalPrefix, Finset.sum_range_succ]
      abel

/-- Polynomial whose value at `w` is the finite thermal shell truncation. -/
def ultrametricThermalTruncationPolynomial (p N : ℕ) : Polynomial ℂ :=
  Polynomial.C ((p : ℂ) - 2) * Polynomial.X +
    ∑ k ∈ Finset.range N,
      Polynomial.C ((((p : ℂ) - 1) ^ (2 : ℕ)) * (p : ℂ) ^ k) *
        Polynomial.X ^ (p ^ (k + 1))

/-- Formal power-series image of the finite thermal truncation polynomial. -/
def ultrametricThermalPrefixSeries (p N : ℕ) : ℂ⟦X⟧ :=
  (ultrametricThermalTruncationPolynomial p N : ℂ⟦X⟧)

/-- The polynomial prefix realizes every scalar truncation exactly. -/
theorem eval_ultrametricThermalTruncationPolynomial (p N : ℕ) (w : ℂ) :
    (ultrametricThermalTruncationPolynomial p N).eval w =
      ultrametricThermalTruncation p w N := by
  simp [ultrametricThermalTruncationPolynomial, ultrametricThermalTruncation,
    ultrametricThermalShell, Polynomial.eval_finsetSum]

/-- The finite thermal polynomial is the corresponding affine transform of the branching prefix. -/
theorem ultrametricThermalPrefixSeries_eq_branchingPrefix
    {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    ultrametricThermalPrefixSeries p N =
      PowerSeries.C (-1 / (p : ℂ)) * PowerSeries.X +
        PowerSeries.C ((((p : ℂ) - 1) ^ (2 : ℕ)) / (p : ℂ)) *
          branchingThermalPrefix p (N + 1) := by
  rw [ultrametricThermalPrefixSeries, ultrametricThermalTruncationPolynomial,
    branchingThermalPrefix, Finset.sum_range_succ']
  push_cast
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  have hcoe :
      ((∑ k ∈ Finset.range N,
          Polynomial.C ((((p : ℂ) - 1) ^ (2 : ℕ)) * (p : ℂ) ^ k) *
            Polynomial.X ^ (p ^ (k + 1)) : Polynomial ℂ) : ℂ⟦X⟧) =
        ∑ k ∈ Finset.range N,
          PowerSeries.C ((((p : ℂ) - 1) ^ (2 : ℕ)) * (p : ℂ) ^ k) *
            PowerSeries.X ^ (p ^ (k + 1)) := by
    change Polynomial.coeToPowerSeries.ringHom
        (∑ k ∈ Finset.range N,
          Polynomial.C ((((p : ℂ) - 1) ^ (2 : ℕ)) * (p : ℂ) ^ k) *
            Polynomial.X ^ (p ^ (k + 1))) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_mul, map_pow]
    simp only [Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_X]
  let A : ℂ := ((p : ℂ) - 1) ^ (2 : ℕ)
  have hbase :
      PowerSeries.C ((p : ℂ) - 2) * PowerSeries.X =
        PowerSeries.C (-1 / (p : ℂ)) * PowerSeries.X +
          PowerSeries.C (A / (p : ℂ)) * PowerSeries.X := by
    calc
      PowerSeries.C ((p : ℂ) - 2) * PowerSeries.X =
          PowerSeries.C (-1 / (p : ℂ) + A / (p : ℂ)) * PowerSeries.X := by
            congr 2
            dsimp only [A]
            field_simp [hp0]
            ring
      _ = (PowerSeries.C (-1 / (p : ℂ)) +
          PowerSeries.C (A / (p : ℂ))) * PowerSeries.X := by rw [map_add]
      _ = _ := by rw [add_mul]
  have hterm (k : ℕ) :
      PowerSeries.C (A * (p : ℂ) ^ k) * PowerSeries.X ^ (p ^ (k + 1)) =
        PowerSeries.C (A / (p : ℂ)) *
          (PowerSeries.C ((p : ℂ) ^ (k + 1)) *
            PowerSeries.X ^ (p ^ (k + 1))) := by
    calc
      PowerSeries.C (A * (p : ℂ) ^ k) * PowerSeries.X ^ (p ^ (k + 1)) =
          PowerSeries.C ((A / (p : ℂ)) * (p : ℂ) ^ (k + 1)) *
            PowerSeries.X ^ (p ^ (k + 1)) := by
              congr 2
              rw [pow_succ]
              field_simp [hp0]
      _ = (PowerSeries.C (A / (p : ℂ)) *
          PowerSeries.C ((p : ℂ) ^ (k + 1))) *
            PowerSeries.X ^ (p ^ (k + 1)) := by rw [map_mul]
      _ = _ := by ring
  rw [hcoe, mul_add, Finset.mul_sum, hbase]
  have hsum :
      (∑ k ∈ Finset.range N,
        PowerSeries.C (A * (p : ℂ) ^ k) * PowerSeries.X ^ (p ^ (k + 1))) =
      ∑ k ∈ Finset.range N,
        PowerSeries.C (A / (p : ℂ)) *
          (PowerSeries.C ((p : ℂ) ^ (k + 1)) *
            PowerSeries.X ^ (p ^ (k + 1))) :=
    Finset.sum_congr rfl fun k _ => hterm k
  change _ + (∑ k ∈ Finset.range N,
      PowerSeries.C (A * (p : ℂ) ^ k) * PowerSeries.X ^ (p ^ (k + 1))) = _
  rw [hsum]
  simp [A, add_comm]
  abel

/-- The infinite thermal signal is the finite truncation prefix plus one exact cofinal tail. -/
theorem ultrametricThermalSignal_eq_prefix_add_exact_tail
    {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    ultrametricThermalSignal p = ultrametricThermalPrefixSeries p N +
      PowerSeries.C ((((p : ℂ) - 1) ^ (2 : ℕ)) / (p : ℂ)) *
        branchingThermalTail p (N + 1) := by
  rw [ultrametricThermalSignal, ultrametricThermalPrefixSeries_eq_branchingPrefix hp N,
    branchingThermalSignal_eq_prefix_add_tail hp (N + 1)]
  ring

/-- **Cofinal-completion universality.**  At every depth, the scalar truncation is evaluation of
the canonical prefix polynomial, and every solution of the affine Mahler constraint is that prefix
plus the same explicit substituted tail. -/
theorem ultrametricThermalCofinalCompletionUniversality
    {p : ℕ} (hp : 2 ≤ p) (N : ℕ) :
    (∀ w : ℂ, (ultrametricThermalTruncationPolynomial p N).eval w =
      ultrametricThermalTruncation p w N) ∧
    ultrametricThermalSignal p = ultrametricThermalPrefixSeries p N +
      PowerSeries.C ((((p : ℂ) - 1) ^ (2 : ℕ)) / (p : ℂ)) *
        branchingThermalTail p (N + 1) ∧
    ∀ Y : ℂ⟦X⟧,
      Y = PowerSeries.C ((p : ℂ) - 2) * PowerSeries.X +
          PowerSeries.X ^ p + PowerSeries.C (p : ℂ) *
            PowerSeries.subst (PowerSeries.X ^ p) Y →
      Y = ultrametricThermalPrefixSeries p N +
        PowerSeries.C ((((p : ℂ) - 1) ^ (2 : ℕ)) / (p : ℂ)) *
          branchingThermalTail p (N + 1) := by
  refine ⟨eval_ultrametricThermalTruncationPolynomial p N,
    ultrametricThermalSignal_eq_prefix_add_exact_tail hp N, ?_⟩
  intro Y hY
  rw [ultrametricThermalSignal_unique hp hY]
  exact ultrametricThermalSignal_eq_prefix_add_exact_tail hp N

end

end GaloisForLFunctions.HTGeometry
