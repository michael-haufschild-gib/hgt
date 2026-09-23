import Mathlib

/-!
# Exponential valuation weights on a lattice

An exponentially decaying weight in the `ℓ¹` valuation norm is summable over `ℤ^d`.  Together with
a linear bound on the event times this is what makes a finite-recurrence event source square
summable against the exponential strip weight: the strip gain `exp(2 sigma tau)` is beaten by the
weight as soon as the decay rate exceeds `sigma` times the recurrence constant.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

/-- The `ℓ¹` valuation norm of a lattice point. -/
def latticeEll1 {d : ℕ} (ν : Fin d → ℤ) : ℝ := ∑ i, |(ν i : ℝ)|

theorem latticeEll1_nonneg {d : ℕ} (ν : Fin d → ℤ) : 0 ≤ latticeEll1 ν :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem latticeEll1_succ {d : ℕ} (ν : Fin (d + 1) → ℤ) :
    latticeEll1 ν = |(ν 0 : ℝ)| + latticeEll1 (Fin.tail ν) := by
  simp [latticeEll1, Fin.sum_univ_succ, Fin.tail]

/-- **The exponential weight is summable on `ℤ`.** -/
theorem summable_exp_neg_abs_int {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℤ => Real.exp (-c * |(n : ℝ)|)) := by
  have hgeom : Summable (fun n : ℕ => Real.exp (-c * (n : ℝ))) := by
    have hr : Real.exp (-c) < 1 := by
      rw [show (1 : ℝ) = Real.exp 0 by simp]
      exact Real.exp_lt_exp.mpr (by linarith)
    have h0 : (0 : ℝ) ≤ Real.exp (-c) := (Real.exp_pos _).le
    have hg := summable_geometric_of_lt_one h0 hr
    refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · refine hgeom.congr fun n => ?_
    rw [Int.cast_natCast, abs_of_nonneg (by positivity)]
  · have hshift : Summable (fun n : ℕ => Real.exp (-c) * Real.exp (-c * (n : ℝ))) :=
      hgeom.mul_left _
    refine hshift.congr fun n => ?_
    have hcast : ((-((n : ℤ) + 1) : ℤ) : ℝ) = -((n : ℝ) + 1) := by push_cast; ring
    rw [hcast, abs_neg, abs_of_nonneg (by positivity), ← Real.exp_add]
    congr 1
    ring

/-- **The exponential `ℓ¹` weight is summable on `ℤ^d`.** -/
theorem summable_exp_neg_latticeEll1 (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Summable (fun ν : Fin d → ℤ => Real.exp (-c * latticeEll1 ν)) := by
  induction d with
  | zero => exact Summable.of_finite
  | succ d ih =>
      have hprod : Summable
          (fun p : ℤ × (Fin d → ℤ) =>
            Real.exp (-c * |(p.1 : ℝ)|) * Real.exp (-c * latticeEll1 p.2)) :=
        Summable.mul_of_nonneg (summable_exp_neg_abs_int hc) ih
          (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
      refine (Equiv.summable_iff (Fin.consEquiv (fun _ : Fin (d + 1) => ℤ))).mp ?_
      refine hprod.congr fun p => ?_
      rw [← Real.exp_add]
      congr 1
      show -c * |(p.1 : ℝ)| + -c * latticeEll1 p.2
        = -c * latticeEll1 (Fin.cons p.1 p.2 : Fin (d + 1) → ℤ)
      rw [latticeEll1_succ]
      simp only [Fin.cons_zero, Fin.tail_cons]
      ring

/-- **The finite-recurrence event source is square summable against the strip weight `(18)`.**
A weight decaying at rate `kappa` in the `ℓ¹` valuation norm beats the strip gain of event times
growing at rate `Ca`, as soon as `kappa > sigma * Ca`. -/
theorem summable_strip_weighted_eventSource {d : ℕ} {σ κ Ca C : ℝ}
    {τ : (Fin d → ℤ) → ℝ} {m : (Fin d → ℤ) → ℝ}
    (hσ : 0 ≤ σ) (hC : 0 ≤ C)
    (hτ : ∀ ν, τ ν ≤ Ca * (1 + latticeEll1 ν))
    (hm : ∀ ν, |m ν| ≤ C * Real.exp (-κ * latticeEll1 ν))
    (hκ : σ * Ca < κ) :
    Summable (fun ν => Real.exp (2 * σ * τ ν) * m ν ^ (2 : ℕ)) := by
  have hc : 0 < 2 * (κ - σ * Ca) := by linarith
  have hdom : Summable
      (fun ν : Fin d → ℤ =>
        (C ^ (2 : ℕ) * Real.exp (2 * σ * Ca)) * Real.exp (-(2 * (κ - σ * Ca)) * latticeEll1 ν)) :=
    (summable_exp_neg_latticeEll1 d hc).mul_left _
  refine hdom.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_)
  have hE : latticeEll1 ν ≥ 0 := latticeEll1_nonneg ν
  have h1 : Real.exp (2 * σ * τ ν) ≤ Real.exp (2 * σ * (Ca * (1 + latticeEll1 ν))) := by
    refine Real.exp_le_exp.mpr ?_
    have := hτ ν
    nlinarith
  have h2 : m ν ^ (2 : ℕ) ≤ (C * Real.exp (-κ * latticeEll1 ν)) ^ (2 : ℕ) := by
    have habs : |m ν| ≤ C * Real.exp (-κ * latticeEll1 ν) := hm ν
    have hnn : 0 ≤ C * Real.exp (-κ * latticeEll1 ν) := by positivity
    calc m ν ^ (2 : ℕ) = |m ν| ^ (2 : ℕ) := (sq_abs _).symm
      _ ≤ (C * Real.exp (-κ * latticeEll1 ν)) ^ (2 : ℕ) := by
          exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc Real.exp (2 * σ * τ ν) * m ν ^ (2 : ℕ)
      ≤ Real.exp (2 * σ * (Ca * (1 + latticeEll1 ν))) * (C * Real.exp (-κ * latticeEll1 ν)) ^ (2 : ℕ) := by
        exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    _ = (C ^ (2 : ℕ) * Real.exp (2 * σ * Ca)) * Real.exp (-(2 * (κ - σ * Ca)) * latticeEll1 ν) := by
        have hsq : Real.exp (-κ * latticeEll1 ν) ^ (2 : ℕ) = Real.exp (-(2 * κ) * latticeEll1 ν) := by
          rw [pow_two, ← Real.exp_add]; congr 1; ring
        have hL : Real.exp (2 * σ * (Ca * (1 + latticeEll1 ν)))
              * Real.exp (-(2 * κ) * latticeEll1 ν)
            = Real.exp (2 * σ * Ca) * Real.exp (-(2 * (κ - σ * Ca)) * latticeEll1 ν) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [mul_pow, hsq]
        calc Real.exp (2 * σ * (Ca * (1 + latticeEll1 ν)))
              * (C ^ (2 : ℕ) * Real.exp (-(2 * κ) * latticeEll1 ν))
            = C ^ (2 : ℕ) * (Real.exp (2 * σ * (Ca * (1 + latticeEll1 ν)))
              * Real.exp (-(2 * κ) * latticeEll1 ν)) := by ring
          _ = C ^ (2 : ℕ) * (Real.exp (2 * σ * Ca)
              * Real.exp (-(2 * (κ - σ * Ca)) * latticeEll1 ν)) := by rw [hL]
          _ = C ^ (2 : ℕ) * Real.exp (2 * σ * Ca)
              * Real.exp (-(2 * (κ - σ * Ca)) * latticeEll1 ν) := by ring

end GaloisForLFunctions.HTGeometry
