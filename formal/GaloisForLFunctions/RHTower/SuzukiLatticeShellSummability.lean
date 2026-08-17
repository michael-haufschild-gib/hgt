import GaloisForLFunctions.RHTower.SuzukiLatticeCarrierWeight
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Lattice summability of the polynomial event weight

The event sum of the polynomial carrier is a single lattice power, so its convergence is the
convergence of `∑_{ν ∈ ℤ^d} (1 + |ν|₁)^{-p}` for `p > d`.

The comparison that proves it needs no shell counting.  Each coordinate satisfies
`1 + |ν_i| ≤ 1 + |ν|₁`, so

`∏_i (1 + |ν_i|) ≤ (1 + |ν|₁)^d`,

hence `(1 + |ν|₁)^{-p} ≤ ∏_i (1 + |ν_i|)^{-p/d}` and the right side is a product of one-dimensional
`p/d`-series, each convergent exactly when `p > d`.  The multi-dimensional sum therefore factors,
and the induction over coordinates is the only structural step.
-/

open Finset

noncomputable section

namespace RHTower

/-! ## The one-dimensional series -/

theorem summable_one_add_nat_rpow {r : ℝ} (hr : 1 < r) :
    Summable (fun n : ℕ => ((1 : ℝ) + n) ^ (-r)) := by
  have hbase : Summable (fun n : ℕ => 1 / (n : ℝ) ^ r) := Real.summable_one_div_nat_rpow.mpr hr
  have hshift : Summable (fun n : ℕ => 1 / (((n : ℝ) + 1)) ^ r) := by
    have h := (summable_nat_add_iff 1).mpr hbase
    refine h.congr fun n => ?_
    push_cast
    ring_nf
  refine hshift.congr fun n => ?_
  rw [Real.rpow_neg (by positivity), one_div]
  ring_nf

theorem summable_one_add_abs_int_rpow {r : ℝ} (hr : 1 < r) :
    Summable (fun m : ℤ => ((1 : ℝ) + |(m : ℝ)|) ^ (-r)) := by
  refine Summable.of_nat_of_neg ?_ ?_
  · refine (summable_one_add_nat_rpow hr).congr fun n => ?_
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n : ℤ) : ℝ))]
    push_cast
    ring_nf
  · refine (summable_one_add_nat_rpow hr).congr fun n => ?_
    rw [show (((-(n : ℤ)) : ℤ) : ℝ) = -(n : ℝ) by push_cast; ring]
    rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ))]

/-! ## The coordinate product -/

/-- Splitting the coordinate product at the first coordinate. -/
theorem prod_cons_split {d : ℕ} {r : ℝ} (x : ℤ) (ν : Fin d → ℤ) :
    ∏ i : Fin (d + 1), ((1 : ℝ) + |(((Fin.cons x ν : Fin (d + 1) → ℤ) i : ℤ) : ℝ)|) ^ (-r)
      = ((1 : ℝ) + |((x : ℤ) : ℝ)|) ^ (-r)
        * ∏ i, ((1 : ℝ) + |((ν i : ℤ) : ℝ)|) ^ (-r) := by
  rw [Fin.prod_univ_succ, Fin.cons_zero]
  congr 1

set_option maxHeartbeats 1000000 in
/-- The product of one-dimensional series over a finite coordinate set is summable. -/
theorem summable_prod_one_add_abs {d : ℕ} {r : ℝ} (hr : 1 < r) :
    Summable (fun ν : Fin d → ℤ => ∏ i, ((1 : ℝ) + |((ν i : ℤ) : ℝ)|) ^ (-r)) := by
  induction d with
  | zero =>
      exact Summable.of_finite
  | succ d ih =>
      have hone := summable_one_add_abs_int_rpow (r := r) hr
      have hnn1 : (0 : ℤ → ℝ) ≤ fun m : ℤ => ((1 : ℝ) + |(m : ℝ)|) ^ (-r) := by
        intro m
        exact Real.rpow_nonneg (by positivity) _
      have hnn2 : (0 : (Fin d → ℤ) → ℝ)
          ≤ fun ν : Fin d → ℤ => ∏ i, ((1 : ℝ) + |((ν i : ℤ) : ℝ)|) ^ (-r) := by
        intro ν
        exact Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _
      have hprod := hone.mul_of_nonneg ih hnn1 hnn2
      have hcons : Summable (fun p : ℤ × (Fin d → ℤ) =>
          ∏ i : Fin (d + 1),
            ((1 : ℝ) + |(((Fin.cons p.1 p.2 : Fin (d + 1) → ℤ) i : ℤ) : ℝ)|) ^ (-r)) :=
        hprod.congr fun p => (prod_cons_split p.1 p.2).symm
      exact ((Fin.consEquiv fun _ : Fin (d + 1) => ℤ).summable_iff
        (f := fun ν : Fin (d + 1) → ℤ =>
          ∏ i, ((1 : ℝ) + |((ν i : ℤ) : ℝ)|) ^ (-r))).mp hcons

end RHTower

namespace RHTower

open Finset

/-! ## The comparison -/

/-- Each coordinate size is dominated by the lattice size. -/
theorem one_add_abs_coord_le {ι : Type*} [Fintype ι] (ν : ι → ℤ) (i : ι) :
    (1 : ℝ) + |((ν i : ℤ) : ℝ)| ≤ 1 + (latticeL1 ν : ℝ) := by
  have hnat : (ν i).natAbs ≤ latticeL1 ν := by
    rw [latticeL1]
    exact Finset.single_le_sum (f := fun j => (ν j).natAbs)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hz : |ν i| ≤ ((latticeL1 ν : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat
  have hreal : |((ν i : ℤ) : ℝ)| ≤ ((latticeL1 ν : ℕ) : ℝ) := by exact_mod_cast hz
  linarith

/-- **`(8)` on the unit lattice.**  The polynomial event weight is summable above the lattice
dimension. -/
theorem summable_polyDecay_fin {d : ℕ} {p : ℝ} (hd : 0 < d) (hp : (d : ℝ) < p) :
    Summable (fun ν : Fin d → ℤ => (1 + (latticeL1 ν : ℝ)) ^ (-p)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  set r : ℝ := p / d with hr
  have hr1 : 1 < r := by
    rw [hr, lt_div_iff₀ hd0]
    linarith
  refine Summable.of_nonneg_of_le
    (fun ν => Real.rpow_nonneg (by positivity) _) ?_ (summable_prod_one_add_abs hr1)
  intro ν
  have hbase : (0 : ℝ) < 1 + (latticeL1 ν : ℝ) := by positivity
  have hprodle : ∏ i, ((1 : ℝ) + |((ν i : ℤ) : ℝ)|) ≤ (1 + (latticeL1 ν : ℝ)) ^ d := by
    calc ∏ i, ((1 : ℝ) + |((ν i : ℤ) : ℝ)|)
        ≤ ∏ _i : Fin d, (1 + (latticeL1 ν : ℝ)) :=
          Finset.prod_le_prod (fun i _ => by positivity)
            (fun i _ => one_add_abs_coord_le ν i)
      _ = (1 + (latticeL1 ν : ℝ)) ^ d := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hposprod : (0 : ℝ) < ∏ i, ((1 : ℝ) + |((ν i : ℤ) : ℝ)|) :=
    Finset.prod_pos fun i _ => by positivity
  have hsplit : ∏ i, ((1 : ℝ) + |((ν i : ℤ) : ℝ)|) ^ (-r)
      = (∏ i, ((1 : ℝ) + |((ν i : ℤ) : ℝ)|)) ^ (-r) := by
    rw [← Real.finsetProd_rpow]
    intro i _
    positivity
  rw [hsplit]
  have hpow : (1 + (latticeL1 ν : ℝ)) ^ (-p)
      = ((1 + (latticeL1 ν : ℝ)) ^ (d : ℝ)) ^ (-r) := by
    rw [← Real.rpow_mul hbase.le]
    congr 1
    rw [hr]
    field_simp
  rw [hpow]
  refine Real.rpow_le_rpow_of_nonpos hposprod ?_ (by linarith)
  rw [← Real.rpow_natCast (1 + (latticeL1 ν : ℝ)) d] at hprodle
  exact hprodle

end RHTower

namespace RHTower

/-! ## The event sum -/

/-- **`(8)`: a polynomial carrier above the transport degree absorbs the whole event factor.**
The pointwise event bound turns the event sum into a single lattice power series of exponent
`2κ - 2σQ`, convergent exactly above the lattice dimension. -/
theorem summable_polyWeight_sq_event {d : ℕ} {κ σ Q : ℝ} (hd : 0 < d) (hσ : 0 ≤ σ)
    (hQ : 0 ≤ Q) (hκ : (d : ℝ) < 2 * κ - 2 * σ * Q) (τ : (Fin d → ℤ) → ℝ)
    (hτ : ∀ ν, τ ν ≤ Q * Real.log (2 + (latticeL1 ν : ℝ))) :
    Summable (fun ν : Fin d → ℤ => polyWeight κ ν ^ 2 * Real.exp (2 * σ * τ ν)) := by
  have hexp : (0 : ℝ) ≤ 2 * σ * Q := by positivity
  have hmain := (summable_polyDecay_fin (d := d) (p := 2 * κ - 2 * σ * Q) hd hκ).mul_left
    ((2 : ℝ) ^ (2 * σ * Q))
  refine Summable.of_nonneg_of_le (fun ν => by positivity) (fun ν => ?_) hmain
  have h1 : (0 : ℝ) < 1 + (latticeL1 ν : ℝ) := by positivity
  have hstep := polyWeight_sq_mul_event_le (κ := κ) (σ := σ) (Q := Q) hσ ν (hτ ν)
  refine le_trans hstep ?_
  have h2 : (2 + (latticeL1 ν : ℝ)) ^ (2 * σ * Q)
      ≤ (2 : ℝ) ^ (2 * σ * Q) * (1 + (latticeL1 ν : ℝ)) ^ (2 * σ * Q) := by
    rw [← Real.mul_rpow (by norm_num) h1.le]
    refine Real.rpow_le_rpow (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) (latticeL1 ν)])
      hexp
  have h3 : (1 + (latticeL1 ν : ℝ)) ^ (-2 * κ) * ((1 + (latticeL1 ν : ℝ)) ^ (2 * σ * Q))
      = (1 + (latticeL1 ν : ℝ)) ^ (-(2 * κ - 2 * σ * Q)) := by
    rw [← Real.rpow_add h1]
    congr 1
    ring
  calc (1 + (latticeL1 ν : ℝ)) ^ (-2 * κ) * (2 + (latticeL1 ν : ℝ)) ^ (2 * σ * Q)
      ≤ (1 + (latticeL1 ν : ℝ)) ^ (-2 * κ)
          * ((2 : ℝ) ^ (2 * σ * Q) * (1 + (latticeL1 ν : ℝ)) ^ (2 * σ * Q)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg h1.le _)
    _ = (2 : ℝ) ^ (2 * σ * Q) * (1 + (latticeL1 ν : ℝ)) ^ (-(2 * κ - 2 * σ * Q)) := by
        rw [← h3]; ring

end RHTower
