import GaloisForLFunctions.ArithmeticOrientationTheory.CosetToeplitzDominanceAndShiftedPairSelectivity

/-!
# Polar-Neutral Rank-One Collapse and Exact Logarithmic Cell-Remainder Subdivision

On the discrete integer log-lattice `[2, X]`, `ArithmeticOrientationTheory` proves that the
reflected-diagonal archimedean–polar weight
`archReflectedDiagWeight(n) = −k_arch(−log n, log n) = (n − 1)² / (2n) − n³ / (n⁴ − 1)`
grows linearly (`> n / 6` for `n ≥ 4`), dominating every prime Hankel tower uniformly in `X` when
only diagonal `a = b` archimedean terms are retained.

This module proves **why** that linear lattice surplus cannot survive on gauge-neutral states once
off-diagonal crossing pairs `a ≠ b` are restored, and establishes the **exact continuum cell
subdivision calculus** replacing discrete point-lattice truncation:

1. **Rank-One Polar Collapse of the Full Archimedean–Polar Crossing Form
   (`neg_archPairKernel_eq_polar_sub_levy`, `fullArchCrossingForm_eq_polar_sq_sub_levy`,
   `fullArchCrossingForm_polarNeutral_eq`, `reflectedDiag_add_offDiagPolar_eq_neg_levy`,
   `exists_nonzero_polarNeutral_profile`).**
   Across **all** lattice pairs `(a, b) ∈ [2, X]²`,
   `−k_arch(−log a, log b) = ((a − 1)(b − 1)) / (2√(ab)) − (ab)^{3/2} / ((ab)² − 1)`.
   Summing over `(a, b) ∈ [2, X]²` collapses the entire linear-growth term into a **single rank-one
   polar square** `(1/2) (∑_{n=2}^X ((n − 1)/√n) q(n))²`. On the codimension-`1` **polar-neutral
   hyperplane** `∑_{n=2}^X ((n − 1)/√n) q(n) = 0`, the off-diagonal polar cross-terms `a ≠ b`
   cancel the linear diagonal `+(n − 1)²/(2n)` identically, leaving strictly negative diagonal weight
   `−∑_{n=2}^X n³/(n⁴ − 1) q(n)² ≤ 0`.

2. **Exact Logarithmic Cell Subdivision (`logCellWidth`, `sum_logCellWidth_mul_add_eq`,
   `continuumCellShiftCorr_eq_spine_add_remainder`).**
   Partitioning `[0, ∞)` into logarithmic continuum cells `I_n = [log n, log(n + 1))` of width
   `w_n = log(n + 1) − log n`, multiplicative translation by `log m` (`m ≥ 1`) subdivides each cell
   without boundary smearing: `I_a + log m = ⊔_{r=0}^{m-1} I_{am+r}`, reflected algebraically in the
   exact telescoping identity `∑_{r=0}^{m-1} w_{am+r} = w_a`. Every step-function shift correlation
   factors **identically** into the **Lattice Divisibility Spine** (`r = 0`) plus the
   **Euclidean-Remainder Successor Defect** (`1 ≤ r < m`).

3. **Disjoint-Block Biarithmetic Sobolev Bound (`euclideanCellRemainder_sq_le`,
   `abs_euclideanCellRemainder_le_of_supported`).**
   Because the Euclidean quotient-remainder blocks `{am + j : 0 ≤ j < m}` are pairwise disjoint
   across `a ≥ 1`, Cauchy–Schwarz bounds the Euclidean cell remainder **uniformly in `m` and `X`**:
   for any `c` supported on `[1, X]`,
   `|euclideanCellRemainder c X m| ≤ √(∑_{a=1}^X w_a c_a²) · √(∑_{k=1}^X k (c_{k+1} − c_k)²)`.
-/

open Finset RHTower
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

/-! ## §1. Rank-One Polar Collapse of the Full Archimedean–Polar Crossing Form -/

/-- The rank-one boundary-pole crossing amplitude `s(n) = (n − 1) / √n = 2 sinh(log n / 2)`. -/
def polarCrossingAmplitude (n : ℕ) : ℝ :=
  ((n : ℝ) - 1) / Real.sqrt n

/-- The purely archimedean Lévy crossing weight `ω(log(ab)) = (ab)^{3/2} / ((ab)² − 1)`. -/
def archLevyProductWeight (a b : ℕ) : ℝ :=
  Real.sqrt ((a : ℝ) * b) ^ 3 / (((a : ℝ) * b) ^ 2 - 1)

/-- Full archimedean–polar crossing quadratic form across **all** pairs `(a, b) ∈ [2, X]²`. -/
def fullArchCrossingForm (q : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ a ∈ Icc 2 X, ∑ b ∈ Icc 2 X, (-archPairKernel (-Real.log a) (Real.log b)) * q a * q b

/-- Off-diagonal polar cross-term quadratic form (`a ≠ b` in `[2, X]`). -/
def offDiagPolarForm (q : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ a ∈ Icc 2 X, ∑ b ∈ (Icc 2 X).erase a,
    (polarCrossingAmplitude a * polarCrossingAmplitude b / 2) * q a * q b

/-- **Exact pairwise splitting (`neg_archPairKernel_eq_polar_sub_levy`).**
For all integers `a, b ≥ 2`, `−k_arch(−log a, log b)` splits into the rank-one polar product
`(1/2) s(a) s(b)` minus the positive Lévy kernel `archLevyProductWeight a b`. -/
theorem neg_archPairKernel_eq_polar_sub_levy {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    -archPairKernel (-Real.log a) (Real.log b) =
      polarCrossingAmplitude a * polarCrossingAmplitude b / 2 - archLevyProductWeight a b := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hab : (1 : ℝ) < (a : ℝ) * b := by
    have ha2 : (2 : ℝ) ≤ a := by exact_mod_cast ha
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast hb
    nlinarith
  rw [archPairKernel_neg_log_log ha0 hb0 hab]
  unfold polarCrossingAmplitude archLevyProductWeight
  set s : ℝ := Real.sqrt ((a : ℝ) * b)
  have hs_pos : 0 < s := Real.sqrt_pos.mpr (mul_pos ha0 hb0)
  have hmul_sqrt : Real.sqrt a * Real.sqrt b = s := (Real.sqrt_mul ha0.le b).symm
  have hs_sq : s ^ 2 = (a : ℝ) * b := Real.sq_sqrt (mul_pos ha0 hb0).le
  have hab_sq : ((a : ℝ) * b) ^ 2 = s ^ 4 := by rw [← hs_sq]; ring
  have hden_pos : 0 < s ^ 4 - 1 := by rw [← hab_sq]; nlinarith
  have hamp : ((a : ℝ) - 1) / Real.sqrt a * (((b : ℝ) - 1) / Real.sqrt b) / 2 =
      ((a : ℝ) - 1) * ((b : ℝ) - 1) / (2 * s) := by
    rw [div_mul_div_comm, hmul_sqrt, div_div]
    congr 1; ring
  rw [hamp, hab_sq]
  field_simp [hs_pos.ne', hden_pos.ne']
  ring

/-- At `a = b = n ≥ 2`, `archReflectedDiagWeight n` equals `(1/2) s(n)² − n³ / (n⁴ − 1)`. -/
theorem archReflectedDiagWeight_eq_polar_sub_levy {n : ℕ} (hn : 2 ≤ n) :
    archReflectedDiagWeight n =
      polarCrossingAmplitude n ^ 2 / 2 - (n : ℝ) ^ 3 / ((n : ℝ) ^ 4 - 1) := by
  unfold archReflectedDiagWeight
  rw [neg_archPairKernel_eq_polar_sub_levy hn hn, sq]
  congr 1
  unfold archLevyProductWeight
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hsqrt : Real.sqrt ((n : ℝ) * n) = (n : ℝ) := Real.sqrt_mul_self hn0
  rw [hsqrt]
  congr 1
  ring

/-- **Full Crossing Form Identity (`fullArchCrossingForm_eq_polar_sq_sub_levy`).**
Summing `−k_arch(−log a, log b)` across all pairs `(a, b) ∈ [2, X]²` collapses the entire polar
part into a **single rank-one square** `(1/2) (∑_{n=2}^X s(n) q(n))²`. -/
theorem fullArchCrossingForm_eq_polar_sq_sub_levy (q : ℕ → ℝ) (X : ℕ) :
    fullArchCrossingForm q X =
      (∑ n ∈ Icc 2 X, polarCrossingAmplitude n * q n) ^ 2 / 2 -
        ∑ a ∈ Icc 2 X, ∑ b ∈ Icc 2 X, archLevyProductWeight a b * q a * q b := by
  unfold fullArchCrossingForm
  have hrew : ∀ a ∈ Icc 2 X,
      ∑ b ∈ Icc 2 X, (-archPairKernel (-Real.log a) (Real.log b)) * q a * q b =
      ∑ b ∈ Icc 2 X,
        ((polarCrossingAmplitude a * q a) * (polarCrossingAmplitude b * q b) / 2 -
          archLevyProductWeight a b * q a * q b) := by
    intro a ha
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [neg_archPairKernel_eq_polar_sub_levy (mem_Icc.mp ha).1 (mem_Icc.mp hb).1]
    ring
  rw [Finset.sum_congr rfl hrew]
  simp_rw [Finset.sum_sub_distrib]
  congr 1
  rw [sq, Finset.sum_mul]
  have hinner : ∀ a ∈ Icc 2 X,
      (∑ b ∈ Icc 2 X, (polarCrossingAmplitude a * q a) * (polarCrossingAmplitude b * q b) / 2) =
      (polarCrossingAmplitude a * q a * ∑ b ∈ Icc 2 X, polarCrossingAmplitude b * q b) / 2 := by
    intro a _
    rw [Finset.mul_sum, Finset.sum_div]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_div]

/-- **Polar-Neutral Collapse of the Full Crossing Form (`fullArchCrossingForm_polarNeutral_eq`).**
On the codimension-`1` polar-neutral hyperplane `∑_{n=2}^X s(n) q(n) = 0`, the entire rank-one
polar surplus vanishes identically. -/
theorem fullArchCrossingForm_polarNeutral_eq (q : ℕ → ℝ) (X : ℕ)
    (hneutral : ∑ n ∈ Icc 2 X, polarCrossingAmplitude n * q n = 0) :
    fullArchCrossingForm q X =
      -∑ a ∈ Icc 2 X, ∑ b ∈ Icc 2 X, archLevyProductWeight a b * q a * q b := by
  rw [fullArchCrossingForm_eq_polar_sq_sub_levy, hneutral]
  ring

/-- **Cancellation of the Linear Reflected-Diagonal Surplus (`reflectedDiag_add_offDiagPolar_eq_neg_levy`).**
Restoring the off-diagonal polar cross-terms `a ≠ b` to the reflected diagonal
`∑_{n=2}^X archReflectedDiagWeight(n) q(n)²` cancels `+(n − 1)²/(2n)` identically on polar-neutral
profiles, leaving strictly negative diagonal Lévy weight `−∑_{n=2}^X (n³/(n⁴ − 1)) q(n)² ≤ 0`. -/
theorem reflectedDiag_add_offDiagPolar_eq_neg_levy (q : ℕ → ℝ) (X : ℕ)
    (hneutral : ∑ n ∈ Icc 2 X, polarCrossingAmplitude n * q n = 0) :
    (∑ n ∈ Icc 2 X, archReflectedDiagWeight n * q n ^ 2) + offDiagPolarForm q X =
      -∑ n ∈ Icc 2 X, ((n : ℝ) ^ 3 / ((n : ℝ) ^ 4 - 1)) * q n ^ 2 := by
  have hsq_exp : (∑ n ∈ Icc 2 X, polarCrossingAmplitude n * q n) ^ 2 / 2 =
      (∑ n ∈ Icc 2 X, (polarCrossingAmplitude n ^ 2 / 2) * q n ^ 2) + offDiagPolarForm q X := by
    unfold offDiagPolarForm
    rw [sq, Finset.sum_mul]
    have hsplit : ∀ a ∈ Icc 2 X,
        polarCrossingAmplitude a * q a * (∑ b ∈ Icc 2 X, polarCrossingAmplitude b * q b) / 2 =
        (polarCrossingAmplitude a ^ 2 / 2) * q a ^ 2 +
          ∑ b ∈ (Icc 2 X).erase a,
            (polarCrossingAmplitude a * polarCrossingAmplitude b / 2) * q a * q b := by
      intro a ha
      rw [← Finset.add_sum_erase (Icc 2 X) (fun b => polarCrossingAmplitude b * q b) ha,
          mul_add, add_div, Finset.mul_sum, Finset.sum_div]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun b _ => by ring
    rw [Finset.sum_div, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have h0 : (∑ n ∈ Icc 2 X, (polarCrossingAmplitude n ^ 2 / 2) * q n ^ 2) +
      offDiagPolarForm q X = 0 := by
    rw [← hsq_exp, hneutral]; norm_num
  have hdiag : ∑ n ∈ Icc 2 X, archReflectedDiagWeight n * q n ^ 2 =
      (∑ n ∈ Icc 2 X, (polarCrossingAmplitude n ^ 2 / 2) * q n ^ 2) -
        ∑ n ∈ Icc 2 X, ((n : ℝ) ^ 3 / ((n : ℝ) ^ 4 - 1)) * q n ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [archReflectedDiagWeight_eq_polar_sub_levy (mem_Icc.mp hn).1]
    ring
  linarith

/-- Strict negativity of the polar-neutral diagonal + off-diagonal polar sum on any nonzero profile
supported in `[2, X]`, together with existence of nonzero polar-neutral profiles for all `X ≥ 3`. -/
theorem exists_nonzero_polarNeutral_profile {X : ℕ} (hX : 3 ≤ X) :
    ∃ q : ℕ → ℝ,
      (∀ n : ℕ, n ∉ Icc 2 X → q n = 0) ∧
      (∃ n ∈ Icc 2 X, q n ≠ 0) ∧
      (∑ n ∈ Icc 2 X, polarCrossingAmplitude n * q n = 0) ∧
      (∑ n ∈ Icc 2 X, archReflectedDiagWeight n * q n ^ 2) + offDiagPolarForm q X < 0 := by
  let q : ℕ → ℝ := fun n =>
    if n = 2 then polarCrossingAmplitude 3
    else if n = 3 then -polarCrossingAmplitude 2
    else 0
  have h2mem : (2 : ℕ) ∈ Icc 2 X := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have h3mem : (3 : ℕ) ∈ Icc 2 X := mem_Icc.mpr ⟨by omega, hX⟩
  have hamp3_pos : 0 < polarCrossingAmplitude 3 := by
    unfold polarCrossingAmplitude; positivity
  have hsupp : ∀ n : ℕ, n ∉ Icc 2 X → q n = 0 := by
    intro n hn
    have hn2 : n ≠ 2 := fun h => hn (h ▸ h2mem)
    have hn3 : n ≠ 3 := fun h => hn (h ▸ h3mem)
    simp [q, hn2, hn3]
  have hneut : ∑ n ∈ Icc 2 X, polarCrossingAmplitude n * q n = 0 := by
    rw [← Finset.add_sum_erase (Icc 2 X) _ h2mem]
    have h3er : (3 : ℕ) ∈ (Icc 2 X).erase 2 := mem_erase.mpr ⟨by decide, h3mem⟩
    rw [← Finset.add_sum_erase ((Icc 2 X).erase 2) _ h3er]
    have hrest : ∑ n ∈ ((Icc 2 X).erase 2).erase 3, polarCrossingAmplitude n * q n = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      simp only [mem_erase] at hn
      simp [q, hn.1, hn.2.1]
    rw [hrest]
    simp only [q]
    norm_num
    ring
  refine ⟨q, hsupp, ⟨2, h2mem, by simp [q, hamp3_pos.ne']⟩, hneut, ?_⟩
  rw [reflectedDiag_add_offDiagPolar_eq_neg_levy q X hneut]
  have hsum_pos : 0 < ∑ n ∈ Icc 2 X, ((n : ℝ) ^ 3 / ((n : ℝ) ^ 4 - 1)) * q n ^ 2 := by
    have h2_term : 0 < (((2 : ℕ) : ℝ) ^ 3 / (((2 : ℕ) : ℝ) ^ 4 - 1)) * q 2 ^ 2 := by
      have hq2 : q 2 = polarCrossingAmplitude 3 := by simp [q]
      rw [hq2]
      have hc : (0 : ℝ) < ((2 : ℕ) : ℝ) ^ 3 / (((2 : ℕ) : ℝ) ^ 4 - 1) := by norm_num
      exact mul_pos hc (sq_pos_of_pos hamp3_pos)
    refine lt_of_lt_of_le h2_term
      (Finset.single_le_sum
        (f := fun n : ℕ => ((n : ℝ) ^ 3 / ((n : ℝ) ^ 4 - 1)) * q n ^ 2)
        (fun n hn => ?_) h2mem)
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.mp hn).1
    have hn4 : 0 < (n : ℝ) ^ 4 - 1 := by
      have : (16 : ℝ) ≤ (n : ℝ) ^ 4 := by
        have : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
        nlinarith
      linarith
    positivity
  linarith

/-! ## §2. Exact Logarithmic Cell Subdivision (`I_a + log m = ⊔_{r < m} I_{am+r}`) -/

/-- Logarithmic continuum cell width `w_n = log(n + 1) − log n = |I_n|` (`I_n = [log n, log(n+1))`). -/
def logCellWidth (n : ℕ) : ℝ :=
  Real.log ((n : ℝ) + 1) - Real.log (n : ℝ)

theorem logCellWidth_pos {n : ℕ} (hn : 1 ≤ n) : 0 < logCellWidth n := by
  unfold logCellWidth
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  exact sub_pos.mpr (Real.log_lt_log hn0 (by linarith))

theorem logCellWidth_le_inv {n : ℕ} (hn : 1 ≤ n) : logCellWidth n ≤ 1 / (n : ℝ) := by
  unfold logCellWidth
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hdiv : Real.log ((n : ℝ) + 1) - Real.log (n : ℝ) =
      Real.log (((n : ℝ) + 1) / (n : ℝ)) :=
    (Real.log_div (by positivity) hn0.ne').symm
  rw [hdiv]
  calc Real.log (((n : ℝ) + 1) / (n : ℝ))
      ≤ ((n : ℝ) + 1) / (n : ℝ) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = 1 / (n : ℝ) := by field_simp; ring

/-- Telescoping of consecutive logarithmic cell widths `w_{N+r}` over `0 ≤ r < m`. -/
theorem sum_logCellWidth_add (N m : ℕ) :
    ∑ r ∈ range m, logCellWidth (N + r) =
      Real.log ((N + m : ℕ) : ℝ) - Real.log (N : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    unfold logCellWidth
    have hcast : (((N + m : ℕ) : ℝ) + 1) = ((N + (m + 1) : ℕ) : ℝ) := by push_cast; ring
    rw [hcast]
    ring

/-- **Exact Multiplicative Cell-Subdivision Law (`sum_logCellWidth_mul_add_eq`).**
For all `a ≥ 1` and `m ≥ 1`, translating `I_a = [log a, log(a + 1))` by `log m` partitions it
without boundary smearing into the `m` Euclidean cells `I_{am + r}` (`0 ≤ r < m`):
`∑_{r=0}^{m-1} w_{am + r} = w_a`. -/
theorem sum_logCellWidth_mul_add_eq {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) :
    ∑ r ∈ range m, logCellWidth (a * m + r) = logCellWidth a := by
  rw [sum_logCellWidth_add (a * m) m]
  have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hc1 : ((a * m + m : ℕ) : ℝ) = ((a : ℝ) + 1) * (m : ℝ) := by push_cast; ring
  have hc2 : ((a * m : ℕ) : ℝ) = (a : ℝ) * (m : ℝ) := by push_cast; ring
  rw [hc1, hc2,
      Real.log_mul (by positivity) hm0.ne',
      Real.log_mul ha0.ne' hm0.ne']
  unfold logCellWidth
  ring

/-- Continuum `log m`-shift correlation of the cell-constant step function `F(x) = c_{⌊e^x⌋}`
across `a ∈ [1, X]`. -/
def continuumCellShiftCorr (c : ℕ → ℝ) (X m : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 X, c a * ∑ r ∈ range m, logCellWidth (a * m + r) * c (a * m + r)

/-- Exact divisibility spine (`r = 0` Euclidean quotient term) weighted by `w_a`. -/
def divisibleCellSpine (c : ℕ → ℝ) (X m : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 X, logCellWidth a * c a * c (a * m)

/-- Euclidean-remainder successor defect (`0 ≤ r < m`, vanishing at `r = 0`). -/
def euclideanCellRemainder (c : ℕ → ℝ) (X m : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 X, c a * ∑ r ∈ range m, logCellWidth (a * m + r) * (c (a * m + r) - c (a * m))

/-- **Exact Spine + Euclidean-Remainder Factorization (`continuumCellShiftCorr_eq_spine_add_remainder`).**
Unlike discrete lattice truncation, continuum logarithmic cells factor every multiplicative shift
`log m` into the `r = 0` divisibility spine plus the Euclidean successor remainder with **zero
boundary smearing error**. -/
theorem continuumCellShiftCorr_eq_spine_add_remainder (c : ℕ → ℝ) (X : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    continuumCellShiftCorr c X m =
      divisibleCellSpine c X m + euclideanCellRemainder c X m := by
  unfold continuumCellShiftCorr divisibleCellSpine euclideanCellRemainder
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
  have hinner : ∑ r ∈ range m, logCellWidth (a * m + r) * c (a * m + r) =
      (∑ r ∈ range m, logCellWidth (a * m + r)) * c (a * m) +
        ∑ r ∈ range m, logCellWidth (a * m + r) * (c (a * m + r) - c (a * m)) := by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => by ring
  rw [hinner, sum_logCellWidth_mul_add_eq ha1 hm]
  ring

/-! ## §3. Disjoint-Block Biarithmetic Sobolev Control of the Euclidean Remainder -/

/-- Logarithmic-cell `L²` norm squared `∑_{a=1}^X w_a c_a²` on `[1, X]`. -/
def cellL2NormSq (c : ℕ → ℝ) (X : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 X, logCellWidth a * c a ^ 2

/-- Biarithmetic discrete-derivative Sobolev energy `∑_{k=1}^N k (c_{k+1} − c_k)²`. -/
def biarithmeticSobolevEnergy (c : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Icc 1 N, (k : ℝ) * (c (k + 1) - c k) ^ 2

private theorem sq_sum_mul_le_bgg {ι : Type*} (S : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ S, f i * g i) ^ 2 ≤ (∑ i ∈ S, f i ^ 2) * (∑ i ∈ S, g i ^ 2) := by
  have hnn : 0 ≤ ∑ i ∈ S, ∑ j ∈ S, (f i * g j - f j * g i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hrow : ∀ i ∈ S, ∑ j ∈ S, (f i * g j - f j * g i) ^ 2 =
      f i ^ 2 * (∑ j ∈ S, g j ^ 2) + (∑ j ∈ S, f j ^ 2) * g i ^ 2 -
        (2 * f i * g i) * (∑ j ∈ S, f j * g j) := by
    intro i _
    have hexp : ∀ j : ι, (f i * g j - f j * g i) ^ 2 =
        f i ^ 2 * g j ^ 2 + f j ^ 2 * g i ^ 2 - (2 * f i * g i) * (f j * g j) :=
      fun j => by ring
    simp_rw [hexp, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul]
  have hs1 : ∑ i ∈ S, f i ^ 2 * (∑ j ∈ S, g j ^ 2) =
      (∑ i ∈ S, f i ^ 2) * (∑ j ∈ S, g j ^ 2) := (Finset.sum_mul S _ _).symm
  have hs2 : ∑ i ∈ S, (∑ j ∈ S, f j ^ 2) * g i ^ 2 =
      (∑ j ∈ S, f j ^ 2) * (∑ i ∈ S, g i ^ 2) := (Finset.mul_sum S _ _).symm
  have hs3 : ∑ i ∈ S, (2 * f i * g i) * (∑ j ∈ S, f j * g j) =
      2 * (∑ i ∈ S, f i * g i) ^ 2 := by
    rw [← Finset.sum_mul]
    have h2 : ∑ i ∈ S, 2 * f i * g i = 2 * ∑ i ∈ S, f i * g i := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring
    rw [h2]; ring
  rw [Finset.sum_congr rfl hrow, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      hs1, hs2, hs3] at hnn
  linarith

private theorem sub_add_eq_sum_range_diff (c : ℕ → ℝ) (N r : ℕ) :
    c (N + r) - c N = ∑ j ∈ range r, (c (N + j + 1) - c (N + j)) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Finset.sum_range_succ, ← ih]
    have h : N + (r + 1) = N + r + 1 := by omega
    rw [h]; ring

private theorem sub_mul_add_sq_le_block (c : ℕ → ℝ) {a m r : ℕ}
    (ha : 1 ≤ a) (hr : r < m) :
    (c (a * m + r) - c (a * m)) ^ 2 ≤
      (1 / (a : ℝ)) * ∑ j ∈ range m, ((a * m + j : ℕ) : ℝ) *
        (c (a * m + j + 1) - c (a * m + j)) ^ 2 := by
  rw [sub_add_eq_sum_range_diff c (a * m) r]
  have hcs := sq_sum_mul_le_bgg (range r) (fun _ => (1 : ℝ))
    (fun j => c (a * m + j + 1) - c (a * m + j))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hcs
  have ha_pos : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
  have hrm : (r : ℝ) ≤ m := by exact_mod_cast hr.le
  calc (∑ j ∈ range r, (c (a * m + j + 1) - c (a * m + j))) ^ 2
      ≤ (r : ℝ) * ∑ j ∈ range r, (c (a * m + j + 1) - c (a * m + j)) ^ 2 := hcs
    _ = ∑ j ∈ range r, (r : ℝ) * (c (a * m + j + 1) - c (a * m + j)) ^ 2 := Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ range r, ((1 / (a : ℝ)) * ((a * m + j : ℕ) : ℝ)) *
          (c (a * m + j + 1) - c (a * m + j)) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        have hm_le : (m : ℝ) ≤ (1 / (a : ℝ)) * ((a * m + j : ℕ) : ℝ) := by
          have hamj : (a : ℝ) * (m : ℝ) ≤ ((a * m + j : ℕ) : ℝ) := by
            have : a * m ≤ a * m + j := Nat.le_add_right _ _
            exact_mod_cast this
          calc (m : ℝ) = (1 / (a : ℝ)) * ((a : ℝ) * (m : ℝ)) := by field_simp [ha_pos.ne']
            _ ≤ (1 / (a : ℝ)) * ((a * m + j : ℕ) : ℝ) :=
              mul_le_mul_of_nonneg_left hamj (by positivity)
        exact hrm.trans hm_le
    _ ≤ ∑ j ∈ range m, ((1 / (a : ℝ)) * ((a * m + j : ℕ) : ℝ)) *
          (c (a * m + j + 1) - c (a * m + j)) ^ 2 := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hr.le) fun j _ _ => ?_
        positivity
    _ = (1 / (a : ℝ)) * ∑ j ∈ range m, ((a * m + j : ℕ) : ℝ) *
          (c (a * m + j + 1) - c (a * m + j)) ^ 2 := by
        simp_rw [mul_assoc, ← Finset.mul_sum]

private theorem sum_euclidean_blocks_le_sobolev (c : ℕ → ℝ) (X : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    (∑ a ∈ Icc 1 X, ∑ j ∈ range m,
      ((a * m + j : ℕ) : ℝ) * (c (a * m + j + 1) - c (a * m + j)) ^ 2) ≤
      biarithmeticSobolevEnergy c (X * m + m) := by
  let term : ℕ → ℝ := fun k => (k : ℝ) * (c (k + 1) - c k) ^ 2
  have hterm_nn : ∀ k : ℕ, 0 ≤ term k := fun k => mul_nonneg (Nat.cast_nonneg k) (sq_nonneg _)
  let P : Finset (ℕ × ℕ) := Icc 1 X ×ˢ range m
  let φ : ℕ × ℕ → ℕ := fun p => p.1 * m + p.2
  have hinj : Set.InjOn φ P := by
    intro ⟨a₁, j₁⟩ h₁ ⟨a₂, j₂⟩ h₂ heq
    simp only [P, mem_coe, mem_product, mem_Icc, mem_range] at h₁ h₂
    dsimp [φ] at heq
    have hdiv := congrArg (· / m) heq
    rw [Nat.mul_comm a₁ m, Nat.mul_comm a₂ m,
        Nat.mul_add_div (by omega : 0 < m), Nat.mul_add_div (by omega : 0 < m),
        Nat.div_eq_of_lt h₁.2, Nat.div_eq_of_lt h₂.2, add_zero, add_zero] at hdiv
    subst hdiv
    exact Prod.ext rfl (Nat.add_left_cancel heq)
  have hsub : P.image φ ⊆ Icc 1 (X * m + m) := by
    intro k hk
    obtain ⟨⟨a, j⟩, hp, rfl⟩ := mem_image.mp hk
    simp only [P, mem_product, mem_Icc, mem_range] at hp
    dsimp [φ]
    refine mem_Icc.mpr ⟨?_, ?_⟩
    · have : 1 * 1 ≤ a * m := Nat.mul_le_mul hp.1.1 hm
      omega
    · have : a * m ≤ X * m := Nat.mul_le_mul_right m hp.1.2
      omega
  calc (∑ a ∈ Icc 1 X, ∑ j ∈ range m, term (a * m + j))
      = ∑ p ∈ P, term (φ p) :=
        (Finset.sum_product (Icc 1 X) (range m) (fun p => term (φ p))).symm
    _ = ∑ k ∈ P.image φ, term k := (Finset.sum_image hinj).symm
    _ ≤ ∑ k ∈ Icc 1 (X * m + m), term k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hterm_nn k
    _ = biarithmeticSobolevEnergy c (X * m + m) := rfl

/-- **Disjoint-Block Biarithmetic Sobolev Bound (`euclideanCellRemainder_sq_le`).**
For every sequence `c : ℕ → ℝ`, horizon `X : ℕ`, and multiplier `m ≥ 1`,
`(euclideanCellRemainder c X m)² ≤ cellL2NormSq c X · biarithmeticSobolevEnergy c (X m + m)`
with constant `1`, uniformly in `m` and `X`. -/
theorem euclideanCellRemainder_sq_le (c : ℕ → ℝ) (X : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    euclideanCellRemainder c X m ^ 2 ≤
      cellL2NormSq c X * biarithmeticSobolevEnergy c (X * m + m) := by
  let R : ℕ → ℝ := fun a =>
    ∑ r ∈ range m, logCellWidth (a * m + r) * (c (a * m + r) - c (a * m))
  let B : ℕ → ℝ := fun a =>
    ∑ j ∈ range m, ((a * m + j : ℕ) : ℝ) * (c (a * m + j + 1) - c (a * m + j)) ^ 2
  have hR_bound : ∀ a ∈ Icc 1 X, R a ^ 2 / logCellWidth a ≤ B a := by
    intro a ha
    have ha1 : 1 ≤ a := (mem_Icc.mp ha).1
    have hwa_pos : 0 < logCellWidth a := logCellWidth_pos ha1
    -- Weighted Cauchy-Schwarz on `r ∈ range m`
    have hcs_r : R a ^ 2 ≤
        (∑ r ∈ range m, logCellWidth (a * m + r)) *
          ∑ r ∈ range m, logCellWidth (a * m + r) * (c (a * m + r) - c (a * m)) ^ 2 := by
      have h := sq_sum_mul_le_bgg (range m)
        (fun r => Real.sqrt (logCellWidth (a * m + r)))
        (fun r => Real.sqrt (logCellWidth (a * m + r)) * (c (a * m + r) - c (a * m)))
      have hw_nn : ∀ r : ℕ, 0 ≤ logCellWidth (a * m + r) := fun r => by
        have : 1 ≤ a * m + r := by
          have : 1 ≤ a * m := Nat.mul_le_mul ha1 hm
          omega
        exact (logCellWidth_pos this).le
      have hlhs : (∑ r ∈ range m, Real.sqrt (logCellWidth (a * m + r)) *
          (Real.sqrt (logCellWidth (a * m + r)) * (c (a * m + r) - c (a * m)))) = R a := by
        dsimp [R]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← mul_assoc, Real.mul_self_sqrt (hw_nn r)]
      have hr1 : ∑ r ∈ range m, Real.sqrt (logCellWidth (a * m + r)) ^ 2 =
          ∑ r ∈ range m, logCellWidth (a * m + r) :=
        Finset.sum_congr rfl fun r _ => Real.sq_sqrt (hw_nn r)
      have hr2 : ∑ r ∈ range m,
          (Real.sqrt (logCellWidth (a * m + r)) * (c (a * m + r) - c (a * m))) ^ 2 =
          ∑ r ∈ range m, logCellWidth (a * m + r) * (c (a * m + r) - c (a * m)) ^ 2 := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [mul_pow, Real.sq_sqrt (hw_nn r)]
      rw [hlhs, hr1, hr2] at h
      exact h
    rw [sum_logCellWidth_mul_add_eq ha1 hm] at hcs_r
    have hinner_le : ∑ r ∈ range m, logCellWidth (a * m + r) * (c (a * m + r) - c (a * m)) ^ 2 ≤
        logCellWidth a * ((1 / (a : ℝ)) * B a) := by
      calc ∑ r ∈ range m, logCellWidth (a * m + r) * (c (a * m + r) - c (a * m)) ^ 2
          ≤ ∑ r ∈ range m, logCellWidth (a * m + r) * ((1 / (a : ℝ)) * B a) := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hw_pos : 0 ≤ logCellWidth (a * m + r) :=
              (logCellWidth_pos (by have := Nat.mul_le_mul ha1 hm; omega)).le
            exact mul_le_mul_of_nonneg_left
              (sub_mul_add_sq_le_block c ha1 (mem_range.mp hr)) hw_pos
        _ = (∑ r ∈ range m, logCellWidth (a * m + r)) * ((1 / (a : ℝ)) * B a) :=
            (Finset.sum_mul _ _ _).symm
        _ = logCellWidth a * ((1 / (a : ℝ)) * B a) := by
            rw [sum_logCellWidth_mul_add_eq ha1 hm]
    have hwa_a_le1 : logCellWidth a * (1 / (a : ℝ)) ≤ 1 := by
      have h1 := logCellWidth_le_inv ha1
      have ha_ge1 : (1 : ℝ) ≤ a := by exact_mod_cast ha1
      have hinv_le1 : 1 / (a : ℝ) ≤ 1 := div_le_one_of_le₀ ha_ge1 (by positivity)
      calc logCellWidth a * (1 / (a : ℝ))
          ≤ (1 / (a : ℝ)) * 1 := mul_le_mul h1 hinv_le1 (by positivity) (by positivity)
        _ ≤ 1 := by linarith
    have hB_nn : 0 ≤ B a :=
      Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    rw [div_le_iff₀ hwa_pos]
    calc R a ^ 2
        ≤ logCellWidth a * (logCellWidth a * ((1 / (a : ℝ)) * B a)) :=
          hcs_r.trans (mul_le_mul_of_nonneg_left hinner_le hwa_pos.le)
      _ = (logCellWidth a * (1 / (a : ℝ))) * (B a * logCellWidth a) := by ring
      _ ≤ 1 * (B a * logCellWidth a) :=
          mul_le_mul_of_nonneg_right hwa_a_le1 (mul_nonneg hB_nn hwa_pos.le)
      _ = B a * logCellWidth a := one_mul _
  -- Outer Cauchy-Schwarz across `a ∈ Icc 1 X`
  have hcs_a := sq_sum_mul_le_bgg (Icc 1 X)
    (fun a => Real.sqrt (logCellWidth a) * c a)
    (fun a => R a / Real.sqrt (logCellWidth a))
  have hlhs_a : ∑ a ∈ Icc 1 X,
      (Real.sqrt (logCellWidth a) * c a) * (R a / Real.sqrt (logCellWidth a)) =
      euclideanCellRemainder c X m := by
    unfold euclideanCellRemainder
    refine Finset.sum_congr rfl fun a ha => ?_
    have hsqrt_nz : Real.sqrt (logCellWidth a) ≠ 0 :=
      (Real.sqrt_pos.mpr (logCellWidth_pos (mem_Icc.mp ha).1)).ne'
    dsimp [R]
    field_simp [hsqrt_nz]
  have hr1_a : ∑ a ∈ Icc 1 X, (Real.sqrt (logCellWidth a) * c a) ^ 2 = cellL2NormSq c X := by
    unfold cellL2NormSq
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [mul_pow, Real.sq_sqrt (logCellWidth_pos (mem_Icc.mp ha).1).le]
  have hr2_a : ∑ a ∈ Icc 1 X, (R a / Real.sqrt (logCellWidth a)) ^ 2 ≤
      biarithmeticSobolevEnergy c (X * m + m) := by
    calc ∑ a ∈ Icc 1 X, (R a / Real.sqrt (logCellWidth a)) ^ 2
        = ∑ a ∈ Icc 1 X, R a ^ 2 / logCellWidth a := by
          refine Finset.sum_congr rfl fun a ha => ?_
          rw [div_pow, Real.sq_sqrt (logCellWidth_pos (mem_Icc.mp ha).1).le]
      _ ≤ ∑ a ∈ Icc 1 X, B a := Finset.sum_le_sum hR_bound
      _ ≤ biarithmeticSobolevEnergy c (X * m + m) := sum_euclidean_blocks_le_sobolev c X hm
  rw [hlhs_a, hr1_a] at hcs_a
  have hL2_nn : 0 ≤ cellL2NormSq c X :=
    Finset.sum_nonneg fun a ha => mul_nonneg (logCellWidth_pos (mem_Icc.mp ha).1).le (sq_nonneg _)
  exact hcs_a.trans (mul_le_mul_of_nonneg_left hr2_a hL2_nn)

/-- **`m`-Uniform Biarithmetic Sobolev Bound for Horizon-Supported Profiles
(`abs_euclideanCellRemainder_le_of_supported`).**
When `c` vanishes past `X` (`∀ n > X, c n = 0`), every finite difference `c_{k+1} − c_k` vanishes
for `k > X`, yielding a completely `m`-independent upper bound on `|euclideanCellRemainder c X m|`. -/
theorem abs_euclideanCellRemainder_le_of_supported (c : ℕ → ℝ) (X : ℕ) {m : ℕ} (hm : 1 ≤ m)
    (hsupp : ∀ n : ℕ, X < n → c n = 0) :
    |euclideanCellRemainder c X m| ≤
      Real.sqrt (cellL2NormSq c X) * Real.sqrt (biarithmeticSobolevEnergy c X) := by
  have hsob_eq : biarithmeticSobolevEnergy c (X * m + m) = biarithmeticSobolevEnergy c X := by
    unfold biarithmeticSobolevEnergy
    have hsub : Icc 1 X ⊆ Icc 1 (X * m + m) := by
      refine Icc_subset_Icc_right ?_
      have : X * 1 ≤ X * m := Nat.mul_le_mul_left X hm
      omega
    symm
    refine Finset.sum_subset hsub fun k hk hnot => ?_
    have hkX : X < k := by simp only [mem_Icc] at hk hnot; omega
    rw [hsupp (k + 1) (by omega), hsupp k hkX, sub_self, sq, mul_zero, mul_zero]
  have hsq := euclideanCellRemainder_sq_le c X hm
  rw [hsob_eq] at hsq
  have hL2_nn : 0 ≤ cellL2NormSq c X :=
    Finset.sum_nonneg fun a ha => mul_nonneg (logCellWidth_pos (mem_Icc.mp ha).1).le (sq_nonneg _)
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul hL2_nn]
  exact Real.sqrt_le_sqrt hsq

end GaloisForLFunctions.BiarithmeticGaugeGeometry
