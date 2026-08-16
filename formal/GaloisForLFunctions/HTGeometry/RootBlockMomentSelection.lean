import GaloisForLFunctions.HTGeometry.MicroSpectrumMomentCollapse

/-!
# Root-of-unity blocks select one moment

A block of `k` eigenvalues placed at the `k`-th roots of unity scaled by `t` has vanishing power
sums except in the degrees divisible by `k`, where the sum is `k t^q`.  So such a block writes an
exact target into one chosen moment and disturbs no lower one.

Its Schatten cost, `k N |t|^p` with `N` copies and `t^k = c/(kN)`, is `(kN)^{1-p/k}|c|^{p/k}`, which
tends to zero as `N` grows precisely because `k < p`.  Selecting a moment below the Schatten order
is therefore free in the limit, and at `k = p` the exponent degenerates and it is not.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The primitive `k`-th root of unity. -/
noncomputable def unitRoot (k : ℕ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I / k)

/-- One eigenvalue of a root-of-unity block of radius `t`. -/
noncomputable def rootBlock (k : ℕ) (t : ℂ) (r : ℕ) : ℂ := t * unitRoot k ^ r

theorem unitRoot_isPrimitiveRoot {k : ℕ} (hk : k ≠ 0) : IsPrimitiveRoot (unitRoot k) k :=
  Complex.isPrimitiveRoot_exp k hk

/-- **Moment selection.**  A root-of-unity block has vanishing power sums except in degrees
divisible by its order. -/
theorem sum_rootBlock_pow {k : ℕ} (hk : k ≠ 0) (t : ℂ) (q : ℕ) :
    ∑ r ∈ Finset.range k, rootBlock k t r ^ q = if k ∣ q then (k : ℂ) * t ^ q else 0 := by
  have hprim := unitRoot_isPrimitiveRoot hk
  have hterm : ∀ r ∈ Finset.range k, rootBlock k t r ^ q = t ^ q * (unitRoot k ^ q) ^ r := by
    intro r _
    rw [rootBlock, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  by_cases hdvd : k ∣ q
  · have hone : unitRoot k ^ q = 1 := (hprim.pow_eq_one_iff_dvd q).mpr hdvd
    rw [hone, if_pos hdvd]
    simp [mul_comm]
  · have hne : unitRoot k ^ q ≠ 1 := fun h => hdvd ((hprim.pow_eq_one_iff_dvd q).mp h)
    rw [if_neg hdvd, geom_sum_eq hne]
    have hpow : (unitRoot k ^ q) ^ k = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    rw [hpow]
    simp

/-- The degree-`k` moment of a root-of-unity block of radius `t` is exactly `k t^k`. -/
theorem sum_rootBlock_pow_self {k : ℕ} (hk : k ≠ 0) (t : ℂ) :
    ∑ r ∈ Finset.range k, rootBlock k t r ^ k = (k : ℂ) * t ^ k := by
  rw [sum_rootBlock_pow hk t k, if_pos dvd_rfl]

/-- Every eigenvalue of the block has modulus `|t|`. -/
theorem norm_rootBlock {k : ℕ} (hk : k ≠ 0) (t : ℂ) (r : ℕ) : ‖rootBlock k t r‖ = ‖t‖ := by
  have hprim := unitRoot_isPrimitiveRoot hk
  have hnorm : ‖unitRoot k‖ = 1 := by
    rw [unitRoot, Complex.norm_exp]
    have hre : (2 * (Real.pi : ℂ) * Complex.I / (k : ℂ)).re = 0 := by
      simp [Complex.div_re, Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero]
  rw [rootBlock, norm_mul, norm_pow, hnorm, one_pow, mul_one]

/-! ## The Schatten cost of a selecting block -/

/-- **The cost of writing one moment below the Schatten order vanishes.**  Distributing a target of
size `c` over `N` copies of a `k`-block costs `(kN)^{1-p/k}|c|^{p/k}` in Schatten `p` energy, which
tends to zero exactly when `k < p`. -/
theorem tendsto_rootBlock_schattenCost {k : ℕ} (hk : 0 < k) {p c : ℝ} (hkp : (k : ℝ) < p) :
    Filter.Tendsto (fun N : ℕ => ((k * N : ℝ)) ^ (1 - p / k) * c ^ (p / k))
      Filter.atTop (nhds 0) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hy : 0 < p / k - 1 := by
    have : 1 < p / k := (one_lt_div hkR).mpr hkp
    linarith
  have hbase : Filter.Tendsto (fun N : ℕ => ((k * N : ℝ))) Filter.atTop Filter.atTop := by
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    refine Filter.tendsto_atTop_mono (fun N => ?_) tendsto_natCast_atTop_atTop
    nlinarith [Nat.cast_nonneg (α := ℝ) N, hk1]
  have h0 : Filter.Tendsto (fun x : ℝ => x ^ (1 - p / k)) Filter.atTop (nhds 0) := by
    have hneg := tendsto_rpow_neg_atTop hy
    have hexp : -(p / k - 1) = 1 - p / k := by ring
    rw [hexp] at hneg
    exact hneg
  have hcomp := h0.comp hbase
  have hmul := hcomp.mul_const (c ^ (p / k))
  simpa using hmul

end

end GaloisForLFunctions.HTGeometry
