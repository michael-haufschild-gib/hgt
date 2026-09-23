import GaloisForLFunctions.RHTower.RadialGramOffDiagonalDecay
import GaloisForLFunctions.RHTower.ConstrainedProlateExteriorWeil
import Mathlib

/-!
# The radial prime first-row reduction: exact split, truncated charge, and coalescing scale

The card reduces the raw prime Gram charge `(2)` to a single weighted first-row series `(14)`.
Four exact layers of that reduction are formalized here; the remaining layers already exist in the
tree and are reused rather than rebuilt.

*The exact three-way split.*  Equations `(10)`–`(11)`.  For every radial cutoff `K` the raw charge
splits, as a finite identity in an arbitrary Gram array, into the diagonal charge, the first-row
charge, and the `j,k ≥ 2` nonstationary sector.

*The truncated divisor charge.*  The exact finite prime aperture replaces `log k` by
`a_λ(k) = ∑_{q ∣ k, q ≤ λ²} Λ(q)`.  It is nonnegative and dominated by `log k`, which is exactly
what makes the dominated-convergence transfer of `(12)`–`(13)` legitimate.

*The limiting radial phase.*  Equation `(6)`: `d/dx ξ_∞(r x) = r² x / √(r²x²−1)`, together with its
derivative, the second derivative of the difference phase.

*The coalescing stationary scale.*  Equations `(15)`, `(16)`, `(20)`.  The difference phase
`ξ_∞(x) − ξ_∞(k x)` has, on `x > 1`, exactly one stationary point `x_k = √(1 + 1/k²)`; there
`ρ(x_k) = 1/k`, `ρ(k x_k) = k`, the second derivative of the difference phase equals `−(k³ − 1/k)`,
and `k²(x_k − 1) → 1/2`.

## Already in the tree, reused here

* The divisor identity `(3)`, `∑_{m ∣ k, m ≥ 2} Λ(m) = log k`, is
  `constrainedProlate_sum_vonMangoldt_divisors_ge_two`.
* The Hilbert-kernel row estimate `(8)` and the weighted sector convergence `(9)` are
  `RHTower.radialRowSum_le`, `RHTower.summable_weighted_rowMajorant` and
  `RHTower.summable_weighted_rowBound`.
* The exterior critical point and curvature `(23f)` of the Weber phase
  `φ_k(r) = r − √(k²r² + k² − 1)` are `radialPhaseDeriv_critical` and
  `radialPhaseSecondDeriv_critical` in `CCMLimitingRadialWeber`.
* The diagonal limit `(12)` series `∑ log k/k · arcsin(1/k)` is `constrainedProlatePrimeSeriesTerm`.

Dunster's uniform radial expansion `(5)`, the phase-preserving Gram bound `(4)`, the
stationary-phase estimates `(21)`–`(24)`, and the Weber–Abel transform `(23b)` are cited parents
and stay outside the Lean statement.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The exact three-way split of the raw prime charge -/

/-- The radial index range `1 ≤ j ≤ K` is the first row together with the sector `2 ≤ j ≤ K`. -/
theorem Icc_one_eq_insert_Icc_two {K : ℕ} (hK : 1 ≤ K) :
    Finset.Icc 1 K = insert 1 (Finset.Icc 2 K) := by
  ext j
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- **Equations (10)–(11), row form.**  Each radial row splits into its first-row entry, its
diagonal entry, and the strictly off-diagonal sector. -/
theorem radialPrimeRow_split {K k : ℕ} (hK : 1 ≤ K) (hk2 : 2 ≤ k) (hkK : k ≤ K)
    (G : ℕ → ℕ → ℝ) :
    (∑ j ∈ Finset.Icc 1 K, G j k)
      = G 1 k + G k k + ∑ j ∈ (Finset.Icc 2 K).erase k, G j k := by
  have hmem : k ∈ Finset.Icc 2 K := Finset.mem_Icc.mpr ⟨hk2, hkK⟩
  have hnot : (1 : ℕ) ∉ Finset.Icc 2 K := by
    simp only [Finset.mem_Icc]
    omega
  rw [Icc_one_eq_insert_Icc_two hK, Finset.sum_insert hnot,
    ← Finset.add_sum_erase _ (fun j => G j k) hmem]
  ring

/-- **Equations (10)–(11).**  The raw prime Gram charge splits exactly into the diagonal charge,
the first-row charge, and the nonstationary `j,k ≥ 2` sector. -/
theorem radialPrimeCharge_split {K : ℕ} (hK : 1 ≤ K) (G : ℕ → ℕ → ℝ) (a : ℕ → ℝ) :
    (-2 : ℝ) * ∑ k ∈ Finset.Icc 2 K, a k * ∑ j ∈ Finset.Icc 1 K, G j k
      = (-2 : ℝ) * ∑ k ∈ Finset.Icc 2 K, a k * G k k
        + (-2 : ℝ) * ∑ k ∈ Finset.Icc 2 K, a k * G 1 k
        + (-2 : ℝ) * ∑ k ∈ Finset.Icc 2 K, a k * ∑ j ∈ (Finset.Icc 2 K).erase k, G j k := by
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  rw [radialPrimeRow_split hK hk'.1 hk'.2 G]
  ring

/-! ## The truncated divisor charge of the exact finite aperture -/

/-- `a_λ(k) = ∑_{q ∣ k, 2 ≤ q ≤ L} Λ(q)`: the exact finite-aperture prime weight, with the divisor
cutoff `L = λ²`. -/
def truncatedVonMangoldtCharge (L k : ℕ) : ℝ :=
  ∑ q ∈ k.divisors.filter (fun q => 2 ≤ q ∧ q ≤ L), ArithmeticFunction.vonMangoldt q

/-- The truncated prime weight is nonnegative. -/
theorem truncatedVonMangoldtCharge_nonneg (L k : ℕ) : 0 ≤ truncatedVonMangoldtCharge L k :=
  Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg

/-- **The aperture domination `a_λ(k) ≤ log k`.**  Truncating the divisor range can only remove
nonnegative von Mangoldt mass, and the untruncated charge is exactly `log k` by `(3)`.  This is the
dominated-convergence hypothesis that transfers `(12)`–`(13)` to the exact finite aperture. -/
theorem truncatedVonMangoldtCharge_le_log (L k : ℕ) :
    truncatedVonMangoldtCharge L k ≤ Real.log k := by
  rw [← constrainedProlate_sum_vonMangoldt_divisors_ge_two k]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro q hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.1⟩
  · intro q _ _
    exact ArithmeticFunction.vonMangoldt_nonneg

/-! ## The limiting radial phase -/

/-- The limiting radial phase `ξ_∞(t) = ρ(t) = √(t² − 1)`. -/
def radialLimitPhase (t : ℝ) : ℝ := Real.sqrt (t ^ (2 : ℕ) - 1)

/-- The derivative of the unscaled limiting phase. -/
theorem hasDerivAt_radialLimitPhase {x : ℝ} (h : 0 < x ^ (2 : ℕ) - 1) :
    HasDerivAt radialLimitPhase (x / Real.sqrt (x ^ (2 : ℕ) - 1)) x := by
  have hu : HasDerivAt (fun s : ℝ => s ^ (2 : ℕ) - 1) (2 * x) x := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ (2 : ℕ)) (2 * x) x := by
      simpa using (hasDerivAt_id x).fun_pow 2
    simpa using h1.sub_const 1
  have hsqrt := hu.sqrt (ne_of_gt h)
  refine hsqrt.congr_deriv ?_
  have hs : 0 < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr h
  field_simp

/-- **Equation (6).**  The scaled limiting radial phase `x ↦ ξ_∞(k x)` has derivative
`k² x / √(k²x² − 1)`. -/
theorem hasDerivAt_radialLimitPhase_scaled {k x : ℝ} (h : 0 < k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) :
    HasDerivAt (fun s : ℝ => radialLimitPhase (k * s))
      (k ^ (2 : ℕ) * x / Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1)) x := by
  have hfun : (fun s : ℝ => radialLimitPhase (k * s))
      = fun s : ℝ => Real.sqrt (k ^ (2 : ℕ) * s ^ (2 : ℕ) - 1) := by
    funext s
    simp [radialLimitPhase, mul_pow]
  rw [hfun]
  have hu : HasDerivAt (fun s : ℝ => k ^ (2 : ℕ) * s ^ (2 : ℕ) - 1) (k ^ (2 : ℕ) * (2 * x)) x := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ (2 : ℕ)) (2 * x) x := by
      simpa using (hasDerivAt_id x).fun_pow 2
    simpa using (h1.const_mul (k ^ (2 : ℕ))).sub_const 1
  have hsqrt := hu.sqrt (ne_of_gt h)
  refine hsqrt.congr_deriv ?_
  have hs : 0 < Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr h
  field_simp

/-- The derivative of the difference phase `ξ_∞(x) − ξ_∞(k x)`. -/
def radialDiffPhaseDeriv (k x : ℝ) : ℝ :=
  x / Real.sqrt (x ^ (2 : ℕ) - 1) - k ^ (2 : ℕ) * x / Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1)

/-- The difference phase differentiates to `radialDiffPhaseDeriv`. -/
theorem hasDerivAt_radialDiffPhase {k x : ℝ} (h1 : 0 < x ^ (2 : ℕ) - 1)
    (h2 : 0 < k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) :
    HasDerivAt (fun s : ℝ => radialLimitPhase s - radialLimitPhase (k * s))
      (radialDiffPhaseDeriv k x) x :=
  (hasDerivAt_radialLimitPhase h1).sub (hasDerivAt_radialLimitPhase_scaled h2)

/-! ## The coalescing stationary point -/

/-- The coalescing stationary point `x_k = √(1 + 1/k²)` of `(15)`. -/
def radialCoalescePoint (k : ℝ) : ℝ := Real.sqrt (1 + 1 / k ^ (2 : ℕ))

/-- **Equation (15).**  The square of the coalescing point. -/
theorem radialCoalescePoint_sq (k : ℝ) : radialCoalescePoint k ^ (2 : ℕ) = 1 + 1 / k ^ (2 : ℕ) :=
  Real.sq_sqrt (by positivity)

/-- The coalescing point exceeds the radial endpoint. -/
theorem one_lt_radialCoalescePoint {k : ℝ} (hk : k ≠ 0) : 1 < radialCoalescePoint k := by
  have hpos : (0 : ℝ) < 1 / k ^ (2 : ℕ) := by positivity
  have h1 : (1 : ℝ) < 1 + 1 / k ^ (2 : ℕ) := by linarith
  have := Real.sqrt_lt_sqrt (by norm_num) h1
  rwa [Real.sqrt_one] at this

/-- **Equation (20), first value.**  `ρ(x_k) = 1/k`. -/
theorem radialLimitPhase_coalescePoint {k : ℝ} (hk : 0 < k) :
    radialLimitPhase (radialCoalescePoint k) = 1 / k := by
  unfold radialLimitPhase
  rw [radialCoalescePoint_sq]
  have harg : (1 : ℝ) + 1 / k ^ (2 : ℕ) - 1 = (1 / k) ^ (2 : ℕ) := by
    field_simp
    ring
  rw [harg, Real.sqrt_sq (by positivity)]

/-- **Equation (20), second value.**  `ρ(k x_k) = k`. -/
theorem radialLimitPhase_scaled_coalescePoint {k : ℝ} (hk : 0 < k) :
    radialLimitPhase (k * radialCoalescePoint k) = k := by
  unfold radialLimitPhase
  rw [mul_pow, radialCoalescePoint_sq]
  have harg : k ^ (2 : ℕ) * (1 + 1 / k ^ (2 : ℕ)) - 1 = k ^ (2 : ℕ) := by
    field_simp
    ring
  rw [harg, Real.sqrt_sq hk.le]

/-- **Equation (15), stationarity.**  The coalescing point is a stationary point of the difference
phase. -/
theorem radialDiffPhaseDeriv_coalescePoint {k : ℝ} (hk : 0 < k) :
    radialDiffPhaseDeriv k (radialCoalescePoint k) = 0 := by
  have hx := radialCoalescePoint_sq k
  have h1 : Real.sqrt (radialCoalescePoint k ^ (2 : ℕ) - 1) = 1 / k := by
    have := radialLimitPhase_coalescePoint hk
    unfold radialLimitPhase at this
    exact this
  have h2 : Real.sqrt (k ^ (2 : ℕ) * radialCoalescePoint k ^ (2 : ℕ) - 1) = k := by
    have := radialLimitPhase_scaled_coalescePoint hk
    unfold radialLimitPhase at this
    rwa [mul_pow] at this
  unfold radialDiffPhaseDeriv
  rw [h1, h2]
  field_simp
  ring

/-- **Equation (15), uniqueness.**  On the radial exterior `x > 1` the coalescing point is the only
stationary point of the difference phase. -/
theorem radialDiffPhaseDeriv_eq_zero_iff {k x : ℝ} (hk : 1 < k) (hx : 1 < x) :
    radialDiffPhaseDeriv k x = 0 ↔ x = radialCoalescePoint k := by
  have hk0 : (0 : ℝ) < k := lt_trans one_pos hk
  have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
  have h1 : (0 : ℝ) < x ^ (2 : ℕ) - 1 := by nlinarith
  have h2 : (0 : ℝ) < k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := by nlinarith
  have hs1 : (0 : ℝ) < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr h1
  have hs2 : (0 : ℝ) < Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr h2
  constructor
  · intro hzero
    have heq : x / Real.sqrt (x ^ (2 : ℕ) - 1) = k ^ (2 : ℕ) * x / Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) := by
      have h := hzero
      unfold radialDiffPhaseDeriv at h
      linarith
    have hcross : x * Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) = k ^ (2 : ℕ) * x * Real.sqrt (x ^ (2 : ℕ) - 1) :=
      (div_eq_div_iff (ne_of_gt hs1) (ne_of_gt hs2)).mp heq
    have hcross' : x * Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1)
        = x * (k ^ (2 : ℕ) * Real.sqrt (x ^ (2 : ℕ) - 1)) := by
      rw [hcross]; ring
    have hdiv : Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) = k ^ (2 : ℕ) * Real.sqrt (x ^ (2 : ℕ) - 1) :=
      mul_left_cancel₀ (ne_of_gt hx0) hcross'
    have hl : Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) ^ (2 : ℕ) = k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := Real.sq_sqrt h2.le
    have hr : Real.sqrt (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) = x ^ (2 : ℕ) - 1 := Real.sq_sqrt h1.le
    have hc : Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) ^ (2 : ℕ)
        = (k ^ (2 : ℕ) * Real.sqrt (x ^ (2 : ℕ) - 1)) ^ (2 : ℕ) := by rw [hdiv]
    rw [hl, mul_pow, hr] at hc
    have hsq : k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 = k ^ (4 : ℕ) * (x ^ (2 : ℕ) - 1) := by
      calc k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 = (k ^ (2 : ℕ)) ^ (2 : ℕ) * (x ^ (2 : ℕ) - 1) := hc
        _ = k ^ (4 : ℕ) * (x ^ (2 : ℕ) - 1) := by ring
    have hk2 : (1 : ℝ) < k ^ (2 : ℕ) := by nlinarith
    have hcancel : (k ^ (2 : ℕ) - 1) * (k ^ (2 : ℕ) + 1) = (k ^ (2 : ℕ) - 1) * (x ^ (2 : ℕ) * k ^ (2 : ℕ)) := by
      linear_combination hsq
    have hx2k : k ^ (2 : ℕ) + 1 = x ^ (2 : ℕ) * k ^ (2 : ℕ) :=
      mul_left_cancel₀ (ne_of_gt (by linarith : (0 : ℝ) < k ^ (2 : ℕ) - 1)) hcancel
    have hx2 : x ^ (2 : ℕ) = 1 + 1 / k ^ (2 : ℕ) := by
      have hkne : (k : ℝ) ^ (2 : ℕ) ≠ 0 := by positivity
      field_simp
      linarith [hx2k]
    have hgoal : Real.sqrt (x ^ (2 : ℕ)) = radialCoalescePoint k := by
      unfold radialCoalescePoint
      rw [hx2]
    rw [← hgoal, Real.sqrt_sq hx0.le]
  · intro hxeq
    rw [hxeq]
    exact radialDiffPhaseDeriv_coalescePoint hk0

/-! ## The curvature at the coalescing point -/

/-- The derivative of `x ↦ x / √(x² − 1)`. -/
theorem hasDerivAt_radialLimitPhaseDeriv {x : ℝ} (h : 0 < x ^ (2 : ℕ) - 1) :
    HasDerivAt (fun s : ℝ => s / Real.sqrt (s ^ (2 : ℕ) - 1))
      (-(1 / Real.sqrt (x ^ (2 : ℕ) - 1) ^ (3 : ℕ))) x := by
  have hs : 0 < Real.sqrt (x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr h
  have hsq : Real.sqrt (x ^ (2 : ℕ) - 1) ^ (2 : ℕ) = x ^ (2 : ℕ) - 1 := Real.sq_sqrt h.le
  have hnum : HasDerivAt (fun s : ℝ => s) 1 x := hasDerivAt_id x
  have hden : HasDerivAt (fun s : ℝ => Real.sqrt (s ^ (2 : ℕ) - 1))
      (x / Real.sqrt (x ^ (2 : ℕ) - 1)) x := hasDerivAt_radialLimitPhase h
  have hres := hnum.fun_div hden (ne_of_gt hs)
  refine hres.congr_deriv ?_
  field_simp
  nlinarith [hsq, hs]

/-- The derivative of `x ↦ k² x / √(k²x² − 1)`. -/
theorem hasDerivAt_radialLimitPhaseDeriv_scaled {k x : ℝ} (h : 0 < k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) :
    HasDerivAt (fun s : ℝ => k ^ (2 : ℕ) * s / Real.sqrt (k ^ (2 : ℕ) * s ^ (2 : ℕ) - 1))
      (-(k ^ (2 : ℕ) / Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) ^ (3 : ℕ))) x := by
  have hs : 0 < Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) := Real.sqrt_pos.mpr h
  have hsq : Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) ^ (2 : ℕ) = k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1 := Real.sq_sqrt h.le
  have hnum : HasDerivAt (fun s : ℝ => k ^ (2 : ℕ) * s) (k ^ (2 : ℕ)) x := by
    simpa using (hasDerivAt_id x).const_mul (k ^ (2 : ℕ))
  have hden : HasDerivAt (fun s : ℝ => Real.sqrt (k ^ (2 : ℕ) * s ^ (2 : ℕ) - 1))
      (k ^ (2 : ℕ) * x / Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1)) x := by
    have hfun : (fun s : ℝ => radialLimitPhase (k * s))
        = fun s : ℝ => Real.sqrt (k ^ (2 : ℕ) * s ^ (2 : ℕ) - 1) := by
      funext s
      simp [radialLimitPhase, mul_pow]
    rw [← hfun]
    exact hasDerivAt_radialLimitPhase_scaled h
  have hres := hnum.fun_div hden (ne_of_gt hs)
  refine hres.congr_deriv ?_
  field_simp
  nlinarith [hsq, hs]

/-- The second derivative of the difference phase. -/
theorem hasDerivAt_radialDiffPhaseDeriv {k x : ℝ} (h1 : 0 < x ^ (2 : ℕ) - 1)
    (h2 : 0 < k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) :
    HasDerivAt (radialDiffPhaseDeriv k)
      (-(1 / Real.sqrt (x ^ (2 : ℕ) - 1) ^ (3 : ℕ)) + k ^ (2 : ℕ) / Real.sqrt (k ^ (2 : ℕ) * x ^ (2 : ℕ) - 1) ^ (3 : ℕ)) x := by
  have hres := (hasDerivAt_radialLimitPhaseDeriv h1).fun_sub
    (hasDerivAt_radialLimitPhaseDeriv_scaled h2)
  have hfun : radialDiffPhaseDeriv k
      = fun s : ℝ => s / Real.sqrt (s ^ (2 : ℕ) - 1) - k ^ (2 : ℕ) * s / Real.sqrt (k ^ (2 : ℕ) * s ^ (2 : ℕ) - 1) := rfl
  rw [hfun]
  refine hres.congr_deriv ?_
  ring

/-- **Equation (20), curvature.**  At the coalescing point the difference phase has second
derivative exactly `−(k³ − 1/k)`. -/
theorem radialDiffPhase_secondDeriv_coalescePoint {k : ℝ} (hk : 1 < k) :
    HasDerivAt (radialDiffPhaseDeriv k) (-(k ^ (3 : ℕ) - 1 / k)) (radialCoalescePoint k) := by
  have hk0 : (0 : ℝ) < k := lt_trans one_pos hk
  have hxsq := radialCoalescePoint_sq k
  have h1 : (0 : ℝ) < radialCoalescePoint k ^ (2 : ℕ) - 1 := by
    rw [hxsq]
    have : (0 : ℝ) < 1 / k ^ (2 : ℕ) := by positivity
    linarith
  have h2 : (0 : ℝ) < k ^ (2 : ℕ) * radialCoalescePoint k ^ (2 : ℕ) - 1 := by
    rw [hxsq]
    have hkne : k ≠ 0 := ne_of_gt hk0
    have hval : k ^ (2 : ℕ) * (1 + 1 / k ^ (2 : ℕ)) - 1 = k ^ (2 : ℕ) := by field_simp; ring
    rw [hval]
    positivity
  have hs1 : Real.sqrt (radialCoalescePoint k ^ (2 : ℕ) - 1) = 1 / k := by
    have := radialLimitPhase_coalescePoint hk0
    unfold radialLimitPhase at this
    exact this
  have hs2 : Real.sqrt (k ^ (2 : ℕ) * radialCoalescePoint k ^ (2 : ℕ) - 1) = k := by
    have := radialLimitPhase_scaled_coalescePoint hk0
    unfold radialLimitPhase at this
    rwa [mul_pow] at this
  have hres := hasDerivAt_radialDiffPhaseDeriv h1 h2
  rw [hs1, hs2] at hres
  refine hres.congr_deriv ?_
  field_simp
  ring

/-! ## The coalescing rate -/

/-- The coalescing point tends to the radial endpoint. -/
theorem tendsto_radialCoalescePoint :
    Filter.Tendsto radialCoalescePoint Filter.atTop (nhds 1) := by
  have hsq : Filter.Tendsto (fun k : ℝ => k ^ (2 : ℕ)) Filter.atTop Filter.atTop := by
    simpa [pow_two] using Filter.tendsto_id.atTop_mul_atTop₀ (Filter.tendsto_id (α := ℝ))
  have hzero : Filter.Tendsto (fun k : ℝ => 1 / k ^ (2 : ℕ)) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun k : ℝ => (k ^ (2 : ℕ))⁻¹) Filter.atTop (nhds 0) :=
      hsq.inv_tendsto_atTop.congr fun k => rfl
    simpa [one_div] using h2
  have hinner : Filter.Tendsto (fun k : ℝ => 1 + 1 / k ^ (2 : ℕ)) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hzero
  have hcomp : Filter.Tendsto (fun k : ℝ => Real.sqrt (1 + 1 / k ^ (2 : ℕ))) Filter.atTop
      (nhds (Real.sqrt 1)) := (Real.continuous_sqrt.tendsto 1).comp hinner
  rw [Real.sqrt_one] at hcomp
  exact hcomp

/-- **Equation (16).**  The coalescing point approaches the radial endpoint at the exact rate
`x_k − 1 ∼ 1/(2k²)`. -/
theorem tendsto_radialCoalesceRate :
    Filter.Tendsto (fun k : ℝ => k ^ (2 : ℕ) * (radialCoalescePoint k - 1)) Filter.atTop
      (nhds (1 / 2)) := by
  have hlim : Filter.Tendsto (fun k : ℝ => 1 / (radialCoalescePoint k + 1)) Filter.atTop
      (nhds (1 / 2)) := by
    have hden : Filter.Tendsto (fun k : ℝ => radialCoalescePoint k + 1) Filter.atTop
        (nhds (1 + 1)) := tendsto_radialCoalescePoint.add tendsto_const_nhds
    have hne : (1 : ℝ) + 1 ≠ 0 := by norm_num
    have hnum : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
    have hdiv := hnum.div hden hne
    norm_num at hdiv
    exact hdiv
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with k hk
  have hkne : (k : ℝ) ^ (2 : ℕ) ≠ 0 := by positivity
  have hone : 1 < radialCoalescePoint k := one_lt_radialCoalescePoint (ne_of_gt hk)
  have hsum : radialCoalescePoint k + 1 ≠ 0 := by linarith
  have hsq := radialCoalescePoint_sq k
  have hfac : (radialCoalescePoint k - 1) * (radialCoalescePoint k + 1) = 1 / k ^ (2 : ℕ) := by
    linear_combination hsq
  rw [eq_comm, eq_div_iff hsum]
  calc k ^ (2 : ℕ) * (radialCoalescePoint k - 1) * (radialCoalescePoint k + 1)
      = k ^ (2 : ℕ) * ((radialCoalescePoint k - 1) * (radialCoalescePoint k + 1)) := by ring
    _ = k ^ (2 : ℕ) * (1 / k ^ (2 : ℕ)) := by rw [hfac]
    _ = 1 := by field_simp

end GaloisForLFunctions.RHTower

end
